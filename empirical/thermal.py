# -*- coding: utf-8 -*-
"""
温度守卫（ThermalGuard）：GPU/CPU 过热的保护性节流
==================================================
- GPU 温度：nvidia-smi（可用）；> gpu_max 时冷却到 gpu_resume 以下
- CPU 温度：Windows 无权限读取（WMI 拒绝），用 CPU 利用率作代理；
  > cpu_util_max 时冷却（sleep）
- 保守节流：两次检查最小间隔 + 训练中定期强制冷却（防热量积累）
用法：
    from thermal import ThermalGuard
    guard = ThermalGuard(gpu_max=70, gpu_resume=65)
    ...训练循环...
    guard.check("step 500")     # 超限则冷却（阻塞 sleep）
    guard.cooldown(20)          # 模式间固定冷却
"""
import os
import subprocess
import threading
import time

_NVIDIA = None
for _p in (r"C:\Windows\System32\nvidia-smi.exe",
           r"C:\Program Files\NVIDIA Corporation\NVSMI\nvidia-smi.exe",
           "nvidia-smi"):
    if os.path.exists(_p) if os.path.sep in _p else True:
        try:
            subprocess.run([_p, "--version"], capture_output=True, timeout=5)
            _NVIDIA = _p
            break
        except Exception:
            _NVIDIA = None


def gpu_temp():
    """GPU 温度（°C）；不可用返回 None。"""
    if not _NVIDIA:
        return None
    try:
        out = subprocess.run([_NVIDIA, "--query-gpu=temperature.gpu",
                              "--format=csv,noheader,nounits"],
                             capture_output=True, text=True, timeout=10)
        return float(out.stdout.strip().split()[0])
    except Exception:
        return None


def cpu_util():
    """CPU 利用率（%）；不可用返回 None。"""
    try:
        ps = 'powershell -NoProfile -Command "(Get-Counter \'\\Processor Information(_Total)\\% Processor Utility\' -ErrorAction Stop).CounterSamples[0].CookedValue"'
        out = subprocess.run(ps, capture_output=True, text=True, timeout=10, shell=True)
        return float(out.stdout.strip())
    except Exception:
        return None


class ThermalGuard:
    """GPU/CPU 过热保护（v3：后台线程 0.5s 高频探测）。

    v2 的教训（2026-08-19 E5 第三次高温宕机）：check_interval=15s 时，
    guard 只在训练循环按步长调用点测温，GPU 在两次采样之间可从 52°C 冲到
    72°C+（越过 ~75-80°C 死机临界）而无人发现。v3 用后台守护线程每
    check_interval（默认 0.5s）采样一次 GPU 温度，独立于训练循环的调用频率；
    check() 仅读取线程的最新读数（微秒级），过热时阻塞训练直到恢复。
    """
    def __init__(self, gpu_max=58.0, gpu_resume=52.0, cpu_util_max=70.0,
                 check_interval=0.5, verbose=True):
        self.gpu_max = gpu_max
        self.gpu_resume = gpu_resume
        self.cpu_util_max = cpu_util_max
        self.check_interval = check_interval
        self.verbose = verbose
        self.cooled = 0
        self._lock = threading.Lock()
        self._gpu_now = None
        self._hot = False
        self._cpu_now = None
        self._cpu_hot = False
        self._cooling = False
        self._stop = False
        self._t0 = time.time()
        self._thread = threading.Thread(target=self._monitor, daemon=True)
        self._thread.start()

    def _log(self, msg):
        if self.verbose:
            print(f"[thermal] {msg}", flush=True)

    def _monitor(self):
        """后台守护线程：GPU 每 check_interval 秒采样；CPU 每 10s 采样（Get-Counter 慢且发热）。"""
        last_cpu = 0.0
        while not self._stop:
            g = gpu_temp()
            with self._lock:
                self._gpu_now = g
                self._hot = (g is not None and g >= self.gpu_max)
            now = time.time()
            if not self._cooling and now - last_cpu >= 10.0:
                c = cpu_util()
                with self._lock:
                    self._cpu_now = c
                    self._cpu_hot = (c is not None and c >= self.cpu_util_max)
                last_cpu = now
            time.sleep(self.check_interval)

    def _read(self):
        with self._lock:
            return self._gpu_now, self._hot, self._cpu_now, self._cpu_hot

    def check(self, label=""):
        """快速检查（读后台线程最新读数）；过热则阻塞冷却（GPU 到 resume 以下 / CPU 30s）。"""
        g, hot, c, cpu_hot = self._read()
        cooled = False
        if hot:
            self._log(f"{label}: GPU {g}°C >= {self.gpu_max}°C，冷却到 {self.gpu_resume}°C 以下")
            with self._lock:
                self._cooling = True
            t_start = time.time()
            try:
                while True:
                    time.sleep(0.5)
                    g2, _, _, _ = self._read()
                    # v3.1 修正：必须冷却到 gpu_resume 以下才恢复；
                    # v3 曾误用 `not hot2`（<gpu_max 就恢复），导致热积累逐次爬升直至宕机。
                    if g2 is None or g2 < self.gpu_resume:
                        g = g2
                        break
                    # 防死锁（v3.2）：机箱过热时 resume 可能不可达（如空闲基线已 > resume），
                    # 若冷却超过 10 分钟且已低于 gpu_max，带警告恢复训练（否则无限阻塞）。
                    if time.time() - t_start > 600.0 and g2 < self.gpu_max:
                        self._log(f"{label}: 冷却超时 600s，温度 {g2}°C 仍高于 resume 但低于 max，警告后恢复")
                        g = g2
                        break
            finally:
                with self._lock:
                    self._cooling = False
            self.cooled += 1
            cooled = True
            self._log(f"{label}: GPU 恢复 {g if g is not None else '?'}°C")
        if cpu_hot:
            self._log(f"{label}: CPU 利用率 {c:.0f}% >= {self.cpu_util_max}%，冷却 30s")
            time.sleep(30)
            self.cooled += 1
            cooled = True
        return cooled

    def cooldown(self, seconds):
        """固定冷却（模式间 / 训练间）。"""
        if seconds > 0:
            self._log(f"固定冷却 {seconds}s")
            time.sleep(seconds)

    def stop(self):
        """停止后台线程（进程退出前调用，避免守护线程残留）。"""
        self._stop = True
        if self._thread.is_alive():
            self._thread.join(timeout=1.0)
