# -*- coding: utf-8 -*-
"""
温度基线探针：训练前确认环境散热余量（新会话第一步）
用法：python thermal_probe.py --minutes 10 [--interval 0.5]
采样 GPU 温度（每 0.5s，v3：高频探测以捕捉快速爬升）+ CPU 利用率（每 5s，
Get-Counter 调用慢），报告峰值，判断是否可安全训练。
"""
import sys, time
sys.path.insert(0, __file__.rsplit("\\", 1)[0])
from thermal import gpu_temp, cpu_util

def main():
    minutes = float(sys.argv[sys.argv.index("--minutes") + 1]) if "--minutes" in sys.argv else 10.0
    interval = float(sys.argv[sys.argv.index("--interval") + 1]) if "--interval" in sys.argv else 0.5
    end = time.time() + minutes * 60
    g_peaks, c_peaks = [], []
    last_cpu_t = 0.0
    t0 = time.time()
    print(f"[probe] 采样 {minutes:.0f} 分钟（GPU 每 {interval:g}s 一次，CPU 每 5s 一次）…（此期间不跑训练）", flush=True)
    while time.time() < end:
        g = gpu_temp()
        if g is not None:
            g_peaks.append(g)
        now = time.time()
        if now - last_cpu_t >= 5.0:
            c = cpu_util()
            if c is not None:
                c_peaks.append(c)
            last_cpu_t = now
            print(f"  {now - t0:.0f}s: GPU={g if g is not None else '?'}°C  CPU util={c if c is not None else '?'}%", flush=True)
        time.sleep(interval)
    gm = max(g_peaks) if g_peaks else None
    cm = max(c_peaks) if c_peaks else None
    print("\n[probe] 结果：", flush=True)
    print(f"  GPU 峰值 {gm}°C（训练安全余量：峰值 <= 50 宽松 / <= 45 紧张 / 高则必须降载）", flush=True)
    print(f"  CPU 利用率峰值 {cm}%（训练安全余量：峰值 <= 60 宽松 / 高则必须限线程+降batch）", flush=True)
    verdict = "✅ 可训练（用 v2 温控参数）" if (gm is not None and gm <= 50) and (cm is None or cm <= 60) else "⚠️ 余量不足，必须降载（见交接文档第二节）"
    print(f"  判定：{verdict}", flush=True)

if __name__ == "__main__":
    main()
