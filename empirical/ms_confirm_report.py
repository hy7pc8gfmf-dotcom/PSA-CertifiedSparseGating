# -*- coding: utf-8 -*-
"""
multi-seed 确认报告（会话 18，2026-08-21）：psi-rope-rand / psi-rope+rand × {42,7,1337} batch 32
================================================================================================
读取 测试数据/ms_rr_s<seed>.txt 与 ms_rand_s<seed>.txt（length_extrap.py 训练自带评估输出），
提取每 T 的 ppl，输出：
  1) 三档 multi-seed 表（mean ± std），与 C=4 psi-rope b32 主表（multi_seed_main_table.md）对齐比较；
  2) batch 效应检查：s1337 在 b32 vs b64（7.29 / 9.82）的差异；
  3) @4096 判定：随机稠密旋转角 vs 几何 C=4 的三 seed 均值差 + 最小差。
用法：python ms_confirm_report.py
"""
import math, os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "测试数据")

def parse_ppl(path, T):
    """从训练日志提取指定 T 的 ppl（外推对比汇总表行：`  4096 | ...`）。"""
    if not os.path.exists(path):
        return None
    txt = open(path, encoding="utf-8").read()
    for line in txt.splitlines():
        if line.strip().startswith(f"{T} |"):
            cells = [c.strip() for c in line.split("|")[1:]]
            vals = []
            for c in cells:
                try:
                    vals.append(float(c))
                except ValueError:
                    pass
            return vals[0] if vals else None
    # 回退：逐行 T= 输出
    m = re.search(rf"T=\s*{T}:\s*loss [\d.\-]+\s+ppl ([\d.]+)", txt)
    return float(m.group(1)) if m else None

def table(name, prefix, seeds, Tlist=(512, 1024, 2048, 4096)):
    rows = {}
    for s in seeds:
        path = os.path.join(DATA, f"{prefix}_s{s}.txt")
        rows[s] = {T: parse_ppl(path, T) for T in Tlist}
    print(f"===== {name}（batch 32，seeds {seeds}）=====")
    print(f"{'T':>6} | " + " | ".join(f"s{s:>6}" for s in seeds) + f" | {'mean':>8} | {'stdev':>8}")
    means = {}
    for T in Tlist:
        vals = [rows[s][T] for s in seeds if rows[s][T] is not None]
        if not vals:
            continue
        m = sum(vals) / len(vals)
        sd = (sum((v - m) ** 2 for v in vals) / len(vals)) ** 0.5
        means[T] = m
        print(f"{T:>6} | " + " | ".join(f"{rows[s][T]:>8.2f}" if rows[s][T] else f"{'—':>8}" for s in seeds)
              + f" | {m:>8.2f} | {sd:>8.2f}")
    return means

def main():
    seeds = [42, 7, 1337]
    rr = table("psi-rope-rand（随机旋转 [3,511]）", "ms_rr", seeds)
    ra = table("psi-rope+rand（排序随机旋转 ≤512）", "ms_rand", seeds)

    # 主表 C=4 psi-rope b32（multi_seed_main_table.md）@4096 三 seed 均值
    c4 = {512: 4.70, 1024: 5.64, 2048: 8.42, 4096: 12.75}  # mean of s1337/s42/s7
    print("\n===== @4096 判定（vs 几何 C=4 b32 主表均值 12.75）=====")
    for name, m in (("psi-rope-rand", rr), ("psi-rope+rand", ra)):
        if 4096 in m:
            diff = m[4096] - c4[4096]
            print(f"{name:<16} mean {m[4096]:.2f}  vs C=4 {c4[4096]:.2f}  Δ {diff:+.2f}  "
                  f"({-diff / c4[4096] * 100:+.1f}%)")
    # batch 效应（s1337：b64 7.29 / 9.82 vs b32 本次）
    print("\n===== batch 效应（s1337 @4096：b64 vs b32）=====")
    b64 = {"psi-rope-rand": 7.29, "psi-rope+rand": 9.82}
    for name, m in (("psi-rope-rand", rr), ("psi-rope+rand", ra)):
        if 4096 in m:
            print(f"{name:<16} b64 {b64[name]:.2f}  b32 {m[4096]:.2f}  Δ {m[4096] - b64[name]:+.2f}")

if __name__ == "__main__":
    main()
