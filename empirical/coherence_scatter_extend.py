# -*- coding: utf-8 -*-
"""
散点扩充（会话 18，2026-08-21）：E1 夜间三档模型并入 coherence_scatter.csv
================================================================================
基础 4 点（C=2 全相位 / C=3 / C=4 / E5'' 七带，3-seed 均值 ppl）保持不变；
新增 3 点（single-seed s1337，ppl 从 eval_*.txt 读取）：
  - psi-rand      ：psi 嵌入用 128 带 log-uniform [3,54613]（排序）梯子
  - psi-rope-rand ：psi-rope 旋转角梯子 = log-uniform [3,511]（未排序）≤512
  - psi-rope+rand ：psi-rope 旋转角梯子 = log-uniform [3,54613]（排序）≤512
用法：python coherence_scatter_extend.py [--T 512] [--Tood 4096]
输出：测试数据/coherence_scatter.csv（全量重写）+ 控制台 R²。
"""
import argparse, math, os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from length_extrap import log_uniform_ladder  # noqa: E402

DATA = os.path.join(HERE, "测试数据")

# ---------- 与 coherence_analysis.py 相同的相干指标 ----------
def psi_inner(na, nb, T):
    d = 1.0 / na - 1.0 / nb
    if abs(d) < 1e-12:
        return T / math.sqrt(na * nb)
    theta = 2 * math.pi * d
    s = math.sin(T * theta / 2) / math.sin(theta / 2)
    return s / math.sqrt(na * nb)

def psi_norm(n, T):
    return math.sqrt(T / n)

def coherence(ladder, T):
    best = 0.0
    for i in range(len(ladder)):
        for j in range(i + 1, len(ladder)):
            ni, nj = ladder[i], ladder[j]
            c = abs(psi_inner(ni, nj, T)) / (psi_norm(ni, T) * psi_norm(nj, T))
            best = max(best, c)
    return best

# ---------- 从评估日志读取 ppl(4096) ----------
def ppl4096_from_log(name):
    p = os.path.join(DATA, name)
    if not os.path.exists(p):
        return None
    txt = open(p, encoding="utf-8").read()
    m = re.search(r"T=\s*4096:\s*loss [\d.\-]+\s+ppl ([\d.]+)", txt)
    return float(m.group(1)) if m else None

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--T", type=int, default=512)
    ap.add_argument("--Tood", type=int, default=4096)
    args = ap.parse_args()

    # 基础 4 点（与 coherence_analysis.py 相同：3-seed 均值 ppl）
    base_ladders = {
        "C=2 全相位": list(range(3, 512, 2))[:8],
        "C=3": [3, 10, 31, 94, 283],
        "C=4": [3, 13, 53, 213],
        "E5'' 七带": [3, 7, 15, 31, 63, 127, 255],
    }
    base_ppl = {"C=2 全相位": 13.84, "C=3": 22.86, "C=4": 12.75, "E5'' 七带": 12.40}

    # E1 夜间三档新点（single-seed s1337）
    rng_ladder = log_uniform_ladder(3, 54613, 128, 1337)            # 排序随机梯子
    rr_ladder = [n for n in log_uniform_ladder(3, 511, 128, 1337, sort=False) if n <= args.T]
    new_ladders = {
        "psi-rand(s1337)": rng_ladder,
        "psi-rope-rand(s1337)": rr_ladder,
        "psi-rope+rand(s1337)": [n for n in rng_ladder if n <= args.T],
    }
    new_logs = {
        "psi-rand(s1337)": "eval_psi_rand_1337.txt",
        "psi-rope-rand(s1337)": "eval_psi-rope_rr_1337.txt",
        "psi-rope+rand(s1337)": "eval_psi-rope_rand_1337.txt",
    }

    print(f"DeltaCoh 扩充：Coh({args.T}) → Coh({args.Tood})，Y = ppl({args.Tood})\n")
    print(f"{'梯子':<22}{'带数':>5}{'Coh(train)':>12}{'Coh(OOD)':>12}{'DeltaCoh':>10}{'ppl':>9}")
    rows = []
    for name, lad in base_ladders.items():
        c_in, c_ood = coherence(lad, args.T), coherence(lad, args.Tood)
        rows.append((name, c_in - c_ood, base_ppl[name], "3-seed 均值"))
        print(f"{name:<22}{len(lad):>5}{c_in:>12.4f}{c_ood:>12.4f}{c_in - c_ood:>10.4f}{base_ppl[name]:>9.2f}")
    for name, lad in new_ladders.items():
        c_in, c_ood = coherence(lad, args.T), coherence(lad, args.Tood)
        p = ppl4096_from_log(new_logs[name])
        rows.append((name, c_in - c_ood, p, "s1337"))
        print(f"{name:<22}{len(lad):>5}{c_in:>12.4f}{c_ood:>12.4f}{c_in - c_ood:>10.4f}"
              f"{(f'{p:.2f}' if p is not None else '—'):>9}")

    with open(os.path.join(DATA, "coherence_scatter.csv"), "w", encoding="utf-8") as f:
        f.write("ladder,delta_coh,ppl4096,seed_status\n")
        for name, dc, p, st in rows:
            if p is not None:
                f.write(f"{name},{dc:.6f},{p:.4f},{st}\n")

    pts = [(dc, p) for _, dc, p, _ in rows if p is not None]
    xs = [p[0] for p in pts]; ys = [p[1] for p in pts]
    n = len(pts)
    mx, my = sum(xs) / n, sum(ys) / n
    cov = sum((x - mx) * (y - my) for x, y in pts)
    vx = sum((x - mx) ** 2 for x in xs); vy = sum((y - my) ** 2 for y in ys)
    r2 = cov * cov / (vx * vy) if vx * vy > 0 else float('nan')
    print(f"\n可用点 {n} 个：Pearson R^2 = {r2:.3f}")
    if n >= 4:
        rho = cov / math.sqrt(vx * vy)
        print(f"Pearson r = {rho:.3f}（正 = ΔCoh 越大 ppl 越差）")

if __name__ == "__main__":
    main()
