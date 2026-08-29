# -*- coding: utf-8 -*-
"""
带间相干衰减率分析 v2（会话 18，指标族扩展）
================================================================
指标（Δ = m(T_train) − m(T_ood)，m 为下列聚合器之一）：
  max      原版：max_{i<j} |G_ij|          （4 点 R²=0.982 → 7 点 0.012，重复带退化）
  dedup    max（排除 |G_ij| ≥ 1−1e-9 的重复带对）
  mean     全对均值                       （7 点 R²≈0.53）
  rms      全对均方根                     （7 点 R²≈0.40，稀疏族内 0.985）
  median   全对中位数                     （7 点 R²≈0.69）
  second   第二大 |G_ij|
  lam      λ_max(归一化 Gram)             （谱范数，Gershgorin/框架界同源）
  f05      相干 >0.5 的带对占比
  effrank  #特征值 > 0.01·λ_max（有效秩；OOD 崩塌是嵌入族定性信号）
G_ij = |⟨ψ_i,ψ_j⟩_T|/(‖ψ_i‖_T·‖ψ_j‖_T) = |Dirichlet(2π(1/n_i−1/n_j))|/T。

数据点：基础 4 稀疏几何梯子（3-seed 均值 ppl）+ E1 消融点（ppl 读 eval_*.txt /
ms_*.txt，梯子按 seed 用 length_extrap.log_uniform_ladder 确定性重建）。

用法：
  python coherence_analysis.py              # 原版行为（--metric max → coherence_scatter.csv）
  python coherence_analysis.py --metric all # 全指标族 → coherence_scatter_full.csv + 逐指标 R²
  python coherence_analysis.py --metric mean
"""
import argparse, math, os, re, sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from length_extrap import log_uniform_ladder  # noqa: E402

DATA = os.path.join(HERE, "测试数据")

# ---------- 相干指标族 ----------
def psi_inner(na, nb, T):
    d = 1.0 / na - 1.0 / nb
    if abs(d) < 1e-12:
        return T / math.sqrt(na * nb)
    th = 2 * math.pi * d
    return math.sin(T * th / 2) / math.sin(th / 2) / math.sqrt(na * nb)

def gram(lad, T):
    """归一化 Gram：G_ii=1，G_ij=|⟨ψ_i,ψ_j⟩_T|/(‖ψ_i‖_T·‖ψ_j‖_T)（带符号）。"""
    n = len(lad)
    G = np.zeros((n, n))
    for i in range(n):
        for j in range(i, n):
            v = psi_inner(lad[i], lad[j], T) * math.sqrt(lad[i] * lad[j]) / T
            G[i, j] = G[j, i] = 1.0 if i == j else v
    return G

def metric_values(lad, T):
    n = len(lad)
    G = gram(lad, T)
    off = np.abs(G[np.triu_indices(n, 1)])
    if off.size == 0:
        off = np.array([0.0])
    m_max = float(off.max())
    off_dedup = off[off < 1.0 - 1e-9]
    m_dedup = float(off_dedup.max()) if off_dedup.size else 0.0
    m_mean = float(off.mean())
    m_rms = float(math.sqrt((off ** 2).mean()))
    m_med = float(np.median(off))
    m_second = float(np.sort(off)[-2]) if off.size >= 2 else m_max
    ev = np.linalg.eigvalsh((G + G.T) / 2)
    m_lam = float(ev.max())
    m_f05 = float((off > 0.5).mean())
    m_rank = float((ev > 0.01 * m_lam).sum()) if m_lam > 0 else 0.0
    return dict(max=m_max, dedup=m_dedup, mean=m_mean, rms=m_rms, median=m_med,
                second=m_second, lam=m_lam, f05=m_f05, effrank=m_rank)

METRICS = ["max", "dedup", "mean", "rms", "median", "second", "lam", "f05", "effrank"]

# ---------- 数据点 ----------
def ppl_from_log(path):
    """从训练/评估日志读 ppl(4096)：优先外推汇总表行，回退逐 T 行。"""
    if not os.path.exists(path):
        return None
    txt = open(path, encoding="utf-8").read()
    for line in txt.splitlines():
        if line.strip().startswith("4096 |"):
            cells = [c.strip() for c in line.split("|")[1:]]
            for c in cells:
                try:
                    return float(c)
                except ValueError:
                    pass
    m = re.search(r"T=\s*4096:\s*loss [\d.\-]+\s+ppl ([\d.]+)", txt)
    return float(m.group(1)) if m else None

def build_points(T):
    """返回 [(name, ladder, ppl4096, status)]——日志存在才纳入。"""
    pts = []
    base = {
        "C=2 全相位": (list(range(3, 512, 2))[:8], 13.84),
        "C=3": ([3, 10, 31, 94, 283], 22.86),
        "C=4": ([3, 13, 53, 213], 12.75),
        "E5'' 七带": ([3, 7, 15, 31, 63, 127, 255], 12.40),
    }
    for name, (lad, ppl) in base.items():
        pts.append((name, lad, ppl, "3-seed 均值"))
    # E1 消融点（单 seed；梯子按 seed 确定性重建）
    e1 = [
        ("psi-rand(s1337)", lambda s: log_uniform_ladder(3, 54613, 128, s), 1337,
         os.path.join(DATA, "eval_psi_rand_1337.txt")),
        ("psi-rope-rand(s1337)", lambda s: [n for n in log_uniform_ladder(3, 511, 128, s, sort=False) if n <= T], 1337,
         os.path.join(DATA, "eval_psi-rope_rr_1337.txt")),
        ("psi-rope+rand(s1337)", lambda s: [n for n in log_uniform_ladder(3, 54613, 128, s) if n <= T], 1337,
         os.path.join(DATA, "eval_psi-rope_rand_1337.txt")),
    ]
    for name, fn, seed, log in e1:
        ppl = ppl_from_log(log)
        if ppl is not None:
            pts.append((name, fn(seed), ppl, f"s{seed}"))
    # multi-seed 确认点（batch 32；日志 ms_*.txt 存在即纳入）
    ms = [
        ("psi-rope-rand", lambda s: [n for n in log_uniform_ladder(3, 511, 128, s, sort=False) if n <= T],
         "ms_rr_s{seed}.txt", (42, 7, 1337)),
        ("psi-rope+rand", lambda s: [n for n in log_uniform_ladder(3, 54613, 128, s) if n <= T],
         "ms_rand_s{seed}.txt", (42, 7, 1337)),
    ]
    for name, fn, fmt, seeds in ms:
        for seed in seeds:
            log = os.path.join(DATA, fmt.format(seed=seed))
            ppl = ppl_from_log(log)
            if ppl is not None:
                pts.append((f"{name}(s{seed})", fn(seed), ppl, f"s{seed}"))
    return pts

def pearson_r2(xs, ys):
    n = len(xs)
    mx, my = sum(xs) / n, sum(ys) / n
    cov = sum((x - mx) * (y - my) for x, y in zip(xs, ys))
    vx = sum((x - mx) ** 2 for x in xs); vy = sum((y - my) ** 2 for y in ys)
    if vx * vy <= 0:
        return float('nan'), float('nan')
    r = cov / math.sqrt(vx * vy)
    return r * r, r

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--T", type=int, default=512)
    ap.add_argument("--Tood", type=int, default=4096)
    ap.add_argument("--metric", type=str, default="max", choices=METRICS + ["all"])
    args = ap.parse_args()

    pts = build_points(args.T)
    print(f"相干衰减指标族分析：Δ{args.metric if args.metric != 'all' else '(all)'} = m({args.T})−m({args.Tood})，"
          f"Y = ppl({args.Tood})，数据点 {len(pts)}\n")
    header = f"{'梯子':<22}{'带数':>5}"
    for m in (METRICS if args.metric == "all" else [args.metric]):
        header += f"{'Δ' + m:>11}"
    header += f"{'ppl':>9}"
    print(header)
    rows = []
    for name, lad, ppl, status in pts:
        mv = metric_values(lad, args.T)
        mv_ood = metric_values(lad, args.Tood)
        delta = {m: mv[m] - mv_ood[m] for m in METRICS}
        rows.append((name, len(lad), delta, ppl, status))
        line = f"{name:<22}{len(lad):>5}"
        for m in (METRICS if args.metric == "all" else [args.metric]):
            line += f"{delta[m]:>11.4f}"
        line += f"{ppl:>9.2f}"
        print(line)

    out_metric = METRICS if args.metric == "all" else [args.metric]
    out_csv = os.path.join(DATA, "coherence_scatter_full.csv" if args.metric == "all" else "coherence_scatter.csv")
    with open(out_csv, "w", encoding="utf-8") as f:
        f.write("ladder," + ",".join("d" + m for m in out_metric) + ",ppl4096,seed_status\n")
        for name, nbands, delta, ppl, status in rows:
            f.write(name + "," + ",".join(f"{delta[m]:.6f}" for m in out_metric)
                    + f",{ppl:.4f},{status}\n")
    print(f"\n散点数据已写：{os.path.basename(out_csv)}")

    print("\n===== 逐指标 R²（Δ vs ppl；全点 | 稀疏几何族 4 点）=====")
    keys_sparse = {"C=2 全相位", "C=3", "C=4", "E5'' 七带"}
    for m in METRICS:
        xs_all, ys_all = [], []
        xs_sp, ys_sp = [], []
        for name, nbands, delta, ppl, status in rows:
            xs_all.append(delta[m]); ys_all.append(ppl)
            if name in keys_sparse:
                xs_sp.append(delta[m]); ys_sp.append(ppl)
        r2a, ra = pearson_r2(xs_all, ys_all)
        r2s, rs = pearson_r2(xs_sp, ys_sp)
        print(f"{m:<8} R²(全)={r2a:6.3f} r={ra:+5.2f}   R²(稀疏族)={r2s:6.3f} r={rs:+5.2f}")

if __name__ == "__main__":
    main()
