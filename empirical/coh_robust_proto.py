# -*- coding: utf-8 -*-
"""
ΔCoh 鲁棒指标原型（会话 18 讨论用，2026-08-21）
=================================================
在 7 点上评测替代聚合器，看哪个能救回「相干结构突变 → ppl(4096)」预测：
  max（原版） / dedup-max / mean / RMS / median / 第二大 / λ_max(Gram) / F_τ 计数 / 有效秩
每指标算 Δ = m(512) − m(4096)，对 ppl(4096) 做 Pearson R²（全 7 点 + 族内 4 点）。
纯 CPU 数学，无 GPU。
用法：python coh_robust_proto.py
"""
import math, os, sys
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from length_extrap import log_uniform_ladder

def psi_inner(na, nb, T):
    d = 1.0 / na - 1.0 / nb
    if abs(d) < 1e-12:
        return T / math.sqrt(na * nb)
    th = 2 * math.pi * d
    return math.sin(T * th / 2) / math.sin(th / 2) / math.sqrt(na * nb)

def gram(lad, T):
    """归一化 Gram（相关性矩阵）：G_ii=1，G_ij = |⟨ψ_i,ψ_j⟩_T|/(‖ψ_i‖_T·‖ψ_j‖_T) = |Dirichlet|/T。
    psi_inner 已含 1/√(ni·nj)，除以 ‖ψ_i‖‖ψ_j‖ = T/√(ni·nj) ⟹ G_ij = psi_inner·√(ni·nj)/T。"""
    n = len(lad)
    G = np.zeros((n, n))
    for i in range(n):
        for j in range(i, n):
            v = psi_inner(lad[i], lad[j], T) * math.sqrt(lad[i] * lad[j]) / T
            G[i, j] = G[j, i] = 1.0 if i == j else v
    return G

def metrics(lad, T):
    """返回 (max, dedup_max, mean, rms, median, second_max, lam_max, f05, effrank, diag_min)。"""
    n = len(lad)
    G = gram(lad, T)
    off = np.abs(G[np.triu_indices(n, 1)])
    if off.size == 0:
        off = np.array([0.0])
    m_max = float(off.max())
    # 去重后第二大/去重 max：排除相同带（相干 = 对角比 1 小的同带对其实不存在；同带对 = 1）
    off_dedup = off[off < 1.0 - 1e-9]
    m_dedup_max = float(off_dedup.max()) if off_dedup.size else 0.0
    m_mean = float(off.mean())
    m_rms = float(math.sqrt((off ** 2).mean()))
    m_med = float(np.median(off))
    m_second = float(np.sort(off)[-2]) if off.size >= 2 else m_max
    ev = np.linalg.eigvalsh((G + G.T) / 2)
    m_lam = float(ev.max())
    m_f05 = float((off > 0.5).mean())
    m_effrank = float((ev > 0.01 * m_lam).sum()) if m_lam > 0 else 0.0
    m_diagmin = float(np.diag(G).min())
    return (m_max, m_dedup_max, m_mean, m_rms, m_med, m_second, m_lam, m_f05, m_effrank, m_diagmin)

NAMES = ["max(原版)", "dedup-max", "mean", "RMS", "median", "第二大", "λ_max", "F_0.5", "有效秩", "最小对角"]

def main():
    ladders = {
        "C=2 全相位": list(range(3, 512, 2))[:8],
        "C=3": [3, 10, 31, 94, 283],
        "C=4": [3, 13, 53, 213],
        "E5'' 七带": [3, 7, 15, 31, 63, 127, 255],
        "psi-rand(s1337)": log_uniform_ladder(3, 54613, 128, 1337),
        "psi-rope-rand(s1337)": [n for n in log_uniform_ladder(3, 511, 128, 1337, sort=False) if n <= 512],
        "psi-rope+rand(s1337)": [n for n in log_uniform_ladder(3, 54613, 128, 1337) if n <= 512],
    }
    ppl = {"C=2 全相位": 13.84, "C=3": 22.86, "C=4": 12.75, "E5'' 七带": 12.40,
           "psi-rand(s1337)": 35.95, "psi-rope-rand(s1337)": 7.29, "psi-rope+rand(s1337)": 9.82}

    print(f"{'指标':<10}" + "".join(f"{k:>10}" for k in ladders))
    deltas = {name: {} for name in NAMES}
    for k, lad in ladders.items():
        m512 = metrics(lad, 512)
        m4096 = metrics(lad, 4096)
        for i, name in enumerate(NAMES):
            deltas[name][k] = m512[i] - m4096[i]
        print(f"{'Δ:' + k:<12}" + "".join(f"{m512[i]-m4096[i]:>10.4f}" for i in range(len(NAMES))))

    print("\n===== Δ指标 vs ppl(4096)：Pearson R²（全 7 点；括号内为稀疏几何族 4 点）=====")
    keys_all = list(ladders)
    keys_sparse = ["C=2 全相位", "C=3", "C=4", "E5'' 七带"]
    for i, name in enumerate(NAMES):
        row = []
        for keys in (keys_all, keys_sparse):
            xs = [deltas[name][k] for k in keys]
            ys = [ppl[k] for k in keys]
            mx, my = sum(xs) / len(xs), sum(ys) / len(ys)
            cov = sum((x - mx) * (y - my) for x, y in zip(xs, ys))
            vx = sum((x - mx) ** 2 for x in xs); vy = sum((y - my) ** 2 for y in ys)
            r2 = cov * cov / (vx * vy) if vx * vy > 0 else float('nan')
            r = cov / math.sqrt(vx * vy) if vx * vy > 0 else float('nan')
            row.append(f"{r2:6.3f}(r={r:+.2f})")
        print(f"{name:<10} 7点 {row[0]}   4点 {row[1]}")

if __name__ == "__main__":
    main()
