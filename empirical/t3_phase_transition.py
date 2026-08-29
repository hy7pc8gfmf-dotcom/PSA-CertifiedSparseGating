# -*- coding: utf-8 -*-
"""
T3b 理论相变点精确数值计算 + 波长分布检查
========================================
目标：用强逻辑锁定 N* 真身的候选——「框架紧相变点」（理论侧），与实验最优区 [352,448] 对照。

方法（T3b）：
- 带集 F = log_uniform_ladder(3, 511, 128, 1337)（与实验同 seed）
- 窗内 Gram：G_T(n,m) = Σ_{k=0}^{T-1} exp(2πik(1/n − 1/m))（Dirichlet 核闭式）
- 归一化行和 μ(n) := Σ_{m≠n} |G_T(n,m)| / T（gershgorin 框架 μ 的离散版）
- 相变点：μ(n) 首次 ≤ 4/5 的临界 n₀（框架可证紧 ⟹ 结构带起点）
- 输出：c₀ = T/n₀，与实验 N*(≈352-448, c*≈1.14-1.45, 384→4/3) 对照

辅助输出：
- 波长集分布（[352,448] 内波长数——判断加密裁剪点是否有意义）
- 裁剪点 N 的「保留带集框架 μ」：μ_crop(N) = max_{n≤N} μ_restricted(n)（裁剪后是否可证紧）
"""
import math

T = 512
FULL = 511

def log_uniform_ladder(lo, hi, m, seed, sort=False):
    import random
    rng = random.Random(seed)
    log_vals = [rng.uniform(math.log(lo), math.log(hi)) for _ in range(m)]
    vals = [int(round(math.exp(v))) for v in log_vals]
    return sorted(vals) if sort else vals

def dirichlet_T(n, m, T):
    """|Σ_{k=0}^{T-1} exp(2πik(1/n − 1/m))| = |sin(πT·δ)|/|sin(π·δ)|，δ = 1/n − 1/m。"""
    delta = 1.0 / n - 1.0 / m
    if delta == 0.0:
        return float(T)
    num = math.sin(math.pi * T * delta)
    den = math.sin(math.pi * delta)
    if abs(den) < 1e-15:
        return float(T)  # 精确共振
    return abs(num / den)

def mu_of_n(F, n, T):
    """带 n 在带集 F 中的归一化窗内行和（gershgorin μ）。"""
    return sum(dirichlet_T(n, m, T) for m in F if m != n) / T

def main():
    F = [n for n in log_uniform_ladder(3, 511, 128, 1337, sort=False) if n <= 512]
    F = sorted(set(F))
    print(f"带集 F：{len(F)} 个波长（log-uniform [3,511] seed=1337）")
    print(f"波长分布：<=256: {sum(1 for n in F if n<=256)}，256-352: {sum(1 for n in F if 256<n<=352)}，"
          f"352-448: {sum(1 for n in F if 352<n<=448)}，448-511: {sum(1 for n in F if 448<n<=511)}")
    in_region = [n for n in F if 352 <= n <= 448]
    print(f"[352,448] 内波长：{in_region}")
    print()

    # T3b：每个带的 μ(n)，找首次 ≤ 4/5 的临界点
    print("===== T3b 理论相变点（μ(n) = 4/5）=====")
    mus = [(n, mu_of_n(F, n, T)) for n in F]
    mus_sorted = sorted(mus, key=lambda x: x[1])
    print(f"{'n':>6} {'c(n)=T/n':>10} {'μ(n)':>10} {'可证紧(μ≤0.8)?':>16}")
    for n, mu in mus_sorted:
        flag = "✓" if mu <= 0.8 else ""
        print(f"{n:>6} {T/n:>10.3f} {mu:>10.4f} {flag:>16}")

    # 首次 μ ≤ 4/5 的临界（从高 n 向低 n 扫：结构带 = μ 小的带）
    print("\n===== 相变判定 =====")
    tight = [(n, mu) for n, mu in mus_sorted if mu <= 0.8]
    loose = [(n, mu) for n, mu in mus_sorted if mu > 0.8]
    if tight:
        n0 = max(n for n, _ in tight)
        mu0 = dict(mus)[n0]
        print(f"框架可证紧的最大带：n₀ = {n0}（c₀ = T/n₀ = {T/n0:.3f}，μ = {mu0:.4f} ≤ 0.8）")
        print(f"⟹ 理论预测 N* ≥ {n0}（保留 n ≤ n0 均可证紧）；实验最优区 [352,448]")
        print(f"对照：4/3 → N = 384（c = 1.333）{'✓ 在理论可证紧区' if n0 <= 384 else '✗ 理论临界高于实验'}")
    else:
        print("无带满足 μ ≤ 0.8（全部松框架）")
    if loose:
        n_loose = min(n for n, _ in loose)
        print(f"框架退化（μ > 0.8）的最小带：n = {n_loose}（c = {T/n_loose:.3f}）")

    # 裁剪点视角：保留 n ≤ N 后，带集的最大 μ（裁剪后是否整体可证紧）
    print("\n===== 裁剪点 N 的框架 μ（保留带集最大行和）=====")
    print(f"{'N':>6} {'保留带数':>8} {'max μ':>10} {'可证紧?':>10}")
    for N in (256, 320, 352, 384, 416, 448, 511):
        Fn = [n for n in F if n <= N]
        if not Fn:
            continue
        mu_max = max(mu_of_n(Fn, n, T) for n in Fn)
        flag = "✓" if mu_max <= 0.8 else "✗"
        print(f"{N:>6} {len(Fn):>8} {mu_max:>10.4f} {flag:>10}")

if __name__ == "__main__":
    main()
