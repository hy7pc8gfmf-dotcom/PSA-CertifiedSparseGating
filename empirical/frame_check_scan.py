# -*- coding: utf-8 -*-
"""
反射检查器系统扫描 v2（评审 9 补强，2026-08-21 会话 18）
================================================================
ground truth = Coq 语义的精确镜像（Python 大整数 + math.isqrt 精确 floor-sqrt，
  逐行对应 PSA_framework.v 的 FrameCheckInstance.frame_check_instance / 
  psa_guard_main.ml 的 frame_check_instance_int）；
exe = psa_guard.exe frame（OCaml int 63 位 + float-sqrt 近似）——对照用，
  分歧即量化「提取整数范围限制」（评审建议 Zarith 的依据）。
分类（checker = 大整数镜像）：
  pass —— 通过；TN —— 拒绝且精确行和 > 4/5（真负）；FN —— 拒绝且精确行和 ≤ 4/5（假阴性）
族：
  1) C-sparse（Python 生成）：C∈{2,3,4,5,6,8}，m∈{2..14}
  2) 几何奇带（E5'' 式）：[2^{k+1}−1]，m∈{2..10}
  3) C=2 全相位：前 m 个奇数，m∈{2..10}
  4) E1 随机 log-uniform（去重）：m∈{4,8,16,32,64,128}，seed∈{1337,42,7}
输出：测试数据/frame_check_scan.csv + 控制台分族统计。
用法：python frame_check_scan.py [--out ...]
"""
import argparse, math, os, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "psa_empirical"))
from psa_guard_ffi import frame_check_instance as exe_frame_check  # noqa: E402
from length_extrap import log_uniform_ladder  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
EMPIRE = os.path.join(os.path.dirname(HERE), "psa_empirical", "测试数据")

MU = 4.0 / 5.0
EPS = 1e-9

# ---------- Coq 语义精确镜像（大整数） ----------
def pair_ok_big(n1, n2):
    f = math.isqrt(n1 * n2)
    return f * f <= n1 * n2 and 0 < f

def row_sum_le_4_5_big(ladder, i):
    n = len(ladder)
    ni = ladder[i]
    num, den = 0, 1
    for j in range(n):
        if j == i:
            continue
        nj = ladder[j]
        n1, n2 = (nj, ni) if nj < ni else (ni, nj)
        f = math.isqrt(n1 * n2)
        pn = n1 * n2
        pd = 2 * (n2 - n1) * f
        num, den = num * pd + pn * den, den * pd
    return 5 * num <= 4 * den

def frame_check_bigint(ladder):
    """逐行镜像 psa_guard_main.ml::frame_check_instance_int（精确整数）。"""
    if any(ladder[i] >= ladder[i + 1] for i in range(len(ladder) - 1)):
        return False
    if any(v < 2 for v in ladder):
        return False
    for i in range(len(ladder)):
        for j in range(i + 1, len(ladder)):
            if not pair_ok_big(ladder[i], ladder[j]):
                return False
    for i in range(len(ladder)):
        if not row_sum_le_4_5_big(ladder, i):
            return False
    return True

# ---------- 数值精确行和（窗口 T = 末带） ----------
def exact_row_sum_max(lad):
    T = lad[-1]
    worst = 0.0
    for i in range(len(lad)):
        s = 0.0
        ni = lad[i]
        for j in range(len(lad)):
            if j == i:
                continue
            nj = lad[j]
            th = math.pi * (1.0 / ni - 1.0 / nj)
            d = math.sin(T * th) / math.sin(th) if abs(math.sin(th)) > 1e-15 else T
            s += abs(d) / T
        worst = max(worst, s)
    return worst

def build_families():
    fam = {}
    for C in (2, 3, 4, 5, 6, 8):
        for m in range(2, 15):
            lad, last = [], 3
            for _ in range(m):
                lad.append(last)
                last = max(last * C + 1, last + 2)
            fam.setdefault(f"C={C}-sparse", []).append(lad)
    for m in range(2, 11):
        fam.setdefault("几何奇带", []).append([2 ** (k + 1) - 1 for k in range(m)])
    for m in range(2, 11):
        fam.setdefault("C=2全相位", []).append(list(range(3, 512, 2))[:m])
    for m in (4, 8, 16, 32, 64, 128):
        for seed in (1337, 42, 7):
            lad = sorted(set(log_uniform_ladder(3, 511, m, seed)))
            if len(lad) >= 2:
                fam.setdefault("E1随机loguniform", []).append(lad)
    return fam

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default=os.path.join(EMPIRE, "frame_check_scan.csv"))
    args = ap.parse_args()

    fams = build_families()
    rows, exe_div, div_in_range, div_out_range, in_range_n, out_range_n = [], 0, 0, 0, 0, 0
    SAFE_NMAX = 2 ** 20
    for fname, lads in fams.items():
        for lad in lads:
            big = frame_check_bigint(lad)          # Coq 语义（ground truth）
            exe = exe_frame_check(lad)             # 提取 exe（对照）
            exact = exact_row_sum_max(lad)
            in_range = lad[-1] < SAFE_NMAX
            if in_range:
                in_range_n += 1
            else:
                out_range_n += 1
            if big != exe:
                exe_div += 1
                if in_range:
                    div_in_range += 1
                else:
                    div_out_range += 1
            if big:
                status = "pass"
            elif exact <= MU + EPS:
                status = "FN"
            else:
                status = "TN"
            rows.append((fname, lad, len(lad), big, exe, exact, status))

    print(f"{'族':<18}{'N':>5}{'通过':>6}{'拒绝':>6}{'FN':>5}{'TN':>5}"
          f"{'通过率':>8}{'FN率(占全)':>10}{'FN率(占拒)':>10}")
    agg = {}
    for fname, lad, nb, big, exe, exact, status in rows:
        a = agg.setdefault(fname, [0, 0, 0, 0])
        a[0] += 1
        if big:
            a[1] += 1
        else:
            a[2] += 1
            if status == "FN":
                a[3] += 1
    for fname, (n, p, r, fn) in sorted(agg.items()):
        print(f"{fname:<18}{n:>5}{p:>6}{r:>6}{fn:>5}{r - fn:>5}"
              f"{p / n * 100:>7.1f}%{fn / n * 100:>9.1f}%{fn / r * 100 if r else 0:>9.1f}%")
    N = len(rows)
    P = sum(1 for r in rows if r[3])
    FN = sum(1 for r in rows if r[6] == "FN")
    TN = sum(1 for r in rows if r[6] == "TN")
    print(f"\n总计：N={N}，通过 {P}（{P / N * 100:.1f}%），拒绝 {N - P}"
          f"（真负 {TN}，假阴性 {FN}）——FN 占全量 {FN / N * 100:.2f}%，占拒绝 {FN / max(N - P, 1) * 100:.1f}%")
    print(f"exe（OCaml int）与 Coq 语义分歧：{exe_div} 个（{exe_div / N * 100:.1f}%）"
          f"——其中安全范围内（末带 < 2^20）{in_range_n} 个分歧 {div_in_range}（{div_in_range / max(in_range_n, 1) * 100:.1f}%）；"
          f"范围外 {out_range_n} 个分歧 {div_out_range}（{div_out_range / max(out_range_n, 1) * 100:.1f}%）")

    print("\n论文代表样本复核（大整数 = Coq 语义）：")
    for name, lad in (("C=4 [3,13,53,213]", [3, 13, 53, 213]),
                      ("T8 核 [3,15,63,255]", [3, 15, 63, 255]),
                      ("E5'' 七带", [3, 7, 15, 31, 63, 127, 255]),
                      ("C=2 八带", list(range(3, 512, 2))[:8])):
        big = frame_check_bigint(lad)
        exe = exe_frame_check(lad)
        ex = exact_row_sum_max(lad)
        print(f"  {name:<22} Coq语义={str(big):<5} exe={str(exe):<5} 精确行和={ex:.4f}  "
              f"状态={'pass' if big else ('FN' if ex <= MU + EPS else 'TN')}")

    os.makedirs(os.path.dirname(args.out), exist_ok=True)
    with open(args.out, "w", encoding="utf-8") as f:
        f.write("family,n_bands,coq_checker,exe_checker,exact_rowsum_max,status,ladder\n")
        for fname, lad, nb, big, exe, exact, status in rows:
            f.write(f"{fname},{nb},{big},{exe},{exact:.6f},{status},\"{','.join(map(str, lad))}\"\n")
    print(f"\n扫描数据已写：{args.out}")

if __name__ == "__main__":
    main()
