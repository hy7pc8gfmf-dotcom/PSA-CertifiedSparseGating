# -*- coding: utf-8 -*-
"""
rope-NTK per-seed 统计（评审 B6 闸门，2026-08-21 会话 18）
================================================================
输入：
  rope-NTK @4096 三 seed（b32 重训 + eval-only --rope-variant ntk 的 ppl4096）
  psi-rope-rand @4096 三 seed（b32：6.44/6.49/6.42，ms_rr_*.txt）
  C=4 psi-rope @4096 三 seed（b32 主表：13.06/12.82/12.38）
  （可选）E5'' 七带 @4096 三 seed（12.87/12.77/11.55）
输出：Welch t / df / p（双尾）/ Cohen's d 对比表。
用法：python ntk_stats.py --rope-ntk 10.5,11.0,10.2 [--out ...]
"""
import argparse, math
from scipy import stats

RR = [6.44, 6.49, 6.42]        # psi-rope-rand b32 三 seed（已确认，会话 18）
C4 = [13.06, 12.82, 12.38]     # C=4 psi-rope b32 三 seed（multi_seed_main_table.md）
E5 = [12.87, 12.77, 11.55]     # E5'' 七带 b32 三 seed（multi_seed_main_table.md）

def welch(a, b, name_a, name_b):
    a, b = list(a), list(b)
    na, nb = len(a), len(b)
    ma, mb = sum(a) / na, sum(b) / nb
    sa = (sum((x - ma) ** 2 for x in a) / (na - 1)) ** 0.5
    sb = (sum((x - mb) ** 2 for x in b) / (nb - 1)) ** 0.5
    t = (ma - mb) / math.sqrt(sa * sa / na + sb * sb / nb)
    df = (sa * sa / na + sb * sb / nb) ** 2 / (
        (sa * sa / na) ** 2 / (na - 1) + (sb * sb / nb) ** 2 / (nb - 1))
    p = 2 * stats.t.sf(abs(t), df)
    sp = math.sqrt(((na - 1) * sa * sa + (nb - 1) * sb * sb) / (na + nb - 2))
    d = (ma - mb) / sp if sp > 0 else float('nan')
    print(f"{name_a:<20} vs {name_b:<22} Δ={ma - mb:+7.2f}  "
          f"t={t:6.2f}  df={df:4.1f}  p={p:.4f}  Cohen's d={d:+6.2f}")
    return t, df, p, d

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--rope-ntk", required=True,
                    help="rope-NTK @4096 三 seed ppl，逗号分隔（如 10.5,11.0,10.2）")
    args = ap.parse_args()
    ntk = [float(x) for x in args.rope_ntk.split(",")]
    assert len(ntk) == 3, "rope-NTK 需 3 个值"

    print(f"样本：psi-rope-rand {RR}  mean {sum(RR)/3:.2f}±{(sum((x-sum(RR)/3)**2 for x in RR)/2)**0.5:.2f}")
    print(f"      C=4 psi-rope {C4}  mean {sum(C4)/3:.2f}±{(sum((x-sum(C4)/3)**2 for x in C4)/2)**0.5:.2f}")
    print(f"      E5'' 七带     {E5}  mean {sum(E5)/3:.2f}±{(sum((x-sum(E5)/3)**2 for x in E5)/2)**0.5:.2f}")
    print(f"      rope-NTK      {ntk}  mean {sum(ntk)/3:.2f}±{(sum((x-sum(ntk)/3)**2 for x in ntk)/2)**0.5:.2f}\n")
    print("===== Welch t（双尾）+ Cohen's d（@4096）=====")
    welch(RR, ntk, "psi-rope-rand", "rope-NTK")
    welch(RR, C4, "psi-rope-rand", "C=4 psi-rope")
    welch(RR, E5, "psi-rope-rand", "E5'' 七带")
    welch(C4, ntk, "C=4 psi-rope", "rope-NTK")
    print("\n注：n=3 时 df 极小、检验力低——p 仅供趋势参考（B6 闸门如实报告）；"
          "若 p<0.05 且 d 绝对值 >0.8 视为强效应，否则声明趋势级。")

if __name__ == "__main__":
    main()
