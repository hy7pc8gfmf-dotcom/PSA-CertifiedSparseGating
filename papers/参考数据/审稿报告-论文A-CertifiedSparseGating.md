# 审稿报告 · 论文 A — Certified Sparse Gating（CPP/ITP）

> 对照代码：`D:\ComplexAnalysis\ConstructiveWorld\30模块`（合并版 `ca_merged_full_25.v` + `PSA_framework.v` + `ca_*` + `probe_*.v`）
> 审稿口径：逐行声明 ↔ 代码实测；数值双方法独立复核；诚信纪律与工件完备性。

## 总体结论
论文 A 的形式化工程**扎实、诚实、可证**。所有核心证书常数经本文独立双方法复核**全部通过**；"零 Admitted / 零 Abort / 42 处 `Require Import Stdlib.Logic.Classical` 全在 `ca_*` 基础设施、`PSA_framework.v` 内为 0"**经结构扫描确认成立**，且 `PSA_audit.v` 已补交、其 165 个审计目标定理**165/165 存在于合并版**。主要风险在两点：(1) **"应用层零 classic / 165 项全部零 classic" 声明 post-M1.5 静态核验支持成立**——`PSA_audit.v` L108–121（2026-08-19 勘误）记载的 4 项注意力链继承 `Classical_Prop.classic` 为 **pre-M1.5 过时状态**；当前 `ca_merged_full_25.v` 已并入 `ExpSeries.exp_mono_le_noclassic`（L63579/L63672/L63719），4 个注意力定理位于其后，`exp_increasing` 实际仅存于 `ca_*` 基础设施（非审计目标）；(2) **工件可复现性**——现有 `audit_run.txt` 仅捕获 55/165 定理块且未随稿 co-locate，须补完整 165 项日志 + 构建配置（P1）；个别计数/版本引用精确性。

---

## A-1 声明 ↔ 代码核验（逐项）

| # | 论文声明（位置） | 代码实测 | 判定 |
|---|---|---|---|
| 1 | 合并版 87733 行 / 55 模块（§2） | 87733 行 / **57** 顶层 Module | 行数✓；模块数差 2（P3） |
| 2 | `PSA_framework.v` 6659 行 / 18 Module / 269 Lemma·Theorem / 0 Admitted（§2, L133） | 6659 / 18 / **316** 顶层声明 / **272** Qed / 0 Admitted | 行/模块/Admitted✓；269 为 Lemma+Theorem 口径，与 272 Qed 一致（P3 注明口径） |
| 3 | C=4 μ=4/5，框架界 [1/5,9/5]（§3, §4.1） | 真值行和 μ=0.312072；6 对有理界全保守；[1/5,9/5] 成立 | ✓ 双方法通过 |
| 4 | 可判定性溢价 2.55（§5, L306） | 0.7965625/0.3120723=2.5525（或 0.8/0.312=2.5635） | ✓ |
| 5 | `champion_e5_composite_certificate`：(S−coh_e5)≤‖F‖²≤(S+coh_e5)，coh_e5=14.21，下界−7.21（§4.3） | `delta_e5` 21 对全保守；2·Σδ=14.2119；S=7⇒−7.2119 | ✓ 双方法通过 |
| 6 | 反射检查器判 E5'' `false` 为真阴性（§4.3, §5） | E5'' 真值行和=1.228720>0.8 | ✓ |
| 7 | T8 核 [3,15,63,255] μ=4/5 可认证（§4.2） | 真值行和=0.2994<0.8 | ✓ |
| 8 | M4 [3,7,15] 溢价 5/3（§5） | 真值行和 0.787043；63/80≥真值；21/16÷63/80=1.6667 | ✓ |
| 9 | `M_bound_2d_wide 4=768` / `3d=3968` / `4d=19968`（§7） | 三处 `Lemma ..._C4_value` 实测一致 | ✓ |
| 10 | 3D K0′=Rmax·8C³/2 常数级勘误（§2） | `ca_basis_3d.v` 含该常数 | ✓ |
| 11 | 165 项 Print Assumptions，RC=0，零 `Classical_Prop.classic`（§11） | `PSA_audit.v` **已补交**（229 行，165 命令）；165 目标 **165/165 在合并版存在**；文件 L108–121 勘误（pre-M1.5 过时）记载 4 项经 exp Rpower/MVT 路线继承 classic，但 **post-M1.5 已消除**：`ca_merged_full_25.v` L63579 `Module ExpSeries`/L63672 `exp_mono_le_noclassic` 已并入，4 个注意力定理（L63937/63852/63910/64137）位于其后，`exp_increasing` 仅存于 `ca_*` 基础设施；现有 `audit_run.txt` 55 个定理块全零 classic，但仅捕获 55/165 | ✓ **post-M1.5 静态核验支持 165/165 零 `Classical_Prop.classic`**；完整审计日志须补（P1） |
| 12 | 42 处 `Require Import Classical` 全在 `ca_*` 基础设施（§11） | 实测 42 处 `Require Import Stdlib.Logic.Classical`，全在 `ca_*`（含合并内 21）；`PSA_framework.v`=0 | ✓ 声称准确 |
| 13 | `unitary_invariance_psi_rope_theta`、`frame_check_instance_sound`、`pareto_law_main` 等已 Qed | 合并版 grep 全部命中 | ✓ |
| 14 | `golden_near_collision_gold` 零公理（§8） | 位于 `probe_nearcoll.v`（z 探针，未并入合并版） | ✓ 但附录 A 未列该文件名（P3） |

---

## A-2 数学正确性与新颖性自评
- 论文 A §1 自述"核心定理为经典结果的机器化，数学新颖性有限，价值在可判定/可提取/可审计"——**诚实且准确**。联网比对确认 Gershgorin/RIP/Welch/Donoho–Stark 均为标准结果。
- 构造性实数轨道（`ca_rip_cr.v` 33 定理、π/sin/sqrt 三角、`decidability_premium_cr`）走纯 ConstructiveReals、零经典公理——这是**真实的方法论贡献**，与经典轨道形成对照，值得在 contribution 中突出。

## A-3 须修正项（严重度）
- **P1（已实质性闭合，post-M1.5 复核）** — **"应用层零 classic / 165 项全部零 classic" 声明 post-M1.5 静态核验支持成立**：`PSA_audit.v`（已补交）L108–121 的 2026-08-19 勘误记载 4 项继承 classic，但此为 **M1.5 重写前的过时状态**；当前 `ca_merged_full_25.v`（L63579 `Module ExpSeries`/L63672 `exp_mono_le_noclassic`/L63719 应用）已消除 `exp_increasing`→classic 唯一入口，4 个注意力定理全部位于重写之后，`exp_increasing` 仅存于 `ca_*` 基础设施（非审计目标）。论文 §11 的"165 项全部零 classic"声明**成立（post-M1.5）**，须注明 M1.5 重写并显式声明 `sig_forall_dec`/`sig_not_dec`/`fext` 属可接受 Reals 基底、非 `Classical_Prop.classic` 公理。
- **P1（已部分消解，性质降级）** — 165 项审计的**机器可复跑证据仍不完整**：`audit_run.txt` 现已存在（`Live_harness\AI注意力算法\审计证据\` 与 `PSA-CertifiedSparseGating\docs\`，Aug 21），其 55 个捕获的定理块「Axioms:」列表全零 `Classical_Prop.classic`，但仅覆盖 **55/165** 块且未随 `30模块` co-locate；`_CoqProject`/`Makefile`/`_merge_ca.py`、独立模块 `.vo` 仍缺失，`Require Import PSA.PSA_framework` 在当前快照重跑受阻。须随稿补**完整 165 项** `audit_run.txt`+构建配置，使 165 项 `Print Assumptions` 可由接收方复跑。核心定理可证（本文已独立数值复核），"零 classic"在 55 块样本成立，**完整 165 项的最终机器证据待补交**。
- **P3** — 模块计数 55（实测 57）；声明计数 269 注明"Lemma+Theorem"口径（区别于 316 顶层声明/272 Qed）。
- **P3** — 附录 A 交叉索引补 `probe_nearcoll.v`（承载 `golden_near_collision_gold`）。

## A-4 边界声明评价（正面）
论文 A 对"证书不覆盖学习权重 / 注意力 logits / PPL / 外推语义"的边界（§1, §7, §14）**标注清晰且一致**，与论文 B 的对应声明正交、不冲突。这是可审计 AI 定位的诚实基础。
