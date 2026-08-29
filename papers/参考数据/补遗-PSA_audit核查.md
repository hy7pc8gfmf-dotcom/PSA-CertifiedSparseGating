# 补遗：PSA_audit.v 核查报告（2026-08-26）

> 本补遗针对用户于 2026-08-26 16:19 补交的 `D:\ComplexAnalysis\ConstructiveWorld\30模块\PSA_audit.v`，
> 更新此前四份报告中的 P1「工件完备性缺口」结论。原结论（代码库分析报告 / 交叉核验总表）中
> 关于"PSA_audit.v 缺失"的部分现部分消解，但引出一项更关键的事实性发现。

> ---
> ## 🔁 修订说明（2026-08-26 post-M1.5 复核，本节具最高效力）
>
> 本补遗 C 节与 E.2(a) 原裁定「**161/165 零 classic，4 项注意力链继承 `Classical_Prop.classic`**」
> 经对当前提交物的 post-M1.5 静态核验后**被推翻**，依据如下：
>
> 1. **`PSA_audit.v` L108–121 勘误描述的是 M1.5 重写前的旧状态**（勘误落款 2026-08-19）。
> 2. 当前权威合并快照 `ca_merged_full_25.v` **已并入 M1.5**：`Module ExpSeries`（L63579）、
>    `exp_mono_le_noclassic`（L63672 定义、L63719 应用），头注释 L61605 明言「M1.5 已清零」。
> 3. 4 个被勘误的注意力定理（`softmax_ratio_le2` L63937 / `softmax_diff_i` L63852 /
>    `softmax_l1_bound_exp` L63910 / `certified_attention_approx` L64137）**全部位于 M1.5 重写之后**。
> 4. 全文件 `exp_increasing` 的实际证明使用仅存于 `ca_*` 分析基础设施（L2557/L2593 等
>    filterlim/Rpower/ln 引理，属允许的 42 处 `Require Import Classical` 范围），**不在 165 项审计目标内**。
> 5. 配套 `audit_run.txt`（`Live_harness\AI注意力算法\审计证据\` 与 `PSA-CertifiedSparseGating\docs\`，
>    Aug 21，68986 字节）**现存在**：其 55 个捕获的定理块「Axioms:」列表**全零 `Classical_Prop.classic`**
>    （全文 3 处该字符串命中均在叙述文字 L1040/L1069/L1091，非公理列表）。
>
> **修正后结论**：**post-M1.5 静态核验支持「165/165 零 `Classical_Prop.classic`」**。
> 论文"165 项全部零 classic"口径**成立**，但须 (i) 注明 M1.5 重写；(ii) 标注 `PSA_audit.v` L108–121
> 为 pre-M1.5 过时勘误；(iii) 随稿补交**完整 165 项**审计日志（现有日志仅捕获 55/165 块、未 co-locate，P1 缺口仍存，性质由「缺失」降级为「不全/未随稿」）。
> ---

---

## A. 文件到位确认

| 项目 | 实测 |
|------|------|
| 路径 / 大小 | `PSA_audit.v`，229 行，12,444 字节，mtime 2026-08-20 |
| `Print Assumptions` 命令数 | **165**（与论文"165 项"吻合）|
| 审计目标在 `ca_merged_full_25.v` 中存在数 | **165 / 165，0 缺失** |
| 被引用的 15 个模块（`Module X.`）在合并版中存在 | **15 / 15 全部存在** |

**结论**："165 项"计数在结构层得到证实；审计脚本的目标定理全部对应于提交物中的真实定理，
证明该审计确系针对本代码库（而非杜撰或指向其他快照）。

---

## B. 关键性质：这是「脚本」而非「运行日志」

- 文件是 coqc 的**输入脚本**（一串 `Print Assumptions <模块>.<定理>.` 命令），
  内部**不包含任何** "RC=0" / "Closed under the global context" / axiom 列表的**捕获输出**。
- 论文声称的"165 项 RC=0 / 零 axiom / 零 classic"需要 `audit_run.txt`（运行输出捕获）作为机器证据，
  该文件**仍缺失**。
- **结论**：机器证据链仍**不可独立复跑**——脚本存在 ≠ 审计结论已被本快照佐证。

---

## C. 🔴 新发现：审计文件自带勘误，证明"零 classic"声明不实

`PSA_audit.v` 第 108–121 行（2026-08-19 勘误）原文记载：

> `softmax_ratio_le2` / `softmax_diff_i` / `softmax_l1_bound_exp`
> 经 `exp_mono_le ← exp_increasing`（Rpower，导数/MVT 路线）继承 `Classical_Prop.classic`——
> 此前交接文档称"85 项全部零 classic"不准确；`softmax_sum_one` 本身零公理。
> …… `certified_attention_approx` 经 `softmax_l1_bound_exp` 继承 `Classical_Prop.classic`（同 M1 勘误）。

经核验，这 **4 个定理均在提交物 `ca_merged_full_25.v` 中存在**（`present_in_merged=True`），
故该依赖**适用于本快照**，非过期或悬空引用。

**裁定（pre-M1.5 原判，已被上方修订说明推翻）**：~~若论文 A 声称"165 项全部零 classic / 应用层零 classic"，此为**事实性错误**，须纠正为：~~

> **post-M1.5 修正（具优先效力）**：经对 `ca_merged_full_25.v` 的静态核验，M1.5 已并入、4 个注意力定理全部位于重写之后、`exp_increasing` 仅存于 `ca_*` 基础设施（非审计目标）→ **post-M1.5 静态核验支持「165/165 零 `Classical_Prop.classic`」**。以下 pre-M1.5 原判保留以彰明演变轨迹：

- ~~**161 / 165 零 `Classical_Prop.classic`**~~ → **165/165 零 `Classical_Prop.classic`（post-M1.5）**；
- ~~**4 项（认证注意力近似链 M1 SoftmaxStability + M2 CertifiedAttention.certified_attention_approx）
  继承 `Classical_Prop.classic`**，已文档化勘误（2026-08-19）~~ → 该勘误为 **pre-M1.5 过时**，M1.5 已消除其 classic 入口；
- **核心证书**（C=4、E5''、T8、frame_check、Gershgorin、Dirichlet —— 即 M3/M4/ChampionCertificate/
  FrameCheck* 模块）经审计注释为"零 `Classical_Prop.classic`"（仅用 `sig_forall_dec`/`sig_not_dec`/
  `fext` 作为 Reals 基底）。这与用户纪律"应用层零 `Classical_Prop.classic`"一致；
  但须注意：该定义将 `sig_forall_dec` 等视为**可接受的 Reals 基础设施**，而非 `Classical_Prop.classic`
  公理本身——论文须显式声明此边界，否则与"42 处 `Require Import Stdlib.Logic.Classical` 全在 `ca_*` 基础设施"
  表面看似矛盾。

---

## D. 构建配置仍缺失 → 审计仍不可重跑

| 构建工件 | 状态 |
|----------|------|
| `_CoqProject` | **MISSING** |
| `Makefile` | **MISSING** |
| `_merge_ca.py` | **MISSING** |
| `PSA/` 逻辑目录 | **MISSING** |
| 独立模块 `.vo` | **MISSING**（仅 `ca_merged_full_25.vo` 存在）|

- 审计第 7 行 `Require Import PSA.PSA_framework` 需要逻辑路径 `PSA → <dir>` 映射，
  该映射原存于缺失的 `_CoqProject`。在仅含合并版 `.vo` 的快照下**无法重跑**。
- 若需独立复跑，须补：`_CoqProject`/`Makefile` + 独立模块 `.vo`（或改造 import 指向
  `ca_merged_full_25`），再捕获 `audit_run.txt` 作为机器证据。

---

## E. 修正后的总体裁定（替代原 P1 结论）

1. **P1「工件完备性缺口」状态（post-M1.5 复核）**
   - ✅ 消解：`PSA_audit.v` 到位，使"165 项"结构属实、审计目标 165/165 对应提交物。
   - ✅ 消解（post-M1.5）：原"🔴 新硬伤：审计文件自身证明'零 classic'声明对 ≥4 项不成立"**已推翻**——`PSA_audit.v` L108–121 勘误为 pre-M1.5 过时，`ca_merged_full_25.v` 已并入 M1.5 `exp_mono_le_noclassic`，4 个注意力定理位于重写之后，`exp_increasing` 仅存于 `ca_*` 基础设施（非审计目标）→ **165/165 零 `Classical_Prop.classic` 静态核验支持成立**。
   - ⚠️ 仍开放：配套 `audit_run.txt` 现存在（55 个定理块全零 classic），但**仅捕获 55/165 块、未随稿 co-locate** → 完整机器证据待补交完整 165 项日志（P1，性质由"缺失"降级为"不全/未随稿"）。

2. **论文 A 须做两项修正**
   - (a) ~~将"165 项全部零 classic"改为"161/165 零 `Classical_Prop.classic`；4 项注意力近似链继承
     `Classical_Prop.classic`（已勘误）"~~ → **post-M1.5 修正：论文"165 项全部零 classic"口径成立**（M1.5 `exp_mono_le_noclassic` 已消除 `exp_increasing`→classic 入口；`PSA_audit.v` L108–121 勘误标注为 pre-M1.5 过时即可）。
   - (b) 显式声明"`sig_forall_dec`/`sig_not_dec`/`fext` 属可接受的 Reals 基底，非 `Classical_Prop.classic`
     公理"，以闭合与"42 处基础设施 `Require Import Classical`"的表面矛盾。

3. **核心证书纪律维持成立**
   - C=4 / E5'' / T8 / frame_check 的数值与"零 `Classical_Prop.classic`"纪律，
     经**独立双方法数值核验** + **审计脚本目标存在性核验（165/165）**双重支撑，**维持成立**，
     不受 C 节 4 项注意力链 classic 依赖影响。

---

## F. 复用建议

- 当前快照下**无法**复跑审计（缺 `_CoqProject`/`.vo`/运行捕获）。建议用户在可行窗口内补交
  `audit_run.txt` + `_CoqProject`/`Makefile`，并将论文 A 的"零 classic"口径按 C 节修正，
  方可使"165 项审计"成为可独立验证的机器证据。
- 本报告与《代码库分析报告》《交叉核验总表》《审稿报告-论文A》配套；本补遗对原 P1 结论具**替代效力**。
