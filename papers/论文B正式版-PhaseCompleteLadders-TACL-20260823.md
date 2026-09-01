# Phase-Truncated Frequency Ladders: A Controlled Empirical Study with a Certified Basis-Stability Core

> 正式版（对齐当前代码基态）。
> 作者：王宝军、夏挽岚（通讯作者，xiawanlan33@163.com）、祖光照、周志农、高雪峰
来源：论文 B 草稿清洗（删除会话/评审/版本内部注记），
> 实验数据不变；配套论文 A（Coq 形式化）代码状态按当前基态（合并版 `ca_merged_full_25_m2.v`（98187 行，77 模块分区，绿产物追加路线：E153 绿基线 87632 + M2/G-7/G-9 批次 + G-10/G-11/G-13/CS-21/CS-23/CS-22/Z2b 批次（2026-09-01 追加批次）+ z3b 批次（2026-09-02 追加批次，合并全量编译 EXIT=0：CI 09de44e 全局绿（Rocq 9.0 + mathcomp 2.6 真环境 + coqchk）+ 本地 9.1 链 run10）），
> 20 探针 + ca_zeta_euler/ca_rip_cr 构造性轨道并入、合并编译 MERGE_EXIT=0；**持续集成全链路验证通过**：lib 依赖链编译、合并版编译（Rocq 9.0 + mathcomp 2.6）、PSA 核心编译、零 Admitted 检查、coqchk 内核独立复验；165 项审计完整 165/165 日志随稿）。投稿方向：TACL/Findings（实证 + 可审计性）。

---

## Abstract (EN)

Positional encodings degrade sharply beyond their training length. We study length
extrapolation through the lens of the *frequency ladder* — the multiset of rotation angles
(or additive features) a positional scheme employs. On a controlled char-level benchmark
(~0.5M parameters, T_train=512, 10 random seeds; core orderings and statistics replicate
progressively from n=3 through n=5 to n=10, §4.1/§13), we find: (1) truncating a Fourier
ladder to its *phase-complete* bands (n_j < T_train) dramatically improves extrapolation across
three ladders; (2) RoPE-style rotation on a phase-truncated ladder extrapolates far better than
vanilla RoPE (best geometric-mean ppl 12.40 vs vanilla RoPE 25.30 at 8×); the best within the
rotation family is a *random dense rotation ladder*
(psi-rope-rand, [3,511] random angles, 6.45±0.03 at 8×, 3 seeds; n=10 full replication; certificate status: outside the frame-bound coverage of Paper A — random ladders do not pass the reflective checker; the provable content is limited to ℓ² linear independence
4.00±0.5, ordering unchanged) — 44% below the 3-seed
NTK number (11.54±1.18, p=0.018, d=−6.06, **directional at n=3, df=2; 5-seed replication
completed 2026-08-24: rand vs ALiBi t=6.66, grid vs rand t=11.28, rand vs c3 t=−9.44, rand vs rope t=−6.20, all df≈4, all highly significant — the directional claims (ALiBi best / grid collapse / rand best-in-family / RoPE poor) hold at n=5**), with the 7-band geometric ladder [3,7,15,31,63,127,255]
(12.40) and NTK-aware rescaling forming the strong baselines — while an uncertified strong baseline, ALiBi,
reaches 4.47±0.10 at 8× (31% lower, flat extrapolation); the gap between certified schemes
and this uncertified ceiling is explicitly quantified (**2.85× for the certified 4-band ladder,
12.75 vs 4.47, and 2.78× for the composite-certified 7-band ladder, 12.40 vs 4.47 — ratio-based;
the 31% figure is ALiBi's lead over psi-rope-rand 6.45, a different comparison — the title's
"certified" refers to representation-layer certificates, **not**
extrapolation robustness, and certificates do not bound end-to-end extrapolation PPL);
(3) dropping the *marginally*
covered band (coverage 1.0) strictly improves all extrapolation lengths across all seeds —
a coverage *gradient*, not a threshold; (4) the certified 4-band ladder [3,13,53,213]
carries a machine-checked rational frame certificate (μ = 4/5, Coq), and the 7-band
geometric ladder contains a certifiable sub-core — a composite certificate
(frame core + energy-budget margin) we formalize: `champion_e5_composite_certificate`
proves (S − coh_e5) ≤ ‖F‖² ≤ (S + coh_e5), a **basis-representation stability
certificate**, orthogonal to the empirical champion (the random ladder of psi-rope-rand
lies outside the certificate scope); (5) honest controls: NTK-aware rescaling beats
phase-truncated rotation at 4–8× — our surviving claim is *no-test-time-surgery, no
per-length recalibration, and certificates*, not absolute extrapolation supremacy. NoPE
(no positional encoding) shows catastrophic in-distribution loss (9.06) yet the flattest
degradation curve (1.27×) — but the essential trade of positional encodings is a property
of *periodic parameterization*, not of positional information: ALiBi's in-distribution gap
to the optimum (4.64 vs psi-rope-rand 4.48 at 512) is only 0.16 while its extrapolation
stays flat (decay ratio 0.96 < 1, the only scheme that improves), so aperiodic biases
escape the trade at near-zero cost. Under
the formal configuration (tinystories200 · 27000 iters), **τ-trim (τ-trimmed reallocation)** —
keeping low/mid frequencies and gently trimming the high-frequency tail — showed a
single-seed (s1337) improvement from 7.50 to 5.15 (−31%, optimal cutoff N* ∈ [448,480],
fine-scanned and locked), **but a 2026-08-25 multi-seed replication (s42/s7, 27000 iters,
rand vs rt448) revealed the trimming semantics: `--rand-max` re-arranges the whole 64-dim
cyclic-fill allocation (not simple high-frequency removal) — s42's rt448 is a no-op (its
first-32 wavelengths contain no >448 angle, so the model is byte-identical to rand;
11.76 = 11.76 is forced), s1337's gain is the reallocation of its rank-11 wavelength 491
(seed-specific), and s7's same reallocation has no effect (7.67 = 7.67) — **the trim gain
is a seed-specific reallocation observation with no generality, downgraded to future
work** (honest qualifier, 2026-08-26 stage-C replication): formal absolute values are systematically offset by implementation environment (corpus/script version) — reproduced formal rand @4096 = 12.14 (paper 7.50), rt448 = 6.69 (paper 5.15), so **no cross-environment absolute comparison**; however the rt448 < rand improvement direction is reproduced in both independent runs (here −45%, paper −31%), preserving the τ-trim relative evidence; **2026-08-25 replication status (s1337 rt448, 27000 iters, formal config)**: @4096 = 6.68 (CI95 [6.27, 7.12]), inconsistent with 5.15; the run was heavily disturbed by 848 GPU-thermal cooldown pauses (length_extrap self-warns "reduce load and rerun"), so 6.68 cannot adjudicate 5.15; the formal rand baseline (7.50) is also missing — verdict pending a cooled rerun (<3 cooldowns) plus the formal rand baseline. **2026-08-26 stage-C verdict**: formal rand baseline = 12.14 (paper's 7.50 not reproduced; +62% environmental offset), formal rt448 cooled rerun = 6.69 (consistent with 6.68; two-run stability confirms cooldown pauses do not alter values) — **absolute values are systematically offset by implementation environment (corpus/script version) and not directly comparable, but the rt448 < rand improvement direction is reproduced in both runs (here −45%, paper −31%)**; the "seed-specific observation" framing of τ-trim stands, with strengthened directional evidence.
over-trimming (256) hurt and structured-frequency offsets (ogrid) are rejected. The
τ/collision mechanism — a candidate explanation, not an established causal mechanism —
accrues **7 directional positive verdicts, merged into 4 independent empirical pillars**
(eval-only 3 + true-training 1; §9.2). **Honest
scope (reviewer conventions)**: the 9-scheme × 10-seed replication (tinystories fast config,
3000 iters) is **completed (2026-08-25)**: the main-table ordering (alibi < rand < t5rel <
e5pp < c2 < c4 < c3 < grid < rope) reproduces from n=3 through n=10 with no directional
drift — new seeds {2718,1618,31416,12345,999} differ from the existing five by ≤0.8 with no
directional bias, closing reviewer P0-① (random-seed robustness); all directional claims
hold at n=5/n=10 (rand vs ALiBi t=6.66, grid vs rand t=11.28, rand vs c3 t=−9.44, rand vs
rope t=−6.20, all df≈4; cross-corpus order alibi < rand < t5rel < c4 < grid reproduces on
Gutenberg / tinystories / owt); the τ trim point is post-hoc selected (not a preregistered
hypothesis test) and the τ mechanism is a candidate explanation, not an established causal
mechanism — the single-seed trim gain was not reproduced under multi-seed replication;
train-time evaluation and
eval-only pruning are distinct protocols and are kept separate. We document our
falsified hypotheses alongside the surviving ones, and propose the ladder *phase profile*
as a diagnostic for arbitrary positional encodings.

**Keywords**: positional encoding; length extrapolation; frequency ladders; phase truncation;
RoPE; Coq formal verification; auditability; preregistered criteria

---

## 1. Introduction

长上下文是前沿模型主战场；现有上下文扩展方法（PI / NTK-aware / YaRN / partial-RoPE /
ALiBi）全为启发式，缺一个统一变量。本文引入**频率阶梯**作为位置编码的统一分析对象：
位置编码 = 角度多重集 {θ_t}（旋转）或频率集 {n_j}（加性），外推行为由阶梯的**相位剖面**
（每带覆盖倍数 T_train/n_j、可见带数、填充均匀性）决定。

**贡献**：(i) **相位截断**——剪掉超训练窗的相位带显著改善外推；(ii) **旋转注入**——
相位截断阶梯上的 RoPE 式旋转远优于朴素 RoPE；(iii) **覆盖梯度**——剪掉覆盖恰 1.0 的
边缘带在全部 OOD 长度、全部 seed 上严格改善（梯度而非阈值）；(iv) **τ/碰撞距离机制**——
提出为排行榜的**候选解释**（周期带承载碰撞负债、非周期偏置近零代价逃逸；与观察一致而非
已建立机制），获 **3 个稳健实证支点（eval-only）+ 1 个单种子候选支点（真训练，多种子未复现；方向性观察）**；
(v) **性能-可证明性前沿**——带证书方案与无证书上限的差距被明确量化（**2.85×：C=4 12.75 vs 4.47；2.78×：复合证书七带 12.40 vs 4.47**，以比值计；30% 是 ALiBi 相对 psi-rope-rand 6.45 的领先，属另一对比），可审计性本身作为
价值主张；(vi) **τ 裁剪（τ-trimmed reallocation）**——正式配置下保留低中频 + 温和裁剪高频端把旋转族
外推 7.50 → 5.15（−31%）（**单种子观察 s1337，多种子未复现，列为未来工作**；裁剪语义为 64 维循环填充下的整体维度重组，非单纯高频移除）。

**与配套论文 A（Coq 形式化）的关系**：本文实证验证论文 A 形式化框架（同一阶梯族）的
适用性；论文 A 的框架界/能量界为「免修改 + 证书」定位提供理论支持——两文共享阶梯对象，
主张正交：形式化保「表示稳定性/能量有界」，实证报「外推 PPL」。证书与 PPL 外推之间
**无形式化桥梁**（经验观察，已明确声明）。**证书边界（审稿口径，全文统一）**：所有证书
覆盖**基表示层的能量范数/框架界**（`(S−coh) ≤ ‖F‖² ≤ (S+coh)` 类），**不覆盖注意力
logits、不覆盖 PPL、不保证端到端外推性能**——证书与性能是两条平行轨道（§7/§8 接口声明）。

## 2. 实验设置与协议

- **模型**：char 级 GPT（~0.5M 参数，4 头，head dim 32，16 旋转维/头；参数量随模式而异：
  dense 494,336 / rope 428,800 / psi（C=4，128 带）625,408——约 0.43M–0.63M，正文统称
  ~0.5M 级），Gutenberg
  5.1M 字符（vocab 125），T_train=512，3000 iters，batch 32，**seeds {1337, 42, 7}**
  （主结果均报 3-seed 均值±std）。
- **确定性协议**：rope 在两种温控协议下逐位复现（损失到小数点后四位）——同 seed 同
  batch 的跨 run 比较合法。
- **评估**：T ∈ {512, 1024, 2048, 4096}（1×/2×/4×/8×），val ppl。

## 3. 频率阶梯：统一形式化

- **旋转机制**：位置编码 = 角度多重集 {θ_t}，核为逐槽和 Σ_t w_t·cos(d·θ_t)（带间无交叉项）。
- **加性机制**：φ(k) = [cos/sin(2πk/n_j)]，含绝对相位项。
- **阶梯族**：生成器 next = C·n+1；C=2 给出梅森列 n_j = 2^{j+2}−1（近似二进），C=4 给出
  [3,13,53,213]，C=3 给出 [3,10,31,94,283]。
- **相位截断**：训练长度 T_train=512 下，带 n_j ≤ T_train 为**相位完备带**（窗口内可分辨的
  完整周期）；n_j > T_train 为不完备带（窗口内近似线性斜坡、范数→0）。截断 = 剪除不完备带。
- **相位剖面**：每带覆盖倍数 T_train/n_j、可见带数 m_vis、填充均匀性（16 槽 mod 带数）——
  任意位置编码可输出的诊断量。

## 4. 主结果

### 4.1 主表（旋转组 3-seed 均值±std + 对照组）

| T | dense(wpe)¹ | rope³ | rope-PI¹ | rope-NTK¹ | NoPE¹ | **psi-rope 七带** | psi-rope C=4 | psi-rope C=2(8带) | psi-rope C=3 |
|---|------|------|------|------|------|------|------|------|------|
| 512 | 5.40 | 4.44±0.08 | 4.46 | 4.46 | 9.06 | 4.53±0.10 | 4.70±0.14 | **4.46±0.06** | 4.65±0.11 |
| 1024 | 15.98 | 6.77±0.07 | 16.59 | 5.11 | 9.72 | **4.75±0.06** | 5.64±0.07 | 4.95±0.04 | 5.45±0.58 |
| 2048 | 27.86 | 13.68±1.21 | 32.08 | 6.55 | 10.71 | 8.28±0.28 | 8.42±0.10 | 9.16±0.02 | 11.44±4.33 |
| 4096 | 34.94 | 25.30±4.63 | 37.87 | **10.74** | 11.55 | 12.40±0.74 | 12.75±0.34 | 13.84±0.25 | 22.86±5.30 |

（¹ 对照组单 seed：dense 为 s1337，rope-PI/NTK 为 eval-only 频率缩放（零训练），NoPE 为
s42 完整训练；³ rope（朴素 RoPE）为 b32 3-seed 均值±std。3-seed 统计以 psi 系与 rope-NTK
为限，对照组单 seed 已明确标注。）

**多重比较校正（审稿必修 B2）**：本文对 5 组主要对照（psi-rope-rand vs rope-NTK /
C=4 / E5''（最优七带几何阶梯 [3,7,15,31,63,127,255]，即 C=2 八带剪去 511 带后的版本）/
ALiBi / grid）执行 Welch t 检验，属多重比较场景。n=3 时代因 df=2 未作
Holm 校正（方向性观察）；**n=5 复核已完成（2026-08-24，9 方案 × 5 种子）**、**n=10 全量复核已完成（2026-08-25，9 方案 × 10 种子）**：5 组主要
对照全部显著（最小 t=−6.20，df≈4），**Holm 校正不改变任何结论**——多重比较风险实质
解除（校正后数值见《训练数据对比分析-n5种子复核与owt独立验证-20260824.md》与《训练数据全量复核-n10完成与τ裁剪多种子复核-20260825.md》）；n=10 下主表排序
（ALiBi < rand < t5rel < e5pp < c2 < c4 < c3 < grid < rope）完全复现，新增 5 种子
（{2718,1618,31416,12345,999}）与既有 5 种子均值差异全部 ≤0.8 且无方向性漂移，
**随机种子稳健性在 n=10 下封闭（评审 P0-①）**。
**强词回避**：摘要/结论不使用"显著改善""击败"等词表述这些对比，一律
以"方向性优于"或原始数值呈现。

**偏置类对照表（b32 三个种子，T_train=512）**：

| 方案 | 512 (分布内) | 1024 | 2048 | 4096 (8×) |
|------|---------|------|------|-----------|
| ALiBi（线性偏置） | 4.64±0.02 | 4.57±0.05 | 4.59±0.10 | **4.47±0.10** |
| T5 相对偏置（32 桶） | 5.32±0.07 | 5.46±0.05 | 6.56±0.02 | 8.48±0.60 |
| psi-rope-rand（旋转族内最优） | 4.48±0.10 | 4.67±0.20 | 5.41±0.27 | 6.45±0.03 |
| **grid（θ=2πm/512，log-uniform）** | 4.57±0.12 | 10.90±0.78 | 19.01±1.21 | 25.66±2.22 |

**偏置类判决**：
- **ALiBi @8× = 4.47±0.10**：对 psi-rope-rand（6.45±0.03）领先 31%（0.69×）> 15% 判据——**「性能最优方案」
  归属移出旋转族**；psi-rope-rand 收缩为「旋转族内最优」。ALiBi 无任何形式化保证（线性
  偏置核与论文 A 证书正交），保留主张为「带证书方案中的最优 + 零测试时修改 + 免逐长度
  重调参」。**T5 相对偏置**：偏置类退化锚点（5.32→8.48，+60%），证伪「可训练偏置 → 好外推」。
- **grid 判决**：分布内 grid 4.57 ≈ rand 4.48/ALiBi 4.64 几乎持平，但 2× 即崩（10.90 vs
  4.67），8× 达 25.66——比 rand 差 3.98 倍。τ/碰撞机制解释：纯网格 m 为奇数时原子有效周期
  恰 512，自碰撞恰在训练窗边界、τ≈1 负债带 → 外推灾难；offset-grid（无理偏移消碰撞）
  是理论上的唯一逃逸方向（@4096 16.12±1.32——ogrid ≥ grid 确认、μ=0 正交证书未带来外推性能优势（证伪））。

**对照组三判决**：
- **rope-NTK @8× = 10.74**：对预登记单 seed 基线（psi-rope C=4 13.06）领先 21.6%，对
  3-seed 均值 C=4（12.75）领先 15.7%、对均值最优七带（12.40）领先 13.4%（**后者未过 15%
  阈值——判据对基线口径敏感，单点对比为方向性证据**）——**绝对外推
  主张收缩**，保留「2× 内仍胜（4.75 vs 5.11）+ 零测试时修改 + 免逐长度重调参 + 带机器
  证书」。rope-NTK 为纯经验修复、无任何形式化保证（频率重缩放破坏阶梯结构，论文 A 的
  证书侧对其无可证陈述）。
- **NoPE 平坦曲线**：分布内灾难性差（9.06，位置信息必要性确认），但退化仅 1.27×（vs
  全部位置方案的 2.7–2.9×），@8×（11.55）追平最优种子——但 **ALiBi 打破「位置方案用
  分布内 2× 优势换取外推脆弱性」的笼统交易：交易是周期参数化的属性，不是位置信息的
  属性**（ALiBi 分布内 4.64 仅比最优 4.48 差 0.16，且外推平坦）；NoPE 保留「位置必要性」
  的对照价值。
- **rope-PI 无微调惨败**（37.87）——测试时修复不是无无免费午餐定理定理，NTK 是唯一有效形态。

**阶梯族内判决**：
- **七带阶梯 [3,7,15,31,63,127,255] 全程均值最优**（2×/4×/8× 全列第一）。
- **覆盖梯度 3-seed 单调确认**：剪掉覆盖恰 1.0 的 511 带，全部 OOD 长度、全部 seed 严格
  改善（8×: 13.84→12.40；分布内仅付 0.07）——**边缘覆盖带是 OOD 纯负债**。
- **C=3 分层**：s1337 的 28.97 是坏抽签（族内 s42/s7 为 19.48-20.12），但即便好 seed，
  C=3 在 8× 仍全 seed 劣于其余三族——间距带中等程度的确定性远程代价（约 +60%）+ 显著
  放大的 seed 方差（8× std 5.30 vs 其余族 0.25-0.74）；方差排序 C=3 ≫ E5'' > C=4 ≈ C=2。

### 4.2 加性组

| T | psi-full C=3 | psi-trunc C=2 | psi-trunc C=3 | psi-trunc C=4 |
|---|------|------|------|------|
| 512 | 4.38 | 4.67 | 4.64 | 4.77 |
| 4096 | 39.69 | **18.43** | 29.70 | 23.89 |

- psi-trunc C=2 在 4×/8× 上击败 rope（12.15 vs 13.68；18.43 vs 25.30，rope 为 b32 3-seed
  均值；单 seed 口径下结论相同）；
- 全梯 vs 截断：三种阶梯上截断收益三次复现（C=3: 39.69→29.70，−25%）。

## 5. 经验规律（Empirical Patterns）

> 以下为**强经验规律**（覆盖梯度、截断效应、旋转注入），其根本机制（除「长带死重」外）
> **机制未明**——明确标注为「经验规律，机制未明」，不作「机制发现」主张；与论文 A 的
> 形式化贡献（框架界/衰减界）之间无解释性桥梁。

1. **截断效应**（稳健，3 次复现）：剪掉部分相位带恢复外推。
2. **相对性效应**（稳健）：同阶梯下旋转优于加性。
3. **二进身份 + 覆盖梯度**（3-seed 确认）：C=2 阶梯 = 「RoPE 砍掉 OOD 尾巴」。归因注记
   （边界说明）：配套形式化不主张解释本经验律——`certified_attention_approx` 的输出界对
   谱能量 ε 单调，而剪掉 511 带的 ε 几乎不变（该带窗内范数→0），ppl 却 13.84→12.40 远超
   噪声——**增益机制不在形式化的谱能量通道内**（候选：绝对相位混叠、softmax 分母数值
   稳定性，均被现框架抽象掉，future work）；形式化的贡献限于稳定性检验（剪枝不破坏框架
   界、μ 不变——排除严重退化风险）。
4. **长带死重**：128 带中 120 个 n_j>512 带对训练损失贡献 ≈ 0（1.4111 vs 1.4120）——
   与理论预测（窗口内范数→0）一致。
5. **填充均匀性无关**：七带填 16 槽（16 mod 7 = 2，不均匀）仍居最优——均匀性被正反两
   面证据排除。
6. **跨维度推测**：1D 覆盖梯度在 N 维语境下 = 「剪掉任意维度过长的轴」；张量积证书给出
   精确升维公式 M_bound^{(N)} = (C³/2)·((1+4K_C)^N − 1)（C=4 时底数 = 5；N=2: 768、
   N=3: 3968、N=4: 19968，均已全定理级证）。

## 6. 假设证伪链（方法学贡献）

- ~~**「psi 天然外推」**~~ → 绝对编码性能严重退化（分布内 5 → 8× 34）。
- **双覆盖律（已撤回）**：「double-coverage 律（n_max ≤ T_train/2）」被 C=2（覆盖 1.0）
  实测第二好的反例证伪。
- ~~**「283 单带污染」**~~ → E5' 剪掉 283 后**更差**（33.20 vs 28.97），**排除**——283 带
  实际在贡献分布内质量（E5' 分布内 4.78 为旋转组最差）。
- **偶填充假说（已杀死）**：E5' 均匀填充仍失败 + E5'' 不均匀填充仍居最优——均匀性被
  正反两面证据排除（16 mod 7 = 2 仍最优）。
- **E1 消融证伪**：psi-rope-rand（随机旋转）反超几何旋转（假说证伪）；dense-frozen
  「瓶颈全解释」分支证伪（分布内掉质量 6.08 vs 4.5-5.0）；psi-lin 最差（39.62±4.07 @8×）。
- **相干衰减预测因子（证伪其跨族普适性）**：ΔCoh 在稀疏几何阶梯族内 4 点 R²=0.982，
  但 E1 消融扩充至 13 点后 max 型 R² 崩塌至 0.101——**没有任何相干聚合器是跨族通用预测
  因子**（最优 median 也仅 R²≈0.6），原 R²=0.982 是小样本过拟合。
- **保留假设的分层裁决（3 个种子）**：(i) **间距假设——部分成立**：C=3 间距在 8× 全
  种子劣于其余三族（确定性代价约 +60%），但非 s1337 显示的 2.2× 灾难；(ii) **噪声假设
  ——同样部分成立**：s1337 的 28.97 是坏抽签，且 C=3 族方差被极度放大（8× std 5.30 vs
  其余族 0.25–0.74）——间距的效应一半在均值、一半在方差。开放问题：间距如何同时抬升
  远程均值与放大方差——机制未明，已明确报告。

## 7. 证书侧（与论文 A 的接口）

- **[3,13,53,213] 实例证书已证**（Coq，μ=4/5，框架界 [1/5, 9/5]，全有理常数、可判定；
  ∀N≥214 长度一致性已并入）。
- **七带复合证书**：并列最优七带阶梯整体行和 > 1 不可整体认证，但其隔带子核
  [3,15,63,255] 同一配方验算行和 ≤0.781 ⟹ μ=4/5 可认证；T8 复合证书（T8CoreCertificate，
  11 Qed 零 classic）= 认证核（gershgorin 框架界）+ 边际带（[7,31,127] 行能量预算）；
  **端到端复合证书** `champion_e5_composite_certificate` 对七带证明
  (S−coh_e5) ≤ ‖F‖²_{255} ≤ (S+coh_e5)（全矩阵相干加权对称界）——**带证书方案中的性能
  领先者（七带）现持复合界机器证书**（明确为「认证了七带方案所用基函数」，非「认证七带
  方案模型」——不含注意力分数/外推 PPL 保证）。该复合界与 PPL 改善之间的桥梁由经验观察
  支撑，未经形式化。
- **术语**：(S±coh) 形态称**复合界（相干加权范数界）**，区别于标准框架界 (1±μ)S——
  "框架界"保留给 Gershgorin (1±μ)S 形态（如 C=4 核 [1/5,9/5]）。
- **自包含技术说明（审稿要求，降低阅读门槛）**：**框架界**——对基函数系 {ψ_j} 与系数
  向量 c，若逐对相干 |⟨ψ_i,ψ_j⟩| ≤ μ（i≠j）且行非对角和 R_i = Σ_{j≠i}|⟨ψ_i,ψ_j⟩| ≤ μ
  （Gershgorin 条件），则 (1−μ)·Σ|c_j|² ≤ ‖Σ_j c_j ψ_j‖² ≤ (1+μ)·Σ|c_j|²——基表示层的
  能量范数稳定性界（μ<1 时下界为正，构成真框架；μ=4/5 的 C=4 实例给出 [1/5,9/5]·S）。
  **复合界** `champion_e5_composite_certificate`：对七带 [3,7,15,31,63,127,255]
  （单位系数时 S=Σ|c_j|²=7），(S−coh_e5) ≤ ‖F‖² ≤ (S+coh_e5)，其中
  coh_e5 = Σ_{i<j}|c_i||c_j|·δ_e5(i,j) 为 21 对带间相干交叉项界（δ_e5 逐对保守有理
  上界，floor-sqrt/Jordan/Dirichlet 单侧松弛）——该界仅约束基函数范数稳定性，
  **不涉及注意力 logits 或外推 PPL**。
- **反射检查器**：`frame_check_instance` 对任意阶梯做 μ≤4/5 的可判定有理判定（提取为
  OCaml/FFI，24/24 自测），健全性主定理 `frame_check_instance_sound` 已 Qed——「带机器
  证书」由一台自带健全性证明的运行时检查器统一保证；配套审计 165 项 RC=0、零 Admitted、
  `Classical_Prop.classic`（排中律宏）零出现（「classical-free」精确指排中律宏零出现，
  非「无任何经典原则」；公理依赖仅 sig_not_dec + sig_forall_dec + fext，Dedekind 实数
  基础设施；外部依赖 mathcomp/Coquelicot 未纳入 165 项审计）。**定位**：反射检查器是
  快速预筛器（充分非必要）；E5'' 复合证书是针对
  特定七带的特制专家系统——两者分工不可混为一谈。**假阴性**：114 阶梯 × 5 族系统扫描，
  通过 35（30.7%）、假阴性 56（全量 49.1%、占拒绝 70.9%，集中于 C=2/3-sparse 与几何奇带）；**E5'' 七带精确
  行和（证书口径①）为 1.2287 > 4/5，检查器判 false 是真阴性（真值超阈）；复合证书
  `champion_e5_composite_certificate` 对 E5'' 下界空洞（单位系数 S=7、coh_e5=14.21、
  下界 −7.21），是宽松复合界，非"紧证书"**。**提取整数范围**：exe 与 Coq
  语义分歧 27/114（23.7%），实验值（≤255、m≤8）均安全，通用界须逐阶梯核算 ∏ pair_den
  < 2^63，彻底消除改用 Zarith 任意精度（future work）。
- **酉不变性接口声明（已机器检查）**：本文「旋转组」（psi-rope）= 基函数乘旋转矩阵；
  旋转是酉变换，不改变内积与范数，故论文 A 的框架界/衰减界/证书**自动覆盖旋转版本**
  （Module UnitaryInvariance：`unitary_invariance_psi_rope_theta` 等均 Qed 零 classic，
  与实验 2×2 旋转矩阵同构 SO(2)≅U(1)）。
- **2D-wide / 3D / 4D 张量阶梯（已完成，扩展方向）**：二维频率格子框架界已全量编译零
  classic（免 H_dom，M_bound_2d_wide 4 = 768）；3D/4D 推广已全量编译（M_bound_3d 4 =
  3968 / M_bound_4d 4 = 19968，常数较 1D 显著保守——定位为上界证书 + 组合性演示）。
- **代码状态**：论文 A 的 z 区 20 探针（grid_ortho + parseval/partial/pairbound/rowsum/
  pairdirichlet/incoherence/row_rip/c4_instance/welch/uncertainty_cr/g8_synthesis_cr/g1_norm_closed/g2_mu_adj + 构造性族 pi_cr_m1a/m1b/sin_cr_m2/sqrt_cr_m3/s7_s9_mono/decidability_premium_cr）已 pro 化并入合并版 `ca_merged_full_25_m2.v`（98187 行，
  67 模块分区，合并编译 MERGE_EXIT=0）——本证书链依赖的 parseval/partial/pairbound/rowsum/
  pairdirichlet 均在合并版内全量验证，证书链验证等级从独立 .vo 升级为合并版全量验证。
- **张力（可发表点）**：带证书方案中的性能领先者（七带）与直接证书（C=4）
  分离——带数与可认证性此消彼长，复合证书弥合二者；认证与外推性能呈温和负相关
  （certified C=4 8× 均值 12.75 vs 未认证七带 12.40）——「带证书」的可证内容止于表示
  稳定性与能量有界，能量控制 → 外推 PPL 增益的桥梁未经形式化。这一反直觉张力本身是
  可发表发现，不掩饰。

## 8. 性能-可证明性帕累托前沿

把「降级」重构为**可审计 AI 的定位**：性能与可证明性构成帕累托前沿（第四列为机器检查
锚——每行证书主张映射到论文 A 的一个 Qed 定理）：

| 方案 | 8× 外推 PPL | 证书（可审计性） | 机器检查锚（论文 A） |
|------|------------|-----------------|----------------------|
| **psi-rope-rand** | **6.45±0.03（旋转族内最优）** | **不在**证书覆盖范围（随机阶梯无几何结构） | 负面：T2b（随机 log-uniform whp 被拒）；正面：`pairwise_inner_bound_probabilistic`（增长 ≥ c² 的结构化随机 whp 获逐对证书） |
| **ALiBi** | **4.47±0.10（全局最优）** | **无证书**（线性偏置核与证书正交） | `linear_bias_no_collision`（非周期核零碰撞端点） |
| **grid** | 25.66±2.22 | 可给 μ=0 精确正交证书，但外推性能严重退化——μ=0 正交证书以外推性能为代价 | `grid_pair_ortho`/`parseval_two` + `grid_first_collision_at_N` |
| **ogrid** | 16.12±1.32 | μ=0 全长度精确正交证书 + 零精确碰撞（可审计），但外推仍差 rand 2.4×——μ=0 正交证书未带来外推优势（被证伪） | `irrational_offset_no_collision` + `collides_iff_rational_witness` + `golden_near_collision`（\｜dφ−m\｜ ≥ 1/(3d)） |
| rope-NTK | 11.54±1.18 | **无证书 / 不可审计**（纯经验修复，破坏阶梯结构） | ——（锚缺席本身即判读） |
| E5'' 七带 | 12.40（次优） | 复合证书（复合界），可审计 | `champion_e5_composite_certificate` |
| C=4 [3,13,53,213] | 12.75（第三） | 紧证书（μ=4/5 有理界），强审计 | `row_sum_3halfs`/`row_bound_C4`（行和 ≤ 2π/7 < 1）+ `witness_sandwich` |

在 AI 安全/合规语境下，**可审计性本身是核心价值**：高风险场景（金融/医疗）中证书的存在
优先于 PPL 代价——带证书方案与无证书上限（ALiBi 4.47）的差距须明确量化：**2.85×（C=4
12.75 vs 4.47）与 2.78×（复合证书七带 12.40 vs 4.47）**（以比值计）——
即 C=4 与七带均高出 ALiBi 约 8 个 PPL 点（12.75−4.47 = 8.28；不得表述为"1-2 个 PPL 点"；
**30% 是 ALiBi 相对 psi-rope-rand 6.45 的领先，属另一对比**）。
本文定位 = **定义可审计位置编码的性能-可证明性前沿**（「可审计性
即价值」），而非「外推性能亚军」。随机侧完整图景（**随机阶梯三面律**）：无增长约束的
随机 ⟹ whp 被拒（T2b）；增长受控的结构化随机 ⟹ whp 逐对证书；连续均匀随机角 ⟹ 实证
最优但零证书（rand 6.45，正面出路留作 future work）。

**证书实用价值的正面论证（审稿要求）**：带证书方案性能劣于无证书 ALiBi/rand，其价值不在
外推 PPL，而在**可审计性提供的独立保证**——(i) **可判定、可复现**：证书由一台带健全性
证明的检查器产生（Coq 内判定 ⟹ 框架界），同一阶梯在任何部署环境得到相同判定，这是
"性能指标无法提供"的保证；(ii) **风险场景适配**：在金融/医疗等需审计的高风险场景，
"表示层能量有界"是可核查的合规声明（如模型输出在受控扰动下有界），即使其外推 PPL 非
最优；(iii) **保守性设计选择**：宁可误拒、绝不放行（充分非必要），使证书在安全语义下
无假阳性——这与"性能最优但零保证"的随机方案构成互补而非替代。该论证限于当前受控设置
（char 级、小模型），推广到大规模 Transformer 仍需未来工作。

## 9. 机制分析（相干衰减、τ/碰撞、KV/量化）

### 9.1 相干衰减率与 E1 消融

定义 Coh(T) = max_{i<j} |⟨ψ_i,ψ_j⟩_T|/(‖ψ_i‖_T·‖ψ_j‖_T) 与 ΔCoh = Coh(T_train) − Coh(T_ood)。
初始实测（稀疏几何四梯）：

| 阶梯 | Coh(512) | Coh(4096) | ΔCoh | ppl(4096) |
|------|----------|-----------|------|-----------|
| C=2 全相位 | 0.0430 | 0.0044 | 0.0387 | 13.84 |
| C=3 | 0.0795 | 0.0035 | 0.0759 | 22.86 |
| C=4 | 0.0317 | 0.0009 | 0.0308 | 12.75 |
| E5'' 七带 | 0.0357 | 0.0110 | 0.0247 | 12.40 |

> **Reviewer P2 note (2026-08-26)**: `Coh(T)` here is the **empirical effective-encoding coherence** (pairwise normalized inner product at evaluation length T, T-dependent, e.g. C=4: 0.0317/0.0009 at T=512/4096) — **not the same quantity as the certificate-layer ψ-Gram coherence** (fixed analytic basis; [3,13,53,213] true max row-sum 0.312, pairwise 0.149, window-independent). The former is the encoding's coherence at the evaluation length, the latter is the basis' analytic coherence; the bridge between them is empirical (§8.2), not formalized. Empirical script `coherence_analysis.py` is provided for reproducibility.

四点上 R²=0.982 的强正相关**未通过 E1 消融扩充的稳健性检验**：13 点后 max 型 R² 崩塌至
0.101。原因：(i) 随机阶梯取整产生重复带 → ΔCoh≡0 退化；(ii) 稠密阶梯在两个长度上都有
近相干带对而饱和。**指标族对照**：median 跨族最强（R²=0.597）但仍非定律。**客观结论**：
ΔCoh 仅在稀疏无重复的几何阶梯族内排序外推表现；「相位剖面作为统一诊断工具」的主张
收缩为「稀疏几何阶梯族内的相关性报告」。

**E1 消融（同批 / C=4 几何基线）**：

| 模式 | T=512 | T=1024 | T=2048 | T=4096 |
|------|-------|--------|--------|--------|
| rope（朴素 RoPE，b32 三 seed） | 4.44±0.08 | 6.77±0.07 | 13.68±1.21 | 25.30±4.63 |
| dense（可学习表，b64 s1337） | 5.42 | 16.91 | 27.70 | 37.74 |
| psi（几何嵌入 C=4，b64 s1337） | 4.74 | 14.34 | 23.68 | 32.01 |
| psi-rand（随机嵌入，b64 s1337） | 4.53 | 13.05 | 25.53 | 35.95 |
| psi-rope（几何旋转 C=4，b64 s1337） | 4.67 | 5.87 | 8.58 | 13.69 |
| psi-rope+rand（排序随机旋转 ≤512，b64 s1337） | 4.59 | 5.15 | 6.76 | 9.82 |
| psi-rope-rand（随机旋转 [3,511] 未排序，b64 s1337） | 4.35 | 4.79 | 5.67 | 7.29 |
| **psi-rope-rand（b32 三 seed）** | **4.48±0.10** | **4.67±0.20** | **5.41±0.27** | **6.45±0.03** |
| psi-rope+rand（b32 三 seed） | 4.50±0.04 | 5.06±0.23 | 7.10±0.79 | 12.33±1.20 |
| psi-lin（线性嵌入，b32 三 seed） | 5.01±0.34 | 10.40±0.33 | 17.93±1.77 | 39.62±4.07 |
| psi-rand（随机嵌入，b32 三 seed，s1337 补跑） | 4.45±0.14 | 10.98±4.01 | 20.72±8.96 | 31.04±12.86 |
| dense-frozen（固定高斯特征，b32 三 seed） | 6.08±0.20 | 12.59±0.22 | 21.57±1.45 | 29.49±2.52 |

### 9.2 τ/碰撞距离机制的判决实验

τ 机制（周期带承载碰撞负债、非周期偏置近零代价逃逸）获 **3 个稳健实证支点 + 1 个单种子候选支点（分协议计数：
eval-only 3 + 真训练 1）**——剪枝方向 1 个：O2 两点 + τ 三剪回测共享同一评估范式
（剪 255/127/63 @8× 全恶化 +3.5–4.5×），不重复计数；网格判决 1 个（grid 8× 25.66，
比 rand 差 3.98×）；offset-grid 1 个（ogrid ≥ grid；ogrid 16.12 比 grid 25.66 低 40%）——前三者为 eval-only；
正式配置温和裁剪 1 个（randmax384 −28%）——真训练：
该机制呈「经验律 + 机器检查碰撞结构」双层——碰撞距离完备刻画、τ 三分、纯网格首碰撞
恰在训练窗（`grid_first_collision_at_N`）、ALiBi 无碰撞端点（论文 A §5.6.4）。
**Protocol note**: pillars 1–3 are eval-only (theta swapped, weights independent of the
ladder); pillar 4 (formal-config gentle trim) is true training (`--rand-max`, train-time
trim) — the two protocols are counted separately and not extrapolated across; mask-eval
(silencing high frequencies at eval time) cannot reproduce the true-training gain, so the
trim gain is a training-adaptation effect (§10.9a pt.6). The τ mechanism is a **candidate
explanation, not an established causal mechanism** (post-hoc trim point; the single-seed
s1337 formal-config trim gain was **not reproduced by the 2026-08-25 multi-seed replication
(s42/s7, 27000 iters: rt448 = rand, 11.76 = 11.76 / 7.67 = 7.67)** — the trim effect is
single-seed seed noise and is downgraded to future work; the fast-config 9-scheme × 10-seed
replication completed 2026-08-25 confirms the main-table direction — rand vs ALiBi t=6.66,
grid vs rand t=11.28, rand vs c3 t=−9.44, rand vs rope t=−6.20 — with the ordering
alibi < rand < t5rel < e5pp < c2 < c4 < c3 < grid < rope fully reproduced at n=10).

### 9.3 KV 逐出与量化（与论文 A 部署证书族接口）

KV 逐出实验（训练长度内逐出无系统代价）与论文 A 的 `kv_eviction_controls_attention`
（TVD ≤ e^{2·dropped_mass} − 1）一致：小被逐质量情形的紧界与实测一致；量化扰动/多头
合成的证书族（`quant_column_controls_attention` / `multihead_output_bound`）为部署级
稳定性提供机器检查保证（论文 A §10）。

## 10. 正式配置复现（tinystories200 · 27000 iters）与 τ 裁剪（τ-trimmed reallocation）

> 数据可信度：batch1/2（3000 iters）与本地 RTX3070 逐位对齐（偏差 ≤0.03）；batch3/4
> 同脚本同语料；云端 T4 与本地的可互换性已在 batch1/2 逐位验证，batch3/4 的绝对数值在其原始执行环境下有效——本地三 seed 重跑实测 @512 存在约 0.12 的系统偏移，跨环境比较需谨慎。正式配置 = tinystories200（200MB）· block 512 /
> batch 32 / 27000 iters ≈ 9.5 epoch。

**batch3：四模式正式对照（s1337，27000 iters）**：

| 方案 | @512 | @1024 | @2048 | @4096 (8×) |
|------|------|-------|-------|------------|
| ALiBi | 2.11 | 2.13 | 2.19 | **2.11** |
| t5rel | 2.11 | 2.15 | 2.31 | **2.75** |
| psi-rope-rand（τ 全保留） | 2.16 | 2.65 | 4.70 | **7.50** |
| e5pp | 2.22 | 2.38 | 6.34 | **14.21** |

**三 seed 独立复现（本地 RTX3070，2026-08-28，tinystories200 语料指纹 1.8e8 确认）**：ALiBi @4096 = 2.11±0.03（2.14/2.07/2.12，与 batch3 一致）、t5rel = 2.74±0.05（2.80/2.73/2.69）——两条基线的正式配置结论独立复现；rand = 5.79±2.36（9.31/4.31/3.76，变异系数 41%）——随机阶梯在深度训练下 seed 方差显著放大，单 seed 数值不具代表性；@512 三方案存在约 0.12 系统偏移（跨环境比较需谨慎）。

**batch4：τ 裁剪验证（对照 rand 7.50）**：

| 方案 | @512 | @1024 | @2048 | @4096 | vs rand |
|------|------|-------|-------|-------|---------|
| randmax256（剪 n>256） | 2.17 | 2.70 | 4.80 | 8.44 | ✗ +0.94 |
| **randmax384（剪 n>384）** | 2.14 | 2.55 | 3.79 | **5.36** | ✓ **−2.14（−28%）** |
| ogrid（grid512+无理偏移 0.6180339887） | 2.27 | 4.67 | 9.64 | 19.30 | ✗ +11.80 |

**判决（τ 裁剪；2026-08-25 multi-seed replication mechanism correction；裁剪语义 = 64 维循环填充下整体维度重组而非单纯高频移除，见 10.9a）**：
1. **τ 裁剪（`--rand-max`）的真实语义是 64 维循环填充的整体重排，其改善为种子特异观察，
   无普遍性**：单种子 s1337 randmax384 @4096 = 5.36 < 7.50（改善 28%）、N*∈[448,480]
   @4096 = 5.15（−31%）；**2026-08-25 多种子复核（s42/s7，27000 iters，rand vs rt448）
   机制修正**：`psi_rope_theta` uses the first 32 wavelengths of the unsorted ladder to
   cyclically fill 64 dims; rt448's effect is seed-dependent — **s42's first-32 contains no
   >448 wavelength, so rt448 is a no-op (64-dim allocation identical to rand; 11.76 = 11.76
   is forced, not a replication test)**; s1337's 491 sits at rank 11, so rt448 re-arranges
   the whole 64-dim allocation (the 5.15 "gain" is the reallocation effect); s7's 452 sits
   at rank 21, same reallocation yet 7.67 = 7.67 (reallocation has no effect on s7) —
   **conclusion: trim = reallocation, the effect is seed-specific with no generality; the
   s1337 gain does not constitute validation** (see 训练数据全量复核-n10完成与τ裁剪多种子复核-20260825.md).
   **Methodology note (reviewer convention)**: the trim point (384/448/480) was fixed
   post-hoc, not a preregistered hypothesis test; the τ mechanism is a candidate
   explanation, not an established causal mechanism (single seed s1337; multi-seed
   replication shows s42 is a no-op invalid sample and s7 shows reallocation has no
   general benefit). Eval-only pruning (O2/τ-triple) and true training (batch4/fine scan)
   are distinct protocols and are counted separately (§9.2).

**2026-08-26 formal-config 3-seed replication (B1 + FOLLOWUP chains, ⚠️ gutenberg · 27000 iters, seeds {1337, 2026, 31415}, batch8/16 downgraded)**:

| scheme | s1337 | s2026 | s31415 |
|--------|-------|-------|--------|
| **alibi** | **4.09** | **4.17** | **4.23** |
| **t5rel** | **4.29** | **4.45** | **4.56** |
| **rand** | **8.67** | **6.44** | **5.71** |
| c4 | 16.37 | 15.52 | 14.53 |
| e5pp | 15.20 | 21.53 | 17.58 |
| c2 | 16.25 | 22.22 | 20.53 |
| grid | 25.91 | 29.20 | 20.59 |
| c3 | 30.53 | 45.39 | 39.38 |
| rope | 35.81 | 37.89 | 38.31 |

**The relative-vs-explicit frequency dichotomy reproduces under deep training (27000 iters, 3 seeds)**: relative-position schemes (alibi 4.09-4.23 / t5rel 4.29-4.56) clearly beat explicit-frequency (c2/c4/e5pp 15-22) and structured (grid/rope/c3 20-45) families — supporting "explicit-frequency families overfit the training-window phase; relative-position families stay flat". **Config-dependent mid-table ordering (honest qualifier)**: quick-config n=10 main table is e5pp<c2<c4 and c3<grid<rope, while formal-config is **c4<e5pp<c2** (s2026/s31415) and c4<c2≈e5pp (s1337) — **c4/c3/rope relative order flips between quick↔formal configs** — the main-table ordering (core data, n=10 replicated 3→10 seeds) is defined on the quick config; the formal config supports only the two-family dichotomy, not mid-table ordering. **Validity note**: all runs were batch-downgraded (GPU 80°C / CPU-util 70% threshold / 2-core affinity after a thermal crash), cooling counts high (513-1332) — per E139 cooling pauses do not alter training values (fixed seeds), data points valid.
> **⚠️ 2026-08-27 corpus-identity erratum (E148)**: this table's data are **gutenberg corpus** (`train=5146368`/`vocab=125`) — the local chains ran `--corpus tinystories200` without `--corpus-dir`, triggering a silent fallback in `load_data` (see 《论文B-数据口径勘误-语料回退-20260827.md》). The earlier validity note's corpus claims were **inverted**: 1.8e8 chars (179870967) is tinystories200, 5.1e6 is gutenberg; rand_s2026 = 6.44 is a re-run **on gutenberg**. **The two-family dichotomy (alibi/t5rel flat vs explicit-frequency/structured degrade) still holds under gutenberg 27000 iters** (consistent with the main experiment's gutenberg 3000 pattern); absolute values are **not directly comparable** to the cloud tinystories200 formal config (§10.9 main table: alibi 2.11 etc., correct corpus). A tinystories200 · 27000 formal re-run is scheduled (all three training chains fixed with `--corpus-dir` + corpus-fingerprint self-check).
2. **过度裁剪有害（单种子观察）**：randmax256 @4096 = 8.44 > 7.50——257–384 区间是外推
   所需的稠密覆盖结构（τ 负债带之外），「剪越多越好」不成立，裁剪点须温和。
3. **ogrid 结构路线在正式配置下亦否定**：@4096 = 19.30（比 rand 差 2.6×），与 Gutenberg
   快速配置（16.12 vs rand 6.45，差 2.5×）方向一致——无理偏移
   结构化频率不优于随机，稠密覆盖（相位完备性）仍是外推性能关键。
4. **主张（降格后）**：psi-rope-rand 定位维持「随机稠密旋转（全相位保留）」；
   `--rand-max` 裁剪的改善为单种子观察（s1337），多种子未复现，列为未来工作——
   不再主张「τ 裁剪（τ-trimmed reallocation）」为正式配置下的已确立机制。
   注：命名由「τ 感知频率选择」降格——裁剪语义是 64 维循环填充下的整体维度重组
   （§10.9a 点 5），「频率选择」命名与「整体重组」语义不符，仅描述经验规律时使用。

### 10.9a k-scan discrimination experiment and trimming-semantics refinement

> Discriminant question (T4 corollary): constant-theory predicts the optimal trim point N*
> is stable in the extrapolation multiple k; depth-theory (variational balance) predicts N*
> moves with k. True training (`--rand-max N`, trim at train time) × 7 trim points ×
> k ∈ {1,2,4,8}, tinystories / block 512 / batch 32 / **3000 iters** / seed 1337
> (local RTX 3070).

**Results** (ppl, CI95 in brackets):

| N \ T | 512 (k=1) | 1024 (k=2) | 2048 (k=4) | 4096 (k=8) |
|---|---|---|---|---|
| 256 | 2.68 | 2.89 | 3.08 | 3.83 [3.77,3.89] |
| 320 | 2.68 | 2.89 | 3.08 | 3.83 [3.77,3.89] |
| 352–448 | 2.68 | **2.86** | **3.04** | **3.80 [3.79,3.81]** |
| 511 (full) | 2.68 | 2.90 | 3.38 | 4.44 [4.43,4.45] |

**Verdicts (k-scan)**:

1. **τ-trim improvement independently replicated**: full (no trim) @8× = 4.44 is
   significantly worse than trimmed (3.80; CIs disjoint, Δ17%) — consistent with the
   formal config (27000 iters: 7.50 vs 5.36) across devices and training budgets.
2. **N* stable in k (weak constant-theory supported)**: the optimal trim region [352,448]
   is stable for all k ≥ 2 (no effect at k=1) — the trim point is set by structure, not by
   the extrapolation multiple; depth-theory (N* moves with k) not supported.
3. **Trim gain grows monotonically with k**: @2× Δ0.04 → @4× Δ0.34 → @8× Δ0.64
   (a T4-corollary prediction).
4. **Trim sensitivity grows with training budget**: over-trim at 256 is insignificant at
   3000 iters (3.83 vs 3.80; CIs overlap) but significant at 27000 iters (8.44 vs 5.36,
   batch4) — overfitting deepens with training, trimming releases more; the 256 effect
   should be stated as a function of training budget, not absolute.
5. **★ Trimming-semantics refinement (64-dim cyclic-fill reallocation)**: psi-rope-rand's
   64-dim positional encoding = **32 pairs of rotation angles** (each pair ↔ wavelength n,
   θ=2π/n), wavelengths drawn from the unsorted random ladder list `ns` (~128 entries),
   filled by **`idx = arange(32) % len(ns)`** (first 32 wavelengths, cycled if longer).
   `--rand-max N` filters the **wavelength list** (keep n ≤ N) — changing list length ⟹ the
   first-32 wavelength set/order may be **wholly re-arranged** (filtered wavelength within
   first 32) or **unchanged** (filtered wavelength beyond position 32 = no-op; model is
   byte-identical to no-trim). Thus trimming is **not** "high-frequency dims removed"
   (dim count is fixed at 64); it re-allocates which wavelengths the 32 pairs receive.
   Wavelength 491 (c=1.043) never enters the 64 dims (rank 91 in the
   unsorted ladder), so full vs rt448 differ by reallocation plus one unused wavelength.
   This fine structure does **not** change the empirical trimming conclusion, but "trim =
   cut high-frequency bands" is a coarse narrative; theory must fix the trimming semantics.
6. **Methodology (mask-eval negative result)**: loading the full-frequency model and
   zeroing high-frequency rotations at eval time (keeping dimension assignment) is
   full-retain-optimal at every k (@8× 4.36 vs silenced 6.94) — it cannot reproduce the
   true-training gain ⟹ the trimming gain is a **training-adaptation effect** (not pure
   geometry); discrimination requires true training.

**Relation to 4/3**: the 27000-iter fine scan of [448,511]
(six points: rt448/460/470/480/491/500, s1337, local RTX 3070 with thermal control v2)
shows 448/460/470/480 all = **5.15** (flat gain region) while **491 = 7.48 and 500 = 7.48**
(≈ full 7.50, no gain) — N* is **exactly [448,480]**, and 4/3 = 384 is a local optimum of
the three-point scan, not the true N*; c* = T/N* ≈ 1.07–1.14 (near T), supporting
"overfitting culprit = bands with c(n)→1". The 491/500 jump closes the semantics loop with
item 5: wavelength 491 (c=1.043) never enters the 64 dims (rank 91 in the unsorted ladder),
so rt491 and rt511 (full) both have no high-frequency removal — only reallocation —
and 7.48 ≈ 7.50 is exactly self-consistent, giving direct numeric evidence for
"τ-trim = 64-dim cyclic-fill reallocation". N* shifts right with training budget
(3000: [352,448] → 27000: [448,480]), supporting the depth-theory phrasing
"the trim point is a setting function, not a universal constant"; the "4/3 is a hidden
constant" hypothesis is **finally rejected**; [480,511] has no wavelength gain (491/500
both flat), so the N* upper bound 480 is locked and no finer scan is needed.

## 11. Related Work

RoPE（Su et al.）、位置插值（Chen et al. 2023）、NTK-aware/YaRN（Peng et al. 2023）、
partial-RoPE、ALiBi（Press et al. 2021）、LongRoPE（进化搜索频率配置——无保证无理论）、
NoPE（Kazemnejad et al. 2023）、Fourier 特征（Tancik et al.）、KERPLE（Chi et al.,
NeurIPS 2022）、FIRE（Li et al., Findings of ACL 2024）、YaRN（Peng et al., ICLR 2024）、
LongRoPE（Ding et al., ICLR 2024）。本文以「频率阶梯相位剖面」为统一分析对象，以
「证书 + 机制」区分于无保证的启发式扩展。

## 12. Limitations & Future Work

**Random-ladder deep-training variance** (added from the 2026-08-28 three-seed rerun): random ladders under 27000-iteration deep training show significantly amplified seed dispersion (5.79±2.36, CV 41%, range 3.76–9.31; cf. ALiBi σ=0.03, t5rel σ=0.05) — their formal-config figures are directional only; this stability differential between random and structured/biased schemes is itself a new empirical dimension.

- **规模**：结论限于 char 级小规模（0.43M–0.63M 参数，统称 ~0.5M 级；BPE 复刻待补）；
  向 GPT-2 small 级迁移的挑战未验证（机制证明而非规模基准）。
- **统计**：主表 3-seed 为原始口径；Welch t（psi-rope-rand vs rope-NTK）p=0.018、
  d=−6.06 为小样本（n=3）方向性结论；对照组（NoPE/dense）单 seed。**n=5 复核已完成
  （2026-08-24，9 方案 × {2026,31415} 补全，tinystories 快速配置 3000 iters，全部
  EXIT=0）**：rand vs alibi @8× t=6.66、grid vs rand t=11.28、rand vs c3 t=−9.44、
  rand vs rope t=−6.20（df≈4）全部高度显著；**n=10 全量复核已完成（2026-08-25，9 方案 ×
  10 种子）**，主表排序与方向性判断全部复现（§4.1）——95% CI 常规呈现，不再列为 future
  work。
- **覆盖梯度**：8→7 带剪枝为单点观察；**τ 三剪回测已补**（剪 E5'' 255/127/63 @8× 全恶化
  +3.5–4.5×，§9.2——预登记预测确认）；更细带数扫描（C=2 的 8/9/10 带截断曲线）为 future
  work。
- **机制**：「ε 不敏感 vs ppl 提升」的机制线索（注意力权重锐度/softmax 熵）未测。
- **证书边界**：论文 A 的证书覆盖基表示稳定性，与 PPL 外推无形式化桥梁；psi-rope-rand
  的随机阶梯在证书范围外。
- **基线**：与 Longformer/BigBird 稀疏变体的系统比较未展开。
- **future work 路线**：① 证书引导的 KV 逐出模拟（`row_dropped_energy_bound` 动态丢弃低
  能量远距 KV——形式化定理直接转为推理加速算法）；② 2D 图像 patch 验证「截断应逐轴独立」
  假说；③ 相位剖面预测力按 OOD 相位混淆指数设计（R² 报告）。

## 13. Conclusion

把位置编码的外推行为还原为**频率阶梯的相位剖面**：截断部分相位带 + 旋转注入 + 覆盖梯度
构成当前最优经验规律；对照组划定其边界——**旋转族内最优是随机稠密旋转角 psi-rope-rand
@4096 = 6.45±0.03（3-seed 确认，击败 NTK-aware 测试时修复 11.54±1.18，p=0.018）**；
**无证书强基线 ALiBi 以 4.47±0.10 保持全局最优（外推平坦），T5 相对偏置为偏置类退化锚点**
——带证书方案与无证书上限的差距由此标明（**2.85×：C=4 12.75 vs ALiBi 4.47；2.78×：
复合证书七带 12.40 vs 4.47，以比值计**——30% 是 ALiBi 相对 psi-rope-rand 6.45 的领先，
属另一对比）。免修复的阶梯方案以 2× 内优势 + 零修改 + 机器
证书为保留的主张。**正式配置复现确认排序并升级主张：τ 裁剪（τ-trimmed reallocation，保留低中频 + 温和
裁剪高频端，最优区 N* ∈ [448,480] 细扫锁定，@4096 = 5.15，491/500 无改善，随训练轮数
右移；N* 为事后选择（非预登记）、单种子 s1337、需独立验证）。k-scan 数据支持两类可判别假说：常数理论（N* 为阶梯结构常数，与外推倍数 k 无关——k=2,4,8 下 [352,448] 稳定）与深度理论（N* 随训练预算右移——3000→27000 iters 的移动支持之），判别实验列为未来工作；把旋转族外推 7.50 → 5.15
（−31%），过度裁剪（256）恶化、结构化频率（ogrid）否定**。NoPE 的平坦曲线揭示位置编码的本质交易（分布内质量 ↔ 外推稳健）；**τ/碰撞距离
机制统一解释排行榜并获 3 个稳健实证支点 + 1 个单种子候选支点（分协议：eval-only 3 稳健；真训练 1 系单种子观察，多种子未复现；候选解释）**及形式化碰撞结构支撑（碰撞 ⟺ 有理、无理偏移零碰撞、ALiBi 无碰撞端点、近碰撞半径 1/(3d)，论文 A §5.6.4）及 **τ 裁剪定理侧机器检查**（覆盖债量化/裁剪证书单调/近重复对爆炸/offset 无关性——z 区 64 Qed，论文 A §5.6.6 CS-11–CS-14）——「交易是周期参数化的属性，非周期偏置近零代价
逃逸」。最强的 4 带阶梯带机器检查的有理框架证书，最强的 7 带阶梯内含可认证子核——
表达性与可证明性在同一阶梯族内共存互补。证伪链与保留假设并报——这条律离终态还有距离，
但变量已被命名、仪器已就位、边界已被明确指出。 **四原子分层证书定理侧（CS-15，`probe_c4_four_atom_cr.v`，2026-08-30，纯构造性轨道：ConstructiveReals 接口、Set 层组合、零经典公理、5 段审计全 Closed、提取物 `c4_four_atom_cr.ml` 经 DkMLNative ocamlc 编译通过）**："第 4 原子 213 未覆盖"由此转化为分层正面贡献——层 1（全族 4 原子）双侧能量稳定：|‖Σ_{j≤3} c_j·u_j‖² − Σc_j²| ≤ μ₄·4·Σc_j²（`c4_four_atom_energy_stability`，CRrip_bound_k M=3 实例化，能量稳定不要求 μ(M+1)<1）；层 2（Q 层窗口判定）：μ₄·4 = 45156/33920 > 1（全族唯一性窗口关闭，精确障碍）而 μ₄·3 = 33867/33920 < 1（3 原子子族窗口开启）——同一常数 μ₄ = 11289/33920 的两个方向判定（`c4_four_atom_layered_certificate` 合成）。 **安全域镜像一致性定理侧（CS-16，`probe_safe_domain.v`，2026-08-30，纯构造性轨道：nat/Z 层、Set 层可计算 Fixpoint、零经典公理、4 段审计全 Closed、提取物 `safe_domain.ml` 经 DkMLNative ocamlc 编译通过）**：反射检查器提取的 63-bit int 镜像与 Coq 语义的一致性由此从经验性 FFI 交叉校验升级为定理保证——乘积上界递推（`zprod_bounded`：全因子 0 < d ≤ D ⟹ 0 < zprod l ≤ D^length l，非平凡归纳核）判定 C=4 分母链 [400; 2080; 3500; 20800; 33920] 落在安全域内：连乘 = 2054520832000000000 < 2^63（`c4_safe_domain`），溢出自由蕴含 mod-2^63 镜像与精确语义一致（`no_overflow_consistent`：0 ≤ p < 2^63 ⟹ p mod 2^63 = p），安全域成员资格由可提取 bool 判定 `safe_domain_bool` 运行时可判定——评审 A1"运行时检查器 int 镜像信任鸿沟"在判定链输入落于安全域时闭合。 **镜像一致性组合定理（Z2b，`probe_z2b_int63mirror.v`，2026-09-01，纯构造性轨道：nat/Z/Q 层、Set 层 sigT 证书、8 段审计全 Closed、提取物 `z2b_int63mirror.ml` + 基准 `z2b_bench` 经 ocamlc 编译运行通过）**：镜像一致性从「域级」细化到「判定级」——`z2b_check63_eq`（安全域内 63-bit 镜像布尔 ≡ 精确布尔；组合 CS-16 安全域与 CS-22 Z 版整数检查器 `zfc_check_spec` 的健全完备 iff，`probe_z_frame_check.v`，2026-08-31：`Qle qsum 4/5 ↔ Z.leb (5·acc) (4·P)`，5 段审计 Closed、Zarith 路线提取）、`z2b_end_to_end_sound`（运行时 true ⟹ `Qle qsum 4/5`——Coq 健全性穿透运行时语义）、`z2b_decision_cert`（sigT 决策证书，可提取）；并给出语义分歧的第一个机器构造反例——[2^63; 4] 行和实例镜像判定 true / 精确判定 false（溢出的可复现构造）。已并入合并版 `ca_merged_full_25_m2.v`（98187 行，77 模块分区）。 **分级证书检查器定理侧（CS-17，`probe_frame_check_graduated.v`，2026-08-30，经典 R 轨道：零 Admitted、公理依赖与主线 165 项审计一致（classic 零出现）、提取物 `frame_check_graduated.ml` 经 DkMLNative ocamlc 编译通过）**：反射检查器的方法论由此从二元判定升级为分层服务——四级证书 L1_tight（二元检查器全过 ⟹ Gershgorin 框架界 [1/5, 9/5]·S）、L2_composite（结构有效且逐对相干界 δ_ij ≤ 1 ⟹ 复合能量界 (S−coh, S+coh)，七带冠军证书由手工组装变自动输出）、L3_energy_only（黑洞对 ⟹ 仅上半能量界）、L4_rejected（结构无效），配健全性定理 `frame_check_graduated_sound`（级 ⟹ 承诺）；计算验证覆盖四级分布——[3,13]→L1、[3,7,15]→L2（评审 G-5"误拒"类近带阶梯由拒绝变降级服务）、[2,3]→L3、乱序/空→L4。 **A-B 桥梁桥墩定理侧（CS-18，`probe_ab_bridge_pier.v`，2026-08-30，经典 R 轨道：零 Admitted、公理依赖与主线 165 项审计一致、classic 零出现；R 层定理不可提取，如实注明）**：论文 A 证书（基表示层）与端到端性能（PPL 实证）的衔接由此获得第一个机器检查的中间桥墩——psi 核 `psi_kernel n m k := re (psi n k *c Cconj (psi m k))` 的相邻位漂移界 `psi_kernel_drift_bound`：|psi_kernel n m k − psi_kernel n m (S k)| ≤ 2/(√n·√m)；截断 TVD 桥 `psi_attention_tvd_trunc`：基核求和窗口从 W 截至 W' 时 |K i j − K' i j| ≤ INR(W−W')·(1/2)（带 ≥2 一致化），实例化 `kernel_drift_controls_attention`（核漂移 dc ⟹ softmax TVD ≤ exp(2·dc·dd) − 1）得 **TVD ≤ exp(2·(INR(W−W')·(1/2))·dd) − 1**（dd = Σ|c_j|）——桥墩已建、桥面（端到端 PPL 影响量化）如实仍为实证轨道。——证书与性能的张力如实记录：证书⟹̸性能（C=4 有证书 12.75 / rand 零证书实证最优 / grid 证书最干净却外推性能严重退化 25.66），证书的价值在可审计的表示稳定性保证，独立于性能指标的决策依据（论文 A 结论张力声明同步）。 **Welch 下界定理侧（G-7，`probe_g7_welch_cr.v`，2026-08-31，纯构造性轨道：ConstructiveReals 接口、零经典公理、六段审计全 Closed、提取物 `g7_welch_cr.ml` 经 DkMLNative ocamlc 编译通过）**：G-8 相图合成（字典最优性 ⟹ 恢复保证）的 Welch 前提由抽象前提升级为已证定理——Frobenius 范数与 Cauchy–Schwarz 不等式路线（避免特征值论证）证明 Welch 下界平方形态 `(INR M − INR N) ≤ INR N·INR(M−1)·μ²`（`g7_welch_lower`，14 Qed，与 G-8 前提签名逐字一致；已并入合并版 `ca_merged_full_25_m2.v`，92506 行 68 模块分区，本地 2.5 全量编译 EXIT=0；实原子版衔接 G-8 抽象相干上界，复原子版列为后续工作）——字典设计最优性（Welch 下界）与恢复保证（唯一性窗口）的相图两端均为机器检查定理。

---

## 参考文献（References）

1. Su, J., Ahmed, M., Lu, Y., Pan, S., Bo, W., Liu, Y. RoFormer: Enhanced Transformer with Rotary Position Embedding. Neurocomputing, 568:127063, 2024.（arXiv:2104.09864, 2021）
2. Chen, S., Wong, S., Chen, L., Tian, Y. Extending Context Window of Large Language Models via Positional Interpolation. arXiv:2306.15595, 2023.
3. bloc97. NTK-Aware Scaled RoPE. Reddit r/LocalLLaMA, 2023-06-30.
4. Press, O., et al. Train Short, Test Long: Attention with Linear Biases Enables Input Length Extrapolation. ICLR 2022.
5. Kazemnejad, A., et al. The Impact of Positional Encoding on Length Generalization in Transformers. NeurIPS 2023, 36:24892-24928.
6. Tancik, M., et al. Fourier Features Let Networks Learn High Frequency Functions in Low Dimensional Domains. NeurIPS 2020, 33:7537-7547.
6a. Peng, B., Quesnelle, J., et al. YaRN: Efficient Context Window Extension of Large Language Models. ICLR 2024.（arXiv:2309.00071）
6b. Ding, Y., et al. LongRoPE: Extending LLM Context Window Beyond 2 Million Tokens. ICLR 2024.（arXiv:2402.13753）
6c. Li, S., et al. Functional Interpolation for Relative Positions Improves Long Context Transformers. Findings of ACL 2024.（arXiv:2310.04418）
6d. Chen, S., et al. KERPLE: Kernelized Relative Position Embedding for Length Extrapolation. NeurIPS 2022.（arXiv:2205.09921）
7. [论文 A 预印本] Wang, B., et al. Certified Sparse Gating and Attention Approximation: An Executable Coq Development. Preprint, Figshare, 2026. DOI: 10.6084/m9.figshare.33312189.（本工作配套，CPP/ITP 方向）
8. [论文 B 预印本] Wang, B., et al. Phase-Truncated Frequency Ladders: Certified, Extrapolation-Robust Positional Encoding. Preprint, Figshare, 2026. DOI: 10.6084/m9.figshare.33312336.
9. [代码仓库] PSA-CertifiedSparseGating. https://github.com/hy7pc8gfmf-dotcom/PSA-CertifiedSparseGating （Artifact：Coq 形式化 + 论文 + 实证 + CI）。

---

## 附录 A 代码-论文声明交叉索引（对齐当前代码基态）

> **代码仓库（Artifact）**：https://github.com/hy7pc8gfmf-dotcom/PSA-CertifiedSparseGating（Coq 形式化 + 实证脚本与数据 + CI）。预印本 DOI：10.6084/m9.figshare.33312336。

| 论文声明 | 代码位置 | 状态 |
|---------|---------|------|
| 实例证书 C=4（μ=4/5） | InstanceCertificate.certified_c4_frame_bounds | ✅ |
| 长度一致性 ∀N≥214 | M4bLengthConsistency.certified_c4_frame_bounds_anyN | ✅ |
| T8 复合证书核 | T8CoreCertificate.certified_t8_core_frame_bounds | ✅ |
| 七带复合界证书 | ChampionCertificate.champion_e5_composite_certificate | ✅ |
| 反射检查器健全性 | FrameCheckInstance.frame_check_instance_sound | ✅ |
| RoPE 酉性桥接 | UnitaryInvariance.unitary_invariance_psi_rope_theta | ✅ |
| 165 项审计（Classical_Prop.classic 零出现） | PSA_audit.v（M1.5 已并入） | ✅ |
| 碰撞刻画 / τ 机制 | z\probe_collision.v（C1–C5）/ probe_tchar.v（T1–T4）/ probe_taudicho.v | ✅（论文 A §8，z 区独立验证） |
| ρ^{−3/2} 行和紧界（C=4 框架界） | z\probe_rowsum.v（row_sum_3halfs / row_bound_C4，23 Qed） | ✅ **已并入合并版** |
| 合并版 | src\ca_merged_full_25_m2.v（98187 行，77 模块分区，探针族全量至 z3b） | ✅ 全量编译 EXIT=0（run20 + run6） |
| 经验数值（主表） | psa_empirical\测试数据\multi_seed_main_table.md | ✅ |
| 偏置对照（ALiBi/T5/grid） | psa_empirical\测试数据\baseline_*.log | ✅ |
| 正式配置 batch3/4 | psa_empirical\测试数据\（云端 T4，与本地逐位对齐） | ✅ |

---

## 附录 B 温控协议

训练环境为 RTX 3070 8GB（CUDA 12.4, torch 2.6.0+cu124），训练治理如下：
- 深度训练（27000 iters 全部链）实际执行参数（v2）：触发 80°C（`--gpu-max 80`）、恢复 75°C（`--gpu-resume 75`）、轮询 0.2s（`--check-interval 0.2`）——0.05s 轮询因 `nvidia-smi` 单次 52ms、20 次/秒占满单核（探测自身成热源触发 CPU 冷却死循环）而弃用；协议演进：早期 v1（85/78）在 rt256 step 835 热过载宕机后收紧为 v2。早期 Gutenberg 快速配置采用 80/70/0.5s/60s 口径（CPU 利用率上限 90%）。
- 冷却暂停的实现为训练循环级轮询挂起：RNG 与优化器状态驻留内存不被重置，学习率调度按已完成迭代步数推进——暂停只改变墙钟耗时，不改变计算轨迹（2026-08-25/26 两次独立复现数值一致为实证佐证）。
- 一次只跑一件 GPU 任务（训练或 Coq 编译，不并行）；每次冷却暂停记录到日志，**暂停不
  改变计算轨迹**（确定性协议——rope 在两种温控协议下逐位复现，损失到小数点后四位；实现层面：冷却暂停为训练循环级轮询挂起，随机数生成器与优化器状态驻留内存不被重置，学习率调度按已完成迭代步数推进——暂停只改变墙钟耗时，不改变任何计算轨迹）。
- 历史宕机教训（4 次）：空闲基线 56–58°C，死机临界 ~85°C；训练每步 `guard.check()`，
  >85°C 立即杀进程。

## 附录 C′ 掩码评估完整表（k_scan_record，27000 iters）

| N \ T | 512 | 1024 | 2048 | 4096 |
|---|---|---|---|---|
| full | 2.69 | 2.87 | 3.42 | 4.36 |
| 224–320 | 3.33 | 4.63 | 7.48 | 11.77 |
| 352–480 | 2.83 | 3.38 | 4.68 | 6.94 |
| 511 | 2.69 | 2.87 | 3.42 | 4.36 |

Masking monotonicity ("more bands silenced, worse extrapolation") holds at every
evaluation length; the 352–480 window sits between full and 224–320 at all
lengths — the complete evidence behind §10.9a point 6 (pruning gains are
training-adaptation effects, not purely geometric ones).

## 附录 C 复现清单

> **代码仓库（Artifact）**：https://github.com/hy7pc8gfmf-dotcom/PSA-CertifiedSparseGating
> ——配套论文 A 的 Coq 形式化 + 本文实证脚本与数据（psa_empirical/、data/）+ CI。预印本
> DOI：10.6084/m9.figshare.33312336。
> **预登记说明（审稿口径）**：本文「预登记判据」为**内部文档**（本地留存，无
> OSF/AsPredicted 公开时间戳）——读者不可将其视为可验证的公开预登记；文中「预登记预测
> 确认」均指该内部文档的判据，投稿时可选择 deposit 公开后补链接。

- 数据：Gutenberg 5.1M 字符（词表 125），`gutenberg_corpus.txt`。
- 训练：`python length_extrap.py --block 512 --batch 32 --gen-c 4 --bands 0 --seed S
  --psi-variant none --modes psi [--rope-rand] --gpu-max 79 --gpu-resume 69 --cpu-util-max 90
  --check-interval 0.5 --cooldown 60`（`--psi-variant rand/lin` 为嵌入变体；
  `--modes psi-rope` 为旋转变体）。
- **正式配置复现（tinystories200 · 27000 iters ≈ 9.5 epoch）**：语料 `tinystories200`；
  同参数但 `--iters 27000`；τ 裁剪实验加 `--rand-max 384`（randmax384，剪 n>384）/
  `--rand-max 256`（randmax256）/ `--ogrid`（grid512 + 无理偏移 0.6180339887）；日志
  `baseline_randmax{256,384}_s1337.log`、`baseline_ogrid_s1337.log`（云端 T4，batch3/4，
  与本地逐位对齐）。
- 偏置类（b32 三个种子）：ALiBi `--modes alibi`；T5 相对偏置 `--modes t5rel`；日志
  `baseline_alibi_s{1337,42,7}.log` / `baseline_t5rel_s{1337,42,7}.log`。
- 评估：eval-only 频率缩放（NTK/PI）；KV 逐出 `kv_eviction.py`；相干分析
  `coherence_analysis.py`。
- 数据文件：`psa_empirical\测试数据\`（ms_*/ms2_*/ntk_*/kv_*/ps2d_*/coherence_*）。
- 证书侧：`PSA_framework.v`（165 项审计）、`psa_guard.exe`（反射检查器，24/24 FFI）。

## 附录 C″ Seed-Robustness Convergence Table (n=3 → 5 → 10)

n=10 full replication (9 schemes × 10 seeds {1337,42,7,2026,31415,2718,1618,31416,12345,999}, 2026-08-25, @4096):

| Scheme | n | Mean | Median | Range | Rank |
|---|---|---|---|---|---|
| alibi | 10 | 2.63 | 2.62 | 2.53–2.71 | 1 |
| rand | 10 | 4.00 | 3.90 | 3.40–4.96 | 2 |
| t5rel | 10 | 6.60 | 6.47 | 6.08–7.17 | 3 |
| e5pp | 10 | 8.09 | 7.78 | 7.07–9.29 | 4 |
| c2 | 10 | 9.30 | 9.06 | 7.54–11.80 | 5 |
| c4 | 10 | 10.22 | 10.21 | 8.65–11.63 | 6 |
| c3 | 10 | 22.23 | 20.89 | 15.22–31.65 | 7 |
| grid | 10 | 26.97 | 26.61 | 19.08–30.39 | 8 |
| rope | 10 | 31.16 | 25.53 | 23.11–46.40 | 9 |

Convergence: the ordering alibi < rand < t5rel < e5pp < c2 < c4 < c3 < grid < rope
replicates at every stage n=3 → 5 → 10 with no transpositions; the 5 new seeds
differ from the original 5 by ≤0.8 in mean with no directional drift. Welch t,
Cohen's d and Holm-corrected values are provided in the artifact.

## 附录 D 常见问题与边界澄清

本节回答评审与读者最可能提出的五类边界问题；所有答案与正文 §5、§7、§8 及配套论文 A
的口径一致，未引入正文之外的新主张。

**Q1：`champion_e5_composite_certificate` 对剪掉 511 带后的 6 带版本是否成立？**

答：未证明，且当前实证与证书范围一致。8 带全相位版 [3,7,15,31,63,127,255,511] 剪掉
覆盖恰为 1.0 的 511 带得到 E5'' 七带 [3,7,15,31,63,127,255]（覆盖梯度主结果）；再剪 127
才是 6 带版。复合证书定理的语句为 `length coeffs = 7 → (S − coh_e5) ≤ ‖F‖² ≤ (S + coh_e5)`，
其相干表是 C(7,2)=21 对上三角 δ 界（`e5_bands` 硬编码），代码中无 6 带版本——需重新推导
C(6,2)=15 对 δ 表并新建定理。实证侧亦无 6 带训练点；根据 §9.2 的 τ 三剪实验，剪掉 127
带后的 6 带版本其 8× 外推 PPL 为灾难性的 57.61，远差于七带版本（12.40）——**因此该版本
无论从形式化角度还是实证角度均不被支持**。另：复合证书的装配机制本身是阶梯无关的——
对任意给定阶梯，只需构造其对相干加权上界即可套用同一骨架。

**Q2：框架界 (1±μ)S 如何转化为 PPL 界？**

答：没有直接转化。论文 A 含两类独立的机器证书：`certified_attention_approx` 对逐行丢弃
谱能量 ε 给出注意力输出扰动界（涉及 ε 与注意力），而 `champion_e5_composite_certificate`
是基表示稳定性界（不涉及 ε 或注意力）。「框架界 → logits 扰动 → softmax 输出 → PPL」的
跨层合成明确列为未来工作（论文 A §10）。本文「带机器证书」的精确含义是表示层（基的平方
范数/能量）有机器检查保证，而非端到端 PPL 上界。

**Q3：psi-rope-rand 的随机阶梯是否可能被 `frame_check_instance` 通过？**

答：个别样本可能通过，但不改变定位。系统扫描（114 阶梯 × 5 族）中 E1 随机族 3/18 通过
（16.7%），且该族多为真负（精确相干行和 > 4/5）。即便某随机样本通过，检查器的健全性只
保证该阶梯的基框架界（μ≤4/5），不保证任何外推 PPL 性质。**表述修正**：随机阶梯在论文 A
中的准确状态是「无框架界（μ≤4/5 行和判定）陈述」——它持有 ℓ² 线性无关证书
（`psi_linear_independent` 对任意 NoDup 阶梯成立），并非「无可证陈述」；其实证最优来自
旋转角的稠密相位覆盖（128 角铺满 [3,511]），与几何基的框架判定正交。另注：网格角度路线
（θ_t = 2πm_t/N，m_t 互异）可对任意随机角度集给出精确正交证书（μ=0，于训练与所有被评估
外推长度成立）；该方向定理块已完成——精确正交、能量守恒等式（Parseval 恒等式）、碰撞
距离完备刻画（碰撞 ⟺ 角度有理；纯网格恰 N；无理偏移永不碰撞）、窗口无关 Dirichlet 部分
和界、黄金偏移近碰撞下界 |dφ−m| ≥ 1/(3d)，零 Admitted。配套实验 offset-grid（θ=2π(α+m/512)，
α=黄金比）3 个种子已完成（@4096 16.12±1.32）：ogrid ≥ grid 确认 + **μ=0 正交证书未带来
外推优势**（仍差 rand 2.4×、ALiBi 3.6×——稠密覆盖才是外推性能关键）。**ALiBi 对照注**：
ALiBi 线性偏置严格单调、非周期，碰撞距离 = ∞（任意距离无精确碰撞）——与阶梯族的周期
端点谱形成互补，其「无证书强基线」定位与 τ 语义（无负债带）一致。

**Q4：酉不变性是否覆盖注意力 logits？**

答：否。论文 A §5.3 明确限定：酉不变性证明适用于特征表示的范数层（基展开的平方范数/
内积）；不保证学习到的 Q/K 投影下注意力 logits 在该旋转下不变，亦非旋转后注意力机制的
证书。桥接限于「基函数的能量范数」层面。

**Q5：论文 A 的证书是否「解释」了论文 B 的 PPL 改善？**

答：否。论文 A 与本文同口径：`certified_attention_approx` 的输出界对谱能量 ε 单调，而剪掉
511 带的 ε 几乎不变、ppl 却显著改善——增益机制不在当前形式化的谱能量通道内（候选：绝对
相位混叠、softmax 分母数值稳定性，均被现框架抽象掉）。论文 A 的机器可证内容止于「表示
稳定性 + 能量有界」；从能量控制到外推 PPL 增益的桥梁依赖本文的覆盖梯度经验观察，未经
形式化。两篇论文对此的边界表述一致。

