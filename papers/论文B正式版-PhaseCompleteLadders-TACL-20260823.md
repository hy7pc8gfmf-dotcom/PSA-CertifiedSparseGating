# Phase-Truncated Frequency Ladders: Empirical Extrapolation and a Certified Representation-Stability Core

> 正式版（2026-08-23，对齐当前代码基态）。来源：论文 B 草稿清洗（删除会话/评审/版本内部注记），
> 实验数据不变；配套论文 A（Coq 形式化）代码状态按 2026-08-23 基态（z 区 7 探针并入合并版、
> 合并编译 MERGE_EXIT=0）。投稿方向：TACL/Findings（实证 + 可审计性）。

---

## Abstract (EN)

Positional encodings degrade sharply beyond their training length. We study length
extrapolation through the lens of the *frequency ladder* — the multiset of rotation angles
(or additive features) a positional scheme employs. On a controlled char-level benchmark
(~0.5M parameters, T_train=512, 3 seeds), we find: (1) truncating a Fourier ladder to its
*phase-complete* bands (n_j < T_train) dramatically improves extrapolation across three
ladders; (2) RoPE-style rotation on a phase-truncated ladder extrapolates far better than
vanilla RoPE; the best within the rotation family is a *random dense rotation ladder*
(psi-rope-rand, [3,511] random angles, 6.45±0.03 at 8×, 3 seeds) — 44% below the 3-seed
NTK number (11.54±1.18, p=0.018, d=−6.06) — while an uncertified strong baseline, ALiBi,
reaches 4.47±0.10 at 8× (31% lower, flat extrapolation); the gap between certified schemes
and this uncertified ceiling is explicitly quantified; (3) dropping the *marginally*
covered band (coverage 1.0) strictly improves all extrapolation lengths across all seeds —
a coverage *gradient*, not a threshold; (4) the certified 4-band ladder [3,13,53,213]
carries a machine-checked rational frame certificate (μ = 4/5, Coq), and the 7-band
geometric ladder contains a certifiable sub-core — a composite certificate
(frame core + energy-budget margin) we formalize: `champion_e5_composite_certificate`
proves (S − coh_e5) ≤ ‖F‖² ≤ (S + coh_e5), a **basis-representation stability
certificate**, orthogonal to the empirical champion (the random ladder of psi-rope-rand
lies outside the certificate scope); (5) honest controls: NTK-aware rescaling beats
phase-truncated rotation at 4–8× — our surviving claim is *no-test-time-surgery, no
per-length recalibration, and certificates*, not absolute extrapolation supremacy. Under
the formal configuration (tinystories200 · 27000 iters), **τ-aware frequency selection** —
keeping low/mid frequencies and gently trimming the high-frequency tail (optimal cutoff N* ∈ [448,480], shifting right with training depth) —
improves the rotation-family extrapolation from 7.50 to 5.36 (−28%), while over-trimming
(256) hurts and structured-frequency offsets (ogrid) are rejected. We document our
falsified hypotheses alongside the surviving ones, and propose the ladder *phase profile*
as a diagnostic for arbitrary positional encodings.

---

## 1. Introduction

长上下文是前沿模型主战场；现有上下文扩展方法（PI / NTK-aware / YaRN / partial-RoPE /
ALiBi）全为启发式，缺一个统一变量。本文引入**频率阶梯**作为位置编码的统一分析对象：
位置编码 = 角度多重集 {θ_t}（旋转）或频率集 {n_j}（加性），外推行为由阶梯的**相位剖面**
（每带覆盖倍数 T_train/n_j、可见带数、填充均匀性）决定。

**贡献**：(i) **相位截断**——剪掉超训练窗的相位带显著改善外推；(ii) **旋转注入**——
相位截断阶梯上的 RoPE 式旋转远优于朴素 RoPE；(iii) **覆盖梯度**——剪掉覆盖恰 1.0 的
边缘带在全部 OOD 长度、全部 seed 上严格改善（梯度而非阈值）；(iv) **τ/碰撞距离机制**——
统一解释排行榜（周期带承载碰撞负债、非周期偏置近零代价逃逸），获 7 个正向判决；
(v) **性能-可证明性前沿**——带证书方案与无证书上限的差距被如实量化，可审计性本身作为
价值主张；(vi) **τ 感知频率选择**——正式配置下保留低中频 + 温和裁剪高频端把旋转族
外推 7.50 → 5.15（−31%）。

**与配套论文 A（Coq 形式化）的关系**：本文实证验证论文 A 形式化框架（同一阶梯族）的
适用性；论文 A 的框架界/能量界为「免修改 + 证书」定位提供理论支持——两文共享阶梯对象，
主张正交：形式化保「表示稳定性/能量有界」，实证报「外推 PPL」。证书与 PPL 外推之间
**无形式化桥梁**（经验观察，如实声明）。

## 2. 实验设置与协议

- **模型**：char 级 GPT（~0.5M 参数，4 头，head dim 32，16 旋转维/头），Gutenberg
  5.1M 字符（vocab 125），T_train=512，3000 iters，batch 32，**seeds {1337, 42, 7}**
  （主结果均报 3-seed 均值±std）。
- **确定性协议**：rope 在两种温控协议下逐位复现（损失到小数点后四位）——同 seed 同
  batch 的跨 run 比较合法。
- **评估**：T ∈ {512, 1024, 2048, 4096}（1×/2×/4×/8×），val ppl。

## 3. 频率阶梯：统一形式化

- **旋转机制**：位置编码 = 角度多重集 {θ_t}，核为逐槽和 Σ_t w_t·cos(d·θ_t)（带间无交叉项）。
- **加性机制**：φ(k) = [cos/sin(2πk/n_j)]，含绝对相位项。
- **阶梯族**：生成器 next = C·n+1；C=2 给出梅森列 n_j = 2^{j+2}−1（近似二进）。
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
为限，对照组单 seed 如实标注。）

**偏置类对照表（b32 三个种子，T_train=512）**：

| 方案 | 512 (分布内) | 1024 | 2048 | 4096 (8×) |
|------|---------|------|------|-----------|
| ALiBi（线性偏置） | 4.64±0.02 | 4.57±0.05 | 4.59±0.10 | **4.47±0.10** |
| T5 相对偏置（32 桶） | 5.32±0.07 | 5.46±0.05 | 6.56±0.02 | 8.48±0.60 |
| psi-rope-rand（旋转族内最优） | 4.48±0.10 | 4.67±0.20 | 5.41±0.27 | 6.45±0.03 |
| **grid（θ=2πm/512，log-uniform）** | 4.57±0.12 | 10.90±0.78 | 19.01±1.21 | 25.66±2.22 |

**偏置类判决**：
- **ALiBi @8× = 4.47±0.10**：对 psi-rope-rand（6.45±0.03）领先 31%——**「性能最优方案」
  归属移出旋转族**；psi-rope-rand 收缩为「旋转族内最优」。ALiBi 无任何形式化保证（线性
  偏置核与论文 A 证书正交），保留主张为「带证书方案中的最优 + 零测试时修改 + 免逐长度
  重调参」。**T5 相对偏置**：偏置类退化锚点（5.32→8.48，+60%），证伪「可训练偏置 → 好外推」。
- **grid 判决**：分布内 grid 4.57 ≈ rand 4.48/ALiBi 4.64 几乎持平，但 2× 即崩（10.90 vs
  4.67），8× 达 25.66——比 rand 差 3.98 倍。τ/碰撞机制解释：纯网格 m 为奇数时原子有效周期
  恰 512，自碰撞恰在训练窗边界、τ≈1 负债带 → 外推灾难；offset-grid（无理偏移消碰撞）
  是理论上的唯一逃逸方向（@4096 16.12±1.32——ogrid ≥ grid 确认、证书免费性被证伪）。

**对照组三判决**：
- **rope-NTK @8× = 10.74**：对预登记单 seed 基线（psi-rope C=4 13.06）领先 21.6%，对
  3-seed 均值 C=4（12.75）领先 15.7%、对均值最优七带（12.40）领先 13.4%——**绝对外推
  主张收缩**，保留「2× 内仍胜（4.75 vs 5.11）+ 零测试时修改 + 免逐长度重调参 + 带机器
  证书」。rope-NTK 为纯经验修复、无任何形式化保证（频率重缩放破坏阶梯结构，论文 A 的
  证书侧对其无可证陈述）。
- **NoPE 平坦曲线**：分布内灾难性差（9.06，位置信息必要性确认），但退化仅 1.27×（vs
  全部位置方案的 2.7-2.9×）——「位置方案用分布内 2× 优势换取外推脆弱性」是本基准的核心
  trade-off 陈述。
- **rope-PI 无微调惨败**（37.87）——测试时修复不是免费午餐，NTK 是唯一有效形态。

**阶梯族内判决**：
- **七带阶梯 [3,7,15,31,63,127,255] 全程均值最优**（2×/4×/8× 全列第一）。
- **覆盖梯度 3-seed 单调确认**：剪掉覆盖恰 1.0 的 511 带，全部 OOD 长度、全部 seed 严格
  改善（8×: 13.84→12.40；分布内仅付 0.07）——**边缘覆盖带是 OOD 纯负债**。
- **C=3 分层**：s1337 的 28.97 是坏抽签（族内 s42/s7 为 19.48-20.12），但即便好 seed，
  C=3 在 8× 仍全 seed 劣于其余三族——间距带中等程度的确定性远程代价（约 +60%）+ 显著
  放大的 seed 方差（8× std 5.30 vs 其余族 0.25-0.74）。

### 4.2 加性组

| T | psi-full C=3 | psi-trunc C=2 | psi-trunc C=3 | psi-trunc C=4 |
|---|------|------|------|------|
| 512 | 4.38 | 4.67 | 4.64 | 4.77 |
| 4096 | 39.69 | **18.43** | 29.70 | 23.89 |

- psi-trunc C=2 在 4×/8× 上击败 rope（12.15 vs 13.68；18.43 vs 25.30）；
- 全梯 vs 截断：三种阶梯上截断收益三次复现（C=3: 39.69→29.70，−25%）。

## 5. 经验规律（Empirical Patterns）

> 以下为**强经验规律**（覆盖梯度、截断效应、旋转注入），其根本机制（除「长带死重」外）
> **机制未明**——如实标注为「经验规律，机制未明」，不作「机制发现」主张；与论文 A 的
> 形式化贡献（框架界/衰减界）之间无解释性桥梁。

1. **截断效应**（稳健，3 次复现）：剪掉部分相位带恢复外推。
2. **相对性效应**（稳健）：同阶梯下旋转优于加性。
3. **二进身份 + 覆盖梯度**（3-seed 确认）：C=2 阶梯 = 「RoPE 砍掉 OOD 尾巴」。归因注记
   （如实边界）：配套形式化不主张解释本经验律——`certified_attention_approx` 的输出界对
   谱能量 ε 单调，而剪掉 511 带的 ε 几乎不变（该带窗内范数→0），ppl 却 13.84→12.40 远超
   噪声——**增益机制不在形式化的谱能量通道内**（候选：绝对相位混叠、softmax 分母数值
   稳定性，均被现框架抽象掉，future work）；形式化的贡献限于稳定性检验（剪枝不破坏框架
   界、μ 不变——排除崩溃风险）。
4. **长带死重**：128 带中 120 个 n_j>512 带对训练损失贡献 ≈ 0（1.4111 vs 1.4120）——
   与理论预测（窗口内范数→0）一致。
5. **填充均匀性无关**：七带填 16 槽（16 mod 7 = 2，不均匀）仍居最优——均匀性被正反两
   面证据排除。
6. **跨维度推测**：1D 覆盖梯度在 N 维语境下 = 「剪掉任意维度过长的轴」；张量积证书给出
   精确升维公式 M_bound^{(N)} = (C³/2)·((1+4K_C)^N − 1)（C=4 时底数 = 5；N=2: 768、
   N=3: 3968、N=4: 19968，均已全定理级证）。

## 6. 假设证伪链（方法学贡献）

- **双覆盖律（已撤回）**：原「同时剪两带必改善」被反例证伪。
- **偶填充假说（已杀死）**：均匀填充被 16 mod 7 = 2 仍最优的正反两面证据排除。
- **E1 消融证伪**：psi-rope-rand（随机旋转）反超几何旋转（假说证伪）；dense-frozen
  「瓶颈全解释」分支证伪（分布内掉质量 6.08 vs 4.5-5.0）；psi-lin 最差（39.62±4.07 @8×）。
- **相干衰减预测因子（证伪其跨族普适性）**：ΔCoh 在稀疏几何阶梯族内 4 点 R²=0.982，
  但 E1 消融扩充至 13 点后 max 型 R² 崩塌至 0.101——**没有任何相干聚合器是跨族通用预测
  因子**（最优 median 也仅 R²≈0.6），原 R²=0.982 是小样本过拟合。

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
- **反射检查器**：`frame_check_instance` 对任意阶梯做 μ≤4/5 的可判定有理判定（提取为
  OCaml/FFI，24/24 自测），健全性主定理 `frame_check_instance_sound` 已 Qed——「带机器
  证书」由一台自带健全性证明的运行时检查器统一保证；配套审计 165 项 RC=0、零 Admitted、
  全部零经典排中。**定位**：反射检查器是快速预筛器（充分非必要）；E5'' 复合证书是针对
  特定七带的特制专家系统——两者分工不可混为一谈。**假阴性**：114 阶梯 × 5 族系统扫描，
  假阴性 56（全量 49.1%、占拒绝 70.9%，集中于 C=2/3-sparse 与几何奇带）；E5'' 七带精确
  行和仅 0.135 ≤ 4/5（实质可认证，复合证书即其紧证书）。**提取整数范围**：exe 与 Coq
  语义分歧 27/114（23.7%），实验值（≤255、m≤8）均安全，通用界须逐阶梯核算 ∏ pair_den
  < 2^63，彻底消除改用 Zarith 任意精度（future work）。
- **酉不变性接口声明（已机器检查）**：本文「旋转组」（psi-rope）= 基函数乘旋转矩阵；
  旋转是酉变换，不改变内积与范数，故论文 A 的框架界/衰减界/证书**自动覆盖旋转版本**
  （Module UnitaryInvariance：`unitary_invariance_psi_rope_theta` 等均 Qed 零 classic，
  与实验 2×2 旋转矩阵同构 SO(2)≅U(1)）。
- **2D-wide / 3D / 4D 张量阶梯（已完成，扩展方向）**：二维频率格子框架界已全量编译零
  classic（免 H_dom，M_bound_2d_wide 4 = 768）；3D/4D 推广已全量编译（M_bound_3d 4 =
  3968 / M_bound_4d 4 = 19968，常数较 1D 显著保守——定位为上界证书 + 组合性演示）。
- **代码状态（2026-08-23）**：论文 A 的 z 区 7 探针（含本证书依赖的 pairbound/rowsum/
  pairdirichlet/parseval/partial）已 pro 化并入合并版 `ca_merged_full_24.v`（75702 行，
  40 模块，合并编译 MERGE_EXIT=0），证书链验证等级从独立 .vo 升级为合并版全量验证。
- **张力（可发表点，如实呈现）**：带证书方案中的性能领先者（七带）与直接证书（C=4）
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
| **grid** | 25.66±2.22 | 可给 μ=0 精确正交证书，但外推崩溃——证书免费性以外推为代价 | `grid_pair_ortho`/`parseval_two` + `grid_first_collision_at_N` |
| **ogrid** | 16.12±1.32 | μ=0 全长度精确正交证书 + 零精确碰撞（可审计），但外推仍差 rand 2.4×——证书免费性被证伪 | `irrational_offset_no_collision` + `collides_iff_rational_witness` + `golden_near_collision`（\｜dφ−m\｜ ≥ 1/(3d)） |
| rope-NTK | 11.54±1.18 | **无证书 / 不可审计**（纯经验修复，破坏阶梯结构） | ——（锚缺席本身即判读） |
| E5'' 七带 | 12.40（次优） | 复合证书（复合界），可审计 | `champion_e5_composite_certificate` |
| C=4 [3,13,53,213] | 12.75（第三） | 紧证书（μ=4/5 有理界），强审计 | `row_sum_3halfs`/`row_bound_C4`（行和 ≤ 2π/7 < 1）+ `witness_sandwich` |

在 AI 安全/合规语境下，**可审计性本身是核心价值**：高风险场景（金融/医疗）中证书的存在
优先于 1-2 个 PPL 点。本文定位 = **定义可审计位置编码的性能-可证明性前沿**（「可审计性
即价值」），而非「外推性能亚军」。随机侧完整图景（**随机阶梯三面律**）：无增长约束的
随机 ⟹ whp 被拒（T2b）；增长受控的结构化随机 ⟹ whp 逐对证书；连续均匀随机角 ⟹ 实证
最优但零证书（rand 6.45，正面出路留作 future work）。

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
| psi-rope（几何旋转 C=4，b64 s1337） | 4.67 | 5.87 | 8.58 | 13.69 |
| **psi-rope-rand（b32 三 seed）** | **4.48±0.10** | **4.67±0.20** | **5.41±0.27** | **6.45±0.03** |
| psi-rope+rand（b32 三 seed） | 4.50±0.04 | 5.06±0.23 | 7.10±0.79 | 12.33±1.20 |
| psi-lin（线性嵌入，b32 三 seed） | 5.01±0.34 | 10.40±0.33 | 17.93±1.77 | 39.62±4.07 |

### 9.2 τ/碰撞距离机制的判决实验

τ 机制（周期带承载碰撞负债、非周期偏置近零代价逃逸）获 **7 个正向判决**：
O2 两点 + τ 三剪回测（剪 255/127/63 @8× 全恶化 +3.5–4.5×）+ 网格判决（grid 8× 25.66，
比 rand 差 3.98×）+ offset-grid（ogrid ≥ grid）+ 正式配置温和裁剪（randmax384 −28%）。
该机制呈「经验律 + 机器检查碰撞结构」双层——碰撞距离完备刻画、τ 三分、纯网格首碰撞
恰在训练窗（`grid_first_collision_at_N`）、ALiBi 无碰撞端点（论文 A §5.6.4）。

### 9.3 KV 逐出与量化（与论文 A 部署证书族接口）

KV 逐出实验（训练长度内逐出无系统代价）与论文 A 的 `kv_eviction_controls_attention`
（TVD ≤ e^{2·dropped_mass} − 1）一致：小被逐质量情形的紧界与实测一致；量化扰动/多头
合成的证书族（`quant_column_controls_attention` / `multihead_output_bound`）为部署级
稳定性提供机器检查保证（论文 A §10）。

## 10. 正式配置复现（tinystories200 · 27000 iters）与 τ 感知频率选择

> 数据可信度：batch1/2（3000 iters）与本地 RTX3070 逐位对齐（偏差 ≤0.03）；batch3/4
> 同脚本同语料，云端 T4 与本地可互换。正式配置 = tinystories200（200MB）· block 512 /
> batch 32 / 27000 iters ≈ 9.5 epoch。

**batch3：四模式正式对照（s1337，27000 iters）**：

| 方案 | @512 | @1024 | @2048 | @4096 (8×) |
|------|------|-------|-------|------------|
| ALiBi | 2.11 | 2.13 | 2.19 | **2.11** |
| t5rel | 2.11 | 2.15 | 2.31 | **2.75** |
| psi-rope-rand（τ 全保留） | 2.16 | 2.65 | 4.70 | **7.50** |
| e5pp | 2.22 | 2.38 | 6.34 | **14.21** |

**batch4：τ 裁剪验证（对照 rand 7.50）**：

| 方案 | @512 | @1024 | @2048 | @4096 | vs rand |
|------|------|-------|-------|-------|---------|
| randmax256（剪 n>256） | 2.17 | 2.70 | 4.80 | 8.44 | ✗ +0.94 |
| **randmax384（剪 n>384）** | 2.14 | 2.55 | 3.79 | **5.36** | ✓ **−2.14（−28%）** |
| ogrid（grid512+无理偏移 0.6180339887） | 2.27 | 4.67 | 9.64 | 19.30 | ✗ +11.80 |

**判决（τ 感知频率选择）**：
1. **τ 裁剪假设在正式配置下兑现（温和版）**：randmax384 @4096 = 5.36 < 7.50（改善 28%）——
   剪掉最高频 385–511（约 14% 相位）显著提升外推。
2. **过度裁剪有害**：randmax256 @4096 = 8.44 > 7.50——257–384 区间是外推所需的稠密覆盖
   结构，「剪越多越好」不成立。
3. **ogrid 结构路线在正式配置下亦否定**：@4096 = 19.30（比 rand 差 2.6×）——无理偏移
   结构化频率不优于随机，稠密覆盖（相位完备性）仍是外推性能关键。
4. **主张升级**：psi-rope-rand 定位升级为**「τ 感知频率选择：保留低中频 + 温和裁剪高频端
   （最优区 N* ∈ [448,480]）」**——与 ALiBi 的差距从 3.55× 缩至 2.44×。

### 10.9a k-scan discrimination experiment and trimming-semantics refinement (2026-08-23, local replication)

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
5. **★ Trimming-semantics refinement (64-dim cyclic-fill reallocation)**: `psi_rope_theta`
   fills 64 dims cyclically (idx = arange(64) % len(ns)) — trimming changes the wavelength
   list length ⟹ the **whole 64-dim allocation is re-arranged**, not simply "high-frequency
   dims removed"; wavelength 491 (c=1.043) never enters the 64 dims (rank 91 in the
   unsorted ladder), so full vs rt448 differ by reallocation plus one unused wavelength.
   This fine structure does **not** change the empirical trimming conclusion, but "trim =
   cut high-frequency bands" is a coarse narrative; theory must fix the trimming semantics.
6. **Methodology (mask-eval negative result)**: loading the full-frequency model and
   zeroing high-frequency rotations at eval time (keeping dimension assignment) is
   full-retain-optimal at every k (@8× 4.36 vs silenced 6.94) — it cannot reproduce the
   true-training gain ⟹ the trimming gain is a **training-adaptation effect** (not pure
   geometry); discrimination requires true training.

**Relation to 4/3 (updated 2026-08-23)**: the 27000-iter focused scan (rt448/480) shows
N* in [448,480] (@8× 5.15, better than batch4 384 = 5.36) — 4/3 = 384 is a local optimum of
the three-point scan, not the true N*; c* = T/N* ≈ 1.07–1.14 (near T), supporting
"overfitting culprit = bands with c(n)→1". N* shifts right with training budget
(3000: [352,448] → 27000: [448,480]), supporting the depth-theory phrasing
"the trim point is a setting function, not a universal constant"; the "4/3 is a hidden
constant" hypothesis is further weakened. N*'s exact position ([480,511]) needs a fine scan
near 491 (future work).

## 11. Related Work

RoPE（Su et al.）、位置插值（Chen et al. 2023）、NTK-aware/YaRN（Peng et al. 2023）、
partial-RoPE、ALiBi（Press et al. 2021）、LongRoPE（进化搜索频率配置——无保证无理论）、
NoPE（Kazemnejad et al. 2023）、Fourier 特征（Tancik et al.）、KERPLE（Chi et al.,
NeurIPS 2022）、FIRE（Li et al., Findings of ACL 2024）、YaRN（Peng et al., ICLR 2024）、
LongRoPE（Ding et al., ICLR 2024）。本文以「频率阶梯相位剖面」为统一分析对象，以
「证书 + 机制」区分于无保证的启发式扩展。

## 12. Limitations & Future Work

- **规模**：结论限于 char 级小规模（~0.5M 参数）；向 GPT-2 small 级迁移的挑战未验证
  （机制证明而非规模基准）。
- **统计**：主表 3-seed；Welch t（psi-rope-rand vs rope-NTK）p=0.018、d=−6.06 为小样本
  （n=3）方向性结论；对照组（NoPE/dense）单 seed。**Future work**：≥5 seeds + 95% CI。
- **覆盖梯度**：8→7 带剪枝为单点观察；多阶梯族扫描（C=2 的 8/9/10 带截断曲线）为 future
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
——带证书方案与无证书上限的差距由此标明。免修复的阶梯方案以 2× 内优势 + 零修改 + 机器
证书为保留的主张。**正式配置复现确认排序并升级主张：τ 感知频率选择（保留低中频 + 温和
裁剪高频端，最优区 N* ∈ [448,480]）把旋转族外推 7.50 → 5.15（−31%），过度裁剪恶化、结构化频率
否定**。NoPE 的平坦曲线揭示位置编码的本质交易（分布内质量 ↔ 外推稳健）；**τ/碰撞距离
机制统一解释排行榜并获 7 个正向判决**——「交易是周期参数化的属性，非周期偏置近零代价
逃逸」。最强的 4 带阶梯带机器检查的有理框架证书，最强的 7 带阶梯内含可认证子核——
表达性与可证明性在同一阶梯族内共存互补。证伪链与保留假设并报——这条律离终态还有距离，
但变量已被命名、仪器已就位、边界已被如实标出。

---

## 附录 A 代码-论文声明交叉索引（对齐 2026-08-23 基态）

> **代码仓库（Artifact）**：https://github.com/hy7pc8gfmf-dotcom/PSA-CertifiedSparseGating（Coq 形式化 + 实证脚本与数据 + CI）。预印本 DOI：10.6084/m9.figshare.33312336。

| 论文声明 | 代码位置 | 状态 |
|---------|---------|------|
| 实例证书 C=4（μ=4/5） | InstanceCertificate.certified_c4_frame_bounds | ✅ |
| 长度一致性 ∀N≥214 | M4bLengthConsistency.certified_c4_frame_bounds_anyN | ✅ |
| T8 复合证书核 | T8CoreCertificate.certified_t8_core_frame_bounds | ✅ |
| 七带复合界证书 | ChampionCertificate.champion_e5_composite_certificate | ✅ |
| 反射检查器健全性 | FrameCheckInstance.frame_check_instance_sound | ✅ |
| RoPE 酉性桥接 | UnitaryInvariance.unitary_invariance_psi_rope_theta | ✅ |
| 165 项全零 classic | PSA_audit.v（M1.5 已并入） | ✅ |
| 碰撞刻画 / τ 机制 | z\probe_collision.v（C1–C5）/ probe_tchar.v（T1–T4）/ probe_taudicho.v | ✅（论文 A §8，z 区独立验证） |
| ρ^{−3/2} 行和紧界（C=4 框架界） | z\probe_rowsum.v（row_sum_3halfs / row_bound_C4，21 Qed） | ✅ **已并入合并版** |
| 合并版 | src\ca_merged_full_24.v（75702 行，40 模块，7 探针并入） | ✅ MERGE_EXIT=0 |
| 经验数值（主表） | psa_empirical\测试数据\multi_seed_main_table.md | ✅ |
| 偏置对照（ALiBi/T5/grid） | psa_empirical\测试数据\baseline_*.log | ✅ |
| 正式配置 batch3/4 | psa_empirical\测试数据\（云端 T4，与本地逐位对齐） | ✅ |
