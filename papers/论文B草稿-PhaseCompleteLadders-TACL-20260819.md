# 论文 B 草稿（TACL/Findings 方向）— 2026-08-20 对齐版 v7
> **对齐协议**：本版对齐至 2026-08-20 会话 17 终态（A2/A1 完成后基态）——multi-seed 裁决
> （E5'' 七带均值冠军 12.40±0.74@8×，覆盖梯度 3-seed 确认）+ T8 复合证书 +
> **端到端冠军证书 `champion_e5_composite_certificate`（会话 14 Qed）** 已并入 +
> **`frame_check_instance` 反射检查器健全性已 Qed（配套审计 165 项全零经典排中，M1.5 已清零）**。
> **v7 对齐修正（2026-08-20 会话 17 终态）**：① **A2 酉不变性已完成机器检查**——v6 的
> "降级为数学事实（未机器检查）"被推翻：Module `UnitaryInvariance` 已并入
> `PSA_framework.v`（`unitary_invariance_point` 全局保内积 + 位置索引 psi-rope 版，
> RoPE 语义；带索引逐点版为假命题未并入）；② **A1 4D 组装完成**：
> `tensor_product_unconditional_basis_4d` 已 Qed（coqchk 复验，合并版 28 分区）。
> **v6 P0 修正（2026-08-20 专家裁定）**：① 端到端冠军证书表述由"在制"改为
> "✅ 已 Qed（`champion_e5_composite_certificate`，七带 `(S−coh_e5) ≤ ‖F‖² ≤ (S+coh_e5)`）"；
> ② 酉不变性接口声明如实降级为"数学事实（未机器检查）"（unitary 在 .v 零命中）——
> **该降级已于 v7 被 A2 完成推翻**。
> **v5 对齐修正（2026-08-20）**：M1.5（exp 单调性去经典）已实际完成并入
> （`Module ExpSeries` Qed，`Classical_Prop.classic` 在全部 165 项审计中出现 0 次）；
> 审计项从 139 增至 165，全部零经典排中，仅继承标准 Dedekind 实数基础设施
> （sig_not_dec + sig_forall_dec + fext）。本文档所有 "139 项/4 项待清零" 表述
> 均已替换为 "165 项全零 classic"。
> **v4 增量（2026-08-20 会话 15/16）**：2D-wide 张量积无条件基交付
> （`tensor_product_unconditional_basis_2d_wide`，免 H_dom；`M_bound_2d_wide 4 = 768`
> 已 Qed，零 classic）——§6 跨维度公式的 N=2 校验从"数值验证"升级为
> **"全定理级已证 + 独立证明路线"**（论文 A §5.4）。
> **投稿闸门：NoPE ✅、rope+NTK ✅（已被 psi-rope-rand 3-seed 逆转，会话 18）、C=3 归因
> seeds ✅、E1 消融 ✅（psi-rand/psi-lin/dense-frozen/psi-rope-rand/psi-rope+rand 全落地，
> 含假说证伪与裁决逆转，§10.6）。**

---

## Title
**Phase-Truncated Frequency Ladders: Certified, Extrapolation-Robust Positional Encoding**

## Authors
王宝军、夏挽岚、祖光照、周志农、高雪峰（单位与通讯邮箱待补）

## Abstract (EN)
Positional encodings degrade sharply beyond their training length. We study length
extrapolation through the lens of the *frequency ladder* — the multiset of rotation
angles (or additive features) a positional scheme employs. On a controlled char-level
benchmark (3 seeds), we find: (1) truncating a Fourier ladder to its *phase-complete*
bands (n_j < T_train) dramatically improves extrapolation across three ladders;
(2) RoPE-style rotation on a phase-truncated ladder extrapolates far better than
vanilla RoPE (best geometric mean ppl 12.40 vs rope b32 3-seed 25.30±4.63 at 8×); **the overall empirical
champion is a *random dense rotation ladder* (psi-rope-rand, [3,511] random angles,
6.45±0.03 at 8×, 3 seeds)** — 44% below the 3-seed NTK number (11.54±1.18,
p=0.018, d=−6.06, §10.6) — while the 7-band geometric ladder [3,7,15,31,63,127,255]
(12.40) and NTK-aware rescaling serve as strong baselines; (3) dropping even the
*marginally* covered band (coverage 1.0) strictly
improves all extrapolation lengths across all seeds — a coverage *gradient*, not a
threshold; (4) the certified 4-band ladder [3,13,53,213] carries a machine-checked
rational frame certificate (μ = 4/5, Coq), and the 7-band geometric ladder contains a
certifiable sub-core — a composite certificate (frame core + energy-budget margin)
we formalize (with the end-to-end composite-certificate composition **Qed**, session 14:
`champion_e5_composite_certificate` proves (S − coh_e5) ≤ ‖F‖² ≤ (S + coh_e5) —
a basis-representation stability certificate, orthogonal to the empirical champion,
see §7); certification extends to arbitrary ladders through a reflective checker
with a machine-checked soundness theorem (165-entry Print Assumptions audit — all
with **zero `Classical_Prop.classic`**, zero Admitted; the only axioms are the
standard Dedekind-real infrastructure sig_not_dec / sig_forall_dec / fext);
(5) honest controls: NTK-aware rescaling beats phase-truncated
rotation at 4–8× (10.74 single-seed, vs 12.40 mean at 8×) — our surviving claim is
*no-test-time-surgery, no per-length recalibration, and certificates*, not absolute
extrapolation supremacy [session-18 final champion: a *random dense rotation
ladder* (psi-rope-rand) reaches 6.45±0.03 at 8× (3 seeds), 44% below the 3-seed NTK
number (11.54±1.18, p=0.018, d=−6.06); its random ladder lacks the geometric structure
required by Paper A's certificates, so it is empirically optimal but **outside** the
certificate scope — the two contributions are orthogonal (R11)]; NoPE shows a
catastrophically worse in-distribution loss
(9.06) yet the flattest curve (1.27× degradation), framing positional encoding as
a trade of in-distribution quality for extrapolation fragility. We document our
falsified hypotheses (including a retracted double-coverage law and an
even-filling hypothesis killed by counter-example) alongside the surviving ones,
and propose the ladder *phase profile* as a diagnostic for arbitrary positional
encodings. [Pending: attribution ablations (E1), control seeds, BPE replication.]

---

## 1. Introduction
- 长上下文是前沿模型主战场；现有上下文扩展方法（PI / NTK-aware / YaRN /
  partial-RoPE / ALiBi）全为启发式，缺一个统一变量。
- 本文贡献：**频率梯子**作为位置编码的统一分析对象；**相位截断**与**旋转注入**
  两个机制的受控分离；**带证书的冠军**（含复合证书结构）；以及一条如实记录的
  假设证伪链（方法学贡献：small-scale 但诚实完备的研究范本）。

## 2. 实验设置与协议
- char 级 GPT（~0.5M 参数 [待补精确数]，4 头，head dim 32，16 旋转维/头），
  Gutenberg 5.1M 字符（vocab 125），T_train=512，3000 iters，batch 32，
  **seeds {1337, 42, 7}（主结果均报 3-seed 均值±std）**。
- **确定性协议**：rope 在两种温控协议下逐位复现（损失到小数点后四位），
  证明冷却暂停不改计算轨迹 ⟹ 同 seed 同 batch 的跨 run 比较合法。
  （温控治理：80°C 触发/70°C 恢复/0.5s 轮询 + 防死锁，附录 [待补]。）
- 评估：T ∈ {512, 1024, 2048, 4096}（1×/2×/4×/8×），val ppl。

## 3. 频率梯子：统一形式化
- 旋转机制：位置编码 = 角度多重集 {θ_t}，核为逐槽和 Σ_t w_t·cos(d·θ_t)
  （**带间无交叉项**——排除一类机制假设的基础）；
- 加性机制：φ(k) = [cos/sin(2πk/n_j)]，含绝对相位项；
- 梯子族：生成器 next = C·n+1；C=2 给出梅森列 n_j = 2^{j+2}−1（近似二进）。
- **相位剖面**：每带覆盖倍数 T_train/n_j、可见带数 m_vis、填充均匀性
  （16 槽 mod 带数）——任意位置编码可输出的诊断量。

## 4. 主结果
### 4.1 主表（旋转组 3-seed 均值±std + 对照组）
| T | dense(wpe)¹ | rope³ | rope-PI¹ | rope-NTK¹ | NoPE¹ | **psi-rope 七带** | psi-rope C=4 | psi-rope C=2(8带) | psi-rope C=3 |
|---|------|------|------|------|------|------|------|------|------|
| 512 | 5.40 | 4.44±0.08 | 4.46 | 4.46 | 9.06 | 4.53±0.10 | 4.70±0.14 | **4.46±0.06** | 4.65±0.11 |
| 1024 | 15.98 | 6.77±0.07 | 16.59 | 5.11 | 9.72 | **4.75±0.06** | 5.64±0.07 | 4.95±0.04 | 5.45±0.58 |
| 2048 | 27.86 | 13.68±1.21 | 32.08 | 6.55 | 10.71 | 8.28±0.28 | 8.42±0.10 | 9.16±0.02 | 11.44±4.33 |
| 4096 | 34.94 | 25.30±4.63 | 37.87 | **10.74** | 11.55 | 12.40±0.74 | 12.75±0.34 | 13.84±0.25 | 22.86±5.30 |

（¹ 对照组单 seed：dense 为 s1337，rope-PI/NTK 为 eval-only 频率缩放（零训练），
NoPE 为 s42 完整训练 [均待补 seed]；rope-PI 无微调失效符合文献。
³ rope 裸绳为 **b32 3-seed 均值±std（会话 18 补，`ms2_rope_s{1337,42,7}.txt`：
@4096 = 20.28 / 29.40 / 26.22，s7 终值 26.22）**——单点 20.28（s1337）见旧版；
dense/rope-PI/NoPE 保持单 seed，3-seed 统计以 psi 系与 rope-NTK 为限（如实）。
**会话 18 补**：rope-NTK 3-seed（b32 重训 + NTK 缩放）@4096 = 10.74 / 12.90 / 10.97
（11.54±1.18）；psi-rope-rand（新冠军）3-seed = 6.44 / 6.49 / 6.42（6.45±0.03），
Welch t（vs NTK）p=0.018、d=−6.06——主表 10.74 列为 s1337 单点，3-seed 见 §10.6）

**对照组三判决（诚实性闸门，§8 预登记判定树执行）**：
- **rope-NTK @8× = 10.74**：对**预登记单 seed 基线**（psi-rope C=4 @4096 = 13.06）
  领先 21.6% > 15% ⟹ **闸门触发**；对 3-seed 均值 C=4（12.75）领先 15.7%、
  对均值冠军七带（12.40）领先 13.4%——恰跨 15% 阈值两侧，**"冠军降级"裁决不变**：
  psi-rope 的**绝对外推主张收缩**，存活主张为"**2× 内仍胜（4.75 vs 5.11）+
  零测试时手术 + 免逐长度重调参 + 带机器证书**"；rope-NTK 需按目标长度改 base
  且无任何保证；
- **NoPE 平坦曲线**：盘内灾难性差（9.06，位置信息必要性确认——叙事地基未塌），
  但退化仅 1.27×（vs 全部位置方案的 2.7-2.9×），**@8×（11.55）追平冠军最好 seed**——
  "位置方案用盘内 2× 优势换取外推脆弱性"是本基准的核心 trade-off 陈述；
- **rope-PI 无微调惨败**（37.87）——测试时修复不是免费午餐，NTK 是唯一有效形态。

- **七带梯 [3,7,15,31,63,127,255] 为全程均值冠军**（2×/4×/8× 全列第一）：
  @2× 对 C=4 不重叠领先（4.75 vs 5.64），@4×/8× 为重叠内领先（12.40±0.74 vs 12.75±0.34）；
- **覆盖梯度的 3-seed 单调确认**：从八带剪掉覆盖恰 1.0 的 511 带，在全部 OOD 长度、
  全部 seed 上严格改善（8×: 13.84→12.40；4×: 9.16→8.28；2×: 4.95→4.75），
  盘内仅付 0.07——**边缘覆盖带是 OOD 纯负债**；
- 帕累托结构 seed 稳定：C=2 盘内极（4.46±0.06），七带外推极；C=4 无均值列冠军
  但远程方差最小（±0.34）且**直接带证书**（§7）；
- **C=3 判决（分层）**：s1337 的 28.97 是坏抽签（其族内 s42/s7 为 19.48-20.12），
  但即便好 seed，C=3 在 8× 仍全 seed 劣于其余三族（>19.4 vs <14.1，不重叠）——
  **间距带中等程度的确定性远程代价（约 +60%）+ 显著放大的 seed 方差**
  （8× std 5.30 vs 其余族 0.25-0.74）；@2×/4× 幸运 seed 下有竞争力（5.07-5.17
  优于 C=4 的 5.57-5.71），失败集中于极程。方差排序 C=3 ≫ E5'' > C=4 ≈ C=2。

### 4.2 加性组
| T | psi-full C=3 | psi-trunc C=2 | psi-trunc C=3 | psi-trunc C=4 |
|---|------|------|------|------|
| 512 | 4.38 | 4.67 | 4.64 | 4.77 |
| 4096 | 39.69 | **18.43** | 29.70 | 23.89 |

- **psi-trunc C=2 在 4×/8× 上击败 rope**（12.15 vs 13.68；18.43 vs 25.30，rope 为 b32 3-seed 均值，§8）——单 seed 口径下（12.15 vs 12.33；18.43 vs 20.28）结论相同，3-seed 下领先更大；
- 全梯 vs 截断：三种梯子上截断收益三次复现（C=3: 39.69→29.70 同 run 内 -25%）。

## 5. 经验规律（Empirical Patterns）
> **评审 11 更名**：本章内容是**强经验规律**（覆盖梯度、截断效应、旋转注入），其
> 根本机制（除"长带死重"外）**机制未明**——剪枝带来的 PPL 突降与覆盖梯度的斜率
> 成因尚无形式化或机制性解释，如实标注为"经验规律，机制未明"，不作"机制发现"
> 宣称。与论文 A 的形式化贡献（框架界/衰减界）之间**无解释性桥梁**。
1. **截断效应**（稳健，3 次复现）：剪掉部分相位带恢复外推；
2. **相对性效应**（稳健）：同梯子下旋转碾压加性；
3. **二进身份 + 覆盖梯度（3-seed 确认；形式化归因如实标注）**：C=2 梯子 = "RoPE 砍掉 OOD 尾巴"；
   归因注记（诚实边界）：配套形式化（论文 A）**不主张解释**本经验律，且实测披露一个
   定量断层——`certified_attention_approx` 的输出界对谱能量 ε 单调，而剪掉 511 带的
   ε 几乎不变（该带窗内范数→0，与第 4 条长带死重一致），ppl 却 13.84→12.40 远超噪声——
   **增益机制不在形式化的谱能量通道内**（候选：绝对相位混叠、softmax 分母数值稳定性，
   均被现框架抽象掉，future work）；形式化的贡献限于稳定性检验（剪枝不破坏框架界，
   μ 不变——排除崩溃风险）；**结构通道候选机制（实证支撑，评审 7 元 IV 对齐，会话 18 修正）**：
   ppl 提升的机制不在能量通道，而在**带间相干结构随外推窗口的突变**——稀疏几何
   梯子族内实测 ΔCoh = Coh(512)−Coh(4096) 与 ppl(4096) 强正相关（4 点 R²=0.982，
   §10.6；能量 ε 几乎不变而 ΔCoh 区分四梯）；**E1 消融扩充（13 点）证伪其跨族
   普适性**（max 型 R²→0.101、median 0.597，无通用指标；§10.6 如实报告），相干性定性叙事
   保留、ΔCoh 定量预测收缩为稀疏几何族内指标；
   进一步剪掉覆盖恰 1.0 的 511 带后，全部 OOD 长度、全部 seed 严格改善
   （8× 均值 13.84→12.40，盘内仅付 0.07）——**边缘覆盖带是 OOD 纯负债，
   覆盖以梯度起作用而非阈值**；
   **两文联合边界图示（P1，强化可读性）**——覆盖梯度的"能量通道不敏感 vs ppl
   跃迁"在论文 A/B 联合视角下的定位：
   ```
   ε（丢弃谱能量）:  ~0（511 带窗内范数→0，死重 1.4111 vs 1.4120）
   ‖F‖² 框架界      :  不变（剪枝不改变框架/衰减结构，μ 不变）→ 稳定性已证
   ppl              :  13.84 → 12.40（-10.4%，远超噪声）
   ────────────────────────────────────────────────────────
   ⇒ 增益机制 ∉ 当前形式化的谱能量通道（ε 不敏感，通道无解释力）
   ⇒ 形式化贡献 = 稳定性检验（排除崩溃）+ 定性线索（长带相干衰减）
   ```
   联合声明边界：论文 A 机器可证的止于"表示稳定性 + 能量有界"；"能量控制 →
   外推 ppl 增益"的桥梁依赖本论文的覆盖梯度经验观察，**未经形式化**（论文 A
   §5.3 联合元定理边界）。此图式供论文定稿插图使用（横轴 T、双纵轴 ppl /
   ε+框架界示意）。
4. **长带死重**：128 带中 120 个 n_j>512 带对训练损失贡献 ≈ 0
   （1.4111 vs 1.4120）——与理论预测（窗口内范数→0）一致；
5. **填充均匀性无关**：七带填 16 槽（16 mod 7 = 2，不均匀）夺冠——
   均匀性被正反两面证据排除；
6. **跨维度推测（N 维推广，与论文 A 2D/3D/4D 证书挂钩）**：1D 覆盖梯度（剪掉覆盖恰 1.0 的
   511 带）在 N 维语境下 = "剪掉任意维度过长的轴"。张量积证书给出**精确的升维公式**：
   M_bound^{(N)} = (C³/2)·((1+4K_C)^N − 1)——**指数于维数 N，底数 1+4K_C**（C=4 时
   = 5；校验 N=2: 768（**2D-wide 全定理级已证，`M_bound_2d_wide 4 = 768`，免 H_dom，
   独立证明路线**）、N=3: 3968 全定理级已证、N=4: 19968 全定理级已证
   （组装定理 `tensor_product_unconditional_basis_4d` 会话 17 Qed，coqchk 复验）。
   指数墙可双因子分解：编码因子 C³/2（等轴退化病理，格雷码类
   编码/非等轴设计可望收回）与行和乘积因子 (1+4K_C)^N−1（与编码无关的主导项，
   需联合行和界突破）——维数敏感性与编码敏感性的定量归因见论文 A §5.4。
   推测性假说：**高维框架常数对维数与最大轴长度均敏感，截断应同时施加于所有
   维度**——轴长敏感性经证书的适用性条件（轴间支配 H_dom）与经验覆盖进入
   （M_bound 本身只依赖 (C,N)）。该假说把经验律与形式化证明显式挂钩：任一轴
   携带过长频带都会破坏轴间可比性并抬升整窗 M = S(max)，相位截断必须**逐轴独立**
   执行——与"边缘覆盖带是 OOD 纯负债"的 1D 裁决同构，且可被 4D/5D 实例化先行
   检验（论文 A §5.4/评估文档 §6）。**逻辑地位（如实标注）**：形式化给出的是
   **必要性**支撑（任一轴过长 ⟹ H_dom 失效 ⟹ 证书不适用）；**充分性未证**——
   "逐轴截断 ⟹ 证书适用"依赖截断后三轴序列满足同调增长，逐实例可判定但无
   一般引理；"逐轴截断 ⟹ 外推性能改善"超出当前形式化框架（框架界与 ppl 之间
   无语义链），不在主张范围内。

## 6. 假设证伪链（方法学小节，如实记录）
- ~~"psi 天然外推"~~ → 绝对编码崩溃（5→34）；
- ~~"double-coverage 律（n_max ≤ T_train/2）"~~ → C=2（覆盖 1.0）实测第二好，**撤回**；
- ~~"283 单带污染"~~ → E5' 剪掉 283 后**更差**（33.20 vs 28.97），**排除**
  （283 带实际在贡献盘内质量：E5' 盘内 4.78 为旋转组最差）；
- ~~"填充均匀性"~~ → E5' 均匀填充仍失败 + E5'' 不均匀填充夺冠，**双向排除**；
- 存活假设（穷举后）的**最终裁决（分层，3-seed）**：
  (i) **间距假设——部分成立**：C=3 间距在 8× 全 seed 劣于其余三族（好 seed 也 >19.4
  vs 其余 <14.1），确定性代价约 +60%；但非 s1337 显示的 2.2× 灾难；
  (ii) **噪声假设——同样部分成立**：s1337 的 28.97 是坏抽签（族内好 seed 19.5-20.1），
  且 C=3 族方差被极度放大（8× std 5.30 vs 其余 0.25-0.74）——
  **间距的效应一半在均值、一半在方差**；
  - E5' [3,10,31,94]（33.20，s1337）需按同族方差解读：可能是 C=3 间距 + 坏 seed
    的叠加，其"更差于全梯"的结论置信度相应下调；
  - 开放问题：间距如何同时抬升远程均值与放大方差——机制未明，如实报告。

## 7. 证书侧（与论文 A 的接口）
- [3,13,53,213]：**实例证书已证**（Coq，μ=4/5，框架界 [1/5, 9/5]，
  全有理常数、可判定；**∀N≥214 长度一致性已并入**——M4b 模块 5 Qed 零 classic）；
- 并列冠军七带梯整体行和 > 1 **不可整体认证**，但其隔带子核
  **[3,15,63,255] 同一配方验算行和 ≤0.781 ⟹ μ=4/5 可认证**；
- **T8 复合证书（已并入）**：T8CoreCertificate 模块 11 Qed 零 classic，
  冠军梯 = 认证核（gershgorin 框架界）+ 边际带（[7,31,127]，行能量预算）——
  "核带框架保证、边带能量保证"——**已证部分即此复合形态**（核 + 边带能量两构件
  均 Qed）；**端到端冠军证书已 Qed（会话 14）**：`champion_e5_composite_certificate`
  对七带证明 `(S−coh_e5) ≤ ‖F‖²_{255} ≤ (S+coh_e5)`（全矩阵相干加权对称界，
  论文 A §5.3）——**冠军现持复合界机器证书**（`(S−coh_e5) ≤ ‖F‖² ≤ (S+coh_e5)`，
  非外推性能证书；明确为**基的复合界证书**（"认证了冠军所用基函数"，非"认证
  冠军模型"——不含注意力分数/外推 ppl 保证），不再存在"在其 Qed 之前"的保留态；
  **评审 10 限定（2.2/3.4）**：该复合界与 PPL 改善之间的桥梁由**经验观察**支撑
  （§10.6 实证），**未经形式化**——我们形式化证明的是七带基的表示稳定性，其外推
  PPL 改善在本形式化框架中是一个**未证明的经验现象**；
  **评审 11 交叉引用声明（两文贡献正交）**：Paper A's formal certificates provide
  machine-checked stability guarantees for the **basis representation** of certain
  structured ladders. These certificates are **orthogonal to** the empirical
  extrapolation performance reported here. In particular, the best-performing
  empirical ladder (psi-rope-rand) does **not** fall within the certificate scope of
  Paper A, as it lacks the required geometric structure (its ladder is log-uniform
  random, not `next = C·last+1`). The value of Paper A's certificates lies in
  guaranteeing that, for structured alternatives (e.g. C=4), their representation is
  well-conditioned — a distinct and complementary form of assurance, **not** an
  extrapolation-performance certificate.
  **术语澄清（评审 9）**：`(S±coh)` 形态称**复合界（相干加权范数界）**，区别于标准
  框架界写法 `(1±μ)S`；二者等价（μ=coh/S），但复合界显式携带相干交叉项、直接对应
  代码形态，本文统一使用"复合界/复合证书"；"框架界"保留给 Gershgorin `(1±μ)S`
  形态（如 C=4 核 [1/5,9/5]、`gershgorin_frame_mu`）；
- **反射检查器（会话 10+11 收尾，本版新增）**：`frame_check_instance` 对任意梯子
  做 μ≤4/5 的**可判定有理判定**（floor-sqrt 有理化 + nat 分数行和，提取为
  OCaml/FFI，24/24 自测）；其健全性主定理 `frame_check_instance_sound` 已 Qed
  （判定通过 ⟹ gershgorin_frame_mu 框架界）——**"带机器证书"不再依赖逐梯子
  手工验算**，而由一台自带健全性证明的运行时检查器统一保证；配套审计
  **165 项** RC=0、零 Admitted（**全部零经典排中**，M1.5 已清零）；
  **定位澄清（评审 7 元 V）**：反射检查器是**快速预筛器**（充分非必要，快速驳回
  坏梯子/接受好梯子）；E5'' 冠军证书（21 对 δ 表手工推导的 `coh_e5`）是**针对
  特定冠军的特制专家系统**（不可泛化到未知梯子）——两者分工：预筛器管通用判定、
  专家系统管冠军深度证书，不可混为一谈；
  **假阴性系统扫描（评审 9 补强，会话 18）**：114 梯子 × 5 族（C-sparse C∈{2..8}、
  几何奇带、C=2 全相位、E1 随机），以窗口 T=末带精确相干行和作 ground truth
  （`frame_check_scan.py`）：通过 35（30.7%）、假阴性 56（全量 49.1%、占拒绝 70.9%，
  集中于 C=2/3-sparse 与几何奇带等"有用"族）——4 样本"50%"的量化推广；E5'' 七带
  精确行和仅 0.135 ≤ 4/5（实质可认证，检查器误拒源于无窗口保守对界），复合证书即
  其紧证书。**提取整数范围（评审 9 点 3，Zarith 依据）**：exe 与 Coq 语义分歧 27/114
  （23.7%），末带 < 2^20 内仍有 14/89（15.7%）——行和累积分母 ∏ pair_den 连乘溢出
  （如 C=6-sparse 五带末带 4147，分母 10^26 ≫ 2^63）；实验值（≤255、m≤8）均安全，
  通用界须逐梯核算 ∏ pair_den < 2^63，彻底消除改用 Zarith 任意精度（future work）；
- **2D-wide 张量梯子（会话 15 交付，宽轨 N=2 成员，免 H_dom）**：二维频率格子
  φ2D(i,j)(k) = γ⁻¹ψ_i(k)ψ_j(k) 的框架界已全量编译零 classic
  （`ca_2d_wide_const.v` / `ca_2d_wide_engine.v` / `ca_2d_wide_asm.v`，
  审计 5 项零 classic）。与 3D 共用 K0 = Rmax 8C³/2，但**免 H_dom**：
  扁平 idx1≠idx2 经 div/mod 解码唯一性自动给出 i1≠i2 ∨ j1≠j2，无需跨轴支配
  条件（论文 A §5.4）——宽轨家族中唯一免支配假设、可运行时判定的成员；
  数值裁决 `M_bound_2d_wide 4 = 768` 已 Qed，验证 §6 升维公式 N=2 预测；
- **2D 窄轨反射化（论文 A §5.5）**：窄轨 2D 的 H_dom 判定 `hdom_2d_narrow` + 反射检查器
  `frame_check_2d_narrow_sound` 已 Qed（判定通过 ⟹ 窄轨 K0=C³/4 口径框架界，可运行时判定）——
  与宽轨 2D-wide 免 H_dom 构成**双轨反射化闭环**：二维应用按"免支配假设"（宽轨）或
  "H_dom 可判定"（窄轨）任选其一，均有机器证明的健全性；
  **范围限定（评审 8 问题3 强化）**：该窄轨检查器仅覆盖**单轴退化（n1=1 或 n2=1）**
  配置，不覆盖真正的 2D 格点（n1,n2≥2，其保证由静态
  `tensor_product_unconditional_basis_pointwise` 给出）——"2D 窄轨"指 2D 口径下的
  退化反射化，非真 2D 运行时判定；
- **3D/4D 张量梯子（已完成，扩展方向）**：三维频率格子 φ(a,b,c)(k) = γ⁻¹ψ_aψ_bψ_c 的框架界
  推广已全量编译（`ca_basis_3d.v`，会话 12 复核 RC=0，**审计 10 项零 classic**；含修正常数
  引理 K0′ = Rmax 8C³/2——2D 的 /4 常数在等轴退化配置不可证，修正为恰好紧的 /2，见论文 A
  §5.4）；四维扩展 `ca_basis_4d.v` 的常数层、数值引理（M_bound_4d 4 = 19968）、主衰减引擎
  `phi_flat_decay_general_4d` 与组装定理 `tensor_product_unconditional_basis_4d` 已全部
  Qed 零 classic（会话 17 单文件版编译 + coqchk 复验 RC=0）。其常数较 1D 显著保守
  （M_bound = K0′·((1+4K_C)³−1)，可双因子分解为编码因子 C³/2 与行和乘积因子
  (1+4K_C)^N−1——后者为主导项；等轴配置为相干最坏情形，非等轴设计可望收回编码因子，
  见论文 A §5.4）——作为"带证书"叙事向图像/视频/3D 数据的扩展轴；
  **尚未接入 PSA 提取链，作为独立模块声明**。证书族为并列双轨（论文 A §5.4）：
  窄轨证书（1D μ=4/5、2D K0/4，前提收紧、常数可用）是**实用证书**，宽轨
  存在性证书（2D-wide/3D/4D K0/2，全覆盖）是**组合性叙事**——仅需 1D/2D 的场景
  （含本文全部实验）采用窄轨，不受高维常数爆炸影响；
- **酉不变性接口声明（✅ 已机器检查，2026-08-20 会话 17）**：本文"旋转组"（psi-rope）
  = 基函数乘旋转矩阵。旋转是酉变换，不改变内积与范数，故论文 A 的框架界/衰减界/
  证书**自动覆盖旋转版本**——Module `UnitaryInvariance` 已并入 `PSA_framework.v`：
  `unitary_invariance_point`（U 保内积 ⟹ ‖Σ U(g_i)‖² = ‖Σ g_i‖²）与位置索引 psi-rope
  实例 `unitary_invariance_psi_rope` / `_global`（每位置乘单位模 u_k，RoPE 语义）均 Qed
  零 classic；**显式实例** `unitary_invariance_psi_rope_theta`（u k := Cexp (0+i·θ_k)，
  `Cexp_unit_mod` 证单位模）与实验 2×2 旋转矩阵同构（SO(2)≅U(1)，逐行对应
  `length_extrap.py` `apply_rope_theta`）；形式化对象（基函数内积）与实验对象
  （旋转后注意力）经酉不变性桥接，无覆盖缺口。注：带索引逐点版本为假命题
  （交叉项需 u_i=u_j），未并入；
- 叙事张力（可发表点，如实呈现）：**外推冠军（七带）与直接证书（C=4）分离**——
  带数与可认证性此消彼长，复合证书弥合二者（可证骨架）；multi-seed 已裁决（并列）。
  更尖锐的表述：认证与外推性能呈**温和负相关**（certified C=4 8× 均值 12.75 vs
  未认证七带 12.40）——"带证书"的可证内容止于表示稳定性与能量有界（论文 A
  联合元定理边界），**能量控制 → 外推 ppl 增益的桥梁未经形式化**、依赖本文的
  覆盖梯度经验观察。这一反直觉张力本身是可发表发现，不掩饰；
  端到端冠军证书的顶层组合定理已 Qed（`champion_e5_composite_certificate`，
  论文 A §5.3，会话 14——七带 `(S−coh_e5) ≤ ‖F‖² ≤ (S+coh_e5)`）。

## 8. 对照组（闸门逐项落地）
| 对照 | 状态 | 堵的质疑 |
|------|------|----------|
| NoPE | ✅ 已跑（seed 42） | "小模型可能不需要位置编码" |
| rope+PI / rope+NTK-aware | ✅ 已跑（eval-only） | "真对手是测试时修复的 rope" |
| E1 消融（psi-rand/lin/frozen） | ✅ 基本落地（psi-rand ✅ 3-seed 高方差、psi-lin ✅ 3-seed 39.62±4.07 最差、dense-frozen ✅ 3-seed 盘内掉质量、psi-rope-rand ✅ 3-seed 6.45±0.03 含假说证伪与裁决逆转，§10.6） | "收益只是瓶颈/正则化" |
| 四梯 multi-seed ×3 | ✅ 已跑 | 单 seed 噪声 + C=3 归因 + 冠军身份 |

**rope-NTK / rope-PI 对照（已跑，诚实性闸门触发）**：
rope-NTK @4096 = **10.74**，对预登记单 seed 基线 psi-rope C=4（13.06）领先 21.6% > 15%
（对 3-seed 均值 C=4 领先 15.7%，对均值冠军 12.40 领先 13.4%）⟹ 按设计判定树：
**冠军主张降级为"免维护的次优选择"**——psi-rope 的"免调参还赢"强主张被测试时 NTK
修复推翻；定位收缩到"零训练额外成本 + 带机器证书（反射检查器 + 165 项全零审计）"。
rope-NTK 本身为**纯经验修复、无任何形式化保证**：频率重缩放破坏梯子结构
（seq 频率不再对应原序列），论文 A 的证书侧对其无可证陈述——"免手术 + 证书"
与"手术 + 无证书"构成两条正交路线，冠军降级后二者不可比性应如实呈现。
**声明（评审对齐）**：该"冠军降级"是**经验性能比较**，不改变已证框架界的
有效性——`champion_e5_composite_certificate` 的 `(S−coh) ≤ ‖F‖² ≤ (S+coh)`
对七带梯子恒成立，与 rope-NTK 的 ppl 优劣无关。
这种正交性在配套形式化（论文 A §10）中被表述为"适用域边界"：框架界与衰减界
的全部证明依赖梯子结构（seq 存在性），rope-NTK 的频率重缩放破坏了该结构，
因此不在证书覆盖范围内——其经验优势与形式化担保构成不可比的两端。
rope-PI @4096 = 37.87（差于裸绳 20.28）——char 级小模型不适用位置插值。
**rope 裸绳 b32 3-seed 补全（会话 18 收尾）**：@4096 = 20.28 / 29.40 / 26.22
（均值 25.30±4.63；全长度 4.44±0.08 / 6.77±0.07 / 13.68±1.21 / 25.30±4.63，
`ms2_rope_s{1337,42,7}.txt`）——单 seed 时代的主表 rope 列（20.28）为 s1337 单点；
rope 裸绳 3-seed 显著差于 psi-rope-rand（6.45±0.03，低 74%）与 rope-NTK（11.54±1.18，
低 55%），且 seed 方差（±4.63）远大于 psi 系——相位截断 + 旋转注入的相对优势在
3-seed 统计下进一步坐实；对照组 dense/rope-PI/NoPE 仍单 seed（如实标注）。
诚实结论：论文 B 重构为以"免手术 + 证书"为核心主张，而非绝对外推冠军。
**会话 18 裁决逆转（multi-seed 确认 + 统计检验）**：E1 消融 psi-rope-rand（随机稠密
旋转角 [3,511] 128 角）@4096 三 seed（batch 32）= **6.44 / 6.49 / 6.42**（均值 ≈6.45，
stdev 0.03）；**rope-NTK 三 seed（b32 重训 + NTK 缩放）= 10.74 / 12.90 / 10.97
（11.54±1.18）**——Welch t（双尾，n=3）：Δ=−5.09，t=−7.42，df=2，**p=0.018 < 0.05**，
Cohen's d=−6.06（强效应；小样本 df 局限如实标注）——**psi-rope-rand 是唯一的最终
实证冠军**（评审 11 统一叙事：七带 12.40 与 rope-NTK 11.54 均降为对比基线；"冠军
降级→逆转"过程如实保留为裁决史）。**证书边界声明（评审 11 修正）**：psi-rope-rand
的梯子为 log-uniform 随机采样，**非**论文 A 定义的几何递推梯子（`next = C·last+1`），
不具稀疏增长/相干衰减/框架界结构——**不在论文 A 的证书覆盖范围**（落在其"无任何
可证陈述"边界之外）；其外推优势是纯实证，与论文 A 的机器可检查保证**正交**。
**附带再审视**：原降级裁决的样本对（C=4 12.75 vs NTK 11.54）在 3-seed 统计下
Δ=+1.22、p=0.21 **不显著**——「NTK 反超」本就在噪声带内；psi-rope-rand 的反超
（p=0.018）则是统计显著的真实逆转。原裁决（上段）按其预登记判定树诚实执行，
此处按新证据重审——两阶段均如实记录。

**NoPE 控制（已跑，闸门确认）**：NoPE 盘内 ppl = **9.06**（seed 42），
vs dense 5.40 / psi-rope 4.67——盘内差 3.66&nbsp;ppl (>1.5) ⟹ **位置信息必要性确认**
（闸门未触发，位置编码叙事存活）。NoPE 外推极平缓（9.06→11.55，仅 1.27×），
因无位置结构可碎（OOD 无位混淆）——与位置方法的"盘内好、外推崩"形成机制对照，
佐证位置信息对盘内质量的关键作用。

**定量交易曲线（两文联合解读）**：位置结构给出一条可量化的交易——盘内 ppl
劣化约 **2×**（NoPE 9.06 vs 最优梯子 4.46），外推退化比改善约 **2.2×**
（1.27× vs 全部位置方案的 2.7–2.9×）。形式化侧（论文 A §10）反向解读：
框架界与衰减界的全部证明依赖梯子结构（seq 存在性）——**形式化锁定的是交易中
"有结构"的一端**：该端同时获得可证性与盘内最优性，代价是长距离处带间
交叉项失控的 OOD 相位混淆风险；无结构端无可证界、亦无此风险，但盘内质量
崩塌。可证性与外推稳健性在此实证上反向，非本框架缺陷而是交易的如实度量。
| 相位余量扫描 | [待补] | 覆盖梯度定量化 |

## 9. Related Work
RoPE（Su et al.）、位置插值、NTK-aware/YaRN、partial-RoPE、ALiBi、
LongRoPE（进化搜索频率配置——无保证无理论，本文以证书+机制区分）、
NoPE（Kazemnejad et al. 2023）、Fourier 特征（Tancik et al.）。
[⚠️ 提交前补全核对。]

## 10. Limitations
对照组（NoPE/dense 单 seed [待补]；rope/rope-NTK 已补 3-seed，会话 18）；char 级
0.5M 参数（BPE 复刻 [待补]）；C=3 间距效应的机制未明（均值+方差双层）；-12% 盘内
收益归因（E1 全臂已跑，§10.6）；rope-NTK 3-seed 统计已补（§8，p=0.018）；温控约束下的实验产能；
证书侧审计 **165 项全零经典排中**（`Classical_Prop.classic` = 0，M1.5 已并入
ExpSeries 幂级数路线；仅继承 sig_not_dec + sig_forall_dec + fext）。
**评审 B 补强（2026-08-20 会话 17）**：
- 规模（B1）：结论限于 char 级小规模；向 GPT-2 small 级迁移的挑战（训练稳定性、
  梯度消失）未验证，为 future work——本工作定位为机制证明而非规模基准；
- 基线（B2）：选型聚焦"免测试时修复"族（NoPE/rope-PI/rope-NTK）；与 ALiBi/T5
  relative bias 等可训练偏置类、Longformer/BigBird 稀疏变体的系统比较未展开
  （理论关系：ALiBi 的线性偏置可视为相位剖面的一阶近似，future work 核验）；
- 覆盖梯度（B3）：8→7 带剪枝为单点观察；多梯子族扫描（C=2 的 8/9/10 带截断
  曲线）与更细带数扫描为 future work；
- 统计（B6）：主表 3-seed 均值±std；**Welch t + Cohen's d 已补（会话 18）**——
  psi-rope-rand vs rope-NTK（11.54±1.18）：t=−7.42，df=2，p=0.018，d=−6.06（**显著**）；
  原降级对（C=4 12.75 vs NTK 11.54）p=0.21 **不显著**（噪声带内，如实）；小样本
  （n=3）df 局限如实标注，建议投稿前补 5-seed 复核；
- E1 消融（B4）：psi-rand/psi-lin/dense-frozen/psi-rope-rand/psi-rope+rand **全部已跑**（§10.6
  全表）——预登记假说证伪（psi-rope-rand 反超）、dense-frozen「瓶颈全解释」分支证伪
  （盘内掉质量 6.08 vs 4.5-5.0）；psi-rand 高方差与 psi-lin 最差如实报告；
- 机制定量（B5）："ε 不敏感 vs ppl 提升"的机制线索（如剪枝对注意力权重锐度/
  softmax 熵的影响）未测，列为 future work 实验。
- 第五版评审增值方向（future work 路线图，需 GPU 训练/实现，如实记录）：
  ③ E1 消融按"相位剖面预测力"设计（OOD 相位混淆指数 vs PPL 散点图，R² 报告）；
  ④ 证书引导的 KV 逐出模拟（用 `row_dropped_energy_bound` 动态丢弃低能量远距
  KV，验证 PPL 不变甚至微降——形式化定理直接转为推理加速算法）；
  ⑤ rope-NTK 补 3-seed 后报告 Cohen's d 效应量与 95% CI；
  ⑥ 2D 图像 patch 验证"截断应逐轴独立"假说（轴间可比性 H_dom 破坏 ⟹ 外推崩坏）。
（与论文 A 的关系：本文实证结果验证论文 A 形式化框架（同一梯子族）的适用性；
论文 A 的框架界/能量界为"免手术 + 证书"定位提供理论支持——两文共享梯子对象，
主张正交：形式化保"表示稳定性/能量有界"，实证报"外推 ppl"。）

## 10.5 性能-可证明性帕累托前沿（评审 5 方向 7，叙事重构）
把"冠军降级"重构为**可审计 AI 的定位**：性能与可证明性构成帕累托前沿——
| 方案 | 8× 外推 PPL | 证书（可审计性） |
|------|------------|-----------------|
| **psi-rope-rand（随机稠密旋转角）** | **6.45±0.03（3-seed，实证冠军）** | **不在**论文 A 证书覆盖范围（随机梯子无几何结构，评审 11）；与证书正交 |
| rope-NTK | 11.54±1.18（3-seed） | **无证书 / 不可审计**（纯经验修复，破坏梯子结构） |
| E5'' 七带 | 12.40（次优） | 复合证书（复合界 `(S−coh) ≤ ‖F‖² ≤ (S+coh)`），**可审计** |
| C=4 [3,13,53,213] | 12.75（第三） | 紧证书（μ=4/5 有理界），**强审计** |
在 AI 安全/合规（如欧盟 AI 法案）语境下，**可审计性本身是核心价值**：高风险场景
（金融/医疗）中证书的存在优先于 1-2 个 PPL 点。本文定位 = **定义了可审计位置编码
的性能-可证明性前沿**（"可审计性即价值"），而非"外推性能亚军"——三方案沿前沿
分布：最优性能（无审计）→ 次优性能（复合证书）→ 紧证书（强审计）。

## 10.6 相干衰减率与 E1 消融：相位剖面预测因子的边界（评审 6 方向一实证，2026-08-20/21 会话 17/18）
定义 `Coh(T) = max_{i<j} |⟨ψ_i,ψ_j⟩_T|/(‖ψ_i‖_T·‖ψ_j‖_T)`（带间相干衰减率）与
**ΔCoh = Coh(T_train) − Coh(T_ood)**。初始实测（四梯**稀疏几何**梯子，配主表 3-seed 均值，
`coherence_analysis.py`）：
| 梯子 | Coh(512) | Coh(4096) | ΔCoh | ppl(4096) |
|------|----------|-----------|------|-----------|
| C=2 全相位 | 0.0430 | 0.0044 | 0.0387 | 13.84 |
| C=3 | 0.0795 | 0.0035 | 0.0759 | 22.86 |
| C=4 | 0.0317 | 0.0009 | 0.0308 | 12.75 |
| E5'' 七带 | 0.0357 | 0.0110 | 0.0247 | 12.40 |

四点上 R²=0.982 的强正相关**未通过 E1 消融扩充的稳健性检验**：加入 E1 随机梯子
multi-seed 样本后（**13 点**，`coherence_scatter_full.csv`，会话 18）max 型 R² 崩塌至
**0.101**（Pearson r=+0.32）。原因有二：(i) 随机梯子取整产生**重复带** → 相同带对
相干恒为 1 → Coh(T_train)=Coh(T_ood)=1、ΔCoh≡0，指标退化（ppl 横跨 6.45–35.95 的点
全落 x=0）；(ii) 即使去重，稠密梯子在两个长度上都有近相干带对（Coh≈1）而**饱和**。
**指标族对照（同一 13 点，Δ = m(512)−m(4096)）**：
| 聚合器 | R²（全 13 点） | R²（稀疏几何族 4 点） | 判定 |
|--------|----------------|----------------------|------|
| max（原版） | 0.101 | 0.982 | 跨族死 |
| dedup-max | 0.001 | 0.982 | 跨族死（反号） |
| mean | 0.406 | 0.903 | 部分恢复 |
| RMS | 0.252 | 0.985 | 族内最优、跨族一般 |
| **median** | **0.597** | 0.434 | 跨族最强但仍非定律 |
| λ_max（谱范数） | 0.461 | 0.299 | 部分恢复，可形式化钩子 |
| F_0.5（相干对数占比） | 0.463 | nan | 稀疏族退化 |
诚实结论（评审 11 降格）：ΔCoh 仅在**稀疏无重复的几何梯子族内**排序外推表现（max 型 4 点 R²=0.982），
**没有任何相干聚合器是跨族通用预测因子**（最优 median 也仅 R²≈0.6，且冠军
psi-rope-rand 恒偏离回归线）——原 R²=0.982 是小样本过拟合，被 E1 消融（本应检验
其预测力）证伪；旋转族 OOD 由稠密相位覆盖主导（见下），相干衰减非其机制。
**据此，"相位剖面作为统一诊断工具"的宣称降格为"稀疏几何梯子族内的相关性报告"**
（评审 11：一个仅在 4 个稀疏点上成立的族内相关，不构成统一预测因子）。

**E1 消融（同批 / C=4 几何基线；b64 = s1337 单 seed，b32 = 3-seed 确认）**：
| 模式 | T=512 | T=1024 | T=2048 | T=4096 |
|------|-------|--------|--------|--------|
| rope（裸绳，b32 三 seed，会话 18 补） | 4.44±0.08 | 6.77±0.07 | 13.68±1.21 | 25.30±4.63 |
| dense（可学习表，b64 s1337） | 5.42 | 16.91 | 27.70 | 37.74 |
| psi（几何嵌入 C=4，b64 s1337） | 4.74 | 14.34 | 23.68 | 32.01 |
| psi-rand（随机嵌入 [3,54613]，b64 s1337） | 4.53 | 13.05 | 25.53 | 35.95 |
| psi-rope（几何旋转 C=4，b64 s1337） | 4.67 | 5.87 | 8.58 | 13.69 |
| psi-rope+rand（排序随机旋转 ≤512，b64 s1337） | 4.59 | 5.15 | 6.76 | 9.82 |
| psi-rope-rand（随机旋转 [3,511] 未排序，b64 s1337） | 4.35 | 4.79 | 5.67 | 7.29 |
| **psi-rope-rand（b32 三 seed 均值±std）** | **4.48±0.10** | **4.67±0.20** | **5.41±0.27** | **6.45±0.03** |
| psi-rope+rand（b32 三 seed 均值±std） | 4.50±0.04 | 5.06±0.23 | 7.10±0.79 | 12.33±1.20 |
| psi-lin（线性嵌入 [3,54613]，b32 三 seed） | 5.01±0.34 | 10.40±0.33 | 17.93±1.77 | 39.62±4.07 |
| psi-rand（随机嵌入，b32 三种子，s1337 已于 2026-08-21 补跑） | 4.45±0.14 | 10.98±4.01 | 20.72±8.96 | 31.04±12.86 |
| dense-frozen（固定高斯特征，b32 三 seed） | 6.08±0.20 | 12.59±0.22 | 21.57±1.45 | 29.49±2.52 |

**设计假说被证伪（诚实性支柱实验设计 §8 预测表，会话 18 3-seed 确认）**：预登记
预测"psi-rope-rand 显著差于 psi-rope（几何波长匹配语言层级）"被**反向推翻**——随机
稠密旋转角 b32 三 seed @4096 = 6.44/6.49/6.42（均值 6.45±0.03），比几何 C=4（12.75）
好 49%、比 E5''（12.40）好 48%、**低于 rope-NTK 3-seed（11.54±1.18）44%**——psi-rope-rand
**是唯一的最终实证冠军**（评审 11：七带/NTK 降为基线；降级-逆转过程如实保留为裁决史）。
机制解读：旋转族（相对位置）中决定 OOD 表现
的是**相位完备性/稠密覆盖**（[3,511] 随机梯子 128 个旋转角、约半数波长 <39 → 细密角
覆盖），而非几何序——三个**独立随机梯子**同点收敛（stdev 0.03）坐实稳健性；排序
随机（psi-rope+rand，仅 54 角）三 seed @4096=12.33±1.20，比未排序（128 角）差 1.9×——
**角度稠密度是关键**。**嵌入族三补充臂（E1 消融收尾）**：(a) **psi-lin 39.62±4.07
最差**——线性铺频带破坏相位完备性（中频带在 OOD 全相位失配），盘内亦略差
（5.01 vs psi 系 4.5-4.7）；(b) **psi-rand 31.04±12.86 高方差**——s42 意外外推好
（16.21）而 s7/s1337 崩（37.83/39.07，s1337 为 b32 补跑值 `ms2_rand_s1337.txt`），随机嵌入梯子的 seed 方差远大于几何梯子
（psi 32.01±? 三 seed 待补），几何序给嵌入族的不是绝对优势而是**稳健性**；
(c) **dense-frozen 盘内 6.08±0.20 显著差于 psi 系**（4.5-5.0，+20-30%）——固定高斯
特征丢失盘内质量，**ψ 基的频率结构对盘内质量有独立贡献**（匹配滤波器假说部分
成立；预登记"dense-frozen ≈ psi 瓶颈全解释"判定树分支被证伪）。两族分离最终图景：
旋转注入 = 稠密相位覆盖夺冠（6.45）；绝对嵌入 = 频率结构给盘内质量、外推全崩
（28-40 区间）。数据 `psa_empirical\测试数据\coherence_scatter.csv`、`ms_rr_*.txt`、
`ms_rand_*.txt`、`ms2_*.txt`、`eval_*.txt`。

## 10.7 KV 逐出与 2D 截断验证（评审 5 方向 4/6 实证，2026-08-21 会话 18）
**KV 逐出（`kv_eviction.py`，psi-rope C=4 三 seed，T=4096；评审 11 修正口径：loss
固定评估**同一批**尾部 64 位置，KV 窗口 W 独立变化——纯逐出净效应，非不同长度
任务）**：
| seed | W=full（全 4096 KV） | W=512 | W=256 | W=128 | W=64 |
|------|---------------------|-------|-------|-------|------|
| s1337 | 20.92 | 4.95 | 4.91 | 4.34 | 5.12 |
| s42 | 27.72 | 4.42 | 4.93 | 4.65 | 4.10 |
| s7 | 21.67 | 5.53 | 4.11 | 4.50 | 4.67 |
**解读（修正后，比初版更强且无设计缺陷）**：(a) **W=full（OOD 全上下文）ppl 20.9–27.7
远差于任何有限窗口（4.1–5.5，~5×）**——OOD 位置（尾部 64 个，全局位置 4032+）在
完整上下文下，远距 KV 的**相位已混淆**（相对位置超出训练范围），污染注意力分布；
**OOD 场景下远距 KV 是净负债而非中性资产**，截断到训练长度内窗口（≤512）等于
去毒，ppl 骤降；(b) **训练长度内窗口（W 512→64）无系统代价**（4.1–5.5 波动 ±0.5，
无单调趋势）——训练范围内 KV 可自由逐出（缓存瘦身）；(c) **与 `row_dropped_energy_bound`
的关系**（评审 11）：该证书给出的是丢弃远距 KV 的**偏差上界**（有界），并不承诺
无害——实测偏差为**负**（改善），兼容且更强；外推崩坏的根源（相位失配）不在
KV 数量，而在此处全上下文本身携带混淆远距信息。
**2D 截断验证（已删除，评审 11 判定）**：两轮实验（初版 vocab 16 纯 MLP：ppl≈1.4
天花板；难任务 vocab 64 + 噪声 + 自注意力：ppl 21–110 但 A/B 差值无方向且不随 T
单调，-5.7 至 +3.0）均**无法判别**"仅截断长轴 vs 双轴独立截断"。深层原因：训练
若遵守相位完备律（带 ≤ T_train），外推 T > T_train 时无带需截断（A/B 恒同）；训练
若不遵守（带 > T_train），模型学习忽略高频不完备带，截断与否无影响——**该假说的
可判别场景在经验侧难以构造**（其语义域在论文 A 的高维框架常数 M = S(max) 形式化
侧）。按评审 11 删除本验证，假说检验列为 future work（真实图像 patch / 高维
M=S(max) 实证）。

## 11. Conclusion
把位置编码的外推行为还原为**频率梯子的相位剖面**：截断部分相位带 + 旋转注入 +
覆盖梯度构成当前最优经验规律；对照组划定其疆界——**唯一的最终实证冠军是
随机稠密旋转角 psi-rope-rand @4096 = 6.45±0.03（3-seed 确认，会话 18），
击败 NTK-aware 测试时修复（11.54±1.18，3-seed，p=0.018）**；其随机梯子**不在**论文 A
证书覆盖范围（与证书正交——评审 11 分岔叙事：实证最优与可证明最优是两条平行轨道）；
免修复的梯子方案以 2× 内优势 + 零手术 +
机器证书为存活主张；NoPE 的平坦曲线揭示位置编码的本质交易（盘内质量 ↔ 外推稳健）**。
最强的 4 带梯子带机器检查的有理框架证书，最强的 7 带梯子内含可认证子核——
表达性与可证明性在同一梯子族内共存互补。证伪链与存活假设并报——这条律
离终态还有距离，但变量已被命名、仪器已就位、疆界已被诚实标出。

---
*配套：论文 A（Coq 开发，含 certified_c4_frame_bounds 与有理支配方法论）、
诚实性支柱实验设计（§8 执行单）、定理栈增强路线。*


---

## 附录：代码-论文声明交叉索引表（评审 6 建议）
| 论文声明 | 代码位置 | 状态 |
|---------|---------|------|
| 实例证书 C=4（mu=4/5） | InstanceCertificate.certified_c4_frame_bounds | ✅ |
| 长度一致性 forall N>=214 | M4bLengthConsistency.certified_c4_frame_bounds_anyN | ✅ |
| T8 复合证书核 | T8CoreCertificate.certified_t8_core_frame_bounds | ✅ |
| 七带冠军复合界证书 | ChampionCertificate.champion_e5_composite_certificate（(S-coh) <= ||F||^2 <= (S+coh)） | ✅ |
| 反射检查器健全性 | FrameCheckInstance.frame_check_instance_sound | ✅ |
| RoPE 酉性桥接 | UnitaryInvariance.unitary_invariance_psi_rope_theta | ✅ |
| 165 项全零 classic | PSA_audit.v | ✅ |
| 经验数值（12.40/12.75/13.84/22.86） | psa_empirical\测试数据\multi_seed_main_table.md | ✅ |
