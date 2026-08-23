# 可认证稀疏门控与注意力近似：一个可执行的 Coq 开发

**Certified Sparse Gating and Attention Approximation: An Executable Coq Development**

> 作者：王宝军、夏挽岚、祖光照、周志农、高雪峰
> 版本：最终版 v2.1（2026-08-23）｜代码基态：PSA_framework.v（18 模块 / 265 Qed / 165 项审计全零经典排中）+ 可证明性边界族（ParetoLaw / P1Coherence / ParetoRandom / CRTResolve）+ z 区 24 探针（**7 个已 pro 化并入合并版**：grid_ortho/parseval/partial/pairbound/rowsum/pairdirichlet/incoherence）+ **合并版 ca_merged_full_24.v（75702 行，40 模块，MERGE_EXIT=0）**｜CI 全绿（GitHub Actions）

---

## 摘要

我们提出一个 Coq 形式化开发，覆盖"可认证稀疏门控注意力"在几何结构化频率基上的完整流水线。开发在**两条正交的认证轨**上证明——表示稳定性轨（(i)–(iii)）与注意力扰动轨（(iv)–(v)），两轨之间无单一依赖链：(i) 一个确定性贪心门控，从任意有序索引集提取通过可判定稀疏增长检查的子集；(ii) 选定子基上成对相干衰减 $\le 1/(\sqrt{C})^{|i-j|}$ 与 Gershgorin 型框架界 $(1\pm\mu)\|c\|^2$；(iii) 行截断能量预算；(iv) softmax 在 $\ell_\infty$ logit 扰动下的 $\ell_1$ 稳定性；(v) 认证注意力近似定理：若每行丢弃谱能量 $\le \varepsilon$，注意力输出偏差至多 $(e^{2\sqrt{\varepsilon}}-1)\cdot V_{\max}$。所有门控与检查器函数提取为可执行 OCaml/Python，并与 Coq 计算参考值交叉核对（24/24）。

对具体几何阶梯 [3,13,53,213]（C=4），我们证明实例证书 `certified_c4_frame_bounds`：框架界 [1/5, 9/5]（μ=4/5），其中每个常数都是经超越界单侧支配得到的有理数（floor-sqrt、Jordan 不等式、Dirichlet 核）——证书层为可判定有理算术，可直接提取。证实例证书模式由反射检查器 `frame_check_instance` 推广到**任意**阶梯（μ≤4/5 的可判定判定，提取为带原生整数镜像的 OCaml）；其健全性定理 `frame_check_instance_sound` 已证明：**Coq 内**检查器通过 ⟹ Gershgorin 框架界。**运行时保证（如实限定）**：Coq 内健全性定理针对 nat 版本；运行时 int 镜像与 Coq 定义的等价性为逐行镜像 + FFI 24/24 交叉校验（非机器证明），且仅在有限整数范围（中间量 < 2^53、累积分母 < 2^63）内与 Coq 语义一致——"运行时检查器带机器证明健全性"精确指 Coq 内判定函数，运行时实现经交叉验证但未形式化验证（§6）。

对实证配套（论文 B）的**性能最优的结构化阶梯** [3,7,15,31,63,127,255]（论文 B 的强几何基线），一个表示级复合界（认证核 [3,15,63,255] 的 μ=4/5 + 边带能量预算 + 相干交叉项界）是本开发的展示定理 `champion_e5_composite_certificate`（Qed）：对七带基函数证明 $(S-\mathrm{coh}_{e5}) \le \|F\|^2 \le (S+\mathrm{coh}_{e5})$——**基表示稳定性界**，非注意力分数、学习投影或外推 PPL；通向论文 B 实证 PPL 增益的桥梁是经验观察而非形式化推论，该证书与实证性能最优方案（psi-rope-rand，随机阶梯在证书域之外）**正交**。审计含 165 项 Print Assumptions（RC=0，零 Admitted），**全部 165 项在应用层零 `Classical_Prop.classic`**（exp 单调性走幂级数路线，无中值定理）；唯一公理为 Dedekind 实数基础设施（sig_not_dec、sig_forall_dec、函数外延性）——实数构造固有的非构造性选择类原则，**非本开发应用层引入**。"端到端"主张有明确边界：认证链覆盖门控→框架界→截断能量→softmax 稳定性→注意力近似；不覆盖学习权重的数值稳定性、Q/K/V 投影、多头拼接或 LayerNorm（"verify the analytic kernel, learn the rest"）。

在认证管线之上，本开发进一步刻画**可证明性边界**（§5.6）：对 μ≤4/5 的保守检查器口径，稠密覆盖与可判定认证**互斥**——超过 9 个相位完备带覆盖 [3,511] 的阶梯必然被拒绝（`pareto_law_N511`，几何增长禁止 + 鸽笼组合论证，增长常数 c≈1.8501）；随机版负定律以高概率成立（同箱带对必触发拒绝，7 带 ≥ 96%、8 带 ≥ 99%，生日-箱计数）。我们同时形式化论文 B τ/碰撞机制的碰撞距离框架：精确碰撞当且仅当角度有理（全构造性 iff，最小距离 = 分母闭式）、无理偏移（黄金比）永无精确碰撞且近碰撞被 1/(3d) 半径挡住、线性偏置核（ALiBi）无碰撞端点——"认证—可证明性边界—碰撞/分辨率刻画"三角被机器检查覆盖（§5.6.4，含 U5 黄金近碰撞半径）。

**压缩感知级理论保证（v2.1 新增，§5.6.6）**：频率阶梯原子族满足**单位范数 → RIP(2,μ) → 稀疏唯一恢复**的完整链条——`psi_norm_one`（‖ψ_n‖=1）、`rip_bound2`（μ-不相干单位原子 ⟹ 能量偏差 ≤ μ·Σc²）、`sparse_uniquenessM`（**μ·(M+1) < 1 ⟹ 窗口内零组合 ⟹ 系数全零**，M+1 原子稀疏表示唯一）——把「无条件基 + 频率阶梯」的理论优势从框架界推进到稀疏恢复（48 Qed，已并入合并版）。

**关键词**：形式化验证；Coq/Rocq；稀疏注意力；框架理论；Gershgorin 界；反射检查器；程序提取；构造性数学

---

## 1 引言

稀疏/近似注意力方法（top-k、KV 逐出、低秩投影）全部缺乏误差证书。形式化方法可在"解析核"层提供保证——"验证解析核，学习其余"（verify the analytic kernel, learn the rest）。本开发的贡献（与代码一一对应）：

1. **确定性门控的形式化**（GreedyGate，28 引理）：原文概率门控前提不可满足（$(INR\,N)^2 p^2 < 1$ 恒假，反例已录），我们裁决并证明确定性平方门 M=C² 是**本文选定模型下**的可行路线（严格表述限定于该概率门控前提框架内，不声称一般意义唯一性）；
2. **有限化守卫衰减界**（PSA_Pipeline）：全局增长前提 → 运行时可判定检查，系数 2/√C 与 tight 1/√C 两版；
3. **行截断能量预算**（RowTruncation）与 **softmax 稳定性**（SoftmaxStability，$\|\mathrm{softmax}\,z - \mathrm{softmax}\,z'\|_1 \le 2(e^d - 1)$）；
4. **认证注意力近似**（CertifiedAttention）：谱能量 ≤ ε ⟹ 输出偏差 ≤ $(e^{2\sqrt{\varepsilon}}-1)\cdot V_{\max}$；
5. **实例证书**（Gershgorin + InstanceCertificate）：对 C=4 阶梯 [3,13,53,213] 证明框架界 [1/5, 9/5]（μ=4/5）——参数化最坏情形 1±4K(C) 在 C=4 空洞成立、需 C>25 的问题就此终结；
6. **有理支配方法论**（实现贡献）：证书全部常数经 floor-sqrt / Jordan / Dirichlet 单侧松弛化为有理数，`compute; field` 封口——零数值策略、零区间算术、可判定、可提取；
7. **可执行提取**：门控/检查器 → OCaml（psa_guard.exe）→ Python FFI，24/24 参考值对齐；
8. **反射检查器及其健全性**（FrameCheckInstance）：`frame_check_instance` 把"任意阶梯 → μ≤4/5"做成可判定有理判定，提取为原生整数镜像（与 Coq 定义逐行同构）；健全性定理 `frame_check_instance_sound`（Qed）证明判定通过 ⟹ Gershgorin 框架界——检查器本身带机器证明的健全性；
9. **基表示稳定性复合证书**（ChampionCertificate，核心展示定理）：论文 B 的七带基线阶梯获得机器证明的平方范数复合界 $(S-\mathrm{coh}_{e5}) \le \|F\|^2_{255} \le (S+\mathrm{coh}_{e5})$——当反射检查器返回 false（健全但非完备）时，核-边缘分解交付的部分证书在此收束为七带整体完整证书；这是对反射器不完备性的系统性工程补丁，作为方法论贡献单列；
10. **高维组合性演示**（2D-wide/3D/4D）：同一 `abstract_unconditional_basis` 骨架逐轴实例化到任意维——形式化方法学在高维逻辑闭合（"Theoretically Composable, Practically Non-Tight"）；
11. **覆盖边界**："端到端"精确指覆盖链门控→框架界→截断能量→softmax 稳定性→注意力近似；不在覆盖内：学习权重（W_Q/W_K/W_V/W_O）、Q/K/V 投影与多头拼接、LayerNorm/激活的数值稳定性、残差连接的累积误差。

## 2 背景

- **ψ 基**：$\psi_n(k) = (1/\sqrt{n})\cdot e^{2\pi i k/n}$，有限支撑（$k \ge n$ 时为 0）。
- **阶梯生成器**：$n_{j+1} = \max(C\cdot n_j + 1,\, n_j + 2)$（非精确几何——证书必须认证实际值，这是需要运行时检查器而非纸面公式的理由）。
- **三处语义勘误**（线性 vs 平方门、`<=?` vs `<?`、≥2 并集）——每处附反例，体现形式化对原草案的纠错价值。
- **一处常数级勘误（3D 张量基，已修正）**：2D 引擎的离对角界常数 K0 = Rmax 8C³/4 在 3D 等轴退化配置（两轴索引相同、仅第三轴差 ≤6）下不可证——归一化三重内积可逼近 1，而 /4 常数只给 1/2。3D 模块改为 K0′ = Rmax 8C³/2（退化配置恰好紧，worst case = 1）。

## 3 形式化开发总览

模块图（PSA_framework.v，6659 行，18 个 Module，265 Qed，零 Admitted）：

```
RuntimeGuards → SeqProps → PSA_Pipeline → GreedyGate → RowTruncation →
PipelineEndToEnd → ExpSeries（M1.5 级数重写，§7）→ SoftmaxStability →
CertifiedAttention → Gershgorin → InstanceCertificate（M4）→
M4bLengthConsistency（长度一致性，∀N≥214）→ T8CoreCertificate（T8 复合证书核）→
FrameCheckInstance（反射检查器 + soundness）→ ChampionCertificate（复合表示稳定性界，§5.3）→
FrameCheck2DNarrow（2D 窄轨反射化，§5.5）→ UnitaryInvariance（A2 酉不变性，§5.3）
```

统计：**165 项** Print Assumptions 审计（PSA_audit.v，RC=0）；**全部 165 项零经典排中**（`Classical_Prop.classic` 出现 0 次——M1.5 已清零，exp 幂级数路线并入）；**零 Admitted**（剥注释后 grep 命中 0）；零自定义公理；外部依赖仅 mathcomp + Coquelicot；Rocq 9.0.1。

## 4 核心定理

```
greedy_selected_correct (C) (vals) : C ≥ 2 → Sorted lt vals → all_ge_2 vals →
  let sel := greedy_selected (C*C) vals in
  Sorted lt sel ∧ NoDup sel ∧ all_ge_2 sel ∧ check_c_sparse_on_vals sel C = true

psa_gated_decay (seq) (I) (C) : 平方门控子集上 ‖⟨ψ_i,ψ_j⟩‖ ≤ 1/(√C)^|i−j|   (* tight 版 *)

gershgorin_frame_mu : 单位向量系 + 行非对角和 ≤ μ < 1 →
  (1−μ)‖c‖² ≤ ‖Σ c_i ψ_i‖² ≤ (1+μ)‖c‖²

psi_inner_dirichlet : |⟨ψ_{n1},ψ_{n2}⟩| = |sin(πNΔ)/sin(πΔ)| / √(n1·n2)

psi_inner_cons_bound : |⟨ψ_{n1},ψ_{n2}⟩| ≤ 1/(2Δ√(n1n2))   (* 窗口无关保守界 *)

softmax_l1_bound_exp : ‖z−z'‖∞ ≤ d → ‖softmax z − softmax z'‖₁ ≤ 2(e^d − 1)

certified_attention_approx : 逐行丢弃谱能量 ≤ ε →
  ‖attn_out − attn_out_approx‖ ≤ (e^{2√ε} − 1) · V_max

certified_c4_frame_bounds (coeffs) : length coeffs = 4 →
  (1 − 4/5)·S ≤ ‖Σ c_i·ψ_{[3,13,53,213],i}‖² ≤ (1 + 4/5)·S   (* 实例证书 *)

certified_c4_frame_bounds_anyN (N) (coeffs) : N ≥ 214 → length coeffs = 4 →
  (1 − 4/5)·S ≤ ‖Σ c_i·ψ_{[3,13,53,213],i}‖² ≤ (1 + 4/5)·S   (* 长度一致性 *)

certified_t8_core_frame_bounds (coeffs) : length coeffs = 4 →
  (1 − 4/5)·S ≤ ‖Σ c_i·ψ_{[3,15,63,255],i}‖² ≤ (1 + 4/5)·S   (* T8 复合证书核 *)

frame_check_instance_sound (I) : 0 < length I → frame_check_instance I = true →
  (1 − 4/5)·‖Σ c_i·phi i‖² ≤ ‖Σ_{k<M} (Σ c_i·phi i k)‖² ≤ (1 + 4/5)·‖Σ c_i·phi i‖²
  (* 反射检查器健全性：判定通过 ⟹ 任意阶梯 μ=4/5 框架界 *)

tensor_product_unconditional_basis_3d (C) (seq1 seq2 seq3) : C > 2 → 三轴稀疏增长 →
  (1 − M_bound)·S ≤ ‖F_3D‖² ≤ (1 + M_bound)·S
  (* φ3D(a,b,c)(k)=γ⁻¹ψ_aψ_bψ_c，M_bound = K0′·((1+4K_C)³−1)，K0′=Rmax 8C³/2 *)

tensor_product_unconditional_basis_2d_wide (C) (seq1 seq2) : C > 2 → 双轴稀疏增长 →
  (1 − M_bound)·S ≤ ‖F_2D‖² ≤ (1 + M_bound)·S
  (* φ2D(i,j)(k)=γ⁻¹ψ_i(k)ψ_j(k)，免 H_dom，M_bound_2d_wide 4 = 768 *)

tensor_product_unconditional_basis_4d (C) (seq1..seq4) : C > 2 → 四轴稀疏增长 →
  (1 − M_bound)·S ≤ ‖F_4D‖² ≤ (1 + M_bound)·S
  (* M_bound_4d 4 = 19968 *)

unitary_invariance_psi_rope_theta (θ) (vals) (coeffs) (n N) :
  Σ_{k<N} |Σ_{i<n} e^{i·(INR k·θ k)}·c_i·ψ_{vals[i]}(k)|² = Σ_{k<N} |Σ_{i<n} c_i·ψ_{vals[i]}(k)|²
  (* RoPE 显式实例：u k := Cexp (0+i·INR k·θ k)，Cexp_unit_mod 证单位模 *)
```

## 5 实例证书与可判定性溢价

### 5.1 实例证书（M3/M4）

对象：C=4 可见子梯 [3,13,53,213]（N=512 窗口内列范数=1；更长频带在窗口内近似线性斜坡、范数→0——窗口自适应认证是正确设计）。11 步证明：`psi_unit_norm`（对角=1）→ 六个有理对界（`pair_3_13` … `pair_53_213`）→ 四个行和引理（各 ≤ 4/5）→ `gershgorin_frame_mu` 一次实例化 ⟹ **[1/5, 9/5]**。

- **长度一致性**：`certified_c4_frame_bounds_anyN`——∀N≥214，O(1) 证书对一切序列长度成立。
- **从实例到通用判定**：`frame_check_instance`（任意阶梯 → μ≤4/5 布尔判定）+ 健全性 `frame_check_instance_sound`（Qed）——实例证书不再逐阶梯手工验算。

### 5.2 有理支配与可判定性溢价

全部超越量被朝可判定方向单侧支配：$\sqrt{m} \leftarrow \lfloor\sqrt{m}\rfloor$、$|\sin(\pi\Delta)| \leftarrow$ Jordan 2Δ、Dirichlet 分子 $|\sin(\pi N\Delta)| \leftarrow 1$、（Tier 2 的 π ← 22/7）。**证书层只需要 ℚ**——运行时验证只做有理算术，这是可提取性的根源。

- **可判定性溢价**：精确 μ = 0.312 → 有理保守 μ = 4/5，因子 2.55——机器可检查性的已量化代价。溢价是设计对象：松弛链可枚举、可优化（`cert_optimize` 方向，未来工作）。
- **检查器的保守性（充分非必要）**：`frame_check_instance = true` 是框架界的充分非必要条件——floor-sqrt 有理松弛的保守因子约 1.5×，存在满足 Gershgorin 条件但因保守上界超 4/5 而被误拒的合法阶梯（假阴性）。典型案例：论文 B 的七带基线阶梯 E5'' 被检查器判 false，不代表它不满足框架条件。正是这一不完备性使**复合证书成为必要**。宁可误拒、绝不放行的保守取向是可判定性的设计选择。
- **反向警示（形式化审查强化）**：检查器返回 `false` **不是**不安全证书——它只表明保守有理界不足以证明 Gershgorin 条件；被误拒的合法阶梯仍可由复合证书覆盖（七带即此情形：其精确相干行和仅 0.135 ≤ 4/5，实质可认证）。"检查器通过 ⟹ 框架界"成立，"检查器失败 ⟹ 不安全"不成立。
- **系统扫描（114 阶梯 × 5 族）**：通过 35（30.7%）、假阴性 56（全量 49.1%，占拒绝 70.9%），集中于"有用"族（C=2/3-sparse、几何奇带）——"可判定性溢价"是当前有理松弛实现的保守性代价（局限），收紧方向：`cert_optimize`、Zarith 大整数。

### 5.3 与实验的对齐（multi-seed + T8 + 复合证书 + 酉不变性）

3 个种子实验中 E5'' 七带与 C=4 并列最优（8× 均值 12.40±0.74 vs 12.75±0.34）；C=2 第三（13.84）；C=3 系统性最差（22.86）。最优表现对论文 A 免疫：

- **直接证书**（C=4）：`certified_c4_frame_bounds` 直接覆盖；
- **T8 复合证书**（E5''）：隔带子核 [3,15,63,255] 的 `certified_t8_core_frame_bounds`（μ=4/5）覆盖最优阶梯的认证核；
- **复合表示稳定性界**（ChampionCertificate）：顶层组合定理 `champion_e5_composite_certificate`（Qed，零 classic）——代码实际证明的目标形状（全矩阵相干加权）：`length coeffs = 7 → (S − coh_e5 c) ≤ ‖F‖²_{255} ≤ (S + coh_e5 c)`，其中 coh_e5 为 21 对上三角 δ 表经 `term_bound_upper/lower` 加权得到的对称相干交叉项界。**非平凡性说明（如实）**：coh_e5 为符号化加权界（逐对 δ 表 `delta_e5` 在代码中，此处未逐对列出）；其量级由七带在窗口 255 的精确相干行和 ≤ **0.135**（已实测披露）界定——相干远小于阈值 4/5，下界 S−coh_e5 在相干充分小时为正（非平凡）；该证书为**基函数范数稳定性保证**，与注意力输出/外推 PPL 无关。构件链：15 个新 pair 界 → 内积/范数引理 → δ 表（21 对）→ `coh_delta_bound`（42 方向）→ 上下界项 → 主定理。注意：早期草拟的"核带框架 + 边带能量"分段形式是装配前的设计稿，最终实现收敛为单一定理下的对称界。
- **酉不变性（已机器检查）**：旋转是酉变换，对任意酉算子 U 与系数向量 c，$\|\sum c_i U\psi_i\|^2 = \|\sum c_i \psi_i\|^2$——框架界/衰减界/证书自动覆盖旋转版本（论文 B 的"旋转组"）。Module UnitaryInvariance：`unitary_invariance_point`（U 保内积 ⟹ 范数不变）+ 位置索引 psi-rope 实例 + 显式 RoPE 实例 `unitary_invariance_psi_rope_theta`（`u k := Cexp (0+i·INR k·θ k)`，`Cexp_unit_mod` 证单位模）。实验的 2×2 块旋转矩阵（`apply_rope_theta`）与复数乘法 $e^{i\theta}$ 是同一酉群的同构表示（SO(2)≅U(1)），实/虚部逐行对应已显式机器检查（`rope_matrix_real/imag/eq`，零 classic）。注：原"每带乘 u_i"逐点版本为假命题（交叉项要 $u_i = u_j$；反例 u0=1, u1=−1, g0=g1=1），未并入。范围限定：酉不变性适用于**特征表示的范数层**；不保证学习到的 Q/K 投影下注意力 logits 不变。
- **相干熵桥接**（PhaseCoherence，`coherence_controls_attention`，Qed，零 classic）：对任意相干核 K（$|K_{ij}| \le \mathrm{coh}$）与系数差 $\ell_1 \le \delta$，logit 扰动 $|z_i - z'_i| \le \mathrm{coh}\cdot\delta$，组合 softmax 稳定性得 $\|\mathrm{softmax}\,z - \mathrm{softmax}\,z'\|_1 \le e^{2\cdot\mathrm{coh}\cdot\delta} - 1$——相干上界 ⟹ softmax 输出 TVD 界的抽象桥梁。当前为已证抽象桥梁 + 未实例化状态；实证支撑：ΔCoh 仅在稀疏几何族内排序（4 点 R²=0.982），13 点扩充后跨族崩溃（max 型 R²=0.101）——相干性定性结论保留、定量预测收缩为族内指标。
- **核漂移口径（已机器检查，2026-08-22）**：`kernel_drift_controls_attention`（PhaseCoherence，coqchk 独立复核）——核逐点漂移 $|K_{ij}-K'_{ij}| \le \mathrm{dc}$（全 i,j）且系数 $\ell_1 \le \mathrm{dd}$ ⟹ softmax 输出 $\ell_1$ 距离 $\le e^{2\cdot\mathrm{dc}\cdot\mathrm{dd}} - 1$（与上条互补：系数漂移×固定核 vs 固定系数×核漂移，覆盖长度外推/蒸馏/量化场景）；对窗口无关核族（网格/偏移网格在任意 $a\cdot N$ 长度核相同）Δ=0 退化为 TVD 界 0（`kernel_identical_tvd_zero`）。**常数演进线**：4K → 2K（`psi_unconditional_basis_tight`）→ μ=0（网格端点）；`abstract_unconditional_basis` 可用 Riesz 序列稳定性语言重述（张成族系数 $\ell^2$ 范数的 $(1\pm M_{\mathrm{bound}})$ 等价）——文本级重述，不改变机器检查内容。

### 5.4 维度推广：三维/四维/2D-wide 张量积无条件基

价值在于**组合性演示**：同一 `abstract_unconditional_basis` 骨架逐轴实例化到任意维。常数非紧性与未提取状态是两条独立限制，共同构成"存在性结果"而非"实用工具"的定位。

- **3D**：φ3D(a,b,c)(k) = γ⁻¹ψ_aψ_bψ_c，M_bound = K0′·((1+4K_C)³−1)，K0′ = Rmax 8C³/2。全量编译 RC=0，审计 10 项零 classic。数值紧度：`M_bound_3d 4 = 3968`（≫2 ⟹ 3D 证书目前仅作为存在性证明）。松弛可机械分解为两个正交因子：**编码因子 K0′ = C³/2 = 32**（等轴退化病理，格雷码类方案可望收回）与**行和乘积因子 (1+4K_C)³−1 = 124**（维数灾难主导项，要联合行和界突破）。
- **4D**：`ca_basis_4d.v`（2073 行）已全部 Qed + coqchk 复验 RC=0；`M_bound_4d 4 = 19968`；16 分支常数引理再次机械确认 /4 常数的单轴退化不可满足性是**维数无关**病理。
- **2D-wide**：φ2D(i,j)(k) = γ⁻¹ψ_i(k)ψ_j(k)，**免 H_dom**（扁平 idx1≠idx2 ⟹ i1≠i2 ∨ j1≠j2，div/mod 解码唯一性）——宽轨家族中唯一免支配假设、可运行时判定的成员；`M_bound_2d_wide 4 = 768`（= 32 × 24）已 Qed，与论文 B §6 N 维公式 N=2 预测完全一致。
- **双轨设计**：窄轨（1D 实例证书 μ=4/5、2D K0=C³/4——收紧前提换常数减半，**实用证书**）与宽轨（2D-wide/3D/4D K0=C³/2——全覆盖换 ×2，**组合性/存在性定位**）。仅要 1D/2D 的场景采用窄轨。

### 5.5 退化 2D（单轴）反射检查器（FrameCheck2DNarrow）

> 更名注："2D 窄轨"实为**退化单轴**情形（仅 n₁=1 ∨ n₂=1 的 1D 参数化 2D），非 2D 通用格点检查器；评审建议更名 `Degenerate2DFrameCheck`/`1DParametric2DFrameCheck`——本文保留原模块名 `FrameCheck2DNarrow`（避免跨文档引用失效），全文按"退化单轴"语义引用；真 2D 格点的运行时反射化为未来工作。

- 覆盖范围（首句明示）：本模块**不覆盖真正的 2D 格点（n1,n2≥2）**——检查器只处理单轴退化配置，是 1D 情形在 2D 口径下的参数化反射化。
- 严格增长延拓 `seq_ext`：窗口内取 nth，窗口外按几何闭式延拓——把有限阶梯提升为全索引序列以满足骨架的全局增长前提。
- 可判定 H_dom `hdom_2d_narrow` + 反射检查器 `frame_check_2d_narrow` 与其健全性 `frame_check_2d_narrow_sound`（Qed）：判定通过 ⟹ 窄轨 2D（K0=C³/4 口径）Gershgorin 框架界。
- 点态组装 `tensor_product_unconditional_basis_pointwise`（Qed）：与宽轨 2D-wide 构成**双轨反射化闭环**。

## 5.6 可证明性边界与碰撞刻画（2026-08-22 新增定理族）

> 本族回答论文 B 的"性能-可证明性张力"：不是工程未达，而是**定理层面**的边界。全部模块零 Admitted、零自定义公理；ParetoLaw/P1Coherence/ParetoRandom 仅 Stdlib Reals 自包含；**z 区 7 探针（grid_ortho + parseval/partial/pairbound/rowsum/pairdirichlet/incoherence）已按 E091 模式 pro 化并入合并版**（mathcomp Require + lia 改 mathcomp 引理，2026-08-23），独立 + 合并双通过；其余 z 区探针按 z/ 独立编译验证。

### 5.6.1 帕累托律：稠密覆盖与 μ≤4/5 可判定认证互斥

- **P2（单对触发）** `pair_bound_gt_4_5`（`src/ParetoLaw.v`）：0 < n < n′ 且 d = n′−n < (5/8)√(nn′) ⟹ 保守对界 B(n,n′) = √(nn′)/(2d) > 4/5 ⟹ 行和 > 4/5 ⟹ 检查器拒绝。
- **P3（增长引理 + 完整主定理）** `pair_bound_le_4_5_geometric` + `pareto_law_main`：不触发 P2 ⟹ n′ ≥ c·n，c = ((5+√281)/16)² ≈ 1.8501；m 个相完备带且检查器通过 ⟹ **3·c^(m−1) ≤ N**（几何增长禁止 + 鸽笼组合论证）。
- **N=511 推论** `pareto_law_N511`：**N=511 时 m ≥ 10 必被拒绝**——"有证书且接近最优"（μ≤4/5 口径）结构性不存在（②的负结果定理化）。实测密集 16–32 带全部拒绝，与定理一致。
- **备注①（5/8 精确阈值）**：`pair_bound_gt_4_5` 是 iff（d < (5/8)√(nn') ⟺ 64n'²−153nn'+64n² < 0 ⟺ B > 4/5，同一二次型）——"收紧检查器保守界"无空间，假阴性收紧路径在有理松弛→精确算术（Zarith）与 `cert_optimize` 子框架搜索。
- **备注②（初等替代证明）**：`ten_bands_reject`（probe_pigeon，零公理）——**任意 10 条 [3,511] 带必含 P2 触发对**：插入排序 + 相邻比率 ≥ 9/5 的指数爆炸（Z 层收口）——`pareto_law_main` 的初等替代（不需增长假设的链式归纳）；与 T2b 概率版互补（鸽笼 = 确定性、概率版 = whp）。

### 5.6.2 精确窗口相干下界（与保守界分层）

- **P1/P1′**（`src/P1Coherence.v`）：1 ≤ n < n′、d ≤ n′/2 ⟹ coh_T ≥ (2/π)·√(n/n′)；精细版 coh_T ≥ √(n/n′)·(1 − π²d²/(6n′²))（Jordan + sin_bound 交替级数，coqchk 复核通过）——近邻大带相干 ≈ 0.997 的解析根源成为定理。

### 5.6.3 随机版负定律

- **T2a** `t2a_same_bin_rejected`（`src/ParetoRandom.v`）：n < n′ < (9/5)·n ⟹ P2 触发 ⟹ 检查器拒绝（9/5 < c）。
- **T2b（生日-箱计数）**：`fall9`/`no_collision` 定义 + **符号化单调性**（no_collision (S m) ≤ no_collision m，递推证明不依赖具体数值）+ 数值界：m=7 ⟹ P(同箱对) ≥ 96/100、m=8 ⟹ ≥ 99/100——负定律从"确定性密度上限"延伸到"随机阶梯高概率拒绝"（m≥10 由鸽笼确定性覆盖）。
- 平台注记（如实）：Rocq 9 大 nat 字面量计算栈溢出，数值界以 R 层显式分数表达（数学等价）。

### 5.6.4 碰撞距离框架与认证外推不变族（z 区探针；grid_ortho + parseval/partial/pairdirichlet/pairbound/rowsum/incoherence 共 7 个已并入合并版，v2.1）

- **碰撞完备刻画**（probe_collision/probe_tchar）：精确碰撞 ⟺ 角度有理（全构造性 iff）；有理时最小碰撞距离 = 分母（纯网格 q=1 恰为 N；偏移分母 q 把碰撞推至 q·N——"零成本旋钮"）；**无理偏移（黄金比）⟹ 永无精确碰撞**；**线性偏置（ALiBi）无碰撞端点**（非周期核，碰撞距离 = ∞）。
- **μ=0 能量守恒等式**（probe_parseval）：互异网格原子在 a·N 窗口 ‖Σc_t·u_t‖² = Σ|c_t|²（等式而非界——框架界退化端点）。
- **窗口无关 Dirichlet 部分和界**（probe_partial）：j ≢ 0 (mod N) ⟹ ‖Σ_{k<W} e^{2πikj/N}‖ ≤ N/(2·min(j mod N, N−j mod N))，窗口无关。
- **任意角度对 Dirichlet 界与混合网格相干界**（probe_pairdirichlet）：任意角度 t1 t2，差频 = 2π·j/N（j mod N ≠ 0）⟹ 任意窗口 W 上 ‖Σ e^{ik·t1}·conj(e^{ik·t2})‖ ≤ N/(2·min(j mod N, N−j mod N))（`pair_dirichlet`）；推论 `mixed_grid_coherence`：嵌套网格 N 与 a·N 两原子跨网格相干界——grid 崩塌后多尺度设计空间的定理。
- **U5 黄金近碰撞半径**（probe_nearcoll，皇冠）：∀ d ≥ 1、∀ m ∈ Z：**|d·φ_gold − m| ≥ 1/(3d)**（代数数范数路线，`square5_zero` 零公理）——近碰撞不能快于 O(1/d) 聚集；与 C5/T2 合成 offset-grid 的完整定量辩护（碰撞谱双向挡死）。
- **τ 三分**（probe_taudicho，零公理）：碰撞质量 τ 的窗内/OOD/三分刻画。
- **素数阶梯分辨率与最优性**（`src/CRTResolve.v` + probe_ladderlimit）：存在性 `prime_ladder_8` + `prime_ladder_8_pairwise_coprime`（8 素数链 [3,7,13,29,59,127,251,503]，两两互素）+ 分辨率 `crt_inj`（联合模单射，lcm ≈ 7.49×10¹² ≫ 8× 视界）+ **最优性 `no_nine_band_ladder`**（**[3,511] 不存在 9 元素素数阶梯**，贪心交换论证，贪心链 113/211/397 更紧）——素数叙事完整（存在性 + 分辨率 + 最优性），支撑论文 B 素数阶梯受控对照（prime-7 vs prime-8）。

### 5.6.5 分级证书、一般维张量与核漂移（z 区探针）

- **容错 Gershgorin**（probe_robust）：坏对每行 ≤ δ·n ⟹ 绝对行和 ≤ n·(μ+δ)；**μ+δ ≤ 4/5 ⟹ 通过帕累托阈值**——检查器从二元升为分级证书。
- **一般维张量**（probe_tensor）：N 轴张量积 off-diag 行和 ≤ **(1+r)^N − 1（∀N 闭式）**——论文 B §6 跨维推测得证（2D/3D/4D 为 N=2/3/4 特例）。
- **核漂移（T4 完全体，已并入 PSA_framework PhaseCoherence）**：`kernel_drift_controls_attention`——核逐点漂移 ≤ dc、系数 ℓ1 ≤ dd ⟹ **softmax ℓ1 TVD ≤ e^{2·dc·dd} − 1**（`coherence_controls_attention` 的核漂移姊妹定理）；`kernel_identical_tvd_zero`：K=K' ⟹ 界=0——网格族（任意 a·N 窗口核相同）"注意力核表示级不变性"的证书 0 端点。
- **ρ^{−3/2} 紧界三件套**（probe_pairbound ① + probe_rowsum ② + probe_witness ③，2026-08-22 全部 Qed）：逐对界 ‖⟨ψ_a,ψ_b⟩‖ ≤ sin(πa/b)·√(ab)/(2(b−a))（`pair_inner_norm`，Jordan 分母，逐对 Θ(ρ^{−3/2})）；行和重组 **`row_sum_3halfs`**：C-稀疏梯子任意行 ≤ 2π·C^{−3/2}/(1−C^{−3/2})，**`row_bound_C4`：C=4 行和 ≤ 2π/7 ≈ 0.898 < 1——1D C=4 从空洞（2>1，仅存在性）变真实框架界**；**见证封顶（③ probe_witness）**：见证对 (2,2C) 精确内积 `witness_exact` = sin(π/(2C))/√C，且 **`witness_sandwich`：(1−1/C)·[上界] ≤ 见证值 ≤ [上界]——上下界之比 ≥ 1−1/C，C→∞ → 1（Θ(C^{−3/2}) 紧性封顶，机器检查）**；常数演进线 4K → 2K → Θ(C^{−3/2})（紧）封顶。风险清单更新：求和窗口口径已对齐 Fpair（消除）；decay_bound 新界接口实例化待 src 侧；K0=32 高维联动不承诺。

**意义**：本族与 §5.1–5.5 认证链正交，构成"认证（正）— 可证明性边界（负定律）— 碰撞/分辨率刻画（机制）"三角；offset-grid（无理偏移）的证书保持（T1a/Parseval）、零精确碰撞（C5）与近碰撞护城河（U5）三半均机器检查。**配套实验已完成（论文 B §8.4，2026-08-22）**：offset-grid @4096 16.12±1.32——ogrid ≥ grid 确认（碰撞机制第 6 个正向判决）+ **证书免费性被证伪**（μ=0 精确正交 ∧ 零精确碰撞仍差 rand 2.4×）——与 P3 定理互证：**可证性（稀疏）与外推性（稠密）在实证与定理双轨分离**。

### 5.6.6 压缩感知：RIP 与稀疏唯一性（probe_incoherence.v，CS-1/2/3，2026-08-23 新增）

> 本小节把 §5.1–5.5 的「框架界/表示稳定性」推进到**压缩感知级**：频率阶梯原子族不仅
> 构成稳定框架，还满足**低相干 → RIP → 稀疏唯一恢复**的完整链条。48 Qed / 5 主定理 /
> 0 Admitted / 0 Axiom，已并入合并版（全量合并编译通过）。

- **原子规范（IC1）** `psi_norm_one`：1 ≤ n ⟹ ‖ψ_n‖²_{pred n} = 1——频率阶梯原子族单位范数
  （phi=rot 桥 + 零前缀 Csum 消除 + `phi_l2_norm` 闭式）。
- **RIP 基元（CS-2）** `rip_bound2`：μ-不相干单位原子（|⟨u1,u2⟩_W| ≤ μ）⟹
  |‖c1u1+c2u2‖²_W − (c1²+c2²)| ≤ μ·(c1²+c2²)——Gershgorin 型 RIP(2,μ) 界；支撑链
  `norm_sq_combo2`（2 原子范数平方显式展开：Σc² + 2c1c2⟨⟩）。
- **稀疏唯一性（CS-3）** `sparse_uniquenessM`（主定理）：0 ≤ μ、单位范数、两两相干 ≤ μ、
  **μ·(M+1) < 1** ⟹ 窗口内零组合 Σ_{j≤M} c_j·u_j ≡ 0 ⟹ 系数全零——M+1 个原子的**稀疏表示
  唯一恢复**；证明链：`rip_lower_M`（RIP 下界归纳，Σc_j² ≤ l2 + μ(M+1)Σc_j²）→ l2=0
  （零组合）→ (1−μ(M+1))Σc_j² ≤ 0 → Σc_j² = 0 → `sum_sq_zero` 逐项归零；基元
  `sparse_uniqueness2`（M=1 最小实例）。
- **意义**：本开发首次获得**可认证稀疏恢复**的理论保证——与框架界正交（框架界 = 表示存在
  且稳定；RIP/唯一性 = 稀疏表示唯一可恢复）；与 ρ^{−3/2} 行和紧界（§5.6.5，C=4 行和
  2π/7 < 1）合成时，频率阶梯在 C=4 同时满足框架界与低相干前提，是「稀疏 + 稳定」双证书
  的机器检查基础。

## 6 提取与可执行检查器

- PSA_extract.v → psa_guard.ml → ocamlc 字节码 exe → psa_guard_ffi.py；核心判定函数由 Coq `Extraction` 机制生成 OCaml（非手动翻译）；`main.ml` 为 CLI 包装（手动，仅 I/O 十进制转换）；`frame` 的原生整数镜像（`frame_check_instance_int`）因效率手动重写（规避 Peano 大数栈溢出），与 Coq 定义的等价性为逐行镜像 + FFI 24/24 交叉校验（非机器证明）。
- 自测 24/24（PSA_refcheck.v 20 项 Check/Eval + 4 项整数行和验算）。
- **范围前提（如实声明）**：整数镜像与 Coq nat 的等价仅对中间量不超过机器字长（OCaml int，63-bit）的阶梯成立；实验中阶梯值 ≤255 安全，对极大输入（≥10⁶ 级）sparse 等走 Peano 提取的子命令仍会栈溢出。
- **定量安全阈值（系统扫描修正）**：行和判定按 num,den 连乘累加，累积分母 ≈ ∏ pair_den（指数增长）。114 阶梯扫描实测：末带 < 2^20 的阶梯中仍有 14/89（15.7%）exe 与 Coq 语义分歧（如 C=6-sparse [3,19,115,691,4147]：Coq 语义 true、exe 溢出误判 false，累积分母达 10^26 ≫ 2^63）。实验实际使用（带值 ≤255、m ≤ 8）全部落在 63-bit 安全区；通用安全阈值须逐梯核算 ∏ pair_den < 2^63（或改用任意精度 Zarith/Python 大整数）。
- **int 平方根实现**：`int_sqrt n = int_of_float (Float.sqrt ...)` 为浮点近似；对 n < 2^53 截断后偏差 ≤ 1，仅在判别阈值附近才可能翻转（如实声明）；安全阈值收紧为中间量 < 2^53。
- **健全性闭环**：`frame_check_instance_sound` 已 Qed——判定通过 ⟹ gershgorin_frame_mu (length I) (S (last I)) (4/5)，检查器 = 框架界定理的可执行投影。
- **反射层纠错实例（形式化发现并修复真 bug）**：反射层原 `row_sum_frac_aux` 在收缩列表上重算 nth，使 Coq 判定与生产原生检查器不一致（[3,13] 误判 false、C4 行和退化为 (0,0) 空洞通过）；加 orig 参数修正后 Coq 与原生逐行同构（FFI 24/24 复核）。
- **方法论教训：逐行同构原则**——"定义等价"不足以保证提取保真性（`row_sum_frac_aux` 的两个版本数学上定义等价，但在收缩列表上计算路径分叉）。提取代码应尽可能镜像 Coq Fixpoint 的结构，而非依赖高阶重写得到的"语义等价"的另一份代码。

## 7 公理记账（审计小节）

- **审计总量**：PSA_audit.v **165 项** Print Assumptions，RC=0，零 Admitted（111 段 Axioms + 54 项 Closed）。
- **公理脚印（全部 165 项仅此）**：ClassicalDedekindReals.sig_not_dec / sig_forall_dec + functional_extensionality_dep（标准库反射层基础设施）；**`Classical_Prop.classic` 出现 0 次**。
- **如实说明**：sig_not_dec / sig_forall_dec / fext 是非构造性选择类原则（Dedekind 实数构造自身携带，非应用层引入）；"classical-free"精确指 `Classical_Prop.classic`（排中律宏）零出现，而非"无任何经典原则"。提取计算性：上述公理仅在证明层（Prop）使用，不参与提取的计算内容（Set/Type 层无 sig_not_dec 调用）。
- **M1.5 经典清零（已完成）**：此前仅剩的 4 项（softmax 系列 + certified_attention_approx）经 exp 单调性继承经典排中。现 Module ExpSeries 已 Qed（`exp_mono_le_noclassic` 等，Stdlib exp 即幂级数定义），exp_mono_le 改走幂级数路线——语句不变、下游零改动。**意义**：整个 CertifiedAttention 模块（注意力近似主定理）为纯构造性——据我们所知，这是第一个不依赖实数完备性排中律的深度学习注意力形式化验证。
- 依赖库（ca_* 六库）全审计为 P4 长期项。

## 8 实证预览

char 级 0.5M 参数（0.43M–0.63M 视模式）、T_train=512、种子 {1337,42,7}、确定性协议：

| 方案 | 512 | 1024 | 2048 | 4096 |
|------|-----|------|------|------|
| rope（b32 三个种子） | 4.44±0.08 | 6.77±0.07 | 13.68±1.21 | 25.30±4.63 |
| **psi-rope [3,13,53,213]（本证书对象）** | 4.70±0.14 | 5.64±0.07 | 8.42±0.10 | 12.75±0.34 |
| **psi-rope 七带 [3,…,255]（T8 复合证书对象）** | 4.53±0.10 | 4.75±0.06 | 8.28±0.28 | **12.40±0.74** |

psi-rope 行 3 个种子均值±std、dense 单个种子（b64 s1337）、rope 为 b32 3 个种子均值±std——定位为 teaser，完整实证与机制分析见配套论文 B。

## 9 相关工作

- **Transformer / 注意力形式化**：rocq-transformer（Rocq 实现）验证 transformer 结构与注意力的类型化实现；本开发与之差异在保证层级——rocq-transformer 验证实现与类型，本开发验证解析核的数值保证（框架界/衰减界/能量预算）——互补而非竞争。
- **Certified ML kernel**：Certificates in AI: Learn but Verify（2025）明确"学习 + 验证"分离主张，与本开发边界完全一致；Coq/OCaml 提取谱系（CompCert 式 proof-carrying kernel、CertiML 类）提供方法论先例——本开发新增的是反射检查器自带健全性证明这一层。
- **Proof-carrying code 谱系（Necula）**：本开发的反射检查器是 PCC 思想的现代实例——运行时布尔判定 + 机器检查的健全性定理，等价于"证书随代码传输、接收端可验证"；差异是证书内容为有理常数界（可判定算术）而非类型/内存安全证明。
- **稀疏注意力无证书方法（对比面）**：top-k 门控、KV 逐出、低秩投影均无误差证书；本开发覆盖的"解析核"层给出可检查保证。
- 与论文 B 的关系：本文实证结果验证论文 A 形式化框架（同一阶梯族）的适用性；论文 A 的框架界/能量界为"免修改 + 证书"定位提供理论支持——主张正交：形式化保"表示稳定性/能量有界"，实证报"外推 ppl"。

## 10 局限性

- **高维证书的定位**：3D 定理是形式化体系的关键组成部分，它证明验证方法学在高维逻辑闭合，并机械固定"维数灾难"的精确表达式（1D μ=0.8 → 3D M_bound=3968）。但定位是"Theoretically Composable, Practically Non-Tight"：(i) H_dom 尚未反射化（N≥3，真值可在 O(n₁n₂n₃·(n₁+n₂+n₃)) 次比较内完全判定，但我们尚未为其编写反射判定器）；(ii) H_dom 经验苛刻（真实数据三轴频率独立增长，要求三轴同调增长很少满足）。2D-wide 不受此限制（免 H_dom）。
- 学习分量（W_Q/W_K、softmax 身份）不在覆盖内——覆盖的是**敏感性**而非身份。
- **What is not certified**：本框架不证明——(a) 学习投影下的注意力 logits/softmax 有界（仅能量界 ⟹ 输出扰动界）；(b) 学习 Q/K 投影与位置旋转对易（酉不变性仅覆盖基函数层）；(c) 多头拼接、残差连接、LayerNorm/激活的数值稳定性；(d) 训练后权重的任何保证（证书对任意系数 c 成立，与训练无关）；(e) 外推 PPL 与框架界之间的语义联系（经验桥梁，未形式化）。
- 证书为框架/能量级保证，不直接给出端到端 ppl 界（跨层合成为未来工作）。
- 审计 165 项全零 classic；公理脚印仅 sig_not_dec + sig_forall_dec + fext。
- 实证规模 toy 级、种子有限（dense/rope 已补；NoPE 单个种子）。
- **形式化的适用域以结构存在为前提**：对无位置结构的编码（NoPE 类）本框架无任何可证陈述。论文 B 实证给出定量交易曲线：有结构端以分布内 ppl ~2× 劣化（4.46 vs 9.06）为代价承受 OOD 相位混淆风险；形式化锁定的正是交易中有结构的一端。

## 11 结论

生成 → 守卫 → 门控 → 衰减 → 框架 → 截断 → 稳定性 → 注意力近似 → **实例证书（有理、可判定）** → 长度一致性（∀N≥214）→ T8 复合证书 → **反射检查器及其健全性定理（165 项审计，全部零经典排中）**：一条完整的、零 Admitted 的**表示层认证管线**——为解析核保证服务，与论文 B 的实证性能正交。

**可组合的反射化（方法论贡献）**：反射检查器的健全性证明是可组合的——3D 张量核的静态定理与 1D `gershgorin_frame_mu` 共享同一骨架，其反射化是提取链的直和扩展而非基础理论修正。宽轨家族 2D/3D/4D 成员齐备（N 维公式 M_bound^{(N)} = (C³/2)·((1+4K_C)^N − 1) 的 N=2/3/4 校验全部定理级成立，且组合指数增长部分已升为 ∀N 定理，§5.6.5）。客观地讲，3D/4D 证书当前是非紧的存在性结果，其价值在架构可组合性与维度推广的定位，而非常数本身；1D 证书（μ=4/5）保持紧且不受影响。

**可证明性边界（v2.0 新增，§5.6）**：在认证管线之上，本开发把论文 B 的"性能-可证明性张力"从实证观察升格为定理——**稠密覆盖与 μ≤4/5 可判定认证互斥**（`pareto_law_main`/`pareto_law_N511`：N=511 时 m≥10 必拒；P1/P1′ 给出精确窗口口径相干下界的解析根源；T2a/T2b 把负定律延伸到随机阶梯高概率拒绝）。配套的碰撞距离框架（碰撞 ⟺ 有理、最小距离 = 分母、无理偏移零碰撞、ALiBi 无碰撞端点、Parseval 能量守恒、窗口无关 Dirichlet 界、容错 Gershgorin 分级证书、一般维张量闭式、核漂移 softmax TVD 界）为论文 B 的 τ/碰撞机制提供形式化镜像——"认证—可证明性边界—碰撞/分辨率刻画"三角被机器检查覆盖，零 Admitted、零自定义公理。

**压缩感知（v2.1 新增，§5.6.6）**：频率阶梯原子族获压缩感知级理论保证（单位范数 `psi_norm_one` + RIP(2,μ) `rip_bound2` + 稀疏唯一恢复 `sparse_uniquenessM`，48 Qed 并入合并版）——「无条件基 + 频率阶梯」从表示稳定性推进到稀疏恢复唯一性，与论文 B 的随机稀疏恢复主张构成定理侧支撑。

## 参考文献

1. Su, J., Ahmed, M., Lu, Y., Pan, S., Bo, W., Liu, Y. RoFormer: Enhanced Transformer with Rotary Position Embedding. Neurocomputing, 568:127063, 2024.（arXiv:2104.09864, 2021）
2. The Rocq Development Team. The Rocq Prover, version 9.0. 2025.（原 Coq，Rocq 9.0.1 本开发所用）
3. Mahboubi, A., Tassi, E. Mathematical Components. 2016–. https://math-comp.github.io/mcb/.（mathcomp 依赖；期刊替代引用：Gonthier, G., Mahboubi, A. An Introduction to Small Scale Reflection in Coq. Journal of Formalized Reasoning, 3(2):95–152, 2010.）
4. Boldo, C., Lelay, S., Melquiond, G. Coquelicot: A User-Friendly Library of Real Analysis for Coq. Mathematics in Computer Science, 9(1):41–62, 2015.（Coquelicot 依赖）
5. Necula, G. Proof-Carrying Code. POPL '97, pp.106-119, 1997.
6. Barrett, C., Henzinger, T.A., Seshia, S.A. Certificates in AI: Learn but Verify. Communications of the ACM, 69(1):66–75, 2026.
7. [论文 B 中文规范版]：相位截断频率阶梯：可认证且外推稳健的位置编码（本工作配套，TACL 方向）。
7a. [论文 A 预印本]：Wang, B., et al. Certified Sparse Gating and Attention Approximation: An Executable Coq Development. Preprint, Figshare, 2026. DOI: 10.6084/m9.figshare.33312189.（2026-08-22 发布）
7b. [论文 B 预印本]：Wang, B., et al. Phase-Truncated Frequency Ladders: Certified, Extrapolation-Robust Positional Encoding. Preprint, Figshare, 2026. DOI: 10.6084/m9.figshare.33312336.（2026-08-22 发布）
8. 卷期页码已经 2026-08-21 文献数据库核查校准（核查报告：《参考文献真实性核查报告》）。

## 附录 复现指引

- **代码分布**：形式化代码 `src/`（`_CoqProject` 声明 load path；各模块独立编译命令见经验卡 E067/E077）；探针 `z/`；**合并版 `src/ca_merged_full_24.v`（75702 行，40 模块含 7 个 z 区探针，`_merge_ca.py` 重新生成，合并编译 MERGE_EXIT=0）**；归档基态 `30模块/`（ca_* + 7 探针 pro 版 + ca_zeta_euler + 合并版，SHA-256 与 src/z 一致）。
- **依赖版本**：Rocq/Coq 9.0.1；mathcomp（本地 vendored）；Coquelicot；Windows 10+ / PowerShell 7。
- **构建命令**：各模块独立编译 `coqc -Q <src> "" -Q <z> "" -Q <mathcomp> mathcomp -Q <Coquelicot> Coquelicot <file>.v`；合并版重新生成 `python src/_merge_ca.py` 后合并编译。
- 提取链：`PSA_extract.v` → `psa_guard.ml` → `psa_guard.exe`（DkMLNative ocamlc 字节码 + camlrun）；FFI 自测 `python psa_guard_ffi.py`（24/24）。
- 审计证据：`AI注意力算法\审计证据\audit_run.txt` 等。
- 实验代码与数据：`psa_empirical/`（length_extrap.py 等，3 个种子固定 {1337,42,7}，见论文 B 附录 B）。
- 关键定理行号：ChampionCertificate L4582–5150（定理本体 L5075）、FrameCheck2DNarrow L5166–6290。
