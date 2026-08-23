# Certified Sparse Gating over Phase-Truncated Frequency Ladders
## A Coq Formalization of Representation Stability and Sparse Recovery Guarantees

> 正式版（2026-08-23，对齐当前代码基态）。来源：论文 A 草稿清洗（删除会话/评审/版本内部注记），
> 全部代码数字按 2026-08-23 基态核验。投稿方向：CPP/ITP（形式化方法）。
> 代码基态：`src/`（正式模块）+ `z/`（探针）+ 合并版 `src/ca_merged_full_24.v` + 归档 `30模块/`。

---

## Abstract (EN)

We present a Coq formalization of certifiably-gated sparse attention
over a geometrically-structured frequency basis. Our development proves, in two orthogonal
certified tracks — representation stability and attention perturbation — with no single
dependency chain joining them: (i) a deterministic greedy gate extracting subsets passing a
decidable sparsity-growth check; (ii) pairwise coherence decay and Gershgorin-type frame
bounds (1±μ)‖c‖² for the selected sub-basis; (iii) row-truncation energy budgets;
(iv) softmax ℓ₁ stability under ℓ∞ logit perturbation; and (v) a certified attention
approximation theorem: if the dropped spectral energy per row is ≤ ε, the attention output
deviates by at most (e^{2√ε}−1)·V_max. For the concrete geometric ladder [3,13,53,213]
(C=4), we prove an instance certificate with frame bounds [1/5, 9/5] (μ = 4/5), where every
constant is a rational number obtained by one-sided domination of transcendental bounds —
the certificate layer is decidable rational arithmetic, extractable as-is. This pattern is
generalized to any ladder by a reflective checker `frame_check_instance` with a machine-checked
soundness theorem (checker pass ⟹ Gershgorin frame bounds). For the structured-ladder
champion [3,7,15,31,63,127,255], a composite certificate (frame core + edge energy budget +
coherence cross-term bound) is proved: (S − coh_e5) ≤ ‖F‖² ≤ (S + coh_e5) — a
**basis-representation stability bound**, not attention scores or extrapolation PPL; the
bridge to empirical PPL gain is an empirical observation, not a formal consequence.
Beyond certification, we prove a **provability-boundary** theorem family (dense coverage and
μ ≤ 4/5 checker certification are mutually exclusive; more than 9 phase-complete bands in
[3,511] must be rejected), a **collision-distance** framework for the τ mechanism (exact
collisions occur iff the angle is rational; irrational offsets never collide), and — new in
this version — a **compressed-sensing** family: the phase-truncated ladder atoms have unit
norm, satisfy an RIP(2,μ) bound, and admit sparse-recovery uniqueness (μ·(M+1) < 1 ⟹ zero
combination ⟹ all coefficients zero), all machine-checked. The audit comprises 165 Print
Assumptions entries (PSA_audit.v) with zero `Classical_Prop.classic` at the application
layer; the only axioms are the standard Dedekind-real infrastructure (sig_not_dec,
sig_forall_dec, functional extensionality) — non-constructive choice-like principles
inherent to the real-number construction, not introduced by our application layer. Full
constructivity is not claimed. Companion paper B provides the empirical validation of the
same ladder family; this work supplies the formal guarantees.

---

## 1. Introduction

稀疏/近似注意力方法（top-k 门控、KV 逐出、低秩投影）在实践中有性能优势，但均无误差证书。
本工作采用「验证解析核、学习其余」（verify the analytic kernel, learn the rest）的路线：
在解析核层（稀疏门控、频率基、截断能量、softmax 稳定性）提供机器检查的保证，而学习分量
（W_Q/W_K/W_V/W_O、softmax 身份、训练后权重）不覆盖。

**贡献清单**（与代码一一对应，全部 Coq 机器检查，零 Admitted / 零自定义公理）：

1. **确定性门控的形式化**（GreedyGate）：原文概率门控前提不可满足（(INR N)²p²<1 恒假，
   已给反例），本工作裁决并证明确定性平方门 M=C² 是唯一可行路线。
2. **有限化守卫衰减界**（PSA_Pipeline）：全局增长前提 → 运行时可判定检查，系数 2/√C 与
   tight 1/√C 两版。
3. **行截断能量预算**（RowTruncation）与 **softmax 稳定性**（SoftmaxStability：
   ‖softmax z − softmax z'‖₁ ≤ 2(e^d − 1)）。
4. **认证注意力近似**（CertifiedAttention）：谱能量 ≤ ε ⟹ 输出偏差 ≤ (e^{2√ε}−1)·V_max。
5. **实例证书**（Gershgorin + InstanceCertificate）：对 C=4 阶梯 [3,13,53,213] 证明框架界
   [1/5, 9/5]（μ=4/5）——参数化最坏情形 1±4K(C) 在 C=4 空洞成立的问题就此终结。
6. **有理支配方法论**（可判定性溢价）：证书全部常数经 floor-sqrt / Jordan / Dirichlet
   的单侧松弛化为有理数，`compute; field` 封口——零数值策略、零区间算术、可判定、可提取。
7. **可执行提取**：门控/检查器 → OCaml（psa_guard.exe）→ Python FFI，24/24 参考值对齐。
8. **反射检查器及其健全性**（FrameCheckInstance）：`frame_check_instance` 把「任意阶梯 →
   μ≤4/5」做成可判定有理判定，提取为原生 int 镜像；`frame_check_instance_sound` 证明判定
   通过 ⟹ Gershgorin 框架界——实例证书推广为通用运行时判定。
9. **基表示稳定性复合证书**（核心展示定理）：论文 B 的七带基线阶梯 [3,7,15,31,63,127,255]
   获得机器证明的平方范数复合界 (S−coh_e5) ≤ ‖F‖² ≤ (S+coh_e5)（全矩阵相干加权、对称交叉项
   界）。该复合界是**基函数范数稳定性保证**，不涉及注意力分数/softmax/PPL；与外推 PPL
   改善之间的桥梁是经验观察，未经形式化。
10. **高维组合性演示**（2D-wide/3D/4D）：同一 `abstract_unconditional_basis` 骨架逐轴
    实例化到任意维——价值在骨架复用与维度推广可行性证明（"Theoretically Composable,
    Practically Non-Tight"），常数非紧，定位为上界证书 + 组合性演示，非实用框架界。
11. **可证明性边界**：稠密覆盖与 μ≤4/5 检查器认证互斥（`pareto_law_main`）；N=511 时
    m ≥ 10 必被拒绝（`pareto_law_N511`）；随机 log-uniform 阶梯 whp 被拒绝（T2a/T2b）。
12. **碰撞距离框架**：精确碰撞 ⟺ 角度有理（构造性 iff）；最小碰撞距离 = 分母；无理偏移
    永无精确碰撞；线性偏置（ALiBi）无碰撞端点——τ 机制的形式化碰撞结构。
13. **压缩感知级理论保证**（新增）：频率阶梯原子族单位范数（psi_norm_one）、RIP(2,μ) 型界
    （rip_bound2）、稀疏恢复唯一性（sparse_uniquenessM：μ·(M+1) < 1 ⟹ 零组合 ⟹ 系数全零）——
    把「无条件基 + 频率阶梯」的理论优势从框架界推进到稀疏恢复。
14. **部署级证书族**：KV 逐出/量化扰动/多头合成的 softmax 稳定性证书，TVD 常数有理化
    （检查器可判定）。

**覆盖边界（What is not certified）**：学习到的权重（W_Q/W_K/W_V/W_O）、Q/K/V 投影与多头
拼接、LayerNorm/激活的数值稳定性、残差累积误差、外推 PPL 与框架界之间的语义联系——均在
「learn the rest」一侧。证书链是**两条正交的定理簇**（表示稳定性轨 / 注意力扰动轨），
无依赖桥接；「certified」精确指解析核层，不构成模型/外推性能证书。

## 2. Formalization Overview

- **主模块** `src/PSA_framework.v`：**6659 行 / 18 个 Module / 265 Qed / 零 Admitted**
  （2026-08-23 复核）。模块链：RuntimeGuards → SeqProps → PSA_Pipeline → GreedyGate →
  RowTruncation → PipelineEndToEnd → ExpSeries → SoftmaxStability → CertifiedAttention →
  Gershgorin → InstanceCertificate → M4bLengthConsistency → T8CoreCertificate →
  FrameCheckInstance → ChampionCertificate → FrameCheck2DNarrow → UnitaryInvariance →
  PhaseCoherence。
- **合并版** `src/ca_merged_full_24.v`：**75702 行 / 40 模块**（30 个 ca_* + PSA_framework +
  独立模块 + **7 个 z 区探针**：probe_grid_ortho/parseval/partial/pairbound/rowsum/
  pairdirichlet/incoherence），`_merge_ca.py` 重新生成，**全量合并编译 MERGE_EXIT=0**。
- **z 区探针（并入合并版 7 个）**：grid_ortho 18 Qed / parseval 17 / partial 15 /
  pairbound 5 / rowsum 21 / pairdirichlet 4 / incoherence 48——各独立编译 EXIT=0 +
  合并编译双通过。
- **审计**：PSA_audit.v **165 项** Print Assumptions，RC=0，零 Admitted；全部 165 项
  `Classical_Prop.classic` 零出现；公理脚印仅 sig_not_dec / sig_forall_dec / fext
  （标准 Dedekind 实数基础设施，如实声明）。
- **依赖**：Rocq 9.0.1；mathcomp（ssreflect/ssrbool/ssrnat/seq/eqtype/div/prime）；
  Coquelicot。外部依赖仅此二者。

## 3. Core Theorems

```
greedy_selected_correct (C) (vals) : C ≥ 2 → Sorted lt vals → all_ge_2 vals →
  let sel := greedy_selected (C*C) vals in
  Sorted lt sel ∧ NoDup sel ∧ all_ge_2 sel ∧ check_c_sparse_on_vals sel C = true

psa_gated_decay (seq) (I) (C) : 平方门控子集上 ‖⟨ψ_i,ψ_j⟩‖ ≤ 1/(√C)^|i−j|

gershgorin_frame_mu : 单位向量系 + 行非对角和 ≤ μ < 1 →
  (1−μ)‖c‖² ≤ ‖Σ c_i ψ_i‖² ≤ (1+μ)‖c‖²

softmax_l1_bound_exp : ‖z−z'‖∞ ≤ d → ‖softmax z − softmax z'‖₁ ≤ 2(e^d − 1)

certified_attention_approx : 逐行丢弃谱能量 ≤ ε →
  ‖attn_out − attn_out_approx‖ ≤ (e^{2√ε} − 1) · V_max

frame_check_instance_sound (I) : 0 < length I → frame_check_instance I = true →
  (1 − 4/5)·‖Σ c_i·phi i‖² ≤ ‖Σ_{k<M} (Σ_{i<n} c_i·phi i k)‖² ≤ (1 + 4/5)·‖Σ c_i·phi i‖²
  (* 反射检查器健全性：判定通过 ⟹ 任意阶梯 μ=4/5 框架界 *)

tensor_product_unconditional_basis_2d_wide (C) : C > 2 → 双轴稀疏增长 → 免 H_dom →
  (1 − M_bound)·S ≤ ‖F_2D‖² ≤ (1 + M_bound)·S   (* 上界证书，M_bound_2d_wide 4 = 768 *)

tensor_product_unconditional_basis_3d (C) : C > 2 → 三轴稀疏增长 → H_dom → 混合进制距离 ≤6 →
  (1 − M_bound)·S ≤ ‖F_3D‖² ≤ (1 + M_bound)·S   (* 上界证书，M_bound_3d 4 = 3968，下界平凡 *)

champion_e5_composite_certificate : length coeffs = 7 →
  (S − coh_e5) ≤ ‖Σ_{i<7} c_i·ψ_{e5_bands[i]}‖²_{255} ≤ (S + coh_e5)
  (* 七带基表示稳定性复合界 *)

pareto_law_N511 : 检查器通过 ∧ m 条相完备带 [3,511] → 3·c^(m−1) ≤ N ⟹ m ≥ 10 必被拒绝

golden_near_collision_gold : ∀ d ≥ 1, ∀ m ∈ Z: |d·φ_gold − m| ≥ 1/(3d)

(* ── 压缩感知族（probe_incoherence.v，48 Qed，已并入合并版）── *)
psi_norm_one (n) : 1 ≤ n → l2_norm_sq (psi n) (pred n) = 1

rip_bound2 (u1 u2) (W) (c1 c2 mu) : ‖u1‖²_W = 1 → ‖u2‖²_W = 1 → |⟨u1,u2⟩_W| ≤ mu →
  |‖c1·u1 + c2·u2‖²_W − (c1² + c2²)| ≤ mu·(c1² + c2²)

sparse_uniquenessM (M) (c) (u) (W) (mu) : 0 ≤ mu → ∀j≤M: ‖u_j‖²_W = 1 →
  ∀i≠j≤M: |⟨u_i,u_j⟩_W| ≤ mu → mu·(M+1) < 1 → ∀k≤W: Σ_{j≤M} c_j·u_j(k) = 0 →
  ∀j≤M: c_j = 0
```

## 4. Instance Certificates（C=4 / T8 / 七带复合）

### 4.1 C=4 实例证书 [1/5, 9/5]
对象：C=4 可见子梯 [3,13,53,213]（N=512 窗口内列范数 = 1）。教科书式 11 步结构：
`psi_unit_norm`（对角 = 1）→ 六个有理对界 `pair_3_13` … `pair_53_213`（如 13/40、
11289/33920）→ 四个行和引理 `c4_row0..3`（各 ≤ 4/5）→ `gershgorin_frame_mu` 一次实例化
⟹ **[1/5, 9/5]**。**长度一致性** `certified_c4_frame_bounds_anyN`：∀N≥214 成立（O(1)
证书对一切序列长度）。

### 4.2 T8 复合证书核
E5'' 七带的隔带子核 [3,15,63,255]（T8CoreCertificate，11 Qed 零 classic，μ=4/5）——
覆盖最优阶梯的认证核。

### 4.3 七带复合证书 `champion_e5_composite_certificate`
论文 B 的七带基线阶梯 E5'' [3,7,15,31,63,127,255] 被反射检查器判 false（健全但非完备，
有理松弛不足以证明），其**精确**相干行和仅 0.135 ≤ 4/5——实质可认证。核-边缘分解交付
**部分证书**：T8 核通过检查 + 边带能量预算 + 相干交叉项（21 对上三角 δ 表
`delta_e5` 经 `term_bound_upper/lower` 加权）⟹ 七带整体对称界
(S − coh_e5) ≤ ‖F‖²_{255} ≤ (S + coh_e5)。**紧度说明（如实）**：δ_e5 上界均为手工挑选的
保守有理数（floor-sqrt/Jordan/Dirichlet 单侧松弛），无最优性保证；该界是基函数范数稳定性
保证，与注意力/softmax/PPL 无关。

### 4.4 从实例到通用判定
同一配方推广为反射检查器 `frame_check_instance`（任意阶梯 → μ≤4/5 布尔判定，floor-sqrt
有理化 + nat 分数行和，全程可判定有理算术）。实例证书不再逐阶梯手工验算，而由一台自带
健全性证明的运行时检查器统一保证。

## 5. 可判定性溢价（Decidability Premium）

全部超越量被朝可判定方向单侧支配：√m ← ⌊√m⌋、|sin(πΔ)| ← Jordan 2Δ、Dirichlet 分子
|sin(πNΔ)| ← 1、（Tier 2 的 π ← 22/7）。**证书层只需要 ℚ**——运行时验证只做有理算术，
这是可提取性的根源。

**可判定性溢价**：精确 μ = 0.312 → 有理保守 μ = 4/5，因子 2.55——机器可检查性的已量化
代价。溢价是**设计对象**：松弛链的每一环（floor-sqrt / Jordan / Dirichlet / π←22/7）都可
枚举、可单独收紧、可机械组合（`cert_optimize` 方向，future work）。相邻对有理界极限
n₁n₂/(2(n₂−n₁)⌊√(n₁n₂)⌋) → √C/(2(C−1))（C=4 时 1/3）——松弛链的渐近代价有闭合形式。

**保守性（充分非必要）**：`frame_check_instance = true` 是框架界的充分非必要条件——存在
满足 Gershgorin 条件但因保守上界超 4/5 而被误拒的合法阶梯。系统扫描（114 阶梯 × 5 族）
实测假阴性 56/114（49.1%），集中于"有用"阶梯（C=2/3-sparse 12/13、几何奇带 9/9）。
被误拒的合法阶梯仍可由复合证书（§4.3）覆盖：「检查器通过 ⟹ 框架界」成立，「检查器失败
⟹ 不安全」不成立。

## 6. 反射检查器与提取（Coq soundness vs 运行时保证）

- **Coq 内健全性**：`frame_check_instance_sound` 已 Qed——判定通过 ⟹ Gershgorin 框架界，
  检查器 = 框架界定理的可执行投影。
- **提取链**：`PSA_extract.v` → `psa_guard.ml` → `psa_guard.exe`（DkMLNative ocamlc 字节码）
  → Python FFI（`psa_guard_ffi.py`，24/24 交叉校验）。
- **运行时保证的量化范围（如实）**：int 镜像（OCaml int，63-bit）只对小整数阶梯成立；
  浮点 `int_sqrt` 是近似（偏差 ≤ 1，仅判别阈值附近可能翻转）；累积分母 ∏ pair_den 指数增长，
  系统扫描实测末带 < 2^20 的阶梯中仍有 14/89（15.7%）exe 与 Coq 语义分歧（如 C=6-sparse
  累积分母达 10^26 ≫ 2^63）。实验实际使用（带值 ≤255、m ≤ 8）全部落在 63-bit 安全区。
  **因此**：运行时检查器**不自动携带** Coq soundness——它只在有限整数范围内、且与 Coq
  语义一致时接近。彻底消除：Zarith（任意精度）提取（future work）。**安全域谓词（评审建议，future work）**：当前"安全区"确认为实验性（扫描核算），未被形式化——未来工作在 Coq 中证明可验证的安全域谓词（输入在该谓词范围内 ⟹ OCaml int 镜像与 Coq 语义一致），或完成 Zarith 任意精度提取。
- **逐行同构原则**（方法论）：提取代码应尽可能镜像 Coq Fixpoint 的结构（而非依赖高阶重写
  得到的"语义等价"的另一份代码）——本开发在 FFI 回归（24/24）中持续检查，并据此发现并
  修复了反射层 `row_sum_frac_aux` 的真 bug（收缩列表重算 nth 致 Coq 与原生不一致）。

## 7. 高维组合性（2D-wide / 3D / 4D，上界证书）

- **对象**：φ3D(a,b,c)(k) = γ⁻¹·ψ_a(k)·ψ_b(k)·ψ_c(k)，γ = √(min(a,b,c)/(abc))；同一
  `abstract_unconditional_basis` 骨架逐轴实例化到任意维。
- **定位（如实）**：M_bound > 1 时下界 (1−M_bound)·S 恒负（如 C=4 的 3D：−3967·S ≤ ‖F‖²
  对非负范数恒真，**无信息量**）——证书的信息量在于**上界** (1+M_bound)·S（排除范数爆炸）
  + 组合性演示。故 3D/4D 定位为**「上界证书 + 组合性演示」**，**不称为框架界**。
- **2D-wide（免 H_dom）**：`tensor_product_unconditional_basis_2d_wide`（K0 = Rmax 8C³/4 或
  2D 口径 C³/2），数值裁决 `M_bound_2d_wide 4 = 768`（= 32 × 24），与论文 B 的 N 维公式
  M_bound^{(N)} = (C³/2)·((1+4K_C)^N − 1) 在 N=2 完全一致。
- **3D/4D 常数（如实）**：`M_bound_3d 4 = 3968`、`M_bound_4d 4 = 19968`——紧度在当前松弛下
  失效，正确归类为理论演示而非实用证书。
- **H_dom 反射化状态**：2D 窄轨的 H_dom 判定已做成可运行时检查（FrameCheck2DNarrow，
  单轴退化 n₁=1 ∨ n₂=1 情形，带健全性证明）；3D/4D 的轴间支配条件尚未编写反射判定器
  （可判定但未工程化）——3D/4D 证书是纯静态定理，为框架理论的纯粹扩展。

## 8. 可证明性边界与碰撞刻画

- **P2（单对触发）** `pair_bound_gt_4_5`：0 < n < n′ 且 d = n′−n < (5/8)√(nn′) ⟹
  保守对界 B(n,n′) > 4/5 ⟹ 行和 > 4/5 ⟹ 检查器拒绝。
- **P3（增长引理 + 主定理）** `pareto_law_main`：m 个相完备带 0 < f(0) < … < f(m−1) ≤ N
  且检查器通过 ⟹ 3·c^(m−1) ≤ N（c = ((5+√281)/16)² ≈ 1.8501）。**N=511 推论**：m ≥ 10
  必被拒绝。
- **随机版（T2a/T2b）**：同箱对触发 P2 ⟹ P(拒绝) ≥ 1 − (9)_m/9^m；m=7 ⟹ ≥ 96/100、
  m=8 ⟹ ≥ 99/100；m ≥ 10 由鸽笼确定性覆盖（`ten_bands_reject` 初等替代证明）。
- **碰撞距离**：精确碰撞 ⟺ 角度有理（`collides_iff_rational_witness`，构造性 iff）；
  最小碰撞距离 = 分母；无理偏移（黄金比）⟹ 永无精确碰撞（`irrational_offset_no_collision`）；
  线性偏置（ALiBi）无碰撞端点（`linear_bias_no_collision`）。
- **U5 黄金近碰撞半径**：∀ d ≥ 1、∀ m ∈ Z：|d·φ_gold − m| ≥ 1/(3d)
  （`golden_near_collision_gold`，代数数范数路线，零公理）。

## 9. 压缩感知：RIP 与稀疏唯一性（probe_incoherence.v，48 Qed）

频率阶梯原子族不仅构成稳定框架，还满足**低相干 → RIP → 稀疏唯一恢复**的完整链条：

- **原子规范** `psi_norm_one`：1 ≤ n ⟹ ‖ψ_n‖²_{pred n} = 1——频率阶梯原子族单位范数。
- **RIP 基元** `rip_bound2`：μ-不相干单位原子 ⟹ |‖c1u1+c2u2‖²_W − (c1²+c2²)| ≤ μ·(c1²+c2²)
  ——Gershgorin 型 RIP(2,μ) 界；支撑链 `norm_sq_combo2`（2 原子范数平方显式展开）。
- **稀疏唯一性** `sparse_uniquenessM`（主定理）：0 ≤ μ、单位范数、两两相干 ≤ μ、
  **μ·(M+1) < 1** ⟹ 窗口内零组合 Σ_{j≤M} c_j·u_j ≡ 0 ⟹ 系数全零——M+1 个原子的稀疏表示
  唯一恢复。证明链：`rip_lower_M`（RIP 下界归纳）→ l2=0（零组合）→ (1−μ(M+1))Σc_j² ≤ 0
  → Σc_j² = 0 → `sum_sq_zero` 逐项归零。

**意义**：本工作在**通用层**建立可认证稀疏恢复的理论保证（单位范数 + RIP(2,μ) + 稀疏唯一性，机器检查）；**具体实例拼接（如 C=4 的 μ·(M+1)<1 实例化，需精确 μ 值的 Coq 证明）尚未完成，为后续工作**；与 ρ^{−3/2} 行和紧界的合成为文本叙述而非形式化定理。**数学新颖性（如实）**：sparse_uniquenessM 是 Gershgorin/互干性唯一恢复定理的机器检查，数学上非新，形式化价值在 Coq 验证。本族（连同 parseval/partial/pairbound/rowsum/pairdirichlet）已并入合并版，
独立 + 合并双通过。

## 10. 部署级证书族（KV 逐出 / 量化 / 多头）

- **KV 逐出**：`kv_eviction_controls_attention`——softmax ℓ₁ TVD ≤ e^{2·dropped_mass} − 1，
  逐出代价 = 被逐质量的显式函数。
- **量化扰动**：`quant_column_controls_attention`——per-key 量化误差 e_j ⟹
  TVD ≤ e^{2·Σ_j |c_j|·e_j} − 1（INT8 per-channel 量化的显式证书）。
- **多头合成**：`multihead_output_bound`——逐头证书可组合性（加权输出的扰动 ≤
  Σ_h |w_h|·直径_h·(e^{2d_h}−1)）；`drift_top1_stable`——漂移源无关的 top-1 概率序保持。
- **TVD 常数可判化**：`tvd_rational_bound`——漂移 ≤ d 且 2d ≤ 1 ⟹ TVD ≤ 2d + (2d)²/2 +
  (2d)³/2，全有理、检查器可判定。

## 11. Audit（公理记账）

- **审计总量**：PSA_audit.v **165 项** Print Assumptions，RC=0，零 Admitted；原始证据
  `audit_run.txt`（111 段 Axioms + 54 项 Closed）。
- **公理脚印（全部 165 项仅此）**：sig_not_dec / sig_forall_dec + functional_extensionality_dep
  ——标准 Dedekind 实数基础设施，**非本开发应用层引入**；`Classical_Prop.classic`（排中律宏）
  **零出现**。「classical-free」精确指排中律宏零出现，而非「无任何经典原则」——完整构造性未声称。**外部依赖说明**：mathcomp / Coquelicot 未纳入 165 项审计，"零 `Classical_Prop.classic`"仅限本开发应用层，不推广到整个开发依赖（Coquelicot 基于实数库，可能含经典公理）。
  未声称。
- **M1.5 经典清零**：`Module ExpSeries` 已 Qed（exp 幂级数路线），`exp_mono_le` 改走级数
  路线，语句不变、下游零改动——整个 CertifiedAttention 模块为纯构造性（不依赖实数完备性
  的排中律）。
- **提取计算性**：上述公理仅在证明层（Prop）使用，不参与提取的计算内容——提取出的判定函数
  为纯构造性计算。
- **新定理族审计**：ParetoLaw/P1Coherence/ParetoRandom 仅 Stdlib Reals 自包含（其 165 项
  审计范围以 PSA_audit.v 为准，P1 的经典 MVT 路线在应用层外如实声明）；z 区并入合并版的
  7 探针各自 Print Assumptions 仅标准库公理。

## 12. Artifact & Reproducibility

> **代码仓库**：https://github.com/hy7pc8gfmf-dotcom/PSA-CertifiedSparseGating（Coq 形式化 + 论文 + 实证 + CI，Apache-2.0；CI 徽章见 README）。预印本 DOI：10.6084/m9.figshare.33312189。

- **代码分布**：`src/`（正式模块，含 `_CoqProject`）；`z/`（探针）；合并版
  `src/ca_merged_full_24.v`；归档基态 `D:\ComplexAnalysis\30模块\`（ca_* + 7 探针 pro 版 +
  ca_zeta_euler + 合并版，SHA-256 与 src/z 一致，旧版备份 `.sync-backup-20260823/`）。
- **依赖版本**：Rocq/Coq 9.0.1（`C:\Rocq-Platform~9.0~2025.08\bin\coqc.exe`）；mathcomp
  （本地 vendored `lib\mathcomp`）；Coquelicot（`lib\Coquelicot`）；Windows 10+ / PowerShell 7。
- **构建命令**：各模块独立编译 `coqc -Q <src> "" -Q <z> "" -Q <mathcomp> mathcomp
  -Q <Coquelicot> Coquelicot <file>.v`；合并版重新生成 `python src/_merge_ca.py`，合并编译
  `coqc -Q <mathcomp> mathcomp -Q <Coquelicot> Coquelicot src/ca_merged_full_24.v`
  （MERGE_EXIT=0）。
- **审计脚本**：PSA_audit.v（165 项，输出 `audit_run.txt`）；PSA_3D_audit.v（10 项）；
  FFI 自测 `python psa_guard_ffi.py`（24/24）。
- **提取链**：PSA_extract.v → psa_guard.ml → psa_guard.exe → psa_guard_ffi.py。

## 13. Related Work

- **Transformer / 注意力形式化（Rocq/Coq）**：[rocq-transformer](https://github.com/jwiegley/rocq-transformer)
  形式化 transformer 结构与注意力的类型化实现；本工作差异在保证层级——验证**解析核的数值
  保证**（框架界/衰减界/能量预算），互补而非竞争。
- **Certified ML kernel**：[Certificates in AI: Learn but Verify](https://dl.acm.org/doi/10.1145/3737447)
  的「学习 + 验证」分离主张与本工作「可学习分量不覆盖、解析核机器检查」的边界一致；
  CompCert 式 proof-carrying kernel 为本工作的可执行提取提供方法论先例——本工作新增的是
  **反射检查器自带健全性证明**这一层。
- **Proof-carrying code（Necula）**：反射检查器是 PCC 思想的现代实例——运行时布尔判定 +
  机器检查的健全性定理，等价于「证书随代码传输、接收端可验证」；差异是证书内容为**有理
  常数界**而非类型/内存安全证明。
- **稀疏注意力无证书方法**：top-k、KV 逐出、低秩投影均无误差证书——本工作覆盖的解析核层
  是上述方法的形式化对照面。
- **压缩感知（RIP/稀疏恢复）**：Candes–Tao 的 RIP 与稀疏唯一恢复理论是本工作 §9 的数学
  背景；本工作是该理论在频率阶梯原子族上的 Coq 机器检查实例。

## 14. Limitations

- **高维证书**：3D/4D 是方法论可行性证明（骨架复用、维度推广逻辑闭合），常数远非紧
  （M_bound_3d 4 = 3968、M_bound_4d 4 = 19968），**不得用作实际误差界**——"Practically
  Non-Tight"按字面执行；3D/4D 的 H_dom 尚未反射化（可判定但未工程化）。
- **运行时检查器的量化范围**：int 镜像只在有限整数范围内且与 Coq 语义一致时接近 Coq
  soundness（§6 如实声明）。
- **证书边界**：不证明学习投影下的注意力 logits 有界、Q/K 投影与位置旋转对易（酉不变性
  仅覆盖基函数层）、残差/LayerNorm 数值稳定性、训练后权重保证、外推 PPL 与框架界的语义
  联系。
- **审计范围**：165 项审计覆盖 PSA_framework 应用层；P1Coherence 的经典 MVT 路线在应用层
  外；Dedekind 实数基础设施的非构造原则如实声明。
- **实证规模**：配套论文 B 为 toy-scale（~0.5M 参数、char-level），实证预览单 seed 部分
  已补 3-seed；完整实证见论文 B。
- **正交刻画单向**：μ=0 家族目前只证 ⟸ 方向（公共偏移 + N-网格 ⟹ 两两正交）；
  ⟹ 方向的完备化（不存在第三种正交家族）列为 future work。
- **形式化适用域**：全部证明依赖频率阶梯（seq 存在性）；对无位置结构的编码（NoPE 类）
  本框架无任何可证陈述。

## 15. Conclusion

本工作给出了「稀疏门控 + 频率阶梯基」完整解析核的 Coq 形式化：从确定性门控、框架界、
截断能量、softmax 稳定性到注意力近似，全部常数落在可判定的有理层；反射检查器自带健全性
证明，实例证书推广为通用运行时判定；可证明性边界（稠密与 μ≤4/5 互斥）、碰撞距离框架与
部署级证书族构成三角支撑；**压缩感知族（单位范数 + RIP + 稀疏唯一性）把「无条件基 + 频率
阶梯」的理论优势推进到稀疏恢复**。全部开发零 Admitted、零自定义公理，165 项审计
`Classical_Prop.classic` 零出现；合并版（75702 行，40 模块含 7 个 z 区探针）全量合并编译
通过。与配套论文 B 的实证共同构成「可证性（稀疏）— 外推性（稠密）」双轨的机器检查 + 实证
记录。

---

## 附录 A 代码-论文声明交叉索引（对齐 2026-08-23 基态）

| 论文声明 | 代码位置 | 状态 |
|---------|---------|------|
| 165 项全零 Classical_Prop.classic | PSA_audit.v（165 项 Print Assumptions） | ✅ |
| 七带复合证书 Qed | PSA_framework.v Module ChampionCertificate（champion_e5_composite_certificate） | ✅ |
| 反射检查器健全性 Qed | FrameCheckInstance.frame_check_instance_sound | ✅ |
| M1.5 经典清零 | Module ExpSeries（exp_mono_le_noclassic） | ✅ |
| 酉不变性机器检查（RoPE） | Module UnitaryInvariance（unitary_invariance_psi_rope_theta） | ✅ |
| 2D-wide 免 H_dom | ca_2d_wide_asm.v（M_bound_2d_wide 4 = 768） | ✅ |
| 3D/4D 上界证书 | ca_basis_3d.v / ca_basis_4d.v（M_bound_3d 4 = 3968 / M_bound_4d 4 = 19968） | ✅ |
| 提取 / FFI 24/24 | PSA_extract.v → psa_guard.exe（frame CLI：C4/T8 true、E5'' false） | ✅ |
| P2/P3/N511（帕累托律） | src/ParetoLaw.v | ✅ |
| P1/P1′ 精确相干下界 | src/P1Coherence.v | ✅ |
| T2a/T2b 随机版负定律 | src/ParetoRandom.v | ✅ |
| CRT/素数链 | src/CRTResolve.v（prime_ladder_8 / crt_inj） | ✅ |
| **压缩感知族（CS-1/2/3）** | **z/probe_incoherence.v（psi_norm_one / rip_bound2 / sparse_uniquenessM，48 Qed）** | ✅ **已并入合并版** |
| ρ^{−3/2} 行和紧界 | z/probe_rowsum.v（row_sum_3halfs / row_bound_C4，21 Qed） | ✅ **已并入合并版** |
| 任意角度 Dirichlet / 混合网格相干 | z/probe_pairdirichlet.v（pair_dirichlet / mixed_grid_coherence，4 Qed） | ✅ **已并入合并版** |
| Parseval / Dirichlet 界 | z/probe_parseval.v / probe_partial.v（17+15 Qed） | ✅ **已并入合并版** |
| ρ^{−3/2} 逐对紧界 | z/probe_pairbound.v（5 Qed） | ✅ **已并入合并版** |
| 碰撞刻画 / τ 机制 | z/probe_collision.v / probe_tchar.v / probe_taudicho.v | ✅（z 区独立验证） |
| 部署级证书族 | z/probe_kvevict.v / probe_quant.v / probe_multihead.v / probe_exprat.v | ✅（z 区独立验证） |
| 合并版 | src/ca_merged_full_24.v（75702 行，40 模块，7 探针并入） | ✅ **MERGE_EXIT=0** |
| 归档基态 | D:\ComplexAnalysis\30模块\（SHA-256 与 src/z 一致） | ✅ |

---

## 附录 B 独立主线：欧拉乘积式的构造性证明（ca_zeta_euler.v，149 Qed）

> **甄别说明（2026-08-23）**：本附录对应代码库中的**独立构造性主线** `src/ca_zeta_euler.v`
> （149 Qed / 0 Admitted / 0 Axiom / EXIT=0，src = 30模块 归档 SHA-256 一致）。它与正文
> 认证管线（§4-§10）**正交**——正文所有主张不依赖它；它作为**级数侧的独立数学贡献**
> 与「可认证稀疏」的表示稳定性主张互补（欧拉积 = 解析数论的经典恒等式，此处给出
> 构造性实数上的零公理机器证明）。

**主定理**（`Theorem euler_product`，L3419-3451，构造性 CR，零公理）：

```
euler_product {R : ConstructiveReals} (s : nat) (Hs2 : 2 ≤ s) :
  CR_cv R (fun P => euler_E_cv (primes_leq P) s …) (1 + zeta_series_cv s)
  (* ζ(s) = Σ_{n≥1} n^{−s} = ∏_{p ≤ P} (1 − p^{−s})^{−1}，P→∞，s ≥ 2 *)
```

**证明链（149 Qed 分解）**：L1b 几何级数（38）→ L2 素数幂（44）→ Part1 ζ 收敛（68）→
L3 有限欧拉积（91）→ L4 E→∞（100）→ 正向主引理（116）→ 反向分解四砖块（120）→
smooth_in（121）→ smooth_cover 砖块（123）→ 反向主引理第一形态（132）→ 尾部界（137）
→ **双极限收尾（137→149，+12）**：`zeta_partial_le_euler_prod`（部分和 ≤ 欧拉积）、
`pow2_unbounded`（2 幂无界辅助）、`CRsum_subseq_pow2_cv`/`CRsum_subseq_pow2_minus2_cv`
（构造性子序列收敛）、`zeta_le_euler_prod_P`（ζ ≤ ∏）、`euler_prod_leq_zeta`（∏ ≤ ζ）、
`euler_prod_err_le`（|F(P)−(1+ζ)| ≤ 1/P 误差界）、`euler_product`（主定理）。

**性质**：数学对象在 Set 层（CRcarrier）；极限/收敛在 Prop 层（CR_cv）；n^{−s} 用
CRpow (CR_of_Q (1/n)) s（整数幂，无超越函数）；唯一分解用 mathcomp prime/div（可计算）；
**零经典实数公理**（构造性 Cauchy 实数，非 Dedekind）。

**对论文的主张影响**：无（正文不依赖）；可选使用——若投稿希望展示级数侧构造性证明能力，
可将其作为独立贡献/附录引用（149+ Qed 口径）。
