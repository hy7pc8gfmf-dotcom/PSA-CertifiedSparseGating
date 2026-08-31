# Certified Sparse Gating over Phase-Truncated Frequency Ladders
## A Coq Formalization of Representation Stability and Sparse Recovery Guarantees

> 正式版。投稿方向：CPP/ITP（形式化方法）。
> 作者：王宝军、夏挽岚（通讯作者，xiawanlan33@163.com）、祖光照、周志农、高雪峰
> 代码基态：合并版 `ca_merged_full_25.v`（93953 行，67 模块分区，SHA-256 基 4901f18e；G-7/G-9 批次见合并版 `ca_merged_full_25_m2.v`（92743 行，69 模块分区，本地 2.5 全量编译 EXIT=0，2026-08-31），公理审计 54 Closed + 111 Dedekind 三公理、`Classical_Prop.classic` 零出现（2026-08-30 重跑确认）；持续集成全链路验证通过——lib 依赖链、合并版编译（Rocq 9.0 + mathcomp 2.6）、PSA 核心编译、零 Admitted 检查、coqchk 内核独立复验）。

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
the certificate layer is decidable rational arithmetic, extractable as-is. All gating and
checker functions are extracted to executable OCaml/Python and cross-checked against Coq
computational reference values (24/24). This pattern is generalized to any ladder by a
reflective checker `frame_check_instance`: a decidable sufficient test for μ ≤ 4/5
(conservatively sound — systematic scan: 49.1% false negatives among rejected ladders),
extracted to OCaml with a native-integer mirror; its soundness theorem
`frame_check_instance_sound` is proved inside Coq (checker pass ⟹ Gershgorin frame bounds).
The machine-checked guarantee refers to the Coq-side nat checker; the runtime native-integer
mirror is cross-validated line-by-line against the Coq definition via a 24/24 FFI check (not
machine-proved) and agrees with the Coq semantics only within a finite integer range
(intermediate values < 2^53, accumulated denominators < 2^63; §6). For the structured-ladder
champion [3,7,15,31,63,127,255], a composite certificate (frame core + edge energy budget +
coherence cross-term bound) is proved: (S − coh_e5) ≤ ‖F‖² ≤ (S + coh_e5) — a
**basis-representation stability bound**, not attention scores or extrapolation PPL; the
bridge to empirical PPL gain is an empirical observation, not a formal consequence.
Beyond certification, we prove a **provability-boundary** theorem family (dense coverage and
μ ≤ 4/5 checker certification are mutually exclusive; more than 9 phase-complete bands in
[3,511] must be rejected, by geometric growth plus pigeonhole with growth constant c ≈ 1.8501;
randomized ladders are rejected with high probability — same-bin band pairs trigger rejection
with probability ≥ 96% at 7 bands and ≥ 99% at 8 bands, birthday-box counting), a
**collision-distance** framework for the τ mechanism (exact collisions occur iff the angle is
rational; minimal collision distance = the denominator; irrational offsets — golden ratio —
never collide, and near-collisions are blocked by a 1/(3d) radius; the linear-bias kernel
(ALiBi) has no collision endpoints — the certification/provability-boundary/
collision-resolution triangle is machine-checked, incl. the U5 golden-ratio near-collision
radius), and — new in
this version — a **compressed-sensing** family: the phase-truncated ladder atoms have unit
norm, satisfy an RIP(2,μ) bound, a k-atomic RIP bound
(|‖Σ_{j≤M} c_j·u_j‖² − Σc_j²| ≤ μ(M+1)Σc_j², proved on constructive reals), a row-sum-to-RIP
bridge (δ_k = (k−1)·μ_row), sparse-recovery uniqueness (μ·(M+1) < 1 ⟹ zero combination ⟹
all coefficients zero), a recovery-correctness skeleton, an incoherent-dictionary uncertainty
principle (μ·(|T1|+|T2|−1) < 1 ⟹ uniqueness on actual support sizes), and a
dictionary-optimality synthesis (Welch lower bound + uniqueness window ⟹ identical sparse
representations) whose Welch premise is itself proved constructively
(`g7_welch_lower`: the squared Welch bound (M − N) ≤ N·(M−1)·μ² via Frobenius norm
and Cauchy–Schwarz, avoiding eigenvalue arguments), all machine-checked; on the C=4
ladder the instance μ = 11289/33920 < 1/3 yields 3-atom sparse uniqueness for [3,13,53]. The asymptotic cost of the
relaxation chain itself admits a machine-checked closed form (G-9: the exact form
c/(2(c²−1)) for square C and a two-sided rational sandwich for general C), and the
reflective checker admits a true iff characterization at the exact rational layer
(G-11: pass ⟺ every row within threshold, reject ⟺ an over-threshold row exists,
plus a quantitative false-negative criterion in terms of relaxation slack). The audit comprises 165 Print
Assumptions entries (PSA_audit.v) with zero `Classical_Prop.classic` at the application
layer; the only axioms are the standard Dedekind-real infrastructure (sig_not_dec,
sig_forall_dec, functional extensionality) — non-constructive choice-like principles
inherent to the real-number construction, not introduced by our application layer. Full
constructivity is not claimed. Companion paper B provides the empirical validation of the
same ladder family; this work supplies the formal guarantees.

---

## 1. Introduction

> **Contribution-type statement.** This paper is *formalization engineering*: the
> contribution is a decidability methodology (the relaxation chain), a reflective
> checker mechanism, and audit discipline — not new mathematics (all proved
> statements are machine-checked instantiations of classical results; see §9.1
> for library comparisons). Readers weighing mathematical novelty as the primary
> criterion should read with this positioning in mind.

稀疏/近似注意力方法（top-k 门控、KV 逐出、低秩投影）在实践中有性能优势，但均无误差证书。
本工作采用「验证解析核、学习其余」（verify the analytic kernel, learn the rest）的路线：
在解析核层（稀疏门控、频率基、截断能量、softmax 稳定性）提供机器检查的保证，而学习分量
（W_Q/W_K/W_V/W_O、softmax 身份、训练后权重）不覆盖。

**贡献清单**（与代码一一对应，全部 Coq 机器检查，零 Admitted / 零自定义公理）：
**形式化工程贡献（审稿要求，先于数学新发现）**：本工作的主要价值在**形式化工程创新**而非
数学新发现——(i) **可判定性松弛链**：将超越数界（sqrt/sin/Dirichlet 核）逐级单侧松弛为
有理数（floor-sqrt、Jordan 不等式、|sin(πNΔ)|≤1），使证书层完全落在可判定有理算术上，
可提取、可运行时验证——这是一条可复用的通用方法而非单一定理；(ii) **反射检查器模式**：
把"实例证书"推广为"任意阶梯 → μ≤4/5 的带健全性证明的运行时判定"，是 proof-carrying
code 思想在数值框架界上的实例化；(iii) **构造性实数轨道**（ca_rip_cr.v）：在纯构造性
实数上独立验证 k-原子 RIP，与经典轨道的经典排中依赖形成对照；(iv) **零自定义公理的
审计纪律**：165 项 Print Assumptions 全审计（完整 165/165 运行日志随稿，post-M1.5 复核零 `Classical_Prop.classic`）、合并版 67 模块分区 全量编译。以下贡献清单中的
核心定理（Gershgorin 框架界、RIP 基元、稀疏唯一性）均为经典结果的机器化，数学新颖性有限，
但上述工程机制使其可判定、可提取、可审计——这是与"把经典数学写进 Coq"的本质区别。

1. **确定性门控的形式化**（GreedyGate，28 引理）：原文概率门控前提不可满足（(INR N)²p²<1 恒假，
   已给反例），本工作裁决并证明确定性平方门 M=C² 是**本文选定模型下**的可行路线（严格表述限定于该概率门控前提框架内，不声称一般意义唯一性）。
2. **有限化守卫衰减界**（PSA_Pipeline）：全局增长前提 → 运行时可判定检查，系数 2/√C 与
   tight 1/√C 两版。
3. **行截断能量预算**（RowTruncation）与 **softmax 稳定性**（SoftmaxStability：
   ‖softmax z − softmax z'‖₁ ≤ exp(2·d) − 1）。
4. **认证注意力近似**（CertifiedAttention）：谱能量 ≤ ε ⟹ 输出偏差 ≤ (e^{2√ε}−1)·V_max。
5. **实例证书**（Gershgorin + InstanceCertificate）：对 C=4 阶梯 [3,13,53,213] 证明框架界
   [1/5, 9/5]（μ=4/5）——参数化最坏情形 1±4K(C) 在 C=4 空洞成立、需 C>25 的问题就此终结。
6. **有理支配方法论**（可判定性溢价）：证书全部常数经 floor-sqrt / Jordan / Dirichlet
   的单侧松弛化为有理数，`compute; field` 完成证明——零数值策略、零区间算术、可判定、可提取。
   **松弛链元理论（CS-19，`probe_relaxation_meta.v`，2026-08-30）**：单调性与组合性已定理化——
   参数化合成界 relax m sb sq := m·(1/(sb·sq))（分子上界 / sin 下界 / √ 下界三层参数）逐层单调
   （M1）、多层组合收紧（M2 relax_refine）、行和提升（M3 rowR_mono）与判定保持（M4
   `checker_preserved_under_refinement`：任一层收紧后检查器通过性不变——「只强化不破坏」）；
   M5 证明反射层 pair_frac_R 恰为该参数化族实例，元理论覆盖现有检查器管线。
7. **可执行提取**：门控/检查器 → OCaml（psa_guard.exe）→ Python FFI，24/24 参考值对齐。
8. **反射检查器及其健全性**（FrameCheckInstance）：`frame_check_instance` 把「任意阶梯 →
   μ≤4/5」做成可判定**充分**判定（保守健全，系统扫描假阴性 49.1%），提取为原生 int 镜像（**注：健全性定理针对 Coq 内 nat 版判定函数；
   运行时 int 镜像仅经 FFI 24/24 交叉校验，未形式化验证其等价性，且限有限整数范围，详见 §6**）；
   `frame_check_instance_sound` 证明判定
   通过 ⟹ Gershgorin 框架界——实例证书推广为通用运行时判定。
9. **基表示稳定性复合证书**（核心展示定理）：七带几何阶梯 [3,7,15,31,63,127,255]
   （自包含说明：本工作实证配套论文 B 中的强几何基线阶梯——C=2 八带 [3,7,15,31,63,127,255,511]
   剪去 511 带后的版本，在配套实证中为带证书方案里的性能领先者；其隔带子核 [3,15,63,255]
   行和 ≤ 0.781 可整体认证）获得机器证明的平方范数复合界 (S−coh_e5) ≤ ‖F‖² ≤ (S+coh_e5)
   （全矩阵相干加权、对称交叉项界）。该复合界是**基函数范数稳定性保证**，不涉及注意力
   分数/softmax/PPL；与外推 PPL 改善之间的桥梁是经验观察，未经形式化。该证书与 `certified_attention_approx` 不组合——后者刻画谱能量丢弃 ⟹ 注意力输出扰动，前者刻画基表示范数稳定性，两个定理簇相互独立。当反射检查器返回
   false（健全但非完备）时，核-边缘分解交付的部分证书在此收束为七带整体完整证书——这是对
   反射器不完备性的系统性工程补丁，作为方法论贡献单列。
10. **高维组合性演示**（2D-wide/3D/4D）：同一 `abstract_unconditional_basis` 骨架逐轴
    实例化到任意维——价值在骨架复用与维度推广可行性证明（"Theoretically Composable,
    Practically Non-Tight"），常数非紧，定位为上界证书 + 组合性演示，非实用框架界。
11. **可证明性边界**：稠密覆盖与 μ≤4/5 检查器认证互斥（`pareto_law_main`）；N=511 时
    m ≥ 10 必被拒绝（`pareto_law_N511`）；随机 log-uniform 阶梯 whp 被拒绝（T2a/T2b）。
12. **碰撞距离框架**：精确碰撞 ⟺ 角度有理（构造性 iff）；最小碰撞距离 = 分母；无理偏移
    永无精确碰撞；线性偏置（ALiBi）无碰撞端点——τ 机制的形式化碰撞结构。
13. **压缩感知级理论保证**：频率阶梯原子族单位范数（psi_norm_one）、RIP(2,μ) 型界
    （rip_bound2）、稀疏恢复唯一性（sparse_uniquenessM：μ·(M+1) < 1 ⟹ 零组合 ⟹ 系数全零）——
    把「无条件基 + 频率阶梯」的理论优势从框架界推进到稀疏恢复。
14. **部署级证书族**：KV 逐出/量化扰动/多头合成的 softmax 稳定性证书，TVD 常数有理化
    （检查器可判定）。

**覆盖边界（What is not certified）**：学习到的权重（W_Q/W_K/W_V/W_O）、Q/K/V 投影与多头
拼接、LayerNorm/激活的数值稳定性、残差累积误差、外推 PPL 与框架界之间的语义联系——均在
「learn the rest」一侧。**酉不变性仅覆盖基函数表示层**（不保证学习到的 Q/K 投影下注意力
logits 不变，§5.3/§10）。证书链是**两条正交的定理簇**（表示稳定性轨 / 注意力扰动轨），
无依赖桥接；「certified」精确指解析核层，不构成模型/外推性能证书。

## 2. Formalization Overview

- **背景定义**：ψ 基 $\psi_n(k) = (1/\sqrt{n})\cdot e^{2\pi i k/n}$，有限支撑（$k \ge n$ 时为 0）；阶梯生成器 $n_{j+1} = \max(C\cdot n_j + 1,\, n_j + 2)$（非精确几何——证书必须认证实际值，这是需要运行时检查器而非纸面公式的理由）。
- **三处语义修正**（线性 vs 平方门、`<=?` vs `<?`、≥2 并集）——每处附反例，体现形式化对原草案的纠错价值；**一处常数级勘误（3D 张量基，已修正）**：2D 引擎的离对角界常数 K0 = Rmax 8C³/4 在 3D 等轴退化配置（两轴索引相同、仅第三轴差 ≤6）下不可证——归一化三重内积可逼近 1，而 /4 常数只给 1/2；3D 模块改为 K0′ = Rmax 8C³/2（退化配置恰好紧，worst case = 1）。
- **主模块** `src/PSA_framework.v`：**6659 行 / 18 个 Module / 269 顶层 Lemma·Theorem（含 Module PhaseCoherence 12 项）/ 零 Admitted**
  （计数口径：含 PhaseCoherence 相干熵桥接；早期审计记录为 265，不含该模块）。模块链：RuntimeGuards → SeqProps → PSA_Pipeline → GreedyGate →
  RowTruncation → PipelineEndToEnd → ExpSeries → SoftmaxStability → CertifiedAttention →
  Gershgorin → InstanceCertificate → M4bLengthConsistency → T8CoreCertificate →
  FrameCheckInstance → ChampionCertificate → FrameCheck2DNarrow → UnitaryInvariance →
  PhaseCoherence。
- **合并版** `src/ca_merged_full_25_m2.v`：**92743 行 / 69 模块分区**（30 个 ca_* + PSA_framework +
  独立模块 + z 区探针族与构造性轨道全量并入至 G-9：probe_grid_ortho/parseval/partial/pairbound/rowsum/
  pairdirichlet/incoherence/row_rip/c4_instance + welch/uncertainty_cr/g8_synthesis_cr/
  g1_norm_closed/g2_mu_adj + 构造性族 pi_cr_m1a/m1b/sin_cr_m2/sqrt_cr_m3/s7_s9_mono/
  decidability_premium_cr + **构造性轨道 ca_zeta_euler / ca_rip_cr** + **CS 定理族 taugrid/taugrid_cr/cs/cs5** + **M2 批次 c4_four_atom_cr/safe_domain/frame_check_graduated/ab_bridge_pier/relaxation_meta/g3_criterion/g5_premium** + **g7_welch_cr + g9_pairfrac_cr（G-9）**），追加式并入，**本地 2.5 全量编译 EXIT=0（run20，2026-08-31）**。
- **z 区探针（并入合并版 9 个：8 经典 pro 化 + c4_instance）**：grid_ortho 18 Qed / parseval 19 / partial 27 /
  pairbound 5 / rowsum 23 / pairdirichlet 5 / incoherence 51 / row_rip 9（行和→RIP 桥接）/ c4_instance 14（C=4 实例拼接）——
  各独立编译 EXIT=0 + 合并编译双通过。
- **审计**：PSA_audit.v **165 项** Print Assumptions，RC=0，零 Admitted；全部 165 项
  `Classical_Prop.classic` 零出现；公理依赖仅 sig_not_dec / sig_forall_dec / fext
  （标准 Dedekind 实数基础设施，已明确声明）。
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

psi_inner_dirichlet : |⟨ψ_{n1},ψ_{n2}⟩| = |sin(πNΔ)/sin(πΔ)| / √(n1·n2)

psi_inner_cons_bound : |⟨ψ_{n1},ψ_{n2}⟩| ≤ 1/(2Δ√(n1n2))   (* 窗口无关保守界 *)

softmax_l1_bound_exp : ‖z−z'‖∞ ≤ d → ‖softmax z − softmax z'‖₁ ≤ exp(2·d) − 1

certified_attention_approx : 逐行丢弃谱能量 ≤ ε →
  ‖attn_out − attn_out_approx‖ ≤ (e^{2√ε} − 1) · V_max

certified_c4_frame_bounds (coeffs) : length coeffs = 4 →
  (1 − 4/5)·S ≤ ‖Σ c_i·ψ_{[3,13,53,213],i}‖² ≤ (1 + 4/5)·S   (* 实例证书 *)

certified_c4_frame_bounds_anyN (N) (coeffs) : N ≥ 214 → length coeffs = 4 →
  (1 − 4/5)·S ≤ ‖Σ c_i·ψ_{[3,13,53,213],i}‖² ≤ (1 + 4/5)·S   (* 长度一致性 *)

certified_t8_core_frame_bounds (coeffs) : length coeffs = 4 →
  (1 − 4/5)·S ≤ ‖Σ c_i·ψ_{[3,15,63,255],i}‖² ≤ (1 + 4/5)·S   (* T8 复合证书核 *)

frame_check_instance_sound (I) : 0 < length I → frame_check_instance I = true →
  (1 − 4/5)·‖Σ c_i·phi i‖² ≤ ‖Σ_{k<M} (Σ_{i<n} c_i·phi i k)‖² ≤ (1 + 4/5)·‖Σ c_i·phi i‖²
  (* 反射检查器健全性：判定通过 ⟹ 任意阶梯 μ=4/5 框架界 *)

tensor_product_unconditional_basis_2d_wide (C) : C > 2 → 双轴稀疏增长 → 免 H_dom →
  (1 − M_bound)·S ≤ ‖F_2D‖² ≤ (1 + M_bound)·S   (* 上界证书，M_bound_2d_wide 4 = 768 *)

tensor_product_unconditional_basis_3d (C) : C > 2 → 三轴稀疏增长 → H_dom → 混合进制距离 ≤6 →
  (1 − M_bound)·S ≤ ‖F_3D‖² ≤ (1 + M_bound)·S   (* 上界证书，M_bound_3d 4 = 3968，下界平凡 *)

tensor_product_unconditional_basis_4d (C) (seq1..seq4) : C > 2 → 四轴稀疏增长 →
  (1 − M_bound)·S ≤ ‖F_4D‖² ≤ (1 + M_bound)·S
  (* M_bound_4d 4 = 19968 *)

unitary_invariance_psi_rope_theta (θ) (vals) (coeffs) (n N) :
  Σ_{k<N} |Σ_{i<n} e^{i·(INR k·θ k)}·c_i·ψ_{vals[i]}(k)|² = Σ_{k<N} |Σ_{i<n} c_i·ψ_{vals[i]}(k)|²
  (* RoPE 显式实例：u k := Cexp (0+i·INR k·θ k)，Cexp_unit_mod 证单位模 *)

champion_e5_composite_certificate : length coeffs = 7 →
  (S − coh_e5) ≤ ‖Σ_{i<7} c_i·ψ_{e5_bands[i]}‖²_{255} ≤ (S + coh_e5)
  (* 七带基表示稳定性复合界 *)

pareto_law_N511 : 检查器通过 ∧ m 条相完备带 [3,511] → 3·c^(m−1) ≤ N ⟹ m ≥ 10 必被拒绝

golden_near_collision_gold : ∀ d ≥ 1, ∀ m ∈ Z: |d·φ_gold − m| ≥ 1/(3d)

(* ── 压缩感知族（probe_incoherence.v 51 Qed + ca_rip_cr.v 33 Qed + probe_c4_instance.v 14 Qed + probe_row_rip.v 9 Qed + probe_recovery_cr.v + probe_uncertainty_cr.v 35 Qed）── *)
psi_norm_one (n) : 1 ≤ n → l2_norm_sq (psi n) (pred n) = 1

rip_bound2 (u1 u2) (W) (c1 c2 mu) : ‖u1‖²_W = 1 → ‖u2‖²_W = 1 → |⟨u1,u2⟩_W| ≤ mu →
  |‖c1·u1 + c2·u2‖²_W − (c1² + c2²)| ≤ mu·(c1² + c2²)

CRrip_bound_k (M) (c) (u) (mu) : 0 ≤ mu → ∀j≤M: ‖u_j‖² = 1 → ∀i≠j≤M: |⟨u_i,u_j⟩| ≤ mu →
  |‖Σ_{j≤M} c_j·u_j‖² − Σ_{j≤M} c_j²| ≤ mu·(M+1)·Σ_{j≤M} c_j²
  （构造性轨道 ca_rip_cr.v：纯构造性实数，零经典公理、零 Admitted，33 定理）

sparse_uniquenessM (M) (c) (u) (W) (mu) : 0 ≤ mu → ∀j≤M: ‖u_j‖²_W = 1 →
  ∀i≠j≤M: |⟨u_i,u_j⟩_W| ≤ mu → mu·(M+1) < 1 → ∀k≤W: Σ_{j≤M} c_j·u_j(k) = 0 →
  ∀j≤M: c_j = 0

C4_sparse_uniqueness_3 (c) (W) : 53 ≤ W → ∀k≤W: Σ_{j≤2} c_j·ψ_{[3;13;53] j}(k) = 0 →
  ∀j≤2: c_j = 0
  （C=4 实例 probe_c4_instance.v：六对相干上界 μ=11289/33920 < 1/3 ⟹ sparse_uniquenessM M=2 实例）

row_rip_bound_M (M) (c) (u) (W) (mu_row) : 行非对角和 ≤ mu_row →
  |‖Σ_{j≤M} c_j·u_j‖² − Σ_{j≤M} c_j²| ≤ mu_row·M·Σ_{j≤M} c_j²
  （行和→RIP 桥接 probe_row_rip.v：δ_k = (k−1)·mu_row，9 Qed）

CRrecovery_correct_prefix (M) (c c') (u) (mu) : 0 ≤ mu → 单位范数 → 相干 ≤ mu →
  mu·(M+1) < 1 → Σ_{j≤M} c_j·u_j == Σ_{j≤M} c'_j·u_j → ∀j≤M: c_j == c'_j
  （唯一性⟹恢复正确性骨架，构造性轨道 probe_recovery_cr.v，零经典公理）

CRuncertainty_principle (T1 T2) (c d) (u) (mu) : 0 ≤ mu → 单位范数（T1∪T2）→ 相干 ≤ mu（T1∪T2）→
  mu·(|T1|+|T2|−1) < 1 → Σ_{T1} c·u == Σ_{T2} d·u（支撑外零）→ ∀j: c_j == d_j
  （相干字典不确定原理，构造性轨道 probe_uncertainty_cr.v：支撑大小版 1+1/μ，35 定理零经典）

g7_welch_lower (M N) (v) (mu) : 1 ≤ N → N < M → (∀i<M: Σ_{k<N} v i k² = 1) →
  (∀i j<M: i ≠ j → |Σ_k v i k·v j k| ≤ mu) →
  INR M − INR N ≤ INR N · INR (Nat.pred M) · mu · mu
  （Welch 下界平方形态，构造性轨道 probe_g7_welch_cr.v：Frobenius/Cauchy–Schwarz
  路线避特征值，14 Qed 六审计全 Closed，签名与 G-8 前提逐字一致）
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
有理松弛不足以证明），其**精确**相干行和（证书口径①）为 **1.2287 > 4/5**——检查器判
false 是**真阴性**（真值超阈），并非"0.135 实质可认证"。核-边缘分解交付
**部分证书**：T8 核通过检查 + 边带能量预算 + 相干交叉项（21 对上三角 δ 表
`delta_e5` 经 `term_bound_upper/lower` 加权）⟹ 七带整体对称界
(S − coh_e5) ≤ ‖F‖²_{255} ≤ (S + coh_e5)。**紧度说明**：δ_e5 上界均为手工挑选的
保守有理数（floor-sqrt/Jordan/Dirichlet 单侧松弛），无最优性保证；**单位系数下 S=7、
coh_e5=14.21、下界 −7.21 空洞**——该界是宽松的基函数范数稳定性界，非框架下界，也不等于
七带相干行和；与注意力/softmax/PPL 无关。

### 4.4 从实例到通用判定
同一配方推广为反射检查器 `frame_check_instance`（任意阶梯 → μ≤4/5 布尔判定，floor-sqrt
有理化 + nat 分数行和，全程可判定有理算术）。实例证书不再逐阶梯手工验算，而由一台自带
健全性证明的运行时检查器统一保证。

**μ ≤ 4/5 的推导路径（审稿要求，证明草图）**：判定函数 `frame_check_instance` 对每个
索引 i 计算其非对角行和的上界——`row_sum_frac_aux` 对每一对 (i,j)，i≠j，用
`pair_den`（floor-sqrt 有理化分母）与保守正弦界（Jordan 不等式 |sin(πΔ)| ≤ 2Δ、
Dirichlet 分子 |sin(πNΔ)| ≤ 1）给出相干上界 |⟨u_i,u_j⟩| ≤ pair_bound(i,j)，再逐项累加
得行和上界 R_i = Σ_{j≠i} pair_bound(i,j)（有理数，分子分母为 nat）。判定通过 ⟺
**∀i: R_i ≤ 4/5**（对 C=4 实例，R_i = 13/40 + 53/400 + 213/3500 = 0.518 < 0.8）。
健全性定理 `frame_check_instance_sound` 证明：若判定通过，则 Gershgorin 框架界
(1 − 4/5)·S ≤ ‖Σc_i u_i‖² ≤ (1 + 4/5)·S 成立——即 μ 取判定阈值 4/5 本身，而非
逐实例重算的精确相干；这是"充分非必要"预筛器的本质（保守上界超阈值即误拒，见 §6 假阴性）。

### 4.5 与实验的对齐（multi-seed + T8 + 复合证书 + 酉不变性）

3 个种子实验中 E5'' 七带与 C=4 并列最优（8× 均值 12.40±0.74 vs 12.75±0.34）；C=2 第三（13.84）；C=3 系统性最差（22.86）。最优表现对论文 A 免疫：

- **直接证书**（C=4）：`certified_c4_frame_bounds` 直接覆盖；
- **T8 复合证书**（E5''）：隔带子核 [3,15,63,255] 的 `certified_t8_core_frame_bounds`（μ=4/5）覆盖最优阶梯的认证核；
- **酉不变性（已机器检查，A2）**：旋转是酉变换，对任意酉算子 U 与系数向量 c，‖Σ c_i Uψ_i‖² = ‖Σ c_i ψ_i‖²——框架界/衰减界/证书自动覆盖旋转版本（论文 B 的"旋转组"）。Module UnitaryInvariance：`unitary_invariance_point`（U 保内积 ⟹ 范数不变）+ 位置索引 psi-rope 实例 + 显式 RoPE 实例 `unitary_invariance_psi_rope_theta`（u k := Cexp (0+i·INR k·θ k)，`Cexp_unit_mod` 证单位模）。实验的 2×2 块旋转矩阵（`apply_rope_theta`）与复数乘法 e^{iθ} 是同一酉群的同构表示（SO(2)≅U(1)），实/虚部逐行对应已显式机器检查（`rope_matrix_real/imag/eq`，零 classic）。注：原"每带乘 u_i"逐点版本为假命题（交叉项要 u_i = u_j；反例 u0=1, u1=−1, g0=g1=1），未并入。范围限定：酉不变性适用于特征表示的范数层；不保证学习到的 Q/K 投影下注意力 logits 不变。
- **相干熵桥接**（PhaseCoherence，`coherence_controls_attention`，Qed，零 classic）：对任意相干核 K（|K_ij| ≤ coh）与系数差 ℓ₁ ≤ δ，logit 扰动 |z_i − z'_i| ≤ coh·δ，组合 softmax 稳定性得 ‖softmax z − softmax z'‖₁ ≤ e^{2·coh·δ} − 1——相干上界 ⟹ softmax 输出 TVD 界的抽象桥梁。已获首个实例（CS-18，`psi_attention_tvd_trunc`，probe_ab_bridge_pier.v：psi 核窗口截断通道，dc = INR(W−W')·(1/2)）——状态从「未实例化」升级为「截断通道已实例化」；实证支撑：ΔCoh 仅在稀疏几何族内排序（4 点 R²=0.982），13 点扩充后跨族失效（max 型 R²=0.101）——相干性定性结论保留、定量预测收缩为族内指标。
- **核漂移口径（已机器检查，2026-08-22）**：`kernel_drift_controls_attention`（PhaseCoherence，coqchk 独立复核）——核逐点漂移 |K_ij−K'_ij| ≤ dc（全 i,j）且系数 ℓ₁ ≤ dd ⟹ softmax 输出 ℓ₁ 距离 ≤ e^{2·dc·dd} − 1（与上条互补：系数漂移×固定核 vs 固定系数×核漂移，覆盖长度外推/蒸馏/量化场景）；对窗口无关核族（网格/偏移网格在任意 a·N 长度核相同）Δ=0 退化为 TVD 界 0（`kernel_identical_tvd_zero`）。**常数演进线**：4K → 2K（`psi_unconditional_basis_tight`）→ μ=0（网格端点）；`abstract_unconditional_basis` 可用 Riesz 序列稳定性语言重述（张成族系数 ℓ² 范数的 (1±M_bound) 等价）——文本级重述，不改变机器检查内容。

**实证预览（teaser，完整实证与机制分析见配套论文 B）**：char 级 0.5M 参数（0.43M–0.63M 视模式）、T_train=512、种子 {1337,42,7}、确定性协议：

| 方案 | 512 | 1024 | 2048 | 4096 |
|------|-----|------|------|------|
| rope（b32 三个种子） | 4.44±0.08 | 6.77±0.07 | 13.68±1.21 | 25.30±4.63 |
| **psi-rope [3,13,53,213]（本证书对象）** | 4.70±0.14 | 5.64±0.07 | 8.42±0.10 | 12.75±0.34 |
| **psi-rope 七带 [3,…,255]（T8 复合证书对象）** | 4.53±0.10 | 4.75±0.06 | 8.28±0.28 | **12.40±0.74** |

psi-rope 行 3 个种子均值±std、dense 单个种子（b64 s1337）、rope 为 b32 3 个种子均值±std——定位为 teaser。

## 5. 可判定性溢价（Decidability Premium）

全部超越量被朝可判定方向单侧支配：√m ← ⌊√m⌋、|sin(πΔ)| ← Jordan 2Δ、Dirichlet 分子
|sin(πNΔ)| ← 1、（Tier 2 的 π ← 22/7）。**证书层只需要 ℚ**——运行时验证只做有理算术，
这是可提取性的根源。

**可判定性溢价**：精确 μ = 0.312 → 有理保守 μ = 4/5，因子 2.55——机器可检查性的已量化
代价。溢价是**设计对象**：松弛链的每一环（floor-sqrt / Jordan / Dirichlet / π←22/7）都可
枚举、可单独收紧、可机械组合（`cert_optimize` 方向，future work）。相邻对有理界极限
n₁n₂/(2(n₂−n₁)⌊√(n₁n₂)⌋) → √C/(2(C−1))（C=4 时 1/3）——松弛链的渐近代价有闭合形式（**已形式化（G-9，`probe_g9_pairfrac_cr.v`）：完全平方 C 精确闭合 + 一般 C 双带有理夹逼 + sigT 可提取证书，零经典零公理**）。

**保守性（充分非必要）**：`frame_check_instance = true` 是框架界的充分非必要条件——floor-sqrt 有理松弛的保守因子约 1.5×，存在满足 Gershgorin 条件但因保守上界超 4/5 而被误拒的合法阶梯（假阴性）。典型真例证：[3,7,15]（起点最低的倍增三带）精确行和 0.7870 ≤ 4/5（满足框架条件），但有理保守界 1.3125 > 4/5 被误拒（可判定性溢价 ≈1.67）；而七带 E5'' 精确行和 1.2287 > 4/5，检查器判 false 是**真阴性**（真值超阈），不在误拒之列。 **充要性精确层口径（G-11，真 iff）**：注意 `probe_g3_criterion.v` 的 `g3_certifiable_iff` **实为单向蕴含**（检查器通过 ⟹ Gershgorin 框架界；名字取自早期草稿，未改）——真正的充要刻画由 **G-11 `probe_g11_checkiff_cr.v`**（2026-08-31，纯 nat/bool/Q 构造性，Set 层 sigT + 可提取 OCaml，6 段 Print Assumptions 全 Closed）给出：在精确有理算术层，行级检查裁定与行和阈值条件**双向等价**——`g11_check_iff`（通过 ⟺ 逐行 ≤ 4/5，健全+完备两方向）、`g11_reject_iff`（拒绝 ⟺ 存在超阈行）、`g11_fn_iff`（**假阴性量化 iff**：精确行在阈内且被松弛拒绝 ⟺ 阈值余量非负且小于松弛盈余）与 `g11_decision_cert`（sigT 决策证书，携带双向 iff）；假阴性全部来源于可判定松弛层的保守性，而非检查器逻辑的完备性缺口——G-11 的量化 iff 即此论断的精确形式（[3,7,15] 精确行和 ≈0.787 ≤ 4/5 被误拒，`probe_g5_premium.v` 机器验证）。正是这一不完备性使**复合证书成为必要**。宁可误拒、绝不放行的保守取向是可判定性的设计选择。系统扫描（114 阶梯 × 5 族）：通过 35（30.7%）、假阴性 56（全量 49.1%，占拒绝 70.9%），集中于"有用"阶梯（C=2/3-sparse 12/13、几何奇带 9/9）。

**证书覆盖地图（阶梯实例 × 认证状态 × 实证对照）**：

| 阶梯实例 | 直接框架界 (μ≤4/5) | 复合证书 | 检查器状态 | 实证 8× PPL | 覆盖结论 |
|---|---|---|---|---|---|
| [3,13,53,213] | ✅ `certified_c4_frame_bounds` | — | true | 12.75 | 4 原子能量有界；3 原子稀疏唯一 |
| [3,15,63,255] | ✅ `certified_t8_core_frame_bounds` | — | true | — | T8 认证核覆盖 |
| [3,7,15,31,63,127,255] | ❌ 精确行和 1.2287 > 4/5 | ✅ `champion_e5_composite_certificate` | false（真阴性） | 12.40 | 基表示稳定性界（单边上界） |
| [3,7,15] | ❌ 检查器 false | — | false（假阴性） | — | 精确行和 ≈0.787 ≤ 4/5，被保守界误拒 |
| 随机 log-uniform [3,511] | ❌ | — | whp false | 6.45 | 旋转族内最优；证书仅 ℓ² 线性无关 |
| ALiBi（非阶梯） | ❌ | ❌ | — | **4.47** | 全局最优，无证书，非周期偏置 |
| grid [3,5,17,…] | ✅ μ=0 正交证书 | ❌ | — | 25.66 | 证书 ≠ 性能的反例锚点 |

（PPL 列为配套论文 B 的实证数据；证书列为本开发形式化结果——两轨无形式化桥梁。）
被误拒的合法阶梯仍可由复合证书（§4.3）覆盖：「检查器通过 ⟹ 框架界」成立，「检查器失败
⟹ 不安全」不成立。

## 6. 反射检查器与提取（Coq soundness vs 运行时保证）

- **Coq 内健全性**：`frame_check_instance_sound` 已 Qed——判定通过 ⟹ Gershgorin 框架界，
  检查器 = 框架界定理的可执行投影。
- **提取链**：`PSA_extract.v` → `psa_guard.ml` → `psa_guard.exe`（DkMLNative ocamlc 字节码）
  → Python FFI（`psa_guard_ffi.py`，24/24 交叉校验）。自测 24/24（PSA_refcheck.v 20 项
  Check/Eval + 4 项整数行和验算）。
- **运行时保证的量化范围**：int 镜像（OCaml int，63-bit）只对小整数阶梯成立；
  浮点 `int_sqrt` 是近似（偏差 ≤ 1，仅判别阈值附近可能翻转）；累积分母 ∏ pair_den 指数增长，
- **提取物运行时基准（2026-08-30，回应评审 §3.3）**：`frame_check_graduated` 四级判定（[3,13]→L1、[3,7,15]→L2、[2,3]→L3、结构败→L4）与 `safe_domain_bool`（C=4 分母链 → 安全）全部 **< 1 ms**（DkMLNative ocamlc 字节码 + ocamlrun）；构造性轨道 `c4_four_atom_cr` 的 Q 层窗口判定 `mu4_window = (45156, 33920)` 运行输出 < 1 ms，与正文引用的 μ₄·4 判定逐字一致——「构造性轨道是否可计算」由运行时证据直接消解（基准文档 `extraction_benchmark_20260830.md` 随稿）；基准覆盖反射分级检查器/安全域/窗口判定，部署族（§10）提取物的同类基准为后续工作。
  系统扫描实测末带 < 2^20 的阶梯中仍有 14/89（15.7%）exe 与 Coq 语义分歧（如 C=6-sparse
  累积分母达 10^26 ≫ 2^63）。实验实际使用（带值 ≤255、m ≤ 8）全部落在 63-bit 安全区。
  **因此**：运行时检查器**不自动携带** Coq soundness——它只在有限整数范围内、且与 Coq
  语义一致时接近。根本消除：Zarith（任意精度）提取（future work）。**安全域谓词（已形式化，CS-16，`probe_safe_domain.v`，2026-08-30）**：安全域从经验确认升级为机器检查定理——`zprod_bounded`（乘积上界递推，非平凡归纳核：全因子 0 < d ≤ D ⟹ 0 < ∏ ≤ D^length）、`no_overflow_consistent`（0 ≤ p < 2^63 ⟹ p mod 2^63 = p，63-bit int 镜像与精确语义一致）、`c4_safe_domain`（C=4 判定链分母连乘 = 2054520832000000000 < 2^63，落于安全域）、`safe_domain_bool`/`in_w63`（可提取 bool 函数，运行时可判定成员资格）；4 段 Print Assumptions 全 Closed（零公理）。全窗口任意阶梯的运行时安全检查与 Zarith 任意精度提取仍为后续工作。
- **两层提取的边界（CR 效率质询澄清）**：运行时检查全部由 Z/Q 反射层承载——上项基准中的四级判定、安全域、窗口判定与 `psa_guard` 原生镜像均为 nat/Z/Q 层函数（Pos/Z 二进制算术，无逼近循环）；构造性实数层（ConstructiveReals）不进入任何运行时路径——其提取物中 `CRcarrier` 保持抽象类型参数（`g7_welch_cr` 等），或仅作柯西实例化的编译验证（`taugrid_cr.ml`）；`CR_of_Q` 在该层仅用于把有理常数嵌入实数 carrier 以调用库引理，其二分表示不承载任何运行时判定。如实定位：构造性轨道提取物「经 DkMLNative 编译通过」是良构性与可执行结构验证，非运行时性能主张——该轨道的角色是公理独立性与可计算性验证，生产检查器由经典/反射轨道承担。
- **逐行同构原则**（方法论）：提取代码应尽可能镜像 Coq Fixpoint 的结构（而非依赖高阶重写
  得到的"语义等价"的另一份代码）——本开发在 FFI 回归（24/24）中持续检查，并据此发现并
  修复了反射层 `row_sum_frac_aux` 的真 bug（收缩列表重算 nth 致 Coq 与原生不一致）。

## 7. 高维组合性（2D-wide / 3D / 4D，上界证书）

- **对象**：φ3D(a,b,c)(k) = γ⁻¹·ψ_a(k)·ψ_b(k)·ψ_c(k)，γ = √(min(a,b,c)/(abc))；同一
  `abstract_unconditional_basis` 骨架逐轴实例化到任意维。
- **定位**：M_bound > 1 时下界 (1−M_bound)·S 恒负（如 C=4 的 3D：−3967·S ≤ ‖F‖²
  对非负范数恒真，**无信息量**）——证书的信息量在于**上界** (1+M_bound)·S（排除范数爆炸）
  + 组合性演示。故 3D/4D 定位为**「上界证书 + 组合性演示」**，**不称为框架界**。
- **2D-wide（免 H_dom）**：`tensor_product_unconditional_basis_2d_wide`（宽轨口径 K0 = C³/2；
  窄轨 2D 为 K0 = C³/4），数值裁决 `M_bound_2d_wide 4 = 768`（= 32 × 24），与论文 B 的 N 维公式
  M_bound^{(N)} = (C³/2)·((1+4K_C)^N − 1) 在 N=2 完全一致。
- **3D/4D 常数**：`M_bound_3d 4 = 3968`、`M_bound_4d 4 = 19968`——紧度在当前松弛下
  失效，正确归类为理论演示而非实用证书。
- **H_dom 反射化状态**：2D 窄轨的 H_dom 判定已做成可运行时检查（FrameCheck2DNarrow，
  单轴退化 n₁=1 ∨ n₂=1 情形，带健全性证明）；3D/4D 的轴间支配条件尚未编写反射判定器
  （可判定但未工程化）——3D/4D 证书是纯静态定理，为框架理论的纯粹扩展。

## 8. 可证明性边界与碰撞刻画

- **P2（单对触发）** `pair_bound_gt_4_5`：0 < n < n′ 且 d = n′−n < (5/8)√(nn′) ⟹
  保守对界 B(n,n′) > 4/5 ⟹ 行和 > 4/5 ⟹ 检查器拒绝。（备注：5/8 阈值是 iff——d < (5/8)√(nn′)
  ⟺ 64n′²−153nn′+64n² < 0 ⟺ B > 4/5，同一二次型；"收紧检查器保守界"无空间，假阴性收紧路径
  在有理松弛→精确算术（Zarith）与 `cert_optimize` 子框架搜索。）
- **P3（增长引理 + 主定理）** `pareto_law_main`：m 个相完备带 0 < f(0) < … < f(m−1) ≤ N
  且检查器通过 ⟹ 3·c^(m−1) ≤ N（c = ((5+√281)/16)² ≈ 1.8501）。**N=511 推论**：m ≥ 10
  必被拒绝。
- **随机版（T2a/T2b）**：同箱对触发 P2 ⟹ P(拒绝) ≥ 1 − (9)_m/9^m；m=7 ⟹ ≥ 96/100、
  m=8 ⟹ ≥ 99/100；m ≥ 10 由鸽笼确定性覆盖（`ten_bands_reject` 初等替代证明）。
- **碰撞距离**：精确碰撞 ⟺ 角度有理（`collides_iff_rational_witness`，构造性 iff）；
  最小碰撞距离 = 分母（纯网格 q=1 恰为 N；偏移分母 q 把碰撞推至 q·N——"零成本旋钮"）；无理偏移
  （黄金比）⟹ 永无精确碰撞（`irrational_offset_no_collision`）；线性偏置（ALiBi）无碰撞端点
  （`linear_bias_no_collision`，非周期核，碰撞距离 = ∞）。
- **U5 黄金近碰撞半径**：∀ d ≥ 1、∀ m ∈ Z：|d·φ_gold − m| ≥ 1/(3d)
  （`golden_near_collision_gold`，代数数范数路线，零公理；承载于 z 区探针 `probe_nearcoll.v`，附录 A 索引）。
- **P1/P1′（精确窗口相干下界）**（src/P1Coherence.v）：1 ≤ n < n′、d ≤ n′/2 ⟹
  coh_T ≥ (2/π)·√(n/n′)；精细版 coh_T ≥ √(n/n′)·(1 − π²d²/(6n′²))（Jordan + sin_bound
  交替级数，coqchk 复核通过）——近邻大带相干 ≈ 0.997 的解析根源成为定理。
- **Parseval 能量守恒（μ=0 退化端点）**（probe_parseval）：互异网格原子在 a·N 窗口
  ‖Σc_t·u_t‖² = Σ|c_t|²（等式而非界——框架界退化端点）。
- **窗口无关 Dirichlet 部分和界**（probe_partial）：j ≢ 0 (mod N) ⟹
  ‖Σ_{k<W} e^{2πikj/N}‖ ≤ N/(2·min(j mod N, N−j mod N))，窗口无关。
- **任意角度对 Dirichlet 界与混合网格相干界**（probe_pairdirichlet）：任意角度 t1 t2，
  差频 = 2π·j/N（j mod N ≠ 0）⟹ 任意窗口 W 上 ‖Σ e^{ik·t1}·conj(e^{ik·t2})‖ ≤
  N/(2·min(j mod N, N−j mod N))（`pair_dirichlet`）；推论 `mixed_grid_coherence`：嵌套网格
  N 与 a·N 两原子跨网格相干界——grid 崩塌后多尺度设计空间的定理。
- **τ 三分**（probe_taudicho，零公理）：碰撞质量 τ 的窗内/OOD/三分刻画。权威独立模块：`ca_tau.v` `tau_crop_mono`（N1≤N2 ⟹ Στ 裁剪单调，纯 mathcomp 零公理）。。
- **素数阶梯分辨率与最优性**（src/CRTResolve.v + probe_ladderlimit）：存在性
  `prime_ladder_8` + `prime_ladder_8_pairwise_coprime`（8 素数链 [3,7,13,29,59,127,251,503]，
  两两互素）+ 分辨率 `crt_inj`（联合模单射，lcm ≈ 7.49×10¹² ≫ 8× 视界）+ **最优性
  `no_nine_band_ladder`**（[3,511] 不存在 9 元素素数阶梯，贪心交换论证，贪心链 113/211/397
  更紧）——素数阶梯论证完整（存在性 + 分辨率 + 最优性），支撑论文 B 素数阶梯受控对照（prime-7
  vs prime-8）。
- **容错 Gershgorin（分级证书）**（probe_robust）：坏对每行 ≤ δ·n ⟹ 绝对行和 ≤ n·(μ+δ)；
  **μ+δ ≤ 4/5 ⟹ 通过帕累托阈值**——检查器从二元升为分级证书。
- **一般维张量**（probe_tensor）：N 轴张量积 off-diag 行和 ≤ **(1+r)^N − 1（∀N 闭式）**——
  论文 B §6 跨维推测得证（2D/3D/4D 为 N=2/3/4 特例）。
- **核漂移（T4 完全体，已并入 PSA_framework PhaseCoherence）**：`kernel_drift_controls_attention`
  ——核逐点漂移 ≤ dc、系数 ℓ1 ≤ dd ⟹ **softmax ℓ1 TVD ≤ e^{2·dc·dd} − 1**
  （`coherence_controls_attention` 的核漂移姊妹定理）；`kernel_identical_tvd_zero`：K=K' ⟹
  界=0——网格族（任意 a·N 窗口核相同）"注意力核表示级不变性"的证书 0 端点。**首个实例
  （CS-18，`probe_ab_bridge_pier.v`，2026-08-30）**：`psi_attention_tvd_trunc`——psi 核相邻位
  漂移界 `psi_kernel_drift_bound`（|psi_kernel n m k − psi_kernel n m (S k)| ≤ 2/(√n·√m)，三角
  不等式路线）+ 窗口截断一致化 dc = INR(W−W')·(1/2)（带 ≥2：√v_i·√v_j ≥ 2）⟹ softmax TVD ≤
  exp(2·dc·dd) − 1（dd = Σ|c_j|）——「无形式化桥梁」负面声明升级为「中间桥墩已机器检查」
  （桥面：端到端 PPL 影响量化仍为实证轨道）。
- **ρ^{−3/2} 紧界三件套**（probe_pairbound ① + probe_rowsum ② + probe_witness ③，
  2026-08-22 全部 Qed）：逐对界 ‖⟨ψ_a,ψ_b⟩‖ ≤ sin(πa/b)·√(ab)/(2(b−a))（`pair_inner_norm`，
  Jordan 分母，逐对 Θ(ρ^{−3/2})）；行和重组 **`row_sum_3halfs`**：C-稀疏梯子任意行 ≤
  2π·C^{−3/2}/(1−C^{−3/2})，**`row_bound_C4`：C=4 行和 ≤ 2π/7 ≈ 0.898 < 1——1D C=4 从空洞
  （2>1，仅存在性）变真实框架界**；见证封顶（③ probe_witness）：见证对 (2,2C) 精确内积
  `witness_exact` = sin(π/(2C))/√C，且 **`witness_sandwich`：(1−1/C)·[上界] ≤ 见证值 ≤
  [上界]——上下界之比 ≥ 1−1/C，C→∞ → 1（Θ(C^{−3/2}) 紧性封顶）**；常数演进线
  4K → 2K → Θ(C^{−3/2})（紧）封顶。

**意义**：本族与 §4 认证链正交，构成"认证（正）— 可证明性边界（负定律）— 碰撞/分辨率刻画
（机制）"三角；offset-grid（无理偏移）的证书保持（T1a/Parseval）、零精确碰撞（C5）与近碰撞
隔离界（U5）三半均机器检查。**配套实验已完成（论文 B §8.4，2026-08-22）**：offset-grid
@4096 16.12±1.32——ogrid ≥ grid 确认（碰撞机制第 6 个正向判决）+ **证书免费性被证伪**
（μ=0 精确正交 ∧ 零精确碰撞仍差 rand 2.4×）——与 P3 定理互证：**可证性（稀疏）与外推性
（稠密）在实证与定理双轨分离**。

## 9. 压缩感知：RIP 与稀疏唯一性（probe_incoherence.v 51 Qed + ca_rip_cr.v 33 Qed + probe_c4_instance.v 14 Qed + probe_row_rip.v 9 Qed + probe_recovery_cr.v + probe_uncertainty_cr.v 35 Qed）

频率阶梯原子族不仅构成稳定框架，还满足**低相干 → RIP → 稀疏唯一恢复**的完整链条：

- **原子规范** `psi_norm_one`：1 ≤ n ⟹ ‖ψ_n‖²_{pred n} = 1——频率阶梯原子族单位范数。
- **RIP 基元** `rip_bound2`：μ-不相干单位原子 ⟹ |‖c1u1+c2u2‖²_W − (c1²+c2²)| ≤ μ·(c1²+c2²)
  ——Gershgorin 型 RIP(2,μ) 界；支撑链 `norm_sq_combo2`（2 原子范数平方显式展开）。
- **k-原子 RIP** `CRrip_bound_k`（ca_rip_cr.v）：0 ≤ μ、单位范数、两两相干 ≤ μ ⟹
  |‖Σ_{j≤M} c_j·u_j‖² − Σ_{j≤M} c_j²| ≤ μ·(M+1)·Σ_{j≤M} c_j²——RIP(2,μ) 的 k-原子
  泛化（k = M+1，δ_k = μ(M+1)），证明链 `CRrip_lower_M` + `CRrip_upper_M` 经 `CRabs_def`
  组合；**纯构造性实数轨道**（Stdlib ConstructiveReals 抽象接口，Set 层 CRcarrier +
  Prop 层 CRle/CRlt），零经典公理、零 Admitted，29 引理全 "Closed under the global
  context"（同事补 P5 收缩链后现 33 定理）——对经典形式化的独立性验证。
- **稀疏唯一性** `sparse_uniquenessM`（主定理）：0 ≤ μ、单位范数、两两相干 ≤ μ、
  **μ·(M+1) < 1** ⟹ 窗口内零组合 Σ_{j≤M} c_j·u_j ≡ 0 ⟹ 系数全零——M+1 个原子的稀疏表示
  唯一恢复。证明链：`rip_lower_M`（RIP 下界归纳）→ l2=0（零组合）→ (1−μ(M+1))Σc_j² ≤ 0
  → Σc_j² = 0 → `sum_sq_zero` 逐项归零。
- **C=4 实例拼接** `C4_sparse_uniqueness_3`（probe_c4_instance.v）：C=4 阶梯
  [3,13,53,213] 六对相干上界（pair_*，已在 PSA_framework）组装为 μ := 11289/33920
  < 1/3 ⟹ 前 3 原子 [3,13,53] 两两相干 ≤ μ 且 μ·3 < 1 ⟹ sparse_uniquenessM 实例化
  （M=2）：窗口内零组合 ⟹ 系数全零——**3 原子稀疏唯一恢复实例**（审计仅 Dedekind 基础
  设施，零自定义公理）。
- **行和 → RIP 桥接** `row_rip_bound_M`（probe_row_rip.v）：**行非对角和假设**
  （∀i≤S M：Σ_{j≠i}|⟨u_i,u_j⟩| ≤ μ_row，对角排除）⟹ k-原子 RIP（k = M+1）：
  |‖Σ_{j≤M} c_j·u_j‖² − Σ_{j≤M} c_j²| ≤ μ_row·M·Σ_{j≤M} c_j²——**δ_k = (k−1)·μ_row**，
  比两两相干 μ 版（δ_k = μ·k）更紧（μ_row ≤ M·μ_pair，行和一次求和直接控制全部非对角
  交互）；证明链 `row_sum` → `row_cross_bound`（交叉项界：2|c_{SM}|·|⟨comboM,u_{SM}⟩|
  ≤ μ_row(Σ_M + c_{SM}²)，ipW_combo_l + 三角 + AM-GM + 单对≤行和）→ `row_rip_lower_M`/
  `row_rip_upper_M`（上下界归纳，IH 行和前提前缀单调截取）→ `row_rip_bound_M`
  （`Rabs_le` 组合）。9 Qed / 0 Admitted / 0 自定义公理。对接 `row_bound_C4`（C=4 行和
  ≤ 2π/7 ≈ 0.898 < 1，见 §8 ρ^{−3/2} 紧界三件套）⟹ k=2 时 δ = 0.898 < 1。
- **唯一性 ⟹ 恢复正确性骨架** `CRrecovery_correct_prefix`（probe_recovery_cr.v，构造性轨道）：
  0 ≤ μ、单位范数、两两相干 ≤ μ、**μ·(M+1) < 1** ⟹ 同一信号两个表示 Σ_{j≤M} c_j·u_j ==
  Σ_{j≤M} c'_j·u_j ⟹ ∀j≤M: c_j == c'_j——稀疏唯一性定理的构造性对偶（"唯一性 ⟹ 恢复
  正确性"确定性骨架，不碰 OMP 算法本体）；证明链：差分线性 → 差组合零 → 差组合范数平方零
  → 差组合 RIP 界（`CRrip_bound_k` 实例化）→ 收缩链（`CRle_scaled_le_zero` + 平方和零 ⟹
  逐项零 + ring 收尾）；零经典公理（"Closed under the global context"），与 ca_rip_cr P5
  代数引理协同。
- **相干字典不确定原理** `CRuncertainty_principle`（probe_uncertainty_cr.v，构造性轨道）：
  **支撑大小口径**（Donoho-Stark 相干字典不确定原理的构造性正形式）：0 ≤ μ、单位范数、
  两两相干 ≤ μ（支撑并集 T1∪T2 上）、**μ·(|T1|+|T2|−1) < 1** ⟹ 同一信号两个稀疏表示
  Σ_{T1} c·u == Σ_{T2} d·u（c/d 在各自支撑外为零）⟹ ∀j: c_j == d_j——稀疏表示唯一性的
  **实际支撑大小版**（比前缀口径更强）；证明链：列表支撑 RIP 下界（`lst_rip_lower`：
  Σe² ≤ ‖Σ_{j∈T} e_j·u_j‖² + μ(|T|−1)Σe²）+ 支撑合并（`list_undup`）+ 零项吸收
  （`lst_sum_restrict`）+ 收缩链（R4 同构）；35 定理全 Qed、零经典公理。**常数口径诚实
  标注**：经典 |S|+|S'| ≥ 2/μ 需两正交基乘积版（a·b ≥ 1/μ²，Donoho–Huo），一般相干
  字典的标准常数是 **1+1/μ**（Foucart–Rauhut）。
- **字典最优性 ⟹ 恢复保证合成（G-8）** `CRg8_recovery_synthesis`（probe_g8_synthesis_cr.v，
  构造性轨道）：**压缩感知三角闭合合成定理**——若字典相干 μ 同时满足 **Welch 下界**
  （平方形态 `(INR M − INR N) ≤ INR N·INR(M−1)·μ²`；前提状态（2026-08-31 升级）：该前提已由
  G-7 构造性证明闭合（见下条 `g7_welch_lower`，与 G-8 前提签名逐字一致））与 **F5 唯一性窗口**
  （`μ·(|T1|+|T2|−1) < 1`），则同一信号的两个 |T|-稀疏表示必相同（∀j: c_j == d_j，直接
  实例化 F5）；配套相图定理 `CRphase_window_nonempty`：Welch 下界 + F5 窗口 ⟹ **窗口非空
  参数条件** `(INR M − INR N)·(INR T)² < INR N·INR(M−1)`（"Welch < 1/|T| 时唯一性窗口
  非空"的定量刻画——μ 落在 [Welch, 1/|T|) 区间才有唯一恢复的相图结论）；证明链（纯 CR，
  手工引理链无 nra/lra）：`CRsqr_lt_one`（0 ≤ z < 1 ⟹ z² < 1）→ (μT)² < 1 → Welch 两边
  乘 T² → ring 整理 → N(M−1)(μT)² < N(M−1)（乘 0 < N(M−1)）→ CRle_lt_trans 组装 → F5
  实例化。6 Qed / 0 Admitted / 0 自定义公理，**Print Assumptions 双定理 Closed under the
  global context（零经典实数）**。**定位**：G-8 是"字典设计最优性（Welch 下界）⟹
  恢复保证（F5 唯一性）"的定量桥，把压缩感知"唯一性⟺恢复⟺相干区间"的相图结构定理化；
  其 Welch 前提已由 G-7 构造性证明闭合（见下条）。
- **Welch 下界构造性证明（G-7，纯构造性轨道，2026-08-31 新增）** `g7_welch_lower`
  （probe_g7_welch_cr.v）：**Welch 下界平方形态的完整构造性证明**——M 个单位范数原子
  （实向量，维度 N，N < M）两两相干 ≤ μ ⟹ `(INR M − INR N) ≤ INR N · INR (Nat.pred M)
  · mu · mu`（与 G-8 前提签名逐字一致）。证明路线：Frobenius 范数与 Cauchy–Schwarz
  不等式（避免特征值论证——构造性实数轨道无谱定理可用）：①迹恒等式（帧算子对角和 =
  INR(M)，单位范数经求和换序）；② Cauchy–Schwarz（Lagrange 恒等式 `cs_core`：双和
  平方差非负，零开方、零特征值）；③ 部分和 ≤ 全和；④ Frobenius 恒等式（帧算子与
  Gram 矩阵的 Frobenius 范数相等，四层求和换位）；⑤ 相干聚束（对角 = 1、非对角 ≤ μ²，
  对最大原子索引归纳，增量 1 + 2·INR(S M)·μ² 精确闭合）→ CR 代数移项（乘正消去）。
  **验收**：828 行 14 Qed / 0 Admitted / 0 公理，六段 Print Assumptions 全 "Closed
  under the global context"；提取物 g7_welch_cr.ml 经 DkMLNative ocamlc 编译通过；
  已并入合并版 `ca_merged_full_25_m2.v`（现 92743 行，69 模块分区，本地 2.5 全量编译 EXIT=0）。
  **范围（如实）**：实原子版（原子分量为构造性实数；G-8 的消费为抽象相干上界 μ，
  实版直接衔接）；复原子版（复向量内积的 Welch 下界）列为后续工作。
- **加权阶梯范数精确闭式（G-1，经典 R 轨道）** G1_norm_closed（probe_g1_norm_closed.v，
  21 Qed / 0 Admitted）：任意长度 M 组合的加权平方范数精确等式
  ‖Σ_{j≤M} c_j·ψ_{n_j}‖²_W = Σ_{j≤M} c_j²·‖ψ_{n_j}‖²_W + 2·Σ_{j<k≤M} c_j·c_k·K_W(n_j,n_k)，
  交叉项 K_W(a,b)=⟨ψ_a,ψ_b⟩_W 用单对 Dirichlet 核比闭式精确替换。定位：把上确界写成闭式，
  根治审稿 A-1/B-1 的 12.5× 口径混用；是 G-2/G-5/G-6 的共同前置。
- **相邻带相干渐近闭式 + 相变定理（G-2，经典 R 轨道）** mu_adj_decreasing /
  mu_adj_phase_transition / mu_adj_asymptotic（probe_g2_mu_adj.v，36 Qed / 0 Admitted）：
  比率 r 阶梯相邻带相干渐近极限 lim_{k→∞} μ(n_k, n_{k+1}) = μ_adj(r)，
  其中 μ_adj(r) := √r·sin(π/r)/(π(r−1))，存在相变点 r*（μ_adj(r*)=4/5，≈1.30）：
  r≥r* ⟹ 渐进可认证，r→1⁺ ⟹ μ_adj→1 不可认证。三定理覆盖：递减（两段式交叉夹逼）、
  相变存在（π<17/5 上界 + IVT 夹逼）、渐近（序列极限复合）——0.4502 相邻带下界 →
  2·0.4502 = 0.9003 > 4/5 的 G-4 前置。
- **检查器充分方向（G-3，经典 R 轨道）** `g3_certifiable_iff` + `g3_row_bound_mu`
  （probe_g3_criterion.v，5 Qed / 0 Admitted）：**反射检查器通过 ⟹ 每行精确相干
  行和 ≤ p/q**（框架界 (1±p/q) 的充分条件；名字沿自早期草稿，实为单向蕴含——
  D7 审查点如实降格）。真 iff 见 G-11（`probe_g11_checkiff_cr.v`：通过 ⟺ 逐行 ≤ 阈、
  拒绝 ⟺ 存在超阈行、假阴性量化 iff，行级精确有理层）。与 G-5 反例共同构成
  可判定性边界的完整刻画。
- **可判定性溢价反例（G-5，经典 R 轨道）** `g5_premium`（probe_g5_premium.v，
  35 Qed / 0 Admitted）：**存在具体阶梯 [3,7,15]：反射检查器拒但精确 Gram 相干
  行和 ≤ 4/5**（完整口径闭式，|⟨ψ_3,ψ_7⟩|≈0.3777、|⟨ψ_7,ψ_15⟩|≈0.4094，
  行和≈0.787043，与评估文档一致；π 界自证 π∈[3.141,3.142] + sin_bound 数值界）——
  把"假阴性 49.1%"的论述升级为具体机器检查反例，是 G-3 必要方向的直接见证。
- **G-5 构造性三角资产（纯构造性轨道）**：M1 构造性 π（`probe_pi_cr_m1a` 25 Qed +
  `probe_pi_cr_m1b` 43 Qed，Leibniz 级数 + CR_complete，3.141 ≤ π ≤ 3.142）、
  M2 构造性 sin（`probe_sin_cr_m2` 39 Qed，交替幂级数）、M3 构造性 sqrt
  （`probe_sqrt_cr_m3` 59 Qed，Q 层二分，√21 ≥ 458/100、√105 ≥ 10246/1000）——
  纯 ConstructiveReals、零经典、零 Admitted、零自定义公理，Print Assumptions 全
  Closed，已并入合并版 `ca_merged_full_25.v`（67 模块分区，MERGE_EXIT=0）。定位：
  G-5 主定理构造化版本的三角基座；**M4 可判定性溢价主定理已构造化完成**（2026-08-26：
  `probe_decidability_premium_cr.v` 并入合并版 25 模块 55/55，Gram 相干行和 ≤ 63/80 + 反射界 21/16
  + 溢价 5/3，核心 `m4_CRinv_le_contravar` 纯构造反变单调，`m4_decidability_premium : {w & CRle w (63/80)}` Set 层 sigT 定理，Print Assumptions 全
  Closed——相干缺口闭合的构造性完成）。
  **意义**：本工作在**通用层**建立可认证稀疏恢复的理论保证（单位范数 + RIP(2,μ) 基元 + k-原子 RIP + 行和版 RIP 桥接 + 稀疏唯一性 + 唯一性⟹恢复正确性骨架 + 相干字典不确定原理（支撑大小版） + 字典最优性⟹恢复保证合成（G-8），机器检查，其中 k-原子 RIP、唯一性骨架、不确定原理与相图合成走纯构造性实数轨道、零经典公理），并在 **C=4 阶梯完成实例级拼接——注意仅前 3 原子 [3,13,53] 获得稀疏唯一恢复**（`C4_sparse_uniqueness_3`，3 原子唯一恢复，**非 4 原子**；第 4 原子 213 未覆盖）；全窗口 [3,13,53,213] 四原子的稀疏唯一性扩展**不在本 Artifact 中**——全库零 `Admitted`、零挂起证明义务（CI 语句形 grep + coqchk 内核复验 + 165 项 Print Assumptions 审计三重背书）；必要的逐对相干界虽已在 `PSA_framework.v`，但两两相干判据对四原子已关窗（μ·4 = 45156/33920 > 1，`c4_mu4_window` 机器判定），扩展须改走精确 Gram 特征值口径的数值裁决，其结果（λ_min 是否 > 0）未定——「直截」仅指判定动作本身，不预支结论。该扩展与更大阶实例（如 C=9 的 s≤4 或全窗口 [3,13,53,213] 四原子）及与 ρ^{−3/2} 行和紧界的合成显式列为后续工作（future work 第一项）。**4 原子障碍分析**：两两相干口径硬限制 μ·4 ≈ 1.33 > 1；出路——精确 Gram 特征值口径（G-1 闭式）、严格 3-稀疏信号由 `sparse_uniquenessM` 覆盖、Welch-窗口合成的理论极限陈述。**数学新颖性说明**：sparse_uniquenessM、CRrip_bound_k、row_rip_bound_M、CRrecovery_correct_prefix、CRuncertainty_principle、CRg8_recovery_synthesis 与 C4_sparse_uniqueness_3 是 Gershgorin/互干性唯一恢复、RIP、Donoho–Stark 不确定性原理与 Welch 界-恢复保证相图的机器检查（Welch 下界本身亦为经典结果的构造性机器检查），数学上非新，形式化价值在 Coq 验证（含 C=4 具体常数核验、行和版 RIP 常数紧化路径、构造性轨道独立性验证与三角闭合相图合成）。本族主要探针已并入合并版 `ca_merged_full_25.v`（67 模块分区，MERGE_EXIT=0），
独立 + 合并双通过；G-3（probe_g3_criterion）/G-5（probe_g5_premium）**已并入合并版**（2026-08-30 M2 批次），probe_recovery_cr 为构造性轨道独立验证。

- **τ 裁剪最优性（CS-11，经典 R 轨道，2026-08-28 新增）** `probe_taugrid.v`（17 Qed / 0 Admitted）：**覆盖债精确量化** `coverage_fraction`/`coverage_debt`（S T < n ⟹ 窗 [0,T] 内能量恰 = (T+1)/n，窗外能量 1−(T+1)/n ∈ (0,1)——**τ 负债的机器可计算量**，"剪 255/127/63 应恶化"的定理侧镜像）；**支撑完备刻画** `support_classification`（n ≤ T ⟺ ψ_n 完全支撑训练窗，iff）；**裁剪证书单调** `prune_row_le`（kept 子族行和 ≤ 全族——上界型证书不损）；**C-梯子稀疏化迁移** `thinning_preserves_ratio`；**三连合成** `tau_prune_optimality`——randmax256/384 裁剪实验的定理化。
- **构造性孪生（CS-12，纯构造性轨道，2026-08-29 新增）** `probe_taugrid_cr.v`（13 Qed / 0 Admitted，Print Assumptions **全 Closed 零公理**）：抽象接口 `{R : ConstructiveReals}` + 归一梯子 u（cos/复指数构造性未实现，接口与主线数学一致）；**严格序 CRlt 本身是 Set 值**（ConstructiveReals.v:88 库设计），覆盖债界定定理以信息性形式 **0 < debt < 1**（Set 值 prod，证明项可提取）陈述，主定理结论 prod 型（信息性分支不能进 Prop 的 /\），sigT 被类型系统强制；序判定下放 Q 层（Qlt 判定经 CR_of_Q_lt 提升为带数据 CRlt，CRlt_proper 信息性搬运）；**提取 `taugrid_cr.ml` 经 DkMLNative ocamlc 4.14.2 编译通过**（柯西实例 cRealConstructive 具象化）。
- **CS 生产线（CS-13，经典 R 轨道，2026-08-29 新增）** `probe_cs.v`（29 Qed / 0 Admitted，审计仅 Dedekind 三允许公理）：**一致 RIP** `cs2_rip_uniform`（(1−δ)‖c‖² ≤ ‖Φc‖² ≤ (1+δ)‖c‖²，δ = 4K(C) **∀s 一致**）；**★s-sparse 唯一性** `cs3_energy_zero`/`cs3_unique`（C ≥ 10：测量 y = y' ⟹ 系数 c = c'——测量端信息不丢失）；**embedding** `cs6_embedding`（1−2K(C) > 0）；**spark 下界** `cs1b_spark`（spark ≥ n+1，Elad–Bruckstein 判据）；**逐对相干** `cs1a_pair_bound`（≤ 2πq/(1−q)）；**★近重复对爆炸** `near_dup_coherence_12`（coh 1 2 = **1/√2 精确值**）+ `cs4c_explosion`（**2μ = √2 > 1**——s ≥ 3 时 Gershgorin 型 RIP 证书在含近重复对梯子上必然失效，"剪 503/255/127 应恶化"完整定理链）。
- **offset 无关性（CS-14，经典 R 轨道，2026-08-29 新增）** `probe_cs5.v`（5 Qed / 0 Admitted）：**同族平移 t→t+δ 下跨网格对相干界不变**（≤ N/(2·min(j mod N, N−j mod N))，**右端不含 δ**——偏移在差频中相消，pair_dirichlet 接管）；**黄金比隔离界** `cs5_golden_moat`（1/(3d) ≤ |d·φ_gold − m|）；**offset 语义非空** `cs5_gold_not_grid`（φ_gold ∉ ℤ）——ogrid 实验的定理侧。

- **正向随机侧（CS-20，经典 R 轨道沉没资产入文，2026-08-31）** `pairwise_inner_bound_probabilistic`
  （src/ca_sparse_ext.v，已 Qed）：超线性增长阶梯（f(S i) ≥ c²·f i，c ≥ 2）的 p-偏置随机子阶梯，
  满足逐对内积条件的概率权重 ≥ 1 − N²p²（`sum_over_subsets_weight` 归一化测度，ca_probabilistic）
  ——与 T2b 构成随机侧完整对偶：log-uniform 无增长约束 ⟹ whp 拒绝；增长受控 ⟹ whp 逐对可控。

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

- **审计总量**：PSA_audit.v **165 项** Print Assumptions，RC=0，零 Admitted；**完整运行日志
  `审计证据/audit_run_20260826_full.txt`（165/165 块随稿 co-locate，111 段 Axioms + 54 项 Closed，2026-08-26 重跑）+ 定理索引 `audit_index_20260826.txt`**；构建配置 `_CoqProject`/`Makefile`/`_merge_ca.py` 随稿。
- **公理依赖（全部 165 项仅此）**：sig_not_dec / sig_forall_dec + functional_extensionality_dep
  ——标准 Dedekind 实数基础设施，**属可接受的 Reals 基底，非本开发应用层引入、非 `Classical_Prop.classic` 公理（显式声明）**；`Classical_Prop.classic`（排中律宏）
  **零出现（post-M1.5 复核成立）**。「classical-free」精确指排中律宏零出现，而非「无任何经典原则」——完整构造性未声称。**外部依赖说明**：mathcomp / Coquelicot 未纳入 165 项审计，"零 `Classical_Prop.classic`"仅限本开发应用层，不推广到整个开发依赖（Coquelicot 基于实数库，可能含经典公理，已明确声明）。
**审计范围与合并版全基态的边界**：165 项审计的对象是 `PSA_framework.v` 应用层定理；合并版 `ca_merged_full_25.v` 其余模块中，`mu_adj_phase_transition`（μ 单调 ⟹ 相变存在性定理）的公理依赖含完整排中律 `classic`（CI 与本地编译日志一致确认）——"零 `Classical_Prop.classic`"结论限于 165 项审计范围，不覆盖合并版全部定理；应用层注意力证书/框架界/反射检查器定理链不受影响。审计分层口径：165 项输出块 = 54 项 Closed under the global context + 111 项 Dedekind 公理依赖（80 项三公理依赖 + 29 项 sig_forall_dec+fext + 2 项仅 sig_forall_dec，机器可读索引 `audit_index_20260830.json`）；构造性轨道（ca_rip_cr.v 33 定理、probe_uncertainty_cr.v 35 定理、probe_taugrid_cr.v 13 定理）各有独立 Print Assumptions 审计且全部 Closed，不在 165 项之内。**构造性轨道公理依赖（单独列出，2026-08-30）**：Stdlib `ConstructiveRcomplete.v`（ConstructiveReals 接口与柯西实例）自身 Axiom/Parameter 计数 = **0**（源文件直接核验——接口不依赖 funext、不依赖排中律）；构造性轨道各模块 Print Assumptions 全部 "Closed under the global context"（零公理，含 funext/classic 均零依赖），机器可读清单 `constructive_track_audit_20260830.json`。**审计计数勘误（166/165 差异关闭）**：PSA_audit.v 头注释提及 "Print Assumptions" 字样致子串计数 +1——语句实为 165 条，与日志 165 块一一对齐。
- **M1.5 经典清零（post-M1.5 复核）**：`Module ExpSeries` 已 Qed（exp 幂级数路线），`exp_mono_le` 改走级数
  路线，语句不变、下游零改动——整个 CertifiedAttention 模块为纯构造性（不依赖实数完备性
  的排中律），据我们所知，这是第一个不依赖实数完备性排中律的深度学习注意力形式化验证。
  **过时记载更正**：`PSA_audit.v` L108–121 所载"4 项经 exp Rpower/MVT 继承 classic"系 pre-M1.5
  （2026-08-19）过时记录；合并版 L63579（Module ExpSeries）/L63672（exp_mono_le_noclassic）/
  L63719（应用）已并入，4 个注意力定理位于其后，`exp_increasing` 仅存于 ca_* 基础设施（非审计目标）。
- **提取计算性**：上述公理仅在证明层（Prop）使用，不参与提取的计算内容——提取出的判定函数
  为纯构造性计算。
- **新定理族审计**：ParetoLaw/P1Coherence/ParetoRandom 仅 Stdlib Reals 自包含（其 165 项
  审计范围以 PSA_audit.v 为准，P1 的经典 MVT 路线位于应用层之外，已明确声明）；z 区并入合并版的
  8 经典 pro 化探针 + c4_instance（共 9 个）各自 Print Assumptions 仅标准库公理。

## 12. Artifact & Reproducibility

> **代码仓库**：https://github.com/hy7pc8gfmf-dotcom/PSA-CertifiedSparseGating（Coq 形式化 + 论文 + 实证 + CI，Apache-2.0；CI 徽章见 README）。预印本 DOI：10.6084/m9.figshare.33312189。

- **代码分布**：`src/`（正式模块，含 `_CoqProject`）；`z/`（探针）；合并版
  `src/ca_merged_full_25_m2.v`（92743 行，69 模块分区，探针族与构造性轨道全量并入至 G-9）；归档基态
  `D:\ComplexAnalysis\30模块\`（ca_* + 探针 pro 版 + ca_zeta_euler + ca_rip_cr + 合并版，
  SHA-256 与 src/z 一致，旧版备份 `.sync-backup-20260823/`）。
- **依赖版本**：Rocq/Coq 9.0.1（`C:\Rocq-Platform~9.0~2025.08\bin\coqc.exe`）；mathcomp
  （本地 vendored `lib\mathcomp`）；Coquelicot（`lib\Coquelicot`）；Windows 10+ / PowerShell 7。
- **构建命令**：各模块独立编译 `coqc -Q <src> "" -Q <z> "" -Q <mathcomp> mathcomp
  -Q <Coquelicot> Coquelicot <file>.v`；合并版重新生成 `python src/_merge_ca.py`，合并编译
  `coqc -Q <mathcomp> mathcomp -Q <Coquelicot> Coquelicot src/ca_merged_full_25_m2.v`
  （本地 2.5 全量 EXIT=0）。**CI 可复现性**：GitHub Actions 缓存 lib 链与合并版 .vo（按源 hash 失效），
  编译命令 `scripts/ci_build.sh`（mathcomp 2.6 前缀经 sed 适配 boot.*）。
- **审计脚本**：PSA_audit.v（165 项，输出 `audit_run_20260826_full.txt`）；PSA_3D_audit.v（10 项）；
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
  常数界**而非类型/内存安全证明。与 **VST/Iris** 等分离逻辑框架的方法论类比：同为「证明
  随组件携带」，但证书对象不同——VST/Iris 面向内存安全与并发正确性，本工作面向数值界
  （有理常数证书），领域正交、思想同源。
- **Lean/mathlib 的数值分析形式化**：mathlib 的经典实数与分析学体系与本开发 Dedekind 主轨
  哲学一致；本开发构造性轨道的 ConstructiveReals（柯西序列、CRlt 为 Set 值）与 Lean 经典
  Real 在「序是否携带信息」上的哲学差异，构成构造性/经典双轨对照的第三参照系。
- **稀疏注意力无证书方法**：top-k、KV 逐出、低秩投影均无误差证书——本工作覆盖的解析核层
  是上述方法的形式化对照面。
- **压缩感知（RIP/稀疏恢复）**：Candes–Tao 的 RIP 与稀疏唯一恢复理论是本工作 §9 的数学
  背景；本工作是该理论在频率阶梯原子族上的 Coq 机器检查实例。
- **与论文 B 的关系**：论文 B 的实证结果验证本工作形式化框架（同一阶梯族）的适用性；本工作
  的框架界/能量界为「免修改 + 证书」定位提供理论支持——主张正交：形式化保「表示稳定性/
  能量有界」，实证报「外推 ppl」。

### 13.1 Design Choices vs. Alternative Libraries

**Real-number representation: Dedekind main track + ConstructiveReals dual track.**
The main track uses the Stdlib Reals Dedekind reals, for two reasons: (a) mature
interoperability with Coquelicot (`Cexp`, complex numbers, derivatives) and the
mathcomp ecosystem; (b) the three classical axioms (`sig_not_dec`,
`sig_forall_dec`, `fext`) are used only at the proof layer and never enter the
extracted computational content. The cost is non-constructivity; the core
theorems (k-atom RIP, sparse uniqueness, coherent-dictionary uncertainty,
decidability-premium synthesis) are therefore independently re-proven over the
Stdlib `ConstructiveReals` (Cauchy-sequence representation whose `CRlt` carries
approximation data as a Set), giving `ca_rip_cr.v` (33 theorems, zero axioms) as
an independence check on the classical formalization rather than a redundancy.
We did not use mathcomp's `algR`/`realalg`: they target algebraic reals and do
not cover the analytic structure needed for `sin`/`π`.

**Rational layer: mathcomp `Q` + boolean reflection.** The certificate decision
layer (μ=4/5, 11289/33920 < 1/3) lives entirely in the rationals. mathcomp's `Q`
was chosen over Stdlib `QArith` for consistency with the ssreflect boolean
reflection style (`<=?`/`<?` decisions map directly to runtime booleans) and
native `Qle_bool`/`Qeq_bool` decidability.

**Why not Flocq**: Flocq formalizes IEEE floating-point semantics; its goal is
correctness of float implementations. Our goal is the opposite — replacing
floating-point numerical bounds by decidable rational certificates. The two are
orthogonal. **Why not interval arithmetic** (Coquelicot Interval / the Interval
plugin): interval methods produce enclosing intervals with externally certified
bounds; our relaxation chain (floor-sqrt → Jordan → Dirichlet → π←22/7) reduces
the certificate layer to one-sided rational domination closed by `compute;
field` — no interval arithmetic, no oracle. **Why not CoqEAL refinement**: the
refinement paradigm suits "Nat prototype → efficient Z/bin"; our direction is
inverted — the `nat` checker is the *specification* (`frame_check_instance_sound`
is stated about the nat decision procedure) and the OCaml int mirror is a
runtime approximation (§6).

**Reflective checker vs. general decision procedures**: compared with CAD-style
decision procedures, `frame_check_instance` is not a general decision procedure
but a specialized *sufficient* condition for the Gershgorin row-sum test —
conservatively sound (false-negative rate 49.1% quantified; exact-layer
iff-criterion proven as G-3; false negatives attributed to the decidability
slack layer, not to checker logic), trading generality for decidability and
runtime lightness (typical ladders < 1 ms).

**Graduated upgrade (CS-17, `frame_check_graduated`, probe_frame_check_graduated.v,
2026-08-30)**: the checker is upgraded from a binary verdict to a four-tier
graduated service — L1_tight (binary checker passes ⟹ Gershgorin frame bounds
[1/5, 9/5]·S), L2_composite (structure valid and per-pair coherence δ_ij ≤ 1 ⟹
composite energy bounds (S−coh, S+coh), automating the seven-band champion
certificate `champion_e5_composite_certificate`), L3_energy_only (black-hole
pair ⟹ upper half only), L4_rejected (structure invalid) — with soundness
theorem `frame_check_graduated_sound` discharging each tier's promise.
Computed distribution covers all four tiers ([3,13]→L1; [3,7,15]→L2, the
G-5 false-negative class demoted from rejection to degraded service; [2,3]→L3;
unsorted/empty→L4); the decision function is nat-extractable (graded entry
point for psa_guard).

### 13.2 Feedback on Rocq / mathcomp

Four rounds of large-scale adaptation (this development spans mathcomp 2.5/2.6
and Rocq 9.0.x/9.1.x) yielded the following first-hand feedback:

1. **ssreflect 2.5 → 2.6 rewrite behavior change**: the side-condition goal
   order of premise-carrying `rewrite H` flipped (last in 2.5, first in 2.6),
   systematically breaking position-dependent selectors (`2: {...}`,
   `; [t1|t2]`) across large scripts; β-redexes are not matched syntactically;
   `rewrite H in H' by tac` does not discharge side goals. *Suggestion*: a
   goal-order compatibility switch and β-normalizing matching; large
   developments should prefer explicit premise parameterization (immune to
   plugin versions).
2. **Scope hijacking**: mathcomp's `_ <= _`/`_ < _` nat notations resolve by
   scope-opening order, so the same notation may parse to different relations at
   different points of a file. *Suggestion*: an optional load mode that does not
   shadow Prop notations.
3. **Large nat usability**: `2^53`-scale nat literals trigger stack warnings and
   micromega fails on nonlinear nat goals — a painless nat↔Z casting layer is
   needed.
4. **`Print Assumptions` output lacks theorem names**: a 165-entry audit cannot
   mechanically align axiom blocks to theorems. *Suggestion*: an option to
   prefix outputs with theorem names — essential for audit automation.
5. **`Require` inside a module**: concatenated-file developments (our 87K-line
   merge of 55 partitions) inevitably trigger this warning — official guidance
   on safe conditions would help.
6. **Toolchain**: coqc with large output over pipes can deadlock (hundreds of
   warnings during merged compilation); file redirection is required — chunked
   flushing or documentation would help.

## 14. Limitations

- **高维证书**：3D/4D 是方法论可行性证明（骨架复用、维度推广逻辑闭合），常数远非紧
  （M_bound_3d 4 = 3968、M_bound_4d 4 = 19968），**不得用作实际误差界**——"Practically
  Non-Tight"按字面执行；3D/4D 的 H_dom 尚未反射化（可判定但未工程化；H_dom 经验苛刻——
  真实数据三轴频率独立增长、要求三轴同调增长很少满足），2D-wide 免 H_dom 不受此限制。
- **运行时检查器的量化范围**：int 镜像只在有限整数范围内且与 Coq 语义一致时接近 Coq
  soundness（§6 已明确声明）。
- **证书边界**：不证明学习投影下的注意力 logits 有界、Q/K 投影与位置旋转对易（酉不变性
  仅覆盖基函数层）、残差/LayerNorm 数值稳定性、训练后权重保证、外推 PPL 与框架界的语义
  联系。
- **审计范围**：165 项审计覆盖 PSA_framework 应用层；P1Coherence 的经典 MVT 路线在应用层
  外；Dedekind 实数基础设施的非构造原则已明确声明。
- **实证规模**：配套论文 B 为 toy-scale（~0.5M 参数、char-level），实证预览以 3-seed 为主、部分对照为单 seed；完整实证见论文 B。
- **对论文 B 的依赖边界**：本工作多处引用论文 B 的实证结论（七带基线、psi-rope-rand 等）作为动机与对照——论文 B 为独立投稿的预印本，其实验结论未经本审稿流程评审；本工作的形式化贡献（框架界/衰减界/证书）不依赖论文 B 的实证有效性，两者正交。
- **正交刻画单向**：μ=0 家族目前只证 ⟸ 方向（公共偏移 + N-网格 ⟹ 两两正交）；
  ⟹ 方向的完备化（不存在第三种正交家族）列为 future work。
- **形式化适用域**：全部证明依赖频率阶梯（seq 存在性）；对无位置结构的编码（NoPE 类）
  本框架无任何可证陈述。论文 B 实证给出定量交易曲线：有结构端以分布内 ppl ~2× 劣化
  （4.46 vs 9.06）为代价承受 OOD 相位混淆风险；形式化锁定的正是交易中有结构的一端。

## 15. Conclusion

本工作给出了「稀疏门控 + 频率阶梯基」完整解析核的 Coq 形式化：从确定性门控、框架界、
截断能量、softmax 稳定性到注意力近似，全部常数落在可判定的有理层；反射检查器自带健全性
证明，实例证书推广为通用运行时判定；可证明性边界（稠密与 μ≤4/5 互斥）、碰撞距离框架与
部署级证书族构成三角支撑；**压缩感知族（单位范数 + RIP(2,μ) 基元 + k-原子 RIP + 稀疏
唯一性）把「无条件基 + 频率阶梯」的理论优势推进到稀疏恢复**（k-原子 RIP 走纯构造性实数
轨道、零经典公理）。全部开发零 Admitted、零自定义公理，165 项审计
`Classical_Prop.classic` 零出现（post-M1.5 复核，完整 165/165 运行日志随稿）；合并版（92743 行，69 模块分区，探针族与构造性轨道全量至 G-9
ca_zeta_euler / ca_rip_cr）全量合并编译通过。与配套论文 B 的实证共同构成「可证性（稀疏）—
外推性（稠密）」双轨的机器检查 + 实证记录。

**可组合的反射化（方法论贡献）**：反射检查器的健全性证明是可组合的——3D 张量核的静态定理
与 1D `gershgorin_frame_mu` 共享同一骨架，其反射化是提取链的直和扩展而非基础理论修正；宽轨
家族 2D/3D/4D 成员齐备（N 维公式 M_bound^{(N)} = (C³/2)·((1+4K_C)^N − 1) 的 N=2/3/4 校验
全部定理级成立，且组合指数增长部分已升为 ∀N 定理，§8）；客观地讲，3D/4D 证书当前是非紧的
存在性结果，其价值在架构可组合性与维度推广的定位，而非常数本身；1D 证书（μ=4/5）保持紧且
不受影响。

**跨 A/B 证书—性能张力（声明）（证书 ⟹̸ 性能）**：本工作不构成「证书 ⟹ 性能」的虚假承诺。形式化与实证
的双轨记录表明：可证性（稀疏性/结构性）与外推性（稠密覆盖/随机性）在频率阶梯语境下呈温和
负相关——三角关系如实记录：随机阶梯在定理侧高概率被拒绝（T2b 负定律）却是实证侧旋转族内
最优（psi-rope-rand 6.45）；μ=0 网格拥有最干净的精确正交证书却外推性能严重退化（25.66）；ALiBi 无
碰撞端点定理侧成立且实证全局最优（4.47）却零证书。证书的价值不在预测 PPL，而在提供**可
审计的表示稳定性保证**——这是高风险部署场景中独立于性能指标的决策依据（论文 B §13 同步
此声明）。

---

## 附录 A 代码-论文声明交叉索引（对齐当前代码基态）

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
| **压缩感知族（CS-1/2/2′/3）** | **z/probe_incoherence.v（psi_norm_one / rip_bound2 / sparse_uniquenessM，51 Qed）+ src/ca_rip_cr.v（CRrip_bound_k，k-原子 RIP 构造性轨道，33 Qed）** | ✅ **已并入合并版** |
| ρ^{−3/2} 行和紧界 | z/probe_rowsum.v（row_sum_3halfs / row_bound_C4，23 Qed） | ✅ **已并入合并版** |
| 任意角度 Dirichlet / 混合网格相干 | z/probe_pairdirichlet.v（pair_dirichlet / mixed_grid_coherence，5 Qed） | ✅ **已并入合并版** |
| Parseval / Dirichlet 界 | z/probe_parseval.v / probe_partial.v（19+27 Qed） | ✅ **已并入合并版** |
| ρ^{−3/2} 逐对紧界 | z/probe_pairbound.v（5 Qed） | ✅ **已并入合并版** |
| 碰撞刻画 / τ 机制 | z/probe_collision.v / probe_tchar.v / probe_taudicho.v | ✅（z 区独立验证） |
| 部署级证书族 | z/probe_kvevict.v / probe_quant.v / probe_multihead.v / probe_exprat.v | ✅（z 区独立验证） |
| Welch 下界构造性证明（G-7） | z/probe_g7_welch_cr.v（g7_welch_lower，14 Qed 6×Closed） | ✅ **已并入 m2 分区 68** |
| 渐近闭合式双带夹逼（G-9） | z/probe_g9_pairfrac_cr.v（10 项 4×Closed） | ✅ **已并入 m2 分区 69** |
| i01 区间构造性代数 + noisy-OR 组合证书（G-10） | z/probe_itv_noisyor_cr.v（iq sigT 接口，6×Closed） | ✅（z 区独立验证） |
| 检查器真 iff（G-11，D7 修复） | z/probe_g11_checkiff_cr.v（check_iff/reject_iff/fn_iff/decision_cert，6×Closed） | ✅（z 区独立验证） |
| 概率逐对界正向随机侧（CS-20） | src/ca_sparse_ext.v（pairwise_inner_bound_probabilistic） | ✅（库内已 Qed，本轮入文） |
| 合并版 | src/ca_merged_full_25_m2.v（92743 行，69 模块分区，探针族全量至 G-9） | ✅ **本地 2.5 全量 EXIT=0（run20）** |
| 归档基态 | D:\ComplexAnalysis\30模块\（SHA-256 与 src/z 一致） | ✅ |

---

## 附录 B 独立主线：欧拉乘积式的构造性证明（ca_zeta_euler.v，173 定理）

> **甄别说明**：本附录对应代码库中的**独立构造性主线** `src/ca_zeta_euler.v`
> （**173 定理** / 0 Admitted / 0 Axiom / EXIT=0，src = 30模块 归档 SHA-256 一致）。它与正文
> 认证管线（§4-§10）**正交**——正文所有主张不依赖它；它作为**级数侧的独立数学贡献**
> 与「可认证稀疏」的表示稳定性主张互补（欧拉积 = 解析数论的经典恒等式，此处给出
> 构造性实数上的零公理机器证明）。

**主定理**（`Theorem euler_product`，L3419-3451，构造性 CR，零公理）：

```
euler_product {R : ConstructiveReals} (s : nat) (Hs2 : 2 ≤ s) :
  CR_cv R (fun P => euler_E_cv (primes_leq P) s …) (1 + zeta_series_cv s)
  (* ζ(s) = Σ_{n≥1} n^{−s} = ∏_{p ≤ P} (1 − p^{−s})^{−1}，P→∞，s ≥ 2 *)
```

**证明链（149 → 173 定理）**：L1b 几何级数（38）→ L2 素数幂（44）→ Part1 ζ 收敛（68）→
L3 有限欧拉积（91）→ L4 E→∞（100）→ 正向主引理（116）→ 反向分解四砖块（120）→
smooth_in（121）→ smooth_cover 砖块（123）→ 反向主引理第一形态（132）→ 尾部界（137）
→ **双极限收尾（137→149，+12）**：`zeta_partial_le_euler_prod`（部分和 ≤ 欧拉积）、
`pow2_unbounded`（2 幂无界辅助）、`CRsum_subseq_pow2_cv`/`CRsum_subseq_pow2_minus2_cv`
（构造性子序列收敛）、`zeta_le_euler_prod_P`（ζ ≤ ∏）、`euler_prod_leq_zeta`（∏ ≤ ζ）、
`euler_prod_err_le`（|F(P)−(1+ζ)| ≤ 1/P 误差界）、`euler_product`（主定理）
→ **延伸（149→173，+24）**：**ζ 单调性**（`zeta_mono_le`，s1≤s2 ⟹ ζ(s2)≤ζ(s1)，
`inv_n_pow_mono_le`/`zeta_sum_mono_le` 逐项链）→ **ζ 数值界**（`zeta_2_le_2`，ζ(2) ≤ 2，
`zeta2_term_le`/`zeta2_sum_le`/`zeta2_sum_telescope` telescope 链）→ **③ ζ(1) 发散**
（`zeta_1_diverges`：对任意 B 存在 N 使 Σ_{n=0}^{N} 1/(S n) > B——调和部分和无界，
CR_archimedean + `harm_pow2_ge`（经典分组归纳 Σ_{k=1}^{2^m} 1/k ≥ (2+m)/2）+
`CRsum_harm_partial`（CRsum↔CRsum_list iota 桥）+ `pow2p` 系（positive 递归 2 幂，
绕开 mathcomp nat Fixpoint 实现难点）17 引理）。

**性质**：数学对象在 Set 层（CRcarrier）；极限/收敛在 Prop 层（CR_cv）；n^{−s} 用
CRpow (CR_of_Q (1/n)) s（整数幂，无超越函数）；唯一分解用 mathcomp prime/div（可计算）；
**零经典实数公理**（构造性 Cauchy 实数，非 Dedekind）。

**对论文的主张影响**：无（正文不依赖）；可选使用——若投稿希望展示级数侧构造性证明能力，
可将其作为独立贡献/附录引用（173 定理口径）。
