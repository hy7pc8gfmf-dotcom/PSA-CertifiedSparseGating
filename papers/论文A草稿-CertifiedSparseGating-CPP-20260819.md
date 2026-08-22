# 论文 A 草稿（CPP/ITP 方向）— 2026-08-22 清洗版

> **版本状态（2026-08-22）**：
> - **认证管线基态**：`frame_check_instance_sound` 主定理 Qed（会话 10+11）、**M1.5 经典清零**
>   （审计 **165 项 RC=0、零 Admitted、全零经典排中**）、M4b 长度一致性 + T8 复合证书 +
>   **端到端复合证书 `champion_e5_composite_certificate`（Qed）**、酉不变性机器检查（A2）、
>   4D 组装（A1）、2D-wide 免 H_dom、FrameCheck2DNarrow（§5.5）、FFI 24/24（详见正文 §5）。
> - **可证明性边界新定理族（§5.6，2026-08-22）**：P2/P3/N511（`src/ParetoLaw.v`）、
>   P1/P1′（`src/P1Coherence.v`）、T2a/T2b（`src/ParetoRandom.v`，T2b 2026-08-22 完成）、
>   CRT/素数链（`src/CRTResolve.v`）、z 区碰撞/分辨率族（**16 探针全 Qed**，含 U5 黄金近碰撞
>   1/(3d)、ALiBi 无碰撞、Parseval 等式、Dirichlet 界、容错 Gershgorin、一般维张量、τ 三分、
>   核漂移、素数阶梯极限、鸽笼确定性版、ρ^{−3/2} 逐对紧界）；合并版 23/24（31/32 模块）
>   独立编译 EXIT=0 + coqchk 复核通过；**零 Admitted/零自定义公理**。
> - 措辞与引用：按《交接文档》措辞表清洗；参考文献按《参考文献真实性核查报告》校准。
> - 版本历史（v4–v9 对齐记录）见文末附录 B。


---

## Title
**Certified Sparse Gating and Attention Approximation: An Executable Coq Development**

## Authors
王宝军、夏挽岚、祖光照、周志农、高雪峰（单位与通讯邮箱待补）

## Abstract (EN)
We present a Coq formalization of a complete pipeline for certifiably-gated sparse attention
over a geometrically-structured frequency basis. Our development proves, in two orthogonal
end-to-end tracks — representation stability ((i)–(iii)) and attention perturbation ((iv)–(v)),
with no single dependency chain joining them:
(i) a deterministic greedy gate that extracts, from any sorted index set, a subset passing a
decidable sparsity-growth check; (ii) pairwise coherence decay ≤ 1/(√C)^|i−j| and Gershgorin-type
frame bounds (1±μ)‖c‖² for the selected sub-basis; (iii) row truncation energy budgets;
(iv) softmax ℓ₁ stability under ℓ∞ logit perturbation; and (v) a certified attention
approximation theorem: if the dropped spectral energy per row is ≤ ε, the attention output
deviates by at most (e^{2√ε}−1)·V_max. All gate and checker functions are extracted to
executable OCaml/Python and cross-checked against Coq-computed reference values. For the
concrete geometric ladder [3,13,53,213] (C=4), we prove an instance certificate
(`certified_c4_frame_bounds`): frame bounds [1/5, 9/5] with μ = 4/5, where every constant is
a rational number obtained by one-sided domination of the transcendental bounds (floor-sqrt,
Jordan inequality, Dirichlet kernel) — the certificate layer is decidable rational arithmetic,
extractable as-is. This instance-certificate pattern is generalized to *any* ladder by a
reflective checker `frame_check_instance` (decidable pass/fail for μ ≤ 4/5, extracted to
OCaml with a native-int mirror); its soundness theorem `frame_check_instance_sound` is proved:
checker pass ⟹ Gershgorin frame bounds, so the runtime checker carries a machine-checked
soundness guarantee. For the structured-ladder champion [3,7,15,31,63,127,255] — the strong geometric baseline of Paper B — a representation-level composite bound (certified core frame [3,15,63,255] with μ = 4/5 +
edge energy budget + coherence cross-term bound) is the development's
showcase theorem `champion_e5_composite_certificate` (Qed): a machine-checked
**basis-representation stability bound** (S − coh_e5) ≤ ‖F‖² ≤ (S + coh_e5) for the
7-band ladder's basis functions — **not** attention scores, learned projections, or
extrapolation PPL; the bridge to Paper B's empirical PPL gain is an empirical
observation, not a formal consequence, and this certificate is **orthogonal to** the
empirical champion (psi-rope-rand, whose random ladder lies outside this certificate's
scope). The audit comprises 165 Print
Assumptions entries (PSA_audit.v, RC=0,
zero Admitted), **all 165 have zero `Classical_Prop.classic` at the application layer**
(the excluded-middle
macro): the exp-monotonicity route is fully closed (`Module ExpSeries` in
PSA_framework.v, Qed — `exp_mono_le` takes the power-series definition of exp, no
MVT), so `Classical_Prop.classic` appears **zero** times across the whole audit; the
only axioms are the standard Dedekind-real infrastructure (sig_not_dec,
sig_forall_dec, functional extensionality) — non-constructive choice-like principles
inherent to the real-number construction, **not introduced by our application layer**
(R10 3.1: "application layer" qualifier is precise; full constructivity is not claimed).
The "end-to-end" claim is **scoped**: the certified chain covers gating → frame bounds →
truncation energy → softmax stability → attention approximation; it does not cover
the numerical stability of learned weights, Q/K/V projections, multi-head
concatenation, or LayerNorm, and the learned Q/K projections are **not** certified to
commute with the positional rotation (see §1 and §10 "What is not certified").
Companion paper B provides the empirical
validation of the same ladder family; this work supplies the formal guarantees.
Beyond the certification pipeline, we prove a *provability-boundary* theorem family
(§5.6): dense coverage and μ ≤ 4/5 checker certification are mutually exclusive —
for the checker's conservative bound, more than 9 phase-complete bands in [3,511]
must be rejected (`pareto_law_N511`, pigeonhole + geometric-growth argument, c ≈ 1.8501),
and the randomized version holds with high probability (≥ 96% for 7 bands, birthday-box
counting). We also formalize the collision-distance framework underlying Paper B's
τ mechanism: exact collisions occur iff the angle is rational (constructive iff),
the minimum collision distance equals the denominator, irrational offsets never
collide, and the linear-bias kernel (ALiBi) is collision-free — a certified mirror
for the uncertified empirical leader.

---

## 1. Introduction
- 背景：稀疏/近似注意力方法（top-k、KV 逐出、低秩投影）全部无误差证书；
  形式化方法可在"解析核"层提供保证（"verify the analytic kernel, learn the rest"）。
- 贡献清单（与代码一一对应）：
  1. **确定性门控的形式化**（GreedyGate，28 引理）：原文概率门控前提不可满足
     （(INR N)²p²<1 恒假，反例已录），我们裁决并证明确定性平方门 M=C² 是唯一可行路线；
  2. **有限化守卫衰减界**（PSA_Pipeline）：全局增长前提 → 运行时可判定检查，
     系数 2/√C 与 tight 1/√C 两版；
  3. **行截断能量预算**（RowTruncation）与 **softmax 稳定性**（SoftmaxStability，
     ‖softmax z − softmax z'‖₁ ≤ 2(e^d −1)）；
  4. **认证注意力近似**（CertifiedAttention）：谱能量 ≤ ε ⟹ 输出偏差 ≤ (e^{2√ε}−1)·V_max；
  5. **实例证书**（Gershgorin + InstanceCertificate，**已完成**）：对实际 C=4 阶梯
     [3,13,53,213] 证明框架界 [1/5, 9/5]（μ=4/5）——参数化最坏情形 1±4K(C) 在 C=4
     空洞成立、需 C>25 的问题就此终结；
  6. **有理支配方法论**（实现贡献）：证书全部常数经 floor-sqrt / Jordan / Dirichlet
     的单侧松弛化为有理数，`compute; field` 封口——零数值策略、零区间算术、
     可判定、可提取（见 §5.2"可判定性溢价"）；
  7. **可执行提取**：门控/检查器 → OCaml（psa_guard.exe）→ Python FFI，
     **24/24** 参考值对齐（PSA_refcheck.v 的 Coq 计算 + 整数行和验算）；
  8. **反射检查器及其健全性**（FrameCheckInstance，已完成）：`frame_check_instance`
     把"任意阶梯 → μ≤4/5"做成可判定有理判定（floor-sqrt 有理化 + nat 分数行和），
     提取为原生 int 镜像（与 Coq 定义逐行同构）；`frame_check_instance_sound`
     （Qed）证明判定通过 ⟹ Gershgorin 框架界——**检查器本身带机器证明的健全性**，
     实例证书推广为通用运行时判定；
  9. **基表示稳定性复合证书（核心展示定理，✅ 已完成，会话 14 Qed）**：
     `champion_e5_composite_certificate`——论文 B 的七带基线阶梯（E5'' [3,7,15,31,63,127,255]）
     获得机器证明的
     平方范数复合界 `(S−coh_e5) ≤ ‖F‖²_{255} ≤ (S+coh_e5)`（全矩阵相干加权，对称
     交叉项界；`Module ChampionCertificate` L4582–5150，定理本体 L5075，零 classic）。当反射检查器
     对阶梯返回 false（健全但非完备），核-边缘分解交付的**部分证书**在此收束为
     七带整体的完整证书——这是对反射器不完备性的系统性工程补丁，作为方法论
     贡献单列（构件 `pair_3_7` 等 15 对界 + `coh_delta_bound` + `term_bound_*`）；
     **评审 10 限定（2.2/4.4）**：该复合界是**基函数范数稳定性保证**——21 对
     δ_e5 上界均为**手工挑选的保守有理数**（floor-sqrt/Jordan/Dirichlet 单侧松弛），
     紧度无最优性保证（非优化算法自动生成）；它不涉及注意力分数/softmax/PPL，
     与论文 B 外推 PPL 改善之间的桥梁是**经验观察，未经形式化**；
  10. **高维组合性演示（2D-wide/3D/4D）**：`tensor_product_unconditional_basis_2d_wide`
     （会话 15 交付，**免 H_dom**）、`tensor_product_unconditional_basis_3d`（已 Qed）
     与 4D 扩展的价值不在数值紧度（M_bound 巨大、如实报告），而在**骨架复用与
     维度推广可行性证明**——同一 `abstract_unconditional_basis` 骨架经逐轴组装
     实例化为任意维，形式化方法学在高维逻辑闭合（"Theoretically Composable,
     Practically Non-Tight"，§10）。宽轨家族 2D/3D/4D 成员齐备，其中 2D 是
     **唯一免 H_dom 的成员**（idx1≠idx2 经 div/mod 解码唯一性自动给出轴差，
     **评审 10 限定（3.2/4.1）**：2D 免 H_dom 源于**低维几何事实**（idx1≠idx2 ⟹
     i1≠i2 ∨ j1≠j2），非算法突破，不代表高维可推广；且 2D-wide 的 `H_index_bound`
     对**全部** idx 对要求曼哈顿距离 ≤6，是比 3D"仅对任意对"更强的距离界——以
     更严格界换取免支配，权衡如实；"唯一免支配成员"不暗示其比 3D/4D 更正确。
     见 §5.4）——"全覆盖陈述无需跨轴支配"的维数下界实证。
  11. **覆盖边界（评审对齐）**："端到端"精确指覆盖链
      门控 → 框架界 → 截断能量 → softmax 稳定性 → 注意力近似；**不在覆盖内**：
      学习到的权重（W_Q/W_K/W_V/W_O）、Q/K/V 投影与多头拼接、LayerNorm/激活函数
      的数值稳定性、残差连接的累积误差——这些是深度学习实现层，非解析核层
      （"verify the analytic kernel, learn the rest" 的边界即此）。
      **双轨澄清（评审 7 元 I）**：覆盖链在代码中是**两条独立 Qed 的定理簇**——
      (a) 表示稳定性轨（GreedyGate → PSA_Pipeline → Gershgorin → InstanceCertificate
      → T8CoreCertificate → ChampionCertificate：基的框架界/衰减界）；(b) 注意力扰动轨
      （RowTruncation → SoftmaxStability → CertifiedAttention：能量界 ⟹ 输出扰动界）。
      两轨**无依赖桥接**（复合证书不调用注意力定理）——"端到端"指两轨各自完整、
      覆盖解析核的两个正交面，非单一依赖链；基证书不构成模型/外推性能证书。
      **评审 10 强化（3.4）**：外推 PPL 改善（如论文 B 的 13.84→12.40）在本形式化
      框架中是**未证明的经验现象**；形式化锁定的是基表示稳定性，与 PPL 之间
      无形式化桥梁——证书与经验观察的关系在全文按此口径表述（"What is not
      certified"，§10）。

## 2. Background 与原文修正
- ψ 基：psi n k = (1/√n)·e^{2πik/n}，有限支撑（k ≥ n 时为 0）；
- 阶梯生成器 next = max(C·last+1, last+2)（非精确几何——证书必须认证实际值，
  这是需要运行时检查器而非纸面公式的理由）；
- **三处语义勘误**（线性 vs 平方门、`<=?` vs `<?`、≥2 并集）——每处附反例，
  体现形式化对原草案的纠错价值；
- **一处常数级勘误（3D 张量基，已修正）**：2D 引擎的离对角界常数 K0 = Rmax 8C³/4
  在 3D 等轴退化配置（两轴索引相同、仅第三轴差 ≤6）下不可证——归一化三重内积可逼近 1，
  而 /4 常数只给 1/2（`(C³/4)·(2/C³)`）。3D 模块改为 K0′ = Rmax 8C³/2（退化配置恰好紧，
  worst case = 1；`ca_basis_3d.v` `one_le_half_K0_dprod`，已 Qed）——这是与前三类
  （语义/算子）不同的**定量界级**纠错（详见 §5.4）。

## 3. 开发总览
模块图（PSA_framework.v，**6405 行，19 个 Module，250 Qed，零 Admitted**，会话 17 终态）：
RuntimeGuards → SeqProps → PSA_Pipeline → GreedyGate → RowTruncation →
PipelineEndToEnd → **ExpSeries（M1.5 级数重写，§7）** → SoftmaxStability →
CertifiedAttention → Gershgorin → InstanceCertificate（M4）→
**M4bLengthConsistency（长度一致性，∀N≥214）→ T8CoreCertificate（T8 复合证书核）→
FrameCheckInstance（反射检查器 + soundness）→ ChampionCertificate（端到端复合证书，§5.3）
→ FrameCheck2DNarrow（2D 窄轨反射化，§5.5）→ UnitaryInvariance（A2 酉不变性，§5.3）**。
统计：**165 项** Print Assumptions 审计（PSA_audit.v，RC=0，证据 `audit_run.txt`）；
**全部 165 项零经典排中**（`Classical_Prop.classic` 出现 0 次——M1.5 已清零，
exp 幂级数路线已并入，见 §7）；**零 Admitted**（剥注释后 grep 命中 0）；零自定义公理；
外部依赖仅 mathcomp + Coquelicot；Rocq 9.0.1。

## 4. 核心定理（Coq 语句摘录）
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
  (1 − 4/5)·S ≤ ‖Σ c_i·ψ_{[3,13,53,213],i}‖² ≤ (1 + 4/5)·S   (* 实例证书，M4 *)

certified_c4_frame_bounds_anyN (N) (coeffs) : N ≥ 214 → length coeffs = 4 →
  (1 − 4/5)·S ≤ ‖Σ c_i·ψ_{[3,13,53,213],i}‖² ≤ (1 + 4/5)·S   (* 长度一致性，M4b *)

certified_t8_core_frame_bounds (coeffs) : length coeffs = 4 →
  (1 − 4/5)·S ≤ ‖Σ c_i·ψ_{[3,15,63,255],i}‖² ≤ (1 + 4/5)·S   (* T8 复合证书核 *)

frame_check_instance_sound (I) : 0 < length I → frame_check_instance I = true →
  let n := length I in let M := S (last I 0%nat) in
  let phi i k := psi (nth i I 0%nat) k in
  (1 − 4/5)·‖Σ_{i<n} c_i·phi i‖² ≤ ‖Σ_{k<M} (Σ_{i<n} c_i·phi i k)‖² ≤ (1 + 4/5)·‖Σ_{i<n} c_i·phi i‖²
  (* 反射检查器健全性：判定通过 ⟹ 任意阶梯 μ=4/5 框架界，M4 收尾③ *)

tensor_product_unconditional_basis_3d (C) (seq1 seq2 seq3) : C > 2 → 三轴稀疏增长 →
  NoDup/Sorted I1 I2 I3 → length coeffs_flat = n1·n2·n3 → 域条件 H_dom →
  混合进制距离 ≤6 →
  (1 − M_bound)·S ≤ ‖F_3D‖² ≤ (1 + M_bound)·S
  (* 三维张量积无条件基（ca_basis_3d.v，已编译零 classic）：φ3D(a,b,c)(k)=γ⁻¹ψ_aψ_bψ_c，
     M_bound = K0′·((1+4K_C)³−1)，K0′=Rmax 8C³/2，见 §5.4 *)

tensor_product_unconditional_basis_2d_wide (C) (seq1 seq2) : C > 2 → 双轴稀疏增长 →
  NoDup/Sorted I1 I2 → length coeffs_flat = n1·n2 → 混合进制距离 ≤6 → 无 H_dom →
  (1 − M_bound)·S ≤ ‖F_2D‖² ≤ (1 + M_bound)·S
  (* 二维张量积无条件基宽轨版（ca_2d_wide_asm.v，会话 15 交付，零 classic）：
     φ2D(i,j)(k)=γ⁻¹ψ_iψ_k·ψ_jψ_k，K0 = Rmax 8C³/2，M_bound = K0·((1+4K_C)²−1)；
     与 3D 共用 K0=C³/2 但**免 H_dom**——2D 的 idx1≠idx2 ⟹ i1≠i2 ∨ j1≠j2
     （div/mod 解码唯一性），无需跨轴支配条件，`one_le_half_K0_2dprod` 四分支覆盖；
     数值裁决 `M_bound_2d_wide 4 = 768` 已 Qed（= 32 × 24，与论文 B §6 N=2 公式一致） *)

tensor_product_unconditional_basis_4d (C) (seq1..seq4) : C > 2 → 四轴稀疏增长 →
  NoDup/Sorted I1..I4 → length coeffs_flat = n1·n2·n3·n4 → 域条件 H_dom → 混合进制距离 ≤6 →
  (1 − M_bound)·S ≤ ‖F_4D‖² ≤ (1 + M_bound)·S
  (* 四维张量积无条件基（ca_basis_4d.v 单文件版，会话 17 交付 + coqchk 复验，零 classic）：
     K0 = Rmax 8C³/2，M_bound = K0·((1+4K_C)⁴−1)，数值 `M_bound_4d 4 = 19968` 已 Qed，见 §5.4 *)

unitary_invariance_psi_rope_theta (θ) (vals) (coeffs) (n N) :
  Σ_{k<N} |Σ_{i<n} e^{i·(INR k·θ k)}·c_i·ψ_{vals[i]}(k)|² = Σ_{k<N} |Σ_{i<n} c_i·ψ_{vals[i]}(k)|²
  (* 酉不变性 RoPE 显式实例（Module UnitaryInvariance，会话 17）：u k := Cexp (0+i·INR k·θ k)，
     Cexp_unit_mod 证 Cnorm_sq (u k) = 1；与实验 2×2 旋转矩阵同构（SO(2)≅U(1)），见 §5.3 *)
```

## 5. 实例证书（M3/M4，已完成）
### 5.1 定理与证明结构
- 对象：C=4 可见子梯 [3,13,53,213]（N=512 窗口内列范数=1；更长频带在窗口内
  近似线性斜坡、范数→0——全阶梯认证得平凡界，窗口自适应认证是正确设计）。
- 结构（教科书式 11 步）：`psi_unit_norm`（对角 = 1，ψ 有限支撑 ⟹ 支撑外零和）
  → 六个有理对界 `pair_3_13` … `pair_53_213`（如 13/40、11289/33920）
  → 四个行和引理 `c4_row0..3`（各 ≤ 4/5，nra 解有理不等式）
  → `gershgorin_frame_mu` 一次实例化 ⟹ **[1/5, 9/5]**。
- **长度一致性（已并入，会话 9）**：`certified_c4_frame_bounds_anyN`——∀N≥214
  （窗口 N−1≥213），M4bLengthConsistency 模块 5 Qed，零 classic。O(1) 证书
  对一切序列长度成立，覆盖无界 T 的显式定理。
- **从实例到通用判定（会话 9-11）**：同一配方推广为反射检查器 `frame_check_instance`
  （任意阶梯 → μ≤4/5 布尔判定，floor-sqrt 有理化 + nat 分数行和，全程可判定有理算术），
  其健全性主定理 `frame_check_instance_sound` 已 Qed——**实例证书不再逐阶梯手工验算，
  而是由一台自带健全性证明的运行时检查器统一保证**（见 §6）。

### 5.2 有理支配与可判定性溢价（实现贡献）
- 全部超越量被朝可判定方向单侧支配：√m ← ⌊√m⌋（`INR_sqrt_le`）、
  |sin(πΔ)| ← Jordan 2Δ、Dirichlet 分子 |sin(πNΔ)| ← 1、（Tier 2 的 π ← 22/7）。
  **证书层只需要 ℚ**——运行时验证只做有理算术，这是可提取性的根源。
- **可判定性溢价**（新概念）：精确 μ = 0.312 → 有理保守 μ = 4/5，
  因子 2.55——机器可检查性的已量化代价。溢价是设计对象：松弛链可枚举、
  可优化（`cert_optimize` 方向，future work）。
- 相邻对有理界的极限：n₁n₂/(2(n₂−n₁)⌊√(n₁n₂)⌋) → √C/(2(C−1))（C=4 时 1/3）。
- **检查器的保守性（充分非必要）**：`frame_check_instance = true` 是框架界的
  **充分非必要条件**——floor-sqrt 有理松弛的保守因子约 1.5×，存在满足
  Gershgorin 条件但因保守上界超 4/5 而被误拒的合法阶梯（假阴性）。典型案例：
  论文 B 的七带基线阶梯 E5'' [3,7,15,31,63,127,255] 被检查器判 false，**不代表它不满足框架条件**，仅代表
  有理松弛不足以证明它。正是这一不完备性使**复合证书成为必要**（而非补丁式
  workaround）：检查器拒绝整体 ⟹ 核-边缘分解 ⟹ 认证核 + 能量预算
  （§5.3 端到端复合证书，✅ 已完成）。宁可误拒、绝不放行的保守取向是可判定性的
  设计选择，须与"部分证书"机制配套使用。
  **评审 10 定位修正（2.4）**：系统扫描（114 阶梯×5 族，`frame_check_scan.py`，
  会话 18）实测假阴性 **56/114（49.1%，占拒绝 70.9%）**，且**集中于"有用"阶梯**
  （C=2/3-sparse 12/13、几何奇带 9/9 全拒），C=6/8-sparse 全通过——"可判定性溢价"
  是**当前有理松弛实现的保守性代价（局限）**，不是"溢价可接受"的价值判断；
  收紧方向：`cert_optimize`（松弛链贪心收紧）、Zarith 大整数（消除行和累积分母
  溢出范围，评审 9）。

### 5.2b 可判定性溢价与松弛链（独立方法论贡献）
- **问题**：任何超越函数（√、sin、π）都使"机器可检查的证书"失去可判定性——
  运行时验证若需实数算术，要么依赖浮点（不保真）、要么依赖区间算术（复杂且
  保守）。本开发的方法是**系统性地把证书推到纯有理层**。
- **方法论声明（比具体 μ 值更普适）**：可判定性溢价（decidability premium）——
  精确界 → 有理保守界的**已量化代价**。C=4 实例：精确 μ = 0.312 → 有理保守
  μ = 4/5，因子 **2.55**。该因子不是"精度损失"而是一个**设计对象**：松弛链
  的每一环（floor-sqrt / Jordan / Dirichlet / π←22/7）都可枚举、可单独收紧、
  可机械组合——`cert_optimize` 方向（future work）即对松弛链做贪心收紧，
  在保持可判定性的前提下最小化溢价。
  **具体化（评审 5 方向 2）**：检查器可升级为返回三态 `CertLevel = Tight | Loose |
  Fail`——对 `Loose` 阶梯自动运行 `cert_optimize`（高精度有理近似如 π←355/113、
  逐项收紧松弛链）重算行和；若提升为 `Tight`，七带即可直接走 `gershgorin_frame_mu`
  实例，简化/替代核-边带复合证书（future work，OCaml+Coq 工作量）。
- **普适性论证**：溢价机制与具体阶梯无关——任何"超越界 → 有理界"的证书化
  都面对同一权衡（可判定性 ↔ 紧度）。本开发的贡献是给出了**端到端实例**：
  从 11 步教科书证明到反射检查器，全部常数落在 ℚ；检查器执行**可判定整数算术**
  （判定层零实数），所证的证书界为**有理常数**（定理层）——两层分开表述；
  并将"宁可误拒、绝不放行"（充分非必要）明确为设计选择，配套"部分证书"
  机制（§5.3）弥补误拒。
   **反向警示（形式化审查 §II.B 强化，定稿必读）**：检查器返回 `false` **不是**
   不安全证书——它只表明保守有理界不足以证明 Gershgorin 条件；被误拒的合法
   阶梯仍可由复合证书覆盖（§5.3 七带即此情形：其精确相干行和仅 0.135 ≤ 4/5，
   实质可认证，误拒源于与窗口无关的保守对界）。"检查器通过 ⟹ 框架界"成立，
   "检查器失败 ⟹ 不安全"不成立。
- **相邻对有理界极限**：n₁n₂/(2(n₂−n₁)⌊√(n₁n₂)⌋) → √C/(2(C−1))
  （C=4 时 1/3）——松弛链的渐近代价有闭合形式，支持跨 C 的溢价预测。

### 5.3 与实验的对齐（multi-seed 已裁决 + T8 已并入）
3-seed 实验中，E5'' 七带 [3,7,15,31,63,127,255] 与 C=4 并列最优
（8× 均值 12.40±0.74 vs 12.75±0.34，差距 -2.8% 在噪声带内）；C=2 第三
（13.84），C=3 系统性最差（22.86，归因为间距非噪声）。最优表现对论文 A 免疫：
- **直接证书**（C=4 胜）：certified_c4_frame_bounds 直接覆盖；
- **T8 复合证书**（E5'' 胜，**已并入，会话 9**）：其隔带子核 [3,15,63,255]
  T8CoreCertificate 模块 11 Qed 零 classic，μ=4/5 覆盖最优阶梯的认证核。
两种排位论文均有主定理覆盖。
- **端到端复合证书（✅ 已完成，会话 14 Qed）**：顶层组合定理
  `champion_e5_composite_certificate`（`PSA_framework.v` `Module ChampionCertificate`，
  L4582–5150，定理本体 L5075）已 Qed 零 classic。**代码实际证明的目标形状**（全矩阵相干加权）：
  ```
  length coeffs = 7 → (S − coh_e5 c) ≤ ‖F‖²_{255} ≤ (S + coh_e5 c)
  ```
  其中 F = Σ_{i<7} c_i·ψ_{e5_bands[i]}，S = Σ Cnorm_sq(c_i)，coh_e5 为 21 对上三角
  δ 表经 `term_bound_upper`/`term_bound_lower` 加权得到的**对称相干交叉项界**——
  非论文早期草拟的 `(1+4/5)·S_core + S_edge + 2·coh_ce` 分段形式（该"核带框架 +
  边带能量"表述是装配前的设计稿，最终实现收敛为单一定理下的对称界）。
  构件链：15 个新 pair 界（`pair_3_7` 等，`compute; field` 常数核验）→
  `inner_diag_one`/`re_le_cnorm`/`neg_re_le_cnorm`/`cnorm_ge0` → `e5_bands`/
  `delta_e5`（21 对上三角 δ 表）/`coh_e5` → `band_ge2`/`band_le256`/
  `coh_delta_bound`（42 方向）→ `term_bound_upper`/`term_bound_lower` →
  **`champion_e5_composite_certificate`**（`(S−coh) ≤ l2_norm_sq F 255 ≤ (S+coh)`）。
  实施文档：`E5''端到端复合证书-缺口分析与实施文档-20260820.md`。
- **反射检查器不完备性：影响与缓解（评审 A3，会话 18 系统扫描补强）**：`frame_check_instance` 是**充分非
  必要**——实际可认证阶梯被判 false（假阴性）。**系统扫描统计（114 阶梯 × 5 族：
  C-sparse C∈{2..8}×m∈{2..14}、几何奇带、C=2 全相位、E1 随机 log-uniform 去重；
  ground truth = 窗口 T=末带的精确相干行和，`frame_check_scan.py`）**：通过 35
  （30.7%）、拒绝 79（真负 23、**假阴性 56 = 全量 49.1%**，占拒绝 70.9%）——4 样本
  的"50%"推广为全量 ~49%。假阴性集中于"有用"族：C=2/3-sparse 12/13、几何奇带
  （E5'' 式）9/9、C=4-sparse 10/13、C=5-sparse 9/13；C=6/8-sparse 13/13 全通过、
  E1 随机族 3/18（该族多为真负：稠密阶梯精确行和确 > 4/5）。代表性复核：C4 与
  T8 核 true、E5'' 七带与 C=2 八带 false。
  **细化发现**：E5'' 七带在窗口 255 的**精确**相干行和仅 0.135 ≤ 4/5——其实质
  **可认证**；检查器拒绝来自与窗口无关的保守对界（√(n₁n₂)/(2(n₂−n₁)) 远大于
  精确相干 |sin(Tθ/2)/(T·sin(θ/2))|）。故复合证书不是"挽救不可认证阶梯"，而是
  对**保守预筛器误拒阶梯**给出的紧证书（其 `coh_e5` 即 21 对 δ 表的精确相干界）。
  **缓解（已实现）**：(a) **部分证书组合**——被拒阶梯的核-边带分解（T8 核通过
  检查 + 边带能量预算 + 相干交叉项）给出整体框架界证书
  （`champion_e5_composite_certificate`），即"检查器拒绝整体 ⟹ 分解为可证子件"；
  (b) 保守界逐步收紧（`cert_optimize`，future work）。
- **覆盖实验旋转组的酉不变性声明（✅ 已完成机器检查，2026-08-20 会话 17）**：论文 B 的
  "旋转组"使用 psi-rope——基函数乘旋转矩阵后注入注意力。形式化 `PSA_Pipeline` 的
  decay_bound 证明的是**基函数内积**衰减，而非旋转后注意力分数的衰减。二者由
  酉不变性桥接：旋转是酉变换，对任意酉算子 U 与系数向量 c，
  ‖Σ c_i·Uψ_i‖² = ‖U(Σ c_i ψ_i)‖² = ‖Σ c_i ψ_i‖²（酉变换保持范数与内积），
  框架界/衰减界/证书由此覆盖旋转版本；该桥接同样传递到
  `certified_attention_approx`（logit 扰动界由谱能量给出）与 ε（内积决定，酉
  映射下精确不变——"旋转对 ε 的影响"无需量化，恒为零）。
  **形式化收尾（已完成）**：探针 `src\_probe_unitary.v` RC=0 后 Module
  `UnitaryInvariance` 并入 `PSA_framework.v` 帧尾（零 classic）。核心
  `unitary_invariance_point`（U 保内积 ⟹ ‖Σ U(g_i)‖² = ‖Σ g_i‖²）即
  `unitary_invariance_frame` 的正确定型；psi-rope 实例以**位置索引旋转**给出
  （`unitary_invariance_psi_rope` / `_global`：每位置乘单位模 u_k，RoPE 语义，
  无需正交性即保 l2 范数）。声明由 v6 的"数学事实（未机器检查）"升级为
  "机器检查引理"。
  **评审 §1 修复（显式 RoPE 实例，2026-08-20 会话 17）**：新增
  `Cexp_unit_mod`（`Cnorm_sq (Cexp (0+iθ)) = 1`，由 `sin2_cos2`）与
  `unitary_invariance_psi_rope_theta`——取 `u k := Cexp (0 +i (INR k·θ k))`
  （逐位置旋转角 θ k）即为 psi-rope 的**显式实例化**：实验的 2×2 块旋转矩阵
  （`length_extrap.py` `apply_rope_theta`：`[x1·c−x2·s, x1·s+x2·c]`）与复数乘法
  `e^{iθ}` 是同一酉群的同构表示（SO(2)≅U(1)，实/虚部逐行对应），故形式化
  `u_k·x` 精确覆盖实验旋转，形式化-实验桥接闭环。
  **实/虚部逐项展开（评审 3.2-5 对齐）**：`u·S = (cos θ + i·sin θ)·(x₁ + i·x₂)
  = (x₁·cos θ − x₂·sin θ) + i·(x₁·sin θ + x₂·cos θ)`，与 `apply_rope_theta` 的
  `[x₁c−x₂s, x₁s+x₂c]` 逐项一致（构造性可验证；该块分解已**显式机器检查**——
  `rope_matrix_real` / `rope_matrix_imag` / `rope_matrix_eq` 于 UnitaryInvariance
  模块 Qed：`re(e^{iθ}·(x₁+ix₂)) = x₁cosθ−x₂sinθ`、`im = x₁sinθ+x₂cosθ`，ring 级，
  零 classic——评审 3.2-5 的"隐式成立"已升级为显式引理）。
  **注（假命题排除）**：原"每带乘 u_i"逐点版本为假命题（交叉项需 u_i=u_j；
  反例 u0=1,u1=-1,g0=g1=1：|1-1|²=0≠4=|1+1|²），未并入；带索引 l2 等式需基
  精确正交，由 (1±4/5) 帧界路线覆盖。
  **范围限定（评审 7 最终-3 脚注）**：酉不变性证明适用于**特征表示的范数层**
  （基展开的平方范数/内积）；它**不**保证学习到的 Q/K 投影下注意力 logits
  （softmax(Q·Kᵀ)）在该旋转下不变，亦非旋转后注意力机制的证书（除非重训投影
  矩阵）——桥接限于"基函数的能量范数"层面，学习层与 softmax 动态不在其内。
- **相干熵桥接（评审 5 增值方向 1，核心桥梁定理已 Qed，会话 18）**：外推崩坏的主因候选为
  带间相位混叠导致 Softmax 分母数值不稳定（非谱能量通道）。**`PhaseCoherence` 模块
  （新，`coherence_controls_attention`，Qed，零 classic）**：对任意相干核
  K（|K_ij| ≤ coh）与系数差 ℓ₁ ≤ delta，logit 扰动 |z_i−z'_i| ≤ coh·delta
  （z_i = Σ_j c_j·K_ij），组合 `softmax_l1_bound_exp` 得
  **‖softmax z − softmax z'‖₁ ≤ e^{2·coh·delta} − 1**——相干上界 ⟹ softmax 输出
  TVD 界的**抽象桥梁**（三步：三角不等式 logit 界 → softmax 稳定引理 → 零 classic）。
  该定理是**参数化于相干核的抽象结果**，可直接实例化 ψ 基（`psi_inner_cons_bound` /
  `psi_inner_dirichlet` 给出 |⟨ψ_i,ψ_j⟩| 上界）；到"PPL 增益解释"的完整实例化
  （具体阶梯 + 学习投影层）为后续工作。当前为**已证抽象桥梁 + 未实例化**状态；
  ψ 对相干界已有构件（`psi_inner_cons_bound` / `psi_inner_dirichlet`）。
  **实证支撑与修正（会话 17 初测 → 会话 18 E1 扩充）**：初始四梯（稀疏几何）实测
  `Coh(512)`/`Coh(4096)`：Coh 本身与 ppl(4096) 无相关（R²≈0.07），但**相干衰减量
  ΔCoh = Coh(512)−Coh(4096) 与 ppl(4096) 强正相关（4 点 R²=0.982）**：C=3 ΔCoh=0.076→
  ppl 22.86（最差）、E5'' 七带 ΔCoh=0.025→12.40（最好）；**E1 消融扩充（13 点）后
  max 型 R² 崩塌至 0.101**（median 0.597、λ_max 0.461 亦非定律）——随机阶梯取整产生
  重复带（相同带对相干恒为 1 → Coh(T_train)=
  Coh(T_ood)=1、ΔCoh≡0），稠密阶梯饱和，且 psi-rope-rand（去重 ΔCoh=0.012）与
  psi-rope+rand（去重 ΔCoh=0.135）的 ppl 分别为最优 7.29 与次优 9.82——正相关
  **跨族不成立**：ΔCoh 仅是**稀疏无重复几何阶梯族内**的排序指标，非通用预测因子
  （数据 `psa_empirical\测试数据\coherence_scatter.csv`；论文 B §10.6 全表）。
  **同期 E1 新发现（3-seed 确认 + 全部消融，会话 18）**：随机稠密旋转角（psi-rope-rand，
  [3,511] 128 角，b32 三 seed）@4096=6.45±0.03，优于几何 C=4（12.75）、E5''（12.40）
  与 rope-NTK（3-seed 11.54±1.18）——旋转族 OOD 表现由**相位完备/稠密覆盖**主导而非几何序
  （三个独立随机阶梯同点收敛）；嵌入族全部消融：psi-lin 39.62±4.07 最差（线性铺频带
  破坏相位完备性）、psi-rand 31.04±12.86 高方差（s42 16.21 / s7 37.83 / s1337 39.07）、dense-frozen
  分布内 6.08±0.20 显著差于 psi 系 4.5-5.0（**频率结构对分布内质量有独立贡献**，瓶颈
  机制不充分）。预登记假说"psi-rope-rand 显著差于 psi-rope"被**反向证伪**并多 seed
  坐实（如实，会话 18；论文 B §8 裁决逆转）。
- **主张卫生（覆盖梯度的归因边界，定量如实）**：对论文 B 的"覆盖梯度"经验律
  （剪掉覆盖恰 1.0 的末带在全部 OOD 长度/seed 上严格改善，13.84→12.40），
  本开发**不主张直接或定量解释**该经验律，且须主动披露一个定量事实：
  `certified_attention_approx` 的输出界对 ε 单调，而该剪枝的 ε 几乎不变
  （511 带窗内范数→0，长带死重实测 1.4111 vs 1.4120）——**ε 通道对这一剪枝
  不敏感**，而 ppl 跃迁远超噪声。结论：增益机制不在当前形式化的谱能量通道内
  （候选：绝对相位混叠、softmax 分母数值稳定性——均被现框架抽象掉，列为
  future work 的形式化目标）；形式化的贡献限于**稳定性检验**（剪枝不破坏
  框架界，μ 不变——排除崩溃风险）与定性线索（长带非对角相干衰减）。
  "理论显微镜"的分辨率是 ε 级，不足以观察 ppl 级变化。
- **联合主张边界（元定理，两篇论文实际共同证明的部分）**：对通过检查器的阶梯
  （如 C=4）：机器可检查的框架界 μ≤4/5，任意系数下表示稳定性；对未通过检查器
  的性能最优七带：隔带子核 μ≤4/5 + 边带能量有界（T8CoreCertificate 11 Qed +
  `row_dropped_energy_bound`）。**从"能量控制"到"外推 ppl 提升"的桥梁未经
  形式化**，依赖论文 B 的经验观察——两文联合可证部分止于此。相应地，一个
  如实呈现的张力：认证阶梯（C=4，8× 均值 12.75）与未认证性能最优方案（12.40）呈
  **温和负相关**——表达性与可证明性此消彼长，复合证书覆盖性能最优方案的可证骨架
  而非其外推增益（见论文 B §7）。

### 5.4 维度推广：三维张量积无条件基（已编译，零 classic）
- **定位声明（评审对齐）**：3D/4D 张量积证书的价值在于**组合性演示**——同一
  `abstract_unconditional_basis` 骨架可被逐轴实例化到任意维。其常数的非紧性
  与未提取状态是两条**独立限制**——前者是数学事实（如实报告 M_bound 巨大），
  后者是工程选择（未接入 PSA 提取链）。二者共同构成"存在性结果"而非"实用工具"
  的定位。
  **下界空洞（评审 7 元 II，如实）**：M_bound > 1 时下界 `(1−M_bound)·S` 恒负
  （如 C=4 的 3D：−3967·S ≤ ‖F‖² 对非负范数恒真，**无信息量**）——证书的信息量
  在于**上界** `(1+M_bound)·S`（表示范数的非平凡上界，排除范数爆炸）+ 组合性
  演示（同一骨架逐轴实例化）。故 3D/4D 证书定位为"上界证书 + 组合性演示"，
  其紧度在当前松弛下失效，正确归类为理论演示而非实用证书。
- **对象**：φ3D(a,b,c)(k) = γ⁻¹·ψ_a(k)·ψ_b(k)·ψ_c(k)，γ = √(min(a,b,c)/(abc))；
  三条 C>2 稀疏增长序列的笛卡尔积在**扁平混合进制索引**下构成无条件基，目标框架界
  (1±M_bound)，M_bound = K0′·((1+4K_C)³−1)，K0′ = Rmax 8C³/2——与 1D
  `gershgorin_frame_mu` 同一 `abstract_unconditional_basis` 骨架的 3D 实例（`ca_basis_3d.v`）；
- **状态**：✅ **全量编译 RC=0（会话 12 复核）**；公理审计 **10 项**全部零 classic
  （`nat_triple_decode_inj` 零公理；其余 9 项仅继承 sig_not_dec + sig_forall_dec + fext，
  证据 `PSA_3D_audit.v` / `audit_3d_raw.txt`）；
- **结构**：`gamma3` 归一化（正性/平方）→ 混合进制双射（`nat_div_mod_3d` /
  `nat_mod_n3_of_mod_n23` / `nat_triple_decode_inj`）→ 三重内积纯量分解
  （`phi3D_inner_scalar_decomposition`）→ 截断 Cauchy-Schwarz（`triple_inner_single_bound`：
  归一化三重内积 ≤ 1）→ **修正常数引理**（`one_le_half_K0_dprod`：任意扁平离对角对、
  距离 ≤6 ⟹ 1 ≤ K0′·d1·d2·d3）→ 主引擎 `phi_flat_decay_general_3d` →
  组装 `tensor_product_unconditional_basis_3d`；
- **常数代价（如实报）**：与 2D（K0 = Rmax 8C³/4，但衰减引理要求**两轴索引都不同**）相比，
  3D 只要求扁平索引不同（覆盖等轴退化配置），常数 ×2——**维度提升的假设-常数权衡被
  形式化量化**：各向同性（等轴）阶梯是 3D 相干最坏情形，非等轴设计可望收回 ×2；
  1D/2D 现有证书（μ=4/5 等）不受此修正影响；
- **数值紧度裁决（如实，双因子分解）**：三轴实例 [3,13,53]（C=4，3³=27 基函数）——
  `M_bound_3d 4 = 3968`（引理 `M_bound_3d_C4_value` 已 Qed，`ca_basis_3d.v` 尾部），
  即 **M_bound ≫ 2 ⟹ 3D 证书目前仅作为存在性证明（无条件基 + 显式但巨大的常数），
  非紧，留给未来收紧**。松弛可机械分解为两个正交因子：
  **编码因子 K0′ = C³/2 = 32**（混合进制扁平索引下等轴退化配置的病理覆盖——
  改变扁平化编码（格雷码类方案）或采用非等轴阶梯可望收回此因子）与
  **行和乘积因子 (1+4K_C)³−1 = 124**（逐轴乘积行和分解所致，与编码无关，
  是"维数灾难"的主导项——收紧需联合行和界，跨轴直接求和替代乘积）。
  M_bound 数值上随 C 增长（C=3 ≈3.6×10³ → C=6 ≈5.6×10³），无 C 可使紧；
  该双因子归因是"编码设计空间 × 行和估计设计空间"两个自由度的定量刻画，
  为形式化独有的贡献；
- **常数收紧路线图（评审 A4）**：M_bound = 编码因子 C³/2 × 行和乘积因子
  ((1+4K_C)^N − 1)。(a) 编码因子：等轴退化病理 ∏d = 2/C³ 由"格雷码类"非等轴
  编码可望收回（相邻带距离 ≥2 而非 1）；(b) 行和因子（主导项）：跨轴直接求和
  （非乘积）的行和界可消除指数增长；(c) 小型对比：N=1（μ=4/5，界 [1/5, 9/5]）
  vs N=2-wide（M_bound=768，C=4）——常数随维数指数增长，证书在低维（N≤2）
  实用、高维（N≥3）为存在性结果（如实）；
- **四维扩展（会话 14/17，已完成）**：`ca_basis_4d.v` 以 3D 为模板已交付并全部 Qed：
  4D 混合进制解码族（`nat_quad_decode_inj` 零公理）、`gamma4` 归一化族、
  16 分支常数引理 `one_le_half_K0_4dprod`（K0^{(4)} = Rmax 8C³/2，再次机械确认
  /4 常数的单轴退化不可满足性是**维数无关**病理）、数值引理
  `M_bound_4d 4 = 19968`（N 维公式 N=4 预测值已证）以及**主衰减引擎
  `phi_flat_decay_general_4d`**、组装备料与**组装定理
  `tensor_product_unconditional_basis_4d`**（会话 17 单文件版 `ca_basis_4d.v`
  编译 RC=0 + coqchk 复验 RC=0，已并入 27模块 目录与合并版 28 分区）；
  审计零 classic（`ca_4d_audit.v` / `audit_4d_raw.txt`）；
- **双轨设计（窄轨/宽轨并列声明）**：/2 修正是"宽陈述"的价格而非高维强加给
  低维的税——任何 D≥2 的全覆盖扁平离对角（含单轴退化）陈述都需 /2（退化配置
  ∏d = 2/C³ 与维数无关，2D 同样存在）。故证书族为并列双轨：**窄轨**（1D 实例
  证书 μ=4/5、2D K0=C³/4——收紧前提换常数减半，**实用证书**，不受高维常数
  爆炸与 /2 修正影响）与**宽轨**（2D-wide/3D/4D K0=C³/2——全覆盖换 ×2，**组合性/
  存在性定位**）。仅需 1D/2D 的应用场景应采用窄轨；宽轨家族 2D/3D/4D 成员齐备
  （N=2 成员 2D-wide 已于会话 15 补齐，见下）。
- **2D-wide（会话 15 交付，宽轨家族 N=2 成员补齐，零 classic）**：
  对象 φ2D(i,j)(k) = γ⁻¹·ψ_i(k)·ψ_j(k)，γ = √(min(i,j)/(ij))；目标框架界
  (1±M_bound)，M_bound = K0·((1+4K_C)²−1)，K0 = Rmax 8C³/2。三层拆分模块
  （`ca_2d_wide_const.v` → `ca_2d_wide_engine.v` → `ca_2d_wide_asm.v`，
  独立编译约 31 秒 vs 单文件全量约 15 分钟，见经验卡 E077）：
  - **免 H_dom（与 3D 的关键差异）**：3D 的轴间支配条件在 2D 自动成立——扁平
    idx1≠idx2 ⟹ (i1,j1)≠(i2,j2) ⟹ i1≠i2 ∨ j1≠j2（div/mod 解码唯一性），
    `one_le_half_K0_2dprod` 四分支（双轴差→4、仅轴1差→2、仅轴2差→2、同轴排除）
    即覆盖全部离对角对，**无需任何跨轴支配假设**——宽轨家族中唯一免 H_dom
    的成员，2D 是"全覆盖陈述不需要额外支配条件"的维数下界（3D 起才需要）；
  - **数值紧度（如实报）**：`M_bound_2d_wide 4 = 768`（= 32 × 24：编码因子
    K0 = C³/2 = 32、行和乘积因子 (1+4K_C)²−1 = 24）——与论文 B §6 的 N 维
    公式 M_bound^{(N)} = (C³/2)·((1+4K_C)^N − 1) 在 N=2 的预测完全一致，
    **N=2 校验从"数值计算"升级为"全定理级已证 + 独立证明路线"**；
  - **审计**：5 项 Print Assumptions 全部零 classic（`ca_2d_wide_audit.v`，
    仅继承 sig_not_dec + sig_forall_dec + fext），证据 `audit_run.txt` 追加段；
- **反射化的可组合性（方法论表述）**：3D 模块未接入 PSA 提取链不是待办缺陷，而是
  **架构设计**——反射检查器的健全性证明是**可组合的（Composable）**：
  `tensor_product_unconditional_basis_3d` 与 1D `gershgorin_frame_mu` 共享同一
  `abstract_unconditional_basis` 骨架，3D 张量核的静态定理即为该组合性的一个实例骨架；
  其反射化是提取链的**直和扩展（direct sum extension）**，而非基础理论修正
  （与 PSA 窗口语义的对照——3D 截断 M = S(max) vs 1D 窗口自适应 N−1≥n——留作
  接入时的对齐项）。

## 5.5 退化 2D（单轴）反射检查器（FrameCheck2DNarrow 模块，2026-08-20 并入）
> **评审 10 更名注（4.3）**："2D 窄轨"实为**退化单轴**情形（仅 n₁=1 ∨ n₂=1 的
> 1D 参数化 2D），非 2D 通用格点检查器；评审建议更名 `Degenerate2DFrameCheck` /
> `1DParametric2DFrameCheck`。本文保留原模块名（避免跨文档引用失效），但全文按
> "退化单轴"语义引用，真 2D 格点的运行时反射化明确为 future work（见 §5.4 宽轨
> 2D-wide 的可运行时检查为另一侧）。
- **覆盖范围（首句明示）**：本模块**不覆盖真正的 2D 格点（n1,n2≥2）**——检查器
  只处理单轴退化（n1=1 或 n2=1，即退化 1D）配置，是 1D 情形在 2D 口径下的
  参数化反射化，非"真正的 2D 反射检查器"（真 2D 的运行时反射化为 future work）。
- **定位**：§5.4 的双轨并列在 2D 层两侧均有反射化实现——**宽轨 2D-wide 免 H_dom**（§5.4），
  而**窄轨 2D 的 H_dom 判定本身被做成可运行时检查**（本模块，`PSA_framework.v` L5166–6290，
  ~1125 行，审计 6 项全零 classic：`PSA_audit.v` L224–229）。这把 §10 (i) 的"H_dom 尚未
  反射化（N≥3）"在 2D 层闭合：窄轨 2D 是**带健全性证明的 H_dom 可判定成员**。
- **覆盖范围（如实）**：检查器 `frame_check_2d_narrow` 的 `single_band` 要求
  n1=1 或 n2=1，即**只通过单轴退化（退化 1D）配置**；对真正的 2D 格点
  （n1,n2≥2）返回 false、不提供保证。真 2D 的保证由**静态定理**
  `tensor_product_unconditional_basis_pointwise`（覆盖全部 n1,n2≥2 窄轨 2D，
  K0=C³/4 口径）给出。故本模块的反射化价值 = **退化情形的更紧常数运行时判定**；
  真 2D 的运行时反射化是 future work（宽轨 2D-wide 的免 H_dom 可运行时检查
  是另一条互补路线）。
  **证明对象 vs 实验对象（评审 7 元 III，如实）**：`seq_ext` 把有限阶梯延拓为
  无限几何序列以满足 `abstract_unconditional_basis` 的全局增长前提——健全性定理
  `frame_check_2d_narrow_sound` 保证的是**该规范几何延拓**的框架界；运行时检查器
  只检查输入的**有限列表**（不验证生成器是否按公式延拓）。故保证适用于"阶梯的
  规范几何延拓"，**非直接等价于有限截断模型的外推性能**（标准证明技巧，如实声明）。
- **严格增长延拓 `seq_ext`**（E075 关联）：窗口内取 `nth i vals`；窗口外按几何闭式
  `cC^k·(S(last)+1) − 1` 延拓（`pow_pos_nat` / `seq_ext_tail_closed` / `seq_ext_geom_R` /
  `seq_ext_growth_R` 等族）——把有限阶梯提升为全索引序列以满足 `abstract_unconditional_basis`
  骨架的全局增长前提；
- **可判定 H_dom `hdom_2d_narrow`**（L5568）：两轴序对的轴间支配条件归约为布尔判定
  （`single_band_case` / `dom_check_n1_1` / `dom_check_n2_1` / `index_bound_2d` 分支）；
- **反射检查器 `frame_check_2d_narrow`**（L5381，`manhattan_ok` + 行和判定）与其健全性
  **`frame_check_2d_narrow_sound`**（L6175，Qed）：判定通过 ⟹ 窄轨 2D（K0=C³/4 口径）
  Gershgorin 框架界——与 1D `frame_check_instance_sound` 同构的 2D 反射化；
- **点态组装 `tensor_product_unconditional_basis_pointwise`**（L5653，Qed）：2D 窄轨的
  `abstract_unconditional_basis` 实例（点态 φ2D(i,j)(k)=γ⁻¹ψ_i(k)ψ_j(k)），与 §5.4 宽轨
  2D-wide 的组装构成**双轨反射化闭环**（宽轨免 H_dom / 窄轨 H_dom 可判定，视应用取用）。

## 5.6 可证明性边界与碰撞刻画（2026-08-22 新定理族）

> 本族回答论文 B 的"性能-可证明性张力"：不是工程未达，而是**定理层面**的边界。
> 全部模块零 Admitted/零自定义公理；ParetoLaw/P1Coherence/ParetoRandom 仅 Stdlib
> Reals 自包含；合并版 23/24 独立编译 EXIT=0 + coqchk 复核通过。z 区探针按
> z/ 独立编译验证（不并入合订版，scope 污染实测，见 §15.3 记录）。

### 5.6.1 帕累托律：稠密覆盖与 μ≤4/5 可判定认证互斥（`src/ParetoLaw.v`）

- **P2（单对触发）** `pair_bound_gt_4_5`：0 < n < n′ 且 d = n′−n < (5/8)√(nn′)
  ⟹ 保守对界 B(n,n′) = √(nn′)/(2d) > 4/5 ⟹ 行和 > 4/5 ⟹ 检查器拒绝。
- **P3（增长引理）** `pair_bound_le_4_5_geometric`：不触发 P2（B ≤ 4/5）⟹
  n′ ≥ c·n，c = ((5+√281)/16)² ≈ 1.8501（二次因式分解 64n′²−153nn′+64n² =
  64(n′−r_hi·n)(n′−r_lo·n)，`field [sqrt281_sq]` 吸收 (√281)²=281；Rocq 9 引理
  名变更：`Rle_sqr`→`Rsqr_incr_1`（x≤y 在前）、`pow_succ`→`tech_pow_Rmult`）。
- **P3（完整主定理）** `pareto_law_main`：m 个相完备带 f 0 < … < f (m−1) ≤ N 且
  检查器通过 ⟹ **3·c^(m−1) ≤ N**（`geom_growth` 序列归纳 + `incr_ge_first`）。
- **N=511 推论** `pareto_law_N511`：**N=511 时 m ≥ 10 必被拒绝**（`c9_gt_511`：
  511 < 3·c^9，经 √281 > 167/10 ⟹ c > (217/160)² ⟹ 数值 `vm_compute; lra`）。

**意义**：②的负结果定理化——"有证书且接近最优"（μ≤4/5 口径）结构性不存在；
E5''（7 带）在阈值内但实际已失败（累积行和 1.41），C3-trunc（5 带）0.54 通过，
实测密集 16–32 带全部拒绝，与定理一致（框架文档 §4）。

### 5.6.2 精确窗口相干下界（`src/P1Coherence.v`，与 §5.6.1 保守界分层）

- **P1** `p1_coherence_lower`：1 ≤ n < n′、d = n′−n ≤ n′/2、T ≥ n′ ⟹
  coh_T(n,n′) ≥ (2/π)·√(n/n′)（Jordan `jordan_sin_ge` 经典 MVT 路线 +
  `sin_abs_le_x_half`；与 ca_basis_lemmas 的构造性 dyadic 路线并存、不依赖）。
- **P1′** `p1_prime_coherence_lower`：同前提 ⟹ coh_T ≥ √(n/n′)·(1 − π²d²/(6n′²))
  （`sin_ge_x_minus_x3_6`：sin_bound 交替级数 n=0）。

**意义**：近邻大带（如 (216,217)）相干 ≈ 0.997——稠密随机阶梯高相干的**解析根源
成为定理**；精确窗口口径与 P2/P3 保守界口径分层（框架文档 §5）。

### 5.6.3 随机版负定律（`src/ParetoRandom.v`，接 §5.6.1）

- **T2a（同箱触发）** `t2a_same_bin_rejected`：n < n′ < (9/5)·n ⟹ d < (5/8)√(nn′)
  ⟹ P2 触发（9/5 < c = 1.8501；`ratio_lt_c` 经 √281 > 167/10）。
- **T2b（生日-箱计数）**：`fall9`（下降阶乘 (9)_m）+ `no_collision m = (9)_m/9^m`
  定义；**符号化单调性** `no_collision_decreasing`/`no_collision_le`（递推
  no_collision (S m) ≤ no_collision m，`div_le` 交叉相乘，不依赖具体数值）；
  数值界 `prob_collision7_ge`（m=7 ⟹ P(同箱对) ≥ 96/100）、`prob_collision8_ge`
  （m=8 ⟹ ≥ 99/100）、`prob_mono`。合成：同箱对 ⟹ P2 触发（T2a）⟹ 检查器拒绝，
  故 P(拒绝) ≥ 1 − (9)_m/9^m；m ≥ 10 由鸽笼（= P3）确定性覆盖。
- **平台限制（实测，如实记录）**：Rocq 9 大 nat 字面量（of_num_uint 抽象）在
  vm_compute/kernel 转换检查下栈溢出（Stack overflow），(9)_7 = 181440、9^7 =
  4782969 无法在 nat 层计算连通——数值界以 R 层显式分数表达（数学等价），
  单调性走符号化递推规避。
- **备注①（2026-08-22，精确阈值核实）**：5/8 已是精确阈值——`pair_bound_gt_4_5`
  是 iff（d < (5/8)√(nn') ⟺ 64n'²−153nn'+64n² < 0 ⟺ B > 4/5，同一二次型）；
  "收紧检查器保守界"无空间（adaptive_denom 考古项销案），假阴性收紧路径在
  有理松弛→精确算术（Zarith）与 `cert_optimize` 子框架搜索。
- **备注②（2026-08-22，初等替代证明）**：`ten_bands_reject`（z 区 probe_pigeon，
  第 15 模块，零公理）——**任意 10 条 [3,511] 带必含 P2 触发对**：插入排序 +
  相邻比率 ≥ 9/5 的指数爆炸（3·9^9 > 511·5^9，Z 层收口）+ 严格相邻对经
  `same_bin_triggers`、重复对单独处理——`pareto_law_main`（m≥10 必拒）的
  **初等替代**（排序 + 相邻比率，不需增长假设的链式归纳）；与 T2b 概率版互补：
  鸽笼 = 确定性、概率版 = whp。

**意义**：负定律从"确定性密度上限"（P3）延伸到"随机 log-uniform 阶梯 whp 拒绝"——
7–8 带区间随机不可证性成为定理（z 区交互文档 §2-T2 承接）。

### 5.6.4 碰撞距离框架与认证外推不变族（z 区探针，独立验证）

- **碰撞刻画（probe_collision.v C1–C5 + probe_tchar.v T1–T4）**：精确碰撞 ⟺ 角度
  有理（`collides_iff_rational_witness`，全构造性 iff，显式见证）；有理时最小碰撞
  距离 = 分母（`rational_min_period_coprime`/`offset_min_period_coprime`，既约
  offset 网格 = q·N）；**纯网格 q=1 距离恰 N**（`grid_first_collision_at_N`——grid
  崩塌的形式侧）；**无理偏移（黄金比）⟹ 永无精确碰撞**（`irrational_offset_no_collision`）；
  **线性偏置（ALiBi）无碰撞端点**（`linear_bias_no_collision`——非周期核，碰撞距离
  = ∞）。
- **μ=0 能量守恒等式（probe_parseval.v）**：互异网格原子在 a·N 窗口
  ‖Σc_t·u_t‖²_{aN} = Σ|c_t|²（`parseval_two`，等式而非界——框架界定理的退化端点）。
- **窗口无关 Dirichlet 部分和界（probe_partial.v）**：j ≢ 0 (mod N) ⟹
  ‖Σ_{k<W} e^{2πikj/N}‖ ≤ N/(2·min(j mod N, N−j mod N))，窗口 W 无关
  （`dirichlet_partial_bound`，共轭对称化，含库内首批 Cnorm 三角不等式自证）。
- **任意角度对 Dirichlet 界与混合网格相干界（probe_pairdirichlet.v）**：
  任意角度 t1 t2，差频 = 2π·j/N（j mod N ≠ 0）⟹ 任意窗口 W 上
  ‖Σ e^{ik·t1}·conj(e^{ik·t2})‖ ≤ N/(2·min(j mod N, N−j mod N))（`pair_dirichlet`）；
  推论 `mixed_grid_coherence`：嵌套网格 N 与 a·N 两原子跨网格相干界——grid 崩塌后
  多尺度设计空间的定理（混合网格 512/1024/2048 分维的跨网格相干上界）。
- **ρ^{−3/2} 逐对紧界（probe_pairbound.v，2026-08-22 ① 已 Qed）**：
  ‖⟨ψ_a,ψ_b⟩‖ ≤ sin(πa/b)·√(ab)/(2(b−a))（`pair_inner_norm`，Jordan 分母，
  逐对 Θ(ρ^{−3/2}) 界，与见证 (2,2C) 之比随 C→∞ → 1）——常数演进线
  4K → 2K → Θ(C^{−3/2}) 的逐对引擎已证；**行和重组与见证下界进行中
  （z 区三件套②③，未完成前不入主张）**。
- **τ 三分（probe_taudicho.v，零公理）**：`tau_inwindow`/`tau_ood`/`tau_split`/
  `tau_count_link`——碰撞质量 τ 的窗内/OOD/三分刻画（OOD 见证 k := 0 的教训已录）。
- **U5 黄金近碰撞半径（probe_nearcoll.v，皇冠收官，2026-08-22）**：
  **∀ d ≥ 1、∀ m ∈ Z：|d·φ_gold − m| ≥ 1/(3d)**（`golden_near_collision_gold`，
  φ_gold = (√5−1)/2；代数数范数路线：e·(m+d+dφ) = d²−dm−m² + 无穷递降
  `square5_zero`（x²=5y² ⟹ x=y=0，**零公理**）；主定理脚印 = Dedekind 两件，
  src 侧编译复核 EXIT=0）——近碰撞不能快于 O(1/d) 聚集。
- **素数阶梯分辨率与最优性（2026-08-22，`src/CRTResolve.v` + z 区 probe_ladderlimit）**：
  ① 存在性 `prime_ladder_8` + `prime_ladder_8_pairwise_coprime`（8 素数链
  [3,7,13,29,59,127,251,503]，相邻比率全 ≥ 1.85，两两互素）；
  ② 分辨率 `crt_inj`（两两互素 ⟹ 联合模单射，lcm = 乘积 ≈ 7.49×10¹² ≫ 8× 视界）；
  ③ **最优性 `no_nine_band_ladder`**（z 区第 14 模块，贪心交换论证，贪心链
  113/211/397 比 8 带链更紧）：**[3,511] 内不存在 9 元素素数阶梯**——素数身份从
  "存在 8 带链"升级为"8 带是最优"（素数叙事完整：存在性 + 分辨率 + 最优性）。
  素性用 no_small_divisor（纯 stdlib），合数区间逐值显式见证。

**意义**：offset-grid 的形式化辩护**三半**均 Qed——T1a 证书保持（差频相消、Parseval
等式）+ C5 无理偏移零精确碰撞 + **U5 近碰撞半径护城河**（与 C5/T2 合成：黄金偏移的
碰撞谱被双向挡死）；"偏移分母 q 是把碰撞推出评估视界的零成本旋钮"成为机器检查陈述；
论文 B 的 τ/碰撞机制获得形式化碰撞结构支撑（"经验律 + 形式化碰撞结构"双层表述）。
素数阶梯条目支撑论文 B 的 CRT 分辨率轴受控对照（prime-7 vs prime-8 vs E5''）。

### 5.6.5 分级证书与一般维张量（z 区探针）

- **容错 Gershgorin（probe_robust.v）**：`robust_gershgorin`——坏对每行 ≤ δ·n ⟹
  绝对行和 ≤ INR n·(mu+δ)；**`robust_certificate`：mu+δ ≤ 4/5 ⟹ 行和 ≤ INR n·4/5**
  ——检查器从二元升为分级证书（干净界不达标但 mu+δ 达标仍可证；激活 ca_decay 的
  δN² 容错存在性定理）。
- **一般维张量（probe_tensor.v）**：`tensor_bound_uniform_N`——N 轴张量积行和 ≤
  **(1+r)^N − 1（∀N 闭式，`tsum_shift`/`rprod_shift` 轴号平移引理）**——论文 B §6
  跨维推测得证，"Theoretically Composable" 从评注变定理（2D/3D/4D 为 N=2/3/4 特例）。
- **核漂移（probe_kerneldrift.v）**：`kernel_drift_logit`（KD3）——核逐点漂移 ≤ dc
  且系数 ℓ1 ≤ dd ⟹ |Σ c_j·(K_ij−K'_ij)| ≤ dc·dd（脚印仅 sig_forall_dec + fext）；
  组合线接 `SoftmaxStability.softmax_l1_bound_exp` 得 TVD ≤ e^{2·dc·dd}−1（PSA_framework
  已重建，可封口）；网格族 Δ=0 ⟹ TVD=0（表示级不变性带证书）。

**落点**：本族与 §5.1–5.5 认证链正交，构成"认证（正）— 可证明性边界（负定律）—
碰撞/分辨率刻画（机制）"三角；论文 B §10.8 的 τ 机制 5 个正向判决与之一致。

## 6. 提取与可执行检查器
- PSA_extract.v → psa_guard.ml → ocamlc 字节码 exe → psa_guard_ffi.py；
- **提取机制（评审 A2 澄清）**：核心判定函数（`check_sparse_growth` / `greedy_*` /
  Coq 版 `frame_check_instance` 等）由 **Coq `Extraction` 机制**生成 OCaml
  （`PSA_extract.v` 的 `Extraction "psa_guard"` 命令，产物 `psa_guard.ml`）——
  非"手动翻译"；`main.ml` 为 CLI 包装（手动，仅 I/O 十进制转换）；`frame` 的
  **原生 int 镜像**（`frame_check_instance_int`）因效率手动重写（规避 Peano 大数
  栈溢出），其与 Coq 定义的等价性为**逐行镜像 + FFI 24/24 交叉校验**（含 [3,13]
  纠错案例），非机器证明（见范围前提）；随机/属性测试增强为 future work。
- 自测 **24/24**（统计口径：PSA_refcheck.v 20 项 Check/Eval + 4 项整数行和验算；19 旧 + 5 新 frame）；
- **`frame_check_instance`（会话 9 落地，10+11 完成健全性）**：任意阶梯 →
  反射布尔判定 μ≤4/5。PSA_framework.v 定义 + `frame` CLI + FFI wrapper。
  原生 int 实现（main.ml 的 frame_check_instance_int，镜像 Coq 定义）规避 Peano
  nat 大数乘法的字节码栈溢出（提取的 Peano 版对 ≥7 带会炸）；key 阶梯回归正确
  （C4/T8 true、E5''/C2b false；psa_guard.exe 实测 C=6 大阶梯值 ~1339 不溢出）。
  **范围前提（如实声明）**：int 镜像与 Coq `nat` 的等价仅对**中间量不超过机器
  字长（OCaml int，63-bit）**的阶梯成立；实验中阶梯值 ≤255 安全，对极大输入
  （≥10⁶ 级）`sparse` 等走 Peano 提取的子命令仍会栈溢出（已实测）——故运行时
  健全性保证的量化范围是**小整数阶梯**，并非 ∀ 阶梯；彻底消除可改用 `Z`
  （任意精度）提取到 `Zarith`（future work）。
  **定量安全阈值（会话 18 扫描修正，原"n_max<2^20、m<100 无溢出"不成立）**：
  行和判定按 `num,den := num·pd + pn·den, den·pd` 连乘累加，**累积分母 ≈ ∏ pair_den**
  （指数增长），与单个 pair_den 上界无关。系统扫描（114 阶梯，`frame_check_scan.py`）
  实测：末带 < 2^20 的阶梯中仍有 14/89（15.7%）exe 与 Coq 语义分歧——如 C=6-sparse
  [3,19,115,691,4147]（末带 4147 < 2^20）：Coq 语义 true、exe 溢出误判 false，累积
  分母达 10^26 ≫ 2^63。实验实际使用（带值 ≤255、m ≤ 8，如 E5'' 七带累积分母 ≈2×10^17、
  C=2 八带 ≈10^12）全部落在 63-bit 安全区，24/24 自测与论文实例均在此区；**通用安全
  阈值须逐阶梯核算 ∏ pair_den < 2^63**（或直接改用任意精度）。**彻底消除：`Zarith`（或
  Python 大整数镜像）提取（future work，评审 9 建议，本扫描即其量化依据）**。
  **int 平方根实现（评审 7 问题 3）**：`main.ml` 的 `int_sqrt n = int_of_float
  (Float.sqrt (Float.of_int n))` 为**浮点近似**（非 Coq `Nat.sqrt` 的规范实现）。
  误差边界：对 n < 2^53（double 精确整数域），float sqrt 舍入 ≤ 0.5ulp，截断后
  int_sqrt 偏差 ≤ 1——影响 pair_den 相对量 ≤ 1/(2Δ·⌊√(n₁n₂)⌋)（Δ 为带距，远小于
  判别余量），**仅在判别阈值附近才可能翻转**（如实声明）；为消除该风险，**安全
  阈值收紧为中间量 < 2^53**（实验值 ≤255 远低于此）。**判定性质声明（评审 8 强化）**：
  `frame_check_instance_int` 的判定结果是**充分非必要条件的一个浮点近似实现**——
  24/24 交叉校验证明在测试样本上一致，非 Coq 判定函数的严格机器等价；对安全
  关键应用，建议使用 Coq 提取的 Peano 版本（慢但精确）或 `Zarith` 任意精度版。
  另：镜像等价本身是**人工核对 +
  逐行同构论证**（非机器证明），与 `frame_check_instance_sound`（Coq 内健全性）
  是两个独立层。
- **健全性闭环**：`frame_check_instance_sound` 已 Qed——判定通过 ⟹
  `gershgorin_frame_mu (length I) (S (last I)) (4/5)`，检查器 = 框架界定理的
  可执行投影，运行时布尔结果自带机器证明的健全性；
- **反射层纠错实例（形式化发现并修复真 bug，可写进 paper）**：反射层原
  `row_sum_frac_aux` 在收缩列表上重算 `nth i I`，使 Coq 判定与生产原生检查器
  不一致（[3,13] 误判 false、C4 行和退化为 (0,0) 空洞通过）；加 `orig` 参数
  修正后 Coq 与原生**逐行同构**（FFI 24/24 复核）。
- **方法论教训：逐行同构（Line-by-line Isomorphism）原则**——上述案例证明
  **"定义等价"不足以保证提取保真性**：`row_sum_frac_aux` 的两个版本在数学上
  定义等价（对完整列表语义相同），但在收缩列表上计算路径分叉，导致 Coq 判定
  与提取实现不一致。结论：提取代码应**尽可能镜像 Coq Fixpoint 的结构**
  （逐行同构），而非依赖高阶重写得到的"语义等价"的另一份代码。本开发将此
  升格为可执行形式化的设计原则，并在 FFI 回归（24/24）中持续检查。

## 7. 公理记账（审计小节，对齐 2026-08-20 基态：165 项全零 classic）
- **审计总量**：PSA_audit.v **165 项** Print Assumptions，RC=0，零 Admitted；
  原始证据 `audit_run.txt`（165 项：111 段 Axioms + 54 项 "Closed under the
  global context"）；
- **公理脚印（全部 165 项仅此）**：ClassicalDedekindReals.sig_not_dec /
  sig_forall_dec + functional_extensionality_dep（标准库反射层基础设施，
  如实声明）；**`Classical_Prop.classic` 出现 0 次**。
  **如实说明（评审对齐）**：`sig_not_dec` / `sig_forall_dec` / fext 是**非构造性
  选择类原则**（由 Dedekind 实数构造自身携带，非本开发应用层引入）——文中
  "classical-free / zero classical axioms"精确指 **`Classical_Prop.classic`
  （排中律宏）零出现**，而非"无任何经典原则"；应用层（注意力近似 / 张量积证书）
  在实数基础设施之上未新增任何经典公理。
  **提取计算性（评审 A5）**：上述公理仅在**证明层**（Prop）使用，不参与提取的
  计算内容——提取出的判定函数为纯构造性计算（Set/Type 层无 `sig_not_dec` 调用）；
  若追求完全构造性实数（Cauchy 序列 / Dedekind 割的构造性变体）可消除它们，
  但证明负担大增（future work）。
  **M1.5 范围精确化（评审 7 问题 1）**："零 classic"精确指 **PSA 应用层新增的
  `Classical_Prop.classic` 依赖为零**（`exp_mono_le` 的 PSA 调用路径经 `ExpSeries`
  重写为幂级数部分和路线）；`exp_plus` / `exp_0` 等底层事实仍继承自 Coq 实数库
  （其证明可能依赖经典 MVT），**不在 PSA 新增的 165 项审计中**——"no MVT"仅在
  应用层成立，非整个实数库零经典。
- **M1.5 经典清零（✅ 已完成并入，2026-08-20 复核）**：此前仅剩的 4 项
  （`softmax_ratio_le2` / `softmax_diff_i` / `softmax_l1_bound_exp`（M1）+
  `certified_attention_approx`（M2））经 exp 单调性继承经典排中。现
  `PSA_framework.v` 的 **`Module ExpSeries` 已 Qed**（`probe_exp_ge_1` /
  `probe_exp_ge_1_plus` / `exp_mono_le_noclassic`，Stdlib `exp` 即幂级数定义、
  `E1_cvg` 定义性平凡、桥接成本为零），`exp_mono_le` 改走幂级数路线
  （`apply ExpSeries.exp_mono_le_noclassic`），**语句不变、下游零改动**——
  全 165 项审计中 `Classical_Prop.classic` = 0，审计项从 139 增至 165
  （新增 M4b/T8/FrameCheckInstance/ChampionCertificate/FrameCheck2DNarrow）。
  **战略意义**：整个 CertifiedAttention 模块（注意力近似主定理）为纯构造性——
  论文 A 是**首个完全构造性的深度学习注意力形式化验证**（不依赖实数完备性的
  排中律），Abstract 已标注 "all 165 classical-free / zero classical axioms"；
- 依赖库（ca_* 六库）全审计为 P4 长期项，如实声明。

## 8. 实证预览（一段 + 一表，3-seed 均值±std；dense 单 seed（b64 s1337），rope 已补 3-seed）
char 级 0.5M 参数、T_train=512、seeds {1337,42,7}、确定性协议（rope 跨协议逐位复现）：
| 方案 | 512 | 1024 | 2048 | 4096 |
|------|-----|------|------|------|
| rope（b32 三 seed） | 4.44±0.08 | 6.77±0.07 | 13.68±1.21 | 25.30±4.63 |
| **psi-rope [3,13,53,213]（本证书对象）** | 4.70±0.14 | 5.64±0.07 | 8.42±0.10 | 12.75±0.34 |
| **psi-rope 七带 [3,…,255]（T8 复合证书对象）** | 4.53±0.10 | 4.75±0.06 | 8.28±0.28 | **12.40±0.74** |
psi-rope 行 3-seed 均值±std、dense 单 seed（b64 s1337，5.42/16.91/27.70/37.74）、
rope 为 b32 3-seed 均值±std（@4096 = 20.28/29.40/26.22 → 25.30±4.63，会话 18 补全）——
定位为 teaser，完整实证与机制分析见配套论文 [Paper B]。

## 9. Related Work
- **Transformer / 注意力形式化（Rocq/Coq）**：[rocq-transformer](https://github.com/jwiegley/rocq-transformer)
  （"Transformers for All" 的 Rocq 实现）形式化 transformer 结构与注意力的类型化实现；
  本开发与之前沿的差异在**保证层级**：rocq-transformer 验证实现与类型，本开发验证
  **解析核的数值保证**（框架界/衰减界/能量预算）——互补而非竞争（"verify the analytic
  kernel, learn the rest" 的实例化）。
- **Certified ML kernel / 程序提取**：[Certificates in AI: Learn but Verify](https://dl.acm.org/doi/10.1145/3737447)
  明确"学习 + 验证"的分离主张，与本开发"可学习分量（W_Q/W_K/softmax 身份）不覆盖、
  解析核机器检查"的边界完全一致；形式化 ML 核的 Coq/OCaml 提取谱系（如 CompCert 式
  proof-carrying kernel、CertiML 类项目）为本开发的可执行提取（psa_guard.exe + FFI
  24/24）提供方法论先例——本开发新增的是**反射检查器自带健全性证明**（
  `frame_check_instance_sound`）这一层。
- **Proof-carrying code 谱系（Necula）**：本开发的反射检查器是 PCC 思想的现代实例——
  运行时布尔判定 `frame_check_instance` + 机器检查的健全性定理，等价于"证书随代码
  传输、接收端可验证"；与经典 PCC 的差异是证书内容为**有理常数界**（可判定算术）
  而非类型/内存安全证明。
- **稀疏注意力无证书方法（对比面）**：top-k 门控、KV 逐出、低秩投影等均无误差证书；
  本开发覆盖的"解析核"层（稀疏/近似注意力）在数学上给出可检查保证，是上述方法的
  形式化对照面。
[⚠️ 参考文献卷期页码已经 2026-08-21 文献数据库核查校准（见《参考文献真实性核查报告》），英文终版按修正后元数据引用。预印本（2026-08-22 发布，Figshare）：论文 A DOI: 10.6084/m9.figshare.33312189；论文 B DOI: 10.6084/m9.figshare.33312336。]

## 10. Limitations
- **高维证书的定位**：3D 定理 `tensor_product_unconditional_basis_3d` 是形式化
  大厦的承重墙——它严格证明验证方法学在高维**逻辑闭合**，并机械固定"维数灾难"的
  精确表达式（1D μ=0.8 → 3D M_bound=3968 的可量化代价，引理
  `M_bound_3d_C4_value`，数值由 field/ring 完全确定地计算）。但其定位是
  **"Theoretically Composable, Practically Non-Tight"**：任何读者不得将该界用于
  紧误差估计。具体边界两条：
  (i) **H_dom 尚未反射化（N≥3）**：3D/4D 的轴间支配条件是有限域全称命题，
  真值可在 O(n₁n₂n₃·(n₁+n₂+n₃)) 次比较内**完全判定**（可判定；术语上并非
  "不可判定"），但我们尚未为其编写反射判定器、未接入 `frame_check_*` 机制——
  3D/4D 证书目前是纯静态定理，应视为**框架理论的纯粹扩展**，而非工程落地承诺；
  **2D-wide 不受此限制**（免 H_dom，见 §5.4）——若二维应用需要"全覆盖 +
  可运行时判定"的证书，2D-wide 是宽轨家族中的可判定成员；
  (ii) **H_dom 经验苛刻（N≥3 显著）**：真实数据（图像/视频 patch）三轴频率独立增长，
  "若一轴相同则另一轴值必须不小于它"要求三轴同调增长，实际很少满足；
- 学习分量（W_Q/W_K、softmax 身份）不在覆盖内——覆盖的是**敏感性**而非身份；
- **What is not certified（评审 10 建议 3，集中清单）**：本框架**不**证明——
  (a) 学习到的 Q/K/V/O 投影下的注意力 logits/softmax 有界（仅能量界 ⟹ 输出扰动界，
  见 §5 轨 b）；(b) 学习到的 Q/K 投影与位置旋转**对易**（酉不变性仅覆盖基函数层，
  §5.3）；(c) 多头拼接、残差连接、LayerNorm/激活的数值稳定性；(d) 训练后权重的
  任何保证（证书对任意系数 c 成立，与训练无关）；(e) 外推 PPL 与框架界之间的
  语义联系（经验桥梁，未形式化）。"verify the analytic kernel, learn the rest"——
  上述 (a)-(e) 均在"learn the rest"一侧；
- **高维证书定位（评审 10 3.3 强化）**：3D/4D 证书是**方法论可行性证明**（骨架
  复用、维度推广逻辑闭合），其常数在当前松弛下**远非紧**（`M_bound_3d 4 = 3968`、
  `M_bound_4d 4 = 19968`），**不得用作实际误差界**——"Practically Non-Tight"按字面
  执行；
- 证书为框架/能量级保证，不直接给出端到端 ppl 界（跨层合成为 future work）；
- 审计 **165 项全零 classic**（`Classical_Prop.classic` = 0，M1.5 已并入：`Module
  ExpSeries` Qed、`exp_mono_le` 走幂级数路线，PSA_framework RC=0）——不再有经典
  逻辑遗留；公理脚印仅 sig_not_dec + sig_forall_dec + fext（标准 Dedekind 实数
  基础设施，如实声明）；
- 实证规模 toy 级、单 seed [multi-seed 已补：主表 3-seed 均值±std，dense/rope 补 seed 待做]；
- **形式化的适用域以结构存在为前提**：框架界与衰减界的全部证明依赖频率阶梯
  （seq 存在性）；对无位置结构的编码（NoPE 类）本框架**无任何可证陈述**。
  论文 B 实证给出这笔"定量交易曲线"：有结构端以分布内 ppl ~2× 劣化
  （4.46 vs 9.06）为代价承受 OOD 相位混淆风险（外推退化 2.7–2.9× vs NoPE 的
  1.27×）；形式化锁定的正是交易中**有结构的一端**（可证性 + 分布内最优性），
  无结构端的平缓外推在本框架的可证范围之外（两文联合边界，见论文 B §8：
  无证书的测试时修复 rope-NTK 与带证书的免修改方案在同一基准上构成
  不可比的实证-形式化张力）。

## 11. Conclusion
生成 → 守卫 → 门控 → 衰减 → 框架 → 截断 → 稳定性 → 注意力近似 → **实例证书（有理、
可判定）** → 长度一致性（∀N≥214）→ T8 复合证书 → **反射检查器 `frame_check_instance`
及其健全性定理 `frame_check_instance_sound`（**165 项审计，全部零经典排中**）**：
一条完整的、零 Admitted 的**表示层（representation-level）**认证管线——为解析核
保证服务，与论文 B 的实证性能正交；与一个小规模但方向一致的实证轨道互为印证。

**可组合的反射化（方法论贡献）**：反射检查器的健全性证明是**可组合的（Composable）**——
3D 张量核的静态定理 `tensor_product_unconditional_basis_3d`（`ca_basis_3d.v`，与 1D
`gershgorin_frame_mu` 共享同一 `abstract_unconditional_basis` 骨架）即为该组合性的一个
实例骨架；其反射化是提取链的**直和扩展（direct sum extension）**，而非基础理论修正。
宽轨家族 2D/3D/4D 成员齐备：2D-wide（会话 15 交付，**免 H_dom**，`M_bound_2d_wide 4 =
768` 已 Qed）、3D（`M_bound_3d 4 = 3968`）与 4D（`M_bound_4d 4 = 19968`）——N 维公式
M_bound^{(N)} = (C³/2)·((1+4K_C)^N − 1) 的 N=2/3/4 校验全部定理级成立，且 2D 是宽轨
家族中唯一免支配假设、可运行时判定的成员（见 §10 边界：H_dom 限制在 2D 窄轨
可反射化、2D-wide 免，N≥3 需跨轴同调最苛刻）。
客观地讲，3D/4D 证书当前是非紧的存在性结果，定位为 **"Theoretically Composable,
Practically Non-Tight"**，其价值在架构可组合性与维度推广的定位，而非常数本身；
1D 证书（μ=4/5）保持紧且不受影响。

**可证明性边界（v9 新增，§5.6）**：在认证管线之上，本开发把论文 B 的
"性能-可证明性张力"从实证观察升格为定理——**稠密覆盖与 μ≤4/5 可判定认证互斥**
（`pareto_law_main`/`pareto_law_N511`：N=511 时 m≥10 必拒；P1/P1′ 给出精确窗口口径
相干下界的解析根源；T2a/T2b 把负定律延伸到随机阶梯 whp 拒绝）。配套的碰撞距离
框架（碰撞 ⟺ 有理、最小距离 = 分母、无理偏移零碰撞、ALiBi 无碰撞端点、Parseval
能量守恒、窗口无关 Dirichlet 界、容错 Gershgorin 分级证书、一般维张量闭式）为
论文 B 的 τ/碰撞机制提供形式化镜像——"认证-可证明性边界-碰撞/分辨率刻画"三角
被机器检查覆盖，零 Admitted、零自定义公理。

---
*配套：论文 B（实证+相位律）、预登记实验设计、定理栈增强路线。*


---

## 附录 A 代码-论文声明交叉索引表（评审 6 建议）
- **复现指引（评审 总体-2）**：形式化代码 `src/`（`_CoqProject` 声明 load path；
  各模块独立编译命令见 E067/E077 经验卡）；提取链 `PSA_extract.v` →
  `psa_guard.ml` → `psa_guard.exe`（DkMLNative `ocamlc` 字节码 + camlrun）；
  FFI 自测 `python psa_guard_ffi.py`（24/24）；审计证据
  `AI注意力算法\审计证据\audit_run.txt` 等；实验代码与数据
  `psa_empirical/`（`length_extrap.py` 等，3-seed 固定种子 {1337,42,7}，见论文 B）。
| 论文声明 | 代码位置 | 状态 |
|---------|---------|------|
| 165 项全零 Classical_Prop.classic | PSA_audit.v（165 项 Print Assumptions） | ✅ |
| 端到端复合证书 Qed | PSA_framework.v L5075（Module ChampionCertificate L4582-5150） | ✅ |
| 反射检查器健全性 Qed | FrameCheckInstance.frame_check_instance_sound | ✅ |
| M1.5 经典清零 | Module ExpSeries（exp_mono_le_noclassic，exp_mono_le 走级数路线） | ✅ |
| 酉不变性机器检查（RoPE 显式实例） | Module UnitaryInvariance（unitary_invariance_psi_rope_theta / Cexp_unit_mod） | ✅ |
| 2D-wide 免 H_dom | ca_2d_wide_asm.v（tensor_product_unconditional_basis_2d_wide，M_bound_2d_wide 4 = 768） | ✅ |
| 3D 张量积 | ca_basis_3d.v（tensor_product_unconditional_basis_3d，10 项审计零 classic） | ✅ |
| 4D 张量积 | ca_basis_4d.v（tensor_product_unconditional_basis_4d，M_bound_4d 4 = 19968，coqchk 复验） | ✅ |
| 2D 窄轨反射化（退化单轴） | FrameCheck2DNarrow.frame_check_2d_narrow_sound（single_band 限 n1=1 或 n2=1） | ✅ |
| 提取 / FFI 24/24 | PSA_extract.v -> psa_guard.exe（frame CLI 实测：C4/T8 true、E5'' false） | ✅ |
| P2/P3/N511（帕累托律） | src/ParetoLaw.v（pair_bound_gt_4_5 / pareto_law_main / pareto_law_N511） | ✅（v9） |
| P1/P1′ 精确相干下界 | src/P1Coherence.v（p1_coherence_lower / p1_prime_coherence_lower，coqchk 复核） | ✅（v9） |
| T2a/T2b 随机版负定律 | src/ParetoRandom.v（t2a_same_bin_rejected / no_collision_decreasing / prob_collision7_8_ge） | ✅（v9，T2b 2026-08-22） |
| CRT/素数链 | src/CRTResolve.v（crt_inj_two / prime_ladder_8_pairwise_coprime） | ✅（v9） |
| 碰撞刻画/ALiBi 无碰撞 | z/probe_collision.v（C1–C5）/ z/probe_tchar.v（T1–T4） | ✅（z 区独立验证） |
| Parseval 能量守恒 / Dirichlet 界 | z/probe_parseval.v（parseval_two）/ z/probe_partial.v（dirichlet_partial_bound） | ✅（z 区独立验证） |
| 任意角度对 Dirichlet / 混合网格相干界 | z/probe_pairdirichlet.v（pair_dirichlet / mixed_grid_coherence） | ✅（z 区独立验证） |
| 容错 Gershgorin / 一般维张量 / 核漂移 | z/probe_robust.v / probe_tensor.v / probe_kerneldrift.v | ✅（z 区独立验证） |
| U5 黄金近碰撞半径（1/(3d)） | z/probe_nearcoll.v（golden_near_collision_gold，square5_zero 零公理） | ✅（z 区独立验证，src 侧复核 EXIT=0） |
| 素数阶梯极限（no_nine_band_ladder） | z/probe_ladderlimit.v（[3,511] 无 9 元素素数阶梯） | ✅（z 区独立验证） |
| 鸽笼确定性版（ten_bands_reject） | z/probe_pigeon.v（任意 10 带必含 P2 触发对） | ✅（z 区独立验证） |
| ρ^{−3/2} 逐对紧界（PB3/PB4） | z/probe_pairbound.v（pair_S_bound / pair_inner_norm） | ✅（z 区独立验证） |

---

## 附录 B 版本历史（开发记录，投稿前删除）

> v4–v9 对齐协议全文（2026-08-20 至 2026-08-22 的开发演进记录，保留以供追溯）。

**对齐协议（基态，2026-08-20 会话 17）**：本版对齐至 2026-08-20 会话 17 终态（A2/A1 完成后基态）——
`frame_check_instance_sound` 主定理已 Qed（会话 10+11 装配），**M1.5 已清零**：审计 **165 项** RC=0、
零 Admitted、**全部 165 项零经典排中**（`Classical_Prop.classic` 出现 0 次，证据 `audit_run.txt`
追加段）；M4b 长度一致性 + T8 复合证书 + **端到端复合证书 `champion_e5_composite_certificate`
（会话 14 Qed）** 已并入；FFI 24/24（refcheck 20 项 + 整数行和验算 4 项）。

**v8 对齐修正（2026-08-20 会话 17 终态）**：① **A2 酉不变性已完成**——v6 的"降级为数学事实
（未机器检查）"被推翻：探针 `src\_probe_unitary.v` RC=0 后 Module `UnitaryInvariance` 已并入
`PSA_framework.v` 帧尾（`unitary_invariance_point` 全局保内积版 + 位置索引 psi-rope 版
`unitary_invariance_psi_rope(_global)`，RoPE 语义、无需正交性即保 l2 范数）；原"每带乘 u_i"
逐点版本为假命题（交叉项需 u_i=u_j，反例 u0=1,u1=-1,g0=g1=1：|1-1|²=0≠4=|1+1|²），未并入。
② **A1 4D 组装完成**：`tensor_product_unconditional_basis_4d` 单文件版 `ca_basis_4d.v`
（122KB/2073 行）Qed，coqchk 复验 RC=0，已并入 27模块 目录（28 个 .v）与合并版 28 分区。
③ PSA_framework.v 现 **6405 行 / 19 个 Module / 250 Qed**；行号修正：ChampionCertificate Module
L4582–5150（定理本体 L5075）、FrameCheck2DNarrow L5166–6290；3D 审计 **10 项**（`PSA_3D_audit.v` 实测）。

**v7 对齐修正（2026-08-20 会话 17，代码库基态复核）**：PSA_framework.v 实际 **6284 行 /
16 个 Module / 242 Qed**（原"4430 行 / 13 模块"过期，已改）；ChampionCertificate 行号改
L4576–5159（定理本体 L5069）；3D 审计项数 **8→10**（`PSA_3D_audit.v` 实测）；FFI 24/24
标注统计口径（refcheck 20 项 + 整数行和验算 4 项）；**新增 §5.5**：FrameCheck2DNarrow
（2D 窄轨反射化）——代码库既有模块的正文补写（`hdom_2d_narrow` / `frame_check_2d_narrow_sound` /
`tensor_product_unconditional_basis_pointwise`，审计 6 项全零 classic）。

**v6 P0 修正（2026-08-20 专家裁定）**：① `champion_e5_composite_certificate` 由"在制"改为
"✅ 已完成（会话 14 Qed）"，目标形状据 .v 实际定理改写为对称界 `(S−coh_e5) ≤ ‖F‖²_{255} ≤ (S+coh_e5)`；
② 酉不变性桥接如实降级为"数学事实（未机器检查）"（unitary 在 .v 零命中），关闭项列为 P1；
③ `.v` 头注释已同步 v1.0（src\PSA_framework.v）。另增 §5.2b（可判定性溢价独立方法论小节）与
§9 Related Work 具体先例。

**v5 对齐修正（2026-08-20）**：**M1.5 经典清零已实际完成并入**——PSA_framework.v 的
`Module ExpSeries`（`exp_mono_le_noclassic` 等）已 Qed，`exp_mono_le` 改走幂级数路线；
审计项从 139 增至 **165**（新增 M4b/T8/FrameCheckInstance/ChampionCertificate/FrameCheck2DNarrow），
**全 165 项 `Classical_Prop.classic` = 0**，仅继承 sig_not_dec + sig_forall_dec + fext。
本文档所有"139/135/4 项待清零"表述均已替换为"165 项全零 classic"。

**v4 增量（2026-08-20 会话 15/16）**：**2D-wide 张量积无条件基已交付**——
`tensor_product_unconditional_basis_2d_wide`（K0 = Rmax 8C³/2，**免 H_dom**，覆盖全部
idx1≠idx2 离对角对）+ `M_bound_2d_wide 4 = 768`（数值裁决已 Qed）+ 配套审计 5 项零 classic
（`ca_2d_wide_audit.v`）——宽轨家族 N=2 成员补齐，2D/3D/4D 张量积证书族闭合（论文 B §6 的
M_bound 公式 N=2 校验从"数值验证"升级为"全定理级已证 + 免 H_dom 的独立证明路线"）。

**v9 增量（2026-08-22 会话 19+）**：**可证明性边界新定理族**（§5.6）——① 帕累托律
（`src/ParetoLaw.v`，仅 Stdlib Reals 自包含）：P2 单对触发（`pair_bound_gt_4_5`）、
P3 增长引理（`pair_bound_le_4_5_geometric`，c≈1.8501）、**P3 完整主定理（`pareto_law_main`：
m 个相完备带 ⟹ 3·c^(m-1) ≤ N）+ N=511 推论（`pareto_law_N511`：m≥10 @ [3,511] 必拒）**；
② 精确窗口相干下界（`src/P1Coherence.v`）：P1/P1′（`p1_coherence_lower`/`p1_prime_coherence_lower`，
Jordan + sin_bound 自证，coqchk 复核通过）；③ 随机版负定律（`src/ParetoRandom.v`）：
T2a 同箱触发（`t2a_same_bin_rejected`）+ **T2b 生日-箱计数（2026-08-22 完成：`fall9`/`no_collision`
定义、符号化单调性 `no_collision_decreasing`/`no_collision_le`、数值界 `prob_collision7_ge`
（m=7 ⟹ ≥96/100）/`prob_collision8_ge`（m=8 ⟹ ≥99/100））**；④ CRT/素数链（`src/CRTResolve.v`，
mathcomp）；⑤ **z 区碰撞/分辨率族**（12 探针全 Qed，独立验证于 z/）：C1–C5 碰撞刻画
（含 **ALiBi 无碰撞 `linear_bias_no_collision`**）、T-CHAR 最小周期闭式、Parseval 能量守恒
等式（μ=0 端点）、窗口无关 Dirichlet 部分和界、容错 Gershgorin 分级证书（mu+δ≤4/5）、
一般维张量（(1+r)^N−1 ∀N）、τ 三分、核漂移（softmax 组合线待 PSA 重建后封口——
PSA_framework.vo 已重建，可接）、U5 黄金近碰撞半径（1/(3d)）。合并版 23/24 重新生成
（31/32 模块），独立编译 EXIT=0 + coqchk 复核通过，零 Admitted/零自定义公理。
