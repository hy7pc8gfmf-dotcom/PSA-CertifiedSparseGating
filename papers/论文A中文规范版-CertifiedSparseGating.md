# 可认证稀疏门控与注意力近似：一个可执行的 Coq 开发

**Certified Sparse Gating and Attention Approximation: An Executable Coq Development**

> 作者：王宝军、夏挽岚、祖光照、周志农、高雪峰
> 版本：最终版 v2.14（2026-08-30）｜代码基态：PSA_framework.v（18 模块 / 269 顶层 Lemma·Theorem（316 顶层声明 / 272 Qed 口径内）/ 165 项审计：**`Classical_Prop.classic`（排中律宏）零出现**——非"零任何经典原则"，公理脚印 sig_not_dec/sig_forall_dec/fext 为 Dedekind 实数基底可接受原则，post-M1.5 复核成立）+ 可证明性边界族（ParetoLaw / P1Coherence / ParetoRandom / CRTResolve）+ z 区 34 探针（**20 个已并入合并版 25**：8 经典 pro 化探针 grid_ortho/parseval/partial/pairbound/rowsum/pairdirichlet/incoherence/row_rip + c4_instance + welch/uncertainty_cr/g8_synthesis_cr/g1_norm_closed/g2_mu_adj + 构造性族 pi_cr_m1a/m1b/sin_cr_m2/sqrt_cr_m3/s7_s9_mono/decidability_premium_cr；2026-08-30 welch/g1_norm_closed/g2_mu_adj 三探针**场景模式化**（独立编译 2.5 EXIT=0：welch 补 `Require Import ca_taylor`、g1 依赖链 8 文件重编收敛））+ **合并版 ca_merged_full_25.v（87632 行，57 顶层 Module = 55 模块分区 + independent/independent′ 2 附加，MERGE_EXIT=0）**——SHA-256 基 4901f18e；公理审计 2026-08-30 重跑：54 Closed + 111 Dedekind 三公理、`Classical_Prop.classic` 零出现，与 08-26 版结果一致｜**CI（GitHub Actions）全链路绿（2026-08-30）**：lib 链编译 + 合并版编译（Rocq 9.0 + mathcomp 2.6 真环境）+ PSA 核心三文件 + 零 Admitted 检查 + coqchk 内核独立复验，五步全过
> 修订摘要（v2.13→v2.14，2026-08-30，E153 收官对齐 + 2026-08-29 交叉分析修订落实）：**代码基态刷新**——合并版 87632 行（E153 批次二：78808→81169 八处 mathcomp 2.6 适配修复，本地 2.5 + WSL 9.1.1 双环境验证），**CI 全链路绿收官**（commit b57a2b5/7628fef/2f21249：编译 + 零 Admitted 检查 + coqchk 内核复验，检查脚本 grep 误报注释已修为语句形态 `Admitted\.`）；**P0-2 softmax 紧度勘误**——摘要/§1/§4 的 ‖softmax z − softmax z'‖₁ 界从 `2(e^d − 1)` 更正为 **`exp(2·d) − 1`**（代码 `softmax_l1_bound_exp` PSA_framework.v:2216-2220 实形态，旧稿高估紧度）；**P1-1 引用-权威对齐**——§5.6 压缩感知/τ 族的探针引用补注权威独立模块（`ca_rip_cr.v` `row_rip_bound_M`、`ca_tau.v` `tau_crop_mono`），探针降级为独立验证附注；**审计口径统一**——"全零经典排中"表述全文统一为诚实口径（排中律宏零出现 + 公理脚印披露，正文 §5/§6 原有精确表述不变）；30模块 归档 2026-08-30 新增 probe_welch / probe_g1_norm_closed / probe_g2_mu_adj（SHA 一致）；开发区→PSA 仓库对齐提交 2f21249（ca_tau 入 lib、CS 战役 4 探针入 probes、14 py 入 empirical）。
> 修订摘要（v2.11→v2.12，2026-08-27，合并版重生成 + M3 代数化）：**合并版 `ca_merged_full_25.v` 重新生成**（87588 行 / 57 顶层 Module / 20 探针，`_merge_ca.py`，MERGE_EXIT=0 复验；30模块 归档 SHA-256 同步）；**M3 构造性 √ 界代数化**（`probe_sqrt_cr_m3.v` 的 `sqrt21_lower`/`sqrt105_lower` 从 qbisec vm_compute 数值核验升级为代数证明——Q 层平方界 `(4582/1000)²≤21` + 自建非负平方单调 `CRle_square_nonneg` + `CR_of_Q_mult`/`CRsqrt_sq` 桥，Print Assumptions 全 Closed 零公理，qbisec 核验保留交叉验证）；**CI 双环境修复**（`probe_partial.v` grid_conj 的 `rewrite !mult_INR` 在 mathcomp 2.6 下 LHS 不匹配——`muln` 新定义 ≢ `Nat.mul`——改 `rewrite mulnE` + 显式 `mult_INR` 参数，经验卡 E150）；**165 项审计重跑确认**（111 段 Axioms + 54 项 Closed，`Classical_Prop.classic` 零出现，post-M1.5 口径维持）。
> 修订摘要（v2.12→v2.13，2026-08-29，CS 战役定理化与代码基态对齐）：§5.6.6 压缩感知族新增 **CS-11/CS-12/CS-13/CS-14 四条目**（z 区四模块合计 **64 Qed / 0 Admitted**，全部独立编译 EXIT=0、归档 30模块 SHA 一致、未并入合并版 25——并入待合并版再生）：**CS-11 τ 裁剪最优性**（`probe_taugrid.v` 17 Qed：覆盖债精确量化（窗 [0,T] 能量恰 = (T+1)/n，债 1−(T+1)/n ∈ (0,1) 机器可计算）+ 支撑完备刻画（n ≤ T ⟺ ψ_n 完全支撑训练窗，iff）+ 裁剪证书单调（kept 子族行和 ≤ 全族，上界型证书不损）+ C-梯子稀疏化迁移 + 三连合成 `tau_prune_optimality`——randmax 裁剪实验的定理侧）；**CS-12 构造性孪生**（`probe_taugrid_cr.v` 13 Qed **零公理**：抽象接口 {R : ConstructiveReals} + 归一梯子 u（cos/复指数构造性未实现，接口与主线数学一致）；**严格序 CRlt 本身是 Set 值**（ConstructiveReals.v:88 库设计——柯西实数在序证明中存储信息），覆盖债界定定理以信息性形式 0 < debt < 1（Set 值 prod，证明项可提取）陈述；主定理结论 prod 型（信息性 (iii) 不能进 Prop 的 /\）；sigT 被类型系统强制；提取 `taugrid_cr.ml` 经 DkMLNative ocamlc 4.14.2 编译通过（柯西实例 cRealConstructive 具象化））；**CS-13 CS 生产线**（`probe_cs.v` 29 Qed：一致 RIP `cs2_rip_uniform`（(1−δ)‖c‖² ≤ ‖Φc‖² ≤ (1+δ)‖c‖²，δ = 4K(C) **∀s 一致**）+ ★s-sparse 唯一性 `cs3_energy_zero`/`cs3_unique`（C ≥ 10 时测量 y = y' ⟹ 系数 c = c'——测量端信息不丢失）+ embedding `cs6_embedding`（1−2K(C) > 0）+ spark 下界 `cs1b_spark`（spark ≥ n+1，Gershgorin 冗余路径收编为 CS-3 推论）+ 逐对相干 `cs1a_pair_bound`（≤ 2πq/(1−q)）+ ★近重复对爆炸 `near_dup_coherence_12`（coh 1 2 = 1/√2 精确值）+ `cs4c_explosion`（2μ = √2 > 1——s ≥ 3 时 Gershgorin 型 RIP 证书在含近重复对梯子上必然失效，"剪 503/255/127 应恶化"的定理侧镜像））；**CS-14 offset 无关性**（`probe_cs5.v` 5 Qed：跨网格对相干界 N/(2·min(j mod N, N−j mod N)) **右端不含偏移 δ**（同族平移差频相消，pair_dirichlet 接管）+ 黄金比护城河 1/(3d) + φ_gold ∉ ℤ（offset 语义非空）——ogrid 实验"跨网格对证书不含偏移"的定理侧）。**轨道定位**：构造性轨道用于公理独立性与可计算性验证（提取物携带 CRlt 的信息性 witness），不用于生产检查器（经典轨道更快）。定位（如实）：CS-11/13/14 为 Candès–Tao RIP 框架与 Elad–Bruckstein 判据在频率阶梯原子族上的机器检查 + 与本项目 randmax/ogrid/τ 三剪实验直接对接的新组合（覆盖债量化、近重复对爆炸、offset 无关性）；CS-12 为构造性轨道平行实现（序的 Set 值信息性 + 可提取 OCaml）。

> 修订摘要（v2.10→v2.11，2026-08-26，CI 双环境兼容）：**41 个正式模块头部注释清洗**（删除会话号/E0xx/交接路径等草稿注记，保留数学内容与纪律声明；规则沉淀于《合并友好编码规范》§6 + 经验卡 E149）；**mathcomp 前缀双环境适配**（本地 ssreflect.* / CI opam≥2.6 boot.*，E081/E082；合并版 CI 编译时 sed 转 boot 前缀）；**带前提引理 rewrite 显式化**（E114 追加：`CRsum_eq`/`Csum_ext`/`rewrite IH` 等 `P→eq` 引理的 rewrite 一律显式 assert 前提，消除 mathcomp 2.5/2.6 子目标顺序差异——ca_rip_cr 3 处 + probe_grid_ortho/pro 4 处 + probe_parseval 2 处）；**CI 缓存机制**（lib/merged .vo 经 actions/cache 按源 hash 缓存，推送秒级复验）；**30模块 归档 + 仓库已同步**（SHA-256 一致）。
> 修订摘要（v2.9→v2.10，2026-08-26，评审口径对齐）：**模块计数统一为实测 57 顶层 Module**（55 分区 + `ca_independence` 内 `independent`/`independent′` 2 附加，审稿实测；此前 55 为分区数）；**声明计数注明口径**（269 = Lemma+Theorem 口径，区别于 316 顶层声明 / 272 Qed，三者一致）；**"165 项全零 classic"注明 post-M1.5 复核成立**（`PSA_audit.v` L108–121 勘误为 pre-M1.5 过时记录；`ExpSeries.exp_mono_le_noclassic` 已并入合并版 L63579/L63672/L63719，4 个注意力定理位于其后，`exp_increasing` 仅存于 ca_* 基础设施非审计目标；`sig_forall_dec`/`sig_not_dec`/`fext` 显式声明为可接受 Reals 基底、非 `Classical_Prop.classic` 公理）；**附录 A 补 `probe_nearcoll.v`**（承载 `golden_near_collision_gold`）；**构造性轨道贡献在贡献清单中突出**（纯 ConstructiveReals、零经典公理，方法论对照）。
> 修订摘要（v2.8→v2.9，2026-08-26）：**M4 可判定性溢价主定理构造化收官**（`probe_decidability_premium_cr.v` 并入合并版 25 模块 55/55：Gram 相干行和 ≤ 63/80 + 反射界 21/16 + 溢价 5/3，`m4_decidability_premium : {w & CRle w (63/80)}` Set 层 sigT 定理，核心 `m4_CRinv_le_contravar` 纯构造反变单调，Print Assumptions 全 Closed）；**合并版 24 修复 G_MORE 遗漏**（`_merge_ca.py` p24 补 G_MORE，恢复 49 模块归档口径）；合并版 25 = 57 顶层 Module（55 分区，原 53 分区 + s7_s9_mono + decidability_premium_cr）；全量编译 41 独立模块 + 23/24/25 合并版 EXIT=0；30模块 归档 SHA-256 同步。
> 修订摘要（v2.7→v2.8）：§5.6.6 压缩感知族新增**检查器充要刻画**（G-3，`g3_certifiable_iff` + `g3_row_bound_mu`，probe_g3_criterion.v 5 Qed：反射检查器通过 ⟺ 每行精确相干行和 ≤ p/q，把"检查器通过 ⟹ 框架界"从单向充分升级为 iff）与**可判定性溢价反例**（G-5，`g5_premium`，probe_g5_premium.v 35 Qed：存在具体阶梯 [3,7,15]——反射检查器拒（frame_check_instance=false）但精确 Gram 相干行和 ≤ 4/5（完整口径闭式 0.787043，与评估文档一致）——把 §5.2"假阴性 49.1%"叙事升级为具体机器检查反例，是 G-3 必要方向的直接见证）。G-3/G-5 未并入合并版（z 区探针待合并）。**追加（v2.8 修订，2026-08-25）**：§5.6.6 压缩感知族新增 **G-5 构造性三角资产**（纯构造性轨道：M1 构造性 π `probe_pi_cr_m1a` 25 Qed + `probe_pi_cr_m1b` 43 Qed（Leibniz 级数 + CR_complete，3.141 ≤ π ≤ 3.142）、M2 构造性 sin `probe_sin_cr_m2` 39 Qed（交替幂级数）、M3 构造性 sqrt `probe_sqrt_cr_m3` 59 Qed（Q 层二分，√21 ≥ 458/100、√105 ≥ 10246/1000）——零经典、零 Admitted、零自定义公理，Print Assumptions 全 Closed，**已并入合并版 `ca_merged_full_25.v`（57 顶层 Module = 55 模块分区，MERGE_EXIT=0）**）。定位：G-5 可判定性溢价主定理构造化版本的三角基座；**M4 可判定性溢价主定理已构造化完成（2026-08-26：`probe_decidability_premium_cr.v` 并入合并版 25 模块 55/55，Gram 相干行和 ≤ 63/80 + 反射界 21/16 > 4/5 + 溢价 5/3，核心 `m4_CRinv_le_contravar`（CRinv 反变单调纯构造），Set 层 sigT 最终定理 `m4_decidability_premium : {w & CRle w (63/80)}`，Print Assumptions 全 Closed——相干缺口闭合的构造性收官）**。**代码-论文漂移标注（✅ 已修复 2026-08-25）**：G-2（mu_adj 相变）曾在 src 重新生成的 24/25 中缺失（_merge_ca.py G_MORE 列表缺 probe_g2_mu_adj）——已补入 `_merge_ca.py`（G_MORE + G_MORE_CLASSIC），重新生成合并版 25 = **87588 行 / 57 顶层 Module（55 模块分区）**，`G2MuAdj` 三定理（mu_adj_decreasing / mu_adj_phase_transition / mu_adj_asymptotic）恢复并入（模块 49/55），**MERGE_EXIT=0 验证通过**；30模块 归档已同步（SHA-256 一致）。（v2.6→v2.7）：§5.6.6 压缩感知族新增**加权阶梯范数精确闭式**（G-1，`G1_norm_closed`，probe_g1_norm_closed.v 21 Qed：任意 M 组合平方范数精确等式，交叉项 K_W 用单对 Dirichlet 核比闭式替换——根治审稿 A-1/B-1 的 12.5× 口径混用，G-2/G-5/G-6 前置）与**相邻带相干渐近闭式 + 相变定理**（G-2，`mu_adj_decreasing`/`mu_adj_phase_transition`/`mu_adj_asymptotic`，probe_g2_mu_adj.v 36 Qed：μ_adj(r)=√r·sin(π/r)/(π(r−1)) 定理化——**真正新数学**，相变点 r*（μ_adj=4/5，≈1.30）经 π<17/5 上界（sin_bound 0 阶）+ IVT_interv 夹逼，落实 B-7 强叙事）。G-1 并入合并版 48 模块、G-2 并入 49 模块，全量合并编译 EXIT=0。（v2.5→v2.6）：§5.6.6 压缩感知族新增**字典最优性⟹恢复保证合成定理**（G-8，`CRg8_recovery_synthesis` + `CRphase_window_nonempty`，构造性轨道：Welch 下界（平方形态抽象前提）+ F5 唯一性窗口（μ(|T1|+|T2|−1)<1）⟹ 两稀疏表示必相同，相图窗口非空参数条件 (M−N)T² < N(M−1)，6 Qed 零经典，Print Assumptions 双定理 Closed under the global context）。同时并入同事 F5 全文件（probe_uncertainty_cr.v 35 定理，此前仅以条目形式入文）与 F4 经典 Welch 界（probe_welch.v，模块 45）。（v2.4→v2.5）：§5.6.6 压缩感知族新增**唯一性⟹恢复正确性骨架**（F7/R4，`CRrecovery_correct_prefix`，构造性轨道：μ(M+1)<1 下两表示相等 ⟹ 系数逐点相等，差分线性 + RIP 界 + 收缩链）与**相干字典不确定原理**（F5，`CRuncertainty_principle`，构造性轨道：μ(|T1|+|T2|−1)<1 下两稀疏表示相等 ⟹ 系数逐点相等，支撑大小口径 1+1/μ，35 定理零经典）。（v2.3→v2.4）：§5.6.6 压缩感知族新增**行和→RIP 桥接**（F3）——`probe_row_rip.v`：行非对角和假设（Σ_{j≠i}|⟨u_i,u_j⟩| ≤ μ_row）⟹ k-原子 RIP（δ_k = (k−1)·μ_row，`row_rip_bound_M`，比两两相干 μ 版更紧：μ_row ≤ M·μ_pair），9 Qed 零公理，并入合并版 44 模块。v2.3 为 C=4 实例拼接（A2：`C4_sparse_uniqueness_3`，μ=11289/33920 < 1/3 ⟹ 3 原子 [3,13,53] 稀疏唯一恢复）；v2.2 为 k-原子 RIP（构造性轨道 ca_rip_cr.v，29 Qed 全 "Closed under the global context"，**2026-08-23 深夜同事补 P5 收缩链后现 33 定理**）。

---

## 摘要

我们提出一个 Coq 形式化开发，覆盖"可认证稀疏门控注意力"在几何结构化频率基上的解析核。开发在**两条正交的认证轨**上证明——表示稳定性轨（(i)–(iii)）与注意力扰动轨（(iv)–(v)），两轨之间无单一依赖链：(i) 一个确定性贪心门控，从任意有序索引集提取通过可判定稀疏增长检查的子集；(ii) 选定子基上成对相干衰减 $\le 1/(\sqrt{C})^{|i-j|}$ 与 Gershgorin 型框架界 $(1\pm\mu)\|c\|^2$；(iii) 行截断能量预算；(iv) softmax 在 $\ell_\infty$ logit 扰动下的 $\ell_1$ 稳定性；(v) 认证注意力近似定理：若每行丢弃谱能量 $\le \varepsilon$，注意力输出偏差至多 $(e^{2\sqrt{\varepsilon}}-1)\cdot V_{\max}$。所有门控与检查器函数提取为可执行 OCaml/Python，并与 Coq 计算参考值交叉核对（24/24）。

对具体几何阶梯 [3,13,53,213]（C=4），我们证明实例证书 `certified_c4_frame_bounds`：框架界 [1/5, 9/5]（μ=4/5），其中每个常数都是经超越界单侧支配得到的有理数（floor-sqrt、Jordan 不等式、Dirichlet 核）——证书层为可判定有理算术，可直接提取。证实例证书模式由反射检查器 `frame_check_instance` 推广到**任意**阶梯（μ≤4/5 的可判定**充分**判定——保守健全，系统扫描假阴性 49.1%；提取为带原生整数镜像的 OCaml）；其健全性定理 `frame_check_instance_sound` 已证明：**Coq 内**检查器通过 ⟹ Gershgorin 框架界。#### 6.1 运行时检查器的威胁模型

**运行时保证（如实限定）**：Coq 内健全性定理针对 nat 版本；运行时 int 镜像与 Coq 定义的等价性为逐行镜像 + FFI 24/24 交叉校验（非机器证明），且仅在有限整数范围（中间量 < 2^53、累积分母 < 2^63）内与 Coq 语义一致——"运行时检查器带机器证明健全性"精确指 Coq 内判定函数，运行时实现经交叉验证但未形式化验证（§6）。

对实证配套（论文 B）的**性能最优的结构化阶梯** [3,7,15,31,63,127,255]（论文 B 的强几何基线），一个表示级复合界（认证核 [3,15,63,255] 的 μ=4/5 + 边带能量预算 + 相干交叉项界）是本开发的展示定理 `champion_e5_composite_certificate`（Qed）：对七带基函数证明 $(S-\mathrm{coh}_{e5}) \le \|F\|^2 \le (S+\mathrm{coh}_{e5})$——**基表示稳定性界**，非注意力分数、学习投影或外推 PPL；通向论文 B 实证 PPL 增益的桥梁是经验观察而非形式化推论，该证书与实证性能最优方案（psi-rope-rand，随机阶梯在证书域之外）**正交**。审计含 165 项 Print Assumptions（RC=0，零 Admitted，完整 165/165 运行日志随稿），**全部 165 项在应用层零 `Classical_Prop.classic`**（exp 单调性走幂级数路线，无中值定理；post-M1.5 复核成立）；唯一公理为 Dedekind 实数基础设施（sig_not_dec、sig_forall_dec、函数外延性）——实数构造固有的非构造性选择类原则，属可接受 Reals 基底，**非本开发应用层引入、非 `Classical_Prop.classic` 公理**。"端到端"主张有明确边界：认证链覆盖门控→框架界→截断能量→softmax 稳定性→注意力近似；不覆盖学习权重的数值稳定性、Q/K/V 投影、多头拼接或 LayerNorm（"verify the analytic kernel, learn the rest"）。

在认证管线之上，本开发进一步刻画**可证明性边界**（§5.6）：对 μ≤4/5 的保守检查器口径，稠密覆盖与可判定认证**互斥**——超过 9 个相位完备带覆盖 [3,511] 的阶梯必然被拒绝（`pareto_law_N511`，几何增长禁止 + 鸽笼组合论证，增长常数 c≈1.8501）；随机版负定律以高概率成立（同箱带对必触发拒绝，7 带 ≥ 96%、8 带 ≥ 99%，生日-箱计数）。我们同时形式化论文 B τ/碰撞机制的碰撞距离框架：精确碰撞当且仅当角度有理（全构造性 iff，最小距离 = 分母闭式）、无理偏移（黄金比）永无精确碰撞且近碰撞被 1/(3d) 半径挡住、线性偏置核（ALiBi）无碰撞端点——"认证—可证明性边界—碰撞/分辨率刻画"三角被机器检查覆盖（§5.6.4，含 U5 黄金近碰撞半径）。

**压缩感知（§5.6.6，v2.2 升级为 k-原子 RIP，v2.3 完成实例拼接，v2.4 新增行和→RIP 桥接，v2.5 新增唯一性骨架与不确定原理，v2.6 新增相图合成 G-8）**：频率阶梯原子族在**通用层**满足单位范数 → **k-原子 RIP** → 稀疏唯一恢复定理，并在 **C=4 阶梯完成实例级拼接**（`C4_sparse_uniqueness_3`：μ=11289/33920 < 1/3 ⟹ 3 原子 [3,13,53] 稀疏唯一恢复）——`psi_norm_one`（‖ψ_n‖=1）、`rip_bound2`（RIP(2,μ) 基元）、**`CRrip_bound_k`（k-原子 RIP 主定理，构造性轨道 `ca_rip_cr.v`：0 ≤ μ、单位范数、两两相干 ≤ μ ⟹ |‖Σ_{j≤M} c_j·u_j‖² − Σc_j²| ≤ μ·(M+1)·Σc_j²，纯构造性实数 Stdlib ConstructiveReals——Set 层 CRcarrier + Prop 层 CRle/CRlt，零经典公理、零 Admitted，29 Qed 全 "Closed under the global context"，同事补 P5 收缩链后现 33 定理）**、**`row_rip_bound_M`（行和→RIP 主定理，经典 R 轨道 `probe_row_rip.v`：行非对角和 ≤ μ_row ⟹ |‖Σ_{j≤M} c_j·u_j‖² − Σc_j²| ≤ μ_row·M·Σc_j²，δ_k=(k−1)·μ_row，9 Qed 零公理）**、`sparse_uniquenessM`（**μ·(M+1) < 1 ⟹ 窗口内零组合 ⟹ 系数全零**，M+1 原子稀疏表示唯一）、**`C4_sparse_uniqueness_3`（C=4 实例，probe_c4_instance.v：六对相干上界组装 μ=11289/33920 < 1/3，3 原子唯一恢复）**、**`CRrecovery_correct_prefix`（R4 唯一性⟹恢复正确性骨架，构造性轨道 `probe_recovery_cr.v`：μ(M+1)<1 下两表示相等 ⟹ 系数逐点相等）**、**`CRuncertainty_principle`（F5 相干字典不确定原理，构造性轨道 `probe_uncertainty_cr.v`：μ(|T1|+|T2|−1)<1 下两稀疏表示相等 ⟹ 系数逐点相等，支撑大小版 1+1/μ，35 定理零经典）**、**`CRg8_recovery_synthesis`（G-8 字典最优性⟹恢复保证合成，构造性轨道 `probe_g8_synthesis_cr.v`：Welch 下界（平方形态抽象前提）+ F5 唯一性窗口 ⟹ 两稀疏表示必相同；相图定理 `CRphase_window_nonempty`：窗口非空参数条件 (M−N)·T² < N(M−1)，6 Qed 零经典）**——把「框架界（1D 无条件基）+ 频率阶梯」的理论优势从表示稳定性推进到稀疏恢复（probe_incoherence 48 Qed + ca_rip_cr 33 Qed + probe_c4_instance + probe_row_rip 9 Qed + probe_recovery_cr + probe_uncertainty_cr 35 Qed + probe_welch 13 Qed + probe_g8_synthesis_cr 6 Qed，构造性轨道独立验证）。

**关键词**：形式化验证；Coq/Rocq；稀疏注意力；框架理论；Gershgorin 界；反射检查器；程序提取；构造性数学

---

## 1 引言

稀疏/近似注意力方法（top-k、KV 逐出、低秩投影）全部缺乏误差证书。形式化方法可在"解析核"层提供保证——"验证解析核，学习其余"（verify the analytic kernel, learn the rest）。本开发的贡献（与代码一一对应）：

1. **确定性门控的形式化**（GreedyGate，28 引理）：原文概率门控前提不可满足（$(INR\,N)^2 p^2 < 1$ 恒假，反例已录），我们裁决并证明确定性平方门 M=C² 是**本文选定模型下**的可行路线（严格表述限定于该概率门控前提框架内，不声称一般意义唯一性）；
2. **有限化守卫衰减界**（PSA_Pipeline）：全局增长前提 → 运行时可判定检查，系数 2/√C 与 tight 1/√C 两版；
3. **行截断能量预算**（RowTruncation）与 **softmax 稳定性**（SoftmaxStability，$\|\mathrm{softmax}\,z - \mathrm{softmax}\,z'\|_1 \le \exp(2d) - 1$；v2.14 勘误对齐代码 `softmax_l1_bound_exp` 实形态，旧稿 2(e^d−1) 高估紧度）；
4. **认证注意力近似**（CertifiedAttention）：谱能量 ≤ ε ⟹ 输出偏差 ≤ $(e^{2\sqrt{\varepsilon}}-1)\cdot V_{\max}$；
5. **实例证书**（Gershgorin + InstanceCertificate）：对 C=4 阶梯 [3,13,53,213] 证明框架界 [1/5, 9/5]（μ=4/5）——参数化最坏情形 1±4K(C) 在 C=4 空洞成立、需 C>25 的问题就此终结；
6. **有理支配方法论**（实现贡献）：证书全部常数经 floor-sqrt / Jordan / Dirichlet 单侧松弛化为有理数，`compute; field` 封口——零数值策略、零区间算术、可判定、可提取；
7. **可执行提取**：门控/检查器 → OCaml（psa_guard.exe）→ Python FFI，24/24 参考值对齐；
8. **反射检查器及其健全性**（FrameCheckInstance）：`frame_check_instance` 把"任意阶梯 → μ≤4/5"做成可判定**充分**判定（保守健全，系统扫描假阴性 49.1%），提取为原生整数镜像（与 Coq 定义逐行同构）；健全性定理 `frame_check_instance_sound`（Qed）证明**Coq 内**判定通过 ⟹ Gershgorin 框架界——检查器带 Coq 内健全性证明，运行时 int 镜像为交叉验证（未形式化验证，§6）；
9. **基表示稳定性复合证书**（ChampionCertificate，核心展示定理）：论文 B 的七带基线阶梯获得机器证明的平方范数复合界 $(S-\mathrm{coh}_{e5}) \le \|F\|^2_{255} \le (S+\mathrm{coh}_{e5})$——当反射检查器返回 false（健全但非完备）时，核-边缘分解交付的部分证书在此收束为七带整体完整证书；这是对反射器不完备性的系统性工程补丁，作为方法论贡献单列；
10. **高维组合性演示**（2D-wide/3D/4D）：同一 `abstract_unconditional_basis` 骨架逐轴实例化到任意维——形式化方法学在高维逻辑闭合（"Theoretically Composable, Practically Non-Tight"）；
11. **构造性实数轨道（方法论对照贡献）**：`ca_rip_cr.v`（33 定理，k-原子 RIP 纯构造）+ 构造性 π/sin/sqrt 三角（`probe_pi_cr_m1a/m1b` 68 Qed、`probe_sin_cr_m2` 39 Qed、`probe_sqrt_cr_m3` 59 Qed，Leibniz 级数 + CR_complete、交替幂级数、Q 层二分）+ **可判定性溢价构造化收官**（`probe_decidability_premium_cr.v`，`m4_decidability_premium : {w & CRle w (63/80)}` Set 层 sigT 定理）——全部走纯 ConstructiveReals（Stdlib），**零经典公理、零 Admitted**（29 Qed 全 "Closed under the global context"，同事补 P5 收缩链后现 33 定理），与经典轨道（R 层）形成真实的方法论对照：同一证书定理在两种实数基础下分别机器检查；
12. **覆盖边界**："端到端"精确指覆盖链门控→框架界→截断能量→softmax 稳定性→注意力近似；不在覆盖内：学习权重（W_Q/W_K/W_V/W_O）、Q/K/V 投影与多头拼接、LayerNorm/激活的数值稳定性、残差连接的累积误差。

## 2 背景

- **ψ 基**：$\psi_n(k) = (1/\sqrt{n})\cdot e^{2\pi i k/n}$，有限支撑（$k \ge n$ 时为 0）。
- **阶梯生成器**：$n_{j+1} = \max(C\cdot n_j + 1,\, n_j + 2)$（非精确几何——证书必须认证实际值，这是需要运行时检查器而非纸面公式的理由）。
- **三处语义勘误**（线性 vs 平方门、`<=?` vs `<?`、≥2 并集）——每处附反例，体现形式化对原草案的纠错价值。
- **一处常数级勘误（3D 张量基，已修正）**：2D 引擎的离对角界常数 K0 = Rmax 8C³/4 在 3D 等轴退化配置（两轴索引相同、仅第三轴差 ≤6）下不可证——归一化三重内积可逼近 1，而 /4 常数只给 1/2。3D 模块改为 K0′ = Rmax 8C³/2（退化配置恰好紧，worst case = 1）。

## 3 形式化开发总览

模块图（PSA_framework.v，6659 行，18 个 Module，269 顶层 Lemma·Theorem（272 Qed 口径），零 Admitted）：

```
RuntimeGuards → SeqProps → PSA_Pipeline → GreedyGate → RowTruncation →
PipelineEndToEnd → ExpSeries（M1.5 级数重写，§7）→ SoftmaxStability →
CertifiedAttention → Gershgorin → InstanceCertificate（M4）→
M4bLengthConsistency（长度一致性，∀N≥214）→ T8CoreCertificate（T8 复合证书核）→
FrameCheckInstance（反射检查器 + soundness）→ ChampionCertificate（复合表示稳定性界，§5.3）→
FrameCheck2DNarrow（2D 窄轨反射化，§5.5）→ UnitaryInvariance（A2 酉不变性，§5.3）
```

统计：**165 项** Print Assumptions 审计（PSA_audit.v，RC=0，完整运行日志 `审计证据/audit_run_20260826_full.txt`，165/165 块随稿 co-locate）；**全部 165 项未直接使用 `Classical_Prop.classic`**（排中律宏零出现；公理脚印含 sig_not_dec/sig_forall_dec/fext——非构造性选择类公理，非"零经典"）——**post-M1.5 复核成立**（`ExpSeries.exp_mono_le_noclassic` 已消除 exp 单调性经 Rpower/MVT 继承 classic 的唯一入口，4 个注意力定理位于重写之后；`PSA_audit.v` L108–121 勘误为 pre-M1.5 过时记录）；**零 Admitted**（剥注释后 grep 命中 0）；零自定义公理；外部依赖仅 mathcomp + Coquelicot；Rocq 9.0.1。**审计范围与合并版全基态的边界（v2.15 精确化）**：165 项审计的对象是 `PSA_framework.v` 应用层定理；合并版 `ca_merged_full_25.v` 其余模块中，`mu_adj_phase_transition`（μ 单调 ⟹ 相变存在性定理，合并版 L81603 审计）的公理脚印**含完整排中律 `classic`**（CI 与本地 2.5 编译日志一致确认）——故"零 `Classical_Prop.classic`"结论**限于 165 项审计范围**，不覆盖合并版全部定理；应用层的注意力证书/框架界/反射检查器定理链不受影响，涉及 classic 的相变存在性结果属实证机制的定性刻画。**审计分层口径（v2.16）**：165 项输出块 = **54 项 Closed under the global context + 111 项 Dedekind 三公理脚印**（sig_not_dec/sig_forall_dec/fext，实数构造固有）；**构造性轨道不在此 165 项内**——`ca_rip_cr.v`（33 定理）、`probe_uncertainty_cr.v`（35 定理）、`probe_taugrid_cr.v`（13 定理）各有独立 Print Assumptions 审计且全部 Closed（零公理），其清洁度高于应用层均值。

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

softmax_l1_bound_exp : ‖z−z'‖∞ ≤ d → ‖softmax z − softmax z'‖₁ ≤ exp(2·d) − 1
  (* v2.14 勘误对齐代码 PSA_framework.v:2216-2220 实形态；原稿 2(e^d − 1) 系紧度高估 *)

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
- **检查器的保守性（充分非必要）**：`frame_check_instance = true` 是框架界的充分非必要条件——floor-sqrt 有理松弛的保守因子约 1.5×，存在满足 Gershgorin 条件但因保守上界超 4/5 而被误拒的合法阶梯（假阴性）。典型真例证：[3,7,15]（起点最低的倍增三带）精确行和 0.7870 ≤ 4/5（满足框架条件），但有理保守界 1.3125 > 4/5 被误拒（可判定性溢价 ≈1.67）；而七带 E5'' 精确行和 1.2287 > 4/5，检查器判 false 是**真阴性**（真值超阈），不在误拒之列。正是这一不完备性使**复合证书成为必要**。宁可误拒、绝不放行的保守取向是可判定性的设计选择。

- **充要性精确层口径（G-3）**：`probe_g3_criterion.v` 的 `g3_certifiable_iff` 证明——在精确有理算术层，检查器通过与否**等价于** Gershgorin 行和阈值条件；假阴性全部来源于 floor-sqrt/Jordan 等**可判定松弛层的保守性**，而非检查器逻辑的完备性缺口（[3,7,15] 即保守性见证：精确行和 0.7870 ≤ 4/5 被误拒，`probe_g5_premium.v` 机器验证）。- **反向警示（形式化审查强化）**：检查器返回 `false` **不是**不安全证书——它只表明保守有理界不足以证明 Gershgorin 条件；被误拒的合法阶梯仍可由复合证书覆盖（但**七带 E5'' 不属此列**：其精确相干行和（证书口径①）为 **1.2287 > 4/5**，检查器判 false 是**真阴性**（真值超阈）而非误拒；复合证书 `champion_e5_composite_certificate` 对 E5'' 的下界在单位系数下**空洞**（S=7、coh_e5=14.21、下界 −7.21 < 0），是宽松复合界，**不构成"0.135 实质可认证"或"紧证书"的证据**——该界是基函数范数稳定性界，非框架下界）。"检查器通过 ⟹ 框架界"成立，"检查器失败 ⟹ 不安全"不成立。
- **系统扫描（114 阶梯 × 5 族）**：通过 35（30.7%）、假阴性 56（全量 49.1%，占拒绝 70.9%），集中于"有用"族（C=2/3-sparse、几何奇带）——"可判定性溢价"是当前有理松弛实现的保守性代价（局限），收紧方向：`cert_optimize`、Zarith 大整数。

**证书覆盖地图（阶梯实例 × 认证状态 × 实证对照）**：

| 阶梯实例 | 直接框架界 (μ≤4/5) | 复合证书 | 检查器状态 | 实证 8× PPL | 覆盖结论 |
|---|---|---|---|---|---|
| [3,13,53,213] | ✅ `certified_c4_frame_bounds` | — | true | 12.75 | 4 原子能量有界；3 原子稀疏唯一 |
| [3,15,63,255] | ✅ `certified_t8_core_frame_bounds` | — | true | — | T8 认证核覆盖 |
| [3,7,15,31,63,127,255] | ❌ 精确行和 1.2287 > 4/5 | ✅ `champion_e5_composite_certificate` | false（真阴性） | 12.40 | 基表示稳定性界（单边上界） |
| [3,7,15] | ❌ 检查器 false | — | false（**假阴性**） | — | 精确行和 ≈0.787 ≤ 4/5，被保守界误拒（G-5 见证） |
| 随机 log-uniform [3,511] | ❌ | — | whp false | 6.45 | 旋转族内最优；证书仅 ℓ² 线性无关 |
| ALiBi（非阶梯） | ❌ | ❌ | — | **4.47** | 全局最优，无证书，非周期偏置 |
| grid [3,5,17,…] | ✅ μ=0 正交证书 | ❌ | — | 25.66 | 证书 ≠ 性能的反例锚点 |

（PPL 列为配套论文 B 的实证数据；证书列为本开发形式化结果——两轨无形式化桥梁，见 §1。）

### 5.3 与实验的对齐（multi-seed + T8 + 复合证书 + 酉不变性）

3 个种子实验中 E5'' 七带与 C=4 并列最优（8× 均值 12.40±0.74 vs 12.75±0.34）；C=2 第三（13.84）；C=3 系统性最差（22.86）。最优表现对论文 A 免疫：

- **直接证书**（C=4）：`certified_c4_frame_bounds` 直接覆盖；
- **T8 复合证书**（E5''）：隔带子核 [3,15,63,255] 的 `certified_t8_core_frame_bounds`（μ=4/5）覆盖最优阶梯的认证核；
- **复合表示稳定性界**（ChampionCertificate）：顶层组合定理 `champion_e5_composite_certificate`（Qed，零 classic）——代码实际证明的目标形状（全矩阵相干加权）：`length coeffs = 7 → (S − coh_e5 c) ≤ ‖F‖²_{255} ≤ (S + coh_e5 c)`，其中 coh_e5 为 21 对上三角 δ 表经 `term_bound_upper/lower` 加权得到的对称相干交叉项界。**非平凡性说明（如实）**：coh_e5 为符号化加权界（逐对 δ 表 `delta_e5` 在代码中，此处未逐对列出）；七带精确相干行和（证书口径①）为 **1.2287 > 4/5**，单位系数下 coh_e5 = 14.21、下界 S−coh_e5 = **−7.21 空洞**——该复合界是宽松的基函数范数稳定性界，**不构成框架下界，也不等于七带相干行和**（"0.135 实质可认证"系错误数值，已更正）；该证书为**基函数范数稳定性保证**，与注意力输出/外推 PPL 无关；且**与 `certified_attention_approx` 不组合**——后者刻画谱能量丢弃 ⟹ 注意力输出扰动（KV 逐出场景），前者刻画基表示范数稳定性（与注意力 logits 无推导关系），两个定理簇相互独立。构件链：15 个新 pair 界 → 内积/范数引理 → δ 表（21 对）→ `coh_delta_bound`（42 方向）→ 上下界项 → 主定理。注意：早期草拟的"核带框架 + 边带能量"分段形式是装配前的设计稿，最终实现收敛为单一定理下的对称界。
- **酉不变性（已机器检查）**：旋转是酉变换，对任意酉算子 U 与系数向量 c，$\|\sum c_i U\psi_i\|^2 = \|\sum c_i \psi_i\|^2$——框架界/衰减界/证书自动覆盖旋转版本（论文 B 的"旋转组"）。Module UnitaryInvariance：`unitary_invariance_point`（U 保内积 ⟹ 范数不变）+ 位置索引 psi-rope 实例 + 显式 RoPE 实例 `unitary_invariance_psi_rope_theta`（`u k := Cexp (0+i·INR k·θ k)`，`Cexp_unit_mod` 证单位模）。实验的 2×2 块旋转矩阵（`apply_rope_theta`）与复数乘法 $e^{i\theta}$ 是同一酉群的同构表示（SO(2)≅U(1)），实/虚部逐行对应已显式机器检查（`rope_matrix_real/imag/eq`，零 classic）。注：原"每带乘 u_i"逐点版本为假命题（交叉项要 $u_i = u_j$；反例 u0=1, u1=−1, g0=g1=1），未并入。范围限定：酉不变性适用于**特征表示的范数层**；不保证学习到的 Q/K 投影下注意力 logits 不变。
- **相干熵桥接**（PhaseCoherence，`coherence_controls_attention`，Qed，零 classic）：对任意相干核 K（$|K_{ij}| \le \mathrm{coh}$）与系数差 $\ell_1 \le \delta$，logit 扰动 $|z_i - z'_i| \le \mathrm{coh}\cdot\delta$，组合 softmax 稳定性得 $\|\mathrm{softmax}\,z - \mathrm{softmax}\,z'\|_1 \le e^{2\cdot\mathrm{coh}\cdot\delta} - 1$——相干上界 ⟹ softmax 输出 TVD 界的抽象桥梁。当前为已证抽象桥梁 + 未实例化状态；实证支撑：ΔCoh 仅在稀疏几何族内排序（4 点 R²=0.982），13 点扩充后跨族崩溃（max 型 R²=0.101）——相干性定性结论保留、定量预测收缩为族内指标。
- **核漂移口径（已机器检查，2026-08-22）**：`kernel_drift_controls_attention`（PhaseCoherence，coqchk 独立复核）——核逐点漂移 $|K_{ij}-K'_{ij}| \le \mathrm{dc}$（全 i,j）且系数 $\ell_1 \le \mathrm{dd}$ ⟹ softmax 输出 $\ell_1$ 距离 $\le e^{2\cdot\mathrm{dc}\cdot\mathrm{dd}} - 1$（与上条互补：系数漂移×固定核 vs 固定系数×核漂移，覆盖长度外推/蒸馏/量化场景）；对窗口无关核族（网格/偏移网格在任意 $a\cdot N$ 长度核相同）Δ=0 退化为 TVD 界 0（`kernel_identical_tvd_zero`）。**常数演进线**：4K → 2K（`psi_unconditional_basis_tight`）→ μ=0（网格端点）；`abstract_unconditional_basis` 可用 Riesz 序列稳定性语言重述（张成族系数 $\ell^2$ 范数的 $(1\pm M_{\mathrm{bound}})$ 等价）——文本级重述，不改变机器检查内容。

### 5.4 维度推广：三维/四维/2D-wide 张量积范数上界（组合性演示；下界平凡，非框架下界）

价值在于**组合性演示**：同一 `abstract_unconditional_basis` 骨架逐轴实例化到任意维。常数非紧性与未提取状态是两条独立限制，共同构成"存在性结果"而非"实用工具"的定位。

- **3D**：φ3D(a,b,c)(k) = γ⁻¹ψ_aψ_bψ_c，M_bound = K0′·((1+4K_C)³−1)，K0′ = Rmax 8C³/2。全量编译 RC=0，审计 10 项零 classic。数值紧度：`M_bound_3d 4 = 3968`（≫2 ⟹ 3D 证书目前仅作为存在性证明）。松弛可机械分解为两个正交因子：**编码因子 K0′ = C³/2 = 32**（等轴退化病理，格雷码类方案可望收回）与**行和乘积因子 (1+4K_C)³−1 = 124**（维数灾难主导项，要联合行和界突破）。
- **4D**：`ca_basis_4d.v`（2073 行）已全部 Qed + coqchk 复验 RC=0；`M_bound_4d 4 = 19968`；16 分支常数引理再次机械确认 /4 常数的单轴退化不可满足性是**维数无关**病理。**使用限定（v2.15）**：3D/4D 的 M_bound 常数（3968/19968，≫1）**下界信息量为零，不得用于实际误差估计**——其价值仅在骨架复用（组合性演示与反射化路径），高维反射化判定器为未来工作。
- **2D-wide**：φ2D(i,j)(k) = γ⁻¹ψ_i(k)ψ_j(k)，**免 H_dom**（扁平 idx1≠idx2 ⟹ i1≠i2 ∨ j1≠j2，div/mod 解码唯一性）——宽轨家族中唯一免支配假设、可运行时判定的成员；`M_bound_2d_wide 4 = 768`（= 32 × 24）已 Qed，与论文 B §6 N 维公式 N=2 预测完全一致。
- **双轨设计**：窄轨（1D 实例证书 μ=4/5、2D K0=C³/4——收紧前提换常数减半，**实用证书**）与宽轨（2D-wide/3D/4D K0=C³/2——全覆盖换 ×2，**组合性/存在性定位**）。仅要 1D/2D 的场景采用窄轨。

### 5.5 退化 2D（单轴）反射检查器（FrameCheck2DNarrow）

> 更名注："2D 窄轨"实为**退化单轴**情形（仅 n₁=1 ∨ n₂=1 的 1D 参数化 2D），非 2D 通用格点检查器；评审建议更名 `Degenerate2DFrameCheck`/`1DParametric2DFrameCheck`——本文保留原模块名 `FrameCheck2DNarrow`（避免跨文档引用失效），全文按"退化单轴"语义引用；真 2D 格点的运行时反射化为未来工作。

- 覆盖范围（首句明示）：本模块**不覆盖真正的 2D 格点（n1,n2≥2）**——检查器只处理单轴退化配置，是 1D 情形在 2D 口径下的参数化反射化。
- 严格增长延拓 `seq_ext`：窗口内取 nth，窗口外按几何闭式延拓——把有限阶梯提升为全索引序列以满足骨架的全局增长前提。
- 可判定 H_dom `hdom_2d_narrow` + 反射检查器 `frame_check_2d_narrow` 与其健全性 `frame_check_2d_narrow_sound`（Qed）：判定通过 ⟹ 窄轨 2D（K0=C³/4 口径）Gershgorin 框架界。
- 点态组装 `tensor_product_unconditional_basis_pointwise`（Qed）：与宽轨 2D-wide 构成**双轨反射化闭环**。

## 5.6 可证明性边界与碰撞刻画（2026-08-22 新增定理族）

> 本族回答论文 B 的"性能-可证明性张力"：不是工程未达，而是**定理层面**的边界。全部模块零 Admitted、零自定义公理；ParetoLaw/P1Coherence/ParetoRandom 仅 Stdlib Reals 自包含；**z 区 8 探针（grid_ortho + parseval/partial/pairbound/rowsum/pairdirichlet/incoherence/c4_instance）已按 E091 模式 pro 化并入合并版**（mathcomp Require + lia 改 mathcomp 引理，2026-08-23），独立 + 合并双通过；其余 z 区探针按 z/ 独立编译验证。

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
- **τ 三分**（probe_taudicho，零公理）：碰撞质量 τ 的窗内/OOD/三分刻画。权威独立模块：`ca_tau.v` `tau_crop_mono`（N1≤N2 ⟹ Στ 裁剪单调，纯 mathcomp 零公理；2026-08-30 对齐补注，论文 B §8.4 经验律的定理侧）。
- **素数阶梯分辨率与最优性**（`src/CRTResolve.v` + probe_ladderlimit）：存在性 `prime_ladder_8` + `prime_ladder_8_pairwise_coprime`（8 素数链 [3,7,13,29,59,127,251,503]，两两互素）+ 分辨率 `crt_inj`（联合模单射，lcm ≈ 7.49×10¹² ≫ 8× 视界）+ **最优性 `no_nine_band_ladder`**（**[3,511] 不存在 9 元素素数阶梯**，贪心交换论证，贪心链 113/211/397 更紧）——素数叙事完整（存在性 + 分辨率 + 最优性），支撑论文 B 素数阶梯受控对照（prime-7 vs prime-8）。

### 5.6.5 分级证书、一般维张量与核漂移（z 区探针）

- **容错 Gershgorin**（probe_robust）：坏对每行 ≤ δ·n ⟹ 绝对行和 ≤ n·(μ+δ)；**μ+δ ≤ 4/5 ⟹ 通过帕累托阈值**——检查器从二元升为分级证书。
- **一般维张量**（probe_tensor）：N 轴张量积 off-diag 行和 ≤ **(1+r)^N − 1（∀N 闭式）**——论文 B §6 跨维推测得证（2D/3D/4D 为 N=2/3/4 特例）。
- **核漂移（T4 完全体，已并入 PSA_framework PhaseCoherence）**：`kernel_drift_controls_attention`——核逐点漂移 ≤ dc、系数 ℓ1 ≤ dd ⟹ **softmax ℓ1 TVD ≤ e^{2·dc·dd} − 1**（`coherence_controls_attention` 的核漂移姊妹定理）；`kernel_identical_tvd_zero`：K=K' ⟹ 界=0——网格族（任意 a·N 窗口核相同）"注意力核表示级不变性"的证书 0 端点。
- **ρ^{−3/2} 紧界三件套**（probe_pairbound ① + probe_rowsum ② + probe_witness ③，2026-08-22 全部 Qed）：逐对界 ‖⟨ψ_a,ψ_b⟩‖ ≤ sin(πa/b)·√(ab)/(2(b−a))（`pair_inner_norm`，Jordan 分母，逐对 Θ(ρ^{−3/2})）；行和重组 **`row_sum_3halfs`**：C-稀疏梯子任意行 ≤ 2π·C^{−3/2}/(1−C^{−3/2})，**`row_bound_C4`：C=4 行和 ≤ 2π/7 ≈ 0.898 < 1——1D C=4 从空洞（2>1，仅存在性）变真实框架界**；**见证封顶（③ probe_witness）**：见证对 (2,2C) 精确内积 `witness_exact` = sin(π/(2C))/√C，且 **`witness_sandwich`：(1−1/C)·[上界] ≤ 见证值 ≤ [上界]——上下界之比 ≥ 1−1/C，C→∞ → 1（Θ(C^{−3/2}) 紧性封顶，机器检查）**；常数演进线 4K → 2K → Θ(C^{−3/2})（紧）封顶。风险清单更新：求和窗口口径已对齐 Fpair（消除）；decay_bound 新界接口实例化待 src 侧；K0=32 高维联动不承诺。

**意义**：本族与 §5.1–5.5 认证链正交，构成"认证（正）— 可证明性边界（负定律）— 碰撞/分辨率刻画（机制）"三角；offset-grid（无理偏移）的证书保持（T1a/Parseval）、零精确碰撞（C5）与近碰撞护城河（U5）三半均机器检查。**配套实验已完成（论文 B §8.4，2026-08-22）**：offset-grid @4096 16.12±1.32——ogrid ≥ grid 确认（碰撞机制第 6 个正向判决）+ **证书免费性被证伪**（μ=0 精确正交 ∧ 零精确碰撞仍差 rand 2.4×）——与 P3 定理互证：**可证性（稀疏）与外推性（稠密）在实证与定理双轨分离**。

### 5.6.6 压缩感知：RIP 与稀疏唯一性（probe_incoherence.v，CS-1/2/3，2026-08-23 新增）

> 本小节把 §5.1–5.5 的「框架界/表示稳定性」推进到**压缩感知级**：频率阶梯原子族不仅
> 构成稳定框架，还满足**低相干 → RIP → 稀疏唯一恢复**的完整链条。51 Qed / 5 主定理 /
> 0 Admitted / 0 Axiom，已并入合并版（全量合并编译通过）。

- **原子规范（IC1）** `psi_norm_one`：1 ≤ n ⟹ ‖ψ_n‖²_{pred n} = 1——频率阶梯原子族单位范数
  （phi=rot 桥 + 零前缀 Csum 消除 + `phi_l2_norm` 闭式）。
- **RIP 基元（CS-2）** `rip_bound2`：μ-不相干单位原子（|⟨u1,u2⟩_W| ≤ μ）⟹
  |‖c1u1+c2u2‖²_W − (c1²+c2²)| ≤ μ·(c1²+c2²)——Gershgorin 型 RIP(2,μ) 界；支撑链
  `norm_sq_combo2`（2 原子范数平方显式展开：Σc² + 2c1c2⟨⟩）。
- **k-原子 RIP（CS-2′，构造性轨道，v2.2 新增）** `CRrip_bound_k`（ca_rip_cr.v，A1）：
  0 ≤ μ、单位范数（∀j≤M：‖u_j‖² = 1）、两两相干 ≤ μ（∀i≠j≤M：|⟨u_i,u_j⟩| ≤ μ）⟹
  |‖Σ_{j≤M} c_j·u_j‖² − Σ_{j≤M} c_j²| ≤ μ·(M+1)·Σ_{j≤M} c_j²——RIP(2,μ) 的 **k-原子
  泛化**（k = M+1，RIP 常数 δ_k = μ·(M+1)，AM-GM 聚合路径的保守界）；证明链：
  `CRrip_lower_M`（RIP 下界归纳）与 `CRrip_upper_M`（上界）经 `CRabs_def` 组合为
  绝对值界（组装引理 `CRrip_final_cr` / `CRrip_upper_final_cr` 全手动 CR 链，无 nra）。
  **纯构造性实数轨道**：Stdlib ConstructiveReals 抽象接口（Set 层 CRcarrier +
  Prop 层 CRle/CRlt），零经典公理（无 sig_not_dec/sig_forall_dec/fext）、零 Admitted，
  29 引理全 "Closed under the global context"；独立编译 EXIT=0 + 合并版（当时快照 44 分区，现合并版 25 = 57 顶层 Module）
  EXIT=0 + 30模块 SHA-256 一致。
- **稀疏唯一性（CS-3）** `sparse_uniquenessM`（主定理）：0 ≤ μ、单位范数、两两相干 ≤ μ、
  **μ·(M+1) < 1** ⟹ 窗口内零组合 Σ_{j≤M} c_j·u_j ≡ 0 ⟹ 系数全零——M+1 个原子的**稀疏表示
  唯一恢复**；证明链：`rip_lower_M`（RIP 下界归纳，Σc_j² ≤ l2 + μ(M+1)Σc_j²）→ l2=0
  （零组合）→ (1−μ(M+1))Σc_j² ≤ 0 → Σc_j² = 0 → `sum_sq_zero` 逐项归零；基元
  `sparse_uniqueness2`（M=1 最小实例）。
- **C=4 实例拼接（CS-3′，v2.3 新增）** `C4_sparse_uniqueness_3`（probe_c4_instance.v，A2）：
  C=4 阶梯 [3,13,53,213] 的**六对相干上界**（pair_3_13 ≤ 13/40、pair_3_53 ≤ 53/400、
  pair_3_213 ≤ 213/3500、pair_13_53 ≤ 689/2080、pair_13_213 ≤ 2769/20800、
  pair_53_213 ≤ 11289/33920，均已在 PSA_framework）经 ipW 对接组装为
  **μ := 11289/33920 < 1/3**（33867 < 33920）⟹ 前 3 原子 [3,13,53] 的两两相干 ≤ μ 且
  **μ·3 < 1** ⟹ `sparse_uniquenessM` 实例化（M=2）：窗口内零组合 Σ_{j≤2} c_j·ψ_{v_j} ≡ 0
  ⟹ c₀=c₁=c₂=0——**3 原子稀疏唯一恢复实例**。审计：仅 Dedekind 实数基础设施
  （sig_not_dec/sig_forall_dec），零自定义公理、零 Admitted。
- **行和 → RIP 桥接（CS-2″，经典 R 轨道，v2.4 新增）** `row_rip_bound_M`（probe_row_rip.v，F3）：
  **行非对角和假设**（∀i≤S M：`row_sum (S M) u W i` = Σ_{j≤S M, j≠i}|⟨u_i,u_j⟩| ≤ μ_row，对角排除）⟹
  k-原子 RIP（k = M+1，M+1 原子）：
  |‖Σ_{j≤M} c_j·u_j‖² − Σ_{j≤M} c_j²| ≤ μ_row·M·Σ_{j≤M} c_j²——**δ_k = (k−1)·μ_row**，
  比两两相干 μ 版（δ_k = μ·k）**更紧**：μ_row ≤ M·μ_pair（单对 ≤ 行和，行和一次求和直接
  控制该行全部非对角交互，而两两相干版需逐对聚合）；证明链：`row_sum`（行非对角和定义）→
  `row_cross_bound`（交叉项界：2|c_{SM}|·|⟨comboM(S M), u_{SM}⟩| ≤ μ_row·(Σ_M + c_{SM}²)，
  经 ipW_combo_l + 三角 + 逐项 AM-GM(2|a||b| ≤ a²+b²) 分配行和 + 单对≤行和）→
  `row_rip_lower_M` / `row_rip_upper_M`（RIP 上下界归纳，IH 的行和前提经**前缀单调**
  （sum_f_R0_le_sub）从 S(S M) 层截取到 S M 层）→ `row_rip_bound_M`（`Rabs_le` 组合
  lower+upper）。**9 Qed / 0 Admitted / 0 自定义公理**，独立编译 EXIT=0 + 合并版
  （44 分区，当时快照；现合并版 25 = 57 顶层 Module）EXIT=0。**对接**：§5.6.5 的 `row_bound_C4`（C=4 行和 ≤ 2π/7 ≈ 0.898 < 1）⟹
  k=2（M=1）时 δ = μ_row·1 = 0.898 < 1——C=4 前 2 原子的行和版 RIP 常数严格小于 1。
- **唯一性 ⟹ 恢复正确性骨架（CS-4，构造性轨道）** `CRrecovery_correct_prefix`（probe_recovery_cr.v，F7）：
  前缀支撑版：0 ≤ μ、单位范数、两两相干 ≤ μ、**μ·(M+1) < 1** ⟹ 同一信号两个表示
  Σ_{j≤M} c_j·u_j == Σ_{j≤M} c'_j·u_j ⟹ ∀j≤M: c_j == c'_j——稀疏唯一性定理的
  **构造性对偶**（R4 主定理，"唯一性 ⟹ 恢复正确性"确定性骨架，不碰 OMP 算法本体）；
  证明链：差分线性（R0）→ 差组合零（R1）→ 差组合范数平方零（R2）→ 差组合 RIP 界
  （R3，`CRrip_bound_k` 实例化）→ 收缩链（R4：`CRle_scaled_le_zero`
  （Σd² ≤ μ(M+1)Σd² 且 μ(M+1)<1 ⟹ Σd²≤0）+ 平方和零 ⟹ 逐项零 + ring 收尾）；
  零经典公理（"Closed under the global context"），与 ca_rip_cr P5 代数引理协同。
- **相干字典不确定原理（CS-5，构造性轨道）** `CRuncertainty_principle`（probe_uncertainty_cr.v，F5）：
  **支撑大小口径**（Donoho-Stark 相干字典不确定原理的构造性正形式）：0 ≤ μ、单位范数、
  两两相干 ≤ μ（在支撑并集 T1∪T2 上）、**μ·(|T1|+|T2|−1) < 1** ⟹ 同一信号两个稀疏
  表示 Σ_{T1} c·u == Σ_{T2} d·u（c/d 在各自支撑外为零）⟹ ∀j: c_j == d_j——稀疏
  表示唯一性的**实际支撑大小版**（比前缀口径更强，|T1|+|T2|−1 用真实支撑大小而非
  前缀界）；证明链：列表支撑 RIP 下界（`lst_rip_lower`：Σ_{j∈T}e_j² ≤
  ‖Σ_{j∈T} e_j·u_j‖² + μ·(|T|−1)·Σ_{j∈T}e_j²，常数 |T|−1 的归纳——范数展开 +
  相干三角 + AM-GM 逐对 + INR(subn) 恒等）+ 支撑合并（`list_undup` 去重）+ 零项吸收
  （`lst_sum_restrict`：T1⊆T 且 f 在 T\T1 为零 ⟹ Σ_T f == Σ_{T1} f）+ 收缩链
  （R4 同构）；35 定理全 Qed、零经典公理（"Closed under the global context"）。
  **常数口径诚实标注**：经典 |S|+|S'| ≥ 2/μ 需两正交基乘积版（a·b ≥ 1/μ²，
  Donoho–Huo + AM-GM），一般相干字典的标准常数是 **1+1/μ**（Foucart–Rauhut 唯一性
  定理 / spark 论证）；经典版 probe_uncertainty.v（前缀口径 μ(M+1)）亦存在。
- **字典最优性 ⟹ 恢复保证合成（CS-6，构造性轨道，G-8）** `CRg8_recovery_synthesis`
  （probe_g8_synthesis_cr.v，G-8）：**压缩感知三角闭环的合成定理**——若字典相干 μ 同时
  满足 **Welch 下界**（平方形态 `(INR M − INR N) ≤ INR N · INR(M−1) · μ²`——**前提状态**：G-7 的完整构造性证明为后续工作，本合成定理在 Welch 前提悬空下陈述逻辑蕴含）
  与 **F5 唯一性窗口**（`μ·(|T1|+|T2|−1) < 1`），则同一信号的两个 |T|-稀疏表示必相同
  （∀j: c_j == d_j，直接实例化 F5 `CRuncertainty_principle`）；配套相图定理
  `CRphase_window_nonempty`：Welch 下界 + F5 窗口 ⟹ **窗口非空参数条件**
  `(INR M − INR N)·(INR T)² < INR N · INR(M−1)`（"Welch < 1/|T| 时唯一性窗口非空"的
  定量刻画——μ 落在 [Welch, 1/|T|) 区间才有唯一恢复的相图结论）；证明链（纯 CR，
  手工引理链无 nra/lra）：CR 算术辅助（`CRsqr_lt_one`：0 ≤ z < 1 ⟹ z² < 1；
  `CRmult_le_compat_4`：0 ≤ a ≤ b、0 ≤ c ≤ d ⟹ ac ≤ bd；`CR0_lt_INR_pos`；
  `CR_INR_pred_nonneg`）→ 相图（① 0 ≤ μT ∧ μT < 1 ⟹ (μT)² < 1 →
  ② Welch 两边乘 T² → ③ ring 整理 → ④ N(M−1)(μT)² < N(M−1)·1（乘 0 < N(M−1)）→
  ⑤ CRle_lt_trans 组装）→ 合成（F5 实例化）。6 Qed / 0 Admitted / 0 自定义公理，
  **Print Assumptions 双定理均 "Closed under the global context"（零经典实数）**；
  依赖 ca_rip_cr + F5（同轨道）；独立编译 EXIT=0 + 合并版（47 分区，当时快照；现合并版 25 = 57 顶层 Module）EXIT=0。
  **定位（如实）**：G-8 是"字典设计最优性（Welch 下界）⟹ 恢复保证（F5 唯一性）"的
  定量桥——把压缩感知"唯一性⟺恢复⟺相干区间"的相图结构定理化；Welch 下界本身
  （G-7 构造性 Welch 完整证明）为后续工作（本条目以其平方形态为抽象前提）。
- **加权阶梯范数精确闭式（CS-7，经典 R 轨道，G-1）** G1_norm_closed
  （probe_g1_norm_closed.v，21 Qed / 0 Admitted）：比率阶梯
  
_{j+1} ≥ r·n_j（或任意长度 M 组合）的加权组合 comboM (S M) c (fun j => psi (n j))
  在窗口 W 上的精确平方范数
  ‖Σ_{j≤M} c_j·ψ_{n_j}‖²_W = Σ_{j≤M} c_j²·‖ψ_{n_j}‖²_W + 2·Σ_{j<k≤M} c_j·c_k·K_W(n_j,n_k)，
  其中交叉项 K_W(a,b) = ⟨ψ_a,ψ_b⟩_W 用**单对 Dirichlet 核比闭式**精确替换
  （ipW (psi a) (psi b) W 显式闭式，psi 定义展开 → rot_atom 几何和 → re 提取）——
  即 Gram 交叉项的精确解析形式。三段式证明：R0 求和工具（sum_f_R0 split/swap、
  索引平移双和编码）、R1 单对闭式（g1_psi_point/g1_ipW_psi）、R2 Gram 组装
  （g1_gram_full）、R3 主定理。**定位（如实）**：G-1 把"上确界写成闭式"——
  根治审稿 Critical A-1/B-1 的 **12.5× 口径混用**（此前框架界用两套近似：精确范数与
  保守界分离；闭式等式使一套口径贯穿）；数学非新（Gram 展开 + Dirichlet 核比是
  经典），形式化价值在机器检查的精确等式与 G-2/G-5/G-6 的共同前置。
- **相邻带相干渐近闭式 + 相变定理（CS-8，经典 R 轨道，G-2）** mu_adj_decreasing /
  mu_adj_phase_transition / mu_adj_asymptotic（probe_g2_mu_adj.v，36 Qed / 0 Admitted）：
  比率 r 阶梯相邻带相干（口径①）的渐近极限 lim_{k→∞} μ(n_k, n_{k+1}) = μ_adj(r)
  其中 **μ_adj(r) := √r·sin(π/r)/(π(r−1))**，且存在**相变点 r\***（μ_adj(r\*)=4/5，
  数值 ≈1.30）：r ≥ r\* ⟹ 渐进可认证；r→1⁺ ⟹ μ_adj→1 不可认证。三定理：
  ① mu_adj_decreasing（r≥2 严格递减，两段式交叉夹逼：√r/(r−1) 递减 × sin(π/r)
  递增的乘积不直接单调，交叉相乘后插入中间项分两段证）；② mu_adj_phase_transition
  （∃r∈(1,2)：μ_adj(r)=4/5，π<17/5 上界（sin_bound 0 阶 + MVT 递减反证）+ 端点
  μ_adj(6/5)>4/5>μ_adj(3/2)（sin 特殊角）夹逼 + IVT_interv 区间中间值定理）；
  ③ mu_adj_asymptotic（序列极限复合：自建 g2_Un_cv_cont（continuity_pt+Un_cv
  复合）+ mu_adj 连续性组装）。**定位（如实）**：G-2 的 μ_adj 定理化是**真正新数学**
  （交叉核验总表的 μ_adj 公式此前未定理化）——把"E5 一个数据点"升级为完整相图，
  直接落实 B-7 强叙事（0.4502 相邻带下界 → 2·0.4502=0.9003>4/5 的 G-4 前置）；
  依赖 G-1（K_W 闭式）+ ca_fourier（渐近工具）。
- **检查器充要刻画（CS-9，经典 R 轨道，G-3，v2.8 新增）** `g3_certifiable_iff` +
  `g3_row_bound_mu`（probe_g3_criterion.v，5 Qed / 0 Admitted）：**反射检查器通过
  ⟺ 每行精确相干行和 ≤ p/q**（框架界 (1±p/q) 的充要条件）。三件套：
  ① `g3_row_bound_mu`（逐对 Cnorm ≤ pair_frac_R ⟹ 行和 ≤ p/q 的分数和分解）；
  ② `frame_check_instance_mu`（参数化检查器，I/p/q 全参数）；
  ③ `g3_certifiable_iff`（检查器判定 ⟺ Gershgorin 框架界条件）。**定位（如实）**：
  G-3 是 Gershgorin 框架界的参数化机器检查（经典结果形式化），价值在**充要性**——
  把"检查器通过 ⟹ 框架界"从单向充分升级为 iff，与 G-5 反例构成可判定性边界完整刻画。
- **可判定性溢价反例（CS-10，经典 R 轨道，G-5，v2.8 新增）** `g5_premium`
  （probe_g5_premium.v，35 Qed / 0 Admitted）：**存在具体阶梯 [3,7,15]：反射检查器
  拒（frame_check_instance = false）但精确 Gram 相干行和 ≤ 4/5**。三件套：
  ① 完整口径 Dirichlet 闭式 `g5_coh_full_*`（min(a,b) 项，|⟨ψ_3,ψ_7⟩|=
  sin(4π/7)/(sin(4π/21)√21)≈0.3777、|⟨ψ_7,ψ_15⟩|=sin(8π/15)/(sin(8π/105)√105)≈0.4094，
  行和≈0.787043，与评估文档一致）；② π 界自证（`g5_pi_ge_3141`/`g5_pi_le_3142`：
  π∈[3.141,3.142]，sin(π/6)=1/2 快收敛路线）；③ 数值界（sin_bound n=0 + 简单分数
  代入点 + 递增性）。**定位（如实）**：G-5 把 §5.2 的"假阴性 49.1%"叙事升级为
  **具体机器检查反例**——[3,7,15] 精确可认证（≤4/5）但被反射检查器误拒，是
  G-3 必要方向的直接见证；与 §5.2b"可判定性溢价"概念闭环。
- **G-5 构造性三角资产（纯构造性轨道，v2.8 修订追加，2026-08-25 并入合并版 25）**：
  M1 构造性 π（`probe_pi_cr_m1a` 25 Qed + `probe_pi_cr_m1b` 43 Qed：Leibniz 级数
  π/4 = Σ(−1)^k/(2k+1) + CR_complete 取极限，有理界 **3.141 ≤ π ≤ 3.142**
  ——`CRpi_lower_3141`/`CRpi_upper_3142`）、M2 构造性 sin（`probe_sin_cr_m2`
  39 Qed：交替幂级数 Σ(−1)^k x^{2k+1}/(2k+1)!）、M3 构造性 sqrt（`probe_sqrt_cr_m3`
  59 Qed：Q 层二分 + CR 极限，**√21 ≥ 458/100、√105 ≥ 10246/1000**）——三者均
  **纯 Stdlib ConstructiveReals、零经典、零 Admitted、零自定义公理，Print
  Assumptions 全 Closed under the global context**，已并入合并版
  `ca_merged_full_25.v`（57 顶层 Module = 55 模块分区，MERGE_EXIT=0）。**定位（如实）**：G-5
  可判定性溢价主定理的**构造化版本三角基座**（M4 探针级主定理为后续工作，
  不构成相干缺口闭合——审稿建议"不得表述为相干进展"）。
- **τ 裁剪最优性（CS-11，经典 R 轨道，2026-08-28 新增）** `probe_taugrid.v`（17 Qed / 0 Admitted，审计 nat 纯 Closed / R 层仅 Dedekind 三允许公理）：**覆盖债精确量化** `coverage_fraction`/`coverage_debt`（S T < n ⟹ 窗 [0,T] 内能量恰 = (T+1)/n，窗外能量 1−(T+1)/n ∈ (0,1)——**τ 负债的机器可计算量**，"剪 255/127/63 应恶化"经验律的定理侧镜像：高负债带 = 大窗外能量）；**支撑完备刻画** `support_classification`（n ≤ T ⟺ ψ_n 完全支撑训练窗 [0,T]，iff——裁剪保表示的充要条件）；**裁剪证书单调** `prune_row_le`（kept 子族行和 ≤ 全族行和——上界型证书经裁剪不损）；**C-梯子稀疏化迁移** `thinning_preserves_ratio`；**三连合成** `tau_prune_optimality`（证书单调 ∧ kept 完全支撑 ∧ pruned 严格超窗带覆盖债 ∈ (0,1)）——τ 感知裁剪 = 保留完全支撑带 + 证书单调 + 覆盖债量化，randmax256/384 裁剪实验的定理化。
- **构造性孪生（CS-12，纯构造性轨道，2026-08-29 新增）** `probe_taugrid_cr.v`（13 Qed / 0 Admitted，Print Assumptions **五段全 Closed——零公理**，比主线（Dedekind 三公理）更干净）：抽象接口 `{R : ConstructiveReals}` + 归一梯子 u（cos/复指数/√n 构造性未实现——接口与主线 psi_norm_sq_pt 数学一致，trig 由 M2E 扩展 plug-in）；**层归属判定落地**：严格序 CRlt 本身是 **Set 值**（Stdlib ConstructiveReals.v:88 库设计），覆盖债界定定理以信息性形式 **0 < debt < 1**（Set 值 prod，证明项可提取）陈述，主定理结论 prod 型（信息性分支不能进 Prop 的 /\——"Cannot enforce Set <= Prop"），sigT 被类型系统强制（谓词含 Set 值 CRlt 时 sig 非法）；**序判定下放 Q 层**（债值 CReq 于有理数，Qlt 判定经 CR_of_Q_lt 提升为带数据 CRlt，CRlt_proper 信息性搬运）；**提取 `taugrid_cr.ml` 经 DkMLNative ocamlc 4.14.2 编译通过**（柯西实例 cRealConstructive 具象化——CRlt 携带逼近数据；DRealConstructive 的 CRlt ≡ Rlt 被经典公理阻断，不采用）。
- **CS 生产线（CS-13，经典 R 轨道，2026-08-29 新增）** `probe_cs.v`（29 Qed / 0 Admitted，审计仅 Dedekind 三允许公理）：**一致 RIP** `cs2_rip_uniform`（(1−δ)‖c‖² ≤ ‖Φc‖² ≤ (1+δ)‖c‖²，δ = 4K(C) **不随稀疏阶 s 增长**——psi_unconditional_basis 的 Candès–Tao 命名打包）；**★s-sparse 唯一性** `cs3_energy_zero` + `cs3_unique`（C ≥ 10 即 2K(C) < 1：测量 y = y' ⟹ 系数 c = c'——**测量端信息不丢失**；路线：差列表 map2_csub + 逐点线性（csum_ext_indep/Csum_sub/csub_distr_r）+ 下界半边 (1−2K)·S ≤ ‖F‖²）；**embedding** `cs6_embedding`（常数 1−2K(C) > 0）；**spark 下界** `cs1b_spark`（无平凡零组合 ⟹ n 列独立 ⟹ spark ≥ n+1，Gershgorin 冗余路径收编为 CS-3 推论，Elad–Bruckstein 判据）；**逐对相干** `cs1a_pair_bound`（C-梯子 ≤ 2πq/(1−q)，row_sum_3halfs 单项抽取）；**★近重复对爆炸** `near_dup_coherence_12`（coh 1 2 = **1/√2 精确值**——零相位使内积为纯实正数）+ `cs4c_explosion`（**2μ = √2 > 1**——s ≥ 3 时 (s−1)μ ≥ √2，Gershgorin 型 RIP 上界证书在含近重复对梯子上必然失效）。
- **offset 无关性（CS-14，经典 R 轨道，2026-08-29 新增）** `probe_cs5.v`（5 Qed / 0 Admitted）：**同族平移 t→t+δ 下跨网格对相干界不变** `cs5_offset_pair`/`cs5_offset_diff`（|⟨ψ_{t1+δ},ψ_{t2+δ}⟩| ≤ N/(2·min(j mod N, N−j mod N))，**右端不含 δ**——偏移在同族对差频中相消（pair_eq_rotdiff + ring 消元），pair_dirichlet 接管）；**黄金比护城河** `cs5_golden_moat`（1/(3d) ≤ |d·φ_gold − m|）；**offset 语义非空** `cs5_gold_not_grid`（φ_gold ∉ ℤ，d=1 护城河反证）——ogrid 实验的定理侧：跨网格对证书不含偏移，结构化频率路线的恶化不来自跨对相干。

- **意义（强度如实声明）**：本开发在**通用层**建立可认证稀疏恢复的理论保证（单位范数 + RIP(2,μ) 基元 + **k-原子 RIP** + 稀疏唯一性 + **行和版 RIP 桥接** + **唯一性⟹恢复正确性骨架（R4）** + **相干字典不确定原理（F5，支撑大小版）** + **字典最优性⟹恢复保证合成（G-8）**，全部机器检查），并在 **C=4 阶梯完成实例级拼接——注意仅前 3 原子 [3,13,53] 获得稀疏唯一恢复**（`C4_sparse_uniqueness_3`，3 原子唯一恢复，**非 4 原子**；第 4 原子 213 未覆盖）；全窗口 [3,13,53,213] 四原子的稀疏唯一性扩展是**直截但未完成的计算**（必要的逐对相干界已在 `PSA_framework.v`，四原子需组装 6 对并验证 μ·4 < 1）；更大阶实例（如 C=9 的 s≤4）及与 ρ^{−3/2} 行和紧界（§5.6.5，C=4 行和 2π/7 < 1）的合成仍为后续工作（future work 第一项）。**4 原子障碍分析**：两两相干口径的硬限制为 μ·4 = (11289/33920)·4 ≈ 1.33 > 1（行和口径 δ_4 = 3×2π/7 ≈ 2.69 更差）；出路有三——精确 Gram 特征值口径（G-1 闭式可算 4×4 特征值下界，λ_min > 0 则四原子仍唯一）、严格 3-稀疏信号由 `sparse_uniquenessM` 覆盖、Welch-窗口合成（G-8）理论极限陈述；实际应用中信号通常 3-稀疏或近似稀疏。形式化贡献定位为：通用层 RIP/唯一性/不确定性原理定理的机器检查 + 原子族单位范数证明（含构造性轨道零经典公理的 k-原子 RIP、唯一性骨架与不确定原理）+ C=4 前 3 原子实例级拼接 + 行和版 RIP 桥接 + 相图合成（G-8）；**数学新颖性说明（如实）**：`sparse_uniquenessM`、`CRrip_bound_k`、`row_rip_bound_M`、`CRrecovery_correct_prefix`、`CRuncertainty_principle`、`CRg8_recovery_synthesis` 与 `C4_sparse_uniqueness_3` 本质是 Gershgorin/互干性唯一恢复、RIP、Donoho–Stark 不确定性原理与 Welch 界-恢复保证相图的机器检查（Candès–Tao RIP 框架下的经典结果），数学上并非新颖——本工作的形式化价值在于用 Coq 机器检查这些定理在频率阶梯原子族上的成立（含 C=4 具体常数核验、行和版 RIP 常数的紧化路径、构造性轨道独立性验证与三角闭环的相图合成）。

## 6 提取与可执行检查器

- PSA_extract.v → psa_guard.ml → ocamlc 字节码 exe → psa_guard_ffi.py；核心判定函数由 Coq `Extraction` 机制生成 OCaml（非手动翻译）；`main.ml` 为 CLI 包装（手动，仅 I/O 十进制转换）；`frame` 的原生整数镜像（`frame_check_instance_int`）因效率手动重写（规避 Peano 大数栈溢出），与 Coq 定义的等价性为逐行镜像 + FFI 24/24 交叉校验（非机器证明）。
- 自测 24/24（PSA_refcheck.v 20 项 Check/Eval + 4 项整数行和验算）。
- **范围前提（如实声明）**：整数镜像与 Coq nat 的等价仅对中间量不超过机器字长（OCaml int，63-bit）的阶梯成立；实验中阶梯值 ≤255 安全，对极大输入（≥10⁶ 级）sparse 等走 Peano 提取的子命令仍会栈溢出。
- **定量安全阈值（系统扫描修正）**：行和判定按 num,den 连乘累加，累积分母 ≈ ∏ pair_den（指数增长）。114 阶梯扫描实测：末带 < 2^20 的阶梯中仍有 14/89（15.7%）exe 与 Coq 语义分歧（如 C=6-sparse [3,19,115,691,4147]：Coq 语义 true、exe 溢出误判 false，累积分母达 10^26 ≫ 2^63）。实验实际使用（带值 ≤255、m ≤ 8）全部落在 63-bit 安全区；通用安全阈值须逐梯核算 ∏ pair_den < 2^63（或改用任意精度 Zarith/Python 大整数）。**安全域谓词（未来工作，评审建议）**：当前"安全区"的确认是实验性的（扫描核算），**未被形式化**——用户无法在运行时自动判断当前输入是否安全；未来工作包括在 Coq 中证明一个可验证的**安全域谓词**（在满足该谓词的输入范围内，OCaml int 镜像与 Coq 语义一致），或完成 Zarith 任意精度提取。
- **int 平方根实现**：`int_sqrt n = int_of_float (Float.sqrt ...)` 为浮点近似；对 n < 2^53 截断后偏差 ≤ 1，仅在判别阈值附近才可能翻转（如实声明）；安全阈值收紧为中间量 < 2^53。
- **健全性闭环**：`frame_check_instance_sound` 已 Qed——判定通过 ⟹ gershgorin_frame_mu (length I) (S (last I)) (4/5)，检查器 = 框架界定理的可执行投影。
- **反射层纠错实例（形式化发现并修复真 bug）**：反射层原 `row_sum_frac_aux` 在收缩列表上重算 nth，使 Coq 判定与生产原生检查器不一致（[3,13] 误判 false、C4 行和退化为 (0,0) 空洞通过）；加 orig 参数修正后 Coq 与原生逐行同构（FFI 24/24 复核）。
- **方法论教训：逐行同构原则**——"定义等价"不足以保证提取保真性（`row_sum_frac_aux` 的两个版本数学上定义等价，但在收缩列表上计算路径分叉）。提取代码应尽可能镜像 Coq Fixpoint 的结构，而非依赖高阶重写得到的"语义等价"的另一份代码。

## 7 公理记账（审计小节）

- **审计总量**：PSA_audit.v **165 项** Print Assumptions，RC=0，零 Admitted（111 段 Axioms + 54 项 Closed）；**完整运行日志 `审计证据/audit_run_20260826_full.txt`（165/165 块随稿 co-locate，可复跑）**；构建配置 `_CoqProject`/`Makefile`/`_merge_ca.py` 随稿。
- **公理脚印（全部 165 项仅此）**：ClassicalDedekindReals.sig_not_dec / sig_forall_dec + functional_extensionality_dep（标准库反射层基础设施）；**`Classical_Prop.classic` 出现 0 次**。
- **如实说明（显式声明）**：sig_not_dec / sig_forall_dec / fext 是 Dedekind 实数构造携带的非构造性选择类原则，**属可接受的 Reals 基底**（标准库反射层自身依赖），**非本开发应用层引入、非 `Classical_Prop.classic` 公理**；"classical-free"精确指 `Classical_Prop.classic`（排中律宏）零出现，而非"无任何经典原则"。提取计算性：上述公理仅在证明层（Prop）使用，不参与提取的计算内容（Set/Type 层无 sig_not_dec 调用）。
- **M1.5 经典清零（已完成，post-M1.5 复核成立）**：此前仅剩的 4 项（softmax 系列 + certified_attention_approx）经 exp 单调性继承经典排中。现 Module ExpSeries 已 Qed（`exp_mono_le_noclassic` 等，Stdlib exp 即幂级数定义），exp_mono_le 改走幂级数路线——语句不变、下游零改动。**勘误标注**：`PSA_audit.v` L108–121 记载的"4 项经 exp Rpower/MVT 继承 classic"为 **pre-M1.5（2026-08-19）过时记录**；合并版 `ca_merged_full_25.v` L63579（Module ExpSeries）/L63672（exp_mono_le_noclassic）/L63719（应用）已并入，4 个注意力定理位于其后，`exp_increasing` 仅存于 ca_* 基础设施（非审计目标）。**意义**：整个 CertifiedAttention 模块（注意力近似主定理）为纯构造性——据我们所知，这是第一个不依赖实数完备性排中律的深度学习注意力形式化验证。
- 依赖库（ca_* 六库）全审计为 P4 长期项。**外部依赖（mathcomp、Coquelicot）未纳入 165 项审计**——"零 `Classical_Prop.classic`"结论仅限本开发应用层，不推广到整个开发依赖（Coquelicot 基于实数库，可能含经典公理，如实声明）。

## 8 实证预览

char 级 0.5M 参数（0.43M–0.63M 视模式）、T_train=512、种子 {1337,42,7}、确定性协议：

| 方案 | 512 | 1024 | 2048 | 4096 |
|------|-----|------|------|------|
| rope（b32 三个种子） | 4.44±0.08 | 6.77±0.07 | 13.68±1.21 | 25.30±4.63 |
| **psi-rope [3,13,53,213]（本证书对象）** | 4.70±0.14 | 5.64±0.07 | 8.42±0.10 | 12.75±0.34 |
| **psi-rope 七带 [3,…,255]（T8 复合证书对象）** | 4.53±0.10 | 4.75±0.06 | 8.28±0.28 | **12.40±0.74** |

psi-rope 行 3 个种子均值±std、dense 单个种子（b64 s1337）、rope 为 b32 3 个种子均值±std——定位为 teaser，完整实证与机制分析见配套论文 B。**种子稳健性（v2.15 注）**：上述 3 种子为原始口径（探索性）；配套论文 B 已完成 9 方案 × 10 随机种子的全量复核（2026-08-25），主表排序在 n=3→5→10 逐级复现、新增种子与既有种子均值差异全部 ≤0.8 且无方向性漂移——本节 teaser 表的方向性结论经受住了该稳健性检验（详见论文 B §10.9/附录）。

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
- 审计 165 项全零 classic（post-M1.5 复核，完整 165/165 日志随稿）；公理脚印仅 sig_not_dec + sig_forall_dec + fext（可接受 Reals 基底，显式声明）。
- 实证规模 toy 级、种子有限（dense/rope 已补；NoPE 单个种子）。**对论文 B 的依赖（如实）**：本文多处引用论文 B 的实证结论（七带基线、psi-rope-rand 等）作为动机与对照——论文 B 为独立投稿的预印本，其实验结论未经本审稿流程评审；本文的形式化贡献（框架界/衰减界/证书）不依赖论文 B 的实证有效性，两者正交。
- **形式化的适用域以结构存在为前提**：对无位置结构的编码（NoPE 类）本框架无任何可证陈述。论文 B 实证给出定量交易曲线：有结构端以分布内 ppl ~2× 劣化（4.46 vs 9.06）为代价承受 OOD 相位混淆风险；形式化锁定的正是交易中有结构的一端。

## 11 结论

生成 → 守卫 → 门控 → 衰减 → 框架 → 截断 → 稳定性 → 注意力近似 → **实例证书（有理、可判定）** → 长度一致性（∀N≥214）→ T8 复合证书 → **反射检查器及其健全性定理（165 项审计，全部 Classical_Prop.classic 零出现（排中律宏零出现，非无任何经典原则））**：一条完整的、零 Admitted 的**表示层认证管线**——为解析核保证服务，与论文 B 的实证性能正交。

**可组合的反射化（方法论贡献）**：反射检查器的健全性证明是可组合的——3D 张量核的静态定理与 1D `gershgorin_frame_mu` 共享同一骨架，其反射化是提取链的直和扩展而非基础理论修正。宽轨家族 2D/3D/4D 成员齐备（N 维公式 M_bound^{(N)} = (C³/2)·((1+4K_C)^N − 1) 的 N=2/3/4 校验全部定理级成立，且组合指数增长部分已升为 ∀N 定理，§5.6.5）。客观地讲，3D/4D 证书当前是非紧的存在性结果，其价值在架构可组合性与维度推广的定位，而非常数本身；1D 证书（μ=4/5）保持紧且不受影响。

**可证明性边界（v2.0 新增，§5.6）**：在认证管线之上，本开发把论文 B 的"性能-可证明性张力"从实证观察升格为定理——**稠密覆盖与 μ≤4/5 可判定认证互斥**（`pareto_law_main`/`pareto_law_N511`：N=511 时 m≥10 必拒；P1/P1′ 给出精确窗口口径相干下界的解析根源；T2a/T2b 把负定律延伸到随机阶梯高概率拒绝）。配套的碰撞距离框架（碰撞 ⟺ 有理、最小距离 = 分母、无理偏移零碰撞、ALiBi 无碰撞端点、Parseval 能量守恒、窗口无关 Dirichlet 界、容错 Gershgorin 分级证书、一般维张量闭式、核漂移 softmax TVD 界）为论文 B 的 τ/碰撞机制提供形式化镜像——"认证—可证明性边界—碰撞/分辨率刻画"三角被机器检查覆盖，零 Admitted、零自定义公理。

**压缩感知（v2.1 新增 §5.6.6，v2.2 升级为 k-原子 RIP，v2.3 完成 C=4 实例拼接，v2.4 新增行和→RIP 桥接，v2.5 新增唯一性骨架与不确定原理）**：频率阶梯原子族在通用层获低相干 → RIP → 稀疏唯一性定理（单位范数 `psi_norm_one` + RIP(2,μ) 基元 `rip_bound2` + **k-原子 RIP `CRrip_bound_k`（构造性轨道 ca_rip_cr.v，纯构造性实数、零经典公理，33 定理）** + **行和→RIP `row_rip_bound_M`（probe_row_rip.v：行非对角和 ≤ μ_row ⟹ δ=(k−1)·μ_row，9 Qed 零公理）** + 稀疏唯一恢复 `sparse_uniquenessM` + **C=4 实例 `C4_sparse_uniqueness_3`（probe_c4_instance.v：μ=11289/33920 < 1/3 ⟹ 3 原子 [3,13,53] 唯一恢复）** + **唯一性⟹恢复正确性骨架 `CRrecovery_correct_prefix`（probe_recovery_cr.v，构造性轨道）** + **相干字典不确定原理 `CRuncertainty_principle`（probe_uncertainty_cr.v，构造性轨道，支撑大小版 1+1/μ，35 定理零经典）**，probe_incoherence 48 Qed + ca_rip_cr 33 Qed + probe_c4_instance + probe_row_rip 9 Qed + probe_recovery_cr + probe_uncertainty_cr 35 Qed 并入合并版）——「框架界 + 频率阶梯」从表示稳定性推进到稀疏恢复唯一性，与论文 B 的随机稀疏恢复主张构成定理侧支撑。

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
9. [代码仓库] PSA-CertifiedSparseGating. https://github.com/hy7pc8gfmf-dotcom/PSA-CertifiedSparseGating （Artifact：Coq 形式化 + 论文 + 实证 + CI，Apache-2.0）。

## 附录 复现指引

> **代码仓库（Artifact）**：https://github.com/hy7pc8gfmf-dotcom/PSA-CertifiedSparseGating —— 含全部 Coq 形式化（coq/lib + coq/core + coq/probes）、两篇论文（草稿/正式版/中文规范版）、实证脚本与数据（mpirical/、data/）、CI 流水线（GitHub Actions：Rocq 9.0 编译 + 165 项审计 + coqchk 内核复验，徽章见仓库 README）。预印本 DOI：10.6084/m9.figshare.33312189。


- **代码分布**：形式化代码 `src/`（`_CoqProject` 声明 load path；各模块独立编译命令见经验卡 E067/E077）；探针 `z/`；**合并版 `src/ca_merged_full_25.v`（87588 行，57 顶层 Module = 55 模块分区 + `ca_independence` 内 `independent`/`independent′` 2 附加，含 20 个 z 区探针 + ca_zeta_euler / ca_rip_cr 构造性轨道，`_merge_ca.py` 重新生成，合并编译 MERGE_EXIT=0）**；归档基态 `30模块/`（ca_* + 探针 pro 版 + ca_zeta_euler + ca_rip_cr + 合并版，SHA-256 与 src/z 一致）。
- **探针交叉索引**：`golden_near_collision_gold`（§5.6.4 U5 黄金近碰撞半径，零公理）承载于 z 区探针 **`probe_nearcoll.v`**（未并入合并版，独立编译验证，`Print Assumptions` Closed）。
- **CS 战役探针（2026-08-29）**：`probe_taugrid.v`（17 Qed，τ 裁剪最优性）/ `probe_taugrid_cr.v`（13 Qed 零公理，构造性孪生，提取 `z/extract/taugrid_cr.ml` 已 OCaml 编译验证）/ `probe_cs.v`（29 Qed，CS 生产线）/ `probe_cs5.v`（5 Qed，offset 无关性）——四模块合计 64 Qed，独立编译 EXIT=0，归档 30模块 SHA 一致，未并入合并版 25（并入待合并版再生）。
- **依赖版本**：Rocq/Coq 9.0.1；mathcomp（本地 vendored）；Coquelicot；Windows 10+ / PowerShell 7。
- **构建命令**：各模块独立编译 `coqc -Q <src> "" -Q <z> "" -Q <mathcomp> mathcomp -Q <Coquelicot> Coquelicot <file>.v`；合并版重新生成 `python src/_merge_ca.py` 后合并编译。
- 提取链：`PSA_extract.v` → `psa_guard.ml` → `psa_guard.exe`（DkMLNative ocamlc 字节码 + camlrun）；FFI 自测 `python psa_guard_ffi.py`（24/24）。
- 审计证据：`AI注意力算法\审计证据\audit_run_20260826_full.txt`（**完整 165/165 项**，2026-08-26 重跑）+ 历史 `audit_run.txt`（55 块样本）；构建配置 `_CoqProject`/`Makefile`/`_merge_ca.py` 随稿。
- 实验代码与数据：`psa_empirical/`（length_extrap.py 等，3 个种子固定 {1337,42,7}，见论文 B 附录 B）。
- 关键定理行号：ChampionCertificate L4582–5150（定理本体 L5075）、FrameCheck2DNarrow L5166–6290。
