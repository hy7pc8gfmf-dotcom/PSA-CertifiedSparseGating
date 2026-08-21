(* ============================================================
   PSA 形式化框架 v1.0（2026-08-20 更新；原 v0.1 2026-08-18 草稿）
   ------------------------------------------------------------
   位置：AI注意力算法/PSA_framework.v（独立文件，不入 22 库）
   依赖：ca_basis（psi/psi_linear_independent）
         ca_basis_lemmas（c_sparse_subset）
         ca_decay（decay_bound / row_sum_bound_K）

   版本史（对齐 2026-08-20 会话 16 基态）：
     v1.2（2026-08-20 会话 17）：评审 §1 修复——UnitaryInvariance 补 RoPE 显式实例：
       Cexp_unit_mod（Cnorm_sq (Cexp (0+iθ)) = 1，sin2_cos2）与
       unitary_invariance_psi_rope_theta（u k := Cexp (0+i (INR k·θ k))，逐位置旋转角
       θ k；与实验 2×2 旋转矩阵同构——SO(2)≅U(1)，实/虚部逐行对应
       length_extrap.py apply_rope_theta）。
     v1.1（2026-08-20 会话 17）：A2 酉不变性并入——新 Module UnitaryInvariance（帧尾）：
       全局保内积版本 unitary_invariance_point（unitary_invariance_frame 正确定型）+
       位置索引 psi-rope 版本 unitary_invariance_psi_rope(_global)（每位置乘单位模 u k）；
       注：原带索引逐点版本（每带乘 u_i 后对和取模）为假命题（反例 u0=1,u1=-1,g0=g1=1，
       |1-1|²=0≠4=|1+1|²），未并入；带索引 l2 等式需基精确正交（本 psi 族截断窗口
       交叉项非零，由 (1±4/5) 帧界路线覆盖）。
     v1.0（2026-08-20）：头注释同步实际内容——M1.5 已清零（Module ExpSeries，
       全 165 项审计零 Classical_Prop.classic）；端到端复合证书
       champion_e5_composite_certificate 已 Qed（Module ChampionCertificate，
       会话 14）；FrameCheck2DNarrow（会话 15）已并入。
     v0.1（2026-08-18）：初稿（下续为历史修正记录）。

   相对 AI注意力算法/*.txt 的修正（文档为未验证草稿）：
   1. c_sparse_subset（ca_basis_lemmas.v:6658）要求平方增长
      INR(f b) >= INR c * INR c * INR(f a)，且为 >=（非严格）、不含 >=2 条件；
      check_c_sparse_on_vals 相应改为检查 (c*c*a) <=? b（会话 3 实测修正：
      原 <? 会误拒 c*c*a = b 的合法稀疏子集，如 [3;3;4] 对 c=1）。
   2. 删除 sparse_subset_exists 误用：其前提 (INR N)²p²<1 对
      p=0.5、N>=2 恒不成立；门控子集改由确定性构造（全索引）。
   3. check_sparse_growthP 的反射证明按 Nat.ltb_spec 两构造子重写。

   状态标记：无 Admitted / admit / Abort（会话 3 已全数 Qed）。
   进度（2026-08-18 会话 3 更新）：
     ✅ 已真证（Qed，会话 2）：all_ge_2P（零公理）；
         check_sparse_growthP 正向分支；psa_pipeline_decay / psa_pipeline_linindep
         （exact 库内定理，公理 = sig_not_dec+sig_forall_dec+fext，零 classic）。
     ✅ 会话 3 补证（17 个引理全部 Qed，含 4 个原骨架）：
         forallb_adjacent_nth / forallb_adjacent_from_nth（相邻对 <-> 逐 nth 判定，零公理）；
         forallb_adjacent_sorted_implies（传递性版；原语句缺传递性前提不可证，已修正）；
         sparse_growth_trans / square_le_trans（<? / <=? 布尔检查的传递性，零公理）；
         sorted_of_strict_adjacent / nth_incr（列表工具，零公理）；
         check_sparse_growthP 反向分支（Hprop ⟹ 相邻布尔全真 ⟹ 与 Hall=false 矛盾）；
         check_c_sparse_growthP（平方增长 <=? 反射）；
         check_c_sparse_on_valsP（含 c_sparse_subset 语义修正，见上 1）；
         generate_correct（generate_indices_spec / generate_rec / gen_aux_tail 支撑，零公理）。
    修正说明（会话 3 实测发现，均与原文档冲突处）：
      1. check_c_sparse_on_vals 改用 (c*c*a) <=? b（见上 1）。
      2. check_c_sparse_on_valsP 右端显式并上「全元素 >= 2」：c_sparse_subset 本身不含
         >=2 条件（ca_basis_lemmas.v:6665 的 c_sparse_subset_ge2 需另加假设），原 reflect
         语句不可证（[0;3] 反例：c_sparse_subset 成立而 all_ge_2 失败）。
      3. generate_base_indices 改为 gen_aux C start len (start::nil)：原 (S len) 使
         length = S(S len)，与 generate_correct 的 length = S len 矛盾。
      4. forallb_adjacent_sorted_implies 原语句（Sorted + f⟹lt + 相邻全真 ⟹ 全局）
         不可证：f 无传递性时反例 f a b = (b=a+1) 于 l=[0;1;2]。
    公理验收（PSA_audit.v，2026-08-18 会话 3）：全部 17 个新引理中
      7 个零公理；3 个反射引理仅 sig_forall_dec+fext（INR 继承，零 classic）。
    ✅ 会话 3 续（P2 外部守卫路线 + 内部序列路线，18 个新引理全部 Qed）：
       - 内部序列：base_seq / base_seq_global_growth / base_seq_shift / seq_shift_gen /
         generate_eq_map（零公理）——生成器 = 全局序列前缀，可实例化 psa_pipeline_decay。
       - 外部守卫：guard_adjacent_growth / guard_ge2_map（守卫⟹有限前提桥梁）、
         nth_lt_backward / fold_right_max_In / I_chain_strict / I_chain_compound（I 链）、
         Csum_psi_conj_truncate_fin（有限截断）、decay_bound_finite_one_factor（one_factor 有限化）、
         **psa_guard_decay**（守卫全部通过 ⟹ 任意 I 内对衰减界；sig_not_dec+sig_forall_dec+fext，
         零 classic）——论文核心声明「运行时守护断言 ⟹ 数学保证」已真证。
    ✅ 会话 4（P0 确定性贪心门控，GreedyGate 模块 23 个新引理全部 Qed）：
       - greedy_aux / greedy_selected：乘数 M 显式参数化（门限 M*last <= v）。
         M = C 与原文 §3.2 fallback_mask(indices, C) 逐字一致（线性门，守卫 is_c_sparse 亦线性）；
         M = C*C 为平方门，保证选中子集满足库内 c_sparse_subset（平方增长）。
         注：路线图草案「线性门 val >= C*last ⟹ check_c_sparse_on_vals sel C」同一 C 不可证
         （反例 C=2、[4;8]：8 >= 2*4 保留而 2*2*4 <=? 8 = false），故 M 参数化并以上述两实例化。
       - 零公理：greedy_aux_In / greedy_selected_In / all_ge_2 保持 / NoDup 保持 /
         sorted_lt_all / greedy_Sorted_NoDup / Sorted 保持 / head_growth / adjacent_growth
         （相邻对被保留者满足 M*前 <= 后，即原文 is_c_sparse 断言）/ strict_growth /
         c_sparse_check / **greedy_selected_correct**（主定理：C>=2 + Sorted + all_ge_2 ⟹
         Sorted/NoDup/all_ge_2/check_c_sparse_on_vals sel C）。
       - greedy_selected_c_sparse_subset（sig_forall_dec+fext 继承反射层，零 classic）：
         反射 ⟹ 选中子集满足库内 c_sparse_subset（ca_basis_lemmas.v:6658）+ 全元素 >= 2。
       - 掩码形式：mask_aux / fallback_mask（布尔掩码）/ selected_by_mask（提取）/
         mask_aux_length / fallback_mask_length / mask_aux_correct / **fallback_mask_correct**
         （提取 = 贪心选中）/ fallback_mask_linear_sparse（原文 is_c_sparse 线性断言，零前提）。
       - **greedy_selected_guard_pass**（P0+P2 汇合）：平方门控 ⟹ 选中子集通过
         check_sparse_growth（严格线性），即 psa_guard_decay 的全部有限前提（vals = map seq I 时可实例化）。
    ✅ 会话 5 续（P0→P2 实例化桥 + P1a，11 个新引理/定义全部 Qed）：
       - 索引层面门控 greedy_idx_aux / greedy_indices（门限 M*last <= seq i，last 为上保留索引的
         seq 值），与值层 greedy_aux 通过 map seq 一一对应：greedy_idx_aux_map / greedy_indices_map。
       - 子序列引理：greedy_idx_aux_In / greedy_idx_aux_Sorted / greedy_indices_Sorted（零公理）。
       - **psa_gated_decay**（P0→P2 实例化桥）：NoDup I + Sorted I + all_ge_2 (map seq I) ⟹
         门控索引子集 I' = greedy_indices seq (C*C) I 上任意对的衰减界（直接 apply psa_guard_decay；
         sig_not_dec+sig_forall_dec+fext 继承，零 classic）。
         注：不需要 check_sparse_growth (map seq I) 前提（平方门自身保证相邻增长），
         也不需要 seq 全局增长 / map seq I 的 Sorted（严格线性由平方门 + C>=2 + all_ge_2 给出）。
       - **psa_gated_decay_base_seq**：seq := base_seq C start 的自然实例（生成器输出上的门控衰减）。
       - P1a：map_nth_seq（通用）、base_seq_list_Sorted（生成器前缀 Sorted）、
         **construct_base_sequence**（生成器 → BaseSequence 记录，字段由 base_seq_global_growth 填充；
         doc Step2 的构造真 Qed）、construct_base_sequence_map（记录列表 = 生成器前缀）。
    ✅ 会话 5 续 2（P1b 行截断误差，RowTruncation 模块 6 引理/定义全 Qed）：
       - list_sum_R（列表 R 能量求和）+ sum_filter_compl（filter 分割求和：全和 = 保留 + 丢弃，
         任意 P、任意分数）。
       - **complement_sum_bound**（路线图 P1b 抽象层）：保留 ≥ 总 − budget ⟹ 丢弃 ≤ budget，
         无排序（构造性：保留/丢弃由布尔判定 P 给出）。
       - row_score（行 i 非对角能量）+ **row_energy_bound**（row_sum_bound_K 直接实例：
         行能量 ≤ 2*K(C)，需 C > 2）+ **row_truncation_error**（complement_sum_bound 行实例）
         + **row_dropped_energy_bound**（论文 §4.2：掩码构造保证保留 ≥ 总 − min(S·ε_rel, R_max·ε_abs)
         ⟹ 丢弃能量 ≤ R_max·ε_abs；Rmax = 2*K(C)，Rmin_r 恒成立无需 ε 非负）。
       - 全部 sig_forall_dec+fext（R 级经 Reals），零 classic。
    ✅ 会话 5 续 3（端到端管线定理 + P3，5 个新引理/定义全 Qed，PipelineEndToEnd 模块）：
       - **psa_low_coherence**（P3a）：门控子集相邻基内积范数 ≤ 2/√C（decay dist=1 命名特例，
         psa_gated_decay_base_seq 特化 + 指数 |i-(S i)|=1 化简）。
       - **psa_pipeline_guard**（端到端管线，论文核心声明的完整形式化）：生成器 base_seq →
         门控 greedy_indices ⟹ ①守卫通过 check_sparse_growth ②任意对衰减界 2/(√C)^|i-j|
         ③低相干 ≤ 2/√C。前提仅 C>=2、start>=2、I NoDup/Sorted/all_ge_2。
       - **row_energy_bound_wide**（2/ 版行能量）：衰减界为 2 系数时行非对角总能量 ≤ 4*K(C)
         （= 2·R_max；复用 split_sum_geometric_bound_one / row_sum_bound_when_i_last_one 骨架）。
       - **psa_frame_bounds**（P3b）：psi_unconditional_basis 实例化于 base_seq（Riesz 常数
         1±4K，需 C>2 + start>=2 + I NoDup/Sorted + coeffs 长度匹配）。
       - **base_seq_strictly_increasing**（SeqProps）：生成器全局序列严格增（P3b 的 Hinc 前提）。
    ✅ 会话 5 终（1/ 系数收紧，P4 前瞻）：**psa_low_coherence_tight**——相邻基内积 ≤ **1/√C**
       （内部序列路线，decay_bound_tight_ij 的 dist=1 特例；比守卫版 psa_low_coherence 的 2/√C
       收紧一倍，前提用全局增长 base_seq_global_growth 而非守卫有限化，两版本互补）。
    ✅ 会话 5 终 2（守卫 1/ 版衰减，PSA_Pipeline 追加）：**psa_guard_decay_tight** +
       **decay_bound_finite_one_factor_tight**——守卫有限化路线的 1/ 系数版：
       用 inner_product_norm_bound_full（单项界 √(n1n2)/(2(n2−n1))）替换 general_n（两项界）⟹
       系数从 2/ 收紧到 1/，且行能量可直接满足 row_sum_bound_K 的 1/ 前提（收紧到 2·K(C)）。
   ============================================================ *)
Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.micromega.Lra.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Sorting.Sorted.
Require Import Stdlib.Reals.Reals.
Require Import Stdlib.ZArith.ZArith.
Require Import ca_base ca_complex_foundation ca_independence ca_basis ca_basis_lemmas ca_decay.
Import ComplexNumbers.
Import UnconditionalBasisLemmas.  (* 合并单文件环境中 c_sparse_subset（3 参版）需显式后导入——ca_probabilistic 有同名 1 参版，会话 12 修复 *)
Open Scope nat_scope.  (* 合并单文件环境无隐式 nat 作用域：=? / nat + / 0 模式需 nat_scope *)
Open Scope R_scope.    (* 后开：未注解 R 表达式（如 INR C - 1）归 R；nat 记法（=?/<=?）仍由 nat_scope 提供（会话 12） *)

Module RuntimeGuards.

(* ---------- 1. 基值 >= 2 的布尔判定 ---------- *)
Definition all_ge_2 (vals : list nat) : bool :=
  List.forallb (fun v => (2 <=? v)%nat) vals.

Lemma all_ge_2P (vals : list nat) :
  reflect (forall v, In v vals -> (v >= 2)%nat) (all_ge_2 vals).
Proof.
  unfold all_ge_2.
  apply iff_reflect.
  rewrite forallb_forall.
  split.
  - intros H v Hv. apply (proj2 (Nat.leb_le 2 v)). exact (H v Hv).
  - intros H v Hv. apply (proj1 (Nat.leb_le 2 v)). exact (H v Hv).
Qed.

(* ---------- 2. 相邻稀疏增长的布尔判定 ---------- *)
(* 相邻对检查：combine l (tl l) 生成 (l0,l1),(l1,l2),... 逐对判定 *)
Definition forallb_adjacent (l : list nat) (f : nat -> nat -> bool) : bool :=
  List.forallb (fun ab : nat * nat => f (fst ab) (snd ab)) (combine l (tl l)).

(* 线性增长检查：C*a < b（对应 decay_bound 前提 INR(seq(S i)) > INR C * INR(seq i)） *)
Definition check_sparse_growth (indices : list nat) (C : nat) : bool :=
  forallb_adjacent indices (fun a b => ((C * a) <? b)%nat).

(* 平方增长检查：c*c*a <= b（非严格；c_sparse_subset 要求 >=，见 ca_basis_lemmas.v:6658。
   原骨架用 <? 会误拒 c*c*a = b 的合法稀疏子集，如 [3;3;4] 对 c=1。） *)
Definition check_c_sparse_on_vals (vals : list nat) (c : nat) : bool :=
  forallb_adjacent vals (fun a b => ((c * c * a) <=? b)%nat) && all_ge_2 vals.

(* ---------- 列表工具：相邻对与 nth 的互推、链式传递 ---------- *)

(* 相邻对检查通过 ⟹ 每个相邻 (nth k, nth (S k)) 满足 f *)
Lemma forallb_adjacent_nth (l : list nat) (f : nat -> nat -> bool) :
  forallb_adjacent l f = true ->
  forall k, (k < length l - 1)%nat -> f (nth k l 0%nat) (nth (S k) l 0%nat) = true.
Proof.
  induction l as [| x xs IH]; intros Hall k Hk.
  - simpl in Hk. lia.
  - destruct xs as [| y ys].
    + simpl in Hk. lia.
    + unfold forallb_adjacent in Hall. simpl in Hall.
      destruct (andb_prop _ _ Hall) as [Hxy Hall'].
      destruct k as [| k'].
      * simpl. exact Hxy.
      * simpl. apply (IH Hall'). simpl in Hk. simpl. lia.
Qed.

(* 每个相邻 (nth k, nth (S k)) 满足 f ⟹ 相邻对检查通过（forallb_adjacent_nth 的逆） *)
Lemma forallb_adjacent_from_nth (l : list nat) (f : nat -> nat -> bool) :
  (forall k, (k < length l - 1)%nat -> f (nth k l 0%nat) (nth (S k) l 0%nat) = true) ->
  forallb_adjacent l f = true.
Proof.
  induction l as [| x xs IH]; intros H.
  - unfold forallb_adjacent. simpl. reflexivity.
  - destruct xs as [| y ys].
    + unfold forallb_adjacent. simpl. reflexivity.
    + unfold forallb_adjacent. simpl.
      assert (Hxy : f x y = true).
      { apply (H 0%nat). simpl. lia. }
      rewrite Hxy. simpl.
      apply IH.
      intros k Hk.
      apply (H (S k)).
      simpl in Hk. simpl. lia.
Qed.

(* 相邻增长 ⟹ 全局增长（链式传递，无需 Sorted）。
   注：原骨架的语句（Sorted + f 蕴含 lt + 相邻全真 ⟹ 全局）不可证：
   f 无传递性时反例 f a b = (b = a+1) 使 l=[0;1;2] 相邻全真而 f 0 2 = false。
   修正：显式加入传递性前提（Htrans），链式拼接相邻步。 *)
Lemma forallb_adjacent_sorted_implies (l : list nat) (f : nat -> nat -> bool) :
  (forall a b c, f a b = true -> f b c = true -> f a c = true) ->
  forallb_adjacent l f = true ->
  (forall i j, (i < j)%nat -> (j < length l)%nat ->
    f (nth i l 0%nat) (nth j l 0%nat) = true).
Proof.
  intros Htrans Hall i j Hij.
  assert (Hadj : forall k, (k < length l - 1)%nat ->
                 f (nth k l 0%nat) (nth (S k) l 0%nat) = true).
  { intros k Hk. apply (forallb_adjacent_nth l f Hall k Hk). }
  induction Hij as [| m Hij' IH].
  - intros Hjlen. apply Hadj. lia.
  - intros Hjlen.
    apply (Htrans (nth i l 0%nat) (nth m l 0%nat) (nth (S m) l 0%nat)).
    + apply IH. lia.
    + apply Hadj. lia.
Qed.

(* 线性增长布尔检查的传递性：C>=1 时 C*a<b 且 C*b<c ⟹ C*a<c（b <= C*b 中继） *)
Lemma sparse_growth_trans (C : nat) : (C >= 1)%nat ->
  forall a b c, (((C * a) <? b)%nat) = true -> (((C * b) <? c)%nat) = true -> (((C * a) <? c)%nat) = true.
Proof.
  intros HC a b c Hab Hbc.
  apply Nat.ltb_lt. apply Nat.ltb_lt in Hab. apply Nat.ltb_lt in Hbc.
  assert (HbCb : (b <= C * b)%nat).
  { rewrite <- (Nat.mul_1_l b) at 1. apply (Nat.mul_le_mono_r 1 C b). lia. }
  assert (Hbc' : (b < c)%nat).
  { apply (Nat.le_lt_trans _ (C * b) _); [exact HbCb | exact Hbc]. }
  exact (Nat.lt_trans _ _ _ Hab Hbc').
Qed.

(* 平方增长布尔检查的传递性（<=? 版）：c*c*a<=b 且 c*c*b<=cc ⟹ c*c*a<=cc。
   c=0 时两个前提平凡（0<=b、0<=cc），结论 0<=cc 直接成立。 *)
Lemma square_le_trans : forall c a b cc,
  (((c * c * a) <=? b)%nat) = true -> (((c * c * b) <=? cc)%nat) = true -> (((c * c * a) <=? cc)%nat) = true.
Proof.
  intros c a b cc Hab Hbc.
  apply Nat.leb_le in Hab. apply Nat.leb_le in Hbc.
  destruct (Nat.eq_dec c 0%nat) as [Hc0 | Hc0].
  - rewrite Hc0 in *. simpl in *. lia.
  - assert (Hcc1 : (1 <= c * c)%nat).
    { apply (Nat.le_trans _ (1 * c) _); [lia | apply (Nat.mul_le_mono_r 1 c c); lia]. }
    assert (HbCb : (b <= c * c * b)%nat).
    { rewrite <- (Nat.mul_1_l b) at 1. apply (Nat.mul_le_mono_r 1 (c * c) b). exact Hcc1. }
    assert (Hbcc : (b <= cc)%nat).
    { apply (Nat.le_trans _ (c * c * b) _); [exact HbCb | exact Hbc]. }
    apply (proj2 (Nat.leb_le (c * c * a) cc)).
    apply (Nat.le_trans _ b _); [exact Hab | exact Hbcc].
Qed.

(* 相邻严格递增 ⟹ Sorted Nat.lt（对 nat 列表，逐段 HdRel/cons 归纳） *)
Lemma sorted_of_strict_adjacent (l : list nat) :
  (forall i, (S i < length l)%nat -> (nth i l 0%nat < nth (S i) l 0%nat)%nat) ->
  Sorted Nat.lt l.
Proof.
  induction l as [| a xs IH]; intros H.
  - constructor.
  - constructor.
    + apply IH. intros i Hi.
      apply (H (S i)).
      simpl in Hi. simpl. lia.
    + destruct xs as [| b ys].
      * constructor.
      * constructor. apply (H 0%nat). simpl. lia.
Qed.

(* 严格递增链上 nth 单调：i <= j ⟹ nth i <= nth j *)
Lemma nth_incr (l : list nat) i j :
  (forall i, (S i < length l)%nat -> (nth i l 0%nat < nth (S i) l 0%nat)%nat) ->
  (i <= j)%nat -> (j < length l)%nat -> (nth i l 0%nat <= nth j l 0%nat)%nat.
Proof.
  intros H Hle.
  induction Hle as [| j Hle' IH]; intros Hj.
  - reflexivity.
  - apply (Nat.le_trans _ (nth j l 0%nat) _).
    + apply IH. lia.
    + apply Nat.lt_le_incl. apply H. exact Hj.
Qed.

(* ---------- 3. 反射：守护断言 <-> 库内稀疏条件 ---------- *)

(* 反射：check_sparse_growth <-> 全局严格线性增长（C>=1 保证传递性） *)
Lemma check_sparse_growthP (indices : list nat) (C : nat) :
  (C >= 1)%nat ->
  Sorted Nat.lt indices ->
  reflect (forall i j, (i < j)%nat -> (j < length indices)%nat ->
             INR (nth j indices 0%nat) > INR C * INR (nth i indices 0%nat))%R
          (check_sparse_growth indices C).
Proof.
  intros HC HSorted.
  unfold check_sparse_growth.
  destruct (forallb_adjacent indices (fun a b => ((C * a) <? b)%nat)) eqn:Hall.
  - left.
    assert (Htrans : forall a b c, (((C * a) <? b)%nat) = true ->
                        (((C * b) <? c)%nat) = true -> (((C * a) <? c)%nat) = true).
    { apply sparse_growth_trans. exact HC. }
    intros i j Hij Hjlen.
    pose proof (forallb_adjacent_sorted_implies indices (fun a b => ((C * a) <? b)%nat)
                  Htrans Hall i j Hij Hjlen) as Hltb.
    apply Nat.ltb_lt in Hltb.
    apply lt_INR in Hltb.
    rewrite Nat.mul_comm in Hltb.
    rewrite mult_INR in Hltb.
    rewrite Rmult_comm in Hltb.
    exact Hltb.
  - right.
    intros Hprop.
    (* 反证：Hprop 在相邻对 (k, S k) 上给出 INR 严格增长，INR_lt 回推
       (C*a <? b)=true，forallb_adjacent_from_nth 导出全真，与 Hall=false 矛盾。 *)
    assert (Hk : forall k, (k < length indices - 1)%nat ->
               (((C * nth k indices 0%nat) <? nth (S k) indices 0%nat)%nat) = true).
    { intros k Hk.
      apply Nat.ltb_lt.
      apply INR_lt.
      assert (Hg : (INR (nth (S k) indices 0%nat) > INR C * INR (nth k indices 0%nat))%R).
      { apply Hprop; lia. }
      apply Rgt_lt in Hg.
      rewrite <- mult_INR in Hg.
      exact Hg. }
    assert (Hall' : forallb_adjacent indices (fun a b => ((C * a) <? b)%nat) = true).
    { apply forallb_adjacent_from_nth. exact Hk. }
    rewrite Hall' in Hall. discriminate.
Qed.

(* 反射：平方增长布尔判定（<=?）<-> 全局 INR 平方增长（>=，任意 c） *)
Lemma check_c_sparse_growthP (vals : list nat) (c : nat) :
  reflect (forall i j, (i < j)%nat -> (j < length vals)%nat ->
             (INR (nth j vals 0%nat) >= INR c * INR c * INR (nth i vals 0%nat))%R)
          (forallb_adjacent vals (fun a b => ((c * c * a) <=? b)%nat)).
Proof.
  destruct (forallb_adjacent vals (fun a b => ((c * c * a) <=? b)%nat)) eqn:Hall.
  - left. intros i j Hij Hjlen.
    pose proof (forallb_adjacent_sorted_implies vals (fun a b => ((c * c * a) <=? b)%nat)
                  (square_le_trans c) Hall i j Hij Hjlen) as Hltb.
    apply (proj1 (Nat.leb_le (c * c * nth i vals 0%nat) (nth j vals 0%nat))) in Hltb.
    apply le_INR in Hltb.
    rewrite (mult_INR (c * c) (nth i vals 0%nat)) in Hltb.
    rewrite (mult_INR c c) in Hltb.
    apply Rle_ge.
    exact Hltb.
  - right. intros Hprop.
    assert (Hk : forall k, (k < length vals - 1)%nat ->
               (((c * c * nth k vals 0%nat) <=? nth (S k) vals 0%nat)%nat) = true).
    { intros k Hk.
      apply (proj2 (Nat.leb_le (c * c * nth k vals 0%nat) (nth (S k) vals 0%nat))).
      apply INR_le.
      assert (Hg : (INR (nth (S k) vals 0%nat) >= INR c * INR c * INR (nth k vals 0%nat))%R).
      { apply Hprop; lia. }
      rewrite <- (mult_INR c c) in Hg.
      rewrite <- (mult_INR (c * c) (nth k vals 0%nat)) in Hg.
      apply Rge_le in Hg.
      exact Hg. }
    assert (Hall' : forallb_adjacent vals (fun a b => ((c * c * a) <=? b)%nat) = true).
    { apply forallb_adjacent_from_nth. exact Hk. }
    rewrite Hall' in Hall. discriminate.
Qed.

(* 反射：check_c_sparse_on_vals <-> c_sparse_subset ∧ 全元素 >= 2（索引取 seq 0 (length vals)）
   注：c_sparse_subset（ca_basis_lemmas.v:6658）只含 NoDup ∧ >= 平方增长，不含 >=2 条件，
   故原骨架语句（reflect c_sparse_subset 本身）不可证——反射右端必须显式并上全元素 >=2。 *)
Lemma check_c_sparse_on_valsP (vals : list nat) (c : nat) :
  Sorted Nat.lt vals ->
  reflect (c_sparse_subset (fun i => nth i vals 0%nat) c (seq 0%nat (length vals))
           /\ forall v, In v vals -> (v >= 2)%nat)
          (check_c_sparse_on_vals vals c).
Proof.
  intros HSorted.
  unfold check_c_sparse_on_vals.
  destruct (forallb_adjacent vals (fun a b => ((c * c * a) <=? b)%nat)) eqn:Hall;
    destruct (all_ge_2 vals) eqn:Hge2.
  - left; split.
    + unfold c_sparse_subset. split.
      * apply seq_NoDup.
      * destruct (check_c_sparse_growthP vals c) as [Hg | Hbad]; [| discriminate].
        intros i j Hi Hj Hij.
        assert (Hiv : (i < length vals)%nat).
        { rewrite length_seq in Hi. exact Hi. }
        assert (Hjv : (j < length vals)%nat).
        { rewrite length_seq in Hj. exact Hj. }
        rewrite (@seq_nth (length vals) 0%nat j 0%nat Hjv).
        rewrite (@seq_nth (length vals) 0%nat i 0%nat Hiv).
        rewrite Nat.add_0_l. rewrite Nat.add_0_l.
        exact (Hg i j Hij Hjv).
    + destruct (all_ge_2P vals) as [Hok | Hbad]; [exact Hok | discriminate].
  - right. intros [Hsubset Hge2'].
    destruct (all_ge_2P vals) as [Hok | Hbad]; [discriminate | apply Hbad; exact Hge2'].
  - right. intros [Hsubset Hge2'].
    destruct Hsubset as [Hnodup Hgrowth].
    assert (Hk : forall k, (k < length vals - 1)%nat ->
               (((c * c * nth k vals 0%nat) <=? nth (S k) vals 0%nat)%nat) = true).
    { intros k Hk.
      apply (proj2 (Nat.leb_le (c * c * nth k vals 0%nat) (nth (S k) vals 0%nat))).
      apply INR_le.
      assert (Hiv : (k < length vals)%nat) by lia.
      assert (Hjv : (S k < length vals)%nat) by lia.
      assert (Hg : (INR (nth (nth (S k) (seq 0%nat (length vals)) 0%nat) vals 0%nat) >=
                     INR c * INR c * INR (nth (nth k (seq 0%nat (length vals)) 0%nat) vals 0%nat))%R).
      { apply (Hgrowth k (S k)); [rewrite length_seq; lia | rewrite length_seq; exact Hjv | lia]. }
      rewrite (@seq_nth (length vals) 0%nat (S k) 0%nat Hjv) in Hg.
      rewrite (@seq_nth (length vals) 0%nat k 0%nat Hiv) in Hg.
      rewrite Nat.add_0_l in Hg. rewrite Nat.add_0_l in Hg.
      rewrite <- (mult_INR c c) in Hg.
      rewrite <- (mult_INR (c * c) (nth k vals 0%nat)) in Hg.
      apply Rge_le in Hg.
      exact Hg. }
    assert (Hall' : forallb_adjacent vals (fun a b => ((c * c * a) <=? b)%nat) = true).
    { apply forallb_adjacent_from_nth. exact Hk. }
    rewrite Hall' in Hall. discriminate.
  - right. intros [Hsubset Hge2'].
    destruct Hsubset as [Hnodup Hgrowth].
    assert (Hk : forall k, (k < length vals - 1)%nat ->
               (((c * c * nth k vals 0%nat) <=? nth (S k) vals 0%nat)%nat) = true).
    { intros k Hk.
      apply (proj2 (Nat.leb_le (c * c * nth k vals 0%nat) (nth (S k) vals 0%nat))).
      apply INR_le.
      assert (Hiv : (k < length vals)%nat) by lia.
      assert (Hjv : (S k < length vals)%nat) by lia.
      assert (Hg : (INR (nth (nth (S k) (seq 0%nat (length vals)) 0%nat) vals 0%nat) >=
                     INR c * INR c * INR (nth (nth k (seq 0%nat (length vals)) 0%nat) vals 0%nat))%R).
      { apply (Hgrowth k (S k)); [rewrite length_seq; lia | rewrite length_seq; exact Hjv | lia]. }
      rewrite (@seq_nth (length vals) 0%nat (S k) 0%nat Hjv) in Hg.
      rewrite (@seq_nth (length vals) 0%nat k 0%nat Hiv) in Hg.
      rewrite Nat.add_0_l in Hg. rewrite Nat.add_0_l in Hg.
      rewrite <- (mult_INR c c) in Hg.
      rewrite <- (mult_INR (c * c) (nth k vals 0%nat)) in Hg.
      apply Rge_le in Hg.
      exact Hg. }
    assert (Hall' : forallb_adjacent vals (fun a b => ((c * c * a) <=? b)%nat) = true).
    { apply forallb_adjacent_from_nth. exact Hk. }
    rewrite Hall' in Hall. discriminate.
Qed.

End RuntimeGuards.

(* ============================================================ *)
Module SeqProps.

Import RuntimeGuards.

Record BaseSequence (C : nat) : Type := {
  seq_val : nat -> nat;
  seq_len : nat;
  seq_ge_2 : forall i, (i < seq_len)%nat -> (seq_val i >= 2)%nat;
  seq_sparse_growth : forall i, (i < seq_len - 1)%nat ->
    (INR (seq_val (S i)) > INR C * INR (seq_val i))%R;
  seq_list_Sorted : Sorted Nat.lt (map seq_val (seq 0 seq_len))
}.

(* 生成器：next = max(last*C+1, last+2)，保证严格倍增。
   （修正：原定义 gen_aux C start (S len) (start::nil) 使长度 = S(S len)，
    与 generate_correct 的 length = S len 矛盾；改为 len 次迭代，长度恰为 S len。） *)
Fixpoint gen_aux (C start len : nat) (acc : list nat) : list nat :=
  match len with
  | 0%nat => rev acc
  | S len' =>
    let last := match acc with
                | nil => start
                | h :: _ => h
                end in
    let next := max (last * C + 1) (last + 2) in
    gen_aux C start len' (next :: acc)
  end.

Definition next_idx (last C : nat) : nat := max (last * C + 1) (last + 2).

Definition generate_base_indices (len C start : nat) : list nat :=
  gen_aux C start len (start :: nil).

(* rev 单元素 cons：rev (x::l) = rev l ++ [x]（Rocq 9.0 的 rev 为 Fixpoint，定义性成立） *)
Lemma rev_cons : forall (x : nat) (l : list nat), rev (x :: l) = rev l ++ x :: nil.
Proof.
  intros x l. reflexivity.
Qed.

(* gen_aux 尾部分解：在 h::t 上续建 len 步 = rev t ++ 以 h 为起点续建 len 步 *)
Lemma gen_aux_tail : forall (C len : nat) (start : nat) (h : nat) (t : list nat),
  gen_aux C start len (h :: t) = rev t ++ gen_aux C h len (h :: nil).
Proof.
  induction len as [| len IH]; intros start h t.
  - simpl. reflexivity.
  - simpl. cbv zeta.
    rewrite (IH start (max (h * C + 1) (h + 2)) (h :: t)).
    rewrite (IH h (max (h * C + 1) (h + 2)) (h :: nil)).
    rewrite rev_cons.
    simpl.
    rewrite <- app_assoc.
    reflexivity.
Qed.

(* 递推：generate_base_indices (S len) C start = start :: generate_base_indices len C (next_idx start C) *)
Lemma generate_rec : forall (len C start : nat),
  generate_base_indices (S len) C start =
  start :: generate_base_indices len C (next_idx start C).
Proof.
  intros len C start.
  unfold generate_base_indices. simpl. cbv zeta.
  rewrite (gen_aux_tail C len start (max (start * C + 1) (start + 2)) (start :: nil)).
  simpl. reflexivity.
Qed.

(* 首元素即 start *)
Lemma generate_nth0 : forall (len C start : nat),
  nth 0 (generate_base_indices len C start) 0%nat = start.
Proof.
  induction len as [| len IH]; intros C start.
  - unfold generate_base_indices. simpl. reflexivity.
  - rewrite generate_rec. simpl. reflexivity.
Qed.

(* 生成器规格：相邻 C-稀疏 / Sorted / NoDup / 全 >=2 / 长度 *)
Lemma generate_indices_spec (len C start : nat) :
  (C >= 2)%nat -> (start >= 2)%nat ->
  (forall i, (S i < length (generate_base_indices len C start))%nat ->
     (C * nth i (generate_base_indices len C start) 0%nat <
      nth (S i) (generate_base_indices len C start) 0%nat)%nat) /\
  Sorted Nat.lt (generate_base_indices len C start) /\
  NoDup (generate_base_indices len C start) /\
  all_ge_2 (generate_base_indices len C start) = true /\
  length (generate_base_indices len C start) = S len.
Proof.
  intros HC.
  revert start.
  induction len as [| len IH]; intros start Hstart.
  - (* len = 0：lst = [start] *)
    unfold generate_base_indices. simpl.
    split; [| split; [| split; [| split]]].
    + intros i Hi. simpl in Hi. lia.
    + constructor; constructor.
    + apply NoDup_cons; [simpl; tauto | apply NoDup_nil].
    + unfold all_ge_2.
      change (((2 <=? start)%nat) && true = true).
      rewrite (proj2 (Nat.leb_le 2 start) Hstart). reflexivity.
    + simpl. reflexivity.
  - (* len = S len：lst = start :: lst'，lst' = generate_base_indices len C (next_idx start C) *)
    assert (Hnext2 : (next_idx start C >= 2)%nat).
    { unfold next_idx. apply (Nat.le_trans _ (start + 2) _); [lia | apply Nat.le_max_r]. }
    specialize (IH (next_idx start C) Hnext2).
    cbv zeta in IH.
    destruct IH as [Hadj' [HSort' [HNoDup' [Hge2' Hlen']]]].
    rewrite generate_rec.
    assert (Hadj_all : forall i, (S i < length (start :: generate_base_indices len C (next_idx start C)))%nat ->
               (C * nth i (start :: generate_base_indices len C (next_idx start C)) 0%nat <
                nth (S i) (start :: generate_base_indices len C (next_idx start C)) 0%nat)%nat).
    { intros i Hi.
      destruct i as [| i'].
      - simpl. rewrite generate_nth0. rewrite Nat.mul_comm.
        unfold next_idx.
        apply (Nat.lt_le_trans _ (start * C + 1) _); [lia | apply Nat.le_max_l].
      - apply (Hadj' i'). simpl in Hi. lia.
    }
    split; [| split; [| split; [| split]]].
    + exact Hadj_all.
    + (* Sorted *)
      apply sorted_of_strict_adjacent.
      intros i Hi.
      assert (Hle : (nth i (start :: generate_base_indices len C (next_idx start C)) 0%nat <=
                     C * nth i (start :: generate_base_indices len C (next_idx start C)) 0%nat)%nat).
      { rewrite <- (Nat.mul_1_l (nth i (start :: generate_base_indices len C (next_idx start C)) 0%nat)) at 1.
        apply (Nat.mul_le_mono_r 1 C (nth i (start :: generate_base_indices len C (next_idx start C)) 0%nat)). lia. }
      exact (Nat.le_lt_trans _ _ _ Hle (Hadj_all i Hi)).
    + (* NoDup *)
      apply NoDup_cons.
      * (* ~In start lst'：lst' 元素均 >= next > start *)
        assert (Hstart_lt : (start < next_idx start C)%nat).
        { unfold next_idx. apply (Nat.lt_le_trans _ (start + 2) _); [lia | apply Nat.le_max_r]. }
        intros Hin.
        destruct (In_nth (generate_base_indices len C (next_idx start C)) start 0%nat Hin) as [k [Hk Hkth]].
        assert (Hle0k : (nth 0 (generate_base_indices len C (next_idx start C)) 0%nat <=
                         nth k (generate_base_indices len C (next_idx start C)) 0%nat)%nat).
        { apply (nth_incr (generate_base_indices len C (next_idx start C)) 0 k).
          - intros i Hi.
            assert (Hle : (nth i (generate_base_indices len C (next_idx start C)) 0%nat <=
                           C * nth i (generate_base_indices len C (next_idx start C)) 0%nat)%nat).
            { rewrite <- (Nat.mul_1_l (nth i (generate_base_indices len C (next_idx start C)) 0%nat)) at 1.
              apply (Nat.mul_le_mono_r 1 C (nth i (generate_base_indices len C (next_idx start C)) 0%nat)). lia. }
            exact (Nat.le_lt_trans _ _ _ Hle (Hadj' i Hi)).
          - lia.
          - exact Hk. }
        rewrite generate_nth0 in Hle0k.
        rewrite Hkth in Hle0k.
        apply (Nat.lt_irrefl start).
        apply (Nat.lt_le_trans _ (next_idx start C) _); [exact Hstart_lt | exact Hle0k].
      * exact HNoDup'.
    + (* all_ge_2 *)
      unfold all_ge_2.
      change (((2 <=? start)%nat) && List.forallb (fun v => (2 <=? v)%nat) (generate_base_indices len C (next_idx start C)) = true).
      rewrite (proj2 (Nat.leb_le 2 start) Hstart).
      unfold all_ge_2 in Hge2'. rewrite Hge2'. reflexivity.
    + (* length *)
      simpl. rewrite Hlen'. reflexivity.
Qed.

(* 生成器正确性：满足 Sorted / NoDup / >=2 / 线性稀疏增长 / 长度 *)
Theorem generate_correct (len C start : nat) :
  (C >= 2)%nat -> (start >= 2)%nat ->
  let lst := generate_base_indices len C start in
  Sorted Nat.lt lst /\ NoDup lst /\ all_ge_2 lst = true /\
  check_sparse_growth lst C = true /\ length lst = S len.
Proof.
  intros HC Hstart.
  pose proof (generate_indices_spec len C start HC Hstart) as Hspec.
  cbv zeta in Hspec.
  destruct Hspec as [Hadj [HSort [HNoDup [Hge2 Hlen]]]].
  split; [| split; [| split; [| split]]].
  - exact HSort.
  - exact HNoDup.
  - exact Hge2.
  - unfold check_sparse_growth.
    apply forallb_adjacent_from_nth.
    intros k Hk.
    apply Nat.ltb_lt.
    apply (Hadj k). lia.
  - exact Hlen.
Qed.

(* ---------- 全局基序列（内部序列路线）：迭代 next_idx，全局增长 ---------- *)

Fixpoint base_seq (C start : nat) (i : nat) : nat :=
  match i with
  | 0%nat => start
  | S i' => next_idx (base_seq C start i') C
  end.

(* 全局增长：任意 i 有 base_seq i >= 2 且 INR (base_seq (S i)) > INR C * INR (base_seq i) *)
Lemma base_seq_global_growth (C start : nat) :
  (C >= 2)%nat -> (start >= 2)%nat ->
  (forall i, (base_seq C start i >= 2)%nat /\
             (INR (base_seq C start (S i)) > INR C * INR (base_seq C start i))%R).
Proof.
  intros HC Hstart.
  assert (Hnext_gt : forall x, (INR (next_idx x C) > INR C * INR x)%R).
  { intros x.
    assert (Hge1 : (INR (next_idx x C) >= INR (x * C + 1))%R).
    { apply Rle_ge. apply le_INR. unfold next_idx. apply Nat.le_max_l. }
    assert (Hgt : (INR (x * C + 1) > INR (x * C))%R).
    { apply lt_INR. lia. }
    assert (Heq : (INR (x * C) = INR C * INR x)%R).
    { rewrite mult_INR. rewrite Rmult_comm. reflexivity. }
    assert (Hr : (INR (x * C) < INR (next_idx x C))%R).
    { apply (Rlt_le_trans _ (INR (x * C + 1)) _); [apply Rgt_lt; exact Hgt | apply Rge_le; exact Hge1]. }
    rewrite Heq in Hr. exact Hr. }
  assert (Hnext_ge2 : forall x, (next_idx x C >= 2)%nat).
  { intros x. unfold next_idx. apply (Nat.le_trans _ (x + 2) _); [lia | apply Nat.le_max_r]. }
  intros i.
  induction i as [| i IH].
  - split.
    + simpl. exact Hstart.
    + simpl. apply Hnext_gt.
  - split.
    + simpl. apply Hnext_ge2.
    + simpl. apply Hnext_gt.
Qed.

(* 平移：base_seq C start (S k) = base_seq C (next_idx start C) k *)
Lemma base_seq_shift (C start : nat) (k : nat) :
  base_seq C start (S k) = base_seq C (next_idx start C) k.
Proof.
  induction k as [| k IH].
  - simpl. reflexivity.
  - change (next_idx (base_seq C start (S k)) C = next_idx (base_seq C (next_idx start C) k) C).
    rewrite IH. reflexivity.
Qed.

(* seq 平移：seq (S start) len = map S (seq start len) *)
Lemma seq_shift_gen (len start : nat) : seq (S start) len = map S (seq start len).
Proof.
  revert start.
  induction len as [| len IH]; intros start.
  - simpl. reflexivity.
  - simpl. rewrite (IH (S start)). reflexivity.
Qed.

(* 生成器与全局序列等价：generate_base_indices len C start = map (base_seq C start) (seq 0 (S len)) *)
Lemma generate_eq_map (len C start : nat) :
  generate_base_indices len C start = map (base_seq C start) (seq 0%nat (S len)).
Proof.
  revert C start.
  induction len as [| len IH]; intros C start.
  - unfold generate_base_indices. simpl. reflexivity.
  - rewrite generate_rec. rewrite IH.
    change (start :: map (base_seq C (next_idx start C)) (seq 0%nat (S len)) =
            start :: map (base_seq C start) (seq 1%nat (S len))).
    f_equal.
    rewrite (seq_shift_gen (S len) 0%nat). rewrite map_map. apply map_ext.
    intros k. symmetry. apply (base_seq_shift C start k).
Qed.


(* ============================================================
   P1a：生成器 → BaseSequence 记录（construct_base_sequence 真 Qed）
   ============================================================ *)


(* P1a：map_nth_seq 通用引理（map (fun i => nth i lst 0) (seq 0 (length lst)) = lst） *)
Lemma map_nth_seq (l : list nat) :
  map (fun i => nth i l 0%nat) (seq 0%nat (length l)) = l.
Proof.
  induction l as [| h t IH].
  - reflexivity.
  - simpl.
    rewrite (seq_shift_gen (length t) 0%nat).
    rewrite map_map.
    change (h :: map (fun k => nth k t 0%nat) (seq 0%nat (length t)) = h :: t).
    f_equal. exact IH.
Qed.

(* P1a：生成器全局序列的前缀是 Sorted（generate_eq_map + generate_indices_spec） *)
Lemma base_seq_list_Sorted (len C start : nat) :
  (C >= 2)%nat -> (start >= 2)%nat ->
  Sorted Nat.lt (map (base_seq C start) (seq 0%nat (S len))).
Proof.
  intros HC Hstart.
  rewrite <- (generate_eq_map len C start).
  destruct (generate_indices_spec len C start HC Hstart) as [Hadj [HSort [HNoDup [Hge2 Hlen]]]].
  exact HSort.
Qed.

(* P1a：construct_base_sequence——由生成器构造 BaseSequence 记录（doc Step2 的构造，真 Qed） *)
Definition construct_base_sequence (len C start : nat)
  (HC : (C >= 2)%nat) (Hstart : (start >= 2)%nat) : BaseSequence C :=
  {| seq_val := base_seq C start;
     seq_len := S len;
     seq_ge_2 := fun i _ => proj1 (base_seq_global_growth C start HC Hstart i);
     seq_sparse_growth := fun i _ => proj2 (base_seq_global_growth C start HC Hstart i);
     seq_list_Sorted := base_seq_list_Sorted len C start HC Hstart |}.

(* 构造正确性：记录的 Sorted 列表恰为生成器前缀（generate_eq_map 的 BaseSequence 视角） *)
Lemma construct_base_sequence_map (len C start : nat)
  (HC : (C >= 2)%nat) (Hstart : (start >= 2)%nat) :
  map (seq_val C (construct_base_sequence len C start HC Hstart))
      (seq 0%nat (seq_len C (construct_base_sequence len C start HC Hstart))) =
  generate_base_indices len C start.
Proof.
  unfold construct_base_sequence. simpl.
  symmetry. apply (generate_eq_map len C start).
Qed.


(* P3b 需要：生成器全局序列严格增（从全局增长 + C>=2 + 值>=2 推出） *)
Lemma base_seq_strictly_increasing (C start : nat) :
  (C >= 2)%nat -> (start >= 2)%nat ->
  forall i, (base_seq C start i < base_seq C start (S i))%nat.
Proof.
  intros HC Hstart i.
  apply (INR_lt _ _).
  assert (Hgt : (INR (base_seq C start (S i)) > INR C * INR (base_seq C start i))%R).
  { apply (proj2 (base_seq_global_growth C start HC Hstart i)). }
  assert (Hge2i : (base_seq C start i >= 2)%nat).
  { apply (proj1 (base_seq_global_growth C start HC Hstart i)). }
  assert (HC1 : (1 <= INR C)%R).
  { change (1%R) with (INR 1). apply le_INR. lia. }
  assert (Hpos : (0 < INR (base_seq C start i))%R).
  { apply lt_0_INR. lia. }
  assert (Hle : (INR (base_seq C start i) <= INR C * INR (base_seq C start i))%R).
  { assert (Hdiff : 0 <= (INR C - 1) * INR (base_seq C start i)).
    { apply Rmult_le_pos.
      - lra.
      - apply Rlt_le. exact Hpos. }
    nra. }
  apply (Rle_lt_trans _ (INR C * INR (base_seq C start i)) _);
    [exact Hle | apply Rgt_lt; exact Hgt].
Qed.
End SeqProps.

(* ============================================================ *)
Module PSA_Pipeline.

Import RuntimeGuards.
Import ExtendedTheorems.

(* 修正版核心定理：守护断言通过 ⟹ 库内衰减界生效（decay_bound 直接实例）。
   形状与 psi_unconditional_basis 一致：全函数 seq + 索引列表 I，
   从而可 exact decay_bound，无需处理 nth 越界填充。 *)
Theorem psa_pipeline_decay (seq : nat -> nat) (I : list nat) (C : nat) :
  (C >= 2)%nat ->
  (forall i, (seq i >= 2)%nat) ->
  (forall i, (INR (seq (S i)) > INR C * INR (seq i))%R) ->
  NoDup I -> Sorted Nat.lt I ->
  forall i j, i <> j -> (i < length I)%nat -> (j < length I)%nat ->
    Cnorm (Csum (fun k => psi (nth i (map seq I) 0%nat) k *c Cconj (psi (nth j (map seq I) 0%nat) k))
              (Nat.sub (seq (fold_right Nat.max 0%nat I)) 1))
    <= 2 / ((sqrt (INR C)) ^ (Z.abs_nat (Z.of_nat i - Z.of_nat j))).
Proof.
  intros HC Hge2 Hsparse Hnodup Hsorted i j Hij Hi Hj.
  exact (decay_bound seq I C HC Hge2 Hsparse Hnodup Hsorted i j Hij Hi Hj).
Qed.

(* 线性无关守护版：全索引子集上，组合恒零 ⟹ 系数全零（psi_linear_independent 直接实例） *)
Theorem psa_pipeline_linindep (vals : list nat) (coeffs : list Complex) :
  (forall v, In v vals -> (v >= 2)%nat) ->
  NoDup vals ->
  length vals = length coeffs ->
  (forall k, Csum (fun i => nth i coeffs C0 *c psi (nth i vals 0%nat) k) (length vals) = C0) ->
  forall i, (i < length vals)%nat -> nth i coeffs C0 = C0.
Proof.
  intros Hge2 Hdup Hlen Heq i Hi.
  exact (psi_linear_independent vals coeffs Hge2 Hdup Hlen Heq i Hi).
Qed.

(* ============================================================
   P2：外部守卫路线（有限化 decay）—— 运行时守护断言 ⟹ 衰减界
   ============================================================ *)

(* 守卫的相邻布尔 ⟹ I 相邻 R 级增长（forallb_adjacent_nth，无需 Sorted） *)
Lemma guard_adjacent_growth (seq : nat -> nat) (I : list nat) (C : nat) :
  check_sparse_growth (map seq I) C = true ->
  forall k, (S k < length I)%nat ->
    (INR (seq (nth (S k) I 0%nat)) > INR C * INR (seq (nth k I 0%nat)))%R.
Proof.
  intros Hguard k Hk.
  pose proof (forallb_adjacent_nth (map seq I) (fun a b => ((C * a) <? b)%nat) Hguard k) as Hltb.
  assert (Hkl : (k < length (map seq I) - 1)%nat).
  { rewrite length_map. lia. }
  specialize (Hltb Hkl).
  apply Nat.ltb_lt in Hltb.
  apply lt_INR in Hltb.
  rewrite mult_INR in Hltb.
  assert (Hnth_k : (nth k (map seq I) 0%nat = seq (nth k I 0%nat))%nat).
  { apply (H_nth_map nat nat seq I 0%nat 0%nat k). lia. }
  assert (Hnth_sk : (nth (S k) (map seq I) 0%nat = seq (nth (S k) I 0%nat))%nat).
  { apply (H_nth_map nat nat seq I 0%nat 0%nat (S k)). lia. }
  rewrite Hnth_k in Hltb. rewrite Hnth_sk in Hltb.
  exact Hltb.
Qed.

(* 守卫的 all_ge_2 ⟹ I 元素值 >= 2 *)
Lemma guard_ge2_map (seq : nat -> nat) (I : list nat) :
  all_ge_2 (map seq I) = true ->
  forall i, (i < length I)%nat -> (seq (nth i I 0%nat) >= 2)%nat.
Proof.
  intros Hge2 i Hi.
  destruct (all_ge_2P (map seq I)) as [Hok | Hbad]; [| discriminate].
  assert (Hnth : (nth i (map seq I) 0%nat = seq (nth i I 0%nat))%nat).
  { apply (H_nth_map nat nat seq I 0%nat 0%nat i). exact Hi. }
  rewrite <- Hnth.
  apply Hok. apply nth_In. rewrite length_map. exact Hi.
Qed.

(* 排序严格列表上 nth 逆序：值小 ⟹ 索引小 *)
Lemma nth_lt_backward (I : list nat) (i j : nat) :
  Sorted Nat.lt I ->
  (i < length I)%nat -> (j < length I)%nat ->
  (nth i I 0%nat < nth j I 0%nat)%nat -> (i < j)%nat.
Proof.
  intros HSorted Hi Hj Hlt.
  destruct (Nat.lt_trichotomy i j) as [Hij | [Heq | Hji]].
  - exact Hij.
  - exfalso. subst j. exact (Nat.lt_irrefl (nth i I 0%nat) Hlt).
  - exfalso. apply (Nat.lt_asymm (nth i I 0%nat) (nth j I 0%nat) Hlt
                   (nth_sorted_strict_lt I j i HSorted Hji Hj Hi)).
Qed.

(* 非空列表的 max 是元素 *)
Lemma fold_right_max_In (I : list nat) :
  (0 < length I)%nat -> In (fold_right Nat.max 0%nat I) I.
Proof.
  induction I as [| h t IH].
  - simpl. lia.
  - simpl. destruct (Nat.le_gt_cases (fold_right Nat.max 0%nat t) h) as [Hh | Hgt].
    + left. rewrite (Nat.max_l h (fold_right Nat.max 0%nat t) Hh). reflexivity.
    + right. rewrite (Nat.max_r h (fold_right Nat.max 0%nat t) (Nat.lt_le_incl _ _ Hgt)).
      assert (Htlen : (0 < length t)%nat).
      { destruct t; simpl in Hgt; simpl; lia. }
      apply IH; exact Htlen.
Qed.

(* I 链严格增：相邻 I 元素 R 级增长 + C>=2 ⟹ 任意 I 元素对严格增 *)
Lemma I_chain_strict (seq : nat -> nat) (I : list nat) (C : nat) :
  (C >= 2)%nat ->
  (forall k, (S k < length I)%nat ->
     (INR (seq (nth (S k) I 0%nat)) > INR C * INR (seq (nth k I 0%nat)))%R) ->
  forall i j, (i < j)%nat -> (j < length I)%nat ->
    (seq (nth i I 0%nat) < seq (nth j I 0%nat))%nat.
Proof.
  intros HC Hgrowth i j Hij.
  assert (Hstep : forall k, (S k < length I)%nat ->
                 (seq (nth k I 0%nat) < seq (nth (S k) I 0%nat))%nat).
  { intros k Hk. apply INR_lt.
    assert (Hgt : (INR (seq (nth (S k) I 0%nat)) > INR C * INR (seq (nth k I 0%nat)))%R).
    { apply Hgrowth. exact Hk. }
    apply Rgt_lt in Hgt.
    assert (Hle : (INR (seq (nth k I 0%nat)) <= INR C * INR (seq (nth k I 0%nat)))%R).
    { rewrite <- mult_INR. apply le_INR.
      rewrite <- (Nat.mul_1_l (seq (nth k I 0%nat))) at 1.
      apply (Nat.mul_le_mono_r 1 C (seq (nth k I 0%nat))). lia. }
    apply (Rle_lt_trans _ (INR C * INR (seq (nth k I 0%nat))) _); [exact Hle | exact Hgt]. }
  induction Hij as [| m Hij' IH]; intros Hjlen.
  - apply Hstep. exact Hjlen.
  - apply (Nat.lt_trans _ (seq (nth m I 0%nat)) _).
    + apply IH. lia.
    + apply Hstep. exact Hjlen.
Qed.

(* I 链复合增长：相邻 R 级增长 ⟹ 任意对的指数界（指数 = 索引距离） *)
Lemma I_chain_compound (seq : nat -> nat) (I : list nat) (C : nat) :
  (C >= 2)%nat ->
  (forall k, (S k < length I)%nat ->
     (INR (seq (nth (S k) I 0%nat)) > INR C * INR (seq (nth k I 0%nat)))%R) ->
  forall i j, (i < j)%nat -> (j < length I)%nat ->
    (INR (seq (nth j I 0%nat)) >= (INR C) ^ (j - i) * INR (seq (nth i I 0%nat)))%R.
Proof.
  intros HC Hgrowth i j Hij.
  induction Hij as [| m Hij' IH]; intros Hjlen.
  - (* j = S i：指数 1 *)
    assert (Hd : (S i - i = 1)%nat) by lia.
    rewrite Hd.
    simpl. rewrite Rmult_1_r.
    assert (Hgt : (INR (seq (nth (S i) I 0%nat)) > INR C * INR (seq (nth i I 0%nat)))%R).
    { apply Hgrowth. exact Hjlen. }
    apply Rle_ge. apply Rlt_le. apply Rgt_lt. exact Hgt.
  - (* j = S m *)
    assert (Hgt : (INR (seq (nth (S m) I 0%nat)) > INR C * INR (seq (nth m I 0%nat)))%R).
    { apply Hgrowth. exact Hjlen. }
    assert (HIH : (INR (seq (nth m I 0%nat)) >= (INR C) ^ (m - i) * INR (seq (nth i I 0%nat)))%R).
    { apply IH. lia. }
    assert (Hmid : (INR C * INR (seq (nth m I 0%nat)) >=
                    (INR C * (INR C) ^ (m - i)) * INR (seq (nth i I 0%nat)))%R).
    { apply Rle_ge. rewrite Rmult_assoc.
      apply (Rmult_le_compat_l (INR C) ((INR C) ^ (m - i) * INR (seq (nth i I 0%nat))) (INR (seq (nth m I 0%nat)))).
      - apply pos_INR; lia.
      - apply Rge_le. exact HIH. }
    assert (Hd : (S m - i = S (m - i))%nat) by lia.
    rewrite Hd.
    change ((INR (seq (nth (S m) I 0%nat)) >=
             (INR C * (INR C) ^ (m - i)) * INR (seq (nth i I 0%nat)))%R).
    apply Rle_ge. apply Rlt_le.
    apply (Rle_lt_trans _ (INR C * INR (seq (nth m I 0%nat))) _);
      [apply Rge_le; exact Hmid | apply Rgt_lt; exact Hgt].
Qed.

(* 截断：I 元素 a 的 psi 内积求和可截到 seq a（seq a < seq (max I) 由 I 链给出） *)
Lemma Csum_psi_conj_truncate_fin (seq : nat -> nat) (I : list nat) (C : nat) (i n1 n2 : nat) :
  (C >= 2)%nat ->
  (forall k, (S k < length I)%nat ->
     (INR (seq (nth (S k) I 0%nat)) > INR C * INR (seq (nth k I 0%nat)))%R) ->
  Sorted Nat.lt I ->
  (i < length I)%nat ->
  (nth i I 0%nat < fold_right Nat.max 0%nat I)%nat ->
  n1 = seq (nth i I 0%nat) ->
  Csum (fun k : nat => psi n1 k *c Cconj (psi n2 k)) (seq (fold_right Nat.max 0%nat I) - 1) =
  Csum (fun k : nat => psi n1 k *c Cconj (psi n2 k)) n1.
Proof.
  intros HC Hgrowth HSorted Hi Ha_lt_max Hn1. subst n1.
  set (a := nth i I 0%nat) in *.
  set (N := seq (fold_right Nat.max 0%nat I)).
  assert (Hlen_pos : (0 < length I)%nat) by lia.
  assert (Hseq_lt : (seq a < N)%nat).
  { unfold N.
    destruct (In_nth I (fold_right Nat.max 0%nat I) 0%nat (fold_right_max_In I Hlen_pos)) as [m [Hm_len Hm_th]].
    assert (Ha_lt_m : (nth i I 0%nat < nth m I 0%nat)%nat).
    { rewrite Hm_th. exact Ha_lt_max. }
    assert (Him : (i < m)%nat).
    { apply (nth_lt_backward I i m HSorted Hi Hm_len). exact Ha_lt_m. }
    rewrite <- Hm_th.
    apply (I_chain_strict seq I C HC Hgrowth i m Him Hm_len). }
  assert (Hle_pred : (seq a <= N - 1)%nat) by lia.
  set (f := fun k : nat => psi (seq a) k *c Cconj (psi n2 k)).
  assert (Hzero : forall k : nat, (seq a <= k)%nat -> f k = C0).
  { intros k Hk. unfold f. rewrite (psi_ge_n_zero (seq a) k Hk). rewrite Cmul_0_l. reflexivity. }
  assert (Hzero_interval : forall k, (seq a <= k < N - 1)%nat -> f k = C0).
  { intros k [Hk1 _]. apply Hzero; exact Hk1. }
  rewrite (Csum_trunc_tail f (seq a) (N - 1) Hle_pred Hzero_interval).
  reflexivity.
Qed.

(* 有限化 one_factor：全局增长换成守卫级有限前提 *)
Lemma decay_bound_finite_one_factor (seq : nat -> nat) (I : list nat) (C : nat)
  (HC : (C >= 2)%nat)
  (Hseq_ge2 : forall i, (i < length I)%nat -> (seq (nth i I 0%nat) >= 2)%nat)
  (Hsparse : forall k, (S k < length I)%nat ->
     (INR (seq (nth (S k) I 0%nat)) > INR C * INR (seq (nth k I 0%nat)))%R)
  (Hsorted : Sorted Nat.lt I)
  (i j : nat) (Hij : (i < j)%nat) (Hi_len : (i < length I)%nat) (Hj_len : (j < length I)%nat) :
  Cnorm (Csum (fun k : nat => psi (seq (nth i I 0%nat)) k *c Cconj (psi (seq (nth j I 0%nat)) k))
              ((seq (fold_right Nat.max 0%nat I) - 1)%nat))
  <= 2 * / ((sqrt (INR C)) ^ (Z.abs_nat (Z.of_nat i - Z.of_nat j))).
Proof.
  set (a := nth i I 0%nat); set (b := nth j I 0%nat).
  set (n1 := seq a); set (n2 := seq b).
  assert (Ha_lt_b : (a < b)%nat).
  { unfold a, b. apply (nth_sorted_strict_lt I i j Hsorted Hij Hi_len Hj_len). }
  assert (Hn1_lt_n2 : (n1 < n2)%nat).
  { unfold n1, n2. apply (I_chain_strict seq I C HC Hsparse i j Hij Hj_len). }
  assert (Hn1_ge2 : (n1 >= 2)%nat) by (unfold n1, a; apply Hseq_ge2; exact Hi_len).
  assert (Hn2_ge2 : (n2 >= 2)%nat) by (unfold n2, b; apply Hseq_ge2; exact Hj_len).
  assert (Ha_lt_max : (a < fold_right Nat.max 0%nat I)%nat).
  { apply Nat.lt_le_trans with b; [exact Ha_lt_b | ].
    apply fold_right_max_ge with (l := I); apply nth_In; exact Hj_len. }
  assert (Hsum_eq1 :
    Csum (fun k : nat => psi (seq a) k *c Cconj (psi (seq b) k)) (seq (fold_right Nat.max 0%nat I) - 1) =
    Csum (fun k : nat => psi n1 k *c Cconj (psi n2 k)) n1).
  { apply (Csum_psi_conj_truncate_fin seq I C i (seq a) (seq b) HC Hsparse Hsorted Hi_len Ha_lt_max).
    reflexivity. }
  replace (Csum (fun k : nat => psi n1 k *c Cconj (psi n2 k)) (seq (fold_right Nat.max 0%nat I) - 1))
    with (Csum (fun k : nat => psi (seq a) k *c Cconj (psi (seq b) k)) (seq (fold_right Nat.max 0%nat I) - 1))
    by (unfold n1, n2; reflexivity).
  rewrite Hsum_eq1.
  assert (Hinner_bound :
    Cnorm (Csum (fun k : nat => psi n1 k *c Cconj (psi n2 k)) n1)
    <= sqrt (INR n1 * INR n2) / (2 * (INR n2 - INR n1)) + 1 / sqrt (INR n1 * INR n2)).
  { apply (inner_product_norm_bound_general_n n1 n2); [exact Hn1_ge2 | exact Hn2_ge2 | exact Hn1_lt_n2]. }
  set (d := (j - i)%nat).
  assert (Hd_pos : (d >= 1)%nat) by (unfold d; lia).
  assert (Hint_exp : INR n2 >= (INR C) ^ d * INR n1).
  { unfold d, n1, n2. apply (I_chain_compound seq I C HC Hsparse i j Hij Hj_len). }
  assert (Hsqrt_bound : sqrt (INR n1 * INR n2) / (2 * (INR n2 - INR n1)) <= / ((sqrt (INR C)) ^ d)).
  { apply (sqrt_div_bound C d n1 n2 HC Hd_pos Hint_exp). }
  assert (Hinv_bound : 1 / sqrt (INR n1 * INR n2) <= / ((sqrt (INR C)) ^ d)).
  { apply (sparse_sqrt_inv_bound C n1 n2 d HC Hn1_ge2 Hd_pos Hint_exp). }
  assert (Hsum_bound : sqrt (INR n1 * INR n2) / (2 * (INR n2 - INR n1)) +
                       1 / sqrt (INR n1 * INR n2) <=
                       2 * / ((sqrt (INR C)) ^ d)) by nra.
  assert (Heq_abs : Z.abs_nat (Z.of_nat i - Z.of_nat j) = d) by (unfold d; lia).
  rewrite Heq_abs.
  eapply Rle_trans; [exact Hinner_bound | exact Hsum_bound].
Qed.

(* 外部守卫主定理：运行时守护断言全部通过 ⟹ 任意 I 内对的衰减界成立 *)
Theorem psa_guard_decay (seq : nat -> nat) (I : list nat) (C : nat) :
  (C >= 2)%nat -> NoDup I -> Sorted Nat.lt I ->
  all_ge_2 (map seq I) = true ->
  check_sparse_growth (map seq I) C = true ->
  forall i j, i <> j -> (i < length I)%nat -> (j < length I)%nat ->
    Cnorm (Csum (fun k => psi (nth i (map seq I) 0%nat) k *c Cconj (psi (nth j (map seq I) 0%nat) k))
                (seq (fold_right Nat.max 0%nat I) - 1))
    <= 2 / ((sqrt (INR C)) ^ (Z.abs_nat (Z.of_nat i - Z.of_nat j))).
Proof.
  intros HC Hnodup Hsorted Hge2 Hguard i j Hneq Hi_len Hj_len.
  assert (Hseq_ge2_fin : forall i, (i < length I)%nat -> (seq (nth i I 0%nat) >= 2)%nat).
  { exact (guard_ge2_map seq I Hge2). }
  assert (Hgrowth_fin : forall k, (S k < length I)%nat ->
     (INR (seq (nth (S k) I 0%nat)) > INR C * INR (seq (nth k I 0%nat)))%R).
  { exact (guard_adjacent_growth seq I C Hguard). }
  destruct (Nat.lt_trichotomy i j) as [Hij | [Heq | Hji]].
  - assert (Hnthi : (nth i (map seq I) 0%nat = seq (nth i I 0%nat))%nat).
    { apply (H_nth_map nat nat seq I 0%nat 0%nat i). exact Hi_len. }
    assert (Hnthj : (nth j (map seq I) 0%nat = seq (nth j I 0%nat))%nat).
    { apply (H_nth_map nat nat seq I 0%nat 0%nat j). exact Hj_len. }
    rewrite Hnthi, Hnthj.
    apply (decay_bound_finite_one_factor seq I C HC Hseq_ge2_fin Hgrowth_fin Hsorted i j Hij Hi_len Hj_len).
  - exfalso. apply Hneq. exact Heq.
  - assert (Hnthi : (nth i (map seq I) 0%nat = seq (nth i I 0%nat))%nat).
    { apply (H_nth_map nat nat seq I 0%nat 0%nat i). exact Hi_len. }
    assert (Hnthj : (nth j (map seq I) 0%nat = seq (nth j I 0%nat))%nat).
    { apply (H_nth_map nat nat seq I 0%nat 0%nat j). exact Hj_len. }
    rewrite Hnthi, Hnthj.
    rewrite (Cnorm_Csum_conj_sym (fun k => psi (seq (nth i I 0%nat)) k)
                                 (fun k => psi (seq (nth j I 0%nat)) k)
                                 (seq (fold_right Nat.max 0%nat I) - 1)).
    assert (Heq : Z.abs_nat (Z.of_nat i - Z.of_nat j) = Z.abs_nat (Z.of_nat j - Z.of_nat i)).
    { replace (Z.of_nat i - Z.of_nat j)%Z with (- (Z.of_nat j - Z.of_nat i))%Z by ring.
      rewrite Z_abs_nat_opp. reflexivity. }
    rewrite Heq.
    apply (decay_bound_finite_one_factor seq I C HC Hseq_ge2_fin Hgrowth_fin Hsorted j i Hji Hj_len Hi_len).
Qed.



(* 有限化 one_factor 的 1/ 版：inner_product_norm_bound_full（单项界）⟹ 系数 1/ *)
Lemma decay_bound_finite_one_factor_tight (seq : nat -> nat) (I : list nat) (C : nat)
  (HC : (C >= 2)%nat)
  (Hseq_ge2 : forall i, (i < length I)%nat -> (seq (nth i I 0%nat) >= 2)%nat)
  (Hsparse : forall k, (S k < length I)%nat ->
     (INR (seq (nth (S k) I 0%nat)) > INR C * INR (seq (nth k I 0%nat)))%R)
  (Hsorted : Sorted Nat.lt I)
  (i j : nat) (Hij : (i < j)%nat) (Hi_len : (i < length I)%nat) (Hj_len : (j < length I)%nat) :
  Cnorm (Csum (fun k : nat => psi (seq (nth i I 0%nat)) k *c Cconj (psi (seq (nth j I 0%nat)) k))
              ((seq (fold_right Nat.max 0%nat I) - 1)%nat))
  <= / ((sqrt (INR C)) ^ (Z.abs_nat (Z.of_nat i - Z.of_nat j))).
Proof.
  set (a := nth i I 0%nat); set (b := nth j I 0%nat).
  set (n1 := seq a); set (n2 := seq b).
  assert (Ha_lt_b : (a < b)%nat).
  { unfold a, b. apply (nth_sorted_strict_lt I i j Hsorted Hij Hi_len Hj_len). }
  assert (Hn1_lt_n2 : (n1 < n2)%nat).
  { unfold n1, n2. apply (I_chain_strict seq I C HC Hsparse i j Hij Hj_len). }
  assert (Hn1_ge2 : (n1 >= 2)%nat) by (unfold n1, a; apply Hseq_ge2; exact Hi_len).
  assert (Hn2_ge2 : (n2 >= 2)%nat) by (unfold n2, b; apply Hseq_ge2; exact Hj_len).
  assert (Ha_lt_max : (a < fold_right Nat.max 0%nat I)%nat).
  { apply Nat.lt_le_trans with b; [exact Ha_lt_b | ].
    apply fold_right_max_ge with (l := I); apply nth_In; exact Hj_len. }
  assert (Hsum_eq1 :
    Csum (fun k : nat => psi (seq a) k *c Cconj (psi (seq b) k)) (seq (fold_right Nat.max 0%nat I) - 1) =
    Csum (fun k : nat => psi n1 k *c Cconj (psi n2 k)) n1).
  { apply (Csum_psi_conj_truncate_fin seq I C i (seq a) (seq b) HC Hsparse Hsorted Hi_len Ha_lt_max).
    reflexivity. }
  replace (Csum (fun k : nat => psi n1 k *c Cconj (psi n2 k)) (seq (fold_right Nat.max 0%nat I) - 1))
    with (Csum (fun k : nat => psi (seq a) k *c Cconj (psi (seq b) k)) (seq (fold_right Nat.max 0%nat I) - 1))
    by (unfold n1, n2; reflexivity).
  rewrite Hsum_eq1.
  (* 1/ 版：单项内积界（对比 2/ 版的 general_n 两项界） *)
  assert (Hinner_bound :
    Cnorm (Csum (fun k : nat => psi n1 k *c Cconj (psi n2 k)) n1)
    <= sqrt (INR n1 * INR n2) / (2 * (INR n2 - INR n1))).
  { apply (inner_product_norm_bound_full n1 n2); [exact Hn1_ge2 | exact Hn2_ge2 | exact Hn1_lt_n2]. }
  set (d := (j - i)%nat).
  assert (Hd_pos : (d >= 1)%nat) by (unfold d; lia).
  assert (Hint_exp : INR n2 >= (INR C) ^ d * INR n1).
  { unfold d, n1, n2. apply (I_chain_compound seq I C HC Hsparse i j Hij Hj_len). }
  assert (Hsqrt_bound : sqrt (INR n1 * INR n2) / (2 * (INR n2 - INR n1)) <= / ((sqrt (INR C)) ^ d)).
  { apply (sqrt_div_bound C d n1 n2 HC Hd_pos Hint_exp). }
  assert (Heq_abs : Z.abs_nat (Z.of_nat i - Z.of_nat j) = d) by (unfold d; lia).
  rewrite Heq_abs.
  eapply Rle_trans; [exact Hinner_bound | exact Hsqrt_bound].
Qed.

(* 守卫主定理 1/ 版：运行时守护断言全部通过 ⟹ 任意 I 内对的衰减界（系数 1/） *)
Theorem psa_guard_decay_tight (seq : nat -> nat) (I : list nat) (C : nat) :
  (C >= 2)%nat -> NoDup I -> Sorted Nat.lt I ->
  all_ge_2 (map seq I) = true ->
  check_sparse_growth (map seq I) C = true ->
  forall i j, i <> j -> (i < length I)%nat -> (j < length I)%nat ->
    Cnorm (Csum (fun k => psi (nth i (map seq I) 0%nat) k *c Cconj (psi (nth j (map seq I) 0%nat) k))
                (seq (fold_right Nat.max 0%nat I) - 1))
    <= / ((sqrt (INR C)) ^ (Z.abs_nat (Z.of_nat i - Z.of_nat j))).
Proof.
  intros HC Hnodup Hsorted Hge2 Hguard i j Hneq Hi_len Hj_len.
  assert (Hseq_ge2_fin : forall i, (i < length I)%nat -> (seq (nth i I 0%nat) >= 2)%nat).
  { exact (guard_ge2_map seq I Hge2). }
  assert (Hgrowth_fin : forall k, (S k < length I)%nat ->
     (INR (seq (nth (S k) I 0%nat)) > INR C * INR (seq (nth k I 0%nat)))%R).
  { exact (guard_adjacent_growth seq I C Hguard). }
  destruct (Nat.lt_trichotomy i j) as [Hij | [Heq | Hji]].
  - assert (Hnthi : (nth i (map seq I) 0%nat = seq (nth i I 0%nat))%nat).
    { apply (H_nth_map nat nat seq I 0%nat 0%nat i). exact Hi_len. }
    assert (Hnthj : (nth j (map seq I) 0%nat = seq (nth j I 0%nat))%nat).
    { apply (H_nth_map nat nat seq I 0%nat 0%nat j). exact Hj_len. }
    rewrite Hnthi, Hnthj.
    apply (decay_bound_finite_one_factor_tight seq I C HC Hseq_ge2_fin Hgrowth_fin Hsorted i j Hij Hi_len Hj_len).
  - exfalso. apply Hneq. exact Heq.
  - assert (Hnthi : (nth i (map seq I) 0%nat = seq (nth i I 0%nat))%nat).
    { apply (H_nth_map nat nat seq I 0%nat 0%nat i). exact Hi_len. }
    assert (Hnthj : (nth j (map seq I) 0%nat = seq (nth j I 0%nat))%nat).
    { apply (H_nth_map nat nat seq I 0%nat 0%nat j). exact Hj_len. }
    rewrite Hnthi, Hnthj.
    rewrite (Cnorm_Csum_conj_sym (fun k => psi (seq (nth i I 0%nat)) k)
                                 (fun k => psi (seq (nth j I 0%nat)) k)
                                 (seq (fold_right Nat.max 0%nat I) - 1)).
    assert (Heq : Z.abs_nat (Z.of_nat i - Z.of_nat j) = Z.abs_nat (Z.of_nat j - Z.of_nat i)).
    { replace (Z.of_nat i - Z.of_nat j)%Z with (- (Z.of_nat j - Z.of_nat i))%Z by ring.
      rewrite Z_abs_nat_opp. reflexivity. }
    rewrite Heq.
    apply (decay_bound_finite_one_factor_tight seq I C HC Hseq_ge2_fin Hgrowth_fin Hsorted j i Hji Hj_len Hi_len).
Qed.

End PSA_Pipeline.
Module GreedyGate.

Import RuntimeGuards.
Import SeqProps.

(* 贪心过滤内核：首个由调用方决定，之后 v 满足 M*last <= v 才保留。 *)
Fixpoint greedy_aux (M last : nat) (vals : list nat) : list nat :=
  match vals with
  | nil => nil
  | v :: vs => if ((M * last <=? v)%nat) then v :: greedy_aux M v vs
               else greedy_aux M last vs
  end.

(* 贪心门控：首个总是保留（与原文 §3.2 fallback_mask 一致），之后 val >= M*last_kept 才保留。
   参数 M 是乘数：
     - M = C   ：与 Python fallback_mask(indices, C) 逐字一致（线性门，其守卫 is_c_sparse 亦线性）；
     - M = C*C ：保证选中子集满足库内 c_sparse_subset（平方增长），即路线图 P0 结论。 *)
Definition greedy_selected (M : nat) (vals : list nat) : list nat :=
  match vals with
  | nil => nil
  | v :: vs => v :: greedy_aux M v vs
  end.

(* ---------- 子集性质（零公理） ---------- *)

Lemma greedy_aux_In (M : nat) (vals : list nat) (last v : nat) :
  In v (greedy_aux M last vals) -> In v vals.
Proof.
  revert last v.
  induction vals as [| h t IH]; intros last v H.
  - simpl in H. exact H.
  - simpl in H.
    destruct ((M * last <=? h)%nat) eqn:Hg.
    + simpl in H. destruct H as [Heq | Ht].
      * left. exact Heq.
      * right. apply (IH h). exact Ht.
    + right. apply (IH last). exact H.
Qed.

Lemma greedy_selected_In (M : nat) (vals : list nat) (v : nat) :
  In v (greedy_selected M vals) -> In v vals.
Proof.
  destruct vals as [| h t]; intros H.
  - simpl in H. exact H.
  - simpl in H. destruct H as [Heq | Ht].
    + left. exact Heq.
    + right. apply (greedy_aux_In M t h v). exact Ht.
Qed.

Lemma greedy_aux_all_ge_2 (M : nat) (vals : list nat) (last : nat) :
  all_ge_2 vals = true -> all_ge_2 (greedy_aux M last vals) = true.
Proof.
  intros H.
  unfold all_ge_2 in *.
  rewrite forallb_forall.
  intros v Hv.
  rewrite forallb_forall in H.
  apply H. apply (greedy_aux_In M vals last v). exact Hv.
Qed.

Lemma greedy_selected_all_ge_2 (M : nat) (vals : list nat) :
  all_ge_2 vals = true -> all_ge_2 (greedy_selected M vals) = true.
Proof.
  intros H.
  unfold all_ge_2 in *.
  rewrite forallb_forall.
  intros v Hv.
  rewrite forallb_forall in H.
  apply H. apply (greedy_selected_In M vals v). exact Hv.
Qed.

Lemma greedy_aux_NoDup (M : nat) (vals : list nat) (last : nat) :
  NoDup vals -> NoDup (greedy_aux M last vals).
Proof.
  revert last.
  induction vals as [| h t IH]; intros last H.
  - constructor.
  - inversion H; subst.
    simpl. destruct ((M * last <=? h)%nat) eqn:Hg.
    + constructor.
      * intros Hin.
        apply H2.
        apply (greedy_aux_In M t h h). exact Hin.
      * apply (IH h). exact H3.
    + apply (IH last). exact H3.
Qed.

Lemma greedy_selected_NoDup (M : nat) (vals : list nat) :
  NoDup vals -> NoDup (greedy_selected M vals).
Proof.
  destruct vals as [| h t]; intros H.
  - constructor.
  - inversion H; subst.
    simpl. constructor.
    + intros Hin.
      apply H2.
      apply (greedy_aux_In M t h h). exact Hin.
    + apply (greedy_aux_NoDup M t h). exact H3.
Qed.

(* ---------- Sorted 保持 ---------- *)

(* Sorted (v :: vs) ⟹ vs 中所有元素 > v（链式；归纳前 revert v 使 IH 对任意头成立） *)
Lemma sorted_lt_all : forall (v : nat) (vs : list nat),
  Sorted Nat.lt (v :: vs) -> forall y, In y vs -> (v < y)%nat.
Proof.
  intros v vs.
  revert v.
  induction vs as [| w ws IH]; intros v H y Hy.
  - simpl in Hy. contradiction.
  - destruct (Sorted_inv H) as [HSorted_ws Hhd].
    simpl in Hy. destruct Hy as [Heq | Hws].
    + subst. apply (HdRel_inv Hhd).
    + apply (Nat.lt_trans _ w _).
      * apply (HdRel_inv Hhd).
      * apply (IH w HSorted_ws y). exact Hws.
Qed.

(* Sorted Nat.lt ⟹ NoDup（严格增列表无重复） *)
Lemma greedy_Sorted_NoDup (l : list nat) :
  Sorted Nat.lt l -> NoDup l.
Proof.
  induction l as [| h t IH]; intros H.
  - constructor.
  - destruct (Sorted_inv H) as [HSorted_t Hhd].
    constructor.
    + intros Hin. apply (Nat.lt_irrefl h).
      apply (sorted_lt_all h t H h). exact Hin.
    + apply IH. exact HSorted_t.
Qed.

Lemma greedy_aux_Sorted (M : nat) (vals : list nat) (last : nat) :
  Sorted Nat.lt vals -> Sorted Nat.lt (greedy_aux M last vals).
Proof.
  revert last.
  induction vals as [| h t IH]; intros last H.
  - constructor.
  - destruct (Sorted_inv H) as [HSorted_t Hhd].
    simpl. destruct ((M * last <=? h)%nat) eqn:Hg.
    + apply Sorted_cons.
      * apply (IH h). exact HSorted_t.
      * destruct (greedy_aux M h t) as [| y ys] eqn:Htail.
        -- constructor.
        -- apply HdRel_cons.
           apply (sorted_lt_all h t H y).
           apply (greedy_aux_In M t h y).
           rewrite Htail. simpl. left. reflexivity.
    + apply (IH last). exact HSorted_t.
Qed.

Lemma greedy_selected_Sorted (M : nat) (vals : list nat) :
  Sorted Nat.lt vals -> Sorted Nat.lt (greedy_selected M vals).
Proof.
  destruct vals as [| h t]; intros H.
  - constructor.
  - destruct (Sorted_inv H) as [HSorted_t Hhd].
    simpl. apply Sorted_cons.
    + apply (greedy_aux_Sorted M t h). exact HSorted_t.
    + destruct (greedy_aux M h t) as [| y ys] eqn:Htail.
      * constructor.
      * apply HdRel_cons.
        apply (sorted_lt_all h t H y).
        apply (greedy_aux_In M t h y).
        rewrite Htail. simpl. left. reflexivity.
Qed.

(* ---------- 门控增长不变量（零公理） ---------- *)

(* greedy_aux 输出非空时，首元素 >= M*last（门限的"第一枪"保证） *)
Lemma greedy_aux_head_growth (M last : nat) (vals : list nat) :
  (0 < length (greedy_aux M last vals))%nat ->
  (M * last <= nth 0 (greedy_aux M last vals) 0%nat)%nat.
Proof.
  induction vals as [| h t IH]; intros Hlen.
  - simpl in Hlen. lia.
  - simpl. destruct ((M * last <=? h)%nat) eqn:Hg.
    + simpl. apply (proj1 (Nat.leb_le (M * last) h)). exact Hg.
    + simpl in Hlen. rewrite Hg in Hlen. apply IH. exact Hlen.
Qed.

(* greedy_aux 输出相邻对被保留者满足 M*前 <= 后（递归的 last 状态推进） *)
Lemma greedy_aux_adjacent_growth (M : nat) (vals : list nat) (last k : nat) :
  (S k < length (greedy_aux M last vals))%nat ->
  (M * nth k (greedy_aux M last vals) 0%nat <= nth (S k) (greedy_aux M last vals) 0%nat)%nat.
Proof.
  revert last k.
  induction vals as [| h t IH]; intros last k Hlen.
  - simpl in Hlen. lia.
  - simpl. destruct ((M * last <=? h)%nat) eqn:Hg.
    + simpl in Hlen. rewrite Hg in Hlen. simpl in Hlen.
      destruct k as [| k'].
      * assert (Htl : (0 < length (greedy_aux M h t))%nat) by lia.
        apply (greedy_aux_head_growth M h t Htl).
      * apply (IH h k'). lia.
    + simpl in Hlen. rewrite Hg in Hlen. simpl in Hlen.
      apply (IH last k). lia.
Qed.

(* greedy_selected 相邻对被保留者满足 M*前 <= 后（原文 is_c_sparse 的线性断言；任意 M） *)
Lemma greedy_selected_adjacent_growth (M : nat) (vals : list nat) (k : nat) :
  (S k < length (greedy_selected M vals))%nat ->
  (M * nth k (greedy_selected M vals) 0%nat <= nth (S k) (greedy_selected M vals) 0%nat)%nat.
Proof.
  destruct vals as [| h t]; intros Hlen.
  - simpl in Hlen. lia.
  - simpl in Hlen. simpl. destruct k as [| k'].
    + assert (Htl : (0 < length (greedy_aux M h t))%nat) by lia.
      apply (greedy_aux_head_growth M h t Htl).
    + apply (greedy_aux_adjacent_growth M t h k'). lia.
Qed.

(* 平方门（M = C*C）+ C>=2 + 全值>=2 ⟹ 严格线性增长（喂 check_sparse_growth / psa_guard_decay） *)
Lemma greedy_selected_strict_growth (C : nat) (vals : list nat) (k : nat) :
  (C >= 2)%nat -> all_ge_2 vals = true ->
  (S k < length (greedy_selected (C * C) vals))%nat ->
  (C * nth k (greedy_selected (C * C) vals) 0%nat < nth (S k) (greedy_selected (C * C) vals) 0%nat)%nat.
Proof.
  intros HC Hge2 Hlen.
  assert (Hsel_ge2 : all_ge_2 (greedy_selected (C * C) vals) = true).
  { apply (greedy_selected_all_ge_2 (C * C) vals). exact Hge2. }
  assert (Ha_ge2 : (nth k (greedy_selected (C * C) vals) 0%nat >= 2)%nat).
  { destruct (all_ge_2P (greedy_selected (C * C) vals)) as [Hok | Hbad]; [| discriminate].
    apply Hok. apply nth_In. lia. }
  assert (Hab : (C * C * nth k (greedy_selected (C * C) vals) 0%nat <=
                 nth (S k) (greedy_selected (C * C) vals) 0%nat)%nat).
  { apply (greedy_selected_adjacent_growth (C * C) vals k). exact Hlen. }
  assert (HCa_lt : (C * nth k (greedy_selected (C * C) vals) 0%nat <
                    C * C * nth k (greedy_selected (C * C) vals) 0%nat)%nat).
  { nia. }
  apply (Nat.lt_le_trans _ (C * C * nth k (greedy_selected (C * C) vals) 0%nat) _);
    [exact HCa_lt | exact Hab].
Qed.

(* 平方门 ⟹ 选中子集通过库内稀疏检查（路线图 P0 结论；零前提） *)
Lemma greedy_selected_c_sparse_check (C : nat) (vals : list nat) :
  all_ge_2 vals = true ->
  check_c_sparse_on_vals (greedy_selected (C * C) vals) C = true.
Proof.
  intros Hge2.
  unfold check_c_sparse_on_vals.
  apply andb_true_intro. split.
  - apply forallb_adjacent_from_nth.
    intros k Hk.
    apply (proj2 (Nat.leb_le (C * C * nth k (greedy_selected (C * C) vals) 0%nat)
                             (nth (S k) (greedy_selected (C * C) vals) 0%nat))).
    apply (greedy_selected_adjacent_growth (C * C) vals k). lia.
  - apply (greedy_selected_all_ge_2 (C * C) vals). exact Hge2.
Qed.

(* ---------- 主定理与库内连接 ---------- *)

(* 路线图 P0 主定理：平方门控 ⟹ Sorted / NoDup / all_ge_2 / check_c_sparse_on_vals 全部保持 *)
Theorem greedy_selected_correct (C : nat) (vals : list nat) :
  (C >= 2)%nat -> Sorted Nat.lt vals -> all_ge_2 vals = true ->
  let sel := greedy_selected (C * C) vals in
  Sorted Nat.lt sel /\ NoDup sel /\ all_ge_2 sel = true /\
  check_c_sparse_on_vals sel C = true.
Proof.
  intros HC HSorted Hge2.
  cbv zeta.
  split; [| split; [| split]].
  - apply (greedy_selected_Sorted (C * C) vals). exact HSorted.
  - apply (greedy_Sorted_NoDup (greedy_selected (C * C) vals)).
    apply (greedy_selected_Sorted (C * C) vals). exact HSorted.
  - apply (greedy_selected_all_ge_2 (C * C) vals). exact Hge2.
  - apply (greedy_selected_c_sparse_check C vals). exact Hge2.
Qed.

(* 推论：反射 ⟹ 选中子集满足库内 c_sparse_subset（ca_basis_lemmas.v:6658）+ 全元素 >= 2 *)
Theorem greedy_selected_c_sparse_subset (C : nat) (vals : list nat) :
  (C >= 2)%nat -> Sorted Nat.lt vals -> all_ge_2 vals = true ->
  c_sparse_subset (fun i => nth i (greedy_selected (C * C) vals) 0%nat) C
                  (seq 0%nat (length (greedy_selected (C * C) vals)))
  /\ forall v, In v (greedy_selected (C * C) vals) -> (v >= 2)%nat.
Proof.
  intros HC HSorted Hge2.
  pose proof (greedy_selected_correct C vals HC HSorted Hge2) as Hcorr.
  cbv zeta in Hcorr.
  destruct Hcorr as [HSel [HNoDup [Hge2sel Hck]]].
  pose proof (check_c_sparse_on_valsP (greedy_selected (C * C) vals) C HSel) as Hr.
  (* Hr : reflect P (check ...) 且 Hck : check ... = true ⟹ P（用 iff_reflect 避免 destruct 丢细化） *)
  exact (proj2 (reflect_iff _ _ Hr) Hck).
Qed.

(* ---------- 掩码形式（原文 §3.2 fallback_mask：与索引等长的布尔掩码） ---------- *)

Fixpoint mask_aux (M last : nat) (vals : list nat) : list bool :=
  match vals with
  | nil => nil
  | v :: vs => if ((M * last <=? v)%nat) then true :: mask_aux M v vs
               else false :: mask_aux M last vs
  end.

Definition fallback_mask (M : nat) (vals : list nat) : list bool :=
  match vals with
  | nil => nil
  | v :: vs => true :: mask_aux M v vs
  end.

(* 掩码提取：按 true 位置取出保留值（对应 np.where(g) 取索引） *)
Fixpoint selected_by_mask (vals : list nat) (g : list bool) : list nat :=
  match vals, g with
  | v :: vs, true :: gs => v :: selected_by_mask vs gs
  | _ :: vs, false :: gs => selected_by_mask vs gs
  | _, _ => nil
  end.

Lemma mask_aux_length (M last : nat) (vals : list nat) :
  length (mask_aux M last vals) = length vals.
Proof.
  revert last.
  induction vals as [| h t IH]; intros last.
  - reflexivity.
  - simpl. destruct ((M * last <=? h)%nat) eqn:Hg.
    + simpl. rewrite (IH h). reflexivity.
    + simpl. rewrite (IH last). reflexivity.
Qed.

Lemma fallback_mask_length (M : nat) (vals : list nat) :
  length (fallback_mask M vals) = length vals.
Proof.
  destruct vals as [| h t]; [reflexivity | simpl; rewrite mask_aux_length; reflexivity].
Qed.

Lemma mask_aux_correct (M last : nat) (vals : list nat) :
  selected_by_mask vals (mask_aux M last vals) = greedy_aux M last vals.
Proof.
  revert last.
  induction vals as [| h t IH]; intros last.
  - reflexivity.
  - simpl. destruct ((M * last <=? h)%nat) eqn:Hg.
    + simpl. rewrite (IH h). reflexivity.
    + simpl. rewrite (IH last). reflexivity.
Qed.

(* 掩码正确性：mask 提取 = 贪心选中（fallback_mask ⟷ greedy_selected 的桥梁） *)
Theorem fallback_mask_correct (M : nat) (vals : list nat) :
  selected_by_mask vals (fallback_mask M vals) = greedy_selected M vals.
Proof.
  destruct vals as [| h t]; [reflexivity | simpl; rewrite mask_aux_correct; reflexivity].
Qed.

(* 原文 §3.2 断言 is_c_sparse（线性 b >= C*a）：掩码选出的相邻值满足。零前提。 *)
Theorem fallback_mask_linear_sparse (M : nat) (vals : list nat) (k : nat) :
  (S k < length (selected_by_mask vals (fallback_mask M vals)))%nat ->
  (M * nth k (selected_by_mask vals (fallback_mask M vals)) 0%nat <=
   nth (S k) (selected_by_mask vals (fallback_mask M vals)) 0%nat)%nat.
Proof.
  intros Hlen.
  rewrite fallback_mask_correct in *.
  apply (greedy_selected_adjacent_growth M vals k). exact Hlen.
Qed.

(* ---------- P0 + P2 汇合：门控子集通过运行时守卫 ---------- *)

(* 平方门控 ⟹ 选中子集满足 psa_guard_decay 的全部有限前提
   （Sorted / NoDup / all_ge_2 / check_sparse_growth），vals = map seq I 时可直接实例化。 *)
Theorem greedy_selected_guard_pass (C : nat) (vals : list nat) :
  (C >= 2)%nat -> Sorted Nat.lt vals -> all_ge_2 vals = true ->
  Sorted Nat.lt (greedy_selected (C * C) vals) /\
  NoDup (greedy_selected (C * C) vals) /\
  all_ge_2 (greedy_selected (C * C) vals) = true /\
  check_sparse_growth (greedy_selected (C * C) vals) C = true.
Proof.
  intros HC HSorted Hge2.
  split; [| split; [| split]].
  - apply (greedy_selected_Sorted (C * C) vals). exact HSorted.
  - apply (greedy_Sorted_NoDup (greedy_selected (C * C) vals)).
    apply (greedy_selected_Sorted (C * C) vals). exact HSorted.
  - apply (greedy_selected_all_ge_2 (C * C) vals). exact Hge2.
  - unfold check_sparse_growth.
    apply forallb_adjacent_from_nth.
    intros k Hk.
    apply Nat.ltb_lt.
    apply (greedy_selected_strict_growth C vals k HC Hge2). lia.
Qed.


(* ============================================================
   P0→P2 实例化桥：索引层面门控 greedy_indices + psa_gated_decay
   ============================================================ *)


(* 索引层面门控：对索引列表 I 逐元素判定，保留索引 i 当且仅当 M*last <= seq i
   （last 是上一个保留索引的 seq 值）。与值层 greedy_aux 通过 map seq 一一对应。 *)
Fixpoint greedy_idx_aux (seq : nat -> nat) (M last : nat) (I : list nat) : list nat :=
  match I with
  | nil => nil
  | i :: is => if ((M * last <=? seq i)%nat) then i :: greedy_idx_aux seq M (seq i) is
               else greedy_idx_aux seq M last is
  end.

Definition greedy_indices (seq : nat -> nat) (M : nat) (I : list nat) : list nat :=
  match I with
  | nil => nil
  | i :: is => i :: greedy_idx_aux seq M (seq i) is
  end.

(* 索引门控输出是输入的子序列 *)
Lemma greedy_idx_aux_In (seq : nat -> nat) (M : nat) (I : list nat) (last j : nat) :
  In j (greedy_idx_aux seq M last I) -> In j I.
Proof.
  revert last j.
  induction I as [| i is IH]; intros last j H.
  - simpl in H. contradiction.
  - simpl in H.
    destruct ((M * last <=? seq i)%nat) eqn:Hg.
    + simpl in H. destruct H as [Heq | Ht].
      * left. exact Heq.
      * right. apply (IH (seq i) j). exact Ht.
    + right. apply (IH last j). exact H.
Qed.

(* 索引门控保持 Sorted（子序列，链论证同 greedy_aux_Sorted） *)
Lemma greedy_idx_aux_Sorted (seq : nat -> nat) (M : nat) (I : list nat) (last : nat) :
  Sorted Nat.lt I -> Sorted Nat.lt (greedy_idx_aux seq M last I).
Proof.
  revert last.
  induction I as [| i is IH]; intros last H.
  - constructor.
  - destruct (Sorted_inv H) as [HSorted_is Hhd].
    simpl. destruct ((M * last <=? seq i)%nat) eqn:Hg.
    + apply Sorted_cons.
      * apply (IH (seq i)). exact HSorted_is.
      * destruct (greedy_idx_aux seq M (seq i) is) as [| j js] eqn:Htail.
        -- constructor.
        -- apply HdRel_cons.
           apply (sorted_lt_all i is H j).
           apply (greedy_idx_aux_In seq M is (seq i) j).
           rewrite Htail. simpl. left. reflexivity.
    + apply (IH last). exact HSorted_is.
Qed.

Lemma greedy_indices_Sorted (seq : nat -> nat) (M : nat) (I : list nat) :
  Sorted Nat.lt I -> Sorted Nat.lt (greedy_indices seq M I).
Proof.
  destruct I as [| i is]; intros H.
  - constructor.
  - destruct (Sorted_inv H) as [HSorted_is Hhd].
    simpl. apply Sorted_cons.
    + apply (greedy_idx_aux_Sorted seq M is (seq i)). exact HSorted_is.
    + destruct (greedy_idx_aux seq M (seq i) is) as [| j js] eqn:Htail.
      * constructor.
      * apply HdRel_cons.
        apply (sorted_lt_all i is H j).
        apply (greedy_idx_aux_In seq M is (seq i) j).
        rewrite Htail. simpl. left. reflexivity.
Qed.

(* map 保持：索引门控 ⟷ 值门控（桥的核心） *)
Lemma greedy_idx_aux_map (seq : nat -> nat) (M : nat) (I : list nat) (last : nat) :
  map seq (greedy_idx_aux seq M last I) = greedy_aux M last (map seq I).
Proof.
  revert last.
  induction I as [| i is IH]; intros last.
  - reflexivity.
  - simpl. destruct ((M * last <=? seq i)%nat) eqn:Hg.
    + simpl. rewrite (IH (seq i)). reflexivity.
    + simpl. rewrite (IH last). reflexivity.
Qed.

Lemma greedy_indices_map (seq : nat -> nat) (M : nat) (I : list nat) :
  map seq (greedy_indices seq M I) = greedy_selected M (map seq I).
Proof.
  destruct I as [| i is]; [reflexivity | simpl; rewrite greedy_idx_aux_map; reflexivity].
Qed.

(* P0→P2 实例化桥：门控后的索引子集满足 psa_guard_decay 的全部前提，
   即「守卫通过 ⟹ 门控子集上的衰减界」（论文叙事：运行时门控 + 守卫 ⟹ 数学保证）。
   注：不需要 check_sparse_growth (map seq I)（门控自身保证相邻增长），
   也不需要 seq 的全局增长或 map seq I 的 Sorted（严格线性增长由平方门 + C>=2 + all_ge_2 给出）。 *)
Theorem psa_gated_decay (seq : nat -> nat) (I : list nat) (C : nat) :
  (C >= 2)%nat -> NoDup I -> Sorted Nat.lt I ->
  all_ge_2 (map seq I) = true ->
  let I' := greedy_indices seq (C * C) I in
  forall i j, i <> j -> (i < length I')%nat -> (j < length I')%nat ->
    Cnorm (Csum (fun k => psi (nth i (map seq I') 0%nat) k *c Cconj (psi (nth j (map seq I') 0%nat) k))
                (seq (fold_right Nat.max 0%nat I') - 1))
    <= 2 / ((sqrt (INR C)) ^ (Z.abs_nat (Z.of_nat i - Z.of_nat j))).
Proof.
  intros HC Hnodup Hsorted Hge2.
  cbv zeta.
  apply (PSA_Pipeline.psa_guard_decay seq (greedy_indices seq (C * C) I) C).
  - exact HC.
  - apply (greedy_Sorted_NoDup (greedy_indices seq (C * C) I)).
    apply (greedy_indices_Sorted seq (C * C) I). exact Hsorted.
  - apply (greedy_indices_Sorted seq (C * C) I). exact Hsorted.
  - rewrite greedy_indices_map.
    apply (greedy_selected_all_ge_2 (C * C) (map seq I)). exact Hge2.
  - rewrite greedy_indices_map.
    unfold check_sparse_growth.
    apply forallb_adjacent_from_nth.
    intros k Hk.
    apply Nat.ltb_lt.
    apply (greedy_selected_strict_growth C (map seq I) k HC Hge2). lia.
Qed.

(* 桥的自然实例：seq 取生成器全局序列 base_seq C start 时，门控作用于生成器输出 *)
Theorem psa_gated_decay_base_seq (len C start : nat) (I : list nat) :
  (C >= 2)%nat -> (start >= 2)%nat -> NoDup I -> Sorted Nat.lt I ->
  all_ge_2 (map (base_seq C start) I) = true ->
  let I' := greedy_indices (base_seq C start) (C * C) I in
  forall i j, i <> j -> (i < length I')%nat -> (j < length I')%nat ->
    Cnorm (Csum (fun k => psi (nth i (map (base_seq C start) I') 0%nat) k *c
                          Cconj (psi (nth j (map (base_seq C start) I') 0%nat) k))
                (base_seq C start (fold_right Nat.max 0%nat I') - 1))
    <= 2 / ((sqrt (INR C)) ^ (Z.abs_nat (Z.of_nat i - Z.of_nat j))).
Proof.
  intros HC Hstart Hnodup Hsorted Hge2.
  cbv zeta.
  apply (psa_gated_decay (base_seq C start) I C HC Hnodup Hsorted Hge2).
Qed.


End GreedyGate.

Module RowTruncation.

Import UnconditionalBasisLemmas.

(* 列表 R 能量求和（与 ca_probabilistic 的 fold_right_Rplus_app 配套） *)
Definition list_sum_R (f : nat -> R) (l : list nat) : R :=
  fold_right (fun i acc => f i + acc) 0%R l.

(* filter 分割求和：全和 = 保留和 + 丢弃和（P 与 negb P 互补，任意 P、任意分数） *)
Lemma sum_filter_compl (score : nat -> R) (l : list nat) (P : nat -> bool) :
  list_sum_R score l =
  list_sum_R score (filter P l) + list_sum_R score (filter (fun x => negb (P x)) l).
Proof.
  induction l as [| x xs IH].
  - simpl. ring.
  - simpl. destruct (P x) eqn:Hpx.
    + simpl. rewrite IH. ring.
    + simpl. rewrite IH. ring.
Qed.

(* 抽象截断界（路线图 P1b）：保留 ≥ 总 − budget ⟹ 丢弃 ≤ budget。
   无排序（构造性）：保留/丢弃由布尔判定 P 给出，分数可正可负。 *)
Lemma complement_sum_bound (n : nat) (score : nat -> R) (P : nat -> bool) (budget : R) :
  list_sum_R score (filter P (seq 0%nat n)) >=
  list_sum_R score (seq 0%nat n) - budget ->
  list_sum_R score (filter (fun x => negb (P x)) (seq 0%nat n)) <= budget.
Proof.
  intros Hkeep.
  pose proof (sum_filter_compl score (seq 0%nat n) P) as Hsplit.
  lra.
Qed.

(* 行 i 的非对角能量函数：j ↦ 0（j = i）或 |<psi_i, psi_j>| 截断内积 *)
Definition row_score (vals : list nat) (M i : nat) : nat -> R :=
  fun j => if eq_nat_dec i j then 0%R else
    Cnorm (Csum (fun k => psi (nth i vals 0%nat) k *c Cconj (psi (nth j vals 0%nat) k)) (M - 1)).

(* 行能量界：行 i 非对角总能量 ≤ 2*K(C)（row_sum_bound_K 的直接实例，C > 2） *)
Theorem row_energy_bound (n : nat) (vals : list nat) (M C : nat) (i : nat) :
  (C > 2)%nat -> length vals = n ->
  (forall v, In v vals -> (v >= 2)%nat) ->
  (forall i j, i <> j -> (i < n)%nat -> (j < n)%nat ->
     Cnorm (Csum (fun k => psi (nth i vals 0%nat) k *c Cconj (psi (nth j vals 0%nat) k)) (M - 1))
     <= / ((sqrt (INR C)) ^ (Z.abs_nat (Z.of_nat i - Z.of_nat j)))) ->
  (i < n)%nat ->
  sum_f_R0 (row_score vals M i) (n - 1) <= 2 * K (INR C).
Proof.
  intros HC Hlen Hge2 Hdecay Hi.
  unfold row_score.
  exact (ExtendedTheorems.row_sum_bound_K n vals M C Hge2 Hlen Hdecay HC i Hi).
Qed.

(* 行截断误差（complement_sum_bound 的行实例）：保留 ≥ 总 − budget ⟹ 丢弃 ≤ budget *)
Theorem row_truncation_error (n : nat) (vals : list nat) (M i : nat)
  (P : nat -> bool) (budget : R) :
  list_sum_R (row_score vals M i) (filter P (seq 0%nat n)) >=
  list_sum_R (row_score vals M i) (seq 0%nat n) - budget ->
  list_sum_R (row_score vals M i) (filter (fun x => negb (P x)) (seq 0%nat n)) <= budget.
Proof.
  intros H. apply (complement_sum_bound n (row_score vals M i) P budget). exact H.
Qed.

(* 论文 §4.2 主定理：掩码构造保证保留 ≥ 总 − min(S·ε_rel, R_max·ε_abs)
   ⟹ 丢弃能量 ≤ R_max·ε_abs（R_max = 2*K(C)；无需 ε 非负，Rmin_le_r 恒成立） *)
Theorem row_dropped_energy_bound (n : nat) (vals : list nat) (M C i : nat)
  (P : nat -> bool) (eps_rel eps_abs : R) :
  (C > 2)%nat -> length vals = n ->
  (forall v, In v vals -> (v >= 2)%nat) ->
  (forall i j, i <> j -> (i < n)%nat -> (j < n)%nat ->
     Cnorm (Csum (fun k => psi (nth i vals 0%nat) k *c Cconj (psi (nth j vals 0%nat) k)) (M - 1))
     <= / ((sqrt (INR C)) ^ (Z.abs_nat (Z.of_nat i - Z.of_nat j)))) ->
  (i < n)%nat ->
  list_sum_R (row_score vals M i) (filter P (seq 0%nat n)) >=
  list_sum_R (row_score vals M i) (seq 0%nat n) -
    Rmin (list_sum_R (row_score vals M i) (seq 0%nat n) * eps_rel) (2 * K (INR C) * eps_abs) ->
  list_sum_R (row_score vals M i) (filter (fun x => negb (P x)) (seq 0%nat n)) <= 2 * K (INR C) * eps_abs.
Proof.
  intros HC Hlen Hge2 Hdecay Hi Hkeep.
  apply (Rle_trans _ (Rmin (list_sum_R (row_score vals M i) (seq 0%nat n) * eps_rel)
                           (2 * K (INR C) * eps_abs)) _).
  - apply (row_truncation_error n vals M i P
             (Rmin (list_sum_R (row_score vals M i) (seq 0%nat n) * eps_rel) (2 * K (INR C) * eps_abs))).
    exact Hkeep.
  - apply Rmin_r.
Qed.

End RowTruncation.
Module PipelineEndToEnd.

Import GreedyGate.
Import SeqProps.
Import RowTruncation.
Import RuntimeGuards.
Import PSA_Pipeline.
Import ExtendedTheorems.
Import UnconditionalBasisLemmas.
Open Scope R_scope.

(* P3a：低相干——门控子集相邻基内积范数 ≤ 2/√C（decay dist=1 命名特例） *)
Theorem psa_low_coherence (len C start : nat) (I : list nat) (i : nat) :
  (C >= 2)%nat -> (start >= 2)%nat -> NoDup I -> Sorted Nat.lt I ->
  all_ge_2 (map (base_seq C start) I) = true ->
  (S i < length (greedy_indices (base_seq C start) (C * C) I))%nat ->
  Cnorm (Csum (fun k => psi (nth i (map (base_seq C start) (greedy_indices (base_seq C start) (C * C) I)) 0%nat) k *c
                         Cconj (psi (nth (S i) (map (base_seq C start) (greedy_indices (base_seq C start) (C * C) I)) 0%nat) k))
               (base_seq C start (fold_right Nat.max 0%nat (greedy_indices (base_seq C start) (C * C) I)) - 1))
  <= 2 / sqrt (INR C).
Proof.
  intros HC Hstart Hdup Hsorted Hge2 Hi.
  pose proof (psa_gated_decay_base_seq len C start I HC Hstart Hdup Hsorted Hge2) as Hdec.
  cbv zeta in Hdec.
  specialize (Hdec i (S i) (Nat.neq_succ_diag_r i)
                    (Nat.lt_trans _ _ _ (Nat.lt_succ_diag_r i) Hi) Hi).
  assert (Hpow : (sqrt (INR C)) ^ Z.abs_nat ((Z.of_nat i - Z.of_nat (S i))%Z) = sqrt (INR C)).
  { assert (Hidx : Z.abs_nat ((Z.of_nat i - Z.of_nat (S i))%Z) = 1%nat).
    { assert (Hz : (Z.of_nat i - Z.of_nat (S i))%Z = (-1)%Z).
      { rewrite Nat2Z.inj_succ. ring. }
      rewrite Hz. reflexivity. }
    rewrite Hidx. apply pow_1. }
  rewrite Hpow in Hdec.
  exact Hdec.
Qed.

(* 端到端管线定理：生成器 base_seq → 门控 greedy_indices ⟹ 守卫通过 + 衰减界 + 低相干。
   前提仅：C>=2、start>=2、I 的 NoDup/Sorted、守卫 all_ge_2 (map base_seq I)。 *)
Theorem psa_pipeline_guard (len C start : nat) (I : list nat) :
  (C >= 2)%nat -> (start >= 2)%nat -> NoDup I -> Sorted Nat.lt I ->
  all_ge_2 (map (base_seq C start) I) = true ->
  let I' := greedy_indices (base_seq C start) (C * C) I in
  let vals' := map (base_seq C start) I' in
  (check_sparse_growth vals' C = true
   /\ (forall i j, i <> j -> (i < length I')%nat -> (j < length I')%nat ->
        Cnorm (Csum (fun k => psi (nth i vals' 0%nat) k *c Cconj (psi (nth j vals' 0%nat) k))
                    (base_seq C start (fold_right Nat.max 0%nat I') - 1))
        <= 2 / ((sqrt (INR C)) ^ (Z.abs_nat (Z.of_nat i - Z.of_nat j))))
   /\ (forall i, (S i < length I')%nat ->
        Cnorm (Csum (fun k => psi (nth i vals' 0%nat) k *c Cconj (psi (nth (S i) vals' 0%nat) k))
                    (base_seq C start (fold_right Nat.max 0%nat I') - 1))
        <= 2 / sqrt (INR C))).
Proof.
  intros HC Hstart Hdup Hsorted Hge2.
  cbv zeta.
  split; [| split].
  - (* ① 守卫通过 *)
    unfold check_sparse_growth.
    rewrite greedy_indices_map.
    apply forallb_adjacent_from_nth.
    intros k Hk.
    apply Nat.ltb_lt.
    apply (greedy_selected_strict_growth C (map (base_seq C start) I) k HC Hge2). lia.
  - (* ② 衰减界：psa_gated_decay_base_seq *)
    exact (psa_gated_decay_base_seq len C start I HC Hstart Hdup Hsorted Hge2).
  - (* ③ 低相干：psa_low_coherence *)
    intros i Hi.
    exact (psa_low_coherence len C start I i HC Hstart Hdup Hsorted Hge2 Hi).
Qed.

(* 2/ 版行能量：衰减界为 2 系数时，行 i 非对角总能量 ≤ 4*K(C)（= 2*R_max，R_max = 2/(√C-1)）。
   复用 split_sum_geometric_bound_one / row_sum_bound_when_i_last_one 的几何和骨架。 *)
Theorem row_energy_bound_wide (n : nat) (vals : list nat) (M C : nat) (i : nat) :
  (C > 2)%nat -> length vals = n ->
  (forall v, In v vals -> (v >= 2)%nat) ->
  (forall i j, i <> j -> (i < n)%nat -> (j < n)%nat ->
     Cnorm (Csum (fun k => psi (nth i vals 0%nat) k *c Cconj (psi (nth j vals 0%nat) k)) (M - 1))
     <= 2 * / ((sqrt (INR C)) ^ (Z.abs_nat (Z.of_nat i - Z.of_nat j)))) ->
  (i < n)%nat ->
  sum_f_R0 (row_score vals M i) (n - 1) <= 4 * K (INR C).
Proof.
  intros HC Hlen Hge2 Hdecay2 Hi.
  unfold row_score.
  set (r := sqrt (INR C)).
  assert (Hr_gt1 : r > 1). {
    unfold r; rewrite <- sqrt_1.
    apply sqrt_lt_1.
    - lra.
    - apply Rlt_le; apply lt_0_INR; lia.
    - change (1%R) with (INR 1); apply lt_INR; lia.
  }
  assert (Hr_gt1' : r - 1 > 0) by lra.
  set (F j := if eq_nat_dec i j then 0%R
             else Cnorm (Csum (fun k => psi (nth i vals 0%nat) k *c Cconj (psi (nth j vals 0%nat) k)) (M - 1))).
  set (G j := if eq_nat_dec i j then 0%R
             else / (r ^ Z.abs_nat (Z.of_nat i - Z.of_nat j))).
  assert (H_F_bound : forall j, (j < n)%nat -> F j <= 2 * / (r ^ Z.abs_nat (Z.of_nat i - Z.of_nat j))).
  { intros j Hj; unfold F.
    destruct (eq_nat_dec i j) as [Heq | Hneq].
    - subst j; simpl.
      destruct (eq_nat_dec i i); [| contradiction].
      rewrite Z.sub_diag. simpl. nra.
    - apply Hdecay2; assumption. }
  assert (H_G_bound : forall j, (j < n)%nat -> j <> i -> G j <= / (r ^ Z.abs_nat (Z.of_nat i - Z.of_nat j))).
  { intros j Hj Hneq. unfold G. destruct (eq_nat_dec i j) as [Heq' | Hneq'].
    - exfalso. apply Hneq. symmetry. exact Heq'.
    - reflexivity. }
  assert (H_F_le_2G : forall j, (j < n)%nat -> F j <= 2 * G j).
  { intros j Hj. unfold G. destruct (eq_nat_dec i j) as [Heq' | Hneq'].
    - subst j. unfold F. simpl. destruct (eq_nat_dec i i); [nra | contradiction].
    - change (F j <= 2 * / (r ^ Z.abs_nat (Z.of_nat i - Z.of_nat j))).
      exact (H_F_bound j Hj). }
  assert (Hsum_le : sum_f_R0 F (n - 1) <= sum_f_R0 (fun j => 2 * G j) (n - 1)).
  { apply sum_f_R0_le_compat; intros j Hj; apply H_F_le_2G; lia. }
  assert (Hsum_scal : sum_f_R0 (fun j => 2 * G j) (n - 1) = 2 * sum_f_R0 G (n - 1)).
  { apply (sum_f_R0_scal_l 2 G (n - 1)). }
  assert (HsumG : sum_f_R0 G (n - 1) <= 2 / (r - 1)).
  { destruct (Nat.lt_ge_cases (i + 1) n) as [Hi1 | Hi1].
    - apply (split_sum_geometric_bound_one r Hr_gt1 i n G).
      + exact Hi1.
      + unfold G; simpl; destruct (eq_nat_dec i i); [reflexivity | lia].
      + exact H_G_bound.
    - apply Rle_trans with (/ (r - 1)).
      + apply (row_sum_bound_when_i_last_one r i n G Hr_gt1).
        * exact Hi.
        * exact Hi1.
        * unfold G; simpl; destruct (eq_nat_dec i i); [reflexivity | lia].
        * exact H_G_bound.
      + assert (H12 : 1 <= 2) by lra.
        apply Rmult_le_compat_r with (r := / (r - 1)) in H12;
          [| apply Rlt_le, Rinv_0_lt_compat; lra].
        rewrite Rmult_1_l in H12. exact H12. }
  (* sum F <= 2 * (2/(r-1)) = 4/(r-1) = 4*K *)
  assert (H2pos : 0 <= 2) by lra.
  assert (HsumF : sum_f_R0 F (n - 1) <= 2 * (2 / (r - 1))).
  { apply Rle_trans with (2 * sum_f_R0 G (n - 1)).
    - rewrite <- Hsum_scal. exact Hsum_le.
    - apply Rmult_le_compat_l; [exact H2pos | exact HsumG]. }
  (* 2 * (2/(r-1)) = 4/(r-1)；4*K(INR C) = 4/(r-1) *)
  assert (HK_eq : 4 * K (INR C) = 4 / (r - 1)).
  { unfold K, r. field. apply Rgt_not_eq. exact Hr_gt1'. }
  apply Rle_trans with (4 / (r - 1)).
  - (* sum F <= 2 * (2/(r-1)) <= 4/(r-1) *)
    apply Rle_trans with (2 * (2 / (r - 1))); [exact HsumF | lra].
  - rewrite <- HK_eq. apply Rle_refl.
Qed.

(* P3b：框架界——base_seq 实例化 psi_unconditional_basis（Riesz 常数 1±4K，C > 2） *)
Theorem psa_frame_bounds (C start : nat) (I : list nat) (coeffs : list Complex) :
  (C > 2)%nat -> (start >= 2)%nat -> NoDup I -> Sorted Nat.lt I ->
  length I = length coeffs ->
  let n := length I in
  let vals := map (base_seq C start) I in
  let F := fun k => Csum (fun idx => nth idx coeffs C0 *c psi (nth idx vals 0%nat) k) n in
  let maxIdx := fold_right Nat.max 0%nat I in
  let M := S (base_seq C start maxIdx) in
  let S := sum_f_R0 (fun i => Cnorm_sq (nth i coeffs C0)) (n - 1) in
  ((1 - 4 * K (INR C)) * S <= l2_norm_sq F (M - 1) <= (1 + 4 * K (INR C)) * S)%R.
Proof.
  intros HC Hstart Hdup Hsorted Hlen.
  cbv zeta.
  apply (ExtendedTheorems.psi_unconditional_basis (base_seq C start)).
  - intros i. apply (proj1 (base_seq_global_growth C start (Nat.lt_le_incl _ _ HC) Hstart i)).
  - intros i. apply (base_seq_strictly_increasing C start (Nat.lt_le_incl _ _ HC) Hstart i).
  - exact HC.
  - intros i. apply (proj2 (base_seq_global_growth C start (Nat.lt_le_incl _ _ HC) Hstart i)).
  - exact Hdup.
  - exact Hsorted.
  - exact Hlen.
Qed.



(* 1/ 系数低相干（P4 前瞻）：内部序列路线（seq := base_seq C start 全局增长），
   decay_bound_tight_ij 的 dist=1 特例——相邻基内积范数 ≤ 1/√C（比 2/√C 收紧一倍）。
   注：此版本用全局增长前提（非守卫有限化），与 psa_low_coherence（2/√C 守卫版）互补。 *)
Theorem psa_low_coherence_tight (C start i : nat) :
  (C >= 2)%nat -> (start >= 2)%nat ->
  Cnorm (Csum (fun k => psi (base_seq C start i) k *c Cconj (psi (base_seq C start (S i)) k))
              (base_seq C start (S i) - 1))
  <= / sqrt (INR C).
Proof.
  intros HC Hstart.
  assert (Hge2 : forall i0, (base_seq C start i0 >= 2)%nat).
  { intros i0. apply (proj1 (base_seq_global_growth C start HC Hstart i0)). }
  assert (Hsparse : forall i0, (INR (base_seq C start (S i0)) > INR C * INR (base_seq C start i0))%R).
  { intros i0. apply (proj2 (base_seq_global_growth C start HC Hstart i0)). }
  assert (Hsorted : Sorted Nat.lt (i :: S i :: nil)).
  { apply Sorted_cons.
    - apply Sorted_cons; [constructor | constructor].
    - apply HdRel_cons. apply Nat.lt_succ_diag_r. }
  assert (Hnodup : NoDup (i :: S i :: nil)).
  { apply NoDup_cons.
    - intros H. simpl in H. destruct H as [Heq | Hf].
      + exfalso. apply (Nat.neq_succ_diag_l i). exact Heq.
      + contradiction.
    - apply NoDup_cons.
      + simpl. intros H. contradiction.
      + constructor. }
  pose proof (decay_bound_tight_ij (base_seq C start) (i :: S i :: nil) C
               HC Hge2 Hsparse Hsorted Hnodup 0 1 (Nat.lt_0_1) (ltac:(simpl; lia)) (ltac:(simpl; lia))) as Ht.
  simpl in Ht.
  (* 求和上限：Nat.max i (S i) = S i（目标用 base_seq (S i)） *)
  replace (base_seq C start (Nat.max i (S i))) with (base_seq C start (S i)) in Ht.
  - (* RHS：/ (sqrt C * 1) = / sqrt C（(sqrt C)^1 的 simpl 展开） *)
    replace (sqrt (INR C) * 1) with (sqrt (INR C)) in Ht.
    + exact Ht.
    + ring.
  - exact (eq_sym (f_equal (base_seq C start) (Nat.max_r i (S i) (Nat.lt_le_incl i (S i) (Nat.lt_succ_diag_r i))))).
Qed.



(* ============ list_sum_R 基础性质 ============ *)

End PipelineEndToEnd.

(* ============================================================================
   ExpSeries：exp 的级数构造性事实（M1.5 级数重写，会话 14）
   ----------------------------------------------------------------------------
   目标：PSA 审计中 4 项 classic 残留的唯一入口是 exp 单调性（exp_mono_le 走
   Req_dec + exp_increasing，而 exp_increasing 经导数/MVT 链携带 classic）。
   本模块从 exp 的级数定义（Stdlib Rtrigo_def.v：exp = proj1_sig (exist_exp)，
   E1_cvg : Un_cv (E1 x) (exp x) 定义性成立）直接构造性导出：
     1) exp t >= 1（t>=0）——部分和 E1 t N >= 1 + ε-N 反证（probe_exp_ge_1）；
     2) exp t >= 1 + t（t>=0）——exp_ineq1 的级数替身（probe_exp_ge_1_plus）；
     3) exp 单调（x<=y -> exp x <= exp y）——exp_plus 分解 + 乘正保序
        （exp_mono_le_noclassic）。
   三条主引理 Print Assumptions 均为 sig_not_dec + sig_forall_dec + fext
   （PSA 135 项干净定理的同一允许集），Classical_Prop.classic 命中 0。
   来源：探针 D:\ComplexAnalysis\Live_GLM\探针\m15_bridge_test.v（RC=0 实测）。
   ============================================================================ *)
Module ExpSeries.

Lemma pow_nonneg_mine : forall (x:R) (n:nat), 0 <= x -> 0 <= x ^ n.
Proof.
  intros x n Hx. induction n as [| n IH].
  - simpl. lra.
  - simpl. apply Rmult_le_pos; [exact Hx | exact IH].
Qed.

(* fact 的 stdlib 定义：fact(S n) = fact n + n * fact n = S n * fact n *)
Lemma fact_ge_1_mine : forall n:nat, (1 <= fact n)%nat.
Proof. induction n as [| n IH]; simpl; nia. Qed.

Lemma term_nonneg : forall (t:R) (k:nat), 0 <= t -> 0 <= / INR (fact k) * t ^ k.
Proof.
  intros t k Ht. apply Rmult_le_pos.
  - apply Rlt_le. apply Rinv_0_lt_compat. apply lt_0_INR.
    pose proof (fact_ge_1_mine k). lia.
  - apply pow_nonneg_mine; exact Ht.
Qed.

(* 部分和下界 E1 t N >= 1（decomp_sum + cond_pos_sum） *)
Lemma E1_ge_1 : forall (t:R) (N:nat), 0 <= t -> 1 <= E1 t N.
Proof.
  intros t N Ht.
  destruct N as [| N'].
  - unfold E1. simpl. rewrite Rmult_1_r, Rinv_1. lra.
  - unfold E1. rewrite decomp_sum by lia. cbv beta.
    replace (Nat.pred (S N')) with N' by reflexivity.
    assert (Hrest : 0 <= sum_f_R0 (fun i : nat => / INR (fact (S i)) * t ^ S i) N').
    { apply cond_pos_sum. intros n. apply term_nonneg; exact Ht. }
    assert (Ha0 : / INR (fact 0) * t ^ 0 = 1%R).
    { simpl. rewrite Rmult_1_r, Rinv_1. reflexivity. }
    rewrite Ha0. apply Rle_trans with (1 + 0)%R; [rewrite Rplus_0_r; apply Rle_refl | apply Rplus_le_compat_l; exact Hrest].
Qed.

(* 部分和下界 E1 t N >= 1 + t（N >= 2） *)
Lemma E1_ge_1_plus : forall (t:R) (N:nat), (2 <= N)%nat -> 0 <= t -> 1 + t <= E1 t N.
Proof.
  intros t N HN Ht.
  assert (Hpos : (0 < N)%nat) by lia. assert (Hpos2 : (0 < Nat.pred N)%nat) by lia.
  unfold E1. rewrite decomp_sum by exact Hpos. cbv beta.
  assert (Ha0 : / INR (fact 0) * t ^ 0 = 1%R).
  { simpl. rewrite Rmult_1_r, Rinv_1. reflexivity. }
  rewrite Ha0.
  rewrite decomp_sum by lia. cbv beta.
  assert (Hrest : 0 <= sum_f_R0 (fun i : nat => / INR (fact (S (S i))) * t ^ S (S i))
                      (Nat.pred (Nat.pred N))).
  { apply cond_pos_sum. intros n. apply term_nonneg; exact Ht. }
  assert (Ha1 : / INR (fact 1) * t ^ 1 = t).
  { simpl. rewrite !Rmult_1_r, Rinv_1, Rmult_1_l. reflexivity. }
  rewrite Ha1. apply Rle_trans with (1 + (t + 0))%R; [rewrite Rplus_0_r; apply Rle_refl | apply Rplus_le_compat_l; apply Rplus_le_compat_l; exact Hrest].
Qed.

(* 主缺口：exp t >= 1（t>=0），ε-N 反证 + E1_cvg（不除 2，eps := 1 - exp t） *)
Lemma probe_exp_ge_1 : forall t:R, 0 <= t -> 1 <= exp t.
Proof.
  intros t Ht.
  destruct (Rle_dec 1 (exp t)) as [H | Hl].
  - exact H.
  - exfalso.
    assert (Hlt : exp t < 1) by (apply Rnot_le_lt; exact Hl).
    assert (Heps : 0 < 1 - exp t) by lra.
    destruct (E1_cvg t (1 - exp t) Heps) as [N HN].
    specialize (HN N (Nat.le_refl N)).
    pose proof (E1_ge_1 t N Ht) as HE.
    unfold Rdist in HN.
    assert (Habs : Rabs (E1 t N - exp t) = E1 t N - exp t).
    { apply Rabs_right. lra. }
    rewrite Habs in HN. lra.
Qed.

(* 1 + t <= exp t（t>=0，供 exp_ineq1 级数重写；二次 decomp_sum + n = max N 2） *)
Lemma probe_exp_ge_1_plus : forall t:R, 0 <= t -> 1 + t <= exp t.
Proof.
  intros t Ht.
  destruct (Rle_dec (1 + t) (exp t)) as [H | Hl].
  - exact H.
  - exfalso.
    assert (Hlt : exp t < 1 + t) by (apply Rnot_le_lt; exact Hl).
    assert (Heps : 0 < 1 + t - exp t) by lra.
    destruct (E1_cvg t (1 + t - exp t) Heps) as [N HN].
    assert (Hn1 : (2 <= Nat.max N 2)%nat) by lia.
    assert (HnN : (N <= Nat.max N 2)%nat) by lia.
    pose proof (E1_ge_1_plus t (Nat.max N 2) Hn1 Ht) as HE.
    specialize (HN (Nat.max N 2) HnN).
    unfold Rdist in HN.
    assert (Habs : Rabs (E1 t (Nat.max N 2) - exp t) = E1 t (Nat.max N 2) - exp t).
    { apply Rabs_right. lra. }
    rewrite Habs in HN. lra.
Qed.

(* 零 classic 单调性（exp_plus 分解 + 乘正保序）——PSA 唯一 classic 入口的构造性替身 *)
Lemma exp_mono_le_noclassic : forall x y:R, x <= y -> exp x <= exp y.
Proof.
  intros x y Hxy.
  assert (Hy : exp y = exp x * exp (y - x)).
  { rewrite <- exp_plus. f_equal. ring. }
  rewrite Hy.
  apply Rle_trans with (exp x * 1).
  - rewrite Rmult_1_r. apply Rle_refl.
  - apply Rmult_le_compat_l.
    + apply Rlt_le. apply exp_pos.
    + apply probe_exp_ge_1. lra.
Qed.

End ExpSeries.

Module SoftmaxStability.

Import RowTruncation.
Import SeqProps.

Lemma list_sum_R_le_compat (f g : nat -> R) (l : list nat) :
  (forall i, In i l -> (f i <= g i)%R) ->
  (list_sum_R f l <= list_sum_R g l)%R.
Proof.
  intros H.
  induction l as [| h t IH].
  - simpl. lra.
  - simpl. apply Rplus_le_compat.
    + apply H. left. reflexivity.
    + apply IH. intros i Hi. apply H. right. exact Hi.
Qed.

Lemma list_sum_R_mult_r (f : nat -> R) (c : R) (l : list nat) :
  list_sum_R (fun i => f i * c) l = (c * list_sum_R f l)%R.
Proof.
  induction l as [| h t IH].
  - simpl. ring.
  - simpl. rewrite IH. ring.
Qed.

(* ============ exp 辅助 ============ *)

(* 证明体替换（M1.5 级数重写，会话 14）：原 Req_dec + exp_increasing（MVT 链）携带
   classic；改用 ExpSeries 的级数构造性单调性（exp_plus 分解 + 乘正保序），零 classic。
   语句不变，下游调用（exp_diff_le_d 等）零改动。 *)
Lemma exp_mono_le : forall x y : R, (x <= y)%R -> (exp x <= exp y)%R.
Proof.
  apply ExpSeries.exp_mono_le_noclassic.
Qed.

Lemma exp_diff_le_d : forall x y d : R,
  (0 <= d)%R -> (Rabs (x - y) <= d)%R ->
  (exp (x - y) <= exp d)%R /\ (exp (y - x) <= exp d)%R.
Proof.
  intros x y d Hd Habs.
  split.
  - apply exp_mono_le.
    assert (H1 : (x - y <= Rabs (x - y))%R) by apply Rle_abs.
    lra.
  - apply exp_mono_le.
    assert (H2 : (y - x <= Rabs (y - x))%R) by apply Rle_abs.
    replace (y - x) with (- (x - y)) in H2 by ring.
    rewrite Rabs_Ropp in H2.
    lra.
Qed.

(* ============ softmax ============ *)

Definition softmax_l (z : nat -> R) (n i : nat) : R :=
  exp (z i) / list_sum_R (fun j => exp (z j)) (seq 0%nat n).

Lemma list_sum_R_seq_pos (f : nat -> R) (n : nat) :
  (forall i, (i < n)%nat -> (0 <= f i)%R) ->
  (0 <= list_sum_R f (seq 0%nat n))%R.
Proof.
  intros H.
  assert (Hzero : (list_sum_R (fun _ => 0%R) (seq 0%nat n) = 0)%R).
  { induction (seq 0%nat n) as [| h t IH2]; simpl; [lra | rewrite IH2; ring]. }
  assert (Hle0 : (list_sum_R (fun _ => 0%R) (seq 0%nat n) <= list_sum_R f (seq 0%nat n))%R).
  { apply list_sum_R_le_compat. intros i Hi.
    destruct (In_nth (seq 0%nat n) i 0%nat Hi) as [k [Hk Hkth]].
    apply H.
    rewrite <- Hkth. rewrite length_seq in Hk. rewrite (@seq_nth n 0%nat k 0%nat Hk). lia. }
  lra.
Qed.

Lemma list_sum_R_pos (f : nat -> R) (l : list nat) :
  (forall i, In i l -> (0 <= f i)%R) -> (0 <= list_sum_R f l)%R.
Proof.
  intros H.
  induction l as [| h t IH].
  - simpl. lra.
  - simpl. apply Rplus_le_le_0_compat.
    + apply H. left. reflexivity.
    + apply IH. intros i Hi. apply H. right. exact Hi.
Qed.

Lemma softmax_denom_pos (z : nat -> R) (n : nat) :
  (0 < n)%nat -> (0 < list_sum_R (fun j => exp (z j)) (seq 0%nat n))%R.
Proof.
  intros Hn.
  destruct n as [| n']; [lia |].
  simpl.
  assert (Hrest : (0 <= list_sum_R (fun j => exp (z j)) (seq 1%nat n'))%R).
  { apply list_sum_R_pos. intros j Hj. apply Rlt_le. apply exp_pos. }
  assert (Hexp0 : (0 < exp (z 0%nat))%R) by apply exp_pos.
  lra.
Qed.

Lemma softmax_sum_one (z : nat -> R) (n : nat) :
  (0 < n)%nat ->
  (list_sum_R (fun i => softmax_l z n i) (seq 0%nat n) = 1)%R.
Proof.
  intros Hn.
  unfold softmax_l, Rdiv.
  rewrite (list_sum_R_mult_r (fun i => exp (z i))
                             (/ list_sum_R (fun j => exp (z j)) (seq 0%nat n))
                             (seq 0%nat n)).
  field.
  apply Rgt_not_eq. apply softmax_denom_pos. exact Hn.
Qed.

(* 比率界：||z - z'||_inf <= d ⟹ softmax z n i <= e^{2d} softmax z' n i *)
Lemma softmax_ratio_le2 (z z' : nat -> R) (n i : nat) (d : R) :
  (0 < n)%nat -> (i < n)%nat -> (0 <= d)%R ->
  (forall k, (k < n)%nat -> (Rabs (z k - z' k) <= d)%R) ->
  (softmax_l z n i <= exp (2 * d) * softmax_l z' n i)%R.
Proof.
  intros Hn Hi Hd H.
  unfold softmax_l, Rdiv.
  set (S := list_sum_R (fun j => exp (z j)) (seq 0%nat n)).
  set (S' := list_sum_R (fun j => exp (z' j)) (seq 0%nat n)).
  assert (HS : (0 < S)%R) by (unfold S; apply softmax_denom_pos; exact Hn).
  assert (HS' : (0 < S')%R) by (unfold S'; apply softmax_denom_pos; exact Hn).
  assert (Hnum : (exp (z i) <= exp d * exp (z' i))%R).
  { destruct (exp_diff_le_d (z i) (z' i) d Hd (H i Hi)) as [Hle _].
    assert (Heq : (exp (z i) = exp (z' i) * exp (z i - z' i))%R).
    { rewrite <- (exp_plus (z' i) (z i - z' i)). f_equal. ring. }
    rewrite Heq.
    rewrite (Rmult_comm (exp (z' i)) (exp (z i - z' i))).
    apply Rmult_le_compat_r; [apply Rlt_le; apply exp_pos | exact Hle]. }
  assert (Hden : (S' <= exp d * S)%R).
  { unfold S, S'.
    rewrite <- (list_sum_R_mult_r (fun j => exp (z j)) (exp d) (seq 0%nat n)).
    apply list_sum_R_le_compat. intros j Hj.
    assert (Hj_lt : (j < n)%nat).
    { destruct (In_nth (seq 0%nat n) j 0%nat Hj) as [k [Hk Hkth]].
      rewrite length_seq in Hk.
      assert (Hkseq : (nth k (seq 0%nat n) 0%nat = k)%nat) by (rewrite (@seq_nth n 0%nat k 0%nat Hk); lia).
      rewrite Hkth in Hkseq. lia. }
    destruct (exp_diff_le_d (z' j) (z j) d Hd) as [Hle _].
    { assert (Habs : (Rabs (z j - z' j) <= d)%R) by (apply H; exact Hj_lt).
      replace (z' j - z j) with (- (z j - z' j)) by ring.
      rewrite Rabs_Ropp. exact Habs. }
    assert (Heq : (exp (z' j) = exp (z j) * exp (z' j - z j))%R).
    { rewrite <- (exp_plus (z j) (z' j - z j)). f_equal. ring. }
    rewrite Heq.
    replace (exp d * exp (z j)) with (exp (z j) * exp d) by ring.
    apply (@Rmult_le_compat_l (exp (z j)) (exp (z' j - z j)) (exp d));
      [apply Rlt_le; apply exp_pos | exact Hle]. }
  (* 目标：a/S <= e^{2d}·b/S'。等价于 a·S' <= e^{2d}·b·S（S,S' > 0，交叉乘） *)
  apply (Rmult_le_reg_r (S')).
  { exact HS'. }
  apply (Rmult_le_reg_l (S)).
  { exact HS. }
  (* 两边乘 S·S'：目标 a·S' <= e^{2d}·b·S（field 化简除法） *)
  (* 注意顺序：先乘 S' 再乘 S，得到 a/S·S·S' <= e^{2d}b/S'·S·S'，field 化简 *)
  field_simplify; [| apply Rgt_not_eq; exact HS' | apply Rgt_not_eq; exact HS].
  apply Rle_trans with (exp d * exp (z' i) * (exp d * S)).
  - apply Rmult_le_compat; [apply Rlt_le; apply exp_pos | apply Rlt_le; exact HS'
                           | exact Hnum | exact Hden].
  - assert (Hsame : (exp d * exp (z' i) * (exp d * S) = exp (2 * d) * (exp (z' i) * S))%R).
    { replace (exp d * exp (z' i) * (exp d * S)) with (exp (z' i) * S * (exp d * exp d)) by ring.
      rewrite <- (exp_plus d d).
      replace (d + d) with (2 * d) by ring.
      ring. }
    rewrite Hsame. ring_simplify. reflexivity.
Qed.

(* 逐分量差：|p_i - p'_i| <= p'_i (e^{2d} - 1) *)
Lemma softmax_diff_i (z z' : nat -> R) (n i : nat) (d : R) :
  (0 < n)%nat -> (i < n)%nat -> (0 <= d)%R ->
  (forall k, (k < n)%nat -> (Rabs (z k - z' k) <= d)%R) ->
  (Rabs (softmax_l z n i - softmax_l z' n i) <=
   softmax_l z' n i * (exp (2 * d) - 1))%R.
Proof.
  intros Hn Hi Hd H.
  pose proof (softmax_ratio_le2 z z' n i d Hn Hi Hd H) as Hle.
  assert (Hge : (softmax_l z' n i <= exp (2 * d) * softmax_l z n i)%R).
  { apply (softmax_ratio_le2 z' z n i d Hn Hi Hd).
    intros k Hk.
    replace (z' k - z k) with (- (z k - z' k)) by ring.
    rewrite Rabs_Ropp.
    exact (H k Hk). }
  assert (Hp' : (0 <= softmax_l z' n i)%R).
  { unfold softmax_l, Rdiv. apply Rmult_le_pos; [apply Rlt_le; apply exp_pos | ].
    apply Rlt_le. apply Rinv_0_lt_compat. apply softmax_denom_pos. exact Hn. }
  destruct (Rle_lt_dec (softmax_l z' n i) (softmax_l z n i)) as [Hpp | Hpp'].
  - (* p >= p' *)
    rewrite Rabs_pos_eq; [| lra].
    apply Rle_trans with (exp (2 * d) * softmax_l z' n i - softmax_l z' n i).
    + apply Rplus_le_compat_r. exact Hle.
    + rewrite Rmult_minus_distr_l. lra.
  - (* p < p'：p' - p <= p'(1 - e^{-2d}) <= p'(e^{2d} - 1) *)
    rewrite Rabs_left; [| lra].
    assert (Hp_ge : (exp (- (2 * d)) * softmax_l z' n i <= softmax_l z n i)%R).
    { apply Rmult_le_reg_l with (exp (2 * d)).
      - apply exp_pos.
      - rewrite <- Rmult_assoc.
        rewrite <- (exp_plus (2 * d) (- (2 * d))).
        rewrite Rplus_opp_r. rewrite exp_0.
        rewrite Rmult_1_l.
        exact Hge. }
    assert (Hdiff : (softmax_l z' n i - softmax_l z n i <=
                     softmax_l z' n i * (1 - exp (- (2 * d))))%R).
    { assert (Hmid : (softmax_l z' n i - softmax_l z n i <=
                      softmax_l z' n i - exp (- (2 * d)) * softmax_l z' n i)%R).
      { apply Rplus_le_compat; [apply Rle_refl | apply Ropp_le_contravar; exact Hp_ge]. }
      apply Rle_trans with (softmax_l z' n i - exp (- (2 * d)) * softmax_l z' n i); [exact Hmid | ].
      assert (Heq : (softmax_l z' n i - exp (- (2 * d)) * softmax_l z' n i =
                     softmax_l z' n i * (1 - exp (- (2 * d))))%R) by ring.
      rewrite Heq. apply Rle_refl. }
    apply Rle_trans with (softmax_l z' n i * (1 - exp (- (2 * d)))).
    + replace (- (softmax_l z n i - softmax_l z' n i)) with (softmax_l z' n i - softmax_l z n i) by ring.
      exact Hdiff.
    apply Rmult_le_compat_l; [exact Hp' | ].
    assert (He1 : (1 <= exp (2 * d))%R).
    { rewrite <- exp_0. apply exp_mono_le. apply Rmult_le_pos; lra. }
    assert (H2 : (1 - exp (- (2 * d)) <= exp (2 * d) - 1)%R).
    { rewrite exp_Ropp.
      apply Rmult_le_reg_l with (exp (2 * d)).
      - apply exp_pos.
      - field_simplify; [| apply exp_neq_0].
        nra. }
    exact H2.
Qed.

(* S1：||softmax z - softmax z'||_1 <= e^{2d} - 1 *)
Lemma softmax_l1_bound_exp (z z' : nat -> R) (n : nat) (d : R) :
  (0 < n)%nat -> (0 <= d)%R ->
  (forall k, (k < n)%nat -> (Rabs (z k - z' k) <= d)%R) ->
  (list_sum_R (fun i => Rabs (softmax_l z n i - softmax_l z' n i)) (seq 0%nat n)
   <= exp (2 * d) - 1)%R.
Proof.
  intros Hn Hd H.
  (* Σ|p - p'| <= (exp(2d)-1) * Σp'，再 Σp' = 1 *)
  apply Rle_trans with ((exp (2 * d) - 1) * list_sum_R (fun i => softmax_l z' n i) (seq 0%nat n)).
  - rewrite <- (list_sum_R_mult_r (fun i => softmax_l z' n i) (exp (2 * d) - 1) (seq 0%nat n)).
    apply list_sum_R_le_compat. intros i Hi.
    assert (Hi_lt : (i < n)%nat).
    { destruct (In_nth (seq 0%nat n) i 0%nat Hi) as [k [Hk Hkth]].
      rewrite length_seq in Hk.
      assert (Hkseq : (nth k (seq 0%nat n) 0%nat = k)%nat) by (rewrite (@seq_nth n 0%nat k 0%nat Hk); lia).
      rewrite Hkth in Hkseq. lia. }
    apply (softmax_diff_i z z' n i d Hn Hi_lt Hd).
    intros k' Hk'. apply H. exact Hk'.
  - rewrite (softmax_sum_one z' n Hn). rewrite Rmult_1_r. apply Rle_refl.
Qed.

End SoftmaxStability.
(* ============================================================
   M2（2026-08-19）：T3 认证低秩注意力链条
   ------------------------------------------------------------
   链条（论文 §4 主线 3 的定理本体，A2 路线）：
     每行丢弃谱能量 ≤ ε ─(linf_le_sqrt_sqsum, ℓ∞≤ℓ₂)─> ‖Δz‖∞ ≤ √ε
     ─(softmax_l1_bound_exp, S1 弱版)─> ‖Δp‖₁ ≤ e^{2√ε} − 1
     ─(weighted_avg_lipschitz)─> ‖Δout‖ ≤ (e^{2√ε} − 1)·V_max
   输出定理：certified_attention_approx（谱能量界 ⟹ 输出扰动界）。
   注：S2 紧版（2√ε 系数）为后续收紧方向；弱版 e^{2√ε}−1 不阻塞链条
   （路线图 A1 明确标注"紧版受阻则弱版足够"）。
   公理：R 级经 Reals 继承 sig_forall_dec+fext，零 classic。
   ============================================================ *)
Module CertifiedAttention.

Import RowTruncation.
Import SeqProps.
Import SoftmaxStability.
Import ExtendedTheorems.
Open Scope R_scope.

(* 本模块使用的 Complex 类型上的相等引理（ComplexFoundation.Complex_eq 是另一类型，勿用） *)
Lemma Complex_eq_local (z1 z2 : Complex) :
  re z1 = re z2 -> im z1 = im z2 -> z1 = z2.
Proof.
  destruct z1 as [x1 y1]; destruct z2 as [x2 y2]; simpl; intros Hre Him; subst; reflexivity.
Qed.

(* ---------- 桥接：list_sum_R 与 sum_f_R0 ---------- *)

Lemma list_sum_R_map (f : nat -> R) (g : nat -> nat) (l : list nat) :
  list_sum_R f (map g l) = list_sum_R (fun i => f (g i)) l.
Proof.
  induction l as [| h t IH]; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma sum_f_R0_shift_head (f : nat -> R) (n : nat) :
  sum_f_R0 f (S n) = f 0%nat + sum_f_R0 (fun k => f (S k)) n.
Proof.
  induction n as [| n IH].
  - simpl. ring.
  - rewrite sum_f_R0_S. rewrite IH. rewrite sum_f_R0_S. ring.
Qed.

Lemma list_sum_R_seq_eq_sum_f_R0 (f : nat -> R) (n : nat) :
  (0 < n)%nat -> list_sum_R f (seq 0%nat n) = sum_f_R0 f (n - 1)%nat.
Proof.
  intros Hn. destruct n as [| n']; [lia |].
  clear Hn.
  replace (S n' - 1)%nat with n' by lia.
  revert f. induction n' as [| n' IH]; intros f.
  - simpl. ring.
  - assert (Hseq1 : seq 0%nat (S (S n')) = 0%nat :: seq 1%nat (S n')) by reflexivity.
    assert (Hseq2 : seq 1%nat (S n') = map S (seq 0%nat (S n'))).
    { apply (seq_shift_gen (S n') 0%nat). }
    rewrite Hseq1, Hseq2.
    change (f 0%nat + list_sum_R f (map S (seq 0%nat (S n'))) = sum_f_R0 f (S n')).
    rewrite (list_sum_R_map f S (seq 0%nat (S n'))).
    rewrite (IH (fun k => f (S k))).
    symmetry. apply sum_f_R0_shift_head.
Qed.

(* ---------- ① ℓ∞ ≤ ℓ₂：能量界 ⟹ 逐元素界 ---------- *)

Lemma Rsqr_le_list_sum (f : nat -> R) (l : list nat) :
  (forall j, In j l -> (0 <= f j)%R) ->
  forall i, In i l -> (f i <= list_sum_R f l)%R.
Proof.
  intros Hnonneg i.
  induction l as [| h t IH]; intros Hi.
  - inversion Hi.
  - simpl.
    destruct (eq_nat_dec i h) as [Heq | Hneq].
    + subst.
      assert (H0 : (0 <= list_sum_R f t)%R).
      { apply list_sum_R_pos. intros j Hj. apply Hnonneg. right. exact Hj. }
      lra.
    + assert (Hi_t : In i t).
      { destruct Hi as [Heq | Hin].
        - exfalso. apply Hneq. symmetry. exact Heq.
        - exact Hin. }
      apply Rle_trans with (list_sum_R f t).
      * apply IH.
        + intros j Hj. apply Hnonneg. right. exact Hj.
        + exact Hi_t.
      * assert (Hh : (0 <= f h)%R) by (apply Hnonneg; left; reflexivity).
        lra.
Qed.

(* 丢弃谱能量 ≤ eps ⟹ 每个 logit 分量扰动 |Δz_i| ≤ sqrt eps *)
Lemma linf_le_sqrt_sqsum (a : nat -> R) (l : list nat) (i : nat) (eps : R) :
  (0 <= eps)%R -> In i l ->
  (list_sum_R (fun j => Rsqr (a j)) l <= eps)%R ->
  (Rabs (a i) <= sqrt eps)%R.
Proof.
  intros Heps Hi Hsum.
  assert (Hsqr : (Rsqr (a i) <= list_sum_R (fun j => Rsqr (a j)) l)%R).
  { apply (Rsqr_le_list_sum (fun j => Rsqr (a j)) l).
    - intros j Hj. apply Rle_0_sqr.
    - exact Hi. }
  apply Rle_trans with (sqrt (Rsqr (a i))).
  - rewrite <- sqrt_Rsqr_abs. apply Rle_refl.
  - apply sqrt_le_1.
    + apply Rle_0_sqr.
    + exact Heps.
    + apply Rle_trans with (list_sum_R (fun j => Rsqr (a j)) l); [exact Hsqr | exact Hsum].
Qed.

(* ---------- 复代数小件 ---------- *)

(* Csum 范数三角不等式：‖Csum g N‖ ≤ Σ_{k<N} ‖g k‖ *)
Lemma Csum_norm_le_sum_pred (g : nat -> Complex) (N : nat) :
  (Cnorm (Csum g N) <= sum_f_R0 (fun k => Cnorm (g k)) (N - 1)%nat)%R.
Proof.
  destruct N as [| p].
  - rewrite Csum_0. rewrite Cnorm_0. simpl. apply Cnorm_nonneg.
  - assert (Hbase : forall g0 p0,
      (Cnorm (Csum g0 (S p0)) <= sum_f_R0 (fun k => Cnorm (g0 k)) p0)%R).
    { intros g0 p0. induction p0 as [| p0 IH].
      - rewrite Csum_S. rewrite Csum_0.
        assert (H0l : forall z : Complex, C0 +c z = z).
        { intro z. destruct z as [x y]. unfold C0, Cadd. apply Complex_eq_local; simpl; ring. }
        rewrite (H0l (g0 0%nat)).
        simpl. apply Rle_refl.
      - rewrite Csum_S. rewrite sum_f_R0_S.
        apply Rle_trans with (Cnorm (Csum g0 (S p0)) + Cnorm (g0 (S p0))).
        + apply ExtendedTheorems.Cnorm_triangle.
        + apply Rplus_le_compat; [exact IH | apply Rle_refl]. }
    replace ((S p) - 1)%nat with p by lia.
    apply Hbase.
Qed.

Lemma Cnorm_Cof_real_abs (r : R) : Cnorm (Cof_real r) = Rabs r.
Proof.
  unfold Cof_real, Cnorm, Cnorm_sq, Rsqr; simpl.
  rewrite Rmult_0_l, Rplus_0_r.
  apply sqrt_Rsqr_abs.
Qed.

Lemma Cof_real_minus (a b : R) : Csub (Cof_real a) (Cof_real b) = Cof_real (a - b).
Proof.
  unfold Cof_real, Csub. apply Complex_eq_local; simpl; ring.
Qed.

Lemma Csub_add_distr (a b c d : Complex) :
  Csub (Cadd a b) (Cadd c d) = Cadd (Csub a c) (Csub b d).
Proof.
  destruct a as [a1 a2]; destruct b as [b1 b2]; destruct c as [c1 c2]; destruct d as [d1 d2].
  unfold Csub, Cadd. apply Complex_eq_local; simpl; ring.
Qed.

Lemma Cmul_sub_distr_l (a b v : Complex) :
  Cmul (Csub a b) v = Csub (Cmul a v) (Cmul b v).
Proof.
  destruct a as [a1 a2]; destruct b as [b1 b2]; destruct v as [v1 v2].
  unfold Csub, Cmul. apply Complex_eq_local; simpl; ring.
Qed.

Lemma Csum_minus (f g : nat -> Complex) (N : nat) :
  Csub (Csum f N) (Csum g N) = Csum (fun k => Csub (f k) (g k)) N.
Proof.
  induction N as [| N IH].
  - rewrite !Csum_0. unfold Csub, C0. apply Complex_eq_local; simpl; ring.
  - rewrite Csum_S. rewrite Csum_S. rewrite Csum_S.
    rewrite Csub_add_distr. rewrite IH. reflexivity.
Qed.

(* 输出差 = 单和：Σ p_j v_j - Σ p'_j v_j = Σ (p_j - p'_j) v_j *)
Lemma attention_output_diff (p p' : nat -> R) (v : nat -> Complex) (n : nat) :
  Csub (Csum (fun j => Cof_real (p j) *c v j) n)
       (Csum (fun j => Cof_real (p' j) *c v j) n)
  = Csum (fun j => Cof_real (p j - p' j) *c v j) n.
Proof.
  rewrite Csum_minus.
  apply Csum_ext. intros k Hk.
  destruct (v k) as [v1 v2].
  unfold Cof_real, Csub, Cmul. apply Complex_eq_local; simpl; ring.
Qed.

(* ---------- ② 加权平均 Lipschitz ---------- *)

Lemma weighted_avg_lipschitz (p p' : nat -> R) (v : nat -> Complex) (n : nat) (delta Vmax : R) :
  (0 < n)%nat -> (0 <= delta)%R -> (0 <= Vmax)%R ->
  (forall j, (j < n)%nat -> (Cnorm (v j) <= Vmax)%R) ->
  (list_sum_R (fun j => Rabs (p j - p' j)) (seq 0%nat n) <= delta)%R ->
  (Cnorm (Csum (fun j => Cof_real (p j - p' j) *c v j) n) <= delta * Vmax)%R.
Proof.
  intros Hn Hd Hvmax Hv Hsum.
  rewrite (list_sum_R_seq_eq_sum_f_R0 (fun j => Rabs (p j - p' j)) n Hn) in Hsum.
  apply Rle_trans with (Vmax * sum_f_R0 (fun k => Rabs (p k - p' k)) (n - 1)%nat)%R.
  - eapply Rle_trans.
    + apply Csum_norm_le_sum_pred.
    + apply Rle_trans with (sum_f_R0 (fun k => Rabs (p k - p' k) * Vmax) (n - 1)%nat).
      * apply sum_f_R0_le_compat. intros k Hk.
        rewrite ExtendedTheorems.Cnorm_mult.
        rewrite Cnorm_Cof_real_abs.
        apply Rmult_le_compat_l; [apply Rabs_pos | apply Hv; lia].
      * rewrite <- (sum_f_R0_scal_l Vmax (fun k => Rabs (p k - p' k)) (n - 1)%nat).
        apply sum_f_R0_le_compat. intros k Hk.
        rewrite (Rmult_comm (Rabs (p k - p' k)) Vmax). apply Rle_refl.
  - rewrite (Rmult_comm delta Vmax).
    apply Rmult_le_compat_l; [exact Hvmax | exact Hsum].
Qed.

(* ---------- ③ T3 链合成 ---------- *)

Theorem certified_attention_approx (z z' : nat -> R) (v : nat -> Complex) (n : nat)
                                  (eps Vmax : R) :
  (0 < n)%nat -> (0 <= eps)%R -> (0 <= Vmax)%R ->
  (forall j, (j < n)%nat -> (Cnorm (v j) <= Vmax)%R) ->
  (list_sum_R (fun j => Rsqr (z j - z' j)) (seq 0%nat n) <= eps)%R ->
  (Cnorm (Csub (Csum (fun j => Cof_real (softmax_l z n j) *c v j) n)
                (Csum (fun j => Cof_real (softmax_l z' n j) *c v j) n))
   <= (exp (2 * sqrt eps) - 1) * Vmax)%R.
Proof.
  intros Hn Heps Hvmax Hv Henergy.
  rewrite (attention_output_diff (fun j => softmax_l z n j) (fun j => softmax_l z' n j) v n).
  apply weighted_avg_lipschitz with (delta := exp (2 * sqrt eps) - 1).
  - exact Hn.
  - assert (H1 : (1 <= exp (2 * sqrt eps))%R).
    { rewrite <- exp_0. apply exp_mono_le. apply Rmult_le_pos; [lra | apply sqrt_pos]. }
    lra.
  - exact Hvmax.
  - exact Hv.
  - apply (softmax_l1_bound_exp z z' n (sqrt eps) Hn).
    + apply sqrt_pos.
    + intros k Hk.
      apply (linf_le_sqrt_sqsum (fun j => z j - z' j) (seq 0%nat n) k eps Heps).
      * rewrite (in_seq n 0%nat k). lia.
      * exact Henergy.
Qed.

End CertifiedAttention.
(* ============================================================
   M3（2026-08-19）：B1 Gershgorin 框架引理 + B2 Dirichlet 闭式
   ------------------------------------------------------------
   B1（框架定理本体）：gershgorin_frame（参数化 μ 版，= 库内
     abstract_unconditional_basis 的命名实例）+ gershgorin_frame_mu
     （论文形式：单位向量系 + 每行非对角内积范数和 ≤ μ ⟹
     (1−μ)‖c‖² ≤ ‖Σc_iψ_i‖² ≤ (1+μ)‖c‖²）。
   B2（实例闭式）：psi_inner_dirichlet——|⟨ψ_{n1},ψ_{n2}⟩| =
     |sin(πNΔ)/sin(πΔ)|/√(n1·n2)（Δ = 1/n1 − 1/n2，窗口 N = n1−1，
     n1 < n2 严格异频带）；支撑：Cexp_pow_local / geom_sum_norm_dirichlet
     （Dirichlet 核范数）/ dirichlet_algebra（末段纯 R 消元）。
   公理：R 级经 Reals 继承 sig_forall_dec+fext，零 classic
     （sin 等 Rtrigo 引理为 Reals 基础，无 Classical_Prop.classic）。
   ============================================================ *)
Module Gershgorin.

Import ExtendedTheorems.
Import UnconditionalBasisLemmas.
Open Scope R_scope.

(* B1a：Gershgorin 框架引理（参数化 μ 版）= 库内 abstract_unconditional_basis 的命名实例。
   前提：单位向量系 + 行非对角内积上界 delta + 行和 ≤ μ ⟹ (1−μ)||c||² ≤ ||F||² ≤ (1+μ)||c||²。 *)
Theorem gershgorin_frame (n : nat) (phi : nat -> nat -> Complex) (M : nat) (mu : R)
                         (delta : nat -> nat -> R) :
  (M > 0)%nat ->
  (forall i k : nat, (i < n)%nat -> (k >= Nat.pred M)%nat -> phi i k = ComplexNumbers.C0) ->
  (forall i : nat, (i < n)%nat -> l2_norm_sq (phi i) (Nat.pred M) = 1%R) ->
  (forall i j : nat, (i < n)%nat -> (j < n)%nat -> delta i j = delta j i) ->
  (forall i j : nat, (i < n)%nat -> (j < n)%nat -> 0%R <= delta i j) ->
  (forall i j : nat, i <> j -> (i < n)%nat -> (j < n)%nat ->
      ComplexNumbers.Cnorm
        (independent.Csum (fun k : nat => phi i k *c ComplexNumbers.Cconj (phi j k))
           (Nat.pred M)) <= delta i j) ->
  (forall i : nat, (i < n)%nat ->
      sum_f_R0 (fun j : nat =>
        if eq_nat_dec i j then 0%R else delta i j) (Nat.pred n) <= mu) ->
  forall (coeffs : list Complex),
    length coeffs = n ->
    let F := fun k : nat =>
      independent.Csum (fun i : nat => nth i coeffs ComplexNumbers.C0 *c phi i k) n in
    let S := sum_f_R0 (fun i : nat => ComplexNumbers.Cnorm_sq (nth i coeffs ComplexNumbers.C0)) (Nat.pred n) in
    ((1 - mu) * S <= l2_norm_sq F (Nat.pred M) <= (1 + mu) * S)%R.
Proof.
  intros H1 H2 H3 H4 H5 H6 H7 coeffs H8.
  cbv zeta.
  exact (ExtendedTheorems.abstract_unconditional_basis n phi M mu delta
           H1 H2 H3 H4 H5 H6 H7 coeffs H8).
Qed.

(* B1b：论文形式——行和直接作用于实际内积范数（delta := |<ψ_i,ψ_j>|），
   单位向量系 + 每行非对角范数和 ≤ μ ⟹ (1−μ)||c||² ≤ ||Σ c_i ψ_i||² ≤ (1+μ)||c||²。 *)
Theorem gershgorin_frame_mu (n : nat) (phi : nat -> nat -> Complex) (M : nat) (mu : R) :
  (M > 0)%nat ->
  (forall i k : nat, (i < n)%nat -> (k >= Nat.pred M)%nat -> phi i k = ComplexNumbers.C0) ->
  (forall i : nat, (i < n)%nat -> l2_norm_sq (phi i) (Nat.pred M) = 1%R) ->
  (forall i : nat, (i < n)%nat ->
      sum_f_R0 (fun j : nat =>
        if eq_nat_dec i j then 0%R
        else ComplexNumbers.Cnorm
               (independent.Csum (fun k : nat => phi i k *c ComplexNumbers.Cconj (phi j k))
                  (Nat.pred M))) (Nat.pred n) <= mu) ->
  forall (coeffs : list Complex),
    length coeffs = n ->
    let F := fun k : nat =>
      independent.Csum (fun i : nat => nth i coeffs ComplexNumbers.C0 *c phi i k) n in
    let S := sum_f_R0 (fun i : nat => ComplexNumbers.Cnorm_sq (nth i coeffs ComplexNumbers.C0)) (Nat.pred n) in
    ((1 - mu) * S <= l2_norm_sq F (Nat.pred M) <= (1 + mu) * S)%R.
Proof.
  intros H1 H2 H3 H4 coeffs H5.
  cbv zeta.
  apply (gershgorin_frame n phi M mu
           (fun i j => ComplexNumbers.Cnorm
             (independent.Csum (fun k : nat => phi i k *c ComplexNumbers.Cconj (phi j k))
                (Nat.pred M)))).
  - exact H1.
  - exact H2.
  - exact H3.
  - intros i j Hi Hj. apply ExtendedTheorems.Cnorm_Csum_conj_sym.
  - intros i j Hi Hj. apply ComplexNumbers.Cnorm_nonneg.
  - intros i j Hneq Hi Hj. apply Rle_refl.
  - exact H4.
  - exact H5.
Qed.

(* ============ B2：Dirichlet 闭式（|⟨ψ_i,ψ_j⟩| = |sin(πNΔ)/sin(πΔ)|/√(n_i n_j)） ============ *)

(* Cexp 幂：Cexp (0+i·n·θ) = (Cexp (0+iθ))^n（模式同 ca_basis_lemmas:4516） *)
Lemma Cexp_pow_local (θ : R) (n : nat) :
  Cexp (0 +i (INR n * θ)) = (Cexp (0 +i θ) ^ n)%C.
Proof.
  induction n as [| n IH].
  - simpl. rewrite Rmult_0_l. apply Cexp_0_eq_1.
  - simpl Cexp.
    change (match n with 0%nat => 1 | S _ => INR n + 1 end) with (INR (S n)).
    rewrite S_INR.
    rewrite Rmult_plus_distr_r.
    rewrite Rmult_1_l.
    replace (0 +i (INR n * θ + θ)) with ((0 +i (INR n * θ)) +c (0 +i θ)).
    2: { unfold Cadd; simpl. f_equal. ring. }
    rewrite Cexp_add.
    rewrite IH.
    simpl. rewrite Cmul_comm. reflexivity.
Qed.

(* 抽象 Dirichlet 核范数：‖Σ_{k<N} z^k‖ = 2|sin(Nθ/2)|·/(2|sin(θ/2)|)，z = e^{iθ} *)
Lemma geom_sum_norm_dirichlet (θ : R) (N : nat) :
  Cexp (0 +i θ) <> C1 ->
  Cnorm (Csum (fun k => (Cexp (0 +i θ) ^ k)%C) N)
  = 2 * Rabs (sin (INR N * θ / 2)) * / (2 * Rabs (sin (θ / 2))).
Proof.
  intros Hz.
  rewrite (geometric_series_sum (Cexp (0 +i θ)) N Hz).
  unfold Cdiv.
  rewrite Cnorm_mult.
  rewrite (norm_of_inverse (C1 -c Cexp (0 +i θ))
             (C1_minus_z_neq0 (Cexp (0 +i θ)) Hz)).
  rewrite <- (Cexp_pow_local θ N).
  rewrite Cnorm_one_minus_exp_i_theta_eq.
  rewrite Cnorm_one_minus_exp_i_theta_eq.
  reflexivity.
Qed.

(* 纯 R 代数：Dirichlet 闭式末段的消元（1/√n1·1/√n2 与 2·|sin| 的约分） *)
Lemma dirichlet_algebra (s t y x : R) :
  s <> 0 -> t <> 0 -> y <> 0 ->
  (1 / s) * (1 / t) * (2 * x * / (2 * y)) = x * / y * / (s * t).
Proof.
  intros Hs Ht Hy.
  field.
  all: try solve [exact Hs | exact Ht | exact Hy | lra
                 | apply Rmult_integral_contrapositive; [exact Hs | exact Ht]
                 | apply Rmult_integral_contrapositive; [lra | exact Hy]].
Qed.

(* B2：psi 基内积的 Dirichlet 闭式（窗口 N := n1−1，库内约定；n1 < n2 严格异频带） *)
Theorem psi_inner_dirichlet (n1 n2 : nat) :
  (n1 >= 2)%nat -> (n2 >= 2)%nat -> (n1 < n2)%nat ->
  let Δ := 1 / INR n1 - 1 / INR n2 in
  let N := (n1 - 1)%nat in
  Cnorm (Csum (fun k => psi n1 k *c Cconj (psi n2 k)) N)
  = Rabs (sin (PI * INR N * Δ)) / Rabs (sin (PI * Δ)) / sqrt (INR n1 * INR n2).
Proof.
  intros Hn1 Hn2 Hlt.
  cbv zeta.
  pose proof (inner_geometric_expansion n1 n2 Hn1 Hn2 (Nat.lt_le_incl _ _ Hlt)) as Hge.
  cbv zeta in Hge.
  rewrite Hge.
  set (Δ := 1 / INR n1 - 1 / INR n2).
  set (θ := 2 * PI * Δ).
  rewrite Cnorm_mult.
  rewrite Cnorm_mult.
  rewrite (Cnorm_Cof_real_pos (1 / sqrt (INR n1))).
  2: { apply Rlt_le. apply Rdiv_lt_0_compat; [lra | apply sqrt_lt_R0_c; apply lt_0_INR; lia]. }
  rewrite (Cnorm_Cof_real_pos (1 / sqrt (INR n2))).
  2: { apply Rlt_le. apply Rdiv_lt_0_compat; [lra | apply sqrt_lt_R0_c; apply lt_0_INR; lia]. }
  (* 几何和 → Dirichlet 核 *)
  assert (Hz : Cexp (0 +i θ) <> C1).
  { unfold θ, Δ. apply (Cexp_diff_not_one n1 n2 Hn1 Hn2 Hlt). }
  rewrite (Csum_ext (n1 - 1) (fun k => Cexp (0 +i (INR k * θ)))
                     (fun k => (Cexp (0 +i θ) ^ k)%C)).
  2: { intros k _. apply Cexp_pow_local. }
  rewrite (geom_sum_norm_dirichlet θ (n1 - 1) Hz).
  (* 纯 R 代数：sin 自变量 + 2 与 √ 的消元 *)
  assert (He1 : (INR (n1 - 1) * θ / 2 = PI * INR (n1 - 1) * Δ)%R).
  { unfold θ. field. }
  rewrite He1.
  assert (He2 : (θ / 2 = PI * Δ)%R).
  { unfold θ. field. }
  rewrite He2.
  rewrite (sqrt_mult (INR n1) (INR n2)).
  2: { apply pos_INR. }
  2: { apply pos_INR. }
  apply (dirichlet_algebra (sqrt (INR n1)) (sqrt (INR n2))
                           (Rabs (sin (PI * Δ))) (Rabs (sin (PI * INR (n1 - 1) * Δ)))).
  - apply Rgt_not_eq. apply sqrt_INR_pos_ge2. exact Hn1.
  - apply Rgt_not_eq. apply sqrt_INR_pos_ge2. exact Hn2.
  - apply Rgt_not_eq. apply Rabs_pos_lt. apply Rgt_not_eq.
    apply sin_gt_0.
    + apply Rmult_lt_0_compat; [apply PI_RGT_0 | apply (proj1 (diff_inv_INR_between_0_1 n1 n2 Hn1 Hn2 Hlt))].
    + apply Rlt_le_trans with (PI * 1).
      * apply Rmult_lt_compat_l; [apply PI_RGT_0 | exact (proj2 (diff_inv_INR_between_0_1 n1 n2 Hn1 Hn2 Hlt))].
      * rewrite Rmult_1_r. apply Rle_refl.
Qed.

End Gershgorin.
(* ============================================================
   M4 Tier 1（2026-08-19）：C=4 实例证书（认证对象 = 最优阶梯）
   ------------------------------------------------------------
   核心：psi_inner_cons_bound（窗口无关保守界 |⟨⟩| ≤ 1/(2Δ√(n1n2))，
   有限支撑 ⟹ 对一切 N ≥ n_max 一致有效）→ 六对界 → 行和 ≤ 4/5 →
   **certified_c4_frame_bounds**：(1/5)·S ≤ ‖Σc_iψ_i‖² ≤ (9/5)·S
   （[3,13,53,213] 子梯，μ = 4/5 保守实例证书，非真空——杀死 C>25 空洞）。
   注：行 13/53 是瓶颈（≈0.79，含对称对）；nra 直接解具体有理数不等式。
   公理：R 级经 Reals 继承 sig_forall_dec+fext，零 classic。
   ============================================================ *)
Module InstanceCertificate.

Import ExtendedTheorems.
Import UnconditionalBasisLemmas.
Import Gershgorin.
Open Scope R_scope.

(* |Cexp (0+iθ)| = 1 *)
Lemma Cnorm_Cexp_unit (θ : R) : Cnorm (Cexp (0 +i θ)) = 1.
Proof.
  unfold Cexp, Cnorm, Cnorm_sq; simpl.
  rewrite exp_0, Rmult_1_l, Rmult_1_l.
  rewrite Rplus_comm.
  rewrite sin2_cos2.
  apply sqrt_1.
Qed.

(* 几何和范数保守界：‖Σ_{k<N} z^k‖ ≤ 2/|1−z|，|z|=1（库内 geometric_sum_norm_bound 命名特例） *)
Lemma geom_norm_cons (z : Complex) (N : nat) :
  z <> C1 -> Cnorm z = 1 ->
  Cnorm (Csum (fun k => (z ^ k)%C) N) <= 2 / Cnorm (C1 -c z).
Proof.
  intros Hz Hnorm.
  apply (geometric_sum_norm_bound z N Hz Hnorm).
Qed.

(* Δ = 1/n1 − 1/n2 > 0（n1 < n2） *)
Lemma delta_pos (n1 n2 : nat) : (n1 > 0)%nat -> (n2 > 0)%nat -> (n1 < n2)%nat ->
  (0 < 1 / INR n1 - 1 / INR n2)%R.
Proof.
  intros H1 H2 Hlt. apply diff_inv_INR_pos; assumption.
Qed.

(* Δ ≤ 1/2（n1 ≥ 2） *)
Lemma delta_le_half (n1 n2 : nat) : (n1 >= 2)%nat -> (n1 < n2)%nat ->
  (1 / INR n1 - 1 / INR n2 <= 1 / 2)%R.
Proof.
  intros Hn1 Hlt.
  assert (Hinv : (1 / INR n1 <= 1 / 2)%R) by (apply inv_INR_le_inv2; exact Hn1).
  assert (Hpos2 : (0 <= 1 / INR n2)%R).
  { apply Rlt_le. apply Rdiv_lt_0_compat; [lra | apply lt_0_INR; lia]. }
  lra.
Qed.

(* sin(πΔ) ≥ 2Δ（Jordan；πΔ ∈ [0, π/2]） *)
Lemma sin_pi_delta_ge_2delta (n1 n2 : nat) :
  (n1 >= 2)%nat -> (n1 < n2)%nat ->
  (2 * (1 / INR n1 - 1 / INR n2) <= sin (PI * (1 / INR n1 - 1 / INR n2)))%R.
Proof.
  intros Hn1 Hlt.
  set (Δ := 1 / INR n1 - 1 / INR n2).
  assert (Hd_pos : 0 < Δ) by (unfold Δ; apply delta_pos; lia).
  assert (Hd_half : Δ <= 1 / 2) by (unfold Δ; apply delta_le_half; [exact Hn1 | exact Hlt]).
  assert (Hpi : (0 <= PI * Δ <= PI / 2)%R).
  { split.
    - apply Rmult_le_pos; [apply Rlt_le; apply PI_RGT_0 | apply Rlt_le; exact Hd_pos].
    - assert (Heq : (PI * (1 / 2) = PI / 2)%R) by (unfold Rdiv; ring).
      rewrite <- Heq.
      apply Rmult_le_compat_l; [apply Rlt_le; apply PI_RGT_0 | exact Hd_half]. }
  pose proof (jordan_standard (PI * Δ) Hpi) as Hj.
  replace (2 / PI * (PI * Δ)) with (2 * Δ) in Hj.
  2: { field. apply Rgt_not_eq; apply PI_RGT_0. }
  apply Rge_le in Hj.
  exact Hj.
Qed.

(* Cnorm (1 − e^{iθ}) ≥ 4Δ，θ = 2πΔ *)
Lemma cnorm_one_minus_z_ge_4delta (n1 n2 : nat) :
  (n1 >= 2)%nat -> (n2 >= 2)%nat -> (n1 < n2)%nat ->
  (4 * (1 / INR n1 - 1 / INR n2) <=
   Cnorm (C1 -c Cexp (0 +i (2 * PI * (1 / INR n1 - 1 / INR n2)))))%R.
Proof.
  intros Hn1 Hn2 Hlt.
  set (Δ := 1 / INR n1 - 1 / INR n2).
  rewrite Cnorm_one_minus_exp_i_theta_eq.
  replace ((2 * PI * Δ) / 2) with (PI * Δ).
  2: { unfold Δ. field. all: split; apply Rgt_not_eq; apply lt_0_INR; lia. }
  assert (Hsin : (2 * Δ <= sin (PI * Δ))%R) by (unfold Δ; apply sin_pi_delta_ge_2delta; [exact Hn1 | exact Hlt]).
  assert (Hsin_pos : (0 <= sin (PI * Δ))%R).
  { apply Rlt_le. apply Rlt_le_trans with (2 * Δ); [ | exact Hsin ].
    apply Rmult_lt_0_compat; [lra | unfold Δ; apply delta_pos; lia]. }
  rewrite (Rabs_pos_eq (sin (PI * Δ)) Hsin_pos).
  lra.
Qed.

(* 几何和 ≤ 1/(2Δ)：‖Σ_{k<n1} e^{ikθ}‖，θ = 2πΔ *)
Lemma geom_cons_2delta (n1 n2 : nat) :
  (n1 >= 2)%nat -> (n2 >= 2)%nat -> (n1 < n2)%nat ->
  (Cnorm (Csum (fun k => Cexp (0 +i (INR k * (2 * PI * (1 / INR n1 - 1 / INR n2))))) n1)
   <= 1 / (2 * (1 / INR n1 - 1 / INR n2)))%R.
Proof.
  intros Hn1 Hn2 Hlt.
  set (Δ := 1 / INR n1 - 1 / INR n2).
  set (θ := 2 * PI * Δ).
  assert (Hz : Cexp (0 +i θ) <> C1).
  { unfold θ, Δ. apply (Cexp_diff_not_one n1 n2 Hn1 Hn2 Hlt). }
  apply Rle_trans with (2 / Cnorm (C1 -c Cexp (0 +i θ))).
  - rewrite (Csum_ext n1 (fun k => Cexp (0 +i (INR k * θ))) (fun k => (Cexp (0 +i θ) ^ k)%C)).
    2: { intros k _. apply Cexp_pow_local. }
    apply (geom_norm_cons (Cexp (0 +i θ)) n1 Hz (Cnorm_Cexp_unit θ)).
  - assert (Hden : (4 * Δ <= Cnorm (C1 -c Cexp (0 +i θ)))%R).
    { unfold θ, Δ. apply cnorm_one_minus_z_ge_4delta; assumption. }
    assert (Hd_pos : 0 < Δ) by (unfold Δ; apply delta_pos; lia).
    assert (Hc_pos : 0 < Cnorm (C1 -c Cexp (0 +i θ))).
    { apply Cnorm_pos_lt. apply (C1_minus_z_neq0 (Cexp (0 +i θ))). exact Hz. }
    assert (H2d_pos : 0 < 2 * Δ) by (apply Rmult_lt_0_compat; [lra | exact Hd_pos]).
    apply (proj2 (Rle_div_div 2 (Cnorm (C1 -c Cexp (0 +i θ))) 1 (2 * Δ) Hc_pos H2d_pos)).
    rewrite Rmult_1_l.
    replace (2 * (2 * Δ)) with (4 * Δ) by ring.
    exact Hden.
Qed.

(* psi 内积的窗口无关保守界（n1 ≤ N 情形）：|⟨ψ_n1,ψ_n2⟩_N| ≤ 1/(2Δ√(n1·n2)) *)
Lemma psi_inner_cons_bound (n1 n2 N : nat) :
  (n1 >= 2)%nat -> (n2 >= 2)%nat -> (n1 < n2)%nat -> (n1 <= N)%nat ->
  Cnorm (Csum (fun k => psi n1 k *c Cconj (psi n2 k)) N)
  <= 1 / (2 * (1 / INR n1 - 1 / INR n2) * sqrt (INR n1 * INR n2)).
Proof.
  intros Hn1 Hn2 Hlt Hle.
  set (Δ := 1 / INR n1 - 1 / INR n2).
  set (θ := 2 * PI * Δ).
  assert (Htr : Csum (fun k => psi n1 k *c Cconj (psi n2 k)) N =
                Csum (fun k => psi n1 k *c Cconj (psi n2 k)) n1).
  { apply Csum_trunc_tail with (N := N) (M := n1).
    - exact Hle.
    - intros k [Hk1 Hk2]. rewrite psi_ge_n_zero by lia. rewrite Cmul_0_l. reflexivity. }
  rewrite Htr.
  assert (Hphase : forall k, (k < n1)%nat ->
      psi n1 k *c Cconj (psi n2 k)
      = Cof_real (/ sqrt (INR n1 * INR n2)) *c Cexp (0 +i (INR k * θ))).
  { intros k Hk. unfold θ, Δ.
    apply (psi_conj_prod_eq_coef_exp n1 n2 k (2 * PI * (1 / INR n1 - 1 / INR n2))).
    - exact Hk.
    - lia.
    - apply lt_0_INR; lia.
    - apply lt_0_INR; lia.
    - unfold Rdiv. ring. }
  rewrite (Csum_ext n1 (fun k => psi n1 k *c Cconj (psi n2 k))
                     (fun k => Cof_real (/ sqrt (INR n1 * INR n2)) *c Cexp (0 +i (INR k * θ)))).
  2: { intros k Hk. apply Hphase. exact Hk. }
  rewrite (Csum_scal_l (Cof_real (/ sqrt (INR n1 * INR n2)))
                       (fun k => Cexp (0 +i (INR k * θ))) n1).
  rewrite Cnorm_mult.
  rewrite (Cnorm_Cof_real_pos (/ sqrt (INR n1 * INR n2))).
  2: { apply Rlt_le. apply Rinv_0_lt_compat. apply sqrt_lt_R0_c. apply Rmult_lt_0_compat; apply lt_0_INR; lia. }
  apply Rle_trans with ((/ sqrt (INR n1 * INR n2)) * (1 / (2 * Δ))).
  - apply Rmult_le_compat_l.
    + apply Rlt_le. apply Rinv_0_lt_compat. apply sqrt_lt_R0_c. apply Rmult_lt_0_compat; apply lt_0_INR; lia.
    + apply geom_cons_2delta; assumption.
  - replace ((/ sqrt (INR n1 * INR n2)) * (1 / (2 * Δ))) with
            (1 / (2 * Δ * sqrt (INR n1 * INR n2))).
    + apply Rle_refl.
    + field. all: split.
      all: try (apply Rgt_not_eq; apply sqrt_lt_R0_c; apply Rmult_lt_0_compat; apply lt_0_INR; lia).
      all: try (apply Rgt_not_eq; unfold Δ; apply delta_pos; lia).
Qed.

(* ============ M4 Tier 1：C=4 子梯 [3,13,53,213] 实例证书 ============ *)

(* Csum 与 independent.Csum 同构桥（若同一常数则 reflexivity；否则归纳） *)
Lemma Csum_eq_independent (f : nat -> Complex) (n : nat) :
  Csum f n = independent.Csum f n.
Proof.
  induction n as [| n IHn].
  - reflexivity.
  - reflexivity.
Qed.

(* 保守界细化：1/(2Δ√(n1n2)) ≤ n1·n2/(2·(n2−n1)·f)，f ≤ √(n1n2) 且 f > 0 *)
Lemma cons_bound_floor (n1 n2 f : nat) :
  (n1 >= 2)%nat -> (n2 >= 2)%nat -> (n1 < n2)%nat ->
  (INR f <= sqrt (INR n1 * INR n2))%R -> (0 < INR f)%R ->
  (1 / (2 * (1 / INR n1 - 1 / INR n2) * sqrt (INR n1 * INR n2))
   <= INR n1 * INR n2 / (2 * INR (n2 - n1) * INR f))%R.
Proof.
  intros Hn1 Hn2 Hlt Hf Hfpos.
  replace (1 / (2 * (1 / INR n1 - 1 / INR n2) * sqrt (INR n1 * INR n2)))
     with (INR n1 * INR n2 / (2 * INR (n2 - n1) * sqrt (INR n1 * INR n2))).
  2: { rewrite (minus_INR n2 n1) by lia.
       field.
       all: repeat split.
       all: try (apply Rgt_not_eq; apply sqrt_lt_R0_c; apply Rmult_lt_0_compat; apply lt_0_INR; lia).
       all: try (apply Rgt_not_eq; apply lt_0_INR; lia).
       all: try (apply Rgt_not_eq; apply (proj2 (Rlt_0_minus (INR n1) (INR n2))); apply lt_INR; lia). }
  apply Rmult_le_compat_l.
  - apply Rmult_le_pos; apply pos_INR.
  - apply Rinv_le_contravar.
    + apply Rmult_lt_0_compat.
      * apply Rmult_lt_0_compat; [lra | apply lt_0_INR; lia].
      * exact Hfpos.
    + apply Rmult_le_compat_l.
      * apply Rlt_le. apply Rmult_lt_0_compat; [lra | apply lt_0_INR; lia].
      * exact Hf.
Qed.

(* 6 ≤ √39 等 floor-sqrt 事实（f² ≤ m ⟹ f ≤ √m） *)
Lemma INR_sqrt_le (f m : nat) : (f * f <= m)%nat ->
  (INR f <= sqrt (INR m))%R.
Proof.
  intros H.
  apply Rle_trans with (sqrt (INR (f * f))).
  - assert (Hsq : INR (f * f) = (INR f) ^ 2).
    { rewrite mult_INR. ring. }
    rewrite Hsq.
    rewrite <- (Rsqr_pow2 (INR f)).
    unfold Rsqr.
    rewrite sqrt_square; [apply Rle_refl | apply pos_INR].
  - apply sqrt_le_1; [apply pos_INR | apply pos_INR | apply le_INR; exact H].
Qed.

(* 具体对界：|⟨ψ_3,ψ_13⟩_N| ≤ 13/40（N ≥ 3） *)
Lemma pair_3_13 (N : nat) : (3 <= N)%nat ->
  Cnorm (Csum (fun k => psi 3 k *c Cconj (psi 13 k)) N) <= 13 / 40.
Proof.
  intros HN.
  apply Rle_trans with (1 / (2 * (1 / INR 3 - 1 / INR 13) * sqrt (INR 3 * INR 13))).
  - apply psi_inner_cons_bound; lia.
  - apply Rle_trans with (INR 3 * INR 13 / (2 * INR (13 - 3) * INR 6)).
    + apply cons_bound_floor.
      * lia.
      * lia.
      * lia.
      * rewrite <- (mult_INR 3 13). apply INR_sqrt_le. lia.
      * apply lt_0_INR. lia.
    + replace (INR 3 * INR 13 / (2 * INR (13 - 3) * INR 6)) with (13 / 40) by (compute; field).
      apply Rle_refl.
Qed.

(* 具体对界：|⟨ψ_3,ψ_53⟩_N| ≤ 53/400 *)
Lemma pair_3_53 (N : nat) : (3 <= N)%nat ->
  Cnorm (Csum (fun k => psi 3 k *c Cconj (psi 53 k)) N) <= 53 / 400.
Proof.
  intros HN.
  apply Rle_trans with (1 / (2 * (1 / INR 3 - 1 / INR 53) * sqrt (INR 3 * INR 53))).
  - apply psi_inner_cons_bound; lia.
  - apply Rle_trans with (INR 3 * INR 53 / (2 * INR (53 - 3) * INR 12)).
    + apply cons_bound_floor.
      * lia.
      * lia.
      * lia.
      * rewrite <- (mult_INR 3 53). apply INR_sqrt_le. lia.
      * apply lt_0_INR. lia.
    + replace (INR 3 * INR 53 / (2 * INR (53 - 3) * INR 12)) with (53 / 400) by (compute; field).
      apply Rle_refl.
Qed.

(* 具体对界：|⟨ψ_3,ψ_213⟩_N| ≤ 213/3500 *)
Lemma pair_3_213 (N : nat) : (3 <= N)%nat ->
  Cnorm (Csum (fun k => psi 3 k *c Cconj (psi 213 k)) N) <= 213 / 3500.
Proof.
  intros HN.
  apply Rle_trans with (1 / (2 * (1 / INR 3 - 1 / INR 213) * sqrt (INR 3 * INR 213))).
  - apply psi_inner_cons_bound; lia.
  - apply Rle_trans with (INR 3 * INR 213 / (2 * INR (213 - 3) * INR 25)).
    + apply cons_bound_floor.
      * lia.
      * lia.
      * lia.
      * rewrite <- (mult_INR 3 213). apply INR_sqrt_le. lia.
      * apply lt_0_INR. lia.
    + replace (INR 3 * INR 213 / (2 * INR (213 - 3) * INR 25)) with (213 / 3500) by (compute; field).
      apply Rle_refl.
Qed.

(* 具体对界：|⟨ψ_13,ψ_53⟩_N| ≤ 689/2080 *)
Lemma pair_13_53 (N : nat) : (13 <= N)%nat ->
  Cnorm (Csum (fun k => psi 13 k *c Cconj (psi 53 k)) N) <= 689 / 2080.
Proof.
  intros HN.
  apply Rle_trans with (1 / (2 * (1 / INR 13 - 1 / INR 53) * sqrt (INR 13 * INR 53))).
  - apply psi_inner_cons_bound; lia.
  - apply Rle_trans with (INR 13 * INR 53 / (2 * INR (53 - 13) * INR 26)).
    + apply cons_bound_floor.
      * lia.
      * lia.
      * lia.
      * rewrite <- (mult_INR 13 53). apply INR_sqrt_le. lia.
      * apply lt_0_INR. lia.
    + replace (INR 13 * INR 53 / (2 * INR (53 - 13) * INR 26)) with (689 / 2080) by (compute; field).
      apply Rle_refl.
Qed.

(* 具体对界：|⟨ψ_13,ψ_213⟩_N| ≤ 2769/20800 *)
Lemma pair_13_213 (N : nat) : (13 <= N)%nat ->
  Cnorm (Csum (fun k => psi 13 k *c Cconj (psi 213 k)) N) <= 2769 / 20800.
Proof.
  intros HN.
  apply Rle_trans with (1 / (2 * (1 / INR 13 - 1 / INR 213) * sqrt (INR 13 * INR 213))).
  - apply psi_inner_cons_bound; lia.
  - apply Rle_trans with (INR 13 * INR 213 / (2 * INR (213 - 13) * INR 52)).
    + apply cons_bound_floor.
      * lia.
      * lia.
      * lia.
      * rewrite <- (mult_INR 13 213). apply INR_sqrt_le. lia.
      * apply lt_0_INR. lia.
    + replace (INR 13 * INR 213 / (2 * INR (213 - 13) * INR 52)) with (2769 / 20800) by (compute; field).
      apply Rle_refl.
Qed.

(* 具体对界：|⟨ψ_53,ψ_213⟩_N| ≤ 11289/33920 *)
Lemma pair_53_213 (N : nat) : (53 <= N)%nat ->
  Cnorm (Csum (fun k => psi 53 k *c Cconj (psi 213 k)) N) <= 11289 / 33920.
Proof.
  intros HN.
  apply Rle_trans with (1 / (2 * (1 / INR 53 - 1 / INR 213) * sqrt (INR 53 * INR 213))).
  - apply psi_inner_cons_bound; lia.
  - apply Rle_trans with (INR 53 * INR 213 / (2 * INR (213 - 53) * INR 106)).
    + apply cons_bound_floor.
      * lia.
      * lia.
      * lia.
      * rewrite <- (mult_INR 53 213). apply INR_sqrt_le. lia.
      * apply lt_0_INR. lia.
    + replace (INR 53 * INR 213 / (2 * INR (213 - 53) * INR 106)) with (11289 / 33920) by (compute; field).
      apply Rle_refl.
Qed.



(* C=4 子梯（cons 形式避免 [;] 记号解析问题） *)
Definition c4l : list nat := (3%nat :: 13%nat :: 53%nat :: 213%nat :: nil).

(* ============ M4 Tier 1 收尾：C=4 实例证书 ============ *)

(* psi 基在窗口 N ≥ n 上单位范数：l2_norm_sq (psi n) N = 1 *)
Lemma psi_unit_norm (n N : nat) : (n >= 2)%nat -> (n <= N)%nat ->
  l2_norm_sq (fun k => psi n k) N = 1.
Proof.
  intros Hn2 HnN.
  unfold l2_norm_sq.
  rewrite (sum_f_R0_ext (fun k => Cnorm_sq (psi n k))
                        (fun k => if Nat.ltb k n then 1 / INR n else 0%R) N).
  2: { intros k _. apply Cnorm_sq_psi_exact. }
  assert (Hle : (n - 1 <= N)%nat) by lia.
  pose proof (sum_f_R0_split (fun k => if Nat.ltb k n then 1 / INR n else 0%R) N (n - 1) Hle) as Hsp.
  assert (Hne : Nat.eqb (N - (n - 1)) 0 = false).
  { apply Nat.eqb_neq. lia. }
  rewrite Hne in Hsp.
  rewrite Hsp.
  assert (Hhead : (sum_f_R0 (fun k => if Nat.ltb k n then 1 / INR n else 0%R) (n - 1) = 1)%R).
  { rewrite (sum_f_R0_ext (fun k => if Nat.ltb k n then 1 / INR n else 0%R) (fun _ => 1 / INR n) (n - 1)).
    2: { intros k Hk. destruct (Nat.ltb_spec k n) as [Hlt | Hge]; [reflexivity | exfalso; lia]. }
    rewrite sum_f_R0_const.
    assert (Hsn : S (n - 1) = n) by lia.
    rewrite Hsn. field. apply Rgt_not_eq; apply lt_0_INR; lia. }
  rewrite Hhead.
  assert (Htail : (sum_f_R0 (fun k => if Nat.ltb (n - 1 + k + 1) n then 1 / INR n else 0%R) (N - (n - 1) - 1) = 0)%R).
  { rewrite (sum_f_R0_ext (fun k => if Nat.ltb (n - 1 + k + 1) n then 1 / INR n else 0%R) (fun _ => 0%R) (N - (n - 1) - 1)).
    2: { intros k _. destruct (Nat.ltb_spec (n - 1 + k + 1) n) as [Hlt | Hge]; [exfalso; lia | reflexivity]. }
    apply sum_f_R0_zero. }
  rewrite Htail. ring.
Qed.

(* 行和 ≤ 4/5（max 行 13/53 ≈ 0.789；nra 直接解有理数不等式） *)
Lemma c4_row0 : sum_f_R0 (fun j => if eq_nat_dec 0 j then 0%R else
      Cnorm (Csum (fun k => psi (nth 0 c4l 0%nat) k *c Cconj (psi (nth j c4l 0%nat) k)) 213)) 3
  <= 4 / 5.
Proof.
  apply Rle_trans with (sum_f_R0 (fun j => match j with 0%nat => 0%R | 1%nat => 13 / 40 | 2%nat => 53 / 400 | _ => 213 / 3500 end) 3).
  - apply sum_f_R0_le_compat. intros j Hj.
    destruct (eq_nat_dec 0 j) as [H0 | H0n].
    + subst j. simpl. nra.
    + destruct j as [|[|[|[|j']]]]; try lia.
      * replace (nth 0 c4l 0%nat) with 3%nat by reflexivity.
        replace (nth 1 c4l 0%nat) with 13%nat by reflexivity.
        apply pair_3_13; lia.
      * replace (nth 0 c4l 0%nat) with 3%nat by reflexivity.
        replace (nth 2 c4l 0%nat) with 53%nat by reflexivity.
        apply pair_3_53; lia.
      * replace (nth 0 c4l 0%nat) with 3%nat by reflexivity.
        replace (nth 3 c4l 0%nat) with 213%nat by reflexivity.
        apply pair_3_213; lia.
  - simpl. nra.
Qed.

Lemma c4_row1 : sum_f_R0 (fun j => if eq_nat_dec 1 j then 0%R else
      Cnorm (Csum (fun k => psi (nth 1 c4l 0%nat) k *c Cconj (psi (nth j c4l 0%nat) k)) 213)) 3
  <= 4 / 5.
Proof.
  apply Rle_trans with (sum_f_R0 (fun j => match j with 0%nat => 13 / 40 | 1%nat => 0%R | 2%nat => 689 / 2080 | _ => 2769 / 20800 end) 3).
  - apply sum_f_R0_le_compat. intros j Hj.
    destruct (eq_nat_dec 1 j) as [H1 | H1n].
    + subst j. simpl. nra.
    + destruct j as [|[|[|[|j']]]]; try lia.
      * replace (nth 1 c4l 0%nat) with 13%nat by reflexivity.
        replace (nth 0 c4l 0%nat) with 3%nat by reflexivity.
        rewrite (ExtendedTheorems.Cnorm_Csum_conj_sym (fun k => psi 13 k) (fun k => psi 3 k) 213).
        apply pair_3_13; lia.
      * replace (nth 1 c4l 0%nat) with 13%nat by reflexivity.
        replace (nth 2 c4l 0%nat) with 53%nat by reflexivity.
        apply pair_13_53; lia.
      * replace (nth 1 c4l 0%nat) with 13%nat by reflexivity.
        replace (nth 3 c4l 0%nat) with 213%nat by reflexivity.
        apply pair_13_213; lia.
  - simpl. nra.
Qed.

Lemma c4_row2 : sum_f_R0 (fun j => if eq_nat_dec 2 j then 0%R else
      Cnorm (Csum (fun k => psi (nth 2 c4l 0%nat) k *c Cconj (psi (nth j c4l 0%nat) k)) 213)) 3
  <= 4 / 5.
Proof.
  apply Rle_trans with (sum_f_R0 (fun j => match j with 0%nat => 53 / 400 | 1%nat => 689 / 2080 | 2%nat => 0%R | _ => 11289 / 33920 end) 3).
  - apply sum_f_R0_le_compat. intros j Hj.
    destruct (eq_nat_dec 2 j) as [H2 | H2n].
    + subst j. simpl. nra.
    + destruct j as [|[|[|[|j']]]]; try lia.
      * replace (nth 2 c4l 0%nat) with 53%nat by reflexivity.
        replace (nth 0 c4l 0%nat) with 3%nat by reflexivity.
        rewrite (ExtendedTheorems.Cnorm_Csum_conj_sym (fun k => psi 53 k) (fun k => psi 3 k) 213).
        apply pair_3_53; lia.
      * replace (nth 2 c4l 0%nat) with 53%nat by reflexivity.
        replace (nth 1 c4l 0%nat) with 13%nat by reflexivity.
        rewrite (ExtendedTheorems.Cnorm_Csum_conj_sym (fun k => psi 53 k) (fun k => psi 13 k) 213).
        apply pair_13_53; lia.
      * replace (nth 2 c4l 0%nat) with 53%nat by reflexivity.
        replace (nth 3 c4l 0%nat) with 213%nat by reflexivity.
        apply pair_53_213; lia.
  - simpl. nra.
Qed.

Lemma c4_row3 : sum_f_R0 (fun j => if eq_nat_dec 3 j then 0%R else
      Cnorm (Csum (fun k => psi (nth 3 c4l 0%nat) k *c Cconj (psi (nth j c4l 0%nat) k)) 213)) 3
  <= 4 / 5.
Proof.
  apply Rle_trans with (sum_f_R0 (fun j => match j with 0%nat => 213 / 3500 | 1%nat => 2769 / 20800 | 2%nat => 11289 / 33920 | _ => 0%R end) 3).
  - apply sum_f_R0_le_compat. intros j Hj.
    destruct (eq_nat_dec 3 j) as [H3 | H3n].
    + subst j. simpl. nra.
    + destruct j as [|[|[|[|j']]]]; try lia.
      * replace (nth 3 c4l 0%nat) with 213%nat by reflexivity.
        replace (nth 0 c4l 0%nat) with 3%nat by reflexivity.
        rewrite (ExtendedTheorems.Cnorm_Csum_conj_sym (fun k => psi 213 k) (fun k => psi 3 k) 213).
        apply pair_3_213; lia.
      * replace (nth 3 c4l 0%nat) with 213%nat by reflexivity.
        replace (nth 1 c4l 0%nat) with 13%nat by reflexivity.
        rewrite (ExtendedTheorems.Cnorm_Csum_conj_sym (fun k => psi 213 k) (fun k => psi 13 k) 213).
        apply pair_13_213; lia.
      * replace (nth 3 c4l 0%nat) with 213%nat by reflexivity.
        replace (nth 2 c4l 0%nat) with 53%nat by reflexivity.
        rewrite (ExtendedTheorems.Cnorm_Csum_conj_sym (fun k => psi 213 k) (fun k => psi 53 k) 213).
        apply pair_53_213; lia.
  - simpl. nra.
Qed.
(* C=4 实例证书：μ = 4/5 ⟹ (1/5)·S ≤ ‖F‖² ≤ (9/5)·S（[3,13,53,213]，窗口 213；对一切 N ≥ 213 有效） *)
Theorem certified_c4_frame_bounds (coeffs : list Complex) :
  length coeffs = 4%nat ->
  let n := 4%nat in
  let M := 214%nat in
  let phi := fun i k => psi (nth i c4l 0%nat) k in
  let F := fun k => Csum (fun i => nth i coeffs C0 *c phi i k) n in
  let S := sum_f_R0 (fun i => Cnorm_sq (nth i coeffs C0)) (Nat.pred n) in
  ((1 - 4 / 5) * S <= l2_norm_sq F (Nat.pred M) <= (1 + 4 / 5) * S)%R.
Proof.
  intros Hlen.
  cbv zeta.
  apply (gershgorin_frame_mu 4 (fun i k => psi (nth i c4l 0%nat) k) 214 (4 / 5)).
  - lia.
  - intros i k Hi Hk.
    destruct i as [|[|[|[|i']]]].
    + simpl. apply psi_ge_n_zero. lia.
    + simpl. apply psi_ge_n_zero. lia.
    + simpl. apply psi_ge_n_zero. lia.
    + simpl. apply psi_ge_n_zero. lia.
    + exfalso. lia.
  - intros i Hi.
    destruct i as [|[|[|[|i']]]].
    + replace (nth 0 c4l 0%nat) with 3%nat by reflexivity. apply psi_unit_norm; lia.
    + replace (nth 1 c4l 0%nat) with 13%nat by reflexivity. apply psi_unit_norm; lia.
    + replace (nth 2 c4l 0%nat) with 53%nat by reflexivity. apply psi_unit_norm; lia.
    + replace (nth 3 c4l 0%nat) with 213%nat by reflexivity. apply psi_unit_norm; lia.
    + exfalso. lia.
  - intros i Hi.
    destruct i as [|[|[|[|i']]]]; try lia.
    + apply c4_row0.
    + apply c4_row1.
    + apply c4_row2.
    + apply c4_row3.
  - exact Hlen.
Qed.

End InstanceCertificate.


(* ============================================================
   M4 收尾①：长度一致性引理（会话 9 并入，探针 PSA_M4b_probe.v 验证 RC=0）
   certified_c4_frame_bounds 固定窗口 213 升级为 ∀N ≥ 214（窗口 N−1 ≥ 213）
   —— O(1) 实例证书覆盖无界序列长度 T 的显式定理，零 classic
   ============================================================ *)

Module M4bLengthConsistency.

Import UnconditionalBasisLemmas.
Import ExtendedTheorems.
Import Gershgorin.
Import InstanceCertificate.
Open Scope R_scope.

(* ============ 窗口参数化行和（∀N ≥ 213，镜像 c4_row* 证明骨架） ============ *)

Lemma c4_row0_gen (N : nat) : (213 <= N)%nat ->
  sum_f_R0 (fun j => if eq_nat_dec 0 j then 0%R else
      Cnorm (Csum (fun k => psi (nth 0 c4l 0%nat) k *c Cconj (psi (nth j c4l 0%nat) k)) N)) 3
  <= 4 / 5.
Proof.
  intros HN.
  apply Rle_trans with (sum_f_R0 (fun j => match j with 0%nat => 0%R | 1%nat => 13 / 40 | 2%nat => 53 / 400 | _ => 213 / 3500 end) 3).
  - apply sum_f_R0_le_compat. intros j Hj.
    destruct (eq_nat_dec 0 j) as [H0 | H0n].
    + subst j. simpl. nra.
    + destruct j as [|[|[|[|j']]]]; try lia.
      * replace (nth 0 c4l 0%nat) with 3%nat by reflexivity.
        replace (nth 1 c4l 0%nat) with 13%nat by reflexivity.
        apply pair_3_13; lia.
      * replace (nth 0 c4l 0%nat) with 3%nat by reflexivity.
        replace (nth 2 c4l 0%nat) with 53%nat by reflexivity.
        apply pair_3_53; lia.
      * replace (nth 0 c4l 0%nat) with 3%nat by reflexivity.
        replace (nth 3 c4l 0%nat) with 213%nat by reflexivity.
        apply pair_3_213; lia.
  - simpl. nra.
Qed.

Lemma c4_row1_gen (N : nat) : (213 <= N)%nat ->
  sum_f_R0 (fun j => if eq_nat_dec 1 j then 0%R else
      Cnorm (Csum (fun k => psi (nth 1 c4l 0%nat) k *c Cconj (psi (nth j c4l 0%nat) k)) N)) 3
  <= 4 / 5.
Proof.
  intros HN.
  apply Rle_trans with (sum_f_R0 (fun j => match j with 0%nat => 13 / 40 | 1%nat => 0%R | 2%nat => 689 / 2080 | _ => 2769 / 20800 end) 3).
  - apply sum_f_R0_le_compat. intros j Hj.
    destruct (eq_nat_dec 1 j) as [H1 | H1n].
    + subst j. simpl. nra.
    + destruct j as [|[|[|[|j']]]]; try lia.
      * replace (nth 1 c4l 0%nat) with 13%nat by reflexivity.
        replace (nth 0 c4l 0%nat) with 3%nat by reflexivity.
        rewrite (ExtendedTheorems.Cnorm_Csum_conj_sym (fun k => psi 13 k) (fun k => psi 3 k) N).
        apply pair_3_13; lia.
      * replace (nth 1 c4l 0%nat) with 13%nat by reflexivity.
        replace (nth 2 c4l 0%nat) with 53%nat by reflexivity.
        apply pair_13_53; lia.
      * replace (nth 1 c4l 0%nat) with 13%nat by reflexivity.
        replace (nth 3 c4l 0%nat) with 213%nat by reflexivity.
        apply pair_13_213; lia.
  - simpl. nra.
Qed.

Lemma c4_row2_gen (N : nat) : (213 <= N)%nat ->
  sum_f_R0 (fun j => if eq_nat_dec 2 j then 0%R else
      Cnorm (Csum (fun k => psi (nth 2 c4l 0%nat) k *c Cconj (psi (nth j c4l 0%nat) k)) N)) 3
  <= 4 / 5.
Proof.
  intros HN.
  apply Rle_trans with (sum_f_R0 (fun j => match j with 0%nat => 53 / 400 | 1%nat => 689 / 2080 | 2%nat => 0%R | _ => 11289 / 33920 end) 3).
  - apply sum_f_R0_le_compat. intros j Hj.
    destruct (eq_nat_dec 2 j) as [H2 | H2n].
    + subst j. simpl. nra.
    + destruct j as [|[|[|[|j']]]]; try lia.
      * replace (nth 2 c4l 0%nat) with 53%nat by reflexivity.
        replace (nth 0 c4l 0%nat) with 3%nat by reflexivity.
        rewrite (ExtendedTheorems.Cnorm_Csum_conj_sym (fun k => psi 53 k) (fun k => psi 3 k) N).
        apply pair_3_53; lia.
      * replace (nth 2 c4l 0%nat) with 53%nat by reflexivity.
        replace (nth 1 c4l 0%nat) with 13%nat by reflexivity.
        rewrite (ExtendedTheorems.Cnorm_Csum_conj_sym (fun k => psi 53 k) (fun k => psi 13 k) N).
        apply pair_13_53; lia.
      * replace (nth 2 c4l 0%nat) with 53%nat by reflexivity.
        replace (nth 3 c4l 0%nat) with 213%nat by reflexivity.
        apply pair_53_213; lia.
  - simpl. nra.
Qed.

Lemma c4_row3_gen (N : nat) : (213 <= N)%nat ->
  sum_f_R0 (fun j => if eq_nat_dec 3 j then 0%R else
      Cnorm (Csum (fun k => psi (nth 3 c4l 0%nat) k *c Cconj (psi (nth j c4l 0%nat) k)) N)) 3
  <= 4 / 5.
Proof.
  intros HN.
  apply Rle_trans with (sum_f_R0 (fun j => match j with 0%nat => 213 / 3500 | 1%nat => 2769 / 20800 | 2%nat => 11289 / 33920 | _ => 0%R end) 3).
  - apply sum_f_R0_le_compat. intros j Hj.
    destruct (eq_nat_dec 3 j) as [H3 | H3n].
    + subst j. simpl. nra.
    + destruct j as [|[|[|[|j']]]]; try lia.
      * replace (nth 3 c4l 0%nat) with 213%nat by reflexivity.
        replace (nth 0 c4l 0%nat) with 3%nat by reflexivity.
        rewrite (ExtendedTheorems.Cnorm_Csum_conj_sym (fun k => psi 213 k) (fun k => psi 3 k) N).
        apply pair_3_213; lia.
      * replace (nth 3 c4l 0%nat) with 213%nat by reflexivity.
        replace (nth 1 c4l 0%nat) with 13%nat by reflexivity.
        rewrite (ExtendedTheorems.Cnorm_Csum_conj_sym (fun k => psi 213 k) (fun k => psi 13 k) N).
        apply pair_13_213; lia.
      * replace (nth 3 c4l 0%nat) with 213%nat by reflexivity.
        replace (nth 2 c4l 0%nat) with 53%nat by reflexivity.
        rewrite (ExtendedTheorems.Cnorm_Csum_conj_sym (fun k => psi 213 k) (fun k => psi 53 k) N).
        apply pair_53_213; lia.
  - simpl. nra.
Qed.

(* ============ 长度一致性证书：∀N ≥ 214（窗口 N−1 ≥ 213），μ = 4/5 ============ *)
(* 意义：O(1) 实例证书对一切序列长度 N−1 ≥ 213（即 N ≥ 214）成立，
   覆盖无界 T 的"长度一致性"显式定理（交接文档 M4 收尾①）。 *)
Theorem certified_c4_frame_bounds_anyN (N : nat) (coeffs : list Complex) :
  (214 <= N)%nat ->
  length coeffs = 4%nat ->
  let phi := fun i k => psi (nth i c4l 0%nat) k in
  let F := fun k => Csum (fun i => nth i coeffs C0 *c phi i k) 4 in
  let S := sum_f_R0 (fun i => Cnorm_sq (nth i coeffs C0)) (Nat.pred 4) in
  ((1 - 4 / 5) * S <= l2_norm_sq F (Nat.pred N) <= (1 + 4 / 5) * S)%R.
Proof.
  intros HN Hlen.
  cbv zeta.
  (* 归一化：Nat.pred 4 折为 3，使 S 与 gershgorin 结论精确一致 *)
  change ((1 - 4 / 5) * sum_f_R0 (fun i => Cnorm_sq (nth i coeffs C0)) 3 <=
          l2_norm_sq (fun k => Csum (fun i => nth i coeffs C0 *c psi (nth i c4l 0%nat) k) 4) (Nat.pred N) <=
          (1 + 4 / 5) * sum_f_R0 (fun i => Cnorm_sq (nth i coeffs C0)) 3).
  apply (gershgorin_frame_mu 4 (fun i k => psi (nth i c4l 0%nat) k) N (4 / 5)).
  - lia.
  - intros i k Hi Hk.
    destruct i as [|[|[|[|i']]]].
    + simpl. apply psi_ge_n_zero. lia.
    + simpl. apply psi_ge_n_zero. lia.
    + simpl. apply psi_ge_n_zero. lia.
    + simpl. apply psi_ge_n_zero. lia.
    + exfalso. lia.
  - intros i Hi.
    destruct i as [|[|[|[|i']]]].
    + replace (nth 0 c4l 0%nat) with 3%nat by reflexivity. apply psi_unit_norm; lia.
    + replace (nth 1 c4l 0%nat) with 13%nat by reflexivity. apply psi_unit_norm; lia.
    + replace (nth 2 c4l 0%nat) with 53%nat by reflexivity. apply psi_unit_norm; lia.
    + replace (nth 3 c4l 0%nat) with 213%nat by reflexivity. apply psi_unit_norm; lia.
    + exfalso. lia.
  - intros i Hi.
    destruct i as [|[|[|[|i']]]]; try lia.
    + apply c4_row0_gen. lia.
    + apply c4_row1_gen. lia.
    + apply c4_row2_gen. lia.
    + apply c4_row3_gen. lia.
  - exact Hlen.
Qed.

End M4bLengthConsistency.

(* ============================================================
   M4 T8 复合证书（会话 9 并入，探针 PSA_T8_probe.v 验证 RC=0）
   核：[3,15,63,255]（E5'' 最优阶梯的隔带子核，packing 最优但整梯不可认证）
   μ=4/5 实例证书 (1/5)·S ≤ ‖F‖² ≤ (9/5)·S，窗口 255——零 classic
   ============================================================ *)
Module T8CoreCertificate.

Import UnconditionalBasisLemmas.
Import ExtendedTheorems.
Import Gershgorin.
Import InstanceCertificate.
Open Scope R_scope.

(* ============ 六对界（floor-sqrt 有理化） ============ *)

(* |⟨ψ_3,ψ_15⟩_N| ≤ 5/16（N ≥ 3） *)
Lemma pair_3_15 (N : nat) : (3 <= N)%nat ->
  Cnorm (Csum (fun k => psi 3 k *c Cconj (psi 15 k)) N) <= 5 / 16.
Proof.
  intros HN.
  apply Rle_trans with (1 / (2 * (1 / INR 3 - 1 / INR 15) * sqrt (INR 3 * INR 15))).
  - apply psi_inner_cons_bound; lia.
  - apply Rle_trans with (INR 3 * INR 15 / (2 * INR (15 - 3) * INR 6)).
    + apply cons_bound_floor.
      * lia.
      * lia.
      * lia.
      * rewrite <- (mult_INR 3 15). apply INR_sqrt_le. lia.
      * apply lt_0_INR. lia.
    + replace (INR 3 * INR 15 / (2 * INR (15 - 3) * INR 6)) with (5 / 16) by (compute; field).
      apply Rle_refl.
Qed.

(* |⟨ψ_3,ψ_63⟩_N| ≤ 63/520（N ≥ 3） *)
Lemma pair_3_63 (N : nat) : (3 <= N)%nat ->
  Cnorm (Csum (fun k => psi 3 k *c Cconj (psi 63 k)) N) <= 63 / 520.
Proof.
  intros HN.
  apply Rle_trans with (1 / (2 * (1 / INR 3 - 1 / INR 63) * sqrt (INR 3 * INR 63))).
  - apply psi_inner_cons_bound; lia.
  - apply Rle_trans with (INR 3 * INR 63 / (2 * INR (63 - 3) * INR 13)).
    + apply cons_bound_floor.
      * lia.
      * lia.
      * lia.
      * rewrite <- (mult_INR 3 63). apply INR_sqrt_le. lia.
      * apply lt_0_INR. lia.
    + replace (INR 3 * INR 63 / (2 * INR (63 - 3) * INR 13)) with (63 / 520) by (compute; field).
      apply Rle_refl.
Qed.

(* |⟨ψ_3,ψ_255⟩_N| ≤ 85/1512（N ≥ 3） *)
Lemma pair_3_255 (N : nat) : (3 <= N)%nat ->
  Cnorm (Csum (fun k => psi 3 k *c Cconj (psi 255 k)) N) <= 85 / 1512.
Proof.
  intros HN.
  apply Rle_trans with (1 / (2 * (1 / INR 3 - 1 / INR 255) * sqrt (INR 3 * INR 255))).
  - apply psi_inner_cons_bound; lia.
  - apply Rle_trans with (INR 3 * INR 255 / (2 * INR (255 - 3) * INR 27)).
    + apply cons_bound_floor.
      * lia.
      * lia.
      * lia.
      * rewrite <- (mult_INR 3 255). apply INR_sqrt_le. lia.
      * apply lt_0_INR. lia.
    + replace (INR 3 * INR 255 / (2 * INR (255 - 3) * INR 27)) with (85 / 1512) by (compute; field).
      apply Rle_refl.
Qed.

(* |⟨ψ_15,ψ_63⟩_N| ≤ 21/64（N ≥ 15） *)
Lemma pair_15_63 (N : nat) : (15 <= N)%nat ->
  Cnorm (Csum (fun k => psi 15 k *c Cconj (psi 63 k)) N) <= 21 / 64.
Proof.
  intros HN.
  apply Rle_trans with (1 / (2 * (1 / INR 15 - 1 / INR 63) * sqrt (INR 15 * INR 63))).
  - apply psi_inner_cons_bound; lia.
  - apply Rle_trans with (INR 15 * INR 63 / (2 * INR (63 - 15) * INR 30)).
    + apply cons_bound_floor.
      * lia.
      * lia.
      * lia.
      * rewrite <- (mult_INR 15 63). apply INR_sqrt_le. lia.
      * apply lt_0_INR. lia.
    + replace (INR 15 * INR 63 / (2 * INR (63 - 15) * INR 30)) with (21 / 64) by (compute; field).
      apply Rle_refl.
Qed.

(* |⟨ψ_15,ψ_255⟩_N| ≤ 255/1952（N ≥ 15） *)
Lemma pair_15_255 (N : nat) : (15 <= N)%nat ->
  Cnorm (Csum (fun k => psi 15 k *c Cconj (psi 255 k)) N) <= 255 / 1952.
Proof.
  intros HN.
  apply Rle_trans with (1 / (2 * (1 / INR 15 - 1 / INR 255) * sqrt (INR 15 * INR 255))).
  - apply psi_inner_cons_bound; lia.
  - apply Rle_trans with (INR 15 * INR 255 / (2 * INR (255 - 15) * INR 61)).
    + apply cons_bound_floor.
      * lia.
      * lia.
      * lia.
      * rewrite <- (mult_INR 15 255). apply INR_sqrt_le. lia.
      * apply lt_0_INR. lia.
    + replace (INR 15 * INR 255 / (2 * INR (255 - 15) * INR 61)) with (255 / 1952) by (compute; field).
      apply Rle_refl.
Qed.

(* |⟨ψ_63,ψ_255⟩_N| ≤ 85/256（N ≥ 63） *)
Lemma pair_63_255 (N : nat) : (63 <= N)%nat ->
  Cnorm (Csum (fun k => psi 63 k *c Cconj (psi 255 k)) N) <= 85 / 256.
Proof.
  intros HN.
  apply Rle_trans with (1 / (2 * (1 / INR 63 - 1 / INR 255) * sqrt (INR 63 * INR 255))).
  - apply psi_inner_cons_bound; lia.
  - apply Rle_trans with (INR 63 * INR 255 / (2 * INR (255 - 63) * INR 126)).
    + apply cons_bound_floor.
      * lia.
      * lia.
      * lia.
      * rewrite <- (mult_INR 63 255). apply INR_sqrt_le. lia.
      * apply lt_0_INR. lia.
    + replace (INR 63 * INR 255 / (2 * INR (255 - 63) * INR 126)) with (85 / 256) by (compute; field).
      apply Rle_refl.
Qed.

(* ============ T8 核（隔带子核）阶梯定义 ============ *)

(* T8 核阶梯（cons 形式）：[3,15,63,255] *)
Definition t8l : list nat := (3%nat :: 15%nat :: 63%nat :: 255%nat :: nil).

(* ============ 行和 ≤ 4/5（窗口 255，镜像 c4_row*） ============ *)

Lemma t8_row0 : sum_f_R0 (fun j => if eq_nat_dec 0 j then 0%R else
      Cnorm (Csum (fun k => psi (nth 0 t8l 0%nat) k *c Cconj (psi (nth j t8l 0%nat) k)) 255)) 3
  <= 4 / 5.
Proof.
  apply Rle_trans with (sum_f_R0 (fun j => match j with 0%nat => 0%R | 1%nat => 5 / 16 | 2%nat => 63 / 520 | _ => 85 / 1512 end) 3).
  - apply sum_f_R0_le_compat. intros j Hj.
    destruct (eq_nat_dec 0 j) as [H0 | H0n].
    + subst j. simpl. nra.
    + destruct j as [|[|[|[|j']]]]; try lia.
      * replace (nth 0 t8l 0%nat) with 3%nat by reflexivity.
        replace (nth 1 t8l 0%nat) with 15%nat by reflexivity.
        apply pair_3_15; lia.
      * replace (nth 0 t8l 0%nat) with 3%nat by reflexivity.
        replace (nth 2 t8l 0%nat) with 63%nat by reflexivity.
        apply pair_3_63; lia.
      * replace (nth 0 t8l 0%nat) with 3%nat by reflexivity.
        replace (nth 3 t8l 0%nat) with 255%nat by reflexivity.
        apply pair_3_255; lia.
  - simpl. nra.
Qed.

Lemma t8_row1 : sum_f_R0 (fun j => if eq_nat_dec 1 j then 0%R else
      Cnorm (Csum (fun k => psi (nth 1 t8l 0%nat) k *c Cconj (psi (nth j t8l 0%nat) k)) 255)) 3
  <= 4 / 5.
Proof.
  apply Rle_trans with (sum_f_R0 (fun j => match j with 0%nat => 5 / 16 | 1%nat => 0%R | 2%nat => 21 / 64 | _ => 255 / 1952 end) 3).
  - apply sum_f_R0_le_compat. intros j Hj.
    destruct (eq_nat_dec 1 j) as [H1 | H1n].
    + subst j. simpl. nra.
    + destruct j as [|[|[|[|j']]]]; try lia.
      * replace (nth 1 t8l 0%nat) with 15%nat by reflexivity.
        replace (nth 0 t8l 0%nat) with 3%nat by reflexivity.
        rewrite (ExtendedTheorems.Cnorm_Csum_conj_sym (fun k => psi 15 k) (fun k => psi 3 k) 255).
        apply pair_3_15; lia.
      * replace (nth 1 t8l 0%nat) with 15%nat by reflexivity.
        replace (nth 2 t8l 0%nat) with 63%nat by reflexivity.
        apply pair_15_63; lia.
      * replace (nth 1 t8l 0%nat) with 15%nat by reflexivity.
        replace (nth 3 t8l 0%nat) with 255%nat by reflexivity.
        apply pair_15_255; lia.
  - simpl. nra.
Qed.

Lemma t8_row2 : sum_f_R0 (fun j => if eq_nat_dec 2 j then 0%R else
      Cnorm (Csum (fun k => psi (nth 2 t8l 0%nat) k *c Cconj (psi (nth j t8l 0%nat) k)) 255)) 3
  <= 4 / 5.
Proof.
  apply Rle_trans with (sum_f_R0 (fun j => match j with 0%nat => 63 / 520 | 1%nat => 21 / 64 | 2%nat => 0%R | _ => 85 / 256 end) 3).
  - apply sum_f_R0_le_compat. intros j Hj.
    destruct (eq_nat_dec 2 j) as [H2 | H2n].
    + subst j. simpl. nra.
    + destruct j as [|[|[|[|j']]]]; try lia.
      * replace (nth 2 t8l 0%nat) with 63%nat by reflexivity.
        replace (nth 0 t8l 0%nat) with 3%nat by reflexivity.
        rewrite (ExtendedTheorems.Cnorm_Csum_conj_sym (fun k => psi 63 k) (fun k => psi 3 k) 255).
        apply pair_3_63; lia.
      * replace (nth 2 t8l 0%nat) with 63%nat by reflexivity.
        replace (nth 1 t8l 0%nat) with 15%nat by reflexivity.
        rewrite (ExtendedTheorems.Cnorm_Csum_conj_sym (fun k => psi 63 k) (fun k => psi 15 k) 255).
        apply pair_15_63; lia.
      * replace (nth 2 t8l 0%nat) with 63%nat by reflexivity.
        replace (nth 3 t8l 0%nat) with 255%nat by reflexivity.
        apply pair_63_255; lia.
  - simpl. nra.
Qed.

Lemma t8_row3 : sum_f_R0 (fun j => if eq_nat_dec 3 j then 0%R else
      Cnorm (Csum (fun k => psi (nth 3 t8l 0%nat) k *c Cconj (psi (nth j t8l 0%nat) k)) 255)) 3
  <= 4 / 5.
Proof.
  apply Rle_trans with (sum_f_R0 (fun j => match j with 0%nat => 85 / 1512 | 1%nat => 255 / 1952 | 2%nat => 85 / 256 | _ => 0%R end) 3).
  - apply sum_f_R0_le_compat. intros j Hj.
    destruct (eq_nat_dec 3 j) as [H3 | H3n].
    + subst j. simpl. nra.
    + destruct j as [|[|[|[|j']]]]; try lia.
      * replace (nth 3 t8l 0%nat) with 255%nat by reflexivity.
        replace (nth 0 t8l 0%nat) with 3%nat by reflexivity.
        rewrite (ExtendedTheorems.Cnorm_Csum_conj_sym (fun k => psi 255 k) (fun k => psi 3 k) 255).
        apply pair_3_255; lia.
      * replace (nth 3 t8l 0%nat) with 255%nat by reflexivity.
        replace (nth 1 t8l 0%nat) with 15%nat by reflexivity.
        rewrite (ExtendedTheorems.Cnorm_Csum_conj_sym (fun k => psi 255 k) (fun k => psi 15 k) 255).
        apply pair_15_255; lia.
      * replace (nth 3 t8l 0%nat) with 255%nat by reflexivity.
        replace (nth 2 t8l 0%nat) with 63%nat by reflexivity.
        rewrite (ExtendedTheorems.Cnorm_Csum_conj_sym (fun k => psi 255 k) (fun k => psi 63 k) 255).
        apply pair_63_255; lia.
  - simpl. nra.
Qed.

(* ============ T8 核实例证书：μ = 4/5 ⟹ (1/5)·S ≤ ‖F‖² ≤ (9/5)·S ============ *)
(* [3,15,63,255]，窗口 255（M = 256）；对一切 N ≥ 255 有效（psi 有限支撑） *)
Theorem certified_t8_core_frame_bounds (coeffs : list Complex) :
  length coeffs = 4%nat ->
  let n := 4%nat in
  let M := 256%nat in
  let phi := fun i k => psi (nth i t8l 0%nat) k in
  let F := fun k => Csum (fun i => nth i coeffs C0 *c phi i k) n in
  let S := sum_f_R0 (fun i => Cnorm_sq (nth i coeffs C0)) (Nat.pred n) in
  ((1 - 4 / 5) * S <= l2_norm_sq F (Nat.pred M) <= (1 + 4 / 5) * S)%R.
Proof.
  intros Hlen.
  cbv zeta.
  apply (gershgorin_frame_mu 4 (fun i k => psi (nth i t8l 0%nat) k) 256 (4 / 5)).
  - lia.
  - intros i k Hi Hk.
    destruct i as [|[|[|[|i']]]].
    + simpl. apply psi_ge_n_zero. lia.
    + simpl. apply psi_ge_n_zero. lia.
    + simpl. apply psi_ge_n_zero. lia.
    + simpl. apply psi_ge_n_zero. lia.
    + exfalso. lia.
  - intros i Hi.
    destruct i as [|[|[|[|i']]]].
    + replace (nth 0 t8l 0%nat) with 3%nat by reflexivity. apply psi_unit_norm; lia.
    + replace (nth 1 t8l 0%nat) with 15%nat by reflexivity. apply psi_unit_norm; lia.
    + replace (nth 2 t8l 0%nat) with 63%nat by reflexivity. apply psi_unit_norm; lia.
    + replace (nth 3 t8l 0%nat) with 255%nat by reflexivity. apply psi_unit_norm; lia.
    + exfalso. lia.
  - intros i Hi.
    destruct i as [|[|[|[|i']]]]; try lia.
    + apply t8_row0.
    + apply t8_row1.
    + apply t8_row2.
    + apply t8_row3.
  - exact Hlen.
Qed.

End T8CoreCertificate.

(* ============================================================
   M4 收尾②：frame_check_instance 反射式框架检查器（会话 9 并入）
   任意阶梯 → 布尔判定 μ ≤ 4/5，可提取到 OCaml（__frame__ 命令）。
   floor-sqrt 有理化 + nat 分数行和，全部可判定有理算术（可提取性根源）。
   零 classic。soundness 定理（pair_sound + frame_check_instance_sound）
   在后续并入时 Qed（见探针注释）。
   ============================================================ *)
Module FrameCheckInstance.

Import UnconditionalBasisLemmas.
Import ExtendedTheorems.
Import InstanceCertificate.
Import RuntimeGuards.
Import Gershgorin.
Open Scope R_scope.

(* ============ 反射层 1：对界分数与有效性检查 ============ *)

(* floor-sqrt 有理化界：bound(n1,n2) = n1·n2 / (2·(n2−n1)·f)，f = Nat.sqrt (n1·n2) *)
Definition pair_num (n1 n2 : nat) : nat := n1 * n2.
Definition pair_den (n1 n2 : nat) : nat := 2 * (n2 - n1) * Nat.sqrt (n1 * n2).

(* f 有效性：f·f ≤ n1·n2 且 0 < f（n2 > n1 由调用方保证） *)
Definition pair_ok (n1 n2 : nat) : bool :=
  andb (Nat.leb (Nat.sqrt (n1 * n2) * Nat.sqrt (n1 * n2)) (n1 * n2))
       (Nat.ltb 0 (Nat.sqrt (n1 * n2))).

(* ============ 反射层 2：行和（nat 分数累加） ============ *)
(* 关键：全程用 nat 分数对（num,den），避免 R scope 下的 * 解释 → 显式 %type *)

(* frac 对类型别名 *)
Notation nat_pair := (nat * nat)%type.

(* 分数 (num, den)，den > 0 不变式由构造保证（初值 (0,1)，加法保持 den > 0） *)
Definition frac_add (a b c d : nat) : nat_pair :=
  ((a * d + c * b)%nat, (b * d)%nat).

(* 把阶梯中第 i 个元素与所有 j ≠ i 的对界累加为分数（i < j 用 pair，i > j 对称同值）
   ⚠️ 会话 9 续勘误（2026-08-19）：n_i 必须取自原始阶梯 orig 的第 i 个元素，
   而非当前收缩列表 I——旧定义在递归中让 n_i 漂移到 orig[j+i]，与原生 int
   检查器（psa_guard_main.ml 的 frame_check_instance_int，ni=arr.(i) 固定）不一致，
   导致 Coq 反射层对 [3,13] 误判 false、对 C4 行和退化为 (0,0) 真空通过。
   本修正使 Coq 定义与原生检查器逐行同构（orig 参数携带原始阶梯）。 *)
Fixpoint row_sum_frac_aux (I orig : list nat) (i : nat) (acc : nat_pair) (j : nat) : nat_pair :=
  match I with
  | nil => acc
  | cons h tl =>
      let n_i := nth i orig 0%nat in
      let (num, den) := acc in
      if Nat.eqb j i then row_sum_frac_aux tl orig i acc (S j)
      else
        let n_j := h in
        if Nat.ltb n_j n_i then row_sum_frac_aux tl orig i (frac_add num den (pair_num n_j n_i) (pair_den n_j n_i)) (S j)
        else row_sum_frac_aux tl orig i (frac_add num den (pair_num n_i n_j) (pair_den n_i n_j)) (S j)
  end.

Definition row_sum_frac (I : list nat) (i : nat) : nat_pair :=
  row_sum_frac_aux I I i (0%nat, 1%nat) 0%nat.

(* 行和 ≤ 4/5 的布尔判定（交叉相乘，分母 > 0） *)
Definition row_le_4_5 (f : nat_pair) : bool :=
  Nat.leb (5 * fst f)%nat (4 * snd f)%nat.

(* ============ 反射层 3：阶梯结构检查 ============ *)

(* 严格升序（相邻对 a < b）——prev 携带上一元素，结构递归在 list 上 *)
Fixpoint sorted_aux (prev : nat) (l : list nat) : bool :=
  match l with
  | nil => true
  | cons h tl => andb (Nat.ltb prev h) (sorted_aux h tl)
  end.

Definition sorted_strict_aux (l : list nat) : bool :=
  match l with
  | nil => true
  | cons h tl => sorted_aux h tl
  end.

(* 全部 ≥ 2 *)
Fixpoint all_ge_2 (l : list nat) : bool :=
  match l with
  | nil => true
  | cons h tl => andb (Nat.leb 2 h) (all_ge_2 tl)
  end.

(* 所有对界有效 *)
Fixpoint all_pairs_ok (I : list nat) : bool :=
  match I with
  | nil => true
  | cons h tl =>
      andb (forallb (fun n => pair_ok h n) tl) (all_pairs_ok tl)
  end.

(* 所有行和 ≤ 4/5（i 为行号；orig 携带原始阶梯——与原生 row_sum_le_4_5 ladder i 一致） *)
Fixpoint all_rows_le (I orig : list nat) (i : nat) : bool :=
  match I with
  | nil => true
  | cons h tl => andb (row_le_4_5 (row_sum_frac orig i)) (all_rows_le tl orig (S i))
  end.

(* ============ 框架检查器（主入口） ============ *)

(* frame_check_instance I = true ⟹ 阶梯 I（升序、全 ≥2、对界有效、行和 ≤ 4/5）
   对任意系数向量，gershgorin μ ≤ 4/5 框架界 [1/5, 9/5] 成立（窗口 = 末元素 n_max） *)
Definition frame_check_instance (I : list nat) : bool :=
  andb (sorted_strict_aux I)
       (andb (all_ge_2 I)
             (andb (all_pairs_ok I) (all_rows_le I I 0%nat))).

(* ============ 计算验证（仅小阶梯——Coq VM 的 Peano 大数乘法不可扩展） ============ *)
(* ⚠️ 设计决策（2026-08-19 会话 9）：
   反射检查器的实际验证交由提取后的 OCaml（psa_guard.exe，机器字整数）。
   Coq 的 vm_compute 用 Peano unary nat，frac_add 的大分母乘法（如 b*d 对
   den≈48384 时会展开海量 S）在 ≥[3,53] 级即栈溢出。因此：
   - 小阶梯（对 ≤[3,13]）：本文件 vm_compute 验证；
   - 大阶梯（C4/T8/E5''/C2b）：提取后 __frame__ 命令逐阶梯验证（见 psa_guard_main.ml）。 *)

(* 反射单对界验证（小，可计算） *)
Example pair_ok_3_13 : pair_ok 3 13 = true.
Proof. vm_compute. reflexivity. Qed.

(* 反射单对界：黑洞对（无 gap）不可认证 *)
Example pair_ok_2_3 : pair_ok 2 3 = true.
Proof. vm_compute. reflexivity. Qed.

(* ============ soundness：反射对界 ⟹ R 层对界（pair_sound） ============ *)
(* pair_ok n1 n2 = true ⟹ 反射有理界是 psi 内积保守界的上界 *)
Lemma pair_sound (n1 n2 : nat) :
  (2 <= n1)%nat -> (n1 < n2)%nat -> pair_ok n1 n2 = true ->
  (1 / (2 * (1 / INR n1 - 1 / INR n2) * sqrt (INR n1 * INR n2))
   <= INR (pair_num n1 n2) / INR (pair_den n1 n2))%R.
Proof.
  intros Hn1 Hlt Hok.
  unfold pair_num, pair_den.
  (* 用 cons_bound_floor：f = Nat.sqrt (n1*n2) *)
  apply Rle_trans with (INR n1 * INR n2 / (2 * INR (n2 - n1) * INR (Nat.sqrt (n1 * n2)))).
  - (* cons_bound_floor，f = Nat.sqrt (n1*n2) *)
    apply cons_bound_floor.
    + exact Hn1.
    + lia.
    + exact Hlt.
    + (* INR f ≤ sqrt (INR n1 · INR n2)：f·f ≤ n1·n2 来自 pair_ok *)
      assert (Hsq : (Nat.sqrt (n1 * n2) * Nat.sqrt (n1 * n2) <= n1 * n2)%nat).
      { unfold pair_ok in Hok.
        destruct (andb_prop _ _ Hok) as [Hleft _].
        exact (proj1 (Nat.leb_le _ _) Hleft). }
      rewrite <- (mult_INR n1 n2).
      apply INR_sqrt_le.
      exact Hsq.
    + (* 0 < INR f：f > 0 来自 pair_ok 第二支 *)
      assert (Hpos : (0 < Nat.sqrt (n1 * n2))%nat).
      { unfold pair_ok in Hok.
        destruct (andb_prop _ _ Hok) as [_ Hright].
        exact (proj1 (Nat.ltb_lt 0 (Nat.sqrt (n1 * n2))) Hright). }
      apply lt_0_INR. exact Hpos.
  - (* 右侧归一化：INR 复合分解，证明中间项 = 右边（lra + ring 处理 INR 多项式） *)
    rewrite (mult_INR n1 n2).
    replace (INR ((2 * (n2 - n1)) * Nat.sqrt (n1 * n2)))
       with (2 * INR (n2 - n1) * INR (Nat.sqrt (n1 * n2))) by
         (rewrite (mult_INR (2 * (n2 - n1)) (Nat.sqrt (n1 * n2)));
          rewrite (mult_INR 2 (n2 - n1));
          replace (INR 2) with 2 by reflexivity;
          ring).
    apply Rle_refl.
Qed.

(* ============ soundness 辅助：除法不等式 / 分数加法 / INR 字面量（会话 9 续） ============ *)

(* 除法不等式交叉相乘：a/b <= c/d 由 a·d <= c·b（b,d>0） *)
Lemma div_le (a b c d : R) (Hb : 0 < b) (Hd : 0 < d) (H : (a * d <= c * b)%R) :
  (a / b <= c / d)%R.
Proof.
  apply (Rmult_le_reg_r (b * d)).
  - apply Rmult_lt_0_compat; [exact Hb | exact Hd].
  - replace ((a / b) * (b * d)) with (a * d).
    + replace ((c / d) * (b * d)) with (c * b).
      * exact H.
      * field. apply Rgt_not_eq; exact Hd.
    + field. apply Rgt_not_eq; exact Hb.
Qed.

(* frac_add 的 R 分数加法：frac_add(a,b,c,d) 解读 = a/b + c/d *)
Lemma frac_add_R (a b c d : nat) (Hb : b <> 0%nat) (Hd : d <> 0%nat) :
  (INR (a * d + c * b) / INR (b * d) = INR a / INR b + INR c / INR d)%R.
Proof.
  rewrite (plus_INR (a*d) (c*b)).
  rewrite (mult_INR a d). rewrite (mult_INR c b). rewrite (mult_INR b d).
  field.
  split.
  - apply Rgt_not_eq. apply lt_0_INR. apply Nat.neq_0_lt_0; exact Hd.
  - apply Rgt_not_eq. apply lt_0_INR. apply Nat.neq_0_lt_0; exact Hb.
Qed.

Lemma INR5 : (INR 5)%R = 5. Proof. compute. rewrite Rplus_assoc. ring. Qed.
Lemma INR4 : (INR 4)%R = 4. Proof. compute. rewrite Rplus_assoc. ring. Qed.

(* row_le_4_5 (num,den)=true (即 5·num ≤ 4·den) ⟹ R 层 num/den ≤ 4/5 *)
Lemma row_le_R (num den : nat) (Hd : den <> 0%nat) :
  (5 * num <= 4 * den)%nat ->
  (INR num / INR den <= 4 / 5)%R.
Proof.
  intros H.
  assert (Hden_pos : 0 < INR den) by (apply lt_0_INR; apply Nat.neq_0_lt_0; exact Hd).
  assert (HleR : (INR (5 * num) <= INR (4 * den))%R) by apply le_INR, H.
  rewrite (mult_INR 5 num) in HleR. rewrite (mult_INR 4 den) in HleR.
  rewrite INR5 in HleR. rewrite INR4 in HleR.
  apply div_le with (b := INR den) (d := 5).
  - exact Hden_pos.
  - lra.
  - replace (INR num * 5) with (5 * INR num) by ring.
    exact HleR.
Qed.

(* ============ soundness 主定理：frame_check_instance_sound（装配完成，零 Admitted） ============
   (a) 逐对 Cnorm ≤ INR(pair_num)/INR(pair_den)（pair_sound + Cnorm_Csum_conj_sym 对称）
   (b) row_sum_frac 累加 = 分数加法（frac_add_R），R 行和 = INR(num)/INR(den)
   (c) row_le_4_5 = true + row_le_R ⟹ R 行和 ≤ 4/5
   (d) psi_unit_norm（sorted+all_ge_2 ⟹ 窗口 last I 覆盖每元素；psi_ge_n_zero 零化高于窗口）
   (e) gershgorin_frame_mu 通用实例化（n=length I 任意，M=S(last I 0%nat)）
   已 Qed：pair_sound + div_le + frac_add_R + row_le_R + 以下全部。 *)

(* ============ 步骤 A：逐对界 ============ *)
Lemma pair_bound_ok (n1 n2 N : nat) :
  (2 <= n1)%nat -> (n1 < n2)%nat -> (n1 <= N)%nat -> pair_ok n1 n2 = true ->
  Cnorm (Csum (fun k => psi n1 k *c Cconj (psi n2 k)) N)
  <= INR (pair_num n1 n2) / INR (pair_den n1 n2).
Proof.
  intros Hn1 Hlt HleN Hok.
  apply Rle_trans with (1 / (2 * (1 / INR n1 - 1 / INR n2) * sqrt (INR n1 * INR n2))).
  - apply psi_inner_cons_bound; auto. lia.
  - exact (pair_sound n1 n2 Hn1 Hlt Hok).
Qed.

(* ============ 结构引理：sorted / all_ge_2 / pair_ok / 分母 ============ *)

Lemma sorted_aux_eq_forallb_aux (l : list nat) :
  forall prev, sorted_aux prev l = forallb_adjacent (prev :: l) Nat.ltb.
Proof.
  induction l as [| h tl IH]; intros prev; simpl; try reflexivity.
  unfold forallb_adjacent. simpl.
  f_equal. exact (IH h).
Qed.

Lemma sorted_strict_aux_eq_forallb (l : list nat) :
  sorted_strict_aux l = forallb_adjacent l Nat.ltb.
Proof.
  destruct l as [| a tl]; simpl; try reflexivity.
  apply (sorted_aux_eq_forallb_aux tl a).
Qed.

Lemma sorted_nth_lt (l : list nat) :
  sorted_strict_aux l = true ->
  forall i j, (i < j)%nat -> (j < length l)%nat -> (nth i l 0%nat < nth j l 0%nat)%nat.
Proof.
  intros Hs i j Hij Hj.
  rewrite sorted_strict_aux_eq_forallb in Hs.
  pose proof (forallb_adjacent_sorted_implies l Nat.ltb
    (fun a b c Hab Hbc =>
       proj2 (Nat.ltb_lt a c)
             (Nat.lt_trans a b c (proj1 (Nat.ltb_lt a b) Hab) (proj1 (Nat.ltb_lt b c) Hbc)))
    Hs i j Hij Hj) as Hltb.
  apply Nat.ltb_lt. exact Hltb.
Qed.

(* sorted 严格递增 ⟹ 不同位置元素互异 *)
Lemma sorted_nth_neq (l : list nat) :
  sorted_strict_aux l = true ->
  forall i j, (i < length l)%nat -> (j < length l)%nat -> i <> j ->
  (nth i l 0%nat <> nth j l 0%nat)%nat.
Proof.
  intros Hs i j Hi Hj Hij.
  destruct (Nat.lt_ge_cases i j) as [Hlt | Hge].
  - apply (Nat.lt_neq _ _ (sorted_nth_lt l Hs i j Hlt Hj)).
  - destruct (Nat.lt_ge_cases j i) as [Hlt2 | Hge2].
    + symmetry. apply (Nat.lt_neq _ _ (sorted_nth_lt l Hs j i Hlt2 Hi)).
    + exfalso. apply Hij. lia.
Qed.

Lemma all_ge_2_nth (l : list nat) :
  all_ge_2 l = true -> forall i, (i < length l)%nat -> (2 <= nth i l 0%nat)%nat.
Proof.
  intros Hg i Hi.
  pose proof (all_ge_2P l) as Hr.
  assert (Hiff := (reflect_iff (forall v : nat, In v l -> (v >= 2)%nat) (all_ge_2 l)) Hr).
  rewrite <- Hiff in Hg.
  assert (Hin : In (nth i l 0%nat) l) by (apply nth_In; exact Hi).
  exact (Hg (nth i l 0%nat) Hin).
Qed.

Lemma last_eq_nth_pred (l : list nat) (d : nat) :
  (0 < length l)%nat -> last l d = nth (length l - 1) l d.
Proof.
  intros Hlen.
  induction l as [| a [| b tll] IH].
  - simpl in Hlen. lia.
  - reflexivity.
  - simpl.
    simpl in IH.
    rewrite Nat.sub_0_r in IH.
    exact (IH (Nat.lt_0_succ _)).
Qed.

Lemma nth_le_last (l : list nat) :
  sorted_strict_aux l = true ->
  forall i, (i < length l)%nat -> (nth i l 0%nat <= last l 0%nat)%nat.
Proof.
  intros Hs i Hi.
  assert (Hpos : (0 < length l)%nat) by lia.
  destruct (Nat.lt_ge_cases i (length l - 1)) as [Hlt | Hge].
  - rewrite (last_eq_nth_pred l 0%nat Hpos).
    apply Nat.lt_le_incl. apply (sorted_nth_lt l Hs i (length l - 1) Hlt).
    lia.
  - rewrite (last_eq_nth_pred l 0%nat Hpos).
    assert (Heq : i = (length l - 1)%nat) by lia.
    rewrite Heq. lia.
Qed.

Lemma pair_ok_ge2 (n1 n2 : nat) : (2 <= n1)%nat -> (2 <= n2)%nat ->
  pair_ok n1 n2 = true.
Proof.
  intros Hn1 Hn2.
  unfold pair_ok.
  apply andb_true_intro. split.
  - apply Nat.leb_le. apply Nat.sqrt_specif.
  - apply Nat.ltb_lt.
    assert (Hsq : (1 <= Nat.sqrt (n1 * n2))%nat).
    { apply (proj1 (Nat.sqrt_le_square (n1 * n2) 1)).
      simpl. nia. }
    lia.
Qed.

Lemma pair_den_pos (n1 n2 : nat) : (2 <= n1)%nat -> (n1 < n2)%nat ->
  (0 < pair_den n1 n2)%nat.
Proof.
  intros Hn1 Hlt.
  unfold pair_den.
  apply Nat.mul_pos_pos.
  - apply Nat.mul_pos_pos; lia.
  - assert (Hsq : (1 <= Nat.sqrt (n1 * n2))%nat).
    { apply (proj1 (Nat.sqrt_le_square (n1 * n2) 1)). simpl. nia. }
    lia.
Qed.

Lemma pair_den_neq0 (n1 n2 : nat) : (2 <= n1)%nat -> (n1 < n2)%nat ->
  pair_den n1 n2 <> 0%nat.
Proof.
  intros Hn1 Hlt.
  apply Nat.neq_0_lt_0. apply (pair_den_pos n1 n2 Hn1 Hlt).
Qed.

(* ============ 步骤 B：row_sum_frac 的 R 层解读 ============ *)
(* 逐对分数：INR(pair_num (min n1 n2) (max n1 n2)) / INR(pair_den (min n1 n2) (max n1 n2)) *)
Definition pair_frac_R (n1 n2 : nat) : R :=
  INR (pair_num (min n1 n2) (max n1 n2)) / INR (pair_den (min n1 n2) (max n1 n2)).

(* sum_f_R0 移位：sum g (S n) = g 0 + sum (fun k => g (S k)) n *)
Lemma sum_f_R0_shift (g : nat -> R) (n : nat) :
  sum_f_R0 g (S n) = g 0%nat + sum_f_R0 (fun k => g (S k)) n.
Proof.
  induction n as [| n IH].
  - simpl. ring.
  - change (sum_f_R0 g (S n) + g (S (S n)) = g 0%nat + (sum_f_R0 (fun k => g (S k)) n + g (S (S n)))).
    rewrite IH. ring.
Qed.

(* ltb 分支选择 (min,max) 对：h ≠ n_i 时，if ltb h n_i then pair(h,n_i) else pair(n_i,h)
   = pair(min n_i h, max n_i h) *)
Lemma ltb_pair_minmax (n_i h : nat) :
  h <> n_i ->
  (if Nat.ltb h n_i then (pair_num h n_i, pair_den h n_i) else (pair_num n_i h, pair_den n_i h))
  = (pair_num (min n_i h) (max n_i h), pair_den (min n_i h) (max n_i h)).
Proof.
  intros Hne.
  destruct (Nat.ltb_spec h n_i) as [Hhlt | Hhge].
  - (* h < n_i：min = h, max = n_i *)
    f_equal.
    + unfold pair_num. simpl. lia.
    + unfold pair_den. simpl.
      assert (H1 : (min n_i h = h)%nat) by lia.
      assert (H2 : (max n_i h = n_i)%nat) by lia.
      rewrite H1, H2. lia.
  - (* h >= n_i，且 h ≠ n_i ⟹ h > n_i：min = n_i, max = h *)
    f_equal.
    + unfold pair_num. simpl. lia.
    + unfold pair_den. simpl.
      assert (Hhgt : (n_i < h)%nat) by lia.
      assert (H1 : (min n_i h = n_i)%nat) by lia.
      assert (H2 : (max n_i h = h)%nat) by lia.
      rewrite H1, H2. lia.
Qed.

(* frac_add 保持分母非零（乘积） *)
Lemma frac_add_snd_neq0 (a b c d : nat) :
  b <> 0%nat -> d <> 0%nat -> snd (frac_add a b c d) <> 0%nat.
Proof.
  unfold frac_add, snd. intros Hb Hd. lia.
Qed.

(* 辅助：frac_add 的 fst/snd 形式（plain rewrite 按转换匹配不到 fst/snd，故单独成引理） *)
Lemma frac_add_R' (a b c d : nat) (Hb : b <> 0%nat) (Hd : d <> 0%nat) :
  (INR (fst (frac_add a b c d)) / INR (snd (frac_add a b c d)) = INR a / INR b + INR c / INR d)%R.
Proof.
  unfold frac_add. simpl.
  apply (frac_add_R a b c d Hb Hd).
Qed.

(* 辅助：对角线跳过（j = i 时 fixpoint 一步归约到跳过分支） *)
Lemma row_sum_frac_aux_skip_diag (orig : list nat) (h y : nat) (tl' : list nat) (i j : nat) (acc : nat_pair) (Hji : j = i) :
  row_sum_frac_aux (h :: y :: tl') orig i acc j = row_sum_frac_aux (y :: tl') orig i acc (S j).
Proof.
  simpl.
  rewrite (proj2 (Nat.eqb_eq j i) Hji).
  simpl.
  destruct acc as [num0 den0]; reflexivity.
Qed.

(* 辅助：非对角线 h < n_i（fixpoint 一步归约到 frac_add 分支） *)
Lemma row_sum_frac_aux_step_lt (orig : list nat) (h y : nat) (tl' : list nat) (i j : nat) (num0 den0 : nat)
  (Hjni : j <> i) (Hhlt : (h < nth i orig 0%nat)%nat) :
  row_sum_frac_aux (h :: y :: tl') orig i (num0, den0) j
  = row_sum_frac_aux (y :: tl') orig i
      (frac_add num0 den0 (pair_num h (nth i orig 0%nat)) (pair_den h (nth i orig 0%nat))) (S j).
Proof.
  simpl.
  rewrite (proj2 (Nat.eqb_neq j i) Hjni).
  simpl.
  rewrite (proj2 (Nat.ltb_lt h (nth i orig 0%nat)) Hhlt).
  simpl.
  reflexivity.
Qed.

(* 辅助：非对角线 h >= n_i（h ≠ n_i ⟹ n_i < h） *)
Lemma row_sum_frac_aux_step_ge (orig : list nat) (h y : nat) (tl' : list nat) (i j : nat) (num0 den0 : nat)
  (Hjni : j <> i) (Hhge : (nth i orig 0 <= h)%nat) (Hhgt : (nth i orig 0 < h)%nat) :
  row_sum_frac_aux (h :: y :: tl') orig i (num0, den0) j
  = row_sum_frac_aux (y :: tl') orig i
      (frac_add num0 den0 (pair_num (nth i orig 0%nat) h) (pair_den (nth i orig 0%nat) h)) (S j).
Proof.
  simpl.
  rewrite (proj2 (Nat.eqb_neq j i) Hjni).
  simpl.
  rewrite (proj2 (Nat.ltb_ge h (nth i orig 0%nat)) Hhge).
  reflexivity.
Qed.

(* 辅助：pair_frac_R 显式化（h < n_i） *)
Lemma pair_frac_R_min (orig : list nat) (h i : nat) (Hhlt : (h < nth i orig 0%nat)%nat) :
  pair_frac_R (nth i orig 0%nat) h = INR (pair_num h (nth i orig 0%nat)) / INR (pair_den h (nth i orig 0%nat)).
Proof.
  unfold pair_frac_R.
  rewrite (Nat.min_r (nth i orig 0%nat) h) by lia.
  rewrite (Nat.max_l (nth i orig 0%nat) h) by lia.
  reflexivity.
Qed.

(* 辅助：pair_frac_R 显式化（n_i < h） *)
Lemma pair_frac_R_max (orig : list nat) (h i : nat) (Hhgt : (nth i orig 0 < h)%nat) :
  pair_frac_R (nth i orig 0%nat) h = INR (pair_num (nth i orig 0%nat) h) / INR (pair_den (nth i orig 0%nat) h).
Proof.
  unfold pair_frac_R.
  rewrite (Nat.min_l (nth i orig 0%nat) h) by lia.
  rewrite (Nat.max_r (nth i orig 0%nat) h) by lia.
  reflexivity.
Qed.
(* 分数累加（R 层）：frac_add 与 + 同态（每个 frac_add 一步用 frac_add_R）。
   核心不变式：row_sum_frac_aux I orig i acc j 的 R 值 = acc 的 R 值
   + Σ_{k=0}^{|I|-1} [若 j+k = i 则 0，否则 pair_frac_R(nth i orig, nth (j+k) orig)]。 *)
Lemma row_sum_frac_aux_R (I orig : list nat) (i : nat) :
  forall acc : nat_pair, forall j : nat,
  (0 < length I)%nat ->
  (j + length I <= length orig)%nat ->
  (forall k, (k < length I)%nat -> nth k I 0%nat = nth (j + k) orig 0%nat) ->
  (snd acc <> 0)%nat ->
  (forall k, (k < length orig)%nat -> (2 <= nth k orig 0)%nat) ->
  (forall k1 k2, (k1 < k2)%nat -> (k2 < length orig)%nat -> (nth k1 orig 0 < nth k2 orig 0)%nat) ->
  (i < length orig)%nat ->
  INR (fst (row_sum_frac_aux I orig i acc j)) / INR (snd (row_sum_frac_aux I orig i acc j))
  = INR (fst acc) / INR (snd acc)
    + sum_f_R0 (fun k => if Nat.eqb (j + k) i then 0%R else
         pair_frac_R (nth i orig 0%nat) (nth (j + k) orig 0%nat)) (Nat.pred (length I)).
Proof.
  induction I as [| h tl IH]; intros acc j Hlen Hsuf Hnth Hden0 Hge2 Hsorted Hi.
  - simpl in Hlen. lia.
  - assert (Hjlen : (j < length orig)%nat).
    { apply Nat.lt_le_trans with (j + length (h :: tl))%nat; [lia | exact Hsuf]. }
    assert (Hsuf' : (S j + length tl <= length orig)%nat).
    { simpl in Hsuf. lia. }
    destruct tl as [| y tl'].
    + (* I = h :: nil：单元素，pred 1 = 0 *)
      simpl.
      destruct (Nat.eqb_spec j i) as [Hji | Hjni].
      * (* 对角线：跳过，贡献 0 *)
        rewrite Hji. simpl.
        assert (Heq : (i + 0 =? i) = true) by (apply (proj2 (Nat.eqb_eq (i + 0) i)); lia).
        rewrite Heq. simpl.
        destruct acc as [num den]. simpl. ring.
      * (* 非对角线：累加对界 *)
        destruct acc as [num0 den0].
        assert (Hh : h = nth j orig 0%nat).
        { specialize (Hnth 0%nat). simpl in Hnth. rewrite Nat.add_0_r in Hnth.
          exact (Hnth (Nat.lt_0_succ _)). }
        assert (Hhne : h <> nth i orig 0%nat).
        { intro Heq.
          destruct (Nat.lt_ge_cases j i) as [Hjlt | Hige].
          - assert (Hlt : (nth j orig 0%nat < nth i orig 0%nat)%nat) by (apply (Hsorted j i); [exact Hjlt | exact Hi]).
            rewrite <- Hh in Hlt. lia.
          - assert (Hij' : (i <> j)%nat) by (exact (fun Hij => Hjni (sym_eq Hij))).
            assert (Hilt : (i < j)%nat).
            { apply (proj2 (Nat.le_neq i j)). split; [exact Hige | exact Hij']. }
            assert (Hlt : (nth i orig 0%nat < nth j orig 0%nat)%nat) by (apply (Hsorted i j); [exact Hilt | exact Hjlen]).
            rewrite <- Hh in Hlt. lia.
        }
        destruct (Nat.ltb_spec h (nth i orig 0%nat)) as [Hhlt | Hhge].
        -- (* h < n_i *)
           unfold frac_add. simpl.
           rewrite (frac_add_R num0 den0
                     (pair_num h (nth i orig 0%nat)) (pair_den h (nth i orig 0%nat))).
           ++ simpl.
             rewrite Nat.add_0_r.
             destruct (Nat.eqb_spec j i) as [Hj0 | Hj0n]; [congruence |].
             rewrite <- Hh.
             f_equal.
             unfold pair_frac_R.
             rewrite (Nat.min_r (nth i orig 0%nat) h) by lia.
             rewrite (Nat.max_l (nth i orig 0%nat) h) by lia.
             reflexivity.
           ++ exact Hden0.
           ++ apply pair_den_neq0; [rewrite Hh; apply (Hge2 j); exact Hjlen | exact Hhlt].
        -- (* h >= n_i 且 h ≠ n_i ⟹ h > n_i *)
           assert (Hhgt : (nth i orig 0%nat < h)%nat) by lia.
           unfold frac_add. simpl.
           rewrite (frac_add_R num0 den0
                     (pair_num (nth i orig 0%nat) h) (pair_den (nth i orig 0%nat) h)).
           ++ simpl.
             rewrite Nat.add_0_r.
             destruct (Nat.eqb_spec j i) as [Hj0 | Hj0n]; [congruence |].
             rewrite <- Hh.
             f_equal.
             unfold pair_frac_R.
             rewrite (Nat.min_l (nth i orig 0%nat) h) by lia.
             rewrite (Nat.max_r (nth i orig 0%nat) h) by lia.
             reflexivity.
           ++ exact Hden0.
           ++ apply pair_den_neq0; [apply (Hge2 i); exact Hi | exact Hhgt].
    + (* I = h :: y :: tl'：递归 *)
      assert (Hnth' : forall k : nat, (k < length (y :: tl'))%nat ->
              nth k (y :: tl') 0%nat = nth (S j + k) orig 0%nat).
      { intros k Hk.
        assert (Hk' : (S k < length (h :: y :: tl'))%nat).
        { exact (proj1 (Nat.succ_lt_mono k (length (y :: tl'))) Hk). }
        pose proof (Hnth (S k) Hk') as HnthS.
        simpl in HnthS.
        rewrite Nat.add_succ_r in HnthS.
        exact HnthS.
      }
      destruct (Nat.eqb_spec j i) as [Hji | Hjni].
      * (* j = i：跳过对角线（该项 0） *)
        subst j.
        assert (Hii : i = i) by reflexivity.
        rewrite (row_sum_frac_aux_skip_diag orig h y tl' i i acc Hii).
        rewrite (IH acc (S i) (Nat.lt_0_succ _) Hsuf' Hnth' Hden0 Hge2 Hsorted Hi).
        replace (Nat.pred (length (y :: tl'))) with (length tl') by reflexivity.
        replace (Nat.pred (length (h :: y :: tl'))) with (S (length tl')) by reflexivity.
        rewrite sum_f_R0_shift.
        rewrite (Nat.add_0_r i).
        rewrite (Nat.eqb_refl i).
        simpl.
        f_equal.
        rewrite Rplus_0_l.
        apply sum_f_R0_ext.
        intros k Hk.
        rewrite Nat.add_succ_r.
        reflexivity.
      * (* j ≠ i：累加对界 *)
        destruct acc as [num0 den0].
        assert (Hh : h = nth j orig 0%nat).
        { specialize (Hnth 0%nat). simpl in Hnth. rewrite Nat.add_0_r in Hnth.
          exact (Hnth (Nat.lt_0_succ _)). }
        assert (Hhne : h <> nth i orig 0%nat).
        { intro Heq.
          destruct (Nat.lt_ge_cases j i) as [Hjlt | Hige].
          - assert (Hlt : (nth j orig 0%nat < nth i orig 0%nat)%nat) by (apply (Hsorted j i); [exact Hjlt | exact Hi]).
            rewrite <- Hh in Hlt. lia.
          - assert (Hij' : (i <> j)%nat) by (exact (fun Hij => Hjni (sym_eq Hij))).
            assert (Hilt : (i < j)%nat).
            { apply (proj2 (Nat.le_neq i j)). split; [exact Hige | exact Hij']. }
            assert (Hlt : (nth i orig 0%nat < nth j orig 0%nat)%nat) by (apply (Hsorted i j); [exact Hilt | exact Hjlen]).
            rewrite <- Hh in Hlt. lia.
        }
        destruct (Nat.ltb_spec h (nth i orig 0%nat)) as [Hhlt | Hhge].
        -- (* h < n_i *)
           assert (Hh2 : (2 <= h)%nat).
           { rewrite Hh. apply (Hge2 j). exact Hjlen. }
           rewrite (row_sum_frac_aux_step_lt orig h y tl' i j num0 den0 Hjni Hhlt).
           rewrite (IH (frac_add num0 den0 (pair_num h (nth i orig 0%nat)) (pair_den h (nth i orig 0%nat))) (S j) (Nat.lt_0_succ _) Hsuf' Hnth'
                 (frac_add_snd_neq0 _ _ _ _ Hden0
                    (pair_den_neq0 h (nth i orig 0%nat) Hh2 Hhlt)) Hge2 Hsorted Hi).
           rewrite (frac_add_R' num0 den0 (pair_num h (nth i orig 0%nat)) (pair_den h (nth i orig 0%nat)) Hden0
                    (pair_den_neq0 h (nth i orig 0%nat) Hh2 Hhlt)).
           replace (Nat.pred (length (y :: tl'))) with (length tl') by reflexivity.
           replace (Nat.pred (length (h :: y :: tl'))) with (S (length tl')) by reflexivity.
           rewrite sum_f_R0_shift.
           rewrite (Nat.add_0_r j).
           rewrite <- Hh.
           rewrite (pair_frac_R_min orig h i Hhlt).
           rewrite (proj2 (Nat.eqb_neq j i) Hjni).
           simpl.
           rewrite <- Rplus_assoc.
           f_equal.
           apply sum_f_R0_ext.
           intros k Hk.
           rewrite Nat.add_succ_r.
           reflexivity.
        -- (* h >= n_i 且 h ≠ n_i ⟹ h > n_i *)
           assert (Hhgt : (nth i orig 0%nat < h)%nat) by lia.
           rewrite (row_sum_frac_aux_step_ge orig h y tl' i j num0 den0 Hjni Hhge Hhgt).
           rewrite (IH (frac_add num0 den0 (pair_num (nth i orig 0%nat) h) (pair_den (nth i orig 0%nat) h)) (S j) (Nat.lt_0_succ _) Hsuf' Hnth'
                 (frac_add_snd_neq0 _ _ _ _ Hden0
                    (pair_den_neq0 (nth i orig 0%nat) h (Hge2 i Hi) Hhgt)) Hge2 Hsorted Hi).
           rewrite (frac_add_R' num0 den0 (pair_num (nth i orig 0%nat) h) (pair_den (nth i orig 0%nat) h) Hden0
                    (pair_den_neq0 (nth i orig 0%nat) h (Hge2 i Hi) Hhgt)).
           replace (Nat.pred (length (y :: tl'))) with (length tl') by reflexivity.
           replace (Nat.pred (length (h :: y :: tl'))) with (S (length tl')) by reflexivity.
           rewrite sum_f_R0_shift.
           rewrite (Nat.add_0_r j).
           rewrite <- Hh.
           rewrite (pair_frac_R_max orig h i Hhgt).
           rewrite (proj2 (Nat.eqb_neq j i) Hjni).
           simpl.
           rewrite <- Rplus_assoc.
           f_equal.
           apply sum_f_R0_ext.
           intros k Hk.
           rewrite Nat.add_succ_r.
           reflexivity.
Qed.

(* ============ 步骤 C：逐对内积范数 ≤ 反射对界（对称化 pair_inner_frac_bound） ============ *)
Lemma pair_inner_frac_bound (a b N : nat) :
  (2 <= a)%nat -> (2 <= b)%nat -> a <> b -> (Nat.min a b <= N)%nat ->
  Cnorm (Csum (fun k => psi a k *c Cconj (psi b k)) N)
  <= pair_frac_R a b.
Proof.
  intros Ha Hb Hne HN.
  unfold pair_frac_R.
  destruct (Nat.lt_ge_cases a b) as [Hab | Hba].
  - (* a < b：min = a, max = b，再 pair_bound_ok a b N *)
    rewrite (Nat.min_l a b) by lia.
    rewrite (Nat.max_r a b) by lia.
    apply pair_bound_ok.
    + exact Ha.
    + exact Hab.
    + rewrite (Nat.min_l a b) in HN by lia. exact HN.
    + apply pair_ok_ge2; assumption.
  - (* b <= a 且 a <> b ⟹ b < a：Cnorm_Csum_conj_sym 交换后 pair_bound_ok b a N *)
    assert (Hba' : (b < a)%nat) by lia.
    rewrite (Cnorm_Csum_conj_sym (fun k => psi a k) (fun k => psi b k) N).
    rewrite (Nat.min_r a b) by lia.
    rewrite (Nat.max_l a b) by lia.
    apply pair_bound_ok.
    + exact Hb.
    + exact Hba'.
    + rewrite (Nat.min_r a b) in HN by lia. exact HN.
    + apply pair_ok_ge2; assumption.
Qed.

(* eq_nat_dec 与 Nat.eqb 在 if 中等价（用于对齐 gershgorin 前提与 row_sum_frac_aux_R） *)
Lemma if_eq_nat_dec_eqb (i k : nat) (X Y : R) :
  (if eq_nat_dec i k then X else Y) = (if Nat.eqb i k then X else Y).
Proof.
  destruct (Nat.eqb_spec i k) as [He | Hne].
  - subst. destruct (eq_nat_dec k k) as [| Hnn]; [reflexivity | exfalso; apply Hnn; reflexivity].
  - destruct (eq_nat_dec i k) as [Heq | Hnn]; [exfalso; apply Hne; exact Heq | reflexivity].
Qed.

(* all_rows_le I I 0 = true ⟹ 每行 row_le_4_5 (row_sum_frac I p) = true *)
Lemma all_rows_le_forall (I orig : list nat) (idx : nat) :
  all_rows_le I orig idx = true ->
  forall p, (p < length I)%nat -> row_le_4_5 (row_sum_frac orig (idx + p)) = true.
Proof.
  revert idx.
  induction I as [| h tl IH]; intros idx Hr p Hp; simpl in Hp; [lia |].
  simpl in Hr.
  destruct (andb_prop _ _ Hr) as [Hh Ht].
  destruct p as [| p'].
  - rewrite (Nat.add_0_r idx). exact Hh.
  - rewrite (Nat.add_succ_r idx p').
    apply (IH (S idx) Ht p').
    simpl in Hp. lia.
Qed.

(* row_sum_frac 分母恒正（构造不变式：初值 1，每步乘正 pair_den） *)
Lemma row_sum_frac_aux_snd_pos (I orig : list nat) (i j : nat) (acc : nat_pair) :
  (j + length I <= length orig)%nat ->
  (i < length orig)%nat ->
  (snd acc > 0)%nat ->
  (forall k, (k < length I)%nat -> nth k I 0%nat = nth (j + k) orig 0%nat) ->
  (forall k, (k < length orig)%nat -> (2 <= nth k orig 0)%nat) ->
  (forall k1 k2, (k1 < k2)%nat -> (k2 < length orig)%nat -> (nth k1 orig 0 < nth k2 orig 0)%nat) ->
  (snd (row_sum_frac_aux I orig i acc j) > 0)%nat.
Proof.
  intros Hsuf Hilen Hacc Hnth Hge2 Hsorted.
  revert j Hsuf Hnth acc Hacc.
  induction I as [| h tl IH]; intros j Hsuf Hnth acc Hacc; simpl; [exact Hacc |].
  assert (Hlen' : (0 < length (h :: tl))%nat) by (simpl; lia).
  assert (Hjlen : (j < length orig)%nat).
  { apply Nat.lt_le_trans with (j + length (h :: tl))%nat; [lia | exact Hsuf]. }
  assert (Hnth_tl : forall k : nat, (k < length tl)%nat -> nth k tl 0%nat = nth (S j + k) orig 0%nat).
  { intros k Hk.
    assert (Hk' : (S k < length (h :: tl))%nat).
    { exact (proj1 (Nat.succ_lt_mono k (length tl)) Hk). }
    pose proof (Hnth (S k) Hk') as HnthS.
    simpl in HnthS.
    rewrite Nat.add_succ_r in HnthS.
    exact HnthS.
  }
  destruct acc as [num0 den0].
  simpl.
  destruct (Nat.eqb_spec j i) as [Hji | Hjni]; simpl.
  - apply IH; [simpl in Hsuf; lia | exact Hnth_tl | exact Hacc].
  - destruct (Nat.ltb_spec h (nth i orig 0%nat)) as [Hlt | Hge].
    + (* h < n_i *)
      assert (Hh2 : (2 <= h)%nat).
      { pose proof (Hnth 0%nat (Nat.lt_0_succ _)) as Hh0.
        simpl in Hh0. rewrite Nat.add_0_r in Hh0.
        rewrite Hh0. apply (Hge2 j). exact Hjlen. }
      assert (Hpd : (0 < pair_den h (nth i orig 0%nat))%nat) by (apply pair_den_pos; [exact Hh2 | exact Hlt]).
      apply IH; [simpl in Hsuf; lia | exact Hnth_tl |].
      unfold frac_add, snd.
      apply Nat.mul_pos_pos; [exact Hacc | exact Hpd].
    + (* h >= n_i 且 h ≠ n_i ⟹ n_i < h *)
      assert (Hni2 : (2 <= nth i orig 0%nat)%nat) by (apply (Hge2 i); exact Hilen).
      assert (Hh : h = nth j orig 0%nat).
      { pose proof (Hnth 0%nat (Nat.lt_0_succ _)) as Hh0.
        simpl in Hh0. rewrite Nat.add_0_r in Hh0. exact Hh0. }
      assert (Hhne : h <> nth i orig 0%nat).
      { intro Heq.
        destruct (Nat.lt_ge_cases j i) as [Hjlt | Hige].
        - assert (Hlt : (nth j orig 0%nat < nth i orig 0%nat)%nat) by (apply (Hsorted j i); [exact Hjlt | exact Hilen]).
          rewrite <- Hh in Hlt. lia.
        - assert (Hij' : (i <> j)%nat) by (exact (fun Hij => Hjni (sym_eq Hij))).
          assert (Hilt : (i < j)%nat).
          { apply (proj2 (Nat.le_neq i j)). split; [exact Hige | exact Hij']. }
          assert (Hlt : (nth i orig 0%nat < nth j orig 0%nat)%nat) by (apply (Hsorted i j); [exact Hilt | exact Hjlen]).
          rewrite <- Hh in Hlt. lia.
      }
      assert (Hhgt : (nth i orig 0%nat < h)%nat) by lia.
      assert (Hpd : (0 < pair_den (nth i orig 0%nat) h)%nat) by (apply pair_den_pos; [exact Hni2 | exact Hhgt]).
      apply IH; [simpl in Hsuf; lia | exact Hnth_tl |].
      unfold frac_add, snd.
      apply Nat.mul_pos_pos; [exact Hacc | exact Hpd].
Qed.

Lemma row_sum_frac_den_neq0 (I : list nat) (i : nat) :
  (i < length I)%nat ->
  (forall k, (k < length I)%nat -> (2 <= nth k I 0%nat)%nat) ->
  (forall k1 k2, (k1 < k2)%nat -> (k2 < length I)%nat -> (nth k1 I 0 < nth k2 I 0)%nat) ->
  (snd (row_sum_frac I i) <> 0%nat).
Proof.
  intros Hi Hge2 Hsorted. unfold row_sum_frac.
  assert (Hpos : (snd (row_sum_frac_aux I I i (0%nat,1%nat) 0%nat) > 0)%nat).
  { apply row_sum_frac_aux_snd_pos.
    - lia.
    - exact Hi.
    - simpl. lia.
    - intros k Hk. rewrite Nat.add_0_l. reflexivity.
    - exact Hge2.
    - exact Hsorted. }
  apply Nat.neq_0_lt_0. exact Hpos.
Qed.

(* row_sum_frac 的 R 层值 = 逐对 pair_frac_R 之和（对角项跳过） *)
Lemma row_sum_frac_R_value (I : list nat) (i : nat) :
  (0 < length I)%nat ->
  (forall k, (k < length I)%nat -> (2 <= nth k I 0%nat)%nat) ->
  sorted_strict_aux I = true ->
  (i < length I)%nat ->
  sum_f_R0 (fun k => if Nat.eqb k i then 0%R else
     pair_frac_R (nth i I 0%nat) (nth k I 0%nat)) (Nat.pred (length I))
  = INR (fst (row_sum_frac I i)) / INR (snd (row_sum_frac I i)).
Proof.
  intros Hlen Hg Hs Hi.
  unfold row_sum_frac.
  rewrite (row_sum_frac_aux_R I I i (0%nat,1%nat) 0%nat).
  - assert (Hx0 : (INR (fst (0%nat,1%nat)) / INR (snd (0%nat,1%nat)) = 0%R)).
    { simpl. unfold Rdiv. rewrite Rmult_0_l. reflexivity. }
    rewrite Hx0.
    simpl.
    rewrite Rplus_0_l.
    reflexivity.
  - exact Hlen.
  - lia. (* j + length I = 0 + length I <= length I *)
  - intros k Hk. rewrite Nat.add_0_l. reflexivity.
  - simpl. lia. (* snd (0,1) <> 0 *)
  - exact Hg.
  - exact (sorted_nth_lt I Hs).
  - exact Hi.
Qed.

(* ============ 主定理装配：每行 R 层行和 ≤ 4/5 ============ *)
Lemma frame_check_instance_row_bound (I : list nat) (i : nat) :
  (0 < length I)%nat ->
  frame_check_instance I = true ->
  (i < length I)%nat ->
  sum_f_R0 (fun j => if eq_nat_dec i j then 0%R else
     Cnorm (Csum (fun k => psi (nth i I 0%nat) k *c Cconj (psi (nth j I 0%nat) k)) (last I 0%nat)))
  (Nat.pred (length I)) <= 4/5.
Proof.
  intros Hlen Hfc Hi.
  unfold frame_check_instance in Hfc.
  apply andb_true_iff in Hfc. destruct Hfc as [Hs Hfc1].
  apply andb_true_iff in Hfc1. destruct Hfc1 as [Hg Hfc2].
  apply andb_true_iff in Hfc2. destruct Hfc2 as [Hp Hr].
  (* eq_nat_dec 和式改写为 Nat.eqb 和式（与 row_sum_frac_aux_R 一致） *)
  rewrite (sum_f_R0_ext
           (fun j => if eq_nat_dec i j then 0%R else
              Cnorm (Csum (fun k => psi (nth i I 0%nat) k *c Cconj (psi (nth j I 0%nat) k)) (last I 0%nat)))
           (fun j => if Nat.eqb i j then 0%R else
              Cnorm (Csum (fun k => psi (nth i I 0%nat) k *c Cconj (psi (nth j I 0%nat) k)) (last I 0%nat)))
           (Nat.pred (length I))).
  - apply Rle_trans with
      (sum_f_R0 (fun j => if Nat.eqb i j then 0%R else
         pair_frac_R (nth i I 0%nat) (nth j I 0%nat)) (Nat.pred (length I))).
    + (* (a)+(b): 每对 Cnorm ≤ pair_frac_R，累加 ≤ 分数和 *)
      apply sum_f_R0_le_compat.
      * intros j Hj.
        destruct (Nat.eqb_spec i j) as [Heq | Hne].
        -- simpl. apply Rle_refl.
        -- assert (Hjlt : (j < length I)%nat) by (apply Nat.le_lt_trans with (Nat.pred (length I)); [exact Hj | lia]).
           assert (Hij : nth i I 0%nat <> nth j I 0%nat).
           { destruct (Nat.lt_ge_cases i j) as [Hilt | Hjge].
             - intro Heq.
               assert (Hlt0 : (nth i I 0%nat < nth j I 0%nat)%nat) by (apply (sorted_nth_lt I Hs i j); [lia | exact Hjlt]).
               rewrite Heq in Hlt0. lia.
             - intro Heq.
               assert (Hlt0 : (nth j I 0%nat < nth i I 0%nat)%nat) by (apply (sorted_nth_lt I Hs j i); [lia | exact Hi]).
               rewrite Heq in Hlt0. lia. }
           apply pair_inner_frac_bound.
           ++ apply all_ge_2_nth with (i := i); [exact Hg | exact Hi].
           ++ apply all_ge_2_nth with (i := j); [exact Hg | exact Hjlt].
           ++ exact Hij.
           ++ apply Nat.le_trans with (nth i I 0%nat); [apply Nat.le_min_l | apply (nth_le_last I Hs i Hi)].
      + (* (c): 分数和 = row_sum_frac R 值 ≤ 4/5 *)
        rewrite (sum_f_R0_ext
                 (fun j => if Nat.eqb i j then 0%R else pair_frac_R (nth i I 0%nat) (nth j I 0%nat))
                 (fun j => if Nat.eqb j i then 0%R else pair_frac_R (nth i I 0%nat) (nth j I 0%nat))
                 (Nat.pred (length I))).
        - rewrite (row_sum_frac_R_value I i Hlen (all_ge_2_nth I Hg) Hs Hi).
          apply row_le_R.
          * apply row_sum_frac_den_neq0; [exact Hi | exact (all_ge_2_nth I Hg) | exact (sorted_nth_lt I Hs)].
          * pose proof (all_rows_le_forall I I 0%nat Hr i Hi) as Hr4.
            unfold row_le_4_5 in Hr4.
            apply Nat.leb_le in Hr4. exact Hr4.
        - intros j Hj. rewrite Nat.eqb_sym. reflexivity.
  - intros j Hj. apply if_eq_nat_dec_eqb.
Qed.

(* ============ frame_check_instance_sound 主定理 (e) gershgorin_frame_mu 通用实例化 ============ *)
Theorem frame_check_instance_sound (I : list nat) :
  (0 < length I)%nat ->
  frame_check_instance I = true ->
  forall coeffs : list Complex,
  length coeffs = length I ->
  let n := length I in
  let M := S (last I 0%nat) in
  let phi := fun i k => psi (nth i I 0%nat) k in
  let F := fun k => Csum (fun i => nth i coeffs C0 *c phi i k) n in
  let S := sum_f_R0 (fun i => Cnorm_sq (nth i coeffs C0)) (Nat.pred n) in
  ((1 - 4 / 5) * S <= l2_norm_sq F (Nat.pred M) <= (1 + 4 / 5) * S)%R.
Proof.
  intros Hlen Hfc0 coeffs Hlencoeffs.
  unfold frame_check_instance in Hfc0.
  apply andb_true_iff in Hfc0. destruct Hfc0 as [Hs Hfc1].
  apply andb_true_iff in Hfc1. destruct Hfc1 as [Hg Hfc2].
  apply andb_true_iff in Hfc2. destruct Hfc2 as [Hp Hr].
  cbv zeta.
  apply (gershgorin_frame_mu (length I) (fun i k => psi (nth i I 0%nat) k) (S (last I 0%nat)) (4/5)).
  - (* M = S (last I 0%nat) > 0 *)
    apply Nat.lt_0_succ.
  - (* 零化高于窗口：k >= Nat.pred M = last I 0 ⟹ psi (nth i I) k = C0 *)
    intros i k Hi Hk.
    apply psi_ge_n_zero.
    pose proof (nth_le_last I Hs i Hi) as Hle. lia.
  - (* 每行单位范数：l2_norm_sq (psi (nth i I)) (Nat.pred M) = 1 *)
    intros i Hi.
    apply psi_unit_norm.
    + apply all_ge_2_nth with (i := i); [exact Hg | exact Hi].
    + pose proof (nth_le_last I Hs i Hi) as Hle. lia.
  - (* 每行非对角范数和 ≤ 4/5 *)
    intros i Hi.
    apply frame_check_instance_row_bound; [exact Hlen | | exact Hi].
    unfold frame_check_instance.
    apply andb_true_iff. split; [exact Hs |].
    apply andb_true_iff. split; [exact Hg |].
    apply andb_true_iff. split; [exact Hp | exact Hr].
  - exact Hlencoeffs.
Qed.

End FrameCheckInstance.

(* ============================================================
   Module ChampionCertificate（会话 14 E5'' 复合证书）
   七带 [3,7,15,31,63,127,255] 输出平方范数的复合界：
     (S - coh) <= l2_norm_sq F 255 <= (S + coh)
   依赖：T8CoreCertificate 6 个 pair 界 + InstanceCertificate
         psi_inner_cons_bound/cons_bound_floor + 新增 15 个 pair 界
   零 classic（审计：ClassicalDedekindReals/FunctionalExtensionality
   为 Stdlib Reals 构造基底公理，与 3D/4D 审计一致）。
   ============================================================ *)
Module ChampionCertificate.
Import ExtendedTheorems.
Import InstanceCertificate.
Import T8CoreCertificate.
Import UnconditionalBasisLemmas.
(* ---- 交叉对（核 × 边带） ---- *)
Lemma pair_3_7 (N : nat) : (3 <= N)%nat ->
  Cnorm (Csum (fun k => psi 3 k *c Cconj (psi 7 k)) N) <= 21 / 32.
Proof.
  intros HN.
  apply Rle_trans with (1 / (2 * (1 / INR 3 - 1 / INR 7) * sqrt (INR 3 * INR 7))).
  - apply psi_inner_cons_bound; lia.
  - apply Rle_trans with (INR 3 * INR 7 / (2 * INR (7 - 3) * INR 4)).
    + apply cons_bound_floor.
      * lia. * lia. * lia.
      * rewrite <- (mult_INR 3 7). apply INR_sqrt_le. lia.
      * apply lt_0_INR. lia.
    + replace (INR 3 * INR 7 / (2 * INR (7 - 3) * INR 4)) with (21 / 32) by (compute; field).
      apply Rle_refl.
Qed.

Lemma pair_3_31 (N : nat) : (3 <= N)%nat ->
  Cnorm (Csum (fun k => psi 3 k *c Cconj (psi 31 k)) N) <= 31 / 168.
Proof.
  intros HN.
  apply Rle_trans with (1 / (2 * (1 / INR 3 - 1 / INR 31) * sqrt (INR 3 * INR 31))).
  - apply psi_inner_cons_bound; lia.
  - apply Rle_trans with (INR 3 * INR 31 / (2 * INR (31 - 3) * INR 9)).
    + apply cons_bound_floor.
      * lia. * lia. * lia.
      * rewrite <- (mult_INR 3 31). apply INR_sqrt_le. lia.
      * apply lt_0_INR. lia.
    + replace (INR 3 * INR 31 / (2 * INR (31 - 3) * INR 9)) with (31 / 168) by (compute; field).
      apply Rle_refl.
Qed.

Lemma pair_3_127 (N : nat) : (3 <= N)%nat ->
  Cnorm (Csum (fun k => psi 3 k *c Cconj (psi 127 k)) N) <= 381 / 4712.
Proof.
  intros HN.
  apply Rle_trans with (1 / (2 * (1 / INR 3 - 1 / INR 127) * sqrt (INR 3 * INR 127))).
  - apply psi_inner_cons_bound; lia.
  - apply Rle_trans with (INR 3 * INR 127 / (2 * INR (127 - 3) * INR 19)).
    + apply cons_bound_floor.
      * lia. * lia. * lia.
      * rewrite <- (mult_INR 3 127). apply INR_sqrt_le. lia.
      * apply lt_0_INR. lia.
    + replace (INR 3 * INR 127 / (2 * INR (127 - 3) * INR 19)) with (381 / 4712) by (compute; field).
      apply Rle_refl.
Qed.

Lemma pair_7_15 (N : nat) : (7 <= N)%nat ->
  Cnorm (Csum (fun k => psi 7 k *c Cconj (psi 15 k)) N) <= 21 / 32.
Proof.
  intros HN.
  apply Rle_trans with (1 / (2 * (1 / INR 7 - 1 / INR 15) * sqrt (INR 7 * INR 15))).
  - apply psi_inner_cons_bound; lia.
  - apply Rle_trans with (INR 7 * INR 15 / (2 * INR (15 - 7) * INR 10)).
    + apply cons_bound_floor.
      * lia. * lia. * lia.
      * rewrite <- (mult_INR 7 15). apply INR_sqrt_le. lia.
      * apply lt_0_INR. lia.
    + replace (INR 7 * INR 15 / (2 * INR (15 - 7) * INR 10)) with (21 / 32) by (compute; field).
      apply Rle_refl.
Qed.

Lemma pair_7_63 (N : nat) : (7 <= N)%nat ->
  Cnorm (Csum (fun k => psi 7 k *c Cconj (psi 63 k)) N) <= 3 / 16.
Proof.
  intros HN.
  apply Rle_trans with (1 / (2 * (1 / INR 7 - 1 / INR 63) * sqrt (INR 7 * INR 63))).
  - apply psi_inner_cons_bound; lia.
  - apply Rle_trans with (INR 7 * INR 63 / (2 * INR (63 - 7) * INR 21)).
    + apply cons_bound_floor.
      * lia. * lia. * lia.
      * rewrite <- (mult_INR 7 63). apply INR_sqrt_le. lia.
      * apply lt_0_INR. lia.
    + replace (INR 7 * INR 63 / (2 * INR (63 - 7) * INR 21)) with (3 / 16) by (compute; field).
      apply Rle_refl.
Qed.

Lemma pair_7_127 (N : nat) : (7 <= N)%nat ->
  Cnorm (Csum (fun k => psi 7 k *c Cconj (psi 127 k)) N) <= 889 / 6960.
Proof.
  intros HN.
  apply Rle_trans with (1 / (2 * (1 / INR 7 - 1 / INR 127) * sqrt (INR 7 * INR 127))).
  - apply psi_inner_cons_bound; lia.
  - apply Rle_trans with (INR 7 * INR 127 / (2 * INR (127 - 7) * INR 29)).
    + apply cons_bound_floor.
      * lia. * lia. * lia.
      * rewrite <- (mult_INR 7 127). apply INR_sqrt_le. lia.
      * apply lt_0_INR. lia.
    + replace (INR 7 * INR 127 / (2 * INR (127 - 7) * INR 29)) with (889 / 6960) by (compute; field).
      apply Rle_refl.
Qed.

Lemma pair_7_255 (N : nat) : (7 <= N)%nat ->
  Cnorm (Csum (fun k => psi 7 k *c Cconj (psi 255 k)) N) <= 85 / 992.
Proof.
  intros HN.
  apply Rle_trans with (1 / (2 * (1 / INR 7 - 1 / INR 255) * sqrt (INR 7 * INR 255))).
  - apply psi_inner_cons_bound; lia.
  - apply Rle_trans with (INR 7 * INR 255 / (2 * INR (255 - 7) * INR 42)).
    + apply cons_bound_floor.
      * lia. * lia. * lia.
      * rewrite <- (mult_INR 7 255). apply INR_sqrt_le. lia.
      * apply lt_0_INR. lia.
    + replace (INR 7 * INR 255 / (2 * INR (255 - 7) * INR 42)) with (85 / 992) by (compute; field).
      apply Rle_refl.
Qed.

Lemma pair_15_31 (N : nat) : (15 <= N)%nat ->
  Cnorm (Csum (fun k => psi 15 k *c Cconj (psi 31 k)) N) <= 155 / 224.
Proof.
  intros HN.
  apply Rle_trans with (1 / (2 * (1 / INR 15 - 1 / INR 31) * sqrt (INR 15 * INR 31))).
  - apply psi_inner_cons_bound; lia.
  - apply Rle_trans with (INR 15 * INR 31 / (2 * INR (31 - 15) * INR 21)).
    + apply cons_bound_floor.
      * lia. * lia. * lia.
      * rewrite <- (mult_INR 15 31). apply INR_sqrt_le. lia.
      * apply lt_0_INR. lia.
    + replace (INR 15 * INR 31 / (2 * INR (31 - 15) * INR 21)) with (155 / 224) by (compute; field).
      apply Rle_refl.
Qed.

Lemma pair_15_127 (N : nat) : (15 <= N)%nat ->
  Cnorm (Csum (fun k => psi 15 k *c Cconj (psi 127 k)) N) <= 1905 / 9632.
Proof.
  intros HN.
  apply Rle_trans with (1 / (2 * (1 / INR 15 - 1 / INR 127) * sqrt (INR 15 * INR 127))).
  - apply psi_inner_cons_bound; lia.
  - apply Rle_trans with (INR 15 * INR 127 / (2 * INR (127 - 15) * INR 43)).
    + apply cons_bound_floor.
      * lia. * lia. * lia.
      * rewrite <- (mult_INR 15 127). apply INR_sqrt_le. lia.
      * apply lt_0_INR. lia.
    + replace (INR 15 * INR 127 / (2 * INR (127 - 15) * INR 43)) with (1905 / 9632) by (compute; field).
      apply Rle_refl.
Qed.

(* ---- 边带内对 ---- *)
Lemma pair_7_31 (N : nat) : (7 <= N)%nat ->
  Cnorm (Csum (fun k => psi 7 k *c Cconj (psi 31 k)) N) <= 217 / 672.
Proof.
  intros HN.
  apply Rle_trans with (1 / (2 * (1 / INR 7 - 1 / INR 31) * sqrt (INR 7 * INR 31))).
  - apply psi_inner_cons_bound; lia.
  - apply Rle_trans with (INR 7 * INR 31 / (2 * INR (31 - 7) * INR 14)).
    + apply cons_bound_floor.
      * lia. * lia. * lia.
      * rewrite <- (mult_INR 7 31). apply INR_sqrt_le. lia.
      * apply lt_0_INR. lia.
    + replace (INR 7 * INR 31 / (2 * INR (31 - 7) * INR 14)) with (217 / 672) by (compute; field).
      apply Rle_refl.
Qed.

Lemma pair_31_63 (N : nat) : (31 <= N)%nat ->
  Cnorm (Csum (fun k => psi 31 k *c Cconj (psi 63 k)) N) <= 1953 / 2816.
Proof.
  intros HN.
  apply Rle_trans with (1 / (2 * (1 / INR 31 - 1 / INR 63) * sqrt (INR 31 * INR 63))).
  - apply psi_inner_cons_bound; lia.
  - apply Rle_trans with (INR 31 * INR 63 / (2 * INR (63 - 31) * INR 44)).
    + apply cons_bound_floor.
      * lia. * lia. * lia.
      * rewrite <- (mult_INR 31 63). apply INR_sqrt_le. lia.
      * apply lt_0_INR. lia.
    + replace (INR 31 * INR 63 / (2 * INR (63 - 31) * INR 44)) with (1953 / 2816) by (compute; field).
      apply Rle_refl.
Qed.

Lemma pair_31_127 (N : nat) : (31 <= N)%nat ->
  Cnorm (Csum (fun k => psi 31 k *c Cconj (psi 127 k)) N) <= 3937 / 11904.
Proof.
  intros HN.
  apply Rle_trans with (1 / (2 * (1 / INR 31 - 1 / INR 127) * sqrt (INR 31 * INR 127))).
  - apply psi_inner_cons_bound; lia.
  - apply Rle_trans with (INR 31 * INR 127 / (2 * INR (127 - 31) * INR 62)).
    + apply cons_bound_floor.
      * lia. * lia. * lia.
      * rewrite <- (mult_INR 31 127). apply INR_sqrt_le. lia.
      * apply lt_0_INR. lia.
    + replace (INR 31 * INR 127 / (2 * INR (127 - 31) * INR 62)) with (3937 / 11904) by (compute; field).
      apply Rle_refl.
Qed.

Lemma pair_31_255 (N : nat) : (31 <= N)%nat ->
  Cnorm (Csum (fun k => psi 31 k *c Cconj (psi 255 k)) N) <= 7905 / 39424.
Proof.
  intros HN.
  apply Rle_trans with (1 / (2 * (1 / INR 31 - 1 / INR 255) * sqrt (INR 31 * INR 255))).
  - apply psi_inner_cons_bound; lia.
  - apply Rle_trans with (INR 31 * INR 255 / (2 * INR (255 - 31) * INR 88)).
    + apply cons_bound_floor.
      * lia. * lia. * lia.
      * rewrite <- (mult_INR 31 255). apply INR_sqrt_le. lia.
      * apply lt_0_INR. lia.
    + replace (INR 31 * INR 255 / (2 * INR (255 - 31) * INR 88)) with (7905 / 39424) by (compute; field).
      apply Rle_refl.
Qed.

Lemma pair_63_127 (N : nat) : (63 <= N)%nat ->
  Cnorm (Csum (fun k => psi 63 k *c Cconj (psi 127 k)) N) <= 8001 / 11392.
Proof.
  intros HN.
  apply Rle_trans with (1 / (2 * (1 / INR 63 - 1 / INR 127) * sqrt (INR 63 * INR 127))).
  - apply psi_inner_cons_bound; lia.
  - apply Rle_trans with (INR 63 * INR 127 / (2 * INR (127 - 63) * INR 89)).
    + apply cons_bound_floor.
      * lia. * lia. * lia.
      * rewrite <- (mult_INR 63 127). apply INR_sqrt_le. lia.
      * apply lt_0_INR. lia.
    + replace (INR 63 * INR 127 / (2 * INR (127 - 63) * INR 89)) with (8001 / 11392) by (compute; field).
      apply Rle_refl.
Qed.

Lemma pair_127_255 (N : nat) : (127 <= N)%nat ->
  Cnorm (Csum (fun k => psi 127 k *c Cconj (psi 255 k)) N) <= 32385 / 45824.
Proof.
  intros HN.
  apply Rle_trans with (1 / (2 * (1 / INR 127 - 1 / INR 255) * sqrt (INR 127 * INR 255))).
  - apply psi_inner_cons_bound; lia.
  - apply Rle_trans with (INR 127 * INR 255 / (2 * INR (255 - 127) * INR 179)).
    + apply cons_bound_floor.
      * lia. * lia. * lia.
      * rewrite <- (mult_INR 127 255). apply INR_sqrt_le. lia.
      * apply lt_0_INR. lia.
    + replace (INR 127 * INR 255 / (2 * INR (255 - 127) * INR 179)) with (32385 / 45824) by (compute; field).
      apply Rle_refl.
Qed.

(* ============================================================
   E5'' 复合证书：顶层定理（全矩阵相干加权版本）
   e5_bands = [3,7,15,31,63,127,255]（索引 0..6）
   δ 表 = 21 对上三角相干界（6 核内 T8 + 15 新对，双方向定义）
   ============================================================ *)

(* 对角内积 = 1（窗口 M ≥ n 时） *)
Lemma inner_diag_one : forall n M : nat, (n >= 2)%nat -> (n <= M)%nat ->
  Csum (fun k => psi n k *c Cconj (psi n k)) M = Cof_real 1.
Proof.
  intros n M Hn2 HnM.
  assert (Heq : forall k, psi n k *c Cconj (psi n k) = Cof_real (Cnorm_sq (psi n k))).
  { intro k. symmetry. apply Cnorm_sq_Cof_real. }
  rewrite (Csum_ext' _ (fun k => Cof_real (Cnorm_sq (psi n k))) M).
  2: { intros k Hk. apply Heq. }
  destruct M as [|M'].
  - exfalso; lia.
  - rewrite <- (Cof_real_sum (fun k => Cnorm_sq (psi n k)) M').
    f_equal.
    assert (Hsum1 : sum_f_R0 (fun k => Cnorm_sq (psi n k)) (S M') = 1).
    { change (l2_norm_sq (fun k => psi n k) (S M') = 1); apply psi_unit_norm; assumption. }
    assert (HfM0 : Cnorm_sq (psi n (S M')) = 0).
    { rewrite (psi_ge_n_zero n (S M') HnM). apply Cnorm_sq_zero. }
    rewrite (sum_f_R0_S (fun k => Cnorm_sq (psi n k)) M') in Hsum1.
    rewrite HfM0 in Hsum1. lra.
Qed.

(* re z <= Cnorm z（下界用 -re z <= Cnorm z）——自证，不依赖 Local 引理 *)
Lemma re_le_cnorm : forall z : Complex, re z <= Cnorm z.
Proof.
  intros z.
  apply Rle_trans with (Rabs (re z)).
  - apply Rle_abs.
  - unfold Cnorm, Cnorm_sq.
    rewrite <- sqrt_Rsqr_abs.
    apply sqrt_le_1_c.
    + apply Rle_0_sqr.
    + apply Rplus_le_le_0_compat; apply Rle_0_sqr.
    + unfold Rsqr. nra.
Qed.

Lemma neg_re_le_cnorm : forall z : Complex, - re z <= Cnorm z.
Proof.
  intros z.
  apply Rle_trans with (Rabs (re z)).
  - unfold Rabs. destruct (Rcase_abs (re z)); lra.
  - unfold Cnorm, Cnorm_sq.
    rewrite <- sqrt_Rsqr_abs.
    apply sqrt_le_1_c.
    + apply Rle_0_sqr.
    + apply Rplus_le_le_0_compat; apply Rle_0_sqr.
    + unfold Rsqr. nra.
Qed.

(* Cnorm 非负（自证，避免跨库同名冲突） *)
Lemma cnorm_ge0 : forall z : Complex, 0 <= Cnorm z.
Proof. intros z; unfold Cnorm; apply sqrt_pos. Qed.

(* 非对角项上界：re (a *c Cconj b *c z) <= |a| |b| |z| *)
Lemma re_mul_le : forall a b z : Complex,
  re (a *c Cconj b *c z) <= Cnorm a * Cnorm b * Cnorm z.
Proof.
  intros a b z.
  eapply Rle_trans.
  - apply re_le_cnorm.
  - rewrite Cnorm_mult.
    rewrite (Cnorm_mult a (Cconj b)).
    rewrite Cnorm_conj_eq.
    lra.
Qed.

Lemma neg_re_mul_le : forall a b z : Complex,
  - re (a *c Cconj b *c z) <= Cnorm a * Cnorm b * Cnorm z.
Proof.
  intros a b z.
  eapply Rle_trans.
  - apply neg_re_le_cnorm.
  - rewrite Cnorm_mult.
    rewrite (Cnorm_mult a (Cconj b)).
    rewrite Cnorm_conj_eq.
    lra.
Qed.

(* E5'' 七带阶梯 *)
Definition e5_bands : list nat := 3%nat :: 7%nat :: 15%nat :: 31%nat :: 63%nat :: 127%nat :: 255%nat :: nil.

(* δ 表（双方向）：对 7 带索引 (i,j)（0..6 → 3,7,15,31,63,127,255） *)
Definition delta_e5 (i j : nat) : R :=
  match i, j with
  | 0,1 | 1,0 => 21/32          (* 3-7 *)
  | 0,2 | 2,0 => 5/16           (* 3-15，T8 *)
  | 0,3 | 3,0 => 31/168         (* 3-31 *)
  | 0,4 | 4,0 => 63/520         (* 3-63，T8 *)
  | 0,5 | 5,0 => 381/4712       (* 3-127 *)
  | 0,6 | 6,0 => 85/1512        (* 3-255，T8 *)
  | 1,2 | 2,1 => 21/32          (* 7-15 *)
  | 1,3 | 3,1 => 217/672        (* 7-31 *)
  | 1,4 | 4,1 => 3/16           (* 7-63 *)
  | 1,5 | 5,1 => 889/6960       (* 7-127 *)
  | 1,6 | 6,1 => 85/992         (* 7-255 *)
  | 2,3 | 3,2 => 155/224        (* 15-31 *)
  | 2,4 | 4,2 => 21/64          (* 15-63，T8 *)
  | 2,5 | 5,2 => 1905/9632      (* 15-127 *)
  | 2,6 | 6,2 => 255/1952       (* 15-255，T8 *)
  | 3,4 | 4,3 => 1953/2816      (* 31-63 *)
  | 3,5 | 5,3 => 3937/11904     (* 31-127 *)
  | 3,6 | 6,3 => 7905/39424     (* 31-255 *)
  | 4,5 | 5,4 => 8001/11392     (* 63-127 *)
  | 4,6 | 6,4 => 85/256         (* 63-255，T8 *)
  | 5,6 | 6,5 => 32385/45824    (* 127-255 *)
  | _, _ => 0%R
  end.

(* 每带值（nth e5_bands） *)
Lemma band_nth : forall i : nat,
  (i < 7)%nat ->
  nth i e5_bands 0%nat = match i with 0%nat => 3%nat | 1%nat => 7%nat | 2%nat => 15%nat
    | 3%nat => 31%nat | 4%nat => 63%nat | 5%nat => 127%nat | _ => 255%nat end.
Proof.
  intros i Hi. destruct i as [|[|[|[|[|[|[|i']]]]]]]; try lia; reflexivity.
Qed.

Lemma band_ge2 : forall i : nat, (i < 7)%nat -> (nth i e5_bands 0%nat >= 2)%nat.
Proof.
  intros i Hi. rewrite (band_nth i Hi).
  destruct i as [|[|[|[|[|[|[|i']]]]]]]; try lia; simpl; lia.
Qed.

Lemma band_le256 : forall i : nat, (i < 7)%nat -> (nth i e5_bands 0%nat <= 256)%nat.
Proof.
  intros i Hi. rewrite (band_nth i Hi).
  destruct i as [|[|[|[|[|[|[|i']]]]]]]; try lia; simpl; lia.
Qed.

(* 相干界：窗口 M=256（≥ 各带）下 Cnorm (⟨ψ_a,ψ_b⟩_M) <= δ *)
Lemma coh_delta_bound : forall i j : nat, (i < 7)%nat -> (j < 7)%nat -> i <> j ->
  Cnorm (Csum (fun k => psi (nth i e5_bands 0%nat) k *c Cconj (psi (nth j e5_bands 0%nat) k)) 256)
  <= delta_e5 i j.
Proof.
  intros i j Hi Hj Hne.
  rewrite (band_nth i Hi), (band_nth j Hj).
  destruct i as [|[|[|[|[|[|[|i']]]]]]]; try lia.
  all: destruct j as [|[|[|[|[|[|[|j']]]]]]]; try lia.
  all: try (exfalso; lia).
  (* 字典序 42 分支：i=0..6，j=0..6，i<>j *)
  - apply pair_3_7; lia.
  - apply pair_3_15; lia.
  - apply pair_3_31; lia.
  - apply pair_3_63; lia.
  - apply pair_3_127; lia.
  - apply pair_3_255; lia.
  - rewrite (ExtendedTheorems.Cnorm_Csum_conj_sym (fun k => psi 7 k) (fun k => psi 3 k) 256); apply pair_3_7; lia.
  - apply pair_7_15; lia.
  - apply pair_7_31; lia.
  - apply pair_7_63; lia.
  - apply pair_7_127; lia.
  - apply pair_7_255; lia.
  - rewrite (ExtendedTheorems.Cnorm_Csum_conj_sym (fun k => psi 15 k) (fun k => psi 3 k) 256); apply pair_3_15; lia.
  - rewrite (ExtendedTheorems.Cnorm_Csum_conj_sym (fun k => psi 15 k) (fun k => psi 7 k) 256); apply pair_7_15; lia.
  - apply pair_15_31; lia.
  - apply pair_15_63; lia.
  - apply pair_15_127; lia.
  - apply pair_15_255; lia.
  - rewrite (ExtendedTheorems.Cnorm_Csum_conj_sym (fun k => psi 31 k) (fun k => psi 3 k) 256); apply pair_3_31; lia.
  - rewrite (ExtendedTheorems.Cnorm_Csum_conj_sym (fun k => psi 31 k) (fun k => psi 7 k) 256); apply pair_7_31; lia.
  - rewrite (ExtendedTheorems.Cnorm_Csum_conj_sym (fun k => psi 31 k) (fun k => psi 15 k) 256); apply pair_15_31; lia.
  - apply pair_31_63; lia.
  - apply pair_31_127; lia.
  - apply pair_31_255; lia.
  - rewrite (ExtendedTheorems.Cnorm_Csum_conj_sym (fun k => psi 63 k) (fun k => psi 3 k) 256); apply pair_3_63; lia.
  - rewrite (ExtendedTheorems.Cnorm_Csum_conj_sym (fun k => psi 63 k) (fun k => psi 7 k) 256); apply pair_7_63; lia.
  - rewrite (ExtendedTheorems.Cnorm_Csum_conj_sym (fun k => psi 63 k) (fun k => psi 15 k) 256); apply pair_15_63; lia.
  - rewrite (ExtendedTheorems.Cnorm_Csum_conj_sym (fun k => psi 63 k) (fun k => psi 31 k) 256); apply pair_31_63; lia.
  - apply pair_63_127; lia.
  - apply pair_63_255; lia.
  - rewrite (ExtendedTheorems.Cnorm_Csum_conj_sym (fun k => psi 127 k) (fun k => psi 3 k) 256); apply pair_3_127; lia.
  - rewrite (ExtendedTheorems.Cnorm_Csum_conj_sym (fun k => psi 127 k) (fun k => psi 7 k) 256); apply pair_7_127; lia.
  - rewrite (ExtendedTheorems.Cnorm_Csum_conj_sym (fun k => psi 127 k) (fun k => psi 15 k) 256); apply pair_15_127; lia.
  - rewrite (ExtendedTheorems.Cnorm_Csum_conj_sym (fun k => psi 127 k) (fun k => psi 31 k) 256); apply pair_31_127; lia.
  - rewrite (ExtendedTheorems.Cnorm_Csum_conj_sym (fun k => psi 127 k) (fun k => psi 63 k) 256); apply pair_63_127; lia.
  - apply pair_127_255; lia.
  - rewrite (ExtendedTheorems.Cnorm_Csum_conj_sym (fun k => psi 255 k) (fun k => psi 3 k) 256); apply pair_3_255; lia.
  - rewrite (ExtendedTheorems.Cnorm_Csum_conj_sym (fun k => psi 255 k) (fun k => psi 7 k) 256); apply pair_7_255; lia.
  - rewrite (ExtendedTheorems.Cnorm_Csum_conj_sym (fun k => psi 255 k) (fun k => psi 15 k) 256); apply pair_15_255; lia.
  - rewrite (ExtendedTheorems.Cnorm_Csum_conj_sym (fun k => psi 255 k) (fun k => psi 31 k) 256); apply pair_31_255; lia.
  - rewrite (ExtendedTheorems.Cnorm_Csum_conj_sym (fun k => psi 255 k) (fun k => psi 63 k) 256); apply pair_63_255; lia.
  - rewrite (ExtendedTheorems.Cnorm_Csum_conj_sym (fun k => psi 255 k) (fun k => psi 127 k) 256); apply pair_127_255; lia.
Qed.

(* 逐项界：i=j 对角精确；i≠j 用 re 上界 *)
Lemma term_bound_upper : forall (c : nat -> Complex) (i j : nat),
  (i < 7)%nat -> (j < 7)%nat ->
  re (c i *c Cconj (c j) *c
      (Csum (fun k => psi (nth i e5_bands 0%nat) k *c Cconj (psi (nth j e5_bands 0%nat) k)) 256))
  <= if eq_nat_dec i j then Cnorm_sq (c i)
     else Cnorm (c i) * Cnorm (c j) * delta_e5 i j.
Proof.
  intros c i j Hi Hj.
  destruct (Nat.eq_dec i j) as [Heq | Hne].
  - subst j.
    rewrite (inner_diag_one (nth i e5_bands 0%nat) 256 (band_ge2 i Hi) (band_le256 i Hi)).
    change (Cof_real 1) with C1.
    rewrite Cmul_1_r.
    assert (Hdiag : c i *c Cconj (c i) = Cof_real (Cnorm_sq (c i))).
    { symmetry. apply Cnorm_sq_Cof_real. }
    rewrite Hdiag.
    simpl. reflexivity.
  - eapply Rle_trans.
    + apply re_le_cnorm.
    + rewrite (Cnorm_mult (c i *c Cconj (c j)) (Csum (fun k => psi (nth i e5_bands 0%nat) k *c Cconj (psi (nth j e5_bands 0%nat) k)) 256)).
      rewrite (Cnorm_mult (c i) (Cconj (c j))).
      rewrite Cnorm_conj_eq.
      apply Rmult_le_compat_l.
      * apply Rmult_le_pos; apply cnorm_ge0.
      * apply coh_delta_bound; assumption.
Qed.

(* 逐项界（下界）：i=j 精确；i≠j 用 -re 上界 *)
Lemma term_bound_lower : forall (c : nat -> Complex) (i j : nat),
  (i < 7)%nat -> (j < 7)%nat ->
  - re (c i *c Cconj (c j) *c
       (Csum (fun k => psi (nth i e5_bands 0%nat) k *c Cconj (psi (nth j e5_bands 0%nat) k)) 256))
  <= if eq_nat_dec i j then - Cnorm_sq (c i)
     else Cnorm (c i) * Cnorm (c j) * delta_e5 i j.
Proof.
  intros c i j Hi Hj.
  destruct (Nat.eq_dec i j) as [Heq | Hne].
  - subst j.
    rewrite (inner_diag_one (nth i e5_bands 0%nat) 256 (band_ge2 i Hi) (band_le256 i Hi)).
    change (Cof_real 1) with C1.
    rewrite Cmul_1_r.
    assert (Hdiag : c i *c Cconj (c i) = Cof_real (Cnorm_sq (c i))).
    { symmetry. apply Cnorm_sq_Cof_real. }
    rewrite Hdiag.
    simpl. reflexivity.
  - eapply Rle_trans.
    + apply neg_re_le_cnorm.
    + rewrite (Cnorm_mult (c i *c Cconj (c j)) (Csum (fun k => psi (nth i e5_bands 0%nat) k *c Cconj (psi (nth j e5_bands 0%nat) k)) 256)).
      rewrite (Cnorm_mult (c i) (Cconj (c j))).
      rewrite Cnorm_conj_eq.
      apply Rmult_le_compat_l.
      * apply Rmult_le_pos; apply cnorm_ge0.
      * apply coh_delta_bound; assumption.
Qed.

(* 相干加权和 coh（双和去对角） *)
Definition coh_e5 (c : nat -> Complex) : R :=
  sum_f_R0 (fun i => sum_f_R0 (fun j =>
    if eq_nat_dec i j then 0%R else Cnorm (c i) * Cnorm (c j) * delta_e5 i j) 6) 6.

(* 负号进出有限和 *)
Lemma sum_opp : forall (f : nat -> R) (n : nat),
  - sum_f_R0 f n = sum_f_R0 (fun i => - f i) n.
Proof.
  intros f n.
  replace (- sum_f_R0 f n) with (-1 * sum_f_R0 f n) by ring.
  rewrite <- (sum_f_R0_scal_l (-1) f n).
  apply sum_f_R0_ext; intros i _. ring.
Qed.

(* E5'' 端到端复合证书：七带完整输出的平方范数复合界 *)
Theorem champion_e5_composite_certificate (coeffs : list Complex) :
  length coeffs = 7%nat ->
  let c := fun i => nth i coeffs C0 in
  let F := fun k => Csum (fun i => c i *c psi (nth i e5_bands 0%nat) k) 7%nat in
  let S := sum_f_R0 (fun i => Cnorm_sq (c i)) 6%nat in
  ((S - coh_e5 c) <= l2_norm_sq F 255%nat <= (S + coh_e5 c))%R.
Proof.
  intros Hlen c F S.
  unfold S.
  set (inner := fun i j : nat =>
    Csum (fun k => psi (nth i e5_bands 0%nat) k *c Cconj (psi (nth j e5_bands 0%nat) k)) 256%nat).
  assert (Hlen_bands : length e5_bands = 7%nat) by (unfold e5_bands; reflexivity).
  pose proof (l2_expand_double_sum coeffs e5_bands 7%nat 256%nat Hlen Hlen_bands (Nat.lt_0_succ 255%nat)) as Hlex.
  cbv zeta in Hlex.
  fold inner in Hlex.
  change ((S - coh_e5 c) <= l2_norm_sq F (256 - 1)%nat <= (S + coh_e5 c))%R.
  assert (Hrew : l2_norm_sq F (256 - 1)%nat =
      sum_f_R0 (fun i => sum_f_R0 (fun j =>
        re (c i *c Cconj (c j) *c inner i j)) 6%nat) 6%nat).
  { unfold inner, F. exact Hlex. }
  rewrite Hrew.  (* l2_norm_sq F 255 = Σ_{i,j} re (c i *c Cconj (c j) *c inner i j) *)
  (* ---- 上界 ---- *)
  assert (Hup_sum : sum_f_R0 (fun i => sum_f_R0 (fun j =>
        re (c i *c Cconj (c j) *c inner i j)) 6%nat) 6%nat
      <= sum_f_R0 (fun i => sum_f_R0 (fun j =>
           if eq_nat_dec i j then Cnorm_sq (c i)
           else Cnorm (c i) * Cnorm (c j) * delta_e5 i j) 6%nat) 6%nat).
  { apply sum_f_R0_le_compat; intros i Hi.
    apply sum_f_R0_le_compat; intros j Hj.
    unfold inner. apply term_bound_upper; lia. }
  (* ---- 下界 ---- *)
  assert (Hlo_sum : sum_f_R0 (fun i => sum_f_R0 (fun j =>
        - re (c i *c Cconj (c j) *c inner i j)) 6%nat) 6%nat
      <= sum_f_R0 (fun i => sum_f_R0 (fun j =>
           if eq_nat_dec i j then - Cnorm_sq (c i)
           else Cnorm (c i) * Cnorm (c j) * delta_e5 i j) 6%nat) 6%nat).
  { apply sum_f_R0_le_compat; intros i Hi.
    apply sum_f_R0_le_compat; intros j Hj.
    unfold inner. apply term_bound_lower; lia. }
  assert (Hup_eq : sum_f_R0 (fun i => sum_f_R0 (fun j =>
        if eq_nat_dec i j then Cnorm_sq (c i)
        else Cnorm (c i) * Cnorm (c j) * delta_e5 i j) 6%nat) 6%nat
      = sum_f_R0 (fun i => Cnorm_sq (c i)) 6%nat + coh_e5 c).
  { unfold coh_e5. simpl. ring. }
  assert (Hlo_eq : sum_f_R0 (fun i => sum_f_R0 (fun j =>
        if eq_nat_dec i j then - Cnorm_sq (c i)
        else Cnorm (c i) * Cnorm (c j) * delta_e5 i j) 6%nat) 6%nat
      = - sum_f_R0 (fun i => Cnorm_sq (c i)) 6%nat + coh_e5 c).
  { unfold coh_e5. simpl. ring. }
  split.
  - (* 下界：S - coh <= ΣΣ re ⟺ -ΣΣ re <= -S + coh *)
    assert (Hlo_neg : - sum_f_R0 (fun i => sum_f_R0 (fun j =>
          re (c i *c Cconj (c j) *c inner i j)) 6%nat) 6%nat
          <= - S + coh_e5 c).
    { rewrite (sum_opp (fun i => sum_f_R0 (fun j => re (c i *c Cconj (c j) *c inner i j)) 6%nat) 6%nat).
      apply Rle_trans with (sum_f_R0 (fun i => sum_f_R0 (fun j =>
          if eq_nat_dec i j then - Cnorm_sq (c i)
          else Cnorm (c i) * Cnorm (c j) * delta_e5 i j) 6%nat) 6%nat).
      + apply Rle_trans with (sum_f_R0 (fun i => sum_f_R0 (fun j =>
            - re (c i *c Cconj (c j) *c inner i j)) 6%nat) 6%nat).
        * apply sum_f_R0_le_compat; intros i Hi.
          rewrite (sum_opp (fun j => re (c i *c Cconj (c j) *c inner i j)) 6%nat).
          apply Rle_refl.
        * exact Hlo_sum.
      + rewrite Hlo_eq. unfold S. apply Rle_refl. }
    unfold S in Hlo_neg |- *.
    lra.
  - (* 上界：ΣΣ re <= S + coh *)
    apply Rle_trans with (sum_f_R0 (fun i => sum_f_R0 (fun j =>
        if eq_nat_dec i j then Cnorm_sq (c i)
        else Cnorm (c i) * Cnorm (c j) * delta_e5 i j) 6%nat) 6%nat).
    + exact Hup_sum.
    + rewrite Hup_eq. unfold S. apply Rle_refl.
Qed.

End ChampionCertificate.

(* ============================================================
   Module FrameCheck2DNarrow（会话 15：2D 窄轨反射检查器）
   ------------------------------------------------------------
   任务：(b) 2D 窄轨反射检查器 —— 把 1D frame_check_instance 反射模式
   推广到 2D 窄轨定理 tensor_product_unconditional_basis_corrected（K0=C³/4）。
   输入两轴阶梯值列表 vals1/vals2 与生长常数 cC，检查
     sorted/ge2/增长/单带退化（n1=1 或 n2=1）/单值支配/曼哈顿≤6，
   判定通过 ⟹ 2D 窄轨无条件基界（M_bound = K0·((1+4K_C)²−1)）。
   关键数学（会话 14）：corrected 的 H_dom forall 版本不可实例化
   （idx1=idx2 时要求 seq1 i = seq2 j）；本模块走 abstract_unconditional_basis
   独立装配（tensor_product_unconditional_basis_pointwise，点态 H_dom 只对 idx1≠idx2）。
   seq_ext：窗口内 nth，窗口外几何闭式 cC^k·(last+1) − 1 ⟹ 严格增长。
   零 classic（axiom 集 = sig_not_dec + sig_forall_dec + fext，与 3D/4D 同款）。
   ============================================================ *)
Module FrameCheck2DNarrow.

Import ExtendedTheorems.
Import InstanceCertificate.
Import UnconditionalBasisLemmas.
Import RuntimeGuards.
Import FrameCheckInstance.
Import ComplexNumbers.
Open Scope R_scope.
(* ---- 严格增长延拓：窗口内 nth；窗口外 cC^k·(last+1) − 1 ---- *)
Definition seq_ext (vals : list nat) (cC : nat) : nat -> nat :=
  fun i => if i <? length vals then nth i vals 0%nat
           else ((cC ^ (i - length vals + 1))%nat *
                 (S (nth (Nat.pred (length vals)) vals 0%nat)) - 1)%nat.

(* 窗口内取值 *)
Lemma seq_ext_window (vals : list nat) (cC i : nat) :
  (i < length vals)%nat -> seq_ext vals cC i = nth i vals 0%nat.
Proof.
  intros Hi. unfold seq_ext.
  destruct (Nat.ltb_spec i (length vals)) as [H | H'].
  - reflexivity.
  - exfalso. lia.
Qed.

(* cC ≥ 2 ⟹ 0 < cC^k（幂正性，归纳） *)
Lemma pow_pos_nat (cC k : nat) : (2 <= cC)%nat -> (0 < cC ^ k)%nat.
Proof.
  intros HC. induction k as [| k' IH].
  - simpl. lia.
  - simpl. apply Nat.mul_pos_pos; [lia | exact IH].
Qed.

(* 窗口外闭式：i >= len ⟹ seq_ext i = cC^(i-len+1)·(last+1) − 1 *)
Lemma seq_ext_tail_closed (vals : list nat) (cC i : nat) :
  (0 < length vals)%nat -> (length vals <= i)%nat ->
  seq_ext vals cC i =
  ((cC ^ (i - length vals + 1))%nat * S (nth (Nat.pred (length vals)) vals 0%nat) - 1)%nat.
Proof.
  intros Hlen Hi. unfold seq_ext.
  destruct (Nat.ltb_spec i (length vals)) as [H | H']; [lia |].
  reflexivity.
Qed.

(* 几何段 R 不等式：i >= len ⟹ INR (seq_ext (S i)) > INR cC * INR (seq_ext i)
   用闭式：seq_ext i = cC^k·(last+1) − 1，seq_ext (S i) = cC^(k+1)·(last+1) − 1 *)
Lemma seq_ext_geom_R (vals : list nat) (cC i : nat) :
  (cC >= 2)%nat -> (0 < length vals)%nat -> all_ge_2 vals = true ->
  (length vals <= i)%nat ->
  (INR (seq_ext vals cC (S i)) > INR cC * INR (seq_ext vals cC i))%R.
Proof.
  intros HC Hlen Hg Hi.
  set (last := nth (Nat.pred (length vals)) vals 0%nat).
  set (k := (i - length vals + 1)%nat).
  assert (Hlast2 : (2 <= last)%nat).
  { unfold last. apply all_ge_2_nth.
    - exact Hg.
    - lia. }
  assert (Hk_pos : (0 < k)%nat).
  { unfold k. lia. }
  (* seq_ext i = cC^k·(last+1) − 1 *)
  assert (Heq_i : seq_ext vals cC i = (cC ^ k * S last - 1)%nat).
  { unfold k, last. rewrite (seq_ext_tail_closed vals cC i Hlen Hi). reflexivity. }
  (* seq_ext (S i) = cC^(S k)·(last+1) − 1 *)
  assert (HleS : (length vals <= S i)%nat) by lia.
  assert (Heq_S : seq_ext vals cC (S i) = (cC ^ S k * S last - 1)%nat).
  { assert (HkS : (S i - length vals + 1)%nat = S k) by (unfold k; lia).
    unfold k, last. rewrite (seq_ext_tail_closed vals cC (S i) Hlen HleS).
    rewrite HkS. reflexivity. }
  rewrite Heq_i, Heq_S.
  (* cC^(S k)·(last+1) − 1 > cC·(cC^k·(last+1) − 1) *)
  assert (HB1 : (1 <= cC ^ k * S last)%nat).
  { assert (Hpos : (0 < cC ^ k)%nat) by (apply pow_pos_nat; exact HC).
    nia. }
  assert (HA1 : (1 <= cC ^ S k * S last)%nat).
  { assert (Hpos : (0 < cC ^ S k)%nat) by (apply pow_pos_nat; exact HC).
    nia. }
  rewrite (minus_INR (cC ^ S k * S last) 1 HA1).
  rewrite (minus_INR (cC ^ k * S last) 1 HB1).
  simpl.
  rewrite (mult_INR (cC * cC ^ k) (S last)).
  rewrite (mult_INR (cC ^ k) (S last)).
  rewrite (mult_INR cC (cC ^ k)).
  assert (HC_R : 1 < INR cC) by (change 1 with (INR 1); apply lt_INR; lia).
  assert (HA_nonneg : 0 <= INR (cC ^ k) * INR (S last)).
  { apply Rmult_le_pos; apply pos_INR. }
  lra.
Qed.

(* 尾部首步 R 不等式：i = len-1 ⟹ INR (seq_ext len) > INR cC * INR last *)
Lemma seq_ext_tail_first_R (vals : list nat) (cC i : nat) :
  (cC >= 2)%nat -> (0 < length vals)%nat -> all_ge_2 vals = true ->
  (i < length vals)%nat -> (length vals <= S i)%nat ->
  (INR (seq_ext vals cC (S i)) > INR cC * INR (seq_ext vals cC i))%R.
Proof.
  intros HC Hlen Hg Hi Hle.
  rewrite (seq_ext_window vals cC i Hi).
  rewrite (seq_ext_tail_closed vals cC (S i) Hlen Hle).
  assert (Hi' : (i = length vals - 1)%nat) by lia.
  rewrite Hi'.
  simpl.
  destruct (length vals) as [| len']; [lia |].
  simpl.
  assert (Hexp : (len' - 0 - len' + 1)%nat = 1%nat) by lia.
  rewrite Hexp.
  simpl.
  assert (Hcm : (cC * 1)%nat = cC) by lia.
  rewrite Hcm.
  (* 不用 set last：simpl 会把它展开成 nth len' vals 0，change 失配；
     直接用显式 nth len' vals 0 形式（会话 14 已 query_goal 验证） *)
  assert (HA1 : (1 <= cC * S (nth len' vals 0%nat))%nat) by nia.
  rewrite (minus_INR (cC * S (nth len' vals 0%nat)) 1 HA1).
  rewrite mult_INR.
  rewrite (S_INR (nth len' vals 0%nat)).
  rewrite INR_1.
  (* RHS 仍为 nth (len' - 0) vals 0：minus 双参匹配，len' 为变量时不归约，
     change 会 Not convertible；replace 用 lia 归一后才能 lra 消原子 *)
  replace (len' - 0)%nat with len' by lia.
  assert (HC_R : 1 < INR cC) by (change 1 with (INR 1); apply lt_INR; lia).
  lra.
Qed.

(* 窗口内相邻增长 ⟹ nth 相邻对 cC 增长 *)
Lemma seq_ext_window_growth_nat (vals : list nat) (cC : nat) :
  (cC >= 1)%nat ->
  check_sparse_growth vals cC = true ->
  forall i, (S i < length vals)%nat -> ((cC * nth i vals 0%nat) < nth (S i) vals 0%nat)%nat.
Proof.
  intros HC Hcg i Hi.
  unfold check_sparse_growth in Hcg.
  pose proof (forallb_adjacent_nth vals (fun a b => ((cC * a) <? b)%nat) Hcg i) as Hnth.
  apply Nat.ltb_lt.
  apply Hnth. lia.
Qed.

(* 窗口内 INR 增长 *)
Lemma seq_ext_window_growth_R (vals : list nat) (cC : nat) :
  (cC >= 1)%nat ->
  check_sparse_growth vals cC = true ->
  forall i, (S i < length vals)%nat ->
  (INR (nth (S i) vals 0%nat) > INR cC * INR (nth i vals 0%nat))%R.
Proof.
  intros HC Hcg i Hi.
  pose proof (seq_ext_window_growth_nat vals cC HC Hcg i Hi) as Hlt.
  apply lt_INR in Hlt.
  rewrite Nat.mul_comm in Hlt.
  rewrite mult_INR in Hlt.
  rewrite Rmult_comm in Hlt.
  exact Hlt.
Qed.

(* seq_ext 全局 INR 增长（Hsparse 前提） *)
Lemma seq_ext_growth_R (vals : list nat) (cC : nat) :
  (cC >= 2)%nat -> (0 < length vals)%nat ->
  check_sparse_growth vals cC = true ->
  all_ge_2 vals = true ->
  forall i, (INR (seq_ext vals cC (S i)) > INR cC * INR (seq_ext vals cC i))%R.
Proof.
  intros HC Hlen Hcg Hg i.
  destruct (lt_dec (S i) (length vals)) as [HSi | HSi_ge].
  - (* 窗口内相邻对 *)
    destruct (lt_dec i (length vals)) as [Hi | Hi_ge]; [| lia].
    rewrite (seq_ext_window vals cC i Hi).
    rewrite (seq_ext_window vals cC (S i) HSi).
    apply seq_ext_window_growth_R; [lia | exact Hcg | exact HSi].
  - (* S i >= len *)
    destruct (lt_dec i (length vals)) as [Hi | Hi_ge].
    + (* i = len-1：尾部首步 *)
      apply seq_ext_tail_first_R; [exact HC | exact Hlen | exact Hg | exact Hi |].
      exact (proj1 (Nat.nlt_ge (S i) (length vals)) HSi_ge).
    + (* i >= len：纯几何段 *)
      apply seq_ext_geom_R; [exact HC | exact Hlen | exact Hg |].
      apply Nat.nlt_ge. exact Hi_ge.
Qed.

(* 窗口内值 ≥2 *)
Lemma seq_ext_window_ge2 (vals : list nat) (i : nat) :
  all_ge_2 vals = true -> (i < length vals)%nat -> (2 <= nth i vals 0%nat)%nat.
Proof.
  intros Hg Hi. apply all_ge_2_nth; assumption.
Qed.

(* 尾部延拓值 ≥2 *)
Lemma seq_ext_tail_ge2 (vals : list nat) (cC i : nat) :
  (cC >= 2)%nat -> (0 < length vals)%nat -> all_ge_2 vals = true ->
  (length vals <= i)%nat -> (2 <= seq_ext vals cC i)%nat.
Proof.
  intros HC Hlen Hg Hi.
  rewrite (seq_ext_tail_closed vals cC i Hlen Hi).
  assert (Hlast2 : (2 <= nth (Nat.pred (length vals)) vals 0%nat)%nat).
  { apply seq_ext_window_ge2.
    - exact Hg.
    - lia. }
  assert (Hpow_ge1 : (1 <= cC ^ (i - length vals + 1))%nat).
  { destruct (i - length vals + 1)%nat as [| k']; [simpl; lia |].
    apply Nat.lt_le_incl.
    apply Nat.pow_gt_1; [lia | lia]. }
  assert (Hpow_pos : (0 < cC ^ (i - length vals + 1))%nat).
  { destruct (cC ^ (i - length vals + 1))%nat as [| k']; [exfalso; lia | lia]. }
  nia.
Qed.

(* ============ 2D 窄轨反射检查器：检查项定义 ============ *)

(* 单带退化判定：n1=1 或 n2=1 *)
Definition single_band (n1 n2 : nat) : bool :=
  (n1 =? 1)%nat || (n2 =? 1)%nat.

(* 单值支配：n1=1 ⟹ vals1[0] ≥ max vals2；n2=1 ⟹ vals2[0] ≥ max vals1 *)
Definition dom_check (vals1 vals2 : list nat) : bool :=
  match (length vals1 =? 1)%nat, (length vals2 =? 1)%nat with
  | true, _ => Nat.leb (fold_right Nat.max 0%nat vals2) (nth 0 vals1 0%nat)
  | _, true => Nat.leb (fold_right Nat.max 0%nat vals1) (nth 0 vals2 0%nat)
  | _, _ => false
  end.

(* 曼哈顿 ≤6：n1+n2 ≤ 8（任意两扁平索引 |i1-i2|+|j1-j2| ≤ (n1-1)+(n2-1) = n1+n2-2 ≤ 6） *)
Definition manhattan_ok (vals1 vals2 : list nat) : bool :=
  Nat.leb (length vals1 + length vals2) 8%nat.

(* 主检查器 *)
Definition frame_check_2d_narrow (cC : nat) (vals1 vals2 : list nat) : bool :=
  andb (sorted_strict_aux vals1) (sorted_strict_aux vals2) &&
  andb (all_ge_2 vals1) (all_ge_2 vals2) &&
  andb (check_sparse_growth vals1 cC) (check_sparse_growth vals2 cC) &&
  andb (single_band (length vals1) (length vals2))
       (andb (dom_check vals1 vals2) (manhattan_ok vals1 vals2)).

(* ---- 检查项 ⟹ 前提的引理 ---- *)

(* single_band 拆解 *)
Lemma single_band_case (n1 n2 : nat) :
  single_band n1 n2 = true ->
  (n1 = 1)%nat \/ (n2 = 1)%nat.
Proof.
  unfold single_band. destruct (Nat.eqb_spec n1 1) as [H1 | H1]; [left; exact H1 |].
  destruct (Nat.eqb_spec n2 1) as [H2 | H2]; [right; exact H2 |].
  intro Habs. discriminate.
Qed.

(* dom_check：n1=1 ⟹ vals1[0] ≥ max vals2 *)
Lemma dom_check_n1_1 (vals1 vals2 : list nat) :
  (length vals1 = 1)%nat ->
  dom_check vals1 vals2 = true ->
  (fold_right Nat.max 0%nat vals2 <= nth 0 vals1 0%nat)%nat.
Proof.
  intros Hn1 Hd.
  unfold dom_check in Hd.
  rewrite Hn1 in Hd.
  simpl in Hd.
  destruct (Nat.eqb_spec (length vals2) 1) as [Hn2 | Hn2]; simpl in Hd.
  - apply Nat.leb_le in Hd. exact Hd.
  - apply Nat.leb_le in Hd. exact Hd.
Qed.

(* dom_check：n2=1 且 n1≠1 ⟹ vals2[0] ≥ max vals1
   （n1=1 ∧ n2=1 时 dom_check 首分支命中，方向相反——该情形下 n1·n2=1 无对，H_dom 真空） *)
Lemma dom_check_n2_1 (vals1 vals2 : list nat) :
  (length vals2 = 1)%nat -> (length vals1 <> 1)%nat ->
  dom_check vals1 vals2 = true ->
  (fold_right Nat.max 0%nat vals1 <= nth 0 vals2 0%nat)%nat.
Proof.
  intros Hn2 Hn1_ne Hd.
  unfold dom_check in Hd.
  destruct (Nat.eqb_spec (length vals1) 1) as [Hn1 | Hn1']; simpl in Hd.
  - exfalso. apply Hn1_ne. exact Hn1.
  - rewrite Hn2 in Hd. simpl in Hd. apply Nat.leb_le in Hd. exact Hd.
Qed.

(* 所有元素 ≤ max（正向） *)
Lemma In_le_fold_max (vals : list nat) (v : nat) :
  In v vals -> (v <= fold_right Nat.max 0%nat vals)%nat.
Proof.
  induction vals as [| h tl IH]; simpl.
  - intro Hv; inversion Hv.
  - intro Hv. destruct Hv as [Heq | Hin].
    + subst. apply Nat.le_max_l.
    + apply (Nat.le_trans _ (fold_right Nat.max 0%nat tl) _);
        [apply IH; exact Hin | apply Nat.le_max_r].
Qed.

(* max 传递：max ≤ x 且 In v ⟹ v ≤ x *)
Lemma fold_max_le_all (vals : list nat) (x v : nat) :
  (fold_right Nat.max 0%nat vals <= x)%nat ->
  In v vals -> (v <= x)%nat.
Proof.
  intros Hle Hin. apply (Nat.le_trans _ (fold_right Nat.max 0%nat vals) _);
    [apply In_le_fold_max; exact Hin | exact Hle].
Qed.

(* 检查项：n1=1 时窗口内任何 vals2 元素 ≤ vals1[0] *)
Lemma dom_n1_1_all_le (vals1 vals2 : list nat) (v : nat) :
  (length vals1 = 1)%nat ->
  dom_check vals1 vals2 = true ->
  In v vals2 -> (v <= nth 0 vals1 0%nat)%nat.
Proof.
  intros Hn1 Hd Hin.
  apply (fold_max_le_all vals2 (nth 0 vals1 0%nat) v).
  - apply dom_check_n1_1; assumption.
  - exact Hin.
Qed.

(* 检查项：n2=1 且 n1≠1 时窗口内任何 vals1 元素 ≤ vals2[0] *)
Lemma dom_n2_1_all_le (vals1 vals2 : list nat) (v : nat) :
  (length vals2 = 1)%nat -> (length vals1 <> 1)%nat ->
  dom_check vals1 vals2 = true ->
  In v vals1 -> (v <= nth 0 vals2 0%nat)%nat.
Proof.
  intros Hn2 Hn1_ne Hd Hin.
  apply (fold_max_le_all vals1 (nth 0 vals2 0%nat) v).
  - apply dom_check_n2_1; assumption.
  - exact Hin.
Qed.

(* ============ H_dom 构造（单带退化） ============ *)
(* H_dom 陈述（corrected 10271-10275）：
   forall idx1 idx2,
     (idx1/n2 = idx2/n2 -> seq1 (idx1/n2) >= max(seq2 (idx1 mod n2))(seq2 (idx2 mod n2))) /\
     (idx1 mod n2 = idx2 mod n2 -> seq2 (idx1 mod n2) >= max(seq1 (idx1/n2))(seq1 (idx2/n2)))
   单带退化 n1=1：i 恒为 0（idx < 1*n2 = n2 ⟹ idx/n2 = 0）。同行（恒成立）⟹
   需要 seq1 0 >= max(seq2 j1)(seq2 j2)，由 dom_check（vals1[0] ≥ max vals2）+ seq_ext_window 给出。
   同列（idx1 mod n2 = idx2 mod n2 = j）：需要 seq2 j >= max(seq1 0)(seq1 0) = seq1 0。
   但这与同行条件（seq1 0 ≥ seq2 j）同时要求 ⟹ 全等。因此 corrected 的 H_dom forall
   版本实际不可实例化（idx1=idx2 时要求 seq1 i = seq2 j）。 *)
(* 结论：2D 窄轨反射检查器不能实例化 corrected 的 H_dom forall，必须走
   abstract_unconditional_basis 独立装配（phi_flat_decay_general 的点态 H_dom 只对 idx1≠idx2）。

   ---- 点态 H_dom 构造（探针新增，会话 15） ----
   输入：single_band n1 n2 = true（n1=1 或 n2=1）+ dom_check（单值支配）
   输出：phi_flat_decay_general 需要的点态 H_dom（forall idx1 idx2, idx1<>idx2 -> ...）
   情形 n1=1：同行分支由 dom_check（vals1[0] ≥ max vals2）+ In_le_fold_max + nth_In 给出；
              同列分支前提 idx1 mod n2 = idx2 mod n2 ⟹ idx1 = idx2（mod_small）⟹ 与 idx1≠idx2 矛盾。
   情形 n2=1（n1≠1）：同列分支由 dom_check_n2_1 给出；同行分支 idx1/1 = idx2/1 ⟹ 矛盾。
   情形 n1=1 ∧ n2=1：n1·n2 = 1，idx1<1 ∧ idx2<1 ⟹ idx1=idx2=0，无对，H_dom 真空。 *)

(* Z 侧辅助：abs_nat 对负数 = 原数（曼哈顿界需要） *)
Lemma Zabs_nat_opp_of_nat (n : nat) : Z.abs_nat (- Z.of_nat n) = n.
Proof.
  rewrite Znat.Zabs2Nat.abs_nat_spec.
  rewrite Z.abs_opp.
  rewrite (Z.abs_eq (Z.of_nat n) (Nat2Z.is_nonneg n)).
  apply Nat2Z.id.
Qed.

(* |a - b| ≤ c−1 当 a,b < c（nat 差的上界） *)
Lemma abs_nat_sub_bounded (a b c : nat) : (a < c)%nat -> (b < c)%nat ->
  (Z.abs_nat (Z.of_nat a - Z.of_nat b) <= c - 1)%nat.
Proof.
  intros Ha Hb.
  destruct (le_lt_dec a b) as [Hab | Hba].
  - assert (Hsub : (Z.of_nat a - Z.of_nat b)%Z = (- Z.of_nat (b - a))%Z).
    { rewrite (Znat.Nat2Z.inj_sub b a Hab). lia. }
    rewrite Hsub.
    rewrite Zabs_nat_opp_of_nat.
    lia.
  - assert (Hsub : (Z.of_nat a - Z.of_nat b)%Z = Z.of_nat (a - b)).
    { rewrite (Znat.Nat2Z.inj_sub a b). lia. apply Nat.lt_le_incl; exact Hba. }
    rewrite Hsub.
    rewrite Znat.Zabs2Nat.id.
    lia.
Qed.

(* 曼哈顿界：n1+n2 ≤ 8 ⟹ |i1−i2| + |j1−j2| ≤ 6（n1,n2 ≥ 1） *)
Lemma index_bound_2d (n1 n2 idx1 idx2 : nat) :
  (n1 > 0)%nat -> (n2 > 0)%nat -> (n1 + n2 <= 8)%nat ->
  (idx1 < n1 * n2)%nat -> (idx2 < n1 * n2)%nat ->
  (Z.abs_nat (Z.of_nat (idx1 / n2) - Z.of_nat (idx2 / n2)) +
   Z.abs_nat (Z.of_nat (idx1 mod n2) - Z.of_nat (idx2 mod n2)) <= 6)%nat.
Proof.
  intros Hn1 Hn2 Hle Hlt1 Hlt2.
  assert (Hi1 : (idx1 / n2 < n1)%nat) by (apply Nat.Div0.div_lt_upper_bound; lia).
  assert (Hi2 : (idx2 / n2 < n1)%nat) by (apply Nat.Div0.div_lt_upper_bound; lia).
  assert (Hj1 : (idx1 mod n2 < n2)%nat) by (apply Nat.mod_upper_bound; lia).
  assert (Hj2 : (idx2 mod n2 < n2)%nat) by (apply Nat.mod_upper_bound; lia).
  assert (Hd1 : (Z.abs_nat (Z.of_nat (idx1 / n2) - Z.of_nat (idx2 / n2)) <= n1 - 1)%nat).
  { apply abs_nat_sub_bounded; auto. }
  assert (Hd2 : (Z.abs_nat (Z.of_nat (idx1 mod n2) - Z.of_nat (idx2 mod n2)) <= n2 - 1)%nat).
  { apply abs_nat_sub_bounded; auto. }
  lia.
Qed.

(* seq start len 严格升序（Sorted Nat.lt），n1/n2 的索引列表用 *)
Lemma sorted_seq (start len : nat) : Sorted Nat.lt (seq start len).
Proof.
  revert start. induction len as [| len' IH]; intros start; simpl.
  - constructor.
  - rewrite cons_seq. constructor.
    + apply IH.
    + destruct len'; simpl; constructor; lia.
Qed.

Lemma sorted_seq_0 (n : nat) : Sorted Nat.lt (seq 0 n).
Proof. apply sorted_seq. Qed.

(* seq_ext 全局 ≥2（窗口内 + 尾部延拓） *)
Lemma seq_ext_ge2 (vals : list nat) (cC : nat) :
  (cC >= 2)%nat -> (0 < length vals)%nat -> all_ge_2 vals = true ->
  forall i, (seq_ext vals cC i >= 2)%nat.
Proof.
  intros HC Hlen Hg i.
  destruct (lt_dec i (length vals)) as [Hi | Hi_ge].
  - rewrite (seq_ext_window vals cC i Hi).
    apply seq_ext_window_ge2; assumption.
  - apply seq_ext_tail_ge2; [exact HC | exact Hlen | exact Hg |].
    apply Nat.nlt_ge. exact Hi_ge.
Qed.

(* 点态 H_dom 构造：single_band + dom_check ⟹ phi_flat_decay_general 的 H_dom *)
Lemma hdom_2d_narrow (vals1 vals2 : list nat) (cC n1 n2 : nat) :
  (n1 = length vals1)%nat -> (n2 = length vals2)%nat ->
  single_band n1 n2 = true -> dom_check vals1 vals2 = true ->
  forall idx1 idx2 : nat, idx1 <> idx2 ->
    (idx1 < n1 * n2)%nat -> (idx2 < n1 * n2)%nat ->
    ((idx1 / n2)%nat = (idx2 / n2)%nat ->
     (seq_ext vals1 cC ((idx1 / n2)%nat) >=
      Nat.max (seq_ext vals2 cC ((idx1 mod n2)%nat)) (seq_ext vals2 cC ((idx2 mod n2)%nat)))%nat) /\
    ((idx1 mod n2)%nat = (idx2 mod n2)%nat ->
     (seq_ext vals2 cC ((idx1 mod n2)%nat) >=
      Nat.max (seq_ext vals1 cC ((idx1 / n2)%nat)) (seq_ext vals1 cC ((idx2 / n2)%nat)))%nat).
Proof.
  intros Hn1 Hn2 Hsb Hdom idx1 idx2 Hneq Hlt1 Hlt2.
  apply single_band_case in Hsb.
  destruct Hsb as [Hn1_1 | Hn2_1].
  - (* n1 = 1：同行由 dom_check；同列矛盾 *)
    subst n1.
    split.
    + (* 同行分支：idx1/n2 = idx2/n2 = 0 *)
      intros _.
      assert (Hlt1' : (idx1 < n2)%nat) by lia.
      assert (Hlt2' : (idx2 < n2)%nat) by lia.
      assert (Hdiv1 : (idx1 / n2)%nat = 0%nat) by (apply Nat.div_small; exact Hlt1').
      assert (Hdiv2 : (idx2 / n2)%nat = 0%nat) by (apply Nat.div_small; exact Hlt2').
      assert (Hmod1 : (idx1 mod n2)%nat = idx1) by (apply Nat.mod_small; exact Hlt1').
      assert (Hmod2 : (idx2 mod n2)%nat = idx2) by (apply Nat.mod_small; exact Hlt2').
      rewrite Hdiv1, Hmod1, Hmod2.
      (* seq_ext vals1 cC 0 = nth 0 vals1 0（窗口内） *)
      assert (Hlen1_pos : (0 < length vals1)%nat) by lia.
      rewrite (seq_ext_window vals1 cC 0 Hlen1_pos).
      (* seq_ext vals2 cC idx1/idx2 = nth idx1/idx2 vals2 0（窗口内） *)
      assert (Hl2a : (idx1 < length vals2)%nat) by lia.
      assert (Hl2b : (idx2 < length vals2)%nat) by lia.
      rewrite (seq_ext_window vals2 cC idx1 Hl2a).
      rewrite (seq_ext_window vals2 cC idx2 Hl2b).
      (* 需要：nth 0 vals1 0 >= max (nth idx1 vals2 0) (nth idx2 vals2 0) *)
      assert (Hdom1 : (fold_right Nat.max 0%nat vals2 <= nth 0 vals1 0%nat)%nat).
      { apply dom_check_n1_1; [lia | exact Hdom]. }
      apply Nat.max_lub_iff. split.
      * eapply Nat.le_trans; [apply In_le_fold_max; apply nth_In; exact Hl2a | exact Hdom1].
      * eapply Nat.le_trans; [apply In_le_fold_max; apply nth_In; exact Hl2b | exact Hdom1].
    + (* 同列分支：idx1 mod n2 = idx2 mod n2 ⟹ idx1 = idx2 ⟹ 矛盾 *)
      intros Hmod_eq.
      assert (Hlt1' : (idx1 < n2)%nat) by lia.
      assert (Hlt2' : (idx2 < n2)%nat) by lia.
      assert (Hmod1 : (idx1 mod n2)%nat = idx1) by (apply Nat.mod_small; exact Hlt1').
      assert (Hmod2 : (idx2 mod n2)%nat = idx2) by (apply Nat.mod_small; exact Hlt2').
      rewrite Hmod1, Hmod2 in Hmod_eq.
      exfalso. apply Hneq. exact Hmod_eq.
  - (* n2 = 1：同行矛盾；同列由 dom_check（需 n1≠1，n1=1 时无对） *)
    assert (Hlt1' : (idx1 < n1)%nat) by (rewrite Hn2_1 in Hlt1; lia).
    assert (Hlt2' : (idx2 < n1)%nat) by (rewrite Hn2_1 in Hlt2; lia).
    assert (Hdiv1 : (idx1 / 1)%nat = idx1) by (apply Nat.div_1_r).
    assert (Hdiv2 : (idx2 / 1)%nat = idx2) by (apply Nat.div_1_r).
    assert (Hmod1 : (idx1 mod 1)%nat = 0%nat) by (apply Nat.mod_1_r).
    assert (Hmod2 : (idx2 mod 1)%nat = 0%nat) by (apply Nat.mod_1_r).
    split.
    + (* 同行分支：idx1/1 = idx2/1 ⟹ idx1 = idx2 ⟹ 矛盾 *)
      intros Hdiv_eq.
      rewrite Hn2_1 in Hdiv_eq.
      rewrite Hdiv1, Hdiv2 in Hdiv_eq.
      exfalso. apply Hneq. exact Hdiv_eq.
    + (* 同列分支：0 = 0，需要 seq_ext vals2 cC 0 >= max (seq_ext vals1 cC idx1) (seq_ext vals1 cC idx2) *)
      intros _.
      destruct (Nat.eqb_spec (length vals1) 1) as [Hlen1_1 | Hlen1_ne].
      * (* n1=1 ∧ n2=1：n1·n2=1，idx1<1 ∧ idx2<1 ⟹ idx1=idx2=0 ⟹ 矛盾 *)
        exfalso. apply Hneq. lia.
      * rewrite Hn2_1.
        rewrite Hdiv1, Hdiv2, Hmod1.
        assert (Hlen2_pos : (0 < length vals2)%nat) by lia.
        rewrite (seq_ext_window vals2 cC 0 Hlen2_pos).
        assert (Hl1a : (idx1 < length vals1)%nat) by lia.
        assert (Hl1b : (idx2 < length vals1)%nat) by lia.
        rewrite (seq_ext_window vals1 cC idx1 Hl1a).
        rewrite (seq_ext_window vals1 cC idx2 Hl1b).
        assert (Hdom2 : (fold_right Nat.max 0%nat vals1 <= nth 0 vals2 0%nat)%nat).
        { apply dom_check_n2_1; [lia | exact Hlen1_ne | exact Hdom]. }
        apply Nat.max_lub_iff. split.
        -- eapply Nat.le_trans; [apply In_le_fold_max; apply nth_In; exact Hl1a | exact Hdom2].
        -- eapply Nat.le_trans; [apply In_le_fold_max; apply nth_In; exact Hl1b | exact Hdom2].
Qed.

(* ============ 点态 H_dom 版 2D 窄轨组装（corrected 的点态变体，会话 15 新增） ============ *)
(* corrected 的 H_dom 是 forall（含 idx1=idx2，不可实例化）；本定理只要求 idx1≠idx2，
   供 frame_check_2d_narrow_sound 直接实例化。其余前提与 corrected 完全相同。 *)
Theorem tensor_product_unconditional_basis_pointwise :
  forall (C : nat) (HCgt2 : (C > 2)%nat)
    (seq1 seq2 : nat -> nat)
    (Hsparse1 : forall i : nat, (INR (seq1 (S i)) > INR C * INR (seq1 i))%R)
    (Hsparse2 : forall i : nat, (INR (seq2 (S i)) > INR C * INR (seq2 i))%R)
    (Hge2_1 : forall i : nat, (seq1 i >= 2)%nat)
    (Hge2_2 : forall i : nat, (seq2 i >= 2)%nat)
    (I1 I2 : list nat)
    (Hdup1 : NoDup I1) (Hsorted1 : Sorted Nat.lt I1)
    (Hdup2 : NoDup I2) (Hsorted2 : Sorted Nat.lt I2)
    (coeffs : nat -> nat -> Complex)
    (n1 n2 : nat) (Hn1 : n1 = length I1) (Hn2 : n2 = length I2)
    (Hn1_pos : (n1 > 0)%nat) (Hn2_pos : (n2 > 0)%nat)
    (HI1 : I1 = seq 0 n1)
    (HI2 : I2 = seq 0 n2)
    (H_dom : forall idx1 idx2 : nat, idx1 <> idx2 ->
        (idx1 < n1 * n2)%nat -> (idx2 < n1 * n2)%nat ->
        ((idx1 / n2)%nat = (idx2 / n2)%nat ->
         (seq1 ((idx1 / n2)%nat) >= Nat.max (seq2 ((idx1 mod n2)%nat)) (seq2 ((idx2 mod n2)%nat)))%nat) /\
        ((idx1 mod n2)%nat = (idx2 mod n2)%nat ->
         (seq2 ((idx1 mod n2)%nat) >= Nat.max (seq1 ((idx1 / n2)%nat)) (seq1 ((idx2 / n2)%nat)))%nat))
    (H_index_bound : forall idx1 idx2 : nat,
        (idx1 < n1 * n2)%nat -> (idx2 < n1 * n2)%nat ->
        (Z.abs_nat (Z.of_nat (idx1 / n2) - Z.of_nat (idx2 / n2)) +
         Z.abs_nat (Z.of_nat (idx1 mod n2) - Z.of_nat (idx2 mod n2)) <= 6)%nat),
  let vals1 := map seq1 I1 in
  let vals2 := map seq2 I2 in
  let a i := nth i vals1 0%nat in
  let b j := nth j vals2 0%nat in
  let w i j := INR (Nat.min (a i) (b j)) / (INR (a i) * INR (b j)) in
  let gamma i j := sqrt (w i j) in
  let phi2D_norm (i j : nat) (k : nat) : Complex :=
    Cof_real (/ gamma i j) *c (psi (a i) k *c psi (b j) k) in
  let F_2D (k : nat) : Complex :=
    Csum (fun i => Csum (fun j => coeffs i j *c phi2D_norm i j k) n2) n1 in
  let maxIdx1 := fold_right Nat.max 0%nat I1 in
  let maxIdx2 := fold_right Nat.max 0%nat I2 in
  let M := S (max (seq1 maxIdx1) (seq2 maxIdx2)) in
  let S := sum_f_R0 (fun i =>
             sum_f_R0 (fun j => Cnorm_sq (coeffs i j)) (n2 - 1)) (n1 - 1) in
  let K_C := K (INR C) in
  let K0 := (Rmax 8 ((INR C) ^ 3)) / 4 in
  let M_bound := K0 * ((1 + 4 * K_C) * (1 + 4 * K_C) - 1) in
  ((1 - M_bound) * S <= l2_norm_sq F_2D (M - 1) <= (1 + M_bound) * S)%R.
Proof.
  intros C HCgt2 seq1 seq2 Hsparse1 Hsparse2 Hge2_1 Hge2_2
         I1 I2 Hdup1 Hsorted1 Hdup2 Hsorted2 coeffs n1 n2 Hn1 Hn2 Hn1_pos Hn2_pos
         HI1 HI2 H_dom H_index_bound.
  assert (Hc_ge2 : (C >= 2)%nat) by lia.
  assert (HCgt1_R : 1 < INR C) by (change 1 with (INR 1); apply lt_INR; lia).
  set (r := sqrt (INR C)).
  assert (Hr_gt1 : r > 1).
  { unfold r; rewrite <- sqrt_1. apply sqrt_lt_1; [lra|apply pos_INR|exact HCgt1_R]. }
  assert (Hr_pos : r > 0) by (apply sqrt_lt_R0_c; apply lt_0_INR; lia).
  set (K_C := K (INR C)).
  assert (HK_pos : 0 < K_C) by (apply K_pos; exact HCgt2).

  set (n := (n1 * n2)%nat).
  set (coeffs_flat := map (fun idx : nat => coeffs (idx / n2)%nat (idx mod n2)%nat) (seq 0 n)).
  assert (Hlen_flat : length coeffs_flat = n).
  { subst n; unfold coeffs_flat; rewrite length_map, List.length_seq; reflexivity. }

  assert (Hseq_nth : forall idx, (idx < n)%nat -> nth idx (seq 0 n) 0%nat = idx).
  { intros idx Hlt; apply nth_seq_general; exact Hlt. }

  assert (Hnth_flat : forall idx, (idx < n)%nat -> nth idx coeffs_flat C0 = coeffs (idx / n2)%nat (idx mod n2)%nat).
  { intros idx Hlt; unfold coeffs_flat.
    rewrite (H_nth_map nat Complex (fun idx0 : nat => coeffs (idx0 / n2)%nat (idx0 mod n2)%nat)
                      (seq 0 n) C0 0%nat idx).
    - rewrite Hseq_nth; auto.
    - rewrite List.length_seq; exact Hlt. }

  set (vals1 := map seq1 I1).
  set (vals2 := map seq2 I2).
  set (a := fun i : nat => nth i vals1 0%nat).
  set (b := fun j : nat => nth j vals2 0%nat).
  set (w := fun i j : nat => INR (Nat.min (a i) (b j)) / (INR (a i) * INR (b j))).
  set (gamma := fun i j : nat => sqrt (w i j)).
  set (phi2D_norm := fun (i j k : nat) => Cof_real (/ gamma i j) *c (psi (a i) k *c psi (b j) k)).
  pose (phi_flat := fun idx k => phi2D_norm (idx / n2)%nat (idx mod n2)%nat k).

  assert (Hseq1_inc : forall x y, (x <= y)%nat -> (seq1 x <= seq1 y)%nat).
  { intros x y Hle; destruct (Nat.eq_dec x y) as [Heq | Hne].
    - subst; apply Nat.le_refl.
    - apply Nat.lt_le_incl; eapply seq_strict_growth_lt; eauto; lia. }
  assert (Hseq2_inc : forall x y, (x <= y)%nat -> (seq2 x <= seq2 y)%nat).
  { intros x y Hle; destruct (Nat.eq_dec x y) as [Heq | Hne].
    - subst; apply Nat.le_refl.
    - apply Nat.lt_le_incl; eapply seq_strict_growth_lt; eauto; lia. }

  set (maxIdx1 := fold_right Nat.max 0%nat I1).
  set (maxIdx2 := fold_right Nat.max 0%nat I2).
  set (M := S (max (seq1 maxIdx1) (seq2 maxIdx2))).

  assert (Htrunc : forall idx k, (idx < n)%nat -> (k >= Nat.pred M)%nat -> phi_flat idx k = C0).
  { intros idx k Hidx Hk; unfold phi_flat.
    set (i := (idx / n2)%nat); set (j := (idx mod n2)%nat).
    assert (Hi : (i < n1)%nat) by (apply Nat.Div0.div_lt_upper_bound; lia).
    assert (Hj : (j < n2)%nat) by (apply Nat.mod_upper_bound; lia).
    unfold phi2D_norm.
    assert (Ha_le_max : (a i <= max (seq1 maxIdx1) (seq2 maxIdx2))%nat).
    { unfold a, vals1.
      assert (Hi_len : (i < length I1)%nat) by (rewrite <- Hn1; exact Hi).
      rewrite (H_nth_map nat nat seq1 I1 0%nat 0%nat i Hi_len).
      apply Nat.le_trans with (seq1 maxIdx1).
      - apply Hseq1_inc.
        eapply fold_right_max_ge.
        apply nth_In; exact Hi_len.
      - apply Nat.le_max_l. }
    assert (Hb_le_max : (b j <= max (seq1 maxIdx1) (seq2 maxIdx2))%nat).
    { unfold b, vals2.
      assert (Hj_len : (j < length I2)%nat) by (rewrite <- Hn2; exact Hj).
      rewrite (H_nth_map nat nat seq2 I2 0%nat 0%nat j Hj_len).
      apply Nat.le_trans with (seq2 maxIdx2).
      - apply Hseq2_inc.
        eapply fold_right_max_ge.
        apply nth_In; exact Hj_len.
      - apply Nat.le_max_r. }
    assert (Hmax_le_k : (max (seq1 maxIdx1) (seq2 maxIdx2) <= k)%nat).
    { unfold M in Hk; lia. }
    assert (Ha_le_k : (a i <= k)%nat) by lia.
    assert (Hb_le_k : (b j <= k)%nat) by lia.
    rewrite (psi_ge_n_zero (a i) k Ha_le_k).
    rewrite (psi_ge_n_zero (b j) k Hb_le_k).
    rewrite Cmul_0_l.
    rewrite Cmul_0_r.
    reflexivity. }

  assert (Hnorm1 : forall idx, (idx < n)%nat -> l2_norm_sq (phi_flat idx) (Nat.pred M) = 1%R).
  { intros idx Hlt; unfold phi_flat.
    set (i := (idx / n2)%nat); set (j := (idx mod n2)%nat).
    assert (Hi : (i < n1)%nat) by (apply Nat.Div0.div_lt_upper_bound; lia).
    assert (Hj : (j < n2)%nat) by (apply Nat.mod_upper_bound; lia).
    unfold phi2D_norm.
    assert (Ha_ge2 : (a i >= 2)%nat).
    { unfold a, vals1.
      assert (Hi_len : (i < length I1)%nat) by (rewrite <- Hn1; exact Hi).
      rewrite (H_nth_map nat nat seq1 I1 0%nat 0%nat i Hi_len).
      apply Hge2_1. }
    assert (Hb_ge2 : (b j >= 2)%nat).
    { unfold b, vals2.
      assert (Hj_len : (j < length I2)%nat) by (rewrite <- Hn2; exact Hj).
      rewrite (H_nth_map nat nat seq2 I2 0%nat 0%nat j Hj_len).
      apply Hge2_2. }
    set (g := gamma i j).
    assert (Hg_pos : 0 < g).
    { unfold g, gamma, w.
      assert (Hmin_pos : (0 < Nat.min (a i) (b j))%nat) by lia.
      apply sqrt_lt_R0_c.
      apply Rdiv_lt_0_compat.
      - apply lt_0_INR; exact Hmin_pos.
      - apply Rmult_lt_0_compat; apply lt_0_INR; lia. }

    assert (Ha_le_max : (a i <= max (seq1 maxIdx1) (seq2 maxIdx2))%nat).
    { unfold a, vals1.
      assert (Hi_len : (i < length I1)%nat) by (rewrite <- Hn1; exact Hi).
      rewrite (H_nth_map nat nat seq1 I1 0%nat 0%nat i Hi_len).
      apply Nat.le_trans with (seq1 maxIdx1).
      - apply Hseq1_inc. eapply fold_right_max_ge. apply nth_In; exact Hi_len.
      - apply Nat.le_max_l. }
    assert (Hb_le_max : (b j <= max (seq1 maxIdx1) (seq2 maxIdx2))%nat).
    { unfold b, vals2.
      assert (Hj_len : (j < length I2)%nat) by (rewrite <- Hn2; exact Hj).
      rewrite (H_nth_map nat nat seq2 I2 0%nat 0%nat j Hj_len).
      apply Nat.le_trans with (seq2 maxIdx2).
      - apply Hseq2_inc. eapply fold_right_max_ge. apply nth_In; exact Hj_len.
      - apply Nat.le_max_r. }
    assert (Ha_lt_M : (a i < M)%nat) by (unfold M; apply Nat.lt_succ_r; exact Ha_le_max).
    assert (Hb_lt_M : (b j < M)%nat) by (unfold M; apply Nat.lt_succ_r; exact Hb_le_max).

    set (F k := Cof_real (/ g) *c (psi (a i) k *c psi (b j) k)).
    assert (HnormF : l2_norm_sq F (Nat.pred M) = 1%R).
    { unfold l2_norm_sq, F.
      assert (Heq : forall k, Cnorm_sq (Cof_real (/ g) *c (psi (a i) k *c psi (b j) k))
                     = (/ g)^2 * (Cnorm_sq (psi (a i) k) * Cnorm_sq (psi (b j) k))).
      { intro k.
        rewrite Cnorm_sq_mult, (Cnorm_sq_mult (psi (a i) k) (psi (b j) k)).
        assert (Hcof_sq : Cnorm_sq (Cof_real (/ g)) = (/ g)^2).
        { unfold Cof_real, Cnorm_sq, Rsqr; simpl; ring. }
        rewrite Hcof_sq; reflexivity. }
      rewrite (sum_f_R0_ext _ (fun k => (/ g)^2 * (Cnorm_sq (psi (a i) k) * Cnorm_sq (psi (b j) k)))).
      - rewrite (sum_f_R0_scal_l ((/ g)^2) (fun k => Cnorm_sq (psi (a i) k) * Cnorm_sq (psi (b j) k)) (Nat.pred M)).

        destruct (Nat.min_spec (a i) (b j)) as [(Hle_ab & Hmin_ab) | (Hle_ba & Hmin_ba)].
        * assert (Ha_le_predM : (a i <= Nat.pred M)%nat) by lia.
          assert (Htrunc_full : sum_f_R0 (fun k => Cnorm_sq (psi (a i) k) * Cnorm_sq (psi (b j) k)) (Nat.pred M)
                              = sum_f_R0 (fun k => Cnorm_sq (psi (a i) k) * Cnorm_sq (psi (b j) k)) (a i)).
          { apply sum_f_R0_trunc_tail with (M := a i) (N := Nat.pred M); auto.
            intros k [Hk1 Hk2]; assert (Hk_ge_ai : (a i <= k)%nat) by exact Hk1;
            rewrite (Cnorm_sq_psi_exact (a i) k), (proj2 (Nat.ltb_ge k (a i)) Hk_ge_ai); ring. }
          rewrite Htrunc_full.

          assert (Ha_i_pos : (a i > 0)%nat) by lia.
          replace (a i) with (S (a i - 1))%nat by lia.
          rewrite sum_f_R0_S.
          replace (S (a i - 1)) with (a i) by lia.
          assert (Hlast_zero : Cnorm_sq (psi (a i) (a i)) * Cnorm_sq (psi (b j) (a i)) = 0%R).
          { rewrite (Cnorm_sq_psi_exact (a i) (a i)).
            replace (Nat.ltb (a i) (a i)) with false by (symmetry; apply Nat.ltb_ge; apply Nat.le_refl).
            ring. }
          rewrite Hlast_zero, Rplus_0_r.

          set (cst := (1 / INR (a i)) * (1 / INR (b j))).
          assert (Hterm_eq : forall k, (k < a i)%nat ->
                       Cnorm_sq (psi (a i) k) * Cnorm_sq (psi (b j) k) = cst).
          { intros k Hk_ai.
            assert (Hk_bj : (k < b j)%nat) by (apply Nat.lt_trans with (a i); auto).
            assert (Htb_ai : Nat.ltb k (a i) = true) by (apply Nat.ltb_lt; exact Hk_ai).
            assert (Htb_bj : Nat.ltb k (b j) = true) by (apply Nat.ltb_lt; exact Hk_bj).
            rewrite Cnorm_sq_psi_exact, Htb_ai, Cnorm_sq_psi_exact, Htb_bj.
            unfold cst, Rdiv; field; split; apply Rgt_not_eq; apply lt_0_INR; lia. }
          rewrite (sum_f_R0_ext _ (fun _ => cst) (a i - 1)).
          { rewrite (sum_f_R0_const cst (a i - 1)).
            replace (S (a i - 1))%nat with (a i)%nat by lia.
            unfold g, gamma, w; rewrite Hmin_ab.
            field_simplify.
            - set (s := sqrt (INR (a i) / (INR (a i) * INR (b j)))).
              assert (H_sqrt_sq : s ^ 2 = INR (a i) / (INR (a i) * INR (b j))).
              { replace (s ^ 2) with (s * s) by ring.
                apply sqrt_sqrt.
                apply Rmult_le_pos; [apply pos_INR; lia | left; apply Rinv_0_lt_compat; apply Rmult_lt_0_compat; apply lt_0_INR; lia]. }
              subst s.
              rewrite H_sqrt_sq.
              unfold cst; field; split; apply Rgt_not_eq; apply lt_0_INR; lia.
            - apply Rgt_not_eq, sqrt_lt_R0_c.
              apply Rdiv_lt_0_compat; [apply lt_0_INR; lia | apply Rmult_lt_0_compat; apply lt_0_INR; lia]. }
          { intros k Hk; apply Hterm_eq; lia. }

        * assert (Hb_le_predM : (b j <= Nat.pred M)%nat) by lia.
          assert (Htrunc_full : sum_f_R0 (fun k => Cnorm_sq (psi (a i) k) * Cnorm_sq (psi (b j) k)) (Nat.pred M)
                              = sum_f_R0 (fun k => Cnorm_sq (psi (a i) k) * Cnorm_sq (psi (b j) k)) (b j)).
          { apply sum_f_R0_trunc_tail with (M := b j) (N := Nat.pred M); auto.
            intros k [Hk1 Hk2]; assert (Hk_ge_bj : (b j <= k)%nat) by exact Hk1;
            rewrite (Cnorm_sq_psi_exact (b j) k), (proj2 (Nat.ltb_ge k (b j)) Hk_ge_bj); ring. }
          rewrite Htrunc_full.

          assert (Hb_j_pos : (b j > 0)%nat) by lia.
          replace (b j) with (S (b j - 1))%nat by lia.
          rewrite sum_f_R0_S.
          replace (S (b j - 1)) with (b j) by lia.
          assert (Hlast_zero : Cnorm_sq (psi (a i) (b j)) * Cnorm_sq (psi (b j) (b j)) = 0%R).
          { rewrite (Cnorm_sq_psi_exact (b j) (b j)).
            replace (Nat.ltb (b j) (b j)) with false by (symmetry; apply Nat.ltb_ge; apply Nat.le_refl).
            ring. }
          rewrite Hlast_zero, Rplus_0_r.

          set (cst := (1 / INR (a i)) * (1 / INR (b j))).
          assert (Hterm_eq : forall k, (k < b j)%nat ->
                       Cnorm_sq (psi (a i) k) * Cnorm_sq (psi (b j) k) = cst).
          { intros k Hk_bj.
            assert (Hk_ai : (k < a i)%nat) by (apply Nat.lt_le_trans with (b j); auto).
            assert (Htb_ai : Nat.ltb k (a i) = true) by (apply Nat.ltb_lt; exact Hk_ai).
            assert (Htb_bj : Nat.ltb k (b j) = true) by (apply Nat.ltb_lt; exact Hk_bj).
            rewrite Cnorm_sq_psi_exact, Htb_ai, Cnorm_sq_psi_exact, Htb_bj.
            unfold cst, Rdiv; field; split; apply Rgt_not_eq; apply lt_0_INR; lia. }
          rewrite (sum_f_R0_ext _ (fun _ => cst) (b j - 1)).
          { rewrite (sum_f_R0_const cst (b j - 1)).
            replace (S (b j - 1))%nat with (b j)%nat by lia.
            unfold g, gamma, w; rewrite Hmin_ba.
            field_simplify.
            - set (s := sqrt (INR (b j) / (INR (a i) * INR (b j)))).
              assert (H_sqrt_sq : s ^ 2 = INR (b j) / (INR (a i) * INR (b j))).
              { replace (s ^ 2) with (s * s) by ring.
                apply sqrt_sqrt.
                apply Rmult_le_pos; [apply pos_INR; lia | left; apply Rinv_0_lt_compat; apply Rmult_lt_0_compat; apply lt_0_INR; lia]. }
              subst s.
              rewrite H_sqrt_sq.
              unfold cst; field; split; apply Rgt_not_eq; apply lt_0_INR; lia.
            - apply Rgt_not_eq, sqrt_lt_R0_c.
              apply Rdiv_lt_0_compat; [apply lt_0_INR; lia | apply Rmult_lt_0_compat; apply lt_0_INR; lia]. }
          { intros k Hk; apply Hterm_eq; lia. }
      - intros k Hk; apply Heq. }
    exact HnormF. }

  set (d1 := d_factor r).
  pose (delta_pair := fun (idx1 idx2 : nat) =>
    d1 (idx1 / n2)%nat (idx2 / n2)%nat * d1 (idx1 mod n2)%nat (idx2 mod n2)%nat).

  assert (d_factor_sym : forall i j, d_factor r i j = d_factor r j i).
  { intros i j; unfold d_factor.
    destruct (Nat.eq_dec i j) as [Heq | Hneq].
    - subst i; reflexivity.
    - assert (Hij_false : (i =? j)%nat = false) by (apply Nat.eqb_neq; exact Hneq).
      assert (Hji_false : (j =? i)%nat = false) by (apply Nat.eqb_neq; auto).
      rewrite Hij_false, Hji_false.
      f_equal. f_equal.
      replace (Z.of_nat j - Z.of_nat i)%Z with (- (Z.of_nat i - Z.of_nat j))%Z by lia.
      rewrite Z_abs_nat_opp.
      reflexivity. }

  assert (Hdelta_sym : forall (i j : nat), (i < n)%nat -> (j < n)%nat -> delta_pair i j = delta_pair j i).
  { intros i j Hi Hj; unfold delta_pair, d1.
    rewrite (d_factor_sym (i / n2)%nat (j / n2)%nat).
    rewrite (d_factor_sym (i mod n2)%nat (j mod n2)%nat).
    reflexivity. }

  assert (d_factor_nonneg : forall i j, 0 <= d_factor r i j).
  { intros i j; unfold d_factor.
    destruct (Nat.eqb_spec i j) as [Heq | Hneq].
    - subst i; lra.
    - apply Rlt_le; apply Rdiv_lt_0_compat; [lra | apply pow_lt; exact Hr_pos]. }

  assert (Hdelta_nonneg : forall (i j : nat), (i < n)%nat -> (j < n)%nat -> 0 <= delta_pair i j).
  { intros i j Hi Hj; unfold delta_pair; apply Rmult_le_pos; apply d_factor_nonneg. }

  set (K0 := (Rmax 8 ((INR C) ^ 3)) / 4).

  assert (Hdecay : forall idx1 idx2, idx1 <> idx2 -> (idx1 < n)%nat -> (idx2 < n)%nat ->
    Cnorm (Csum (fun k => phi_flat idx1 k *c Cconj (phi_flat idx2 k)) (Nat.pred M))
    <= K0 * delta_pair idx1 idx2).
  {
    intros idx1 idx2 Hneq Hlt1 Hlt2.
    destruct (H_dom idx1 idx2 Hneq Hlt1 Hlt2) as [H_dom_i H_dom_j].

    assert (Ha_eq : a = (fun i => nth i (map seq1 I1) 0%nat)).
    { unfold a, vals1; reflexivity. }
    assert (Hb_eq : b = (fun j => nth j (map seq2 I2) 0%nat)).
    { unfold b, vals2; reflexivity. }
    assert (Hgamma_eq : gamma = (fun i j => sqrt (INR (Nat.min (a i) (b j)) / (INR (a i) * INR (b j))))).
    { unfold gamma, w; reflexivity. }
    assert (Hphi2D_norm_eq : phi2D_norm = (fun i j k => Cof_real (/ gamma i j) *c (psi (a i) k *c psi (b j) k))).
    { unfold phi2D_norm; reflexivity. }
    assert (Hphi_flat_eq : phi_flat = (fun idx k => phi2D_norm ((idx / n2)%nat) ((idx mod n2)%nat) k)).
    { unfold phi_flat; reflexivity. }
    assert (Hdelta_pair_eq : delta_pair = (fun idx1 idx2 => d_factor r ((idx1 / n2)%nat) ((idx2 / n2)%nat) * d_factor r ((idx1 mod n2)%nat) ((idx2 mod n2)%nat))).
    { unfold delta_pair, d1; reflexivity. }

    assert (HmaxIdx1_eq : maxIdx1 = fold_right Nat.max 0%nat I1).
    { unfold maxIdx1; reflexivity. }
    assert (HmaxIdx2_eq : maxIdx2 = fold_right Nat.max 0%nat I2).
    { unfold maxIdx2; reflexivity. }
    assert (HM_eq : M = S (max (seq1 maxIdx1) (seq2 maxIdx2))).
    { unfold M; reflexivity. }
    assert (Hr_eq : r = sqrt (INR C)).
    { unfold r; reflexivity. }

    pose proof (phi_flat_decay_general C Hc_ge2 seq1 seq2
                  Hsparse1 Hsparse2 Hge2_1 Hge2_2
                  I1 I2 Hdup1 Hsorted1 Hdup2 Hsorted2
                  n1 n2 Hn1 Hn2 HI1 HI2
                  a b Ha_eq Hb_eq
                  gamma Hgamma_eq
                  phi2D_norm Hphi2D_norm_eq
                  maxIdx1 maxIdx2 HmaxIdx1_eq HmaxIdx2_eq
                  M HM_eq r Hr_eq
                  phi_flat Hphi_flat_eq
                  delta_pair Hdelta_pair_eq
                  idx1 idx2 Hneq Hlt1 Hlt2
                  (H_index_bound idx1 idx2 Hlt1 Hlt2)
                  (conj H_dom_i H_dom_j)) as Hbound.
    unfold K0; exact Hbound.
  }

  set (M_bound' := K0 * ((1 + 4 * K_C) * (1 + 4 * K_C) - 1)).

  assert (Hc_ge2_R : INR C >= 2) by (apply Rle_ge; change 2 with (INR 2); apply le_INR; exact Hc_ge2).

  assert (Hrow_sum_U : forall idx : nat, (idx < n)%nat ->
    sum_f_R0 (fun jdx : nat => if eq_nat_dec idx jdx then 0 else delta_pair idx jdx) (Nat.pred n)
    <= (1 + 4 * K_C) * (1 + 4 * K_C) - 1).
  {
    intros idx Hlt.
    set (i0 := (idx / n2)%nat); set (j0 := (idx mod n2)%nat).
    assert (Hi0 : (i0 < n1)%nat) by (apply Nat.Div0.div_lt_upper_bound; lia).
    assert (Hj0 : (j0 < n2)%nat) by (apply Nat.mod_upper_bound; lia).
    set (S1 := sum_f_R0 (fun i' => if eq_nat_dec i0 i' then 0 else d1 i0 i') (Nat.pred n1)).
    set (S2 := sum_f_R0 (fun j' => if eq_nat_dec j0 j' then 0 else d1 j0 j') (Nat.pred n2)).

    assert (HS1 : S1 <= 4 * K_C).
    { unfold S1, d1, r, K_C. apply (d_factor_row_sum_le_4K C HCgt2 n1 i0 Hi0). }
    assert (HS2 : S2 <= 4 * K_C).
    { unfold S2, d1, r, K_C. apply (d_factor_row_sum_le_4K C HCgt2 n2 j0 Hj0). }
    assert (HS1_nonneg : 0 <= S1) by (unfold S1; apply sum_f_R0_nonneg; intros i'; destruct (eq_nat_dec i0 i'); [apply Rle_refl | unfold d1; apply d_factor_nonneg]).
    assert (HS2_nonneg : 0 <= S2) by (unfold S2; apply sum_f_R0_nonneg; intros j'; destruct (eq_nat_dec j0 j'); [apply Rle_refl | unfold d1; apply d_factor_nonneg]).
    assert (Hrow_decomp : sum_f_R0 (fun jdx : nat => if eq_nat_dec idx jdx then 0
      else delta_pair idx jdx) (Nat.pred n) = (1 + S1) * (1 + S2) - 1).
    {
      subst n; unfold delta_pair, d1, S1, S2.
      replace (idx / n2)%nat with i0 by (unfold i0; reflexivity).
      replace (idx mod n2)%nat with j0 by (unfold j0; reflexivity).
      assert (Hidx_form : idx = (i0 * n2 + j0)%nat) by (unfold i0, j0; rewrite Nat.mul_comm; apply Nat.div_mod; lia).
      rewrite Hidx_form.
      apply (prod_row_sum_decomp_eq n1 n2 i0 j0 (d_factor r) Hi0 Hj0 (d_factor_diag r)).
    }
    rewrite Hrow_decomp.
    assert (Hprod_ub : (1 + S1) * (1 + S2) - 1 <= (1 + 4 * K_C) * (1 + 4 * K_C) - 1) by nra.
    exact Hprod_ub.
  }

  assert (Hrow_sum : forall idx : nat, (idx < n)%nat ->
    sum_f_R0 (fun jdx : nat => if eq_nat_dec idx jdx then 0
      else delta_pair idx jdx) (Nat.pred n) <= M_bound').
  {
    intros idx Hlt.
    apply Rle_trans with ((1 + 4 * K_C) * (1 + 4 * K_C) - 1).
    - apply Hrow_sum_U; auto.
    - assert (H_K0_ge1 : 1 <= K0).
      {
        unfold K0.
        assert (H_cube_ge_8 : (INR C)^3 >= 8).
        {
          apply Rle_ge. transitivity (2^3).
          - assert (H23 : 2^3 = 8) by (unfold pow; simpl; ring). rewrite H23; lra.
          - apply pow_incr with (x := 2) (y := INR C) (n := 3%nat);
              split; [lra | apply Rge_le; exact Hc_ge2_R].
        }
        assert (Hmax_eq : Rmax 8 ((INR C)^3) = (INR C)^3) by (apply Rmax_right; apply Rge_le; exact H_cube_ge_8).
        rewrite Hmax_eq; lra.
      }
      assert (H_nonneg : 0 <= (1 + 4 * K_C) * (1 + 4 * K_C) - 1) by nra.
      unfold M_bound'.
      apply Rmult_le_compat_r with (r := (1 + 4 * K_C) * (1 + 4 * K_C) - 1) in H_K0_ge1.
      -- rewrite Rmult_1_l in H_K0_ge1.
         exact H_K0_ge1.
      -- exact H_nonneg.
  }

  set (delta_pair_K0 := fun i j : nat => K0 * delta_pair i j).

  assert (Hdelta_sym_K0 : forall i j : nat, (i < n)%nat -> (j < n)%nat ->
    delta_pair_K0 i j = delta_pair_K0 j i).
  { intros i j Hi Hj; unfold delta_pair_K0; rewrite (Hdelta_sym i j Hi Hj); reflexivity. }

  assert (Hdelta_nonneg_K0 : forall i j : nat, (i < n)%nat -> (j < n)%nat ->
    0 <= delta_pair_K0 i j).
  { intros i j Hi Hj; unfold delta_pair_K0; apply Rmult_le_pos.
    - assert (H_K0_nonneg : 0 <= K0).
      { apply Rlt_le; unfold K0; apply Rdiv_lt_0_compat.
        - apply Rlt_le_trans with 8; [lra | apply Rmax_l].
        - lra. }
      exact H_K0_nonneg.
    - apply Hdelta_nonneg; auto. }

  assert (Hdecay_K0 : forall idx1 idx2, idx1 <> idx2 -> (idx1 < n)%nat -> (idx2 < n)%nat ->
    Cnorm (Csum (fun k => phi_flat idx1 k *c Cconj (phi_flat idx2 k)) (Nat.pred M))
    <= delta_pair_K0 idx1 idx2).
  { intros idx1 idx2 Hneq Hlt1 Hlt2; unfold delta_pair_K0; apply Hdecay; auto. }

  assert (Hrow_sum_K0 : forall idx : nat, (idx < n)%nat ->
    sum_f_R0 (fun jdx : nat => if eq_nat_dec idx jdx then 0
      else delta_pair_K0 idx jdx) (Nat.pred n) <= M_bound').
  {
    intros idx Hlt.
    unfold delta_pair_K0.
    assert (Hsum_mult : forall (c : R) (f : nat -> R) (m : nat),
      sum_f_R0 (fun i => c * f i) m = c * sum_f_R0 f m).
    { intros c f m; induction m; simpl; [ring | rewrite IHm; ring]. }
    assert (H_if_eq : forall jdx, (if eq_nat_dec idx jdx then 0 else K0 * delta_pair idx jdx)
      = K0 * (if eq_nat_dec idx jdx then 0 else delta_pair idx jdx)).
    { intros jdx; destruct (eq_nat_dec idx jdx); ring. }
    assert (Hgoal_eq : sum_f_R0 (fun jdx : nat => if eq_nat_dec idx jdx then 0 else K0 * delta_pair idx jdx) (Nat.pred n)
                     = sum_f_R0 (fun jdx : nat => K0 * (if eq_nat_dec idx jdx then 0 else delta_pair idx jdx)) (Nat.pred n)).
    { apply sum_f_R0_ext; intros i Hi; apply H_if_eq. }
    rewrite Hgoal_eq.
    rewrite (Hsum_mult K0 (fun jdx : nat => if eq_nat_dec idx jdx then 0 else delta_pair idx jdx) (Nat.pred n)).
    apply Rmult_le_compat_l.
    { apply Rlt_le; unfold K0; apply Rdiv_lt_0_compat.
      - apply Rlt_le_trans with 8; [lra | apply Rmax_l].
      - lra. }
    apply Hrow_sum_U; auto.
  }

  assert (HM_pos : (M > 0)%nat) by (unfold M; lia).
  pose proof (abstract_unconditional_basis n phi_flat M M_bound'
    delta_pair_K0 HM_pos Htrunc Hnorm1 Hdelta_sym_K0 Hdelta_nonneg_K0 Hdecay_K0 Hrow_sum_K0
    coeffs_flat Hlen_flat) as H_abs.

  assert (HF_flat_eq : forall k,
    Csum (fun i => Csum (fun j => coeffs i j *c phi2D_norm i j k) n2) n1
    = Csum (fun idx : nat => nth idx coeffs_flat C0 *c phi_flat idx k) n).
  { intros k; unfold phi_flat.
    rewrite <- (Csum_flatten n1 n2 (fun i j => coeffs i j *c phi2D_norm i j k)).
    apply Csum_ext'; intros idx Hidx.
    rewrite (Hnth_flat idx Hidx); reflexivity. }

  assert (HS_flat_eq : sum_f_R0 (fun i =>
      sum_f_R0 (fun j => Cnorm_sq (coeffs i j)) (n2 - 1)) (n1 - 1)
    = sum_f_R0 (fun idx : nat => Cnorm_sq (nth idx coeffs_flat C0)) (Nat.pred n)).
  {
    subst n.
    rewrite <- (sum_f_R0_flatten n1 n2 Hn1_pos Hn2_pos (fun i j => Cnorm_sq (coeffs i j))).
    transitivity (sum_f_R0 (fun idx : nat => Cnorm_sq (coeffs (idx / n2)%nat (idx mod n2)%nat))
                          (Nat.pred (n1 * n2))).
    - apply f_equal; lia.
    - apply sum_f_R0_ext; intros idx Hle.
      assert (Hidx_lt : (idx < n1 * n2)%nat) by lia.
      rewrite (Hnth_flat idx Hidx_lt); reflexivity.
  }

  assert (HM_pred_eq : Nat.pred M = (M - 1)%nat) by (unfold M; lia).

  assert (H_final : (1 - M_bound') *
    (sum_f_R0 (fun i => sum_f_R0 (fun j => Cnorm_sq (coeffs i j)) (n2 - 1)) (n1 - 1))
    <= l2_norm_sq (fun k : nat =>
         Csum (fun i => Csum (fun j => coeffs i j *c phi2D_norm i j k) n2) n1) (M - 1)
    <= (1 + M_bound') *
    (sum_f_R0 (fun i => sum_f_R0 (fun j => Cnorm_sq (coeffs i j)) (n2 - 1)) (n1 - 1))).
  {
    set (F := fun k : nat => Csum (fun idx : nat => nth idx coeffs_flat C0 *c phi_flat idx k) n).
    cbv zeta in H_abs.
    destruct H_abs as [H_low H_high].
    assert (H_eq : l2_norm_sq (fun k : nat =>
        Csum (fun i => Csum (fun j => coeffs i j *c phi2D_norm i j k) n2) n1) (M - 1)
        = l2_norm_sq F (Nat.pred M)).
    {
      unfold l2_norm_sq.
      rewrite <- HM_pred_eq.
      apply sum_f_R0_ext; intros k Hk.
      rewrite (HF_flat_eq k); reflexivity.
    }
    rewrite H_eq, HS_flat_eq.
    unfold F.
    exact (conj H_low H_high).
  }
  apply H_final.
Qed.

(* ============ 顶层 soundness：frame_check_2d_narrow_sound（会话 15 新增） ============ *)
(* frame_check_2d_narrow cC vals1 vals2 = true（两轴 sorted/ge2/增长/单带/支配/曼哈顿）
   ⟹ 对任意系数矩阵，2D 窄轨无条件基界成立：
     (1 - M_bound) S ≤ l2_norm_sq F_2D (M-1) ≤ (1 + M_bound) S
   M_bound = K0·((1+4K_C)²−1)，K0 = Rmax 8 (C³) / 4。 *)
Theorem frame_check_2d_narrow_sound (cC : nat) (vals1 vals2 : list nat) :
  (cC > 2)%nat -> (0 < length vals1)%nat -> (0 < length vals2)%nat ->
  frame_check_2d_narrow cC vals1 vals2 = true ->
  forall coeffs : nat -> nat -> Complex,
    let n1 := length vals1 in
    let n2 := length vals2 in
    let I1 := seq 0 n1 in
    let I2 := seq 0 n2 in
    let seq1 := seq_ext vals1 cC in
    let seq2 := seq_ext vals2 cC in
    let vals1' := map seq1 I1 in
    let vals2' := map seq2 I2 in
    let a i := nth i vals1' 0%nat in
    let b j := nth j vals2' 0%nat in
    let w i j := INR (Nat.min (a i) (b j)) / (INR (a i) * INR (b j)) in
    let gamma i j := sqrt (w i j) in
    let phi2D_norm (i j : nat) (k : nat) : Complex :=
      Cof_real (/ gamma i j) *c (psi (a i) k *c psi (b j) k) in
    let F_2D (k : nat) : Complex :=
      Csum (fun i => Csum (fun j => coeffs i j *c phi2D_norm i j k) n2) n1 in
    let maxIdx1 := fold_right Nat.max 0%nat I1 in
    let maxIdx2 := fold_right Nat.max 0%nat I2 in
    let M := S (max (seq1 maxIdx1) (seq2 maxIdx2)) in
    let S := sum_f_R0 (fun i =>
               sum_f_R0 (fun j => Cnorm_sq (coeffs i j)) (n2 - 1)) (n1 - 1) in
    let K_C := K (INR cC) in
    let K0 := (Rmax 8 ((INR cC) ^ 3)) / 4 in
    let M_bound := K0 * ((1 + 4 * K_C) * (1 + 4 * K_C) - 1) in
    ((1 - M_bound) * S <= l2_norm_sq F_2D (M - 1) <= (1 + M_bound) * S)%R.
Proof.
  intros Hc Hlen1 Hlen2 Hfc coeffs.
  unfold frame_check_2d_narrow in Hfc.
  (* && 左结合：((s1&&s2)&&(g1&&g2))&&(cg1&&cg2) 再 && single_band(dom&&man) *)
  apply andb_true_iff in Hfc. destruct Hfc as [Habc Hrest].
  apply andb_true_iff in Habc. destruct Habc as [Hab Hcg12].
  apply andb_true_iff in Hab. destruct Hab as [Hs12 Hg12].
  apply andb_true_iff in Hrest. destruct Hrest as [Hsb Hrest].
  apply andb_true_iff in Hrest. destruct Hrest as [Hdom Hman].
  apply andb_true_iff in Hs12. destruct Hs12 as [Hs1 Hs2].
  apply andb_true_iff in Hg12. destruct Hg12 as [Hg1 Hg2].
  apply andb_true_iff in Hcg12. destruct Hcg12 as [Hcg1 Hcg2].

  cbv zeta.
  set (n1 := length vals1).
  set (n2 := length vals2).
  set (I1 := seq 0 n1).
  set (I2 := seq 0 n2).
  set (seq1 := seq_ext vals1 cC).
  set (seq2 := seq_ext vals2 cC).

  assert (Hc_ge2 : (cC >= 2)%nat) by lia.

  (* Hsparse1/2：seq_ext 全局增长 *)
  assert (Hsparse1 : forall i : nat, (INR (seq1 (S i)) > INR cC * INR (seq1 i))%R).
  { intro i; unfold seq1; apply (seq_ext_growth_R vals1 cC Hc_ge2 Hlen1 Hcg1 Hg1 i). }
  assert (Hsparse2 : forall i : nat, (INR (seq2 (S i)) > INR cC * INR (seq2 i))%R).
  { intro i; unfold seq2; apply (seq_ext_growth_R vals2 cC Hc_ge2 Hlen2 Hcg2 Hg2 i). }

  (* Hge2_1/2：全局 ≥2 *)
  assert (Hge2_1 : forall i : nat, (seq1 i >= 2)%nat).
  { intro i; unfold seq1; apply (seq_ext_ge2 vals1 cC Hc_ge2 Hlen1 Hg1 i). }
  assert (Hge2_2 : forall i : nat, (seq2 i >= 2)%nat).
  { intro i; unfold seq2; apply (seq_ext_ge2 vals2 cC Hc_ge2 Hlen2 Hg2 i). }

  (* I1/I2：NoDup + Sorted + n1/n2 对齐 *)
  assert (Hdup1 : NoDup I1) by (unfold I1; apply seq_NoDup).
  assert (Hsorted1 : Sorted Nat.lt I1) by (unfold I1; apply sorted_seq_0).
  assert (Hdup2 : NoDup I2) by (unfold I2; apply seq_NoDup).
  assert (Hsorted2 : Sorted Nat.lt I2) by (unfold I2; apply sorted_seq_0).
  assert (Hn1_eq : n1 = length I1) by (unfold I1, n1; rewrite length_seq; reflexivity).
  assert (Hn2_eq : n2 = length I2) by (unfold I2, n2; rewrite length_seq; reflexivity).
  assert (Hn1_pos : (n1 > 0)%nat) by (unfold n1; lia).
  assert (Hn2_pos : (n2 > 0)%nat) by (unfold n2; lia).
  assert (HI1 : I1 = seq 0 n1) by (unfold I1; reflexivity).
  assert (HI2 : I2 = seq 0 n2) by (unfold I2; reflexivity).

  (* H_dom：由 hdom_2d_narrow 给出（点态） *)
  assert (H_dom : forall idx1 idx2 : nat, idx1 <> idx2 ->
      (idx1 < n1 * n2)%nat -> (idx2 < n1 * n2)%nat ->
      ((idx1 / n2)%nat = (idx2 / n2)%nat ->
       (seq1 ((idx1 / n2)%nat) >= Nat.max (seq2 ((idx1 mod n2)%nat)) (seq2 ((idx2 mod n2)%nat)))%nat) /\
      ((idx1 mod n2)%nat = (idx2 mod n2)%nat ->
       (seq2 ((idx1 mod n2)%nat) >= Nat.max (seq1 ((idx1 / n2)%nat)) (seq1 ((idx2 / n2)%nat)))%nat)).
  { intros idx1 idx2 Hneq Hlt1' Hlt2'.
    assert (Hn1_r : (n1 = length vals1)%nat) by (unfold n1; reflexivity).
    assert (Hn2_r : (n2 = length vals2)%nat) by (unfold n2; reflexivity).
    pose proof (hdom_2d_narrow vals1 vals2 cC n1 n2 Hn1_r Hn2_r Hsb Hdom idx1 idx2 Hneq Hlt1' Hlt2')
      as Hdom_pair.
    unfold seq1, seq2 in Hdom_pair.
    exact Hdom_pair. }

  (* H_index_bound：由 manhattan_ok（n1+n2 ≤ 8）给出 *)
  assert (Hman_le : (n1 + n2 <= 8)%nat).
  { unfold n1, n2; apply Nat.leb_le. exact Hman. }
  assert (H_index_bound : forall idx1 idx2 : nat,
      (idx1 < n1 * n2)%nat -> (idx2 < n1 * n2)%nat ->
      (Z.abs_nat (Z.of_nat (idx1 / n2) - Z.of_nat (idx2 / n2)) +
       Z.abs_nat (Z.of_nat (idx1 mod n2) - Z.of_nat (idx2 mod n2)) <= 6)%nat).
  { intros idx1 idx2 Hlt1 Hlt2.
    apply (index_bound_2d n1 n2 idx1 idx2 Hn1_pos Hn2_pos Hman_le Hlt1 Hlt2). }

  pose proof (tensor_product_unconditional_basis_pointwise cC Hc
    seq1 seq2 Hsparse1 Hsparse2 Hge2_1 Hge2_2
    I1 I2 Hdup1 Hsorted1 Hdup2 Hsorted2
    coeffs n1 n2 Hn1_eq Hn2_eq Hn1_pos Hn2_pos HI1 HI2
    H_dom H_index_bound) as H_asm.
  cbv zeta in H_asm.
  exact H_asm.
Qed.
End FrameCheck2DNarrow.

(* ============================================================
   A2 酉不变性（2026-08-20 会话 17，探针 src\_probe_unitary.v 验证 RC=0 后并入）
   ------------------------------------------------------------
   论文 A/B §4「旋转组（psi-rope）是酉变换」的形式化（unitary_invariance_frame）：
   - rot_preserves_inner：单位模 u（Cnorm_sq u = 1）⟹ (u·x)·conj(u·y) = x·conj y（酉性步骤）
   - unitary_invariance_point：全局保内积 U ⟹ ‖Σ U(g_i)‖² = ‖Σ g_i‖²（核心定理）
   - unitary_invariance_rope_point / _rope：逐点单位模 ⟹ 位置索引旋转保 l2 范数（RoPE 算子酉性）
   - unitary_invariance_psi_rope / _psi_rope_global：psi-rope 实例（因子形式 / 内和形式）
   注：带索引逐点版本（每带乘 u_i 后对和取模）为假命题（反例 u0=1,u1=-1,g0=g1=1，
       |1-1|²=0≠4=|1+1|²），未并入；带索引 l2 等式需基精确正交（本 psi 族截断窗口
       交叉项非零，由 (1±4/5) 帧界路线覆盖）。
   ============================================================ *)
Module UnitaryInvariance.

Import ExtendedTheorems.
Open Scope R_scope.

(* 1a. 分解恒等式（无假设，纯展开）：(u*x)·conj(u*y) = (u·conj u)·(x·conj y) *)
Lemma rot_preserves_inner_aux (u x y : Complex) :
  (u *c x) *c Cconj (u *c y) = (u *c Cconj u) *c (x *c Cconj y).
Proof.
  destruct u as [a b]; destruct x as [c d]; destruct y as [e f].
  unfold Cmul, Cconj; simpl; f_equal; ring.
Qed.

(* 1b. 单位模 ⟹ u·conj u = C1（= 1+i0） *)
Lemma Cconj_mul_self (u : Complex) (Hu : Cnorm_sq u = 1) : u *c Cconj u = C1.
Proof.
  destruct u as [a b].
  unfold Cmul, Cconj, Cnorm_sq, Rsqr, C1 in *.
  simpl in Hu.
  simpl; f_equal.
  - nra.
  - nra.
Qed.

(* 1. 旋转保内积：u 单位模（Cnorm_sq u = 1）⟹ (u*x)·conj(u*y) = x·conj y（酉性步骤） *)
Lemma rot_preserves_inner (u : Complex) (Hu : Cnorm_sq u = 1) :
  forall x y, (u *c x) *c Cconj (u *c y) = x *c Cconj y.
Proof.
  intros x y.
  rewrite rot_preserves_inner_aux.
  rewrite (Cconj_mul_self u Hu).
  rewrite Cmul_1_l.
  reflexivity.
Qed.

(* 2. 全局酉不变性：U 保内积 ⟹ ‖Σ U(g_i)‖² = ‖Σ g_i‖²（unitary_invariance_frame 正确定型） *)
Lemma unitary_invariance_point (U : Complex -> Complex)
  (H_unitary : forall x y, U x *c Cconj (U y) = x *c Cconj y) :
  forall (g : nat -> Complex) (n : nat),
  Cnorm_sq (Csum (fun i => U (g i)) n) = Cnorm_sq (Csum g n).
Proof.
  intros g n.
  destruct n as [|n].
  - simpl; reflexivity.
  - rewrite (Cnorm_sq_csum (fun i => U (g i)) (S n)).
    rewrite (Cnorm_sq_csum g (S n)).
    (* 只约掉 match (S n)，不展开 re (x *c Cconj y)（否则 f_equal 失配） *)
    change (sum_f_R0 (fun i : nat => sum_f_R0 (fun j : nat => re (U (g i) *c Cconj (U (g j)))) n) n
          = sum_f_R0 (fun i : nat => sum_f_R0 (fun j : nat => re (g i *c Cconj (g j))) n) n).
    apply sum_f_R0_ext; intros i _.
    apply sum_f_R0_ext; intros j _.
    apply f_equal.
    apply H_unitary.
Qed.

(* 3. 逐点单位模保模（对角 / 每位置）：Cnorm_sq u = 1 ⟹ ‖u·S‖² = ‖S‖² *)
Lemma unitary_invariance_rope_point (u S : Complex) (Hu : Cnorm_sq u = 1) :
  Cnorm_sq (u *c S) = Cnorm_sq S.
Proof.
  destruct u as [a b]; destruct S as [c d].
  unfold Cmul, Cnorm_sq, Rsqr in *.
  simpl in Hu.
  simpl.
  nra.
Qed.

(* 4. 位置索引旋转保 l2 范数（psi-rope / RoPE 算子酉性）：每位置乘单位模 u k ⟹ ‖u·F‖²_N = ‖F‖²_N *)
Lemma unitary_invariance_rope (u : nat -> Complex) (Hu : forall k, Cnorm_sq (u k) = 1) :
  forall (F : nat -> Complex) (N : nat),
  l2_norm_sq (fun k => u k *c F k) N = l2_norm_sq F N.
Proof.
  intros F N.
  unfold l2_norm_sq.
  apply sum_f_R0_ext; intros k _.
  apply (unitary_invariance_rope_point (u k) (F k) (Hu k)).
Qed.

(* 5. psi-rope 实例（因子形式）：‖Σ_i c_i·ψ_i‖²_N 在逐点乘 u k 后不变 *)
Theorem unitary_invariance_psi_rope (vals : list nat) (u : nat -> Complex)
  (Hu : forall k, Cnorm_sq (u k) = 1)
  (coeffs : list Complex) (n N : nat) :
  l2_norm_sq (fun k => u k *c Csum (fun i => nth i coeffs C0 *c psi (nth i vals 0%nat) k) n) N
  = l2_norm_sq (fun k => Csum (fun i => nth i coeffs C0 *c psi (nth i vals 0%nat) k) n) N.
Proof.
  apply (unitary_invariance_rope u Hu
           (fun k => Csum (fun i => nth i coeffs C0 *c psi (nth i vals 0%nat) k) n) N).
Qed.

(* 6. psi-rope 实例（内和形式）：u k 作用于每个基函数值——经全局酉不变性（lemma 2 + 1）给出 *)
Theorem unitary_invariance_psi_rope_global (vals : list nat) (u : nat -> Complex)
  (Hu : forall k, Cnorm_sq (u k) = 1)
  (coeffs : list Complex) (n N : nat) :
  l2_norm_sq (fun k => Csum (fun i => u k *c (nth i coeffs C0 *c psi (nth i vals 0%nat) k)) n) N
  = l2_norm_sq (fun k => Csum (fun i => nth i coeffs C0 *c psi (nth i vals 0%nat) k) n) N.
Proof.
  unfold l2_norm_sq.
  apply sum_f_R0_ext; intros k _.
  apply (unitary_invariance_point (fun x => u k *c x) (rot_preserves_inner (u k) (Hu k))
           (fun i => nth i coeffs C0 *c psi (nth i vals 0%nat) k) n).
Qed.

(* 7. RoPE 显式实例（评审 §1 修复，2026-08-20 会话 17）：θ k 为逐位置旋转角 ⟹
   u k := Cexp (0 +i (INR k * θ k))（单位模标量）覆盖 psi-rope 的 2×2 块旋转——
   SO(2) 与 U(1) 同构，维度对 (x1,x2) 上的 [cosθ −sinθ; sinθ cosθ] 即复数乘法
   (x1 + i·x2)·e^{iθ} 的实/虚部（length_extrap.py apply_rope_theta 逐行对应）。 *)
Lemma Cexp_unit_mod (θ : R) : Cnorm_sq (Cexp (0 +i θ)) = 1.
Proof.
  unfold Cexp, Cnorm_sq.
  simpl.
  rewrite exp_0.
  replace (1 * cos θ) with (cos θ) by ring.
  replace (1 * sin θ) with (sin θ) by ring.
  replace (Rsqr (cos θ) + Rsqr (sin θ)) with (Rsqr (sin θ) + Rsqr (cos θ)) by (unfold Rsqr; ring).
  apply sin2_cos2.
Qed.

Theorem unitary_invariance_psi_rope_theta (θ : nat -> R) (vals : list nat)
  (coeffs : list Complex) (n N : nat) :
  l2_norm_sq (fun k => Csum (fun i => Cexp (0 +i (INR k * θ k)) *c (nth i coeffs C0 *c psi (nth i vals 0%nat) k)) n) N
  = l2_norm_sq (fun k => Csum (fun i => nth i coeffs C0 *c psi (nth i vals 0%nat) k) n) N.
Proof.
  apply (unitary_invariance_psi_rope_global vals (fun k => Cexp (0 +i (INR k * θ k)))
           (fun k => Cexp_unit_mod (INR k * θ k)) coeffs n N).
Qed.

End UnitaryInvariance.
Module PhaseCoherence.

Import RowTruncation.
Import SoftmaxStability.
Open Scope R_scope.

(* ---------- list_sum_R 线性（fold_right 展开） ---------- *)

Lemma list_sum_R_plus (f g : nat -> R) (l : list nat) :
  list_sum_R (fun i => f i + g i) l = (list_sum_R f l + list_sum_R g l)%R.
Proof.
  unfold list_sum_R. induction l as [| h t IH]; simpl; [ring | rewrite IH; ring].
Qed.

Lemma list_sum_R_neg (f : nat -> R) (l : list nat) :
  list_sum_R (fun i => - f i) l = (- list_sum_R f l)%R.
Proof.
  unfold list_sum_R. induction l as [| h t IH]; simpl; [ring | rewrite IH; ring].
Qed.

Lemma list_sum_R_scale_l (f : nat -> R) (c : R) (l : list nat) :
  list_sum_R (fun i => c * f i) l = (c * list_sum_R f l)%R.
Proof.
  unfold list_sum_R. induction l as [| h t IH]; simpl; [ring | rewrite IH; ring].
Qed.

Lemma list_sum_R_scale_r (f : nat -> R) (c : R) (l : list nat) :
  list_sum_R (fun i => f i * c) l = (list_sum_R f l * c)%R.
Proof.
  unfold list_sum_R. induction l as [| h t IH]; simpl; [ring | rewrite IH; ring].
Qed.

(* 外延：逐点相等 ⟹ 和相等（不需要全局 funext） *)
Lemma list_sum_R_ext (f g : nat -> R) (l : list nat) :
  (forall i, In i l -> f i = g i) -> list_sum_R f l = list_sum_R g l.
Proof.
  induction l as [| h t IH]; simpl; intro H.
  - reflexivity.
  - rewrite (H h (or_introl eq_refl)). rewrite (IH (fun i Hi => H i (or_intror Hi))). reflexivity.
Qed.

(* ---------- 和的绝对三角不等式 ---------- *)

Lemma list_sum_R_abs (f : nat -> R) (l : list nat) :
  (Rabs (list_sum_R f l) <= list_sum_R (fun i => Rabs (f i)) l)%R.
Proof.
  unfold list_sum_R. induction l as [| h t IH]; simpl.
  - rewrite Rabs_R0. apply Rle_refl.
  - apply Rle_trans with (Rabs (f h) + Rabs (fold_right (fun i acc => f i + acc) 0%R t))%R.
    + apply Rabs_triang.
    + apply Rplus_le_compat_l; exact IH.
Qed.

(* ---------- 步骤 1：logit 扰动界 ---------- *)

(* In j (seq 0 n) ⟹ j < n *)
Lemma In_seq_lt (j n : nat) :
  In j (seq 0%nat n) -> (j < n)%nat.
Proof.
  intro Hj.
  destruct (In_nth (seq 0%nat n) j 0%nat Hj) as [k [Hk Hkth]].
  rewrite length_seq in Hk.
  assert (Hkseq : (nth k (seq 0%nat n) 0%nat = k)%nat)
    by (rewrite (@seq_nth n 0%nat k 0%nat Hk); lia).
  rewrite Hkth in Hkseq. lia.
Qed.

(* |z_i - z'_i| <= coh·delta，其中 z_i = Σ_j c_j·K_ij，z'_i = Σ_j c'_j·K_ij *)
Lemma coh_logit_bound (K : nat -> nat -> R) (c c' : nat -> R) (n i : nat)
  (coh delta : R) :
  (i < n)%nat -> (0 <= coh)%R ->
  (forall i0 j, (i0 < n)%nat -> (j < n)%nat -> (Rabs (K i0 j) <= coh)%R) ->
  (list_sum_R (fun j => Rabs (c j - c' j)) (seq 0%nat n) <= delta)%R ->
  (Rabs (list_sum_R (fun j => (c j - c' j) * K i j) (seq 0%nat n)) <= coh * delta)%R.
Proof.
  intros Hi Hcoh HK Hdelta.
  apply Rle_trans with (list_sum_R (fun j => Rabs ((c j - c' j) * K i j)) (seq 0%nat n)).
  - apply list_sum_R_abs.
  - apply Rle_trans with (list_sum_R (fun j => Rabs (c j - c' j) * coh) (seq 0%nat n)).
    + apply list_sum_R_le_compat. intros j0 Hj0.
      rewrite Rabs_mult.
      apply Rmult_le_compat_l.
      * apply Rabs_pos.
      * apply HK; [exact Hi | apply In_seq_lt; exact Hj0].
    + rewrite (list_sum_R_scale_r (fun j => Rabs (c j - c' j)) coh (seq 0%nat n)).
      replace (coh * delta) with (delta * coh)%R by ring.
      apply Rmult_le_compat_r; [exact Hcoh | exact Hdelta].
Qed.

(* ---------- 步骤 2+3：softmax_l1_bound_exp 组合（主定理） ---------- *)

(* 抽象相干-softmax 桥接引理（abstract lemma，评审 12）：参数化于任意相干核 K，
   不绑定 ψ 基或学习投影层——实例化到具体阶梯为后续工作。 *)
Theorem coherence_controls_attention (K : nat -> nat -> R) (c c' : nat -> R)
  (n : nat) (coh delta : R) :
  (0 < n)%nat -> (0 <= coh)%R -> (0 <= delta)%R ->
  (forall i j, (i < n)%nat -> (j < n)%nat -> (Rabs (K i j) <= coh)%R) ->
  (list_sum_R (fun j => Rabs (c j - c' j)) (seq 0%nat n) <= delta)%R ->
  (list_sum_R (fun i => Rabs
     (softmax_l (fun i => list_sum_R (fun j => c j * K i j) (seq 0%nat n)) n i
      - softmax_l (fun i => list_sum_R (fun j => c' j * K i j) (seq 0%nat n)) n i))
     (seq 0%nat n) <= exp (2 * (coh * delta)) - 1)%R.
Proof.
  intros Hn Hcoh Hdelta HK Hd.
  (* 1. logit 扰动：|z_i - z'_i| <= coh·delta *)
  assert (Hz : forall i, (i < n)%nat ->
    (Rabs (list_sum_R (fun j => c j * K i j) (seq 0%nat n)
        - list_sum_R (fun j => c' j * K i j) (seq 0%nat n)) <= coh * delta)%R).
  { intros i Hi.
    replace (list_sum_R (fun j => c j * K i j) (seq 0%nat n)
             - list_sum_R (fun j => c' j * K i j) (seq 0%nat n))
      with (list_sum_R (fun j => (c j - c' j) * K i j) (seq 0%nat n)).
    - apply coh_logit_bound; auto.
    - replace (list_sum_R (fun j => c j * K i j) (seq 0%nat n)
               - list_sum_R (fun j => c' j * K i j) (seq 0%nat n))
        with (list_sum_R (fun j => c j * K i j) (seq 0%nat n)
              + (- list_sum_R (fun j => c' j * K i j) (seq 0%nat n)))%R by ring.
      rewrite <- (list_sum_R_neg (fun j => c' j * K i j) (seq 0%nat n)).
      rewrite <- (list_sum_R_plus (fun j => c j * K i j)
                                  (fun j => - (c' j * K i j)) (seq 0%nat n)).
      apply list_sum_R_ext. intros j0 Hj0. ring.
  }
  (* 2. softmax_l1_bound_exp *)
  apply (softmax_l1_bound_exp
           (fun i => list_sum_R (fun j => c j * K i j) (seq 0%nat n))
           (fun i => list_sum_R (fun j => c' j * K i j) (seq 0%nat n))
           n (coh * delta) Hn).
  - apply Rmult_le_pos; auto.
  - intros k Hk. apply Hz. exact Hk.
Qed.

End PhaseCoherence.
