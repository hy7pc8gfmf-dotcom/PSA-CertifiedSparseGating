(* 拆分自 Riemann_Hypothesis_Proof_Framework.v（复分析证明库 v6.0）*)
(* 库: ca_sparse_ext  原文行区间: 36343-36658  机械拆分，未改动内容 *)

Require Import Stdlib.Reals.Reals.          (* 实数公理系统及全套定理 *)
Require Import Stdlib.Reals.Rdefinitions.  (* 实数的原始定义（0,1,加法,乘法等）*)
Require Import Stdlib.Reals.RIneq.         (* 实数不等式基本引理 *)
Require Import Stdlib.Reals.Rtrigo_def.    (* 三角函数定义（sin, cos, PI）*)
Require Import Stdlib.Reals.Rtrigo1.       (* 三角函数基本性质（恒等式、单调性）*)
Require Import Stdlib.Reals.Rsqrt_def.     (* 平方根函数 sqrt 的定义 *)
Require Import Stdlib.Reals.Ranalysis1.    (* 一元实分析基础（导数、可导性、连续性）*)
Require Import Stdlib.Reals.Ranalysis.     (* 实分析汇总模块（包含 Ranalysis1-5）*)
Require Import Stdlib.Reals.Ranalysis3.    (* 高级导数定理（链式法则、反函数定理等）*)
Require Import Stdlib.Reals.Rpower.        (* 实数幂函数 Rpower 及其性质 *)
Require Import Stdlib.Lists.List.          (* 标准列表库，提供列表类型及常用操作 *)
Require Import Stdlib.Arith.Arith.         (* 自然数算术基础库 *)
Require Import Stdlib.Init.Nat.            (* 自然数初始化模块，定义 nat 类型及基本运算 *)
Require Import Stdlib.Classes.RelationClasses.  (* 关系类，定义 Reflexive, Symmetric, Transitive 等 *)
Require Import Stdlib.Program.Basics.      (* 编程基础，提供 id, compose 等函数 *)
Require Import Stdlib.Reals.R_sqrt.        (* 平方根函数及其性质（与 Rsqrt_def 类似）*)
Require Import Stdlib.Logic.ProofIrrelevance.   (* 证明无关性公理 *)
Require Import Stdlib.Logic.Classical.     (* 经典逻辑（排中律）*)
Require Import Stdlib.Logic.FunctionalExtensionality. (* 函数外延性公理 *)
Require Import Stdlib.Logic.IndefiniteDescription. (* 不定描述原理 *)
Require Import Stdlib.Classes.Morphisms.   (* 态射类，用于 Proper 等 *)
Require Import Stdlib.Classes.RelationPairs. (* 关系对组合 *)
Require Import Stdlib.Arith.PeanoNat.      (* 皮亚诺自然数算术，包含加法、乘法、比较等 *)
Require Import Stdlib.ZArith.ZArith.       (* 整数算术总集 *)
Require Import Stdlib.ZArith.Zdiv.         (* 整数除法 *)
Require Import Stdlib.micromega.Lia.       (* 线性整数算术自动化策略（用于 lia）*)
Require Import Stdlib.Strings.String.      (* 字符串类型及操作（用于调试/注释）*)
Require Import Stdlib.micromega.Lra.       (* 线性实数算术自动化策略（用于 lra）*)
From Stdlib Require Import Lia.            (* 再次导入 Lia，确保可用（冗余）*)
  
Local Open Scope R_scope.               (* 开启实数作用域，使实数运算符自动生效 *)
  
(* 导入 Rolle 定理所需的库 *)
From Stdlib Require Ranalysis5.              (* 包含 Rolle 定理的高级分析模块 *)
Open Scope R_scope.

Require Import ca_base ca_algebra ca_primes ca_complex_analysis ca_fourier ca_zeta_scaffold ca_trig ca_gamma ca_taylor ca_zeta_axioms ca_complex_log ca_complex_foundation ca_log_bounds ca_independence ca_prime_power ca_basis ca_basis_lemmas ca_probabilistic.

Require Import Stdlib.Logic.IndefiniteDescription.
Require Import Stdlib.Reals.Reals.
Require Import Stdlib.Reals.Rtrigo1.
Require Import Stdlib.Reals.Rpower.
Require Import Stdlib.Reals.Rseries.
Require Import Stdlib.Logic.ProofIrrelevance.
Require Import Stdlib.micromega.Lra.
Local Open Scope R_scope.
Import ComplexNumbers.
Import ConstructivePrimes.
Import PrimeEmbedding.
Import FourierAnalysis.
Import ComplexLogarithm.
Require Import Stdlib.Reals.Reals.
Require Import Stdlib.Reals.Rtrigo1.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lra.
From Stdlib Require List.
Local Open Scope R_scope.
Local Open Scope complex_scope.
Local Close Scope R_scope.  (* 确保使用 nat 算术 *)
Require Import Stdlib.Reals.Reals.
Require Import Stdlib.Reals.Rtrigo1.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lra.
Import ComplexNumbers.
Import independent independent'.
Import independent.
Import independent'.
Import List.
Import Nat.
Import ComplexNumbers.
Local Open Scope complex_scope.
Local Open Scope R_scope.
Local Close Scope R_scope.
Require Import Stdlib.Reals.Reals.
Require Import Stdlib.Lists.List.
Import ComplexNumbers.
Import independent.
Import independent'.
Import PrimePowerIndependent.
Local Open Scope complex_scope.
Local Open Scope R_scope.
Require Import Stdlib.Reals.Reals.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lra.
Import independent.
Import independent'.
Import PrimePowerIndependent.
Import UnconditionalBasis.
Import ComplexNumbers.
Local Open Scope complex_scope.
Local Open Scope R_scope.
Local Close Scope R_scope.
Local Open Scope nat_scope.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lra.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.NArith.NArith.
Require Import Stdlib.Sorting.Sorted.
Require Import Stdlib.Reals.Reals.
Require Import Stdlib.Lists.List.
Import ListNotations.
Local Open Scope R_scope.
Import independent.
Import independent'.
Import UnconditionalBasisLemmas.

Require Import Stdlib.Reals.Reals.
Require Import Stdlib.micromega.Lra.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.Lists.List.
Import independent.
Import independent'.
Import UnconditionalBasisLemmas.
Import ProbabilisticSparseBasis.

Local Open Scope nat_scope.
Local Open Scope R_scope.

Module SparseInnerBoundExtensions.

(* 分母缩放 *)
Lemma denom_scale_lemma (n1 n2 c : nat) (M : R) :
  (c >= 2)%nat -> (n1 >= 2)%nat -> (n2 >= 2)%nat -> (n1 < n2)%nat ->
  (M >= INR c)%R -> (INR n2 >= INR c * INR n1)%R ->
  (sqrt (INR n1 * INR n2) / (M * (INR n2 - INR n1)) <=
   sqrt (INR n1 / INR n2) / (sqrt (INR c) - 1))%R.
Proof.
  intros Hc Hn1 Hn2 Hlt HM Hineq.
  assert (Hdiff_pos : (0 < INR n2 - INR n1)%R).
  { apply Rgt_minus. apply lt_INR; exact Hlt. }
  assert (Hc_pos : (0 < INR c)%R) by (apply lt_0_INR; lia).
  assert (Hcore : (sqrt (INR n1 * INR n2) / (INR c * (INR n2 - INR n1)) <=
                  sqrt (INR n1 / INR n2) / (sqrt (INR c) - 1))%R).
  { exact (core_algebraic_inequality_general n1 n2 c Hn1 Hn2 Hlt Hc Hineq). }
  assert (Hdenom_le : (INR c * (INR n2 - INR n1) <= M * (INR n2 - INR n1))%R).
  { apply Rmult_le_compat_r; [left; exact Hdiff_pos | apply Rge_le; exact HM]. }
  assert (Hleft_smaller : (sqrt (INR n1 * INR n2) / (M * (INR n2 - INR n1)) <=
                           sqrt (INR n1 * INR n2) / (INR c * (INR n2 - INR n1)))%R).
  {
    unfold Rdiv.
    apply Rmult_le_compat_l.
    - apply Rlt_le, sqrt_lt_R0_c; apply Rmult_lt_0_compat; apply lt_0_INR; lia.
    - apply Rinv_le_contravar.
      + apply Rmult_lt_0_compat; [exact Hc_pos | exact Hdiff_pos].
      + exact Hdenom_le.
  }
  eapply Rle_trans; [exact Hleft_smaller | exact Hcore].
Qed.

(* 缩放与eps因子的不等式 *)
Lemma scale_by_r_and_eps (c : nat) (n1 n2 : nat) (eps r : R) :
  (c >= 2)%nat -> (n1 >= 2)%nat -> (n2 >= 2)%nat ->
  (eps > 0)%R -> (r >= 0)%R ->
  ((sqrt (INR n1 / INR n2) / (sqrt (INR c) - 1)) * r <=
   ((1 + eps) * sqrt (INR n1 / INR n2) / (sqrt (INR c) - 1)) * r)%R.
Proof.
  intros Hc Hn1 Hn2 Heps Hr.
  apply Rmult_le_compat_r. 
  { apply Rge_le; exact Hr. }
  unfold Rdiv.
  apply Rmult_le_compat_r with (r := / (sqrt (INR c) - 1)).
  { left. apply Rinv_0_lt_compat. apply sqrt_c_minus_1_pos; lia. }
  assert (H_sqrt_nonneg : (0 <= sqrt (INR n1 * / INR n2))%R).
  { apply Rlt_le, sqrt_lt_R0_c; apply Rmult_lt_0_compat.
    - apply lt_0_INR; lia.
    - apply Rinv_0_lt_compat; apply lt_0_INR; lia. }
  rewrite <- (Rmult_1_l (sqrt (INR n1 * / INR n2))) at 1.
  apply Rmult_le_compat_r.
  - exact H_sqrt_nonneg.
  - lra.
Qed.

(* 定理：广义一维稀疏内积界 *)
Theorem sparse_inner_bound_generalized (c : nat) (n1 n2 : nat) (M eps r : R) :
  (c >= 2)%nat -> (n1 >= 2)%nat -> (n2 >= 2)%nat -> (n1 < n2)%nat ->
  (M >= INR c)%R -> (eps > 0)%R -> (r >= 0)%R ->
  (INR n2 >= INR c * INR n1)%R ->
  (sqrt (INR n1 * INR n2) / (M * (INR n2 - INR n1)) * r <=
   (1 + eps) * sqrt (INR n1 / INR n2) / (sqrt (INR c) - 1) * r)%R.
Proof.
  intros Hc Hn1 Hn2 Hlt HM Heps Hr Hineq.
  pose proof (denom_scale_lemma n1 n2 c M Hc Hn1 Hn2 Hlt HM Hineq) as Hcore.
  assert (Hcore_r : ((sqrt (INR n1 * INR n2) / (M * (INR n2 - INR n1))) * r <=
                     (sqrt (INR n1 / INR n2) / (sqrt (INR c) - 1)) * r)%R).
  { apply Rmult_le_compat_r; [apply Rge_le; exact Hr | exact Hcore]. }
  pose proof (scale_by_r_and_eps c n1 n2 eps r Hc Hn1 Hn2 Heps Hr) as H_scale.
  eapply Rle_trans; [exact Hcore_r | exact H_scale].
Qed.

(* 二维乘积化简 *)
Lemma simplify_2D_right_product (n1x n1y n2x n2y : nat) (c : nat) (eps : R) :
  (c >= 2)%nat -> (n1x >= 2)%nat -> (n1y >= 2)%nat -> (n2x >= 2)%nat -> (n2y >= 2)%nat ->
  ((1 + eps) * sqrt (INR n1x / INR n2x) / (sqrt (INR c) - 1) *
   ((1 + eps) * sqrt (INR n1y / INR n2y) / (sqrt (INR c) - 1)) =
   (1 + eps)^2 * sqrt ((INR n1x * INR n1y) / (INR n2x * INR n2y)) / ((sqrt (INR c) - 1)^2))%R.
Proof.
  intros Hc H1x H1y H2x H2y.

  assert (Hdiv_nonneg_x : 0 <= INR n1x / INR n2x).
  { unfold Rdiv; apply Rmult_le_pos.
    - apply pos_INR.
    - apply Rlt_le, Rinv_0_lt_compat; apply lt_0_INR; lia. }
  assert (Hdiv_nonneg_y : 0 <= INR n1y / INR n2y).
  { unfold Rdiv; apply Rmult_le_pos.
    - apply pos_INR.
    - apply Rlt_le, Rinv_0_lt_compat; apply lt_0_INR; lia. }

  assert (Hsqrt_prod : sqrt (INR n1x / INR n2x) * sqrt (INR n1y / INR n2y) =
                       sqrt ((INR n1x * INR n1y) / (INR n2x * INR n2y))).
  { rewrite <- sqrt_mult.
    - f_equal; field; split; apply Rgt_not_eq, lt_0_INR; lia.
    - exact Hdiv_nonneg_x.
    - exact Hdiv_nonneg_y. }

  assert (Htemp : ((1 + eps) * sqrt (INR n1x / INR n2x) / (sqrt (INR c) - 1) *
                  ((1 + eps) * sqrt (INR n1y / INR n2y) / (sqrt (INR c) - 1)) =
                  (1 + eps)^2 * (sqrt (INR n1x / INR n2x) * sqrt (INR n1y / INR n2y)) / ((sqrt (INR c) - 1)^2))%R).
  { field. apply Rgt_not_eq, sqrt_c_minus_1_pos; lia. }
  rewrite Hsqrt_prod in Htemp; exact Htemp.
Qed.

(* 定理：广义二维稀疏内积界 *)
Theorem sparse_inner_bound_2D_generalized
  (c : nat) (n1x n1y n2x n2y : nat) (M eps r : R) :
  (c >= 2)%nat -> (n1x >= 2)%nat -> (n1y >= 2)%nat ->
  (n2x >= 2)%nat -> (n2y >= 2)%nat ->
  (n1x < n2x)%nat -> (n1y < n2y)%nat ->
  (M >= INR c)%R -> (eps > 0)%R -> (r >= 0)%R ->
  (INR n2x >= INR c * INR n1x)%R -> (INR n2y >= INR c * INR n1y)%R ->
  (sqrt (INR n1x * INR n1y * INR n2x * INR n2y) /
   (M * M * (INR n2x - INR n1x) * (INR n2y - INR n1y)) * r <=
   (1 + eps)^2 * sqrt ((INR n1x * INR n1y) / (INR n2x * INR n2y)) /
   ((sqrt (INR c) - 1)^2) * r)%R.
Proof.
  intros Hc H1x H1y H2x H2y Hlx Hly HM Heps Hr Hineqx Hineqy.
  assert (Hx_full : (sqrt (INR n1x * INR n2x) / (M * (INR n2x - INR n1x)) * 1 <=
                     (1 + eps) * sqrt (INR n1x / INR n2x) / (sqrt (INR c) - 1) * 1)%R).
  { apply (sparse_inner_bound_generalized c n1x n2x M eps 1); try lra; try assumption. }
  rewrite Rmult_1_r in Hx_full; rewrite Rmult_1_r in Hx_full.
  assert (Hx : (sqrt (INR n1x * INR n2x) / (M * (INR n2x - INR n1x)) <=
               (1 + eps) * sqrt (INR n1x / INR n2x) / (sqrt (INR c) - 1))%R)
    by exact Hx_full.
  assert (Hy_full : (sqrt (INR n1y * INR n2y) / (M * (INR n2y - INR n1y)) * 1 <=
                     (1 + eps) * sqrt (INR n1y / INR n2y) / (sqrt (INR c) - 1) * 1)%R).
  { apply (sparse_inner_bound_generalized c n1y n2y M eps 1); try lra; try assumption. }
  rewrite Rmult_1_r in Hy_full; rewrite Rmult_1_r in Hy_full.
  assert (Hy : (sqrt (INR n1y * INR n2y) / (M * (INR n2y - INR n1y)) <=
               (1 + eps) * sqrt (INR n1y / INR n2y) / (sqrt (INR c) - 1))%R)
    by exact Hy_full.
  assert (Hx_nonneg : (0 <= sqrt (INR n1x * INR n2x) / (M * (INR n2x - INR n1x)))%R).
  { apply Rmult_le_pos.
    - apply sqrt_positivity; apply Rmult_le_pos; apply pos_INR; lia.
    - left; apply Rinv_0_lt_compat. apply Rmult_lt_0_compat.
      + apply Rlt_le_trans with (INR c).
        * apply lt_0_INR; lia.
        * now apply Rge_le.
      + apply Rgt_minus; apply lt_INR; exact Hlx. }
  assert (Hy_nonneg : (0 <= sqrt (INR n1y * INR n2y) / (M * (INR n2y - INR n1y)))%R).
  { apply Rmult_le_pos.
    - apply sqrt_positivity; apply Rmult_le_pos; apply pos_INR; lia.
    - left; apply Rinv_0_lt_compat. apply Rmult_lt_0_compat.
      + apply Rlt_le_trans with (INR c).
        * apply lt_0_INR; lia.
        * now apply Rge_le.
      + apply Rgt_minus; apply lt_INR; exact Hly. }
  assert (Hprod : ((sqrt (INR n1x * INR n2x) / (M * (INR n2x - INR n1x))) *
                   (sqrt (INR n1y * INR n2y) / (M * (INR n2y - INR n1y))) <=
                   ((1+eps) * sqrt (INR n1x / INR n2x) / (sqrt (INR c) - 1)) *
                   ((1+eps) * sqrt (INR n1y / INR n2y) / (sqrt (INR c) - 1)))%R).
  { apply Rmult_le_compat; [exact Hx_nonneg | exact Hy_nonneg | exact Hx | exact Hy]. }
  assert (Hleft_eq : ((sqrt (INR n1x * INR n2x) / (M * (INR n2x - INR n1x))) *
                      (sqrt (INR n1y * INR n2y) / (M * (INR n2y - INR n1y))) =
                      sqrt (INR n1x * INR n1y * INR n2x * INR n2y) /
                      (M * M * (INR n2x - INR n1x) * (INR n2y - INR n1y)))%R).
  {
    assert (Hfield : ((sqrt (INR n1x * INR n2x) / (M * (INR n2x - INR n1x))) *
                      (sqrt (INR n1y * INR n2y) / (M * (INR n2y - INR n1y))) =
                      (sqrt (INR n1x * INR n2x) * sqrt (INR n1y * INR n2y)) /
                      (M * M * (INR n2x - INR n1x) * (INR n2y - INR n1y)))%R).
    {
      field.
      split; [| split]; apply Rgt_not_eq.
      - apply Rgt_minus; apply lt_INR; exact Hly.
      - apply Rgt_minus; apply lt_INR; exact Hlx.
      - apply Rlt_le_trans with (INR c); [apply lt_0_INR; lia | apply Rge_le; exact HM].
    }
    assert (Hnum : sqrt (INR n1x * INR n2x) * sqrt (INR n1y * INR n2y) =
                   sqrt (INR n1x * INR n1y * INR n2x * INR n2y)).
    {
      rewrite <- sqrt_mult.
      - f_equal; ring.
      - apply Rmult_le_pos; apply pos_INR; lia.
      - apply Rmult_le_pos; apply pos_INR; lia.
    }
    rewrite Hnum in Hfield.
    exact Hfield.
  }
  assert (Hright_eq : (((1+eps) * sqrt (INR n1x / INR n2x) / (sqrt (INR c) - 1)) *
                       ((1+eps) * sqrt (INR n1y / INR n2y) / (sqrt (INR c) - 1)) =
                       (1+eps)^2 * sqrt ((INR n1x * INR n1y) / (INR n2x * INR n2y)) /
                       ((sqrt (INR c) - 1)^2))%R).
  { apply simplify_2D_right_product; assumption. }
  rewrite Hleft_eq in Hprod; rewrite Hright_eq in Hprod.
  apply Rmult_le_compat_r with (r := r) in Hprod; [| now apply Rge_le].
  exact Hprod.
Qed.

(* 定理：概率两两内积界 *)
Theorem pairwise_inner_bound_probabilistic (c : nat) (f : nat -> nat) (p : R) (N : nat) :
  (c >= 2)%nat -> (forall i, (f i >= 2)%nat) ->
  (forall i, (INR (f (S i)) >= INR c * INR c * INR (f i))%R) ->
  (0 < p < 1)%R ->
  let alpha := (INR (N*N) * p * p)%R in
  sum_over_subsets_weight p N (pairwise_inner_condition_b c f) >= 1 - alpha.
Proof.
  intros Hc Hf_ge2 Hf_growth Hp_bounds alpha.
  destruct Hp_bounds as [Hp_pos Hp_lt1].
  assert (Hp_range : 0 <= p <= 1) by (split; lra).

  pose proof (bad_event_weight_bound c f p N Hc (conj Hp_pos Hp_lt1)) as Hbad_upper.
  assert (Hdelta_eq_alpha : INR N * INR N * p * p = alpha).
  { unfold alpha; rewrite <- mult_INR; ring. }
  assert (Hbad_alpha : sum_over_subsets_weight p N (bad_event_b c f) <= alpha).
  { rewrite <- Hdelta_eq_alpha; exact Hbad_upper. }

  set (bad_b := bad_event_b c f).
  set (good_b := pairwise_inner_condition_b c f).

  assert (H_notbad_imp_good_prop : forall I, In I (all_subsets N) -> bad_b I = false ->
    (forall i j, (i < j)%nat -> (j < length I)%nat ->
      (sqrt (INR (f (nth i I 0%nat)) * INR (f (nth j I 0%nat))) /
       (INR c * (INR (f (nth j I 0%nat)) - INR (f (nth i I 0%nat)))) <=
       sqrt (INR (f (nth i I 0%nat)) / INR (f (nth j I 0%nat))) / (sqrt (INR c) - 1))%R)).
  {
    intros I Hin Hbad_false i j Hij Hjlen.
    unfold bad_b in Hbad_false.
    assert (Hi_len : (i < length I)%nat) by (apply Nat.lt_trans with j; assumption).
    assert (Hno_bad_pair : ~ (exists i j, (i < length I)%nat /\ (j < length I)%nat /\ (i < j)%nat /\
                            INR (f (nth j I 0%nat)) < INR c * INR c * INR (f (nth i I 0%nat)))).
    {
      intro Hbad_exists.
      apply (proj2 (bad_event_b_true_iff c f I)) in Hbad_exists.
      rewrite Hbad_false in Hbad_exists.
      discriminate.
    }
    assert (H_not_ineq : ~ INR (f (nth j I 0%nat)) < INR c * INR c * INR (f (nth i I 0%nat))).
    { intro Hlt. apply Hno_bad_pair. exists i, j; repeat split; assumption. }
    apply Rnot_lt_ge in H_not_ineq.
    assert (Hc_INR : INR c >= 2) by (apply le_INR in Hc; simpl in Hc; lra).
    assert (Hc_ge_1_R : 1 <= INR c) by lra.
    assert (Hineq_weak : INR (f (nth j I 0%nat)) >= INR c * INR (f (nth i I 0%nat))).
    {
      apply Rle_ge.
      eapply Rle_trans with (INR c * INR c * INR (f (nth i I 0%nat))).
      - replace (INR c * INR (f (nth i I 0%nat)))
          with (INR (f (nth i I 0%nat)) * INR c) by ring.
        replace (INR c * INR c * INR (f (nth i I 0%nat)))
          with (INR (f (nth i I 0%nat)) * (INR c * INR c)) by ring.
        apply Rmult_le_compat_l.
        + apply pos_INR; lia.
        + pattern (INR c) at 1; replace (INR c) with (1 * INR c) by ring.
          apply Rmult_le_compat_r; [apply pos_INR; lia | exact Hc_ge_1_R].
      - apply Rge_le; exact H_not_ineq.
    }
    assert (Hn1_ge2 : (f (nth i I 0%nat) >= 2)%nat) by apply Hf_ge2.
    assert (Hn2_ge2 : (f (nth j I 0%nat) >= 2)%nat) by apply Hf_ge2.
    assert (Hlt_f : (f (nth i I 0%nat) < f (nth j I 0%nat))%nat).
    {
      apply INR_lt.
      apply Rlt_le_trans with (INR c * INR c * INR (f (nth i I 0%nat))).
      - rewrite <- (Rmult_1_l (INR (f (nth i I 0%nat)))) at 1.
        apply Rmult_lt_compat_r.
        + apply lt_0_INR; lia.
        + apply Rlt_le_trans with 4; [lra |].
          replace 4 with (2 * 2) by ring.
          apply Rmult_le_compat; lra.
      - apply Rge_le; exact H_not_ineq.
    }
    eapply core_algebraic_inequality_general; eauto.
  }

  assert (H_notbad_imp_good : forall I, In I (all_subsets N) -> negb (bad_b I) = true -> good_b I = true).
  {
    intros I Hin Hnegb.
    unfold good_b.
    destruct (bad_b I) eqn:Hbad; [discriminate | ].
    destruct (pairwise_inner_condition_bP c f I) as [Hprop | Hnprop].
    - reflexivity.
    - exfalso. apply Hnprop. apply H_notbad_imp_good_prop; auto.
  }

  assert (H_all : sum_over_subsets_weight p N (fun _ => true) = 1).
  { apply sum_weights_all_true_general_P; exact Hp_range. }

  pose proof (sum_over_subsets_weight_complement p N bad_b) as Hcomp.
  rewrite H_all in Hcomp.
  assert (H_sum_notbad : sum_over_subsets_weight p N (fun I => negb (bad_b I)) = 1 - sum_over_subsets_weight p N bad_b).
  { lra. }

  assert (H_lower1 : 1 - sum_over_subsets_weight p N bad_b >= 1 - alpha).
  {
    cut (sum_over_subsets_weight p N bad_b <= alpha). { intro H; lra. }
    exact Hbad_alpha.
  }

  assert (Hmono : sum_over_subsets_weight p N (fun I => negb (bad_b I)) <= sum_over_subsets_weight p N good_b).
  {
    apply sum_over_subsets_weight_mono_in.
    - exact (conj Hp_pos Hp_lt1).
    - exact H_notbad_imp_good.
  }

  assert (H_lower1' : 1 - alpha <= 1 - sum_over_subsets_weight p N bad_b) by lra.
  assert (H_lower2 : 1 - alpha <= sum_over_subsets_weight p N good_b).
  {
    eapply Rle_trans. apply H_lower1'.
    rewrite <- H_sum_notbad. exact Hmono.
  }
  apply Rle_ge; exact H_lower2.
Qed.

End SparseInnerBoundExtensions.
