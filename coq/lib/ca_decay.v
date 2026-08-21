(* 拆分自 Riemann_Hypothesis_Proof_Framework.v（复分析证明库 v6.0）*)
(* 库: ca_decay  原文行区间: 37115-48942  机械拆分，未改动内容 *)

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

Require Import ca_base ca_algebra ca_primes ca_complex_analysis ca_fourier ca_zeta_scaffold ca_trig ca_gamma ca_taylor ca_zeta_axioms ca_complex_log ca_complex_foundation ca_log_bounds ca_independence ca_prime_power ca_basis ca_basis_lemmas ca_probabilistic ca_sparse_ext ca_char_ortho.

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
Require Import Stdlib.Reals.Reals.
Require Import Stdlib.Reals.Rtrigo1.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lra.
Require Import Stdlib.Arith.Arith.
Local Open Scope R_scope.
Local Open Scope complex_scope.
Local Open Scope nat_scope.
Import PrimeEmbedding.
Import ComplexNumbers.
Import UnconditionalBasis.
Import UnconditionalBasisLemmas.

Require Import Stdlib.Reals.Reals.
Require Import Stdlib.micromega.Lra.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.NArith.NArith.
Require Import Stdlib.Reals.Rsqrt_def.

Import independent.
Import independent'.
Import UnconditionalBasisLemmas.
Import ProbabilisticSparseBasis.

Local Open Scope nat_scope.
Local Open Scope complex_scope.
Local Open Scope R_scope.
  
Module ExtendedTheorems.

(* 分母正性判定 *)
Lemma denom_pos (c n1 n2 : nat) :
  (c >= 2)%nat -> (n1 < n2)%nat -> (0 < INR c * (INR n2 - INR n1))%R.
Proof.
  intros Hc Hlt.
  apply Rmult_lt_0_compat.
  - apply lt_0_INR; lia.
  - apply Rgt_minus; now apply lt_INR.
Qed.

(* 平方根减一的正性（标准版） *)
Lemma sqrt_c_minus_1_pos_std (c : nat) : (c >= 2)%nat -> (0 < sqrt (INR c) - 1)%R.
Proof.
  intros Hc. apply Rgt_minus. rewrite <- sqrt_1.
  apply sqrt_lt_1; [lra | apply pos_INR; lia |].
  apply Rlt_le_trans with (INR 2); [simpl; lra |].
  apply le_INR; lia.
Qed.

(* 平方增长蕴含线性增长 *)
Lemma square_growth_implies_linear_growth (c n1 n2 : nat) :
  (c >= 2)%nat ->
  (INR n2 >= INR c * INR c * INR n1)%R ->
  (INR n2 >= INR c * INR n1)%R.
Proof.
  intros Hc Hineq.
  apply Rle_ge.
  transitivity (INR c * INR c * INR n1).
  - apply Rmult_le_compat_r.
    + change 0 with (INR 0). apply le_INR; lia.
    + rewrite <- (Rmult_1_r (INR c)) at 1.
      apply Rmult_le_compat_l.
      * change 0 with (INR 0). apply le_INR; lia.
      * rewrite <- INR_1. apply le_INR; lia.
  - apply Rge_le; exact Hineq.
Qed.

(* 定理：尺度参数化的比例型代数不等式（自然数指数） *)
Theorem core_algebraic_inequality_scaled (c n1 n2 : nat) (m : nat) :
  (c >= 2)%nat -> (n1 >= 2)%nat -> (n2 >= 2)%nat -> (n1 < n2)%nat ->
  (INR n2 >= INR c * INR c * INR n1)%R ->
  ((sqrt (INR n1 * INR n2) / (INR c * (INR n2 - INR n1))) ^ m <=
   (sqrt (INR n1 / INR n2) / (sqrt (INR c) - 1)) ^ m)%R.
Proof.
  intros Hc H1 H2 Hlt Hineq.
  assert (H_weak : (INR n2 >= INR c * INR n1)%R) by
    (apply square_growth_implies_linear_growth with (c:=c) (n1:=n1) (n2:=n2); assumption).

  assert (H_main : (sqrt (INR n1 * INR n2) / (INR c * (INR n2 - INR n1)) <=
                    sqrt (INR n1 / INR n2) / (sqrt (INR c) - 1))%R).
  { apply core_algebraic_inequality_general; auto. }

  assert (H_nonneg_left : (0 <= sqrt (INR n1 * INR n2) / (INR c * (INR n2 - INR n1)))%R).
  { unfold Rdiv.
    apply Rmult_le_pos.
    - apply sqrt_pos; apply Rmult_le_pos; apply pos_INR.
    - left; apply Rinv_0_lt_compat.
      apply Rmult_lt_0_compat.
      + apply lt_0_INR; lia.
      + apply Rgt_minus; apply lt_INR; exact Hlt. }

  assert (H_combined : 0 <= sqrt (INR n1 * INR n2) / (INR c * (INR n2 - INR n1))
                       <= sqrt (INR n1 / INR n2) / (sqrt (INR c) - 1%R)).
  { split; [exact H_nonneg_left | exact H_main]. }

  exact (pow_incr (sqrt (INR n1 * INR n2) / (INR c * (INR n2 - INR n1)))
                 (sqrt (INR n1 / INR n2) / (sqrt (INR c) - 1))
                 m
                 H_combined).
Qed.

(* 空序对列表在单点集上为空 *)
Lemma all_pairs_lt_1_nil : all_pairs_lt 1 = [].
Proof.
  unfold all_pairs_lt, all_pairs_lt_aux. simpl. reflexivity.
Qed.

(* 定理：带噪声容忍的概率稀疏子集存在性 *)
Theorem sparse_subset_exists_with_tolerance_corrected (c : nat) (f : nat -> nat) (p δ : R) (N : nat) :
  (c >= 2)%nat ->
  (forall i, (f i >= 2)%nat) ->
  (forall i, INR (f (S i)) >= INR c * INR c * INR (f i))%R ->
  0 < p < 1 -> 0 < δ < 1 ->
  exists I : list nat,
    In I (all_subsets N) /\
    NoDup I /\
    (let bad_count :=
       length (filter (fun '(i,j) =>
         f (nth j I 0%nat) <? c * c * f (nth i I 0%nat)
       ) (all_pairs_lt (length I)))
     in INR bad_count <= δ * INR N * INR N) /\
    weight_of_subset p N I > 0.
Proof.
  intros Hc Hf_ge2 Hf_growth [Hp_pos Hp_lt1] [Hδ_pos Hδ_lt1].
  destruct N as [|N'].
  - (* N = 0 *)
    exists [].
    split.
    + unfold all_subsets, all_subsets_upto. simpl. left; reflexivity.
    + split.
      * constructor.
      * split.
        -- simpl. lra.
        -- unfold weight_of_subset. simpl. lra.
  - (* N = S N' *)
    assert (H_in : In [0%nat] (all_subsets (S N'))).
    { clear. induction N'; [simpl; auto |].
      simpl. apply in_app_iff. right; auto. }
    exists [0%nat]. split; [exact H_in | split].
    + (* NoDup [0] *)
      apply NoDup_cons.
      * simpl. intros H. inversion H.
      * apply NoDup_nil.
    + split.
      -- (* 坏对计数 *)
         cbv beta.
         simpl (Datatypes.length [0%nat]).
         unfold all_pairs_lt, all_pairs_lt_aux.
         simpl.
         rewrite <- ?S_INR.
         assert (H_nonneg : 0 <= INR (S N')) by apply pos_INR.
         nra.
      -- (* 权重为正 *)
         unfold weight_of_subset.
         simpl (length [0%nat]).
         replace (S N' - 1)%nat with N' by lia.
         replace (p ^ 1) with p by ring.
         apply Rmult_gt_0_compat; [exact Hp_pos | apply pow_lt; lra].
Qed.

(* 复数范数三角不等式 *)
Lemma Cnorm_triang : forall z w : Complex, Cnorm (z +c w) <= Cnorm z + Cnorm w.
Proof.
  intros z w.
  unfold Cnorm, Cnorm_sq, Cadd; simpl.
  set (a1 := re z); set (b1 := im z); set (a2 := re w); set (b2 := im w).

  assert (H_nonneg1 : 0 <= a1 * a1 + b1 * b1)
    by (apply Rplus_le_le_0_compat; apply Rle_0_sqr).
  assert (H_nonneg2 : 0 <= a2 * a2 + b2 * b2)
    by (apply Rplus_le_le_0_compat; apply Rle_0_sqr).

  assert (Rsqr_sqrt_intro : forall x, 0 <= x -> Rsqr (sqrt x) = x). {
    intros x Hx; unfold Rsqr; rewrite sqrt_sqrt; auto.
  }

  assert (Hcs : a1 * a2 + b1 * b2 <= sqrt (a1 * a1 + b1 * b1) * sqrt (a2 * a2 + b2 * b2)). {
    destruct (Rle_or_lt (a1 * a2 + b1 * b2) 0) as [Hle | Hgt].
    - apply Rle_trans with 0; [exact Hle | apply Rmult_le_pos; apply sqrt_pos].
    - assert (H_sq : Rsqr (a1 * a2 + b1 * b2) <= (a1*a1 + b1*b1) * (a2*a2 + b2*b2)). {
        cut (0 <= (a1*a1 + b1*b1) * (a2*a2 + b2*b2) - Rsqr (a1 * a2 + b1 * b2)); [lra |].
        replace ((a1*a1 + b1*b1) * (a2*a2 + b2*b2) - Rsqr (a1 * a2 + b1 * b2))
          with (Rsqr (a1 * b2 - a2 * b1)).
        - apply Rle_0_sqr.
        - unfold Rsqr; ring.
      }
      assert (Hl : 0 <= a1 * a2 + b1 * b2) by lra.
      assert (Hr : 0 <= sqrt (a1*a1 + b1*b1) * sqrt (a2*a2 + b2*b2))
        by (apply Rmult_le_pos; apply sqrt_pos).
      apply Rsqr_incr_0; auto.
      rewrite Rsqr_mult.
      rewrite !Rsqr_sqrt_intro; auto.
  }

  set (A := (a1 + a2)*(a1 + a2) + (b1 + b2)*(b1 + b2)).
  set (S1 := a1*a1 + b1*b1).
  set (S2 := a2*a2 + b2*b2).

  assert (HA_nonneg : 0 <= A) by (subst A; apply Rplus_le_le_0_compat; apply Rle_0_sqr).
  assert (Hsum_nonneg : 0 <= sqrt S1 + sqrt S2)
    by (apply Rplus_le_le_0_compat; apply sqrt_pos).

  assert (H_target_sq : A <= (sqrt S1 + sqrt S2)^2). {
    unfold A, S1, S2.
    replace ((a1 + a2)*(a1 + a2) + (b1 + b2)*(b1 + b2))
      with (a1*a1 + b1*b1 + a2*a2 + b2*b2 + 2 * (a1 * a2 + b1 * b2)) by ring.
    replace ((sqrt (a1*a1 + b1*b1) + sqrt (a2*a2 + b2*b2))^2)
      with (a1*a1 + b1*b1 + a2*a2 + b2*b2 + 2 * sqrt (a1*a1 + b1*b1) * sqrt (a2*a2 + b2*b2)).
    2: {
      rewrite (pow2_sqr (sqrt (a1*a1 + b1*b1) + sqrt (a2*a2 + b2*b2))).
      rewrite Rsqr_plus.
      rewrite !Rsqr_sqrt_intro; auto.
      ring.
    }
    apply Rplus_le_compat_l.
    replace (2 * sqrt (a1*a1 + b1*b1) * sqrt (a2*a2 + b2*b2))
      with (2 * (sqrt (a1*a1 + b1*b1) * sqrt (a2*a2 + b2*b2))) by ring.
    apply Rmult_le_compat_l; [lra | exact Hcs].
  }

  apply Rsqr_incr_0 with (x := sqrt A) (y := sqrt S1 + sqrt S2).
  - rewrite (Rsqr_sqrt_intro A HA_nonneg).
    replace (Rsqr (sqrt S1 + sqrt S2)) with ((sqrt S1 + sqrt S2)^2)
      by (unfold Rsqr; ring).
    exact H_target_sq.
  - destruct (Rle_lt_or_eq_dec 0 A HA_nonneg) as [HA_pos | HA_zero].
    + apply Rlt_le; apply sqrt_lt_R0_c; exact HA_pos.
    + rewrite <- HA_zero. simpl. rewrite sqrt_0. lra.
  - exact Hsum_nonneg.
Qed.

(* 定理：部分质数特征弱上界 *)
Theorem partial_prime_character_bound_weak (p a b m : nat) :
  (p >= 2)%nat -> (m < p)%nat -> a mod p <> b mod p ->
  Cnorm (Csum (fun x : nat =>
    Cexp (0 +i (2 * PI * INR (a * x) / INR p)) *c
    Cconj (Cexp (0 +i (2 * PI * INR (b * x) / INR p)))) m) <= INR m.
Proof.
  intros Hp Hm Hmod.
  assert (Cnorm_Cexp : forall θ : R, Cnorm (Cexp (0 +i θ)) = 1%R). {
    intros θ.
    assert (Hsq : Cnorm_sq (Cexp (0 +i θ)) = 1). {
      unfold Cexp, Cnorm_sq; simpl.
      rewrite exp_0, Rmult_1_l, Rmult_1_l, Rplus_comm, sin2_cos2; reflexivity.
    }
    unfold Cnorm; rewrite Hsq; apply sqrt_1.
  }
  assert (H2 : forall x, Cnorm (Cexp (0 +i (2 * PI * INR (a * x) / INR p)) *c
                              Cconj (Cexp (0 +i (2 * PI * INR (b * x) / INR p)))) = 1). {
    intro x; rewrite Cnorm_mult, Cnorm_Cexp, Cnorm_conj_eq, Cnorm_Cexp; lra.
  }
  assert (Cnorm_C0 : Cnorm C0 = 0%R). {
    unfold Cnorm, Cnorm_sq, C0; simpl.
    rewrite Rsqr_0, Rplus_0_l; apply sqrt_0.
  }

  induction m as [| m' IH].
  - simpl Csum.
    change (Cnorm C0 <= INR 0).
    rewrite Cnorm_C0; simpl; lra.
  - simpl Csum.
    eapply Rle_trans.
    + apply Cnorm_triang.
    + rewrite S_INR.
      apply Rplus_le_compat.
      * apply IH; lia.
      * rewrite H2; lra.
Qed.

(* 复数范数平方加法展开 *)
Lemma Cnorm_sq_add (z w : Complex) :
  Cnorm_sq (z +c w) = Cnorm_sq z + Cnorm_sq w + 2 * (re z * re w + im z * im w).
Proof.
  destruct z as [x1 y1], w as [x2 y2].
  unfold Cnorm_sq, Cadd; simpl.
  unfold Rsqr.
  ring.
Qed.

(* 非负实数平方根的平方恒等式 *)
Lemma Rsqr_sqrt : forall x : R, 0 <= x -> Rsqr (sqrt x) = x.
Proof. intros x Hx; unfold Rsqr; rewrite sqrt_sqrt; trivial. Qed.

(* 柯西‑施瓦茨代数恒等式 *)
Lemma cauchy_schwarz_sq_identity : forall a b u d : R,
  (a*a + b*b)*(u*u + d*d) = Rsqr (a * u + b * d) + Rsqr (a * d - b * u).
Proof.
  intros; unfold Rsqr; ring.
Qed.

(* 复数柯西‑施瓦茨不等式 *)
Lemma CauchySchwarz_complex : forall z w : Complex,
  re z * re w + im z * im w <= Cnorm z * Cnorm w.
Proof.
  intros z w.
  destruct z as [a b]; destruct w as [u d].
  unfold re, im, Cnorm, Cnorm_sq; simpl.
  set (A := a * a + b * b).
  set (B := u * u + d * d).
  assert (HA : 0 <= A) by (subst A; apply Rplus_le_le_0_compat; apply Rle_0_sqr).
  assert (HB : 0 <= B) by (subst B; apply Rplus_le_le_0_compat; apply Rle_0_sqr).
  destruct (Rle_or_lt (a * u + b * d) 0) as [Hle | Hgt].
  - apply Rle_trans with 0; [exact Hle | apply Rmult_le_pos; apply sqrt_pos].
  - assert (Hl : 0 <= a * u + b * d) by lra.
    assert (Hr : 0 <= sqrt A * sqrt B) by (apply Rmult_le_pos; apply sqrt_pos).
    assert (Hsq_sq : Rsqr (a * u + b * d) <= A * B).
    { subst A B.
      rewrite cauchy_schwarz_sq_identity.
      rewrite <- (Rplus_0_r (Rsqr (a * u + b * d))) at 1.
      apply Rplus_le_compat_l.
      apply Rle_0_sqr.
    }
    rewrite <- (Rsqr_sqrt A HA) in Hsq_sq.
    rewrite <- (Rsqr_sqrt B HB) in Hsq_sq.
    rewrite <- Rsqr_mult in Hsq_sq.
    apply Rsqr_incr_0; assumption.
Qed.

(* 复数范数的三角不等式 *)
Lemma Cnorm_triangle : forall z w : Complex, Cnorm (z +c w) <= Cnorm z + Cnorm w.
Proof.
  intros z w.
  assert (H_pos1 : 0 <= Cnorm (z +c w)) by apply Cnorm_ge_0.
  assert (H_pos2 : 0 <= Cnorm z + Cnorm w)
    by (apply Rplus_le_le_0_compat; apply Cnorm_ge_0).
  apply Rsqr_incr_0; [ | exact H_pos1 | exact H_pos2].
  assert (Cnorm_sq_eq : forall x, (Cnorm x)² = Cnorm_sq x).
  {
    intros x.
    unfold Cnorm.
    rewrite Rsqr_sqrt.
    - reflexivity.
    - apply Rplus_le_le_0_compat; apply Rle_0_sqr.
  }
  rewrite !Cnorm_sq_eq.
  rewrite Cnorm_sq_add.
  replace ((∥ z ∥ + ∥ w ∥)²)
    with (Cnorm_sq z + Cnorm_sq w + 2 * Cnorm z * Cnorm w).
  2:{
    rewrite <- (Cnorm_sq_eq z), <- (Cnorm_sq_eq w).
    unfold Rsqr; ring.
  }
  apply Rplus_le_compat; [apply Rle_refl |].
  apply Rle_trans with (2 * (Cnorm z * Cnorm w)).
  - apply Rmult_le_compat_l; [lra | exact (CauchySchwarz_complex z w)].
  - rewrite Rmult_assoc; apply Rle_refl.
Qed.

(* 分式不等式等价条件 *)
Lemma Rle_div_div (A B C D : R) (HB : 0 < B) (HD : 0 < D) :
  A / B <= C / D <-> A * D <= C * B.
Proof.
  assert (HB0 : B <> 0) by (apply Rgt_not_eq; exact HB).
  assert (HD0 : D <> 0) by (apply Rgt_not_eq; exact HD).
  assert (HposBD : 0 < B * D) by (apply Rmult_lt_0_compat; assumption).
  assert (HleBD : 0 <= B * D) by (apply Rlt_le; exact HposBD).
  assert (Hpos_invBD : 0 < / (B * D))
    by (apply Rinv_0_lt_compat; exact HposBD).
  assert (Hle_invBD : 0 <= / (B * D))
    by (apply Rlt_le; exact Hpos_invBD).
  split.
  - intro H.
    pose proof (Rmult_le_compat_r (B * D) (A / B) (C / D) HleBD H) as H_mul.
    replace (A / B * (B * D)) with (A * D) in H_mul
      by (field; auto).
    replace (C / D * (B * D)) with (C * B) in H_mul
      by (field; auto).
    exact H_mul.
  - intro H.
    pose proof (Rmult_le_compat_r (/ (B * D)) (A * D) (C * B) Hle_invBD H) as H_mul.
    replace (A * D * / (B * D)) with (A / B) in H_mul
      by (field; auto).
    replace (C * B * / (B * D)) with (C / D) in H_mul
      by (field; auto).
    exact H_mul.
Qed.

(* 底数不小于一的幂保持不小于一 *)
Lemma pow_ge_1 (x : R) (n : nat) : 1 <= x -> 1 <= x ^ n.
Proof.
  intros H; induction n; simpl.
  - lra.
  - apply Rle_trans with (x * 1); [lra |].
    apply Rmult_le_compat_l; [lra | exact IHn].
Qed.

(* 定理：自适应分母显式K阶 *)
Theorem adaptive_denom_explicit_K (c : nat) (eps : R) :
  (c >= 2)%nat -> eps > 0 -> eps < INR c - 1 ->
  let K := max 2%nat (Z.to_nat (up (ln (4 / eps) / ln (INR c)))) in
  (K >= 2)%nat /\
  (forall (n1 n2 : nat),
      (n1 >= 2)%nat ->
      INR n2 >= (INR c)^K * INR n1 ->
      sqrt (INR n1 * INR n2) / ((INR c)^K / (1 + eps) * (INR n2 - INR n1)) <=
      sqrt (INR n1 / INR n2) / (sqrt (INR c) - 1)).
Proof.
  intros Hc Heps Hc_eps.
  set (K := max 2%nat (Z.to_nat (up (ln (4 / eps) / ln (INR c))))).
  assert (HK2 : (K >= 2)%nat) by (unfold K; apply Nat.le_max_l).
  assert (Heps_range : 0 < eps < INR c - 1) by (split; assumption).
  split.
  - exact HK2.
  - intros n1 n2 Hn1 Hineq.
    apply (adaptive_denom_general_K c K eps Hc HK2 Heps_range n1 n2 Hn1 Hineq).
Qed.

(* 改进的内积范数上界 *)
Lemma inner_norm_bound_improved (c n1 n2 : nat) :
  (c >= 2)%nat -> (n1 >= 2)%nat -> (n2 >= 2)%nat -> (n1 < n2)%nat ->
  INR n2 >= INR c * INR c * INR n1 ->
  Cnorm (Csum (fun k => psi n1 k *c Cconj (psi n2 k)) (n1 - 1)) <=
  (INR c)^2 / 4 * sqrt (INR n1 / INR n2) / (sqrt (INR c) - 1).
Proof.
  intros Hc Hn1 Hn2 Hlt Hineq.

  assert (Hc0 : INR c <> 0)          by (apply Rgt_not_eq, lt_0_INR; lia).
  assert (Hdiff0 : INR n2 - INR n1 <> 0).
  { apply Rgt_not_eq. apply Rgt_minus. apply lt_INR. exact Hlt. }
  assert (Hsqrt0 : sqrt (INR c) - 1 <> 0).
  { apply Rgt_not_eq. apply sqrt_c_minus_1_pos; lia. }

  assert (Hineq_weak : INR n2 >= INR c * INR n1).
  { apply Rle_ge.
    eapply Rle_trans; [ | apply Rge_le; exact Hineq ].
    apply Rmult_le_compat_r.
    - apply pos_INR.
    - replace (INR c) with (INR c * 1) at 1 by ring.
      apply Rmult_le_compat_l; [ apply pos_INR | ].
      rewrite <- INR_1. apply le_INR; lia. }

  assert (Hcore : sqrt (INR n1 * INR n2) / (INR c * (INR n2 - INR n1)) <=
                  sqrt (INR n1 / INR n2) / (sqrt (INR c) - 1)).
  { apply core_algebraic_inequality_general; assumption. }

  set (L := sqrt (INR n1 * INR n2) / (INR c * (INR n2 - INR n1))).
  set (R := sqrt (INR n1 / INR n2) / (sqrt (INR c) - 1)).
  assert (HL : L * INR c = sqrt (INR n1 * INR n2) / (INR n2 - INR n1)).
  { unfold L. field. auto. }
  assert (HR : R * INR c = INR c * sqrt (INR n1 / INR n2) / (sqrt (INR c) - 1)).
  { unfold R. field. auto. }
  assert (Hcore2 : sqrt (INR n1 * INR n2) / (INR n2 - INR n1) <=
                   INR c * sqrt (INR n1 / INR n2) / (sqrt (INR c) - 1)).
  {
    assert (Hcore_mul : L * INR c <= R * INR c).
    { apply Rmult_le_compat_r; [apply Rlt_le, lt_0_INR; lia | exact Hcore]. }
    rewrite HL in Hcore_mul; rewrite HR in Hcore_mul.
    exact Hcore_mul.
  }

  assert (H_bound1 : Cnorm (Csum (fun k => psi n1 k *c Cconj (psi n2 k)) (n1 - 1)) <=
                     INR c * sqrt (INR n1 * INR n2) / (4 * (INR n2 - INR n1))).
  { exact (inner_product_norm_bound_general_corrected n1 n2 c Hn1 Hn2 Hlt Hc Hineq). }

  assert (H_ineq_mul : INR c * sqrt (INR n1 * INR n2) / (4 * (INR n2 - INR n1)) <=
                       (INR c)^2 / 4 * sqrt (INR n1 / INR n2) / (sqrt (INR c) - 1)).
  {
    assert (Htmp : INR c * sqrt (INR n1 * INR n2) / (4 * (INR n2 - INR n1)) =
                   (INR c / 4) * (sqrt (INR n1 * INR n2) / (INR n2 - INR n1))).
    { field. auto. }
    rewrite Htmp.
    cut (sqrt (INR n1 * INR n2) / (INR n2 - INR n1) <= INR c * sqrt (INR n1 / INR n2) / (sqrt (INR c) - 1)).
    - intros H.
      apply Rmult_le_compat_l with (r := INR c / 4) in H.
      + replace ((INR c)^2 / 4 * sqrt (INR n1 / INR n2) / (sqrt (INR c) - 1))
          with ((INR c / 4) * (INR c * sqrt (INR n1 / INR n2) / (sqrt (INR c) - 1))).
        * exact H.
        * field; auto.
      + apply Rmult_le_pos; [apply Rlt_le, lt_0_INR; lia | lra].
    - exact Hcore2.
  }
  eapply Rle_trans; [exact H_bound1 | exact H_ineq_mul].
Qed.

(* 定理：非对角内积范数的二维联合上界（乘积等式与分项界） *)
Theorem inner_offdiag_bound_2D (c : nat) (n1x n1y n2x n2y : nat) :
  (c >= 2)%nat ->
  (n1x >= 2)%nat -> (n1y >= 2)%nat -> (n2x >= 2)%nat -> (n2y >= 2)%nat ->
  (n1x < n2x)%nat -> (n1y < n2y)%nat ->
  INR n2x >= INR c * INR c * INR n1x ->
  INR n2y >= INR c * INR c * INR n1y ->
  let innerx := Csum (fun k => psi n1x k *c Cconj (psi n2x k)) (n1x - 1) in
  let innery := Csum (fun k => psi n1y k *c Cconj (psi n2y k)) (n1y - 1) in
  Cnorm (innerx *c innery) <=
    ((Cnorm innerx) * (Cnorm innery)) /\
  Cnorm innerx <= (INR c)^2 / 4 * sqrt (INR n1x / INR n2x) / (sqrt (INR c) - 1) /\
  Cnorm innery <= (INR c)^2 / 4 * sqrt (INR n1y / INR n2y) / (sqrt (INR c) - 1).
Proof.
  intros.
  split.
  - rewrite Cnorm_mult; reflexivity.
  - split.
    + unfold innerx; apply inner_norm_bound_improved; eauto.
    + unfold innery; apply inner_norm_bound_improved; eauto.
Qed.

(* 复数单位元的范数恒等式 *)
Lemma Cnorm_C1 : ComplexNumbers.Cnorm ComplexNumbers.C1 = 1%R.
Proof.
  unfold ComplexNumbers.Cnorm, ComplexNumbers.Cnorm_sq, ComplexNumbers.C1; simpl.
  rewrite Rsqr_1, Rsqr_0, Rplus_0_r.
  apply sqrt_1.
Qed.

(* 复数模的乘积性质 *)
Lemma Cnorm_mult (z w : Complex) : Cnorm (z *c w) = Cnorm z * Cnorm w.
Proof.
  unfold Cnorm, Cnorm_sq, Cmul.
  destruct z as [a b], w as [c d].
  simpl.
  assert (Ha : 0 <= a² + b²).
  { apply Rplus_le_le_0_compat; apply Rle_0_sqr. }
  assert (Hb : 0 <= c² + d²).
  { apply Rplus_le_le_0_compat; apply Rle_0_sqr. }
  rewrite <- sqrt_mult; [| apply Ha | apply Hb].
  apply f_equal.
  unfold Rsqr; ring.
Qed.

(* 非负实数列表的元素累积乘积非负 *)
Lemma fold_right_Rmult_nonneg (l : list R) :
  Forall (fun x => 0 <= x) l ->
  0 <= fold_right Rmult 1%R l.
Proof.
  induction l as [| x l IH]; intros H.
  - simpl; lra.
  - inversion H as [| Hx Hl]; subst.
    simpl; apply Rmult_le_pos; auto.
Qed.

(* psi 内积函数定义 *)
Definition psi_inner (n m : nat) : Complex :=
  Csum (fun k : nat => psi n k *c Cconj (psi m k)) (n - 1)%nat.

(* 定理：内积非对角项乘积范数上界（自然数列表版本） *)
Theorem inner_offdiag_bound_nd (c : nat) (ns ms : list nat) :
  (c >= 2)%nat ->
  Forall (fun n => (n >= 2)%nat) ns ->
  Forall (fun m => (m >= 2)%nat) ms ->
  length ns = length ms ->
  Forall2 (fun n m => (n < m)%nat) ns ms ->
  Forall2 (fun n m => INR m >= INR c * INR c * INR n) ns ms ->
  Cnorm
    (fold_right ComplexNumbers.Cmul ComplexNumbers.C1
       (map (fun '(n, m) => psi_inner n m) (List.combine ns ms)))
  <=
  fold_right Rmult 1%R
    (map (fun '(n, m) =>
            (Rsqr (INR c) / 4 * sqrt (INR n / INR m) / (sqrt (INR c) - 1))%R)
         (List.combine ns ms)).
Proof.
  intros Hc Halln Hallm Hlen Hlt2 Hineq2.
  assert (HeqRsqr : forall x, Rsqr x = x^2) by (intros; unfold Rsqr; ring).
  rewrite !HeqRsqr.
  unfold psi_inner.
  revert ms Hallm Hlen Hlt2 Hineq2.
  induction ns as [| n ns' IH]; intros ms Hallm Hlen Hlt2 Hineq2.
  - destruct ms; [| simpl in Hlen; lia].
    simpl; rewrite Cnorm_C1; lra.
  - destruct ms as [| m ms']; [simpl in Hlen; lia|].
    simpl in Halln, Hallm, Hlt2, Hineq2, Hlen.
    inversion Halln as [|? ? Hn_ge2 Hns']; clear Halln.
    inversion Hallm as [|? ? Hm_ge2 Hms']; clear Hallm.
    inversion Hlt2 as [|? ? ? Hnm_lt Hlt2']; clear Hlt2.
    inversion Hineq2 as [|? ? ? Hnm_ineq Hineq2']; clear Hineq2.
    simpl combine; simpl map; simpl fold_right.
    rewrite Cnorm_mult.
    set (rest := fold_right ComplexNumbers.Cmul ComplexNumbers.C1
               (map (fun '(n0, m0) => psi_inner n0 m0) (combine ns' ms'))).
    set (bound_rest := fold_right Rmult 1 (map (fun '(n0, m0) => (INR c)^2 / 4 * sqrt (INR n0 / INR m0) / (sqrt (INR c) - 1)) (combine ns' ms'))).
    assert (Hnonneg_Cnorm_nm : 0 <= Cnorm (Csum (fun k : nat => psi n k *c Cconj (psi m k)) (n - 1)%nat))
      by apply Cnorm_ge_0.
    assert (Hbound_single : Cnorm (Csum (fun k : nat => psi n k *c Cconj (psi m k)) (n - 1)%nat)
                           <= (INR c)^2 / 4 * sqrt (INR n / INR m) / (sqrt (INR c) - 1)).
    { apply inner_norm_bound_improved; assumption. }
    assert (Hlen' : length ns' = length ms') by (simpl in Hlen; lia).
    specialize (IH Hns' ms' Hms' Hlen' H3 H8).
    assert (Hbound_rest : Cnorm rest <= bound_rest) by exact IH.
    assert (Hc_sq_nonneg : 0 <= INR c ^ 2).
    { rewrite <- (HeqRsqr (INR c)); apply Rle_0_sqr. }
    assert (Hinv4_nonneg : 0 <= / 4).
    { apply Rlt_le; apply Rinv_0_lt_compat; lra. }
    assert (Hsqrt_nonneg : 0 <= sqrt (INR n / INR m)).
    { apply sqrt_pos. }
    assert (Hnum_nonneg : 0 <= (INR c)^2 / 4 * sqrt (INR n / INR m)).
    { apply Rmult_le_pos; [apply Rmult_le_pos; [exact Hc_sq_nonneg | exact Hinv4_nonneg] | exact Hsqrt_nonneg]. }
    assert (Hinv_den_nonneg : 0 <= / (sqrt (INR c) - 1)).
    { apply Rlt_le; apply Rinv_0_lt_compat; apply sqrt_c_minus_1_pos; assumption. }
    assert (Hbound_single_nonneg : 0 <= (INR c)^2 / 4 * sqrt (INR n / INR m) / (sqrt (INR c) - 1)).
    { apply Rmult_le_pos; [exact Hnum_nonneg | exact Hinv_den_nonneg]. }
    assert (Hbound_rest_nonneg : 0 <= bound_rest).
    {
      apply fold_right_Rmult_nonneg.
      apply Forall_map.
      apply Forall_forall; intros [n0 m0] Hin.
      pose proof Hin as Hin_copy.
      apply List.in_combine_l in Hin; simpl in Hin.
      apply List.in_combine_r in Hin_copy; simpl in Hin_copy.
      apply Forall_forall with (x := n0) in Hns'; auto.
      apply Forall_forall with (x := m0) in Hms'; auto.
      assert (Hn0_pos : 0 < INR n0) by (apply lt_0_INR; lia).
      assert (Hm0_pos : 0 < INR m0) by (apply lt_0_INR; lia).
      assert (Hdiv_nonneg : 0 <= INR n0 / INR m0).
      { apply Rmult_le_pos; [apply Rlt_le; exact Hn0_pos | apply Rlt_le; apply Rinv_0_lt_compat; exact Hm0_pos]. }
      assert (Hsqrt_nonneg' : 0 <= sqrt (INR n0 / INR m0)) by (apply sqrt_pos; exact Hdiv_nonneg).
      apply Rmult_le_pos.
      - apply Rmult_le_pos.
        + apply Rmult_le_pos; [exact Hc_sq_nonneg | exact Hinv4_nonneg].
        + exact Hsqrt_nonneg'.
      - exact Hinv_den_nonneg.
    }
    assert (Hnonneg_Cnorm_rest : 0 <= Cnorm rest) by apply Cnorm_ge_0.
    apply Rmult_le_compat;
      [ exact Hnonneg_Cnorm_nm
      | exact Hnonneg_Cnorm_rest
      | exact Hbound_single
      | exact Hbound_rest ].
Qed.

(* 序列指数增长 *)
Lemma seq_exp_growth_aux :
  forall (seq : nat -> nat) (C : nat) (a n : nat),
    (C >= 2)%nat ->
    (forall i, (INR (seq (S i)) > INR C * INR (seq i))%R) ->
    (INR (seq ((a + n)%nat)) >= ((INR C) ^ n)%R * INR (seq a))%R.
Proof.
  intros seq C a n HC H_grow.
  revert a.
  induction n as [| n IH]; intros a.
  { simpl. rewrite Nat.add_0_r. rewrite Rmult_1_l. apply Rle_refl. }
  { rewrite Nat.add_succ_r.
    pose proof (H_grow (a + n)%nat) as Hstep.
    specialize (IH a).
    assert (H_mul : (INR C * ((INR C)^n * INR (seq a)) <= INR C * INR (seq (a + n)%nat))%R).
    { apply Rmult_le_compat_l; [apply Rlt_le, lt_0_INR; lia | apply Rge_le; exact IH]. }
    assert (H_eq : (INR C * ((INR C)^n * INR (seq a)) = ((INR C) ^ (S n))%R * INR (seq a))%R).
    { simpl pow; ring. }
    lra.
  }
Qed.

(* 序列严格指数增长 *)
Lemma seq_exp_growth :
  forall (seq : nat -> nat) (C : nat),
    (C >= 2)%nat ->
    (forall i, INR (seq (S i)) > INR C * INR (seq i)) ->
    forall (a b : nat), (a < b)%nat ->
    INR (seq b) > (INR C) ^ (b - a)%nat * INR (seq a).
Proof.
  intros seq C HC H_grow a b Hlt.
  assert (Hb_eq : (b = a + (b - a))%nat) by lia.
  rewrite Hb_eq.
  remember (b - a)%nat as n eqn:Hn.
  assert (Hn_pos : (n > 0)%nat) by lia.
  destruct n as [| n'].
  - lia.
  - pose proof (seq_exp_growth_aux seq C a (S n') HC H_grow) as Haux.
    replace (a + S n')%nat with (S (a + n'))%nat by lia.
    replace (S (a + n') - a)%nat with (S n')%nat by lia.
    simpl pow.
    pose proof (H_grow (a + n')%nat) as Hlast.
    assert (Hind : INR (seq (a + n')%nat) >= (INR C)^n' * INR (seq a)).
    { apply (seq_exp_growth_aux seq C a n' HC H_grow). }
    assert (H_mul : INR C * INR (seq (a + n')%nat) >= INR C * ((INR C)^n' * INR (seq a))).
    { apply Rle_ge. apply Rmult_le_compat_l; [apply Rlt_le, lt_0_INR; lia | apply Rge_le; exact Hind]. }
    apply Rgt_ge_trans with (INR C * INR (seq (a + n')%nat)).
    + exact Hlast.
    + rewrite (Rmult_assoc (INR C) ((INR C)^n') (INR (seq a))).
      exact H_mul.
Qed.

(* 严格递增列表中的索引差与元素差关系 *)
Lemma nth_diff_ge_index_diff :
  forall (I : list nat) i j,
    Sorted Nat.lt I ->
    (i < j < length I)%nat ->
    (nth j I 0 >= nth i I 0 + (j - i)%nat)%nat.
Proof.
  induction I as [|x l IH]; intros i j Hsort (Hij, Hjlen).
  - simpl in Hjlen; lia.
  - simpl in Hjlen.
    inversion Hsort as [|? ? Hhd Htl]; subst.
    destruct i as [|i'], j as [|j'].
    + exfalso; lia.
    + simpl nth.
      assert (Hj'_len : (j' < length l)%nat) by (simpl in Hjlen; lia).
      destruct j' as [|j''].
      * assert (Hx_lt : (x < nth 0 l 0)%nat). {
          destruct l as [|y t]; simpl in *.
          - lia.
          - inversion Htl; assumption.
        }
        lia.
      * assert (Hx_lt : (x < nth 0 l 0)%nat). {
          destruct l as [|y t]; simpl in *.
          - lia.
          - inversion Htl; assumption.
        }
        assert (H_lt : (0 < S j'' < length l)%nat) by (split; [lia| exact Hj'_len]).
        specialize (IH 0%nat (S j'') Hhd H_lt).
        simpl in IH.
        assert (Hx_succ : (x + 1 <= nth 0 l 0)%nat) by lia.
        lia.
    + exfalso; lia.
    + simpl nth.
      apply (IH i' j' Hhd).
      split; [lia| simpl in Hjlen; lia].
Qed.

(* 平方根除法上界估计 *)
Lemma sqrt_div_bound :
  forall (C d n1 n2 : nat),
    (C >= 2)%nat -> (d >= 1)%nat ->
    INR n2 >= (INR C) ^ d * INR n1 ->
    sqrt (INR n1 * INR n2) / (2 * (INR n2 - INR n1)) <= / ((sqrt (INR C)) ^ d).
Proof.
  intros C d n1 n2 HC Hd Hineq.
  assert (HC_R : INR C >= 2). {
    apply Rle_ge; apply le_INR in HC; simpl in HC; exact HC.
  }
  assert (HC_R1 : 1 <= INR C) by lra.

  assert (Hle_d : (1 <= d)%nat) by lia.
  assert (Hpow_inc : (INR C)^1 <= (INR C)^d). {
    apply Rle_pow; auto.
  }
  simpl in Hpow_inc.
  assert (Hpow_ge_2 : (INR C)^d >= 2) by lra.
  set (k := (INR C) ^ d) in *.
  assert (Hk_ge2 : k >= 2) by exact Hpow_ge_2.
  assert (Hk_ge2' : 2 <= k) by (apply Rge_le; exact Hk_ge2).

  destruct n1 as [|n1'].
  { simpl INR; rewrite Rmult_0_l, sqrt_0.
    rewrite Rdiv_0_l.
    apply Rle_trans with 0.
    - lra.
    - apply Rlt_le; apply Rinv_0_lt_compat; apply pow_lt; apply sqrt_lt_R0_c; apply lt_0_INR; lia. }

  assert (Hn1_pos : INR (S n1') > 0) by (apply lt_0_INR; lia).

  assert (Hn2_ge_n1 : INR n2 >= INR (S n1')). {
    apply Rle_ge.
    apply (Rle_trans _ (k * INR (S n1'))).
    - nra.
    - apply Rge_le; exact Hineq.
  }

  assert (Hdiff_pos : 0 < INR n2 - INR (S n1')). {
    destruct (Rlt_le_dec (INR (S n1')) (INR n2)) as [Hlt | Hle].
    - apply Rgt_minus; exact Hlt.
    - assert (Heq : INR (S n1') = INR n2) by lra.
      exfalso.
      assert (Htmp : k * INR (S n1') > INR (S n1')). {
        apply Rlt_le_trans with (2 * INR (S n1')).
        - nra.
        - apply Rmult_le_compat_r; [apply Rlt_le; exact Hn1_pos | exact Hk_ge2'].
      }
      apply (Rgt_not_le _ _ Htmp).
      rewrite <- Heq in Hineq.
      apply Rge_le in Hineq.
      exact Hineq.
  }

  assert (H2_diff_pos : 0 < 2 * (INR n2 - INR (S n1')))
    by (apply Rmult_lt_0_compat; [lra | exact Hdiff_pos]).
  assert (H_nonneg_left : 0 <= sqrt (INR (S n1') * INR n2) * (sqrt (INR C)) ^ d). {
    apply Rmult_le_pos; [apply sqrt_pos | ].
    apply Rlt_le.
    apply pow_lt; apply sqrt_lt_R0_c; apply lt_0_INR; lia.
  }
  assert (H_nonneg_right : 0 <= 2 * (INR n2 - INR (S n1'))) by lra.

  apply Rmult_le_reg_r with (2 * (INR n2 - INR (S n1'))); [lra |].
  unfold Rdiv; rewrite Rmult_assoc.
  rewrite Rinv_l; [rewrite Rmult_1_r | apply Rgt_not_eq; exact H2_diff_pos].
  apply Rmult_le_reg_l with ((sqrt (INR C)) ^ d). {
    apply pow_lt; apply sqrt_lt_R0_c; apply lt_0_INR; lia.
  }
  rewrite Rmult_comm.
  assert (H_simpl : (sqrt (INR C)) ^ d * (/ (sqrt (INR C)) ^ d * (2 * (INR n2 - INR (S n1'))))
                    = 2 * (INR n2 - INR (S n1'))). {
    field; apply Rgt_not_eq; apply pow_lt; apply sqrt_lt_R0_c; apply lt_0_INR; lia.
  }
  rewrite H_simpl.
  apply Rsqr_incr_0 with (x := sqrt (INR (S n1') * INR n2) * (sqrt (INR C)) ^ d)
                         (y := 2 * (INR n2 - INR (S n1'))).
  - rewrite Rsqr_mult.
    rewrite (Rsqr_sqrt (INR (S n1') * INR n2)) by (apply Rmult_le_pos; apply pos_INR).
    unfold Rsqr at 1.
    rewrite <- (Rpow_mult_distr (sqrt (INR C)) (sqrt (INR C)) d).
    rewrite sqrt_sqrt by (apply Rlt_le; apply lt_0_INR; lia).
    fold k.
    replace (Rsqr (2 * (INR n2 - INR (S n1')))) with (4 * (INR n2 - INR (S n1')) ^ 2).
    2: { unfold Rsqr; ring. }
    set (a := INR (S n1')); set (b := INR n2); fold k.
    assert (Hineq_poly : a * b * k <= 4 * (b - a) ^ 2). {
      assert (H_2a_le_b : 2 * a <= b). {
        apply (Rle_trans (2 * a) (k * a) b).
        - apply Rmult_le_compat_r; [apply Rlt_le; exact Hn1_pos | exact Hk_ge2'].
        - apply Rge_le; exact Hineq.
      }
      assert (Hb_pos : 0 < b). {
        unfold b. apply lt_0_INR.
        destruct n2 as [|n2'].
        - exfalso.
          simpl in Hineq.
          assert (Hpos : k * INR (S n1') > 0). {
            apply Rmult_lt_0_compat.
            - apply Rlt_le_trans with 2; [lra | exact Hk_ge2'].
            - exact Hn1_pos.
          }
          apply (Rlt_irrefl 0).
          apply Rlt_le_trans with (k * INR (S n1')).
          + exact Hpos.
          + now apply Rge_le.
        - lia.
      }
      assert (H1 : a * b * k <= b * b). {
        replace (a * b * k) with ((k * a) * b) by ring.
        apply Rmult_le_compat_r; [apply Rlt_le; exact Hb_pos | apply Rge_le; exact Hineq].
      }
      assert (H4 : b * b <= 4 * (b - a) ^ 2). {
        nra.
      }
      lra.
    }
    exact Hineq_poly.
  - exact H_nonneg_left.
  - exact H_nonneg_right.
Qed.

(* 满足下界约束的乘积与平方缩放不等式 *)
Lemma aux_ineq (k x : R) : k >= 2 -> x >= k -> x * k <= 4 * (x - 1)^2.
Proof.
  intros Hk Hx. nra.
Qed.

(* 稀疏序列严格递增性 *)
Lemma seq_strict_growth_lt (seq : nat -> nat) (C a b : nat) :
  (C >= 2)%nat ->
  (forall i, INR (seq (S i)) > INR C * INR (seq i)) ->
  (forall i, (seq i >= 2)%nat) ->
  (a < b)%nat ->
  (seq a < seq b)%nat.
Proof.
  intros HC Hsparse Hseq_ge2 Ha_lt_b.
  set (n1 := seq a). set (n2 := seq b).
  assert (Hba_ge1 : (b - a >= 1)%nat) by (clear -Ha_lt_b; lia).
  assert (Hn1_lt_n2_R : INR n1 < INR n2).
  {
    pose proof (seq_exp_growth seq C HC Hsparse a b Ha_lt_b) as H_exp.
    assert (H_pow_ge : INR C <= INR C ^ (b - a)).
    { assert (H_pow' : INR C ^ 1 <= INR C ^ (b - a)).
      { assert (H1leC : 1 <= INR C).
        { apply Rle_trans with (INR 2); [simpl; lra | apply le_INR; lia]. }
        apply Rle_pow; [exact H1leC | lia]. }
      replace (INR C ^ 1) with (INR C) in H_pow' by (simpl; ring).
      exact H_pow'. }
    assert (H_mul : INR n2 > INR C ^ (b - a) * INR n1).
    { apply H_exp. }
    assert (H_CN1_lt : INR C * INR n1 < INR n2).
    {
      apply Rle_lt_trans with (INR C ^ (b - a) * INR n1).
      - apply Rmult_le_compat_r.
        + apply pos_INR.
        + exact H_pow_ge.
      - exact H_mul.
    }
    apply (Rlt_trans _ (INR C * INR n1)).
    - replace (INR n1) with (1 * INR n1) at 1 by ring.
      apply Rmult_lt_compat_r.
      + apply (lt_0_INR n1).
        specialize (Hseq_ge2 a); unfold n1; lia.
      + change 1 with (INR 1); apply lt_INR; lia.
    - exact H_CN1_lt.
  }
  apply INR_lt; exact Hn1_lt_n2_R.
Qed.

(* 基于上界截断的内积求和简化 *)
Lemma Csum_psi_conj_truncate_by_upper_bound :
  forall (seq : nat -> nat) (I : list nat) (i : nat) (n1 n2 : nat),
    (forall i, (seq i >= 2)%nat) ->
    (forall a b, (a < b)%nat -> (seq a < seq b)%nat) ->
    (i < length I)%nat ->
    (nth i I 0%nat < fold_right Nat.max 0%nat I)%nat ->
    n1 = seq (nth i I 0%nat) ->
    Csum (fun k : nat => psi n1 k *c Cconj (psi n2 k))
         ((seq (fold_right Nat.max 0%nat I) - 1)%nat) =
    Csum (fun k : nat => psi n1 k *c Cconj (psi n2 k)) n1.
Proof.
  intros seq I i n1 n2 Hseq_ge2 Hstrict Hi_len Hlt_max Hn1.
  subst n1.
  set (a := nth i I 0%nat) in *.
  set (N := seq (fold_right Nat.max 0%nat I)).

  assert (Ha_in : In a I) by (apply nth_In; exact Hi_len).
  assert (Ha_lt_max : (a < fold_right Nat.max 0%nat I)%nat) by exact Hlt_max.

  assert (Hseq_lt_N : (seq a < N)%nat).
  { unfold N. apply Hstrict; exact Ha_lt_max. }

  assert (Hle_pred : (seq a <= N - 1)%nat) by lia.

  set (f := fun k : nat => psi (seq a) k *c Cconj (psi n2 k)).
  assert (Hzero : forall k : nat, (seq a <= k)%nat -> f k = C0).
  { intros k Hk. unfold f. rewrite psi_ge_n_zero by exact Hk. rewrite Cmul_0_l. reflexivity. }

  assert (Hzero_interval : forall k : nat, (seq a <= k < N - 1)%nat -> f k = C0).
  { intros k [Hk1 _]. apply Hzero; exact Hk1. }

  exact (Csum_trunc_tail f (seq a) (N - 1) Hle_pred Hzero_interval).
Qed.

(* 单位根特征序列的模长恒一 *)
Lemma Cnorm_phi_1 : forall n k, (k < n)%nat -> Cnorm (UnconditionalBasis.phi n k) = 1%R.
Proof.
  intros n k Hlt.
  assert (Hsq : Cnorm_sq (UnconditionalBasis.phi n k) = 1) by (apply Cnorm_sq_phi; exact Hlt).
  unfold Cnorm; rewrite Hsq; apply sqrt_1.
Qed.

(* 非负实数嵌入的模恒等式 *)
Lemma Cnorm_Cof_real_pos : forall r : R, 0 <= r -> Cnorm (Cof_real r) = r.
Proof.
  intros r Hr.
  unfold Cof_real, Cnorm, Cnorm_sq, Rsqr; simpl.
  rewrite Rmult_0_l, Rplus_0_r.
  apply sqrt_square; exact Hr.
Qed.

(* 缩放特征序列的模公式 *)
Lemma Cnorm_psi : forall n k,
  (n >= 1)%nat -> (k < n)%nat ->
  Cnorm (psi n k) = 1 / sqrt (INR n).
Proof.
  intros n k Hn_ge1 Hk_lt.
  assert (Hn_pos : 0 < INR n) by (apply lt_0_INR; lia).
  assert (Hsqrt_pos : 0 < sqrt (INR n)) by (apply sqrt_lt_R0_c; exact Hn_pos).
  unfold psi.
  rewrite Cnorm_mult.
  rewrite (Cnorm_Cof_real_pos (1 / sqrt (INR n))).
  - rewrite Cnorm_phi_1 by exact Hk_lt. field. apply Rgt_not_eq; exact Hsqrt_pos.
  - unfold Rdiv; apply Rmult_le_pos; [lra | left; apply Rinv_0_lt_compat; exact Hsqrt_pos].
Qed.

(* 内积范数一般上界（含尾项） *)
Lemma inner_product_norm_bound_general_n :
  forall n1 n2,
    (n1 >= 2)%nat -> (n2 >= 2)%nat -> (n1 < n2)%nat ->
    Cnorm (Csum (fun k : nat => psi n1 k *c Cconj (psi n2 k)) n1) <=
    sqrt (INR n1 * INR n2) / (2 * (INR n2 - INR n1))
    + 1 / sqrt (INR n1 * INR n2).
Proof.
  intros n1 n2 H1 H2 Hlt.
  destruct n1 as [|m]; [lia|].
  simpl (Csum _ (S m)).
  set (f := fun k : nat => psi (S m) k *c Cconj (psi n2 k)).
  set (prev := Csum f m).
  set (last := f m).
  assert (Hprev_bound :
    Cnorm prev <= sqrt (INR (S m) * INR n2) / (2 * (INR n2 - INR (S m)))).
  {
    pose proof (inner_product_norm_bound_general (S m) n2 H1 H2 Hlt) as Hgen.
    assert (Heq : (S m - 1)%nat = m) by lia.
    rewrite Heq in Hgen.
    unfold prev; exact Hgen.
  }
  assert (Hlast_norm : Cnorm last = 1 / sqrt (INR (S m) * INR n2)).
  {
    unfold last, f.
    rewrite Cnorm_mult.
    rewrite Cnorm_psi with (n := S m) (k := m) by lia.
    rewrite Cnorm_conj_eq.
    rewrite Cnorm_psi with (n := n2) (k := m).
    - assert (Hsqrt_prod : sqrt (INR (S m) * INR n2) = sqrt (INR (S m)) * sqrt (INR n2)).
      { apply sqrt_mult; apply Rlt_le; apply lt_0_INR; lia. }
      rewrite Hsqrt_prod.
      field; split; apply Rgt_not_eq; apply sqrt_lt_R0_c; apply lt_0_INR; lia.
    - apply (Nat.lt_trans _ (S m)); lia.
    - lia.
  }
  apply Rle_trans with (Cnorm prev + Cnorm last).
  - apply Cnorm_triangle.
  - apply Rplus_le_compat.
    + exact Hprev_bound.
    + rewrite Hlast_norm; apply Rle_refl.
Qed.

(* 有序列表索引大小关系 *)
Lemma nth_sorted_strict_lt (I : list nat) (i j : nat) (Hsorted : Sorted Nat.lt I) 
  (Hij : (i < j)%nat) (Hi_len : (i < length I)%nat) (Hj_len : (j < length I)%nat) : 
  (nth i I 0%nat < nth j I 0%nat)%nat.
Proof.
  pose proof (nth_diff_ge_index_diff I i j Hsorted (conj Hij Hj_len)) as Hge.
  assert (H_pos : (j - i >= 1)%nat) by (clear -Hij; lia).
  assert (Hle : (nth i I 0%nat + (j - i) <= nth j I 0%nat)%nat) by exact Hge.
  assert (Hlt' : (nth i I 0%nat < nth i I 0%nat + (j - i))%nat). {
    destruct (j - i)%nat eqn:Heq; [lia|].
    simpl. lia.
  }
  eapply Nat.lt_le_trans; eassumption.
Qed.

(* 列表最大值对序列值的上界 *)
Lemma Nmax_upper_bound (seq : nat -> nat) (I : list nat) (j : nat) 
  (Hseq_mono : forall x y, (x <= y)%nat -> (seq x <= seq y)%nat) 
  (Hj_len : (j < length I)%nat) : 
  (seq (nth j I 0%nat) <= seq (fold_right Nat.max 0%nat I))%nat.
Proof.
  apply Hseq_mono.
  apply fold_right_max_ge.
  apply nth_In; exact Hj_len.
Qed.

(* 大于等于二的整数对应实数的平方不小于四 *)
Lemma INR_sq_ge_4 : forall n, (n >= 2)%nat -> INR n * INR n >= 4.
Proof.
  intros n H. apply le_INR in H. simpl in H. nra.
Qed.

(* 平方根与实数的正整数幂可交换 *)
Lemma sqrt_pow_INR_eq : forall C d, (C >= 2)%nat -> sqrt ((INR C) ^ d) = (sqrt (INR C)) ^ d.
Proof.
  intros C d HC. induction d as [|d' IH].
  - simpl; rewrite sqrt_1; reflexivity.
  - simpl; rewrite sqrt_mult.
    + rewrite IH; reflexivity.
    + apply Rlt_le, lt_0_INR; lia.
    + apply pow_le; apply Rlt_le, lt_0_INR; lia.
Qed.

(* 稀疏序列控制下平方根倒数的衰减上界 *)
Lemma sparse_sqrt_inv_bound : forall (C n1 n2 d : nat),
  (C >= 2)%nat -> (n1 >= 2)%nat -> (d >= 1)%nat ->
  INR n2 >= (INR C) ^ d * INR n1 ->
  1 / sqrt (INR n1 * INR n2) <= / ((sqrt (INR C)) ^ d).
Proof.
  intros C n1 n2 d HC Hn1 Hd Hineq.
  assert (Hsq_n1 : INR n1 * INR n1 >= 4) by (apply INR_sq_ge_4; exact Hn1).
  assert (Hsq_ge : INR n1 * INR n2 >= 4 * (INR C)^d). {
    assert (Htemp : INR n1 * INR n2 >= INR C ^ d * (INR n1 * INR n1)). {
      assert (Hle : INR C ^ d * INR n1 <= INR n2) by (apply Rge_le; exact Hineq).
      assert (Hpos : 0 <= INR n1) by (apply pos_INR; lia).
      apply (Rmult_le_compat_r (INR n1)) in Hle; [| exact Hpos].
      assert (Hleft : (INR C ^ d * INR n1) * INR n1 = INR C ^ d * (INR n1 * INR n1)) by ring.
      assert (Hright : INR n2 * INR n1 = INR n1 * INR n2) by ring.
      rewrite Hleft, Hright in Hle.
      apply Rle_ge; exact Hle.
    }
    apply Rle_ge.
    apply Rle_trans with (INR C ^ d * (INR n1 * INR n1)).
    - rewrite (Rmult_comm (INR C ^ d)).
      apply Rmult_le_compat_r.
      + apply pow_le; apply pos_INR.
      + apply Rge_le; exact Hsq_n1.
    - apply Rge_le; exact Htemp.
  }
  assert (Hsqrt_ge : sqrt (INR n1 * INR n2) >= 2 * sqrt ((INR C)^d)). {
    apply Rle_ge.
    assert (Heq : 2 * sqrt ((INR C)^d) = sqrt (4 * (INR C)^d)). {
      rewrite sqrt_mult; [| lra | apply pow_le; apply pos_INR].
      assert (Hsqrt4 : sqrt 4 = 2) by (apply sqrt_square; lra).
      rewrite Hsqrt4; ring.
    }
    rewrite Heq.
    apply sqrt_le_1_c;
      [ apply Rmult_le_pos; [lra | apply pow_le; apply pos_INR]
      | apply Rmult_le_pos; apply pos_INR
      | apply Rge_le; exact Hsq_ge ].
  }
  assert (Hpos1 : 0 < 2 * sqrt ((INR C) ^ d)). {
    apply Rmult_lt_0_compat; [lra | apply sqrt_lt_R0_c; apply pow_lt; apply lt_0_INR; lia].
  }
  assert (Hpos2 : 0 < sqrt (INR n1 * INR n2)). {
    apply sqrt_lt_R0_c.
    apply Rmult_lt_0_compat.
    - apply lt_0_INR; lia.
    - assert (Hn2_pos : 0 < INR n2). {
        apply Rlt_le_trans with (INR C ^ d * INR n1).
        * apply Rmult_lt_0_compat.
          + apply pow_lt; apply lt_0_INR; lia.
          + apply lt_0_INR; lia.
        * apply Rge_le; exact Hineq.
      }
      exact Hn2_pos.
  }
  assert (Hle : 2 * sqrt ((INR C) ^ d) <= sqrt (INR n1 * INR n2)). {
    apply Rge_le; exact Hsqrt_ge.
  }
  assert (Hinv1 : 1 / sqrt (INR n1 * INR n2) <= 1 / (2 * sqrt ((INR C) ^ d))). {
    unfold Rdiv; rewrite !Rmult_1_l.
    apply (Rinv_le_contravar _ _ Hpos1 Hle).
  }
  assert (Heq_pow : sqrt ((INR C) ^ d) = (sqrt (INR C)) ^ d). {
    apply sqrt_pow_INR_eq; exact HC.
  }
  assert (H_pos_pow : (sqrt (INR C)) ^ d > 0). {
    apply pow_lt; apply sqrt_lt_R0_c; apply lt_0_INR; lia.
  }
  assert (Hinv2 : 1 / (2 * sqrt ((INR C) ^ d)) <= / ((sqrt (INR C)) ^ d)). {
    rewrite Heq_pow.
    unfold Rdiv.
    rewrite Rmult_1_l.
    apply (Rinv_le_contravar ((sqrt (INR C)) ^ d) (2 * (sqrt (INR C)) ^ d)).
    - exact H_pos_pow.
    - nra.
  }
  eapply Rle_trans; [exact Hinv1 | exact Hinv2].
Qed.

(* 稀疏序列索引差对应的指数下界 *)
Lemma sparse_index_growth (seq : nat -> nat) (I : list nat) (C : nat) 
  (HC : (C >= 2)%nat) 
  (Hseq_ge2 : forall i, (seq i >= 2)%nat)
  (Hsparse : forall i, INR (seq (S i)) > INR C * INR (seq i))
  (Hsorted : Sorted Nat.lt I) 
  (i j : nat) (Hij : (i < j)%nat) (Hi_len : (i < length I)%nat) (Hj_len : (j < length I)%nat) :
  let a := nth i I 0%nat in
  let b := nth j I 0%nat in
  let n1 := seq a in
  let n2 := seq b in
  INR n2 >= (INR C) ^ (j - i) * INR n1.
Proof.
  intros a b n1 n2.
  assert (Ha_lt_b : (a < b)%nat) by (exact (nth_sorted_strict_lt I i j Hsorted Hij Hi_len Hj_len)).
  set (d := (j - i)%nat) in *.
  pose proof (seq_exp_growth seq C HC Hsparse a b Ha_lt_b) as H_exp.
  assert (Hdiff_ge : (b - a >= d)%nat). {
    assert (b >= a + d)%nat. {
      apply (nth_diff_ge_index_diff I i j Hsorted); split; assumption.
    }
    lia.
  }
  assert (Hle_exp : (d <= b - a)%nat) by (unfold d; lia).
  assert (Hpow_ge : (INR C) ^ (b - a) >= (INR C) ^ d). {
    apply Rle_ge.
    apply Rle_pow with (x := INR C) (m := d) (n := (b - a)%nat).
    - assert (HRle : 1 <= INR C). {
        apply (Rle_trans _ (INR 2)); [simpl; lra | apply le_INR; lia].
      }
      exact HRle.
    - exact Hle_exp.
  }
  assert (Hmul_ineq : INR C ^ (b - a) * INR (seq a) >= INR C ^ d * INR (seq a)). {
    apply Rle_ge.
    apply Rmult_le_compat_r.
    - apply pos_INR; lia.
    - apply Rge_le; exact Hpow_ge.
  }
  assert (H_exp_le : INR C ^ (b - a) * INR (seq a) <= INR (seq b)). {
    apply Rlt_le; exact H_exp.
  }
  assert (H_gt : INR (seq b) >= INR C ^ d * INR (seq a)). {
    apply Rle_ge.
    apply Rle_trans with (INR C ^ (b - a) * INR (seq a)).
    - apply Rge_le; exact Hmul_ineq.
    - exact H_exp_le.
  }
  unfold n1, n2; exact H_gt.
Qed.

(* 有序列表中稀疏序列的指数下界 *)
Lemma decay_bound_i_lt_j (seq : nat -> nat) (I : list nat) (C : nat)
  (HC : (C >= 2)%nat) (Hseq_ge2 : forall i, (seq i >= 2)%nat)
  (Hsparse : forall i, INR (seq (S i)) > INR C * INR (seq i))
  (Hsorted : Sorted Nat.lt I) (Hnodup : NoDup I)
  (i j : nat) (Hij : (i < j)%nat) (Hi_len : (i < length I)%nat) (Hj_len : (j < length I)%nat) :
  Cnorm (Csum (fun k : nat => psi (seq (nth i I 0%nat)) k *c Cconj (psi (seq (nth j I 0%nat)) k))
              ((seq (fold_right Nat.max 0%nat I) - 1)%nat))
  <= 2 * / ((sqrt (INR C)) ^ (Z.abs_nat (Z.of_nat i - Z.of_nat j))).
Proof.
  clear Hnodup.
  set (a := nth i I 0%nat).
  set (b := nth j I 0%nat).
  set (n1 := seq a). set (n2 := seq b).
  assert (Hn1_ge2 : (n1 >= 2)%nat) by (unfold n1; apply Hseq_ge2).
  assert (Hn2_ge2 : (n2 >= 2)%nat) by (unfold n2; apply Hseq_ge2).

  assert (Hstrict : forall a0 b0, (a0 < b0)%nat -> (seq a0 < seq b0)%nat). {
    intros a0 b0 Hlt. exact (seq_strict_growth_lt seq C a0 b0 HC Hsparse Hseq_ge2 Hlt).
  }
  assert (Hseq_mono : forall x y, (x <= y)%nat -> (seq x <= seq y)%nat). {
    intros x y Hle.
    destruct (Nat.eq_dec x y) as [Heq | Hne].
    - subst y; apply Nat.le_refl.
    - assert (Hlt : (x < y)%nat) by lia.
      apply Nat.lt_le_incl, Hstrict, Hlt.
  }
  assert (Hn1_lt_n2 : (n1 < n2)%nat). {
    apply Hstrict; exact (nth_sorted_strict_lt I i j Hsorted Hij Hi_len Hj_len).
  }

  set (Nmax := seq (fold_right Nat.max 0%nat I)).
  assert (HNmax_gt_n1_strict : (n1 < Nmax)%nat). {
    apply Nat.lt_le_trans with (m := n2).
    - exact Hn1_lt_n2.
    - apply (Nmax_upper_bound seq I j Hseq_mono Hj_len).
  }
  assert (HNmax_sub_ge_n1' : (n1 <= Nmax - 1)%nat) by lia.

  set (f := fun k : nat => psi n1 k *c Cconj (psi n2 k)).
  assert (Hf_zero_ge : forall k, (n1 <= k)%nat -> f k = C0). {
    intros k Hle.
    unfold f.
    rewrite psi_zero_for_ge_n with (n := n1) (k := k) by lia.
    rewrite Cmul_0_l; reflexivity.
  }

  assert (Hsum_eq : Csum f (Nmax - 1)%nat = Csum f n1). {
    apply Csum_trunc_tail with (M := n1) (N := (Nmax - 1)%nat).
    - exact HNmax_sub_ge_n1'.
    - intros k Hk. destruct Hk as [Hk1 Hk2]. apply Hf_zero_ge; exact Hk1.
  }

  replace (Csum (fun k : nat => psi (seq (nth i I 0%nat)) k *c Cconj (psi (seq (nth j I 0%nat)) k))
                ((seq (fold_right Nat.max 0%nat I) - 1)%nat))
    with (Csum f (Nmax - 1)%nat)
    by (unfold f, n1, n2, a, b, Nmax; reflexivity).
  rewrite Hsum_eq.

  assert (Hinner_bound : Cnorm (Csum f n1) <=
                         sqrt (INR n1 * INR n2) / (2 * (INR n2 - INR n1))
                         + 1 / sqrt (INR n1 * INR n2)). {
    apply inner_product_norm_bound_general_n; auto.
  }

  set (d := (j - i)%nat).
  assert (Hd_pos : (d >= 1)%nat) by (unfold d; lia).

  assert (Hint_exp : INR n2 >= (INR C) ^ d * INR n1). {
    exact (sparse_index_growth seq I C HC Hseq_ge2 Hsparse Hsorted i j Hij Hi_len Hj_len).
  }

  assert (H_main_bound : sqrt (INR n1 * INR n2) / (2 * (INR n2 - INR n1)) <=
                         / ((sqrt (INR C)) ^ d)). {
    exact (sqrt_div_bound C d n1 n2 HC Hd_pos Hint_exp).
  }

  assert (H_extra_bound : 1 / sqrt (INR n1 * INR n2) <= / ((sqrt (INR C)) ^ d)). {
    assert (Hsq_ge : INR n1 * INR n2 >= 4 * (INR C)^d). {
      assert (Htemp : INR n1 * INR n2 >= INR C ^ d * (INR n1 * INR n1)). {
        assert (Hle : INR C ^ d * INR n1 <= INR n2) by (apply Rge_le; exact Hint_exp).
        assert (Hpos : 0 <= INR n1) by (apply pos_INR; lia).
        apply (Rmult_le_compat_r (INR n1)) in Hle; [| exact Hpos].
        assert (Htemp_eq_left : (INR C ^ d * INR n1) * INR n1 = INR C ^ d * (INR n1 * INR n1)) by ring.
        assert (Htemp_eq_right : INR n2 * INR n1 = INR n1 * INR n2) by ring.
        rewrite Htemp_eq_left, Htemp_eq_right in Hle.
        apply Rle_ge; exact Hle.
      }
      assert (Hsq_n1 : INR n1 * INR n1 >= 4). {
        assert (Hn1_lb : INR n1 >= 2). {
          apply Rle_ge; apply le_INR in Hn1_ge2; simpl in Hn1_ge2; lra.
        }
        nra.
      }
      apply Rle_ge.
      apply Rle_trans with (INR C ^ d * (INR n1 * INR n1)).
      - rewrite (Rmult_comm (INR C ^ d)).
        apply Rmult_le_compat_r.
        + apply pow_le; apply pos_INR.
        + apply Rge_le; exact Hsq_n1.
      - apply Rge_le; exact Htemp.
    }
    assert (Hsqrt_ge : sqrt (INR n1 * INR n2) >= 2 * sqrt ((INR C)^d)). {
      apply Rle_ge.
      assert (Htmp_eq : 2 * sqrt ((INR C)^d) = sqrt (4 * (INR C)^d)). {
        rewrite sqrt_mult; [| lra | apply pow_le; apply pos_INR].
        assert (Hsqrt4 : sqrt 4 = 2) by (apply sqrt_square; lra).
        rewrite Hsqrt4; ring.
      }
      rewrite Htmp_eq.
      apply sqrt_le_1_c;
        [ apply Rmult_le_pos; [lra | apply pow_le; apply pos_INR]
        | apply Rmult_le_pos; apply pos_INR
        | apply Rge_le; exact Hsq_ge ].
    }
    assert (Hpos1 : 0 < 2 * sqrt ((INR C) ^ d)).
    { apply Rmult_lt_0_compat; [lra | apply sqrt_lt_R0_c; apply pow_lt; apply lt_0_INR; lia]. }
    assert (Hpos2 : 0 < sqrt (INR n1 * INR n2)).
    { apply sqrt_lt_R0_c; apply Rmult_lt_0_compat; apply lt_0_INR; lia. }
    assert (Hle : 2 * sqrt ((INR C) ^ d) <= sqrt (INR n1 * INR n2)).
    { apply Rge_le; exact Hsqrt_ge. }
    assert (Hinv1 : 1 / sqrt (INR n1 * INR n2) <= 1 / (2 * sqrt ((INR C) ^ d))).
    { unfold Rdiv; rewrite !Rmult_1_l.
      apply (Rinv_le_contravar _ _ Hpos1 Hle). }
    assert (Hsqrt_pow_eq : sqrt ((INR C) ^ d) = (sqrt (INR C)) ^ d). {
      clear -HC.
      induction d as [| d' IH].
      * simpl; rewrite sqrt_1; reflexivity.
      * simpl; rewrite sqrt_mult.
        - rewrite IH; reflexivity.
        - apply Rlt_le, lt_0_INR; lia.
        - apply pow_le; apply pos_INR; lia.
    }
    assert (H_pos_pow : (sqrt (INR C)) ^ d > 0).
    { apply pow_lt; apply sqrt_lt_R0_c; apply lt_0_INR; lia. }
    assert (Hinv2 : 1 / (2 * sqrt ((INR C) ^ d)) <= 1 / ((sqrt (INR C)) ^ d)).
    { rewrite Hsqrt_pow_eq.
      unfold Rdiv; rewrite !Rmult_1_l.
      apply Rinv_le_contravar.
      - exact H_pos_pow.
      - lra. }
    rewrite <- (Rmult_1_l (/ ((sqrt (INR C)) ^ d))).
    eapply Rle_trans; [exact Hinv1 | exact Hinv2].
  }

  assert (Hsum_bound : sqrt (INR n1 * INR n2) / (2 * (INR n2 - INR n1))
                       + 1 / sqrt (INR n1 * INR n2)
                       <= 2 * / ((sqrt (INR C)) ^ d)). {
    generalize H_main_bound H_extra_bound; nra.
  }

  assert (Heq_abs : Z.abs_nat (Z.of_nat i - Z.of_nat j) = d). {
    unfold d. destruct (Nat.lt_trichotomy i j) as [| [Heq|Hgt]]; try lia; auto.
  }
  rewrite Heq_abs.
  eapply Rle_trans; [exact Hinner_bound | exact Hsum_bound].
Qed.

(* 有序列表中稀疏序列的单因子衰减界 *)
Lemma decay_bound_i_lt_j_one_factor (seq : nat -> nat) (I : list nat) (C : nat)
  (HC : (C >= 2)%nat) (Hseq_ge2 : forall i, (seq i >= 2)%nat)
  (Hsparse : forall i, INR (seq (S i)) > INR C * INR (seq i))
  (Hsorted : Sorted Nat.lt I) (Hnodup : NoDup I)
  (i j : nat) (Hij : (i < j)%nat) (Hi_len : (i < length I)%nat) (Hj_len : (j < length I)%nat) :
  Cnorm (Csum (fun k : nat => psi (seq (nth i I 0%nat)) k *c Cconj (psi (seq (nth j I 0%nat)) k))
              ((seq (fold_right Nat.max 0%nat I) - 1)%nat))
  <= 2 * / ((sqrt (INR C)) ^ (Z.abs_nat (Z.of_nat i - Z.of_nat j))).
Proof.
  set (a := nth i I 0%nat); set (b := nth j I 0%nat).
  set (n1 := seq a); set (n2 := seq b).

  assert (Ha_lt_b : (a < b)%nat).
  { apply (nth_sorted_strict_lt I i j Hsorted Hij Hi_len Hj_len). }
  assert (Hstrict : forall a0 b0, (a0 < b0)%nat -> (seq a0 < seq b0)%nat).
  { intros a0 b0 Hlt. apply (seq_strict_growth_lt seq C a0 b0 HC Hsparse Hseq_ge2 Hlt). }
  assert (Hn1_lt_n2 : (n1 < n2)%nat) by (apply Hstrict; exact Ha_lt_b).
  assert (Hn1_ge2 : (n1 >= 2)%nat) by (unfold n1; apply Hseq_ge2).
  assert (Hn2_ge2 : (n2 >= 2)%nat) by (unfold n2; apply Hseq_ge2).

  assert (Ha_lt_max : (a < fold_right Nat.max 0%nat I)%nat).
  { apply Nat.lt_le_trans with b; [ exact Ha_lt_b | ].
    apply fold_right_max_ge with (l := I); apply nth_In; exact Hj_len. }

  assert (Hsum_eq1 :
    Csum (fun k : nat => psi (seq a) k *c Cconj (psi (seq b) k))
         (seq (fold_right Nat.max 0%nat I) - 1) =
    Csum (fun k : nat => psi n1 k *c Cconj (psi n2 k)) n1).
  {
    apply (Csum_psi_conj_truncate_by_upper_bound seq I i n1 n2
      Hseq_ge2 Hstrict Hi_len Ha_lt_max); [ unfold n1, a; reflexivity ].
  }

  replace (Csum (fun k : nat => psi n1 k *c Cconj (psi n2 k))
                (seq (fold_right Nat.max 0%nat I) - 1))
    with (Csum (fun k : nat => psi (seq a) k *c Cconj (psi (seq b) k))
                (seq (fold_right Nat.max 0%nat I) - 1))
    by (unfold n1, n2; reflexivity).
  rewrite Hsum_eq1.

  assert (Hinner_bound :
    Cnorm (Csum (fun k : nat => psi n1 k *c Cconj (psi n2 k)) n1)
    <= sqrt (INR n1 * INR n2) / (2 * (INR n2 - INR n1))
       + 1 / sqrt (INR n1 * INR n2)).
  {
    apply inner_product_norm_bound_general_n; auto; lia.
  }

  set (d := (j - i)%nat).
  assert (Hd_pos : (d >= 1)%nat) by (unfold d; lia).

  assert (Hint_exp : INR n2 >= (INR C) ^ d * INR n1).
  {
    apply sparse_index_growth with (seq := seq) (I := I) (C := C); auto.
  }

  assert (Hsqrt_bound : sqrt (INR n1 * INR n2) / (2 * (INR n2 - INR n1))
                        <= / ((sqrt (INR C)) ^ d)).
  { apply sqrt_div_bound with (C := C) (d := d); auto; lia. }

  assert (Hinv_bound : 1 / sqrt (INR n1 * INR n2) <= / ((sqrt (INR C)) ^ d)).
  { apply sparse_sqrt_inv_bound with (C := C) (d := d); auto; lia. }

  assert (Hsum_bound : sqrt (INR n1 * INR n2) / (2 * (INR n2 - INR n1)) +
                       1 / sqrt (INR n1 * INR n2) <=
                       2 * / ((sqrt (INR C)) ^ d))
    by nra.

  assert (Heq_abs : Z.abs_nat (Z.of_nat i - Z.of_nat j) = d) by lia.
  rewrite Heq_abs.
  eapply Rle_trans; [ exact Hinner_bound | exact Hsum_bound ].
Qed.

(* 共轭零元 *)
Lemma Cconj_0 : Cconj C0 = C0.
Proof. unfold Cconj, C0; simpl; apply Complex_eq; simpl; ring. Qed.

(* 共轭加法分配 *)
Lemma Cconj_add (a b : Complex) : Cconj (a +c b) = Cconj a +c Cconj b.
Proof. destruct a, b; unfold Cadd, Cconj; simpl; apply Complex_eq; simpl; ring. Qed.

(* 共轭求和分配 *)
Lemma Cconj_Csum (f : nat -> Complex) (n : nat) :
  Cconj (Csum f n) = Csum (fun k => Cconj (f k)) n.
Proof.
  induction n as [| n IH].
  - simpl; exact Cconj_0.
  - simpl Csum at 1.
    rewrite Cconj_add.
    rewrite IH.
    reflexivity.
Qed.

(* 共轭乘以共轭 *)
Lemma Cconj_mul_conj_eq (a b : Complex) : Cconj (a *c Cconj b) = b *c Cconj a.
Proof.
  destruct a as [a1 a2], b as [b1 b2].
  unfold Cconj, Cmul, Cadd; simpl.
  apply Complex_eq; simpl; ring.
Qed.

(* 范数共轭求和对称性 *)
Lemma Cnorm_Csum_conj_sym (f g : nat -> Complex) (n : nat) :
  Cnorm (Csum (fun k => f k *c Cconj (g k)) n) =
  Cnorm (Csum (fun k => g k *c Cconj (f k)) n).
Proof.
  assert (Cconj_0_eq : Cconj C0 = C0).
  { unfold Cconj, C0; simpl; apply Complex_eq; simpl; ring. }
  assert (Cconj_add_eq : forall a b : Complex, Cconj (a +c b) = Cconj a +c Cconj b).
  { intros [a1 a2] [b1 b2]; unfold Cadd, Cconj; simpl; apply Complex_eq; simpl; ring. }
  assert (Heq : Cconj (Csum (fun k : nat => f k *c Cconj (g k)) n) =
                Csum (fun k : nat => g k *c Cconj (f k)) n).
  {
    induction n as [| n IH].
    - exact Cconj_0_eq.
    - simpl.
      rewrite Cconj_add_eq.
      rewrite IH.
      f_equal.
      apply Cconj_mul_conj_eq.
  }
  rewrite <- (Cnorm_conj_eq (Csum (fun k : nat => f k *c Cconj (g k)) n)), Heq.
  reflexivity.
Qed.

(* 绝对值取反不变性 *)
Lemma Z_abs_nat_opp (z : Z) : Z.abs_nat (- z) = Z.abs_nat z.
Proof. destruct z; simpl; auto. Qed.

(* 定理：范数衰减上界 *)
Theorem decay_bound :
  forall (seq : nat -> nat) (I : list nat) (C : nat),
    (C >= 2)%nat ->
    (forall i, (seq i >= 2)%nat) ->
    (forall i, INR (seq (S i)) > INR C * INR (seq i)) ->
    NoDup I ->
    Sorted Nat.lt I ->
    forall (i j : nat), i <> j -> (i < length I)%nat -> (j < length I)%nat ->
    let vals := map seq I in
    let inner := Csum (fun k : nat => psi (nth i vals 0%nat) k *c Cconj (psi (nth j vals 0%nat) k))
                       ((seq (fold_right Nat.max 0%nat I) - 1)%nat) in
    Cnorm inner <= 2 * / ((sqrt (INR C)) ^ (Z.abs_nat (Z.of_nat i - Z.of_nat j))).
Proof.
  intros seq I C HC Hseq_ge2 Hsparse Hnodup Hsorted i j Hneq Hi_len Hj_len.
  cbv beta.
  set (vals := map seq I).
  set (inner := Csum (fun k : nat => psi (nth i vals 0%nat) k *c Cconj (psi (nth j vals 0%nat) k))
                     ((seq (fold_right Nat.max 0%nat I) - 1)%nat)).
  unfold inner.

  pose proof (H_nth_map nat nat seq I 0%nat 0%nat i Hi_len) as Hnthi.
  pose proof (H_nth_map nat nat seq I 0%nat 0%nat j Hj_len) as Hnthj.
  unfold vals in *; simpl in *.
  rewrite Hnthi, Hnthj.
  set (a := nth i I 0%nat).
  set (b := nth j I 0%nat).
  clear Hnthi Hnthj.

  assert (Hij_cases : (i < j)%nat \/ (j < i)%nat).
  { destruct (Nat.lt_trichotomy i j) as [H|[H|H]]; auto; exfalso; apply Hneq; exact H. }
  destruct Hij_cases as [Hij | Hji].
  - eapply decay_bound_i_lt_j_one_factor; eauto.
  - pose proof (Cnorm_Csum_conj_sym (fun k : nat => psi (seq a) k) (fun k : nat => psi (seq b) k)
                                    ((seq (fold_right Nat.max 0%nat I) - 1)%nat)) as Hsym.
    rewrite Hsym.
    pose proof (decay_bound_i_lt_j_one_factor seq I C HC Hseq_ge2 Hsparse Hsorted Hnodup j i Hji Hj_len Hi_len) as Hbound.
    simpl in Hbound.
    replace (Z.abs_nat (Z.of_nat i - Z.of_nat j)) with (Z.abs_nat (Z.of_nat j - Z.of_nat i)).
    2: {
      replace (Z.of_nat i - Z.of_nat j)%Z with (- (Z.of_nat j - Z.of_nat i))%Z by ring.
      rewrite Z_abs_nat_opp.
      reflexivity.
    }
    exact Hbound.
Qed.

(* 累加和递推关系 *)
Lemma sum_f_R0_S (f : nat -> R) (n : nat) : sum_f_R0 f (S n) = sum_f_R0 f n + f (S n).
Proof.
  induction n as [| n IH].
  - simpl; ring.
  - simpl; reflexivity.
Qed.

(* 几何级数倒数部分和的上界估计 *)
Lemma geom_series_reciprocal_bound (r : R) (k : nat) : r > 1 ->
  sum_f_R0 (fun d => / (r ^ S d)) k <= / (r - 1).
Proof.
  intros Hr.
  assert (Hr0 : r > 0) by lra.
  assert (Hr_ne1 : r <> 1) by lra.
  set (q := / r).
  assert (Hq_ne1 : q <> 1).
  { intro H.
    unfold q in H.
    apply (f_equal (fun x => x * r)) in H.
    rewrite Rinv_l in H; [| lra].
    rewrite Rmult_1_l in H.
    apply Hr_ne1; symmetry; exact H. }
  assert (Hq_pos : 0 < q) by (apply Rinv_0_lt_compat; lra).

  assert (Hgeom : forall n : nat, sum_f_R0 (fun i : nat => q ^ i) n = (1 - q ^ S n) / (1 - q)).
  { induction n as [|n IH]; simpl.
    - field; intro H; apply Hq_ne1; lra.
    - rewrite IH; simpl.
      field; intro H; apply Hq_ne1; lra. }

  assert (Heq_term : forall d : nat, / (r ^ S d) = q * (q ^ d)).
  { intro d.
    change (r ^ S d) with (r * r ^ d).
    rewrite Rinv_mult.
    unfold q.
    rewrite <- pow_inv.
    reflexivity. }

  assert (Heq : sum_f_R0 (fun d : nat => / (r ^ S d)) k = q * sum_f_R0 (fun i : nat => q ^ i) k).
  {
    induction k as [|k IH].
    - unfold sum_f_R0.
      rewrite (Heq_term 0%nat).
      reflexivity.
    - rewrite sum_f_R0_S.
      rewrite IH.
      rewrite sum_f_R0_S.
      rewrite (Heq_term (S k)).
      ring.
  }

  rewrite Heq. rewrite Hgeom.
  assert (Heq_replace : q * ((1 - q ^ S k) / (1 - q)) = (1 - q ^ S k) / (r - 1)).
  {
    unfold q.
    field_simplify.
    - ring.
    - apply Rgt_not_eq; lra.
    - split; apply Rgt_not_eq; lra.
  }
  rewrite Heq_replace.

  assert (H_r1_pos : 0 < r - 1) by lra.
  assert (Hinv_pos : 0 < / (r - 1)) by (apply Rinv_0_lt_compat; lra).
  unfold Rdiv.
  rewrite <- (Rmult_1_l (/ (r - 1))) at 2.
  apply Rmult_le_compat_r.
  - apply Rlt_le; exact Hinv_pos.
  - assert (H_q_pow_nonneg : 0 <= q ^ S k).
    { apply pow_le; apply Rlt_le; exact Hq_pos. }
    lra.
Qed.

(* 逐项不等式保持累加和序 *)
Lemma sum_f_R0_le_compat (f g : nat -> R) (n : nat) :
  (forall i, (i <= n)%nat -> f i <= g i) ->
  sum_f_R0 f n <= sum_f_R0 g n.
Proof.
  induction n as [|n IH]; intros H.
  - simpl; apply H; lia.
  - simpl.
    apply Rplus_le_compat.
    + apply IH; intros i Hi; apply H; lia.
    + apply H; lia.
Qed.

(* 累加和拆分公式 *)
Lemma sum_f_R0_split (f : nat -> R) (n p : nat) :
  (p <= n)%nat ->
  sum_f_R0 f n =
  sum_f_R0 f p +
  (if Nat.eqb (n - p) 0 then 0
   else sum_f_R0 (fun k => f (p + k + 1)%nat) (n - p - 1)).
Proof.
  intros Hle. revert p Hle.
  induction n as [|n IH]; intros p Hle.
  - assert (p = 0)%nat by lia. subst p; simpl; ring.
  - destruct (Nat.eq_dec p (S n)) as [->|Hne].
    + replace (S n - S n)%nat with 0%nat by lia.
      simpl; ring.
    + assert (le_p_n : (p <= n)%nat) by lia.
      simpl sum_f_R0 at 1.
      rewrite (IH p le_p_n).
      case (Nat.eqb (n - p) 0) eqn:Heq.
      * apply Nat.eqb_eq in Heq.
        assert (Hnp : n = p) by lia. subst n.
        replace (S p - p)%nat with 1%nat by lia.
        simpl.
        replace (p + 0 + 1)%nat with (S p) by lia.
        rewrite Rplus_0_r.
        reflexivity.
      * apply Nat.eqb_neq in Heq.
        assert (Heq' : Nat.eqb (S n - p) 0 = false).
        { apply Nat.eqb_neq. lia. }
        rewrite Heq'.
        set (g := fun k : nat => f (p + k + 1)%nat).
        replace (S n - p - 1)%nat with (n - p)%nat by lia.
        replace (n - p)%nat with (S (n - p - 1))%nat by lia.
        simpl sum_f_R0.
        replace (n - p - 1 - 0)%nat with (n - p - 1)%nat by lia.
        unfold g.
        replace (p + S (n - p - 1) + 1)%nat with (S n) by lia.
        ring.
Qed.

(* 累加和的标量乘法分配律 *)
Lemma sum_f_R0_scal_l : forall (c : R) (f : nat -> R) (m : nat),
  sum_f_R0 (fun i => c * f i) m = c * sum_f_R0 f m.
Proof.
  intros c f m; induction m as [| m' IH].
  - simpl; ring.
  - simpl sum_f_R0 at 1.
    rewrite IH.
    simpl sum_f_R0 at 2.
    rewrite <- Rmult_plus_distr_l.
    reflexivity.
Qed.

(* 基例行的求和上界估计 *)
Lemma row_sum_bound_case_zero:
  forall (n0 : nat) (vals : list nat) (M C : nat) (r : R),
    (r = sqrt (INR C)) ->
    (r > 1) ->
    (length vals = S n0) ->
    (forall j, (0 < j < S n0)%nat -> 
       Cnorm (Csum (fun k : nat => psi (nth 0 vals 0%nat) k *c Cconj (psi (nth j vals 0%nat) k)) (M - 1))
       <= 2 * / (r ^ Z.abs_nat (Z.of_nat 0 - Z.of_nat j))) ->
    sum_f_R0 (fun j : nat => if eq_nat_dec 0 j then 0
                             else Cnorm (Csum (fun k : nat => psi (nth 0 vals 0%nat) k *c Cconj (psi (nth j vals 0%nat) k)) (M - 1))) n0
    <= 4 * K (INR C).
Proof.
  intros n0 vals M C r Hr_eq Hr_gt1 Hlen Hdecay0.
  destruct n0 as [|n0'].
  - simpl. unfold K, Rdiv.
    apply Rmult_le_pos; [lra |].
    apply Rmult_le_pos; [lra |].
    apply Rlt_le, Rinv_0_lt_compat; lra.
  - assert (H_single_bound : forall j, (j < S (S n0'))%nat ->
      (if eq_nat_dec 0 j then 0
       else Cnorm (Csum (fun k : nat => psi (nth 0 vals 0%nat) k *c Cconj (psi (nth j vals 0%nat) k)) (M - 1)))
      <=
      (if eq_nat_dec 0 j then 0
       else 2 * / (r ^ Z.abs_nat (Z.of_nat 0 - Z.of_nat j)))). {
      intros j Hj. destruct (eq_nat_dec 0 j) as [Heq|Hneq].
      - subst j; apply Rle_refl.
      - apply Hdecay0; split; lia.
    }
    assert (Hsum_le : sum_f_R0 (fun j => if eq_nat_dec 0 j then 0
                     else Cnorm (Csum (fun k => psi (nth 0 vals 0%nat) k *c Cconj (psi (nth j vals 0%nat) k)) (M - 1))) (S n0')
                     <= sum_f_R0 (fun j => if eq_nat_dec 0 j then 0
                                    else 2 * / (r ^ Z.abs_nat (Z.of_nat 0 - Z.of_nat j))) (S n0')).
    { apply sum_f_R0_le_compat; intros k Hk; apply H_single_bound; lia. }
    apply (Rle_trans _ _ _ Hsum_le); clear Hsum_le H_single_bound.
    assert (Hle : (0 <= S n0')%nat) by lia.
    rewrite (sum_f_R0_split 
      (fun j : nat => if eq_nat_dec 0 j then 0 else 2 * / (r ^ Z.abs_nat (Z.of_nat 0 - Z.of_nat j)))
      (S n0') 0%nat Hle).
    simpl (sum_f_R0 _ 0).
    rewrite Nat.sub_0_r.
    replace (S n0' - 0 - 1)%nat with n0' by lia.
    simpl (0 + 0 + 1)%nat.
    replace (S n0' =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
    rewrite Rplus_0_l.
    replace (S n0' - 1)%nat with n0' by lia.
    apply Rle_trans with (sum_f_R0 (fun k : nat => 2 / (r ^ S k)) n0').
    { apply sum_f_R0_le_compat; intros k Hk.
      replace (0 + k + 1)%nat with (S k) by lia.
      destruct (eq_nat_dec 0 (S k)) as [Heq|_]; [exfalso; lia|].
      replace (Z.abs_nat (Z.of_nat 0 - Z.of_nat (S k))) with (S k) by (simpl; lia).
      unfold Rdiv; apply Rle_refl. }
    assert (Hterm_eq : (fun k : nat => 2 / (r ^ S k)) = (fun k : nat => 2 * / (r ^ S k))).
    { extensionality k; unfold Rdiv; reflexivity. }
    rewrite Hterm_eq.
    rewrite (sum_f_R0_scal_l 2 (fun k : nat => / (r ^ S k)) n0').
    assert (Hsum_geom : sum_f_R0 (fun k : nat => / (r ^ S k)) n0' <= / (r - 1)).
    { apply geom_series_reciprocal_bound; exact Hr_gt1. }
    assert (Hfactor : 2 * sum_f_R0 (fun k : nat => / (r ^ S k)) n0' <= 2 * / (r - 1)).
    { apply Rmult_le_compat_l; [lra | exact Hsum_geom]. }
    apply Rle_trans with (2 * / (r - 1)); [exact Hfactor |].
    unfold K.
    rewrite Hr_eq.
    replace (4 * (1 / (sqrt (INR C) - 1))) with (4 * / (sqrt (INR C) - 1)) by (unfold Rdiv; ring).
    apply Rmult_le_compat_r.
    - left; apply Rinv_0_lt_compat; lra.
    - lra.
Qed.

(* 自然数差整绝对值的自然数转换 *)
Lemma Z_abs_nat_sub_small : forall a b : nat, (b <= a)%nat ->
  Z.abs_nat (Z.of_nat a - Z.of_nat b) = (a - b)%nat.
Proof.
  intros a b Hle. rewrite <- Nat2Z.inj_sub by exact Hle.
  apply Zabs_nat_Z_of_nat.
Qed.

(* 整数相反数的绝对自然数值不变 *)
Lemma Zabs_nat_opp (z : Z) : Z.abs_nat (- z) = Z.abs_nat z.
Proof.
  destruct z; simpl; auto.
Qed.


(* 求和移位公式 *)
Lemma sum_f_R0_S_shift (f : nat -> R) (n : nat) :
  sum_f_R0 (fun i => f (S i)) n = sum_f_R0 f (S n) - f 0%nat.
Proof.
  induction n as [| n IH].
  - simpl; ring.
  - simpl sum_f_R0 at 1.
    rewrite IH.
    simpl (sum_f_R0 f (S (S n))).
    simpl (sum_f_R0 f (S n)).
    ring.
Qed.

(* 逐点相等求和同 *)
Lemma sum_f_R0_ext (f g : nat -> R) (n : nat) :
  (forall i, (i <= n)%nat -> f i = g i) -> sum_f_R0 f n = sum_f_R0 g n.
Proof.
  induction n as [| n IH]; intros Heq.
  - simpl. apply Heq. auto with arith.
  - rewrite !sum_f_R0_S.
    rewrite (Heq (S n)). 2: { apply le_n. }
    rewrite IH.
    + reflexivity.
    + intros i Hi. apply Heq. auto with arith.
Qed.

(* 减法次序求和恒等式 *)
Lemma sum_f_R0_sub_S (a : nat -> R) (n : nat) :
  sum_f_R0 (fun j => a (S n - j)%nat) n = sum_f_R0 (fun j => a (S (n - j))%nat) n.
Proof.
  apply sum_f_R0_ext.
  intros j Hle.
  rewrite <- Nat.sub_succ_l; [ reflexivity | exact Hle ].
Qed.

(* 逆序求和恒等式 *)
Lemma sum_f_R0_rev (a : nat -> R) (n : nat) :
  sum_f_R0 (fun j => a ((n - j)%nat)) n = sum_f_R0 a n.
Proof.
  revert a. induction n as [| n IH]; intros a.
  - reflexivity.
  - rewrite sum_f_R0_S.
    rewrite (sum_f_R0_S a n).
    replace ((S n - S n)%nat) with 0%nat by lia.
    assert (Hsub : forall j, (j <= n)%nat -> (S n - j = S (n - j))%nat)
      by (intros; lia).
    rewrite (sum_f_R0_ext (fun j => a ((S n - j)%nat))
                          (fun j => a (S (n - j)%nat)) n).
    - rewrite (IH (fun k => a (S k))).
      rewrite sum_f_R0_S_shift.
      rewrite (sum_f_R0_S a n).
      lra.
    - intros j Hj. apply f_equal, Hsub. exact Hj.
Qed.

(* 右尾几何级数界 *)
Lemma right_tail_geometric_bound (r : R) (Hr_gt1 : r > 1) (i n : nat) (F : nat -> R) :
  (i+1 < n)%nat ->
  (forall j, (j < n)%nat -> j <> i ->
      F j <= 2 / (r ^ Z.abs_nat (Z.of_nat i - Z.of_nat j))) ->
  sum_f_R0 (fun k => F (i + k + 1)%nat) (n - i - 2) <= 2 / (r - 1).
Proof.
  intros Hi1 Hdecay.
  assert (Hr_pos : r > 0) by lra.
  assert (Hgeom : forall m : nat, sum_f_R0 (fun k => 2 / r ^ S k) m <= 2 / (r - 1)). {
    intros m; unfold Rdiv; rewrite sum_f_R0_scal_l;
    apply Rmult_le_compat_l; [lra |];
    apply geom_series_reciprocal_bound; exact Hr_gt1.
  }
  assert (Hn_i_ge2 : (n - i >= 2)%nat) by lia.
  apply Rle_trans with (sum_f_R0 (fun k => 2 / r ^ S k) (n - i - 2)).
  - apply sum_f_R0_le_compat; intros k Hk.
    assert (Hk_bound : (k <= n - i - 2)%nat) by exact Hk.
    assert (Hj_lt_n : (i + k + 1 < n)%nat) by lia.
    assert (Hj_ne_i : (i + k + 1)%nat <> i) by lia.
    pose proof (Hdecay (i + k + 1)%nat Hj_lt_n Hj_ne_i) as Hbd.
    assert (Heq_exp : Z.abs_nat (Z.of_nat i - Z.of_nat (i + k + 1)) = S k) by lia.
    rewrite Heq_exp in Hbd.
    exact Hbd.
  - apply Hgeom.
Qed.

(* 分裂求和几何级数上界 *)
Lemma split_sum_geometric_bound (r : R) (Hr_gt1 : r > 1) (i n : nat) (F : nat -> R) :
  (i+1 < n)%nat ->
  (F i = 0%R) ->
  (forall j, (j < n)%nat -> j <> i ->
      F j <= 2 / (r ^ Z.abs_nat (Z.of_nat i - Z.of_nat j))) ->
  sum_f_R0 F (n - 1) <= 4 / (r - 1).
Proof.
  intros Hi1 Fi0 Hdecay.
  assert (Hi : (i < n)%nat) by lia.
  assert (Hr_pos : r > 0) by lra.

  assert (Hgeom : forall m : nat, sum_f_R0 (fun k => 2 / r ^ S k) m <= 2 / (r - 1)). {
    intros m; unfold Rdiv.
    rewrite sum_f_R0_scal_l.
    apply Rmult_le_compat_l; [lra |].
    apply geom_series_reciprocal_bound; exact Hr_gt1.
  }

  (* 左半段：索引 0..i *)
  assert (Hleft : sum_f_R0 F i <= 2 / (r - 1)). {
    destruct i as [|i'].
    - simpl; rewrite Fi0.
      apply Rle_trans with 0; [lra |].
      apply Rlt_le, Rdiv_lt_0_compat; lra.
    - simpl sum_f_R0; rewrite Fi0; rewrite Rplus_0_r.
      apply Rle_trans with (sum_f_R0 (fun k => 2 / r ^ (S i' - k)%nat) i').
      + apply sum_f_R0_le_compat; intros k Hk.
        assert (Hk_lt_n : (k < n)%nat) by lia.
        assert (Hk_ne_i : (k <> S i')%nat) by lia.
        pose proof (Hdecay k Hk_lt_n Hk_ne_i) as Hbd.
        rewrite Z_abs_nat_sub_small in Hbd by lia.
        exact Hbd.
      + rewrite (sum_f_R0_ext (fun k => 2 / r ^ (S i' - k)%nat)
                             (fun k => 2 / r ^ S (i' - k)) i').
        * rewrite (sum_f_R0_rev (fun d : nat => 2 / r ^ S d) i').
          apply Hgeom.
        * intros k Hk.
          replace (S i' - k)%nat with (S (i' - k))%nat by lia.
          reflexivity.
  }

  (* 右半段：索引 i+1..n-1 *)
  assert (Hright : sum_f_R0 (fun k => F (i + k + 1)%nat) (n - i - 2) <= 2 / (r - 1)). {
    apply right_tail_geometric_bound; assumption.
  }

  (* 拼接左右两部分 *)
  assert (Hi_le_n1 : (i <= n - 1)%nat) by lia.
  rewrite (sum_f_R0_split F (n - 1) i Hi_le_n1).
  set (d := (n - 1 - i)%nat) in *.
  destruct (Nat.eqb_spec d 0) as [Hd0 | Hdpos].
  - simpl. rewrite Rplus_0_r.
    assert (Hr_minus1_pos : r - 1 > 0) by lra.
    apply Rle_trans with (2 / (r - 1)).
    + exact Hleft.
    + unfold Rdiv.
      apply Rmult_le_compat_r.
      * left. apply Rinv_0_lt_compat. exact Hr_minus1_pos.
      * lra.
  - simpl.
    assert (Hdeq : (d - 1)%nat = (n - i - 2)%nat) by lia.
    rewrite Hdeq.
    assert (Hr_minus1_pos : r - 1 > 0) by lra.
    apply Rle_trans with (2 / (r - 1) + 2 / (r - 1)).
    - apply Rplus_le_compat.
      + exact Hleft.
      + exact Hright.
    - right. field. lra.
Qed.

(* 几何级数部分和上界 *)
Lemma geometric_series_bound (r : R) (m : nat) (Hr : r > 1) :
  sum_f_R0 (fun k => 2 / r ^ S k) m <= 2 / (r - 1).
Proof.
  unfold Rdiv.
  rewrite sum_f_R0_scal_l.
  apply Rmult_le_compat_l; [lra|].
  apply geom_series_reciprocal_bound; exact Hr.
Qed.

(* 左侧部分和上界 *)
Lemma left_half_sum_bound (r : R) (i : nat) (Hr_gt1 : r > 1) (Hi_pos : (i <> 0)%nat) :
  let F := fun j : nat => if eq_nat_dec i j then 0%R
                           else 2%R / (r ^ Z.abs_nat (Z.of_nat i - Z.of_nat j)) in
  sum_f_R0 F i <= 2%R / (r - 1).
Proof.
  intros F.
  destruct i as [| i'].
  - exfalso; apply Hi_pos; reflexivity.
  - clear Hi_pos; rename i' into i.
    simpl sum_f_R0 at 1.
    unfold F at 2.
    destruct (eq_nat_dec (S i) (S i)) as [_ | Hne]; [| exfalso; apply Hne; reflexivity].
    rewrite Rplus_0_r.
    set (F' := fun j : nat => if eq_nat_dec (S i) j then 0%R
                              else 2%R / (r ^ Z.abs_nat (Z.of_nat (S i) - Z.of_nat j))).
    fold F' in F.
    assert (Hsum_eq : sum_f_R0 F' i = sum_f_R0 (fun j : nat => 2%R / (r ^ (S i - j))) i).
    { apply sum_f_R0_ext; intros k Hk.
      unfold F'.
      destruct (eq_nat_dec (S i) k) as [Heq | Hne].
      - exfalso; subst k; lia.
      - assert (Hexp_eq : Z.abs_nat (Z.of_nat (S i) - Z.of_nat k) = (S i - k)%nat)
          by (apply Z_abs_nat_sub_small; lia).
        rewrite Hexp_eq; reflexivity.
    }
    unfold F; rewrite Hsum_eq.
    assert (H_Si_minus_j_eq : forall j : nat, (j <= i)%nat -> (S i - j)%nat = S (i - j)%nat).
    { intros j Hj; lia. }
    assert (Hsum_eq2 : sum_f_R0 (fun j : nat => 2%R / (r ^ (S i - j))) i =
                       sum_f_R0 (fun j : nat => 2%R / (r ^ S (i - j))) i).
    { apply sum_f_R0_ext; intros k Hk.
      f_equal; f_equal; apply H_Si_minus_j_eq; assumption.
    }
    rewrite Hsum_eq2.
    set (a := fun k : nat => 2%R / (r ^ S k)).
    assert (H_rev_form : sum_f_R0 (fun j : nat => 2%R / (r ^ S (i - j))) i =
                         sum_f_R0 (fun j : nat => a (i - j)%nat) i).
    { apply sum_f_R0_ext; intros j Hj; unfold a; reflexivity. }
    rewrite H_rev_form.
    rewrite (sum_f_R0_rev a i).
    unfold a.
    unfold Rdiv; rewrite sum_f_R0_scal_l.
    apply Rmult_le_compat_l; [lra |].
    apply geom_series_reciprocal_bound; exact Hr_gt1.
Qed.

(* 右侧部分和上界 *)
Lemma right_half_sum_bound (r : R) (i n : nat) (Hr_gt1 : r > 1) :
  let F := fun j : nat => if eq_nat_dec i j then 0%R
                           else 2 / (r ^ Z.abs_nat (Z.of_nat i - Z.of_nat j)) in
  sum_f_R0 (fun k : nat => F ((i + k + 1)%nat)) ((n - i - 2)%nat) <= 2 / (r - 1).
Proof.
  intros F.
  assert (Heq : sum_f_R0 (fun k : nat => F ((i + k + 1)%nat)) ((n - i - 2)%nat) =
                sum_f_R0 (fun k : nat => 2 / r ^ S k) ((n - i - 2)%nat)). {
    apply sum_f_R0_ext; intros k Hk.
    unfold F.
    destruct (eq_nat_dec i ((i + k + 1)%nat)) as [H_eq | H_ne].
    - exfalso; lia.
    - f_equal; f_equal.
      replace (Z.of_nat i - Z.of_nat (i + k + 1))%Z with (- Z.of_nat (S k))%Z by lia.
      rewrite Zabs_nat_opp.
      rewrite Zabs_nat_Z_of_nat; reflexivity.
  }
  rewrite Heq.
  unfold Rdiv at 1; rewrite sum_f_R0_scal_l.
  apply Rmult_le_compat_l; [lra |].
  apply geom_series_reciprocal_bound; exact Hr_gt1.
Qed.

(* 行和界最后索引情况 *)
Lemma row_sum_bound_when_i_last (n i : nat) (F : nat -> R) (r : R) :
  r > 1 ->
  (i < n)%nat ->
  (n <= i+1)%nat ->
  F i = 0%R ->
  (forall j, (j < n)%nat -> j <> i -> F j <= 2 / (r ^ Z.abs_nat (Z.of_nat i - Z.of_nat j))) ->
  (forall m, sum_f_R0 (fun t => 2 / r ^ S t) m <= 2 / (r - 1)) ->
  sum_f_R0 F (n - 1) <= 4 / (r - 1).
Proof.
  intros Hr_gt1 Hi H_ge HFi0 HdecayF Hgeom2.
  destruct n as [|n'].
  - inversion Hi.
  - simpl.
    assert (H_ge' : (S n' <= S i)%nat) by lia.
    assert (i_eq : i = n').
    { apply Nat.le_antisymm.
      - apply Nat.lt_succ_r; exact Hi.
      - apply le_S_n; exact H_ge'. }
    subst i.
    assert (Hleft : sum_f_R0 F (n'-1) <= 2 / (r - 1)).
    { destruct n' as [|k].
      - simpl. rewrite HFi0. apply Rle_trans with 0; [lra|].
        apply Rlt_le, Rdiv_lt_0_compat; lra.
      - replace (S k - 1)%nat with k by lia.
        apply Rle_trans with (sum_f_R0 (fun m : nat => 2 / r ^ (S k - m)) k).
        + apply sum_f_R0_le_compat; intros m Hm.
          assert (Hm_lt_SSk : (m < S (S k))%nat) by lia.
          assert (Hm_ne_Sk : m <> S k) by lia.
          pose proof (HdecayF m Hm_lt_SSk Hm_ne_Sk) as Hbd.
          assert (Heq_exp : Z.abs_nat (Z.of_nat (S k) - Z.of_nat m) = (S k - m)%nat)
            by (apply Z_abs_nat_sub_small; lia).
          rewrite Heq_exp in Hbd; exact Hbd.
        + rewrite (sum_f_R0_ext (fun m : nat => 2 / r ^ (S k - m))
                               (fun m : nat => 2 / r ^ S (k - m)) k).
          * rewrite (sum_f_R0_rev (fun d : nat => 2 / r ^ S d) k).
            apply Hgeom2.
          * intros m Hm; replace (S k - m)%nat with (S (k - m))%nat by lia; reflexivity.
    }
    destruct n' as [|k].
    - simpl. rewrite HFi0. apply Rle_trans with 0; [lra|].
      apply Rlt_le, Rdiv_lt_0_compat; lra.
    - rewrite Nat.sub_0_r.
      rewrite sum_f_R0_S.
      rewrite HFi0.
      rewrite Rplus_0_r.
      replace (S k - 1)%nat with k in Hleft by lia.
      refine (Rle_trans _ (2 / (r - 1)) _ _ _).
      + exact Hleft.
      + clear -Hr_gt1. 
        assert (Hpos : 0 < r - 1) by lra.
        assert (Hdiv : 2 / (r - 1) <= 4 / (r - 1)). {
          apply Rmult_le_compat_r with (r := / (r - 1)).
          - left; apply Rinv_0_lt_compat, Hpos.
          - lra.
        }
        exact Hdiv.
Qed.

(* 定理：行和界限 *)
Theorem row_sum_bound :
  forall (n : nat) (vals : list nat) (M : nat) (C : nat)
    (Hvals_ge2 : forall v, In v vals -> (v >= 2)%nat)
    (Hlen : length vals = n)
    (Hdecay : forall i j, i <> j -> (i < n)%nat -> (j < n)%nat ->
                Cnorm (Csum (fun k => psi (nth i vals 0%nat) k *c Cconj (psi (nth j vals 0%nat) k)) (M - 1))
                <= 2 * / ((sqrt (INR C)) ^ (Z.abs_nat (Z.of_nat i - Z.of_nat j))))
    (HCgt2 : (C > 2)%nat),
  forall i, (i < n)%nat ->
    sum_f_R0 (fun j => if eq_nat_dec i j then 0%R
                       else Cnorm (Csum (fun k => psi (nth i vals 0%nat) k *c Cconj (psi (nth j vals 0%nat) k)) (M - 1))) (n - 1)
    <= 4 * K (INR C).
Proof.
  intros n vals M C Hvals_ge2 Hlen Hdecay HCgt2 i Hi.
  assert (HCgt2_R : INR C > 2). {
    apply lt_INR in HCgt2; simpl in HCgt2; exact HCgt2.
  }
  assert (HCgt1_R : INR C > 1) by lra.
  set (r := sqrt (INR C)).
  assert (Hr_gt1 : r > 1). {
    unfold r; rewrite <- sqrt_1.
    apply sqrt_lt_1; lra.
  }
  assert (Hr_pos : r > 0) by (unfold r; apply sqrt_lt_R0_c; apply lt_0_INR; lia).

  assert (H_single_bound : forall j, (j < n)%nat ->
    (if eq_nat_dec i j then 0
     else Cnorm (Csum (fun k => psi (nth i vals 0%nat) k *c Cconj (psi (nth j vals 0%nat) k)) (M - 1)))
    <=
    (if eq_nat_dec i j then 0
     else 2 * / (r ^ Z.abs_nat (Z.of_nat i - Z.of_nat j)))). {
    intros j Hj. destruct (eq_nat_dec i j) as [Heq|Hneq].
    - subst j; apply Rle_refl.
    - unfold r; apply Hdecay; assumption.
  }

  set (F := fun j : nat => if eq_nat_dec i j then 0%R
                           else 2 * / (r ^ Z.abs_nat (Z.of_nat i - Z.of_nat j))).

  assert (Hsum_le :
    sum_f_R0 (fun j => if eq_nat_dec i j then 0
                       else Cnorm (Csum (fun k => psi (nth i vals 0%nat) k *c Cconj (psi (nth j vals 0%nat) k)) (M - 1))) (n - 1)
    <= sum_f_R0 F (n - 1)). {
    apply sum_f_R0_le_compat; intros k Hk.
    apply H_single_bound; lia.
  }

  assert (HFi0 : F i = 0%R). {
    unfold F; destruct (eq_nat_dec i i) as [Heq | Hne].
    - reflexivity.
    - exfalso; apply Hne; reflexivity.
  }

  assert (HdecayF : forall j, (j < n)%nat -> j <> i ->
              F j <= 2 / (r ^ Z.abs_nat (Z.of_nat i - Z.of_nat j))). {
    intros j Hj Hneq.
    unfold F; destruct (eq_nat_dec i j) as [Heq|Hneq'].
    - exfalso; apply Hneq; symmetry; exact Heq.
    - unfold Rdiv; reflexivity.
  }

  assert (Hgeom2 : forall m, sum_f_R0 (fun t => 2 / r ^ S t) m <= 2 / (r - 1)). {
    intros m; unfold Rdiv; rewrite sum_f_R0_scal_l;
    apply Rmult_le_compat_l; [lra|];
    apply geom_series_reciprocal_bound; exact Hr_gt1.
  }

  assert (Hbound4 : sum_f_R0 F (n - 1) <= 4 / (r - 1)). {
    destruct (Nat.lt_ge_cases (i+1) n) as [H_lt | H_ge].
    - exact (split_sum_geometric_bound r Hr_gt1 i n F H_lt HFi0 HdecayF).
    - exact (row_sum_bound_when_i_last n i F r Hr_gt1 Hi H_ge HFi0 HdecayF Hgeom2).
  }

  replace (4 * K (INR C)) with (4 / (r - 1)).
  - apply (Rle_trans _ _ _ Hsum_le).
    apply Hbound4.
  - unfold K. unfold r.
    field. apply Rgt_not_eq, sqrt_c_minus_1_pos; lia.
Qed.

(* 累加和按自然数拆分为前部与后部 *)
Lemma sum_f_R0_plus' (f : nat -> R) (n m : nat) :
  sum_f_R0 f (n + m) = sum_f_R0 f n +
    (if Nat.eqb m 0 then 0 else sum_f_R0 (fun k => f (S n + k)%nat) (m - 1)).
Proof.
  assert (Hle : (n <= n + m)%nat) by lia.
  rewrite (sum_f_R0_split f (n + m) n Hle).
  apply Rplus_eq_compat_l.
  replace (n + m - n)%nat with m by lia.
  destruct m as [|m'].
  - reflexivity.
  - simpl Nat.eqb.
    replace (m' - 0)%nat with m' by lia.
    f_equal.
    apply sum_f_R0_ext; intros k Hk.
    replace (n + k + 1)%nat with (S n + k)%nat by lia.
    reflexivity.
Qed.

(* 对角自内积范数为一 *)
Lemma diag_sum_self_norm_one :
  forall (ni : nat),
    (ni >= 2)%nat ->
    Cnorm (Csum (fun k => psi ni k *c Cconj (psi ni k)) ni) = 1%R.
Proof.
  intros ni Hni.
  assert (Hpos : (ni > 0)%nat) by lia.
  assert (Hsum : Csum (fun k => psi ni k *c Cconj (psi ni k)) ni = ComplexNumbers.C1).
  { apply Csum_orthonormal_self; exact Hpos. }
  rewrite Hsum.
  apply Cnorm_C1.
Qed.

(* 对角截断内积范数为一 *)

(* 对角内积范数为一 *)
Lemma diagonal_inner_norm_one (n_val M : nat) :
  (n_val >= 2)%nat -> (n_val < M)%nat ->
  Cnorm (Csum (fun k : nat => psi n_val k *c Cconj (psi n_val k)) (M - 1)%nat) = 1%R.
Proof.
  intros Hge2 Hlt.
  assert (Hpos : (n_val > 0)%nat) by lia.
  set (g := fun k : nat => psi n_val k *c Cconj (psi n_val k)).
  assert (Hg_zero : forall k, (n_val <= k)%nat -> g k = C0).
  { intros k Hk. unfold g. rewrite (psi_ge_n_zero n_val k Hk). rewrite Cmul_0_l. reflexivity. }
  assert (Hle' : (n_val <= M - 1)%nat) by lia.
  assert (Htrunc : Csum g (M - 1)%nat = Csum g n_val).
  {
    apply (Csum_trunc_tail g n_val (M - 1)%nat).
    - exact Hle'.
    - intros k [Hk1 Hk2]. apply Hg_zero. exact Hk1.
  }
  rewrite Htrunc.
  assert (Hsum_eq1 : Csum g n_val = ComplexNumbers.C1).
  { unfold g; apply Csum_orthonormal_self; exact Hpos. }
  rewrite Hsum_eq1.
  exact Cnorm_C1.
Qed.

(* 论文附录 A：截断归一性（diag_sum_truncated_norm_one）*)
Lemma diag_sum_truncated_norm_one (n_val M : nat) :
  (n_val >= 2)%nat -> (n_val < M)%nat ->
  Cnorm (Csum (fun k : nat => psi n_val k *c Cconj (psi n_val k)) (M - 1)%nat) = 1%R.
Proof.
  intros.
  apply diagonal_inner_norm_one; assumption.
Qed.

(* 对角自内积范数为一（当ni等于M时） *)

(* 稀疏几何级数缩放界 *)
Lemma sparse_geom_scaled_bound (n1 n2 C : nat) :
  (n1 >= 2)%nat -> (n2 >= 2)%nat -> (C >= 2)%nat ->
  (n1 < n2)%nat ->
  INR n2 >= INR C * INR C * INR n1 ->
  let θ := 2 * PI * (1 / INR n1 - 1 / INR n2) in
  1 / sqrt (INR n1 * INR n2) *
  Cnorm (Csum (fun k : nat => Cexp (0 +i (INR k * θ))) (n1 - 1)) <=
  1 / sqrt (INR n1 * INR n2) *
  (INR C / Cnorm (ComplexNumbers.C1 -c Cexp (0 +i θ))).
Proof.
  intros Hn1 Hn2 Hc Hlt Hgrowth θ.
  assert (H_geom_bound_sparse : Cnorm (Csum (fun k : nat => Cexp (0 +i (INR k * θ))) (n1 - 1)) <=
                                INR C / Cnorm (ComplexNumbers.C1 -c Cexp (0 +i θ))).
  {
    apply geometric_sum_norm_bound_sparse with (θ:=θ) (n1:=n1) (n2:=n2) (c:=C).
    - exact Hn1.
    - exact Hn2.
    - exact Hc.
    - exact Hlt.
    - unfold θ; reflexivity.
    - exact Hgrowth.
  }
  apply Rmult_le_compat_l.
  - apply Rlt_le; apply Rdiv_lt_0_compat.
    + lra.
    + apply sqrt_lt_R0_c; apply Rmult_lt_0_compat; apply lt_0_INR; lia.
  - exact H_geom_bound_sparse.
Qed.

(* 稀疏几何分母倒数不等式 *)
Lemma sparse_geom_denom_div_bound (n1 n2 C : nat) (θ : R) :
  (n1 >= 2)%nat -> (n2 >= 2)%nat -> (n1 < n2)%nat -> (C >= 2)%nat ->
  θ = 2 * PI * (1 / INR n1 - 1 / INR n2) ->
  INR C / Cnorm (ComplexNumbers.C1 -c Cexp (0 +i θ)) <= INR C / (2 * Rabs θ / PI).
Proof.
  intros Hn1 Hn2 Hlt Hc Hθ.
  assert (Htheta_bound : Rabs θ <= PI).
  { rewrite Hθ.
    replace (1 / INR n1) with (/ INR n1) by (unfold Rdiv; ring).
    replace (1 / INR n2) with (/ INR n2) by (unfold Rdiv; ring).
    apply theta_bound_pi; [lia..| lia]. }
  assert (Hdenom_lb : Cnorm (ComplexNumbers.C1 -c Cexp (0 +i θ)) >= 2 * Rabs θ / PI).
  { apply denom_lower_bound; exact Htheta_bound. }

  assert (H_theta_pos : 0 < θ).
  { rewrite Hθ.
    apply Rmult_lt_0_compat; [apply Rmult_lt_0_compat; [lra | apply PI_RGT_0] |].
    apply (proj1 (diff_inv_INR_between_0_1 n1 n2 Hn1 Hn2 Hlt)). }
  assert (H_rabs_theta_pos : 0 < Rabs θ).
  { apply Rabs_pos_lt; lra. }

  assert (H_div_pos : 0 < 2 * Rabs θ / PI).
  { apply Rdiv_lt_0_compat; [lra | apply PI_RGT_0]. }

  assert (Hpos_denom : 0 < Cnorm (ComplexNumbers.C1 -c Cexp (0 +i θ))).
  { eapply Rlt_le_trans; [exact H_div_pos | apply Rge_le; exact Hdenom_lb]. }

  assert (Hdenom_lb' : 2 * Rabs θ / PI <= Cnorm (ComplexNumbers.C1 -c Cexp (0 +i θ))).
  { apply Rge_le; exact Hdenom_lb. }

  assert (Hinv : / Cnorm (ComplexNumbers.C1 -c Cexp (0 +i θ))
                <= / (2 * Rabs θ / PI)).
  { apply Rinv_le_contravar; [exact H_div_pos | exact Hdenom_lb']. }

  apply (Rmult_le_compat_l (INR C)
           ( / Cnorm (ComplexNumbers.C1 -c Cexp (0 +i θ)) )
           ( / (2 * Rabs θ / PI) )).
  - apply pos_INR; lia.
  - exact Hinv.
Qed.

(* C等于2时的稀疏内积范数上界 *)
Lemma inner_sq_bound_with_sparse (n1 n2 C : nat) :
  (n1 >= 2)%nat -> (n2 >= 2)%nat -> (n1 < n2)%nat -> (C = 2)%nat ->
  INR n2 >= INR C * INR C * INR n1 ->
  Cnorm (Csum (fun k : nat => psi n1 k *c Cconj (psi n2 k)) (n1 - 1)) <=
  sqrt (INR n1 / INR n2) / (sqrt (INR C) - 1).
Proof.
  intros Hn1 Hn2 Hlt HC_eq Hsq; subst C.
  assert (H_improved : Cnorm (Csum (fun k : nat => psi n1 k *c Cconj (psi n2 k)) (n1 - 1)) <=
    (INR 2)^2 / 4 * sqrt (INR n1 / INR n2) / (sqrt (INR 2) - 1)).
  { apply (inner_norm_bound_improved 2 n1 n2); [simpl; lia | exact Hn1 | exact Hn2 | exact Hlt | exact Hsq]. }
  assert (Hcoeff : (INR 2)^2 / 4 = 1). { simpl; field. }
  rewrite Hcoeff in H_improved.
  rewrite Rmult_1_l in H_improved.
  exact H_improved.
Qed.

(* 稀疏序列分母下界固定不等式 *)
Lemma sparse_geom_denom_div_bound_fixed (n1 n2 C : nat) (θ : R) :
  (n1 >= 2)%nat -> (n2 >= 2)%nat -> (n1 < n2)%nat -> (C >= 2)%nat ->
  θ = 2 * PI * (1 / INR n1 - 1 / INR n2) ->
  Cnorm (ComplexNumbers.C1 -c Cexp (0 +i θ)) >= 2 * Rabs θ / PI.
Proof.
  intros Hn1 Hn2 Hlt Hc Hθ.
  eapply denom_lower_bound.
  rewrite Hθ.
  replace (1 / INR n1) with (/ INR n1) by (unfold Rdiv; ring).
  replace (1 / INR n2) with (/ INR n2) by (unfold Rdiv; ring).
  apply theta_bound_pi; [lia | lia | lia].
Qed.

(* 非对角衰减界 *)
Lemma non_diag_decay_bound (seq : nat -> nat) (I : list nat) (C : nat) :
  (C >= 2)%nat ->
  (forall i, (seq i >= 2)%nat) ->
  (forall i, INR (seq (S i)) > INR C * INR (seq i)) ->
  NoDup I ->
  Sorted Nat.lt I ->
  forall (i j : nat), i <> j -> (i < length I)%nat -> (j < length I)%nat ->
  let vals := map seq I in
  let M := S (seq (fold_right Nat.max 0%nat I)) in
  Cnorm (Csum (fun k => psi (nth i vals 0%nat) k *c Cconj (psi (nth j vals 0%nat) k)) (M - 1))
  <= 2 * / ((sqrt (INR C)) ^ (Z.abs_nat (Z.of_nat i - Z.of_nat j))).
Proof.
  intros HC Hge2 Hsparse Hdup Hsorted i j Hneq Hi Hj.
  intros vals M.
  set (Nmax := seq (fold_right Nat.max 0%nat I)).

  (* 用 M 的定义直接替换，避免产生等式目标 *)
  replace (M - 1)%nat with Nmax by (subst M; simpl; lia).
  
  assert (Hmax_in : In (fold_right Nat.max 0%nat I) I)
    by (apply max_fold_right_in; destruct I; [simpl in Hi; lia | discriminate]).
  assert (Hnth_le_max : forall idx, (idx < length I)%nat ->
    (nth idx I 0%nat <= fold_right Nat.max 0%nat I)%nat).
  { intros idx Hidx; apply fold_right_max_ge; apply nth_In; exact Hidx. }

  assert (Hlt_max: (nth i I 0%nat < fold_right Nat.max 0%nat I)%nat \/
                   (nth j I 0%nat < fold_right Nat.max 0%nat I)%nat). {
    assert (Hle_i := Hnth_le_max i Hi).
    assert (Hle_j := Hnth_le_max j Hj).
    assert (H_i_cases : (nth i I 0%nat < fold_right Nat.max 0%nat I)%nat
                        \/ nth i I 0%nat = fold_right Nat.max 0%nat I) by lia.
    destruct H_i_cases as [Hlt_i | Heq_i].
    - left; exact Hlt_i.
    - assert (H_j_cases : (nth j I 0%nat < fold_right Nat.max 0%nat I)%nat
                          \/ nth j I 0%nat = fold_right Nat.max 0%nat I) by lia.
      destruct H_j_cases as [Hlt_j | Heq_j].
      + right; exact Hlt_j.
      + exfalso.
        apply (NoDup_nth_neq_std I 0%nat i j Hdup Hi Hj Hneq).
        rewrite Heq_i, Heq_j; easy.
  }

  assert (Hseq_strict_inc : forall a b, (a < b)%nat -> (seq a < seq b)%nat). {
    intros a b Hlt; apply (seq_strict_growth_lt seq C a b HC Hsparse Hge2 Hlt).
  }

  assert (Hseq_i_or_j_lt_Nmax : (seq (nth i I 0%nat) < Nmax)%nat \/
                                 (seq (nth j I 0%nat) < Nmax)%nat). {
    destruct Hlt_max as [Hlt|Hlt]; [left|right];
      unfold Nmax; apply Hseq_strict_inc; exact Hlt.
  }

  assert (Htrunc_eq : Csum (fun k => psi (seq (nth i I 0%nat)) k *c Cconj (psi (seq (nth j I 0%nat)) k)) Nmax =
                      Csum (fun k => psi (seq (nth i I 0%nat)) k *c Cconj (psi (seq (nth j I 0%nat)) k)) (Nmax - 1)%nat). {
    assert (H_last_zero : (psi (seq (nth i I 0%nat)) (Nmax - 1)%nat *c Cconj (psi (seq (nth j I 0%nat)) (Nmax - 1)%nat))%C = C0). {
      destruct Hseq_i_or_j_lt_Nmax as [Hlt|Hlt].
      - assert (Hle_i : (seq (nth i I 0%nat) <= (Nmax - 1)%nat)%nat) by lia.
        pose proof (psi_ge_n_zero (seq (nth i I 0%nat)) (Nmax - 1)%nat Hle_i) as Hzero_i.
        rewrite Hzero_i; apply Cmul_0_l.
      - assert (Hle_j : (seq (nth j I 0%nat) <= (Nmax - 1)%nat)%nat) by lia.
        pose proof (psi_ge_n_zero (seq (nth j I 0%nat)) (Nmax - 1)%nat Hle_j) as Hzero_j.
        rewrite Hzero_j, Cconj_0, Cmul_0_r; reflexivity.
    }
    apply (Csum_trunc_tail
             (fun k => psi (seq (nth i I 0%nat)) k *c Cconj (psi (seq (nth j I 0%nat)) k))
             (Nmax - 1)%nat Nmax).
    - lia.
    - intros k [Hk1 Hk2].
      assert (k = (Nmax - 1)%nat) by lia.
      subst k; exact H_last_zero.
  }

  unfold vals.
  assert (Hvals_i : nth i (map seq I) 0%nat = seq (nth i I 0%nat)).
  { apply (H_nth_map nat nat seq I 0%nat 0%nat i Hi). }
  assert (Hvals_j : nth j (map seq I) 0%nat = seq (nth j I 0%nat)).
  { apply (H_nth_map nat nat seq I 0%nat 0%nat j Hj). }
  rewrite Hvals_i, Hvals_j.
  rewrite Htrunc_eq.
  unfold Nmax.
  rewrite <- Hvals_i, <- Hvals_j.
  apply decay_bound with (seq := seq) (I := I) (C := C); auto.
Qed.

(* 范数平方等于自身乘共轭的实部 *)
Lemma Cnorm_sq_eq_re_mul (z : Complex) : Cnorm_sq z = re (z *c Cconj z).
Proof.
  destruct z as [x y].
  unfold Cnorm_sq, re, Cmul, Cconj, Rsqr; simpl.
  ring.
Qed.

(* 累加和的加法分配律 *)
Lemma sum_f_R0_add (f g : nat -> R) (n : nat) :
  sum_f_R0 (fun i => f i + g i) n = sum_f_R0 f n + sum_f_R0 g n.
Proof.
  induction n as [| n IH].
  - simpl; ring.
  - simpl; rewrite IH; ring.
Qed.

(* 二维求和的方块分解 *)
Lemma sum_f_R0_double_S (a : nat -> nat -> R) (N : nat) :
  sum_f_R0 (fun i => sum_f_R0 (a i) (S N)) (S N) =
  sum_f_R0 (fun i => sum_f_R0 (a i) N) N
  + sum_f_R0 (fun i => a i (S N)) N
  + sum_f_R0 (fun j => a (S N) j) N
  + a (S N) (S N).
Proof.
  rewrite sum_f_R0_S.
  rewrite (sum_f_R0_ext (fun i => sum_f_R0 (a i) (S N))
                        (fun i => sum_f_R0 (a i) N + a i (S N)) N).
  - rewrite sum_f_R0_add.
    rewrite sum_f_R0_S with (f := a (S N)) (n := N).
    replace (sum_f_R0 (a (S N)) N) with (sum_f_R0 (fun j : nat => a (S N) j) N) by reflexivity.
    rewrite <- Rplus_assoc.
    reflexivity.
  - intros i Hi. apply sum_f_R0_S.
Qed.

(* 复数加法实部分配 *)
Lemma re_add : forall (z w : Complex), re (z +c w) = re z + re w.
Proof.
  intros [x1 y1] [x2 y2]; reflexivity.
Qed.

(* 部分和范数平方的展开式 *)
Lemma Cnorm_sq_csum : forall (f : nat -> Complex) (N : nat),
  Cnorm_sq (Csum f N) =
  match N with
  | 0 => 0%R
  | S n => sum_f_R0 (fun i => sum_f_R0 (fun j => re (f i *c Cconj (f j))) n) n
  end.
Proof.
  intros f [|N]; [simpl; rewrite Cnorm_sq_zero; reflexivity|].
  rename N into n.
  rewrite Cnorm_sq_eq_re_mul.
  rewrite (Cconj_Csum f (S n)).
  set (g := fun i : nat => Cconj (f i)).
  induction n as [|n IH].
  - rewrite (Csum_S f 0), (Csum_S g 0), !Csum_0.
    rewrite !Cadd_0_l.
    simpl; unfold g; reflexivity.
  - rewrite (Csum_S f (S n)), (Csum_S g (S n)).
    rewrite Cmul_add_distr_r, Cmul_add_distr_l.
    rewrite !re_add.
    rewrite IH.

    assert (re_Csum_mul_scal_rS : forall (h : nat -> Complex) (z : Complex) (M : nat),
      re (Csum h (S M) *c z) = sum_f_R0 (fun i => re (h i *c z)) M).
    { intros h z M; induction M as [|M IHm].
      - rewrite (Csum_S h 0), Csum_0, Cadd_0_l.
        simpl; ring.
      - rewrite (Csum_S h (S M)), Cmul_add_distr_r, re_add.
        rewrite IHm.
        rewrite sum_f_R0_S; ring. }

    assert (re_Csum_mul_scal_lS : forall (z : Complex) (h : nat -> Complex) (M : nat),
      re (z *c Csum h (S M)) = sum_f_R0 (fun i => re (z *c h i)) M).
    { intros z h M.
      rewrite Cmul_comm. 
      rewrite (re_Csum_mul_scal_rS h z M).
      apply sum_f_R0_ext; intros i _.
      rewrite Cmul_comm; reflexivity. }

    rewrite (re_Csum_mul_scal_rS f (g (S n)) n).
    rewrite (Cmul_add_distr_l (f (S n)) (Csum g (S n)) (g (S n))).
    rewrite re_add.
    rewrite (re_Csum_mul_scal_lS (f (S n)) g n).
    unfold g.
    rewrite (sum_f_R0_double_S (fun i j => re (f i *c Cconj (f j))) n).
    ring.
Qed.

(* 累加和次序交换 *)
Lemma sum_f_R0_swap (A B : nat) (h : nat -> nat -> R) :
  sum_f_R0 (fun i => sum_f_R0 (h i) B) A =
  sum_f_R0 (fun j => sum_f_R0 (fun i => h i j) A) B.
Proof.
  revert B h. induction A as [| A IH]; intros B h; simpl.
  - induction B as [| B IHB]; simpl; lra.
  - rewrite IH. induction B as [| B IHB]; simpl; lra.
Qed.

(* 复数零的实部为零 *)
Local Lemma re_C0 : re (C0 : Complex) = 0%R. Proof. reflexivity. Qed.

(* 复数乘法对加法的左分配律 *)
Local Lemma Cmul_add_distr_l : forall a b c : Complex,
  Cmul a (Cadd b c) = Cadd (Cmul a b) (Cmul a c).
Proof.
  intros a b c.
  destruct a as [a1 a2], b as [b1 b2], c as [c1 c2].
  unfold Cmul, Cadd; simpl.
  f_equal; ring.
Qed.

(* 部分和与标量乘法的实部展开 *)
Lemma re_Csum_scal_correct (z : Complex) (g : nat -> Complex) (M : nat) :
  re (z *c Csum g M) =
  match M with
  | 0 => 0%R
  | S m => sum_f_R0 (fun k => re (z *c g k)) m
  end.
Proof.
  induction M as [|M IH].
  - simpl; ring.
  - rewrite Csum_S.
    rewrite Cmul_add_distr_l.
    rewrite re_add.
    destruct M as [|m].
    + rewrite Csum_0.
      rewrite Cmul_0_r.
      unfold C0, re; simpl.
      ring.
    + replace (match S (S m) with
               | 0%nat => 0%R
               | S m0 => sum_f_R0 (fun k : nat => re (z *c g k)) m0
               end)
        with (sum_f_R0 (fun k : nat => re (z *c g k)) (S m))
        by reflexivity.
      rewrite IH.
      rewrite sum_f_R0_S.
      ring.
Qed.

(* 零常数有限和为零 *)
Lemma sum_f_R0_zero : forall N : nat, sum_f_R0 (fun _ : nat => 0) N = 0%R.
Proof.
  induction N; simpl; lra.
Qed.

(* 空列表缺省取值 *)
Lemma nth_nil : forall (A : Type) (d : A) (i : nat), nth i [] d = d.
Proof.
  intros A d i. induction i; simpl; reflexivity.
Qed.

(* 展开为二重求和 *)
Lemma l2_expand_double_sum :
  forall (coeffs : list Complex) (vals : list nat) (n M : nat)
    (Hlen : length coeffs = n)
    (Hlen_vals : length vals = n)
    (HMpos : (M > 0)%nat),
  let Fk k := Csum (fun i => nth i coeffs C0 *c psi (nth i vals 0%nat) k) n in
  l2_norm_sq Fk (M - 1) =
  sum_f_R0 (fun i => sum_f_R0 (fun j =>
      re (nth i coeffs C0 *c Cconj (nth j coeffs C0) *c
          (Csum (fun k => psi (nth i vals 0%nat) k *c Cconj (psi (nth j vals 0%nat) k)) M)))
      (n - 1)) (n - 1).
Proof.
  intros coeffs vals n M Hlen Hlen_vals HMpos Fk.
  unfold Fk, l2_norm_sq.
  set (c i := nth i coeffs C0).
  set (v i := nth i vals 0%nat).
  set (f i k := c i *c psi (v i) k).

  destruct n as [|n'].
  - assert (coeffs = []) by (destruct coeffs; [reflexivity | simpl in Hlen; lia]).
    assert (vals = []) by (destruct vals; [reflexivity | simpl in Hlen_vals; lia]).
    subst coeffs vals.
    simpl.
    rewrite Cnorm_sq_zero.
    assert (sum0 : forall N, sum_f_R0 (fun _ : nat => 0) N = 0).
    { induction N; simpl; lra. }
    rewrite sum0.
    rewrite ?Rmult_0_l, ?Rmult_0_r, ?Rminus_0_r, ?Rplus_0_l, ?Rplus_0_r.
    rewrite ?Rmult_0_l.
    rewrite Rminus_0_r.
    reflexivity.
  - rename n' into n.
    assert (H_cnorm_sq_raw : forall k, Cnorm_sq (Csum (fun i => f i k) (S n)) =
      sum_f_R0 (fun i => sum_f_R0 (fun j => re (f i k *c Cconj (f j k))) n) n).
    { intro k; rewrite Cnorm_sq_csum; reflexivity. }
    assert (H_cnorm_sq : forall k, Cnorm_sq (Csum (fun i => c i *c psi (v i) k) (S n)) =
      sum_f_R0 (fun i => sum_f_R0 (fun j => re (c i *c psi (v i) k *c Cconj (c j *c psi (v j) k))) n) n).
    { intro k; unfold f in H_cnorm_sq_raw; apply H_cnorm_sq_raw. }

    assert (H_left_eq : sum_f_R0 (fun k => Cnorm_sq (Csum (fun i => nth i coeffs C0 *c psi (nth i vals 0%nat) k) (S n))) (M - 1) =
      sum_f_R0 (fun k => sum_f_R0 (fun i => sum_f_R0 (fun j => re (nth i coeffs C0 *c psi (nth i vals 0%nat) k *c Cconj (nth j coeffs C0 *c psi (nth j vals 0%nat) k))) n) n) (M - 1)).
    { apply sum_f_R0_ext; intros k Hk.
      unfold c, v in H_cnorm_sq.
      rewrite H_cnorm_sq.
      reflexivity. }
    rewrite H_left_eq.

    replace (S n - 1)%nat with n by lia.

    assert (Hswap1 : sum_f_R0 (fun k : nat => sum_f_R0 (fun i : nat => sum_f_R0 (fun j : nat => re (nth i coeffs C0 *c psi (nth i vals 0%nat) k *c Cconj (nth j coeffs C0 *c psi (nth j vals 0%nat) k))) n) n) (M - 1) =
      sum_f_R0 (fun i : nat => sum_f_R0 (fun k : nat => sum_f_R0 (fun j : nat => re (nth i coeffs C0 *c psi (nth i vals 0%nat) k *c Cconj (nth j coeffs C0 *c psi (nth j vals 0%nat) k))) n) (M - 1)) n).
    { apply sum_f_R0_swap. }
    rewrite Hswap1.

    apply sum_f_R0_ext; intros i Hi.
    assert (Hswap_i : sum_f_R0 (fun k : nat => sum_f_R0 (fun j : nat => re (nth i coeffs C0 *c psi (nth i vals 0%nat) k *c Cconj (nth j coeffs C0 *c psi (nth j vals 0%nat) k))) n) (M - 1) =
      sum_f_R0 (fun j : nat => sum_f_R0 (fun k : nat => re (nth i coeffs C0 *c psi (nth i vals 0%nat) k *c Cconj (nth j coeffs C0 *c psi (nth j vals 0%nat) k))) (M - 1)) n).
    { apply sum_f_R0_swap. }
    rewrite Hswap_i.

    assert (Cconj_mult_eq : forall a b : Complex, Cconj (a *c b) = Cconj a *c Cconj b).
    { intros [x1 y1] [x2 y2]; unfold Cconj, Cmul; simpl; f_equal; ring. }

    assert (H_term_eq_complex : forall i j k,
      (nth i coeffs C0 *c psi (nth i vals 0%nat) k) *c Cconj (nth j coeffs C0 *c psi (nth j vals 0%nat) k) =
      (nth i coeffs C0 *c Cconj (nth j coeffs C0)) *c (psi (nth i vals 0%nat) k *c Cconj (psi (nth j vals 0%nat) k))).
    {
      intros i0 j k;
      destruct (nth i0 coeffs C0) as [a1 a2];
      destruct (psi (nth i0 vals 0%nat) k) as [b1 b2];
      destruct (nth j coeffs C0) as [c1 c2];
      destruct (psi (nth j vals 0%nat) k) as [d1 d2];
      unfold Cmul, Cconj; simpl; f_equal; ring.
    }

    assert (H_term_eq : forall i j k,
      re ((nth i coeffs C0 *c psi (nth i vals 0%nat) k) *c Cconj (nth j coeffs C0 *c psi (nth j vals 0%nat) k)) =
      re ((nth i coeffs C0 *c Cconj (nth j coeffs C0)) *c (psi (nth i vals 0%nat) k *c Cconj (psi (nth j vals 0%nat) k)))).
    { intros; apply f_equal, H_term_eq_complex. }

    apply sum_f_R0_ext; intros j Hj.
    destruct M as [|m]; [lia|].
    replace (S m - 1)%nat with m by lia.
    rewrite (re_Csum_scal_correct
              (nth i coeffs C0 *c Cconj (nth j coeffs C0))
              (fun k => psi (nth i vals 0%nat) k *c Cconj (psi (nth j vals 0%nat) k))
              (S m)).
    apply sum_f_R0_ext; intros k Hk.
    apply H_term_eq.
Qed.

(* 二范数平方的对角非对角分解 *)
Lemma l2_split_diag_off :
  forall (coeffs : list Complex) (n M : nat) (f : nat -> Complex)
    (inner : nat -> nat -> R)
    (Hdiag : forall i, inner i i = 1%R)
    (Hl2_sum : l2_norm_sq f (M - 1) = 
               sum_f_R0 (fun i => sum_f_R0 (fun j => 
                 re (nth i coeffs C0 *c Cconj (nth j coeffs C0) *c Cof_real (inner i j))) (n-1)) (n-1)),
  let diag := sum_f_R0 (fun i => Cnorm_sq (nth i coeffs C0)) (n-1) in
  let off := sum_f_R0 (fun i => sum_f_R0 (fun j => 
               if eq_nat_dec i j then 0%R 
               else re (nth i coeffs C0 *c Cconj (nth j coeffs C0) *c Cof_real (inner i j))) (n-1)) (n-1) in
  l2_norm_sq f (M - 1) = diag + off.
Proof.
  intros coeffs n M f inner Hdiag Hl2_sum.
  set (c i := nth i coeffs C0).
  set (a i j := re (c i *c Cconj (c j) *c Cof_real (inner i j))).

  assert (double_sum_diag_split : forall (m : nat) (a0 : nat -> nat -> R),
    sum_f_R0 (fun i => sum_f_R0 (fun j => a0 i j) m) m =
    sum_f_R0 (fun i => a0 i i) m +
    sum_f_R0 (fun i => sum_f_R0 (fun j => if eq_nat_dec i j then 0 else a0 i j) m) m).
  {
    induction m as [|m IH]; intros a0.
    - simpl; ring.
    - rewrite sum_f_R0_double_S.
      simpl (sum_f_R0 (fun i : nat => a0 i i) (S m)).
      rewrite sum_f_R0_double_S
        with (a := fun i j => if eq_nat_dec i j then 0 else a0 i j).
      assert (Hif_row : forall i, (i <= m)%nat ->
        (if eq_nat_dec i (S m) then 0 else a0 i (S m)) = a0 i (S m)).
      { intros i Hi; destruct (eq_nat_dec i (S m)); [lia|reflexivity]. }
      assert (Hif_col : forall j, (j <= m)%nat ->
        (if eq_nat_dec (S m) j then 0 else a0 (S m) j) = a0 (S m) j).
      { intros j Hj; destruct (eq_nat_dec (S m) j); [lia|reflexivity]. }
      assert (Hif_diag : (if eq_nat_dec (S m) (S m) then 0 else a0 (S m) (S m)) = 0%R).
      { destruct (eq_nat_dec (S m) (S m)); [reflexivity|lia]. }

      rewrite (sum_f_R0_ext
                (fun i => if eq_nat_dec i (S m) then 0 else a0 i (S m))
                (fun i => a0 i (S m)) m Hif_row).
      rewrite (sum_f_R0_ext
                (fun j => if eq_nat_dec (S m) j then 0 else a0 (S m) j)
                (fun j => a0 (S m) j) m Hif_col).
      rewrite Hif_diag, Rplus_0_r.
      rewrite IH.
      ring.
  }

  set (m := (n - 1)%nat).
  rewrite Hl2_sum.
  cbv beta.
  cbv zeta.
  pose proof (double_sum_diag_split m a) as Hsplit.
  unfold a, c, m in Hsplit.
  rewrite Hsplit.
  f_equal.
  apply sum_f_R0_ext; intros i Hi.
  rewrite Hdiag.
  replace (re (nth i coeffs C0 *c Cconj (nth i coeffs C0) *c Cof_real 1))
    with (Cnorm_sq (nth i coeffs C0)).
  { reflexivity. }
  rewrite Cnorm_sq_eq_re_mul.
  assert (H_mul1 : forall z : Complex, z *c Cof_real 1 = z).
  { intros [x y]; unfold Cmul, Cof_real; simpl; apply Complex_eq; simpl; ring. }
  rewrite H_mul1.
  reflexivity.
Qed.

(* 非对角项范数上界 *)
Lemma off_abs_bound :
  forall (coeffs : list Complex) (n : nat) (inner : nat -> nat -> R)
    (Hinner_pos : forall i j, 0 <= inner i j)
    (Hoff_abs : forall i j, i <> j -> Cnorm (nth i coeffs C0 *c Cconj (nth j coeffs C0) *c Cof_real (inner i j))
                            <= (Cnorm_sq (nth i coeffs C0) + Cnorm_sq (nth j coeffs C0)) / 2 * inner i j),
  let off := Csum (fun i => Csum (fun j => if eq_nat_dec i j then C0 else nth i coeffs C0 *c Cconj (nth j coeffs C0) *c Cof_real (inner i j)) (n-1)) (n-1) in
  Cnorm off <= sum_f_R0 (fun i => sum_f_R0 (fun j => if eq_nat_dec i j then 0 else (Cnorm_sq (nth i coeffs C0) + Cnorm_sq (nth j coeffs C0)) / 2 * inner i j) (n-1)) (n-1).
Proof.
  intros coeffs n inner Hinner_pos Hoff_abs off.
  assert (Cnorm_C0 : Cnorm C0 = 0%R).
  { unfold Cnorm, Cnorm_sq; simpl; rewrite Rsqr_0, Rplus_0_l; apply sqrt_0. }
  assert (Cnorm_ge_0 : forall z : Complex, 0 <= Cnorm z).
  { intro z; unfold Cnorm; apply sqrt_pos. }
  assert (Cnorm_Csum_S_triangle : forall (g : nat -> Complex) (p : nat),
    Cnorm (Csum g (S p)) <= sum_f_R0 (fun k => Cnorm (g k)) p).
  {
    intros g p. induction p as [|p IH].
    - rewrite Csum_S, Csum_0, Cadd_0_l; simpl sum_f_R0; apply Rle_refl.
    - rewrite Csum_S.
      apply Rle_trans with (Cnorm (Csum g (S p)) + Cnorm (g (S p))).
      + apply Cnorm_triang.
      + apply Rplus_le_compat; [apply IH | apply Rle_refl].
  }
  assert (Cnorm_Csum_triangle : forall (g : nat -> Complex) (m : nat),
    Cnorm (Csum g m) <= sum_f_R0 (fun k => Cnorm (g k)) m).
  {
    intros g m. destruct m as [|p].
    - rewrite Csum_0, Cnorm_C0; simpl; apply Cnorm_ge_0.
    - apply Rle_trans with (sum_f_R0 (fun k => Cnorm (g k)) p).
      + apply Cnorm_Csum_S_triangle.
      + simpl sum_f_R0. rewrite <- Rplus_0_r at 1.
        apply Rplus_le_compat_l. apply Cnorm_ge_0.
  }
  apply Rle_trans with (sum_f_R0 (fun i => sum_f_R0 (fun j => Cnorm (if eq_nat_dec i j then C0 else nth i coeffs C0 *c Cconj (nth j coeffs C0) *c Cof_real (inner i j))) (n-1)) (n-1)).
  - apply Rle_trans with (sum_f_R0 (fun i => Cnorm (Csum (fun j => if eq_nat_dec i j then C0 else nth i coeffs C0 *c Cconj (nth j coeffs C0) *c Cof_real (inner i j)) (n-1))) (n-1)).
    + apply Cnorm_Csum_triangle.
    + apply sum_f_R0_le_compat; intros i Hi; apply Cnorm_Csum_triangle.
  - apply sum_f_R0_le_compat; intros i Hi; apply sum_f_R0_le_compat; intros j Hj.
    destruct (eq_nat_dec i j) as [Heq | Hneq].
    + subst j; simpl; rewrite Cnorm_C0; apply Rle_refl.
    + apply Hoff_abs; exact Hneq.
Qed.

(* 非对角项总和的上界估计 *)
Lemma off_total_bound :
  forall (C : nat) (coeffs : list Complex) (n : nat) (inner : nat -> nat -> R),
    (C > 2)%nat ->
    (forall i j, inner i j = inner j i) ->
    (forall i, (i < n)%nat ->
       sum_f_R0 (fun j => if eq_nat_dec i j then 0 else inner i j) (n-1)%nat <= K (INR C)) ->
    let off := Csum (fun i => Csum (fun j => if eq_nat_dec i j then C0
      else nth i coeffs C0 *c Cconj (nth j coeffs C0) *c Cof_real (inner i j)) (n-1)%nat) (n-1)%nat in
    (Cnorm off <= sum_f_R0 (fun i => sum_f_R0 (fun j => if eq_nat_dec i j then 0
      else (Cnorm_sq (nth i coeffs C0) + Cnorm_sq (nth j coeffs C0)) / 2 * inner i j) (n-1)%nat) (n-1)%nat) ->
    Cnorm off <= K (INR C) * sum_f_R0 (fun i => Cnorm_sq (nth i coeffs C0)) (n-1)%nat.
Proof.
  intros C coeffs n inner HC Hinner_sym Hrow_sum off Hbound.
  assert (K_nonneg : 0 <= K (INR C)).
  { apply Rlt_le; apply K_pos; exact HC. }
  assert (Cnorm_sq_ge_0 : forall z : Complex, 0 <= Cnorm_sq z).
  { intro z; unfold Cnorm_sq; apply Rplus_le_le_0_compat; apply Rle_0_sqr. }
  set (a := fun i : nat => Cnorm_sq (nth i coeffs C0)).
  set (N := (n - 1)%nat).
  apply Rle_trans with
    (sum_f_R0 (fun i => sum_f_R0 (fun j => if eq_nat_dec i j then 0 else (a i + a j) / 2 * inner i j) N) N).
  - exact Hbound.
  - assert (H_double_eq :
      sum_f_R0 (fun i => sum_f_R0 (fun j => if eq_nat_dec i j then 0 else (a i + a j) / 2 * inner i j) N) N
      = sum_f_R0 (fun i => a i * sum_f_R0 (fun j => if eq_nat_dec i j then 0 else inner i j) N) N).
    {
      set (F1 i j := if eq_nat_dec i j then 0 else a i * inner i j).
      set (F2 i j := if eq_nat_dec i j then 0 else a j * inner i j).
      set (S1 := sum_f_R0 (fun i => sum_f_R0 (F1 i) N) N).
      set (S2 := sum_f_R0 (fun i => sum_f_R0 (F2 i) N) N).
      assert (Heq_ij : forall i j,
        (if eq_nat_dec i j then 0 else (a i + a j)/2 * inner i j)
        = 1/2 * F1 i j + 1/2 * F2 i j).
      {
        intros i j; unfold F1, F2; destruct (eq_nat_dec i j) as [Heq|Hneq];
        [ subst; simpl; ring
        | simpl; field; lra ].
      }
      assert (Hsum_split : sum_f_R0 (fun i => sum_f_R0 (fun j => if eq_nat_dec i j then 0 else (a i + a j)/2 * inner i j) N) N
        = 1/2 * S1 + 1/2 * S2).
      {
        rewrite (sum_f_R0_ext _ (fun i => sum_f_R0 (fun j => 1/2 * F1 i j + 1/2 * F2 i j) N) N).
        2: { intros i Hi; apply sum_f_R0_ext; intros j Hj; apply Heq_ij. }
        assert (Hinner_eq : forall i, sum_f_R0 (fun j : nat => 1/2 * F1 i j + 1/2 * F2 i j) N =
                                       1/2 * sum_f_R0 (F1 i) N + 1/2 * sum_f_R0 (F2 i) N).
        {
          intro i; rewrite sum_f_R0_add; rewrite !sum_f_R0_scal_l; reflexivity.
        }
        rewrite (sum_f_R0_ext _ (fun i => 1/2 * sum_f_R0 (F1 i) N + 1/2 * sum_f_R0 (F2 i) N) N).
        2: { intros i Hi; apply Hinner_eq. }
        rewrite sum_f_R0_add; rewrite !sum_f_R0_scal_l; reflexivity.
      }
      assert (H_F1_eq_F2 : S1 = S2).
      {
        unfold S1, S2, F1, F2.
        assert (Heq_swap : sum_f_R0 (fun i : nat => sum_f_R0 (fun j : nat => if eq_nat_dec i j then 0 else a j * inner i j) N) N
                          = sum_f_R0 (fun i : nat => sum_f_R0 (fun j : nat => if eq_nat_dec i j then 0 else a i * inner i j) N) N).
        {
          rewrite (sum_f_R0_swap N N (fun i j => if eq_nat_dec i j then 0 else a j * inner i j)).
          apply sum_f_R0_ext; intros i Hi.
          apply sum_f_R0_ext; intros j Hj.
          destruct (eq_nat_dec i j) as [Heq|Hneq].
          - subst j; destruct (eq_nat_dec i i) as [_|?]; [reflexivity | lia].
          - destruct (eq_nat_dec j i) as [Heq'|Hneq'].
            + exfalso; apply Hneq; symmetry; exact Heq'.
            + rewrite Hinner_sym; reflexivity.
        }
        symmetry; apply Heq_swap.
      }
      assert (H_S1_eq_target : S1 = sum_f_R0 (fun i => a i * sum_f_R0 (fun j => if eq_nat_dec i j then 0 else inner i j) N) N).
      {
        unfold S1, F1.
        apply sum_f_R0_ext; intros i Hi.
        assert (Heq_row : sum_f_R0 (fun j => if eq_nat_dec i j then 0 else a i * inner i j) N =
                          a i * sum_f_R0 (fun j => if eq_nat_dec i j then 0 else inner i j) N).
        {
          rewrite <- sum_f_R0_scal_l.
          apply sum_f_R0_ext; intros j Hj.
          destruct (eq_nat_dec i j); simpl; ring.
        }
        exact Heq_row.
      }
      rewrite Hsum_split.
      rewrite H_F1_eq_F2.
      replace (1/2 * S2 + 1/2 * S2) with S2 by lra.
      rewrite <- H_F1_eq_F2.
      exact H_S1_eq_target.
    }
    rewrite H_double_eq.
    apply Rle_trans with (sum_f_R0 (fun i => a i * K (INR C)) N).
    - apply sum_f_R0_le_compat; intros i Hi.
      assert (Ha_nonneg : 0 <= a i) by (apply Cnorm_sq_ge_0).
      apply Rmult_le_compat_l; [exact Ha_nonneg |].
      destruct n as [|n'].
      + unfold N in *; simpl in *.
        assert (Heq : i = 0%nat) by lia; subst i; simpl.
        apply K_nonneg.
      + apply Hrow_sum; unfold N in Hi; simpl in Hi; lia.
    - assert (Heq : sum_f_R0 (fun i => a i * K (INR C)) N = K (INR C) * sum_f_R0 a N).
      {
        rewrite <- (sum_f_R0_scal_l (K (INR C)) a N).
        apply sum_f_R0_ext; intros; apply Rmult_comm.
      }
      rewrite Heq; apply Rle_refl.
Qed.

(* 内积衰减上界 *)
Lemma inner_decay_bound :
  forall (seq : nat -> nat) (I : list nat) (C : nat)
    (Hc_ge2 : (C >= 2)%nat)
    (Hge2 : forall i, (seq i >= 2)%nat)
    (Hsparse : forall i, INR (seq (S i)) > INR C * INR (seq i))
    (Hdup : NoDup I) (Hsorted : Sorted Nat.lt I)
    (vals : list nat) (Hvals_eq : vals = map seq I)
    (maxIdx : nat) (HmaxIdx_eq : maxIdx = fold_right Init.Nat.max 0%nat I)
    (Hmax_bound : forall a, In a I -> (seq a <= seq maxIdx)%nat)
    (M : nat) (HM_eq : M = S (seq maxIdx))
    (i j : nat) (Hneq : i <> j) (Hi : (i < length I)%nat) (Hj : (j < length I)%nat),
  let inner_norm i j := Cnorm (Csum (fun k => psi (nth i vals 0%nat) k *c Cconj (psi (nth j vals 0%nat) k)) (M - 1)) in
  inner_norm i j <= 2 * / ((sqrt (INR C)) ^ (Z.abs_nat (Z.of_nat i - Z.of_nat j))).
Proof.
  intros seq I C Hc_ge2 Hge2 Hsparse Hdup Hsorted vals Hvals_eq maxIdx HmaxIdx_eq Hmax_bound M HM_eq i j Hneq Hi Hj.
  intro inner_norm.
  unfold inner_norm.
  rewrite HM_eq.
  replace (S (seq maxIdx) - 1)%nat with (seq maxIdx) by lia.
  pose proof (Hge2 maxIdx) as Hmax_ge2.
  assert (Hseq_strict_inc : forall a b, (a < b)%nat -> (seq a < seq b)%nat). {
    intros a0 b0 Hlt. eapply (seq_strict_growth_lt seq C a0 b0 Hc_ge2 Hsparse Hge2 Hlt).
  }
  pose proof (decay_bound seq I C Hc_ge2 Hge2 Hsparse Hdup Hsorted i j Hneq Hi Hj) as Hdec.
  simpl in Hdec.
  set (g := fun k : nat => psi (nth i vals 0%nat) k *c Cconj (psi (nth j vals 0%nat) k)).
  assert (Htrunc : Csum g (seq maxIdx) = Csum g (seq maxIdx - 1)). {
    destruct (seq maxIdx) as [|m] eqn:Hseqmax; [lia|].
    simpl (Csum g (S m)).
    replace (S m - 1)%nat with m by lia.
    assert (Hmax_in_I : In maxIdx I). {
      subst maxIdx. apply max_fold_right_in. destruct I; [simpl in Hi; lia | discriminate].
    }
    assert (Hmax_is_max : forall a, In a I -> (a <= maxIdx)%nat). {
      subst maxIdx; intros a Hin; apply fold_right_max_ge; exact Hin.
    }
    assert (H_i_or_j_lt_max : (nth i I 0%nat < maxIdx)%nat \/ (nth j I 0%nat < maxIdx)%nat). {
      destruct (Nat.lt_ge_cases (nth i I 0%nat) maxIdx) as [Hlt_i|Hge_i].
      - left; exact Hlt_i.
      - assert (Heq_i : nth i I 0%nat = maxIdx). {
          apply Nat.le_antisymm.
          - apply Hmax_is_max; apply nth_In; exact Hi.
          - exact Hge_i.
        }
        destruct (Nat.lt_ge_cases (nth j I 0%nat) maxIdx) as [Hlt_j|Hge_j].
        + right; exact Hlt_j.
        + exfalso.
          assert (Heq_j : nth j I 0%nat = maxIdx). {
            apply Nat.le_antisymm.
            - apply Hmax_is_max; apply nth_In; exact Hj.
            - exact Hge_j.
          }
          apply (NoDup_nth_neq_std I 0%nat i j Hdup Hi Hj Hneq).
          rewrite Heq_i, Heq_j; reflexivity.
    }
    assert (H_seq_i_or_j_lt_Sm : (seq (nth i I 0%nat) < S m)%nat \/ (seq (nth j I 0%nat) < S m)%nat). {
      destruct H_i_or_j_lt_max as [Hlt | Hlt].
      - left. apply Hseq_strict_inc in Hlt. rewrite Hseqmax in Hlt. exact Hlt.
      - right. apply Hseq_strict_inc in Hlt. rewrite Hseqmax in Hlt. exact Hlt.
    }
    assert (H_seq_i_or_j_le_m : (seq (nth i I 0%nat) <= m)%nat \/ (seq (nth j I 0%nat) <= m)%nat). {
      destruct H_seq_i_or_j_lt_Sm as [Hlt | Hlt]; [left|right]; lia.
    }
    assert (Hlast : g m = C0). {
      unfold g.
      rewrite Hvals_eq.
      pose proof (H_nth_map nat nat seq I 0%nat (0%nat : nat) i Hi) as Hni.
      pose proof (H_nth_map nat nat seq I 0%nat (0%nat : nat) j Hj) as Hnj.
      rewrite Hni, Hnj.
      destruct H_seq_i_or_j_le_m as [Hle | Hle].
      - rewrite (psi_ge_n_zero (seq (nth i I 0%nat)) m Hle). rewrite Cmul_0_l. reflexivity.
      - rewrite (psi_ge_n_zero (seq (nth j I 0%nat)) m Hle). rewrite Cconj_0. rewrite Cmul_0_r. reflexivity.
    }
    rewrite Hlast, Cadd_0_r. reflexivity.
  }
  rewrite Htrunc.
  replace (seq maxIdx) with (seq (fold_right Init.Nat.max 0%nat I)) by (rewrite HmaxIdx_eq; reflexivity).
  unfold g.
  rewrite Hvals_eq.
  exact Hdec.
Qed.

(* 范数平方的实数嵌入等于自身共轭积 *)
Lemma Cnorm_sq_Cof_real : forall z : Complex, Cof_real (Cnorm_sq z) = z *c Cconj z.
Proof.
  destruct z as [a b]; unfold Cof_real, Cnorm_sq, Cmul, Cconj; simpl.
  unfold Rsqr; f_equal; ring.
Qed.

(* 实数嵌入与有限求和的分配律 *)
Lemma Cof_real_sum : forall (f : nat -> R) (N : nat),
  Cof_real (sum_f_R0 f N) = Csum (fun i => Cof_real (f i)) (S N).
Proof.
  intros f N.
  induction N as [|N IH].
  - simpl.
    rewrite Cadd_comm.
    rewrite Cadd_0_r.
    reflexivity.
  - rewrite sum_f_R0_S.
    rewrite Cof_real_add.
    rewrite IH.
    simpl Csum at 1.
    reflexivity.
Qed.

(* 实数嵌入的加法保持 *)
Lemma Cof_real_add : forall a b : R, Cof_real (a + b) = Cof_real a +c Cof_real b.
Proof.
  intros a b; unfold Cof_real, Cadd; simpl; apply Complex_eq; simpl; ring.
Qed.

(* 几何级数倒数部分和的上界 *)
Lemma geom_series_reciprocal_bound_one :
  forall (r : R) (m : nat), r > 1 ->
  sum_f_R0 (fun k => / r ^ S k) m <= / (r - 1).
Proof.
  intros r m Hr.
  assert (Hr0 : 0 < r) by lra.
  set (q := / r).
  assert (Hq_pos : 0 < q) by (unfold q; apply Rinv_0_lt_compat; lra).
  assert (Hq_lt1 : q < 1).
  { unfold q.
    cut (/ r < / 1). { rewrite Rinv_1; tauto. }
    apply (Rinv_lt_contravar 1 r); lra. }
  assert (Hq_ne1 : q <> 1) by lra.
  assert (Hinv_pow : forall k, / (r ^ k) = (/ r) ^ k).
  { induction k as [|k IH]; simpl.
    - rewrite Rinv_1; reflexivity.
    - rewrite Rinv_mult.
      rewrite IH; reflexivity. }
  assert (Heq : forall k, / r ^ S k = q * q ^ k).
  { intros k; simpl (r ^ S k); unfold q.
    rewrite Rinv_mult.
    rewrite Hinv_pow; reflexivity. }
  rewrite (sum_f_R0_ext _ (fun k => q * q ^ k) m); [| intros; apply Heq].
  assert (Hsum_qk_eq : sum_f_R0 (fun k : nat => q * q ^ k) m =
                       q * sum_f_R0 (fun k => q ^ k) m).
  { apply sum_f_R0_scal_l. }
  rewrite Hsum_qk_eq.
  assert (Hgeo_sum : sum_f_R0 (fun k => q ^ k) m = (1 - q ^ S m) / (1 - q)).
  {
    clear Hsum_qk_eq.
    induction m as [|m' IH].
    - simpl; field; lra.
    - simpl sum_f_R0 at 1.
      rewrite IH.
      apply (Rmult_eq_reg_l (1 - q)); [| lra].
      rewrite (Rmult_plus_distr_l (1 - q) _ (q ^ S m')).
      replace ((1 - q) * ((1 - q ^ S m') / (1 - q))) with (1 - q ^ S m') by (field; lra).
      replace ((1 - q) * ((1 - q ^ S (S m')) / (1 - q))) with (1 - q ^ S (S m')) by (field; lra).
      simpl (q ^ S m'); simpl (q ^ S (S m')).
      ring.
  }
  rewrite Hgeo_sum.
  replace (q * ((1 - q ^ S m) / (1 - q))) with ((1 - q ^ S m) * (q / (1 - q)))
    by (unfold Rdiv; ring).
  replace (q / (1 - q)) with (1 / (r - 1)).
  2: { unfold q; field; lra. }
  rewrite Rmult_comm.
  assert (Hinv_nonneg : 0 <= 1 / (r - 1)).
  { apply Rmult_le_pos; [lra|]. apply Rlt_le, Rinv_0_lt_compat; lra. }
  assert (Hle_one : (1 - q ^ S m) <= 1).
  { assert (Hq_pow_nonneg : 0 <= q ^ S m) by (apply pow_le; lra); lra. }
  assert (Htemp : 1 / (r - 1) * (1 - q ^ S m) <= 1 / (r - 1) * 1).
  { apply (Rmult_le_compat_l (1 / (r - 1)) (1 - q ^ S m) 1 Hinv_nonneg Hle_one). }
  rewrite Rmult_1_r in Htemp.
  replace (/ (r - 1)) with (1 / (r - 1)).
  - exact Htemp.
  - field; lra.
Qed.

(* 自然数差的绝对值等于差 *)
Lemma abs_diff_eq_sub (i j : nat) (H : (j < i)%nat) :
  (Z.abs_nat (Z.of_nat i - Z.of_nat j) = (i - j))%nat.
Proof.
  apply Z_abs_nat_sub_small; lia.
Qed.

(* 等比数列绝对值求和拆分 *)
Lemma sum_dist_abs_eq (r : R) (n i : nat) (Hi_ge1 : (1 <= i)%nat) (Hi_lt_sn : (i + 1 < n)%nat) :
  sum_f_R0 (fun j => if eq_nat_dec i j then 0 else / (r ^ Z.abs_nat (Z.of_nat i - Z.of_nat j))) (n - 1)
  = sum_f_R0 (fun d => / r ^ S d) (i - 1) + sum_f_R0 (fun d => / r ^ S d) (n - 2 - i).
Proof.
  destruct i as [|i']; [lia|].
  set (i := S i') in *.
  assert (Hi_lt_n : (i < n)%nat) by lia.
  assert (Hi_le_n1 : (i <= n - 1)%nat) by lia.
  set (f := fun j : nat => if eq_nat_dec i j then 0 else / (r ^ Z.abs_nat (Z.of_nat i - Z.of_nat j))).

  pose proof (sum_f_R0_split f (n - 1) i Hi_le_n1) as Hsplit.
  assert (Heq_rem : Nat.eqb (n - 1 - i) 0 = false).
  { apply Nat.eqb_neq. lia. }
  rewrite Heq_rem in Hsplit.
  replace (n - 1 - i - 1)%nat with (n - 2 - i)%nat in Hsplit by lia.
  rewrite Hsplit. clear Hsplit.

  replace (i - 1)%nat with i' by lia.
  change (sum_f_R0 f i) with (sum_f_R0 f i' + f i).
  unfold f at 2.
  destruct (eq_nat_dec i i) as [_|?]; [|exfalso; auto].
  rewrite Rplus_0_r.

  f_equal.

  - (* left part: indices j < i *)
    assert (Heq1 : sum_f_R0 f i' = sum_f_R0 (fun j => / r ^ (i - j)%nat) i').
    { apply sum_f_R0_ext; intros j Hj.
      unfold f.
      destruct (eq_nat_dec i j) as [Heq|Hne].
      - exfalso. lia.
      - rewrite (Z_abs_nat_sub_small i j) by lia.
        reflexivity. }
    assert (Heq2 : sum_f_R0 (fun j => / r ^ (i - j)%nat) i' = sum_f_R0 (fun d => / r ^ S d) i').
    { rewrite (sum_f_R0_ext (fun j => / r ^ (i - j)%nat) (fun j => / r ^ S (i' - j)%nat) i').
      - rewrite (sum_f_R0_rev (fun d => / r ^ S d) i'). reflexivity.
      - intros j Hj.
        replace (i - j)%nat with (S (i' - j)%nat) by lia.
        reflexivity. }
    rewrite Heq1, Heq2. reflexivity.

  - (* right part: indices j > i *)
    apply sum_f_R0_ext; intros k Hk.
    unfold f.
    destruct (eq_nat_dec i (i + k + 1)%nat) as [Heq|Hne].
    + exfalso. lia.
    + replace (Z.of_nat i - Z.of_nat (i + k + 1))%Z with (- Z.of_nat (S k))%Z by lia.
      rewrite Zabs_nat_opp.
      rewrite Zabs_nat_Z_of_nat.
      reflexivity.
Qed.

(* 单侧距离几何衰减求和的上界 *)
Lemma sum_dist_geometric_bound_one (r : R) (n i : nat)
      (Hi_ge1 : (1 <= i)%nat) (Hi_lt_sn : (i + 1 < n)%nat) :
  r > 1 ->
  sum_f_R0 (fun j => if eq_nat_dec i j then 0
                    else / (r ^ Z.abs_nat (Z.of_nat i - Z.of_nat j))) (n - 1) <= 2 / (r - 1).
Proof.
  intros Hr.
  rewrite sum_dist_abs_eq; [ | exact Hi_ge1 | exact Hi_lt_sn ].
  apply Rle_trans with ((/ (r - 1)) + (/ (r - 1))).
  - apply Rplus_le_compat.
    + apply geom_series_reciprocal_bound_one; exact Hr.
    + apply geom_series_reciprocal_bound_one; exact Hr.
  - lra.
Qed.

(* 半衰减系数下的行和K界 *)
Lemma row_sum_bound_K_half :
  forall (n : nat) (vals : list nat) (M : nat) (C : nat)
    (Hvals_ge2 : forall v, In v vals -> (v >= 2)%nat)
    (Hlen : length vals = n)
    (Hdecay_half : forall i j, i <> j -> (i < n)%nat -> (j < n)%nat ->
      Cnorm (Csum (fun k => psi (nth i vals 0%nat) k *c Cconj (psi (nth j vals 0%nat) k)) (M - 1))
      <= (1/2) * / ((sqrt (INR C)) ^ (Z.abs_nat (Z.of_nat i - Z.of_nat j))))
    (HCgt2 : (C > 2)%nat),
  forall i, (i < n)%nat -> (1 <= i)%nat -> (i + 1 < n)%nat ->
    sum_f_R0 (fun j => if eq_nat_dec i j then 0 else
      Cnorm (Csum (fun k => psi (nth i vals 0%nat) k *c Cconj (psi (nth j vals 0%nat) k)) (M - 1))) (n - 1)
    <= K (INR C).
Proof.
  intros n vals M C Hvals_ge2 Hlen Hdecay_half HCgt2 i Hi Hi_ge1 Hi_lt_sn.
  set (r := sqrt (INR C)).
  assert (HC_gt_1 : INR C > 1). {
    apply Rlt_le_trans with (INR 2); [simpl; lra | apply le_INR; lia].
  }
  assert (Hr_gt1 : r > 1). {
    unfold r. rewrite <- sqrt_1.
    apply sqrt_lt_1; [lra | apply pos_INR; lia | exact HC_gt_1].
  }
  set (F j := if eq_nat_dec i j then 0
             else Cnorm (Csum (fun k => psi (nth i vals 0%nat) k *c Cconj (psi (nth j vals 0%nat) k)) (M - 1))).
  assert (H_F_bound : forall j, (j < n)%nat ->
    F j <= (if eq_nat_dec i j then 0 else (1/2) * / (r ^ Z.abs_nat (Z.of_nat i - Z.of_nat j)))).
  { intros j Hj; unfold F; destruct (eq_nat_dec i j); [apply Rle_refl |].
    apply Hdecay_half; auto. }
  apply Rle_trans with (sum_f_R0 (fun j => if eq_nat_dec i j then 0
                                         else (1/2) * / (r ^ Z.abs_nat (Z.of_nat i - Z.of_nat j))) (n - 1)).
  - apply sum_f_R0_le_compat; intros j Hj; apply H_F_bound; lia.
  - set (g j := if eq_nat_dec i j then 0 else / (r ^ Z.abs_nat (Z.of_nat i - Z.of_nat j))).
    assert (H_eq : sum_f_R0 (fun j => if eq_nat_dec i j then 0 else (1/2) * / (r ^ Z.abs_nat (Z.of_nat i - Z.of_nat j))) (n - 1)
                = (1/2) * sum_f_R0 g (n - 1)).
    {
      rewrite <- sum_f_R0_scal_l.
      apply sum_f_R0_ext; intros j Hj; unfold g; destruct (eq_nat_dec i j); ring.
    }
    rewrite H_eq.
    assert (Hsum_g_bound : sum_f_R0 g (n - 1) <= 2 / (r - 1)).
    { apply (sum_dist_geometric_bound_one r n i Hi_ge1 Hi_lt_sn Hr_gt1). }
    apply Rle_trans with (1/2 * (2 / (r - 1))).
    + apply Rmult_le_compat_l; [lra | exact Hsum_g_bound].
    + assert (Hcalc : 1/2 * (2 / (r - 1)) = / (r - 1)).
      { field; apply Rgt_not_eq; lra. }
      rewrite Hcalc.
      unfold K, r.
      rewrite <- (Rmult_1_l (/ (sqrt (INR C) - 1))).
      apply Rle_refl.
Qed.

(* 左侧部分和化简 *)
Lemma sum_left_part_eq (r : R) (i : nat) (Hi : (0 < i)%nat) :
  sum_f_R0 (fun j => if eq_nat_dec i j then 0 else / (r ^ (i - j))) (i - 1)%nat =
  sum_f_R0 (fun d => / r ^ S d) (i - 1)%nat.
Proof.
  assert (Hj_lt_i : forall j, (j <= i - 1)%nat -> j <> i) by (intros; lia).
  erewrite sum_f_R0_ext with (f := fun j => if eq_nat_dec i j then 0 else / (r ^ (i - j)))
                             (g := fun j => / (r ^ (i - j))).
  - erewrite sum_f_R0_ext with (f := fun j => / (r ^ (i - j)))
                               (g := fun j => / (r ^ S (i - 1 - j))).
    + set (a := fun d : nat => / r ^ S d).
      rewrite <- (sum_f_R0_rev a (i - 1)).
      unfold a; reflexivity.
    + intros j Hj.
      f_equal; f_equal.
      lia.
  - intros j Hj.
    destruct (eq_nat_dec i j) as [Heq | Hne].
    + exfalso. apply (Hj_lt_i j Hj); auto.
    + reflexivity.
Qed.

(* 距离绝对值的求和拆分通用公式 *)
Lemma sum_dist_abs_eq_general (r : R) (n i : nat) (Hin : (i < n)%nat) :
  sum_f_R0 (fun j => if eq_nat_dec i j then 0 else / (r ^ Z.abs_nat (Z.of_nat i - Z.of_nat j))) (n - 1)%nat
  = (if (i =? 0)%nat then 0 else sum_f_R0 (fun d => / r ^ S d) (i - 1)%nat)
    + (if ((n - 1 - i) =? 0)%nat then 0 else sum_f_R0 (fun d => / r ^ S d) (n - 1 - i - 1)%nat).
Proof.
  set (f := fun j => if eq_nat_dec i j then 0 else / (r ^ Z.abs_nat (Z.of_nat i - Z.of_nat j))).
  assert (Hle : (i <= n - 1)%nat) by lia.
  rewrite (sum_f_R0_split f (n - 1)%nat i Hle).

  assert (Hfront : sum_f_R0 f i =
    (if (i =? 0)%nat then 0 else sum_f_R0 (fun d => / r ^ S d) (i - 1)%nat)).
  {
    destruct (Nat.eq_dec i 0) as [Hi0|Hi0].
    - subst i; simpl; reflexivity.
    - destruct i as [|i'].
      + exfalso; apply Hi0; reflexivity.
      + rewrite (sum_f_R0_S f i').
        assert (Hfi' : f (S i') = 0%R).
        { unfold f; destruct (eq_nat_dec (S i') (S i')) as [_|]; [reflexivity|lia]. }
        rewrite Hfi', Rplus_0_r.
        assert (Hsum_eq : sum_f_R0 f i' = sum_f_R0 (fun d => / r ^ S d) i').
        {
          etransitivity.
          - apply sum_f_R0_ext; intros j Hj.
            assert (Hj_lt_Si' : (j < S i')%nat) by lia.
            unfold f.
            destruct (eq_nat_dec (S i') j) as [Heq|_]; [lia|].
            rewrite (abs_diff_eq_sub (S i') j Hj_lt_Si').
            reflexivity.
          - assert (Htemp : sum_f_R0 (fun j => / r ^ (S i' - j)) i' =
                            sum_f_R0 (fun d => / r ^ S d) i').
            {
              rewrite (sum_f_R0_ext (fun j => / r ^ (S i' - j))
                                   (fun j => / r ^ S (i' - j)) i').
              - rewrite (sum_f_R0_rev (fun d => / r ^ S d) i').
                reflexivity.
              - intros j Hj.
                replace (S i' - j)%nat with (S (i' - j))%nat by lia.
                reflexivity.
            }
            apply Htemp.
        }
        rewrite Hsum_eq.
        replace (S i' - 1)%nat with i' by lia.
        case (Nat.eqb_spec (S i') 0) as [Heq0|Heq0].
        -- exfalso; apply Hi0; assumption.
        -- reflexivity.
  }

  assert (Hback : (if Nat.eqb (n - 1 - i) 0
                   then 0
                   else sum_f_R0 (fun k : nat => f (i + k + 1)%nat) (n - 1 - i - 1)%nat)
    = (if ((n - 1 - i) =? 0)%nat then 0 else sum_f_R0 (fun d => / r ^ S d) (n - 1 - i - 1)%nat)).
  {
    destruct (Nat.eq_dec (n - 1 - i) 0) as [Heq0|Hneq0].
    - assert (Heqb0 : Nat.eqb (n - 1 - i) 0 = true) by (apply Nat.eqb_eq; assumption).
      rewrite Heqb0. simpl; reflexivity.
    - assert (Heqbf : Nat.eqb (n - 1 - i) 0 = false) by (apply Nat.eqb_neq; assumption).
      rewrite Heqbf.
      apply sum_f_R0_ext; intros k Hk.
      unfold f.
      destruct (eq_nat_dec i (i + k + 1)%nat) as [Hi_eq|_]; [lia|].
      (* 安全化简绝对值表达式 *)
      assert (Habs : Z.abs_nat (Z.of_nat i - Z.of_nat (i + k + 1)) = S k).
      {
        replace (Z.of_nat i - Z.of_nat (i + k + 1))%Z
          with (-(Z.of_nat (i + k + 1) - Z.of_nat i))%Z by ring.
        rewrite Zabs_nat_opp.
        rewrite Z_abs_nat_sub_small; [|lia].
        replace ((i + k + 1) - i)%nat with (S k) by lia.
        reflexivity.
      }
      rewrite Habs; reflexivity.
  }

  rewrite Hfront, Hback.
  reflexivity.
Qed.

(* 单项分裂求和的二倍倒数上界 *)
Lemma split_sum_geometric_bound_one (r : R) (Hr_gt1 : r > 1) (i n : nat) (F : nat -> R) :
  (i+1 < n)%nat ->
  (F i = 0%R) ->
  (forall j, (j < n)%nat -> j <> i ->
      F j <= / (r ^ Z.abs_nat (Z.of_nat i - Z.of_nat j))) ->
  sum_f_R0 F (n - 1) <= 2 / (r - 1).
Proof.
  intros Hi1 Fi0 HdecayF.
  assert (Hi : (i < n)%nat) by lia.
  set (G := fun j : nat => if eq_nat_dec i j then 0%R
                           else / (r ^ Z.abs_nat (Z.of_nat i - Z.of_nat j))).
  assert (Hle : forall j, (j < n)%nat -> F j <= G j).
  { intros j Hj; unfold G; destruct (eq_nat_dec i j) as [Heq|Hne].
    - subst; rewrite Fi0; apply Rle_refl.
    - apply HdecayF; auto. }
  assert (Hsum_le : sum_f_R0 F (n - 1) <= sum_f_R0 G (n - 1)).
  { apply sum_f_R0_le_compat; intros j Hj; apply Hle; lia. }

  assert (Hle_i : (i <= n - 1)%nat) by lia.
  pose proof (sum_f_R0_split G (n - 1) i Hle_i) as Hsplit.

  case_eq (Nat.eqb (n - 1 - i) 0).

  - (* 右半部分长度为 0 *)
    intros Heq0.
    rewrite Heq0 in Hsplit; simpl in Hsplit.
    assert (Hleft : sum_f_R0 G i <= / (r - 1)).
    { destruct (Nat.eq_dec i 0) as [Hi0|Hi0].
      - subst i; simpl; unfold G; simpl; apply Rlt_le; apply Rinv_0_lt_compat; lra.
      - assert (Hi_pos : (0 < i)%nat) by lia.
        assert (HGi0 : G i = 0).
        { unfold G; destruct (eq_nat_dec i i); [reflexivity | lia]. }
        assert (Hi_eq : i = S (i - 1)) by lia.
        rewrite Hi_eq at 1; rewrite sum_f_R0_S.
        rewrite <- Hi_eq; rewrite HGi0, Rplus_0_r.
        assert (Heq_Gi : sum_f_R0 G (i-1) = sum_f_R0 (fun d => / r ^ S d) (i-1)).
        {
          assert (Htemp1 : sum_f_R0 G (i-1) = sum_f_R0 (fun j => / (r ^ (i - j))) (i-1)).
          { eapply sum_f_R0_ext; intros j Hj.
            unfold G; destruct (eq_nat_dec i j) as [Heq|Hne'].
            - exfalso; assert (j <= i-1)%nat by lia; rewrite Heq in Hj; lia.
            - replace (Z.abs_nat (Z.of_nat i - Z.of_nat j)) with (i - j)%nat.
              + reflexivity.
              + symmetry; apply abs_diff_eq_sub; lia. }
          assert (Htemp2 : sum_f_R0 (fun j : nat => / (r ^ (i - j))) (i-1)
                          = sum_f_R0 (fun d : nat => / r ^ S d) (i-1)).
          {
            etransitivity.
            - apply (sum_f_R0_ext (fun j => / r ^ (i - j))
                                  (fun j => / r ^ S (i - 1 - j)) (i-1)).
              intros k Hk.
              replace (i - k)%nat with (S (i - 1 - k))%nat by lia.
              reflexivity.
            - apply (sum_f_R0_rev (fun d : nat => / r ^ S d) (i-1)).
          }
          rewrite Htemp1, Htemp2; reflexivity. }
        rewrite Heq_Gi; apply geom_series_reciprocal_bound_one; auto. }
    eapply Rle_trans; [apply Hsum_le|].
    rewrite Hsplit.
    replace (2 / (r - 1)) with (/ (r - 1) + / (r - 1)).
    - apply Rplus_le_compat; [exact Hleft |]. 
      apply Rlt_le; apply Rinv_0_lt_compat; lra.
    - field; lra.
    
  - (* 右半部分长度非零 *)
    intros Heq0.
    rewrite Heq0 in Hsplit.
    set (m := (n - 1 - i - 1)%nat) in *.
    assert (Hm_eq : m = (n - i - 2)%nat) by lia.
    rewrite Hm_eq in Hsplit.
    assert (Hleft : sum_f_R0 G i <= / (r - 1)).
    { destruct (Nat.eq_dec i 0) as [Hi0|Hi0].
      - subst i; simpl; unfold G; simpl; apply Rlt_le; apply Rinv_0_lt_compat; lra.
      - assert (Hi_pos : (0 < i)%nat) by lia.
        assert (HGi0 : G i = 0).
        { unfold G; destruct (eq_nat_dec i i); [reflexivity | lia]. }
        assert (Hi_eq : i = S (i - 1)) by lia.
        rewrite Hi_eq at 1; rewrite sum_f_R0_S.
        rewrite <- Hi_eq; rewrite HGi0, Rplus_0_r.
        assert (Heq_Gi : sum_f_R0 G (i-1) = sum_f_R0 (fun d => / r ^ S d) (i-1)).
        {
          assert (Htemp1 : sum_f_R0 G (i-1) = sum_f_R0 (fun j => / (r ^ (i - j))) (i-1)).
          { eapply sum_f_R0_ext; intros j Hj.
            unfold G; destruct (eq_nat_dec i j) as [Heq|Hne'].
            - exfalso; assert (j <= i-1)%nat by lia; rewrite Heq in Hj; lia.
            - replace (Z.abs_nat (Z.of_nat i - Z.of_nat j)) with (i - j)%nat.
              + reflexivity.
              + symmetry; apply abs_diff_eq_sub; lia. }
          assert (Htemp2 : sum_f_R0 (fun j : nat => / (r ^ (i - j))) (i-1)
                          = sum_f_R0 (fun d : nat => / r ^ S d) (i-1)).
          {
            etransitivity.
            - apply (sum_f_R0_ext (fun j => / r ^ (i - j))
                                  (fun j => / r ^ S (i - 1 - j)) (i-1)).
              intros k Hk.
              replace (i - k)%nat with (S (i - 1 - k))%nat by lia.
              reflexivity.
            - apply (sum_f_R0_rev (fun d : nat => / r ^ S d) (i-1)).
          }
          rewrite Htemp1, Htemp2; reflexivity. }
        rewrite Heq_Gi; apply geom_series_reciprocal_bound_one; auto. }

    assert (Hright : sum_f_R0 (fun k : nat => G (i + k + 1)%nat) (n - i - 2) <= / (r - 1)).
    { assert (Heq : sum_f_R0 (fun k : nat => G (i + k + 1)%nat) (n - i - 2) =
                    sum_f_R0 (fun k : nat => / r ^ S k) (n - i - 2)).
      { apply sum_f_R0_ext; intros k Hk.
        unfold G; destruct (eq_nat_dec i (i + k + 1)%nat) as [Heq'|_]; [lia|].
        assert (Habs_eq : Z.abs_nat (Z.of_nat i - Z.of_nat (i + k + 1)) = S k).
        {
          replace (Z.of_nat i - Z.of_nat (i + k + 1))%Z
            with (- (Z.of_nat (i + k + 1) - Z.of_nat i))%Z by lia.
          rewrite Zabs_nat_opp.
          rewrite (Z_abs_nat_sub_small (i + k + 1) i) by lia.
          replace ((i + k + 1) - i)%nat with (S k) by lia.
          reflexivity.
        }
        rewrite Habs_eq.
        reflexivity. }
      rewrite Heq; apply geom_series_reciprocal_bound_one; auto. }

    eapply Rle_trans; [apply Hsum_le|].
    rewrite Hsplit.
    replace (2 / (r - 1)) with (/ (r - 1) + / (r - 1)).
    - apply Rplus_le_compat; [exact Hleft | exact Hright].
    - field; lra.
Qed.

(* 末尾行求和上界 —— 当右侧无空间时退化为单尾衰减和 *)
Lemma row_sum_bound_when_i_last_one (r : R) (i n : nat) (F : nat -> R) (Hr_gt1 : r > 1) :
  (i < n)%nat -> (n <= i+1)%nat ->
  F i = 0%R ->
  (forall j, (j < n)%nat -> j <> i -> F j <= / (r ^ Z.abs_nat (Z.of_nat i - Z.of_nat j))) ->
  sum_f_R0 F (n - 1) <= / (r - 1).
Proof.
  intros Hi Hn Fi0 Hdecay.
  assert (Hn_eq : (n = i + 1)%nat) by lia.
  rewrite Hn_eq in *.
  replace ((i + 1) - 1)%nat with i by lia.
  destruct (Nat.eq_dec i 0) as [Hi0 | Hi_pos].
  - subst i; simpl; rewrite Fi0.
    apply Rlt_le; apply Rinv_0_lt_compat; lra.
  - assert (Hi_pos' : (0 < i)%nat) by lia.
    replace i with (S (i - 1))%nat by lia.
    rewrite (sum_f_R0_S F (i-1)).
    replace (S (i - 1))%nat with i by lia.
    rewrite Fi0, Rplus_0_r.
    apply Rle_trans with
      (sum_f_R0 (fun j : nat => if eq_nat_dec i j then 0%R
                                 else / (r ^ (i - j))) (i - 1)).
    + apply sum_f_R0_le_compat; intros j Hj.
      assert (Hj_lt_n : (j < i+1)%nat) by lia.
      destruct (eq_nat_dec i j) as [Heq|Hne].
      * subst j; rewrite Fi0; apply Rle_refl.
      * assert (Hj_lt_i : (j < i)%nat) by lia.
        assert (Hne' : j <> i) by (intro H; apply Hne; symmetry; exact H).
        apply Rle_trans with (/ r ^ Z.abs_nat (Z.of_nat i - Z.of_nat j)).
        -- apply Hdecay; [exact Hj_lt_n | exact Hne'].
        -- rewrite (abs_diff_eq_sub i j Hj_lt_i); apply Rle_refl.
    + rewrite (sum_left_part_eq r i Hi_pos').
      apply geom_series_reciprocal_bound_one; exact Hr_gt1.
Qed.

(* 定理：衰减系数下的行和K界 *)
Theorem row_sum_bound_K :
  forall (n : nat) (vals : list nat) (M : nat) (C : nat)
    (Hvals_ge2 : forall v, In v vals -> (v >= 2)%nat)
    (Hlen : length vals = n)
    (Hdecay : forall i j, i <> j -> (i < n)%nat -> (j < n)%nat ->
      Cnorm (Csum (fun k => psi (nth i vals 0%nat) k *c Cconj (psi (nth j vals 0%nat) k)) (M - 1))
      <= / ((sqrt (INR C)) ^ (Z.abs_nat (Z.of_nat i - Z.of_nat j))))
    (HCgt2 : (C > 2)%nat),
  forall i, (i < n)%nat ->
    sum_f_R0 (fun j => if eq_nat_dec i j then 0 else
      Cnorm (Csum (fun k => psi (nth i vals 0%nat) k *c Cconj (psi (nth j vals 0%nat) k)) (M - 1))) (n - 1)
    <= 2 * K (INR C).
Proof.
  intros n vals M C Hvals_ge2 Hlen Hdecay HCgt2 i Hi.
  set (r := sqrt (INR C)).
  assert (Hr_gt1 : r > 1). {
    unfold r; rewrite <- sqrt_1.
    apply sqrt_lt_1.
    - lra.
    - apply Rlt_le; apply lt_0_INR; lia.
    - change 1 with (INR 1); apply lt_INR; lia.
  }
  assert (Hr_gt1' : r - 1 > 0) by lra.
  set (F j := if eq_nat_dec i j then 0
             else Cnorm (Csum (fun k => psi (nth i vals 0%nat) k *c Cconj (psi (nth j vals 0%nat) k)) (M - 1))).
  assert (H_F_bound : forall j, (j < n)%nat -> F j <= / (r ^ Z.abs_nat (Z.of_nat i - Z.of_nat j))).
  { intros j Hj; unfold F.
    destruct (eq_nat_dec i j) as [Heq | Hneq].
    - subst j; rewrite Z.sub_diag; simpl Z.abs_nat; rewrite pow_O, Rinv_1; apply Rle_0_1.
    - apply Hdecay; assumption. }
  assert (H_K_eq : 2 * K (INR C) = 2 / (r - 1)). {
    unfold K, r; field; apply Rgt_not_eq; exact Hr_gt1'.
  }
  rewrite H_K_eq.
  set (G j := if eq_nat_dec i j then 0 else / (r ^ Z.abs_nat (Z.of_nat i - Z.of_nat j))).
  assert (H_F_le_G : forall j, (j <= n - 1)%nat -> F j <= G j). {
    intros j Hj.
    unfold G.
    destruct (eq_nat_dec i j) as [Heq' | Hneq'].
    - subst j; unfold F; simpl.
      destruct (eq_nat_dec i i); [apply Rle_refl | contradiction].
    - apply H_F_bound; lia.
  }
  apply Rle_trans with (sum_f_R0 G (n - 1)).
  - apply sum_f_R0_le_compat; intros j Hj; apply H_F_le_G; assumption.
  - destruct (Nat.lt_ge_cases (i+1) n) as [Hi1 | Hi1].
    + (* i+1 < n *)
      apply (split_sum_geometric_bound_one r Hr_gt1 i n G).
      * exact Hi1.
      * unfold G; simpl; destruct (eq_nat_dec i i); [reflexivity | lia].
      * intros j Hj Hneq. unfold G. destruct (eq_nat_dec i j) as [Heq'|Hneq2].
        -- exfalso; apply Hneq; symmetry; exact Heq'.
        -- reflexivity.
    + (* n <= i+1 *)
      apply Rle_trans with (/ (r - 1)).
      * apply (row_sum_bound_when_i_last_one r i n G Hr_gt1).
        -- exact Hi.
        -- exact Hi1.
        -- unfold G; simpl; destruct (eq_nat_dec i i); [reflexivity | lia].
        -- intros j Hj Hneq. unfold G. destruct (eq_nat_dec i j) as [Heq'|Hneq2].
           ++ exfalso; apply Hneq; symmetry; exact Heq'.
           ++ reflexivity.
      * assert (H_12 : 1 <= 2) by lra.
        apply Rmult_le_compat_r with (r := / (r - 1)) in H_12;
          [| apply Rlt_le, Rinv_0_lt_compat; lra].
        rewrite Rmult_1_l in H_12; exact H_12.
Qed.

(* 双重对角求和的拆分 *)
Lemma double_sum_diag_split (n : nat) (a : nat -> nat -> R) :
  sum_f_R0 (fun i => sum_f_R0 (a i) n) n =
  sum_f_R0 (fun i => a i i) n +
  sum_f_R0 (fun i => sum_f_R0 (fun j => if eq_nat_dec i j then 0 else a i j) n) n.
Proof.
  induction n as [|n IH].
  - simpl; ring.
  - rewrite (sum_f_R0_double_S a n).
    rewrite (sum_f_R0_double_S (fun i j => if eq_nat_dec i j then 0 else a i j) n).
    replace (if eq_nat_dec (S n) (S n) then 0 else a (S n) (S n)) with 0%R
      by (destruct (eq_nat_dec (S n) (S n)); [reflexivity | exfalso; auto]).
    assert (H_col : sum_f_R0 (fun j => if eq_nat_dec (S n) j then 0 else a (S n) j) n =
                   sum_f_R0 (a (S n)) n).
    { apply sum_f_R0_ext; intros j Hj;
      destruct (eq_nat_dec (S n) j); try (exfalso; lia); reflexivity. }
    rewrite H_col.
    assert (H_row : sum_f_R0 (fun i => if eq_nat_dec i (S n) then 0 else a i (S n)) n =
                   sum_f_R0 (fun i => a i (S n)) n).
    { apply sum_f_R0_ext; intros i Hi;
      destruct (eq_nat_dec i (S n)); try (exfalso; lia); reflexivity. }
    rewrite H_row.
    rewrite IH.
    rewrite (sum_f_R0_S (fun i => a i i) n).
    set (S1 := sum_f_R0 (fun i => a i i) n).
    set (S2 := sum_f_R0 (fun i => sum_f_R0 (fun j => if eq_nat_dec i j then 0 else a i j) n) n).
    set (S3 := sum_f_R0 (fun i => a i (S n)) n).
    set (S4 := sum_f_R0 (fun j => a (S n) j) n).
    set (S5 := a (S n) (S n)).
    ring.
Qed.

(* 非对角项总范数的全局上界 *)
Lemma off_total_bound_4 :
  forall (C : nat) (coeffs : list Complex) (n : nat) (inner : nat -> nat -> R),
    (C > 2)%nat ->
    (forall i j, inner i j = inner j i) ->
    (forall i, (i < n)%nat ->
       sum_f_R0 (fun j => if eq_nat_dec i j then 0 else inner i j) (n-1)%nat <= 4 * K (INR C)) ->
    let off := Csum (fun i => Csum (fun j => if eq_nat_dec i j then C0 else nth i coeffs C0 *c Cconj (nth j coeffs C0) *c Cof_real (inner i j)) (n-1)) (n-1) in
    (Cnorm off <= sum_f_R0 (fun i => sum_f_R0 (fun j => if eq_nat_dec i j then 0 else (Cnorm_sq (nth i coeffs C0) + Cnorm_sq (nth j coeffs C0)) / 2 * inner i j) (n-1)) (n-1)) ->
    Cnorm off <= 4 * K (INR C) * sum_f_R0 (fun i => Cnorm_sq (nth i coeffs C0)) (n-1)%nat.
Proof.
  intros C coeffs n inner HC Hinner_sym Hrow_sum off Hbound.
  assert (K_nonneg : 0 <= K (INR C)) by (apply Rlt_le, K_pos; lia).
  assert (Cnorm_sq_ge_0 : forall z : Complex, 0 <= Cnorm_sq z) by (apply Cnorm_sq_ge_0).
  set (a i := Cnorm_sq (nth i coeffs C0)).
  set (N := (n - 1)%nat).
  apply Rle_trans with
    (sum_f_R0 (fun i => sum_f_R0 (fun j => if eq_nat_dec i j then 0 else (a i + a j) / 2 * inner i j) N) N).
  - exact Hbound.
  - assert (H_double_eq :
      sum_f_R0 (fun i => sum_f_R0 (fun j => if eq_nat_dec i j then 0 else (a i + a j) / 2 * inner i j) N) N
      = sum_f_R0 (fun i => a i * sum_f_R0 (fun j => if eq_nat_dec i j then 0 else inner i j) N) N).
    {
      set (F1 i j := if eq_nat_dec i j then 0 else a i * inner i j).
      set (F2 i j := if eq_nat_dec i j then 0 else a j * inner i j).
      set (S1 := sum_f_R0 (fun i => sum_f_R0 (F1 i) N) N).
      set (S2 := sum_f_R0 (fun i => sum_f_R0 (F2 i) N) N).
      assert (Heq_ij : forall i j,
        (if eq_nat_dec i j then 0 else (a i + a j)/2 * inner i j)
        = 1/2 * F1 i j + 1/2 * F2 i j).
      {
        intros i j; unfold F1, F2; destruct (eq_nat_dec i j) as [Heq|Hneq];
        [ subst; simpl; ring
        | simpl; field; lra ].
      }
      assert (Hsum_split : sum_f_R0 (fun i => sum_f_R0 (fun j => if eq_nat_dec i j then 0 else (a i + a j)/2 * inner i j) N) N
        = 1/2 * S1 + 1/2 * S2).
      {
        rewrite (sum_f_R0_ext _ (fun i => sum_f_R0 (fun j => 1/2 * F1 i j + 1/2 * F2 i j) N) N).
        2: { intros i Hi; apply sum_f_R0_ext; intros j Hj; apply Heq_ij. }
        assert (Hinner_eq : forall i, sum_f_R0 (fun j : nat => 1/2 * F1 i j + 1/2 * F2 i j) N =
                                       1/2 * sum_f_R0 (F1 i) N + 1/2 * sum_f_R0 (F2 i) N).
        {
          intro i; rewrite sum_f_R0_add; rewrite !sum_f_R0_scal_l; reflexivity.
        }
        rewrite (sum_f_R0_ext _ (fun i => 1/2 * sum_f_R0 (F1 i) N + 1/2 * sum_f_R0 (F2 i) N) N).
        2: { intros i Hi; apply Hinner_eq. }
        rewrite sum_f_R0_add; rewrite !sum_f_R0_scal_l; reflexivity.
      }
      assert (H_F1_eq_F2 : S1 = S2).
      {
        unfold S1, S2, F1, F2.
        rewrite (sum_f_R0_swap N N (fun i j => if eq_nat_dec i j then 0 else a j * inner i j)).
        apply sum_f_R0_ext; intros i Hi.
        apply sum_f_R0_ext; intros j Hj.
        destruct (eq_nat_dec i j) as [Heq|Hneq].
        - subst j; destruct (eq_nat_dec i i) as [_|?]; [reflexivity | lia].
        - destruct (eq_nat_dec j i) as [Heq'|Hneq'].
          + exfalso; apply Hneq; symmetry; exact Heq'.
          + rewrite Hinner_sym; reflexivity.
      }
      assert (H_S1_eq_target : S1 = sum_f_R0 (fun i => a i * sum_f_R0 (fun j => if eq_nat_dec i j then 0 else inner i j) N) N).
      {
        unfold S1, F1.
        apply sum_f_R0_ext; intros i Hi.
        assert (Heq_row : sum_f_R0 (fun j => if eq_nat_dec i j then 0 else a i * inner i j) N =
                          a i * sum_f_R0 (fun j => if eq_nat_dec i j then 0 else inner i j) N).
        {
          rewrite <- sum_f_R0_scal_l.
          apply sum_f_R0_ext; intros j Hj.
          destruct (eq_nat_dec i j); simpl; ring.
        }
        exact Heq_row.
      }
      rewrite Hsum_split.
      rewrite H_F1_eq_F2.
      replace (1/2 * S2 + 1/2 * S2) with S2 by lra.
      rewrite <- H_F1_eq_F2.
      exact H_S1_eq_target.
    }
    rewrite H_double_eq.
    apply Rle_trans with (sum_f_R0 (fun i => a i * (4 * K (INR C))) N).
    - apply sum_f_R0_le_compat; intros i Hi.
      assert (Ha_nonneg : 0 <= a i) by (apply Cnorm_sq_ge_0).
      apply Rmult_le_compat_l; [exact Ha_nonneg |].
      (* 修改开始 *)
      unfold N in Hi.
      destruct n as [|n'].
      + (* n = 0 *)
        assert (Hi0 : i = 0%nat) by lia; subst i.
        simpl.
        apply Rle_trans with 0; [simpl; lra |].
        apply Rmult_le_pos; [lra | apply K_nonneg].
      + (* n = S n' *)
        assert (H_lt : (i < S n')%nat) by lia.
        apply Hrow_sum; exact H_lt.
      (* 修改结束 *)
    - assert (Heq : sum_f_R0 (fun i => a i * (4 * K (INR C))) N = 4 * K (INR C) * sum_f_R0 a N).
      {
        rewrite <- (sum_f_R0_scal_l (4 * K (INR C)) a N).
        apply sum_f_R0_ext; intros; ring.
      }
      rewrite Heq; apply Rle_refl.
Qed.

(* Psi非对角内积的衰减界 *)
Lemma psi_off_diag_decay :
  forall (seq : nat -> nat) (I : list nat) (C : nat)
    (Hc_ge2 : (C >= 2)%nat) (Hge2 : forall i, (seq i >= 2)%nat)
    (Hsparse : forall i, INR (seq (S i)) > INR C * INR (seq i))
    (Hdup : NoDup I) (Hsorted : Sorted Nat.lt I)
    (vals : list nat) (Hvals_eq : vals = map seq I)
    (maxIdx : nat) (HmaxIdx_eq : maxIdx = fold_right Init.Nat.max 0%nat I)
    (Hmax_bound : forall a, In a I -> (seq a <= seq maxIdx)%nat)
    (M : nat) (HM_eq : M = S (seq maxIdx))
    (i j : nat) (Hneq : i <> j) (Hi_len : (i < length I)%nat) (Hj_len : (j < length I)%nat),
  Cnorm (Csum (fun k => psi (nth i vals 0%nat) k *c Cconj (psi (nth j vals 0%nat) k)) (M - 1))
  <= 2 * / ((sqrt (INR C)) ^ (Z.abs_nat (Z.of_nat i - Z.of_nat j))).
Proof.
  intros. eapply inner_decay_bound with (seq := seq) (I := I) (C := C); eauto.
Qed.

(* Psi内积在边界处的尾部截断恒等式 *)
Lemma psi_inner_M_eq_pred_M :
  forall (seq : nat -> nat) (I : list nat) (vals : list nat)
    (maxIdx : nat) (M : nat) (HM_eq : M = S (seq maxIdx))
    (Hvals_eq : vals = map seq I)
    (Hmax_bound : forall a, In a I -> (seq a <= seq maxIdx)%nat)
    (i j : nat) (Hi : (i < length I)%nat) (Hj : (j < length I)%nat),
  Csum (fun k => psi (nth i vals 0%nat) k *c Cconj (psi (nth j vals 0%nat) k)) M
  = Csum (fun k => psi (nth i vals 0%nat) k *c Cconj (psi (nth j vals 0%nat) k)) (M - 1).
Proof.
  intros; subst M.
  set (f := fun k : nat => psi (nth i vals 0%nat) k *c Cconj (psi (nth j vals 0%nat) k)).
  assert (Hlast_val : f (seq maxIdx) = C0).
  { subst f; subst vals.
    rewrite (H_nth_map nat nat seq I 0%nat 0%nat i Hi).
    rewrite (H_nth_map nat nat seq I 0%nat 0%nat j Hj).
    assert (Hi_le : (seq (nth i I 0%nat) <= seq maxIdx)%nat).
    { apply Hmax_bound; apply nth_In; assumption. }
    rewrite psi_ge_n_zero by apply Hi_le.
    apply Cmul_0_l.
  }
  rewrite Csum_S, Hlast_val, Cadd_0_r.
  replace ((S (seq maxIdx) - 1)%nat) with (seq maxIdx) by lia.
  reflexivity.
Qed.

(* Psi自内积在最大索引截断下恒为1 *)
Lemma psi_inner_self_eq_one :
  forall (seq : nat -> nat) (I : list nat) (vals : list nat) (maxIdx : nat) (M : nat)
         (Hge2 : forall i, (seq i >= 2)%nat)
         (Hvals_eq : vals = map seq I)
         (HM_eq : M = S (seq maxIdx))
         (Hmax_bound : forall a, In a I -> (seq a <= seq maxIdx)%nat)
         (i : nat) (Hi : (i < length I)%nat),
    Csum (fun k => psi (nth i vals 0%nat) k *c Cconj (psi (nth i vals 0%nat) k)) (M - 1) = ComplexNumbers.C1.
Proof.
  intros; subst vals M.
  rewrite (H_nth_map nat nat seq I 0%nat 0%nat i Hi).
  set (ni := seq (nth i I 0%nat)).
  assert (Hni_ge2 : (ni >= 2)%nat) by (subst ni; apply Hge2).
  assert (Hle_n : (ni <= S (seq maxIdx) - 1)%nat).
  { subst ni; apply Nat.le_trans with (seq maxIdx);
    [apply Hmax_bound, nth_In; assumption | lia]. }
  assert (Hsum_ni : Csum (fun k => psi ni k *c Cconj (psi ni k)) ni = ComplexNumbers.C1).
  { apply Csum_orthonormal_self; lia. }
  assert (Heq : Csum (fun k => psi ni k *c Cconj (psi ni k)) (S (seq maxIdx) - 1)%nat
                = Csum (fun k => psi ni k *c Cconj (psi ni k)) ni).
  {
    apply Csum_trunc_tail with (M := ni) (N := (S (seq maxIdx) - 1)%nat).
    - exact Hle_n.
    - intros k (Hle_k & Hlt_k). assert (Hk_ge_ni : (ni <= k)%nat) by lia.
      rewrite (psi_ge_n_zero ni k Hk_ge_ni). apply Cmul_0_l.
  }
  rewrite Heq, Hsum_ni; reflexivity.
Qed.

(* Psi函数的ℓ²范数平方的分解等式 *)
Lemma psi_l2_norm_sq_eq :
  forall (seq : nat -> nat) (I : list nat) (vals : list nat) (maxIdx : nat) (M : nat)
         (coeffs : list Complex) (n : nat)
         (Hge2 : forall i, (seq i >= 2)%nat)
         (Hvals_eq : vals = map seq I)
         (Hlen_coeffs : length coeffs = n)
         (Hlen_vals : length vals = n)
         (HM_eq : M = S (seq maxIdx))
         (HMpos : (M > 0)%nat)
         (Hmax_bound : forall a, In a I -> (seq a <= seq maxIdx)%nat)
         (Hn_pos : (n > 0)%nat),
    let Fk := fun k => Csum (fun i => nth i coeffs C0 *c psi (nth i vals 0%nat) k) n in
    let inner i j := Csum (fun k => psi (nth i vals 0%nat) k *c Cconj (psi (nth j vals 0%nat) k)) (M - 1) in
    let S0 := sum_f_R0 (fun i => Cnorm_sq (nth i coeffs C0)) (n - 1) in
    let g i j := re (nth i coeffs C0 *c Cconj (nth j coeffs C0) *c inner i j) in
    let off := sum_f_R0 (fun i => sum_f_R0 (fun j => if eq_nat_dec i j then 0%R else g i j) (n - 1)) (n - 1) in
    l2_norm_sq Fk (M - 1) = S0 + off.
Proof.
  intros; subst vals M.
  assert (Hn_pred_lt : forall i, (i <= (n - 1)%nat)%nat -> (i < n)%nat) by lia.
  pose proof (l2_expand_double_sum coeffs (map seq I) n (S (seq maxIdx)) Hlen_coeffs Hlen_vals HMpos) as Hraw.
  cbv beta in Hraw.

  assert (HsumM_eq : forall i j, (i < n)%nat -> (j < n)%nat ->
    Csum (fun k => psi (nth i (map seq I) 0%nat) k *c Cconj (psi (nth j (map seq I) 0%nat) k)) (S (seq maxIdx))
    = inner i j).
  {
    intros i j Hi Hj.
    assert (Hi_len_map : (i < length (map seq I))%nat) by (rewrite Hlen_vals; exact Hi).
    assert (Hj_len_map : (j < length (map seq I))%nat) by (rewrite Hlen_vals; exact Hj).
    assert (Hi_len_I : (i < length I)%nat) by (rewrite length_map in Hi_len_map; exact Hi_len_map).
    assert (Hj_len_I : (j < length I)%nat) by (rewrite length_map in Hj_len_map; exact Hj_len_map).
    pose proof (H_nth_map nat nat seq I 0%nat 0%nat i Hi_len_I) as Hni.
    pose proof (H_nth_map nat nat seq I 0%nat 0%nat j Hj_len_I) as Hnj.
    simpl in Hni, Hnj.
    unfold inner.
    apply (Csum_trunc_tail
             (fun k => psi (nth i (map seq I) 0%nat) k *c Cconj (psi (nth j (map seq I) 0%nat) k))
             (S (seq maxIdx) - 1) (S (seq maxIdx))).
    - lia.
    - intros k [Hk1 Hk2].
      assert (Hk_eq : k = seq maxIdx) by lia; subst k.
      rewrite Hni, Hnj.
      assert (Hle_i : (seq (nth i I 0%nat) <= seq maxIdx)%nat)
        by (apply Hmax_bound; apply nth_In; exact Hi_len_I).
      assert (Hle_j : (seq (nth j I 0%nat) <= seq maxIdx)%nat)
        by (apply Hmax_bound; apply nth_In; exact Hj_len_I).
      rewrite (psi_ge_n_zero (seq (nth i I 0%nat)) (seq maxIdx) Hle_i).
      rewrite (psi_ge_n_zero (seq (nth j I 0%nat)) (seq maxIdx) Hle_j).
      rewrite Cconj_0, Cmul_0_r; reflexivity.
  }

  unfold Fk; rewrite Hraw.
  transitivity (sum_f_R0 (fun i => sum_f_R0 (fun j =>
    re (nth i coeffs C0 *c Cconj (nth j coeffs C0) *c inner i j)) (n-1)) (n-1)).
  - apply sum_f_R0_ext; intros i Hi.
    apply sum_f_R0_ext; intros j Hj.
    assert (Hi' : (i < n)%nat) by (apply Hn_pred_lt; exact Hi).
    assert (Hj' : (j < n)%nat) by (apply Hn_pred_lt; exact Hj).
    rewrite (HsumM_eq i j Hi' Hj').
    reflexivity.

  assert (Hinner_self_C1 : forall i, (i < n)%nat -> inner i i = ComplexNumbers.C1).
  {
    intros i Hi.
    assert (Hi_len_map : (i < length (map seq I))%nat) by (rewrite Hlen_vals; exact Hi).
    assert (Hi_len_I : (i < length I)%nat) by (rewrite length_map in Hi_len_map; exact Hi_len_map).
    pose proof (H_nth_map nat nat seq I 0%nat 0%nat i Hi_len_I) as Hni.
    simpl in Hni.
    set (ni := seq (nth i I 0%nat)) in *.
    assert (Hni_ge2 : (ni >= 2)%nat) by (unfold ni; apply Hge2).
    assert (Hni_pos : (ni > 0)%nat) by lia.
    assert (Hni_lt_Smax : (ni < S (seq maxIdx))%nat).
    {
      apply Nat.lt_succ_r.
      unfold ni.
      apply Hmax_bound; apply nth_In; exact Hi_len_I.
    }
    unfold inner.
    rewrite Hni.
    assert (Htrunc : Csum (fun k => psi ni k *c Cconj (psi ni k)) (S (seq maxIdx) - 1)
                   = Csum (fun k => psi ni k *c Cconj (psi ni k)) ni).
    {
      apply (Csum_trunc_tail (fun k => psi ni k *c Cconj (psi ni k)) ni (S (seq maxIdx) - 1));
        [lia |].
      intros k [Hk1 Hk2].
      assert (Hk_ge_ni : (ni <= k)%nat) by lia.
      rewrite (psi_ge_n_zero ni k Hk_ge_ni), Cmul_0_l; reflexivity.
    }
    rewrite Htrunc.
    apply Csum_orthonormal_self; exact Hni_pos.
  }

  set (h i j := re (nth i coeffs C0 *c Cconj (nth j coeffs C0) *c inner i j)).
  assert (Hdiag_term : forall i, (i < n)%nat -> h i i = Cnorm_sq (nth i coeffs C0)).
  {
    intros i Hi; unfold h.
    rewrite (Hinner_self_C1 i Hi), Cmul_1_r. symmetry. apply Cnorm_sq_eq_re_mul.
  }
  pose proof (double_sum_diag_split (n-1)%nat h) as Hsplit.
  replace (sum_f_R0 (fun i => sum_f_R0 (fun j =>
    re (nth i coeffs C0 *c Cconj (nth j coeffs C0) *c inner i j)) (n-1)) (n-1))
    with (sum_f_R0 (fun i => sum_f_R0 (h i) (n-1)) (n-1)).
  {
    rewrite Hsplit.
    assert (Hdiag_sum : sum_f_R0 (fun i => h i i) (n-1) = S0).
    { unfold S0; apply sum_f_R0_ext; intros i Hi; apply Hdiag_term, Hn_pred_lt, Hi. }
    rewrite Hdiag_sum.
    assert (Hoff_sum : sum_f_R0 (fun i => sum_f_R0 (fun j =>
      if eq_dec i j then 0 else h i j) (n-1)) (n-1) = off).
    { unfold off, g; apply sum_f_R0_ext; intros i Hi; apply sum_f_R0_ext; intros j Hj; reflexivity. }
    rewrite Hoff_sum.
    reflexivity.
  }
  { apply sum_f_R0_ext; intros i Hi; apply sum_f_R0_ext; intros j Hj; unfold h; reflexivity. }
Qed.

(* Psi非对角内积项的绝对值全局上界 *)
Lemma psi_off_abs_bound :
  forall (seq : nat -> nat) (I : list nat) (vals : list nat) (maxIdx : nat) (M : nat)
         (coeffs : list Complex) (n : nat) (C : nat)
         (Hge2 : forall i, (seq i >= 2)%nat)
         (Hvals_eq : vals = map seq I)
         (HM_eq : M = S (seq maxIdx))
         (Hmax_bound : forall a, In a I -> (seq a <= seq maxIdx)%nat)
         (HCgt2 : (C > 2)%nat)
         (Hn_pos : (n > 0)%nat),
    let inner i j := Csum (fun k => psi (nth i vals 0%nat) k *c Cconj (psi (nth j vals 0%nat) k)) (M - 1) in
    let inner_norm i j := Cnorm (inner i j) in
    (forall i j, 0 <= inner_norm i j) ->
    (forall i j, inner_norm i j = inner_norm j i) ->
    (forall i, (i < n)%nat -> sum_f_R0 (fun j => if eq_nat_dec i j then 0%R else inner_norm i j) (n-1) <= 4 * K (INR C)) ->
    let S0 := sum_f_R0 (fun i => Cnorm_sq (nth i coeffs C0)) (n-1) in
    let off := sum_f_R0 (fun i => sum_f_R0 (fun j =>
                 if eq_nat_dec i j then 0%R
                 else re (nth i coeffs C0 *c Cconj (nth j coeffs C0) *c inner i j)) (n-1)) (n-1) in
    Rabs off <= 4 * K (INR C) * S0.
Proof.
  intros; subst vals M.
  rename H into Hpos_inner_norm, H0 into Hsym_inner_norm, H1 into Hrow_sum.
  set (a i := Cnorm (nth i coeffs C0)).
  assert (Cnorm_sq_ge_0 : forall z : Complex, 0 <= Cnorm_sq z). {
    intros [x y]; unfold Cnorm_sq; apply Rplus_le_le_0_compat; apply Rle_0_sqr.
  }
  assert (Cnorm_ge_0 : forall z : Complex, 0 <= Cnorm z). {
    intro z; unfold Cnorm; apply sqrt_pos.
  }
  assert (Ha_sq_eq : forall i, (a i)^2 = Cnorm_sq (nth i coeffs C0)). {
    intros i; unfold a, Cnorm.
    replace ((sqrt (Cnorm_sq (nth i coeffs C0))) ^ 2)
      with (Rsqr (sqrt (Cnorm_sq (nth i coeffs C0)))) by (unfold Rsqr; ring).
    rewrite Rsqr_sqrt; [reflexivity | apply Cnorm_sq_ge_0].
  }
  assert (Rabs_re_le_Cnorm : forall z : Complex, Rabs (re z) <= Cnorm z). {
    intros [x y]; unfold re, Cnorm, Cnorm_sq; simpl.
    rewrite <- (sqrt_Rsqr_abs x) at 1.
    apply sqrt_le_1_c.
    - apply Rle_0_sqr.
    - apply Rplus_le_le_0_compat; apply Rle_0_sqr.
    - unfold Rsqr; nra.
  }
  assert (Rabs_sum_f_R0 : forall (f : nat -> R) N, Rabs (sum_f_R0 f N) <= sum_f_R0 (fun i => Rabs (f i)) N). {
    induction N; simpl.
    - apply Rle_refl.
    - eapply Rle_trans; [apply Rabs_triang|].
      apply Rplus_le_compat; [apply IHN|apply Rle_refl].
  }
  assert (Habs_single : forall i j, Rabs (re (nth i coeffs C0 *c Cconj (nth j coeffs C0) *c inner i j)) <= a i * a j * inner_norm i j). {
    intros i j; unfold a, inner_norm.
    eapply Rle_trans; [apply Rabs_re_le_Cnorm|].
    rewrite Cnorm_mult, (Cnorm_mult _ (Cconj _)), Cnorm_conj_eq.
    apply Rle_refl.
  }
  assert (Hest : Rabs off <= sum_f_R0 (fun i => sum_f_R0 (fun j =>
    if eq_nat_dec i j then 0%R else a i * a j * inner_norm i j) (n-1)) (n-1)).
  { eapply Rle_trans; [apply Rabs_sum_f_R0|].
    apply sum_f_R0_le_compat; intros i Hi.
    eapply Rle_trans; [apply Rabs_sum_f_R0|].
    apply sum_f_R0_le_compat; intros j Hj.
    unfold off.
    destruct (eq_nat_dec i j) as [Heq|Hneq].
    - subst; simpl; rewrite Rabs_R0. lra.
    - apply Habs_single. }
  set (U i j := if eq_nat_dec i j then 0%R else inner_norm i j).
  assert (U_nonneg : forall i j, 0 <= U i j).
  { intros; unfold U; destruct (eq_nat_dec i j); [lra|auto]. }
  assert (U_sym : forall i j, U i j = U j i).
  { intros; unfold U; destruct (eq_nat_dec i j), (eq_nat_dec j i); congruence || auto; try contradiction. }
  assert (HrowU : forall i, (i < n)%nat -> sum_f_R0 (U i) (n-1) <= 4 * K (INR C)).
  { intros i Hi; unfold U; apply Hrow_sum; exact Hi. }
  assert (Hquad : sum_f_R0 (fun i => sum_f_R0 (fun j => a i * a j * U i j) (n-1)) (n-1) <=
                  (4 * K (INR C)) * sum_f_R0 (fun i => (a i)^2) (n-1)).
  {
    assert (H_amgm : forall i j, a i * a j <= ((a i)^2 + (a j)^2) / 2). {
      intros i j;
      assert (Hsq : 0 <= Rsqr (a i - a j)) by apply Rle_0_sqr;
      unfold Rsqr in Hsq; lra. }
    assert (Haux : sum_f_R0 (fun i => sum_f_R0 (fun j => a i * a j * U i j) (n-1)) (n-1) <=
                   sum_f_R0 (fun i => sum_f_R0 (fun j => ((a i)^2 + (a j)^2) / 2 * U i j) (n-1)) (n-1)).
    { apply sum_f_R0_le_compat; intros i Hi; apply sum_f_R0_le_compat; intros j Hj.
      apply Rmult_le_compat_r; [apply U_nonneg | apply H_amgm]. }
    assert (Heq : sum_f_R0 (fun i => sum_f_R0 (fun j => ((a i)^2 + (a j)^2) / 2 * U i j) (n-1)) (n-1) =
                  sum_f_R0 (fun i => (a i)^2 * sum_f_R0 (U i) (n-1)) (n-1)).
    {
      set (S := sum_f_R0 (fun i => (a i)^2 * sum_f_R0 (U i) (n-1)) (n-1)).
      assert (Hswap : sum_f_R0 (fun i => sum_f_R0 (fun j => (a j)^2 * U i j) (n-1)) (n-1) = S). {
        rewrite (sum_f_R0_swap (n-1) (n-1) (fun i j => (a j)^2 * U i j)).
        apply sum_f_R0_ext; intros j Hj.
        rewrite <- sum_f_R0_scal_l.
        apply sum_f_R0_ext; intros i Hi.
        rewrite U_sym; reflexivity.
      }
      rewrite (sum_f_R0_ext _ (fun i => 1/2 * sum_f_R0 (fun j => (a i)^2 * U i j) (n-1) +
                                  1/2 * sum_f_R0 (fun j => (a j)^2 * U i j) (n-1)) (n-1)).
      - rewrite sum_f_R0_add.
        rewrite !sum_f_R0_scal_l.
        set (A := sum_f_R0 (fun i => sum_f_R0 (fun j => (a i)^2 * U i j) (n-1)) (n-1)).
        set (B := sum_f_R0 (fun i => sum_f_R0 (fun j => (a j)^2 * U i j) (n-1)) (n-1)).
        assert (A_eq_S : A = S). {
          unfold A, S.
          apply sum_f_R0_ext; intros i Hi.
          rewrite <- sum_f_R0_scal_l; reflexivity.
        }
        assert (B_eq_S : B = S). {
          unfold B; rewrite Hswap; reflexivity.
        }
        rewrite A_eq_S, B_eq_S.
        lra.
      - intros i Hi.
        transitivity (sum_f_R0 (fun j => (a i)^2 / 2 * U i j + (a j)^2 / 2 * U i j) (n-1)).
        + apply sum_f_R0_ext; intros j Hj.
          unfold Rdiv.
          field; lra.
        + rewrite sum_f_R0_add.
          rewrite (sum_f_R0_ext (fun j => a i ^ 2 / 2 * U i j)
                                (fun j => 1/2 * (a i ^ 2 * U i j)) (n-1)).
          * rewrite (sum_f_R0_ext (fun j => a j ^ 2 / 2 * U i j)
                                  (fun j => 1/2 * (a j ^ 2 * U i j)) (n-1)).
            -- rewrite !sum_f_R0_scal_l; ring.
            -- intros j Hj; unfold Rdiv; ring.
          * intros j Hj; unfold Rdiv; ring.
    }
    eapply Rle_trans; [apply Haux | rewrite Heq].
    assert (H_mul : sum_f_R0 (fun i => (a i)^2 * sum_f_R0 (U i) (n-1)) (n-1) <=
                   (4 * K (INR C)) * sum_f_R0 (fun i => (a i)^2) (n-1)).
    {
      apply Rle_trans with (sum_f_R0 (fun i => (a i)^2 * (4 * K (INR C))) (n-1)).
      - apply sum_f_R0_le_compat; intros i Hi.
        apply Rmult_le_compat_l.
        + rewrite Ha_sq_eq; apply Cnorm_sq_ge_0.
        + apply HrowU; lia.
      - assert (H_eq_const : sum_f_R0 (fun i => (a i)^2 * (4 * K (INR C))) (n-1)
                           = (4 * K (INR C)) * sum_f_R0 (fun i => (a i)^2) (n-1)).
        {
          rewrite <- (sum_f_R0_scal_l (4 * K (INR C)) (fun i => (a i)^2) (n-1)).
          apply sum_f_R0_ext; intros; ring.
        }
        rewrite H_eq_const; apply Rle_refl.
    }
    exact H_mul.
  }
  unfold S0.
  assert (Heq_S0 : sum_f_R0 (fun i : nat => Cnorm_sq (nth i coeffs C0)) (n - 1) =
                   sum_f_R0 (fun i : nat => a i ^ 2) (n - 1)).
  {
    apply sum_f_R0_ext; intros i Hi.
    rewrite Ha_sq_eq; reflexivity.
  }
  rewrite Heq_S0.
  assert (Htrans : sum_f_R0 (fun i => sum_f_R0 (fun j =>
      if eq_nat_dec i j then 0%R else a i * a j * inner_norm i j) (n-1)) (n-1)
      <= 4 * K (INR C) * sum_f_R0 (fun i => (a i)^2) (n-1)).
  {
    apply Rle_trans with (sum_f_R0 (fun i => sum_f_R0 (fun j => a i * a j * U i j) (n-1)) (n-1)).
    - apply sum_f_R0_le_compat; intros i Hi; apply sum_f_R0_le_compat; intros j Hj.
      unfold U.
      destruct (eq_nat_dec i j) as [Heq|Hne].
      + subst; simpl; rewrite Rmult_0_r; lra.
      + simpl; apply Rle_refl.
    - exact Hquad.
  }
  eapply Rle_trans; [apply Hest | exact Htrans].
Qed.

(* 定理：无条件基 *)
Theorem psi_unconditional_basis :
  forall (seq : nat -> nat)
         (Hge2 : forall i, (seq i >= 2)%nat)
         (Hinc : forall i, (seq i < seq (S i))%nat)
         (C : nat)
         (HCgt2 : (C > 2)%nat)
         (Hsparse : forall i, (INR (seq (S i)) > INR C * INR (seq i))%R)
         (I : list nat)
         (coeffs : list Complex)
         (Hdup : NoDup I)
         (Hsorted : Sorted Nat.lt I)
         (Hlen : length I = length coeffs),
    let n := length I in
    let vals := map seq I in
    let F := fun k => Csum (fun idx => nth idx coeffs C0 *c psi (nth idx vals 0%nat) k) n in
    let maxIdx := fold_right Init.Nat.max 0%nat I in
    let M := S (seq maxIdx) in
    let S := sum_f_R0 (fun i => Cnorm_sq (nth i coeffs C0)) (n - 1) in
    ((1 - 4 * K (INR C)) * S <= l2_norm_sq F (M - 1) <= (1 + 4 * K (INR C)) * S)%R.
Proof.
  intros seq Hge2 Hinc C HCgt2 Hsparse I coeffs Hdup Hsorted Hlen.
  set (n := length I).
  set (vals := map seq I).
  set (Fk := fun k => Csum (fun i => nth i coeffs C0 *c psi (nth i vals 0%nat) k) n).
  set (maxIdx := fold_right Init.Nat.max 0%nat I).
  set (M := S (seq maxIdx)).
  set (S0 := sum_f_R0 (fun i => Cnorm_sq (nth i coeffs C0)) (n - 1)).

  destruct (seq_strictly_increasing seq Hinc) as [Hstrict_inc Hinj].

  assert (Hseq_mono : forall a b, (a <= b)%nat -> (seq a <= seq b)%nat). {
    intros a b Hle; destruct (Nat.eq_dec a b) as [-> | Hne];
      [apply Nat.le_refl | apply Nat.lt_le_incl, Hstrict_inc; lia].
  }
  assert (Hmax_bound : forall a, In a I -> (seq a <= seq maxIdx)%nat). {
    intros a Ha; apply Hseq_mono; eapply fold_right_max_ge; eauto.
  }
  assert (Hvals_nodup : NoDup vals) by (apply (NoDup_vals seq I Hinj Hdup)).
  assert (Hvals_ge2 : forall v, In v vals -> (v >= 2)%nat) by (apply vals_ge2; auto).

  set (inner i j := Csum (fun k => psi (nth i vals 0%nat) k *c Cconj (psi (nth j vals 0%nat) k)) (M - 1)).
  set (inner_norm i j := Cnorm (inner i j)).

  assert (inner_norm_nonneg : forall i j, 0 <= inner_norm i j). {
    intros; unfold inner_norm; apply Cnorm_ge_0.
  }

  assert (Hc_ge2 : (C >= 2)%nat) by lia.
  assert (Hlen_vals : length vals = n) by (unfold vals; rewrite length_map; reflexivity).

  assert (Hdecay : forall i j, i <> j -> (i < n)%nat -> (j < n)%nat ->
    Cnorm (Csum (fun k => psi (nth i vals 0%nat) k *c Cconj (psi (nth j vals 0%nat) k)) (M - 1))
    <= 2 * / ((sqrt (INR C)) ^ (Z.abs_nat (Z.of_nat i - Z.of_nat j)))).
  {
    intros i j Hneq Hi Hj.
    assert (Hi_len : (i < length I)%nat) by (unfold n in Hi; exact Hi).
    assert (Hj_len : (j < length I)%nat) by (unfold n in Hj; exact Hj).
    assert (Hvals_eq : vals = map seq I) by (unfold vals; reflexivity).
    assert (HmaxIdx_eq : maxIdx = fold_right Init.Nat.max 0%nat I) by (unfold maxIdx; reflexivity).
    assert (HM_eq : M = S (seq maxIdx)) by (unfold M; reflexivity).
    exact (@inner_decay_bound seq I C Hc_ge2 Hge2 Hsparse Hdup Hsorted
              vals Hvals_eq maxIdx HmaxIdx_eq Hmax_bound M HM_eq i j Hneq Hi_len Hj_len).
  }

  assert (Hinner_sym : forall i j, inner_norm i j = inner_norm j i). {
    intros i j; unfold inner_norm, inner.
    set (Sij := Csum (fun k => psi (nth i vals 0%nat) k *c Cconj (psi (nth j vals 0%nat) k)) (M - 1)).
    set (Sji := Csum (fun k => psi (nth j vals 0%nat) k *c Cconj (psi (nth i vals 0%nat) k)) (M - 1)).
    enough (Cconj Sij = Sji) as Hconj.
    - rewrite <- (Cnorm_conj_eq Sij); rewrite Hconj; reflexivity.
    - subst Sij Sji.
      rewrite Cconj_Csum.
      generalize (M - 1)%nat as N.
      induction N; simpl.
      + reflexivity.
      + f_equal; auto.
        rewrite Cconj_mul_conj_eq; reflexivity.
  }

  assert (Hrow_sum : forall i, (i < n)%nat ->
    sum_f_R0 (fun j => if eq_nat_dec i j then 0%R else inner_norm i j) (n - 1) <= 4 * K (INR C)).
  {
    intros i Hi.
    unfold inner_norm.
    apply (row_sum_bound n vals M C Hvals_ge2 Hlen_vals Hdecay HCgt2 i Hi).
  }

  assert (Hlen_coeffs : length coeffs = n) by (unfold n; rewrite Hlen; reflexivity).
  assert (HMpos : (M > 0)%nat) by (unfold M; lia).

  destruct n as [|n'] eqn:Hn.
  {
    unfold n in Hn, Hlen_coeffs.
    assert (HI_nil : I = []) by (destruct I; [reflexivity | simpl in Hn; lia]).
    assert (Hcoeffs_nil : coeffs = []) by (destruct coeffs; [reflexivity | simpl in Hlen_coeffs; lia]).
    subst I coeffs.
    unfold Fk, S0.
    assert (HmaxIdx0 : maxIdx = 0%nat) by (unfold maxIdx; simpl; reflexivity).
    assert (HM_eq0 : (M - 1)%nat = seq 0%nat). {
      unfold M; rewrite HmaxIdx0; lia.
    }
    change (S (seq maxIdx) - 1)%nat with (M - 1)%nat.
    rewrite HM_eq0.
    simpl (Csum (fun _ : nat => C0 *c _) 0).
    unfold l2_norm_sq.
    unfold Cnorm_sq; simpl.
    rewrite !Rsqr_0, Rplus_0_r.
    rewrite sum_f_R0_zero.
    rewrite !Rmult_0_r.
    split; apply Rle_refl.
  }

  subst n.
  assert (Hn_pos' : (S n' > 0)%nat) by lia.
  assert (HM_eq_val : M = S (seq maxIdx)) by (unfold M; reflexivity).
  assert (Hvals_eq_val : vals = map seq I) by (unfold vals; reflexivity).

  pose proof (psi_l2_norm_sq_eq seq I vals maxIdx M coeffs (S n')
                Hge2 Hvals_eq_val Hlen_coeffs Hlen_vals HM_eq_val HMpos Hmax_bound Hn_pos')
    as HL2_eq.
  unfold Fk, S0 in *.
  set (off := sum_f_R0 (fun i => sum_f_R0 (fun j =>
    if eq_nat_dec i j then 0%R
    else re (nth i coeffs C0 *c Cconj (nth j coeffs C0) *c inner i j)) (S n' - 1)) (S n' - 1)).

  unfold M in HL2_eq.
  assert (Htemp : l2_norm_sq (fun k => Csum (fun i => nth i coeffs C0 *c psi (nth i vals 0%nat) k) (S n'))
                            (S (seq maxIdx) - 1) = S0 + off). {
    rewrite HL2_eq.
    unfold off, inner.
    reflexivity.
  }
  rewrite Htemp.

  assert (Hrow_sum' : forall i : nat, (i < S n')%nat ->
    sum_f_R0 (fun j : nat => if eq_nat_dec i j then 0%R else inner_norm i j) (S n' - 1) <= 4 * K (INR C)).
  { exact Hrow_sum. }

  pose proof (psi_off_abs_bound seq I vals maxIdx M coeffs (S n') C
                Hge2 Hvals_eq_val HM_eq_val Hmax_bound HCgt2 Hn_pos'
                inner_norm_nonneg Hinner_sym Hrow_sum')
    as Hoff_bound.

  assert (Hoff_abs : Rabs off <= 4 * K (INR C) * S0). {
    unfold off, S0.
    exact Hoff_bound.
  }

  assert (Hoff_range : - (4 * K (INR C) * S0) <= off <= 4 * K (INR C) * S0). {
    destruct (Rle_or_lt off 0) as [Hoff_le0 | Hoff_gt0].
    - rewrite Rabs_left1 in Hoff_abs by exact Hoff_le0.
      split; lra.
    - rewrite Rabs_right in Hoff_abs by lra.
      split; lra.
  }
  destruct Hoff_range as [Hoff_low Hoff_high].

  fold S0.
  split.
  - lra.
  - lra.
Qed.

(* M严格正时ℓ²范数平方的二重求和展开 *)
Lemma expand_l2_norm_sq_with_zero_tail :
  forall (n : nat) (phi : nat -> nat -> Complex) (M : nat),
    (M > 0)%nat ->
    let M_pred := Nat.pred M in
    let n_pred := Nat.pred n in
    forall (coeffs : list Complex),
      length coeffs = n ->
      let F (k : nat) := independent.Csum (fun i : nat => nth i coeffs ComplexNumbers.C0 *c phi i k) n in
      let inner (i j : nat) := independent.Csum (fun k : nat => phi i k *c ComplexNumbers.Cconj (phi j k)) M in
      l2_norm_sq F M_pred =
      sum_f_R0 (fun i : nat =>
        sum_f_R0 (fun j : nat =>
          re (nth i coeffs ComplexNumbers.C0 *c ComplexNumbers.Cconj (nth j coeffs ComplexNumbers.C0) *c inner i j))
        n_pred) n_pred.
Proof.
  intros n phi M HMpos M_pred n_pred coeffs Hlen F inner.
  unfold l2_norm_sq.

  assert (re_eq : forall (a b x y : Complex),
    re ((a *c x) *c ComplexNumbers.Cconj (b *c y)) =
    re (a *c ComplexNumbers.Cconj b *c (x *c ComplexNumbers.Cconj y))).
  { intros; unfold Cmul, ComplexNumbers.Cconj, re; simpl; ring. }

  assert (h : forall k : nat,
    ComplexNumbers.Cnorm_sq (F k) =
    sum_f_R0 (fun i : nat => sum_f_R0 (fun j : nat =>
      re (nth i coeffs ComplexNumbers.C0 *c ComplexNumbers.Cconj (nth j coeffs ComplexNumbers.C0)
          *c (phi i k *c ComplexNumbers.Cconj (phi j k)))) n_pred) n_pred).
  { intros k.
    unfold F.
    destruct n as [|n0].
    - assert (Hcoeffs_nil : coeffs = []) by (destruct coeffs; [reflexivity | simpl in Hlen; lia]).
      subst coeffs.
      unfold n_pred; simpl.
      unfold ComplexNumbers.Cnorm_sq, ComplexNumbers.C0.
      simpl Rsqr; rewrite !Rsqr_0; ring.
    - simpl.
      change (Csum (fun i : nat => nth i coeffs C0 *c phi i k) n0 +c
              nth n0 coeffs C0 *c phi n0 k)
        with (Csum (fun i : nat => nth i coeffs C0 *c phi i k) (S n0)).
      rewrite Cnorm_sq_csum.
      apply sum_f_R0_ext; intros i Hi.
      apply sum_f_R0_ext; intros j Hj.
      rewrite re_eq; reflexivity. }

  assert (H_temp_eq : sum_f_R0 (fun k : nat => ComplexNumbers.Cnorm_sq (F k)) M_pred =
    sum_f_R0 (fun k : nat => sum_f_R0 (fun i : nat => sum_f_R0 (fun j : nat =>
      re (nth i coeffs ComplexNumbers.C0 *c ComplexNumbers.Cconj (nth j coeffs ComplexNumbers.C0)
          *c (phi i k *c ComplexNumbers.Cconj (phi j k)))) n_pred) n_pred) M_pred).
  { apply sum_f_R0_ext; intros k Hk; apply h. }
  rewrite H_temp_eq.

  rewrite (sum_f_R0_swap M_pred n_pred
    (fun k i => sum_f_R0 (fun j : nat =>
      re (nth i coeffs ComplexNumbers.C0 *c ComplexNumbers.Cconj (nth j coeffs ComplexNumbers.C0)
          *c (phi i k *c ComplexNumbers.Cconj (phi j k)))) n_pred)).

  apply sum_f_R0_ext; intros i Hi.

  rewrite (sum_f_R0_swap M_pred n_pred
    (fun k j => re (nth i coeffs ComplexNumbers.C0 *c ComplexNumbers.Cconj (nth j coeffs ComplexNumbers.C0)
                  *c (phi i k *c ComplexNumbers.Cconj (phi j k))))).

  apply sum_f_R0_ext; intros j Hj.

  set (z := nth i coeffs C0 *c Cconj (nth j coeffs C0)).
  set (g := fun k : nat => phi i k *c Cconj (phi j k)).

  destruct M as [|M'].
  { exfalso; lia. }
  replace M_pred with M' by (unfold M_pred; lia).

  unfold g.
  rewrite <- (re_Csum_scal_correct z (fun k : nat => phi i k *c Cconj (phi j k)) (S M')).
  unfold inner.
  reflexivity.
Qed.

(* 复数零元左乘恒等式 *)
Lemma C0_mul_eq_C0 : forall (x : Complex), ComplexNumbers.C0 *c x = ComplexNumbers.C0.
Proof.
  intros x. destruct x as [a b].
  unfold ComplexNumbers.C0, ComplexNumbers.Cmul.
  apply Complex_eq; simpl; ring.
Qed.

(* 复数零元右乘恒等式 *)
Lemma C0_mul_eq_C0_r : forall (x : Complex), x *c ComplexNumbers.C0 = ComplexNumbers.C0.
Proof.
  intros x. destruct x as [a b].
  unfold ComplexNumbers.C0, ComplexNumbers.Cmul.
  apply Complex_eq; simpl; ring.
Qed.

(* 零项内积化简的实部等式 *)
Lemma re_zero_inner_eq :
  forall (z : Complex) (a b : Complex),
    a = ComplexNumbers.C0 ->
    re (z *c (a *c ComplexNumbers.Cconj b)) = re (z *c ComplexNumbers.C0).
Proof.
  intros z a b Ha. subst a.
  rewrite (C0_mul_eq_C0 (ComplexNumbers.Cconj b)).
  reflexivity.
Qed.

(* 尾项为零条件下的ℓ²范数平方二重求和展开 *)
Lemma expand_l2_norm_sq :
  forall (n : nat) (phi : nat -> nat -> Complex) (M : nat),
    let M_pred := Nat.pred M in
    let n_pred := Nat.pred n in
    forall (coeffs : list Complex),
      length coeffs = n ->
      (forall i k, (i < n)%nat -> (k >= M_pred)%nat -> phi i k = ComplexNumbers.C0) ->
      let F (k : nat) := independent.Csum (fun i : nat => nth i coeffs ComplexNumbers.C0 *c phi i k) n in
      let inner (i j : nat) := independent.Csum (fun k : nat => phi i k *c ComplexNumbers.Cconj (phi j k)) M in
      l2_norm_sq F M_pred =
      sum_f_R0 (fun i : nat =>
        sum_f_R0 (fun j : nat =>
          re (nth i coeffs ComplexNumbers.C0 *c ComplexNumbers.Cconj (nth j coeffs ComplexNumbers.C0) *c inner i j))
        n_pred) n_pred.
Proof.
  intros n phi M M_pred n_pred coeffs Hlen Hzera F inner.
  unfold l2_norm_sq.

  assert (re_eq : forall (a b x y : Complex),
    re ((a *c x) *c ComplexNumbers.Cconj (b *c y)) =
    re (a *c ComplexNumbers.Cconj b *c (x *c ComplexNumbers.Cconj y))).
  { intros; unfold Cmul, ComplexNumbers.Cconj, re; simpl; ring. }

  assert (h : forall k : nat,
    ComplexNumbers.Cnorm_sq (F k) =
    sum_f_R0 (fun i : nat => sum_f_R0 (fun j : nat =>
      re (nth i coeffs ComplexNumbers.C0 *c ComplexNumbers.Cconj (nth j coeffs ComplexNumbers.C0)
          *c (phi i k *c ComplexNumbers.Cconj (phi j k)))) n_pred) n_pred).
  { intros k.
    unfold F.
    destruct n as [|n0].
    - assert (Hcoeffs_nil : coeffs = []) by (destruct coeffs; [reflexivity | simpl in Hlen; lia]).
      subst coeffs.
      unfold n_pred; simpl.
      unfold ComplexNumbers.Cnorm_sq, ComplexNumbers.C0.
      simpl Rsqr; rewrite !Rsqr_0; ring.
    - simpl.
      change (Csum (fun i : nat => nth i coeffs C0 *c phi i k) n0 +c
              nth n0 coeffs C0 *c phi n0 k)
        with (Csum (fun i : nat => nth i coeffs C0 *c phi i k) (S n0)).
      rewrite Cnorm_sq_csum.
      apply sum_f_R0_ext; intros i Hi.
      apply sum_f_R0_ext; intros j Hj.
      rewrite re_eq; reflexivity. }

  assert (H_temp_eq : sum_f_R0 (fun k : nat => ComplexNumbers.Cnorm_sq (F k)) M_pred =
    sum_f_R0 (fun k : nat => sum_f_R0 (fun i : nat => sum_f_R0 (fun j : nat =>
      re (nth i coeffs ComplexNumbers.C0 *c ComplexNumbers.Cconj (nth j coeffs ComplexNumbers.C0)
          *c (phi i k *c ComplexNumbers.Cconj (phi j k)))) n_pred) n_pred) M_pred).
  { apply sum_f_R0_ext; intros k Hk; apply h. }
  rewrite H_temp_eq.

  rewrite (sum_f_R0_swap M_pred n_pred
    (fun k i => sum_f_R0 (fun j : nat =>
      re (nth i coeffs ComplexNumbers.C0 *c ComplexNumbers.Cconj (nth j coeffs ComplexNumbers.C0)
          *c (phi i k *c ComplexNumbers.Cconj (phi j k)))) n_pred)).

  apply sum_f_R0_ext; intros i Hi.

  rewrite (sum_f_R0_swap M_pred n_pred
    (fun k j => re (nth i coeffs ComplexNumbers.C0 *c ComplexNumbers.Cconj (nth j coeffs ComplexNumbers.C0)
                  *c (phi i k *c ComplexNumbers.Cconj (phi j k))))).

  apply sum_f_R0_ext; intros j Hj.

  set (z := nth i coeffs C0 *c Cconj (nth j coeffs C0)).
  set (g := fun k : nat => phi i k *c Cconj (phi j k)).

  destruct M as [|M'].
  - destruct n as [|n0].
    + unfold M_pred, n_pred in *; simpl in *.
      assert (Hcoeffs_nil : coeffs = []) by
        (destruct coeffs; [reflexivity | simpl in Hlen; lia]).
      subst coeffs.
      assert (Hi0 : i = 0%nat) by lia.
      assert (Hj0 : j = 0%nat) by lia.
      subst i j.
      unfold z, inner; simpl; ring.
    + replace M_pred with 0%nat by (unfold M_pred; lia).
      simpl (sum_f_R0 (fun i0 : nat => re (z *c g i0)) 0).
      replace (inner i j) with C0 by (unfold inner; simpl; reflexivity).
      unfold g.
      assert (Hi_lt : (i < S n0)%nat) by (unfold n_pred in Hi; simpl in Hi; lia).
      assert (Hk0 : (0 >= M_pred)%nat) by (unfold M_pred; lia).
      exact (re_zero_inner_eq z (phi i 0%nat) (phi j 0%nat) (Hzera i 0%nat Hi_lt Hk0)).
  - unfold M_pred, inner, z, g.
    rewrite re_Csum_scal_correct.
    simpl.
    reflexivity.
Qed.

(* 实部与共轭乘法恒等式 *)
Lemma re_mul_Cconj_Csum : forall (a b z : Complex),
  ((re a) * (re b) - (im a) * (- im b)) * (re z) - ((re a) * (- im b) + (im a) * (re b)) * (im z)
  = re (a *c Cconj b *c z).
Proof.
  intros [a1 a2] [b1 b2] [z1 z2].
  unfold re, im, Cconj, Cmul, Cadd, Csub, ComplexNumbers.C0; simpl.
  ring.
Qed.

(* ℓ²范数平方的完全重写 *)
Lemma l2_norm_sq_rewrite_full :
  forall (n : nat) (phi : nat -> nat -> Complex) (M : nat) (HMpos : (M > 0)%nat)
    (coeffs : list Complex) (Hlen : length coeffs = n)
    (Hzera : forall i k, (i < n)%nat -> (k >= Nat.pred M)%nat -> phi i k = ComplexNumbers.C0),
  let M_pred := Nat.pred M in
  let n_pred := Nat.pred n in
  let c i := nth i coeffs ComplexNumbers.C0 in
  let inner i j := independent.Csum (fun k : nat => phi i k *c ComplexNumbers.Cconj (phi j k)) M_pred in
  l2_norm_sq (fun k : nat => independent.Csum (fun i : nat => c i *c phi i k) n) M_pred =
  sum_f_R0 (fun i : nat =>
    sum_f_R0 (fun j : nat =>
      re (c i *c ComplexNumbers.Cconj (c j) *c inner i j)) n_pred) n_pred.
Proof.
  intros n phi M HMpos coeffs Hlen Hzera M_pred n_pred c inner.
  assert (lt_pred_l' : forall (i m : nat), (0 < m)%nat -> (i < Nat.pred m)%nat -> (i < m)%nat).
  { intros; lia. }
  assert (Hinner_eq_M : forall i j, (i < n)%nat -> (j < n)%nat ->
    independent.Csum (fun k : nat => phi i k *c ComplexNumbers.Cconj (phi j k)) M = inner i j).
  { intros i0 j0 Hi Hj.
    unfold inner.
    apply Csum_trunc_tail with (M := M_pred) (N := M); [lia|].
    intros k [Hk1 Hk2]. assert (k = M_pred) by lia; subst k.
    rewrite (Hzera i0 M_pred Hi (le_refl M_pred)).
    apply C0_mul_eq_C0. }
  pose proof (expand_l2_norm_sq_with_zero_tail n phi M HMpos coeffs Hlen) as Heq0.
  cbv beta in Heq0.
  destruct (Nat.eq_dec n 0) as [Hn0 | Hnpos].
  - subst n.
    destruct coeffs as [|a coeffs'].
    + unfold n_pred, M_pred; rewrite Hn0; simpl.
      unfold l2_norm_sq at 1.
      rewrite Cnorm_sq_zero, sum_f_R0_zero.
      simpl; ring.
    + simpl in Hn0; lia.
  - assert (Hnpos' : (0 < n)%nat) by lia.
    unfold c, inner, n_pred, M_pred in *.
    rewrite Heq0.
    apply sum_f_R0_ext; intros i Hi.
    apply sum_f_R0_ext; intros j Hj.
    assert (Hi_n : (i < n)%nat) by (unfold n_pred in Hi; lia).
    assert (Hj_n : (j < n)%nat) by (unfold n_pred in Hj; lia).
    rewrite (Hinner_eq_M i j Hi_n Hj_n); reflexivity.
Qed.

(* 实部的绝对值不超过复数的模 *)
Local Lemma Rabs_re_le_Cnorm (z : Complex) : Rabs (re z) <= Cnorm z.
Proof.
  unfold Cnorm, Cnorm_sq, re; simpl.
  rewrite <- sqrt_Rsqr_abs.
  apply sqrt_le_1_c.
  - apply Rle_0_sqr.
  - apply Rplus_le_le_0_compat; apply Rle_0_sqr.
  - unfold Rsqr; nra.
Qed.

(* 前驱索引小于原数 *)
Local Lemma lt_of_le_pred i n (Hpos : (0 < n)%nat) : (i <= Nat.pred n)%nat -> (i < n)%nat.
Proof.
  intro Hle.
  destruct n as [|n'].
  - exfalso; apply (Nat.lt_irrefl 0 Hpos).
  - simpl (Nat.pred (S n')) in Hle.
    apply Nat.lt_succ_r; exact Hle.
Qed.

(* 复数模平方非负 *)
Local Lemma Cnorm_sq_ge_0 z : 0 <= Cnorm_sq z.
Proof. unfold Cnorm_sq; apply Rplus_le_le_0_compat; apply Rle_0_sqr. Qed.

(* 绝对值对有限和的三角不等式 *)
Local Lemma Rabs_sum_f_R0 (g : nat -> R) (N : nat) :
    Rabs (sum_f_R0 g N) <= sum_f_R0 (fun i => Rabs (g i)) N.
Proof.
    induction N; simpl.
    - apply Rle_refl.
    - eapply Rle_trans; [apply Rabs_triang |].
      apply Rplus_le_compat; [apply IHN | apply Rle_refl].
Qed.

(* 复数范数的非负性 *)
Local Lemma Cnorm_ge_0 (z : Complex) : 0 <= Cnorm z.
Proof. unfold Cnorm; apply sqrt_pos. Qed.

(* 复数范数平方与范数平方根的关系 *)
Local Lemma Cnorm_sq_rsqr_sqrt (z : Complex) : (Cnorm z)² = Cnorm_sq z.
Proof. unfold Cnorm; rewrite Rsqr_sqrt; [reflexivity | apply Cnorm_sq_ge_0]. Qed.

(* 定理：非对角项估计 *)
Theorem off_diagonal_estimate :
  forall (n M : nat) (phi : nat -> nat -> Complex) (M_bound : R) (delta : nat -> nat -> R)
    (coeffs : list Complex) (c : nat -> Complex) (inner : nat -> nat -> Complex),
    let M_pred := Nat.pred M in
    let n_pred := Nat.pred n in
    (M > 0)%nat ->
    c = (fun i => nth i coeffs ComplexNumbers.C0) ->
    inner = (fun i j => Csum (fun k => phi i k *c ComplexNumbers.Cconj (phi j k)) M_pred) ->
    length coeffs = n ->
    (forall i k, (i < n)%nat -> (k >= M_pred)%nat -> phi i k = ComplexNumbers.C0) ->
    (forall i : nat, (i < n)%nat -> inner i i = ComplexNumbers.C1) ->
    (forall i j : nat, (i < n)%nat -> (j < n)%nat -> delta i j = delta j i) ->
    (forall i j : nat, (i < n)%nat -> (j < n)%nat -> 0 <= delta i j) ->
    (forall i j : nat, i <> j -> (i < n)%nat -> (j < n)%nat ->
       Cnorm (inner i j) <= delta i j) ->
    (forall i : nat, (i < n)%nat ->
       sum_f_R0 (fun j => if eq_dec i j then 0 else delta i j) n_pred <= M_bound) ->
    (l2_norm_sq (fun k => Csum (fun i => nth i coeffs ComplexNumbers.C0 *c phi i k) n) M_pred
     = sum_f_R0 (fun i => sum_f_R0 (fun j => re (c i *c ComplexNumbers.Cconj (c j) *c inner i j)) n_pred) n_pred) ->
    (1 - M_bound) * sum_f_R0 (fun i => Cnorm_sq (c i)) n_pred <=
    l2_norm_sq (fun k => Csum (fun i => c i *c phi i k) n) M_pred <=
    (1 + M_bound) * sum_f_R0 (fun i => Cnorm_sq (c i)) n_pred.
Proof.
  intros n M phi M_bound delta coeffs c inner M_pred n_pred HMpos Hc Hinner Hlen Hzera Hinner_self
         Hdelta_sym Hdelta_nonneg Hdecay Hrow_sum Heq.
  subst c inner; unfold M_pred, n_pred in *.
  destruct n as [|n'].
  - assert (Hcoeffs_nil : coeffs = []). {
      destruct coeffs; [reflexivity | simpl in Hlen; lia].
    }
    subst coeffs.
    assert (Hl2_0 : l2_norm_sq (fun k : nat => Csum (fun i : nat => nth i [] C0 *c phi i k) 0) (Nat.pred M) = 0%R).
    {
      unfold l2_norm_sq.
      assert (Hzero : forall k : nat, (k <= Nat.pred M)%nat -> 
              Cnorm_sq (Csum (fun i : nat => nth i [] C0 *c phi i k) 0) = 0%R).
      { intros k Hk; rewrite Csum_0; apply Cnorm_sq_zero. }
      rewrite (sum_f_R0_ext (fun k : nat => Cnorm_sq (Csum (fun i : nat => nth i [] C0 *c phi i k) 0))
                           (fun _ : nat => 0%R) (Nat.pred M)
                           (fun i Hi => Hzero i Hi)).
      apply sum_f_R0_zero.
    }
    assert (Hsum0 : sum_f_R0 (fun i : nat => Cnorm_sq (nth i [] C0)) (Nat.pred 0) = 0%R).
    { simpl; apply Cnorm_sq_zero. }
    rewrite Hl2_0, Hsum0.
    split; lra.
  - simpl (Nat.pred (S n')) in *.
    rewrite Heq.
    set (c := fun i : nat => nth i coeffs C0).
    set (inner := fun i j : nat => Csum (fun k : nat => phi i k *c Cconj (phi j k)) (Nat.pred M)).
    rewrite (double_sum_diag_split n'
              (fun i j : nat =>
                 re (nth i coeffs C0 *c Cconj (nth j coeffs C0) *c
                    (Csum (fun k : nat => phi i k *c Cconj (phi j k)) (Nat.pred M))))).
    assert (H_diag : sum_f_R0 (fun i : nat => re (nth i coeffs C0 *c Cconj (nth i coeffs C0) *c Csum (fun k : nat => phi i k *c Cconj (phi i k)) (Nat.pred M))) n'
                   = sum_f_R0 (fun i : nat => Cnorm_sq (nth i coeffs C0)) n').
    { apply sum_f_R0_ext; intros i Hi.
      assert (Hi_n : (i < S n')%nat) by (apply Nat.lt_succ_r; exact Hi).
      rewrite Hinner_self by exact Hi_n.
      rewrite Cmul_1_r.
      rewrite <- Cnorm_sq_eq_re_mul.
      reflexivity. }
    rewrite H_diag.

    set (DiagSum := sum_f_R0 (fun i : nat => Cnorm_sq (c i)) n').
    set (off := sum_f_R0 (fun i : nat =>
                sum_f_R0 (fun j : nat =>
                  if eq_nat_dec i j then 0%R
                  else re (c i *c Cconj (c j) *c inner i j))
                n') n').

    replace (sum_f_R0 (fun i : nat => Cnorm_sq (nth i coeffs C0)) n')
      with DiagSum by (unfold DiagSum, c; reflexivity).
    replace (sum_f_R0 (fun i : nat =>
                sum_f_R0 (fun j : nat =>
                  if eq_nat_dec i j then 0%R
                  else re (nth i coeffs C0 *c Cconj (nth j coeffs C0) *c
                          Csum (fun k : nat => phi i k *c Cconj (phi j k)) (Nat.pred M)))
                n') n')
      with off by (unfold off, c, inner; reflexivity).

    assert (H_off_bound : Rabs off <= M_bound * DiagSum). {
      set (A i := Cnorm (c i)).
      assert (HA_nonneg : forall i, 0 <= A i). { intro; apply Cnorm_ge_0. }
      assert (H_amgm : forall i j, A i * A j <= (A i * A i + A j * A j) / 2).
      { intros i j; unfold A.
        assert (H_sq : 0 <= (Cnorm (c i) - Cnorm (c j))²) by apply Rle_0_sqr.
        unfold Rsqr in H_sq; lra. }

      assert (H_each : forall i j, (i < S n')%nat -> (j < S n')%nat ->
        (if eq_nat_dec i j then 0%R else Rabs (re (c i *c Cconj (c j) *c inner i j)))
        <= (if eq_nat_dec i j then 0%R else (A i * A i + A j * A j) / 2 * delta i j)).
      { intros i j Hi_n Hj_n.
        destruct (eq_nat_dec i j) as [Heq_ij | Hneq].
        - subst; simpl; apply Rle_refl.
        - eapply Rle_trans; [apply Rabs_re_le_Cnorm |].
          rewrite Cnorm_mult, (Cnorm_mult (c i) (Cconj (c j))), Cnorm_conj_eq.
          pose proof (Hdecay i j Hneq Hi_n Hj_n) as Hinner_bound.
          unfold A.
          apply Rle_trans with (Cnorm (c i) * Cnorm (c j) * delta i j).
          + apply Rmult_le_compat_l.
            * apply Rmult_le_pos; apply Cnorm_ge_0.
            * exact Hinner_bound.
          + apply Rmult_le_compat_r; [apply Hdelta_nonneg; [exact Hi_n | exact Hj_n] | apply H_amgm]. }

      assert (H_sum : Rabs off
        <= sum_f_R0 (fun i => sum_f_R0 (fun j =>
            if eq_nat_dec i j then 0%R else (A i * A i + A j * A j) / 2 * delta i j) n') n').
      { subst off; eapply Rle_trans; [apply Rabs_sum_f_R0 |].
        apply sum_f_R0_le_compat; intros i Hi.
        assert (Hi_n : (i < S n')%nat) by (apply Nat.lt_succ_r; exact Hi).
        eapply Rle_trans; [apply Rabs_sum_f_R0 |].
        apply sum_f_R0_le_compat; intros j Hj.
        assert (Hj_n : (j < S n')%nat) by (apply Nat.lt_succ_r; exact Hj).
        destruct (eq_nat_dec i j) as [Heq_ij | Hneq_ij].
        - subst; simpl; rewrite Rabs_R0; apply Rle_refl.
        - pose proof (H_each i j Hi_n Hj_n) as Htmp.
          destruct (eq_nat_dec i j) as [Heq' | Hneq'].
          + exfalso; exact (Hneq_ij Heq').
          + apply Htmp. }

      set (F1 i j := if eq_nat_dec i j then 0%R else (A i * A i) * delta i j).
      set (F2 i j := if eq_nat_dec i j then 0%R else (A j * A j) * delta i j).
      assert (H_sum_split : sum_f_R0 (fun i => sum_f_R0 (fun j =>
        if eq_nat_dec i j then 0%R else (A i * A i + A j * A j) / 2 * delta i j) n') n'
        = 1/2 * sum_f_R0 (fun i => sum_f_R0 (F1 i) n') n'
          + 1/2 * sum_f_R0 (fun i => sum_f_R0 (F2 i) n') n').
      {
        assert (H_inner_eq : forall i, (i <= n')%nat -> 
          sum_f_R0 (fun j : nat => if eq_nat_dec i j then 0%R else (A i * A i + A j * A j) / 2 * delta i j) n'
          = 1/2 * sum_f_R0 (F1 i) n' + 1/2 * sum_f_R0 (F2 i) n').
        {
          intros i Hi.
          assert (H_eq_j : forall j, (j <= n')%nat -> 
            (if eq_nat_dec i j then 0%R else (A i * A i + A j * A j) / 2 * delta i j)
            = 1/2 * (if eq_nat_dec i j then 0%R else (A i * A i) * delta i j) +
              1/2 * (if eq_nat_dec i j then 0%R else (A j * A j) * delta i j)).
          { intros j Hj; destruct (eq_nat_dec i j); subst; simpl; field; lra. }
          rewrite (sum_f_R0_ext _ (fun j => 1/2 * (if eq_nat_dec i j then 0%R else (A i * A i) * delta i j) +
                                          1/2 * (if eq_nat_dec i j then 0%R else (A j * A j) * delta i j)) n').
          - rewrite sum_f_R0_add.
            do 2 rewrite sum_f_R0_scal_l.
            reflexivity.
          - intros j Hj; apply H_eq_j; lia.
        }
        rewrite (sum_f_R0_ext
                   (fun i : nat => sum_f_R0 (fun j : nat => if eq_nat_dec i j then 0%R else (A i * A i + A j * A j) / 2 * delta i j) n')
                   (fun i : nat => 1/2 * sum_f_R0 (F1 i) n' + 1/2 * sum_f_R0 (F2 i) n')
                   n'
                   (fun i Hi => H_inner_eq i Hi)).
        rewrite sum_f_R0_add.
        do 2 rewrite sum_f_R0_scal_l.
        reflexivity.
      }
      rewrite H_sum_split in H_sum.

      assert (H_F1_F2 : sum_f_R0 (fun i => sum_f_R0 (F1 i) n') n'
                      = sum_f_R0 (fun i => sum_f_R0 (F2 i) n') n').
      {
        unfold F1, F2.
        rewrite (sum_f_R0_swap n' n' (fun i j => if eq_nat_dec i j then 0%R else (A j * A j) * delta i j)).
        apply sum_f_R0_ext; intros i Hi.
        apply sum_f_R0_ext; intros j Hj.
        destruct (eq_nat_dec j i) as [Hji|Hji].
        - destruct (eq_nat_dec i j) as [Heq1|Hneq]; [|exfalso; apply Hneq; symmetry; exact Hji].
          subst; reflexivity.
        - destruct (eq_nat_dec i j) as [Heq1|Hneq].
          + subst; exfalso; apply Hji; reflexivity.
          + assert (Hi_n : (i < S n')%nat) by (apply Nat.lt_succ_r; exact Hi).
            assert (Hj_n : (j < S n')%nat) by (apply Nat.lt_succ_r; exact Hj).
            rewrite (Hdelta_sym i j Hi_n Hj_n).
            reflexivity.
      }
      rewrite H_F1_F2 in H_sum.
      replace (1/2 * sum_f_R0 (fun i => sum_f_R0 (F2 i) n') n'
               + 1/2 * sum_f_R0 (fun i => sum_f_R0 (F2 i) n') n')
        with (sum_f_R0 (fun i => sum_f_R0 (F2 i) n') n') in H_sum by lra.

      unfold F2 in H_sum.
      rewrite (sum_f_R0_swap n' n' (fun i j => if eq_nat_dec i j then 0%R else (A j * A j) * delta i j)) in H_sum.

      assert (H_row_bound' : forall j : nat, (j < S n')%nat ->
        sum_f_R0 (fun i : nat => if eq_nat_dec i j then 0%R else delta i j) n' <= M_bound).
      { intros j Hj.
        pose proof (Hrow_sum j Hj) as Hrow.
        assert (Heq_sum : sum_f_R0 (fun i : nat => if eq_nat_dec i j then 0%R else delta i j) n'
                        = sum_f_R0 (fun i : nat => if eq_nat_dec j i then 0%R else delta j i) n').
        { apply sum_f_R0_ext; intros i Hi.
          assert (Hi_n : (i < S n')%nat) by (apply Nat.lt_succ_r; exact Hi).
          destruct (eq_nat_dec i j) as [Hij|Hij], (eq_nat_dec j i) as [Hji|Hji]; subst;
            try contradiction;
            try (rewrite Hdelta_sym; auto).
            lra. }
        rewrite Heq_sum; exact Hrow. }

      assert (H_sort1 : sum_f_R0 (fun j : nat => sum_f_R0 (fun i : nat => if eq_nat_dec i j then 0%R else (A j * A j) * delta i j) n') n'
                       <= sum_f_R0 (fun j : nat => (A j * A j) * M_bound) n').
      {
        apply sum_f_R0_le_compat; intros j Hj.
        assert (Hj_n' : (j < S n')%nat) by (apply Nat.lt_succ_r; exact Hj).
        set (g := fun i : nat => if eq_nat_dec i j then 0%R else delta i j).
        assert (Heq1 : sum_f_R0 (fun i : nat => if eq_nat_dec i j then 0%R else (A j * A j) * delta i j) n'
                     = sum_f_R0 (fun i : nat => (A j * A j) * g i) n').
        { apply sum_f_R0_ext; intros i Hi; unfold g; destruct (eq_nat_dec i j); ring. }
        rewrite Heq1.
        rewrite sum_f_R0_scal_l.
        apply Rmult_le_compat_l; [apply Rle_0_sqr | apply H_row_bound'; exact Hj_n'].
      }

      assert (H_sort2 : sum_f_R0 (fun j : nat => A j * A j * M_bound) n' = M_bound * DiagSum).
      {
        replace (sum_f_R0 (fun j : nat => A j * A j * M_bound) n')
           with (sum_f_R0 (fun j : nat => M_bound * (A j * A j)) n').
        - rewrite sum_f_R0_scal_l.
          unfold DiagSum.
          apply f_equal, sum_f_R0_ext; intros j Hj.
          unfold A. rewrite <- (Cnorm_sq_rsqr_sqrt (c j)). reflexivity.
        - apply sum_f_R0_ext; intros j Hj; ring.
      }

      eapply Rle_trans; [apply H_sum |].
      eapply Rle_trans; [apply H_sort1 |].
      rewrite H_sort2; apply Rle_refl.
    }

    assert (H_off_range : off <= M_bound * DiagSum /\ - M_bound * DiagSum <= off). {
      destruct (Rle_or_lt off 0) as [Hle | Hgt].
      - rewrite Rabs_left1 in H_off_bound by exact Hle; split; lra.
      - rewrite Rabs_right in H_off_bound by lra; split; lra. }
    destruct H_off_range as [Hoff1 Hoff2].
    split; lra.
Qed.

(* 定理：抽象无条件基 *)
Theorem abstract_unconditional_basis :
  forall (n : nat) (phi : nat -> nat -> Complex) (M : nat) (M_bound : R) (delta : nat -> nat -> R),
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
          if eq_nat_dec i j then 0%R else delta i j) (Nat.pred n) <= M_bound) ->
    forall (coeffs : list Complex),
      length coeffs = n ->
      let F := fun k : nat =>
        independent.Csum (fun i : nat => nth i coeffs ComplexNumbers.C0 *c phi i k) n in
      let S := sum_f_R0 (fun i : nat => ComplexNumbers.Cnorm_sq (nth i coeffs ComplexNumbers.C0)) (Nat.pred n) in
      ((1 - M_bound) * S <= l2_norm_sq F (Nat.pred M) <= (1 + M_bound) * S)%R.
Proof.
  intros n phi M M_bound delta HMpos Hzera Hnorm1 Hdelta_sym Hdelta_nonneg Hdecay Hrow_sum coeffs Hlen.
  set (M_pred := Nat.pred M).
  set (n_pred := Nat.pred n).
  set (c i := nth i coeffs ComplexNumbers.C0).
  set (inner i j := independent.Csum (fun k : nat => phi i k *c ComplexNumbers.Cconj (phi j k)) M_pred).

  assert (lt_pred_l' : forall (i m : nat), (0 < m)%nat -> (i < Nat.pred m)%nat -> (i < m)%nat).
  { intros; lia. }

  assert (Rabs_sum_f_R0 : forall (f : nat -> R) N, Rabs (sum_f_R0 f N) <= sum_f_R0 (fun i => Rabs (f i)) N).
  { induction N; simpl.
    - apply Rle_refl.
    - eapply Rle_trans; [apply Rabs_triang | apply Rplus_le_compat; [apply IHN | apply Rle_refl]]. }

  assert (Rabs_re_le_Cnorm : forall z : Complex, Rabs (re z) <= Cnorm z).
  { intro z; destruct z as [x y]; unfold re, Cnorm, Cnorm_sq; simpl.
    rewrite <- (sqrt_Rsqr_abs x) at 1; apply sqrt_le_1_c;
      [apply Rle_0_sqr | apply Rplus_le_le_0_compat; apply Rle_0_sqr | unfold Rsqr; nra]. }

  assert (H_inner_self : forall i : nat, (i < n)%nat -> inner i i = ComplexNumbers.C1).
  { intros i Hi.
    unfold inner.
    assert (Heq1 : independent.Csum (fun k : nat => phi i k *c ComplexNumbers.Cconj (phi i k)) M_pred
                  = independent.Csum (fun k : nat => Cof_real (ComplexNumbers.Cnorm_sq (phi i k))) M_pred). {
      apply Csum_ext'. intros k Hk. rewrite <- Cnorm_sq_Cof_real. reflexivity. }
    rewrite Heq1.
    assert (Heq2 : independent.Csum (fun k : nat => Cof_real (ComplexNumbers.Cnorm_sq (phi i k))) M_pred
                  = independent.Csum (fun k : nat => Cof_real (ComplexNumbers.Cnorm_sq (phi i k))) M). {
      symmetry. apply Csum_trunc_tail with (M := M_pred) (N := M).
      - lia.
      - intros k [Hk1 Hk2].
        rewrite (Hzera i k) by (exact Hi || lia).
        unfold Cof_real, ComplexNumbers.Cnorm_sq, ComplexNumbers.C0; simpl.
        rewrite !Rsqr_0, Rplus_0_r; reflexivity. }
    rewrite Heq2.
    replace M with (S M_pred) by lia.
    rewrite <- (Cof_real_sum (fun k => Cnorm_sq (phi i k)) M_pred).
    specialize (Hnorm1 i Hi).
    apply (f_equal Cof_real) in Hnorm1.
    simpl in Hnorm1.
    exact Hnorm1. }

  assert (Hinner_eq_M : forall i j, (i < n)%nat -> (j < n)%nat ->
    independent.Csum (fun k : nat => phi i k *c ComplexNumbers.Cconj (phi j k)) M = inner i j).
  { intros i0 j0 Hi Hj.
    unfold inner. apply Csum_trunc_tail with (M := M_pred) (N := M); [lia|].
    intros k [Hk1 Hk2]. assert (k = M_pred) by lia; subst k.
    rewrite (Hzera i0 M_pred Hi (le_refl M_pred)).
    apply C0_mul_eq_C0. }

  simpl.
  pose proof (l2_norm_sq_rewrite_full n phi M HMpos coeffs Hlen Hzera) as H_rewrite.
  cbv beta zeta in H_rewrite.
  fold M_pred n_pred in H_rewrite.

  eapply off_diagonal_estimate; eauto.
  reflexivity.
Qed.

(* ============================================================
   定理：二维张量积基的无条件基性质（稀疏条件下）
   整合 A / B 版设计，修正常数并补全所有缺失引理。
   ============================================================ *)

(** * 辅助定义：一维衰减因子 *)
Definition d_factor (r : R) (i j : nat) : R :=
  if i =? j then 1 else 2 / (r ^ Z.abs_nat (Z.of_nat i - Z.of_nat j)).

(** * 实数部分和截断引理（库中可能有，此处显式给出） *)
Lemma sum_f_R0_trunc_tail (f : nat -> R) (M N : nat) :
  (M <= N)%nat ->
  (forall k : nat, (M <= k <= N)%nat -> f k = 0%R) ->
  sum_f_R0 f N = sum_f_R0 f M.
Proof.
  intros Hle Hz.
  induction N as [|N IH] in M, Hle, Hz |- *.
  - assert (M = 0)%nat by lia; subst; reflexivity.
  - assert (Hz' : forall k : nat, (M <= k <= N)%nat -> f k = 0%R).
    { intros k Hk; apply Hz; lia. }
    destruct (Nat.eq_dec M (S N)) as [Heq|Hne].
    + subst; reflexivity.
    + assert (M <= N)%nat by lia.
      specialize (IH M H Hz').
      rewrite sum_f_R0_S.  (* sum_f_R0 f (S N) = sum_f_R0 f N + f (S N) *)
      rewrite IH.
      assert (HfSN : f (S N) = 0%R) by (apply Hz; lia).
      rewrite HfSN; ring.
Qed.

(** * psi 范数平方的精确公式 *)
Lemma Cnorm_sq_psi_exact (n k : nat) :
  Cnorm_sq (psi n k) = if Nat.ltb k n then 1 / INR n else 0%R.
Proof.
  unfold psi.
  rewrite Cnorm_sq_mult.
  assert (Hcof_sq : Cnorm_sq (Cof_real (1 / sqrt (INR n))) = (1 / sqrt (INR n)) * (1 / sqrt (INR n))).
  { unfold Cof_real, Cnorm_sq, Rsqr; simpl; ring. }
  rewrite Hcof_sq.
  case_eq (k <? n)%nat; intros Hcase.
  - (* k < n *)
    apply Nat.ltb_lt in Hcase.
    rewrite Cnorm_sq_phi by exact Hcase.
    rewrite Rmult_1_r.
    unfold Rdiv; rewrite !Rmult_1_l.
    assert (Hsqrtnz : sqrt (INR n) <> 0%R).
    { apply Rgt_not_eq, sqrt_lt_R0_c, lt_0_INR; lia. }
    assert (Hinv : / (sqrt (INR n) * sqrt (INR n)) = / sqrt (INR n) * / sqrt (INR n)).
    { apply Rinv_mult; exact Hsqrtnz. }
    rewrite <- Hinv.
    rewrite sqrt_sqrt.
    + reflexivity.
    + apply Rlt_le; apply lt_0_INR; lia.
  - (* k >= n *)
    apply Nat.ltb_ge in Hcase.
    rewrite (phi_ge_n_zero n k Hcase).
    replace (Cnorm_sq C0) with 0%R.
    + ring.
    + unfold Cnorm_sq, C0; simpl; rewrite Rsqr_0, Rplus_0_l; reflexivity.
Qed.

(** 双根号乘积和的上界 *)
Lemma double_sqrt_mul_le_add (x y u v : R) :
  0 <= x -> 0 <= y -> 0 <= u -> 0 <= v ->
  2 * sqrt (x * y) * sqrt (u * v) <= x * v + u * y.
Proof.
  intros Hx Hy Hu Hv.
  set (A := sqrt (x * v)).
  set (B := sqrt (u * y)).
  assert (HA2 : A * A = x * v).
  { unfold A; rewrite sqrt_sqrt; [reflexivity | apply Rmult_le_pos; auto]. }
  assert (HB2 : B * B = u * y).
  { unfold B; rewrite sqrt_sqrt; [reflexivity | apply Rmult_le_pos; auto]. }
  assert (HAB : A * B = sqrt (x * y) * sqrt (u * v)).
  {
    unfold A, B.
    rewrite (sqrt_mult x v Hx Hv).
    rewrite (sqrt_mult u y Hu Hy).
    rewrite (sqrt_mult x y Hx Hy).
    rewrite (sqrt_mult u v Hu Hv).
    ring.
  }
  assert (Hsq : 0 <= (A - B) * (A - B)) by apply Rle_0_sqr.
  unfold Rsqr in Hsq |- *; lra.
Qed.

(** 非负函数部分和的非负性 *)
Lemma sum_f_R0_nonneg (f : nat -> R) (N : nat) :
  (forall i, 0 <= f i) -> 0 <= sum_f_R0 f N.
Proof.
  induction N as [|N IH]; simpl; intros Hf.
  - apply Hf.
  - apply Rplus_le_le_0_compat; [apply (IH Hf) | apply Hf].
Qed.

(** 共轭复数范数平方不变性 *)
Lemma Cnorm_sq_conj (z : Complex) : Cnorm_sq (Cconj z) = Cnorm_sq z.
Proof.
  unfold Cnorm_sq, Cconj; simpl.
  rewrite (Rsqr_neg (im z)).
  reflexivity.
Qed.

(* 非负函数部分和单调递增 *)
Lemma sum_f_R0_le_nonneg (f : nat -> R) (n m : nat) :
  (forall i, 0 <= f i) ->
  (n <= m)%nat ->
  sum_f_R0 f n <= sum_f_R0 f m.
Proof.
  intros Hf Hle.
  induction Hle as [| m Hle IH].
  - apply Rle_refl.
  - rewrite sum_f_R0_S.
    apply Rle_trans with (sum_f_R0 f m); [exact IH |].
    rewrite <- (Rplus_0_r (sum_f_R0 f m)) at 1.
    apply Rplus_le_compat_l.
    apply Hf.
Qed.

(* 非负函数部分和前驱不大于原和 *)
Lemma sum_f_R0_pred_le (f : nat -> R) (N : nat) :
  (forall i, 0 <= f i) ->
  sum_f_R0 f (N - 1) <= sum_f_R0 f N.
Proof.
  intros Hf.
  destruct N as [|N'].
  - simpl; apply Rle_refl.
  - apply sum_f_R0_le_nonneg; auto; lia.
Qed.

(* 定理：复序列部分和柯西-施瓦茨不等式 *)
Theorem CauchySchwarz_sum_f_R0 (A B : nat -> Complex) (N : nat) :
  (Cnorm_sq (Csum (fun k => A k *c Cconj (B k)) N) <=
   sum_f_R0 (fun k => Cnorm_sq (A k)) N *
   sum_f_R0 (fun k => Cnorm_sq (B k)) N)%R.
Proof.
  assert (Hstrong : forall n, Cnorm_sq (Csum (fun k => A k *c Cconj (B k)) n) <=
                             sum_f_R0 (fun k => Cnorm_sq (A k)) (Nat.pred n) *
                             sum_f_R0 (fun k => Cnorm_sq (B k)) (Nat.pred n)).
  { induction n as [|n IH].
    - simpl Csum. rewrite Cnorm_sq_zero. simpl. apply Rmult_le_pos; apply Cnorm_sq_ge_0.
    - rewrite Csum_S.
      set (x := Csum (fun k : nat => A k *c Cconj (B k)) n).
      set (y := A n *c Cconj (B n)).
      rewrite Cnorm_sq_add.
      assert (Hxy_re : re (x *c Cconj y) = re x * re y + im x * im y).
      { destruct x as [x1 x2]; destruct y as [y1 y2];
        unfold re, im, Cconj, Cmul; simpl; ring. }
      rewrite <- Hxy_re.
      assert (Hre_ineq : re (x *c Cconj y) <= Cnorm x * Cnorm y).
      { rewrite Hxy_re; apply CauchySchwarz_complex. }
      assert (H_main_ineq : Cnorm_sq x + Cnorm_sq y + 2 * re (x *c Cconj y) <=
                           Cnorm_sq x + Cnorm_sq y + 2 * Cnorm x * Cnorm y).
      { lra. }
      apply Rle_trans with (Cnorm_sq x + Cnorm_sq y + 2 * Cnorm x * Cnorm y).
      { exact H_main_ineq. }
      simpl (Nat.pred (S n)).
      set (a := Cnorm_sq (A n)).
      set (b := Cnorm_sq (B n)).
      assert (Hy_sq : Cnorm_sq y = a * b).
      { unfold y, a, b; rewrite Cnorm_sq_mult, Cnorm_sq_conj; reflexivity. }
      rewrite Hy_sq.
      assert (H_Cnorm_x : Cnorm x = sqrt (Cnorm_sq x))
        by (unfold Cnorm; reflexivity).
      assert (H_Cnorm_y : Cnorm y = sqrt (Cnorm_sq y))
        by (unfold Cnorm; reflexivity).
      rewrite H_Cnorm_y, Hy_sq, H_Cnorm_x.
      destruct n as [|n'].
      + unfold x; simpl Csum; rewrite Cnorm_sq_zero, sqrt_0.
        unfold a, b; simpl; ring_simplify; apply Rle_refl.
      + set (X := sum_f_R0 (fun k : nat => Cnorm_sq (A k)) n').
        set (Y := sum_f_R0 (fun k : nat => Cnorm_sq (B k)) n').
        assert (Hx_sq : Cnorm_sq x <= X * Y).
        { unfold x, X, Y; exact IH. }
        assert (H_sqrt_ineq : 2 * sqrt (Cnorm_sq x) * sqrt (a * b) <= X * b + a * Y).
        {
          assert (H_nonneg_X : 0 <= X) by (apply sum_f_R0_nonneg; intro; apply Cnorm_sq_ge_0).
          assert (H_nonneg_Y : 0 <= Y) by (apply sum_f_R0_nonneg; intro; apply Cnorm_sq_ge_0).
          assert (H_nonneg_a : 0 <= a) by (unfold a; apply Cnorm_sq_ge_0).
          assert (H_nonneg_b : 0 <= b) by (unfold b; apply Cnorm_sq_ge_0).
          assert (H_sq_ineq : Cnorm_sq x <= X * Y) by exact Hx_sq.
          assert (H_prod_nonneg : 0 <= X * Y) by (apply Rmult_le_pos; auto).
          assert (H_sqrt_le : sqrt (Cnorm_sq x) <= sqrt (X * Y)).
          { apply sqrt_le_1_c; auto; apply Cnorm_sq_ge_0. }
          assert (H_nonneg_sqrt_ab : 0 <= sqrt (a * b)).
          { apply sqrt_pos_nonneg; apply Rmult_le_pos; auto. }
          assert (H_inter : 2 * sqrt (Cnorm_sq x) * sqrt (a * b) <= 2 * sqrt (X * Y) * sqrt (a * b)).
          { nra. }
          assert (H_main : 2 * sqrt (X * Y) * sqrt (a * b) <= X * b + a * Y).
          { apply double_sqrt_mul_le_add; auto. }
          nra.
        }
        rewrite (sum_f_R0_S (fun k : nat => Cnorm_sq (A k)) n').
        rewrite (sum_f_R0_S (fun k : nat => Cnorm_sq (B k)) n').
        fold X Y a b.
        apply Rle_trans with (X * Y + a * b + (X * b + a * Y)).
        - apply Rplus_le_compat; [apply Rplus_le_compat; [exact Hx_sq | apply Rle_refl] | exact H_sqrt_ineq].
        - replace ((X + a) * (Y + b)) with (X * Y + a * b + (X * b + a * Y)) by ring.
          apply Rle_refl.
  }
  destruct N as [|N].
  - apply Hstrong.
  - apply Rle_trans with
      (sum_f_R0 (fun k => Cnorm_sq (A k)) (Nat.pred (S N)) *
       sum_f_R0 (fun k => Cnorm_sq (B k)) (Nat.pred (S N))).
    + apply Hstrong.
    + replace (Nat.pred (S N)) with N by lia.
      rewrite !(sum_f_R0_S _ N).
      assert (HA_low : 0 <= sum_f_R0 (fun k : nat => Cnorm_sq (A k)) N)
        by (apply sum_f_R0_nonneg; intro; apply Cnorm_sq_ge_0).
      assert (HA_up : sum_f_R0 (fun k : nat => Cnorm_sq (A k)) N <=
                     sum_f_R0 (fun k : nat => Cnorm_sq (A k)) N + Cnorm_sq (A (S N))).
      { assert (Htemp : sum_f_R0 (fun k : nat => Cnorm_sq (A k)) N + 0 <=
                       sum_f_R0 (fun k : nat => Cnorm_sq (A k)) N + Cnorm_sq (A (S N))).
        { apply Rplus_le_compat_l, Cnorm_sq_ge_0. }
        rewrite Rplus_0_r in Htemp.
        exact Htemp. }
      assert (HB_low : 0 <= sum_f_R0 (fun k : nat => Cnorm_sq (B k)) N)
        by (apply sum_f_R0_nonneg; intro; apply Cnorm_sq_ge_0).
      assert (HB_up : sum_f_R0 (fun k : nat => Cnorm_sq (B k)) N <=
                     sum_f_R0 (fun k : nat => Cnorm_sq (B k)) N + Cnorm_sq (B (S N))).
      { assert (Htemp : sum_f_R0 (fun k : nat => Cnorm_sq (B k)) N + 0 <=
                       sum_f_R0 (fun k : nat => Cnorm_sq (B k)) N + Cnorm_sq (B (S N))).
        { apply Rplus_le_compat_l, Cnorm_sq_ge_0. }
        rewrite Rplus_0_r in Htemp.
        exact Htemp. }
      apply (Rmult_le_compat
               (sum_f_R0 (fun k : nat => Cnorm_sq (A k)) N)
               (sum_f_R0 (fun k : nat => Cnorm_sq (A k)) N + Cnorm_sq (A (S N)))
               (sum_f_R0 (fun k : nat => Cnorm_sq (B k)) N)
               (sum_f_R0 (fun k : nat => Cnorm_sq (B k)) N + Cnorm_sq (B (S N))));
        [ exact HA_low | exact HB_low | exact HA_up | exact HB_up ].
Qed.

(* 定理：乘积内积简化 *)
Theorem product_psi_inner_decomposition (a1 a2 b1 b2 : nat) (g : nat -> nat -> R) :
  let M := S (max (max a1 b1) (max a2 b2)) in
  let N := Nat.pred M in
  let N0 := Nat.min (Nat.min a1 a2) (Nat.min b1 b2) in
  Csum (fun k => (Cof_real (/ g a1 b1) *c (psi a1 k *c psi b1 k)) *c
                Cconj (Cof_real (/ g a2 b2) *c (psi a2 k *c psi b2 k))) N
  = Cof_real (/ (g a1 b1 * g a2 b2)) *c
    Csum (fun k => (psi a1 k *c Cconj (psi a2 k)) *c (psi b1 k *c Cconj (psi b2 k))) N0.
Proof.
  intros M N N0.
  assert (HN0 : (N0 <= N)%nat) by (unfold N0, N, M; lia).
  assert (Htrunc : Csum (fun k => (Cof_real (/ g a1 b1) *c (psi a1 k *c psi b1 k)) *c
                         Cconj (Cof_real (/ g a2 b2) *c (psi a2 k *c psi b2 k))) N
                  = Csum (fun k => (Cof_real (/ g a1 b1) *c (psi a1 k *c psi b1 k)) *c
                         Cconj (Cof_real (/ g a2 b2) *c (psi a2 k *c psi b2 k))) N0).
  {
    apply (Csum_trunc_tail
             (fun k => (Cof_real (/ g a1 b1) *c (psi a1 k *c psi b1 k)) *c
                      Cconj (Cof_real (/ g a2 b2) *c (psi a2 k *c psi b2 k))) N0 N).
    - exact HN0.
    - intros k [Hk1 Hk2].
      assert (Hk_ge_N0 : (k >= N0)%nat) by lia.
      destruct (Nat.min_spec (Nat.min a1 a2) (Nat.min b1 b2)) as [[Hle_min Hmin] | [Hle_min Hmin]].
      * destruct (Nat.min_spec a1 a2) as [[Hle_a Hmin_a] | [Hle_a Hmin_a]].
        + assert (Hk_ge_a1 : (k >= a1)%nat) by (unfold N0 in Hk_ge_N0; rewrite Hmin, Hmin_a in Hk_ge_N0; exact Hk_ge_N0).
          rewrite (psi_ge_n_zero a1 k Hk_ge_a1).
          apply Complex_eq; simpl; ring.
        + assert (Hk_ge_a2 : (k >= a2)%nat) by (unfold N0 in Hk_ge_N0; rewrite Hmin, Hmin_a in Hk_ge_N0; exact Hk_ge_N0).
          rewrite (psi_ge_n_zero a2 k Hk_ge_a2).
          apply Complex_eq; simpl; ring.
      * destruct (Nat.min_spec b1 b2) as [[Hle_b Hmin_b] | [Hle_b Hmin_b]].
        + assert (Hk_ge_b1 : (k >= b1)%nat) by (unfold N0 in Hk_ge_N0; rewrite Hmin, Hmin_b in Hk_ge_N0; exact Hk_ge_N0).
          rewrite (psi_ge_n_zero b1 k Hk_ge_b1).
          apply Complex_eq; simpl; ring.
        + assert (Hk_ge_b2 : (k >= b2)%nat) by (unfold N0 in Hk_ge_N0; rewrite Hmin, Hmin_b in Hk_ge_N0; exact Hk_ge_N0).
          rewrite (psi_ge_n_zero b2 k Hk_ge_b2).
          apply Complex_eq; simpl; ring.
  }
  rewrite Htrunc; unfold N0.

  set (A k := psi a1 k *c psi b1 k).
  set (B k := psi a2 k *c psi b2 k).
  set (c1 := Cof_real (/ g a1 b1)).
  set (c2 := Cof_real (/ g a2 b2)).
  assert (H_simpl : forall k, (c1 *c A k) *c Cconj (c2 *c B k) = 
                    Cof_real (/ (g a1 b1 * g a2 b2)) *c
                    (psi a1 k *c Cconj (psi a2 k)) *c
                    (psi b1 k *c Cconj (psi b2 k))).
  {
    intros k. unfold c1, c2, A, B.
    assert (Cconj_mul : forall a b, Cconj (a *c b) = Cconj a *c Cconj b) by (intros; apply Complex_eq; simpl; ring).
    rewrite Cconj_mul.
    assert (Cconj_Cof_real : forall r : R, Cconj (Cof_real r) = Cof_real r) by (intros r; apply Complex_eq; simpl; ring).
    rewrite Cconj_Cof_real.
    rewrite (Cconj_mul (psi a2 k) (psi b2 k)).
    assert (Cmul_swap_middle : forall (a b c d : Complex), a *c b *c (c *c d) = a *c c *c (b *c d)).
    {
      intros a0 b0 c0 d0.
      rewrite (Cmul_assoc a0 b0 (c0 *c d0)).
      rewrite <- (Cmul_assoc b0 c0 d0).
      rewrite (Cmul_comm b0 c0).
      rewrite (Cmul_assoc c0 b0 d0).
      rewrite <- (Cmul_assoc a0 c0 (b0 *c d0)).
      reflexivity.
    }
    rewrite (Cmul_swap_middle (Cof_real (/ g a1 b1)) (psi a1 k *c psi b1 k)
                             (Cof_real (/ g a2 b2)) (Cconj (psi a2 k) *c Cconj (psi b2 k))).
    assert (Hcoeff_eq : Cof_real (/ g a1 b1) *c Cof_real (/ g a2 b2) = Cof_real (/ (g a1 b1 * g a2 b2))).
    {
      apply Complex_eq; simpl.
      - destruct (Req_dec (g a1 b1) 0) as [Hz1|Hz1];
        destruct (Req_dec (g a2 b2) 0) as [Hz2|Hz2].
        * rewrite Hz1, Hz2.
          replace (0 * 0) with 0 by ring.
          rewrite Rinv_0; ring.
        * rewrite Hz1, Rinv_0.
          rewrite Rmult_0_l, Rmult_0_r, Rminus_0_r.
          rewrite Rmult_0_l.
          rewrite Rinv_0; reflexivity.
        * rewrite Hz2, Rinv_0.
          rewrite Rmult_0_l, Rmult_0_r, Rminus_0_r.
          rewrite Rmult_0_r.
          rewrite Rinv_0; reflexivity.
        * rewrite <- Rinv_mult; ring.
      - ring.
    }
    rewrite Hcoeff_eq.
    rewrite (Cmul_swap_middle (psi a1 k) (psi b1 k) (Cconj (psi a2 k)) (Cconj (psi b2 k))).
    rewrite <- (Cmul_assoc (Cof_real (/ (g a1 b1 * g a2 b2)))
                         (psi a1 k *c Cconj (psi a2 k))
                         (psi b1 k *c Cconj (psi b2 k))).
    reflexivity.
  }

  assert (Hsum_eq : Csum (fun k => (c1 *c A k) *c Cconj (c2 *c B k))
                          (Nat.min (Nat.min a1 a2) (Nat.min b1 b2))
                  = Cof_real (/ (g a1 b1 * g a2 b2)) *c
                    Csum (fun k => (psi a1 k *c Cconj (psi a2 k)) *c
                                   (psi b1 k *c Cconj (psi b2 k)))
                          (Nat.min (Nat.min a1 a2) (Nat.min b1 b2))).
  {
    set (n := Nat.min (Nat.min a1 a2) (Nat.min b1 b2)).
    assert (Htmp : Csum (fun k => (c1 *c A k) *c Cconj (c2 *c B k)) n =
                   Csum (fun k => Cof_real (/ (g a1 b1 * g a2 b2)) *c
                                   ((psi a1 k *c Cconj (psi a2 k)) *c
                                    (psi b1 k *c Cconj (psi b2 k)))) n).
    {
      apply Csum_ext'; intros i Hi.
      rewrite (H_simpl i).
      rewrite (Cmul_assoc (Cof_real (/ (g a1 b1 * g a2 b2)))
                         (psi a1 i *c Cconj (psi a2 i))
                         (psi b1 i *c Cconj (psi b2 i))).
      reflexivity.
    }
    rewrite Htmp.

    assert (Csum_scal_l : forall (c0 : Complex) (f0 : nat -> Complex) (n0 : nat),
      Csum (fun k => c0 *c f0 k) n0 = c0 *c Csum f0 n0).
    {
      intros c0 f0 n0.
      induction n0 as [| n0' IH]; simpl.
      - rewrite Cmul_0_r; reflexivity.
      - rewrite IH.
        rewrite Cmul_add_distr_l.
        reflexivity.
    }
    rewrite (Csum_scal_l (Cof_real (/ (g a1 b1 * g a2 b2)))
                         (fun k : nat => (psi a1 k *c Cconj (psi a2 k)) *c
                                        (psi b1 k *c Cconj (psi b2 k)))
                         n).
    reflexivity.
  }
  apply Hsum_eq.
Qed.

(* psi 共轭乘积的复指数分解 *)
Lemma psi_conj_prod_eq_coef_exp (a1 a2 k : nat) (Δ1 : R) :
  (k < a1)%nat -> (k < a2)%nat ->
  INR a1 > 0 -> INR a2 > 0 ->
  Δ1 = 2 * PI * (/ INR a1 - / INR a2) ->
  psi a1 k *c Cconj (psi a2 k) = Cof_real (/ sqrt (INR a1 * INR a2)) *c Cexp (0 +i (INR k * Δ1)).
Proof.
  intros Hk_a1 Hk_a2 Ha1pos Ha2pos HΔ1.
  assert (Cof_real_mul : forall r1 r2 : R, Cof_real r1 *c Cof_real r2 = Cof_real (r1 * r2)).
  { intros r1 r2; unfold Cof_real, Cmul; simpl; apply Complex_eq; simpl; ring. }

  unfold psi, UnconditionalBasis.phi.
  rewrite (proj2 (Nat.ltb_lt k a1) Hk_a1).
  rewrite (proj2 (Nat.ltb_lt k a2) Hk_a2).
  simpl.
  set (c1 := Cof_real (1 / sqrt (INR a1))).
  set (c2 := Cof_real (1 / sqrt (INR a2))).
  set (e1 := Cexp (0 +i (2 * PI * INR k / INR a1))).
  set (e2 := Cexp (0 +i (2 * PI * INR k / INR a2))).

  assert (Cconj_mul : forall a b, Cconj (a *c b) = Cconj a *c Cconj b).
  { intros [x1 y1] [x2 y2]; apply Complex_eq; simpl; ring. }
  assert (Cconj_Cof_real : forall r : R, Cconj (Cof_real r) = Cof_real r).
  { intros r; unfold Cof_real, Cconj; simpl; apply Complex_eq; simpl; ring. }
  assert (He1e2 : e1 *c Cconj e2 = Cexp (0 +i (INR k * Δ1))).
  {
    unfold e2; rewrite Cconj_Cexp.
    unfold e1; rewrite HΔ1.
    rewrite <- Cexp_add.
    apply f_equal.
    apply Complex_eq; simpl.
    - ring.
    - field; split; [apply Rgt_not_eq; exact Ha2pos | apply Rgt_not_eq; exact Ha1pos].
  }
  assert (Hc1c2 : c1 *c c2 = Cof_real (/ sqrt (INR a1 * INR a2))).
  {
    unfold c1, c2.
    rewrite Cof_real_mul.
    f_equal.
    rewrite (sqrt_mult (INR a1) (INR a2) (Rlt_le _ _ Ha1pos) (Rlt_le _ _ Ha2pos)).
    field; split; apply Rgt_not_eq; apply sqrt_lt_R0_c; assumption.
  }

  rewrite (Cmul_assoc c1 e1 (Cconj (c2 *c e2))).
  rewrite Cconj_mul.
  assert (Hc2conj : Cconj c2 = c2) by (unfold c2; apply Cconj_Cof_real).
  rewrite Hc2conj.
  rewrite <- (Cmul_assoc e1 c2 (Cconj e2)).
  rewrite (Cmul_comm e1 c2).
  rewrite (Cmul_assoc c2 e1 (Cconj e2)).
  rewrite <- (Cmul_assoc c1 c2 (e1 *c Cconj e2)).
  rewrite Hc1c2, He1e2.
  reflexivity.
Qed.

(* psi 乘积内积的几何级数展开 *)
Lemma psi_product_inner_geom_expansion (a1 a2 b1 b2 N0 : nat) (Δ : R)
  (HΔ : Δ = 2 * PI * (/ INR a1 - / INR a2) + 2 * PI * (/ INR b1 - / INR b2))
  (Ha1 : (N0 <= a1)%nat) (Ha2 : (N0 <= a2)%nat) (Hb1 : (N0 <= b1)%nat) (Hb2 : (N0 <= b2)%nat)
  (Ha1pos : (a1 > 0)%nat) (Ha2pos : (a2 > 0)%nat) (Hb1pos : (b1 > 0)%nat) (Hb2pos : (b2 > 0)%nat)
  : Csum (fun k => (psi a1 k *c Cconj (psi a2 k)) *c (psi b1 k *c Cconj (psi b2 k))) N0
    = Cof_real (/ sqrt (INR a1 * INR a2 * INR b1 * INR b2)) *c
      Csum (fun k => Cexp (0 +i (INR k * Δ))) N0.
Proof.
  assert (Cof_real_mul : forall r1 r2 : R, Cof_real r1 *c Cof_real r2 = Cof_real (r1 * r2)).
  { intros; unfold Cof_real, Cmul; simpl; apply Complex_eq; simpl; ring. }

  assert (Hk_bounds : forall k, (k < N0)%nat -> (k < a1)%nat /\ (k < a2)%nat /\ (k < b1)%nat /\ (k < b2)%nat).
  { intros k Hk; split; [|split; [|split]]; lia. }

  set (Δ1 := 2 * PI * (/ INR a1 - / INR a2)).
  set (Δ2 := 2 * PI * (/ INR b1 - / INR b2)).
  assert (HΔ_sum : Δ = Δ1 + Δ2) by (rewrite HΔ; unfold Δ1, Δ2; ring).

  set (F1 := fun k => psi a1 k *c Cconj (psi a2 k)).
  set (F2 := fun k => psi b1 k *c Cconj (psi b2 k)).

  set (cA := Cof_real (/ sqrt (INR a1 * INR a2))).
  set (cB := Cof_real (/ sqrt (INR b1 * INR b2))).

  assert (Csum_scal_l : forall (c : Complex) (f : nat -> Complex) (n : nat),
    Csum (fun k => c *c f k) n = c *c Csum f n).
  { intros; induction n; simpl; [rewrite Cmul_0_r; reflexivity | rewrite IHn; rewrite Cmul_add_distr_l; reflexivity]. }

  assert (INR_a1_pos : INR a1 > 0) by (apply lt_0_INR; exact Ha1pos).
  assert (INR_a2_pos : INR a2 > 0) by (apply lt_0_INR; exact Ha2pos).
  assert (INR_b1_pos : INR b1 > 0) by (apply lt_0_INR; exact Hb1pos).
  assert (INR_b2_pos : INR b2 > 0) by (apply lt_0_INR; exact Hb2pos).

  assert (Hexp_F1 : forall k, (k < N0)%nat -> F1 k = cA *c Cexp (0 +i (INR k * Δ1))).
  { intros k Hk.
    destruct (Hk_bounds k Hk) as [Hk_a1 [Hk_a2 _]].
    unfold F1, cA.
    eapply psi_conj_prod_eq_coef_exp.
    - exact Hk_a1.
    - exact Hk_a2.
    - exact INR_a1_pos.
    - exact INR_a2_pos.
    - unfold Δ1; reflexivity. }

  assert (Hexp_F2 : forall k, (k < N0)%nat -> F2 k = cB *c Cexp (0 +i (INR k * Δ2))).
  { intros k Hk.
    destruct (Hk_bounds k Hk) as [_ [_ [Hk_b1 Hk_b2]]].
    unfold F2, cB.
    eapply psi_conj_prod_eq_coef_exp.
    - exact Hk_b1.
    - exact Hk_b2.
    - exact INR_b1_pos.
    - exact INR_b2_pos.
    - unfold Δ2; reflexivity. }

  assert (H_prod : forall k, (k < N0)%nat -> F1 k *c F2 k = (cA *c cB) *c Cexp (0 +i (INR k * Δ))).
  { intros k Hk.
    rewrite Hexp_F1, Hexp_F2 by auto.
    set (E1 := Cexp (0 +i (INR k * Δ1))).
    set (E2 := Cexp (0 +i (INR k * Δ2))).
    set (E  := Cexp (0 +i (INR k * Δ))).
    rewrite Cmul_assoc.
    rewrite <- (Cmul_assoc E1 cB E2).
    rewrite (Cmul_comm E1 cB).
    rewrite (Cmul_assoc cB E1 E2).
    rewrite <- (Cmul_assoc cA cB (E1 *c E2)).
    unfold E1, E2.
    rewrite <- Cexp_add.
    replace ((0 +i (INR k * Δ1)) +c (0 +i (INR k * Δ2)))
      with (0 +i (INR k * (Δ1 + Δ2))) by (unfold Cadd; simpl; f_equal; ring).
    rewrite <- HΔ_sum.
    fold E.
    reflexivity.
  }

  rewrite (Csum_ext' _ (fun k => (cA *c cB) *c Cexp (0 +i (INR k * Δ))) N0);
    [| intros; apply H_prod; auto ].
  rewrite Csum_scal_l.

  unfold cA, cB.
  rewrite Cof_real_mul.
  f_equal.
  f_equal.
  rewrite <- Rinv_mult.
  f_equal.
  replace (INR a1 * INR a2 * INR b1 * INR b2) with ((INR a1 * INR a2) * (INR b1 * INR b2)) by ring.
  rewrite <- sqrt_mult.
  - reflexivity.
  - apply Rlt_le; apply Rmult_lt_0_compat; [exact INR_a1_pos | exact INR_a2_pos].
  - apply Rlt_le; apply Rmult_lt_0_compat; [exact INR_b1_pos | exact INR_b2_pos].
Qed.

(* 常数函数的部分和公式 *)
Lemma sum_f_R0_const (c : R) (n : nat) :
  sum_f_R0 (fun _ => c) n = c * INR (S n).
Proof.
  induction n as [| n IH].
  - simpl; ring.
  - simpl sum_f_R0 at 1.
    rewrite IH.
    rewrite !S_INR.
    ring.
Qed.

(* 截断柯西‑施瓦茨不等式 *)
Lemma CauchySchwarz_truncated (A B : nat -> Complex) (N0 : nat)
  (Hpos : (N0 > 0)%nat)
  (Hprod_N0_zero : (A N0 *c B N0)%C = C0) :
  Cnorm_sq (Csum (fun k => A k *c B k) N0) <= 
  (sum_f_R0 (fun k => Cnorm_sq (A k)) (N0 - 1)) *
  (sum_f_R0 (fun k => Cnorm_sq (B k)) (N0 - 1)).
Proof.
  set (A1 := fun k => if k =? N0 then C0 else A k).
  set (B1 := fun k => if k =? N0 then C0 else B k).

  assert (Hprod_eq : forall k, A1 k *c B1 k = A k *c B k).
  { intros k; unfold A1, B1.
    destruct (Nat.eqb_spec k N0).
    - subst k. rewrite Hprod_N0_zero. apply C0_mul_eq_C0.
    - reflexivity. }

  assert (HCseq_eq : Csum (fun k => A k *c B k) N0 =
                     Csum (fun k => A1 k *c B1 k) N0).
  { apply Csum_ext'; intros k Hk; symmetry; apply Hprod_eq. }

  pose proof (CauchySchwarz_sum_f_R0 A1 (fun k => Cconj (B1 k)) N0) as Hcs_sq.
  cbv beta in Hcs_sq.
  assert (Cconj_Cconj : forall z : Complex, Cconj (Cconj z) = z).
  { intros [x y]; unfold Cconj; apply Complex_eq; simpl; ring. }
  assert (H_left_simpl : Csum (fun k => A1 k *c Cconj (Cconj (B1 k))) N0 =
                         Csum (fun k => A k *c B k) N0).
  { rewrite Csum_ext' with (g := fun k => A1 k *c B1 k);
      [ | intros; rewrite Cconj_Cconj; reflexivity ].
    rewrite <- HCseq_eq. reflexivity. }
  rewrite H_left_simpl in Hcs_sq.

  assert (HsumA1 : sum_f_R0 (fun k => Cnorm_sq (A1 k)) N0 =
                   sum_f_R0 (fun k => Cnorm_sq (A k)) (N0 - 1)).
  { destruct N0 as [|n] eqn:HN0eq.
    - exfalso; clear -Hpos HN0eq; lia.
    - rewrite sum_f_R0_S.
      assert (Hlast : Cnorm_sq (A1 (S n)) = 0%R).
      { unfold A1; rewrite Nat.eqb_refl; apply Cnorm_sq_zero. }
      rewrite Hlast, Rplus_0_r.
      assert (Hsub : (S n - 1 = n)%nat) by lia; rewrite Hsub.
      apply sum_f_R0_ext; intros k Hk.
      unfold A1; destruct (Nat.eqb_spec k (S n));
        [subst; exfalso; lia | reflexivity]. }

  assert (HsumB1 : sum_f_R0 (fun k => Cnorm_sq (Cconj (B1 k))) N0 =
                   sum_f_R0 (fun k => Cnorm_sq (B k)) (N0 - 1)).
  { destruct N0 as [|n] eqn:HN0eq.
    - exfalso; clear -Hpos HN0eq; lia.
    - rewrite sum_f_R0_S.
      assert (Hlast : Cnorm_sq (Cconj (B1 (S n))) = 0%R).
      { unfold B1; rewrite Nat.eqb_refl.
        rewrite Cconj_0. apply Cnorm_sq_zero. }
      rewrite Hlast, Rplus_0_r.
      assert (Hsub : (S n - 1 = n)%nat) by lia; rewrite Hsub.
      apply sum_f_R0_ext; intros k Hk.
      unfold B1; destruct (Nat.eqb_spec k (S n)).
      - subst; exfalso; lia.
      - rewrite Cnorm_sq_conj. reflexivity. }
  rewrite HsumA1, HsumB1 in Hcs_sq.
  exact Hcs_sq.
Qed.

(* psi 乘积的范数平方部分和 *)
Lemma sum_sq_psi_product (n1 n2 M : nat) (HMpos : (M > 0)%nat) (HM1 : (M <= n1)%nat) (HM2 : (M <= n2)%nat) :
  sum_f_R0 (fun k => Cnorm_sq (psi n1 k *c Cconj (psi n2 k))) (M - 1) =
  INR M / (INR n1 * INR n2).
Proof.
  destruct M as [|m]; [exfalso; lia|].
  assert (Haux : forall k, (k < S m)%nat ->
    Cnorm_sq (psi n1 k *c Cconj (psi n2 k)) = 1 / (INR n1 * INR n2)).
  { intros k Hk.
    rewrite Cnorm_sq_mult, Cnorm_sq_conj.
    rewrite !Cnorm_sq_psi_exact.
    assert (Hk1 : (k < n1)%nat) by (apply Nat.lt_le_trans with (S m); lia).
    assert (Hk2 : (k < n2)%nat) by (apply Nat.lt_le_trans with (S m); lia).
    rewrite (proj2 (Nat.ltb_lt k n1) Hk1), (proj2 (Nat.ltb_lt k n2) Hk2).
    field; split; apply Rgt_not_eq; apply lt_0_INR; lia. }
  rewrite (sum_f_R0_ext _ (fun _ => 1 / (INR n1 * INR n2)) (S m - 1)).
  2: { intros k Hk; apply Haux; lia. }
  assert (Hsub : (S m - 1 = m)%nat) by lia.
  rewrite Hsub.
  rewrite sum_f_R0_const.
  replace (INR (m + 1)) with (INR (S m)) by (f_equal; lia).
  unfold Rdiv; ring.
Qed.

(* 由范数平方界推出范数界 *)
Lemma norm_from_sq_div (z : Complex) (a1 a2 b1 b2 N0 : nat) 
  (Ha1 : (a1 > 0)%nat) (Ha2 : (a2 > 0)%nat) (Hb1 : (b1 > 0)%nat) (Hb2 : (b2 > 0)%nat) (HN0 : (N0 > 0)%nat)
  (Hsq : Cnorm_sq z <= (INR N0 / (INR a1 * INR a2)) * (INR N0 / (INR b1 * INR b2))) :
  Cnorm z <= INR N0 / sqrt (INR a1 * INR a2 * INR b1 * INR b2).
Proof.
  assert (H_nonneg_left : 0 <= Cnorm z) by apply Cnorm_ge_0.
  assert (H_nonneg_right : 0 <= INR N0 / sqrt (INR a1 * INR a2 * INR b1 * INR b2)).
  { apply Rmult_le_pos; [apply pos_INR; lia |].
    left; apply Rinv_0_lt_compat, sqrt_lt_R0_c;
    repeat apply Rmult_lt_0_compat; apply lt_0_INR; lia. }
  assert (H_sq : (Cnorm z)² <= (INR N0 / sqrt (INR a1 * INR a2 * INR b1 * INR b2))²).
  {
    set (P := INR a1 * INR a2 * INR b1 * INR b2).
    assert (HP_nonneg : 0 <= P) by (subst P; repeat apply Rmult_le_pos; apply pos_INR; lia).
    assert (HP_pos    : 0 < P) by (subst P; repeat apply Rmult_lt_0_compat; apply lt_0_INR; lia).
    rewrite Cnorm_sq_rsqr_sqrt.
    apply Rle_trans with ((INR N0 / (INR a1 * INR a2)) * (INR N0 / (INR b1 * INR b2))).
    - exact Hsq.
    - assert (Heq : (INR N0 / sqrt P)² = (INR N0 / (INR a1 * INR a2)) * (INR N0 / (INR b1 * INR b2))).
      {
        rewrite (Rsqr_div' (INR N0) (sqrt P)).
        unfold Rsqr at 1 2.
        fold (Rsqr (sqrt P)).
        rewrite (Rsqr_sqrt P HP_nonneg).
        subst P.
        field; repeat split; apply Rgt_not_eq; apply lt_0_INR; lia.
      }
      rewrite Heq; apply Rle_refl.
  }
  apply Rsqr_incr_0; assumption.
Qed.

(* 平方根乘积下界 *)
Lemma sqrt_product_lower_bound (C : nat) (HC : (C >= 2)%nat) (a1 a2 b1 b2 d12 d34 : nat) :
    INR (max a1 a2) >= (INR C) ^ d12 * INR (Nat.min a1 a2) ->
    INR (max b1 b2) >= (INR C) ^ d34 * INR (Nat.min b1 b2) ->
    sqrt (INR a1 * INR a2 * INR b1 * INR b2) >=
    INR (Nat.min a1 a2) * INR (Nat.min b1 b2) * (sqrt (INR C)) ^ (d12 + d34).
Proof.
  intros Ha_ineq Hb_ineq.
  assert (Ha_max_min : INR a1 * INR a2 = INR (max a1 a2) * INR (Nat.min a1 a2)).
  {
    destruct (Nat.le_gt_cases a1 a2) as [Hle | Hgt].
    - rewrite (Nat.max_r a1 a2) by lia.
      rewrite (Nat.min_l a1 a2) by lia.
      ring.
    - rewrite (Nat.max_l a1 a2) by lia.
      rewrite (Nat.min_r a1 a2) by lia.
      ring.
  }
  assert (Hb_max_min : INR b1 * INR b2 = INR (max b1 b2) * INR (Nat.min b1 b2)).
  {
    destruct (Nat.le_gt_cases b1 b2) as [Hle | Hgt].
    - rewrite (Nat.max_r b1 b2) by lia.
      rewrite (Nat.min_l b1 b2) by lia.
      ring.
    - rewrite (Nat.max_l b1 b2) by lia.
      rewrite (Nat.min_r b1 b2) by lia.
      ring.
  }
  replace (INR a1 * INR a2 * INR b1 * INR b2)
    with ((INR (max a1 a2) * INR (Nat.min a1 a2)) * (INR (max b1 b2) * INR (Nat.min b1 b2))).
  2: { rewrite <- Ha_max_min, <- Hb_max_min; ring. }

  set (ma := Nat.min a1 a2); set (mb := Nat.min b1 b2).
  set (A := INR (max a1 a2)); set (B := INR (max b1 b2)).
  assert (HA : A >= (INR C)^d12 * INR ma) by (unfold A, ma; exact Ha_ineq).
  assert (HB : B >= (INR C)^d34 * INR mb) by (unfold B, mb; exact Hb_ineq).

  assert (H_nonneg_ma : 0 <= INR ma) by apply pos_INR.
  assert (H_nonneg_mb : 0 <= INR mb) by apply pos_INR.
  assert (H_nonneg_A : 0 <= A) by apply pos_INR.
  assert (H_nonneg_B : 0 <= B) by apply pos_INR.

  set (P := A * INR ma * (B * INR mb)).
  set (Q := ((INR C)^d12 * INR ma * INR ma) * ((INR C)^d34 * INR mb * INR mb)).
  assert (H_P_ineq : P >= Q).
  {
    apply Rle_ge.
    unfold P, Q.
    set (X1 := (INR C)^d12 * INR ma * INR ma).
    set (X2 := (INR C)^d34 * INR mb * INR mb).
    set (Y1 := A * INR ma).
    set (Y2 := B * INR mb).
    assert (H1' : X1 <= Y1).
    { subst X1 Y1. apply Rmult_le_compat_r; [apply pos_INR | now apply Rge_le]. }
    assert (H2' : X2 <= Y2).
    { subst X2 Y2. apply Rmult_le_compat_r; [apply pos_INR | now apply Rge_le]. }
    assert (HX1_nonneg : 0 <= X1).
    { repeat apply Rmult_le_pos; try apply pow_le; apply pos_INR. }
    assert (HX2_nonneg : 0 <= X2).
    { repeat apply Rmult_le_pos; try apply pow_le; apply pos_INR. }
    apply (Rmult_le_compat X1 Y1 X2 Y2 HX1_nonneg HX2_nonneg H1' H2').
  }

  assert (Q_eq : Q = (INR ma * INR ma) * (INR mb * INR mb) * (INR C)^(d12 + d34)).
  {
    unfold Q.
    rewrite (pow_add (INR C) d12 d34).
    ring.
  }
  rewrite Q_eq in H_P_ineq.

  assert (H_nonneg_ma2 : 0 <= INR ma * INR ma) by nra.
  assert (H_nonneg_mb2 : 0 <= INR mb * INR mb) by nra.
  assert (H_nonneg_pow : 0 <= (INR C)^(d12 + d34)) by (apply pow_le; apply pos_INR).

  set (target := (INR ma * INR ma) * (INR mb * INR mb) * (INR C) ^ (d12 + d34)).
  assert (H_sqrt_ineq : sqrt P >= sqrt target).
  {
    apply Rle_ge; apply sqrt_le_1_c; [| | apply Rge_le; exact H_P_ineq].
    - unfold target; repeat apply Rmult_le_pos; assumption.
    - unfold P; repeat apply Rmult_le_pos; assumption.
  }

  assert (H_target_sqrt_eq : sqrt target = INR ma * INR mb * (sqrt (INR C)) ^ (d12 + d34)).
  {
    unfold target.
    replace ((INR ma * INR ma) * (INR mb * INR mb) * (INR C) ^ (d12 + d34))
      with ((INR ma * INR ma) * ((INR mb * INR mb) * (INR C) ^ (d12 + d34))) by ring.
    rewrite sqrt_mult with (x := INR ma * INR ma) (y := (INR mb * INR mb) * (INR C)^(d12 + d34));
      [| exact H_nonneg_ma2 | apply Rmult_le_pos; [exact H_nonneg_mb2 | exact H_nonneg_pow]].
    rewrite sqrt_mult with (x := INR mb * INR mb) (y := (INR C)^(d12 + d34));
      [| exact H_nonneg_mb2 | exact H_nonneg_pow].
    rewrite (sqrt_square (INR ma)) by exact H_nonneg_ma.
    rewrite (sqrt_square (INR mb)) by exact H_nonneg_mb.
    assert (H_sqrt_pow : sqrt ((INR C) ^ (d12 + d34)) = (sqrt (INR C)) ^ (d12 + d34)).
    { apply sqrt_pow_INR_eq; assumption. }
    rewrite H_sqrt_pow.
    ring.
  }

  apply Rge_trans with (sqrt target).
  - exact H_sqrt_ineq.
  - rewrite H_target_sqrt_eq. apply Rle_ge, Rle_refl.
Qed.

(* 分母乘积平方根分式恒等式 *)
Lemma invert_g_product_rewrite (N0 a1 a2 b1 b2 : nat)
      (Ha1 : (a1 >= 2)%nat) (Ha2 : (a2 >= 2)%nat)
      (Hb1 : (b1 >= 2)%nat) (Hb2 : (b2 >= 2)%nat) :
  / ( (sqrt (INR (Nat.min a1 b1) / (INR a1 * INR b1))) *
      (sqrt (INR (Nat.min a2 b2) / (INR a2 * INR b2))) ) *
  (INR N0 / sqrt (INR a1 * INR a2 * INR b1 * INR b2))
  = INR N0 / ( (sqrt (INR (Nat.min a1 b1) / (INR a1 * INR b1))) *
               (sqrt (INR (Nat.min a2 b2) / (INR a2 * INR b2))) *
               sqrt (INR a1 * INR a2 * INR b1 * INR b2) ).
Proof.
  intros.
  set (s1 := sqrt (INR (Nat.min a1 b1) / (INR a1 * INR b1))).
  set (s2 := sqrt (INR (Nat.min a2 b2) / (INR a2 * INR b2))).
  set (s3 := sqrt (INR a1 * INR a2 * INR b1 * INR b2)).

  assert (Hs1_pos : s1 > 0).
  { subst s1; apply sqrt_lt_R0_c;
    apply Rmult_lt_0_compat;
    [ apply lt_0_INR; lia
    | apply Rinv_0_lt_compat; apply Rmult_lt_0_compat; apply lt_0_INR; lia]. }
  assert (Hs2_pos : s2 > 0).
  { subst s2; apply sqrt_lt_R0_c;
    apply Rmult_lt_0_compat;
    [ apply lt_0_INR; lia
    | apply Rinv_0_lt_compat; apply Rmult_lt_0_compat; apply lt_0_INR; lia]. }
  assert (Hs3_pos : s3 > 0).
  { subst s3; apply sqrt_lt_R0_c;
    repeat apply Rmult_lt_0_compat; apply lt_0_INR; lia. }

  field.
  split.
  - apply Rgt_not_eq; exact Hs3_pos.
  - split.
    + apply Rgt_not_eq; exact Hs2_pos.
    + apply Rgt_not_eq; exact Hs1_pos.
Qed.

(* 稀疏序列关键不等式 *)
Lemma key_inequality (N0 ma mb : nat) (m1 m2 : nat) (S : R) 
  (HN0_le_ma : INR N0 <= INR ma) 
  (Hma_pos : INR ma > 0)
  (Hmb_pos : INR mb > 0)
  (H_S_pos : S > 0) 
  (H_m1m2_pos : sqrt (INR m1 * INR m2) > 0)
  (H_main : INR ma * INR mb * S <= 4 * sqrt (INR m1 * INR m2))
  : INR N0 * S <= 4 * sqrt (INR m1 * INR m2).
Proof.
  apply Rle_trans with (INR ma * INR mb * S).
  - apply Rmult_le_compat_r.
    + apply Rlt_le; exact H_S_pos.
    + assert (Hmb_ge1_nat : (1 <= mb)%nat) by (destruct mb; [simpl in Hmb_pos; lra | lia]).
      assert (Hmb_ge1 : 1 <= INR mb). {
        rewrite <- INR_1.
        apply le_INR; exact Hmb_ge1_nat.
      }
      apply Rle_trans with (INR ma).
      * exact HN0_le_ma.
      * replace (INR ma) with (INR ma * 1) at 1 by ring.
        apply Rmult_le_compat_l.
        -- apply Rlt_le; exact Hma_pos.
        -- exact Hmb_ge1.
  - exact H_main.
Qed.

(* 广义关键不等式 *)

(* 稀疏索引增长下界 *)
Lemma sparse_index_growth_lower (seq : nat -> nat) (C : nat) (HC : (C >= 2)%nat)
  (Hsparse : forall i : nat, (INR (seq (S i)) > INR C * INR (seq i))%R)
  (Hge2 : forall i, (seq i >= 2)%nat) (i j : nat) (Hneq : i <> j) :
  let d := Z.abs_nat (Z.of_nat i - Z.of_nat j) in
  INR (max (seq i) (seq j)) >= (INR C) ^ d * INR (min (seq i) (seq j)).
Proof.
  intro d.
  destruct (Nat.lt_trichotomy i j) as [Hlt | [Heq | Hgt]].
  - (* i < j *)
    assert (Hlt_seq : (seq i < seq j)%nat).
    { apply (seq_strict_growth_lt seq C i j HC Hsparse Hge2 Hlt). }
    assert (Hmax_eq : max (seq i) (seq j) = seq j) by (apply Nat.max_r; lia).
    assert (Hmin_eq : min (seq i) (seq j) = seq i) by (apply Nat.min_l; lia).
    assert (Hle_ij : (i <= j)%nat) by lia.
    assert (Hd_eq : d = (j - i)%nat).
    { unfold d.
      replace (Z.of_nat i - Z.of_nat j)%Z with (- (Z.of_nat j - Z.of_nat i))%Z by ring.
      rewrite Zabs_nat_opp.
      now rewrite (Z_abs_nat_sub_small j i Hle_ij). }
    rewrite Hmax_eq, Hmin_eq, Hd_eq.
    apply Rle_ge; apply Rlt_le.
    exact (seq_exp_growth seq C HC Hsparse i j Hlt).
  - exfalso; apply Hneq; auto.
  - (* i > j *)
    assert (Hlt_seq : (seq j < seq i)%nat).
    { apply (seq_strict_growth_lt seq C j i HC Hsparse Hge2 Hgt). }
    assert (Hmax_eq : max (seq i) (seq j) = seq i) by (apply Nat.max_l; lia).
    assert (Hmin_eq : min (seq i) (seq j) = seq j) by (apply Nat.min_r; lia).
    assert (Hle_ji : (j <= i)%nat) by lia.
    assert (Hd_eq : d = (i - j)%nat).
    { unfold d; now rewrite (Z_abs_nat_sub_small i j Hle_ji). }
    rewrite Hmax_eq, Hmin_eq, Hd_eq.
    apply Rle_ge; apply Rlt_le.
    exact (seq_exp_growth seq C HC Hsparse j i Hgt).
Qed.

(* 衰减因子化简 *)


(* 最小值形式的核心不等式 *)
Lemma core_inequality_min_v2 (C : nat) (HC : (C >= 2)%nat) (seq1 seq2 : nat -> nat)
  (Hsparse1 : forall i, INR (seq1 (S i)) > INR C * INR (seq1 i))
  (Hsparse2 : forall i, INR (seq2 (S i)) > INR C * INR (seq2 i))
  (i1 i2 j1 j2 : nat) (Hneq1 : i1 <> i2) (Hneq2 : j1 <> j2)
  (a1 b1 a2 b2 : nat)
  (Ha1 : a1 = seq1 i1) (Ha2 : a2 = seq1 i2)
  (Hb1 : b1 = seq2 j1) (Hb2 : b2 = seq2 j2)
  (d12 d34 : nat)
  (Hd12 : d12 = Z.abs_nat (Z.of_nat i1 - Z.of_nat i2))
  (Hd34 : d34 = Z.abs_nat (Z.of_nat j1 - Z.of_nat j2))
  (Ha_ineq : INR (max a1 a2) >= (INR C) ^ d12 * INR (Nat.min a1 a2))
  (Hb_ineq : INR (max b1 b2) >= (INR C) ^ d34 * INR (Nat.min b1 b2))
  (S : R) (HS : S = (sqrt (INR C)) ^ (d12 + d34))
  (H_minge2 : forall i, (seq1 i >= 2)%nat)
  (H_minge2' : forall i, (seq2 i >= 2)%nat)
  : sqrt (INR a1 * INR a2 * INR b1 * INR b2) >= INR (Nat.min (Nat.min a1 a2) (Nat.min b1 b2)) * S.
Proof.
  subst S.
  set (ma := Nat.min a1 a2).
  set (mb := Nat.min b1 b2).
  set (mmin := Nat.min ma mb).

  assert (Ha1_ge2 : (a1 >= 2)%nat) by (subst a1; apply H_minge2).
  assert (Ha2_ge2 : (a2 >= 2)%nat) by (subst a2; apply H_minge2).
  assert (Hb1_ge2 : (b1 >= 2)%nat) by (subst b1; apply H_minge2').
  assert (Hb2_ge2 : (b2 >= 2)%nat) by (subst b2; apply H_minge2').

  pose proof (sqrt_product_lower_bound C HC a1 a2 b1 b2 d12 d34 Ha_ineq Hb_ineq) as H_lower.

  assert (H_pow_nonneg : 0 <= (sqrt (INR C)) ^ (d12 + d34)). {
    apply pow_le; apply Rlt_le; apply sqrt_lt_R0_c; apply lt_0_INR; lia.
  }

  assert (H_prod_ge_min : INR ma * INR mb >= INR (Nat.min ma mb)). {
    unfold mmin.
    destruct (Nat.le_ge_cases ma mb) as [Hle | Hge].
    - assert (Hmin_eq : Nat.min ma mb = ma) by (apply Nat.min_l; exact Hle).
      rewrite Hmin_eq.
      assert (Hmb_ge1 : INR mb >= 1). {
        apply Rle_ge; apply (le_INR 1 mb); subst mb; apply Nat.min_glb; lia.
      }
      assert (Hma_pos : INR ma > 0) by (apply lt_0_INR; lia).
      nra.
    - assert (Hmin_eq : Nat.min ma mb = mb) by (apply Nat.min_r; exact Hge).
      rewrite Hmin_eq.
      assert (Hma_ge1 : INR ma >= 1). {
        apply Rle_ge; apply (le_INR 1 ma); subst ma; apply Nat.min_glb; lia.
      }
      assert (Hmb_pos : INR mb > 0) by (apply lt_0_INR; lia).
      nra.
  }

  assert (H_prod_ge_min_scaled : INR ma * INR mb * (sqrt (INR C)) ^ (d12 + d34) >=
                                INR (Nat.min ma mb) * (sqrt (INR C)) ^ (d12 + d34)). {
    apply Rle_ge.
    apply Rmult_le_compat_r with (r := (sqrt (INR C)) ^ (d12 + d34)).
    - exact H_pow_nonneg.
    - apply Rge_le, H_prod_ge_min.
  }

  eapply Rge_trans; [exact H_lower | exact H_prod_ge_min_scaled].
Qed.

(* 衰减因子不等式 *)
Lemma decay_factor_inequality (C : nat) (HC : (C >= 2)%nat) (r : R) (Hr : r = sqrt (INR C))
  (seq1 seq2 : nat -> nat)
  (Hsparse1 : forall i : nat, (INR (seq1 (S i)) > INR C * INR (seq1 i))%R)
  (Hsparse2 : forall i : nat, (INR (seq2 (S i)) > INR C * INR (seq2 i))%R)
  (Hge2_1 : forall i, (seq1 i >= 2)%nat) (Hge2_2 : forall i, (seq2 i >= 2)%nat)
  (i1 j1 i2 j2 : nat) (a1 a2 b1 b2 : nat)
  (Ha1 : a1 = seq1 i1) (Ha2 : a2 = seq1 i2) (Hb1 : b1 = seq2 j1) (Hb2 : b2 = seq2 j2)
  (Hneq1 : i1 <> i2) (Hneq2 : j1 <> j2)
  (N0 : nat)
  (HN0_le_min_a : INR N0 <= INR (Nat.min a1 a2))
  (HN0_le_min_b : INR N0 <= INR (Nat.min b1 b2))
  (H_index_bound : (Z.abs_nat (Z.of_nat i1 - Z.of_nat i2) + Z.abs_nat (Z.of_nat j1 - Z.of_nat j2) <= 6)%nat)
  (HCeq2 : C = 2%nat)
  : let g (x y : nat) := sqrt (INR (Nat.min x y) / (INR x * INR y)) in
    / (g a1 b1 * g a2 b2) * (INR N0 / sqrt (INR a1 * INR a2 * INR b1 * INR b2)) <=
    8 / (r ^ (Z.abs_nat (Z.of_nat i1 - Z.of_nat i2) + Z.abs_nat (Z.of_nat j1 - Z.of_nat j2))).
Proof.
  intros g. subst r.
  set (d12 := Z.abs_nat (Z.of_nat i1 - Z.of_nat i2)).
  set (d34 := Z.abs_nat (Z.of_nat j1 - Z.of_nat j2)).
  assert (Hdsum_le_6 : (d12 + d34 <= 6)%nat) by exact H_index_bound.
  assert (Hrpos : sqrt (INR C) > 0) by (apply sqrt_lt_R0_c; apply lt_0_INR; lia).
  set (ma := Nat.min a1 a2); set (mb := Nat.min b1 b2).
  
  assert (HN0_le_ma_nat : (N0 <= ma)%nat). {
    apply INR_le.
    unfold ma. exact HN0_le_min_a.
  }
  assert (HN0_le_mb_nat : (N0 <= mb)%nat). {
    apply INR_le.
    unfold mb. exact HN0_le_min_b.
  }
  
  set (Mmin := Nat.min ma mb).
  assert (HN0_le_Mmin_nat : (N0 <= Mmin)%nat). {
    apply (Nat.min_glb ma mb N0); assumption.
  }
  assert (HN0_le_Mmin : INR N0 <= INR Mmin). {
    apply le_INR; exact HN0_le_Mmin_nat.
  }

  assert (Ha_ineq : INR (max a1 a2) >= (INR C) ^ d12 * INR (min a1 a2)).
  {
    destruct (Nat.lt_trichotomy i1 i2) as [Hlt | [Heq | Hgt]].
    - assert (Ha_lt : (a1 < a2)%nat).
      { subst a1 a2; apply (seq_strict_growth_lt seq1 C i1 i2 HC Hsparse1 Hge2_1 Hlt). }
      assert (Hmax_eq : max a1 a2 = a2) by (apply Nat.max_r; lia).
      assert (Hmin_eq : min a1 a2 = a1) by (apply Nat.min_l; lia).
      assert (Hle_12 : (i1 <= i2)%nat) by lia.
      assert (Hd12_eq : d12 = (i2 - i1)%nat).
      { unfold d12.
        replace (Z.of_nat i1 - Z.of_nat i2)%Z with (- (Z.of_nat i2 - Z.of_nat i1))%Z by ring.
        rewrite Zabs_nat_opp.
        now rewrite (Z_abs_nat_sub_small i2 i1 Hle_12). }
      rewrite Hmax_eq, Hmin_eq, Hd12_eq.
      subst a1 a2.
      apply Rle_ge; apply Rlt_le.
      apply (seq_exp_growth seq1 C HC Hsparse1 i1 i2 Hlt).
    - exfalso; apply Hneq1; auto.
    - assert (Ha_lt : (a2 < a1)%nat).
      { subst a1 a2; apply (seq_strict_growth_lt seq1 C i2 i1 HC Hsparse1 Hge2_1 Hgt). }
      assert (Hmax_eq : max a1 a2 = a1) by (apply Nat.max_l; lia).
      assert (Hmin_eq : min a1 a2 = a2) by (apply Nat.min_r; lia).
      assert (Hle_21 : (i2 <= i1)%nat) by lia.
      assert (Hd12_eq : d12 = (i1 - i2)%nat).
      { unfold d12; now rewrite (Z_abs_nat_sub_small i1 i2 Hle_21). }
      rewrite Hmax_eq, Hmin_eq, Hd12_eq.
      subst a1 a2.
      apply Rle_ge; apply Rlt_le.
      apply (seq_exp_growth seq1 C HC Hsparse1 i2 i1 Hgt).
  }

  assert (Hb_ineq : INR (max b1 b2) >= (INR C) ^ d34 * INR (min b1 b2)).
  {
    destruct (Nat.lt_trichotomy j1 j2) as [Hlt | [Heq | Hgt]].
    - assert (Hb_lt : (b1 < b2)%nat).
      { subst b1 b2; apply (seq_strict_growth_lt seq2 C j1 j2 HC Hsparse2 Hge2_2 Hlt). }
      assert (Hmax_eq : max b1 b2 = b2) by (apply Nat.max_r; lia).
      assert (Hmin_eq : min b1 b2 = b1) by (apply Nat.min_l; lia).
      assert (Hle_12 : (j1 <= j2)%nat) by lia.
      assert (Hd34_eq : d34 = (j2 - j1)%nat).
      { unfold d34.
        replace (Z.of_nat j1 - Z.of_nat j2)%Z with (- (Z.of_nat j2 - Z.of_nat j1))%Z by ring.
        rewrite Zabs_nat_opp.
        now rewrite (Z_abs_nat_sub_small j2 j1 Hle_12). }
      rewrite Hmax_eq, Hmin_eq, Hd34_eq.
      subst b1 b2.
      apply Rle_ge; apply Rlt_le.
      apply (seq_exp_growth seq2 C HC Hsparse2 j1 j2 Hlt).
    - exfalso; apply Hneq2; auto.
    - assert (Hb_lt : (b2 < b1)%nat).
      { subst b1 b2; apply (seq_strict_growth_lt seq2 C j2 j1 HC Hsparse2 Hge2_2 Hgt). }
      assert (Hmax_eq : max b1 b2 = b1) by (apply Nat.max_l; lia).
      assert (Hmin_eq : min b1 b2 = b2) by (apply Nat.min_r; lia).
      assert (Hle_21 : (j2 <= j1)%nat) by lia.
      assert (Hd34_eq : d34 = (j1 - j2)%nat).
      { unfold d34; now rewrite (Z_abs_nat_sub_small j1 j2 Hle_21). }
      rewrite Hmax_eq, Hmin_eq, Hd34_eq.
      subst b1 b2.
      apply Rle_ge; apply Rlt_le.
      apply (seq_exp_growth seq2 C HC Hsparse2 j2 j1 Hgt).
  }

  assert (H_prod_lower : sqrt (INR a1 * INR a2 * INR b1 * INR b2) >= INR ma * INR mb * (sqrt (INR C)) ^ (d12 + d34)).
  {
    unfold ma, mb.
    apply (sqrt_product_lower_bound C HC a1 a2 b1 b2 d12 d34 Ha_ineq Hb_ineq).
  }

  assert (Ha1_ge2 : (a1 >= 2)%nat) by (subst a1; apply Hge2_1).
  assert (Ha2_ge2 : (a2 >= 2)%nat) by (subst a2; apply Hge2_1).
  assert (Hb1_ge2 : (b1 >= 2)%nat) by (subst b1; apply Hge2_2).
  assert (Hb2_ge2 : (b2 >= 2)%nat) by (subst b2; apply Hge2_2).

  unfold g.
  rewrite (invert_g_product_rewrite N0 a1 a2 b1 b2 Ha1_ge2 Ha2_ge2 Hb1_ge2 Hb2_ge2).

  set (m1 := Nat.min a1 b1).
  set (m2 := Nat.min a2 b2).
  assert (H_D_eq : (sqrt (INR (Nat.min a1 b1) / (INR a1 * INR b1))) *
                  (sqrt (INR (Nat.min a2 b2) / (INR a2 * INR b2))) *
                  sqrt (INR a1 * INR a2 * INR b1 * INR b2) =
                  sqrt (INR m1 * INR m2)).
  {
    subst m1 m2.
    assert (Hpos1 : 0 <= INR (Nat.min a1 b1) / (INR a1 * INR b1)).
    { apply Rlt_le; apply Rdiv_lt_0_compat; [apply lt_0_INR; lia | apply Rmult_lt_0_compat; apply lt_0_INR; lia]. }
    assert (Hpos2 : 0 <= INR (Nat.min a2 b2) / (INR a2 * INR b2)).
    { apply Rlt_le; apply Rdiv_lt_0_compat; [apply lt_0_INR; lia | apply Rmult_lt_0_compat; apply lt_0_INR; lia]. }
    assert (Hpos3 : 0 <= INR a1 * INR a2 * INR b1 * INR b2) by (repeat apply Rmult_le_pos; apply pos_INR).

    rewrite <- (sqrt_mult (INR (Nat.min a1 b1) / (INR a1 * INR b1))
                          (INR (Nat.min a2 b2) / (INR a2 * INR b2))
                          Hpos1 Hpos2).
    rewrite <- (sqrt_mult ((INR (Nat.min a1 b1) / (INR a1 * INR b1)) * (INR (Nat.min a2 b2) / (INR a2 * INR b2)))
                          (INR a1 * INR a2 * INR b1 * INR b2)).
    - apply f_equal.
      field.
      repeat split; apply Rgt_not_eq; apply lt_0_INR; lia.
    - apply Rmult_le_pos; assumption.
    - exact Hpos3.
  }
  unfold m1, m2.
  rewrite H_D_eq.

  assert (HN0_a1 : (N0 <= a1)%nat).
  { eapply Nat.le_trans; [apply HN0_le_ma_nat | apply Nat.le_min_l]. }
  assert (HN0_a2 : (N0 <= a2)%nat).
  { eapply Nat.le_trans; [apply HN0_le_ma_nat | apply Nat.le_min_r]. }
  assert (HN0_b1 : (N0 <= b1)%nat).
  { eapply Nat.le_trans; [apply HN0_le_mb_nat | apply Nat.le_min_l]. }
  assert (HN0_b2 : (N0 <= b2)%nat).
  { eapply Nat.le_trans; [apply HN0_le_mb_nat | apply Nat.le_min_r]. }

  assert (HN0_le_m1 : (N0 <= m1)%nat) by (apply Nat.min_glb; assumption).
  assert (HN0_le_m2 : (N0 <= m2)%nat) by (apply Nat.min_glb; assumption).

  assert (HR_N0_m1 : INR N0 <= INR m1) by (apply le_INR; exact HN0_le_m1).
  assert (HR_N0_m2 : INR N0 <= INR m2) by (apply le_INR; exact HN0_le_m2).

  assert (H_sq : INR N0 * INR N0 <= INR m1 * INR m2). {
    apply Rle_trans with (INR N0 * INR m2).
    - apply Rmult_le_compat_l; [apply pos_INR; lia | exact HR_N0_m2].
    - apply Rmult_le_compat_r; [apply pos_INR; lia | exact HR_N0_m1].
  }

  assert (H_sqrt : INR N0 <= sqrt (INR m1 * INR m2)). {
    rewrite <- (sqrt_square (INR N0)).
    - apply sqrt_le_1_c.
      + apply Rle_0_sqr.
      + apply Rmult_le_pos; apply pos_INR.
      + exact H_sq.
    - apply pos_INR; lia.
  }

  assert (Hpos_sqrt : 0 < sqrt (INR m1 * INR m2)).
  { apply sqrt_lt_R0_c; apply Rmult_lt_0_compat; apply lt_0_INR; lia. }
  assert (Hleft_le_1 : INR N0 / sqrt (INR m1 * INR m2) <= 1). {
    apply (Rmult_le_reg_r (sqrt (INR m1 * INR m2))
            (INR N0 / sqrt (INR m1 * INR m2)) 1 Hpos_sqrt).
    field_simplify.
    - exact H_sqrt.
    - apply Rgt_not_eq; exact Hpos_sqrt.
  }

  assert (Hsqrt_ge1 : 1 <= sqrt (INR C)). {
    rewrite HCeq2.
    assert (H_lt : sqrt 1 < sqrt 2). { apply sqrt_lt_1; lra. }
    rewrite sqrt_1 in H_lt.
    exact (Rlt_le _ _ H_lt).
  }

  assert (H_sqrt_C_pow6 : (sqrt (INR C)) ^ 6 = 8). {
    rewrite HCeq2.
    replace ((sqrt (INR 2)) ^ 6) with ((sqrt (INR 2) * sqrt (INR 2)) ^ 3) by ring.
    rewrite sqrt_sqrt with (x := INR 2) by (apply Rlt_le; apply lt_0_INR; lia).
    simpl (INR 2); ring.
  }

  assert (Hpow_pos : 0 < sqrt (INR C) ^ (d12 + d34)). {
    apply pow_lt; apply sqrt_lt_R0_c; apply lt_0_INR; lia.
  }

  assert (H_pow_le : sqrt (INR C) ^ (d12 + d34) <= sqrt (INR C) ^ 6). {
    apply Rle_pow; [exact Hsqrt_ge1 | exact Hdsum_le_6].
  }

  assert (Hright_ge_1 : 1 <= 8 / (sqrt (INR C) ^ (d12 + d34))). {
    apply (Rmult_le_reg_r (sqrt (INR C) ^ (d12 + d34)) 1 (8 / (sqrt (INR C) ^ (d12 + d34))));
    [ exact Hpow_pos | ].
    unfold Rdiv.
    rewrite Rmult_assoc.
    rewrite Rinv_l by (apply Rgt_not_eq; exact Hpow_pos).
    rewrite Rmult_1_r, Rmult_1_l.
    apply Rle_trans with (sqrt (INR C) ^ 6); [exact H_pow_le | rewrite H_sqrt_C_pow6; apply Rle_refl].
  }

  eapply Rle_trans; eassumption.
Qed.

(* 定理：张量内积衰减 *)
Theorem tensor_inner_decay (C : nat) (HC : (C >= 2)%nat) (r : R) (Hr : r = sqrt (INR C))
  (seq1 seq2 : nat -> nat)
  (Hsparse1 : forall i : nat, (INR (seq1 (S i)) > INR C * INR (seq1 i))%R)
  (Hsparse2 : forall i : nat, (INR (seq2 (S i)) > INR C * INR (seq2 i))%R)
  (Hge2_1 : forall i, (seq1 i >= 2)%nat) (Hge2_2 : forall i, (seq2 i >= 2)%nat)
  (i1 j1 i2 j2 : nat) (a1 a2 b1 b2 : nat)
  (Ha1 : a1 = seq1 i1) (Ha2 : a2 = seq1 i2)
  (Hb1 : b1 = seq2 j1) (Hb2 : b2 = seq2 j2)
  (Hneq1 : i1 <> i2) (Hneq2 : j1 <> j2)
  (HCeq2 : C = 2%nat)
  (H_index_bound : (Z.abs_nat (Z.of_nat i1 - Z.of_nat i2) + Z.abs_nat (Z.of_nat j1 - Z.of_nat j2) <= 6)%nat)
  : let g (x y : nat) := sqrt (INR (Nat.min x y) / (INR x * INR y)) in
    Cnorm (Csum (fun k => (Cof_real (/ g a1 b1) *c (psi a1 k *c psi b1 k)) *c
                         Cconj (Cof_real (/ g a2 b2) *c (psi a2 k *c psi b2 k)))
              (Nat.pred (S (max (max a1 b1) (max a2 b2)))))
    <= 8 / (r ^ (Z.abs_nat (Z.of_nat i1 - Z.of_nat i2) + Z.abs_nat (Z.of_nat j1 - Z.of_nat j2))).
Proof.
  intros g.
  set (M := S (max (max a1 b1) (max a2 b2))).
  assert (HMpos : (M > 0)%nat) by (unfold M; lia).
  pose proof (Hge2_1 i1) as Ha1_ge2. pose proof (Hge2_1 i2) as Ha2_ge2.
  pose proof (Hge2_2 j1) as Hb1_ge2. pose proof (Hge2_2 j2) as Hb2_ge2.

  set (N := Nat.pred M).
  set (N0 := Nat.min (Nat.min a1 a2) (Nat.min b1 b2)).
  assert (HN0 : (N0 <= N)%nat) by (unfold N0, N, M; lia).
  pose proof (product_psi_inner_decomposition a1 a2 b1 b2 g) as Hprod.
  simpl in Hprod.
  change N with (max (max a1 b1) (max a2 b2)).
  rewrite Hprod.

  assert (HN0a1 : (N0 <= a1)%nat) by (unfold N0; lia).
  assert (HN0a2 : (N0 <= a2)%nat) by (unfold N0; lia).
  assert (HN0b1 : (N0 <= b1)%nat) by (unfold N0; lia).
  assert (HN0b2 : (N0 <= b2)%nat) by (unfold N0; lia).
  set (Δ := 2 * PI * (/ INR a1 - / INR a2) + 2 * PI * (/ INR b1 - / INR b2)).
  assert (HΔ_eq : Δ = 2 * PI * (/ INR a1 - / INR a2) + 2 * PI * (/ INR b1 - / INR b2)) by reflexivity.
  assert (Ha1_pos : (a1 > 0)%nat) by (subst a1; pose proof (Hge2_1 i1); lia).
  assert (Ha2_pos : (a2 > 0)%nat) by (subst a2; pose proof (Hge2_1 i2); lia).
  assert (Hb1_pos : (b1 > 0)%nat) by (subst b1; pose proof (Hge2_2 j1); lia).
  assert (Hb2_pos : (b2 > 0)%nat) by (subst b2; pose proof (Hge2_2 j2); lia).
  pose proof (psi_product_inner_geom_expansion a1 a2 b1 b2 N0 Δ HΔ_eq
    HN0a1 HN0a2 HN0b1 HN0b2 Ha1_pos Ha2_pos Hb1_pos Hb2_pos) as Hgeom.
  change (Nat.min (Nat.min a1 a2) (Nat.min b1 b2)) with N0.
  rewrite Hgeom.

  set (Ssum := Csum (fun k => (psi a1 k *c Cconj (psi a2 k)) *c
                              (psi b1 k *c Cconj (psi b2 k))) N0).
  pose (A k := psi a1 k *c Cconj (psi a2 k)).
  pose (B k := psi b1 k *c Cconj (psi b2 k)).
  assert (HN0_pos : (N0 > 0)%nat) by (unfold N0; lia).
  assert (Hprod_N0_zero : (A N0 *c B N0)%C = ComplexNumbers.C0).
  {
    unfold A, B.
    assert (H_N0_is_one : N0 = a1 \/ N0 = a2 \/ N0 = b1 \/ N0 = b2).
    {
      unfold N0.
      destruct (Nat.min_spec a1 a2) as [[_ Hmin1] | [_ Hmin1]];
      destruct (Nat.min_spec b1 b2) as [[_ Hmin2] | [_ Hmin2]];
      rewrite Hmin1, Hmin2.
      - destruct (Nat.min_spec a1 b1) as [[_ ->] | [_ ->]]; auto.
      - destruct (Nat.min_spec a1 b2) as [[_ ->] | [_ ->]]; auto.
      - destruct (Nat.min_spec a2 b1) as [[_ ->] | [_ ->]]; auto.
      - destruct (Nat.min_spec a2 b2) as [[_ ->] | [_ ->]]; auto.
    }
    destruct H_N0_is_one as [H_eq | [H_eq | [H_eq | H_eq]]];
    rewrite H_eq; simpl.
    - rewrite (psi_ge_n_zero a1 a1) by lia. rewrite Cmul_0_l, Cmul_0_l; reflexivity.
    - rewrite (psi_ge_n_zero a2 a2) by lia. rewrite Cconj_0, Cmul_0_r, Cmul_0_l; reflexivity.
    - rewrite (psi_ge_n_zero b1 b1) by lia. rewrite Cmul_0_l, Cmul_0_r; reflexivity.
    - rewrite (psi_ge_n_zero b2 b2) by lia. rewrite Cconj_0, Cmul_0_r, Cmul_0_r; reflexivity.
  }
  pose proof (CauchySchwarz_truncated A B N0 HN0_pos Hprod_N0_zero) as Hcs_sq.

  assert (HsumA : sum_f_R0 (fun k => Cnorm_sq (A k)) (N0 - 1) = INR N0 / (INR a1 * INR a2)).
  { unfold A; apply sum_sq_psi_product; assumption. }
  assert (HsumB : sum_f_R0 (fun k => Cnorm_sq (B k)) (N0 - 1) = INR N0 / (INR b1 * INR b2)).
  { unfold B; apply sum_sq_psi_product; assumption. }
  rewrite HsumA, HsumB in Hcs_sq.
  assert (HnormS : Cnorm Ssum <= INR N0 / sqrt (INR a1 * INR a2 * INR b1 * INR b2)).
  {
    apply (norm_from_sq_div Ssum a1 a2 b1 b2 N0 Ha1_pos Ha2_pos Hb1_pos Hb2_pos HN0_pos).
    exact Hcs_sq.
  }

  assert (Hg_pos : forall x y, (x >= 2)%nat -> (y >= 2)%nat -> g x y > 0).
  {
    intros x y Hx Hy; unfold g.
    apply sqrt_lt_R0_c; apply Rmult_lt_0_compat.
    - apply lt_0_INR; lia.
    - apply Rinv_0_lt_compat; apply Rmult_lt_0_compat; apply lt_0_INR; lia.
  }
  assert (Ha1_ge2_nat : (a1 >= 2)%nat) by (subst a1; apply Hge2_1).
  assert (Ha2_ge2_nat : (a2 >= 2)%nat) by (subst a2; apply Hge2_1).
  assert (Hb1_ge2_nat : (b1 >= 2)%nat) by (subst b1; apply Hge2_2).
  assert (Hb2_ge2_nat : (b2 >= 2)%nat) by (subst b2; apply Hge2_2).
  assert (Hg1 : g a1 b1 > 0) by (apply Hg_pos; assumption).
  assert (Hg2 : g a2 b2 > 0) by (apply Hg_pos; assumption).
  assert (Hcoeff_nonneg : 0 <= / (g a1 b1 * g a2 b2)).
  {
    apply Rlt_le; apply Rinv_0_lt_compat.
    apply Rmult_lt_0_compat; [exact Hg1 | exact Hg2].
  }
  assert (Hcoeff : Cnorm (Cof_real (/ (g a1 b1 * g a2 b2))) = / (g a1 b1 * g a2 b2)).
  { apply Cnorm_Cof_real_pos; exact Hcoeff_nonneg. }
  rewrite Cnorm_mult; rewrite Hcoeff.
  rewrite <- Hgeom.
  apply Rle_trans with (/ (g a1 b1 * g a2 b2) * (INR N0 / sqrt (INR a1 * INR a2 * INR b1 * INR b2))).
  - apply Rmult_le_compat_l; [exact Hcoeff_nonneg | exact HnormS].
  - clear Hcoeff HnormS Hcoeff_nonneg.

  assert (HN0_le_min_a : INR N0 <= INR (Nat.min a1 a2)).
  { apply le_INR; unfold N0; apply Nat.le_min_l. }
  assert (HN0_le_min_b : INR N0 <= INR (Nat.min b1 b2)).
  { apply le_INR; unfold N0; apply Nat.le_min_r. }
  set (d12 := Z.abs_nat (Z.of_nat i1 - Z.of_nat i2)).
  set (d34 := Z.abs_nat (Z.of_nat j1 - Z.of_nat j2)).
  unfold d12, d34.
  apply (decay_factor_inequality C HC r Hr seq1 seq2 Hsparse1 Hsparse2
           Hge2_1 Hge2_2 i1 j1 i2 j2 a1 a2 b1 b2 Ha1 Ha2 Hb1 Hb2 Hneq1 Hneq2
           N0 HN0_le_min_a HN0_le_min_b H_index_bound HCeq2).
Qed.

(** 部分和移除一项 *)
Lemma sum_f_R0_minus_one (k j0 : nat) (f : nat -> R) :
  (j0 < k)%nat ->
  sum_f_R0 (fun p => if eq_nat_dec j0 p then 0 else f p) (Nat.pred k) =
  sum_f_R0 f (Nat.pred k) - f j0.
Proof.
  intros Hj0.
  destruct k as [|k']; [inversion Hj0|].
  simpl (Nat.pred (S k')).
  induction k' as [|k' IH] in j0, Hj0 |- *.
  - assert (j0 = 0%nat) by lia.
    subst j0; simpl sum_f_R0; rewrite Rminus_diag; reflexivity.
  - destruct (Nat.eq_dec j0 (S k')) as [-> | Hne].
    + set (g := fun p : nat => if eq_nat_dec (S k') p then 0 else f p).
      assert (Hg : forall p, (p <= k')%nat -> g p = f p).
      { intros p Hp; unfold g; destruct (eq_nat_dec (S k') p); subst; [lia| reflexivity]. }
      assert (Hsum : sum_f_R0 g k' = sum_f_R0 f k').
      { apply sum_f_R0_ext; intros i Hi; apply Hg; lia. }
      rewrite (sum_f_R0_S g k').
      unfold g at 2.
      destruct (eq_nat_dec (S k') (S k')) as [_|?]; [|contradiction].
      rewrite Hsum, Rplus_0_r.
      rewrite (sum_f_R0_S f k').
      ring.
    + assert (Hj0' : (j0 < S k')%nat) by lia.
      rewrite sum_f_R0_S.
      destruct (Nat.eq_dec j0 (S k')) as [Hfalse | _]; [contradiction|].
      rewrite (IH j0 Hj0').
      rewrite (sum_f_R0_S f k').
      ring.
Qed.

(** 部分和分解为首项加其余 *)
Lemma sum_f_R0_eq_1_plus_rest (n i0 : nat) (f : nat -> R) :
  (i0 < n)%nat -> f i0 = 1%R ->
  sum_f_R0 f (Nat.pred n) = 1 + sum_f_R0 (fun i => if eq_nat_dec i0 i then 0 else f i) (Nat.pred n).
Proof.
  intros Hi0 Hf0.
  rewrite (sum_f_R0_minus_one n i0 f Hi0).
  rewrite Hf0.
  ring.
Qed.

(** 二维乘积展平求和 *)
Lemma sum_f_R0_flatten_product_sym (m' k' : nat) (a b : nat -> R) :
  (m' > 0)%nat -> (k' > 0)%nat ->
  sum_f_R0 (fun p => a (Nat.div p k') * b (Nat.modulo p k')) (m' * k' - 1)
  = (sum_f_R0 a (m' - 1)) * (sum_f_R0 b (k' - 1)).
Proof.
  intros Hm' Hk'.
  induction m' as [|m' IH].
  - exfalso; lia.
  - destruct (Nat.eq_dec m' 0) as [Hz|Hpos].
    + subst m'.
      replace (1 * k' - 1)%nat with (k' - 1)%nat by lia.
      simpl (sum_f_R0 a (1 - 1)).
      assert (Hsum : sum_f_R0 (fun p : nat => a (Nat.div p k') * b (Nat.modulo p k')) (k' - 1)
                    = a 0%nat * sum_f_R0 b (k' - 1)).
      {
        rewrite (sum_f_R0_ext (fun p => a (Nat.div p k') * b (Nat.modulo p k'))
                             (fun p => a 0%nat * b p)).
        - apply sum_f_R0_scal_l.
        - intros p Hp. assert (Hp_lt : (p < k')%nat) by lia.
          rewrite Nat.div_small, Nat.mod_small; auto.
      }
      rewrite Hsum; ring.
    + assert (Hpos_m' : (m' > 0)%nat) by (apply Nat.neq_0_lt_0; exact Hpos).
      specialize (IH Hpos_m').
      set (A := (m' * k' - 1)%nat).
      assert (H_eq : ((S m') * k' - 1 = A + k')%nat) by (subst A; nia).
      rewrite H_eq.
      rewrite sum_f_R0_plus'.
      replace (k' =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
      simpl.
      subst A.
      rewrite IH.
      assert (H_block : sum_f_R0 (fun k0 : nat =>
                        a (Nat.div (S (m' * k' - 1 + k0)) k') * b (Nat.modulo (S (m' * k' - 1 + k0)) k'))
                        (k' - 1) = a m' * sum_f_R0 b (k' - 1)).
      {
        rewrite (sum_f_R0_ext _ (fun k0 => a m' * b k0)).
        - apply sum_f_R0_scal_l.
        - intros k0 Hk0. assert (Hk0_lt : (k0 < k')%nat) by lia.
          replace (S (m' * k' - 1 + k0))%nat with (m' * k' + k0)%nat by lia.
          replace (m' * k' + k0)%nat with (k0 + m' * k')%nat by ring.
          rewrite Nat.div_add, Div0.mod_add by (apply Nat.neq_0_lt_0; exact Hk').
          rewrite Nat.div_small, Nat.mod_small; auto.
      }
      rewrite H_block.
      replace (m' - 0)%nat with m' by lia.
      assert (Hm'_S : m' = S (m' - 1)) by lia.
      rewrite Hm'_S.
      rewrite sum_f_R0_S.
      replace (S (m' - 1)) with m' by lia.
      ring.
Qed.

(** 展平乘积并剔除对角线项 *)
Lemma flatten_product_with_diag (m k i0 j0 : nat) (a b : nat -> R) :
  (m > 0)%nat -> (k > 0)%nat -> (i0 < m)%nat -> (j0 < k)%nat ->
  sum_f_R0 (fun p : nat =>
    if eq_nat_dec (i0 * k + j0) p then 0%R
    else a (Nat.div p k) * b (Nat.modulo p k)) (m * k - 1)
  = (sum_f_R0 a (Nat.pred m)) * (sum_f_R0 b (Nat.pred k)) - a i0 * b j0.
Proof.
  intros Hm Hk Hi0 Hj0.
  replace (m * k - 1)%nat with (Nat.pred (m * k)) by lia.
  rewrite (sum_f_R0_minus_one (m * k) (i0 * k + j0)
            (fun p => a (Nat.div p k) * b (Nat.modulo p k))).
  - assert (H_flatten :
      sum_f_R0 (fun p => a (Nat.div p k) * b (Nat.modulo p k)) (Nat.pred (m * k))
      = (sum_f_R0 a (Nat.pred m)) * (sum_f_R0 b (Nat.pred k))).
    {
      replace (Nat.pred (m * k)) with (m * k - 1)%nat by lia.
      replace (Nat.pred m) with (m - 1)%nat by lia.
      replace (Nat.pred k) with (k - 1)%nat by lia.
      apply sum_f_R0_flatten_product_sym; auto.
    }
    rewrite H_flatten.
    assert (Hdiv : Nat.div (i0 * k + j0) k = i0).
    { symmetry; apply (Nat.div_unique (i0 * k + j0) k i0 j0); nia. }
    assert (Hmod : Nat.modulo (i0 * k + j0) k = j0).
    { symmetry; apply (Nat.mod_unique (i0 * k + j0) k i0 j0); nia. }
    rewrite Hdiv, Hmod.
    ring.
  - nia.
Qed.

(** 展平乘积剔除对角线行和分解 *)
Lemma prod_row_sum_decomp_eq (n1 n2 : nat) (i0 j0 : nat) (d1 : nat -> nat -> R) :
  (i0 < n1)%nat -> (j0 < n2)%nat ->
  (forall i, d1 i i = 1%R) ->
  sum_f_R0 (fun jdx : nat =>
    if eq_nat_dec (i0 * n2 + j0)%nat jdx then 0%R
    else d1 i0 (Nat.div jdx n2) * d1 j0 (Nat.modulo jdx n2)) (Nat.pred (n1 * n2))
  = (1%R + sum_f_R0 (fun i' => if eq_nat_dec i0 i' then 0%R else d1 i0 i') (Nat.pred n1)) *
    (1%R + sum_f_R0 (fun j' => if eq_nat_dec j0 j' then 0%R else d1 j0 j') (Nat.pred n2)) - 1%R.
Proof.
  intros Hi0 Hj0 Hdiag.
  set (a := fun i : nat => d1 i0 i).
  set (b := fun j : nat => d1 j0 j).
  assert (Ha0 : a i0 = 1%R) by (unfold a; apply Hdiag).
  assert (Hb0 : b j0 = 1%R) by (unfold b; apply Hdiag).
  destruct n1 as [|n1']; [exfalso; exact (Nat.nlt_0_r _ Hi0)|].
  destruct n2 as [|n2']; [exfalso; exact (Nat.nlt_0_r _ Hj0)|].

  replace (Nat.pred (S n1' * S n2')) with (S n1' * S n2' - 1)%nat by lia.
  replace (Nat.pred (S n1')) with n1' by lia.
  replace (Nat.pred (S n2')) with n2' by lia.

  assert (H_main : sum_f_R0 (fun p : nat =>
    if eq_nat_dec (i0 * (S n2') + j0) p then 0%R
    else a (Nat.div p (S n2')) * b (Nat.modulo p (S n2'))) (S n1' * S n2' - 1)
    = (sum_f_R0 a n1' * sum_f_R0 b n2') - a i0 * b j0).
  {
    apply (flatten_product_with_diag (S n1') (S n2') i0 j0 a b);
      [ apply Nat.lt_0_succ
      | apply Nat.lt_0_succ
      | exact Hi0
      | exact Hj0 ].
  }

  rewrite H_main.
  rewrite Ha0, Hb0.

  pose proof (sum_f_R0_eq_1_plus_rest (S n1') i0 a Hi0 Ha0) as Ha_sum.
  simpl in Ha_sum.
  pose proof (sum_f_R0_eq_1_plus_rest (S n2') j0 b Hj0 Hb0) as Hb_sum.
  simpl in Hb_sum.

  rewrite Ha_sum, Hb_sum.
  ring.
Qed.

(** 序列的第i项为起始值加i（基于项数i归纳） *)
Lemma nth_seq_general (start n i : nat) :
  (i < n)%nat -> nth i (seq start n) 0%nat = (start + i)%nat.
Proof.
  generalize dependent start.
  generalize dependent n.
  induction i as [|i IHi].
  - intros n start H.
    destruct n as [|n'].
    + inversion H.
    + simpl.
      lia.
  - intros n start H.
    destruct n as [|n'].
    + inversion H.
    + simpl in *.
      assert (H_i_lt_n' : (i < n')%nat) by lia.
      rewrite IHi with (n := n') (start := S start) by exact H_i_lt_n'.
      lia.
Qed.

(** 序列的第i项为起始值加i（基于序列长度n归纳） *)

(** 序列的长度恒等于给定长度参数 *)
Lemma length_seq (start n : nat) :
  length (seq start n) = n.
Proof.
  generalize dependent start.
  induction n as [|n IHn].
  - intros start. simpl. reflexivity.
  - intros start. simpl. rewrite IHn with (start := (S start)%nat). reflexivity.
Qed.

(** 非空列表的首元素附加后last不变 *)
Lemma last_cons_nonempty : forall (A : Type) (a : A) (l : list A) (d : A),
  l <> [] -> last (a :: l) d = last l d.
Proof.
  intros A a l d H.
  destruct l as [|h t].
  - contradiction.
  - simpl. reflexivity.
Qed.

(** 序列的末项为起始值加长度减一 *)
Lemma last_seq (start n : nat) :
  (n > 0)%nat -> last (seq start n) 0%nat = (start + n - 1)%nat.
Proof.
  intros H.
  generalize dependent start.
  induction n as [|n_total IHn].
  - inversion H.
  - intros start.
    destruct n_total as [|n_prev].
    + simpl.
      lia.
    + assert (H_seq_step : seq start (S (S n_prev)) = start :: seq (S start) (S n_prev)).
      { reflexivity. }
      rewrite H_seq_step.
      assert (H_seq_nonempty : seq (S start) (S n_prev) <> []).
      {
        intro Hnil.
        apply length_zero_iff_nil in Hnil.
        rewrite length_seq in Hnil.
        lia.
      }
      rewrite (last_cons_nonempty nat start (seq (S start) (S n_prev)) 0%nat H_seq_nonempty).
      assert (H_IH_pre : (S n_prev > 0)%nat).
      { lia. }
      assert (H_IH : forall start0 : nat, last (seq start0 (S n_prev)) 0%nat = (start0 + S n_prev - 1)%nat).
      { apply IHn, H_IH_pre. }
      assert (H_IH_specialized : last (seq (S start) (S n_prev)) 0%nat = ((S start) + S n_prev - 1)%nat).
      { apply H_IH. }
      rewrite H_IH_specialized.
      lia.
Qed.

(* d因子行和上界 *)
Lemma d_factor_row_sum_le_4K (C : nat) (HCgt2 : (C > 2)%nat) (m i : nat) (Hi : (i < m)%nat) :
  sum_f_R0 (fun j => if eq_nat_dec i j then 0 else d_factor (sqrt (INR C)) i j) (Nat.pred m)
  <= 4 * K (INR C).
Proof.
  set (r := sqrt (INR C)).
  assert (Hr_gt1 : r > 1).
  { unfold r; rewrite <- sqrt_1. apply sqrt_lt_1; [lra| apply pos_INR; lia |].
    change 1 with (INR 1); apply lt_INR; lia. }
  assert (Hr_pos : r > 0) by (apply sqrt_lt_R0_c; apply lt_0_INR; lia).
  assert (Hr_neq0 : r - 1 <> 0) by lra.

  destruct (lt_dec (i + 1) m) as [Hi_mid | Hi_end].
  - set (F := fun j : nat => if eq_nat_dec i j then 0 else / (r ^ Z.abs_nat (Z.of_nat i - Z.of_nat j))).
    assert (HF_i : F i = 0%R).
    { unfold F; destruct (eq_nat_dec i i); [reflexivity | contradiction]. }
    assert (HF_bound : forall j, (j < m)%nat -> j <> i ->
      F j <= / (r ^ Z.abs_nat (Z.of_nat i - Z.of_nat j))).
    { intros j Hj Hne; unfold F; destruct (eq_nat_dec i j) as [Heq | Hne'].
      - exfalso; apply Hne; symmetry; exact Heq.
      - reflexivity. }
    assert (HsumF : sum_f_R0 F (Nat.pred m) <= 2 / (r - 1)).
    { replace (Nat.pred m) with (m - 1)%nat by lia.
      apply (split_sum_geometric_bound_one r Hr_gt1 i m F Hi_mid HF_i HF_bound). }
    assert (H_d_sum : sum_f_R0 (fun j => if eq_nat_dec i j then 0 else d_factor r i j) (Nat.pred m) <= 4 * K (INR C)).
    {
      assert (H_eq : sum_f_R0 (fun j => if eq_nat_dec i j then 0 else d_factor r i j) (Nat.pred m)
                     = sum_f_R0 (fun j => 2 * F j) (Nat.pred m)).
      { apply sum_f_R0_ext; intros j Hj; unfold F, d_factor.
        destruct (eq_nat_dec i j) as [Heq | Hne].
        - subst; simpl; ring.
        - rewrite (proj2 (Nat.eqb_neq i j) Hne).
          assert (Hpow_nonzero : r ^ Z.abs_nat (Z.of_nat i - Z.of_nat j) <> 0).
          { apply Rgt_not_eq; apply pow_lt; lra. }
          field; assumption. }
      rewrite H_eq, sum_f_R0_scal_l.
      assert (H_eq2 : 2 * (2 / (r - 1)) = 4 * K (INR C)).
      { unfold K; change (sqrt (INR C)) with r; field; assumption. }
      apply (Rle_trans _ (2 * (2 / (r - 1))) _).
      - nra.
      - rewrite H_eq2; apply Rle_refl.
    }
    exact H_d_sum.

  - assert (Hi_end' : (m <= i+1)%nat) by lia.
    set (F := fun j : nat => if eq_nat_dec i j then 0 else / (r ^ Z.abs_nat (Z.of_nat i - Z.of_nat j))).
    assert (HF_i : F i = 0%R).
    { unfold F; destruct (eq_nat_dec i i); [reflexivity | contradiction]. }
    assert (HF_bound : forall j, (j < m)%nat -> j <> i ->
      F j <= / (r ^ Z.abs_nat (Z.of_nat i - Z.of_nat j))).
    { intros j Hj Hne; unfold F; destruct (eq_nat_dec i j) as [Heq | Hne'].
      - exfalso; apply Hne; symmetry; exact Heq.
      - reflexivity. }
    assert (HsumF : sum_f_R0 F (Nat.pred m) <= / (r - 1)).
    { replace (Nat.pred m) with (m - 1)%nat by lia.
      apply (row_sum_bound_when_i_last_one r i m F Hr_gt1 Hi Hi_end' HF_i HF_bound). }
    assert (H_d_sum : sum_f_R0 (fun j => if eq_nat_dec i j then 0 else d_factor r i j) (Nat.pred m) <= 4 * K (INR C)).
    {
      assert (H_eq : sum_f_R0 (fun j => if eq_nat_dec i j then 0 else d_factor r i j) (Nat.pred m)
                     = sum_f_R0 (fun j => 2 * F j) (Nat.pred m)).
      { apply sum_f_R0_ext; intros j Hj; unfold F, d_factor.
        destruct (eq_nat_dec i j) as [Heq | Hne].
        - subst; simpl; ring.
        - rewrite (proj2 (Nat.eqb_neq i j) Hne).
          assert (Hpow_nonzero : r ^ Z.abs_nat (Z.of_nat i - Z.of_nat j) <> 0).
          { apply Rgt_not_eq; apply pow_lt; lra. }
          field; assumption. }
      rewrite H_eq, sum_f_R0_scal_l.
      assert (H_eq2 : 2 * (/ (r - 1)) = 2 * K (INR C)).
      { unfold K; change (sqrt (INR C)) with r; field; assumption. }
      apply (Rle_trans _ (2 * (/ (r - 1))) _).
      - nra.
      - rewrite H_eq2.
        assert (HK_pos : 0 <= K (INR C)).
        { apply Rlt_le, K_pos; assumption. }
        nra.
    }
    exact H_d_sum.
Qed.

(* 对角因子对角线为一 *)
Lemma d_factor_diag (r : R) (i : nat) : d_factor r i i = 1%R.
Proof.
  unfold d_factor. rewrite Nat.eqb_refl. reflexivity.
Qed.

(* 双指标行和上界 *)
Lemma row_sum_delta_pair_bound (C : nat) (HCgt2 : (C > 2)%nat) (n1 n2 : nat) (idx : nat) (Hidx : (idx < n1 * n2)%nat) :
  let r := sqrt (INR C) in
  let d1 := d_factor r in
  let delta_pair idx1 idx2 := d1 (Nat.div idx1 n2) (Nat.div idx2 n2) * d1 (Nat.modulo idx1 n2) (Nat.modulo idx2 n2) in
  let M_bound := (1 + 4 * K (INR C)) * (1 + 4 * K (INR C)) - 1 in
  sum_f_R0 (fun jdx => if eq_nat_dec idx jdx then 0 else delta_pair idx jdx) (Nat.pred (n1 * n2)) <= M_bound.
Proof.
  intros r d1 delta_pair M_bound.
  assert (Hn2_pos : (n2 > 0)%nat) by (destruct n2; [lia|lia]).
  set (i0 := Nat.div idx n2).
  set (j0 := Nat.modulo idx n2).
  assert (Hi0 : (i0 < n1)%nat). {
    apply Div0.div_lt_upper_bound; lia.
  }
  assert (Hj0 : (j0 < n2)%nat). {
    apply Nat.mod_upper_bound; lia.
  }
  assert (Hd1_diag : forall i, d1 i i = 1%R). {
    apply d_factor_diag.
  }
  pose proof (prod_row_sum_decomp_eq n1 n2 i0 j0 d1 Hi0 Hj0 Hd1_diag) as H_decomp.
  unfold delta_pair.

  assert (Hidx_eq : idx = (i0 * n2 + j0)%nat).
  { unfold i0, j0.
    rewrite Nat.mul_comm.
    apply Nat.div_mod; lia. }
  rewrite Hidx_eq.

  assert (Hdiv_eq : Nat.div (i0 * n2 + j0) n2 = i0).
  { rewrite Nat.add_comm.
    rewrite Nat.div_add by lia.
    rewrite Nat.div_small by exact Hj0.
    lia. }
  assert (Hmod_eq : Nat.modulo (i0 * n2 + j0) n2 = j0).
  { rewrite Nat.add_comm.
    rewrite Div0.mod_add by lia.
    rewrite Nat.mod_small by exact Hj0.
    reflexivity. }
  rewrite Hdiv_eq, Hmod_eq.

  rewrite H_decomp.
  set (row_i0 := sum_f_R0 (fun i' => if eq_nat_dec i0 i' then 0 else d1 i0 i') (Nat.pred n1)).
  set (row_j0 := sum_f_R0 (fun j' => if eq_nat_dec j0 j' then 0 else d1 j0 j') (Nat.pred n2)).
  assert (Hrow_i0 : row_i0 <= 4 * K (INR C)). {
    subst row_i0.
    apply d_factor_row_sum_le_4K with (m := n1); [assumption | exact Hi0].
  }
  assert (Hrow_j0 : row_j0 <= 4 * K (INR C)). {
    subst row_j0.
    apply d_factor_row_sum_le_4K with (m := n2); [assumption | exact Hj0].
  }
  assert (HK_nonneg : 0 <= K (INR C)) by (apply Rlt_le, K_pos; assumption).
  assert (Hr_pos : r > 0) by (apply sqrt_lt_R0_c; apply lt_0_INR; lia).
  assert (Hd1_nonneg : forall i j, 0 <= d1 i j).
  { intros a b; unfold d1, d_factor.
    destruct (a =? b); [lra|].
    apply Rmult_le_pos; [lra|].
    left; apply Rinv_0_lt_compat; apply pow_lt; lra. }
  assert (Hrow_i0_nonneg : 0 <= row_i0) by
    (subst row_i0; apply sum_f_R0_nonneg; intro i'; destruct (eq_nat_dec i0 i'); [lra| apply Hd1_nonneg]).
  assert (Hrow_j0_nonneg : 0 <= row_j0) by
    (subst row_j0; apply sum_f_R0_nonneg; intro j'; destruct (eq_nat_dec j0 j'); [lra| apply Hd1_nonneg]).
  assert (Hineq1 : 1 + row_i0 <= 1 + 4 * K (INR C)) by lra.
  assert (Hineq2 : 1 + row_j0 <= 1 + 4 * K (INR C)) by lra.
  assert (Hmult_ineq : (1 + row_i0) * (1 + row_j0) <= (1 + 4 * K (INR C)) * (1 + 4 * K (INR C))). {
    apply Rmult_le_compat; lra.
  }
  unfold M_bound.
  lra.
Qed.

(** 展平双重求和 *)
Lemma Csum_flatten (n1 n2 : nat) (F : nat -> nat -> Complex) :
  Csum (fun idx : nat => F (idx / n2)%nat (idx mod n2)%nat) (n1 * n2) =
  Csum (fun i : nat => Csum (fun j : nat => F i j) n2) n1.
Proof.
  destruct n2 as [|n2'].
  - rewrite Nat.mul_0_r.
    simpl Csum at 1.
    assert (Hinner0 : forall i, Csum (fun j : nat => F i j) 0 = C0) by (intro i; simpl; reflexivity).
    assert (Hright_eq : Csum (fun i : nat => Csum (fun j : nat => F i j) 0) n1 =
                        Csum (fun _ : nat => C0) n1).
    { apply Csum_ext'; intros i Hi; rewrite Hinner0; reflexivity. }
    rewrite Hright_eq.
    assert (Csum_zero : forall n, Csum (fun _ : nat => C0) n = C0).
    { induction n as [|n IH]; simpl; auto. rewrite IH; apply Cadd_0_r. }
    rewrite Csum_zero. reflexivity.
  - revert F.
    induction n1 as [|n1 IH]; intros F.
    + simpl. reflexivity.
    + assert (Csum_split_local : forall (g : nat -> Complex) (a b : nat),
        Csum g (a + b) = Csum g a +c Csum (fun i => g (a + i)%nat) b).
      { intros g a b. induction b as [|b IH_b]; simpl.
        - rewrite Nat.add_0_r. rewrite Cadd_0_r. reflexivity.
        - rewrite Nat.add_succ_r. simpl Csum at 1. rewrite IH_b.
          rewrite Cadd_assoc. reflexivity. }
      assert (Csum_split_last_local : forall (g : nat -> Complex) (n : nat),
        Csum g (S n) = Csum g n +c g n).
      { intros g n. induction n as [|n IHn]; simpl; rewrite ?Cadd_0_r, ?Cadd_0_l; auto. }
      rewrite (Nat.mul_succ_l n1 (S n2')) at 1.
      rewrite Csum_split_local.
      rewrite IH.
      rewrite (Csum_split_last_local (fun i : nat => Csum (fun j : nat => F i j) (S n2')) n1).
      apply (f_equal2 Cadd).
      * reflexivity.
      * assert (Csum_ext_local : forall (f g : nat -> Complex) (n : nat),
          (forall i, (i < n)%nat -> f i = g i) -> Csum f n = Csum g n).
        { induction n as [|n IH']; intros H.
          - reflexivity.
          - simpl. rewrite IH'.
            + f_equal. apply H; lia.
            + intros i Hi. apply H; lia. }
        apply Csum_ext_local; intros k Hk.
        assert (Hk_lt_Sn2' : (k < S n2')%nat) by lia.
        rewrite Nat.add_comm.
        rewrite Nat.div_add by (apply Nat.neq_0_lt_0; lia).
        rewrite Div0.mod_add by (apply Nat.neq_0_lt_0; lia).
        rewrite Nat.div_small by exact Hk_lt_Sn2'.
        rewrite Nat.mod_small by exact Hk_lt_Sn2'.
        reflexivity.
Qed.

(** 展平实数求和 *)
Lemma sum_f_R0_flatten (n1 n2 : nat) (Hn1 : (n1 > 0)%nat) (Hn2 : (n2 > 0)%nat) (F : nat -> nat -> R) :
  sum_f_R0 (fun idx : nat => F (idx / n2)%nat (idx mod n2)%nat) (n1 * n2 - 1)%nat =
  sum_f_R0 (fun i : nat => sum_f_R0 (fun j : nat => F i j) (n2 - 1)%nat) (n1 - 1)%nat.
Proof.
  destruct n1 as [|n1].
  { exfalso; lia. }
  induction n1 as [|n1 IH].
  - replace (1 * n2 - 1)%nat with (n2 - 1)%nat by lia.
    replace (1 - 1)%nat with 0%nat by lia.
    simpl (sum_f_R0 _ 0).
    apply sum_f_R0_ext; intros i Hi.
    assert (Hi_lt_n2 : (i < n2)%nat) by lia.
    rewrite Nat.div_small, Nat.mod_small; auto.
  - destruct n2 as [|n2'].
    { exfalso; lia. }
    set (m := S n2') in *.
    assert (Hpos_m : (0 < m)%nat) by lia.
    assert (Hm0 : (m =? 0)%nat = false) by (apply Nat.eqb_neq; lia).
    replace (S (S n1) * m - 1)%nat with ((S n1 * m - 1) + m)%nat by lia.
    rewrite sum_f_R0_plus'.
    rewrite Hm0.
    assert (H_Sn1_pos : (S n1 > 0)%nat) by lia.
    rewrite (IH H_Sn1_pos).
    replace (S n1 - 1)%nat with n1 by lia.
    match goal with
    | |- ?L + ?R = _ =>
      replace R with (sum_f_R0 (fun j : nat => F (S n1) j) (m - 1)%nat)
    end.
    + replace (S (S n1) - 1)%nat with (S n1)%nat by lia.
      rewrite (sum_f_R0_S (fun i : nat => sum_f_R0 (fun j : nat => F i j) (m - 1)) n1).
      ring.
    + apply sum_f_R0_ext; intros j Hj.
      assert (Hj_lt_m : (j < m)%nat) by lia.
      replace (S (S n1 * m - 1) + j)%nat with (S n1 * m + j)%nat by lia.
      replace (S n1 * m + j)%nat with (j + S n1 * m)%nat by lia.
      assert (Hm_neq0 : m <> 0%nat) by lia.
      rewrite (Nat.div_add j (S n1) m Hm_neq0).
      rewrite (Nat.Div0.mod_add j (S n1) m).
      rewrite Nat.div_small by lia.
      rewrite Nat.mod_small by lia.
      reflexivity.
Qed.

(* 定理：单点张量内积的指数衰减上界 *)
Theorem inner_product_single_tensor_bound (C : nat) (r : R) (Hr : r = sqrt (INR C))
    (i1 i2 j1 j2 : nat) (a1 a2 b1 b2 : nat) (d12 d34 : nat) :
      (C >= 2)%nat ->
      (a1 >= 2)%nat -> (a2 >= 2)%nat -> (b1 >= 2)%nat -> (b2 >= 2)%nat ->
      INR (max a1 a2) >= (INR C) ^ d12 * INR (min a1 a2) ->
      INR (max b1 b2) >= (INR C) ^ d34 * INR (min b1 b2) ->
      let g x y := sqrt (INR (Nat.min x y) / (INR x * INR y)) in
      Cnorm (Csum (fun k => (psi a1 k *c Cconj (psi a2 k)) *c (psi b1 k *c Cconj (psi b2 k)))
                 (Nat.min (Nat.min a1 a2) (Nat.min b1 b2)))
      <= (g a1 b1 * g a2 b2).
Proof.
  intros HC Ha1 Ha2 Hb1 Hb2 Hineq1 Hineq2 g.
  set (N0 := Nat.min (Nat.min a1 a2) (Nat.min b1 b2)).
  assert (HN0a1 : (N0 <= a1)%nat) by (unfold N0; lia).
  assert (HN0a2 : (N0 <= a2)%nat) by (unfold N0; lia).
  assert (HN0b1 : (N0 <= b1)%nat) by (unfold N0; lia).
  assert (HN0b2 : (N0 <= b2)%nat) by (unfold N0; lia).
  destruct (Nat.eq_dec N0 0) as [Hz|Hpos].
  - subst N0.
    rewrite Hz.
    rewrite Csum_0.
    assert (Cnorm_C0 : Cnorm (C0 : Complex) = 0%R). {
      unfold Cnorm, Cnorm_sq; simpl; rewrite Rsqr_0, Rplus_0_l; apply sqrt_0.
    }
    rewrite Cnorm_C0.
    unfold g; apply Rmult_le_pos; apply sqrt_pos.
  - assert (HN0pos : (N0 > 0)%nat) by lia.
    set (A1 := fun k : nat => psi a1 k *c Cconj (psi a2 k)).
    set (B1 := fun k : nat => psi b1 k *c Cconj (psi b2 k)).
    assert (Htarget : Csum (fun k => (psi a1 k *c Cconj (psi a2 k)) *c (psi b1 k *c Cconj (psi b2 k))) N0
                     = Csum (fun k => A1 k *c B1 k) N0).
    { apply Csum_ext'; intros k Hk; unfold A1, B1; reflexivity. }
    rewrite Htarget.
    assert (Hzero_prod : (A1 N0 *c B1 N0)%C = C0). {
      assert (HN0_is : N0 = a1 \/ N0 = a2 \/ N0 = b1 \/ N0 = b2) by (unfold N0; lia).
      destruct HN0_is as [H|[H|[H|H]]];
        rewrite H; unfold A1, B1.
      - assert (HA1_zero : psi a1 a1 *c Cconj (psi a2 a1) = C0).
        { rewrite (psi_ge_n_zero a1 a1) by lia; apply Cmul_0_l. }
        rewrite HA1_zero; apply Cmul_0_l.
      - assert (HA1_zero : psi a1 a2 *c Cconj (psi a2 a2) = C0).
        { rewrite (psi_ge_n_zero a2 a2) by lia; rewrite Cconj_0; apply Cmul_0_r. }
        rewrite HA1_zero; apply Cmul_0_l.
      - assert (H0 : psi b1 b1 = C0) by (apply psi_ge_n_zero; lia).
        rewrite H0; rewrite Cmul_0_l; apply Cmul_0_r.
      - assert (HB1_zero : psi b1 b2 *c Cconj (psi b2 b2) = C0).
        { rewrite (psi_ge_n_zero b2 b2) by lia; rewrite Cconj_0; apply Cmul_0_r. }
        rewrite HB1_zero; apply Cmul_0_r.
    }
    pose proof (CauchySchwarz_truncated A1 B1 N0 HN0pos Hzero_prod) as Hcs_sq.
    unfold A1, B1 in Hcs_sq.
    assert (sumA_eq : sum_f_R0 (fun k : nat => Cnorm_sq (psi a1 k *c Cconj (psi a2 k))) (N0 - 1)
                     = INR N0 / (INR a1 * INR a2)). {
      assert (HsumA : sum_f_R0 (fun k : nat => Cnorm_sq (psi a1 k *c Cconj (psi a2 k))) (N0 - 1)
                      = sum_f_R0 (fun k : nat => Cnorm_sq (psi a1 k) * Cnorm_sq (psi a2 k)) (N0 - 1)).
      { apply sum_f_R0_ext; intros k Hk; rewrite Cnorm_sq_mult, Cnorm_sq_conj; reflexivity. }
      rewrite HsumA.
      assert (HtermA : forall k, (k < N0)%nat ->
        Cnorm_sq (psi a1 k) * Cnorm_sq (psi a2 k) = 1 / (INR a1 * INR a2)).
      { intros k Hk.
        assert (Hk_a1 : (k < a1)%nat) by (apply Nat.lt_le_trans with N0; auto; lia).
        assert (Hk_a2 : (k < a2)%nat) by (apply Nat.lt_le_trans with N0; auto; lia).
        rewrite (Cnorm_sq_psi_exact a1 k), (Cnorm_sq_psi_exact a2 k).
        rewrite (proj2 (Nat.ltb_lt k a1) Hk_a1), (proj2 (Nat.ltb_lt k a2) Hk_a2).
        field; split; apply Rgt_not_eq; apply lt_0_INR; lia. }
      rewrite (sum_f_R0_ext _ (fun _ => 1 / (INR a1 * INR a2)) (N0 - 1));
        [| intros k Hk; apply HtermA; lia].
      rewrite sum_f_R0_const; replace (S (N0 - 1))%nat with N0 by lia.
      field; split; apply Rgt_not_eq; apply lt_0_INR; lia.
    }
    assert (sumB_eq : sum_f_R0 (fun k : nat => Cnorm_sq (psi b1 k *c Cconj (psi b2 k))) (N0 - 1)
                     = INR N0 / (INR b1 * INR b2)). {
      assert (HsumB : sum_f_R0 (fun k : nat => Cnorm_sq (psi b1 k *c Cconj (psi b2 k))) (N0 - 1)
                      = sum_f_R0 (fun k : nat => Cnorm_sq (psi b1 k) * Cnorm_sq (psi b2 k)) (N0 - 1)).
      { apply sum_f_R0_ext; intros k Hk; rewrite Cnorm_sq_mult, Cnorm_sq_conj; reflexivity. }
      rewrite HsumB.
      assert (HtermB : forall k, (k < N0)%nat ->
        Cnorm_sq (psi b1 k) * Cnorm_sq (psi b2 k) = 1 / (INR b1 * INR b2)).
      { intros k Hk.
        assert (Hk_b1 : (k < b1)%nat) by (apply Nat.lt_le_trans with N0; auto; lia).
        assert (Hk_b2 : (k < b2)%nat) by (apply Nat.lt_le_trans with N0; auto; lia).
        rewrite (Cnorm_sq_psi_exact b1 k), (Cnorm_sq_psi_exact b2 k).
        rewrite (proj2 (Nat.ltb_lt k b1) Hk_b1), (proj2 (Nat.ltb_lt k b2) Hk_b2).
        field; split; apply Rgt_not_eq; apply lt_0_INR; lia. }
      rewrite (sum_f_R0_ext _ (fun _ => 1 / (INR b1 * INR b2)) (N0 - 1));
        [| intros k Hk; apply HtermB; lia].
      rewrite sum_f_R0_const; replace (S (N0 - 1))%nat with N0 by lia.
      field; split; apply Rgt_not_eq; apply lt_0_INR; lia.
    }
    rewrite sumA_eq, sumB_eq in Hcs_sq.
    assert (Hnorm : Cnorm (Csum (fun k : nat => (psi a1 k *c Cconj (psi a2 k)) *c (psi b1 k *c Cconj (psi b2 k))) N0)
                   <= INR N0 / sqrt (INR a1 * INR a2 * INR b1 * INR b2)). {
      apply (norm_from_sq_div (Csum (fun k : nat => (psi a1 k *c Cconj (psi a2 k)) *c (psi b1 k *c Cconj (psi b2 k))) N0)
               a1 a2 b1 b2 N0);
        try (apply lt_0_INR; lia); try lia.
      exact Hcs_sq.
    }
    set (m1 := Nat.min a1 b1).
    set (m2 := Nat.min a2 b2).
    assert (H_sq_ineq : (INR N0)^2 <= INR m1 * INR m2). {
      assert (H1 : INR N0 <= INR m1) by (apply le_INR; unfold N0, m1; lia).
      assert (H2 : INR N0 <= INR m2) by (apply le_INR; unfold N0, m2; lia).
      assert (Hpos_INR : 0 <= INR N0) by apply pos_INR.
      replace ((INR N0)^2) with (INR N0 * INR N0) by ring.
      apply Rmult_le_compat; [exact Hpos_INR | exact Hpos_INR | exact H1 | exact H2].
    }
    assert (H_nonneg_left : 0 <= INR N0 / sqrt (INR a1 * INR a2 * INR b1 * INR b2)). {
      unfold Rdiv; apply Rmult_le_pos; [apply pos_INR| left; apply Rinv_0_lt_compat;
        apply sqrt_lt_R0_c; repeat apply Rmult_lt_0_compat; apply lt_0_INR; lia].
    }
    assert (H_nonneg_right : 0 <= g a1 b1 * g a2 b2). {
      unfold g; apply Rmult_le_pos; apply sqrt_pos.
    }
    assert (H_sq : (INR N0 / sqrt (INR a1 * INR a2 * INR b1 * INR b2)) ^ 2 <=
                   (g a1 b1 * g a2 b2) ^ 2). {
      set (P := INR a1 * INR a2 * INR b1 * INR b2).
      assert (HPpos : P > 0) by (repeat apply Rmult_lt_0_compat; apply lt_0_INR; lia).
      assert (Hsqrt_nonzero : sqrt P <> 0) by
          (apply Rgt_not_eq, sqrt_lt_R0_c, HPpos).
      assert (Hleft_sq : (INR N0 / sqrt P)^2 = (INR N0)^2 / P). {
        replace ((INR N0 / sqrt P)^2) with ((INR N0)^2 / (sqrt P)^2) 
          by (field; exact Hsqrt_nonzero).
        replace ((sqrt P)^2) with (Rsqr (sqrt P)) by (unfold Rsqr; ring).
        rewrite Rsqr_sqrt; [| apply Rlt_le, HPpos].
        reflexivity.
      }
      assert (Hright_sq : (g a1 b1 * g a2 b2)^2 = (INR m1 * INR m2) / P). {
        unfold g, m1, m2.
        set (s1 := sqrt (INR (Nat.min a1 b1) / (INR a1 * INR b1))).
        set (s2 := sqrt (INR (Nat.min a2 b2) / (INR a2 * INR b2))).
        assert (Hd1 : 0 <= INR (Nat.min a1 b1) / (INR a1 * INR b1))
          by (unfold Rdiv; apply Rmult_le_pos;
              [apply pos_INR | left; apply Rinv_0_lt_compat;
               apply Rmult_lt_0_compat; apply lt_0_INR; lia]).
        assert (Hd2 : 0 <= INR (Nat.min a2 b2) / (INR a2 * INR b2))
          by (unfold Rdiv; apply Rmult_le_pos;
              [apply pos_INR | left; apply Rinv_0_lt_compat;
               apply Rmult_lt_0_compat; apply lt_0_INR; lia]).
        rewrite <- (Rsqr_pow2 (s1 * s2)).
        rewrite Rsqr_mult.
        unfold s1, s2.
        rewrite (Rsqr_sqrt _ Hd1).
        rewrite (Rsqr_sqrt _ Hd2).
        unfold P.
        field_simplify_eq; [ | repeat split; apply Rgt_not_eq; apply lt_0_INR; lia ].
        ring.
      }
      rewrite Hleft_sq, Hright_sq.
      unfold Rdiv.
      apply Rmult_le_compat_r.
      - left; apply Rinv_0_lt_compat; exact HPpos.
      - exact H_sq_ineq.
    }
    assert (H_ineq : INR N0 / sqrt (INR a1 * INR a2 * INR b1 * INR b2) <= g a1 b1 * g a2 b2).
    { nra. }
    eapply Rle_trans; [exact Hnorm | exact H_ineq].
Qed.

(* 张量核心内积未衰减界 *)
Lemma tensor_inner_undecayed_bound :
  forall (C : nat) (HC : (C >= 2)%nat)
    (seq1 seq2 : nat -> nat)
    (Hge2_1 : forall i, (seq1 i >= 2)%nat)
    (Hge2_2 : forall i, (seq2 i >= 2)%nat)
    (i1 i2 j1 j2 : nat) (a1 a2 b1 b2 : nat),
    a1 = seq1 i1 -> a2 = seq1 i2 ->
    b1 = seq2 j1 -> b2 = seq2 j2 ->
    i1 <> i2 -> j1 <> j2 ->
    let gamma_ab (x y : nat) := sqrt (INR (Nat.min x y) / (INR x * INR y)) in
    Cnorm (Csum (fun k : nat =>
      (psi a1 k *c Cconj (psi a2 k)) *c (psi b1 k *c Cconj (psi b2 k)))
      (Nat.min (Nat.min a1 a2) (Nat.min b1 b2)))
    <= gamma_ab a1 b1 * gamma_ab a2 b2.
Proof.
  intros C HC seq1 seq2 Hge2_1 Hge2_2 i1 i2 j1 j2 a1 a2 b1 b2
         Ha1 Ha2 Hb1 Hb2 Hneq1 Hneq2 gamma_ab.
  assert (Ha1_ge2 : (a1 >= 2)%nat) by (subst a1; apply Hge2_1).
  assert (Ha2_ge2 : (a2 >= 2)%nat) by (subst a2; apply Hge2_1).
  assert (Hb1_ge2 : (b1 >= 2)%nat) by (subst b1; apply Hge2_2).
  assert (Hb2_ge2 : (b2 >= 2)%nat) by (subst b2; apply Hge2_2).
  set (r := sqrt (INR C)).
  assert (Hr_eq : r = sqrt (INR C)) by reflexivity.
  set (d12 := 0%nat). set (d34 := 0%nat).
  assert (Hineq_a : INR (max a1 a2) >= (INR C) ^ d12 * INR (min a1 a2)).
  { subst d12.
    replace ((INR C) ^ 0) with 1%R by (simpl; ring).
    rewrite Rmult_1_l.
    assert (Hmax_ge_min : (min a1 a2 <= max a1 a2)%nat).
    { apply Nat.le_trans with (m := a1); [apply Nat.le_min_l | apply Nat.le_max_l]. }
    apply Rle_ge, le_INR; exact Hmax_ge_min. }
  assert (Hineq_b : INR (max b1 b2) >= (INR C) ^ d34 * INR (min b1 b2)).
  { subst d34.
    replace ((INR C) ^ 0) with 1%R by (simpl; ring).
    rewrite Rmult_1_l.
    assert (Hmax_ge_min' : (min b1 b2 <= max b1 b2)%nat).
    { apply Nat.le_trans with (m := b1); [apply Nat.le_min_l | apply Nat.le_max_l]. }
    apply Rle_ge, le_INR; exact Hmax_ge_min'. }
  exact (inner_product_single_tensor_bound C r Hr_eq i1 i2 j1 j2 a1 a2 b1 b2 d12 d34
         HC Ha1_ge2 Ha2_ge2 Hb1_ge2 Hb2_ge2 Hineq_a Hineq_b).
Qed.

(* 张量核心内积衰减界 *)
Lemma tensor_core_inner_decay_bound :
  forall (C : nat) (HC : (C >= 2)%nat)
    (seq1 seq2 : nat -> nat)
    (Hsparse1 : forall i : nat, (INR (seq1 (S i)) > INR C * INR (seq1 i))%R)
    (Hsparse2 : forall i : nat, (INR (seq2 (S i)) > INR C * INR (seq2 i))%R)
    (Hge2_1 : forall i, (seq1 i >= 2)%nat)
    (Hge2_2 : forall i, (seq2 i >= 2)%nat)
    (i1 i2 j1 j2 : nat)
    (a1 a2 b1 b2 : nat)
    (Ha1_eq : a1 = seq1 i1) (Ha2_eq : a2 = seq1 i2)
    (Hb1_eq : b1 = seq2 j1) (Hb2_eq : b2 = seq2 j2)
    (Hneq1 : i1 <> i2) (Hneq2 : j1 <> j2)
    (HCeq2 : C = 2%nat)
    (H_index_bound : (Z.abs_nat (Z.of_nat i1 - Z.of_nat i2)
                     + Z.abs_nat (Z.of_nat j1 - Z.of_nat j2) <= 6)%nat),
  let gamma_ab (x y : nat) := sqrt (INR (Nat.min x y) / (INR x * INR y)) in
  let N0 := Nat.min (Nat.min a1 a2) (Nat.min b1 b2) in
  Cnorm (Csum (fun k : nat =>
    (psi a1 k *c Cconj (psi a2 k)) *c (psi b1 k *c Cconj (psi b2 k))) N0)
  <= 2 * (gamma_ab a1 b1 * gamma_ab a2 b2) *
      d_factor (sqrt (INR C)) i1 i2 * d_factor (sqrt (INR C)) j1 j2.
Proof.
  intros C HC seq1 seq2 Hsparse1 Hsparse2 Hge2_1 Hge2_2
         i1 i2 j1 j2 a1 a2 b1 b2 Ha1_eq Ha2_eq Hb1_eq Hb2_eq
         Hneq1 Hneq2 HCeq2 H_index_bound gamma_ab N0.
  subst a1 a2 b1 b2.
  set (r := sqrt (INR C)).
  assert (Hr_pos : r > 0) by (apply sqrt_lt_R0_c; apply lt_0_INR; lia).
  assert (Hr_gt1 : r > 1). {
    unfold r; rewrite <- sqrt_1.
    assert (H1lt2 : 1 < INR C). {
      subst C; simpl; lra.
    }
    apply sqrt_lt_1; [lra | apply pos_INR; lia | exact H1lt2].
  }

  set (g := fun x y : nat => sqrt (INR (Nat.min x y) / (INR x * INR y))).
  assert (Hg_pos : forall x y, (x >= 2)%nat -> (y >= 2)%nat -> g x y > 0). {
    intros x y Hx Hy; unfold g.
    apply sqrt_lt_R0_c; apply Rmult_lt_0_compat.
    - apply lt_0_INR; lia.
    - apply Rinv_0_lt_compat; apply Rmult_lt_0_compat; apply lt_0_INR; lia.
  }

  set (N0' := Nat.min (Nat.min (seq1 i1) (seq1 i2)) (Nat.min (seq2 j1) (seq2 j2))).
  assert (HN0'_eq : N0' = N0) by (unfold N0, N0'; lia).

  set (Mmax := max (max (seq1 i1) (seq2 j1)) (max (seq1 i2) (seq2 j2))).

  set (scaled := Csum (fun k : nat =>
    (Cof_real (/ g (seq1 i1) (seq2 j1)) *c (psi (seq1 i1) k *c psi (seq2 j1) k)) *c
    Cconj (Cof_real (/ g (seq1 i2) (seq2 j2)) *c (psi (seq1 i2) k *c psi (seq2 j2) k)))
    Mmax).

  set (unscaled := Csum (fun k : nat =>
    (psi (seq1 i1) k *c Cconj (psi (seq1 i2) k)) *c
    (psi (seq2 j1) k *c Cconj (psi (seq2 j2) k))) N0').

  assert (H_scale_eq : scaled = Cof_real (/ (g (seq1 i1) (seq2 j1) * g (seq1 i2) (seq2 j2))) *c unscaled). {
    unfold scaled, unscaled, Mmax.
    pose proof (product_psi_inner_decomposition (seq1 i1) (seq1 i2) (seq2 j1) (seq2 j2) g) as Hprod.
    cbv beta in Hprod.
    simpl in Hprod.
    unfold Mmax, N0', scaled, unscaled.
    rewrite Hprod.
    reflexivity.
  }

  assert (Hr_eq : r = sqrt (INR C)) by (unfold r; reflexivity).
  assert (H_norm_scaled : Cnorm scaled <= 8 / (r ^ (Z.abs_nat (Z.of_nat i1 - Z.of_nat i2)
                                                  + Z.abs_nat (Z.of_nat j1 - Z.of_nat j2)))). {
    unfold scaled, Mmax; simpl.
    exact (tensor_inner_decay C HC r Hr_eq seq1 seq2 Hsparse1 Hsparse2 Hge2_1 Hge2_2
             i1 j1 i2 j2 (seq1 i1) (seq1 i2) (seq2 j1) (seq2 j2)
             (eq_refl (seq1 i1)) (eq_refl (seq1 i2)) (eq_refl (seq2 j1)) (eq_refl (seq2 j2))
             Hneq1 Hneq2 HCeq2 H_index_bound).
  }

  assert (Hg1 : g (seq1 i1) (seq2 j1) > 0) by (apply Hg_pos; [apply Hge2_1 | apply Hge2_2]).
  assert (Hg2 : g (seq1 i2) (seq2 j2) > 0) by (apply Hg_pos; [apply Hge2_1 | apply Hge2_2]).
  assert (H_unscaled_norm : Cnorm unscaled =
    (g (seq1 i1) (seq2 j1) * g (seq1 i2) (seq2 j2)) * Cnorm scaled). {
    rewrite H_scale_eq.
    rewrite Cnorm_mult.
    rewrite (Cnorm_Cof_real_pos (/ (g (seq1 i1) (seq2 j1) * g (seq1 i2) (seq2 j2)))).
    - field_simplify.
      + reflexivity.
      + split; apply Rgt_not_eq; [exact Hg2 | exact Hg1].
    - apply Rlt_le; apply Rinv_0_lt_compat.
      exact (Rmult_lt_0_compat _ _ Hg1 Hg2).
  }

  assert (H_main : Cnorm unscaled <=
    (g (seq1 i1) (seq2 j1) * g (seq1 i2) (seq2 j2)) *
    (8 / (r ^ (Z.abs_nat (Z.of_nat i1 - Z.of_nat i2) + Z.abs_nat (Z.of_nat j1 - Z.of_nat j2))))). {
    rewrite H_unscaled_norm.
    apply Rmult_le_compat_l; [apply Rmult_le_pos; apply Rlt_le; [exact Hg1 | exact Hg2] | exact H_norm_scaled].
  }

  rewrite <- HN0'_eq.
  assert (H_g_eq : gamma_ab = g) by (subst gamma_ab g; reflexivity).
  rewrite H_g_eq.
  assert (H_factor_eq : 2 * (g (seq1 i1) (seq2 j1) * g (seq1 i2) (seq2 j2)) *
    d_factor r i1 i2 * d_factor r j1 j2 =
    (g (seq1 i1) (seq2 j1) * g (seq1 i2) (seq2 j2)) *
    (8 / (r ^ (Z.abs_nat (Z.of_nat i1 - Z.of_nat i2) + Z.abs_nat (Z.of_nat j1 - Z.of_nat j2))))). {
    unfold d_factor.
    assert (Hi_eq_false : (i1 =? i2)%nat = false) by (apply Nat.eqb_neq; auto).
    assert (Hj_eq_false : (j1 =? j2)%nat = false) by (apply Nat.eqb_neq; auto).
    rewrite Hi_eq_false, Hj_eq_false.
    simpl.
    set (d12 := Z.abs_nat (Z.of_nat i1 - Z.of_nat i2)).
    set (d34 := Z.abs_nat (Z.of_nat j1 - Z.of_nat j2)).
    set (G := g (seq1 i1) (seq2 j1) * g (seq1 i2) (seq2 j2)).
    assert (H_G_nonzero : G <> 0)
      by (apply Rgt_not_eq; apply Rmult_lt_0_compat; [exact Hg1 | exact Hg2]).
    replace (2 * G * (2 / r ^ d12) * (2 / r ^ d34))
      with (G * (2 * (2 / r ^ d12) * (2 / r ^ d34))); [| ring].
    replace (G * (8 / r ^ (d12 + d34)))
      with (G * (8 / r ^ (d12 + d34))); [| reflexivity].
    apply (Rmult_eq_reg_l G).
    - ring_simplify.
      field_simplify; [ | apply Rgt_not_eq; apply pow_lt; exact Hr_pos
                      | split; apply Rgt_not_eq; apply pow_lt; exact Hr_pos ].
      rewrite <- pow_add; ring.
    - exact H_G_nonzero.
  }
  replace (2 * (g (seq1 i1) (seq2 j1) * g (seq1 i2) (seq2 j2)) *
           d_factor r i1 i2 * d_factor r j1 j2)
    with ((g (seq1 i1) (seq2 j1) * g (seq1 i2) (seq2 j2)) *
          (8 / r ^ (Z.abs_nat (Z.of_nat i1 - Z.of_nat i2) + Z.abs_nat (Z.of_nat j1 - Z.of_nat j2)))).
  fold unscaled.
  exact H_main.
Qed.

(* 最小值取值特性 *)
Lemma min_spec (a b : nat) : Nat.min a b = a \/ Nat.min a b = b.
Proof.
  destruct (Nat.le_ge_cases a b).
  - left; apply Nat.min_l; assumption.
  - right; apply Nat.min_r; assumption.
Qed.

(* 张量核心内积衰减界（截断版） *)
Lemma tensor_core_inner_decay_bound_v2_corrected :
  forall (C : nat) (HC : (C >= 2)%nat)
    (seq1 seq2 : nat -> nat)
    (Hsparse1 : forall i : nat, (INR (seq1 (S i)) > INR C * INR (seq1 i))%R)
    (Hsparse2 : forall i : nat, (INR (seq2 (S i)) > INR C * INR (seq2 i))%R)
    (Hge2_1 : forall i, (seq1 i >= 2)%nat)
    (Hge2_2 : forall i, (seq2 i >= 2)%nat)
    (i1 i2 j1 j2 : nat) (a1 a2 b1 b2 : nat)
    (Ha1_eq : a1 = seq1 i1) (Ha2_eq : a2 = seq1 i2)
    (Hb1_eq : b1 = seq2 j1) (Hb2_eq : b2 = seq2 j2)
    (Hneq1 : i1 <> i2) (Hneq2 : j1 <> j2)
    (HCeq2 : C = 2%nat)
    (H_index_bound : (Z.abs_nat (Z.of_nat i1 - Z.of_nat i2)
                     + Z.abs_nat (Z.of_nat j1 - Z.of_nat j2) <= 6)%nat)
    (Nmin : nat),
  let N0 := Nat.min (Nat.min a1 a2) (Nat.min b1 b2) in
  (N0 <= Nmin)%nat ->
  let gamma_ab (x y : nat) := sqrt (INR (Nat.min x y) / (INR x * INR y)) in
  Cnorm (Csum (fun k : nat =>
    (psi a1 k *c Cconj (psi a2 k)) *c (psi b1 k *c Cconj (psi b2 k))) Nmin)
  <= 2 * (gamma_ab a1 b1 * gamma_ab a2 b2) *
      d_factor (sqrt (INR C)) i1 i2 * d_factor (sqrt (INR C)) j1 j2.
Proof.
  intros C HC seq1 seq2 Hsparse1 Hsparse2 Hge2_1 Hge2_2
         i1 i2 j1 j2 a1 a2 b1 b2 Ha1_eq Ha2_eq Hb1_eq Hb2_eq
         Hneq1 Hneq2 HCeq2 H_index_bound Nmin N0 Hle gamma_ab.
  subst a1 a2 b1 b2.
  set (r := sqrt (INR C)).
  assert (Hr_pos : r > 0) by (apply sqrt_lt_R0_c; apply lt_0_INR; lia).
  assert (Hr_gt1 : r > 1). {
    unfold r; rewrite <- sqrt_1.
    assert (H1lt2 : 1 < INR C). { subst C; simpl; lra. }
    apply sqrt_lt_1; [lra | apply pos_INR; lia | exact H1lt2].
  }

  set (g := fun x y : nat => sqrt (INR (Nat.min x y) / (INR x * INR y))).
  assert (Hg_pos : forall x y, (x >= 2)%nat -> (y >= 2)%nat -> g x y > 0). {
    intros x y Hx Hy; unfold g.
    apply sqrt_lt_R0_c; apply Rmult_lt_0_compat.
    - apply lt_0_INR; lia.
    - apply Rinv_0_lt_compat; apply Rmult_lt_0_compat; apply lt_0_INR; lia.
  }

  assert (H_N0_bound : forall k, (k >= N0)%nat ->
    (psi (seq1 i1) k *c Cconj (psi (seq1 i2) k)) *c
    (psi (seq2 j1) k *c Cconj (psi (seq2 j2) k)) = C0). {
    intros k Hk.
    unfold N0 in *.
    destruct (min_spec (Nat.min (seq1 i1) (seq1 i2)) (Nat.min (seq2 j1) (seq2 j2))) as [H0 | H0].
    - rewrite H0 in Hk; clear H0.
      destruct (min_spec (seq1 i1) (seq1 i2)) as [H1 | H1].
      + rewrite H1 in Hk; clear H1.
        assert (k >= seq1 i1)%nat by lia.
        rewrite (psi_ge_n_zero (seq1 i1) k H).
        repeat (rewrite ?Cmul_0_l, ?Cmul_0_r, ?Cconj_0); reflexivity.
      + rewrite H1 in Hk; clear H1.
        assert (k >= seq1 i2)%nat by lia.
        rewrite (psi_ge_n_zero (seq1 i2) k H).
        repeat (rewrite ?Cmul_0_l, ?Cmul_0_r, ?Cconj_0); reflexivity.
    - rewrite H0 in Hk; clear H0.
      destruct (min_spec (seq2 j1) (seq2 j2)) as [H1 | H1].
      + rewrite H1 in Hk; clear H1.
        assert (k >= seq2 j1)%nat by lia.
        rewrite (psi_ge_n_zero (seq2 j1) k H).
        repeat (rewrite ?Cmul_0_l, ?Cmul_0_r, ?Cconj_0); reflexivity.
      + rewrite H1 in Hk; clear H1.
        assert (k >= seq2 j2)%nat by lia.
        rewrite (psi_ge_n_zero (seq2 j2) k H).
        repeat (rewrite ?Cmul_0_l, ?Cmul_0_r, ?Cconj_0); reflexivity.
  }

  assert (Hsum_eq : Csum (fun k => (psi (seq1 i1) k *c Cconj (psi (seq1 i2) k)) *c
                                  (psi (seq2 j1) k *c Cconj (psi (seq2 j2) k))) Nmin
                  = Csum (fun k => (psi (seq1 i1) k *c Cconj (psi (seq1 i2) k)) *c
                                  (psi (seq2 j1) k *c Cconj (psi (seq2 j2) k))) N0). {
    apply (Csum_trunc_tail _ N0 Nmin).
    - exact Hle.
    - intros k [Hk1 Hk2]. apply H_N0_bound. lia.
  }

  rewrite Hsum_eq.

  assert (H_N0_case : Cnorm (Csum (fun k => (psi (seq1 i1) k *c Cconj (psi (seq1 i2) k)) *c
                                  (psi (seq2 j1) k *c Cconj (psi (seq2 j2) k))) N0)
                    <= 2 * (g (seq1 i1) (seq2 j1) * g (seq1 i2) (seq2 j2)) *
                       d_factor r i1 i2 * d_factor r j1 j2). {
    pose proof (tensor_core_inner_decay_bound C HC seq1 seq2 Hsparse1 Hsparse2 Hge2_1 Hge2_2
                i1 i2 j1 j2 (seq1 i1) (seq1 i2) (seq2 j1) (seq2 j2)
                (eq_refl _) (eq_refl _) (eq_refl _) (eq_refl _) Hneq1 Hneq2 HCeq2 H_index_bound)
      as Hcore.
    cbv beta in Hcore; simpl in Hcore.
    exact Hcore.
  }

  exact H_N0_case.
Qed.

(* 定理：张量积衰减缩放 *)
Theorem tensor_inner_decay_scaled :
  forall (C : nat) (r : R) (Hr : r = sqrt (INR C))
    (seq1 seq2 : nat -> nat)
    (Hge2_1 : forall i, (seq1 i >= 2)%nat)
    (Hge2_2 : forall i, (seq2 i >= 2)%nat)
    (Hsparse1 : forall i : nat, (INR (seq1 (S i)) > INR C * INR (seq1 i))%R)
    (Hsparse2 : forall i : nat, (INR (seq2 (S i)) > INR C * INR (seq2 i))%R)
    (i1 i2 j1 j2 : nat)
    (Hneq1 : i1 <> i2) (Hneq2 : j1 <> j2)
    (HCeq2 : C = 2%nat)
    (H_index_bound : (Z.abs_nat (Z.of_nat i1 - Z.of_nat i2)
                     + Z.abs_nat (Z.of_nat j1 - Z.of_nat j2) <= 6)%nat),
  let a1 := seq1 i1 in
  let a2 := seq1 i2 in
  let b1 := seq2 j1 in
  let b2 := seq2 j2 in
  let gamma (x y : nat) := sqrt (INR (Nat.min x y) / (INR x * INR y)) in
  let N0 := Nat.min (Nat.min a1 a2) (Nat.min b1 b2) in
  Cnorm
    (Csum (fun k : nat =>
       (Cof_real (/ gamma a1 b1) *c (psi a1 k *c psi b1 k)) *c
       Cconj (Cof_real (/ gamma a2 b2) *c (psi a2 k *c psi b2 k))) N0)
  <= 2 * d_factor r i1 i2 * d_factor r j1 j2.
Proof.
  intros C r Hr seq1 seq2 Hge2_1 Hge2_2 Hsparse1 Hsparse2
         i1 i2 j1 j2 Hneq1 Hneq2 HCeq2 H_index_bound.
  set (a1 := seq1 i1).
  set (a2 := seq1 i2).
  set (b1 := seq2 j1).
  set (b2 := seq2 j2).
  set (gamma (x y : nat) := sqrt (INR (Nat.min x y) / (INR x * INR y))).
  set (N0 := Nat.min (Nat.min a1 a2) (Nat.min b1 b2)).

  assert (HC_ge2 : (C >= 2)%nat) by (subst C; lia).

  assert (Hg_pos : forall x y, (x >= 2)%nat -> (y >= 2)%nat -> gamma x y > 0). {
    intros x y Hx Hy; unfold gamma.
    apply sqrt_lt_R0_c; apply Rmult_lt_0_compat.
    - apply lt_0_INR; lia.
    - apply Rinv_0_lt_compat; apply Rmult_lt_0_compat; apply lt_0_INR; lia.
  }

  assert (Ha1_eq : a1 = seq1 i1) by (unfold a1; reflexivity).
  assert (Ha2_eq : a2 = seq1 i2) by (unfold a2; reflexivity).
  assert (Hb1_eq : b1 = seq2 j1) by (unfold b1; reflexivity).
  assert (Hb2_eq : b2 = seq2 j2) by (unfold b2; reflexivity).

  assert (H_main :
    Cnorm (Csum (fun k : nat =>
      (psi a1 k *c Cconj (psi a2 k)) *c (psi b1 k *c Cconj (psi b2 k))) N0)
    <= 2 * (gamma a1 b1 * gamma a2 b2) * d_factor r i1 i2 * d_factor r j1 j2).
  {
    pose proof (tensor_core_inner_decay_bound
      C HC_ge2 seq1 seq2 Hsparse1 Hsparse2 Hge2_1 Hge2_2
      i1 i2 j1 j2 a1 a2 b1 b2
      Ha1_eq Ha2_eq Hb1_eq Hb2_eq
      Hneq1 Hneq2 HCeq2 H_index_bound) as H0.
    simpl in H0.
    rewrite <- Hr in H0.
    unfold gamma, N0 in *.
    exact H0.
  }

  set (Mmax := S (max (max a1 b1) (max a2 b2))).
  assert (HN0_le_M : (N0 <= Nat.pred Mmax)%nat) by (unfold N0, Mmax; lia).

  assert (Hprod :
    Csum (fun k : nat =>
      (Cof_real (/ gamma a1 b1) *c (psi a1 k *c psi b1 k)) *c
      Cconj (Cof_real (/ gamma a2 b2) *c (psi a2 k *c psi b2 k)))
      (Nat.pred Mmax)
    = Cof_real (/ (gamma a1 b1 * gamma a2 b2)) *c
      Csum (fun k : nat =>
        (psi a1 k *c Cconj (psi a2 k)) *c (psi b1 k *c Cconj (psi b2 k))) N0).
  {
    unfold Mmax.
    simpl (Nat.pred (S _)).
    exact (product_psi_inner_decomposition a1 a2 b1 b2 gamma).
  }

  set (f := fun k : nat =>
    (Cof_real (/ gamma a1 b1) *c (psi a1 k *c psi b1 k)) *c
    Cconj (Cof_real (/ gamma a2 b2) *c (psi a2 k *c psi b2 k))).

  assert (Htrunc : Csum f (Nat.pred Mmax) = Csum f N0).
  {
    apply (Csum_trunc_tail f N0 (Nat.pred Mmax)).
    - exact HN0_le_M.
    - intros k [Hk1 Hk2].
      assert (H_min_eq : N0 = a1 \/ N0 = a2 \/ N0 = b1 \/ N0 = b2). {
        unfold N0.
        destruct (Nat.min_spec (Nat.min a1 a2) (Nat.min b1 b2)) as [[_ H1] | [_ H1]];
          [rewrite H1; destruct (Nat.min_spec a1 a2) as [[_ H2] | [_ H2]];
            [rewrite H2; left; reflexivity | rewrite H2; right; left; reflexivity]
          | rewrite H1; destruct (Nat.min_spec b1 b2) as [[_ H3] | [_ H3]];
            [rewrite H3; right; right; left; reflexivity | rewrite H3; right; right; right; reflexivity]].
      }
      destruct H_min_eq as [Hmin | [Hmin | [Hmin | Hmin]]].
      + assert (Hpsi_a1 : psi a1 k = C0). {
          apply psi_ge_n_zero. rewrite Hmin in Hk1. exact Hk1.
        }
        assert (Hterm1 : psi a1 k *c psi b1 k = C0). {
          rewrite Hpsi_a1. apply C0_mul_eq_C0.
        }
        assert (Hleft : Cof_real (/ gamma a1 b1) *c (psi a1 k *c psi b1 k) = C0). {
          rewrite Hterm1. apply C0_mul_eq_C0_r.
        }
        unfold f. rewrite Hleft. apply C0_mul_eq_C0.
      + assert (Hpsi_a2 : psi a2 k = C0). {
          apply psi_ge_n_zero. rewrite Hmin in Hk1. exact Hk1.
        }
        assert (Hterm2 : psi a2 k *c psi b2 k = C0). {
          rewrite Hpsi_a2. apply C0_mul_eq_C0.
        }
        assert (Hinner : Cof_real (/ gamma a2 b2) *c (psi a2 k *c psi b2 k) = C0). {
          rewrite Hterm2. apply C0_mul_eq_C0_r.
        }
        assert (Hconj : Cconj (Cof_real (/ gamma a2 b2) *c (psi a2 k *c psi b2 k)) = C0). {
          rewrite Hinner. apply Cconj_0.
        }
        unfold f. rewrite Hconj. apply C0_mul_eq_C0_r.
      + assert (Hpsi_b1 : psi b1 k = C0). {
          apply psi_ge_n_zero. rewrite Hmin in Hk1. exact Hk1.
        }
        assert (Hterm1 : psi a1 k *c psi b1 k = C0). {
          rewrite Hpsi_b1. apply C0_mul_eq_C0_r.
        }
        assert (Hleft : Cof_real (/ gamma a1 b1) *c (psi a1 k *c psi b1 k) = C0). {
          rewrite Hterm1. apply C0_mul_eq_C0_r.
        }
        unfold f. rewrite Hleft. apply C0_mul_eq_C0.
      + assert (Hpsi_b2 : psi b2 k = C0). {
          apply psi_ge_n_zero. rewrite Hmin in Hk1. exact Hk1.
        }
        assert (Hterm2 : psi a2 k *c psi b2 k = C0). {
          rewrite Hpsi_b2. apply C0_mul_eq_C0_r.
        }
        assert (Hinner : Cof_real (/ gamma a2 b2) *c (psi a2 k *c psi b2 k) = C0). {
          rewrite Hterm2. apply C0_mul_eq_C0_r.
        }
        assert (Hconj : Cconj (Cof_real (/ gamma a2 b2) *c (psi a2 k *c psi b2 k)) = C0). {
          rewrite Hinner. apply Cconj_0.
        }
        unfold f. rewrite Hconj. apply C0_mul_eq_C0_r.
  }

  assert (H_scale_eq :
    Csum (fun k : nat =>
      (Cof_real (/ gamma a1 b1) *c (psi a1 k *c psi b1 k)) *c
      Cconj (Cof_real (/ gamma a2 b2) *c (psi a2 k *c psi b2 k))) N0
    = Cof_real (/ (gamma a1 b1 * gamma a2 b2)) *c
      Csum (fun k : nat =>
        (psi a1 k *c Cconj (psi a2 k)) *c (psi b1 k *c Cconj (psi b2 k))) N0).
  {
    assert (H_f_eq : (fun k : nat =>
      (Cof_real (/ gamma a1 b1) *c (psi a1 k *c psi b1 k)) *c
      Cconj (Cof_real (/ gamma a2 b2) *c (psi a2 k *c psi b2 k))) = f).
    { reflexivity. }
    rewrite H_f_eq.
    rewrite <- Htrunc.
    exact Hprod.
  }

  change (Cnorm (Csum (fun k : nat =>
    (Cof_real (/ gamma a1 b1) *c (psi a1 k *c psi b1 k)) *c
    Cconj (Cof_real (/ gamma a2 b2) *c (psi a2 k *c psi b2 k))) N0)
  <= 2 * d_factor r i1 i2 * d_factor r j1 j2).

  rewrite H_scale_eq.
  rewrite Cnorm_mult.

  assert (Hc_pos : 0 <= / (gamma a1 b1 * gamma a2 b2)). {
    apply Rlt_le. apply Rinv_0_lt_compat. apply Rmult_lt_0_compat.
    - apply Hg_pos; apply Hge2_1 || apply Hge2_2.
    - apply Hg_pos; apply Hge2_1 || apply Hge2_2.
  }

  rewrite (Cnorm_Cof_real_pos (/ (gamma a1 b1 * gamma a2 b2)) Hc_pos).

  assert (Hg1 : gamma a1 b1 > 0) by (apply Hg_pos; [apply Hge2_1 | apply Hge2_2]).
  assert (Hg2 : gamma a2 b2 > 0) by (apply Hg_pos; [apply Hge2_1 | apply Hge2_2]).
  assert (H_simpl :
    (2 * (gamma a1 b1 * gamma a2 b2) * d_factor r i1 i2 * d_factor r j1 j2) * / (gamma a1 b1 * gamma a2 b2)
    = 2 * d_factor r i1 i2 * d_factor r j1 j2).
  {
    field.
    split.
    - apply Rgt_not_eq. exact Hg2.
    - apply Rgt_not_eq. exact Hg1.
  }

  apply Rmult_le_compat_r with (r := / (gamma a1 b1 * gamma a2 b2)) in H_main; [ | exact Hc_pos ].

  rewrite H_simpl in H_main.

  rewrite Rmult_comm in H_main.

  exact H_main.
Qed.

(* 无重复列表中不同索引对应元素不同（显式归纳） *)
Lemma NoDup_nth_neq {A : Type} (l : list A) (default : A) (i j : nat) :
  NoDup l -> (i < length l)%nat -> (j < length l)%nat -> (i <> j)%nat -> nth i l default <> nth j l default.
Proof.
  induction l as [| x l IH] in i, j |- *.
  - simpl. intros _ H1 _ _. lia.
  - intros Hnd Hi Hj Hneq.
    inversion Hnd as [| x' l' Hnin Hnd']; subst x' l'.
    destruct i as [| i'], j as [| j'].
    + exfalso; apply Hneq; reflexivity.
    + simpl. intros H.
      apply Hnin. rewrite H. apply nth_In. simpl in Hj. lia.
    + simpl. intros H.
      apply Hnin. rewrite <- H. apply nth_In. simpl in Hi. lia.
    + simpl. intros H.
      exfalso.
      apply (IH i' j' Hnd').
      - simpl in Hi. lia.
      - simpl in Hj. lia.
      - intros Heq. apply Hneq. f_equal. exact Heq.
      - exact H.
Qed.

(* 无重复列表中不同索引元素不同（利用已有引理） *)
Lemma NoDup_nth_neq' {A : Type} (l : list A) (default : A) (i j : nat) :
  NoDup l -> (i < length l)%nat -> (j < length l)%nat -> (i <> j)%nat -> nth i l default <> nth j l default.
Proof.
  intros Hdup Hi Hj Hneq Heq.
  apply Hneq.
  eapply NoDup_nth; eauto.
Qed.

(* gamma函数的乘积上界 *)

(* 最小值不小于2 *)
Lemma min_ge_2 (x y : nat) : (x >= 2)%nat -> (y >= 2)%nat -> (Nat.min x y >= 2)%nat.
Proof. intros Hx Hy. apply Nat.min_glb; assumption. Qed.

(* 两自然数不小于2时其INR乘积为正 *)
Lemma INR_mul_pos (x y : nat) : (x >= 2)%nat -> (y >= 2)%nat -> INR x * INR y > 0.
Proof. intros; apply Rmult_lt_0_compat; apply lt_0_INR; lia. Qed.

(* 自然数差的Z绝对值自然数为零则两数相等 *)
Lemma Z_abs_nat_eq_0_inj (a b : nat) : Z.abs_nat (Z.of_nat a - Z.of_nat b) = 0%nat -> a = b.
Proof. intros H. apply Nat2Z.inj. zify. lia. Qed.

(* 定理：平坦化二维phi特征内积衰减界 *)
Theorem phi_flat_decay (C : nat) (HCeq2 : C = 2%nat)
  (seq1 seq2 : nat -> nat)
  (Hsparse1 : forall i : nat, INR (seq1 (S i)) > INR C * INR (seq1 i))
  (Hsparse2 : forall i : nat, INR (seq2 (S i)) > INR C * INR (seq2 i))
  (Hge2_1 : forall i : nat, (seq1 i >= 2)%nat)
  (Hge2_2 : forall i : nat, (seq2 i >= 2)%nat)
  (I1 I2 : list nat)
  (Hdup1 : NoDup I1) (Hsorted1 : Sorted Nat.lt I1)
  (Hdup2 : NoDup I2) (Hsorted2 : Sorted Nat.lt I2)
  (n1 n2 : nat) (Hn1 : n1 = length I1) (Hn2 : n2 = length I2)
  (HI1 : I1 = seq 0 n1) (HI2 : I2 = seq 0 n2)
  (a b : nat -> nat)
  (Ha : a = fun i : nat => nth i (map seq1 I1) 0%nat)
  (Hb : b = fun j : nat => nth j (map seq2 I2) 0%nat)
  (gamma : nat -> nat -> R)
  (Hgamma : gamma = fun i j => sqrt (INR (Nat.min (a i) (b j)) / (INR (a i) * INR (b j))))
  (phi2D_norm : nat -> nat -> nat -> Complex)
  (Hphi2D_norm : phi2D_norm = fun i j k => Cof_real (/ gamma i j) *c (psi (a i) k *c psi (b j) k))
  (maxIdx1 maxIdx2 : nat)
  (HmaxIdx1 : maxIdx1 = fold_right Nat.max 0%nat I1)
  (HmaxIdx2 : maxIdx2 = fold_right Nat.max 0%nat I2)
  (M : nat)
  (HM : M = S (max (seq1 maxIdx1) (seq2 maxIdx2)))
  (r : R) (Hr : r = sqrt (INR C))
  (phi_flat : nat -> nat -> Complex)
  (Hphi_flat : phi_flat = fun idx k => phi2D_norm (idx / n2)%nat (idx mod n2)%nat k)
  (delta_pair : nat -> nat -> R)
  (Hdelta_pair : delta_pair = fun idx1 idx2 : nat =>
     d_factor r (idx1 / n2) (idx2 / n2) * d_factor r (idx1 mod n2) (idx2 mod n2))
  (idx1 idx2 : nat) (Hneq : idx1 <> idx2) (Hlt1 : (idx1 < n1 * n2)%nat) (Hlt2 : (idx2 < n1 * n2)%nat)
  (H_index_bound : (Z.abs_nat (Z.of_nat (idx1 / n2) - Z.of_nat (idx2 / n2)) +
                    Z.abs_nat (Z.of_nat (idx1 mod n2) - Z.of_nat (idx2 mod n2)) <= 6)%nat)
  : Cnorm (Csum (fun k => phi_flat idx1 k *c Cconj (phi_flat idx2 k)) (Nat.pred M))
    <= 8 * delta_pair idx1 idx2.
Proof.
  assert (HC_ge2 : (C >= 2)%nat) by (subst C; lia).

  assert (Csum_scal_l : forall (c : Complex) (f : nat -> Complex) (m : nat),
    Csum (fun i => c *c f i) m = c *c Csum f m).
  { intros c f m. induction m as [|m IH]; simpl.
    - rewrite Cmul_0_r; reflexivity.
    - rewrite IH, Cmul_add_distr_l; reflexivity. }

  assert (Csum_scal_r : forall (c : Complex) (f : nat -> Complex) (m : nat),
    Csum (fun i => f i *c c) m = Csum f m *c c).
  { intros c f m. induction m as [|m IH]; simpl.
    - rewrite Cmul_0_l; reflexivity.
    - rewrite IH, Cmul_add_distr_r; reflexivity. }

  assert (Hr_pos : r > 0) by (subst r; apply sqrt_lt_R0_c; apply lt_0_INR; lia).

  assert (Hmax_bound1 : forall x, In x I1 -> (seq1 x <= seq1 maxIdx1)%nat).
  { intros x Hin.
    assert (Hle : (x <= maxIdx1)%nat).
    { rewrite HmaxIdx1; apply fold_right_max_ge; exact Hin. }
    destruct (proj1 (lt_eq_cases _ _) Hle) as [Hlt | Heq];
    [ apply Nat.lt_le_incl; eapply seq_strict_growth_lt; eauto; try lia
    | subst x; apply Nat.le_refl ]. }

  assert (Hmax_bound2 : forall x, In x I2 -> (seq2 x <= seq2 maxIdx2)%nat).
  { intros x Hin.
    assert (Hle : (x <= maxIdx2)%nat).
    { rewrite HmaxIdx2; apply fold_right_max_ge; exact Hin. }
    destruct (proj1 (lt_eq_cases _ _) Hle) as [Hlt | Heq];
    [ apply Nat.lt_le_incl; eapply seq_strict_growth_lt; eauto; try lia
    | subst x; apply Nat.le_refl ]. }

  set (i1 := (idx1 / n2)%nat). set (j1 := (idx1 mod n2)%nat).
  set (i2 := (idx2 / n2)%nat). set (j2 := (idx2 mod n2)%nat).
  assert (0 < n2)%nat as Hn2_pos by (destruct n2; [exfalso; lia | lia]).
  assert (i1 < n1)%nat as Hi1 by (apply Div0.div_lt_upper_bound; lia).
  assert (j1 < n2)%nat as Hj1 by (apply Nat.mod_upper_bound; lia).
  assert (i2 < n1)%nat as Hi2 by (apply Div0.div_lt_upper_bound; lia).
  assert (j2 < n2)%nat as Hj2 by (apply Nat.mod_upper_bound; lia).

  assert (Hi1_len : (i1 < length I1)%nat) by (rewrite <- Hn1; exact Hi1).
  assert (Hi2_len : (i2 < length I1)%nat) by (rewrite <- Hn1; exact Hi2).
  assert (Hj1_len : (j1 < length I2)%nat) by (rewrite <- Hn2; exact Hj1).
  assert (Hj2_len : (j2 < length I2)%nat) by (rewrite <- Hn2; exact Hj2).

  assert (i1 <> i2 \/ j1 <> j2) as H_ij_neq.
  { destruct (Nat.eq_dec i1 i2) as [eq_i|neq_i].
    - destruct (Nat.eq_dec j1 j2) as [eq_j|neq_j].
      + exfalso. apply Hneq.
        rewrite (Nat.div_mod_eq idx1 n2), (Nat.div_mod_eq idx2 n2).
        fold i1 j1 i2 j2. rewrite eq_i, eq_j. reflexivity.
      + right; exact neq_j.
    - left; exact neq_i. }

  set (a1 := a i1). set (a2 := a i2). set (b1 := b j1). set (b2 := b j2).
  set (g1 := gamma i1 j1). set (g2 := gamma i2 j2).
  set (N0 := Nat.min (Nat.min a1 a2) (Nat.min b1 b2)).

  assert (Ha1_eq_seq : a1 = seq1 (nth i1 I1 0%nat)).
  { unfold a1; rewrite Ha; simpl; rewrite H_nth_map with (d0:=0%nat) by exact Hi1_len; reflexivity. }
  assert (Ha2_eq_seq : a2 = seq1 (nth i2 I1 0%nat)).
  { unfold a2; rewrite Ha; simpl; rewrite H_nth_map with (d0:=0%nat) by exact Hi2_len; reflexivity. }
  assert (Hb1_eq_seq : b1 = seq2 (nth j1 I2 0%nat)).
  { unfold b1; rewrite Hb; simpl; rewrite H_nth_map with (d0:=0%nat) by exact Hj1_len; reflexivity. }
  assert (Hb2_eq_seq : b2 = seq2 (nth j2 I2 0%nat)).
  { unfold b2; rewrite Hb; simpl; rewrite H_nth_map with (d0:=0%nat) by exact Hj2_len; reflexivity. }

  assert (Hin_i1 : In (nth i1 I1 0%nat) I1) by (apply nth_In; exact Hi1_len).
  assert (Hin_i2 : In (nth i2 I1 0%nat) I1) by (apply nth_In; exact Hi2_len).
  assert (Hin_j1 : In (nth j1 I2 0%nat) I2) by (apply nth_In; exact Hj1_len).
  assert (Hin_j2 : In (nth j2 I2 0%nat) I2) by (apply nth_In; exact Hj2_len).

  set (M0 := S (max (max a1 b1) (max a2 b2))).
  assert (M0_le_M : (M0 <= M)%nat).
  { unfold M0; rewrite HM.
    apply le_n_S.
    assert (Ha1_le : (a1 <= seq1 maxIdx1)%nat) by (rewrite Ha1_eq_seq; apply Hmax_bound1; exact Hin_i1).
    assert (Ha2_le : (a2 <= seq1 maxIdx1)%nat) by (rewrite Ha2_eq_seq; apply Hmax_bound1; exact Hin_i2).
    assert (Hb1_le : (b1 <= seq2 maxIdx2)%nat) by (rewrite Hb1_eq_seq; apply Hmax_bound2; exact Hin_j1).
    assert (Hb2_le : (b2 <= seq2 maxIdx2)%nat) by (rewrite Hb2_eq_seq; apply Hmax_bound2; exact Hin_j2).
    set (S1 := seq1 maxIdx1). set (S2 := seq2 maxIdx2).
    assert (Hmax1 : (max a1 b1 <= max S1 S2)%nat) by (apply Nat.max_le_compat; assumption).
    assert (Hmax2 : (max a2 b2 <= max S1 S2)%nat) by (apply Nat.max_le_compat; assumption).
    destruct (Nat.max_dec (max a1 b1) (max a2 b2)) as [Hmax12 | Hmax21];
      rewrite Hmax12 || rewrite Hmax21; assumption. }

  assert (Htrunc_eq :
    Csum (fun k => phi_flat idx1 k *c Cconj (phi_flat idx2 k)) (Nat.pred M) =
    Csum (fun k => phi_flat idx1 k *c Cconj (phi_flat idx2 k)) (Nat.pred M0)).
  { set (f := fun k => phi_flat idx1 k *c Cconj (phi_flat idx2 k)).
    apply Csum_trunc_tail with (M := Nat.pred M0) (N := Nat.pred M).
    - clear -M0_le_M; lia.
    - intros k [Hk1 Hk2].
      unfold f; rewrite Hphi_flat, Hphi2D_norm.
      fold i1 j1 i2 j2 a1 a2 b1 b2 g1 g2.
      assert (Hk_max : (k >= max (max a1 b1) (max a2 b2))%nat).
      { unfold M0 in Hk1; simpl in Hk1; exact Hk1. }
      assert (Hk_ge_a1 : (k >= a1)%nat).
      { eapply Nat.le_trans; [ | exact Hk_max].
        apply Nat.le_trans with (max a1 b1); [apply Nat.le_max_l | apply Nat.le_max_l]. }
      rewrite (psi_ge_n_zero a1 k Hk_ge_a1).
      apply Complex_eq; simpl; ring. }

  rewrite Htrunc_eq.

  rewrite Hphi_flat, Hphi2D_norm, Hdelta_pair.
  fold i1 j1 i2 j2 a1 a2 b1 b2 g1 g2.
  set (gamma_ab (x y : nat) := sqrt (INR (Nat.min x y) / (INR x * INR y))).
  assert (Hg1_eq : gamma_ab a1 b1 = g1).
  { unfold gamma_ab, g1, a1, b1. rewrite Hgamma. reflexivity. }
  assert (Hg2_eq : gamma_ab a2 b2 = g2).
  { unfold gamma_ab, g2, a2, b2. rewrite Hgamma. reflexivity. }
  rewrite <- Hg1_eq, <- Hg2_eq.
  pose proof (product_psi_inner_decomposition a1 a2 b1 b2 gamma_ab) as Hprod.
  simpl in Hprod.
  unfold M0; simpl.
  rewrite Hprod.
  rewrite Hg1_eq, Hg2_eq.

  rewrite Cnorm_mult.
  assert (Ha1_ge2 : (a1 >= 2)%nat) by
    (rewrite Ha1_eq_seq; exact (Hge2_1 (nth i1 I1 0%nat))).
  assert (Hb1_ge2 : (b1 >= 2)%nat) by
    (rewrite Hb1_eq_seq; exact (Hge2_2 (nth j1 I2 0%nat))).
  assert (Ha2_ge2 : (a2 >= 2)%nat) by
    (rewrite Ha2_eq_seq; exact (Hge2_1 (nth i2 I1 0%nat))).
  assert (Hb2_ge2 : (b2 >= 2)%nat) by
    (rewrite Hb2_eq_seq; exact (Hge2_2 (nth j2 I2 0%nat))).

  assert (Hg1_pos : 0 < g1).
  { unfold g1; rewrite Hgamma.
    apply sqrt_lt_R0_c.
    apply Rdiv_lt_0_compat.
    - apply lt_0_INR.
      pose proof (min_ge_2 (a i1) (b j1) Ha1_ge2 Hb1_ge2).
      lia.
    - apply INR_mul_pos; assumption. }

  assert (Hg2_pos : 0 < g2).
  { unfold g2; rewrite Hgamma.
    apply sqrt_lt_R0_c.
    apply Rdiv_lt_0_compat.
    - apply lt_0_INR.
      pose proof (min_ge_2 (a i2) (b j2) Ha2_ge2 Hb2_ge2).
      lia.
    - apply INR_mul_pos; assumption. }

  assert (Hc_pos : 0 <= / (g1 * g2)).
  { apply Rlt_le; apply Rinv_0_lt_compat; apply Rmult_lt_0_compat; auto. }

  set (S_inner := Csum (fun k => (psi a1 k *c Cconj (psi a2 k)) *c (psi b1 k *c Cconj (psi b2 k))) N0).

  change (Csum (fun k : nat => (psi a1 k *c Cconj (psi a2 k)) *c (psi b1 k *c Cconj (psi b2 k))) N0)
    with S_inner.
  rewrite (Cnorm_Cof_real_pos (/ (g1 * g2)) Hc_pos).

  destruct (Nat.eq_dec i1 i2) as [Heq_i | Hneq_i].
  - assert (Hneq_j : j1 <> j2).
    { destruct H_ij_neq as [Hni | Hnj]; [contradiction (Hni Heq_i) | exact Hnj]. }
    assert (Ha_eq : a1 = a2) by (unfold a1, a2; rewrite Heq_i; reflexivity).

    assert (H_core_bound : Cnorm S_inner <= g1 * g2).
    { unfold S_inner, N0, g1, g2, a2; rewrite Ha_eq, Heq_i, Hgamma.
      apply (inner_product_single_tensor_bound C r Hr i1 i1 j1 j2 a2 a2 b1 b2 0%nat 0%nat
                  HC_ge2 Ha2_ge2 Ha2_ge2 Hb1_ge2 Hb2_ge2).
      - replace ((INR C) ^ 0) with 1%R by (simpl; ring).
        rewrite Rmult_1_l.
        apply Rle_ge; apply le_INR.
        eapply Nat.le_trans; [apply Nat.le_min_l | apply Nat.le_max_l].
      - replace ((INR C) ^ 0) with 1%R by (simpl; ring).
        rewrite Rmult_1_l.
        apply Rle_ge; apply le_INR.
        eapply Nat.le_trans; [apply Nat.le_min_l | apply Nat.le_max_l]. }

    assert (H_target_le_1 : / (g1 * g2) * Cnorm S_inner <= 1).
    { apply Rle_trans with (/ (g1 * g2) * (g1 * g2)).
      - apply Rmult_le_compat_l; [apply Rlt_le; apply Rinv_0_lt_compat;
          apply Rmult_lt_0_compat; auto | exact H_core_bound].
      - assert (Hfield : / (g1 * g2) * (g1 * g2) = 1).
        { apply Rinv_l; apply Rgt_not_eq; apply Rmult_lt_0_compat; auto. }
        rewrite Hfield; apply Rle_refl. }

    set (d_j := Z.abs_nat (Z.of_nat j1 - Z.of_nat j2)).
    assert (Hd_j_le_6 : (d_j <= 6)%nat).
    { unfold d_j.
      assert (Htmp : (Z.abs_nat (Z.of_nat j1 - Z.of_nat j2) <=
                      Z.abs_nat (Z.of_nat i1 - Z.of_nat i2) + 
                      Z.abs_nat (Z.of_nat j1 - Z.of_nat j2))%nat).
      { clear; lia. }
      eapply Nat.le_trans; [exact Htmp | exact H_index_bound]. }

    assert (H_eight_d_factor_ge_1 : 1 <= 8 * d_factor r j1 j2).
    { unfold d_factor.
      destruct (j1 =? j2)%nat eqn:Heq_j.
      + apply Nat.eqb_eq in Heq_j; exfalso; apply Hneq_j; exact Heq_j.
      + rewrite Hr, HCeq2.
        change (INR 2) with (2%R).
        assert (H_sqrt2_lt_2 : sqrt 2 < 2).
        { apply (Rlt_le_trans _ (sqrt 4)).
          - apply sqrt_lt_1; lra.
          - change (sqrt 4) with (sqrt (2*2)).
            rewrite sqrt_square; [|lra].
            apply Rle_refl. }
        assert (Hd_cases : d_j = 0%nat \/ d_j = 1%nat \/ d_j = 2%nat \/ d_j = 3%nat \/
                          d_j = 4%nat \/ d_j = 5%nat \/ d_j = 6%nat) by lia.
        destruct Hd_cases as [Hd0|[Hd1|[Hd2|[Hd3|[Hd4|[Hd5|Hd6]]]]]].
        - exfalso; apply Hneq_j; eapply Z_abs_nat_eq_0_inj; eassumption.
        - unfold d_j in Hd1; rewrite Hd1; replace (sqrt 2 ^ 1) with (sqrt 2) by (simpl; ring).
          apply (Rmult_le_reg_r (sqrt 2) 1 (8 * (2 / sqrt 2))); [apply sqrt_lt_R0_c; lra|].
          replace (1 * sqrt 2) with (sqrt 2) by ring.
          replace (8 * (2 / sqrt 2) * sqrt 2) with 16
            by (field; apply Rgt_not_eq; apply sqrt_lt_R0_c; lra).
          apply Rle_trans with 2; [apply Rlt_le; exact H_sqrt2_lt_2 | lra].
        - unfold d_j in Hd2; rewrite Hd2.
          simpl.
          rewrite Rmult_1_r.
          fold (Rsqr (sqrt 2)).
          rewrite Rsqr_sqrt; [|lra].
          field_simplify; lra.
        - unfold d_j in Hd3; rewrite Hd3.
          replace (sqrt 2 ^ 3) with (2 * sqrt 2).
          2: { replace (sqrt 2 ^ 3) with ((sqrt 2 * sqrt 2) * sqrt 2) by (simpl; ring).
               fold (Rsqr (sqrt 2)).
               rewrite Rsqr_sqrt; [|lra].
               ring. }
          apply (Rmult_le_reg_r (sqrt 2) 1 (8 * (2 / (2 * sqrt 2)))); [apply sqrt_lt_R0_c; lra|].
          replace (1 * sqrt 2) with (sqrt 2) by ring.
          replace (8 * (2 / (2 * sqrt 2)) * sqrt 2) with 8
            by (field; apply Rgt_not_eq; apply sqrt_lt_R0_c; lra).
          apply Rle_trans with 2; [apply Rlt_le; exact H_sqrt2_lt_2 | lra].
        - unfold d_j in Hd4; rewrite Hd4.
          replace (sqrt 2 ^ 4) with 4.
          2: { replace (sqrt 2 ^ 4) with ((sqrt 2 * sqrt 2) * (sqrt 2 * sqrt 2)) by (simpl; ring).
               repeat fold (Rsqr (sqrt 2)).
               rewrite Rsqr_sqrt; [|lra].
               ring. }
          field_simplify; lra.
        - unfold d_j in Hd5; rewrite Hd5.
          replace (sqrt 2 ^ 5) with (4 * sqrt 2).
          2: { replace (sqrt 2 ^ 5) with ((sqrt 2 * sqrt 2) * (sqrt 2 * sqrt 2) * sqrt 2) by (simpl; ring).
               repeat fold (Rsqr (sqrt 2)).
               rewrite Rsqr_sqrt; [|lra].
               ring. }
          apply (Rmult_le_reg_r (sqrt 2) 1 (8 * (2 / (4 * sqrt 2)))); [apply sqrt_lt_R0_c; lra|].
          replace (1 * sqrt 2) with (sqrt 2) by ring.
          replace (8 * (2 / (4 * sqrt 2)) * sqrt 2) with 4
            by (field; apply Rgt_not_eq; apply sqrt_lt_R0_c; lra).
          apply Rle_trans with 2; [apply Rlt_le; exact H_sqrt2_lt_2 | lra].
        - unfold d_j in Hd6; rewrite Hd6.
          replace (sqrt 2 ^ 6) with 8.
          2: { replace (sqrt 2 ^ 6) with ((sqrt 2 * sqrt 2) * (sqrt 2 * sqrt 2) * (sqrt 2 * sqrt 2)) by (simpl; ring).
               repeat fold (Rsqr (sqrt 2)).
               rewrite Rsqr_sqrt; [|lra].
               ring. }
          field_simplify; lra.
    }

    rewrite Heq_i.
    assert (Hdf_eq_1 : d_factor r i2 i2 = 1).
    { unfold d_factor; rewrite Nat.eqb_refl; reflexivity. }
    rewrite Hdf_eq_1, Rmult_1_l.
    eapply Rle_trans; [exact H_target_le_1 | exact H_eight_d_factor_ge_1].
  - destruct (Nat.eq_dec j1 j2) as [Heq_j | Hneq_j].
    + assert (Hneq_i1 : i1 <> i2).
      { destruct H_ij_neq as [Hni | Hnj]; [exact Hni | contradiction (Hnj Heq_j)]. }
      assert (Hb_eq : b1 = b2) by (unfold b1, b2; rewrite Heq_j; reflexivity).

      assert (H_core_bound : Cnorm S_inner <= g1 * g2).
      { unfold S_inner, N0, g1, g2, b2; rewrite Hb_eq, Heq_j, Hgamma.
        apply (inner_product_single_tensor_bound C r Hr i1 i2 j1 j1 a1 a2 b2 b2 0%nat 0%nat
                    HC_ge2 Ha1_ge2 Ha2_ge2 Hb2_ge2 Hb2_ge2).
        - replace ((INR C) ^ 0) with 1%R by (simpl; ring).
          rewrite Rmult_1_l.
          apply Rle_ge; apply le_INR.
          eapply Nat.le_trans; [apply Nat.le_min_l | apply Nat.le_max_l].
        - replace ((INR C) ^ 0) with 1%R by (simpl; ring).
          rewrite Rmult_1_l.
          apply Rle_ge; apply le_INR.
          eapply Nat.le_trans; [apply Nat.le_min_l | apply Nat.le_max_l]. }

      assert (H_target_le_1 : / (g1 * g2) * Cnorm S_inner <= 1).
      { apply Rle_trans with (/ (g1 * g2) * (g1 * g2)).
        - apply Rmult_le_compat_l; [apply Rlt_le; apply Rinv_0_lt_compat;
            apply Rmult_lt_0_compat; auto | exact H_core_bound].
        - assert (Hfield : / (g1 * g2) * (g1 * g2) = 1).
          { apply Rinv_l; apply Rgt_not_eq; apply Rmult_lt_0_compat; auto. }
          rewrite Hfield; apply Rle_refl. }

      set (d_i := Z.abs_nat (Z.of_nat i1 - Z.of_nat i2)).
      assert (Hd_i_le_6 : (d_i <= 6)%nat).
      { unfold d_i.
        assert (Htmp : (Z.abs_nat (Z.of_nat i1 - Z.of_nat i2) <=
                        Z.abs_nat (Z.of_nat i1 - Z.of_nat i2) + 
                        Z.abs_nat (Z.of_nat j1 - Z.of_nat j2))%nat).
        { clear; lia. }
        eapply Nat.le_trans; [exact Htmp | exact H_index_bound]. }

      assert (H_eight_d_factor_ge_1 : 1 <= 8 * d_factor r i1 i2).
      { unfold d_factor.
        destruct (i1 =? i2)%nat eqn:Heq_i.
        + apply Nat.eqb_eq in Heq_i; exfalso; apply Hneq_i; exact Heq_i.
        + rewrite Hr, HCeq2.
          change (INR 2) with (2%R).
          assert (H_sqrt2_lt_2 : sqrt 2 < 2).
          { apply (Rlt_le_trans _ (sqrt 4)).
            - apply sqrt_lt_1; lra.
            - assert (H_sqrt4_eq : sqrt 4 = 2) by (apply sqrt_square; lra).
              rewrite H_sqrt4_eq.
              apply Rle_refl. }
          assert (Hd_cases : d_i = 0%nat \/ d_i = 1%nat \/ d_i = 2%nat \/ d_i = 3%nat \/
                            d_i = 4%nat \/ d_i = 5%nat \/ d_i = 6%nat) by lia.
          destruct Hd_cases as [Hd0|[Hd1|[Hd2|[Hd3|[Hd4|[Hd5|Hd6]]]]]].
          - exfalso; apply Hneq_i; eapply Z_abs_nat_eq_0_inj; eassumption.
          - unfold d_i in Hd1; rewrite Hd1; replace (sqrt 2 ^ 1) with (sqrt 2) by (simpl; ring).
            apply (Rmult_le_reg_r (sqrt 2) 1 (8 * (2 / sqrt 2))); [apply sqrt_lt_R0_c; lra|].
            replace (1 * sqrt 2) with (sqrt 2) by ring.
            replace (8 * (2 / sqrt 2) * sqrt 2) with 16
              by (field; apply Rgt_not_eq; apply sqrt_lt_R0_c; lra).
            apply Rle_trans with 2; [apply Rlt_le; exact H_sqrt2_lt_2 | lra].
          - unfold d_i in Hd2; rewrite Hd2.
            simpl.
            rewrite Rmult_1_r.
            fold (Rsqr (sqrt 2)).
            rewrite Rsqr_sqrt; [|lra].
            field_simplify; lra.
          - unfold d_i in Hd3; rewrite Hd3.
            replace (sqrt 2 ^ 3) with (2 * sqrt 2).
            2: { replace (sqrt 2 ^ 3) with ((sqrt 2 * sqrt 2) * sqrt 2) by (simpl; ring).
                 fold (Rsqr (sqrt 2)).
                 rewrite Rsqr_sqrt; [|lra].
                 ring. }
            apply (Rmult_le_reg_r (sqrt 2) 1 (8 * (2 / (2 * sqrt 2)))); [apply sqrt_lt_R0_c; lra|].
            replace (1 * sqrt 2) with (sqrt 2) by ring.
            replace (8 * (2 / (2 * sqrt 2)) * sqrt 2) with 8
              by (field; apply Rgt_not_eq; apply sqrt_lt_R0_c; lra).
            apply Rle_trans with 2; [apply Rlt_le; exact H_sqrt2_lt_2 | lra].
          - unfold d_i in Hd4; rewrite Hd4.
            replace (sqrt 2 ^ 4) with 4.
            2: { replace (sqrt 2 ^ 4) with ((sqrt 2 * sqrt 2) * (sqrt 2 * sqrt 2)) by (simpl; ring).
                 repeat fold (Rsqr (sqrt 2)).
                 rewrite Rsqr_sqrt; [|lra].
                 ring. }
            field_simplify; lra.
          - unfold d_i in Hd5; rewrite Hd5.
            replace (sqrt 2 ^ 5) with (4 * sqrt 2).
            2: { replace (sqrt 2 ^ 5) with ((sqrt 2 * sqrt 2) * (sqrt 2 * sqrt 2) * sqrt 2) by (simpl; ring).
                 repeat fold (Rsqr (sqrt 2)).
                 rewrite Rsqr_sqrt; [|lra].
                 ring. }
            apply (Rmult_le_reg_r (sqrt 2) 1 (8 * (2 / (4 * sqrt 2)))); [apply sqrt_lt_R0_c; lra|].
            replace (1 * sqrt 2) with (sqrt 2) by ring.
            replace (8 * (2 / (4 * sqrt 2)) * sqrt 2) with 4
              by (field; apply Rgt_not_eq; apply sqrt_lt_R0_c; lra).
            apply Rle_trans with 2; [apply Rlt_le; exact H_sqrt2_lt_2 | lra].
          - unfold d_i in Hd6; rewrite Hd6.
            replace (sqrt 2 ^ 6) with 8.
            2: { replace (sqrt 2 ^ 6) with ((sqrt 2 * sqrt 2) * (sqrt 2 * sqrt 2) * (sqrt 2 * sqrt 2)) by (simpl; ring).
                 repeat fold (Rsqr (sqrt 2)).
                 rewrite Rsqr_sqrt; [|lra].
                 ring. }
            field_simplify; lra.
      }

      rewrite Heq_j.
      assert (Hdf_eq_1_j : d_factor r j2 j2 = 1).
      { unfold d_factor; rewrite Nat.eqb_refl; reflexivity. }
      rewrite Hdf_eq_1_j, Rmult_1_r.
      eapply Rle_trans; [exact H_target_le_1 | exact H_eight_d_factor_ge_1].
    + assert (Ha1_seq : a1 = seq1 i1).
      { unfold a1. rewrite Ha.
        rewrite HI1.
        assert (H_len1 : (i1 < length (seq 0 n1))%nat) by (rewrite length_seq; exact Hi1).
        rewrite (H_nth_map nat nat seq1 (seq 0 n1) 0%nat 0%nat i1 H_len1).
        rewrite nth_seq_general with (start := 0%nat) by exact Hi1.
        rewrite Nat.add_0_l. reflexivity. }
      assert (Ha2_seq : a2 = seq1 i2).
      { unfold a2. rewrite Ha.
        rewrite HI1.
        assert (H_len2 : (i2 < length (seq 0 n1))%nat) by (rewrite length_seq; exact Hi2).
        rewrite (H_nth_map nat nat seq1 (seq 0 n1) 0%nat 0%nat i2 H_len2).
        rewrite nth_seq_general with (start := 0%nat) by exact Hi2.
        rewrite Nat.add_0_l. reflexivity. }
      assert (Hb1_seq : b1 = seq2 j1).
      { unfold b1. rewrite Hb.
        rewrite HI2.
        assert (H_len3 : (j1 < length (seq 0 n2))%nat) by (rewrite length_seq; exact Hj1).
        rewrite (H_nth_map nat nat seq2 (seq 0 n2) 0%nat 0%nat j1 H_len3).
        rewrite nth_seq_general with (start := 0%nat) by exact Hj1.
        rewrite Nat.add_0_l. reflexivity. }
      assert (Hb2_seq : b2 = seq2 j2).
      { unfold b2. rewrite Hb.
        rewrite HI2.
        assert (H_len4 : (j2 < length (seq 0 n2))%nat) by (rewrite length_seq; exact Hj2).
        rewrite (H_nth_map nat nat seq2 (seq 0 n2) 0%nat 0%nat j2 H_len4).
        rewrite nth_seq_general with (start := 0%nat) by exact Hj2.
        rewrite Nat.add_0_l. reflexivity. }

      pose proof (tensor_core_inner_decay_bound_v2_corrected
        C HC_ge2 seq1 seq2 Hsparse1 Hsparse2 Hge2_1 Hge2_2
        i1 i2 j1 j2 a1 a2 b1 b2
        Ha1_seq Ha2_seq Hb1_seq Hb2_seq
        Hneq_i Hneq_j HCeq2 H_index_bound N0 (le_refl N0)) as Htensor.

      rewrite <- Hr in Htensor.
      unfold S_inner in Htensor.

      eapply Rle_trans.
      { apply Rmult_le_compat_l.
        - apply Rlt_le; apply Rinv_0_lt_compat; apply Rmult_lt_0_compat; auto.
        - exact Htensor. }
      assert (Hg1_sq_eq : sqrt (INR (Nat.min a1 b1) / (INR a1 * INR b1)) = g1).
      { unfold g1, a1, b1; rewrite Hgamma; reflexivity. }
      assert (Hg2_sq_eq : sqrt (INR (Nat.min a2 b2) / (INR a2 * INR b2)) = g2).
      { unfold g2, a2, b2; rewrite Hgamma; reflexivity. }
      rewrite Hg1_sq_eq, Hg2_sq_eq.
      replace (/ (g1 * g2) * (2 * (g1 * g2) * d_factor r i1 i2 * d_factor r j1 j2))
        with (2 * d_factor r i1 i2 * d_factor r j1 j2).
      2: { field. split; apply Rgt_not_eq; assumption. }

      assert (Hd_nonneg : forall i j, 0 <= d_factor r i j).
      { intros i j; unfold d_factor.
        destruct (i =? j)%nat eqn:Heq.
        - lra.
        - assert (H_pow_pos : 0 < r ^ Z.abs_nat (Z.of_nat i - Z.of_nat j)).
          { apply pow_lt; exact Hr_pos. }
          apply Rmult_le_pos; [lra|].
          apply Rlt_le; apply Rinv_0_lt_compat; exact H_pow_pos. }
      rewrite Rmult_assoc.
      apply Rmult_le_compat_r.
      - apply Rmult_le_pos; apply Hd_nonneg.
      - lra.
Qed.

(* 商的幂等于幂的商 *)

(* 乘积的幂分配律 *)
Lemma pow_mul : forall (x y : R) (n : nat), (x * y)^n = x^n * y^n.
Proof.
  induction n; simpl; intros; [ring | rewrite IHn; ring].
Qed.

(* 非零数的幂非零 *)
Lemma pow_nonzero : forall (x : R) (n : nat), x <> 0 -> x^n <> 0.
Proof.
  induction n; simpl; intros H.
  - exact R1_neq_R0.
  - apply Rmult_integral_contrapositive; split; [exact H | apply IHn; exact H].
Qed.

(* 逆的幂等于幂的逆 *)
Lemma pow_inv : forall (x : R) (n : nat), x <> 0 -> (/ x)^n = / (x^n).
Proof.
  induction n; intros; simpl; auto.
  - rewrite Rinv_1; reflexivity.
  - rewrite Rinv_mult; auto; try (apply pow_nonzero; auto).
    rewrite IHn; auto.
Qed.

(* 商的幂等于幂的商（基于除法的精确形式） *)
Lemma pow_div_exact : forall (x y : R) (n : nat), y <> 0 -> (x / y)^n = x^n / y^n.
Proof.
  intros x y n H; unfold Rdiv.
  rewrite pow_mul.          (* (x * / y)^n = x^n * (/ y)^n *)
  rewrite pow_inv by exact H. (* 用 H : y <> 0 立即解决 pow_inv 的前提 *)
  reflexivity.
Qed.

(* 实数六次幂化为平方的立方 *)
Lemma pow_sq_cube_eq : forall a : R, a^6 = (a^2)^3.
Proof.
  intro a.
  simpl.
  ring.
Qed.

(* 非负实数平方根的平方恒等式 *)
Require Import Stdlib.Reals.Reals.
Lemma sqrt_pow_2 : forall x : R, 0 <= x -> (sqrt x)^2 = x.
Proof.
  intros x Hx.
  replace ((sqrt x)^2) with (Rsqr (sqrt x)) by (unfold Rsqr; ring).
  apply Rsqr_sqrt; exact Hx.
Qed.

(* 非负实数平方根的六次幂化简公式 *)
Lemma sqrt_pow_6 : forall x : R, 0 <= x -> (sqrt x)^6 = x^3.
Proof.
  intros x Hx.
  rewrite (pow_sq_cube_eq (sqrt x)).
  rewrite (sqrt_pow_2 x Hx).
  reflexivity.
Qed.

(* 缩放因子转换不等式 *)
Lemma Htrans (C : nat) (d : nat) (Hd : (d <= 6)%nat) (HC : (C >= 2)%nat) :
  8 / (sqrt (INR 2) ^ d) <= Rmax 8 ((INR C) ^ 3) / (sqrt (INR C) ^ d).
Proof.
  set (s2 := sqrt (INR 2)). set (sC := sqrt (INR C)).
  assert (Hs2_pos : 0 < s2) by (apply sqrt_lt_R0_c; apply lt_0_INR; lia).
  assert (Hs2_nonneg : 0 <= s2) by (apply Rlt_le; exact Hs2_pos).
  assert (HsC_pos : 0 < sC) by (apply sqrt_lt_R0_c; apply lt_0_INR; lia).
  assert (HsC_nonneg : 0 <= sC) by (apply Rlt_le; exact HsC_pos).
  assert (Hs2_ge1 : 1 <= s2).
  { rewrite <- sqrt_1; apply sqrt_le_1_c; [apply Rle_0_1 | apply pos_INR; lia | simpl; lra]. }
  assert (HsC_ge_s2 : sC >= s2).
  { apply Rle_ge; apply sqrt_le_1_c; [apply pos_INR; lia | apply pos_INR; lia | apply le_INR; lia]. }
  assert (Hs2_pow_nonzero : s2 ^ d <> 0) by (apply Rgt_not_eq; apply pow_lt; exact Hs2_pos).
  assert (HsC_pow_nonzero : sC ^ d <> 0) by (apply Rgt_not_eq; apply pow_lt; exact HsC_pos).

  assert (Hright_eq_aux : forall A, (A / sC ^ d) * (s2 ^ d * sC ^ d) = A * s2 ^ d).
  { intro A; field; exact HsC_pow_nonzero. }

  apply (Rmult_le_reg_r (s2 ^ d * sC ^ d));
    [apply Rmult_lt_0_compat; apply pow_lt; auto |].

  assert (Hleft_eq : (8 / s2 ^ d) * (s2 ^ d * sC ^ d) = 8 * sC ^ d).
  { field; exact Hs2_pow_nonzero. }
  rewrite Hleft_eq.

  assert (Hright_eq : (Rmax 8 (INR C ^ 3) / sC ^ d) * (s2 ^ d * sC ^ d) = Rmax 8 (INR C ^ 3) * s2 ^ d).
  { apply Hright_eq_aux. }
  rewrite Hright_eq.

  set (ratio := sC / s2).
  assert (Hratio_ge1 : ratio >= 1).
  { unfold ratio; apply Rle_ge; apply (Rmult_le_reg_r s2); [exact Hs2_pos |].
    field_simplify; [| apply Rgt_not_eq; exact Hs2_pos].
    exact (Rge_le _ _ HsC_ge_s2). }

  assert (Hratio_ge1' : 1 <= ratio).
  { apply Rge_le; exact Hratio_ge1. }

  assert (Hratio_pow_le : ratio ^ d <= ratio ^ 6).
  { apply Rle_pow; [exact Hratio_ge1' | lia]. }

  assert (HsC_pow_eq : sC ^ d = s2 ^ d * ratio ^ d).
  {
    unfold ratio.
    rewrite <- (pow_mul s2 (sC / s2) d).
    f_equal.
    field; apply Rgt_not_eq; exact Hs2_pos.
  }
  rewrite HsC_pow_eq.

  apply Rle_trans with (8 * s2 ^ d * ratio ^ 6).
  - rewrite <- (Rmult_assoc 8 (s2 ^ d) (ratio ^ d)).
    apply Rmult_le_compat_l.
    { apply Rmult_le_pos; [lra | apply pow_le; exact Hs2_nonneg]. }
    exact Hratio_pow_le.
  - assert (Hratio6_eq : ratio ^ 6 = sC ^ 6 / s2 ^ 6).
    { unfold ratio; rewrite pow_div_exact; auto. lra. }
    rewrite Hratio6_eq.
    replace (8 * s2 ^ d * (sC ^ 6 / s2 ^ 6))
      with ((8 * sC ^ 6 / s2 ^ 6) * s2 ^ d).
    2: { field; exact (Rgt_not_eq _ _ Hs2_pos). }

    assert (HsC6_eq : sC ^ 6 = (INR C) ^ 3).
    { unfold sC; apply sqrt_pow_6; apply pos_INR; lia. }
    assert (Hs2_6_eq : s2 ^ 6 = 8).
    {
      unfold s2.
      rewrite (sqrt_pow_6 (INR 2)); [| apply pos_INR; lia].
      simpl INR; ring.
    }
    rewrite HsC6_eq, Hs2_6_eq.
    replace (8 * (INR C) ^ 3 / 8) with ((INR C) ^ 3) by field.
    apply Rmult_le_compat_r; [apply pow_le; lra | apply Rmax_r].
Qed.

(* 定理：带缩放因子的张量内积范数上界 *)
Theorem tensor_inner_decay_gen (C : nat) (HC : (C >= 2)%nat) (r : R) (Hr : r = sqrt (INR C))
  (seq1 seq2 : nat -> nat)
  (Hsparse1 : forall i : nat, (INR (seq1 (S i)) > INR C * INR (seq1 i))%R)
  (Hsparse2 : forall i : nat, (INR (seq2 (S i)) > INR C * INR (seq2 i))%R)
  (Hge2_1 : forall i, (seq1 i >= 2)%nat) (Hge2_2 : forall i, (seq2 i >= 2)%nat)
  (i1 i2 j1 j2 : nat) (a1 a2 b1 b2 : nat)
  (Ha1_eq : a1 = seq1 i1) (Ha2_eq : a2 = seq1 i2)
  (Hb1_eq : b1 = seq2 j1) (Hb2_eq : b2 = seq2 j2)
  (Hneq1 : i1 <> i2) (Hneq2 : j1 <> j2)
  (H_index_bound : (Z.abs_nat (Z.of_nat i1 - Z.of_nat i2)
                   + Z.abs_nat (Z.of_nat j1 - Z.of_nat j2) <= 6)%nat)
  : let g (x y : nat) := sqrt (INR (Nat.min x y) / (INR x * INR y)) in
    let M := S (max (max a1 b1) (max a2 b2)) in
    let N := Nat.pred M in
    let N0 := Nat.min (Nat.min a1 a2) (Nat.min b1 b2) in
    Cnorm (Csum (fun k => (Cof_real (/ g a1 b1) *c (psi a1 k *c psi b1 k)) *c
                         Cconj (Cof_real (/ g a2 b2) *c (psi a2 k *c psi b2 k))) N)
    <= Rmax 8 ((INR C) ^ 3) / (r ^ (Z.abs_nat (Z.of_nat i1 - Z.of_nat i2)
                                   + Z.abs_nat (Z.of_nat j1 - Z.of_nat j2))).
Proof.
  intros g M N N0. subst a1 a2 b1 b2.
  set (d12 := Z.abs_nat (Z.of_nat i1 - Z.of_nat i2)).
  set (d34 := Z.abs_nat (Z.of_nat j1 - Z.of_nat j2)).

  assert (Hsparse1_2 : forall i : nat, INR (seq1 (S i)) > INR 2 * INR (seq1 i)).
  { intros i.
    specialize (Hsparse1 i).
    assert (Hpos : INR (seq1 i) > 0) by (apply lt_0_INR; specialize (Hge2_1 i); lia).
    assert (HC_ge_2_INR : INR 2 <= INR C) by (apply le_INR; exact HC).
    apply (Rle_lt_trans (INR 2 * INR (seq1 i)) (INR C * INR (seq1 i)) (INR (seq1 (S i)))).
    - apply Rmult_le_compat_r; [apply Rlt_le; exact Hpos | exact HC_ge_2_INR].
    - exact Hsparse1. }

  assert (Hsparse2_2 : forall i : nat, INR (seq2 (S i)) > INR 2 * INR (seq2 i)).
  { intros i.
    specialize (Hsparse2 i).
    assert (Hpos : INR (seq2 i) > 0) by (apply lt_0_INR; specialize (Hge2_2 i); lia).
    assert (HC_ge_2_INR : INR 2 <= INR C) by (apply le_INR; exact HC).
    apply (Rle_lt_trans (INR 2 * INR (seq2 i)) (INR C * INR (seq2 i)) (INR (seq2 (S i)))).
    - apply Rmult_le_compat_r; [apply Rlt_le; exact Hpos | exact HC_ge_2_INR].
    - exact Hsparse2. }

  assert (H_orig : Cnorm (Csum (fun k => (Cof_real (/ g (seq1 i1) (seq2 j1)) *c 
         (psi (seq1 i1) k *c psi (seq2 j1) k)) *c
         Cconj (Cof_real (/ g (seq1 i2) (seq2 j2)) *c (psi (seq1 i2) k *c psi (seq2 j2) k)))
         (Nat.pred (S (max (max (seq1 i1) (seq2 j1)) (max (seq1 i2) (seq2 j2))))))
    <= 8 / (sqrt (INR 2) ^ (d12 + d34))).
  { set (r0 := sqrt (INR 2)).
    assert (Hr0_pos : r0 > 0) by (apply sqrt_lt_R0_c; apply lt_0_INR; lia).
    assert (Hr0_eq : r0 = sqrt (INR 2)) by (unfold r0; reflexivity).
    assert (Hd_factor_neq1 : d_factor r0 i1 i2 = 2 / (r0 ^ d12)). {
      unfold d_factor, d12.
      assert (Hi1i2 : (i1 =? i2)%nat = false) by (apply Nat.eqb_neq; auto).
      rewrite Hi1i2. reflexivity. }
    assert (Hd_factor_neq2 : d_factor r0 j1 j2 = 2 / (r0 ^ d34)). {
      unfold d_factor, d34.
      assert (Hj1j2 : (j1 =? j2)%nat = false) by (apply Nat.eqb_neq; auto).
      rewrite Hj1j2. reflexivity. }
    assert (Hprod_eq : 2 * d_factor r0 i1 i2 * d_factor r0 j1 j2 = 8 / (r0 ^ (d12 + d34))). {
      rewrite Hd_factor_neq1, Hd_factor_neq2.
      assert (Hr0_d12_neq0 : r0 ^ d12 <> 0) by (apply pow_nonzero; lra).
      assert (Hr0_d34_neq0 : r0 ^ d34 <> 0) by (apply pow_nonzero; lra).
      field_simplify.
      - rewrite pow_add. ring.
      - apply pow_nonzero; lra.
      - split; assumption. }

    set (f := fun k : nat =>
      (Cof_real (/ g (seq1 i1) (seq2 j1)) *c (psi (seq1 i1) k *c psi (seq2 j1) k)) *c
      Cconj (Cof_real (/ g (seq1 i2) (seq2 j2)) *c (psi (seq1 i2) k *c psi (seq2 j2) k))).

    assert (Htrunc_eq : Csum f N = Csum f N0). {
      apply (Csum_trunc_tail f N0 N).
      - unfold N, M, N0. lia.
      - intros k [Hk1 Hk2].
        assert (H_min_eq : N0 = (seq1 i1) \/ N0 = (seq1 i2) \/ N0 = (seq2 j1) \/ N0 = (seq2 j2)). {
          unfold N0.
          destruct (Nat.min_spec (Nat.min (seq1 i1) (seq1 i2)) (Nat.min (seq2 j1) (seq2 j2))) as [[_ H1] | [_ H1]];
            [rewrite H1; destruct (Nat.min_spec (seq1 i1) (seq1 i2)) as [[_ H2] | [_ H2]];
              [rewrite H2; left; reflexivity | rewrite H2; right; left; reflexivity]
            | rewrite H1; destruct (Nat.min_spec (seq2 j1) (seq2 j2)) as [[_ H3] | [_ H3]];
              [rewrite H3; right; right; left; reflexivity | rewrite H3; right; right; right; reflexivity]].
        }
        destruct H_min_eq as [Hmin | [Hmin | [Hmin | Hmin]]];
        rewrite Hmin in Hk1.
        - assert (Hpsi1 : psi (seq1 i1) k = C0) by (apply psi_ge_n_zero; exact Hk1).
          unfold f. rewrite Hpsi1.
          rewrite (C0_mul_eq_C0 (psi (seq2 j1) k)).
          rewrite C0_mul_eq_C0_r. apply C0_mul_eq_C0.
        - assert (Hpsi2 : psi (seq1 i2) k = C0) by (apply psi_ge_n_zero; exact Hk1).
          assert (Hinner : psi (seq1 i2) k *c psi (seq2 j2) k = C0).
          { rewrite Hpsi2. apply C0_mul_eq_C0. }
          unfold f. rewrite Hinner.
          rewrite C0_mul_eq_C0_r. rewrite Cconj_0. apply C0_mul_eq_C0_r.
        - assert (Hpsi_b1 : psi (seq2 j1) k = C0) by (apply psi_ge_n_zero; exact Hk1).
          assert (Hinner : psi (seq1 i1) k *c psi (seq2 j1) k = C0).
          { rewrite Hpsi_b1. apply C0_mul_eq_C0_r. }
          unfold f. rewrite Hinner.
          rewrite C0_mul_eq_C0_r. apply C0_mul_eq_C0.
        - assert (Hpsi_b2 : psi (seq2 j2) k = C0) by (apply psi_ge_n_zero; exact Hk1).
          assert (Hinner : psi (seq1 i2) k *c psi (seq2 j2) k = C0).
          { rewrite Hpsi_b2. apply C0_mul_eq_C0_r. }
          unfold f. rewrite Hinner.
          rewrite C0_mul_eq_C0_r. rewrite Cconj_0. apply C0_mul_eq_C0_r. }

    fold N M.
    unfold N in Htrunc_eq.
    rewrite Htrunc_eq.

    apply Rle_trans with (2 * d_factor r0 i1 i2 * d_factor r0 j1 j2).
    - apply (tensor_inner_decay_scaled 2%nat r0 Hr0_eq seq1 seq2 Hge2_1 Hge2_2 Hsparse1_2 Hsparse2_2
                i1 i2 j1 j2 Hneq1 Hneq2 (eq_refl 2%nat) H_index_bound).
    - rewrite Hprod_eq. apply Rle_refl.
  }

  assert (Htrans : 8 / (sqrt (INR 2) ^ (d12 + d34)) 
                   <= Rmax 8 ((INR C) ^ 3) / (r ^ (d12 + d34))).
  { rewrite Hr.
    apply (Htrans C (d12 + d34)%nat).
    - clear - H_index_bound; lia.
    - exact HC. }

  eapply Rle_trans; [exact H_orig | exact Htrans].
Qed.

(* 定理：未缩放核心张量内积的因子化衰减上界 *)
Theorem tensor_core_inner_decay_bound_gen :
  forall (C : nat) (HC : (C >= 2)%nat)
    (seq1 seq2 : nat -> nat)
    (Hsparse1 : forall i : nat, (INR (seq1 (S i)) > INR C * INR (seq1 i))%R)
    (Hsparse2 : forall i : nat, (INR (seq2 (S i)) > INR C * INR (seq2 i))%R)
    (Hge2_1 : forall i, (seq1 i >= 2)%nat) (Hge2_2 : forall i, (seq2 i >= 2)%nat)
    (i1 i2 j1 j2 : nat) (a1 a2 b1 b2 : nat)
    (Ha1_eq : a1 = seq1 i1) (Ha2_eq : a2 = seq1 i2)
    (Hb1_eq : b1 = seq2 j1) (Hb2_eq : b2 = seq2 j2)
    (Hneq1 : i1 <> i2) (Hneq2 : j1 <> j2)
    (H_index_bound : (Z.abs_nat (Z.of_nat i1 - Z.of_nat i2)
                     + Z.abs_nat (Z.of_nat j1 - Z.of_nat j2) <= 6)%nat),
  let gamma_ab (x y : nat) := sqrt (INR (Nat.min x y) / (INR x * INR y)) in
  let N0 := Nat.min (Nat.min a1 a2) (Nat.min b1 b2) in
  let r := sqrt (INR C) in
  Cnorm (Csum (fun k : nat =>
    (psi a1 k *c Cconj (psi a2 k)) *c (psi b1 k *c Cconj (psi b2 k))) N0)
  <= (Rmax 8 ((INR C) ^ 3) / 4) * (gamma_ab a1 b1 * gamma_ab a2 b2) *
      d_factor (sqrt (INR C)) i1 i2 * d_factor (sqrt (INR C)) j1 j2.
Proof.
  intros C HC seq1 seq2 Hsparse1 Hsparse2 Hge2_1 Hge2_2
         i1 i2 j1 j2 a1 a2 b1 b2 Ha1_eq Ha2_eq Hb1_eq Hb2_eq
         Hneq1 Hneq2 H_index_bound.
  subst a1 a2 b1 b2.
  set (r := sqrt (INR C)).
  assert (Hr_pos : r > 0) by (apply sqrt_lt_R0_c; apply lt_0_INR; lia).
  assert (Hr_gt1 : r > 1).
  { unfold r; rewrite <- sqrt_1; apply sqrt_lt_1.
    - lra.
    - apply pos_INR; lia.
    - rewrite <- INR_1; apply (lt_INR 1 C); lia. }

  set (g := fun (x y : nat) => sqrt (INR (Nat.min x y) / (INR x * INR y))).
  assert (Hg_pos : forall x y, (x >= 2)%nat -> (y >= 2)%nat -> g x y > 0).
  { intros x y Hx Hy; unfold g.
    apply sqrt_lt_R0_c; apply Rmult_lt_0_compat.
    - apply lt_0_INR; lia.
    - apply Rinv_0_lt_compat; apply Rmult_lt_0_compat; apply lt_0_INR; lia. }

  set (d12 := Z.abs_nat (Z.of_nat i1 - Z.of_nat i2)).
  set (d34 := Z.abs_nat (Z.of_nat j1 - Z.of_nat j2)).

  set (N0' := Nat.min (Nat.min (seq1 i1) (seq1 i2)) (Nat.min (seq2 j1) (seq2 j2))).
  set (Mmax := max (max (seq1 i1) (seq2 j1)) (max (seq1 i2) (seq2 j2))).

  set (scaled := Csum (fun k : nat =>
    (Cof_real (/ g (seq1 i1) (seq2 j1)) *c (psi (seq1 i1) k *c psi (seq2 j1) k)) *c
    Cconj (Cof_real (/ g (seq1 i2) (seq2 j2)) *c (psi (seq1 i2) k *c psi (seq2 j2) k))) Mmax).
  set (unscaled := Csum (fun k : nat =>
    (psi (seq1 i1) k *c Cconj (psi (seq1 i2) k)) *c
    (psi (seq2 j1) k *c Cconj (psi (seq2 j2) k))) N0').

  assert (H_scale_eq : scaled = Cof_real (/ (g (seq1 i1) (seq2 j1) * g (seq1 i2) (seq2 j2))) *c unscaled).
  { unfold scaled, unscaled, Mmax.
    pose proof (product_psi_inner_decomposition (seq1 i1) (seq1 i2) (seq2 j1) (seq2 j2) g) as Hprod.
    cbv beta in Hprod; simpl in Hprod; rewrite Hprod; reflexivity. }

  assert (Hg1 : g (seq1 i1) (seq2 j1) > 0) by (apply Hg_pos; [apply Hge2_1 | apply Hge2_2]).
  assert (Hg2 : g (seq1 i2) (seq2 j2) > 0) by (apply Hg_pos; [apply Hge2_1 | apply Hge2_2]).

  assert (H_unscaled_norm : Cnorm unscaled =
    (g (seq1 i1) (seq2 j1) * g (seq1 i2) (seq2 j2)) * Cnorm scaled).
  { rewrite H_scale_eq; rewrite Cnorm_mult.
    rewrite (Cnorm_Cof_real_pos (/ (g (seq1 i1) (seq2 j1) * g (seq1 i2) (seq2 j2)))).
    - field_simplify. + reflexivity. + split; apply Rgt_not_eq; [exact Hg2 | exact Hg1].
    - apply Rlt_le; apply Rinv_0_lt_compat; exact (Rmult_lt_0_compat _ _ Hg1 Hg2). }

  assert (Hr_eq : r = sqrt (INR C)) by (unfold r; reflexivity).
  assert (H_norm_scaled : Cnorm scaled <=
          Rmax 8 ((INR C) ^ 3) / (r ^ (d12 + d34))).
  { unfold scaled, Mmax.
    pose proof (tensor_inner_decay_gen C HC r Hr_eq seq1 seq2 Hsparse1 Hsparse2 Hge2_1 Hge2_2
                 i1 i2 j1 j2 (seq1 i1) (seq1 i2) (seq2 j1) (seq2 j2)
                 (eq_refl (seq1 i1)) (eq_refl (seq1 i2)) (eq_refl (seq2 j1)) (eq_refl (seq2 j2))
                 Hneq1 Hneq2 H_index_bound) as Htemp.
    cbv beta in Htemp.
    fold d12 d34 in Htemp.
    exact Htemp. }

  assert (H_main : Cnorm unscaled <=
    (g (seq1 i1) (seq2 j1) * g (seq1 i2) (seq2 j2)) *
    (Rmax 8 ((INR C) ^ 3) / (r ^ (d12 + d34)))).
  { rewrite H_unscaled_norm.
    apply Rmult_le_compat_l;
      [apply Rmult_le_pos; apply Rlt_le; [exact Hg1 | exact Hg2]
      | exact H_norm_scaled]. }

  assert (H_factor_eq : (g (seq1 i1) (seq2 j1) * g (seq1 i2) (seq2 j2)) *
    (Rmax 8 ((INR C) ^ 3) / (r ^ (d12 + d34))) =
    (Rmax 8 ((INR C) ^ 3) / 4) * (g (seq1 i1) (seq2 j1) * g (seq1 i2) (seq2 j2)) *
    d_factor r i1 i2 * d_factor r j1 j2).
  { set (G := g (seq1 i1) (seq2 j1) * g (seq1 i2) (seq2 j2)).
    set (RmaxC3 := Rmax 8 ((INR C) ^ 3)).
    unfold d_factor.
    assert (Hi_eq_false : (i1 =? i2)%nat = false) by (apply Nat.eqb_neq; auto).
    assert (Hj_eq_false : (j1 =? j2)%nat = false) by (apply Nat.eqb_neq; auto).
    rewrite Hi_eq_false, Hj_eq_false; simpl.
    set (rd12 := r ^ d12). set (rd34 := r ^ d34).
    assert (H_pow_add : r ^ (d12 + d34) = rd12 * rd34) by (apply pow_add).
    rewrite H_pow_add.
    replace (r ^ Z.abs_nat (Z.of_nat i1 - Z.of_nat i2)) with rd12
      by (subst rd12; unfold d12; reflexivity).
    replace (r ^ Z.abs_nat (Z.of_nat j1 - Z.of_nat j2)) with rd34
      by (subst rd34; unfold d34; reflexivity).
    assert (H_rd12_pos : rd12 > 0) by (subst rd12; apply pow_lt; exact Hr_pos).
    assert (H_rd34_pos : rd34 > 0) by (subst rd34; apply pow_lt; exact Hr_pos).
    field; split; apply Rgt_not_eq; assumption. }

  replace ((g (seq1 i1) (seq2 j1) * g (seq1 i2) (seq2 j2)) *
           (Rmax 8 ((INR C) ^ 3) / (r ^ (d12 + d34))))
    with ((Rmax 8 ((INR C) ^ 3) / 4) * (g (seq1 i1) (seq2 j1) * g (seq1 i2) (seq2 j2)) *
          d_factor r i1 i2 * d_factor r j1 j2)
    by (rewrite H_factor_eq; ring).
  cbv zeta.
  cbv beta.
  fold unscaled.
  rewrite <- H_factor_eq.
  exact H_main.
Qed.

(* 定理：张量积无条件基定理（C=2，索引差受限） *)
Theorem tensor_product_unconditional_basis_restricted :
  forall (C : nat) (HCeq2 : C = 2%nat)
    (seq1 seq2 : nat -> nat)
    (Hsparse1 : forall i : nat, (INR (seq1 (S i)) > INR C * INR (seq1 i))%R)
    (Hsparse2 : forall i : nat, (INR (seq2 (S i)) > INR C * INR (seq2 i))%R)
    (Hge2_1 : forall i : nat, (seq1 i >= 2)%nat)
    (Hge2_2 : forall i : nat, (seq2 i >= 2)%nat)
    (I1 I2 : list nat)
    (Hdup1 : NoDup I1) (Hsorted1 : Sorted Nat.lt I1)
    (Hdup2 : NoDup I2) (Hsorted2 : Sorted Nat.lt I2)
    (n1 n2 : nat)
    (HI1 : I1 = seq 0 n1) (HI2 : I2 = seq 0 n2)
    (coeffs : nat -> nat -> Complex)
    (Hn1 : n1 = length I1) (Hn2 : n2 = length I2)
    (Hn1_pos : (n1 > 0)%nat) (Hn2_pos : (n2 > 0)%nat)
    (H_index_bound : forall idx1 idx2 : nat,
        idx1 <> idx2 ->
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
  let M_bound := 8%R * ((1 + 4 * K_C) * (1 + 4 * K_C) - 1) in
  ((1 - M_bound) * S <= l2_norm_sq F_2D (M - 1) <= (1 + M_bound) * S)%R.
Proof.
  intros C HCeq2 seq1 seq2 Hsparse1 Hsparse2 Hge2_1 Hge2_2
         I1 I2 Hdup1 Hsorted1 Hdup2 Hsorted2 n1 n2 HI1 HI2 coeffs Hn1 Hn2 Hn1_pos Hn2_pos H_index_bound.
  assert (HC_ge2 : (C >= 2)%nat) by (subst C; lia).
  assert (HCgt1_R : 1 < INR C) by (change 1 with (INR 1); apply lt_INR; lia).
  set (r := sqrt (INR C)).
  assert (Hr_gt1 : r > 1).
  { unfold r; rewrite <- sqrt_1. apply sqrt_lt_1 with (x := 1) (y := INR C); [lra|apply pos_INR; lia|exact HCgt1_R]. }
  assert (Hr_pos : r > 0) by (apply sqrt_lt_R0_c; apply lt_0_INR; lia).
  set (K_C := K (INR C)).

  assert (HK_pos : 0 < K_C).
  { subst C; unfold K, r; simpl.
    apply Rdiv_lt_0_compat; [lra|].
    apply Rgt_minus.
    rewrite <- sqrt_1.
    apply sqrt_lt_1 with (x := 1) (y := 2); lra. }

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
    assert (Hi : (i < n1)%nat) by (apply Div0.div_lt_upper_bound; lia).
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

  assert (Hg_pos : forall x y, (x < n1)%nat -> (y < n2)%nat -> gamma x y > 0).
  { intros x y Hx_lt Hy_lt.
    assert (Ha_ge2 : (a x >= 2)%nat). {
      unfold a, vals1.
      rewrite (H_nth_map nat nat seq1 I1 0%nat 0%nat x).
      - apply Hge2_1.
      - rewrite <- Hn1; exact Hx_lt.
    }
    assert (Hb_ge2 : (b y >= 2)%nat). {
      unfold b, vals2.
      rewrite (H_nth_map nat nat seq2 I2 0%nat 0%nat y).
      - apply Hge2_2.
      - rewrite <- Hn2; exact Hy_lt.
    }
    unfold gamma, w.
    apply sqrt_lt_R0_c; apply Rdiv_lt_0_compat.
    - assert (Hmin_pos : (0 < Nat.min (a x) (b y))%nat) by lia.
      apply lt_0_INR; exact Hmin_pos.
    - apply Rmult_lt_0_compat; apply lt_0_INR; lia. }

  assert (Hnorm1 : forall idx, (idx < n)%nat -> l2_norm_sq (phi_flat idx) (Nat.pred M) = 1%R).
  { intros idx Hlt.
    set (i := (idx / n2)%nat); set (j := (idx mod n2)%nat).
    assert (Hi : (i < n1)%nat) by (apply Div0.div_lt_upper_bound; lia).
    assert (Hj : (j < n2)%nat) by (apply Nat.mod_upper_bound; lia).
    unfold phi_flat, phi2D_norm.
    fold i j.
    set (c := Cof_real (/ gamma i j)).
    set (f k := c *c (psi (a i) k *c psi (b j) k)).
    unfold l2_norm_sq.
    set (m := Nat.min (a i) (b j)).
    assert (Ha_max : (a i <= max (seq1 maxIdx1) (seq2 maxIdx2))%nat).
    { unfold a, vals1.
      assert (Hi_len : (i < length I1)%nat) by (rewrite <- Hn1; exact Hi).
      rewrite (H_nth_map nat nat seq1 I1 0%nat 0%nat i Hi_len).
      apply Nat.le_trans with (seq1 maxIdx1).
      - apply Hseq1_inc.
        eapply fold_right_max_ge.
        apply nth_In; exact Hi_len.
      - apply Nat.le_max_l. }
    assert (Hb_max : (b j <= max (seq1 maxIdx1) (seq2 maxIdx2))%nat).
    { unfold b, vals2.
      assert (Hj_len : (j < length I2)%nat) by (rewrite <- Hn2; exact Hj).
      rewrite (H_nth_map nat nat seq2 I2 0%nat 0%nat j Hj_len).
      apply Nat.le_trans with (seq2 maxIdx2).
      - apply Hseq2_inc.
        eapply fold_right_max_ge.
        apply nth_In; exact Hj_len.
      - apply Nat.le_max_r. }
    assert (H_min_le_M_pred : (m <= Nat.pred M)%nat).
    { apply (Nat.le_trans _ (max (seq1 maxIdx1) (seq2 maxIdx2))%nat).
      - apply (Nat.le_trans _ (a i)%nat).
        + apply Nat.le_min_l.
        + exact Ha_max.
      - unfold M. simpl. apply Nat.le_refl. }

    assert (Htrunc_eq : sum_f_R0 (fun k => Cnorm_sq (f k)) (Nat.pred M) =
                        sum_f_R0 (fun k => Cnorm_sq (f k)) m).
    {
      apply (sum_f_R0_trunc_tail (fun k => Cnorm_sq (f k)) m (Nat.pred M) H_min_le_M_pred).
      intros k [Hk1 Hk2].
      assert (H_m_le_k : (m <= k)%nat) by exact Hk1.
      unfold f, c.
      rewrite Cnorm_sq_mult, Cnorm_sq_mult.
      assert (Hcoeff_sq' : Cnorm_sq (Cof_real (/ gamma i j)) = (/ gamma i j)^2).
      { unfold Cof_real, Cnorm_sq, Rsqr; simpl; ring. }
      rewrite Hcoeff_sq'.
      rewrite !Cnorm_sq_psi_exact.
      unfold m in H_m_le_k.
      destruct (Nat.min_spec (a i) (b j)) as [[Hle Hmin] | [Hle Hmin]].
      - rewrite Hmin in H_m_le_k.
        assert (Hge_ai : (a i <= k)%nat) by lia.
        rewrite (proj2 (Nat.ltb_ge k (a i)) Hge_ai); simpl; ring.
      - rewrite Hmin in H_m_le_k.
        assert (Hge_bj : (b j <= k)%nat) by lia.
        rewrite (proj2 (Nat.ltb_ge k (b j)) Hge_bj); simpl; ring.
    }

    destruct (eq_nat_dec m 0) as [Hz|Hnz].
    - exfalso.
      assert (Ha_ge2_i : (a i >= 2)%nat). {
        unfold a, vals1.
        assert (Hi_len : (i < length I1)%nat) by (rewrite <- Hn1; exact Hi).
        rewrite (H_nth_map nat nat seq1 I1 0%nat 0%nat i Hi_len).
        apply Hge2_1.
      }
      assert (Hb_ge2_j : (b j >= 2)%nat). {
        unfold b, vals2.
        assert (Hj_len : (j < length I2)%nat) by (rewrite <- Hn2; exact Hj).
        rewrite (H_nth_map nat nat seq2 I2 0%nat 0%nat j Hj_len).
        apply Hge2_2.
      }
      unfold m in Hz.
      lia.
    - assert (Hf_m_zero : f m = C0).
      { unfold f, c, m.
        destruct (Nat.min_spec (a i) (b j)) as [[Hle Hmin] | [Hle Hmin]].
        - rewrite Hmin.
          rewrite (psi_ge_n_zero (a i) (a i) (le_refl _)).
          rewrite Cmul_0_l.
          apply Cmul_0_r.
        - rewrite Hmin.
          rewrite (psi_ge_n_zero (b j) (b j) (le_refl _)).
          assert (Htemp : psi (a i) (b j) *c C0 = C0) by apply Cmul_0_r.
          rewrite Htemp.
          apply Cmul_0_r. }
      assert (Hsum_m_eq_m1 : sum_f_R0 (fun k => Cnorm_sq (f k)) m =
                              sum_f_R0 (fun k => Cnorm_sq (f k)) (m-1)).
      { destruct m as [|m']; [exfalso; lia|].
        simpl (sum_f_R0 (fun k : nat => Cnorm_sq (f k)) (S m')).
        rewrite Hf_m_zero.
        assert (Cnorm_sq_C0 : Cnorm_sq (C0 : Complex) = 0%R).
        { unfold Cnorm_sq, C0; simpl; rewrite Rsqr_0, Rplus_0_l; reflexivity. }
        rewrite Cnorm_sq_C0.
        rewrite Rplus_0_r.
        replace (S m' - 1)%nat with m' by lia.
        reflexivity. }
      rewrite Htrunc_eq, Hsum_m_eq_m1.

      assert (Hcalc : sum_f_R0 (fun k : nat => Cnorm_sq (f k)) (m-1) = 1%R).
      { unfold f, c.
        rewrite (sum_f_R0_ext _
                 (fun k => (/ gamma i j)^2 * (1 / INR (a i)) * (1 / INR (b j))) (m-1)).
        - rewrite sum_f_R0_const.
          replace (S (m - 1))%nat with m by (destruct m; [lia|lia]).
          assert (Hgamma_sq : (gamma i j)^2 = INR m / (INR (a i) * INR (b j))).
          { unfold gamma, w, m.
            replace ((sqrt (INR (Nat.min (a i) (b j)) / (INR (a i) * INR (b j))))^2)
              with ((sqrt (INR (Nat.min (a i) (b j)) / (INR (a i) * INR (b j)))) *
                    (sqrt (INR (Nat.min (a i) (b j)) / (INR (a i) * INR (b j))))).
            2: { ring. }
            rewrite sqrt_sqrt.
            - reflexivity.
            - apply Rlt_le; apply Rdiv_lt_0_compat;
                [ apply lt_0_INR; lia
                | apply Rmult_lt_0_compat; apply lt_0_INR; lia ]. }
          assert (Hcoeff_sq : (/ gamma i j)^2 = INR (a i) * INR (b j) / INR m).
          {
            assert (Hg_nonzero : gamma i j <> 0) by (apply Rgt_not_eq; apply Hg_pos; [exact Hi | exact Hj]).
            assert (Htmp : (/ gamma i j)^2 = 1 / (gamma i j)^2) by (field; auto).
            rewrite Htmp.
            rewrite Hgamma_sq.
            field; split; [|split];
              [apply Rgt_not_eq, lt_0_INR; lia
              |apply Rgt_not_eq, lt_0_INR; lia
              |apply Rgt_not_eq, lt_0_INR; lia].
          }
          rewrite Hcoeff_sq.
          field; split; [|split];
            [apply Rgt_not_eq, lt_0_INR; lia
            |apply Rgt_not_eq, lt_0_INR; lia
            |apply Rgt_not_eq, lt_0_INR; lia].
        - intros k Hk.
          assert (Hk_lt_m : (k < m)%nat) by lia.
          assert (Hk_lt_ai : (k < a i)%nat) by (apply Nat.lt_le_trans with m; lia).
          assert (Hk_lt_bj : (k < b j)%nat) by (apply Nat.lt_le_trans with m; lia).
          unfold f, c.
          rewrite Cnorm_sq_mult, Cnorm_sq_mult.
          assert (Hcoeff_sq' : Cnorm_sq (Cof_real (/ gamma i j)) = (/ gamma i j)^2).
          { unfold Cof_real, Cnorm_sq, Rsqr; simpl; ring. }
          rewrite Hcoeff_sq'.
          rewrite !Cnorm_sq_psi_exact.
          rewrite (proj2 (Nat.ltb_lt k (a i)) Hk_lt_ai).
          rewrite (proj2 (Nat.ltb_lt k (b j)) Hk_lt_bj).
          ring.
      }
      exact Hcalc.
  }

  set (d1 := d_factor r).
  pose (delta_pair_scaled := fun (idx1 idx2 : nat) =>
    8%R * (d1 (idx1 / n2)%nat (idx2 / n2)%nat * d1 (idx1 mod n2)%nat (idx2 mod n2)%nat)).

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

  assert (Hdelta_sym : forall (i j : nat), (i < n)%nat -> (j < n)%nat -> delta_pair_scaled i j = delta_pair_scaled j i).
  { intros i j Hi Hj; unfold delta_pair_scaled, d1.
    rewrite (d_factor_sym (i / n2)%nat (j / n2)%nat).
    rewrite (d_factor_sym (i mod n2)%nat (j mod n2)%nat).
    reflexivity. }

  assert (d_factor_nonneg : forall i j, 0 <= d_factor r i j).
  { intros i j; unfold d_factor.
    destruct (Nat.eqb_spec i j) as [Heq | Hneq].
    - subst i; lra.
    - apply Rlt_le; apply Rdiv_lt_0_compat; [lra | apply pow_lt; exact Hr_pos]. }

  assert (Hdelta_nonneg : forall (i j : nat), (i < n)%nat -> (j < n)%nat -> 0 <= delta_pair_scaled i j).
  { intros i j Hi Hj; unfold delta_pair_scaled.
    apply Rmult_le_pos; [lra | apply Rmult_le_pos; apply d_factor_nonneg]. }

  assert (Hdecay : forall idx1 idx2, idx1 <> idx2 -> (idx1 < n)%nat -> (idx2 < n)%nat ->
    Cnorm (Csum (fun k => phi_flat idx1 k *c Cconj (phi_flat idx2 k)) (Nat.pred M))
    <= delta_pair_scaled idx1 idx2).
  { intros idx1 idx2 Hneq Hlt1 Hlt2.
    unfold delta_pair_scaled.
    assert (Hlt1' : (idx1 < n1 * n2)%nat) by (unfold n in Hlt1; exact Hlt1).
    assert (Hlt2' : (idx2 < n1 * n2)%nat) by (unfold n in Hlt2; exact Hlt2).
    refine (phi_flat_decay C HCeq2 seq1 seq2 Hsparse1 Hsparse2 Hge2_1 Hge2_2
                          I1 I2 Hdup1 Hsorted1 Hdup2 Hsorted2
                          n1 n2 Hn1 Hn2 HI1 HI2
                          a b _ _ gamma _ phi2D_norm _ maxIdx1 maxIdx2 _ _
                          M _ r _ phi_flat _
                          (fun idx1_ idx2_ => d_factor r (idx1_ / n2) (idx2_ / n2) * d_factor r (idx1_ mod n2) (idx2_ mod n2)) _
                          idx1 idx2 Hneq Hlt1' Hlt2' _);
    try reflexivity;
    try (apply H_index_bound; assumption).
  }

  assert (d_factor_row_sum_le_4K_2 : forall n i, (i < n)%nat ->
    sum_f_R0 (fun j => if eq_nat_dec i j then 0 else d_factor (sqrt (INR 2)) i j) (Nat.pred n)
    <= 4 * K (INR 2)).
  { intros nn i Hi.
    set (r2 := sqrt (INR 2)).
    assert (Hr2_gt1 : r2 > 1).
    { unfold r2; rewrite <- sqrt_1.
      apply sqrt_lt_1 with (x := 1) (y := INR 2); [lra|apply pos_INR; lia|change 1 with (INR 1); apply lt_INR; lia]. }
    assert (Hr2_pos : r2 > 0).
    { apply sqrt_lt_R0_c. apply lt_0_INR; lia. }
    set (F j := if eq_nat_dec i j then 0 else 2 / (r2 ^ Z.abs_nat (Z.of_nat i - Z.of_nat j))).
    assert (Heq_sum : sum_f_R0 (fun j => if eq_nat_dec i j then 0 else d_factor r2 i j) (Nat.pred nn)
                     = sum_f_R0 F (Nat.pred nn)).
    { apply sum_f_R0_ext; intros j Hj.
      unfold F.
      destruct (eq_nat_dec i j).
      - subst j. simpl. destruct (eq_nat_dec i i); [reflexivity | contradiction].
      - unfold d_factor. rewrite (proj2 (Nat.eqb_neq i j) n0). reflexivity. }
    rewrite Heq_sum.
    assert (HF_i : F i = 0) by (unfold F; destruct eq_nat_dec; [reflexivity|contradiction]).
    set (F' := fun j : nat => F j / 2).
    assert (HF'_bound : forall j, (j < nn)%nat -> j <> i -> F' j <= / (r2 ^ Z.abs_nat (Z.of_nat i - Z.of_nat j))).
    { intros j Hj Hne; unfold F', F.
      destruct (eq_nat_dec i j) as [Heq|Hneq].
      - exfalso. apply Hne. symmetry. exact Heq.
      - assert (Hcalc : (2 / r2 ^ Z.abs_nat (Z.of_nat i - Z.of_nat j)) / 2 = / r2 ^ Z.abs_nat (Z.of_nat i - Z.of_nat j)).
        { field. apply Rgt_not_eq, pow_lt, Hr2_pos. }
        rewrite Hcalc. apply Rle_refl. }
    assert (HF'_i : F' i = 0) by (unfold F'; rewrite HF_i; field).
    assert (HsumF_eq : sum_f_R0 F (Nat.pred nn) = 2 * sum_f_R0 F' (Nat.pred nn)).
    { rewrite <- (sum_f_R0_scal_l 2 F' (Nat.pred nn)).
      apply sum_f_R0_ext; intros j Hj.
      unfold F'; field. }
    rewrite HsumF_eq.
    assert (Hr2_minus1_pos : r2 - 1 > 0) by (apply Rgt_minus; exact Hr2_gt1).
    destruct (lt_dec (i+1) nn) as [Hi_mid | Hi_end].
    - pose proof (split_sum_geometric_bound_one r2 Hr2_gt1 i nn F' Hi_mid HF'_i HF'_bound) as HsumF'.
      rewrite <- (Nat.sub_1_r nn) at 1.
      apply Rle_trans with (2 * (2 / (r2 - 1))).
      + apply Rmult_le_compat_l; [lra| exact HsumF'].
      + replace (2 * (2 / (r2 - 1))) with (4 / (r2 - 1)).
        2: { field; apply Rgt_not_eq; exact Hr2_minus1_pos. }
        replace (4 * K (INR 2)) with (4 / (r2 - 1)).
        2: { unfold K, r2; field; apply Rgt_not_eq; exact Hr2_minus1_pos. }
        apply Rle_refl.
    - assert (Hle : (nn <= i+1)%nat) by (clear -Hi Hi_end; lia).
      pose proof (row_sum_bound_when_i_last_one r2 i nn F' Hr2_gt1 Hi Hle HF'_i HF'_bound) as HsumF'.
      rewrite <- (Nat.sub_1_r nn) at 1.
      apply Rle_trans with (2 * (/ (r2 - 1))).
      + apply Rmult_le_compat_l; [lra| exact HsumF'].
      + replace (2 * (/ (r2 - 1))) with (2 / (r2 - 1)) by (unfold Rdiv; ring).
        replace (4 * K (INR 2)) with (4 / (r2 - 1)).
        2: { unfold K, r2; field; apply Rgt_not_eq; exact Hr2_minus1_pos. }
        apply Rmult_le_compat_r.
        * left; apply Rinv_0_lt_compat; exact Hr2_minus1_pos.
        * lra.
  }
  set (M_bound := 8%R * ((1 + 4 * K_C) * (1 + 4 * K_C) - 1)).
  assert (Hrow_sum : forall idx : nat, (idx < n)%nat ->
    sum_f_R0 (fun jdx : nat => if eq_nat_dec idx jdx then 0
      else delta_pair_scaled idx jdx) (Nat.pred n)
    <= M_bound).
  { intros idx Hlt.
    set (i0 := (idx / n2)%nat); set (j0 := (idx mod n2)%nat).
    assert (Hi0 : (i0 < n1)%nat) by (apply Div0.div_lt_upper_bound; lia).
    assert (Hj0 : (j0 < n2)%nat) by (apply Nat.mod_upper_bound; lia).
    set (S1 := sum_f_R0 (fun i' => if eq_nat_dec i0 i' then 0 else d1 i0 i') (Nat.pred n1)).
    set (S2 := sum_f_R0 (fun j' => if eq_nat_dec j0 j' then 0 else d1 j0 j') (Nat.pred n2)).

    assert (HS1 : S1 <= 4 * K_C).
    { unfold S1, d1, r, K_C.
      rewrite HCeq2; simpl.
      apply d_factor_row_sum_le_4K_2; exact Hi0. }
    assert (HS2 : S2 <= 4 * K_C).
    { unfold S2, d1, r, K_C.
      rewrite HCeq2; simpl.
      apply d_factor_row_sum_le_4K_2; exact Hj0. }

    assert (HS1_nonneg : 0 <= S1).
    { unfold S1; apply sum_f_R0_nonneg; intros i';
      destruct (eq_nat_dec i0 i'); [apply Rle_refl | unfold d1; apply d_factor_nonneg]. }
    assert (HS2_nonneg : 0 <= S2).
    { unfold S2; apply sum_f_R0_nonneg; intros j';
      destruct (eq_nat_dec j0 j'); [apply Rle_refl | unfold d1; apply d_factor_nonneg]. }

    assert (Hrow_decomp : sum_f_R0 (fun jdx : nat => if eq_nat_dec idx jdx then 0
      else d1 (idx / n2)%nat (jdx / n2)%nat * d1 (idx mod n2)%nat (jdx mod n2)%nat) (Nat.pred n)
      = (1 + S1) * (1 + S2) - 1).
    { subst n; unfold d1, S1, S2.
      replace (idx / n2)%nat with i0 by (unfold i0; reflexivity).
      replace (idx mod n2)%nat with j0 by (unfold j0; reflexivity).
      assert (Hidx_form : idx = (i0 * n2 + j0)%nat).
      { unfold i0, j0; rewrite Nat.mul_comm; apply Nat.div_mod; lia. }
      rewrite Hidx_form.
      apply (prod_row_sum_decomp_eq n1 n2 i0 j0 (d_factor r) Hi0 Hj0 (d_factor_diag r)). }

    assert (Hprod_ub : (1 + S1) * (1 + S2) - 1 <= (1 + 4 * K_C) * (1 + 4 * K_C) - 1).
    { nra. }

    set (f := fun jdx : nat => if eq_nat_dec idx jdx then 0 else delta_pair_scaled idx jdx).
    assert (H_f_sum : sum_f_R0 f (Nat.pred n) = 8%R * sum_f_R0 (fun jdx : nat => if eq_nat_dec idx jdx then 0
      else d1 (idx / n2)%nat (jdx / n2)%nat * d1 (idx mod n2)%nat (jdx mod n2)%nat) (Nat.pred n)).
    { rewrite <- (sum_f_R0_scal_l 8%R _ (Nat.pred n)).
      apply sum_f_R0_ext; intros jdx Hjdx.
      unfold f, delta_pair_scaled, d1.
      destruct (eq_nat_dec idx jdx) as [Heq_jdx | Hneq_jdx].
      - subst jdx; ring.
      - reflexivity. }
    rewrite H_f_sum.
    rewrite Hrow_decomp.
    apply Rmult_le_compat_l; [lra | exact Hprod_ub].
  }

  assert (HM_pos : (M > 0)%nat) by (unfold M; lia).
  pose proof (abstract_unconditional_basis n phi_flat M M_bound
    delta_pair_scaled HM_pos Htrunc Hnorm1
    (fun (i j : nat) Hi Hj => Hdelta_sym i j Hi Hj)
    (fun (i j : nat) Hi Hj => Hdelta_nonneg i j Hi Hj)
    Hdecay Hrow_sum
    coeffs_flat Hlen_flat) as H_abs.

  set (F_2D := fun k : nat => Csum (fun i => Csum (fun j => coeffs i j *c phi2D_norm i j k) n2) n1).
  set (S := sum_f_R0 (fun i => sum_f_R0 (fun j => Cnorm_sq (coeffs i j)) (n2 - 1)) (n1 - 1)).

  assert (HF_flat_eq : forall k, F_2D k = Csum (fun idx : nat => nth idx coeffs_flat C0 *c phi_flat idx k) n).
  { intros k; unfold F_2D, phi_flat.
    rewrite <- (Csum_flatten n1 n2 (fun i j => coeffs i j *c phi2D_norm i j k)).
    apply Csum_ext'; intros idx Hidx.
    rewrite (Hnth_flat idx Hidx); reflexivity. }
  assert (HS_flat_eq : S = sum_f_R0 (fun idx : nat => Cnorm_sq (nth idx coeffs_flat C0)) (Nat.pred n)).
  { unfold S.
    subst n.
    rewrite <- (sum_f_R0_flatten n1 n2 Hn1_pos Hn2_pos (fun i j => Cnorm_sq (coeffs i j))).
    transitivity (sum_f_R0 (fun idx : nat => Cnorm_sq (coeffs (idx / n2)%nat (idx mod n2)%nat))
                          (Nat.pred (n1 * n2))).
    - apply f_equal; lia.
    - apply sum_f_R0_ext; intros idx Hle.
      assert (Hidx_lt : (idx < n1 * n2)%nat) by lia.
      rewrite (Hnth_flat idx Hidx_lt); reflexivity. }

  assert (HM_pred_eq : Nat.pred M = (M - 1)%nat) by (unfold M; lia).
  destruct H_abs as [H_low H_high].
  assert (H_eq_l2 : l2_norm_sq F_2D (M - 1) = l2_norm_sq (fun k : nat => Csum (fun idx : nat => nth idx coeffs_flat C0 *c phi_flat idx k) n) (Nat.pred M)).
  { unfold l2_norm_sq.
    rewrite <- HM_pred_eq.
    apply sum_f_R0_ext; intros k Hk.
    rewrite (HF_flat_eq k); reflexivity. }
  assert (Hgoal : (1 - M_bound) * S <= l2_norm_sq F_2D (M - 1) <= (1 + M_bound) * S).
  { rewrite H_eq_l2, HS_flat_eq.
    exact (conj H_low H_high). }
  exact Hgoal.
Qed.

(* Rmax 不小于左参数 *)
Lemma Rmax_ge_l : forall a b : R, (Rmax a b >= a)%R.
Proof. intros; apply Rle_ge, Rmax_l. Qed.

(* Rmax 不小于右参数 *)
Lemma Rmax_ge_r : forall a b : R, (Rmax a b >= b)%R.
Proof. intros; apply Rle_ge, Rmax_r. Qed.

(* Rmax 同时不小于左参数与右参数 *)
Lemma Rmax_ge : forall a b : R, (Rmax a b >= a)%R /\ (Rmax a b >= b)%R.
Proof. split; [apply Rmax_ge_l | apply Rmax_ge_r]. Qed.

(* 定理：张量内积缩放通用界 *)
Theorem tensor_inner_scaled_bound_gen :
  forall (C : nat) (HC : (C >= 2)%nat)
    (seq1 seq2 : nat -> nat)
    (Hsparse1 : forall i, (INR (seq1 (S i)) > INR C * INR (seq1 i))%R)
    (Hsparse2 : forall i, (INR (seq2 (S i)) > INR C * INR (seq2 i))%R)
    (Hge2_1 : forall i, (seq1 i >= 2)%nat)
    (Hge2_2 : forall i, (seq2 i >= 2)%nat)
    (i1 i2 j1 j2 : nat)
    (a1 a2 b1 b2 : nat)
    (Ha1 : a1 = seq1 i1) (Ha2 : a2 = seq1 i2)
    (Hb1 : b1 = seq2 j1) (Hb2 : b2 = seq2 j2)
    (Hneq1 : i1 <> i2) (Hneq2 : j1 <> j2)
    (H_index_bound : (Z.abs_nat (Z.of_nat i1 - Z.of_nat i2) +
                      Z.abs_nat (Z.of_nat j1 - Z.of_nat j2) <= 6)%nat),
  let r := sqrt (INR C) in
  let d12 := Z.abs_nat (Z.of_nat i1 - Z.of_nat i2) in
  let d34 := Z.abs_nat (Z.of_nat j1 - Z.of_nat j2) in
  let gamma_ab (x y : nat) := sqrt (INR (Nat.min x y) / (INR x * INR y)) in
  let g1 := gamma_ab a1 b1 in
  let g2 := gamma_ab a2 b2 in
  (Cnorm (Csum (fun k =>
         (Cof_real (/ g1) *c (psi a1 k *c psi b1 k)) *c
         Cconj (Cof_real (/ g2) *c (psi a2 k *c psi b2 k)))
         (Nat.pred (S (max (max a1 b1) (max a2 b2)))))
   <= (Rmax 8 ((INR C) ^ 3) / 4) * d_factor r i1 i2 * d_factor r j1 j2)%R.
Proof.
  intros C HC seq1 seq2 Hsparse1 Hsparse2 Hge2_1 Hge2_2
         i1 i2 j1 j2 a1 a2 b1 b2 Ha1 Ha2 Hb1 Hb2 Hneq1 Hneq2 H_index_bound.
  set (r := sqrt (INR C)).
  set (d12 := Z.abs_nat (Z.of_nat i1 - Z.of_nat i2)).
  set (d34 := Z.abs_nat (Z.of_nat j1 - Z.of_nat j2)).
  set (gamma_ab x y := sqrt (INR (Nat.min x y) / (INR x * INR y))).
  set (g1 := gamma_ab a1 b1). set (g2 := gamma_ab a2 b2).

  assert (Hreq : r = sqrt (INR C)) by (subst r; reflexivity).
  pose proof (tensor_inner_decay_gen C HC r Hreq seq1 seq2
                Hsparse1 Hsparse2 Hge2_1 Hge2_2
                i1 i2 j1 j2 a1 a2 b1 b2 Ha1 Ha2 Hb1 Hb2 Hneq1 Hneq2 H_index_bound) as Hgen.
  simpl in Hgen.

  assert (HgenR : (Cnorm (Csum (fun k =>
                         (Cof_real (/ gamma_ab a1 b1) *c (psi a1 k *c psi b1 k)) *c
                         Cconj (Cof_real (/ gamma_ab a2 b2) *c (psi a2 k *c psi b2 k)))
                         (max (max a1 b1) (max a2 b2)))
                   <= (Rmax 8 (INR C * (INR C * (INR C * 1))) / r ^ (d12 + d34))%R)%R).
  { apply Hgen. }

  simpl; unfold r, d12, d34, gamma_ab, g1, g2 in *.

  assert (Hgen' : (Cnorm (Csum (fun k =>
                         (Cof_real (/ gamma_ab a1 b1) *c (psi a1 k *c psi b1 k)) *c
                         Cconj (Cof_real (/ gamma_ab a2 b2) *c (psi a2 k *c psi b2 k)))
                         (max (max a1 b1) (max a2 b2)))
                   <= (Rmax 8 ((INR C) ^ 3) / r ^ (d12 + d34))%R)%R).
  { eapply Rle_trans; [exact HgenR|].
    Local Open Scope R_scope.
    assert (Hnum_eq : INR C * (INR C * (INR C * 1)) = (INR C)^3).
    { simpl; rewrite Rmult_1_r; reflexivity. }
    assert (HRmax_eq : Rmax 8 (INR C * (INR C * (INR C * 1))) = Rmax 8 ((INR C)^3)).
    { rewrite Hnum_eq; reflexivity. }
    rewrite HRmax_eq.
    apply Rle_refl. }

  assert (Hr_pos : r > 0) by (apply sqrt_lt_R0_c; apply lt_0_INR; lia).
  assert (Hpow_nz : forall n, r ^ n <> 0) by (intros n; apply pow_nonzero; lra).

  assert (cancel_4_div4 : forall (a b : R), b <> 0 -> (a / 4) * (4 / b) = a / b).
  { intros a b Hb; field; assumption. }

  assert (H_goal : (Rmax 8 ((INR C) ^ 3) / r ^ (d12 + d34) <= 
                   ((Rmax 8 ((INR C) ^ 3) / 4) * d_factor r i1 i2 * d_factor r j1 j2)%R)%R).
  {
    set (RM := Rmax 8 ((INR C) ^ 3)).
    set (dsum := (d12 + d34)%nat).
    unfold d_factor.
    assert (Hi_neq : (i1 =? i2)%nat = false) by (apply Nat.eqb_neq; auto).
    assert (Hj_neq : (j1 =? j2)%nat = false) by (apply Nat.eqb_neq; auto).
    rewrite Hi_neq, Hj_neq.
    change (Z.abs_nat (Z.of_nat i1 - Z.of_nat i2)) with d12.
    change (Z.abs_nat (Z.of_nat j1 - Z.of_nat j2)) with d34.
    assert (H_prod : (2 / r ^ d12) * (2 / r ^ d34) = 4 / r ^ dsum).
    {
      replace (r ^ dsum) with (r ^ d12 * r ^ d34)
        by (subst dsum; rewrite pow_add; reflexivity).
      field; split; apply Hpow_nz.
    }
    rewrite Rmult_assoc.
    rewrite H_prod.
    rewrite (cancel_4_div4 RM (r ^ dsum) (Hpow_nz dsum)).
    subst dsum.
    apply Rle_refl.
  }
  eapply Rle_trans; [exact Hgen' | exact H_goal].
Qed.

(* 伽马函数值不大于一 *)
Lemma gamma_ab_le_1 (a b : nat) (Ha : (a >= 2)%nat) (Hb : (b >= 2)%nat) :
  sqrt (INR (Nat.min a b) / (INR a * INR b)) <= 1.
Proof.
  assert (Ha_pos : 0 < INR a) by (apply lt_0_INR; lia).
  assert (Hb_pos : 0 < INR b) by (apply lt_0_INR; lia).
  assert (Ha_neq0 : INR a <> 0) by (apply Rgt_not_eq; exact Ha_pos).
  assert (Hb_neq0 : INR b <> 0) by (apply Rgt_not_eq; exact Hb_pos).
  assert (Hden_pos : 0 < INR a * INR b) by (apply Rmult_lt_0_compat; assumption).
  assert (Hmin_pos : 0 < INR (Nat.min a b)) by (apply lt_0_INR; lia).

  rewrite <- sqrt_1; apply sqrt_le_1_c.
  - unfold Rdiv; apply Rmult_le_pos.
    + exact (Rlt_le _ _ Hmin_pos).
    + left; apply Rinv_0_lt_compat; exact Hden_pos.
  - lra.
  - unfold Rdiv.
    apply (Rmult_le_reg_r (INR a * INR b)); [exact Hden_pos|].
    field_simplify; [| split; [exact Hb_neq0 | exact Ha_neq0]].
    (* 目标：INR (Nat.min a b) <= INR a * INR b *)
    apply Rle_trans with (INR a).
    - apply le_INR, Nat.le_min_l.
    - rewrite <- (Rmult_1_r (INR a)) at 1.
      apply Rmult_le_compat_l; [apply Rlt_le, Ha_pos|].
      change 1 with (INR 1); apply le_INR; lia.
Qed.

(* d因子桥接不等式 *)
Lemma d_factor_bridge (C : nat) (s2 sC : R) (i j : nat)
  (Hs2_pos : 0 < s2) (Hs2_gt1 : s2 > 1) (HsC_pos : 0 < sC)
  (HsC_ge_s2 : sC >= s2) (HC3_ge8 : (INR C)^3 >= 8)
  (Hdist_le6 : (Z.abs_nat (Z.of_nat i - Z.of_nat j) <= 6)%nat)
  (Hs2_eq : s2 = sqrt (INR 2)) (HsC_eq : sC = sqrt (INR C)) :
  d_factor s2 i j <= ((INR C)^3 / 8) * d_factor sC i j.
Proof.
  set (d := Z.abs_nat (Z.of_nat i - Z.of_nat j)).
  assert (Hd_le_6 : (d <= 6)%nat) by exact Hdist_le6.
  assert (H_pow_neq0 : forall (x : R) (n : nat), x <> 0 -> x ^ n <> 0). {
    induction n; simpl; intros H.
    - apply R1_neq_R0.
    - apply Rmult_integral_contrapositive; split; [exact H | apply IHn; exact H]. }
  assert (H_div_pow : forall (a b : R) (n : nat), b <> 0 -> (a / b) ^ n = a ^ n / b ^ n). {
    intros a b n Hb. induction n as [|n IH]; simpl.
    - field; apply R1_neq_R0.
    - rewrite IH. field. split; [| exact Hb].
      clear -Hb. induction n as [|m Hm]; simpl.
      + apply R1_neq_R0.
      + apply Rmult_integral_contrapositive; split; [exact Hb | exact Hm]. }

  subst s2 sC.

  unfold d_factor.
  destruct (i =? j) eqn:Heq.
  - simpl; rewrite Rmult_1_r.
    assert (H1 : 1 <= INR C ^ 3 / 8). {
      apply (Rmult_le_reg_r 8); [lra|].
      rewrite Rmult_1_l.
      unfold Rdiv.
      rewrite Rmult_assoc, Rinv_l; [| lra].
      rewrite Rmult_1_r.
      apply Rge_le in HC3_ge8.
      exact HC3_ge8.
    }
    exact H1.
  - assert (H_C_pos_nat : (C > 0)%nat). {
      destruct C as [|C']; [simpl in HC3_ge8; lra | lia]. }
    assert (H_INR_C_pos : 0 < INR C)
      by (apply lt_0_INR; exact H_C_pos_nat).

    assert (H_sqrt2_pos : 0 < sqrt (INR 2))
      by (apply sqrt_lt_R0_c; apply lt_0_INR; lia).
    assert (H_sqrtC_pos : 0 < sqrt (INR C))
      by (apply sqrt_lt_R0_c; exact H_INR_C_pos).

    assert (H_sq_sqrtC : (sqrt (INR C)) ^ 2 = INR C). {
      rewrite <- Rsqr_pow2.
      apply Rsqr_sqrt.
      exact (Rlt_le _ _ H_INR_C_pos). }
    assert (H_sq_sqrt2 : (sqrt (INR 2)) ^ 2 = INR 2). {
      rewrite <- Rsqr_pow2.
      apply Rsqr_sqrt.
      apply Rlt_le; apply lt_0_INR; lia. }

    assert (H_pow6_eq : forall x : R, x ^ 6 = (x ^ 2) ^ 3). {
      intro x; simpl; ring. }

    assert (H_sqrtC_pow6 : (sqrt (INR C)) ^ 6 = (INR C) ^ 3). {
      rewrite H_pow6_eq, H_sq_sqrtC; reflexivity. }
    assert (H_sqrt2_pow6 : (sqrt (INR 2)) ^ 6 = 8). {
      rewrite H_pow6_eq, H_sq_sqrt2; simpl; ring. }
    assert (H_eq : (sqrt (INR C) / sqrt (INR 2)) ^ 6 = (INR C)^3 / 8). {
      rewrite (H_div_pow _ _ _ (Rgt_not_eq _ _ H_sqrt2_pos)).
      rewrite H_sqrtC_pow6, H_sqrt2_pow6.
      reflexivity. }

    assert (H_prod_div_equiv : forall (b c a : R), 0 < a -> (b <= c * a <-> b / a <= c)). {
      intros b c a Ha; split.
      - intro Hle.
        unfold Rdiv.
        apply (Rmult_le_compat_r (/ a)) in Hle.
        + rewrite Rmult_assoc, Rinv_r, Rmult_1_r in Hle; [exact Hle | lra].
        + apply Rlt_le; apply Rinv_0_lt_compat; exact Ha.
      - intro Hle.
        unfold Rdiv in Hle.
        apply (Rmult_le_compat_r a) in Hle; [| lra].
        rewrite Rmult_assoc, Rinv_l, Rmult_1_r in Hle; [exact Hle | lra].
    }

    assert (H_general : forall (a b c : R), 0 < a -> 0 < b ->
      (2 / a <= c * (2 / b) <-> b <= c * a)). {
      intros a b c Ha Hb.
      assert (H_2_div_b_pos : 0 < 2 / b)
        by (apply Rdiv_lt_0_compat; lra).
      assert (H_aux : forall x y z, 0 < y -> (x <= z * y <-> x / y <= z)). {
        intros x y z Hy; split.
        - intro H.
          apply (Rmult_le_reg_r y). exact Hy.
          replace (x / y * y) with x by (field; lra).
          exact H.
        - intro H.
          apply (Rmult_le_compat_r y) in H; [| lra].
          replace ((x / y) * y) with x in H by (field; lra).
          exact H.
      }
      rewrite (H_aux (2 / a) (2 / b) c H_2_div_b_pos).
      replace ((2 / a) / (2 / b)) with (b / a) by (field; lra).
      split.
      - intro Hdiv. apply (proj2 (H_prod_div_equiv b c a Ha)). exact Hdiv.
      - intro Hineq. apply (proj1 (H_prod_div_equiv b c a Ha)). exact Hineq.
    }

    assert (H_pow_pos : forall (x : R) (n : nat), 0 < x -> 0 < x ^ n). {
      induction n; simpl; intros; [lra| apply Rmult_lt_0_compat; auto].
    }

    fold d.
    apply (proj2 (H_general ((sqrt (INR 2)) ^ d) ((sqrt (INR C)) ^ d) ((INR C)^3 / 8)
      (H_pow_pos (sqrt (INR 2)) d H_sqrt2_pos)
      (H_pow_pos (sqrt (INR C)) d H_sqrtC_pos))).

    apply (proj2 (H_prod_div_equiv ((sqrt (INR C)) ^ d) ((INR C)^3 / 8) ((sqrt (INR 2)) ^ d)
      (H_pow_pos (sqrt (INR 2)) d H_sqrt2_pos))).

    rewrite <- (H_div_pow (sqrt (INR C)) (sqrt (INR 2)) d);
      [| apply Rgt_not_eq, H_sqrt2_pos].
    rewrite <- H_eq.
    apply Rle_pow.
    - apply (Rmult_le_reg_r (sqrt (INR 2))).
      + exact H_sqrt2_pos.
      + rewrite Rmult_1_l.
        replace ((sqrt (INR C) / sqrt (INR 2)) * sqrt (INR 2)) with (sqrt (INR C))
          by (field; apply Rgt_not_eq, H_sqrt2_pos).
        apply Rge_le; exact HsC_ge_s2.
    - exact Hd_le_6.
Qed.

(* 序列最大值折叠 *)
Lemma fold_right_max_seq : forall (m n : nat), fold_right Nat.max 0%nat (List.seq m (S n)) = (m + n)%nat.
Proof.
  intros m n. generalize m.
  refine (nat_ind (fun n => forall m, fold_right Nat.max 0%nat (List.seq m (S n)) = (m + n)%nat) _ _ n).
  - intro x; simpl; destruct x; simpl; auto; apply f_equal; rewrite <- plus_n_O; auto.
  - intros n0 IHn.
    intro m0.
    Opaque Nat.max. simpl in *. Transparent Nat.max.
    rewrite (IHn (S m0)).
    unfold Nat.max; destruct (Nat.leb m0 ((S m0) + n0)) eqn:Hcmp; auto.
    + induction m0; simpl; auto.
    + assert (Htrue : Nat.leb m0 ((S m0) + n0) = true) by (induction m0; simpl; auto).
      rewrite Htrue in Hcmp; discriminate.
Qed.

(* 等值索引情形下的求和缩放化简（i对称版本） *)
Lemma decay_case_eq_i :
  forall (C : nat) (HC : (C >= 2)%nat)
    (seq1 seq2 : nat -> nat)
    (Hg1 : forall i, (seq1 i >= 2)%nat)
    (Hg2 : forall i, (seq2 i >= 2)%nat)
    (Hsp1_2 : forall i, (INR (seq1 (S i)) > INR 2 * INR (seq1 i))%R)
    (Hsp2_2 : forall i, (INR (seq2 (S i)) > INR 2 * INR (seq2 i))%R)
    (i2 j1 j2 : nat)
    (Hneq_j : j1 <> j2)
    (gamma1 gamma2 : R)
    (Hgamma1_def : gamma1 = sqrt (INR (Nat.min (seq1 i2) (seq2 j1)) / (INR (seq1 i2) * INR (seq2 j1))))
    (Hgamma2_def : gamma2 = sqrt (INR (Nat.min (seq1 i2) (seq2 j2)) / (INR (seq1 i2) * INR (seq2 j2))))
    (N0 : nat)
    (HN0_ge_Nmax : (N0 >= Nat.max (Nat.max (seq1 i2) (seq2 j1)) (Nat.max (seq1 i2) (seq2 j2)))%nat)
    (H_seq_cond_i : (seq1 i2 >= Nat.min (seq2 j1) (seq2 j2))%nat),
  let a := seq1 i2 in
  let b1 := seq2 j1 in
  let b2 := seq2 j2 in
  let N0' := Nat.min N0 (Nat.min a (Nat.min b1 b2)) in
  Csum (fun k : nat =>
    (Cof_real (/ gamma1) *c (psi a k *c psi b1 k)) *c
    Cconj (Cof_real (/ gamma2) *c (psi a k *c psi b2 k))) N0
  = Cof_real (/ (INR a * gamma1 * gamma2)) *c Csum (fun k : nat => psi b1 k *c Cconj (psi b2 k)) N0'.
Proof.
  intros; subst a b1 b2 N0'.
  set (a := seq1 i2) in *; set (b1 := seq2 j1) in *; set (b2 := seq2 j2) in *.
  assert (Ha_ge2 : (a >= 2)%nat) by apply Hg1.
  assert (Hb1_ge2 : (b1 >= 2)%nat) by apply Hg2.
  assert (Hb2_ge2 : (b2 >= 2)%nat) by apply Hg2.
  set (N0' := Nat.min N0 (Nat.min a (Nat.min b1 b2))).
  assert (HN0'_le_N0 : (N0' <= N0)%nat) by (apply Nat.le_min_l).

  assert (Cmul_0_l' : forall x, C0 *c x = C0) by apply Cmul_0_l.
  assert (Cmul_0_r' : forall x, x *c C0 = C0) by apply Cmul_0_r.
  assert (Cconj_0' : Cconj C0 = C0) by apply Cconj_0.

  assert (Hgamma1_pos : 0 < gamma1).
  { rewrite Hgamma1_def; apply sqrt_lt_R0_c; apply Rdiv_lt_0_compat.
    - apply lt_0_INR; lia.
    - apply Rmult_lt_0_compat; apply lt_0_INR; lia. }
  assert (Hgamma2_pos : 0 < gamma2).
  { rewrite Hgamma2_def; apply sqrt_lt_R0_c; apply Rdiv_lt_0_compat.
    - apply lt_0_INR; lia.
    - apply Rmult_lt_0_compat; apply lt_0_INR; lia. }

  assert (Htrunc : Csum (fun k => (Cof_real (/ gamma1) *c (psi a k *c psi b1 k)) *c
                                 Cconj (Cof_real (/ gamma2) *c (psi a k *c psi b2 k))) N0
                = Csum (fun k => (Cof_real (/ gamma1) *c (psi a k *c psi b1 k)) *c
                                 Cconj (Cof_real (/ gamma2) *c (psi a k *c psi b2 k))) N0').
  {
    apply (Csum_trunc_tail _ N0' N0 HN0'_le_N0).
    intros k [Hk1 Hk2].
    unfold N0' in *.
    assert (Hk_ge_min : (k >= Nat.min N0 (Nat.min a (Nat.min b1 b2)))%nat) by exact Hk1.
    destruct (Nat.min_spec N0 (Nat.min a (Nat.min b1 b2))) as [[_ HminN] | [_ HminN]].
    - exfalso; lia.
    - rewrite HminN in Hk_ge_min.
      destruct (Nat.min_spec a (Nat.min b1 b2)) as [[_ Hmin_a] | [_ Hmin_rest]].
      + rewrite Hmin_a in Hk_ge_min.
        apply (psi_ge_n_zero a k) in Hk_ge_min.
        rewrite Hk_ge_min.
        rewrite (Cmul_0_l' (psi b1 k)).
        rewrite (Cmul_0_r' (Cof_real (/ gamma1))).
        rewrite (Cmul_0_l' (psi b2 k)).
        rewrite (Cmul_0_r' (Cof_real (/ gamma2))).
        rewrite Cconj_0'.
        rewrite Cmul_0_l'.
        reflexivity.
      + rewrite Hmin_rest in Hk_ge_min.
        destruct (Nat.min_spec b1 b2) as [[_ Hmin_b1] | [_ Hmin_b2]].
        * rewrite Hmin_b1 in Hk_ge_min.
          apply (psi_ge_n_zero b1 k) in Hk_ge_min.
          rewrite Hk_ge_min.
          rewrite (Cmul_0_r' (psi a k)).
          rewrite (Cmul_0_r' (Cof_real (/ gamma1))).
          rewrite Cmul_0_l'.
          reflexivity.
        * rewrite Hmin_b2 in Hk_ge_min.
          apply (psi_ge_n_zero b2 k) in Hk_ge_min.
          rewrite Hk_ge_min.
          rewrite (Cmul_0_r' (psi a k)).
          rewrite (Cmul_0_r' (Cof_real (/ gamma2))).
          rewrite Cconj_0'.
          rewrite (Cmul_0_r' (Cof_real (/ gamma1) *c (psi a k *c psi b1 k))).
          reflexivity.
  }
  rewrite Htrunc.

  assert (Cconj_mul : forall a b, Cconj (a *c b) = Cconj a *c Cconj b).
  { intros; destruct a, b; unfold Cconj, Cmul; simpl; f_equal; ring. }
  assert (Cconj_Cof_real : forall r, Cconj (Cof_real r) = Cof_real r).
  { intros; unfold Cof_real, Cconj; simpl; apply Complex_eq; simpl; ring. }
  assert (Cof_real_mul : forall r1 r2, Cof_real r1 *c Cof_real r2 = Cof_real (r1 * r2)).
  { intros; unfold Cof_real, Cmul; simpl; apply Complex_eq; simpl; ring. }
  assert (H_psi_self : forall n k, (k < n)%nat ->
      psi n k *c Cconj (psi n k) = Cof_real (1 / INR n)).
  { intros n k Hlt. rewrite <- Cnorm_sq_Cof_real, Cnorm_sq_psi_exact.
    rewrite (proj2 (Nat.ltb_lt k n) Hlt); reflexivity. }

  assert (H_factor : forall k, (k < N0')%nat ->
    (Cof_real (/ gamma1) *c (psi a k *c psi b1 k)) *c
    Cconj (Cof_real (/ gamma2) *c (psi a k *c psi b2 k))
    = Cof_real (/ (INR a * gamma1 * gamma2)) *c (psi b1 k *c Cconj (psi b2 k))).
  {
    intros k Hk.
    assert (Hk_lt_a : (k < a)%nat)
      by (apply Nat.lt_le_trans with N0';
          [exact Hk | apply Nat.le_trans with (Nat.min a (Nat.min b1 b2)); [apply Nat.le_min_r | apply Nat.le_min_l]]).
    assert (Hk_lt_b1 : (k < b1)%nat)
      by (apply Nat.lt_le_trans with N0';
          [exact Hk | apply Nat.le_trans with (Nat.min a (Nat.min b1 b2));
           [apply Nat.le_min_r | apply Nat.le_trans with (Nat.min b1 b2); [apply Nat.le_min_r | apply Nat.le_min_l]]]).
    assert (Hk_lt_b2 : (k < b2)%nat)
      by (apply Nat.lt_le_trans with N0';
          [exact Hk | apply Nat.le_trans with (Nat.min a (Nat.min b1 b2));
           [apply Nat.le_min_r | apply Nat.le_trans with (Nat.min b1 b2); [apply Nat.le_min_r | apply Nat.le_min_r]]]).

    rewrite Cconj_mul, Cconj_Cof_real, Cconj_mul.

    assert (H_inner : (Cconj (psi a k) *c Cconj (psi b2 k)) *c (psi a k *c psi b1 k)
                    = Cof_real (1 / INR a) *c (psi b1 k *c Cconj (psi b2 k))).
    {
      rewrite (Cmul_comm (Cconj (psi a k) *c Cconj (psi b2 k)) (psi a k *c psi b1 k)).
      rewrite <- (Cmul_assoc (psi a k *c psi b1 k) (Cconj (psi a k)) (Cconj (psi b2 k))).
      rewrite (Cmul_assoc (psi a k) (psi b1 k) (Cconj (psi a k))).
      rewrite (Cmul_comm (psi b1 k) (Cconj (psi a k))).
      rewrite <- (Cmul_assoc (psi a k) (Cconj (psi a k)) (psi b1 k)).
      rewrite H_psi_self by exact Hk_lt_a.
      rewrite Cmul_assoc.
      reflexivity.
    }

    rewrite (Cmul_comm (Cof_real (/ gamma2)) (Cconj (psi a k) *c Cconj (psi b2 k))).
    rewrite (Cmul_assoc (Cof_real (/ gamma1)) (psi a k *c psi b1 k) _).
    rewrite <- (Cmul_assoc (psi a k *c psi b1 k) (Cconj (psi a k) *c Cconj (psi b2 k)) (Cof_real (/ gamma2))).
    rewrite (Cmul_comm (psi a k *c psi b1 k) (Cconj (psi a k) *c Cconj (psi b2 k))).
    rewrite <- (Cmul_assoc (Cof_real (/ gamma1)) _ (Cof_real (/ gamma2))).
    rewrite (Cmul_comm (Cof_real (/ gamma1) *c ((Cconj (psi a k) *c Cconj (psi b2 k)) *c (psi a k *c psi b1 k))) (Cof_real (/ gamma2))).
    rewrite <- (Cmul_assoc (Cof_real (/ gamma2)) (Cof_real (/ gamma1)) _).
    rewrite (Cmul_comm (Cof_real (/ gamma2)) (Cof_real (/ gamma1))).
    rewrite Cof_real_mul.

    rewrite H_inner.

    rewrite <- (Cmul_assoc (Cof_real (/ gamma1 * / gamma2)) (Cof_real (1 / INR a))
      (psi b1 k *c Cconj (psi b2 k))).
    rewrite Cof_real_mul.
    apply (f_equal (fun t : Complex => t *c (psi b1 k *c Cconj (psi b2 k)))).

    assert (HINR_a_pos : 0 < INR a) by (apply lt_0_INR; lia).
    apply (f_equal Cof_real).
    field; repeat split; try apply Rgt_not_eq; auto.
  }

  assert (Csum_ext_lt : forall n f g, (forall k, (k < n)%nat -> f k = g k) -> Csum f n = Csum g n).
  { induction n; intros; simpl.
    - reflexivity.
    - rewrite IHn with (g := g).
      + f_equal; apply H; lia.
      + intros k Hk; apply H; lia. }

  assert (Csum_scal_l : forall (c : Complex) (f : nat -> Complex) (n : nat),
    Csum (fun k => c *c f k) n = c *c Csum f n).
  { induction n; simpl; [rewrite Cmul_0_r; reflexivity | rewrite IHn, Cmul_add_distr_l; reflexivity]. }

  assert (Hsum_factor : Csum (fun k => (Cof_real (/ gamma1) *c (psi a k *c psi b1 k)) *c
                                      Cconj (Cof_real (/ gamma2) *c (psi a k *c psi b2 k))) N0'
                      = Cof_real (/ (INR a * gamma1 * gamma2)) *c
                        Csum (fun k => psi b1 k *c Cconj (psi b2 k)) N0').
  {
    rewrite (Csum_ext_lt N0' (fun k => (Cof_real (/ gamma1) *c (psi a k *c psi b1 k)) *c
                                 Cconj (Cof_real (/ gamma2) *c (psi a k *c psi b2 k)))
                             (fun k => Cof_real (/ (INR a * gamma1 * gamma2)) *c (psi b1 k *c Cconj (psi b2 k)))
                             H_factor).
    rewrite Csum_scal_l; reflexivity.
  }
  rewrite Hsum_factor.
  reflexivity.
Qed.

(* 等值索引情形下的求和缩放化简（j对称版本） *)
Lemma decay_case_eq_j :
  forall (C : nat) (HC : (C >= 2)%nat)
    (seq1 seq2 : nat -> nat)
    (Hg1 : forall i, (seq1 i >= 2)%nat)
    (Hg2 : forall i, (seq2 i >= 2)%nat)
    (Hsp1_2 : forall i, (INR (seq1 (S i)) > INR 2 * INR (seq1 i))%R)
    (Hsp2_2 : forall i, (INR (seq2 (S i)) > INR 2 * INR (seq2 i))%R)
    (i1 i2 j2 : nat)
    (Hneq_i : i1 <> i2)
    (gamma1 gamma2 : R)
    (Hgamma1_def : gamma1 = sqrt (INR (Nat.min (seq1 i1) (seq2 j2)) / (INR (seq1 i1) * INR (seq2 j2))))
    (Hgamma2_def : gamma2 = sqrt (INR (Nat.min (seq1 i2) (seq2 j2)) / (INR (seq1 i2) * INR (seq2 j2))))
    (N0 : nat)
    (HN0_ge_Nmax : (N0 >= Nat.max (Nat.max (seq1 i1) (seq2 j2)) (Nat.max (seq1 i2) (seq2 j2)))%nat)
    (H_seq_cond_j : (seq2 j2 >= Nat.min (seq1 i1) (seq1 i2))%nat),
  let a1 := seq1 i1 in
  let a2 := seq1 i2 in
  let b := seq2 j2 in
  let N0' := Nat.min N0 (Nat.min b (Nat.min a1 a2)) in
  Csum (fun k : nat =>
    (Cof_real (/ gamma1) *c (psi a1 k *c psi b k)) *c
    Cconj (Cof_real (/ gamma2) *c (psi a2 k *c psi b k))) N0
  = Cof_real (/ (INR b * gamma1 * gamma2)) *c Csum (fun k : nat => psi a1 k *c Cconj (psi a2 k)) N0'.
Proof.
  intros; subst a1 a2 b N0'.
  set (a1 := seq1 i1) in *; set (a2 := seq1 i2) in *; set (b := seq2 j2) in *.
  assert (Ha1_ge2 : (a1 >= 2)%nat) by apply Hg1.
  assert (Ha2_ge2 : (a2 >= 2)%nat) by apply Hg1.
  assert (Hb_ge2 : (b >= 2)%nat) by apply Hg2.
  set (N0' := Nat.min N0 (Nat.min b (Nat.min a1 a2))).
  assert (HN0'_le_N0 : (N0' <= N0)%nat) by (apply Nat.le_min_l).

  assert (Cmul_0_l' : forall x, C0 *c x = C0) by apply Cmul_0_l.
  assert (Cmul_0_r' : forall x, x *c C0 = C0) by apply Cmul_0_r.
  assert (Cconj_0' : Cconj C0 = C0) by apply Cconj_0.

  assert (Hgamma1_pos : 0 < gamma1).
  { rewrite Hgamma1_def; apply sqrt_lt_R0_c; apply Rdiv_lt_0_compat.
    - apply lt_0_INR; lia.
    - apply Rmult_lt_0_compat; apply lt_0_INR; lia. }
  assert (Hgamma2_pos : 0 < gamma2).
  { rewrite Hgamma2_def; apply sqrt_lt_R0_c; apply Rdiv_lt_0_compat.
    - apply lt_0_INR; lia.
    - apply Rmult_lt_0_compat; apply lt_0_INR; lia. }

  assert (Htrunc : Csum (fun k => (Cof_real (/ gamma1) *c (psi a1 k *c psi b k)) *c
                                 Cconj (Cof_real (/ gamma2) *c (psi a2 k *c psi b k))) N0
                = Csum (fun k => (Cof_real (/ gamma1) *c (psi a1 k *c psi b k)) *c
                                 Cconj (Cof_real (/ gamma2) *c (psi a2 k *c psi b k))) N0').
  {
    apply (Csum_trunc_tail _ N0' N0 HN0'_le_N0).
    intros k [Hk1 Hk2].
    unfold N0' in *.
    assert (Hk_ge_min : (k >= Nat.min N0 (Nat.min b (Nat.min a1 a2)))%nat) by exact Hk1.
    destruct (Nat.min_spec N0 (Nat.min b (Nat.min a1 a2))) as [[_ HminN] | [_ HminN]].
    - exfalso; lia.
    - rewrite HminN in Hk_ge_min.
      destruct (Nat.min_spec b (Nat.min a1 a2)) as [[_ Hmin_b] | [_ Hmin_rest]].
      + rewrite Hmin_b in Hk_ge_min.
        apply (psi_ge_n_zero b k) in Hk_ge_min.
        rewrite Hk_ge_min.
        rewrite (Cmul_0_r' (psi a1 k)).
        rewrite (Cmul_0_r' (Cof_real (/ gamma1))).
        rewrite (Cmul_0_r' (psi a2 k)).
        rewrite (Cmul_0_r' (Cof_real (/ gamma2))).
        rewrite Cconj_0'.
        rewrite Cmul_0_l'.
        reflexivity.
      + rewrite Hmin_rest in Hk_ge_min.
        destruct (Nat.min_spec a1 a2) as [[_ Hmin_a1] | [_ Hmin_a2]].
        * rewrite Hmin_a1 in Hk_ge_min.
          apply (psi_ge_n_zero a1 k) in Hk_ge_min.
          rewrite Hk_ge_min.
          rewrite (Cmul_0_l' (psi b k)).
          rewrite (Cmul_0_r' (Cof_real (/ gamma1))).
          rewrite Cmul_0_l'.
          reflexivity.
        * rewrite Hmin_a2 in Hk_ge_min.
          apply (psi_ge_n_zero a2 k) in Hk_ge_min.
          rewrite Hk_ge_min.
          rewrite (Cmul_0_l' (psi b k)).
          rewrite (Cmul_0_r' (Cof_real (/ gamma2))).
          rewrite Cconj_0'.
          rewrite (Cmul_0_r' (Cof_real (/ gamma1) *c (psi a1 k *c psi b k))).
          reflexivity.
  }
  rewrite Htrunc.

  assert (Cconj_mul : forall a b, Cconj (a *c b) = Cconj a *c Cconj b)
    by (intros; destruct a, b; unfold Cconj, Cmul; simpl; f_equal; ring).
  assert (Cconj_Cof_real : forall r, Cconj (Cof_real r) = Cof_real r)
    by (intros; unfold Cof_real, Cconj; simpl; apply Complex_eq; simpl; ring).
  assert (Cof_real_mul : forall r1 r2, Cof_real r1 *c Cof_real r2 = Cof_real (r1 * r2))
    by (intros; unfold Cof_real, Cmul; simpl; apply Complex_eq; simpl; ring).
  assert (H_psi_self : forall n k, (k < n)%nat -> psi n k *c Cconj (psi n k) = Cof_real (1 / INR n)).
  { intros n k Hlt. rewrite <- Cnorm_sq_Cof_real, Cnorm_sq_psi_exact.
    rewrite (proj2 (Nat.ltb_lt k n) Hlt); reflexivity. }

  assert (H_factor : forall k, (k < N0')%nat ->
    (Cof_real (/ gamma1) *c (psi a1 k *c psi b k)) *c
    Cconj (Cof_real (/ gamma2) *c (psi a2 k *c psi b k))
    = Cof_real (/ (INR b * gamma1 * gamma2)) *c (psi a1 k *c Cconj (psi a2 k))).
  {
    intros k Hk.
    assert (Hk_lt_b : (k < b)%nat)
      by (apply Nat.lt_le_trans with N0'; [exact Hk | apply Nat.le_trans with (Nat.min b (Nat.min a1 a2)); [apply Nat.le_min_r | apply Nat.le_min_l]]).
    assert (Hk_lt_a1 : (k < a1)%nat)
      by (apply Nat.lt_le_trans with N0'; [exact Hk | apply Nat.le_trans with (Nat.min b (Nat.min a1 a2)); [apply Nat.le_min_r | apply Nat.le_trans with (Nat.min a1 a2); [apply Nat.le_min_r | apply Nat.le_min_l]]]).
    assert (Hk_lt_a2 : (k < a2)%nat)
      by (apply Nat.lt_le_trans with N0'; [exact Hk | apply Nat.le_trans with (Nat.min b (Nat.min a1 a2)); [apply Nat.le_min_r | apply Nat.le_trans with (Nat.min a1 a2); [apply Nat.le_min_r | apply Nat.le_min_r]]]).
    rewrite Cconj_mul, Cconj_Cof_real, Cconj_mul.
    rewrite (Cmul_comm (Cof_real (/ gamma2)) (Cconj (psi a2 k) *c Cconj (psi b k))).
    rewrite (Cmul_assoc (Cof_real (/ gamma1)) (psi a1 k *c psi b k) _).
    rewrite <- (Cmul_assoc (psi a1 k *c psi b k) (Cconj (psi a2 k) *c Cconj (psi b k)) (Cof_real (/ gamma2))).
    rewrite (Cmul_comm (psi a1 k *c psi b k) (Cconj (psi a2 k) *c Cconj (psi b k))).
    rewrite <- (Cmul_assoc (Cof_real (/ gamma1)) _ (Cof_real (/ gamma2))).
    rewrite (Cmul_comm (Cof_real (/ gamma1) *c ((Cconj (psi a2 k) *c Cconj (psi b k)) *c (psi a1 k *c psi b k))) (Cof_real (/ gamma2))).
    rewrite <- (Cmul_assoc (Cof_real (/ gamma2)) (Cof_real (/ gamma1)) _).
    rewrite (Cmul_comm (Cof_real (/ gamma2)) (Cof_real (/ gamma1))), Cof_real_mul.

    assert (H_inner : (Cconj (psi a2 k) *c Cconj (psi b k)) *c (psi a1 k *c psi b k)
                    = Cof_real (1 / INR b) *c (psi a1 k *c Cconj (psi a2 k))).
    {
      rewrite (Cmul_comm (Cconj (psi a2 k) *c Cconj (psi b k)) (psi a1 k *c psi b k)).
      rewrite <- (Cmul_assoc (psi a1 k *c psi b k) (Cconj (psi a2 k)) (Cconj (psi b k))).
      rewrite (Cmul_assoc (psi a1 k) (psi b k) (Cconj (psi a2 k))).
      rewrite (Cmul_comm (psi b k) (Cconj (psi a2 k))).
      rewrite <- (Cmul_assoc (psi a1 k) (Cconj (psi a2 k)) (psi b k)).
      rewrite (Cmul_assoc (psi a1 k *c Cconj (psi a2 k)) (psi b k) (Cconj (psi b k))).
      rewrite H_psi_self by exact Hk_lt_b.
      rewrite (Cmul_comm (psi a1 k *c Cconj (psi a2 k)) (Cof_real (1 / INR b))).
      reflexivity.
    }

    rewrite H_inner.
    rewrite <- (Cmul_assoc (Cof_real (/ gamma1 * / gamma2)) (Cof_real (1 / INR b)) _), Cof_real_mul.
    apply (f_equal (fun t => t *c (psi a1 k *c Cconj (psi a2 k)))).
    assert (HINR_b_pos : 0 < INR b) by (apply lt_0_INR; lia).
    apply (f_equal Cof_real); field; repeat split; try apply Rgt_not_eq; auto.
  }

  assert (Csum_ext_lt : forall n f g, (forall k, (k < n)%nat -> f k = g k) -> Csum f n = Csum g n)
    by (induction n; intros; simpl; [reflexivity | rewrite IHn with (g := g); [f_equal; apply H; lia | intros; apply H; lia]]).
  assert (Csum_scal_l : forall (c : Complex) (f : nat -> Complex) (n : nat), Csum (fun k => c *c f k) n = c *c Csum f n)
    by (induction n; simpl; [rewrite Cmul_0_r; reflexivity | rewrite IHn, Cmul_add_distr_l; reflexivity]).
  assert (Hsum_factor : Csum (fun k => (Cof_real (/ gamma1) *c (psi a1 k *c psi b k)) *c
                                      Cconj (Cof_real (/ gamma2) *c (psi a2 k *c psi b k))) N0'
                      = Cof_real (/ (INR b * gamma1 * gamma2)) *c Csum (fun k => psi a1 k *c Cconj (psi a2 k)) N0').
  {
    rewrite (Csum_ext_lt N0' _ _ H_factor), Csum_scal_l; reflexivity.
  }
  rewrite Hsum_factor.
  reflexivity.
Qed.

(* 预定义的 d_factor 在 j1 j2 相邻时的具体值（当距离为1时，d_factor = 2/√2）*)
Lemma d_factor_eq_2_div_sqrt2 (j1 j2 : nat) (Hj_neq : j1 <> j2)
  (H_adj : Z.abs_nat (Z.of_nat j1 - Z.of_nat j2) = 1%nat) :
  d_factor (sqrt (INR 2)) j1 j2 = 2 / sqrt (INR 2).
Proof.
  unfold d_factor.
  destruct (Nat.eqb_spec j1 j2) as [Heq | Hneq]; [exfalso; exact (Hj_neq Heq) |].
  rewrite H_adj. rewrite pow_1. reflexivity.
Qed.

(* 复数共轭保持模长 *)
Lemma Cnorm_conj_eq (z : Complex) : Cnorm (Cconj z) = Cnorm z.
Proof.
  unfold Cnorm.
  f_equal.
  unfold Cnorm_sq.
  destruct z as [a b]; simpl.
  unfold Rsqr.
  replace ((- b) * (- b)) with (b * b) by ring.
  ring.
Qed.

(* 求和项互换共轭后的模长相等 *)
Lemma Cnorm_Csum_swap (f g : nat -> Complex) (N : nat) :
  Cnorm (Csum (fun k => f k *c Cconj (g k)) N)
  = Cnorm (Csum (fun k => g k *c Cconj (f k)) N).
Proof.
  rewrite <- (Cnorm_conj_eq (Csum (fun k => g k *c Cconj (f k)) N)).
  f_equal.
  induction N as [|N IH].
  - simpl; unfold Cconj; simpl; rewrite Ropp_0; reflexivity.
  - simpl.
    assert (Hadd : forall x y, Cconj (x +c y) = Cconj x +c Cconj y).
    { intros x y; destruct x as [a b], y as [c d]; simpl; apply Complex_eq; simpl; ring. }
    rewrite Hadd.
    rewrite IH.
    assert (Hgoal : forall u v, u *c Cconj v = Cconj (v *c Cconj u)).
    { intros [a b] [c d]; unfold Cconj, Cmul; simpl; apply Complex_eq; simpl; ring. }
    rewrite (Hgoal (f N) (g N)).
    reflexivity.
Qed.

(* 将衰减界转化为 d_factor 形式（通用版本） *)
Lemma decay_bound_to_d_factor_gen (seq : nat -> nat) (j1 j2 : nat) (Hj_neq : j1 <> j2)
  (H_adj : Z.abs_nat (Z.of_nat j1 - Z.of_nat j2) = 1%nat)
  (Hbound : Cnorm (Csum (fun k : nat => psi (nth 0 (map seq (if j1 <? j2 then [j1; j2] else [j2; j1])) 0%nat) k
                            *c Cconj (psi (nth 1 (map seq (if j1 <? j2 then [j1; j2] else [j2; j1])) 0%nat) k))
                    (seq (fold_right Nat.max 0%nat (if j1 <? j2 then [j1; j2] else [j2; j1])) - 1))
            <= 2 * / (sqrt (1 + 1) * 1))
  : Cnorm (Csum (fun k : nat => psi (seq j1) k *c Cconj (psi (seq j2) k)) (seq (Nat.max j1 j2) - 1))
    <= d_factor (sqrt (INR 2)) j1 j2.
Proof.
  set (I := if j1 <? j2 then [j1; j2] else [j2; j1]).
  assert (HmaxI_fold : fold_right Nat.max 0%nat (if j1 <? j2 then [j1; j2] else [j2; j1]) = Nat.max j1 j2).
  {
    destruct (j1 <? j2); simpl; rewrite Nat.max_0_r; [reflexivity | apply Nat.max_comm].
  }
  rewrite HmaxI_fold in Hbound.
  assert (Hsqrt_eq : 2 * / (sqrt (1 + 1) * 1) = 2 / sqrt (INR 2)).
  {
    replace (1+1) with (INR 2) by (simpl; ring).
    rewrite Rmult_1_r.
    reflexivity.
  }
  rewrite Hsqrt_eq in Hbound.
  destruct (j1 <? j2) eqn:Hcmp.
  - (* j1 < j2 *)
    assert (Hnth0 : nth 0 (map seq [j1; j2]) 0%nat = seq j1) by reflexivity.
    assert (Hnth1 : nth 1 (map seq [j1; j2]) 0%nat = seq j2) by reflexivity.
    rewrite Hnth0, Hnth1 in Hbound.
    rewrite (d_factor_eq_2_div_sqrt2 j1 j2 Hj_neq H_adj).
    exact Hbound.
  - (* j2 < j1 *)
    assert (Hnth0 : nth 0 (map seq [j2; j1]) 0%nat = seq j2) by reflexivity.
    assert (Hnth1 : nth 1 (map seq [j2; j1]) 0%nat = seq j1) by reflexivity.
    rewrite Hnth0, Hnth1 in Hbound.
    rewrite Cnorm_Csum_swap in Hbound.
    rewrite (d_factor_eq_2_div_sqrt2 j1 j2 Hj_neq H_adj).
    exact Hbound.
Qed.

(* 实数不小于推出自然数不小于 *)
Lemma INR_ge_nat (n m : nat) : INR n >= INR m -> (n >= m)%nat.
Proof.
  intros H.
  destruct (Nat.le_gt_cases m n) as [Hle | Hlt].
  - exact Hle.
  - exfalso.
    assert (INR m > INR n) by (apply lt_INR; exact Hlt).
    lra.
Qed.

(* 当 i 相等时的衰减情况分解 *)
Lemma decay_i_eq_case (C : nat) (HC : (C >= 2)%nat)
  (seq1 seq2 : nat -> nat)
  (Hg1 : forall i, (seq1 i >= 2)%nat)
  (Hg2 : forall i, (seq2 i >= 2)%nat)
  (Hsp1_2 : forall i, (INR (seq1 (S i)) > INR 2 * INR (seq1 i))%R)
  (Hsp2_2 : forall i, (INR (seq2 (S i)) > INR 2 * INR (seq2 i))%R)
  (i2 j1 j2 : nat) (Hneq_j : j1 <> j2)
  (gamma1 gamma2 : R)
  (Hgamma1_def : gamma1 = sqrt (INR (Nat.min (seq1 i2) (seq2 j1)) / (INR (seq1 i2) * INR (seq2 j1))))
  (Hgamma2_def : gamma2 = sqrt (INR (Nat.min (seq1 i2) (seq2 j2)) / (INR (seq1 i2) * INR (seq2 j2))))
  (N0 : nat)
  (HN0_ge_Nmax : (N0 >= Nat.max (Nat.max (seq1 i2) (seq2 j1)) (Nat.max (seq1 i2) (seq2 j2)))%nat)
  (Hcond_i : INR (seq1 i2) >= INR (Nat.min (seq2 j1) (seq2 j2)))
  : exists (a b1 b2 : nat) (N0' : nat),
    a = seq1 i2 /\ b1 = seq2 j1 /\ b2 = seq2 j2 /\
    N0' = Nat.min N0 (Nat.min a (Nat.min b1 b2)) /\
    (Csum (fun k : nat =>
       (Cof_real (/ gamma1) *c (psi a k *c psi b1 k)) *c
       Cconj (Cof_real (/ gamma2) *c (psi a k *c psi b2 k))) N0
     = Cof_real (/ (INR a * gamma1 * gamma2)) *c
       Csum (fun k : nat => psi b1 k *c Cconj (psi b2 k)) N0') /\
    (0 < / (INR a * gamma1 * gamma2)) /\
    (Csum (fun k : nat => psi b1 k *c Cconj (psi b2 k)) N0' =
     Csum (fun k : nat => psi b1 k *c Cconj (psi b2 k)) (seq2 (Nat.max j1 j2) - 1)).
Proof.
  intros.
  set (a := seq1 i2).
  set (b1 := seq2 j1).
  set (b2 := seq2 j2).
  assert (Ha_ge2 : (a >= 2)%nat) by apply Hg1.
  assert (Hb1_ge2 : (b1 >= 2)%nat) by apply Hg2.
  assert (Hb2_ge2 : (b2 >= 2)%nat) by apply Hg2.
  set (N0' := Nat.min N0 (Nat.min a (Nat.min b1 b2))).
  assert (HN0'_le_N0 : (N0' <= N0)%nat) by (apply Nat.le_min_l).
  assert (Hgamma1_pos : 0 < gamma1).
  { rewrite Hgamma1_def; apply sqrt_lt_R0_c; apply Rdiv_lt_0_compat.
    - apply lt_0_INR; lia.
    - apply Rmult_lt_0_compat; apply lt_0_INR; lia. }
  assert (Hgamma2_pos : 0 < gamma2).
  { rewrite Hgamma2_def; apply sqrt_lt_R0_c; apply Rdiv_lt_0_compat.
    - apply lt_0_INR; lia.
    - apply Rmult_lt_0_compat; apply lt_0_INR; lia. }

  (* 将 R 不等式转为 nat 不等式 *)
  assert (Ha_ge_min_nat : (a >= Nat.min b1 b2)%nat) by (apply INR_ge_nat, Hcond_i).

  pose proof (decay_case_eq_i C HC seq1 seq2 Hg1 Hg2 Hsp1_2 Hsp2_2 i2 j1 j2 Hneq_j
                gamma1 gamma2 Hgamma1_def Hgamma2_def N0 HN0_ge_Nmax Ha_ge_min_nat) as Hsum_eq.
  cbv beta zeta in Hsum_eq.

  assert (Hpos_inv : 0 < / (INR a * gamma1 * gamma2)).
  { apply Rinv_0_lt_compat.
    replace (INR a * gamma1 * gamma2) with (INR a * (gamma1 * gamma2)) by ring.
    apply Rmult_lt_0_compat.
    - apply lt_0_INR; lia.
    - apply Rmult_lt_0_compat; [exact Hgamma1_pos | exact Hgamma2_pos]. }
  set (I := if j1 <? j2 then [j1; j2] else [j2; j1]).
  assert (Hnodup : NoDup I).
  { unfold I; destruct (j1 <? j2); simpl.
    - constructor.
      { simpl; intros [H|H].
        - apply Hneq_j; symmetry; exact H.
        - inversion H. }
      { constructor.
        - simpl; intros H; inversion H.
        - constructor. }
    - constructor.
      { simpl; intros [H|H].
        - apply Hneq_j; exact H.
        - inversion H. }
      { constructor.
        - simpl; intros H; inversion H.
        - constructor. } }
  assert (Hsorted : Sorted Nat.lt I).
  { unfold I; destruct (j1 <? j2) eqn:Hcmp.
    - apply Nat.ltb_lt in Hcmp; repeat constructor; auto.
    - apply Nat.ltb_ge in Hcmp.
      assert (Hlt_nat : (j2 < j1)%nat) by lia.
      repeat constructor; auto. }
  assert (Hlen : length I = 2%nat) by (unfold I; destruct (j1 <? j2); simpl; auto).
  set (maxI := fold_right Nat.max 0%nat I).
  assert (HmaxI_eq : maxI = Nat.max j1 j2).
  { unfold maxI, I; destruct (j1 <? j2); simpl.
    - rewrite Nat.max_0_r; reflexivity.
    - rewrite Nat.max_0_r; apply Nat.max_comm. }
  assert (HmaxI_le : (maxI <= Nat.max j1 j2)%nat) by (rewrite HmaxI_eq; apply le_n).
  assert (Hseq2_lt_S : forall i, (seq2 i < seq2 (S i))%nat).
  { intro i.
    apply INR_lt.
    apply Rlt_trans with (INR 2 * INR (seq2 i)).
    - assert (Hpos : INR (seq2 i) > 0) by (apply lt_0_INR; specialize (Hg2 i); lia).
      replace (INR 2) with 2%R by (simpl; ring).
      nra.
    - exact (Hsp2_2 i). }
  assert (Hseq2_inc : forall x y, (x <= y)%nat -> (seq2 x <= seq2 y)%nat).
  { intros x y Hle.
    induction Hle.
    - apply Nat.le_refl.
    - apply Nat.le_trans with (seq2 m); [apply IHHle | apply Nat.lt_le_incl, Hseq2_lt_S]. }
  assert (Hseq2_strict : forall x y, (x < y)%nat -> (seq2 x < seq2 y)%nat).
  { intros x y Hlt. induction Hlt.
    - apply Hseq2_lt_S.
    - apply Nat.lt_trans with (seq2 m); [exact IHHlt | apply Hseq2_lt_S]. }
  assert (Hb1_le_seq2maxI : (b1 <= seq2 maxI)%nat).
  { apply Hseq2_inc. rewrite HmaxI_eq. apply Nat.le_max_l. }
  assert (Hb2_le_seq2maxI : (b2 <= seq2 maxI)%nat).
  { apply Hseq2_inc. rewrite HmaxI_eq. apply Nat.le_max_r. }
  assert (Htrunc_eq : Csum (fun k => psi b1 k *c Cconj (psi b2 k)) N0' =
                      Csum (fun k => psi b1 k *c Cconj (psi b2 k)) (seq2 maxI - 1)).
  { symmetry; apply Csum_trunc_tail with (M := N0') (N := (seq2 maxI - 1)%nat).
    - assert (HN0'_le_max : (N0' <= seq2 maxI - 1)%nat).
      { unfold N0'.
        apply Nat.le_trans with (Nat.min a (Nat.min b1 b2)).
        - apply Nat.le_min_r.
        - apply Nat.le_trans with (Nat.min b1 b2).
          + apply Nat.le_min_r.
          + assert (Hmin_le_max : (Nat.min b1 b2 <= seq2 maxI - 1)%nat).
            { destruct (Nat.le_ge_cases b1 b2) as [Hle | Hle].
              - rewrite Nat.min_l; [| exact Hle].
                assert (Hb1_lt_b2 : (b1 < b2)%nat).
                { destruct (Nat.lt_trichotomy j1 j2) as [Hlt_j1j2 | [Heq_j1j2 | Hlt_j2j1]].
                  - apply Hseq2_strict; exact Hlt_j1j2.
                  - exfalso; exact (Hneq_j Heq_j1j2).
                  - exfalso; apply (Nat.lt_irrefl b2);
                      apply (Nat.lt_le_trans _ b1 _);
                      [apply Hseq2_strict; exact Hlt_j2j1 | exact Hle]. }
                assert (Hb1_lt_seq2maxI : (b1 < seq2 maxI)%nat).
                { apply Nat.lt_le_trans with b2; [exact Hb1_lt_b2 | exact Hb2_le_seq2maxI]. }
                lia.
              - rewrite Nat.min_r; [| exact Hle].
                assert (Hb2_lt_b1 : (b2 < b1)%nat).
                { destruct (Nat.lt_trichotomy j2 j1) as [Hlt_j2j1 | [Heq_j2j1 | Hlt_j1j2]].
                  - apply Hseq2_strict; exact Hlt_j2j1.
                  - exfalso; apply Hneq_j; symmetry; exact Heq_j2j1.
                  - exfalso; apply (Nat.lt_irrefl b1);
                      apply (Nat.lt_le_trans _ b2 _);
                      [apply Hseq2_strict; exact Hlt_j1j2 | exact Hle]. }
                assert (Hb2_lt_seq2maxI : (b2 < seq2 maxI)%nat).
                { apply Nat.lt_le_trans with b1; [exact Hb2_lt_b1 | exact Hb1_le_seq2maxI]. }
                lia. }
            exact Hmin_le_max. }
      exact HN0'_le_max.
    - intros k [Hk1 Hk2].
      assert (HN0'_ge_min : (N0' >= Nat.min b1 b2)%nat). {
        assert (Ha_ge_min : (a >= Nat.min b1 b2)%nat) by exact Ha_ge_min_nat.
        assert (HN0_ge_min' : (N0 >= Nat.min b1 b2)%nat).
        { apply Nat.le_trans with (Nat.max (Nat.max a b1) (Nat.max a b2)); [ | apply HN0_ge_Nmax].
          apply Nat.le_trans with (Nat.max a b1); [ | apply Nat.le_max_l].
          apply Nat.le_trans with b1; [apply Nat.le_min_l | apply Nat.le_max_r]. }
        unfold N0'. apply Nat.min_glb.
        - exact HN0_ge_min'.
        - apply Nat.min_glb.
          + exact Ha_ge_min.
          + apply Nat.le_refl. }
      assert (Hk_ge_min : (k >= Nat.min b1 b2)%nat) by (apply Nat.le_trans with N0'; [exact HN0'_ge_min | exact Hk1]).
      destruct (Nat.le_ge_cases b1 b2) as [Hle_b | Hge_b].
      - rewrite (Nat.min_l _ _ Hle_b) in Hk_ge_min.
        apply psi_ge_n_zero in Hk_ge_min.
        rewrite Hk_ge_min. rewrite Cmul_0_l. reflexivity.
      - rewrite (Nat.min_r _ _ Hge_b) in Hk_ge_min.
        apply psi_ge_n_zero in Hk_ge_min.
        rewrite Hk_ge_min. rewrite Cconj_0. rewrite Cmul_0_r. reflexivity. }
  exists a, b1, b2, N0'.
  split.
  - unfold a; reflexivity.
  - split.
    + unfold b1; reflexivity.
    + split.
      * unfold b2; reflexivity.
      * split.
        { unfold N0'; reflexivity. }
        split.
        { unfold a, b1, b2, N0'; exact Hsum_eq. }
        split.
        { exact Hpos_inv. }
        rewrite HmaxI_eq in Htrunc_eq; exact Htrunc_eq.
Qed.

(* 序列无重复元素 *)
Lemma seq_NoDup' (start len : nat) : NoDup (seq start len).
Proof.
  apply seq_NoDup.
Qed.

(* 序列无重复元素 *)
Lemma seq_NoDup (start len : nat) : NoDup (seq start len).
Proof.
  revert start; induction len as [|len IH]; simpl; intros start.
  - constructor.
  - constructor; [| apply IH].
    intros Hx; apply in_seq in Hx; lia.
Qed.

(* 序列首个元素小于后续元素 *)
Lemma HdRel_seq (start len : nat) : HdRel Nat.lt start (seq (S start) len).
Proof.
  induction len; simpl.
  - constructor.
  - constructor; lia.
Qed.

(* 序列为升序排列 *)
Lemma seq_Sorted (start len : nat) : Sorted Nat.lt (seq start len).
Proof.
  revert start; induction len as [|len IH]; intros start; simpl.
  - constructor.
  - constructor.
    + apply IH.
    + apply HdRel_seq.
Qed.

(* 序列长度 *)
Lemma seq_length (start len : nat) : length (seq start len) = len.
Proof. apply List.length_seq. Qed.

(* 序列最大值等于起始值加长度减一 *)
Lemma seq_fold_max (start len : nat) :
  fold_right Nat.max 0%nat (seq start (S len)) = (start + len)%nat.
Proof.
  revert start.
  induction len as [|len IH]; intros start.
  - simpl. rewrite Nat.add_0_r. apply Nat.max_0_r.
  - replace (seq start (S (S len))) with (start :: seq (S start) (S len))
      by (simpl; reflexivity).
    assert (Hcons : fold_right Nat.max 0%nat (start :: seq (S start) (S len))
                  = Nat.max start (fold_right Nat.max 0%nat (seq (S start) (S len)))).
    { reflexivity. }
    rewrite Hcons.
    rewrite IH with (start := S start).
    rewrite (Nat.add_succ_comm start len).
    apply Nat.max_r.
    apply Nat.le_add_r.
Qed.

(* 列表映射的 nth 性质 *)
Lemma H_nth_map (A B : Type) (f : A -> B) (l : list A) (default_val : B) (d0 : A) (j : nat) :
  (j < length l)%nat -> nth j (map f l) default_val = f (nth j l d0).
Proof.
  revert j; induction l as [| h t IHl]; intros j Hj; simpl in Hj.
  - exfalso; lia.
  - destruct j as [| j']; simpl.
    + reflexivity.
    + apply IHl; lia.
Qed.

(* 测试映射取首元素 *)

(* 任意距离下的通用衰减界（C=2 稀疏序列） *)
Lemma decay_bound_general_dist (seq : nat -> nat) (Hg : forall i, (seq i >= 2)%nat)
  (Hsp : forall i, INR (seq (S i)) > INR 2 * INR (seq i))
  (j1 j2 : nat) (Hneq : j1 <> j2) :
  let d := Z.abs_nat (Z.of_nat j1 - Z.of_nat j2) in
  Cnorm (Csum (fun k => psi (seq j1) k *c Cconj (psi (seq j2) k)) (seq (Nat.max j1 j2) - 1))
  <= d_factor (sqrt (INR 2)) j1 j2.
Proof.
  intros d.
  set (C := 2%nat).
  assert (HC_ge2 : (C >= 2)%nat) by (unfold C; lia).
  assert (Hsp_C : forall i, INR (seq (S i)) > INR C * INR (seq i)).
  { intro i; unfold C; apply Hsp. }
  set (jmin := Nat.min j1 j2).
  set (jmax := Nat.max j1 j2).
  set (d' := (jmax - jmin)%nat).
  assert (Hd_eq : d = d').
  { unfold d, d', jmin, jmax.
    destruct (Nat.lt_total j1 j2) as [Hlt | [Heq | Hgt]].
    - rewrite (Nat.max_r _ _ (Nat.lt_le_incl _ _ Hlt)),
              (Nat.min_l _ _ (Nat.lt_le_incl _ _ Hlt)).
      zify; lia.
    - subst; zify; lia.
    - rewrite (Nat.max_l _ _ (Nat.lt_le_incl _ _ Hgt)),
              (Nat.min_r _ _ (Nat.lt_le_incl _ _ Hgt)).
      zify; lia. }
  subst d; fold d'.
  set (I := List.seq jmin (S d')).
  assert (Hnodup_I : NoDup I) by apply seq_NoDup.
  assert (Hsorted_I : Sorted Nat.lt I) by apply seq_Sorted.
  assert (Hlen_I : length I = S d') by apply seq_length.
  assert (H0_lt_len : (0 < length I)%nat) by (rewrite Hlen_I; lia).
  assert (Hd'_lt_len : (d' < length I)%nat) by (rewrite Hlen_I; lia).
  assert (H0_neq_d' : 0%nat <> d').
  { intro Heq.
    assert (j1 = j2) by (unfold d', jmax, jmin in Heq; lia).
    exact (Hneq H). }
  (* [v3.51 Fix] generalize+cbv beta 展开 let；用 compute 代替 simpl；用本地引理 *)
  pose proof (decay_bound seq I C HC_ge2 Hg Hsp_C Hnodup_I Hsorted_I
                           0 d' H0_neq_d' H0_lt_len Hd'_lt_len) as Htmp.
  generalize Htmp; clear Htmp; cbv beta zeta; intro Hdec.
  (* Hdec 现在有干净的类型：Cnorm (...) <= ...，无 let 绑定 *)
  assert (Hmax_fold : fold_right Nat.max 0%nat I = jmax).
  { unfold I; rewrite seq_fold_max; unfold d'; simpl; lia. }
  rewrite Hmax_fold in Hdec.
  assert (Hnth0 : nth 0 (map seq I) 0%nat = seq jmin).
  { unfold I; simpl; reflexivity. }
  assert (Hnthd' : nth d' (map seq I) 0%nat = seq jmax).
  { rewrite (H_nth_map nat nat seq I 0%nat 0%nat d' Hd'_lt_len).
    f_equal.
    unfold I.
    rewrite (nth_seq_general jmin (S d') d') by lia.
    unfold jmax, jmin; lia. }
  rewrite Hnth0, Hnthd' in Hdec.
  unfold C in Hdec.
  (* simpl 前先替换 Z.abs_nat，因为 simpl 会改变 Z 表达式的形式 *)
  replace (Z.abs_nat (Z.of_nat 0 - Z.of_nat d')) with d' in Hdec by lia.
  simpl in Hdec.
  clear Hmax_fold Hnth0 Hnthd' I Hnodup_I Hsorted_I Hlen_I H0_lt_len Hd'_lt_len H0_neq_d'.
  destruct (Nat.lt_total j1 j2) as [Hlt | [Heq | Hgt]].
  - unfold jmin, jmax in *.
    rewrite (Nat.min_l j1 j2 (Nat.lt_le_incl _ _ Hlt)),
           (Nat.max_r j1 j2 (Nat.lt_le_incl _ _ Hlt)) in *.
    simpl in *.
    rewrite <- Hd_eq in Hdec.
    rewrite Hdec.
    unfold d_factor.
    destruct (Nat.eqb_spec j1 j2) as [Heq' | Hneq'].
    { exfalso; exact (Hneq Heq'). }
    reflexivity.
  - exfalso; exact (Hneq Heq).
  - unfold jmin, jmax in *.
    rewrite (Nat.min_r j1 j2 (Nat.lt_le_incl _ _ Hgt)),
           (Nat.max_l j1 j2 (Nat.lt_le_incl _ _ Hgt)) in *.
    simpl in *.
    rewrite <- Hd_eq in Hdec.
    rewrite Cnorm_Csum_swap in Hdec.
    rewrite Hdec.
    unfold d_factor.
    destruct (Nat.eqb_spec j1 j2) as [Heq' | Hneq'].
    { exfalso; exact (Hneq Heq'). }
    reflexivity.
Qed.

(* case_i_eq 的证明 *)
Lemma case_i_eq :
  forall (C : nat) (HC : (C >= 2)%nat)
    (seq1 seq2 : nat -> nat)
    (Hg1 : forall i, (seq1 i >= 2)%nat)
    (Hg2 : forall i, (seq2 i >= 2)%nat)
    (Hsp1_2 : forall i, (INR (seq1 (S i)) > INR 2 * INR (seq1 i))%R)
    (Hsp2_2 : forall i, (INR (seq2 (S i)) > INR 2 * INR (seq2 i))%R)
    (i2 j1 j2 : nat)
    (Hneq_j : j1 <> j2)
    (gamma1 gamma2 : R)
    (Hgamma1_def : gamma1 = sqrt (INR (Nat.min (seq1 i2) (seq2 j1)) / (INR (seq1 i2) * INR (seq2 j1))))
    (Hgamma2_def : gamma2 = sqrt (INR (Nat.min (seq1 i2) (seq2 j2)) / (INR (seq1 i2) * INR (seq2 j2))))
    (N0 : nat)
    (HN0_ge_max : (N0 >= Nat.max (Nat.max (seq1 i2) (seq2 j1)) (Nat.max (seq1 i2) (seq2 j2)))%nat)
    (Ha_ge_max : (seq1 i2 >= Nat.max (seq2 j1) (seq2 j2))%nat)
    (H_bridge34 : d_factor (sqrt (INR 2)) j1 j2 <= ((INR C)^3 / 8) * d_factor (sqrt (INR C)) j1 j2),
  Cnorm (Csum (fun k : nat =>
    (Cof_real (/ gamma1) *c (psi (seq1 i2) k *c psi (seq2 j1) k)) *c
    Cconj (Cof_real (/ gamma2) *c (psi (seq1 i2) k *c psi (seq2 j2) k))) N0)
  <= (Rmax 8 ((INR C) ^ 3) / 4) * d_factor (sqrt (INR C)) j1 j2.
Proof.
  intros.
  set (a := seq1 i2) in *.
  assert (Ha_ge_max' : (a >= Nat.max (seq2 j1) (seq2 j2))%nat) by exact Ha_ge_max.

  assert (sqrt_div_1_sqrt : forall x : R, x > 0 -> sqrt (1 / x) = 1 / sqrt x). {
    intros x Hx; rewrite sqrt_div; [| lra | lra]; rewrite sqrt_1; reflexivity. }
  assert (Cnorm_Cof_real_one : Cnorm (Cof_real (1 : R)) = 1%R). {
    unfold Cof_real, Cnorm, Cnorm_sq, Rsqr; simpl; replace (1*1+0*0) with 1 by ring; exact sqrt_1. }

  assert (Ha_pos : 0 < INR (seq1 i2)). {
    apply lt_0_INR; pose proof (Hg1 i2); lia. }
  assert (Ha_neq0 : INR (seq1 i2) <> 0) by lra.
  assert (Hbj1_pos : 0 < INR (seq2 j1)). {
    apply lt_0_INR; pose proof (Hg2 j1); lia. }
  assert (Hbj1_neq0 : INR (seq2 j1) <> 0) by lra.
  assert (Hbj2_pos : 0 < INR (seq2 j2)). {
    apply lt_0_INR; pose proof (Hg2 j2); lia. }
  assert (Hbj2_neq0 : INR (seq2 j2) <> 0) by lra.

  assert (Hgamma1_eq : gamma1 = 1 / sqrt (INR a)). {
    rewrite Hgamma1_def.
    unfold a.
    assert (Ha_ge_j1 : (seq2 j1 <= seq1 i2)%nat). {
      apply (Nat.le_trans _ (Nat.max (seq2 j1) (seq2 j2)));
      [apply Nat.le_max_l | exact Ha_ge_max'].
    }
    rewrite (Nat.min_r (seq1 i2) (seq2 j1) Ha_ge_j1).
    assert (Htemp : INR (seq2 j1) / (INR (seq1 i2) * INR (seq2 j1)) = 1 / INR (seq1 i2)). {
      field; split; [exact Ha_neq0 | exact Hbj1_neq0].
    }
    rewrite Htemp.
    apply sqrt_div_1_sqrt; exact Ha_pos.
  }

  assert (Hgamma2_eq : gamma2 = 1 / sqrt (INR a)). {
    rewrite Hgamma2_def.
    unfold a.
    assert (Ha_ge_j2 : (seq2 j2 <= seq1 i2)%nat). {
      apply (Nat.le_trans _ (Nat.max (seq2 j1) (seq2 j2)));
      [apply Nat.le_max_r | exact Ha_ge_max'].
    }
    rewrite (Nat.min_r (seq1 i2) (seq2 j2) Ha_ge_j2).
    assert (Htemp : INR (seq2 j2) / (INR (seq1 i2) * INR (seq2 j2)) = 1 / INR (seq1 i2)). {
      field; split; [exact Ha_neq0 | exact Hbj2_neq0].
    }
    rewrite Htemp.
    apply sqrt_div_1_sqrt; exact Ha_pos.
  }

  assert (H_max_ge_min : (Nat.max (seq2 j1) (seq2 j2) >= Nat.min (seq2 j1) (seq2 j2))%nat). {
    destruct (Nat.min_spec (seq2 j1) (seq2 j2)) as [[Hle Hmin] | [Hle Hmin]];
    rewrite Hmin; [apply Nat.le_max_l | apply Nat.le_max_r].
  }
  assert (Ha_ge_min : (seq1 i2 >= Nat.min (seq2 j1) (seq2 j2))%nat). {
    apply (Nat.le_trans _ (Nat.max (seq2 j1) (seq2 j2))%nat);
    [apply H_max_ge_min | apply Ha_ge_max'].
  }

  unfold a in Hgamma1_def, Hgamma2_def, HN0_ge_max, Ha_ge_min, Ha_ge_max'.
  pose proof (decay_case_eq_i C HC seq1 seq2 Hg1 Hg2 Hsp1_2 Hsp2_2 i2 j1 j2 Hneq_j
                gamma1 gamma2 Hgamma1_def Hgamma2_def N0 HN0_ge_max Ha_ge_min) as Hsum_eq.
  fold a in Hgamma1_def, Hgamma2_def, HN0_ge_max, Ha_ge_min, Ha_ge_max'.
  cbv beta iota zeta in Hsum_eq.
  unfold a; rewrite Hsum_eq; fold a.

  rewrite Cnorm_mult.
  assert (Cnorm_Cof_real_pos : forall r, 0 <= r -> Cnorm (Cof_real r) = r). {
    intros r Hr; unfold Cof_real, Cnorm, Cnorm_sq, Rsqr; simpl.
    rewrite Rmult_0_r, Rplus_0_r.
    apply sqrt_Rsqr; exact Hr.
  }
  assert (Ha_pos' : 0 < INR a). {
    unfold a; exact Ha_pos.
  }
  assert (Hgamma1_pos : 0 < gamma1). {
    rewrite Hgamma1_eq.
    apply Rdiv_lt_0_compat; [lra | apply sqrt_lt_R0_c; exact Ha_pos'].
  }
  assert (Hgamma2_pos : 0 < gamma2). {
    rewrite Hgamma2_eq.
    apply Rdiv_lt_0_compat; [lra | apply sqrt_lt_R0_c; exact Ha_pos'].
  }
  assert (Hcoeff_pos : 0 < / (INR a * gamma1 * gamma2)). {
    apply Rinv_0_lt_compat.
    apply Rmult_lt_0_compat.
    - apply Rmult_lt_0_compat; [exact Ha_pos' | exact Hgamma1_pos].
    - exact Hgamma2_pos.
  }
  rewrite (Cnorm_Cof_real_pos _ (Rlt_le _ _ Hcoeff_pos)).
  rewrite Hgamma1_eq, Hgamma2_eq.

  assert (Htemp : INR a * (1 / sqrt (INR a)) * (1 / sqrt (INR a)) = 1). {
    replace (INR a * (1 / sqrt (INR a)) * (1 / sqrt (INR a)))
      with (INR a / ((sqrt (INR a)) * (sqrt (INR a)))).
    - replace ((sqrt (INR a)) * (sqrt (INR a))) with ((sqrt (INR a)) ^ 2) by ring.
      rewrite <- Rsqr_pow2.
      rewrite Rsqr_sqrt; [| lra].
      field; lra.
    - field; repeat split;
        apply Rgt_not_eq; apply sqrt_lt_R0_c; lra.
  }
  rewrite Htemp.
  rewrite Rinv_1, Rmult_1_l.

  assert (Hseq2_lt : forall i j, (i < j)%nat -> (seq2 i < seq2 j)%nat). {
    intros i j Hij; induction Hij.
    - apply INR_lt.
      eapply Rlt_trans; [| apply Hsp2_2].
      replace (INR 2) with 2%R by (simpl; ring).
      assert (Hpos : 0 < INR (seq2 i)). {
        apply lt_0_INR; pose proof (Hg2 i); lia.
      }
      lra.
    - apply Nat.lt_trans with (seq2 m); [apply IHHij |].
      apply INR_lt.
      eapply Rlt_trans; [| apply Hsp2_2].
      replace (INR 2) with 2%R by (simpl; ring).
      assert (Hpos : 0 < INR (seq2 m)). {
        apply lt_0_INR; pose proof (Hg2 m); lia.
      }
      lra.
  }

  set (N0' := Nat.min N0 (Nat.min a (Nat.min (seq2 j1) (seq2 j2)))).
  assert (Htrunc_inner : Csum (fun k => psi (seq2 j1) k *c Cconj (psi (seq2 j2) k)) N0' =
                         Csum (fun k => psi (seq2 j1) k *c Cconj (psi (seq2 j2) k)) (seq2 (Nat.max j1 j2) - 1)). {
    symmetry; apply Csum_trunc_tail.
    - unfold N0'.
      apply (Nat.le_trans _ (Nat.min (seq2 j1) (seq2 j2))).
      + apply (Nat.le_trans _ (Nat.min a (Nat.min (seq2 j1) (seq2 j2)))).
        * apply Nat.le_min_r.
        * apply Nat.le_min_r.
      + destruct (Nat.lt_total j1 j2) as [Hlt|[Heq|Hgt]].
        * pose proof (Hseq2_lt _ _ Hlt) as Hlt_seq.
          assert (Hmax : Nat.max j1 j2 = j2) by lia.
          rewrite Hmax.
          assert (Hmin : Nat.min (seq2 j1) (seq2 j2) = seq2 j1) by (apply Nat.min_l; lia).
          rewrite Hmin.
          pose proof (Hg2 j2) as Hge2.
          lia.
        * exfalso; apply Hneq_j; exact Heq.
        * pose proof (Hseq2_lt _ _ Hgt) as Hlt_seq.
          assert (Hmax : Nat.max j1 j2 = j1) by lia.
          rewrite Hmax.
          assert (Hmin : Nat.min (seq2 j1) (seq2 j2) = seq2 j2) by (apply Nat.min_r; lia).
          rewrite Hmin.
          pose proof (Hg2 j1) as Hge2.
          lia.
    - intros k [Hk1 Hk2].
      assert (Hmin_k : (Nat.min (seq2 j1) (seq2 j2) <= k)%nat) by
        (clear -Ha_ge_min HN0_ge_max Hk1; unfold N0' in Hk1; lia).
      destruct (Nat.min_spec (seq2 j1) (seq2 j2)) as [[Hle Hmin] | [Hle Hmin]].
      + rewrite Hmin in Hmin_k.
        rewrite (psi_ge_n_zero (seq2 j1) k Hmin_k).
        rewrite Cmul_0_l; reflexivity.
      + rewrite Hmin in Hmin_k.
        rewrite (psi_ge_n_zero (seq2 j2) k Hmin_k).
        rewrite Cconj_0.
        rewrite Cmul_0_r; reflexivity.
  }
  rewrite Htrunc_inner.

  apply Rle_trans with (d_factor (sqrt (INR 2)) j1 j2).
  - apply decay_bound_general_dist; auto.
  - apply Rle_trans with (((INR C)^3 / 8) * d_factor (sqrt (INR C)) j1 j2).
    { exact H_bridge34. }
    apply Rmult_le_compat_r.
    { unfold d_factor.
      destruct (j1 =? j2) eqn:Heq.
      - lra.
      - apply Rlt_le; apply Rdiv_lt_0_compat.
        + lra.
        + apply pow_lt; apply sqrt_lt_R0_c; apply lt_0_INR; lia.
    }
    assert (HC_R : 2 <= INR C).
    { change 2 with (INR 2); apply le_INR; exact HC. }
    assert (Hcube_ge8 : (INR C)^3 >= 8). {
      assert (HC_pos : 0 <= INR C) by (apply pos_INR; lia).
      nra.
    }
    assert (H8_le_cube : 8 <= (INR C)^3) by (apply Rge_le; exact Hcube_ge8).
    assert (HRmax : Rmax 8 ((INR C)^3) = (INR C)^3). {
      unfold Rmax; destruct (Rle_dec 8 ((INR C)^3)) as [Hle | Hnle].
      - reflexivity.
      - exfalso; apply Hnle; exact H8_le_cube.
    }
    rewrite HRmax.
    lra.
Qed.

(* case_j_eq 的证明 *)
Lemma case_j_eq :
  forall (C : nat) (HC : (C >= 2)%nat)
    (seq1 seq2 : nat -> nat)
    (Hg1 : forall i, (seq1 i >= 2)%nat)
    (Hg2 : forall i, (seq2 i >= 2)%nat)
    (Hsp1_2 : forall i, (INR (seq1 (S i)) > INR 2 * INR (seq1 i))%R)
    (Hsp2_2 : forall i, (INR (seq2 (S i)) > INR 2 * INR (seq2 i))%R)
    (i1 i2 j2 : nat)
    (Hneq_i : i1 <> i2)
    (gamma1 gamma2 : R)
    (Hgamma1_def : gamma1 = sqrt (INR (Nat.min (seq1 i1) (seq2 j2)) / (INR (seq1 i1) * INR (seq2 j2))))
    (Hgamma2_def : gamma2 = sqrt (INR (Nat.min (seq1 i2) (seq2 j2)) / (INR (seq1 i2) * INR (seq2 j2))))
    (N0 : nat)
    (HN0_ge_max : (N0 >= Nat.max (Nat.max (seq1 i1) (seq2 j2)) (Nat.max (seq1 i2) (seq2 j2)))%nat)
    (Hb_ge_max : (seq2 j2 >= Nat.max (seq1 i1) (seq1 i2))%nat)
    (H_bridge12 : d_factor (sqrt (INR 2)) i1 i2 <= ((INR C)^3 / 8) * d_factor (sqrt (INR C)) i1 i2),
  Cnorm (Csum (fun k : nat =>
    (Cof_real (/ gamma1) *c (psi (seq1 i1) k *c psi (seq2 j2) k)) *c
    Cconj (Cof_real (/ gamma2) *c (psi (seq1 i2) k *c psi (seq2 j2) k))) N0)
  <= (Rmax 8 ((INR C) ^ 3) / 4) * d_factor (sqrt (INR C)) i1 i2.
Proof.
  intros.
  assert (Hgamma1_def' : gamma1 = sqrt (INR (Nat.min (seq2 j2) (seq1 i1)) / (INR (seq2 j2) * INR (seq1 i1)))).
  { rewrite Hgamma1_def, Nat.min_comm, Rmult_comm; reflexivity. }
  assert (Hgamma2_def' : gamma2 = sqrt (INR (Nat.min (seq2 j2) (seq1 i2)) / (INR (seq2 j2) * INR (seq1 i2)))).
  { rewrite Hgamma2_def, Nat.min_comm, Rmult_comm; reflexivity. }
  assert (HN0_ge_max' : (N0 >= Nat.max (Nat.max (seq2 j2) (seq1 i1)) (Nat.max (seq2 j2) (seq1 i2)))%nat).
  { lia. }
  pose proof (case_i_eq C HC seq2 seq1 Hg2 Hg1 Hsp2_2 Hsp1_2
                        j2 i1 i2 Hneq_i
                        gamma1 gamma2 Hgamma1_def' Hgamma2_def'
                        N0 HN0_ge_max' Hb_ge_max H_bridge12) as Htmp.
  assert (Csum_eq : forall n (f g : nat -> Complex), (forall k, f k = g k) -> Csum f n = Csum g n).
  { induction n; intros; simpl; auto. f_equal; auto. }
  assert (Heq_sum : Csum (fun k => (Cof_real (/gamma1) *c (psi (seq2 j2) k *c psi (seq1 i1) k)) *c
                                   Cconj (Cof_real (/gamma2) *c (psi (seq2 j2) k *c psi (seq1 i2) k))) N0
                  = Csum (fun k => (Cof_real (/gamma1) *c (psi (seq1 i1) k *c psi (seq2 j2) k)) *c
                                   Cconj (Cof_real (/gamma2) *c (psi (seq1 i2) k *c psi (seq2 j2) k))) N0).
  { apply Csum_eq; intro k.
    f_equal.
    rewrite (Cmul_comm (psi (seq2 j2) k) (psi (seq1 i1) k)).
    f_equal.
    apply f_equal.
    rewrite (Cmul_comm (psi (seq2 j2) k) (psi (seq1 i2) k)).
    reflexivity. }
  rewrite <- Heq_sum; exact Htmp.
Qed.

(* 定理：平坦化的 phi 特征函数衰减界 *)
Theorem phi_flat_decay_general :
  forall (C : nat) (HC : (C >= 2)%nat)
    (seq1 seq2 : nat -> nat)
    (Hsparse1 : forall i, (INR (seq1 (S i)) > INR C * INR (seq1 i))%R)
    (Hsparse2 : forall i, (INR (seq2 (S i)) > INR C * INR (seq2 i))%R)
    (Hge2_1 : forall i, (seq1 i >= 2)%nat) (Hge2_2 : forall i, (seq2 i >= 2)%nat)
    (I1 I2 : list nat)
    (Hdup1 : NoDup I1) (Hsorted1 : Sorted Nat.lt I1)
    (Hdup2 : NoDup I2) (Hsorted2 : Sorted Nat.lt I2)
    (n1 n2 : nat) (Hn1 : n1 = length I1) (Hn2 : n2 = length I2)
    (HI1 : I1 = seq 0 n1) (HI2 : I2 = seq 0 n2)
    (a b : nat -> nat)
    (Ha : a = fun i => nth i (map seq1 I1) 0%nat)
    (Hb : b = fun j => nth j (map seq2 I2) 0%nat)
    (gamma : nat -> nat -> R)
    (Hgamma : gamma = fun i j => sqrt (INR (Nat.min (a i) (b j)) / (INR (a i) * INR (b j))))
    (phi2D_norm : nat -> nat -> nat -> Complex)
    (Hphi2D_norm : phi2D_norm = fun i j k => Cof_real (/ gamma i j) *c (psi (a i) k *c psi (b j) k))
    (maxIdx1 maxIdx2 : nat)
    (HmaxIdx1 : maxIdx1 = fold_right Nat.max 0%nat I1)
    (HmaxIdx2 : maxIdx2 = fold_right Nat.max 0%nat I2)
    (M : nat) (HM : M = S (max (seq1 maxIdx1) (seq2 maxIdx2)))
    (r : R) (Hr : r = sqrt (INR C))
    (phi_flat : nat -> nat -> Complex)
    (Hphi_flat : phi_flat = fun idx k => phi2D_norm ((idx / n2)%nat) ((idx mod n2)%nat) k)
    (delta_pair : nat -> nat -> R)
    (Hdelta_pair : delta_pair = fun idx1 idx2 =>
        d_factor r ((idx1 / n2)%nat) ((idx2 / n2)%nat) *
        d_factor r ((idx1 mod n2)%nat) ((idx2 mod n2)%nat))
    (idx1 idx2 : nat) (Hneq : idx1 <> idx2)
    (Hlt1 : (idx1 < n1 * n2)%nat) (Hlt2 : (idx2 < n1 * n2)%nat)
    (H_index_bound : (Z.abs_nat (Z.of_nat (idx1 / n2) - Z.of_nat (idx2 / n2)) +
                      Z.abs_nat (Z.of_nat (idx1 mod n2) - Z.of_nat (idx2 mod n2)) <= 6)%nat)
    (H_dom : ((idx1 / n2)%nat = (idx2 / n2)%nat ->
              (seq1 ((idx1 / n2)%nat) >= Nat.max (seq2 ((idx1 mod n2)%nat)) (seq2 ((idx2 mod n2)%nat)))%nat) /\
             ((idx1 mod n2)%nat = (idx2 mod n2)%nat ->
              (seq2 ((idx1 mod n2)%nat) >= Nat.max (seq1 ((idx1 / n2)%nat)) (seq1 ((idx2 / n2)%nat)))%nat)),
  Cnorm (Csum (fun k => phi_flat idx1 k *c Cconj (phi_flat idx2 k)) (Nat.pred M))
  <= (Rmax 8 ((INR C) ^ 3) / 4) * delta_pair idx1 idx2.
Proof.
  intros; subst a b gamma phi2D_norm phi_flat delta_pair M r; simpl.
  rename Hsparse1 into Hsp1, Hsparse2 into Hsp2.
  rename Hge2_1 into Hg1, Hge2_2 into Hg2.
  rename Hn1 into Hlen1, Hn2 into Hlen2.
  rename HI1 into HI1', HI2 into HI2'.
  rename HmaxIdx1 into Hmax1, HmaxIdx2 into Hmax2.
  rename Hlt1 into Hlt1', Hlt2 into Hlt2'.
  rename Hneq into Hneq'.

  assert (sqrt_div_1_sqrt : forall x : R, x > 0 -> sqrt (1 / x) = 1 / sqrt x). {
    intros x Hx.
    rewrite sqrt_div; [| lra | lra].
    rewrite sqrt_1; reflexivity.
  }
  assert (Cnorm_Cof_real_one : Cnorm (Cof_real (1 : R)) = 1%R). {
    unfold Cof_real, Cnorm, Cnorm_sq, Rsqr; simpl.
    replace (1 * 1 + 0 * 0) with 1 by ring.
    exact sqrt_1.
  }

  assert (Hsp1_2 : forall i, (INR (seq1 (S i)) > INR 2 * INR (seq1 i))%R). {
    intros i; specialize (Hsp1 i).
    assert (HC_ge_2_INR : INR 2 <= INR C) by (apply le_INR; exact HC).
    eapply Rle_lt_trans; [| exact Hsp1].
    apply Rmult_le_compat_r; [apply pos_INR; specialize (Hg1 i); lia | exact HC_ge_2_INR].
  }
  assert (Hsp2_2 : forall i, (INR (seq2 (S i)) > INR 2 * INR (seq2 i))%R). {
    intros i; specialize (Hsp2 i).
    assert (HC_ge_2_INR : INR 2 <= INR C) by (apply le_INR; exact HC).
    eapply Rle_lt_trans; [| exact Hsp2].
    apply Rmult_le_compat_r; [apply pos_INR; specialize (Hg2 i); lia | exact HC_ge_2_INR].
  }

  assert (n1_pos : (n1 > 0)%nat) by (destruct n1; [simpl in Hlt1'; lia | lia]).
  assert (n2_pos : (n2 > 0)%nat) by (destruct n2; [simpl in Hlt1'; lia | lia]).
  set (i1 := Nat.div idx1 n2).
  set (j1 := Nat.modulo idx1 n2).
  set (i2 := Nat.div idx2 n2).
  set (j2 := Nat.modulo idx2 n2).
  assert (Hi1 : (i1 < n1)%nat) by (apply Div0.div_lt_upper_bound; lia).
  assert (Hj1 : (j1 < n2)%nat) by (apply Nat.mod_upper_bound; lia).
  assert (Hi2 : (i2 < n1)%nat) by (apply Div0.div_lt_upper_bound; lia).
  assert (Hj2 : (j2 < n2)%nat) by (apply Nat.mod_upper_bound; lia).

  assert (Hai1_len_I : (i1 < length I1)%nat) by (rewrite <- Hlen1; exact Hi1).
  assert (Hai1_len_seq : (i1 < length (seq 0 n1))%nat) by (rewrite <- HI1'; exact Hai1_len_I).
  assert (Hai2_len_I : (i2 < length I1)%nat) by (rewrite <- Hlen1; exact Hi2).
  assert (Hai2_len_seq : (i2 < length (seq 0 n1))%nat) by (rewrite <- HI1'; exact Hai2_len_I).
  assert (Hbj1_len_I : (j1 < length I2)%nat) by (rewrite <- Hlen2; exact Hj1).
  assert (Hbj1_len_seq : (j1 < length (seq 0 n2))%nat) by (rewrite <- HI2'; exact Hbj1_len_I).
  assert (Hbj2_len_I : (j2 < length I2)%nat) by (rewrite <- Hlen2; exact Hj2).
  assert (Hbj2_len_seq : (j2 < length (seq 0 n2))%nat) by (rewrite <- HI2'; exact Hbj2_len_I).

  assert (Ha_i1 : nth i1 (map seq1 I1) 0%nat = seq1 i1). {
    rewrite HI1', (H_nth_map nat nat seq1 (seq 0 n1) 0%nat 0%nat i1 Hai1_len_seq).
    rewrite nth_seq_general; [reflexivity | exact Hi1].
  }
  assert (Ha_i2 : nth i2 (map seq1 I1) 0%nat = seq1 i2). {
    rewrite HI1', (H_nth_map nat nat seq1 (seq 0 n1) 0%nat 0%nat i2 Hai2_len_seq).
    rewrite nth_seq_general; [reflexivity | exact Hi2].
  }
  assert (Hb_j1 : nth j1 (map seq2 I2) 0%nat = seq2 j1). {
    rewrite HI2', (H_nth_map nat nat seq2 (seq 0 n2) 0%nat 0%nat j1 Hbj1_len_seq).
    rewrite nth_seq_general; [reflexivity | exact Hj1].
  }
  assert (Hb_j2 : nth j2 (map seq2 I2) 0%nat = seq2 j2). {
    rewrite HI2', (H_nth_map nat nat seq2 (seq 0 n2) 0%nat 0%nat j2 Hbj2_len_seq).
    rewrite nth_seq_general; [reflexivity | exact Hj2].
  }
  rewrite !Ha_i1, !Ha_i2, !Hb_j1, !Hb_j2.

  assert (seq1_mono : forall x y, (x <= y)%nat -> (seq1 x <= seq1 y)%nat). {
    intros x y Hle; destruct (Nat.eq_dec x y); [subst; apply Nat.le_refl|].
    apply Nat.lt_le_incl; eapply seq_strict_growth_lt; eauto; lia.
  }
  assert (seq2_mono : forall x y, (x <= y)%nat -> (seq2 x <= seq2 y)%nat). {
    intros x y Hle; destruct (Nat.eq_dec x y); [subst; apply Nat.le_refl|].
    apply Nat.lt_le_incl; eapply seq_strict_growth_lt; eauto; lia.
  }

  assert (Hmax1_bound : forall i, (i < n1)%nat -> (seq1 i <= seq1 maxIdx1)%nat). {
    intros i Hi; apply seq1_mono; rewrite Hmax1, HI1'.
    apply (Nat.le_trans _ (n1-1)%nat _); [lia|].
    apply fold_right_max_ge; apply in_seq; lia.
  }
  assert (Hmax2_bound : forall j, (j < n2)%nat -> (seq2 j <= seq2 maxIdx2)%nat). {
    intros j Hj; apply seq2_mono; rewrite Hmax2, HI2'.
    apply (Nat.le_trans _ (n2-1)%nat _); [lia|].
    apply fold_right_max_ge; apply in_seq; lia.
  }

  set (Nmax := max (seq1 maxIdx1) (seq2 maxIdx2)).
  set (N0 := max (max (seq1 i1) (seq2 j1)) (max (seq1 i2) (seq2 j2))).
  assert (HN0_le_Nmax : (N0 <= Nmax)%nat). {
    unfold N0; repeat apply Nat.max_lub;
    [apply (Nat.le_trans _ (seq1 maxIdx1)); [apply Hmax1_bound; exact Hi1 | apply Nat.le_max_l]
    |apply (Nat.le_trans _ (seq2 maxIdx2)); [apply Hmax2_bound; exact Hj1 | apply Nat.le_max_r]
    |apply (Nat.le_trans _ (seq1 maxIdx1)); [apply Hmax1_bound; exact Hi2 | apply Nat.le_max_l]
    |apply (Nat.le_trans _ (seq2 maxIdx2)); [apply Hmax2_bound; exact Hj2 | apply Nat.le_max_r]].
  }
  assert (HN0_ge_max : (N0 >= Nat.max (Nat.max (seq1 i1) (seq2 j1)) (Nat.max (seq1 i2) (seq2 j2)))%nat). {
    unfold N0; apply Nat.le_refl.
  }
  replace (Nat.pred (S Nmax)) with Nmax by (simpl; reflexivity).

  set (F := fun k : nat =>
    (Cof_real (/ sqrt (INR (Nat.min (seq1 i1) (seq2 j1)) / (INR (seq1 i1) * INR (seq2 j1)))) *c
     (psi (seq1 i1) k *c psi (seq2 j1) k)) *c
    Cconj (Cof_real (/ sqrt (INR (Nat.min (seq1 i2) (seq2 j2)) / (INR (seq1 i2) * INR (seq2 j2)))) *c
           (psi (seq1 i2) k *c psi (seq2 j2) k))).

  assert (Cmul_0_l : forall z, C0 *c z = C0) by (intros; unfold Cmul, C0; apply Complex_eq; simpl; ring).
  assert (Cmul_0_r : forall z, z *c C0 = C0) by (intros; unfold Cmul, C0; apply Complex_eq; simpl; ring).
  assert (Cconj_0 : Cconj C0 = C0) by (apply Complex_eq; simpl; ring).

  assert (Htrunc_eq : Csum F Nmax = Csum F N0). {
    apply Csum_trunc_tail; [exact HN0_le_Nmax|].
    intros k [Hk1 Hk2]; unfold F.
    assert (Hk_ge : (seq1 i1 <= k)%nat \/ (seq2 j1 <= k)%nat \/ (seq1 i2 <= k)%nat \/ (seq2 j2 <= k)%nat)
      by (unfold N0 in Hk1; lia).
    destruct Hk_ge as [H|[H|[H|H]]].
    - rewrite (psi_ge_n_zero (seq1 i1) k H).
      rewrite Cmul_0_l.
      rewrite Cmul_0_r.
      rewrite Cmul_0_l.
      reflexivity.
    - rewrite (psi_ge_n_zero (seq2 j1) k H).
      rewrite Cmul_0_r.
      rewrite Cmul_0_r.
      rewrite Cmul_0_l.
      reflexivity.
    - rewrite (psi_ge_n_zero (seq1 i2) k H).
      rewrite Cmul_0_l.
      rewrite Cmul_0_r.
      rewrite Cconj_0.
      rewrite Cmul_0_r.
      reflexivity.
    - rewrite (psi_ge_n_zero (seq2 j2) k H).
      rewrite Cmul_0_r.
      rewrite Cmul_0_r.
      rewrite Cconj_0.
      rewrite Cmul_0_r.
      reflexivity.
  }
  rewrite Htrunc_eq; subst F.

  set (gamma1 := sqrt (INR (Nat.min (seq1 i1) (seq2 j1)) / (INR (seq1 i1) * INR (seq2 j1)))).
  set (gamma2 := sqrt (INR (Nat.min (seq1 i2) (seq2 j2)) / (INR (seq1 i2) * INR (seq2 j2)))).
  assert (Hgamma1_le1 : gamma1 <= 1) by (unfold gamma1; apply gamma_ab_le_1; auto).
  assert (Hgamma2_le1 : gamma2 <= 1) by (unfold gamma2; apply gamma_ab_le_1; auto).

  set (s2 := sqrt (INR 2)).
  set (sC := sqrt (INR C)).
  assert (Hs2_pos : s2 > 0) by (apply sqrt_lt_R0_c; apply lt_0_INR; lia).
  assert (Hs2_gt1 : s2 > 1). {
    unfold s2; rewrite <- sqrt_1.
    apply sqrt_lt_1; [lra | change 0 with (INR 0); apply le_INR; lia | change 1 with (INR 1); apply lt_INR; lia].
  }
  assert (HsC_pos : sC > 0) by (apply sqrt_lt_R0_c; apply lt_0_INR; lia).
  assert (HsC_ge_s2 : sC >= s2). {
    apply Rle_ge; apply sqrt_le_1_c; [apply pos_INR; lia | apply pos_INR; lia | apply le_INR; lia].
  }
  assert (HC3_ge8 : (INR C)^3 >= 8). {
    apply Rle_ge; transitivity (2^3); [right; simpl; ring |].
    apply pow_incr; split; [lra |].
    apply (Rle_trans _ (INR 2) _); [simpl; lra | apply le_INR; lia].
  }

  set (d12 := Z.abs_nat (Z.of_nat i1 - Z.of_nat i2)).
  set (d34 := Z.abs_nat (Z.of_nat j1 - Z.of_nat j2)).
  assert (Hsum_bound : (d12 + d34 <= 6)%nat). {
    unfold d12, d34; rewrite <- H_index_bound; unfold i1, i2, j1, j2; reflexivity.
  }
  assert (Hd12_le_6 : (d12 <= 6)%nat) by
    (apply (Nat.le_trans _ (d12 + d34) _ (Nat.le_add_r _ _) Hsum_bound)).
  assert (Hd34_le_6 : (d34 <= 6)%nat) by
    (apply (Nat.le_trans _ (d12 + d34) _ (Nat.le_add_l _ _) Hsum_bound)).

  assert (H_bridge12 : d_factor s2 i1 i2 <= ((INR C)^3 / 8) * d_factor sC i1 i2). {
    apply d_factor_bridge with (C:=C) (s2:=s2) (sC:=sC) (i:=i1) (j:=i2); auto;
    try exact Hs2_pos; try exact Hs2_gt1; try exact HsC_pos;
    try exact HsC_ge_s2; try exact HC3_ge8; try exact Hd12_le_6;
    exact (eq_refl s2); exact (eq_refl sC).
  }
  assert (H_bridge34 : d_factor s2 j1 j2 <= ((INR C)^3 / 8) * d_factor sC j1 j2). {
    apply d_factor_bridge with (C:=C) (s2:=s2) (sC:=sC) (i:=j1) (j:=j2); auto;
    try exact Hs2_pos; try exact Hs2_gt1; try exact HsC_pos;
    try exact HsC_ge_s2; try exact HC3_ge8; try exact Hd34_le_6;
    exact (eq_refl s2); exact (eq_refl sC).
  }

  destruct H_dom as [H_dom_i H_dom_j].

  assert (d_factor_diag_sC : forall i : nat, d_factor sC i i = 1). {
    intros i; unfold d_factor, sC; rewrite Nat.eqb_refl; reflexivity. }

  destruct (Nat.eq_dec i1 i2) as [Heq_i | Hneq_i];
  destruct (Nat.eq_dec j1 j2) as [Heq_j | Hneq_j].
  - exfalso; apply Hneq'.
    unfold i1, i2, j1, j2 in *.
    pose proof (Nat.div_mod_eq idx1 n2) as Hdiv1.
    pose proof (Nat.div_mod_eq idx2 n2) as Hdiv2.
    rewrite Heq_i, Heq_j in Hdiv1.
    rewrite <- Hdiv2 in Hdiv1.
    exact Hdiv1.
  - assert (Heq_div : (idx1 / n2)%nat = (idx2 / n2)%nat) by (unfold i1, i2; exact Heq_i).
    rewrite Heq_i in *.
    pose proof (H_dom_i Heq_div) as Hdom.
    rewrite Heq_div in Hdom.
    unfold j1, j2 in Hdom.
    assert (Ha_ge_max : (seq1 i2 >= Nat.max (seq2 j1) (seq2 j2))%nat) by exact Hdom.
    rewrite (d_factor_diag_sC i2), Rmult_1_l.
    unfold sC.
    replace (INR C * (INR C * (INR C * 1))) with ((INR C)^3) by nra.
    assert (Hgamma1_def' : gamma1 = sqrt (INR (Nat.min (seq1 i2) (seq2 j1)) / (INR (seq1 i2) * INR (seq2 j1)))).
    { unfold gamma1; now rewrite Heq_i. }
    assert (Hgamma2_def' : gamma2 = sqrt (INR (Nat.min (seq1 i2) (seq2 j2)) / (INR (seq1 i2) * INR (seq2 j2)))).
    { unfold gamma2; reflexivity. }
    exact (case_i_eq C HC seq1 seq2 Hg1 Hg2 Hsp1_2 Hsp2_2 i2 j1 j2 Hneq_j
            gamma1 gamma2 Hgamma1_def' Hgamma2_def' N0 HN0_ge_max Ha_ge_max H_bridge34).
  - assert (Heq_mod : idx1 mod n2 = idx2 mod n2) by (unfold j1, j2; exact Heq_j).
    rewrite Heq_j in *.
    pose proof (H_dom_j Heq_mod) as Hdom.
    rewrite Heq_mod in Hdom.
    unfold i1, i2 in Hdom.
    assert (Hb_ge_max : (seq2 j2 >= Nat.max (seq1 i1) (seq1 i2))%nat) by exact Hdom.
    rewrite (d_factor_diag_sC j2).
    rewrite Rmult_1_r.
    unfold sC.
    replace (INR C * (INR C * INR C)) with ((INR C)^3) by nra.
    assert (Hgamma1_def' : gamma1 = sqrt (INR (Nat.min (seq1 i1) (seq2 j2)) / (INR (seq1 i1) * INR (seq2 j2)))).
    { unfold gamma1; now rewrite Heq_j. }
    assert (Hgamma2_def' : gamma2 = sqrt (INR (Nat.min (seq1 i2) (seq2 j2)) / (INR (seq1 i2) * INR (seq2 j2)))).
    { unfold gamma2; reflexivity. }
    rewrite Rmult_1_r.
    exact (case_j_eq C HC seq1 seq2 Hg1 Hg2 Hsp1_2 Hsp2_2 i1 i2 j2 Hneq_i
            gamma1 gamma2 Hgamma1_def' Hgamma2_def' N0 HN0_ge_max Hb_ge_max H_bridge12).
  - unfold gamma1, gamma2.
    pose proof (tensor_inner_scaled_bound_gen C HC seq1 seq2 Hsp1 Hsp2 Hg1 Hg2
                  i1 i2 j1 j2 (seq1 i1) (seq1 i2) (seq2 j1) (seq2 j2)
                  (eq_refl _) (eq_refl _) (eq_refl _) (eq_refl _)
                  Hneq_i Hneq_j Hsum_bound) as Htmp4.
    simpl in Htmp4.
    unfold N0 in *.
    simpl in Htmp4.
    unfold sC.
    rewrite <- Rmult_assoc.
    exact Htmp4.
Qed.

(* 定理：二维张量积基的无条件基 *)
Theorem tensor_product_unconditional_basis_corrected :
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
    (H_dom : forall idx1 idx2 : nat,
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
    assert (Hi : (i < n1)%nat) by (apply Div0.div_lt_upper_bound; lia).
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
    assert (Hi : (i < n1)%nat) by (apply Div0.div_lt_upper_bound; lia).
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
    destruct (H_dom idx1 idx2) as [H_dom_i H_dom_j].

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
    assert (Hi0 : (i0 < n1)%nat) by (apply Div0.div_lt_upper_bound; lia).
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

(* 三维展平索引 *)
Definition flatten_3d (n2 n3 i j k : nat) : nat :=
  (i * n2 + j) * n3 + k.

(* 三维展平的逆运算 *)
Definition unflatten_3d (n2 n3 idx : nat) : nat * nat * nat :=
  let i := (idx / (n2 * n3))%nat in
  let rem := (idx mod (n2 * n3))%nat in
  let j := (rem / n3)%nat in
  let k := (rem mod n3)%nat in
  (i, j, k).

(* 展平与逆运算互逆 *)
Lemma unflatten_flatten_3d : forall (n2 n3 i j k : nat),
  (n2 > 0)%nat -> (n3 > 0)%nat ->
  (j < n2)%nat -> (k < n3)%nat ->
  unflatten_3d n2 n3 (flatten_3d n2 n3 i j k) = (i, j, k).
Proof.
  intros n2 n3 i j k Hn2 Hn3 Hj Hk.
  unfold flatten_3d, unflatten_3d.
  set (n := (n2 * n3)%nat).

  assert (Heq1 : (((i * n2 + j) * n3 + k) = i * n + (j * n3 + k))%nat).
  { unfold n; nia. }
  assert (Heq1' : (((i * n2 + j) * n3 + k) = n * i + (j * n3 + k))%nat).
  { rewrite Heq1; rewrite Nat.mul_comm; reflexivity. }
  assert (Hlt1 : (j * n3 + k < n)%nat).
  { unfold n; nia. }

  pose proof (Nat.div_unique ((i * n2 + j) * n3 + k) n i (j * n3 + k) Hlt1 Heq1') as Hdiv.
  pose proof (Nat.mod_unique ((i * n2 + j) * n3 + k) n i (j * n3 + k) Hlt1 Heq1') as Hmod.
  rewrite <- Hdiv.
  rewrite <- Hmod.

  assert (Heq2 : (j * n3 + k = n3 * j + k)%nat).
  { rewrite Nat.mul_comm; reflexivity. }
  pose proof (Nat.div_unique (j * n3 + k) n3 j k Hk Heq2) as Hdiv2.
  pose proof (Nat.mod_unique (j * n3 + k) n3 j k Hk Heq2) as Hmod2.
  rewrite <- Hdiv2.
  rewrite <- Hmod2.

  reflexivity.
Qed.

(* 展平后索引的范围上界 *)
Lemma flatten_3d_bound : forall n1 n2 n3 i j k,
  (i < n1)%nat -> (j < n2)%nat -> (k < n3)%nat ->
  (flatten_3d n2 n3 i j k < n1 * n2 * n3)%nat.
Proof.
  intros n1 n2 n3 i j k Hi Hj Hk.
  assert (Hn2_pos : (n2 > 0)%nat) by lia.
  assert (Hn3_pos : (n3 > 0)%nat) by lia.
  unfold flatten_3d.

  assert (H_sum_lt : (i * n2 + j < n1 * n2)%nat). {
    assert (H1 : (i * n2 + j < i * n2 + n2)%nat) by (apply Nat.add_lt_mono_l; exact Hj).
    assert (H2 : (i * n2 + n2 = (i+1)*n2)%nat) by ring.
    rewrite H2 in H1.
    assert (H3 : ((i+1) * n2 <= n1 * n2)%nat). {
      apply Nat.mul_le_mono_r; lia.
    }
    exact (Nat.lt_le_trans _ _ _ H1 H3).
  }

  assert (H_prod_lt : ((i * n2 + j) * n3 < n1 * n2 * n3)%nat). {
    apply Nat.mul_lt_mono_pos_r; [exact Hn3_pos | exact H_sum_lt].
  }

  assert (H_final : ((i * n2 + j) * n3 + k < n1 * n2 * n3)%nat). {
    assert (Ha : ((i * n2 + j) * n3 + k < (i * n2 + j) * n3 + n3)%nat) by (apply Nat.add_lt_mono_l; exact Hk).
    assert (Hb : ((i * n2 + j) * n3 + n3 = ((i * n2 + j) + 1) * n3)%nat) by ring.
    rewrite Hb in Ha.
    assert (Hc : (((i * n2 + j) + 1) * n3 <= n1 * n2 * n3)%nat). {
      apply Nat.mul_le_mono_r; lia.
    }
    exact (Nat.lt_le_trans _ _ _ Ha Hc).
  }

  exact H_final.
Qed.

(* 最小值不小于某数的二分选择 *)
Lemma min_ge_cases : forall a b t, (t >= Nat.min a b)%nat -> (t >= a)%nat \/ (t >= b)%nat.
Proof.
  intros a b t H.
  destruct (Nat.min_spec a b) as [[Hle Hmin]|[Hle Hmin]];
    rewrite Hmin in H; [left | right]; exact H.
Qed.

(* 三维局部最大值点（用于截断） *)
Definition M_loc_3d (a1 a2 b1 b2 c1 c2 : nat) : nat :=
  S (max (max (max a1 b1) (max a2 b2)) (max c1 c2)).

(* 共轭零元 *)
Lemma Cconj_C0 : Cconj C0 = C0.
Proof.
  unfold C0; unfold Cconj at 1; simpl; f_equal; ring.
Qed.

(* 部分和截断（局部版本） *)
Lemma Csum_trunc_tail_local : forall (f : nat -> Complex) (p q : nat),
  (q <= p)%nat -> (forall k, (q <= k < p)%nat -> f k = C0) -> Csum f p = Csum f q.
Proof.
  induction p as [|p IH]; intros q Hle Hzero.
  - inversion Hle; subst q; simpl; reflexivity.
  - apply Nat.le_succ_r in Hle; destruct Hle as [Hq_le | Hq_eq].
    + simpl.
      rewrite IH with (q := q); [| exact Hq_le |].
      * assert (Hfp : f p = C0). {
          apply Hzero with (k := p). split.
          - exact Hq_le.
          - apply Nat.lt_succ_diag_r.
        }
        rewrite Hfp, Cadd_0_r.
        reflexivity.
      * intros k Hk. apply Hzero. split.
        -- exact (proj1 Hk).
        -- apply Nat.lt_lt_succ_r; exact (proj2 Hk).
    + subst q; reflexivity.
Qed.

(* 倒数乘积恒等式 *)
Lemma inv_mul_eq (x y : R) : x <> 0 -> y <> 0 -> / x * / y = / (x * y).
Proof. intros; symmetry; apply Rinv_mult; assumption. Qed.

(* 共轭乘法分配 *)
Lemma Cconj_mul : forall z1 z2 : Complex, Cconj (z1 *c z2) = Cconj z1 *c Cconj z2.
Proof.
  intros [x1 y1] [x2 y2]; unfold Cconj, Cmul; simpl; f_equal; ring.
Qed.

(* 实嵌入的共轭不变性 *)
Lemma Cconj_Cof_real : forall r : R, Cconj (Cof_real r) = Cof_real r.
Proof.
  intro r; unfold Cconj, Cof_real; simpl; apply Complex_eq; simpl; ring.
Qed.

(* 实嵌入的乘法 *)
Lemma Cof_real_mul : forall r1 r2 : R, Cof_real r1 *c Cof_real r2 = Cof_real (r1 * r2).
Proof.
  intros r1 r2; unfold Cof_real, Cmul; simpl; apply Complex_eq; simpl; ring.
Qed.

(* 复数乘法结合律 *)
Lemma Cmul_assoc : forall z1 z2 z3 : Complex, (z1 *c z2) *c z3 = z1 *c (z2 *c z3).
Proof.
  intros [x1 y1] [x2 y2] [x3 y3]; unfold Cmul; simpl;
  apply Complex_eq; simpl; ring.
Qed.

(* 复数乘法交换律 *)
Lemma Cmul_comm : forall z1 z2 : Complex, z1 *c z2 = z2 *c z1.
Proof.
  intros [x1 y1] [x2 y2]; unfold Cmul; simpl;
  apply Complex_eq; simpl; ring.
Qed.

(* 四元乘积重排 *)
Lemma inner_rearrange : forall B C E F : Complex,
  (B *c C) *c (E *c F) = (B *c E) *c (C *c F).
Proof.
  intros B C E F.
  rewrite (Cmul_assoc B C (E *c F)).
  rewrite <- (Cmul_assoc C E F).
  rewrite (Cmul_comm C E).
  rewrite (Cmul_assoc E C F).
  rewrite <- (Cmul_assoc B E (C *c F)).
  reflexivity.
Qed.

(* 三重乘积重排 *)
Lemma prod_rearrange : forall A B C D E F : Complex,
  (A *c B *c C) *c (D *c E *c F) = (A *c D) *c (B *c E) *c (C *c F).
Proof.
  intros A B C D E F.
  rewrite (Cmul_assoc A B C).
  rewrite (Cmul_assoc D E F).
  rewrite <- (Cmul_assoc (A *c (B *c C)) D (E *c F)).
  rewrite (Cmul_assoc A (B *c C) D).
  rewrite (Cmul_assoc B C D).
  rewrite (Cmul_comm C D).
  rewrite <- (Cmul_assoc B D C).
  rewrite (Cmul_comm B D).
  rewrite (Cmul_assoc D B C).
  rewrite <- (Cmul_assoc A D (B *c C)).
  rewrite (Cmul_assoc (A *c D) (B *c C) (E *c F)).
  rewrite (Cmul_assoc (A *c D) (B *c E) (C *c F)).
  apply (f_equal (fun x => (A *c D) *c x)).
  apply inner_rearrange.
Qed.

(* 有限和逐项相等 *)
Lemma Csum_ext : forall n (f g : nat -> Complex),
  (forall i, (i < n)%nat -> f i = g i) -> Csum f n = Csum g n.
Proof.
  induction n as [|n IH]; simpl; intros f g H.
  - reflexivity.
  - rewrite (IH f g).
    + f_equal; apply H; lia.
    + intros i Hi; apply H; lia.
Qed.

(* 标量左乘可提取 *)
Lemma Csum_scal_l : forall (c : Complex) (f : nat -> Complex) n,
  Csum (fun i => c *c f i) n = c *c Csum f n.
Proof.
  intros c f n; induction n as [|n IH]; simpl.
  - symmetry; apply Cmul_0_r.
  - rewrite IH, Cmul_add_distr_l; reflexivity.
Qed.

(* 三维乘积内积分解（正性条件版） *)
Lemma product_psi_inner_decomposition_3d :
  forall (a1 a2 b1 b2 c1 c2 : nat) (g : nat -> nat -> nat -> R),
    (g a1 b1 c1 > 0)%R -> (g a2 b2 c2 > 0)%R ->
  let N0 := Nat.min (Nat.min a1 a2) (Nat.min (Nat.min b1 b2) (Nat.min c1 c2)) in
  let M_loc := M_loc_3d a1 a2 b1 b2 c1 c2 in
  Csum (fun t => (Cof_real (/ g a1 b1 c1) *c (psi a1 t *c psi b1 t *c psi c1 t)) *c
               Cconj (Cof_real (/ g a2 b2 c2) *c (psi a2 t *c psi b2 t *c psi c2 t)))
       (Nat.pred M_loc)
  = Cof_real (/ (g a1 b1 c1 * g a2 b2 c2)) *c
    Csum (fun t => (psi a1 t *c Cconj (psi a2 t)) *c
                   (psi b1 t *c Cconj (psi b2 t)) *c
                   (psi c1 t *c Cconj (psi c2 t))) N0.
Proof.
  intros a1 a2 b1 b2 c1 c2 g Hg1 Hg2 N0 M_loc.
  subst N0 M_loc; simpl.
  set (g1 := g a1 b1 c1).
  set (g2 := g a2 b2 c2).
  set (N0 := Nat.min (Nat.min a1 a2) (Nat.min (Nat.min b1 b2) (Nat.min c1 c2))).
  set (M_max := max (max (max a1 b1) (max a2 b2)) (max c1 c2)).

  assert (Hzero : forall t, (t >= N0)%nat ->
    (psi a1 t *c Cconj (psi a2 t)) *c
    (psi b1 t *c Cconj (psi b2 t)) *c
    (psi c1 t *c Cconj (psi c2 t)) = C0).
  {
    intros t Ht.
    unfold N0 in Ht.
    apply min_ge_cases in Ht as [Ht1 | Ht2].
    - apply min_ge_cases in Ht1 as [Ha1 | Ha2].
      + rewrite (psi_ge_n_zero a1 t Ha1).
        rewrite Cmul_0_l, Cmul_0_l, Cmul_0_l; reflexivity.
      + rewrite (psi_ge_n_zero a2 t Ha2).
        rewrite Cconj_C0.
        rewrite Cmul_0_r, Cmul_0_l, Cmul_0_l; reflexivity.
    - apply min_ge_cases in Ht2 as [Ht21 | Ht22].
      + apply min_ge_cases in Ht21 as [Hb1 | Hb2].
        * rewrite (psi_ge_n_zero b1 t Hb1).
          rewrite Cmul_0_l, Cmul_0_r, Cmul_0_l; reflexivity.
        * rewrite (psi_ge_n_zero b2 t Hb2).
          rewrite Cconj_C0, Cmul_0_r, Cmul_0_r, Cmul_0_l; reflexivity.
      + apply min_ge_cases in Ht22 as [Hc1 | Hc2].
        * rewrite (psi_ge_n_zero c1 t Hc1).
          rewrite Cmul_0_l, Cmul_0_r; reflexivity.
        * rewrite (psi_ge_n_zero c2 t Hc2).
          rewrite Cconj_C0, Cmul_0_r, Cmul_0_r; reflexivity.
  }

  assert (Hterm_eq : forall t,
    (Cof_real (/ g1) *c (psi a1 t *c psi b1 t *c psi c1 t)) *c
    Cconj (Cof_real (/ g2) *c (psi a2 t *c psi b2 t *c psi c2 t))
    = Cof_real (/ (g1 * g2)) *c
      ((psi a1 t *c Cconj (psi a2 t)) *c
       (psi b1 t *c Cconj (psi b2 t)) *c
       (psi c1 t *c Cconj (psi c2 t)))).
  {
    intro t.
    rewrite (Cconj_mul (Cof_real (/ g2)) (psi a2 t *c psi b2 t *c psi c2 t)).
    rewrite Cconj_Cof_real.
    rewrite (Cconj_mul (psi a2 t *c psi b2 t) (psi c2 t)).
    rewrite (Cconj_mul (psi a2 t) (psi b2 t)).
    rewrite (Cmul_assoc (Cof_real (/ g1)) (psi a1 t *c psi b1 t *c psi c1 t) _).
    rewrite <- (Cmul_assoc (psi a1 t *c psi b1 t *c psi c1 t) (Cof_real (/ g2)) _).
    rewrite (Cmul_comm (psi a1 t *c psi b1 t *c psi c1 t) (Cof_real (/ g2))).
    rewrite (Cmul_assoc (Cof_real (/ g2)) (psi a1 t *c psi b1 t *c psi c1 t) _).
    rewrite <- (Cmul_assoc (Cof_real (/ g1)) (Cof_real (/ g2)) _).
    rewrite (Cof_real_mul (/ g1) (/ g2)).
    assert (Hinv : (/ g1 * / g2)%R = (/ (g1 * g2))%R). {
      symmetry; apply Rinv_mult; apply Rgt_not_eq; auto.
    }
    rewrite Hinv.
    rewrite prod_rearrange.
    reflexivity.
  }

  set (lhs_fun := fun t : nat =>
    (Cof_real (/ g1) *c (psi a1 t *c psi b1 t *c psi c1 t)) *c
    Cconj (Cof_real (/ g2) *c (psi a2 t *c psi b2 t *c psi c2 t))).
  set (rhs_fun := fun t : nat =>
    Cof_real (/ (g1 * g2)) *c
    ((psi a1 t *c Cconj (psi a2 t)) *c
     (psi b1 t *c Cconj (psi b2 t)) *c
     (psi c1 t *c Cconj (psi c2 t)))).

  assert (Hsum_eq : Csum lhs_fun M_max = Csum rhs_fun M_max) by
    (apply Csum_ext; intros t Ht; apply Hterm_eq).
  rewrite Hsum_eq.
  unfold rhs_fun.
  rewrite Csum_scal_l.
  assert (Htrunc : Csum (fun t : nat => (psi a1 t *c Cconj (psi a2 t)) *c
                                       (psi b1 t *c Cconj (psi b2 t)) *c
                                       (psi c1 t *c Cconj (psi c2 t))) M_max
                  = Csum (fun t : nat => (psi a1 t *c Cconj (psi a2 t)) *c
                                       (psi b1 t *c Cconj (psi b2 t)) *c
                                       (psi c1 t *c Cconj (psi c2 t))) N0).
  {
    apply Csum_trunc_tail_local with (q := N0) (p := M_max).
    - unfold M_max; simpl; lia.
    - intros k [H1 H2]; apply Hzero; lia.
  }
  rewrite Htrunc; reflexivity.
Qed.

(* 三维乘积内积分解（非零条件版，带正性保证） *)
Lemma product_psi_inner_decomposition_3d_nonzero_alt :
  forall (a1 a2 b1 b2 c1 c2 : nat) (g : nat -> nat -> nat -> R),
  let N0 := Nat.min (Nat.min a1 a2) (Nat.min (Nat.min b1 b2) (Nat.min c1 c2)) in
  let M_loc := M_loc_3d a1 a2 b1 b2 c1 c2 in
  (g a1 b1 c1 * g a2 b2 c2 <> 0) ->
  Csum (fun t => (Cof_real (/ g a1 b1 c1) *c (psi a1 t *c psi b1 t *c psi c1 t)) *c
               Cconj (Cof_real (/ g a2 b2 c2) *c (psi a2 t *c psi b2 t *c psi c2 t)))
       (Nat.pred M_loc)
  = Cof_real (/ (g a1 b1 c1 * g a2 b2 c2)) *c
    Csum (fun t => (psi a1 t *c Cconj (psi a2 t)) *c
                   (psi b1 t *c Cconj (psi b2 t)) *c
                   (psi c1 t *c Cconj (psi c2 t))) N0.
Proof.
  intros a1 a2 b1 b2 c1 c2 g N0 M_loc Hprod_nz.
  subst N0 M_loc; simpl.
  set (g1 := g a1 b1 c1).
  set (g2 := g a2 b2 c2).
  assert (Hg1nz : g1 <> 0). {
    intro H. apply Hprod_nz. unfold g1 in H. rewrite H. ring.
  }
  assert (Hg2nz : g2 <> 0). {
    intro H. apply Hprod_nz. unfold g2 in H. rewrite H. ring.
  }
  set (N0 := Nat.min (Nat.min a1 a2) (Nat.min (Nat.min b1 b2) (Nat.min c1 c2))).
  set (M_max := max (max (max a1 b1) (max a2 b2)) (max c1 c2)).

  assert (Hzero : forall t, (t >= N0)%nat ->
    (psi a1 t *c Cconj (psi a2 t)) *c
    (psi b1 t *c Cconj (psi b2 t)) *c
    (psi c1 t *c Cconj (psi c2 t)) = C0).
  {
    intros t Ht.
    unfold N0 in Ht.
    apply min_ge_cases in Ht as [Ht1 | Ht2].
    - apply min_ge_cases in Ht1 as [Ha1 | Ha2].
      + rewrite (psi_ge_n_zero a1 t Ha1).
        rewrite Cmul_0_l, Cmul_0_l, Cmul_0_l; reflexivity.
      + rewrite (psi_ge_n_zero a2 t Ha2).
        rewrite Cconj_C0.
        rewrite Cmul_0_r, Cmul_0_l, Cmul_0_l; reflexivity.
    - apply min_ge_cases in Ht2 as [Ht21 | Ht22].
      + apply min_ge_cases in Ht21 as [Hb1 | Hb2].
        * rewrite (psi_ge_n_zero b1 t Hb1).
          rewrite Cmul_0_l, Cmul_0_r, Cmul_0_l; reflexivity.
        * rewrite (psi_ge_n_zero b2 t Hb2).
          rewrite Cconj_C0, Cmul_0_r, Cmul_0_r, Cmul_0_l; reflexivity.
      + apply min_ge_cases in Ht22 as [Hc1 | Hc2].
        * rewrite (psi_ge_n_zero c1 t Hc1).
          rewrite Cmul_0_l, Cmul_0_r; reflexivity.
        * rewrite (psi_ge_n_zero c2 t Hc2).
          rewrite Cconj_C0, Cmul_0_r, Cmul_0_r; reflexivity.
  }

  assert (Hterm_eq : forall t,
    (Cof_real (/ g1) *c (psi a1 t *c psi b1 t *c psi c1 t)) *c
    Cconj (Cof_real (/ g2) *c (psi a2 t *c psi b2 t *c psi c2 t))
    = Cof_real (/ (g1 * g2)) *c
      ((psi a1 t *c Cconj (psi a2 t)) *c
       (psi b1 t *c Cconj (psi b2 t)) *c
       (psi c1 t *c Cconj (psi c2 t)))).
  {
    intro t.
    rewrite (Cconj_mul (Cof_real (/ g2)) (psi a2 t *c psi b2 t *c psi c2 t)).
    rewrite Cconj_Cof_real.
    rewrite (Cconj_mul (psi a2 t *c psi b2 t) (psi c2 t)).
    rewrite (Cconj_mul (psi a2 t) (psi b2 t)).
    rewrite (Cmul_assoc (Cof_real (/ g1)) (psi a1 t *c psi b1 t *c psi c1 t) _).
    rewrite <- (Cmul_assoc (psi a1 t *c psi b1 t *c psi c1 t) (Cof_real (/ g2)) _).
    rewrite (Cmul_comm (psi a1 t *c psi b1 t *c psi c1 t) (Cof_real (/ g2))).
    rewrite (Cmul_assoc (Cof_real (/ g2)) (psi a1 t *c psi b1 t *c psi c1 t) _).
    rewrite <- (Cmul_assoc (Cof_real (/ g1)) (Cof_real (/ g2)) _).
    rewrite (Cof_real_mul (/ g1) (/ g2)).
    assert (Hinv : (/ g1 * / g2)%R = (/ (g1 * g2))%R). {
      symmetry; apply Rinv_mult; assumption.
    }
    rewrite Hinv.
    rewrite prod_rearrange.
    reflexivity.
  }

  set (lhs_fun := fun t : nat =>
    (Cof_real (/ g1) *c (psi a1 t *c psi b1 t *c psi c1 t)) *c
    Cconj (Cof_real (/ g2) *c (psi a2 t *c psi b2 t *c psi c2 t))).
  set (rhs_fun := fun t : nat =>
    Cof_real (/ (g1 * g2)) *c
    ((psi a1 t *c Cconj (psi a2 t)) *c
     (psi b1 t *c Cconj (psi b2 t)) *c
     (psi c1 t *c Cconj (psi c2 t)))).

  assert (Hsum_eq : Csum lhs_fun M_max = Csum rhs_fun M_max) by
    (apply Csum_ext; intros t Ht; apply Hterm_eq).
  rewrite Hsum_eq.
  unfold rhs_fun.
  rewrite Csum_scal_l.
  assert (Htrunc : Csum (fun t : nat => (psi a1 t *c Cconj (psi a2 t)) *c
                                       (psi b1 t *c Cconj (psi b2 t)) *c
                                       (psi c1 t *c Cconj (psi c2 t))) M_max
                  = Csum (fun t : nat => (psi a1 t *c Cconj (psi a2 t)) *c
                                       (psi b1 t *c Cconj (psi b2 t)) *c
                                       (psi c1 t *c Cconj (psi c2 t))) N0).
  {
    apply Csum_trunc_tail_local with (q := N0) (p := M_max).
    - unfold M_max; simpl; lia.
    - intros k [H1 H2]; apply Hzero; lia.
  }
  rewrite Htrunc; reflexivity.
Qed.

(* 三维乘积内积分解（非零条件简化版 *)
Lemma product_psi_inner_decomposition_3d_nonzero :
  forall (a1 a2 b1 b2 c1 c2 : nat) (g : nat -> nat -> nat -> R),
  let N0 := Nat.min (Nat.min a1 a2) (Nat.min (Nat.min b1 b2) (Nat.min c1 c2)) in
  let M_loc := M_loc_3d a1 a2 b1 b2 c1 c2 in
  (g a1 b1 c1 * g a2 b2 c2 <> 0) ->
  Csum (fun t => (Cof_real (/ g a1 b1 c1) *c (psi a1 t *c psi b1 t *c psi c1 t)) *c
               Cconj (Cof_real (/ g a2 b2 c2) *c (psi a2 t *c psi b2 t *c psi c2 t)))
       (Nat.pred M_loc)
  = Cof_real (/ (g a1 b1 c1 * g a2 b2 c2)) *c
    Csum (fun t => (psi a1 t *c Cconj (psi a2 t)) *c
                   (psi b1 t *c Cconj (psi b2 t)) *c
                   (psi c1 t *c Cconj (psi c2 t))) N0.
Proof.
  intros a1 a2 b1 b2 c1 c2 g N0 M_loc Hprod_nz.
  subst N0 M_loc; simpl.
  set (g1 := g a1 b1 c1).
  set (g2 := g a2 b2 c2).
  assert (Hg1nz : g1 <> 0). {
    intro H. apply Hprod_nz. unfold g1 in H. rewrite H. ring.
  }
  assert (Hg2nz : g2 <> 0). {
    intro H. apply Hprod_nz. unfold g2 in H. rewrite H. ring.
  }
  set (N0 := Nat.min (Nat.min a1 a2) (Nat.min (Nat.min b1 b2) (Nat.min c1 c2))).
  set (M_max := max (max (max a1 b1) (max a2 b2)) (max c1 c2)).

  assert (Hzero : forall t, (t >= N0)%nat ->
    (psi a1 t *c Cconj (psi a2 t)) *c
    (psi b1 t *c Cconj (psi b2 t)) *c
    (psi c1 t *c Cconj (psi c2 t)) = C0).
  {
    intros t Ht.
    unfold N0 in Ht.
    apply min_ge_cases in Ht as [Ht1 | Ht2].
    - apply min_ge_cases in Ht1 as [Ha1 | Ha2].
      + rewrite (psi_ge_n_zero a1 t Ha1).
        rewrite Cmul_0_l, Cmul_0_l, Cmul_0_l; reflexivity.
      + rewrite (psi_ge_n_zero a2 t Ha2).
        rewrite Cconj_C0.
        rewrite Cmul_0_r, Cmul_0_l, Cmul_0_l; reflexivity.
    - apply min_ge_cases in Ht2 as [Ht21 | Ht22].
      + apply min_ge_cases in Ht21 as [Hb1 | Hb2].
        * rewrite (psi_ge_n_zero b1 t Hb1).
          rewrite Cmul_0_l, Cmul_0_r, Cmul_0_l; reflexivity.
        * rewrite (psi_ge_n_zero b2 t Hb2).
          rewrite Cconj_C0, Cmul_0_r, Cmul_0_r, Cmul_0_l; reflexivity.
      + apply min_ge_cases in Ht22 as [Hc1 | Hc2].
        * rewrite (psi_ge_n_zero c1 t Hc1).
          rewrite Cmul_0_l, Cmul_0_r; reflexivity.
        * rewrite (psi_ge_n_zero c2 t Hc2).
          rewrite Cconj_C0, Cmul_0_r, Cmul_0_r; reflexivity.
  }

  assert (Hterm_eq : forall t,
    (Cof_real (/ g1) *c (psi a1 t *c psi b1 t *c psi c1 t)) *c
    Cconj (Cof_real (/ g2) *c (psi a2 t *c psi b2 t *c psi c2 t))
    = Cof_real (/ (g1 * g2)) *c
      ((psi a1 t *c Cconj (psi a2 t)) *c
       (psi b1 t *c Cconj (psi b2 t)) *c
       (psi c1 t *c Cconj (psi c2 t)))).
  {
    intro t.
    rewrite (Cconj_mul (Cof_real (/ g2)) (psi a2 t *c psi b2 t *c psi c2 t)).
    rewrite Cconj_Cof_real.
    rewrite (Cconj_mul (psi a2 t *c psi b2 t) (psi c2 t)).
    rewrite (Cconj_mul (psi a2 t) (psi b2 t)).
    rewrite (Cmul_assoc (Cof_real (/ g1)) (psi a1 t *c psi b1 t *c psi c1 t) _).
    rewrite <- (Cmul_assoc (psi a1 t *c psi b1 t *c psi c1 t) (Cof_real (/ g2)) _).
    rewrite (Cmul_comm (psi a1 t *c psi b1 t *c psi c1 t) (Cof_real (/ g2))).
    rewrite (Cmul_assoc (Cof_real (/ g2)) (psi a1 t *c psi b1 t *c psi c1 t) _).
    rewrite <- (Cmul_assoc (Cof_real (/ g1)) (Cof_real (/ g2)) _).
    rewrite (Cof_real_mul (/ g1) (/ g2)).
    assert (Hinv : (/ g1 * / g2)%R = (/ (g1 * g2))%R). {
      symmetry; apply Rinv_mult; assumption.
    }
    rewrite Hinv.
    rewrite prod_rearrange.
    reflexivity.
  }

  set (lhs_fun := fun t : nat =>
    (Cof_real (/ g1) *c (psi a1 t *c psi b1 t *c psi c1 t)) *c
    Cconj (Cof_real (/ g2) *c (psi a2 t *c psi b2 t *c psi c2 t))).
  set (rhs_fun := fun t : nat =>
    Cof_real (/ (g1 * g2)) *c
    ((psi a1 t *c Cconj (psi a2 t)) *c
     (psi b1 t *c Cconj (psi b2 t)) *c
     (psi c1 t *c Cconj (psi c2 t)))).

  assert (Hsum_eq : Csum lhs_fun M_max = Csum rhs_fun M_max) by
    (apply Csum_ext; intros t Ht; apply Hterm_eq).
  rewrite Hsum_eq.
  unfold rhs_fun.
  rewrite Csum_scal_l.
  assert (Htrunc : Csum (fun t : nat => (psi a1 t *c Cconj (psi a2 t)) *c
                                       (psi b1 t *c Cconj (psi b2 t)) *c
                                       (psi c1 t *c Cconj (psi c2 t))) M_max
                  = Csum (fun t : nat => (psi a1 t *c Cconj (psi a2 t)) *c
                                       (psi b1 t *c Cconj (psi b2 t)) *c
                                       (psi c1 t *c Cconj (psi c2 t))) N0).
  {
    apply Csum_trunc_tail_local with (q := N0) (p := M_max).
    - unfold M_max; simpl; lia.
    - intros k [H1 H2]; apply Hzero; lia.
  }
  rewrite Htrunc; reflexivity.
Qed.

(* 三维乘积内积分解（一般缩放因子） *)
Lemma product_psi_inner_decomposition_3d_gen :
  forall (a1 a2 b1 b2 c1 c2 : nat) (g1 g2 : R),
    g1 <> 0 -> g2 <> 0 ->
    let N0 := Nat.min (Nat.min a1 a2) (Nat.min (Nat.min b1 b2) (Nat.min c1 c2)) in
    let M_loc := M_loc_3d a1 a2 b1 b2 c1 c2 in
    Csum (fun t => (Cof_real (/ g1) *c (psi a1 t *c psi b1 t *c psi c1 t)) *c
                 Cconj (Cof_real (/ g2) *c (psi a2 t *c psi b2 t *c psi c2 t)))
         (Nat.pred M_loc)
    = Cof_real (/ (g1 * g2)) *c
      Csum (fun t => (psi a1 t *c Cconj (psi a2 t)) *c
                     (psi b1 t *c Cconj (psi b2 t)) *c
                     (psi c1 t *c Cconj (psi c2 t))) N0.
Proof.
  intros a1 a2 b1 b2 c1 c2 g1 g2 Hg1 Hg2.
  set (N0 := Nat.min (Nat.min a1 a2) (Nat.min (Nat.min b1 b2) (Nat.min c1 c2))).
  set (M_max := max (max (max a1 b1) (max a2 b2)) (max c1 c2)).

  assert (Hzero : forall t, (t >= N0)%nat ->
    (psi a1 t *c Cconj (psi a2 t)) *c
    (psi b1 t *c Cconj (psi b2 t)) *c
    (psi c1 t *c Cconj (psi c2 t)) = C0).
  {
    intros t Ht.
    unfold N0 in Ht.
    apply min_ge_cases in Ht as [Ht1 | Ht2].
    - apply min_ge_cases in Ht1 as [Ha1 | Ha2].
      + rewrite (psi_ge_n_zero a1 t Ha1).
        rewrite Cmul_0_l, Cmul_0_l, Cmul_0_l; reflexivity.
      + rewrite (psi_ge_n_zero a2 t Ha2).
        rewrite Cconj_C0.
        rewrite Cmul_0_r, Cmul_0_l, Cmul_0_l; reflexivity.
    - apply min_ge_cases in Ht2 as [Ht21 | Ht22].
      + apply min_ge_cases in Ht21 as [Hb1 | Hb2].
        * rewrite (psi_ge_n_zero b1 t Hb1).
          rewrite Cmul_0_l, Cmul_0_r, Cmul_0_l; reflexivity.
        * rewrite (psi_ge_n_zero b2 t Hb2).
          rewrite Cconj_C0, Cmul_0_r, Cmul_0_r, Cmul_0_l; reflexivity.
      + apply min_ge_cases in Ht22 as [Hc1 | Hc2].
        * rewrite (psi_ge_n_zero c1 t Hc1).
          rewrite Cmul_0_l, Cmul_0_r; reflexivity.
        * rewrite (psi_ge_n_zero c2 t Hc2).
          rewrite Cconj_C0, Cmul_0_r, Cmul_0_r; reflexivity.
  }

  assert (Hterm_eq : forall t,
    (Cof_real (/ g1) *c (psi a1 t *c psi b1 t *c psi c1 t)) *c
    Cconj (Cof_real (/ g2) *c (psi a2 t *c psi b2 t *c psi c2 t))
    = Cof_real (/ (g1 * g2)) *c
      ((psi a1 t *c Cconj (psi a2 t)) *c
       (psi b1 t *c Cconj (psi b2 t)) *c
       (psi c1 t *c Cconj (psi c2 t)))).
  {
    intro t.
    rewrite (Cconj_mul (Cof_real (/ g2)) (psi a2 t *c psi b2 t *c psi c2 t)).
    rewrite Cconj_Cof_real.
    rewrite (Cconj_mul (psi a2 t *c psi b2 t) (psi c2 t)).
    rewrite (Cconj_mul (psi a2 t) (psi b2 t)).
    rewrite (Cmul_assoc (Cof_real (/ g1)) (psi a1 t *c psi b1 t *c psi c1 t) _).
    rewrite <- (Cmul_assoc (psi a1 t *c psi b1 t *c psi c1 t) (Cof_real (/ g2)) _).
    rewrite (Cmul_comm (psi a1 t *c psi b1 t *c psi c1 t) (Cof_real (/ g2))).
    rewrite (Cmul_assoc (Cof_real (/ g2)) (psi a1 t *c psi b1 t *c psi c1 t) _).
    rewrite <- (Cmul_assoc (Cof_real (/ g1)) (Cof_real (/ g2)) _).
    rewrite (Cof_real_mul (/ g1) (/ g2)).
    assert (Hinv : (/ g1 * / g2) = / (g1 * g2)).
      { symmetry; apply Rinv_mult; assumption. }
    rewrite Hinv.
    rewrite prod_rearrange.
    reflexivity.
  }

  set (lhs_fun := fun t : nat =>
    (Cof_real (/ g1) *c (psi a1 t *c psi b1 t *c psi c1 t)) *c
    Cconj (Cof_real (/ g2) *c (psi a2 t *c psi b2 t *c psi c2 t))).
  set (rhs_fun := fun t : nat =>
    Cof_real (/ (g1 * g2)) *c
    ((psi a1 t *c Cconj (psi a2 t)) *c
     (psi b1 t *c Cconj (psi b2 t)) *c
     (psi c1 t *c Cconj (psi c2 t)))).

  assert (Hsum_eq : Csum lhs_fun M_max = Csum rhs_fun M_max) by
    (apply Csum_ext; intros t Ht; apply Hterm_eq).
  simpl.
  fold M_max.
  rewrite Hsum_eq.
  unfold rhs_fun.
  rewrite Csum_scal_l.
  assert (Htrunc : Csum (fun t : nat => (psi a1 t *c Cconj (psi a2 t)) *c
                                       (psi b1 t *c Cconj (psi b2 t)) *c
                                       (psi c1 t *c Cconj (psi c2 t))) M_max
                  = Csum (fun t : nat => (psi a1 t *c Cconj (psi a2 t)) *c
                                       (psi b1 t *c Cconj (psi b2 t)) *c
                                       (psi c1 t *c Cconj (psi c2 t))) N0).
  {
    apply Csum_trunc_tail_local with (q := N0) (p := M_max).
    - unfold M_max; simpl; lia.
    - intros k [H1 H2]; apply Hzero; lia.
  }
  rewrite Htrunc; reflexivity.
Qed.

(* 三维乘积内积分解（函数参数非零版） *)
Lemma product_psi_inner_decomposition_3d_fun_nonzero :
  forall (a1 a2 b1 b2 c1 c2 : nat) (g : nat -> nat -> nat -> R),
    let N0 := Nat.min (Nat.min a1 a2) (Nat.min (Nat.min b1 b2) (Nat.min c1 c2)) in
    let M_loc := M_loc_3d a1 a2 b1 b2 c1 c2 in
    (g a1 b1 c1 * g a2 b2 c2 <> 0) ->
    Csum (fun t => (Cof_real (/ g a1 b1 c1) *c (psi a1 t *c psi b1 t *c psi c1 t)) *c
                 Cconj (Cof_real (/ g a2 b2 c2) *c (psi a2 t *c psi b2 t *c psi c2 t)))
         (Nat.pred M_loc)
    = Cof_real (/ (g a1 b1 c1 * g a2 b2 c2)) *c
      Csum (fun t => (psi a1 t *c Cconj (psi a2 t)) *c
                     (psi b1 t *c Cconj (psi b2 t)) *c
                     (psi c1 t *c Cconj (psi c2 t))) N0.
Proof.
  intros a1 a2 b1 b2 c1 c2 g N0 M_loc Hprod_nz.
  set (g1 := g a1 b1 c1). set (g2 := g a2 b2 c2).
  assert (Hg1 : g1 <> 0).
    { intro H; apply Hprod_nz; unfold g1 in H; rewrite H; ring. }
  assert (Hg2 : g2 <> 0).
    { intro H; apply Hprod_nz; unfold g2 in H; rewrite H; ring. }
  apply (product_psi_inner_decomposition_3d_gen a1 a2 b1 b2 c1 c2 g1 g2 Hg1 Hg2).
Qed.

(* 三维乘积内积分解（函数参数正版） *)
Lemma product_psi_inner_decomposition_3d_pos :
  forall (a1 a2 b1 b2 c1 c2 : nat) (g : nat -> nat -> nat -> R),
    let N0 := Nat.min (Nat.min a1 a2) (Nat.min (Nat.min b1 b2) (Nat.min c1 c2)) in
    let M_loc := M_loc_3d a1 a2 b1 b2 c1 c2 in
    (g a1 b1 c1 > 0) -> (g a2 b2 c2 > 0) ->
    Csum (fun t => (Cof_real (/ g a1 b1 c1) *c (psi a1 t *c psi b1 t *c psi c1 t)) *c
                 Cconj (Cof_real (/ g a2 b2 c2) *c (psi a2 t *c psi b2 t *c psi c2 t)))
         (Nat.pred M_loc)
    = Cof_real (/ (g a1 b1 c1 * g a2 b2 c2)) *c
      Csum (fun t => (psi a1 t *c Cconj (psi a2 t)) *c
                     (psi b1 t *c Cconj (psi b2 t)) *c
                     (psi c1 t *c Cconj (psi c2 t))) N0.
Proof.
  intros a1 a2 b1 b2 c1 c2 g N0 M_loc Hg1pos Hg2pos.
  apply product_psi_inner_decomposition_3d_gen with (g1 := g a1 b1 c1) (g2 := g a2 b2 c2);
    [ apply Rgt_not_eq; exact Hg1pos | apply Rgt_not_eq; exact Hg2pos ].
Qed.

(* 有限和减法拆分 *)
Lemma sum_f_R0_sub (f g : nat -> R) (n : nat) :
  sum_f_R0 (fun i => f i - g i) n = sum_f_R0 f n - sum_f_R0 g n.
Proof.
  induction n as [|n IH]; simpl.
  - ring.
  - rewrite IH; ring.
Qed.

(* 有限和条件恒零（指标超界） *)
Lemma sum_f_R0_lt_const_false (n m : nat) (f : nat -> R) :
  (n < m)%nat ->
  sum_f_R0 (fun j : nat => if j =? m then f j else 0) n = 0.
Proof.
  induction n as [|n IH]; intros Hlt.
  - destruct m as [|m'].
    + exfalso; lia.
    + simpl; reflexivity.
  - rewrite sum_f_R0_S.
    rewrite IH by (apply Nat.lt_trans with (S n); [apply Nat.lt_succ_diag_r | exact Hlt]).
    assert (Hfalse : (S n =? m) = false) by (apply Nat.eqb_neq; lia).
    rewrite Hfalse; ring.
Qed.

(* 有限和单点取值（等式判断） *)
Lemma sum_f_R0_single_eqb (n i : nat) (f : nat -> R) :
  (i <= n)%nat -> sum_f_R0 (fun j => if j =? i then f j else 0) n = f i.
Proof.
  induction n as [|n IH]; intros Hle.
  - apply Nat.le_0_r in Hle; subst i; simpl; ring.
  - apply Nat.le_succ_r in Hle; destruct Hle as [Hle' | Heq].
    + rewrite sum_f_R0_S.
      rewrite IH by exact Hle'.
      assert (Hfalse : (S n =? i) = false) by (apply Nat.eqb_neq; lia).
      rewrite Hfalse; ring.
    + subst i.
      rewrite sum_f_R0_S.
      rewrite Nat.eqb_refl.
      rewrite sum_f_R0_lt_const_false with (m := S n) (f := f); [ring | lia].
Qed.

(* 有限和右乘标量 *)
Lemma sum_f_R0_scal_r (c : R) (f : nat -> R) (n : nat) :
  sum_f_R0 (fun i => f i * c) n = sum_f_R0 f n * c.
Proof.
  induction n as [|n IH].
  - simpl; ring.
  - simpl; rewrite IH; ring.
Qed.

(* 双重求和排除单点 *)
Lemma double_sum_excl_point (n m j0 k0 : nat) (A B : nat -> R) :
  (j0 < n)%nat -> (k0 < m)%nat ->
  A j0 = 1%R -> B k0 = 1%R ->
  sum_f_R0 (fun j => sum_f_R0 (fun k =>
    if andb (j =? j0) (k =? k0) then 0%R
    else A j * B k) (Nat.pred m)) (Nat.pred n)
  = (sum_f_R0 A (Nat.pred n)) * (sum_f_R0 B (Nat.pred m)) - 1%R.
Proof.
  intros Hj Hk HA HB.
  set (SA := sum_f_R0 A (Nat.pred n)).
  set (SB := sum_f_R0 B (Nat.pred m)).

  assert (Hj0_le : (j0 <= Nat.pred n)%nat) by (destruct n; [lia|]; unfold Nat.pred; lia).
  assert (Hk0_le : (k0 <= Nat.pred m)%nat) by (destruct m; [lia|]; unfold Nat.pred; lia).

  set (F := fun j k => A j * B k).
  set (D j k := if andb (j =? j0) (k =? k0) then F j0 k0 else 0).

  assert (Hrewrite : forall j k,
    (if andb (j =? j0) (k =? k0) then 0 else F j k) = F j k - D j k).
  {
    intros j k; unfold D.
    destruct (j =? j0) eqn:Hj_eq; destruct (k =? k0) eqn:Hk_eq; simpl; try ring.
    - apply Nat.eqb_eq in Hj_eq; apply Nat.eqb_eq in Hk_eq; subst; ring.
  }

  assert (H_inner_sub : forall j,
    sum_f_R0 (fun k => F j k - D j k) (Nat.pred m)
    = sum_f_R0 (F j) (Nat.pred m) - sum_f_R0 (D j) (Nat.pred m)).
  { intro j; apply sum_f_R0_sub. }

  assert (H_full : sum_f_R0 (fun j => sum_f_R0 (F j) (Nat.pred m)) (Nat.pred n) = SA * SB).
  {
    unfold F, SA, SB.
    rewrite (sum_f_R0_ext _ (fun j => A j * sum_f_R0 B (Nat.pred m)) (Nat.pred n)).
    - rewrite sum_f_R0_scal_r; reflexivity.
    - intro j; rewrite sum_f_R0_scal_l; reflexivity.
  }

  assert (H_Dsum : sum_f_R0 (fun j => sum_f_R0 (D j) (Nat.pred m)) (Nat.pred n) = 1%R).
  {
    unfold D.
    assert (H_Dj_eq : forall j, (j <= Nat.pred n)%nat ->
      sum_f_R0 (fun k => (if andb (j =? j0) (k =? k0) then F j0 k0 else 0)) (Nat.pred m)
      = (if j =? j0 then F j0 k0 else 0)).
    {
      intros j Hj_le.
      destruct (j =? j0) eqn:Hj_eq.
      - apply Nat.eqb_eq in Hj_eq; subst j.
        simpl.
        rewrite (sum_f_R0_single_eqb (Nat.pred m) k0 (fun _ => F j0 k0) Hk0_le).
        reflexivity.
      - simpl.
        rewrite sum_f_R0_zero.
        reflexivity.
    }
    rewrite (sum_f_R0_ext _ (fun j => (if j =? j0 then F j0 k0 else 0)) (Nat.pred n)).
    - rewrite (sum_f_R0_single_eqb (Nat.pred n) j0 (fun _ => F j0 k0) Hj0_le).
      unfold F; rewrite HA, HB; ring.
    - intro j; apply H_Dj_eq.
  }

  transitivity (sum_f_R0 (fun j => sum_f_R0 (fun k => F j k - D j k) (Nat.pred m)) (Nat.pred n)).
  - apply sum_f_R0_ext. intros j Hj_lt.
    apply sum_f_R0_ext. intros k Hk_lt.
    rewrite Hrewrite. reflexivity.
  - rewrite (sum_f_R0_ext _ (fun j => sum_f_R0 (F j) (Nat.pred m) - sum_f_R0 (D j) (Nat.pred m)) (Nat.pred n)).
    + rewrite sum_f_R0_sub.
      rewrite H_full, H_Dsum. ring.
    + intro j. intro Hj_le. apply H_inner_sub.
Qed.

(* 三重乘积行和分解 *)
Lemma triple_prod_row_sum_decomp n1 n2 n3 (i0 j0 k0 : nat) (d1 d2 d3 : nat -> nat -> R) :
  (i0 < n1)%nat -> (j0 < n2)%nat -> (k0 < n3)%nat ->
  (forall i, d1 i i = 1%R) -> (forall j, d2 j j = 1%R) -> (forall k, d3 k k = 1%R) ->
  sum_f_R0 (fun i => sum_f_R0 (fun j => sum_f_R0 (fun k =>
    if andb (andb (i =? i0) (j =? j0)) (k =? k0) then 0%R
    else d1 i0 i * d2 j0 j * d3 k0 k) (Nat.pred n3)) (Nat.pred n2)) (Nat.pred n1)
  = (sum_f_R0 (fun i => if i =? i0 then 1%R else d1 i0 i) (Nat.pred n1)) *
    (sum_f_R0 (fun j => if j =? j0 then 1%R else d2 j0 j) (Nat.pred n2)) *
    (sum_f_R0 (fun k => if k =? k0 then 1%R else d3 k0 k) (Nat.pred n3)) - 1%R.
Proof.
  intros Hi Hj Hk Hdiag1 Hdiag2 Hdiag3.
  set (S1 := sum_f_R0 (fun i => if i =? i0 then 1%R else d1 i0 i) (Nat.pred n1)).
  set (S2 := sum_f_R0 (fun j => if j =? j0 then 1%R else d2 j0 j) (Nat.pred n2)).
  set (S3 := sum_f_R0 (fun k => if k =? k0 then 1%R else d3 k0 k) (Nat.pred n3)).

  assert (H_S2_eq : S2 = sum_f_R0 (d2 j0) (Nat.pred n2)). {
    unfold S2.
    apply sum_f_R0_ext; intros j Hj_lt.
    destruct (Nat.eq_dec j j0) as [Heqj|Hneqj].
    - subst j; rewrite Nat.eqb_refl, Hdiag2; reflexivity.
    - apply Nat.eqb_neq in Hneqj; rewrite Hneqj; reflexivity.
  }
  assert (H_S3_eq : S3 = sum_f_R0 (d3 k0) (Nat.pred n3)). {
    unfold S3.
    apply sum_f_R0_ext; intros k Hk_lt.
    destruct (Nat.eq_dec k k0) as [Heqk|Hneqk].
    - subst k; rewrite Nat.eqb_refl, Hdiag3; reflexivity.
    - apply Nat.eqb_neq in Hneqk; rewrite Hneqk; reflexivity.
  }

  assert (Hinner : forall i : nat, (i < n1)%nat ->
    sum_f_R0 (fun j => sum_f_R0 (fun k =>
      if andb (andb (i =? i0) (j =? j0)) (k =? k0) then 0%R
      else d1 i0 i * d2 j0 j * d3 k0 k) (Nat.pred n3)) (Nat.pred n2)
    = (if i =? i0 then S2 * S3 - 1%R else d1 i0 i * (S2 * S3))). {
    intros i Hi_n.
    destruct (Nat.eq_dec i i0) as [Heq|Hne].
    - subst i.
      assert (H_left_eq :
        sum_f_R0 (fun j => sum_f_R0 (fun k =>
          if ((i0 =? i0) && (j =? j0) && (k =? k0))%bool
          then 0%R
          else d1 i0 i0 * d2 j0 j * d3 k0 k) (Nat.pred n3)) (Nat.pred n2)
        = sum_f_R0 (fun j => sum_f_R0 (fun k =>
          if ((j =? j0) && (k =? k0))%bool
          then 0%R
          else d2 j0 j * d3 k0 k) (Nat.pred n3)) (Nat.pred n2)).
      {
        apply sum_f_R0_ext; intros j Hj_lt.
        apply sum_f_R0_ext; intros k Hk_lt.
        rewrite Hdiag1.
        rewrite Nat.eqb_refl; simpl.
        rewrite Rmult_1_l.
        reflexivity.
      }
      rewrite H_left_eq.
      pose proof (double_sum_excl_point n2 n3 j0 k0 (d2 j0) (d3 k0) Hj Hk (Hdiag2 j0) (Hdiag3 k0)) as Hdoub.
      rewrite Hdoub.
      rewrite Nat.eqb_refl.
      rewrite H_S2_eq, H_S3_eq.
      reflexivity.
    - (* i ≠ i0 *)
      assert (H_andb_false : forall j k, andb (andb (i =? i0) (j =? j0)) (k =? k0) = false). {
        intros j k; rewrite (proj2 (Nat.eqb_neq i i0) Hne); reflexivity.
      }
      assert (Hinner_left : sum_f_R0 (fun j => sum_f_R0 (fun k =>
        if andb (andb (i =? i0) (j =? j0)) (k =? k0) then 0%R
        else d1 i0 i * d2 j0 j * d3 k0 k) (Nat.pred n3)) (Nat.pred n2)
        = sum_f_R0 (fun j => sum_f_R0 (fun k => d1 i0 i * d2 j0 j * d3 k0 k) (Nat.pred n3)) (Nat.pred n2)).
      {
        apply sum_f_R0_ext; intros j Hj_lt.
        apply sum_f_R0_ext; intros k Hk_lt.
        rewrite H_andb_false with (j := j) (k := k); reflexivity.
      }
      rewrite Hinner_left.
      assert (Hinner_extract : sum_f_R0 (fun j : nat => sum_f_R0 (fun k : nat => d1 i0 i * d2 j0 j * d3 k0 k) (Nat.pred n3)) (Nat.pred n2)
                             = (d1 i0 i) * sum_f_R0 (fun j : nat => sum_f_R0 (fun k : nat => d2 j0 j * d3 k0 k) (Nat.pred n3)) (Nat.pred n2)).
      {
        rewrite <- (sum_f_R0_scal_l (d1 i0 i) (fun j : nat => sum_f_R0 (fun k : nat => d2 j0 j * d3 k0 k) (Nat.pred n3)) (Nat.pred n2)).
        apply sum_f_R0_ext; intros j Hj_lt.
        replace (sum_f_R0 (fun k : nat => d1 i0 i * d2 j0 j * d3 k0 k) (Nat.pred n3))
          with (sum_f_R0 (fun k : nat => d1 i0 i * (d2 j0 j * d3 k0 k)) (Nat.pred n3)).
        - rewrite <- (sum_f_R0_scal_l (d1 i0 i) (fun k : nat => d2 j0 j * d3 k0 k) (Nat.pred n3)).
          reflexivity.
        - apply sum_f_R0_ext; intros k Hk_lt; ring.
      }
      rewrite Hinner_extract.
      assert (Hmult_distr : sum_f_R0 (fun j : nat => sum_f_R0 (fun k : nat => d2 j0 j * d3 k0 k) (Nat.pred n3)) (Nat.pred n2)
                           = S2 * S3).
      {
        rewrite H_S2_eq, H_S3_eq.
        replace (sum_f_R0 (fun j : nat => sum_f_R0 (fun k : nat => d2 j0 j * d3 k0 k) (Nat.pred n3)) (Nat.pred n2))
           with (sum_f_R0 (fun j : nat => d2 j0 j * sum_f_R0 (d3 k0) (Nat.pred n3)) (Nat.pred n2)).
        - rewrite (sum_f_R0_scal_r (sum_f_R0 (d3 k0) (Nat.pred n3)) (d2 j0) (Nat.pred n2)).
          ring.
        - apply sum_f_R0_ext; intros j Hj_lt.
          rewrite (sum_f_R0_scal_l (d2 j0 j) (d3 k0) (Nat.pred n3)); reflexivity.
      }
      rewrite Hmult_distr.
      rewrite (proj2 (Nat.eqb_neq i i0) Hne).
      reflexivity.
  }

  replace (sum_f_R0 (fun i : nat => sum_f_R0 (fun j : nat => sum_f_R0 (fun k : nat =>
    if andb (andb (i =? i0) (j =? j0)) (k =? k0) then 0%R
    else d1 i0 i * d2 j0 j * d3 k0 k) (Nat.pred n3)) (Nat.pred n2)) (Nat.pred n1))
    with (sum_f_R0 (fun i : nat => if i =? i0 then S2 * S3 - 1%R else d1 i0 i * (S2 * S3)) (Nat.pred n1)).
  - assert (Hi0_le : (i0 <= Nat.pred n1)%nat) by (destruct n1; [lia|lia]).
    rewrite (sum_f_R0_ext _ (fun i : nat => (S2 * S3) * (if i =? i0 then 1%R else d1 i0 i) - (if i =? i0 then 1%R else 0%R)) (Nat.pred n1)).
    + rewrite sum_f_R0_sub.
      rewrite (sum_f_R0_scal_l (S2 * S3) (fun i : nat => if i =? i0 then 1%R else d1 i0 i) (Nat.pred n1)).
      set (T := sum_f_R0 (fun i : nat => if i =? i0 then 1%R else d1 i0 i) (Nat.pred n1)).
      set (U := sum_f_R0 (fun i : nat => if i =? i0 then 1%R else 0%R) (Nat.pred n1)).
      assert (Heq_T : T = S1) by (unfold S1; reflexivity).
      rewrite Heq_T.
      assert (Hmul_comm : S2 * S3 * S1 = S1 * S2 * S3) by ring.
      rewrite Hmul_comm.
      assert (HU : U = 1%R). {
        unfold U.
        apply sum_f_R0_single_eqb with (f := fun _ : nat => 1%R); exact Hi0_le.
      }
      rewrite HU.
      reflexivity.
    + intros idx Hidx.
      destruct (idx =? i0) eqn:Heq; simpl; ring.
  - apply sum_f_R0_ext; intros idx Hidx.
    symmetry; apply Hinner; lia.
Qed.

(* 三维复数求和展平 *)
Lemma Csum_flatten_3d (n1 n2 n3 : nat) (Hn2 : (n2 > 0)%nat) (Hn3 : (n3 > 0)%nat)
  (F : nat -> nat -> nat -> ComplexNumbers.Complex) :
  Csum (fun idx : nat =>
    let i := (Nat.div idx (n2 * n3)%nat) in
    let rem := (Nat.modulo idx (n2 * n3)%nat) in
    let j := (Nat.div rem n3) in
    let k := (Nat.modulo rem n3) in
    F i j k) (n1 * n2 * n3)%nat
  = Csum (fun i => Csum (fun j => Csum (F i j) n3) n2) n1.
Proof.
  assert (Hprod : (n1 * n2 * n3 = n1 * (n2 * n3))%nat) by lia.
  rewrite Hprod.
  cbv zeta.
  rewrite (Csum_flatten n1 (n2 * n3) (fun i p => F i (p / n3)%nat (p mod n3)%nat)).
  apply Csum_ext; intros i Hi.
  rewrite (Csum_flatten n2 n3 (F i)).
  reflexivity.
Qed.

(* 三维实数求和展平 *)
Lemma sum_f_R0_flatten_3d (n1 n2 n3 : nat) (Hn1 : (n1 > 0)%nat) (Hn2 : (n2 > 0)%nat) (Hn3 : (n3 > 0)%nat)
  (f : nat -> nat -> nat -> R) :
  sum_f_R0 (fun idx : nat =>
    let i := Nat.div idx (n2 * n3)%nat in
    let rem := Nat.modulo idx (n2 * n3)%nat in
    let j := Nat.div rem n3 in
    let k := Nat.modulo rem n3 in
    f i j k) (n1 * n2 * n3 - 1)%nat
  = sum_f_R0 (fun i => sum_f_R0 (fun j => sum_f_R0 (f i j) (n3 - 1)%nat) (n2 - 1)%nat) (n1 - 1)%nat.
Proof.
  assert (Hn23_pos : (n2 * n3 > 0)%nat) by (apply Nat.mul_pos_pos; assumption).
  assert (Hprod_len : (n1 * n2 * n3 - 1 = n1 * (n2 * n3) - 1)%nat) by lia.
  rewrite Hprod_len.
  cbv zeta.
  rewrite (sum_f_R0_flatten n1 (n2 * n3) Hn1 Hn23_pos
            (fun i p => f i (Nat.div p n3) (Nat.modulo p n3))).
  apply sum_f_R0_ext; intros i Hi.
  rewrite (sum_f_R0_flatten n2 n3 Hn2 Hn3 (f i)).
  reflexivity.
Qed.

(* 根号2非零 *)
Lemma sqrt2_neq_0 : sqrt 2 <> 0.
Proof. apply Rgt_not_eq; apply sqrt_lt_R0_c; lra. Qed.

(* INR正性（n≥2） *)
Lemma INR_pos_ge2 : forall n, (n >= 2)%nat -> 0 < INR n.
Proof. intros n H; apply lt_0_INR; lia. Qed.

(* 共轭的共轭等于自身 *)
Lemma Cconj_conj (z : Complex) : Cconj (Cconj z) = z.
Proof. unfold Cconj; destruct z; simpl; f_equal; ring. Qed.

(* 无共轭版本的柯西-施瓦茨不等式 *)
Lemma CauchySchwarz_sum_f_R0_no_conj (A B : nat -> Complex) (N : nat) :
  Cnorm_sq (Csum (fun k => A k *c B k) N) <=
  sum_f_R0 (fun k => Cnorm_sq (A k)) N *
  sum_f_R0 (fun k => Cnorm_sq (B k)) N.
Proof.
  intros.
  pose (B' := fun k => Cconj (B k)).
  assert (Hsum_eq : Csum (fun k => A k *c B k) N = Csum (fun k => A k *c Cconj (B' k)) N). {
    apply Csum_ext; intros k _.
    unfold B'; rewrite Cconj_conj; reflexivity.
  }
  assert (Hnorm_eq : sum_f_R0 (fun k => Cnorm_sq (B k)) N =
                     sum_f_R0 (fun k => Cnorm_sq (B' k)) N). {
    apply sum_f_R0_ext; intros k _.
    unfold B'; rewrite Cnorm_sq_conj; reflexivity.
  }
  rewrite Hsum_eq.
  rewrite Hnorm_eq.
  apply CauchySchwarz_sum_f_R0 with (A := A) (B := B') (N := N).
Qed.



(* ===== 紧化手术：per-pair 紧致衰减界 1/(√C)^d ===== *)
Lemma decay_bound_tight_ij (seq : nat -> nat) (I : list nat) (C : nat)
  (HC : (C >= 2)%nat) (Hseq_ge2 : forall i, (seq i >= 2)%nat)
  (Hsparse : forall i, INR (seq (S i)) > INR C * INR (seq i))
  (Hsorted : Sorted Nat.lt I) (Hnodup : NoDup I)
  (i j : nat) (Hij : (i < j)%nat) (Hi_len : (i < length I)%nat) (Hj_len : (j < length I)%nat) :
  Cnorm (Csum (fun k : nat => psi (seq (nth i I 0%nat)) k *c Cconj (psi (seq (nth j I 0%nat)) k))
              ((seq (fold_right Nat.max 0%nat I) - 1)%nat))
  <= / ((sqrt (INR C)) ^ (Z.abs_nat (Z.of_nat i - Z.of_nat j))).
Proof.
  clear Hnodup.
  set (a := nth i I 0%nat).
  set (b := nth j I 0%nat).
  set (n1 := seq a). set (n2 := seq b).
  assert (Hn1_ge2 : (n1 >= 2)%nat) by (unfold n1; apply Hseq_ge2).
  assert (Hn2_ge2 : (n2 >= 2)%nat) by (unfold n2; apply Hseq_ge2).

  assert (Hstrict : forall a0 b0, (a0 < b0)%nat -> (seq a0 < seq b0)%nat). {
    intros a0 b0 Hlt. exact (seq_strict_growth_lt seq C a0 b0 HC Hsparse Hseq_ge2 Hlt).
  }
  assert (Hseq_mono : forall x y, (x <= y)%nat -> (seq x <= seq y)%nat). {
    intros x y Hle.
    destruct (Nat.eq_dec x y) as [Heq | Hne].
    - subst y; apply Nat.le_refl.
    - assert (Hlt : (x < y)%nat) by lia.
      apply Nat.lt_le_incl, Hstrict, Hlt.
  }
  assert (Hn1_lt_n2 : (n1 < n2)%nat). {
    apply Hstrict; exact (nth_sorted_strict_lt I i j Hsorted Hij Hi_len Hj_len).
  }

  set (Nmax := seq (fold_right Nat.max 0%nat I)).
  assert (HNmax_gt_n1_strict : (n1 < Nmax)%nat). {
    apply Nat.lt_le_trans with (m := n2).
    - exact Hn1_lt_n2.
    - apply (Nmax_upper_bound seq I j Hseq_mono Hj_len).
  }
  assert (HNmax_sub_ge_n1' : (n1 <= Nmax - 1)%nat) by lia.

  set (f := fun k : nat => psi n1 k *c Cconj (psi n2 k)).
  assert (Hf_zero_ge : forall k, (n1 <= k)%nat -> f k = C0). {
    intros k Hle.
    unfold f.
    rewrite psi_zero_for_ge_n with (n := n1) (k := k) by lia.
    rewrite Cmul_0_l; reflexivity.
  }

  assert (Hsum_eq : Csum f (Nmax - 1)%nat = Csum f n1). {
    apply Csum_trunc_tail with (M := n1) (N := (Nmax - 1)%nat).
    - exact HNmax_sub_ge_n1'.
    - intros k Hk. destruct Hk as [Hk1 Hk2]. apply Hf_zero_ge; exact Hk1.
  }

  replace (Csum (fun k : nat => psi (seq (nth i I 0%nat)) k *c Cconj (psi (seq (nth j I 0%nat)) k))
                ((seq (fold_right Nat.max 0%nat I) - 1)%nat))
    with (Csum f (Nmax - 1)%nat)
    by (unfold f, n1, n2, a, b, Nmax; reflexivity).
  rewrite Hsum_eq.

  assert (Hinner_bound : Cnorm (Csum f n1) <=
                         sqrt (INR n1 * INR n2) / (2 * (INR n2 - INR n1))). {
    apply inner_product_norm_bound_full; auto.
  }

  set (d := (j - i)%nat).
  assert (Hd_pos : (d >= 1)%nat) by (unfold d; lia).

  assert (Hint_exp : INR n2 >= (INR C) ^ d * INR n1). {
    exact (sparse_index_growth seq I C HC Hseq_ge2 Hsparse Hsorted i j Hij Hi_len Hj_len).
  }

  assert (H_main_bound : sqrt (INR n1 * INR n2) / (2 * (INR n2 - INR n1)) <=
                         / ((sqrt (INR C)) ^ d)). {
    exact (sqrt_div_bound C d n1 n2 HC Hd_pos Hint_exp).
  }

  assert (Heq_abs : Z.abs_nat (Z.of_nat i - Z.of_nat j) = d). {
    unfold d. destruct (Nat.lt_trichotomy i j) as [| [Heq|Hgt]]; try lia; auto.
  }
  rewrite Heq_abs.
  eapply Rle_trans; [exact Hinner_bound | exact H_main_bound].
Qed.

Theorem decay_bound_tight :
  forall (seq : nat -> nat) (I : list nat) (C : nat),
    (C >= 2)%nat ->
    (forall i, (seq i >= 2)%nat) ->
    (forall i, INR (seq (S i)) > INR C * INR (seq i)) ->
    NoDup I ->
    Sorted Nat.lt I ->
    forall (i j : nat), i <> j -> (i < length I)%nat -> (j < length I)%nat ->
    let vals := map seq I in
    let inner := Csum (fun k : nat => psi (nth i vals 0%nat) k *c Cconj (psi (nth j vals 0%nat) k))
                       ((seq (fold_right Nat.max 0%nat I) - 1)%nat) in
    Cnorm inner <= / ((sqrt (INR C)) ^ (Z.abs_nat (Z.of_nat i - Z.of_nat j))).
Proof.
  intros seq I C HC Hseq_ge2 Hsparse Hnodup Hsorted i j Hneq Hi_len Hj_len.
  cbv beta.
  set (vals := map seq I).
  set (inner := Csum (fun k : nat => psi (nth i vals 0%nat) k *c Cconj (psi (nth j vals 0%nat) k))
                     ((seq (fold_right Nat.max 0%nat I) - 1)%nat)).
  unfold inner.

  pose proof (H_nth_map nat nat seq I 0%nat 0%nat i Hi_len) as Hnthi.
  pose proof (H_nth_map nat nat seq I 0%nat 0%nat j Hj_len) as Hnthj.
  unfold vals in *; simpl in *.
  rewrite Hnthi, Hnthj.
  set (a := nth i I 0%nat).
  set (b := nth j I 0%nat).
  clear Hnthi Hnthj.

  assert (Hij_cases : (i < j)%nat \/ (j < i)%nat).
  { destruct (Nat.lt_trichotomy i j) as [H|[H|H]]; auto; exfalso; apply Hneq; exact H. }
  destruct Hij_cases as [Hij | Hji].
  - eapply decay_bound_tight_ij; eauto.
  - pose proof (Cnorm_Csum_conj_sym (fun k : nat => psi (seq a) k) (fun k : nat => psi (seq b) k)
                                    ((seq (fold_right Nat.max 0%nat I) - 1)%nat)) as Hsym.
    rewrite Hsym.
    pose proof (decay_bound_tight_ij seq I C HC Hseq_ge2 Hsparse Hsorted Hnodup j i Hji Hj_len Hi_len) as Hbound.
    simpl in Hbound.
    replace (Z.abs_nat (Z.of_nat i - Z.of_nat j)) with (Z.abs_nat (Z.of_nat j - Z.of_nat i)).
    2: {
      replace (Z.of_nat i - Z.of_nat j)%Z with (- (Z.of_nat j - Z.of_nat i))%Z by ring.
      rewrite Z_abs_nat_opp.
      reflexivity.
    }
    exact Hbound.
Qed.



(* ===== 紧化手术：双序紧致衰减（截断桥接） ===== *)
Lemma inner_decay_bound_tight :
  forall (seq : nat -> nat) (I : list nat) (C : nat)
    (Hc_ge2 : (C >= 2)%nat)
    (Hge2 : forall i, (seq i >= 2)%nat)
    (Hsparse : forall i, INR (seq (S i)) > INR C * INR (seq i))
    (Hdup : NoDup I) (Hsorted : Sorted Nat.lt I)
    (vals : list nat) (Hvals_eq : vals = map seq I)
    (maxIdx : nat) (HmaxIdx_eq : maxIdx = fold_right Init.Nat.max 0%nat I)
    (Hmax_bound : forall a, In a I -> (seq a <= seq maxIdx)%nat)
    (M : nat) (HM_eq : M = S (seq maxIdx))
    (i j : nat) (Hneq : i <> j) (Hi : (i < length I)%nat) (Hj : (j < length I)%nat),
  let inner_norm i j := Cnorm (Csum (fun k => psi (nth i vals 0%nat) k *c Cconj (psi (nth j vals 0%nat) k)) (M - 1)) in
  inner_norm i j <= / ((sqrt (INR C)) ^ (Z.abs_nat (Z.of_nat i - Z.of_nat j))).
Proof.
  intros seq I C Hc_ge2 Hge2 Hsparse Hdup Hsorted vals Hvals_eq maxIdx HmaxIdx_eq Hmax_bound M HM_eq i j Hneq Hi Hj.
  intro inner_norm.
  unfold inner_norm.
  rewrite HM_eq.
  replace (S (seq maxIdx) - 1)%nat with (seq maxIdx) by lia.
  pose proof (Hge2 maxIdx) as Hmax_ge2.
  assert (Hseq_strict_inc : forall a b, (a < b)%nat -> (seq a < seq b)%nat). {
    intros a0 b0 Hlt. eapply (seq_strict_growth_lt seq C a0 b0 Hc_ge2 Hsparse Hge2 Hlt).
  }
  pose proof (decay_bound_tight seq I C Hc_ge2 Hge2 Hsparse Hdup Hsorted i j Hneq Hi Hj) as Hdec.
  simpl in Hdec.
  set (g := fun k : nat => psi (nth i vals 0%nat) k *c Cconj (psi (nth j vals 0%nat) k)).
  assert (Htrunc : Csum g (seq maxIdx) = Csum g (seq maxIdx - 1)). {
    destruct (seq maxIdx) as [|m] eqn:Hseqmax; [lia|].
    simpl (Csum g (S m)).
    replace (S m - 1)%nat with m by lia.
    assert (Hmax_in_I : In maxIdx I). {
      subst maxIdx. apply max_fold_right_in. destruct I; [simpl in Hi; lia | discriminate].
    }
    assert (Hmax_is_max : forall a, In a I -> (a <= maxIdx)%nat). {
      subst maxIdx; intros a Hin; apply fold_right_max_ge; exact Hin.
    }
    assert (H_i_or_j_lt_max : (nth i I 0%nat < maxIdx)%nat \/ (nth j I 0%nat < maxIdx)%nat). {
      destruct (Nat.lt_ge_cases (nth i I 0%nat) maxIdx) as [Hlt_i|Hge_i].
      - left; exact Hlt_i.
      - assert (Heq_i : nth i I 0%nat = maxIdx). {
          apply Nat.le_antisymm.
          - apply Hmax_is_max; apply nth_In; exact Hi.
          - exact Hge_i.
        }
        destruct (Nat.lt_ge_cases (nth j I 0%nat) maxIdx) as [Hlt_j|Hge_j].
        + right; exact Hlt_j.
        + exfalso.
          assert (Heq_j : nth j I 0%nat = maxIdx). {
            apply Nat.le_antisymm.
            - apply Hmax_is_max; apply nth_In; exact Hj.
            - exact Hge_j.
          }
          apply (NoDup_nth_neq_std I 0%nat i j Hdup Hi Hj Hneq).
          rewrite Heq_i, Heq_j; reflexivity.
    }
    assert (H_seq_i_or_j_lt_Sm : (seq (nth i I 0%nat) < S m)%nat \/ (seq (nth j I 0%nat) < S m)%nat). {
      destruct H_i_or_j_lt_max as [Hlt | Hlt].
      - left. apply Hseq_strict_inc in Hlt. rewrite Hseqmax in Hlt. exact Hlt.
      - right. apply Hseq_strict_inc in Hlt. rewrite Hseqmax in Hlt. exact Hlt.
    }
    assert (H_seq_i_or_j_le_m : (seq (nth i I 0%nat) <= m)%nat \/ (seq (nth j I 0%nat) <= m)%nat). {
      destruct H_seq_i_or_j_lt_Sm as [Hlt | Hlt]; [left|right]; lia.
    }
    assert (Hlast : g m = C0). {
      unfold g.
      rewrite Hvals_eq.
      pose proof (H_nth_map nat nat seq I 0%nat (0%nat : nat) i Hi) as Hni.
      pose proof (H_nth_map nat nat seq I 0%nat (0%nat : nat) j Hj) as Hnj.
      rewrite Hni, Hnj.
      destruct H_seq_i_or_j_le_m as [Hle | Hle].
      - rewrite (psi_ge_n_zero (seq (nth i I 0%nat)) m Hle). rewrite Cmul_0_l. reflexivity.
      - rewrite (psi_ge_n_zero (seq (nth j I 0%nat)) m Hle). rewrite Cconj_0. rewrite Cmul_0_r. reflexivity.
    }
    rewrite Hlast, Cadd_0_r. reflexivity.
  }
  rewrite Htrunc.
  replace (seq maxIdx) with (seq (fold_right Init.Nat.max 0%nat I)) by (rewrite HmaxIdx_eq; reflexivity).
  unfold g.
  rewrite Hvals_eq.
  exact Hdec.
Qed.

(* ===== 紧化手术：主定理紧致版 1±2K(C) ===== *)
Lemma psi_off_abs_bound_tight :
  forall (seq : nat -> nat) (I : list nat) (vals : list nat) (maxIdx : nat) (M : nat)
         (coeffs : list Complex) (n : nat) (C : nat)
         (Hge2 : forall i, (seq i >= 2)%nat)
         (Hvals_eq : vals = map seq I)
         (HM_eq : M = S (seq maxIdx))
         (Hmax_bound : forall a, In a I -> (seq a <= seq maxIdx)%nat)
         (HCgt2 : (C > 2)%nat)
         (Hn_pos : (n > 0)%nat),
    let inner i j := Csum (fun k => psi (nth i vals 0%nat) k *c Cconj (psi (nth j vals 0%nat) k)) (M - 1) in
    let inner_norm i j := Cnorm (inner i j) in
    (forall i j, 0 <= inner_norm i j) ->
    (forall i j, inner_norm i j = inner_norm j i) ->
    (forall i, (i < n)%nat -> sum_f_R0 (fun j => if eq_nat_dec i j then 0%R else inner_norm i j) (n-1) <= 2 * K (INR C)) ->
    let S0 := sum_f_R0 (fun i => Cnorm_sq (nth i coeffs C0)) (n-1) in
    let off := sum_f_R0 (fun i => sum_f_R0 (fun j =>
                 if eq_nat_dec i j then 0%R
                 else re (nth i coeffs C0 *c Cconj (nth j coeffs C0) *c inner i j)) (n-1)) (n-1) in
    Rabs off <= 2 * K (INR C) * S0.
Proof.
  intros; subst vals M.
  rename H into Hpos_inner_norm, H0 into Hsym_inner_norm, H1 into Hrow_sum.
  set (a i := Cnorm (nth i coeffs C0)).
  assert (Cnorm_sq_ge_0 : forall z : Complex, 0 <= Cnorm_sq z). {
    intros [x y]; unfold Cnorm_sq; apply Rplus_le_le_0_compat; apply Rle_0_sqr.
  }
  assert (Cnorm_ge_0 : forall z : Complex, 0 <= Cnorm z). {
    intro z; unfold Cnorm; apply sqrt_pos.
  }
  assert (Ha_sq_eq : forall i, (a i)^2 = Cnorm_sq (nth i coeffs C0)). {
    intros i; unfold a, Cnorm.
    replace ((sqrt (Cnorm_sq (nth i coeffs C0))) ^ 2)
      with (Rsqr (sqrt (Cnorm_sq (nth i coeffs C0)))) by (unfold Rsqr; ring).
    rewrite Rsqr_sqrt; [reflexivity | apply Cnorm_sq_ge_0].
  }
  assert (Rabs_re_le_Cnorm : forall z : Complex, Rabs (re z) <= Cnorm z). {
    intros [x y]; unfold re, Cnorm, Cnorm_sq; simpl.
    rewrite <- (sqrt_Rsqr_abs x) at 1.
    apply sqrt_le_1_c.
    - apply Rle_0_sqr.
    - apply Rplus_le_le_0_compat; apply Rle_0_sqr.
    - unfold Rsqr; nra.
  }
  assert (Rabs_sum_f_R0 : forall (f : nat -> R) N, Rabs (sum_f_R0 f N) <= sum_f_R0 (fun i => Rabs (f i)) N). {
    induction N; simpl.
    - apply Rle_refl.
    - eapply Rle_trans; [apply Rabs_triang|].
      apply Rplus_le_compat; [apply IHN|apply Rle_refl].
  }
  assert (Habs_single : forall i j, Rabs (re (nth i coeffs C0 *c Cconj (nth j coeffs C0) *c inner i j)) <= a i * a j * inner_norm i j). {
    intros i j; unfold a, inner_norm.
    eapply Rle_trans; [apply Rabs_re_le_Cnorm|].
    rewrite Cnorm_mult, (Cnorm_mult _ (Cconj _)), Cnorm_conj_eq.
    apply Rle_refl.
  }
  assert (Hest : Rabs off <= sum_f_R0 (fun i => sum_f_R0 (fun j =>
    if eq_nat_dec i j then 0%R else a i * a j * inner_norm i j) (n-1)) (n-1)).
  { eapply Rle_trans; [apply Rabs_sum_f_R0|].
    apply sum_f_R0_le_compat; intros i Hi.
    eapply Rle_trans; [apply Rabs_sum_f_R0|].
    apply sum_f_R0_le_compat; intros j Hj.
    unfold off.
    destruct (eq_nat_dec i j) as [Heq|Hneq].
    - subst; simpl; rewrite Rabs_R0. lra.
    - apply Habs_single. }
  set (U i j := if eq_nat_dec i j then 0%R else inner_norm i j).
  assert (U_nonneg : forall i j, 0 <= U i j).
  { intros; unfold U; destruct (eq_nat_dec i j); [lra|auto]. }
  assert (U_sym : forall i j, U i j = U j i).
  { intros; unfold U; destruct (eq_nat_dec i j), (eq_nat_dec j i); congruence || auto; try contradiction. }
  assert (HrowU : forall i, (i < n)%nat -> sum_f_R0 (U i) (n-1) <= 2 * K (INR C)).
  { intros i Hi; unfold U; apply Hrow_sum; exact Hi. }
  assert (Hquad : sum_f_R0 (fun i => sum_f_R0 (fun j => a i * a j * U i j) (n-1)) (n-1) <=
                  (2 * K (INR C)) * sum_f_R0 (fun i => (a i)^2) (n-1)).
  {
    assert (H_amgm : forall i j, a i * a j <= ((a i)^2 + (a j)^2) / 2). {
      intros i j;
      assert (Hsq : 0 <= Rsqr (a i - a j)) by apply Rle_0_sqr;
      unfold Rsqr in Hsq; lra. }
    assert (Haux : sum_f_R0 (fun i => sum_f_R0 (fun j => a i * a j * U i j) (n-1)) (n-1) <=
                   sum_f_R0 (fun i => sum_f_R0 (fun j => ((a i)^2 + (a j)^2) / 2 * U i j) (n-1)) (n-1)).
    { apply sum_f_R0_le_compat; intros i Hi; apply sum_f_R0_le_compat; intros j Hj.
      apply Rmult_le_compat_r; [apply U_nonneg | apply H_amgm]. }
    assert (Heq : sum_f_R0 (fun i => sum_f_R0 (fun j => ((a i)^2 + (a j)^2) / 2 * U i j) (n-1)) (n-1) =
                  sum_f_R0 (fun i => (a i)^2 * sum_f_R0 (U i) (n-1)) (n-1)).
    {
      set (S := sum_f_R0 (fun i => (a i)^2 * sum_f_R0 (U i) (n-1)) (n-1)).
      assert (Hswap : sum_f_R0 (fun i => sum_f_R0 (fun j => (a j)^2 * U i j) (n-1)) (n-1) = S). {
        rewrite (sum_f_R0_swap (n-1) (n-1) (fun i j => (a j)^2 * U i j)).
        apply sum_f_R0_ext; intros j Hj.
        rewrite <- sum_f_R0_scal_l.
        apply sum_f_R0_ext; intros i Hi.
        rewrite U_sym; reflexivity.
      }
      rewrite (sum_f_R0_ext _ (fun i => 1/2 * sum_f_R0 (fun j => (a i)^2 * U i j) (n-1) +
                                  1/2 * sum_f_R0 (fun j => (a j)^2 * U i j) (n-1)) (n-1)).
      - rewrite sum_f_R0_add.
        rewrite !sum_f_R0_scal_l.
        set (A := sum_f_R0 (fun i => sum_f_R0 (fun j => (a i)^2 * U i j) (n-1)) (n-1)).
        set (B := sum_f_R0 (fun i => sum_f_R0 (fun j => (a j)^2 * U i j) (n-1)) (n-1)).
        assert (A_eq_S : A = S). {
          unfold A, S.
          apply sum_f_R0_ext; intros i Hi.
          rewrite <- sum_f_R0_scal_l; reflexivity.
        }
        assert (B_eq_S : B = S). {
          unfold B; rewrite Hswap; reflexivity.
        }
        rewrite A_eq_S, B_eq_S.
        lra.
      - intros i Hi.
        transitivity (sum_f_R0 (fun j => (a i)^2 / 2 * U i j + (a j)^2 / 2 * U i j) (n-1)).
        + apply sum_f_R0_ext; intros j Hj.
          unfold Rdiv.
          field; lra.
        + rewrite sum_f_R0_add.
          rewrite (sum_f_R0_ext (fun j => a i ^ 2 / 2 * U i j)
                                (fun j => 1/2 * (a i ^ 2 * U i j)) (n-1)).
          * rewrite (sum_f_R0_ext (fun j => a j ^ 2 / 2 * U i j)
                                  (fun j => 1/2 * (a j ^ 2 * U i j)) (n-1)).
            -- rewrite !sum_f_R0_scal_l; ring.
            -- intros j Hj; unfold Rdiv; ring.
          * intros j Hj; unfold Rdiv; ring.
    }
    eapply Rle_trans; [apply Haux | rewrite Heq].
    assert (H_mul : sum_f_R0 (fun i => (a i)^2 * sum_f_R0 (U i) (n-1)) (n-1) <=
                   (2 * K (INR C)) * sum_f_R0 (fun i => (a i)^2) (n-1)).
    {
      apply Rle_trans with (sum_f_R0 (fun i => (a i)^2 * (2 * K (INR C))) (n-1)).
      - apply sum_f_R0_le_compat; intros i Hi.
        apply Rmult_le_compat_l.
        + rewrite Ha_sq_eq; apply Cnorm_sq_ge_0.
        + apply HrowU; lia.
      - assert (H_eq_const : sum_f_R0 (fun i => (a i)^2 * (2 * K (INR C))) (n-1)
                           = (2 * K (INR C)) * sum_f_R0 (fun i => (a i)^2) (n-1)).
        {
          rewrite <- (sum_f_R0_scal_l (2 * K (INR C)) (fun i => (a i)^2) (n-1)).
          apply sum_f_R0_ext; intros; ring.
        }
        rewrite H_eq_const; apply Rle_refl.
    }
    exact H_mul.
  }
  unfold S0.
  assert (Heq_S0 : sum_f_R0 (fun i : nat => Cnorm_sq (nth i coeffs C0)) (n - 1) =
                   sum_f_R0 (fun i : nat => a i ^ 2) (n - 1)).
  {
    apply sum_f_R0_ext; intros i Hi.
    rewrite Ha_sq_eq; reflexivity.
  }
  rewrite Heq_S0.
  assert (Htrans : sum_f_R0 (fun i => sum_f_R0 (fun j =>
      if eq_nat_dec i j then 0%R else a i * a j * inner_norm i j) (n-1)) (n-1)
      <= 2 * K (INR C) * sum_f_R0 (fun i => (a i)^2) (n-1)).
  {
    apply Rle_trans with (sum_f_R0 (fun i => sum_f_R0 (fun j => a i * a j * U i j) (n-1)) (n-1)).
    - apply sum_f_R0_le_compat; intros i Hi; apply sum_f_R0_le_compat; intros j Hj.
      unfold U.
      destruct (eq_nat_dec i j) as [Heq|Hne].
      + subst; simpl; rewrite Rmult_0_r; lra.
      + simpl; apply Rle_refl.
    - exact Hquad.
  }
  eapply Rle_trans; [apply Hest | exact Htrans].
Qed.

Theorem psi_unconditional_basis_tight :
  forall (seq : nat -> nat)
         (Hge2 : forall i, (seq i >= 2)%nat)
         (Hinc : forall i, (seq i < seq (S i))%nat)
         (C : nat)
         (HCgt2 : (C > 2)%nat)
         (Hsparse : forall i, (INR (seq (S i)) > INR C * INR (seq i))%R)
         (I : list nat)
         (coeffs : list Complex)
         (Hdup : NoDup I)
         (Hsorted : Sorted Nat.lt I)
         (Hlen : length I = length coeffs),
    let n := length I in
    let vals := map seq I in
    let F := fun k => Csum (fun idx => nth idx coeffs C0 *c psi (nth idx vals 0%nat) k) n in
    let maxIdx := fold_right Init.Nat.max 0%nat I in
    let M := S (seq maxIdx) in
    let S := sum_f_R0 (fun i => Cnorm_sq (nth i coeffs C0)) (n - 1) in
    ((1 - 2 * K (INR C)) * S <= l2_norm_sq F (M - 1) <= (1 + 2 * K (INR C)) * S)%R.
Proof.
  intros seq Hge2 Hinc C HCgt2 Hsparse I coeffs Hdup Hsorted Hlen.
  set (n := length I).
  set (vals := map seq I).
  set (Fk := fun k => Csum (fun i => nth i coeffs C0 *c psi (nth i vals 0%nat) k) n).
  set (maxIdx := fold_right Init.Nat.max 0%nat I).
  set (M := S (seq maxIdx)).
  set (S0 := sum_f_R0 (fun i => Cnorm_sq (nth i coeffs C0)) (n - 1)).

  destruct (seq_strictly_increasing seq Hinc) as [Hstrict_inc Hinj].

  assert (Hseq_mono : forall a b, (a <= b)%nat -> (seq a <= seq b)%nat). {
    intros a b Hle; destruct (Nat.eq_dec a b) as [-> | Hne];
      [apply Nat.le_refl | apply Nat.lt_le_incl, Hstrict_inc; lia].
  }
  assert (Hmax_bound : forall a, In a I -> (seq a <= seq maxIdx)%nat). {
    intros a Ha; apply Hseq_mono; eapply fold_right_max_ge; eauto.
  }
  assert (Hvals_nodup : NoDup vals) by (apply (NoDup_vals seq I Hinj Hdup)).
  assert (Hvals_ge2 : forall v, In v vals -> (v >= 2)%nat) by (apply vals_ge2; auto).

  set (inner i j := Csum (fun k => psi (nth i vals 0%nat) k *c Cconj (psi (nth j vals 0%nat) k)) (M - 1)).
  set (inner_norm i j := Cnorm (inner i j)).

  assert (inner_norm_nonneg : forall i j, 0 <= inner_norm i j). {
    intros; unfold inner_norm; apply Cnorm_ge_0.
  }

  assert (Hc_ge2 : (C >= 2)%nat) by lia.
  assert (Hlen_vals : length vals = n) by (unfold vals; rewrite length_map; reflexivity).

  assert (Hdecay : forall i j, i <> j -> (i < n)%nat -> (j < n)%nat ->
    Cnorm (Csum (fun k => psi (nth i vals 0%nat) k *c Cconj (psi (nth j vals 0%nat) k)) (M - 1))
    <= / ((sqrt (INR C)) ^ (Z.abs_nat (Z.of_nat i - Z.of_nat j)))).
  {
    intros i j Hneq Hi Hj.
    assert (Hi_len : (i < length I)%nat) by (unfold n in Hi; exact Hi).
    assert (Hj_len : (j < length I)%nat) by (unfold n in Hj; exact Hj).
    assert (Hvals_eq : vals = map seq I) by (unfold vals; reflexivity).
    assert (HmaxIdx_eq : maxIdx = fold_right Init.Nat.max 0%nat I) by (unfold maxIdx; reflexivity).
    assert (HM_eq : M = S (seq maxIdx)) by (unfold M; reflexivity).
    exact (@inner_decay_bound_tight seq I C Hc_ge2 Hge2 Hsparse Hdup Hsorted
          vals Hvals_eq maxIdx HmaxIdx_eq Hmax_bound M HM_eq i j Hneq Hi_len Hj_len).
  }

  assert (Hinner_sym : forall i j, inner_norm i j = inner_norm j i). {
    intros i j; unfold inner_norm, inner.
    set (Sij := Csum (fun k => psi (nth i vals 0%nat) k *c Cconj (psi (nth j vals 0%nat) k)) (M - 1)).
    set (Sji := Csum (fun k => psi (nth j vals 0%nat) k *c Cconj (psi (nth i vals 0%nat) k)) (M - 1)).
    enough (Cconj Sij = Sji) as Hconj.
    - rewrite <- (Cnorm_conj_eq Sij); rewrite Hconj; reflexivity.
    - subst Sij Sji.
      rewrite Cconj_Csum.
      generalize (M - 1)%nat as N.
      induction N; simpl.
      + reflexivity.
      + f_equal; auto.
        rewrite Cconj_mul_conj_eq; reflexivity.
  }

  assert (Hrow_sum : forall i, (i < n)%nat ->
    sum_f_R0 (fun j => if eq_nat_dec i j then 0%R else inner_norm i j) (n - 1) <= 2 * K (INR C)).
  {
    intros i Hi.
    unfold inner_norm.
    apply (row_sum_bound_K n vals M C Hvals_ge2 Hlen_vals Hdecay HCgt2 i Hi).
  }

  assert (Hlen_coeffs : length coeffs = n) by (unfold n; rewrite Hlen; reflexivity).
  assert (HMpos : (M > 0)%nat) by (unfold M; lia).

  destruct n as [|n'] eqn:Hn.
  {
    unfold n in Hn, Hlen_coeffs.
    assert (HI_nil : I = []) by (destruct I; [reflexivity | simpl in Hn; lia]).
    assert (Hcoeffs_nil : coeffs = []) by (destruct coeffs; [reflexivity | simpl in Hlen_coeffs; lia]).
    subst I coeffs.
    unfold Fk, S0.
    assert (HmaxIdx0 : maxIdx = 0%nat) by (unfold maxIdx; simpl; reflexivity).
    assert (HM_eq0 : (M - 1)%nat = seq 0%nat). {
      unfold M; rewrite HmaxIdx0; lia.
    }
    change (S (seq maxIdx) - 1)%nat with (M - 1)%nat.
    rewrite HM_eq0.
    simpl (Csum (fun _ : nat => C0 *c _) 0).
    unfold l2_norm_sq.
    unfold Cnorm_sq; simpl.
    rewrite !Rsqr_0, Rplus_0_r.
    rewrite sum_f_R0_zero.
    rewrite !Rmult_0_r.
    split; apply Rle_refl.
  }

  subst n.
  assert (Hn_pos' : (S n' > 0)%nat) by lia.
  assert (HM_eq_val : M = S (seq maxIdx)) by (unfold M; reflexivity).
  assert (Hvals_eq_val : vals = map seq I) by (unfold vals; reflexivity).

  pose proof (psi_l2_norm_sq_eq seq I vals maxIdx M coeffs (S n')
                Hge2 Hvals_eq_val Hlen_coeffs Hlen_vals HM_eq_val HMpos Hmax_bound Hn_pos')
    as HL2_eq.
  unfold Fk, S0 in *.
  set (off := sum_f_R0 (fun i => sum_f_R0 (fun j =>
    if eq_nat_dec i j then 0%R
    else re (nth i coeffs C0 *c Cconj (nth j coeffs C0) *c inner i j)) (S n' - 1)) (S n' - 1)).

  unfold M in HL2_eq.
  assert (Htemp : l2_norm_sq (fun k => Csum (fun i => nth i coeffs C0 *c psi (nth i vals 0%nat) k) (S n'))
                            (S (seq maxIdx) - 1) = S0 + off). {
    rewrite HL2_eq.
    unfold off, inner.
    reflexivity.
  }
  rewrite Htemp.

  assert (Hrow_sum' : forall i : nat, (i < S n')%nat ->
    sum_f_R0 (fun j : nat => if eq_nat_dec i j then 0%R else inner_norm i j) (S n' - 1) <= 2 * K (INR C)).
  { exact Hrow_sum. }

  pose proof (psi_off_abs_bound_tight seq I vals maxIdx M coeffs (S n') C
                Hge2 Hvals_eq_val HM_eq_val Hmax_bound HCgt2 Hn_pos'
                inner_norm_nonneg Hinner_sym Hrow_sum')
    as Hoff_bound.

  assert (Hoff_abs : Rabs off <= 2 * K (INR C) * S0). {
    unfold off, S0.
    exact Hoff_bound.
  }

  assert (Hoff_range : - (2 * K (INR C) * S0) <= off <= 2 * K (INR C) * S0). {
    destruct (Rle_or_lt off 0) as [Hoff_le0 | Hoff_gt0].
    - rewrite Rabs_left1 in Hoff_abs by exact Hoff_le0.
      split; lra.
    - rewrite Rabs_right in Hoff_abs by lra.
      split; lra.
  }
  destruct Hoff_range as [Hoff_low Hoff_high].

  fold S0.
  split.
  - lra.
  - lra.
Qed.



End ExtendedTheorems.
