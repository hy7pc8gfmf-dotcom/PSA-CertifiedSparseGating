(* 拆分自 Riemann_Hypothesis_Proof_Framework.v（复分析证明库 v6.0）*)
(* 库: ca_basis  原文行区间: 25795-26928  机械拆分，未改动内容 *)

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

Require Import ca_base ca_algebra ca_primes ca_complex_analysis ca_fourier ca_zeta_scaffold ca_trig ca_gamma ca_taylor ca_zeta_axioms ca_complex_log ca_complex_foundation ca_log_bounds ca_independence ca_prime_power.

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

(* ====================================================
   模块：UnconditionalBasis
   目的：基于稀疏递增正整数序列构造 ℓ² 的无条件基
   依赖：independent.phi_linear_independent（泛化版）
   ==================================================== *)

Require Import Stdlib.Reals.Reals.
Require Import Stdlib.Lists.List.
Import ComplexNumbers.
Import independent.
Import independent'.
Import PrimePowerIndependent.

Local Open Scope complex_scope.
Local Open Scope R_scope.

Module UnconditionalBasis.

(* ---------- 辅助定义 ---------- *)

Definition Cof_real (r : R) : Complex := r +i 0.

Definition phi (n : nat) (k : nat) : Complex :=
  if Nat.ltb k n then Cexp (0 +i (2 * PI * INR k / INR n)) else C0.

Definition psi (n : nat) (k : nat) : Complex :=
  Cof_real (1 / sqrt (INR n)) *c phi n k.

Definition l2_norm_sq (f : nat -> Complex) (N : nat) : R :=
  sum_f_R0 (fun k => Cnorm_sq (f k)) N.

(* ---------- 辅助引理 ---------- *)

(** 当索引不小于质数时，特征序列为零 *)
Lemma phi_ge_n_zero : forall n k, (k >= n)%nat -> phi n k = C0.
Proof.
  intros n k H. unfold phi.
  destruct (Nat.ltb_spec k n) as [Hlt | Hge].
  - lia.  (* 如果 k < n，与 H 矛盾 *)
  - reflexivity.
Qed.

(** 索引小于质数时，特征序列的模平方为 1 *)
Lemma Cnorm_sq_phi : forall n k, (k < n)%nat -> Cnorm_sq (phi n k) = 1.
Proof.
  intros n k H. unfold phi.
  rewrite (proj2 (Nat.ltb_lt k n) H). simpl.
  unfold Cexp; simpl.
  rewrite exp_0, Rmult_1_l, Rmult_1_l.
  unfold Cnorm_sq; simpl.
  rewrite Rplus_comm.
  rewrite sin2_cos2.
  reflexivity.
Qed.

(** 1 减去非 1 的复数不为零 *)
Lemma C1_minus_z_nonzero : forall z, z <> C1 -> C1 -c z <> C0.
Proof.
  intros z H Hc.
  apply H.
  destruct z as [x y].
  unfold C1, C0 in Hc; simpl in Hc.
  injection Hc as Hre Him.
  assert (x = 1) by lra.
  assert (y = 0) by lra.
  rewrite H0, H1.
  unfold C1; reflexivity.
Qed.

(** 非零复数的模平方不为零 *)
Lemma Cnorm_sq_neq_0 : forall z, z <> C0 -> Cnorm_sq z <> 0.
Proof.
  intros z H Hsq.
  apply H.
  apply Cnorm_sq_eq_0.
  auto.
Qed.

(** 零项求和为零 *)
Lemma Csum_0 : forall f, Csum f 0 = C0.
Proof. reflexivity. Qed.

(** 复数乘法的左单位元 *)
Lemma Cmul_1_l : forall z, C1 *c z = z.
Proof.
  destruct z as [x y]; unfold C1, Cmul; simpl.
  rewrite Rmult_1_l, Rmult_0_l, Rminus_0_r.
  rewrite Rmult_1_l, Rmult_0_l, Rplus_0_r.
  reflexivity.
Qed.

(** 复数乘法的右单位元 *)
Lemma Cmul_1_r : forall z, z *c C1 = z.
Proof.
  destruct z as [x y]; unfold C1, Cmul; simpl.
  rewrite Rmult_1_r, Rmult_0_r, Rminus_0_r.
  rewrite Rmult_0_r, Rmult_1_r, Rplus_0_l.
  reflexivity.
Qed.

(** 复数幂与自身可交换 *)
Lemma Cpow_comm : forall z n, z *c (z ^ n) = (z ^ n) *c z.
Proof.
  induction n; simpl.
  - rewrite Cmul_1_r, Cmul_1_l. reflexivity.
  - rewrite IHn.
    rewrite <- Cmul_assoc.
    rewrite IHn.
    reflexivity.
Qed.

(** 复数幂的递归定义（右乘） *)
Lemma Cpow_S_r : forall z n, (z ^ S n)%C = (z ^ n)%C *c z.
Proof.
  intros z n. simpl. rewrite Cpow_comm. reflexivity.
Qed.
(** 复数乘法的交换律 *)
Lemma Cmul_comm : forall a b, a *c b = b *c a.
Proof.
  intros [a1 a2] [b1 b2]; unfold Cmul; simpl.
  rewrite Rmult_comm, Rmult_comm; f_equal; ring.
Qed.

(** 复数加法的右分配律（通常已存在）*)
Lemma Cmul_add_distr_r : forall a b c, (a +c b) *c c = a *c c +c b *c c.
Proof.
  intros; unfold Cadd, Cmul; simpl.
  destruct a, b, c; simpl; f_equal; ring.
Qed.

(** 复数乘法的左分配律（由交换律和右分配律推出）*)
Lemma Cmul_add_distr_l : forall a b c, a *c (b +c c) = a *c b +c a *c c.
Proof.
  intros; rewrite (Cmul_comm a (b +c c)), Cmul_add_distr_r,
          !(Cmul_comm a b), !(Cmul_comm a c); reflexivity.
Qed.

(** 减法定义为加法的相反数 *)
Lemma Csub_def : forall a b, a -c b = a +c (-c b).
Proof.
  intros [a1 a2] [b1 b2].
  unfold Csub, Cadd; simpl.
  f_equal; ring.
Qed.

(** 自身相减为零 *)
Lemma Csub_self : forall a, a -c a = C0.
Proof.
  intros [x y]; unfold Csub; simpl.
  rewrite Rminus_diag, Rminus_diag.
  reflexivity.
Qed.

(** 部分和的递归定义（若 Csum 是 Fixpoint，simpl 会自动展开，但有时需要显式引理）*)
Lemma Csum_S : forall f n, Csum f (S n) = Csum f n +c f n.
Proof. reflexivity. Qed.

(** 零次幂为 1 *)
Lemma Cpow_0 : forall z, (z ^ 0)%C = C1.
Proof. reflexivity. Qed.

(* 相反数加法消去律 *)
Lemma Cadd_opp_r : forall a, a +c (-c a) = C0.
Proof.
  destruct a as [x y]; unfold Cadd; simpl.
  apply Complex_eq; simpl; ring.
Qed.

(** 等比数列部分和公式的辅助引理 *)
Lemma Csum_geometric_aux : forall z n,
  (C1 -c z) *c Csum (fun i => (z ^ i)%C) n = C1 -c (z ^ n)%C.
Proof.
  intros z n.
  induction n as [|n IH].
  - rewrite Csum_0, Cmul_0_r, Cpow_0, Csub_self; reflexivity.
  - rewrite Csum_S, Cmul_add_distr_l, IH, Cpow_S_r, Cmul_sub_distr_r,
      Cmul_1_l, (Cmul_comm z (z^n)), <- Cpow_S_r.
    (* 目标: C1 -c z^n +c (z^n -c z^(S n)) = C1 -c z^(S n) *)
    rewrite (Csub_def C1 (z^n)), (Csub_def (z^n) (z^(S n))).
    apply Complex_eq; simpl; ring.
Qed.

(* 复数右逆元性质 *)
Lemma Cinv_mult_r : forall x (H : Cnorm_sq x <> 0), x *c Cinv x H = C1.
Proof.
  intros [a b] H.
  unfold Cinv, Cmul, C1; simpl.
  unfold Cnorm_sq; simpl.
  set (n := a*a + b*b).
  assert (Hn : n <> 0) by (unfold n; apply H).
  apply Complex_eq; simpl; unfold Rsqr in *; field; auto.
Qed.

(* 几何级数求和公式 *)
Lemma Csum_geometric : forall (z : Complex) (n : nat) (Hz : z <> C1),
  Csum (fun i => (z ^ i)%C) n =
    (C1 -c (z ^ n)%C) *c Cinv (C1 -c z) (Cnorm_sq_neq_0 (C1 -c z) (C1_minus_z_nonzero z Hz)).
Proof.
  intros z n Hz.
  rewrite (Cmul_comm (C1 -c (z ^ n)%C) (Cinv (C1 -c z) _)).
  rewrite <- Csum_geometric_aux.
  rewrite <- Cmul_assoc.
  rewrite (Cmul_comm (Cinv (C1 -c z) _) (C1 -c z)).
  rewrite (Cinv_mult_r (C1 -c z) (Cnorm_sq_neq_0 (C1 -c z) (C1_minus_z_nonzero z Hz))).
  rewrite Cmul_1_l.
  reflexivity.
Qed.

(* 实数嵌入加法保持 *)
Lemma Cof_real_add : forall a b, Cof_real (a + b) = Cof_real a +c Cof_real b.
Proof.
  intros; unfold Cof_real, Cadd; simpl.
  apply Complex_eq; simpl; ring.
Qed.

(* 正交归一基的自内积恒等式 *)
Lemma Csum_orthonormal_self : forall (n : nat), (n > 0)%nat ->
  Csum (fun i => psi n i *c Cconj (psi n i)) n = C1.
Proof.
  intros n Hn_pos. unfold psi.
  set (c := Cof_real (1 / sqrt (INR n))).

  assert (forall (a : Complex) (f : nat -> Complex) (m : nat),
          Csum (fun i => a *c f i) m = a *c Csum f m) as Csum_scal_l.
  { induction m as [|m IH]; intros.
    - simpl; rewrite Cmul_0_r; reflexivity.
    - simpl. rewrite IH.
      rewrite (Cmul_add_distr_l a (Csum f m) (f m)).
      reflexivity. }

  assert (forall (a : Complex) (f : nat -> Complex) (m : nat),
          Csum (fun i => f i *c a) m = Csum f m *c a) as Csum_scal_r.
  { induction m as [|m IH]; intros.
    - simpl; rewrite Cmul_0_l; reflexivity.
    - simpl. rewrite IH.
      rewrite (Cmul_add_distr_r (Csum f m) (f m) a).
      reflexivity. }

  assert (Hmul : forall i, c *c phi n i *c Cconj (c *c phi n i) =
                         (c *c Cconj c) *c (phi n i *c Cconj (phi n i))).
  { intros i. unfold c. simpl.
    destruct (phi n i) as [x y]. unfold Cconj, Cmul, Cof_real; simpl.
    apply Complex_eq; simpl; ring. }

  assert (Heq_sum : forall m, (m <= n)%nat ->
                    Csum (fun i => c *c phi n i *c Cconj (c *c phi n i)) m =
                    Csum (fun i => (c *c Cconj c) *c (phi n i *c Cconj (phi n i))) m).
  { induction m as [|m IH]; intros Hle.
    - simpl; reflexivity.
    - simpl. rewrite IH; [| lia]. rewrite Hmul. reflexivity. }
  rewrite Heq_sum; [| lia].

  rewrite Csum_scal_l.

  assert (Hnorm : forall i, (i < n)%nat -> phi n i *c Cconj (phi n i) = C1).
  { intros i Hlt. unfold phi.
    rewrite (proj2 (Nat.ltb_lt i n) Hlt).
    set (theta := 2 * PI * INR i / INR n).
    replace (Cexp (0 +i theta) *c Cconj (Cexp (0 +i theta))) with C1.
    - reflexivity.
    - unfold Cexp, Cconj, Cmul; simpl.
      rewrite exp_0, Rmult_1_l, Rmult_1_l.
      apply Complex_eq; simpl.
      + replace (cos theta * cos theta - sin theta * - sin theta)
           with (sin theta * sin theta + cos theta * cos theta) by ring.
        replace (sin theta * sin theta + cos theta * cos theta)
           with (Rsqr (sin theta) + Rsqr (cos theta)) by (unfold Rsqr; ring).
        rewrite sin2_cos2. reflexivity.
      + replace (cos theta * - sin theta + sin theta * cos theta) with 0 by ring.
        reflexivity. }

  assert (Heq_inner: Csum (fun i => phi n i *c Cconj (phi n i)) n = Csum (fun _ => C1) n).
  {
    rewrite Csum_equiv_PrimeEmbedding, Csum_equiv_PrimeEmbedding.
    apply Csum_ext.
    intros i Hi.
    apply Hnorm.
    exact Hi.
  }

  assert (forall m, Csum (fun _ => C1) m = Cof_real (INR m)) as H_const.
  { induction m as [|m IH]; simpl.
    - reflexivity.
    - rewrite IH. destruct m; [apply Complex_eq; simpl; ring | rewrite S_INR; apply Complex_eq; simpl; ring]. }

  rewrite Heq_inner, H_const.

  assert (H_conj_mul_norm : forall z : Complex, z *c Cconj z = Cof_real (Cnorm_sq z)).
  {
    intros z.
    destruct z as [x y].
    apply Complex_eq.
    - unfold Cconj, Cmul, Cnorm_sq, Cof_real, Rsqr; simpl. lra.
    - unfold Cconj, Cmul, Cnorm_sq, Cof_real; simpl. lra.
  }

  assert (Hn_posR : 0 < INR n) by (apply lt_0_INR; lia).
  assert (Hsqrt_eq : sqrt (INR n) * sqrt (INR n) = INR n)
    by (apply sqrt_sqrt; apply Rlt_le; exact Hn_posR).
  assert (H_INR_n_nonzero : INR n <> 0)
    by (apply Rgt_not_eq; exact Hn_posR).
  assert (H_sqrt_nonzero : sqrt (INR n) <> 0)
    by (apply Rgt_not_eq; apply sqrt_lt_R0_c; exact Hn_posR).

  assert (Hc_conj : c *c Cconj c = Cof_real (1 / INR n)).
  {
    rewrite H_conj_mul_norm.
    unfold c, Cnorm_sq, Cof_real; simpl.
    unfold Rsqr.
    rewrite Rmult_0_r, Rplus_0_r.
    apply Complex_eq; simpl.
    - unfold Rdiv.
      rewrite !Rmult_1_l.
      rewrite <- (Rinv_mult (sqrt (INR n)) (sqrt (INR n))) by auto.
      rewrite Hsqrt_eq.
      reflexivity.
    - reflexivity.
  }

  assert (H_Cof_real_mul : forall r1 r2 : R, Cof_real r1 *c Cof_real r2 = Cof_real (r1 * r2)).
  {
    intros r1 r2; unfold Cof_real, Cmul; simpl.
    apply Complex_eq; simpl; ring.
  }

  rewrite Hc_conj, H_Cof_real_mul.
  replace (1 / INR n * INR n) with 1.
  - unfold C1, Cof_real; simpl; apply Complex_eq; simpl; ring.
  - field; auto.
Qed.

(* 列表元素索引存在 *)
Lemma in_nth_index : forall (l : list nat) (x : nat) (d : nat),
  In x l -> exists i, (i < length l)%nat /\ nth i l d = x.
Proof.
  induction l as [|h t IH]; intros x d H; [inversion H |].
  simpl in H. destruct H as [Heq|Hin].
  - subst. exists 0%nat. split.
    + simpl. apply Nat.lt_0_succ.
    + reflexivity.
  - destruct (IH x d Hin) as [i [Hi Hnth]].
    exists (S i). split.
    + simpl. lia.
    + simpl. exact Hnth.
Qed.

(* 自然数列表最大值索引存在 *)
Lemma max_nat_index_exists : forall (l : list nat),
  l <> nil ->
  exists i, (i < length l)%nat /\
    (forall j, (j < length l)%nat -> (nth j l 0%nat <= nth i l 0%nat)%nat).
Proof.
  intros l Hnonnil.
  set (max_val := fold_right Init.Nat.max 0%nat l).
  assert (In max_val l) as H_in_max by (apply max_fold_right_in; auto).
  destruct (in_nth_index l max_val 0%nat H_in_max) as [i [Hi Hnth]].
  exists i. split; [exact Hi |].
  intros j Hj.
  apply (Nat.le_trans _ max_val _).
  - apply fold_right_max_ge with (l := l) (x := nth j l 0%nat); apply nth_In; assumption.
  - rewrite Hnth. apply Nat.le_refl.
Qed.

(* 最大值严格不等式（基于 NoDup） *)
Lemma max_nat_strict_ineq : forall (l : list nat) (i0 : nat),
  NoDup l ->
  (i0 < length l)%nat ->
  (forall j, (j < length l)%nat -> (nth j l 0%nat <= nth i0 l 0%nat)%nat) ->
  forall j, j <> i0 -> (j < length l)%nat -> (nth j l 0%nat < nth i0 l 0%nat)%nat.
Proof.
  intros l i0 Hdup Hi0 Hmax j Hneq Hj.
  specialize (Hmax j Hj).
  destruct (Nat.lt_ge_cases (nth j l 0%nat) (nth i0 l 0%nat)) as [Hlt|Hge].
  - exact Hlt.
  - assert (Heq : nth j l 0%nat = nth i0 l 0%nat) by lia.
    exfalso.
    assert (j = i0).
    { apply NoDup_nth with (A := nat) (l := l) (i := j) (j := i0) (d := 0%nat); auto. }
    contradiction.
Qed.

(* 对于非最大项，phi 在 k = M-1 处为零 *)
Lemma term_zero_for_others_general : forall (ns : list nat) (coeffs : list Complex) (i0 : nat),
  (forall j, (j < length ns)%nat -> (nth j ns 0%nat <= nth i0 ns 0%nat)%nat) ->
  (forall j, j <> i0 -> (j < length ns)%nat -> (nth j ns 0%nat < nth i0 ns 0%nat)%nat) ->
  let M := nth i0 ns 0%nat in
  let k0 := (M - 1)%nat in
  forall j, (j < length ns)%nat -> j <> i0 ->
    nth j coeffs C0 *c phi (nth j ns 0%nat) k0 = C0.
Proof.
  intros ns coeffs i0 Hle Hlt M k0 j Hj Hneq.
  unfold phi.
  assert (Hlt_j : (nth j ns 0%nat < M)%nat) by (apply Hlt; auto).
  apply Nat.lt_le_pred in Hlt_j.
  assert (Hk0_ge : (k0 >= nth j ns 0%nat)%nat).
  { apply Nat.le_trans with (Nat.pred M); [exact Hlt_j | unfold k0; lia]. }
  assert (Hfalse : (k0 <? nth j ns 0%nat)%nat = false).
  { apply Nat.ltb_ge. assumption. }
  rewrite Hfalse.
  rewrite Cmul_0_r.
  reflexivity.
Qed.

(* phi n (n-1) 非零（当 n >= 2） *)
Lemma phi_pred_nonzero : forall n, (n >= 2)%nat -> phi n (n-1) <> C0.
Proof.
  intros n Hn.
  unfold phi.
  assert (Hlt : (n-1 < n)%nat) by lia.
  rewrite (proj2 (Nat.ltb_lt (n-1) n) Hlt).
  apply Cexp_neq_0.
Qed.

Local Open Scope nat_scope.

(* 约化系统方程保持（通用） *)
Lemma reduced_system_equation_general : forall (ns : list nat) (coeffs : list Complex) (i0 : nat)
  (Hlen : length ns = length coeffs)
  (Hi0 : (i0 < length ns)%nat)
  (Hne_last : (i0 < Nat.pred (length ns))%nat)
  (Hc0 : nth i0 coeffs C0 = C0)
  (Heq : forall k, Csum (fun i => nth i coeffs C0 *c phi (nth i ns 0%nat) k) (Nat.pred (length ns)) = C0),
  forall k,
    Csum (fun i =>
            let idx := if (i <? i0)%nat then i else (S i)%nat in
            nth idx coeffs C0 *c phi (nth idx ns 0%nat) k)
         (Nat.pred (length (firstn i0 ns ++ skipn (S i0) ns))) = C0.
Proof.
  intros ns coeffs i0 Hlen Hi0 Hne_last Hc0 Heq k.
  set (m := length ns).
  set (ns' := firstn i0 ns ++ skipn (S i0) ns).
  set (coeffs' := firstn i0 coeffs ++ skipn (S i0) coeffs).

  assert (Hlen_ns' : length ns' = pred m).
  { unfold ns'. rewrite length_app, length_firstn, length_skipn. lia. }

  change (Nat.pred (length (firstn i0 ns ++ skipn (S i0) ns))) with (Nat.pred (length ns')).
  rewrite Hlen_ns'.
  set (N := (m - 2)%nat).
  assert (Heq_bound : Nat.pred (pred m) = N) by (unfold N; lia).
  rewrite Heq_bound.
  assert (Hi0_bound : (i0 <= N)%nat) by (unfold N; lia).

  set (f := fun i => nth i coeffs C0 *c phi (nth i ns 0%nat) k).

  replace N with (i0 + (N - i0))%nat by lia.
  rewrite (Csum_split' (fun i => let idx := if (i <? i0)%nat then i else S i in
                                 nth idx coeffs C0 *c phi (nth idx ns 0%nat) k) i0 (N - i0)).

  (* 前 i0 项相等 *)
  assert (H1 : Csum (fun i => nth i coeffs' C0 *c phi (nth i ns' 0%nat) k) i0 =
               Csum f i0).
  { apply Csum_ext'; intros j Hj.
    unfold coeffs', ns'.
    rewrite (nth_app_left _ (firstn i0 coeffs) (skipn (S i0) coeffs) j C0);
      [| rewrite length_firstn; rewrite min_l by (rewrite <- Hlen; lia); lia].
    rewrite (nth_firstn_lt _ i0 coeffs j C0); [| lia].
    rewrite (nth_app_left _ (firstn i0 ns) (skipn (S i0) ns) j 0%nat);
      [| rewrite length_firstn; rewrite min_l by lia; lia].
    rewrite (nth_firstn_lt _ i0 ns j 0%nat); [| lia].
    reflexivity. }

  (* 后缀项相等 *)
  assert (H2 : Csum (fun j => nth (i0 + j) coeffs' C0 *c phi (nth (i0 + j) ns' 0%nat) k) (N - i0) =
               Csum (fun j => nth (i0 + S j) coeffs C0 *c phi (nth (i0 + S j) ns 0%nat) k) (N - i0)).
  { apply Csum_ext'; intros j Hj.
    unfold coeffs', ns'.
    assert (Hlen_firstn_c : length (firstn i0 coeffs) = i0).
    { rewrite length_firstn; rewrite min_l by (rewrite <- Hlen; lia); lia. }
    assert (Hlen_firstn_n : length (firstn i0 ns) = i0).
    { rewrite length_firstn; rewrite min_l by lia; lia. }
    rewrite (nth_app_right _ (firstn i0 coeffs) (skipn (S i0) coeffs) (i0 + j) C0);
      [| rewrite Hlen_firstn_c; lia].
    rewrite nth_skipn.
    rewrite Hlen_firstn_c.
    replace (i0 + j - length (firstn i0 coeffs)) with j by lia.
    rewrite (nth_app_right _ (firstn i0 ns) (skipn (S i0) ns) (i0 + j) 0%nat);
      [| rewrite Hlen_firstn_n; lia].
    rewrite nth_skipn.
    rewrite Hlen_firstn_n.
    replace (i0 + j - length (firstn i0 ns)) with j by lia.
    replace (i0 + j - i0) with j by lia.
    replace (S i0 + j) with (i0 + S j) by lia.
    reflexivity. }

  (* 化简目标中的条件表达式 *)
  assert (Hfirst_target : Csum (fun i => let idx := if i <? i0 then i else S i in nth idx coeffs C0 *c phi (nth idx ns 0) k) i0 = Csum f i0).
  { apply Csum_ext'; intros i Hi. destruct (Nat.ltb_spec i i0); [reflexivity | lia]. }

  assert (Hsecond_target : Csum (fun i => let idx := if (i0 + i) <? i0 then (i0 + i) else S (i0 + i) in nth idx coeffs C0 *c phi (nth idx ns 0) k) (N - i0) = Csum (fun j => f (i0 + S j)) (N - i0)).
  { apply Csum_ext'; intros i Hi. destruct (Nat.ltb_spec (i0 + i) i0); [lia |]. simpl. replace (S (i0 + i)) with (i0 + S i) by lia. reflexivity. }

  rewrite Hfirst_target, Hsecond_target.

  assert (Hf0 : f i0 = C0) by (unfold f; rewrite Hc0; apply Cmul_0_l).
  assert (Hpred : pred m = i0 + S (N - i0)) by lia.

  (* 证明左侧等于 Csum f (pred m) *)
  assert (Heq_eq: Csum f (pred m) = Csum f i0 +c Csum (fun j => f (i0 + S j)) (N - i0)).
  { rewrite Hpred.
    rewrite (Csum_split' f i0 (S (N - i0))).
    replace (S (N - i0)) with (1 + (N - i0))%nat by lia.
    rewrite (Csum_split' (fun i => f (i0 + i)) 1 (N - i0)).
    assert (Htemp: Csum (fun i => f (i0 + i)) 1 = f i0).
    { unfold Csum; simpl. rewrite Nat.add_0_r. rewrite Cadd_0_l. reflexivity. }
    rewrite Htemp.
    rewrite Hf0.
    rewrite Cadd_0_l.
    reflexivity. }

  rewrite <- Heq_eq.
  apply Heq.
Qed.

Local Close Scope nat_scope.

(* 约化列表保持元素 ≥ 2 的性质（使用自然数比较） *)
Lemma reduced_list_ge2 : forall (ns : list nat) (i0 : nat),
  (forall n, In n ns -> (n >= 2)%nat) ->
  forall n, In n (firstn i0 ns ++ skipn (S i0) ns) -> (n >= 2)%nat.
Proof.
  intros ns i0 Hge2 n Hin.
  apply in_app_iff in Hin as [Hin1 | Hin2].
  - apply Hge2. apply In_firstn with (n:=i0) in Hin1; exact Hin1.
  - apply Hge2. apply In_skipn with (n:=S i0) in Hin2; exact Hin2.
Qed.

(* 从 ns 中删除第 i0 个元素后，剩余元素仍然满足 ≥ 2 的条件 *)
Lemma In_removelist_ge2 : forall (ns : list nat) (i0 : nat),
  (forall n, In n ns -> (n >= 2)%nat) ->
  forall n, In n (firstn i0 ns ++ skipn (S i0) ns) -> (n >= 2)%nat.
Proof.
  intros ns i0 Hge2 n Hin.
  apply in_app_iff in Hin as [Hin1 | Hin2].
  - (* 元素在前缀 firstn i0 ns 中 *)
    apply Hge2.
    apply In_firstn with (n := i0) in Hin1.
    exact Hin1.
  - (* 元素在后缀 skipn (S i0) ns 中 *)
    apply Hge2.
    apply In_skipn with (n := S i0) in Hin2.
    exact Hin2.
Qed.

(* 删除列表第i0个元素后，索引小于i0时nth结果与原列表一致 *)
Lemma nth_remove_at_lt : forall (A : Type) (l : list A) (i0 j : nat) (d : A),
  (j < i0)%nat ->
  nth j (firstn i0 l ++ skipn (S i0) l) d = nth j l d.
Proof.
  intros A l i0 j d Hlt.
  destruct (lt_dec j (length (firstn i0 l))) as [Hj_lt_firstn | Hj_ge_firstn].
  - rewrite nth_app_left with (l1 := firstn i0 l) (l2 := skipn (S i0) l) by auto.
    apply nth_firstn_lt; auto.
  - assert (Hlen_firstn : length (firstn i0 l) = min i0 (length l)) by apply length_firstn.
    destruct (le_ge_dec i0 (length l)) as [Hle | Hge'].
    + exfalso.
      rewrite Hlen_firstn in Hj_ge_firstn.
      rewrite min_l in Hj_ge_firstn by auto.
      lia.
    + assert (Hmin_eq : min i0 (length l) = length l).
      { apply min_r. auto. }
      assert (Hlen_firstn_eq : length (firstn i0 l) = length l).
      { rewrite Hlen_firstn, Hmin_eq. reflexivity. }
      assert (Hj_ge_len_l : ~ (j < length l)%nat).
      { rewrite Hlen_firstn_eq in Hj_ge_firstn. exact Hj_ge_firstn. }
      assert (Hj_ge_len : (j >= length l)%nat).
      { apply Nat.nlt_ge. exact Hj_ge_len_l. }
      assert (H_Si0_ge_len : (S i0 >= length l)%nat).
      { lia. }
      assert (H_skipn_general : forall (A' : Type) (l' : list A') (n : nat),
        (n >= length l')%nat -> skipn n l' = nil).
      { intros A' l'. induction l' as [|h t IH].
        - intros n H. simpl. destruct n; reflexivity.
        - intros n H. destruct n as [|n'].
          + exfalso. simpl in H. lia.
          + simpl in H. simpl. apply IH. lia. }
      assert (H2 : skipn (S i0) l = nil).
      { apply H_skipn_general with (A' := A) (l' := l) (n := S i0). exact H_Si0_ge_len. }
      assert (Hskip_len : length (skipn (S i0) l) = 0%nat).
      { rewrite H2. reflexivity. }
      assert (Happ_len : length (firstn i0 l ++ skipn (S i0) l) = length l).
      { rewrite length_app, Hlen_firstn_eq.
        rewrite Hskip_len. lia. }
      assert (Hleft_eq_d : nth j (firstn i0 l ++ skipn (S i0) l) d = d).
      { apply nth_overflow. rewrite Happ_len. exact Hj_ge_len. }
      assert (Hright_eq_d : nth j l d = d).
      { apply nth_overflow. exact Hj_ge_len. }
      rewrite Hleft_eq_d, Hright_eq_d.
      reflexivity.
Qed.

(* 删除列表第i0个元素后，索引大于等于i0时nth对应原列表S j位置 *)
Lemma nth_remove_at_ge : forall (A : Type) (l : list A) (i0 j : nat) (d : A),
  (j >= i0)%nat ->
  nth j (firstn i0 l ++ skipn (S i0) l) d = nth (S j) l d.
Proof.
  intros A l i0 j d Hge.
  destruct (le_ge_dec i0 (length l)) as [Hle | Hgt].
  - (* 情况1：i0 <= 列表长度，合法删除元素的场景 *)
    assert (Hlen_l1 : length (firstn i0 l) = i0).
    { rewrite length_firstn. apply Nat.min_l. assumption. }
    assert (Hge_len_l1 : (j >= length (firstn i0 l))%nat).
    { rewrite Hlen_l1. exact Hge. }
    (* 正确应用列表拼接右段索引引理，明确指定参数 *)
    rewrite (nth_app_right A (firstn i0 l) (skipn (S i0) l) j d Hge_len_l1).
    rewrite Hlen_l1.
    (* 应用skipn的索引映射引理 *)
    rewrite nth_skipn.
    (* 自然数算术等价性证明，处理索引偏移 *)
    f_equal.
    lia.
  - (* 情况2：i0 > 列表长度，删除操作后列表与原表一致，索引均越界 *)
    assert (H1 : (i0 >= length l)%nat) by exact Hgt.
    (* 先证明一个小引理：对任意n:nat，firstn n nil = nil *)
    assert (H_firstn_nil : forall (n : nat), firstn n (@nil A) = @nil A).
    {
      intros n.
      destruct n; simpl; reflexivity.
    }
    (* 再证明通用引理：对任意n >= length l，firstn n l = l *)
    assert (H_aux : forall (l' : list A), forall (n : nat), (n >= length l')%nat -> firstn n l' = l').
    {
      Local Open Scope nat_scope.
      induction l' as [|h t IH].
      - (* 基例：l' = nil *)
        intros n Hn.
        apply H_firstn_nil.
      - (* 归纳步：l' = h :: t *)
        intros n Hn.
        simpl in Hn.
        destruct n as [|n'].
        + lia. (* n = 0 不可能满足 n >= S (length t) *)
        + simpl.
          f_equal.
          apply IH.
          lia.
    }
    (* 应用通用引理得到 firstn i0 l = l *)
    assert (Hfirstn_full : firstn i0 l = l).
    { apply H_aux. exact H1. }
    (* 证明通用引理：对任意n >= length l，skipn n l = nil *)
    assert (H_skipn_aux : forall (l' : list A) (n : nat), (n >= length l')%nat -> skipn n l' = @nil A).
    {
      Local Open Scope nat_scope.
      induction l' as [|h t IH].
      - (* 基例：l' = nil *)
        intros n Hn. simpl. destruct n; reflexivity.
      - (* 归纳步：l' = h :: t *)
        intros n Hn.
        simpl in Hn.
        destruct n as [|n'].
        + lia. (* n = 0 不可能满足 n >= S (length t) *)
        + simpl.
          apply IH.
          lia.
    }
    (* 证明当i0 >= length l时，S i0 > length l，故skipn (S i0) l = nil *)
    assert (H2 : (S i0 > length l)%nat) by lia.
    assert (H2' : (S i0 >= length l)%nat) by lia.
    assert (Hskipn_nil : skipn (S i0) l = nil).
    { apply H_skipn_aux. exact H2'. }
    (* 重写目标 *)
    rewrite Hfirstn_full, Hskipn_nil.
    rewrite app_nil_r.
    (* 越界索引的nth恒返回默认值d，故左右两边相等 *)
    assert (Hj_overflow : (j >= length l)%nat) by lia.
    assert (HSj_overflow : (S j >= length l)%nat) by lia.
    (* 将 >= 转换为 <= 以匹配 nth_overflow 的参数类型 *)
    assert (Hj' : (length l <= j)%nat) by lia.
    assert (HSj' : (length l <= S j)%nat) by lia.
    (* 应用 nth_overflow 证明两边都等于 d，注意参数顺序：列表、索引、默认值、证明 *)
    assert (H_eq1 : nth j l d = d).
    { apply nth_overflow. exact Hj'. }
    assert (H_eq2 : nth (S j) l d = d).
    { apply nth_overflow. exact HSj'. }
    rewrite H_eq1, H_eq2.
    reflexivity.
Qed.

(* 删除指定索引后复数求和的拆分恒等式 *)
Lemma Csum_remove_at : forall (f : nat -> Complex) (m i0 : nat),
  (i0 < m)%nat ->
  Csum (fun j => if Nat.ltb j i0 then f j else f (S j)) (Nat.pred m) +c f i0 = Csum f m.
Proof.
  intros f m i0 Hi0.
  induction m as [| m' IH].
  - (* 基例：m = 0，i0 < 0 不存在合法情况 *)
    exfalso. lia.
  - (* 归纳步：m = S m'，前提 i0 < S m' *)
    destruct (Nat.eq_dec i0 m') as [Heq | Hne].
    + (* 分支1：i0 = m'，即i0是当前m的前一个值 *)
      subst i0. simpl Nat.pred.
      (* 证明求和范围内函数与f完全一致 *)
      assert (H_eq_on_domain : forall j : nat, (j < m')%nat -> 
        (if Nat.ltb j m' then f j else f (S j)) = f j).
      {
        intros j Hj.
        assert (Hlt_true : (Nat.ltb j m') = true) by (apply Nat.ltb_lt; exact Hj).
        rewrite Hlt_true. reflexivity.
      }
      (* 在当前上下文中直接证明本地Csum的外延性引理 *)
      assert (H_local_Csum_ext : forall (g h : nat -> Complex) (n : nat),
        (forall k : nat, k < n -> g k = h k) -> Csum g n = Csum h n).
      {
        intros g h n Hext.
        induction n as [| k IHk].
        - simpl. reflexivity.
        - simpl. rewrite IHk.
          + f_equal. apply Hext. lia.
          + intros j Hj. apply Hext. lia.
      }
      (* 应用本地外延引理完成目标转换 *)
      assert (H_sum_eq : Csum (fun j : nat => if Nat.ltb j m' then f j else f (S j)) m' = Csum f m').
      {
        apply H_local_Csum_ext.
        exact H_eq_on_domain.
      }
      (* 直接利用Csum的定义化简 *)
      rewrite H_sum_eq.
      simpl.
      reflexivity.
    + (* 分支2：i0 ≠ m'，结合前提得 i0 < m' *)
      assert (Hlt_i0 : (i0 < m')%nat) by lia.
      assert (Hm'_pos : (0 < m')%nat) by lia.
      assert (Hm'_eq : m' = S (Nat.pred m')) by (destruct m'; [lia | simpl; lia]).
      set (G := fun j : nat => if Nat.ltb j i0 then f j else f (S j)).
      (* 拆分 Csum G m' 为前 pred m' 项加末项 *)
      assert (H_csum_split : Csum G m' = Csum G (Nat.pred m') +c G (Nat.pred m')).
      { rewrite Hm'_eq. simpl. reflexivity. }
      (* 证明末项 G (Nat.pred m') 等于 f m' *)
      assert (H_G_eq : G (Nat.pred m') = f m').
      {
        unfold G.
        assert (H_ge : (Nat.pred m' >= i0)%nat) by lia.
        assert (Htb_false : (Nat.ltb (Nat.pred m') i0) = false) by (apply Nat.ltb_ge; exact H_ge).
        rewrite Htb_false. rewrite Hm'_eq. simpl. reflexivity.
      }
      (* 【核心修复】先简化目标中的 pred (S m') 为 m'，再逐步 rewrite *)
      assert (H_pred_S : Nat.pred (S m') = m') by (simpl; lia).
      rewrite H_pred_S.
      (* 现在目标为 Csum G m' +c f i0 = Csum f (S m')，可以应用 H_csum_split *)
      rewrite H_csum_split.
      rewrite H_G_eq.
      (* 简化右边的 Csum f (S m') *)
      simpl.
      (* 应用复数加法结合律与交换律调整顺序 *)
      rewrite Cadd_assoc.
      rewrite (Cadd_comm (f m') (f i0)).
      rewrite <- Cadd_assoc.
      (* 应用归纳假设 *)
      assert (H_IH : Csum G (Nat.pred m') +c f i0 = Csum f m') by (apply IH; exact Hlt_i0).
      rewrite H_IH.
      reflexivity.
Qed.

(* 主定理：通用自然数特征序列的线性无关性 *)
Theorem phi_linear_independent_general :
  forall (ns : list nat) (coeffs : list Complex),
    (forall n, In n ns -> (n >= 2)%nat) ->
    NoDup ns ->
    length ns = length coeffs ->
    (forall k, Csum (fun i => nth i coeffs C0 *c phi (nth i ns 0%nat) k) (length ns) = C0) ->
    forall i, (i < length ns)%nat -> nth i coeffs C0 = C0.
Proof.
  assert (H_main : forall (n : nat),
    forall (ns : list nat) (coeffs : list Complex),
      length ns = n ->
      (forall n0, In n0 ns -> (n0 >= 2)%nat) ->
      NoDup ns ->
      length ns = length coeffs ->
      (forall k, Csum (fun i => nth i coeffs C0 *c phi (nth i ns 0%nat) k) (length ns) = C0) ->
      forall i, (i < length ns)%nat -> nth i coeffs C0 = C0).
  {
    intros n.
    induction n as [n IH] using lt_wf_ind.
    intros ns coeffs Hlen_n Hge2 Hdup Hlen Heq i Hi.

    destruct n as [|m'].
    - simpl in Hlen_n; subst; simpl in Hi; lia.
    - assert (Hnonnil : ns <> nil) by (intro H; rewrite H in Hlen_n; simpl in Hlen_n; lia).

      destruct (max_nat_index_exists ns Hnonnil) as [i0 [Hi0_lt_m Hmax_le]].
      assert (Hmax_strict : forall j, j <> i0 -> (j < length ns)%nat ->
                (nth j ns 0%nat < nth i0 ns 0%nat)%nat).
      { apply max_nat_strict_ineq with (l := ns) (i0 := i0); auto. }

      set (M := nth i0 ns 0%nat).
      assert (Hge3 : (M >= 2)%nat) by (apply Hge2, nth_In; exact Hi0_lt_m).
      set (k0 := (M - 1)%nat).

      assert (Heq_k0 : Csum (fun i => nth i coeffs C0 *c phi (nth i ns 0%nat) k0) (length ns) = C0)
        by apply Heq.

      set (f := fun j => nth j coeffs C0 *c phi (nth j ns 0%nat) k0).

      assert (Hterm_zero : forall j, (j < length ns)%nat -> j <> i0 -> f j = C0).
      { intros j Hj Hneq. unfold f.
        apply term_zero_for_others_general with (ns:=ns) (coeffs:=coeffs) (i0:=i0); auto. }

      assert (Hsum_reduce : Csum f (length ns) = f i0).
      {
        rewrite Hlen_n.
        apply Csum_reduce_to_single with (f := f) (n := S m') (idx := i0).
        - rewrite Hlen_n in Hi0_lt_m; exact Hi0_lt_m.
        - intros j Hj. split.
          + intros ->; reflexivity.
          + intros Hneq. apply Hterm_zero; [rewrite Hlen_n; exact Hj | exact Hneq].
      }

      assert (Hfi0 : nth i0 coeffs C0 = C0).
      {
        assert (Hfi0_eq : f i0 = C0) by (rewrite <- Hsum_reduce; exact Heq_k0).
        unfold f in Hfi0_eq.
        assert (Hnonzero : phi (nth i0 ns 0%nat) k0 <> C0)
          by (apply phi_pred_nonzero; exact Hge3).
        apply product_zero_implies_factor_zero in Hfi0_eq; auto.
      }

      set (ns' := firstn i0 ns ++ skipn (S i0) ns).
      set (coeffs' := firstn i0 coeffs ++ skipn (S i0) coeffs).

      assert (Hlen' : length ns' = length coeffs').
      { unfold ns', coeffs'; rewrite !length_app, !length_firstn, !length_skipn; lia. }
      assert (Hdup' : NoDup ns').
      { apply NoDup_remove_at with (A := nat) (l := ns) (i := i0); auto. }
      assert (Hge2' : forall n, In n ns' -> (n >= 2)%nat).
      { intros n Hin. apply Hge2. apply in_app_iff in Hin as [Hin1|Hin2].
        - apply In_firstn with (n:=i0) in Hin1; exact Hin1.
        - apply In_skipn with (n:=S i0) in Hin2; exact Hin2. }

      assert (Hlen_lt : (length ns' < length ns)%nat).
      { unfold ns'; rewrite length_app, length_firstn, length_skipn; lia. }
      assert (Hlen_lt_Sm' : (length ns' < S m')%nat) by (rewrite Hlen_n in Hlen_lt; exact Hlen_lt).

      assert (Hlen_ns'_eq : length ns' = pred (length ns)).
      { unfold ns'. rewrite length_app, length_firstn, length_skipn.
        rewrite min_l by lia. lia. }
      assert (Hlen_coeffs'_eq : length coeffs' = pred (length coeffs)).
      { unfold coeffs'. rewrite length_app, length_firstn, length_skipn.
        rewrite min_l by (rewrite <- Hlen; lia). lia. }
      assert (H_len_ns_pos : (0 < length ns)%nat) by (rewrite Hlen_n; lia).

      assert (Heq' : forall k, Csum (fun i => nth i coeffs' C0 *c phi (nth i ns' 0%nat) k) (length ns') = C0).
      {
        intros k.
        set (f_k := fun i : nat => nth i coeffs C0 *c phi (nth i ns 0%nat) k).
        set (g_k := fun i : nat => nth i coeffs' C0 *c phi (nth i ns' 0%nat) k).

        assert (H_g_eq : forall j, g_k j = if Nat.ltb j i0 then f_k j else f_k (S j)).
        {
          intros j.
          unfold g_k, f_k, coeffs', ns'.
          destruct (Nat.ltb_spec j i0) as [Hlt | Hge].
          - rewrite !nth_remove_at_lt by auto.
            reflexivity.
          - rewrite !nth_remove_at_ge by auto.
            reflexivity.
        }

        assert (H_local_Csum_ext : forall (h1 h2 : nat -> Complex) (N : nat),
          (forall j : nat, (j < N)%nat -> h1 j = h2 j) -> Csum h1 N = Csum h2 N).
        {
          intros h1 h2 N Hext.
          induction N as [| N' IH_N].
          - simpl. reflexivity.
          - simpl. rewrite IH_N.
            + f_equal. apply Hext. lia.
            + intros j Hj. apply Hext. lia.
        }

        assert (H1 : Csum g_k (pred (length ns)) = 
                  Csum (fun j : nat => if Nat.ltb j i0 then f_k j else f_k (S j)) (pred (length ns))).
        {
          apply H_local_Csum_ext.
          intros j Hj.
          exact (H_g_eq j).
        }

        assert (H_csum_eq : Csum g_k (pred (length ns)) +c f_k i0 = Csum f_k (length ns)).
        {
          rewrite H1.
          apply Csum_remove_at.
          exact Hi0_lt_m.
        }

        assert (H_fk_i0 : f_k i0 = C0).
        {
          unfold f_k.
          rewrite Hfi0.
          simpl.
          rewrite Cmul_0_l.
          reflexivity.
        }

        assert (H_Heq_k : Csum f_k (length ns) = C0) by (apply Heq).
        assert (H_step1 : Csum g_k (pred (length ns)) +c C0 = Csum f_k (length ns)).
        {
          rewrite H_fk_i0 in H_csum_eq.
          exact H_csum_eq.
        }
        assert (H_step2 : Csum g_k (pred (length ns)) = Csum f_k (length ns)).
        {
          rewrite Cadd_0_r in H_step1.
          exact H_step1.
        }
        assert (H_step3 : Csum g_k (pred (length ns)) = C0).
        {
          rewrite H_step2, H_Heq_k.
          reflexivity.
        }

        rewrite Hlen_ns'_eq.
        exact H_step3.
      }

      destruct (Nat.eq_dec i i0) as [Heq_i | Hneq_i].
      - subst i.
        exact Hfi0.
      - assert (H_trichotomy : (i < i0)%nat \/ (i > i0)%nat).
        {
          destruct (Nat.lt_ge_cases i i0) as [Hlt | Hge].
          - left; exact Hlt.
          - right; lia.
        }
        destruct H_trichotomy as [H_i_lt_i0 | H_i_gt_i0].
        + assert (Hi' : (i < length ns')%nat).
          {
            rewrite Hlen_ns'_eq.
            lia.
          }
          assert (H_ind_result : forall j, (j < length ns')%nat -> nth j coeffs' C0 = C0).
          {
            specialize (IH (length ns') Hlen_lt_Sm').
            apply IH.
            - reflexivity.
            - exact Hge2'.
            - exact Hdup'.
            - exact Hlen'.
            - exact Heq'.
          }
          assert (H_nth_eq : nth i coeffs C0 = nth i coeffs' C0).
          {
            unfold coeffs'.
            rewrite !nth_remove_at_lt by auto.
            reflexivity.
          }
          rewrite H_nth_eq.
          apply H_ind_result.
          exact Hi'.
        + assert (Hi'' : ((i - 1) < length ns')%nat).
          {
            rewrite Hlen_ns'_eq.
            lia.
          }
          assert (H_ind_result : forall j, (j < length ns')%nat -> nth j coeffs' C0 = C0).
          {
            specialize (IH (length ns') Hlen_lt_Sm').
            apply IH.
            - reflexivity.
            - exact Hge2'.
            - exact Hdup'.
            - exact Hlen'.
            - exact Heq'.
          }
          assert (H_ge_i0 : (i - 1 >= i0)%nat) by lia.
          assert (H_nth_ge : nth (i - 1) coeffs' C0 = nth (S (i - 1)) coeffs C0).
          {
            unfold coeffs'.
            apply nth_remove_at_ge with (A := Complex) (l := coeffs) (i0 := i0) (j := i - 1) (d := C0).
            exact H_ge_i0.
          }
          assert (H_S_pred : S (i - 1) = i) by lia.
          assert (H_final : nth i coeffs C0 = nth (i - 1) coeffs' C0).
          {
            rewrite H_nth_ge.
            rewrite H_S_pred.
            reflexivity.
          }
          rewrite H_final.
          apply H_ind_result.
          exact Hi''.
  }
  intros ns coeffs Hge2 Hdup Hlen Heq i Hi.
  specialize (H_main (length ns) ns coeffs).
  apply H_main.
  - reflexivity.
  - exact Hge2.
  - exact Hdup.
  - exact Hlen.
  - exact Heq.
  - exact Hi.
Qed.

(* 映射保持索引取值 *)
Lemma H_nth_map : forall (A B : Type) (f : A -> B) (l : list A) (d : B) (d0 : A) (j : nat),
  (j < length l)%nat -> nth j (map f l) d = f (nth j l d0).
Proof.
  intros A B f l.
  induction l as [| h t IHl].
  - intros d d0 j Hj.
    exfalso.
    simpl in Hj.
    lia.
  - intros d d0 j Hj.
    destruct j as [| j'].
    + simpl.
      reflexivity.
    + simpl in *.
      apply IHl.
      lia.
Qed.

(* 缩放因子非零 *)
Lemma scale_factor_nonzero : forall (n : nat),
  (n >= 2)%nat -> Cof_real (1 / sqrt (INR n)) <> C0.
Proof.
  intros n Hn.
  assert (Hn_pos_nat : (0 < n)%nat) by lia.
  assert (Hn_pos_R : (0 < INR n)%R) by (apply lt_0_INR; exact Hn_pos_nat).
  assert (Hsqrt_pos : (0 < sqrt (INR n))%R) by (apply sqrt_lt_R0_c; exact Hn_pos_R).
  assert (Hsqrt_neq0 : (sqrt (INR n) <> 0)%R) by (apply Rgt_not_eq; exact Hsqrt_pos).
  assert (Hinv_pos : (0 < / sqrt (INR n))%R) by (apply Rinv_0_lt_compat; exact Hsqrt_pos).
  assert (Hdiv_pos : (0 < 1 / sqrt (INR n))%R).
  { unfold Rdiv; rewrite Rmult_1_l; exact Hinv_pos. }
  assert (Hdiv_neq0 : (1 / sqrt (INR n) <> 0)%R) by (apply Rgt_not_eq; exact Hdiv_pos).
  assert (Hcof_real_neq0 : forall (r : R), r <> 0%R -> Cof_real r <> C0).
  {
    intros r Hr.
    unfold Cof_real, C0.
    intro H_contra.
    apply Hr.
    inversion H_contra.
    subst.
    reflexivity.
  }
  apply Hcof_real_neq0.
  exact Hdiv_neq0.
Qed.

(* 定理：psi线性无关性 *)
Theorem psi_linear_independent :
  forall (ns : list nat) (coeffs : list Complex),
    (forall n, In n ns -> (n >= 2)%nat) ->
    NoDup ns ->
    length ns = length coeffs ->
    (forall k, Csum (fun i => nth i coeffs C0 *c psi (nth i ns 0) k) (length ns) = C0) ->
    forall i, (i < length ns)%nat -> nth i coeffs C0 = C0.
Proof.
  intros ns coeffs Hge2 Hdup Hlen Heq i Hi.
  set (s := fun j : nat => Cof_real (1 / sqrt (INR (nth j ns 0)))).
  set (coeffs_phi := map (fun idx : nat => nth idx coeffs C0 *c s idx) (seq 0 (length ns))).

  assert (Hlen_phi : length coeffs_phi = length ns).
  { unfold coeffs_phi. rewrite length_map, length_seq. reflexivity. }

  assert (H_nth_seq_general : forall m start j d : nat,
    (j < m)%nat -> nth j (seq start m) d = start + j).
  { induction m; intros start j d Hj.
    - exfalso; lia.
    - destruct j; simpl.
      + lia.
      + rewrite IHm by lia; lia. }

  assert (H_seq_nth : forall m j : nat,
    (j < m)%nat -> nth j (seq 0 m) 0 = j).
  { intros m j Hj.
    rewrite H_nth_seq_general with (d:=0) by auto.
    lia. }

  assert (H_sum_eq : forall k : nat,
    Csum (fun i => nth i coeffs_phi C0 *c phi (nth i ns 0) k) (length ns) = C0).
  { intros k.
    assert (H_coeffs_phi_nth : forall j : nat,
      (j < length ns)%nat -> nth j coeffs_phi C0 = nth j coeffs C0 *c s j).
    { intros j Hj.
      unfold coeffs_phi.
      rewrite H_nth_map with (d0:=0) by (rewrite length_seq; auto).
      rewrite H_seq_nth by auto.
      reflexivity. }
    assert (H_term_eq : forall j : nat,
      (j < length ns)%nat ->
      nth j coeffs_phi C0 *c phi (nth j ns 0) k = nth j coeffs C0 *c psi (nth j ns 0) k).
    { intros j Hj.
      rewrite H_coeffs_phi_nth by auto.
      unfold psi, s.
      rewrite Cmul_assoc.
      reflexivity. }
    assert (H_csum_eq : Csum (fun i => nth i coeffs_phi C0 *c phi (nth i ns 0) k) (length ns) =
      Csum (fun i => nth i coeffs C0 *c psi (nth i ns 0) k) (length ns)).
    { apply Csum_ext'.
      intros j Hj.
      exact (H_term_eq j Hj). }
    rewrite H_csum_eq.
    exact (Heq k). }

  assert (Hlen_phi_sym : length ns = length coeffs_phi).
  { apply eq_sym. exact Hlen_phi. }

  assert (H_phi_coeffs_zero : forall j : nat,
    (j < length ns)%nat -> nth j coeffs_phi C0 = C0).
  { apply phi_linear_independent_general with (ns:=ns) (coeffs:=coeffs_phi).
    - exact Hge2.
    - exact Hdup.
    - exact Hlen_phi_sym.
    - exact H_sum_eq. }

  assert (H_s_nonzero : forall j : nat,
    (j < length ns)%nat -> s j <> C0).
  { intros j Hj.
    unfold s.
    assert (Hn_ge2 : (nth j ns 0 >= 2)%nat).
    { apply Hge2. apply nth_In. exact Hj. }
    apply scale_factor_nonzero. exact Hn_ge2. }

  assert (H_main : forall j : nat,
    (j < length ns)%nat -> nth j coeffs C0 = C0).
  { intros j Hj.
    assert (H1 : nth j coeffs_phi C0 = C0) by (apply H_phi_coeffs_zero; exact Hj).
    assert (H2 : nth j coeffs_phi C0 = nth j coeffs C0 *c s j).
    { unfold coeffs_phi.
      rewrite H_nth_map with (d0:=0) by (rewrite length_seq; auto).
      rewrite H_seq_nth by auto.
      reflexivity. }
    rewrite H2 in H1.
    apply product_zero_implies_factor_zero in H1.
    - exact H1.
    - apply H_s_nonzero. exact Hj. }

  exact (H_main i Hi).
Qed.

End UnconditionalBasis.

Export UnconditionalBasis.
