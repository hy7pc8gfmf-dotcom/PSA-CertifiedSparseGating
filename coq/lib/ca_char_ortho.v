(* 拆分自 Riemann_Hypothesis_Proof_Framework.v（复分析证明库 v6.0）*)
(* 库: ca_char_ortho  原文行区间: 36660-37113  机械拆分，未改动内容 *)

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

Require Import ca_base ca_algebra ca_primes ca_complex_analysis ca_fourier ca_zeta_scaffold ca_trig ca_gamma ca_taylor ca_zeta_axioms ca_complex_log ca_complex_foundation ca_log_bounds ca_independence ca_prime_power ca_basis ca_basis_lemmas ca_probabilistic ca_sparse_ext.

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

(* ==================================================== *)
(* 模块：PrimeFieldCharacterOrthogonality               *)
(* 目的：素数域上不同线性相位特征序列的正交性         *)
(* 依赖：ComplexNumbers, UnconditionalBasis,             *)
(*        UnconditionalBasisLemmas, ConstructivePrimes   *)
(* ==================================================== *)

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

Module PrimeFieldCharacterOrthogonality.

(* 复指数为一时角度为2π整数倍 *)
Lemma Cexp_eq_1_iff (θ : R) :
  (exists k : Z, θ = 2 * PI * IZR k) <-> Cexp (0 +i θ) = C1.
Proof.
  split.
  - intros [k ->].
    unfold Cexp, C1; simpl.
    assert (Hcos : cos (2 * PI * IZR k) = 1).
    { rewrite <- (Rplus_0_l (2 * PI * IZR k)) at 1.
      rewrite cos_periodic_int; apply cos_0. }
    assert (Hsin : sin (2 * PI * IZR k) = 0).
    { rewrite <- (Rplus_0_l (2 * PI * IZR k)) at 1.
      rewrite sin_periodic_int; apply sin_0. }
    rewrite Hcos, Hsin, exp_0.
    apply Complex_eq; simpl; ring.
  - intros H.
    assert (Hdiff : (1 +i 0) -c Cexp (0 +i θ) = C0) by
      (rewrite H; apply Csub_self).
    apply cexp_eq_1_implies_cos1_sin0 in Hdiff.
    destruct Hdiff as [Hcos Hsin].
    apply reduce_angle_to_0_2pi in Hcos.
    destruct Hcos as [r [k [Hr [Heq Hr_cos]]]].
    assert (Hr_sin : sin r = 0).
    { rewrite Heq in Hsin.
      rewrite sin_plus in Hsin.
      assert (sin2πk : sin (2 * PI * IZR k) = 0).
      { rewrite <- (Rplus_0_l (2 * PI * IZR k)) at 1.
        rewrite sin_periodic_int; apply sin_0. }
      assert (cos2πk : cos (2 * PI * IZR k) = 1).
      { rewrite <- (Rplus_0_l (2 * PI * IZR k)) at 1.
        rewrite cos_periodic_int; apply cos_0. }
      rewrite sin2πk, cos2πk in Hsin; ring_simplify in Hsin; exact Hsin. }
    assert (r = 0) by (apply (cos1_sin0_in_0_2pi_implies_0 r Hr Hr_cos Hr_sin)).
    subst r; rewrite Rplus_0_r in Heq; exists k; exact Heq.
Qed.

(* 复指数的共轭 *)
Lemma Cconj_Cexp (θ : R) : Cconj (Cexp (0 +i θ)) = Cexp (0 +i (-θ)).
Proof.
  unfold Cexp, Cconj; simpl.
  rewrite cos_neg, sin_neg.
  apply Complex_eq; simpl; ring.
Qed.

(* 复指数的幂次 *)
Lemma Cexp_pow (θ : R) (n : nat) : (Cexp (0 +i θ) ^ n)%C = Cexp (0 +i (INR n * θ)).
Proof.
  induction n as [|n IH].
  - simpl; rewrite Rmult_0_l; symmetry; apply Cexp_0_eq_1.
  - simpl Cpow; rewrite IH.
    rewrite <- Cexp_add.
    apply f_equal.
    apply Complex_eq; simpl; (destruct n; simpl; ring).
Qed.

(* 几何级数零和 *)
Lemma geometric_sum_zero (z : Complex) (n : nat) (Hz : z <> C1) (Hn : (z ^ n)%C = C1) :
  independent.Csum (fun i => (z ^ i)%C) n = C0.
Proof.
  pose proof (Csum_geometric_aux z n) as H_aux.
  rewrite Hn in H_aux.
  rewrite Csub_self in H_aux.
  assert (Hz_diff : C1 -c z <> C0).
  { apply C1_minus_z_nonzero; exact Hz. }
  apply Cmul_no_zero_divisors in H_aux as [H_zero | H_sum].
  - exfalso; apply Hz_diff; exact H_zero.
  - exact H_sum.
Qed.

(* 模非零则严格小于模数 *)
Lemma mod_lt_neq0_impl_lt (p a : nat) :
  (p >= 2)%nat -> a mod p <> 0%nat -> (a mod p < p)%nat.
Proof.
  intros Hp Hmod.
  assert (Hp0 : p <> 0%nat) by lia.
  exact (Nat.mod_upper_bound a p Hp0).
Qed.

(* 模非零推出不可整除 *)
Lemma mod_neq0_impl_not_dvd p a : a mod p <> 0%nat -> ~ (Nat.divide p a).
Proof.
  intros Hmod [q Hq].
  apply Hmod.
  rewrite Hq.
  apply Nat.Div0.mod_mul.
Qed.

(* 2π整数倍复指数为一 *)
Lemma Cexp_2PI_int (k : Z) : Cexp (0 +i (2 * PI * IZR k)) = C1.
Proof.
  unfold Cexp; simpl.
  rewrite exp_0, !Rmult_1_l.
  assert (Hcos : cos (2 * PI * IZR k) = 1). {
    rewrite <- cos_0.
    replace (2 * PI * IZR k) with (0 + 2 * PI * IZR k) by ring.
    apply cos_periodic_int.
  }
  assert (Hsin : sin (2 * PI * IZR k) = 0). {
    rewrite <- sin_0.
    replace (2 * PI * IZR k) with (0 + 2 * PI * IZR k) by ring.
    apply sin_periodic_int.
  }
  rewrite Hcos, Hsin.
  unfold C1; reflexivity.
Qed.

(* 模 N 特征正交性（去素化 2026-08-22：语句与证明均无素性假设，对任意 N≥2 成立；
   历史名 prime_character_orthogonality 保留为下方兼容别名——此前同事已将其用于复合 N=512 网格） *)
Theorem character_orthogonality_mod_N (p a b : nat) :
  (p >= 2)%nat ->
  a mod p <> b mod p ->
  Csum (fun x => Cexp (0 +i (2 * PI * INR (a * x) / INR p)) *c
                 Cconj (Cexp (0 +i (2 * PI * INR (b * x) / INR p)))) p = C0.
Proof.
  intros Hp_ge2 Hneq.
  assert (Hp_pos : INR p > 0) by (apply lt_0_INR; lia).

  (* 构造非零余数 c = (a - b) mod p *)
  set (r := ((Z.of_nat a - Z.of_nat b) mod Z.of_nat p)%Z).
  assert (Hr_bound : (0 <= r < Z.of_nat p)%Z). {
    apply Z.mod_pos_bound; lia.
  }
  set (c := Z.to_nat r).

  assert (Hc_nonzero : c <> 0%nat). {
    intro Hc0.
    assert (Hr0 : r = 0%Z). {
      apply (Z2Nat.inj r 0%Z); [apply (proj1 Hr_bound) | lia | ].
      unfold c in Hc0; exact Hc0.
    }
    subst r.
    assert (Hmod_zero : ((Z.of_nat a - Z.of_nat b) mod Z.of_nat p)%Z = 0%Z) by (exact Hr0).
    apply Z.mod_divide in Hmod_zero; [| lia].
    destruct Hmod_zero as [k Hk].
    assert (Ha_mod_eq_Z : (Z.of_nat a mod Z.of_nat p)%Z = (Z.of_nat b mod Z.of_nat p)%Z). {
      assert (H_eq_plus : (Z.of_nat a = Z.of_nat b + k * Z.of_nat p)%Z) by lia.
      rewrite H_eq_plus%Z.
      rewrite (Z.mod_add (Z.of_nat b) k (Z.of_nat p))%Z; [| lia].
      reflexivity.
    }
    apply Hneq.
    apply Nat2Z.inj.
    rewrite !Nat2Z.inj_mod.
    exact Ha_mod_eq_Z.
  }

  assert (Hc_lt_p : (c < p)%nat). {
    unfold c.
    destruct Hr_bound as [Hr_ge0 Hr_lt].
    pose proof (Z2Nat.inj_lt r (Z.of_nat p) Hr_ge0 (Zle_0_nat p)) as [H _].
    apply H in Hr_lt.
    assert (Htemp : Z.to_nat (Z.of_nat p) = p) by lia.
    rewrite Htemp in Hr_lt.
    exact Hr_lt.
  }

  (* 将每一项转换成 z^x 的形式 *)
  assert (H_inner_eq : forall x,
    Cexp (0 +i (2 * PI * INR (a * x) / INR p)) *c
    Cconj (Cexp (0 +i (2 * PI * INR (b * x) / INR p))) =
    Cexp (0 +i (2 * PI * INR (c * x) / INR p))).
  {
    intros x.
    rewrite Cconj_Cexp.
    rewrite <- Cexp_add.

    assert (H_mod : exists k : Z, (Z.of_nat a - Z.of_nat b = r + k * Z.of_nat p)%Z). {
      exists ((Z.of_nat a - Z.of_nat b) / Z.of_nat p)%Z.
      unfold r.
      rewrite Z.mul_comm, Z.add_comm.
      apply Z.div_mod; lia.
    }
    destruct H_mod as [k Hk].

    assert (H_real_eq : INR a - INR b = INR c + IZR k * INR p). {
      apply (f_equal IZR) in Hk.
      rewrite !minus_IZR, !plus_IZR, !mult_IZR in Hk.
      rewrite <- !INR_IZR_INZ in Hk.
      assert (Hr_eq_IZR : IZR r = INR c). {
        unfold c.
        rewrite INR_IZR_INZ.
        rewrite Z2Nat.id by (apply Hr_bound).
        reflexivity.
      }
      rewrite Hr_eq_IZR in Hk.
      exact Hk.
    }

    assert (H_angle : (2 * PI * INR (a * x) / INR p) - (2 * PI * INR (b * x) / INR p) =
                      2 * PI * INR (c * x) / INR p + 2 * PI * IZR k * INR x).
    {
      rewrite !mult_INR.
      replace (2 * PI * (INR a * INR x) / INR p - 2 * PI * (INR b * INR x) / INR p)
        with ((2 * PI * INR x / INR p) * (INR a - INR b))
        by (field; apply Rgt_not_eq, Hp_pos).
      replace (2 * PI * (INR c * INR x) / INR p + 2 * PI * IZR k * INR x)
        with ((2 * PI * INR x / INR p) * (INR c + IZR k * INR p))
        by (field; apply Rgt_not_eq, Hp_pos).
      rewrite H_real_eq.
      reflexivity.
    }

    replace ((0 +i (2 * PI * INR (a * x) / INR p)) +c
             (0 +i (- (2 * PI * INR (b * x) / INR p))))
      with (0 +i ((2 * PI * INR (a * x) / INR p) - (2 * PI * INR (b * x) / INR p))).
    2: { unfold Cadd; simpl; f_equal; ring. }

    rewrite H_angle.

    replace (0 +i (2 * PI * INR (c * x) / INR p + 2 * PI * IZR k * INR x))
      with ((0 +i (2 * PI * INR (c * x) / INR p)) +c (0 +i (2 * PI * IZR k * INR x))).
    2: { unfold Cadd; simpl; f_equal; ring. }

    rewrite Cexp_add.

    replace (2 * PI * IZR k * INR x) with (2 * PI * IZR (k * Z.of_nat x)).
    2: { rewrite mult_IZR; rewrite INR_IZR_INZ; ring. }

    rewrite Cexp_2PI_int.
    rewrite Cmul_1_r.
    reflexivity.
  }

  (* 定义 z *)
  set (z := Cexp (0 +i (2 * PI * INR c / INR p))).
  assert (H_pow_eq : forall x, Cexp (0 +i (2 * PI * INR (c * x) / INR p)) = (z ^ x)%C). {
    intro x0; unfold z.
    rewrite Cexp_pow.
    assert (H_arg : 2 * PI * INR (c * x0) / INR p = INR x0 * (2 * PI * INR c / INR p)).
    { rewrite mult_INR. field; lra. }
    apply Complex_eq; simpl; rewrite !exp_0, !Rmult_1_l; rewrite H_arg; reflexivity.
  }

  assert (Hsumeq : Csum (fun x => Cexp (0 +i (2 * PI * INR (a * x) / INR p)) *c
                     Cconj (Cexp (0 +i (2 * PI * INR (b * x) / INR p)))) p =
                 Csum (fun x : nat => (z ^ x)%C) p).
  {
    eapply independent.Csum_ext with (n := p).
    intros x Hx_lt_p.
    rewrite H_inner_eq.
    apply H_pow_eq.
  }
  rewrite Hsumeq.

  (* z ≠ 1 *)
  assert (Hz1 : z <> C1). {
    intro Hc1.
    apply Cexp_eq_1_iff in Hc1.
    destruct Hc1 as [k Hk].
    apply (f_equal (fun t => INR p * t)) in Hk.
    simpl in Hk.
    assert (H_left_simplify : INR p * (2 * PI * INR c / INR p) = 2 * PI * INR c).
    { field; lra. }
    rewrite H_left_simplify in Hk.
    replace (INR p * (2 * PI * IZR k)) with (2 * PI * (IZR k * INR p)) in Hk by ring.
    apply Rmult_eq_reg_l with (r := 2 * PI) in Hk;
      [| apply Rgt_not_eq, Rmult_lt_0_compat; [lra | apply PI_RGT_0]].
    rewrite Rmult_comm in Hk.
    assert (H_c_gt0 : 0 < INR c) by (apply lt_0_INR; lia).
    assert (H_c_lt_p : INR c < INR p) by (apply lt_INR; exact Hc_lt_p).
    destruct (Z_lt_ge_dec k 1) as [Hk_lt1 | Hk_ge1].
    - assert (k <= 0)%Z by lia.
      assert (IZR k <= 0) by (apply IZR_le; lia).
      assert (INR p * IZR k <= 0). {
        apply Rle_trans with (INR p * 0).
        - apply Rmult_le_compat_l; [lra | exact H0].
        - ring_simplify; lra.
      }
      lra.
    - assert (1 <= IZR k) by (apply IZR_le; lia).
      assert (Hineq : INR p <= INR p * IZR k). {
        rewrite <- (Rmult_1_r (INR p)) at 1.
        apply Rmult_le_compat_l; [lra | exact H].
      }
      lra.
  }

  (* z^p = 1 *)
  assert (H_pow_1 : (z ^ p)%C = C1). {
    unfold z.
    rewrite Cexp_pow.
    replace (INR p * (2 * PI * INR c / INR p)) with (2 * PI * INR c) by (field; lra).
    rewrite (INR_IZR_INZ c).
    apply Cexp_2PI_int.
  }

  (* 应用几何级数求和为零的推导 *)
  assert (Hz_sum : Csum (fun i => (z ^ i)%C) p = C0). {
    pose proof (Csum_geometric_aux z p) as H_aux.
    rewrite H_pow_1 in H_aux.
    rewrite Csub_self in H_aux.
    assert (Hz_diff : C1 -c z <> C0) by (apply C1_minus_z_nonzero; exact Hz1).
    apply Cmul_no_zero_divisors in H_aux as [H_zero | H_sum].
    - exfalso; apply Hz_diff; exact H_zero.
    - rewrite <- (Csum_equiv_PrimeEmbedding (fun i => (z ^ i)%C) p).
      rewrite H_sum.
      reflexivity.
  }
  exact Hz_sum.

Qed.

(* 兼容别名（历史名转发，防下游断链） *)
Lemma prime_character_orthogonality (p a b : nat) :
  (p >= 2)%nat ->
  a mod p <> b mod p ->
  Csum (fun x => Cexp (0 +i (2 * PI * INR (a * x) / INR p)) *c
                 Cconj (Cexp (0 +i (2 * PI * INR (b * x) / INR p)))) p = C0.
Proof. exact (character_orthogonality_mod_N p a b). Qed.

(* 素数特征正交性推论：求和范数为零 *)
Corollary prime_character_bound_zero (p a b : nat) :
  (p >= 2)%nat ->
  (a mod p <> b mod p)%nat ->
  Cnorm (Csum (fun x : nat => Cexp (0 +i (2 * PI * INR (a * x) / INR p)) *c
                        Cconj (Cexp (0 +i (2 * PI * INR (b * x) / INR p)))) p) = 0%R.
Proof.
  intros Hp Hmod.
  assert (Hsum : Csum (fun x : nat => Cexp (0 +i (2 * PI * INR (a * x) / INR p)) *c
                               Cconj (Cexp (0 +i (2 * PI * INR (b * x) / INR p)))) p = C0).
  { apply prime_character_orthogonality; assumption. }
  rewrite Hsum.
  unfold Cnorm, Cnorm_sq, C0; simpl.
  rewrite Rsqr_0, Rplus_0_r, sqrt_0.
  reflexivity.
Qed.

Import independent.

(* 定理：非对角内积范数上界（带因子） *)
Theorem inner_offdiag_bound_with_factor :
  forall (seq : nat -> nat) (I : list nat) (c : nat)
    (Hc_ge2 : (c >= 2)%nat)
    (Hseq0_ge2 : (seq 0 >= 2)%nat)
    (Hbase : forall idx : nat, (INR (seq (S idx)) > INR c * INR (seq idx))%R)
    (HnodupI : NoDup I)
    (idx1 idx2 : nat)
    (Hneq : (idx1 <> idx2)%nat)
    (Hidx1 : (idx1 < length I)%nat)
    (Hidx2 : (idx2 < length I)%nat)
    (vals : list nat)
    (Hvals : vals = map seq I)
    (n1 : nat)
    (Hn1 : n1 = nth idx1 vals 0%nat)
    (n2 : nat)
    (Hn2 : n2 = nth idx2 vals 0%nat)
    (n_small : nat)
    (Hsmall_eq : n_small = min n1 n2)
    (n_large : nat)
    (Hlarge_eq : n_large = max n1 n2),
  INR n_large >= INR c * INR c * INR n_small ->
  let N := (n_small - 1)%nat in
  let inner := Csum (fun k : nat => psi n_small k *c Cconj (psi n_large k)) N in
  Cnorm inner <= (INR c)^2 / 4 * sqrt (INR n_small / INR n_large) / (sqrt (INR c) - 1).
Proof.
  intros seq I c Hc_ge2 Hseq0_ge2 Hbase HnodupI idx1 idx2 Hneq Hidx1 Hidx2
         vals Hvals n1 Hn1 n2 Hn2 n_small Hsmall_eq n_large Hlarge_eq Hsq_growth.
  subst vals n1 n2 n_small n_large.

  assert (Hc_ge1 : (c >= 1)%nat) by lia.

  pose proof (basic_properties seq I c Hc_ge1 Hseq0_ge2 Hbase HnodupI
                                idx1 idx2 Hneq Hidx1 Hidx2) as Hprops.
  cbv beta zeta in Hprops.
  destruct Hprops as (Hinc & Hstrict & Hall_ge2 & Hnodup_vals & Hn1_ge2 & Hn2_ge2 & Hn1_neq_n2).

  set (a := nth idx1 (map seq I) 0%nat) in *.
  set (b := nth idx2 (map seq I) 0%nat) in *.

  fold a b in Hsq_growth.

  assert (Hsmall_ge2 : (min a b >= 2)%nat).
  { destruct (Nat.le_ge_cases a b) as [Hle | Hge].
    - rewrite (Nat.min_l a b Hle). exact Hn1_ge2.
    - rewrite (Nat.min_r a b Hge). exact Hn2_ge2. }
  assert (Hlarge_ge2 : (max a b >= 2)%nat).
  { destruct (Nat.le_ge_cases a b) as [Hle | Hge].
    - rewrite (Nat.max_r a b Hle). exact Hn2_ge2.
    - rewrite (Nat.max_l a b Hge). exact Hn1_ge2. }

  assert (Hlt_small_large : (min a b < max a b)%nat).
  { destruct (Nat.lt_trichotomy a b) as [Hlt | [Heq | Hlt]].
    - rewrite (Nat.min_l a b) by lia. 
      rewrite (Nat.max_r a b) by lia. 
      exact Hlt.
    - exfalso. exact (Hn1_neq_n2 Heq).
    - rewrite (Nat.min_r a b) by lia. 
      rewrite (Nat.max_l a b) by lia. 
      exact Hlt. }

  assert (Hlin_growth : INR (max a b) >= INR c * INR (min a b)).
  { apply Rle_ge.
    eapply Rle_trans; [| apply Rge_le; exact Hsq_growth].
    apply Rmult_le_compat_r.
    - apply Rlt_le, lt_0_INR; lia.
    - assert (Hc_le_1 : 1 <= INR c).
      { rewrite <- INR_1; apply le_INR; lia. }
      rewrite <- (Rmult_1_r (INR c)) at 1.
      apply Rmult_le_compat_l.
      + apply pos_INR; lia.
      + exact Hc_le_1.
  }

  pose proof (inner_product_norm_bound_general_corrected (min a b) (max a b) c
                Hsmall_ge2 Hlarge_ge2 Hlt_small_large Hc_ge2 Hsq_growth) as Hnorm.

  pose proof (core_algebraic_inequality_general (min a b) (max a b) c
                Hsmall_ge2 Hlarge_ge2 Hlt_small_large Hc_ge2 Hlin_growth) as Hcore.

  assert (Hsqrt_c_gt_1 : sqrt (INR c) - 1 > 0).
  { apply sqrt_c_minus_1_pos; lia. }

  assert (H_scaled : INR c * sqrt (INR (min a b) * INR (max a b)) / (4 * (INR (max a b) - INR (min a b))) <=
                     (INR c)^2 / 4 * sqrt (INR (min a b) / INR (max a b)) / (sqrt (INR c) - 1)).
  {
    assert (H_eq_left : INR c * sqrt (INR (min a b) * INR (max a b)) / (4 * (INR (max a b) - INR (min a b))) =
                       (INR c)^2 / 4 * (sqrt (INR (min a b) * INR (max a b)) / (INR c * (INR (max a b) - INR (min a b))))).
    {
      field.
      split.
      - apply Rgt_not_eq, Rgt_minus, lt_INR; exact Hlt_small_large.
      - apply Rgt_not_eq, lt_0_INR; lia.
    }
    rewrite H_eq_left.
    replace ((INR c)^2 / 4 * sqrt (INR (min a b) / INR (max a b)) / (sqrt (INR c) - 1))
      with ((INR c)^2 / 4 * (sqrt (INR (min a b) / INR (max a b)) / (sqrt (INR c) - 1))).
    - apply Rmult_le_compat_l.
      + nra.
      + exact Hcore.
    - field; apply Rgt_not_eq; exact Hsqrt_c_gt_1.
  }

  cbv beta.
  eapply Rle_trans; [exact Hnorm | exact H_scaled].
Qed.

End PrimeFieldCharacterOrthogonality.

Export UnconditionalBasisLemmas.

Export PrimeFieldCharacterOrthogonality.
