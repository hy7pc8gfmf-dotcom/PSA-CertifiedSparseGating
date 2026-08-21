(* ============================================================
   库: ca_zeta_honest —— Re(s) > 1 半平面上的诚实 ζ 函数（2026-08-15 新增）
   ============================================================
   目的：用 ca_gamma 中**已证明**的级数收敛（zeta_series_converges，配合
   my_complex_pow 修复后对应真正的 Σ n^{-s}）构造 ζ(s)，取代原 ZetaAxioms
   的公理化定义（该模块已清空）。

   内容：
     - zeta            ：ζ(s)（经典选择提取收敛级数极限的见证）
     - Cseq_limit_unique：序列极限唯一性
     - zeta_series_identity：ζ(s) = Σ_{n≥1} n^{-s}（Cseq_limit 意义下）
     - zeta_re_series  ：Re ζ(s) = lim Σ re_term（分量收敛）
     - zeta_re_series_sum：Re ζ(s) = Σ_{n≥0} re_term s n（sum_f_R0 形式）

   审计说明（Print Assumptions）：
     zeta_series_identity 依赖 经典选择 constructive_indefinite_description
     （仅用于从"存在极限"提取见证值，标准做法，数学lib/Isabelle 亦如此），
     以及 ca_gamma 链条的经典逻辑/完备性/函数外延性。无任何自定义公理。
   ============================================================ *)

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
Require Import Stdlib.Logic.IndefiniteDescription. (* 不定描述原理（经典选择）*)
Require Import Stdlib.Classes.Morphisms.   (* 态射类，用于 Proper 等 *)
Require Import Stdlib.Classes.RelationPairs. (* 关系对组合 *)
Require Import Stdlib.Arith.PeanoNat.      (* 皮亚诺自然数算术，包含加法、乘法、比较等 *)
Require Import Stdlib.ZArith.ZArith.       (* 整数算术总集 *)
Require Import Stdlib.ZArith.Zdiv.         (* 整数除法 *)
Require Import Stdlib.micromega.Lia.       (* 线性整数算术自动化策略（用于 lia）*)
Require Import Stdlib.Strings.String.      (* 字符串类型及操作（用于调试/注释）*)
Require Import Stdlib.micromega.Lra.       (* 线性实数算术自动化策略（用于 lra）*)
From Stdlib Require Import Lia.            (* 再次导入 Lia，确保可用（冗余）*)
From Stdlib Require Ranalysis5.            (* 包含 Rolle 定理的高级分析模块 *)

Local Open Scope R_scope.
Open Scope R_scope.
Require Import ca_base.
Require Import ca_algebra.
Require Import ca_primes.
Require Import ca_complex_analysis.
Require Import ca_fourier.
Require Import ca_zeta_scaffold.
Require Import ca_trig.
Require Import ca_gamma.
Require Import ca_taylor.
Require Import ca_complex_log.
Require Import ca_complex_foundation.
Require Import ca_log_bounds.
Require Import ca_independence.
Require Import ca_prime_power.
Require Import ca_basis.
Require Import ca_basis_lemmas.
Require Import ca_probabilistic.
Require Import ca_sparse_ext.
Require Import ca_char_ortho.
Require Import ca_decay.

Module HonestZeta.

Import ComplexNumbers.
Import PrimeEmbedding.
Import GammaIntegralConverges.
Local Open Scope complex_scope.
Open Scope R_scope.

(* 辅助：若 ∀ε>0, |x| < ε，则 x = 0 *)
Lemma abs_lt_all_zero (x : R) : (forall eps : R, 0 < eps -> Rabs x < eps) -> x = 0.
Proof.
  intros H.
  assert (Habs0 : Rabs x = 0).
  { apply Rle_antisym.
    - apply Rnot_lt_le; intro Hlt.
      assert (Hhalf : 0 < Rabs x / 2) by lra.
      specialize (H (Rabs x / 2) Hhalf).
      lra.
    - apply Rabs_pos. }
  apply Rle_antisym.
  - apply Rle_trans with (Rabs x); [apply Rle_abs | rewrite Habs0; lra].
  - apply Ropp_le_cancel.
    rewrite Ropp_0.
    apply Rle_trans with (Rabs (- x)); [apply Rle_abs | rewrite Rabs_Ropp, Habs0; lra].
Qed.

(* 复数序列极限唯一性 *)
Lemma Cseq_limit_unique : forall (u : nat -> Complex) (l1 l2 : Complex),
  Cseq_limit u l1 -> Cseq_limit u l2 -> l1 = l2.
Proof.
  intros u l1 l2 H1 H2.
  destruct l1 as [r1 i1]; destruct l2 as [r2 i2]; simpl in *.
  f_equal.
  - assert (Hdiff : r1 - r2 = 0).
    { apply abs_lt_all_zero.
      intros eps Heps.
      assert (Heps2 : 0 < eps / 2) by lra.
      destruct (H1 (eps / 2) Heps2) as [N1 HN1].
      destruct (H2 (eps / 2) Heps2) as [N2 HN2].
      set (N := Nat.max N1 N2).
      pose proof (HN1 N (Nat.le_max_l N1 N2)) as H1N.
      pose proof (HN2 N (Nat.le_max_r N1 N2)) as H2N.
      unfold Capprox in H1N, H2N.
      destruct H1N as [H1re _]; destruct H2N as [H2re _].
      rewrite Rabs_minus_sym in H1re.
      apply Rle_lt_trans with (Rabs (r1 - re (u N)) + Rabs (re (u N) - r2)).
      + replace (r1 - r2) with ((r1 - re (u N)) + (re (u N) - r2)) by ring.
        apply Rabs_triang.
      + apply Rlt_le_trans with (eps / 2 + eps / 2).
        * apply Rplus_lt_compat; assumption.
        * lra. }
    apply Rminus_diag_uniq; exact Hdiff.
  - assert (Hdiff : i1 - i2 = 0).
    { apply abs_lt_all_zero.
      intros eps Heps.
      assert (Heps2 : 0 < eps / 2) by lra.
      destruct (H1 (eps / 2) Heps2) as [N1 HN1].
      destruct (H2 (eps / 2) Heps2) as [N2 HN2].
      set (N := Nat.max N1 N2).
      pose proof (HN1 N (Nat.le_max_l N1 N2)) as H1N.
      pose proof (HN2 N (Nat.le_max_r N1 N2)) as H2N.
      unfold Capprox in H1N, H2N.
      destruct H1N as [_ H1im]; destruct H2N as [_ H2im].
      rewrite Rabs_minus_sym in H1im.
      apply Rle_lt_trans with (Rabs (i1 - im (u N)) + Rabs (im (u N) - i2)).
      + replace (i1 - i2) with ((i1 - im (u N)) + (im (u N) - i2)) by ring.
        apply Rabs_triang.
      + apply Rlt_le_trans with (eps / 2 + eps / 2).
        * apply Rplus_lt_compat; assumption.
        * lra. }
    apply Rminus_diag_uniq; exact Hdiff.
Qed.

(* ζ(s) 的定义：已证收敛的 Dirichlet 级数 Σ_{n≥1} n^{-s} 的极限（经典选择提取见证） *)
Definition zeta (s : Complex) (Hs : re s > 1) : Complex :=
  proj1_sig (constructive_indefinite_description _ (zeta_series_converges s Hs)).

(* 级数恒等式：ζ(s) = Σ_{n≥1} n^{-s}（收敛意义下） *)
Lemma zeta_series_identity (s : Complex) (Hs : re s > 1) :
  Cseq_limit (fun N : nat => Csum (zeta_series_term s) N) (zeta s Hs).
Proof.
  unfold zeta.
  exact (proj2_sig (constructive_indefinite_description _ (zeta_series_converges s Hs))).
Qed.

(* 复序列收敛 ⟹ 实部序列收敛（分量论证） *)
Lemma re_of_Cseq_limit (u : nat -> Complex) (l : Complex) :
  Cseq_limit u l ->
  forall eps : R, eps > 0 -> exists N : nat, forall n : nat,
    (n >= N)%nat -> Rabs (re (u n) - re l) < eps.
Proof.
  intros H eps Heps.
  destruct (H eps Heps) as [N HN].
  exists N.
  intros n Hn.
  specialize (HN n Hn) as Hn_approx.
  unfold Capprox in Hn_approx.
  exact (proj1 Hn_approx).
Qed.

(* Re ζ(s) = lim_N Re(Σ_{n≤N} n^{-s}) *)
Lemma zeta_re_series (s : Complex) (Hs : re s > 1) :
  Un_cv (fun N : nat => re (Csum (zeta_series_term s) N)) (re (zeta s Hs)).
Proof.
  unfold Un_cv.
  intros eps Heps.
  destruct (re_of_Cseq_limit (fun N : nat => Csum (zeta_series_term s) N) (zeta s Hs)
            (zeta_series_identity s Hs) eps Heps) as [N HN].
  exists N.
  intros n Hn.
  specialize (HN n Hn).
  unfold Rdist in HN.
  change (Rabs (re (Csum (zeta_series_term s) n) - re (zeta s Hs)) < eps).
  exact HN.
Qed.

(* Re ζ(s) = Σ_{n≥0} re_term s n（re_term = n^{-σ}·cos(τ·ln n)，见 ca_gamma） *)
Lemma zeta_re_series_sum (s : Complex) (Hs : re s > 1) :
  Un_cv (fun N : nat => sum_f_R0 (re_term s) N) (re (zeta s Hs)).
Proof.
  intros eps Heps.
  destruct (zeta_re_series s Hs eps Heps) as [N0 HN0].
  exists (S N0).
  intros n Hn.
  rewrite <- (re_Csum_zeta s n).
  apply HN0.
  lia.
Qed.

End HonestZeta.

Export HonestZeta.
