(* 拆分自 Riemann_Hypothesis_Proof_Framework.v（复分析证明库 v6.0）*)
(* 库: ca_zeta_scaffold  原文行区间: 1301-2049  机械拆分，未改动内容 *)

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

Require Import ca_base ca_algebra ca_primes ca_complex_analysis ca_fourier.

Require Import Stdlib.Logic.IndefiniteDescription.

(* ====================================================
   第6章：质数理论 (Level 4)
   ==================================================== *)

(* 6.1 质数在无限维空间中的嵌入 *)
Module PrimeEmbedding.

(* 导入必要的实数库 *)
Require Import Stdlib.Reals.Reals.         (* 实数公理系统及全套定理 *)
Require Import Stdlib.Reals.Rfunctions.    (* 实数函数，包含 sum_f_R0（有限项求和）*)
Require Import Stdlib.Reals.RiemannInt.    (* 黎曼积分理论 *)
Require Import Stdlib.micromega.Lia.       (* 线性整数算术自动化策略，支持 lia 策略 *)
Require Import Stdlib.Reals.RIneq.         (* 实数不等式基本引理 *)
Require Import Stdlib.Reals.R_sqrt.        (* 平方根函数 sqrt 及其性质 *)
Require Import Stdlib.Reals.Reals.         (* 实数公理系统及全套定理（重复导入，保证完备）*)
Require Import Stdlib.micromega.Lra.       (* 线性实数算术自动化策略，提供 lra 策略 *)
Require Import Stdlib.Reals.Reals.                   (* 标准实数库，自动加载 Rdefinitions, Raxioms, Rbasic_fun 等 *)
Require Import Stdlib.setoid_ring.RealField.               (* 实域结构，提供域公理及域运算性质 *)
Require Import Stdlib.micromega.Psatz.                   (* 非线性算术策略集，包含 lra, nra, psatz 等高级自动化策略 *)
Require Import Stdlib.Logic.ProofIrrelevance.        (* 证明无关性公理（全局导入）*)
Require Import Stdlib.Strings.String.      (* 字符串类型及操作，用于调试、信息输出等 *)
Require Import Stdlib.Logic.ProofIrrelevance. (* 证明无关性公理（显式导入）*)
Require Import Stdlib.Program.Equality.    (* 依赖类型等式推理，支持 dependent destruction 等策略 *)
Require Import Stdlib.Reals.Rtrigo.        (* 三角函数理论（基础）*)
Require Import Stdlib.Reals.Rtrigo1.       (* 三角函数理论（进阶），包含 sin²+cos²=1 等恒等式 *)
Require Import Stdlib.Reals.Ranalysis.     (* 实分析基础，导数、连续性、Rolle 定理等 *)
Require Import Stdlib.Arith.Arith.         (* 自然数算术基础库 *)

(* 导入必要的模块 *)
Import ComplexNumbers.                  (* 复数模块：复数定义、运算、极坐标、指数、对数等 *)
Import ListNotations.                   (* 列表记法，提供 [ ]、++ 等语法糖 *)
Import ConstructivePrimes.              (* 构造性质数模块：质数判定、质数序列、计数函数 *)
Import FourierAnalysis.                 (* 傅里叶分析模块：构造性傅里叶变换及相关工具 *)
Import HilbertSpace.                    (* 希尔伯特空间模块：无限维/有限维希尔伯特空间 *)

Local Open Scope complex_scope.         (* 局部打开复数作用域，使复数运算符自动生效 *)

Open Scope R_scope.                     (* 开启实数作用域，使实数运算符自动生效 *)

(* 质数特征序列 *)
Definition prime_characteristic_sequence (p : Prime) : nat -> Complex :=
  let n := prime_value p in
  fun (k : nat) =>
    if (k <? n)%nat
    then Cexp (0 +i (2 * PI * INR k / INR n))
    else C0.

(* 指数零点引理 *)
Lemma exp_0_lemma : exp 0 = 1.
Proof.
  exact exp_0.
Qed.

(* 三角恒等式 *)
Lemma cos_sq_plus_sin_sq : forall θ : R, (cos θ)² + (sin θ)² = 1.
Proof.
  intro θ.
  unfold Rsqr.
  rewrite <- (cos_minus θ θ).
  replace (θ - θ) with 0 by ring.
  exact cos_0.
Qed.

(* 单位根模一引理 *)
Lemma unit_root_norm (k n : nat) :
  Cnorm_sq (Cexp (0 +i (2 * PI * INR k / INR n))) = 1.
Proof.
  unfold Cnorm_sq, Cexp.
  simpl.
  rewrite exp_0.
  rewrite Rmult_1_l, Rmult_1_l.
  apply cos_sq_plus_sin_sq.
Qed.

(* 质数特征序列部分和公式 *)
Lemma prime_seq_sum_lt : forall p N, (N < prime_value p)%nat ->
  sum_f_R0 (fun k => Cnorm_sq (prime_characteristic_sequence p k)) N = INR (N + 1).
Proof.
  intros p N H_lt.
  induction N as [|N IH].
  - simpl.
    unfold prime_characteristic_sequence.
    assert (H0_cond: (0%nat <? prime_value p)%nat = true).
    { apply Nat.ltb_lt. exact H_lt. }
    rewrite H0_cond.
    apply unit_root_norm.
  - simpl.
    assert (HN_lt: (N < prime_value p)%nat) by lia.
    rewrite IH by exact HN_lt.
    unfold prime_characteristic_sequence.
    assert (HSN_cond: (S N <? prime_value p)%nat = true).
    { apply Nat.ltb_lt. lia. }
    rewrite HSN_cond.
    rewrite unit_root_norm.
    replace (match (N + 1)%nat with 0%nat => 1 | S _ => INR (N + 1) + 1 end) with (INR (N + 1) + 1).
    + ring.
    + assert (H_nonzero: (N + 1)%nat <> 0%nat) by lia.
      destruct (N+1)%nat as [|m] eqn:Hcase.
      * exfalso; apply H_nonzero; reflexivity.
      * simpl; reflexivity.
Qed.

(* 零复数模平方为零 *)
Lemma Cnorm_sq_zero : Cnorm_sq C0 = 0.
Proof.
  unfold Cnorm_sq, C0.
  simpl.
  unfold Rsqr.
  ring.
Qed.

(* ssrnat.leq 转标准小于等于引理 *)
Lemma leq2_impl_le : forall n,
  ssrnat.leq 2 n = true -> (2 <= n)%nat.
Proof.
  destruct n as [| [| n0] ].
  - simpl; intros H; discriminate.
  - simpl; intros H; discriminate.
  - intros _.
    do 2 apply le_n_S.
    apply le_0_n.
Qed.

(* 质数最小值至少为二 *)
Lemma prime_value_ge_2 : forall (p : Prime), (prime_value p >= 2)%nat.
Proof.
  intros [n Hp].
  unfold prime_value; simpl.
  apply prime.prime_gt1 in Hp.
  apply leq2_impl_le in Hp.
  exact Hp.
Qed.

(* 质数值非零 *)
Lemma prime_value_nonzero : forall (p : Prime), prime_value p <> 0%nat.
Proof.
  intro p.
  pose proof (prime_value_ge_2 p) as H.
  lia.
Qed.

(* 大索引时特征序列为零 *)
Lemma prime_char_seq_zero_ge : forall p k, (k >= prime_value p)%nat ->
  prime_characteristic_sequence p k = C0.
Proof.
  intros p k H.
  unfold prime_characteristic_sequence.
  assert (Hk: (k <? prime_value p)%nat = false).
  { apply Nat.ltb_ge. exact H. }
  rewrite Hk.
  reflexivity.
Qed.

(* 有限和递归公式 *)
Lemma sum_f_R0_S : forall f n, sum_f_R0 f (S n) = sum_f_R0 f n + f (S n).
Proof.
  intros f n.
  simpl.
  reflexivity.
Qed.

(* 常数部分和截断 *)
Lemma sum_f_R0_constant_ge: forall (f : nat -> R) (a : nat),
  (forall k, (k >= a)%nat -> f k = 0) ->
  forall N, (N >= a)%nat -> sum_f_R0 f N = sum_f_R0 f (a-1).
Proof.
  intros f a Hzero N Hge.
  induction N as [|n IH].
  - destruct a as [|a'].
    + reflexivity.
    + lia.
  - destruct (Nat.eq_dec n (a-1)) as [Heq|Hneq].
    + subst n.
      simpl.
      rewrite Hzero by lia.
      rewrite Rplus_0_r.
      reflexivity.
    + assert (Hge': (n >= a)%nat) by lia.
      simpl.
      rewrite Hzero by lia.
      rewrite Rplus_0_r.
      apply IH.
      exact Hge'.
Qed.

(* 质数特征序列部分和（N ≥ 质数值） *)
Lemma prime_seq_sum_ge : forall p N, (N >= prime_value p)%nat ->
  sum_f_R0 (fun k => Cnorm_sq (prime_characteristic_sequence p k)) N = INR (prime_value p).
Proof.
  intros p N Hge.
  assert (Hzero: forall k, (k >= prime_value p)%nat ->
            Cnorm_sq (prime_characteristic_sequence p k) = 0).
  {
    intros k Hk.
    rewrite prime_char_seq_zero_ge by assumption.
    apply Cnorm_sq_zero.
  }
  destruct (prime_value p) eqn:Hp_val.
  - pose proof (prime_value_nonzero p) as Hnz.
    rewrite Hp_val in Hnz.
    contradiction.
  - rewrite (sum_f_R0_constant_ge
              (fun k => Cnorm_sq (prime_characteristic_sequence p k))
              (S n) Hzero N Hge).
    replace (S n - 1)%nat with n by lia.
    assert (Hlt: (n < prime_value p)%nat).
    { rewrite Hp_val. lia. }
    rewrite prime_seq_sum_lt by exact Hlt.
    replace (n + 1)%nat with (S n) by lia.
    reflexivity.
Qed.

(* 质数特征序列的模平方和有界性 *)
Lemma prime_sequence_norm_bound (p : Prime) : 
  exists M : R, forall N : nat, 
    let partial_sum := 
      sum_f_R0 (fun k : nat => Cnorm_sq (prime_characteristic_sequence p k)) N in
    partial_sum <= M.
Proof.
  exists (INR (prime_value p)).
  intro N.
  destruct (Nat.ltb_spec0 N (prime_value p)) as [Hlt | Hge].
  - rewrite (prime_seq_sum_lt p N Hlt).
    apply le_INR.
    lia.
  - assert (Hge' : (N >= prime_value p)%nat) by lia.
    rewrite (prime_seq_sum_ge p N Hge').
    apply Rle_refl.
Qed.

(* 平方可和序列空间 l²(N, ℂ) 的定义 *)
Definition l2_sequence : Type :=
  { f : nat -> Complex | 
    exists M : R, forall N : nat, 
      let partial_sum := 
        sum_f_R0 (fun k : nat => Cnorm_sq (f k)) N in
      partial_sum <= M }.

(* 质数嵌入到 l² 空间的定义 *)
Definition prime_embedding_l2 (p : Prime) : l2_sequence :=
  let char_seq := prime_characteristic_sequence p in
  exist (fun f : nat -> Complex => exists M : R, forall N : nat,
    let partial_sum := sum_f_R0 (fun k : nat => Cnorm_sq (f k)) N in
    partial_sum <= M) 
    char_seq 
    (prime_sequence_norm_bound p).

(* 素数生成的空间类型 *)
Inductive PrimeGeneratedSpace : Type :=
| prime_basis : Prime -> PrimeGeneratedSpace
| linear_comb : Complex -> PrimeGeneratedSpace -> PrimeGeneratedSpace -> PrimeGeneratedSpace.

(* 素数空间范数 *)
Fixpoint prime_space_norm (v : PrimeGeneratedSpace) : R :=
  match v with
  | prime_basis p => 1.0
  | linear_comb c v1 v2 =>
      Cnorm c * prime_space_norm v1 + prime_space_norm v2
  end.

(* 素数空间元素转序列 *)
Fixpoint prime_generated_to_sequence (v : PrimeGeneratedSpace) : nat -> Complex :=
  match v with
  | prime_basis p => prime_characteristic_sequence p
  | linear_comb c v1 v2 =>
      fun k => c *c prime_generated_to_sequence v1 k
                +c prime_generated_to_sequence v2 k
  end.

(* 黎曼ζ函数的定义域（除s=1外） *)
Definition zeta_domain (s : Complex) : Prop :=
  ~(re s = 1 /\ im s = 0).

(* 临界线上的点不在ζ函数的极点上 *)
Lemma not_on_pole (s : Complex) (Hre : re s = 1/2) : zeta_domain s.
Proof.
  unfold zeta_domain.
  intros H_pole.
  destruct H_pole as [H_re_eq1 H_im_eq0].
  rewrite Hre in H_re_eq1.
  lra.
Qed.

(* 复数幂 *)
Definition complex_pow (z : Complex) (s : Complex) (Hz : z <> C0) : Complex :=
  Cexp (Cmul s (Clog z Hz)).

(* 实部非一则不在极点 *)
Lemma re_neq_1_not_on_pole (s : Complex) (Hre_neq : re s <> 1) : zeta_domain s.
Proof.
  unfold zeta_domain.
  intros H_pole.
  destruct H_pole as [H_re_eq1 _].
  apply Hre_neq.
  exact H_re_eq1.
Qed.

(* 临界线上不在极点 *)
Lemma not_on_pole_critical_line (s : Complex) (Hre : re s = 1/2) : zeta_domain s.
Proof.
  apply re_neq_1_not_on_pole.
  rewrite Hre.
  lra.
Qed.

(* 一减s实部大于零 *)
Lemma Rlt_0_1_minus_re_s (s : Complex) (Hre : re s < 1) : 0 < re (C1 -c s).
Proof.
  destruct s as [a b].
  simpl in *.
  lra.
Qed.

(* 复数部分和 *)
Fixpoint Csum (f : nat -> Complex) (N : nat) : Complex :=
  match N with
  | O => C0
  | S m => Cadd (f m) (Csum f m)
  end.

(* [清理] 已移除占位定义 fun_approx（原返回第 1000 项而非近似，0 处使用） *)

(* 素数计数函数 *)
Definition prime_counting (x : R) : R :=
  INR (prime_pi x).

(* 非零复数模平方为正 *)
Lemma nonzero_norm_sq_pos : forall (z : Complex), z <> C0 -> Cnorm_sq z > 0.
Proof.
  intros z Hnz.
  unfold Cnorm_sq.
  destruct z as [re im]; simpl.
  apply Rnot_le_gt; intro Hle.

  assert (Hre0 : Rsqr re = 0).
  { apply Rle_antisym.
    - eapply Rle_trans.
      + replace (Rsqr re) with (Rsqr re + 0) by ring.
        apply Rplus_le_compat_l.
        apply Rle_0_sqr.
      + exact Hle.
    - apply Rle_0_sqr. }

  assert (Him0 : Rsqr im = 0).
  { apply Rle_antisym.
    - eapply Rle_trans.
      + replace (Rsqr im) with (0 + Rsqr im) by ring.
        apply Rplus_le_compat_r.
        apply Rle_0_sqr.
      + exact Hle.
    - apply Rle_0_sqr. }

  apply Rsqr_eq_0 in Hre0.
  apply Rsqr_eq_0 in Him0.

  apply Hnz.
  rewrite Hre0, Him0.
  reflexivity.
Qed.

(* 非零复数模平方非零 *)
Lemma nonzero_norm_sq_nonzero : forall (z : Complex), z <> C0 -> Cnorm_sq z <> 0.
Proof.
  intros z Hnz.
  pose proof (nonzero_norm_sq_pos z Hnz) as Hpos.
  apply Rgt_not_eq.
  exact Hpos.
Qed.

(* 显式公式项 *)
Definition explicit_formula_term (x : R) (Hx : x > 0) (ρ : Complex) (Hρ : ρ <> C0) : Complex :=
  Cdiv (Cexp (ρ *c (ln x +i 0))) ρ (nonzero_norm_sq_nonzero ρ Hρ).

(* [清理] 已移除 li_simple（原为 x/ln x 却标注"对数积分简化"，实为 PNT 渐近式而非 li(x)；0 处使用）、
   sum_over_zeros_simple（恒返回 C0 的占位）、error_term_simple（恒为 0 的占位） *)

(* 定义 Re 作为函数 *)
Definition Re (z : Complex) : R := re z.

(* 非负整数的实数表示非负 *)
Lemma pos_INR : forall n, 0 <= INR n.
Proof.
  intro n.
  induction n as [|n IH].
  - simpl. lra.
  - rewrite S_INR. lra.
Qed.

(* 正整数的实数表示为正 *)
Lemma lt_0_INR : forall n, (0 < n)%nat -> 0 < INR n.
Proof.
  intros n H.
  apply lt_INR_0.
  exact H.
Qed.

(* 自然数大小关系保持实数大小关系 *)
Lemma le_INR : forall n m, (n <= m)%nat -> INR n <= INR m.
Proof.
  intros n m H.
  induction H as [|m' H IH].
  - apply Rle_refl.
  - rewrite S_INR.
    apply Rle_trans with (INR m').
    + exact IH.
    + pattern (INR m') at 1.
      rewrite <- (Rplus_0_r (INR m')).
      apply Rplus_le_compat_l.
      apply Rlt_le, Rlt_0_1.
Qed.

(* 自然数后继保持小于等于关系 *)
Lemma le_n_S : forall n m, (n <= m)%nat -> (S n <= S m)%nat.
Proof.
  intros n m H.
  induction H as [| m' H' IH].
  - constructor.
  - constructor.
    exact IH.
Qed.

(* 素数计数函数不超过自变量 *)
Lemma count_primes_upto_nat_le : forall n,
  (count_primes_upto_nat n <= n)%nat.
Proof.
  induction n as [|n IH].
  - simpl. apply le_n.
  - simpl.
    destruct (prime (S n)) eqn:Hprime.
    + destruct n as [|m].
      * simpl. apply le_S, le_n.
      * simpl.
        fold (count_primes_upto_nat (S m)).
        rewrite Nat.add_1_r.
        apply le_n_S.
        exact IH.
    + destruct n as [|m].
      * simpl. apply le_S, le_n.
      * simpl.
        rewrite Nat.add_0_r.
        apply le_S.
        exact IH.
Qed.

(* 素数计数函数非负 *)
Lemma count_primes_upto_nat_ge_0 : forall n,
  (0 <= count_primes_upto_nat n)%nat.
Proof.
  intro n.
  induction n as [|n IH].
  - simpl. apply le_n.
  - simpl.
    destruct (prime (S n)) eqn:Hprime.
    + destruct n as [|m].
      * simpl. apply le_n.
      * simpl.
        apply Nat.add_nonneg_nonneg.
        -- exact IH.
        -- apply le_0_n.
    + destruct n as [|m].
      * simpl. apply le_n.
      * simpl.
        rewrite Nat.add_0_r.
        exact IH.
Qed.

(* 自然数加法的实数表示 *)
Lemma plus_INR : forall n m, INR (n + m) = INR n + INR m.
Proof.
  intros n m.
  induction n as [|n IH].
  - simpl. rewrite Rplus_0_l. reflexivity.
  - rewrite Nat.add_succ_l.
    rewrite S_INR.
    rewrite S_INR.
    rewrite IH.
    ring.
Qed.

(* 自然数后继的实数表示 *)
Lemma S_INR : forall n, INR (S n) = INR n + 1.
Proof.
  intro n.
  induction n as [|n IH].
  - simpl. lra.
  - do 2 rewrite S_INR in *. lra.
Qed.

(* INR 与 IZR 转换关系 *)
Lemma INR_IZR_INZ : forall n, INR n = IZR (Z.of_nat n).
Proof.
  intro n.
  rewrite INR_IZR_INZ.
  reflexivity.
Qed.

(* 向下取整函数的界 *)
Lemma archimed : forall x : R, IZR (Int_part x) <= x < IZR (Int_part x) + 1.
Proof.
  intro x.
  destruct (Raxioms.archimed x) as [Hup_gt Hup_le].
  unfold Int_part.
  split.
  - rewrite minus_IZR. simpl. lra.
  - rewrite minus_IZR. simpl. lra.
Qed.

(* 整数部分实数表示的上界 *)
Lemma Rlt_floor_IZR : forall z : Z, IZR (Int_part (IZR z)) <= IZR z.
Proof.
  intro z.
  destruct (archimed (IZR z)) as [H _].
  exact H.
Qed.

(* 除法不等式的等价形式 *)
Lemma Rlt_div_r : forall a b c, 0 < b -> (a / b < c <-> a < c * b).
Proof.
  intros a b c Hb.
  split.
  - intro H.
    apply (Rmult_lt_compat_r b) in H; [|exact Hb].
    unfold Rdiv in H.
    rewrite Rmult_assoc in H.
    rewrite Rinv_l in H; [|lra].
    rewrite Rmult_1_r in H.
    exact H.
  - intro H.
    apply (Rmult_lt_compat_r (/b)) in H; [|apply Rinv_0_lt_compat, Hb].
    rewrite Rmult_assoc in H.
    rewrite Rinv_r in H; [|lra].
    rewrite Rmult_1_r in H.
    unfold Rdiv.
    exact H.
Qed.

(* 指数与对数互逆 *)
Lemma ln_exp_1 : ln (exp 1) = 1.
Proof.
  apply ln_exp.
Qed.

(* 阶乘下界估计 *)
Lemma fact_ge_6_pow_n_minus_6_nat : forall n : nat, (n >= 6)%nat -> (fact n >= 720 * 6 ^ (n - 6))%nat.
Proof.
  intros n Hn.
  induction n as [n IH] using lt_wf_ind.
  destruct (Nat.eq_dec n 6) as [Heq|Hneq].
  - subst n. compute. lia.
  - assert (Hn_ge_7 : (n >= 7)%nat) by lia.
    destruct n as [|m]; [lia|].
    assert (Hm_ge_6 : (m >= 6)%nat) by lia.
    rewrite fact_simpl.
    replace (S m - 6)%nat with (S (m - 6))%nat by lia.
    assert (Hm_lt : (m < S m)%nat) by lia.
    apply IH in Hm_lt; [|exact Hm_ge_6].
    rewrite Nat.pow_succ_r' by lia.
    apply (Nat.le_trans _ (S m * (720 * 6 ^ (m - 6)))%nat).
    {
      rewrite Nat.mul_assoc at 1.
      rewrite Nat.mul_assoc.
      apply Nat.mul_le_mono_r.
      rewrite (Nat.mul_comm (S m)%nat 720%nat).
      apply Nat.mul_le_mono_l.
      lia.
    }
    {
      apply Nat.mul_le_mono_l.
      exact Hm_lt.
    }
Qed.

(* INR阶乘下界估计 *)
Lemma INR_fact_ge_6_pow_n_minus_6 : forall n : nat, (n >= 6)%nat -> 
  INR (fact n) >= 720 * (INR 6) ^ (n - 6).
Proof.
  intros n Hn.
  pose proof (fact_ge_6_pow_n_minus_6_nat n Hn) as Hnat.
  apply le_INR in Hnat.
  rewrite mult_INR in Hnat.
  rewrite pow_INR in Hnat.
  replace (INR 6) with 6 in Hnat by (simpl; ring).
  replace (INR 720) with 720 in Hnat by (simpl; ring).
  replace (INR 6) with 6 by (simpl; ring).
  apply Rle_ge.
  exact Hnat.
Qed.

(* Cmod：复数的模长 *)
Definition Cmod (z : Complex) : R := sqrt (re z ^ 2 + im z ^ 2).

(* Cdist：复数的距离（模长） *)
Definition Cdist (z1 z2 : Complex) : R := Cmod (z1 -c z2).

(* is_limit：复数序列的极限 *)
Definition is_limit (u : nat -> Complex) (l : Complex) : Prop :=
  forall ε : R, ε > 0 -> exists N : nat, forall n : nat, (n > N)%nat -> Cdist (u n) l < ε.

(* fun_approx_limit：极限定义版本的函数近似（要求序列收敛，使用 sig 类型携带极限值） *)
Definition fun_approx_limit (f : nat -> Complex) 
  (Hconv : {l : Complex | is_limit f l}) : Complex :=
  proj1_sig Hconv.

(* 简化命名 *)
Definition C1 := 1 +i 0.
Definition C0 := 0 +i 0.
Definition C2 := 2 +i 0.
Definition Cpi := PI +i 0.
Definition Chalf := (1/2)%R +i 0.

(* 实数幂：正实数 x 的 y 次幂 *)
Definition real_pow (x : R) (y : R) (Hx : 0 < x) : R :=
  exp (y * ln x).

(* 复数绝对值（模长） *)
Definition complex_abs (z : Complex) : R :=
  sqrt ((ComplexNumbers.re z)^2 + (ComplexNumbers.im z)^2).

(* 双参数反正切（atan2） *)
Definition my_arctan2 (y x : R) : R :=
  if Rgt_dec x 0 then
    atan (y / x)
  else if Rlt_dec x 0 then
    if Rge_dec y 0 then
      PI + atan (y / x)
    else
      -PI + atan (y / x)
  else
    if Rgt_dec y 0 then
      PI / 2
    else
      -PI / 2.

(* 非零复数的辐角（主值） *)
Definition complex_arg (z : Complex) (Hz : z <> C0) : R :=
  my_arctan2 (ComplexNumbers.im z) (ComplexNumbers.re z).

(* 复数绝对值正性 *)
Lemma lemma_complex_abs_pos : forall z : Complex, z <> C0 -> 0 < complex_abs z.
Proof.
  intros z Hz.
  unfold complex_abs.
  apply sqrt_lt_R0_c.
  destruct z as [a b]; simpl.
  apply Rnot_le_gt; intro Hle.
  assert (Heq: a * a + b * b = a * (a * 1) + b * (b * 1)) by ring.
  assert (Hle': a * a + b * b <= 0) by (rewrite Heq; exact Hle).
  clear Heq Hle.
  assert (Hsq_ge_0_a: 0 <= a * a) by (apply Rle_0_sqr).
  assert (Hsq_ge_0_b: 0 <= b * b) by (apply Rle_0_sqr).

  assert (H_a: a * a = 0).
  {
    apply Rle_antisym.
    - eapply Rle_trans with (a * a + b * b).
      + rewrite <- (Rplus_0_r (a * a)) at 1.
        apply Rplus_le_compat_l; exact Hsq_ge_0_b.
      + exact Hle'.
    - exact Hsq_ge_0_a.
  }
  assert (H_b: b * b = 0).
  {
    apply Rle_antisym.
    - eapply Rle_trans with (a * a + b * b).
      + rewrite <- (Rplus_0_l (b * b)) at 1.
        apply Rplus_le_compat_r; exact Hsq_ge_0_a.
      + exact Hle'.
    - exact Hsq_ge_0_b.
  }

  assert (Ha_eq: a² = a * a) by (unfold Rsqr; reflexivity).
  assert (Hb_eq: b² = b * b) by (unfold Rsqr; reflexivity).
  rewrite <- Ha_eq in H_a.
  rewrite <- Hb_eq in H_b.
  apply Rsqr_eq_0 in H_a.
  apply Rsqr_eq_0 in H_b.
  subst a b.
  contradiction Hz; reflexivity.
Qed.

(* [修复] my_complex_pow：角度公式原为 (im w)·θ + (re w)·ln r，实虚部角色对调；
   正确应为 (re w)·θ + (im w)·ln r（z^w = exp((re w)·ln r − (im w)·θ + i((re w)·θ + (im w)·ln r))）。
   修复后 zeta_series_term 才真正等于 n^{-s}。 *)
Definition my_complex_pow (z : Complex) (w : Complex) (Hz : z <> C0) : Complex :=
  let r := complex_abs z in
  let H_r_pos := lemma_complex_abs_pos z Hz in
  let w_re := ComplexNumbers.re w in
  let r_pow_re := real_pow r w_re H_r_pos in
  let theta := complex_arg z Hz in
  let exp_im := exp (-(ComplexNumbers.im w) * theta) in
  let re_part := r_pow_re * exp_im * cos (w_re * theta + (ComplexNumbers.im w) * ln r) in
  let im_part := r_pow_re * exp_im * sin (w_re * theta + (ComplexNumbers.im w) * ln r) in
  re_part +i im_part.

(* 复数序列收敛 *)
Definition Cseq_converges (u : nat -> Complex) (l : Complex) : Prop :=
  forall ε : R, ε > 0 -> exists N : nat, forall n : nat,
    (n > N)%nat -> 
    sqrt (((ComplexNumbers.re (u n -c l))^2) + ((ComplexNumbers.im (u n -c l))^2)) < ε.

(* 复数级数求和 *)
Definition Cseries_sum (u : nat -> Complex) (l : Complex) : Prop :=
  Cseq_converges (fun N => Csum u N) l.

(* [修复] 伽马被积函数：原实现为截断式 e^{-t}·t^{σ-1}·(1 + i·τ·ln t)，不是 t^{s-1}。
   真值：t^{s-1}·e^{-t} = e^{-t}·t^{σ-1}·(cos(τ·ln t) + i·sin(τ·ln t))，σ = re s，τ = im s。 *)
Definition gamma_integrand (s : Complex) (t : R) (Ht : 0 < t) : Complex :=
  let exponent := ComplexNumbers.re s - 1 in
  let t_pow := real_pow t exponent Ht in
  let angle := (ComplexNumbers.im s) * ln t in
  (exp (-t) * t_pow * cos angle) +i (exp (-t) * t_pow * sin angle).

(* 实数 Γ(σ) 被积函数（ca_gamma 的 Γ 积分段实际积分的是它：
   ∫₀^∞ e^{-t}·t^{σ-1} dt 对 σ > 1 收敛 = 实数伽马函数积分的收敛性）。
   注：gamma_integrand 的实部 = gamma_integrand_real · cos(τ ln t)，二者不同。 *)
Definition gamma_integrand_real (s : Complex) (t : R) (Ht : 0 < t) : R :=
  exp (-t) * Rpower t (ComplexNumbers.re s - 1).

(* 泽塔级数项 *)
Definition zeta_series_term (s : Complex) (n : nat) : Complex :=
  let n_R := INR (S n) in
  let n_complex := n_R +i 0 in
  let neg_s := -c s in
  my_complex_pow n_complex neg_s
    (let Hpos := lt_0_INR (S n) (Nat.lt_0_succ n) in
     let Hnz := Rgt_not_eq n_R 0 Hpos in
     fun Heq : n_complex = C0 => Hnz (f_equal re Heq)).

(* [清理] 已移除伪 ζ 定义（原为 1001 项有限截断 + 伪函数方程分支：γ 项在单点 t=1 取值，
   并非黎曼 ζ 函数；0 处使用）。Re(s) > 1 的级数收敛见 ca_gamma（zeta_series_converges）。 *)

(* 复数实部记号 *)
Notation "ℜ( z )" := (ComplexNumbers.re z) (at level 10, format "ℜ( z )").

(* 复数虚部记号 *)
Notation "ℑ( z )" := (ComplexNumbers.im z) (at level 10, format "ℑ( z )").

End PrimeEmbedding.
