(* 拆分自 Riemann_Hypothesis_Proof_Framework.v（复分析证明库 v6.0）*)
(* 库: ca_basis_lemmas  原文行区间: 26930-33542  机械拆分，未改动内容 *)

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

Require Import ca_base ca_algebra ca_primes ca_complex_analysis ca_fourier ca_zeta_scaffold ca_trig ca_gamma ca_taylor ca_zeta_axioms ca_complex_log ca_complex_foundation ca_log_bounds ca_independence ca_prime_power ca_basis.

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

(* ====================================================
   模块：UnconditionalBasisLemmas
   目的：为 psi_unconditional_basis 定理提供辅助引理
   ==================================================== *)

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

Module UnconditionalBasisLemmas.

(* ---------- 交叉项上界常数 ---------- *)
(* K 函数 *)
Definition K (C : R) : R :=
  let r := sqrt C in
  1 / (r - 1).

(* 左端点函数 和 右端点函数 *)
Definition A (C : R) : R := 1 - K C.
Definition B (C : R) : R := 1 + K C.

(* K 正性引理 *)
Lemma K_pos : forall C : nat, (C > 2)%nat -> (K (INR C) > 0)%R.
Proof.
  intros C Hc.
  unfold K.
  assert (H_C_gt_2 : (2 < C)%nat) by lia.
  assert (H_INR_C_gt_2 : (INR 2 < INR C)%R) by (apply lt_INR; exact H_C_gt_2).
  simpl in H_INR_C_gt_2.
  assert (H_INR_C_gt_1 : (1 < INR C)%R) by lra.
  (* 证明 sqrt (INR C) > 1 *)
  assert (H_sqrt_gt_1 : (1 < sqrt (INR C))%R).
  { destruct (Rle_or_lt (sqrt (INR C)) 1) as [Hle | Hgt].
    - apply Rsqr_incr_1 in Hle; [|apply sqrt_pos|apply Rlt_le; apply Rlt_0_1].
      unfold Rsqr in Hle; rewrite sqrt_sqrt in Hle; [|lra].
      lra.
    - exact Hgt. }
  (* 分母为正 *)
  assert (H_denom_pos : (sqrt (INR C) - 1 > 0)%R) by lra.
  (* 正数的倒数仍为正，再乘以 1 保持正性 *)
  apply Rmult_lt_0_compat.
  - apply Rlt_0_1.
  - apply Rinv_0_lt_compat. exact H_denom_pos.
Qed.

(* 充分大时 A 恒小于 B *)
Lemma A_lt_B : forall C : nat, (C > 2)%nat -> (A (INR C) < B (INR C))%R.
Proof.
  intros C Hc.
  unfold A, B.
  pose proof (K_pos C Hc) as Hk.
  lra.
Qed.

(* 充分大时 A 恒正 *)
Lemma A_pos : forall C : nat, (C > 4)%nat -> (A (INR C) > 0)%R.
Proof.
  intros C Hc.
  unfold A.
  assert (Hk_lt_1 : (K (INR C) < 1)%R).
  { unfold K.
    assert (H_C_gt_4 : (4 < C)%nat) by lia.
    assert (H_INR_C_gt_4 : (INR 4 < INR C)%R) by (apply lt_INR; exact H_C_gt_4).
    (* 证明 sqrt (INR C) > 2 *)
    assert (H_sqrt_gt_2 : (2%R < sqrt (INR C))%R).
    {
      apply Rnot_le_lt. intros Hle.
      apply Rsqr_incr_1 with (x := sqrt (INR C)) (y := 2%R) in Hle.
      - rewrite Rsqr_sqrt in Hle.
        + replace (2²)%R with 4%R in Hle by (unfold Rsqr; ring).
          replace 4%R with (INR 4) in Hle by (unfold INR; simpl; ring).
          apply (Rlt_not_le _ _ H_INR_C_gt_4). exact Hle.
        + left. apply Rlt_trans with (INR 4).
          * change 0%R with (INR 0). apply lt_INR; lia.
          * exact H_INR_C_gt_4.
      - apply sqrt_positivity. left. apply Rlt_trans with (INR 4).
        * change 0%R with (INR 0). apply lt_INR; lia.
        * exact H_INR_C_gt_4.
      - lra.
    }
    (* 分母 > 1 *)
    assert (H_denom_gt_1 : (sqrt (INR C) - 1 > 1)%R) by lra.
    apply Rinv_lt_contravar in H_denom_gt_1; [ | lra ].
    rewrite Rinv_1 in H_denom_gt_1.
    unfold Rdiv; rewrite Rmult_1_l; exact H_denom_gt_1.
  }
  (* 由 K < 1 推出 1 - K > 0 *)
  lra.
Qed.

Require Import Nat Lia.

(* seq 严格递增且单射 *)
Lemma seq_strictly_increasing_aux :
  forall (seq : nat -> nat) (Hinc : forall i : nat, (seq i < seq (S i))%nat),
  forall (i j : nat), (i < j)%nat -> (seq i < seq j)%nat.
Proof.
  intros seq Hinc i j Hlt.
  induction j as [|j IH] in i, Hlt |- *.
  - (* j = 0 时，i < 0 不可能 *)
    lia.
  - (* j = S j 的情况 *)
    destruct (Nat.eq_dec i j) as [->|Hne].
    + (* i = j *)
      apply Hinc.
    + (* i < j *)
      assert (i < j)%nat as H by lia.
      specialize (IH i H).
      (* 使用传递性：seq i < seq j < seq (S j) *)
      apply Nat.lt_trans with (seq j).
      * exact IH.
      * apply Hinc.
Qed.

(* 严格递增性与单射性 *)
Lemma seq_strictly_increasing :
  forall (seq : nat -> nat) (Hinc : forall i : nat, (seq i < seq (S i))%nat),
  (forall (i j : nat), (i < j)%nat -> (seq i < seq j)%nat) /\
  (forall (x y : nat), seq x = seq y -> x = y).
Proof.
  intros seq Hinc.
  split.
  - apply seq_strictly_increasing_aux; auto.
  - (* 单射性 *)
    intros x y Heq.
    destruct (Nat.lt_trichotomy x y) as [Hlt|[Heq'|Hgt]]; auto.
    + (* x < y 情形 *)
      exfalso.
      pose proof (seq_strictly_increasing_aux seq Hinc x y Hlt) as Hxy.
      lia. (* Hxy 是 seq x < seq y，与 Heq 矛盾 *)
    + (* y < x 情形 *)
      exfalso.
      pose proof (seq_strictly_increasing_aux seq Hinc y x Hgt) as Hyx.
      lia.
Qed.

(* vals 无重复 *)
Lemma NoDup_vals :
  forall (seq : nat -> nat) (I : list nat) (Hinj : forall x y, seq x = seq y -> x = y)
    (Hdup : NoDup I),
  NoDup (map seq I).
Proof.
  intros seq I Hinj Hdup.
  induction I as [|x xs IH]; simpl.
  - constructor.                     (* 空列表无重复 *)
  - inversion Hdup; subst.           (* 获取 NoDup xs 和 x ∉ xs *)
    constructor; [| apply IH; auto].
    intro Hin.                       (* 假设 seq x ∈ map seq xs *)
    apply in_map_iff in Hin.
    destruct Hin as [y [Hxy Hyin]].
    apply Hinj in Hxy; subst y.
    contradiction.
Qed.

(* vals 中元素均 ≥ 2 *)
Lemma vals_ge2 :
  forall (seq : nat -> nat) (I : list nat) (Hge2 : forall i, (seq i >= 2)%nat),
  forall v, In v (map seq I) -> (v >= 2)%nat.
Proof.
  intros seq I Hge2 v Hv.
  apply in_map_iff in Hv.                 (* 转化为存在量词 *)
  destruct Hv as [i [Heq _]].             (* 解构得到 i 和等式 *)
  subst v.                                (* 将 v 替换为 seq i *)
  apply Hge2.                             (* 应用全局条件 *)
Qed.

(* 复数单位模为一 *)
Lemma Cnorm_C1 : ComplexNumbers.Cnorm ComplexNumbers.C1 = 1%R.
Proof.
  unfold ComplexNumbers.Cnorm, ComplexNumbers.Cnorm_sq, ComplexNumbers.C1; simpl.
  rewrite Rsqr_1, Rsqr_0, Rplus_0_r.
  apply sqrt_1.
Qed.

(* 对角内积模一 *)
Lemma inner_diag_norm1 :
  forall (vals : list nat) (M i : nat)
    (H_norm_assump : forall v, In v vals -> (v >= 2)%nat)
    (Hvals_ge2 : (i < length vals)%nat)
    (M_eq_n : M = nth i vals 0%nat),
  let inner := independent.Csum
                (fun k => psi (nth i vals 0%nat) k *c ComplexNumbers.Cconj (psi (nth i vals 0%nat) k))
                M in
  ComplexNumbers.Cnorm inner = 1%R.
Proof.
  intros vals M i H_norm_assump Hvals_ge2 M_eq_n.
  set (n := nth i vals 0%nat).
  rewrite M_eq_n.
  (* 由假设知 n >= 2，故 n > 0 *)
  assert (n >= 2)%nat by (apply H_norm_assump, nth_In; assumption).
  assert (norm_one : independent.Csum (fun k => psi n k *c ComplexNumbers.Cconj (psi n k)) n = C1).
  { apply Csum_orthonormal_self. lia. }
  change (ComplexNumbers.Cnorm (independent.Csum (fun k => psi n k *c Cconj (psi n k)) n) = 1%R).
  rewrite norm_one.
  apply Cnorm_C1.
Qed.

(* 序列值不小于二 *)
Lemma seq_vals_ge2 :
  forall (seq : nat -> nat) (c : nat)
    (Hc_ge1 : (c >= 1)%nat)
    (Hbase : (seq 0 >= 2)%nat)
    (Hsparse : forall idx, (INR (seq (S idx)) > INR c * INR (seq idx))%R)
    (I : list nat) (n : nat),
  In n (map seq I) -> (n >= 2)%nat.
Proof.
  intros seq c Hc_ge1 Hbase Hsparse I n Hin.
  apply in_map_iff in Hin.
  destruct Hin as [i [Heq _]].
  assert (H_all : forall idx : nat, (seq idx >= 2)%nat).
  {
    induction idx as [| idx IH].
    - exact Hbase.
    - assert (Hc_R_ge1 : (INR c >= 1)%R).
      {
        assert (H1 : (1 <= c)%nat) by lia.
        apply le_INR in H1.
        simpl in H1.
        lra.
      }
      assert (Hseq_idx_R_ge2 : (INR (seq idx) >= 2)%R).
      {
        assert (H3 : (2 <= seq idx)%nat) by lia.
        apply le_INR in H3.
        simpl in H3.
        lra.
      }
      assert (Hmul_ge2 : (INR c * INR (seq idx) >= 2)%R).
      {
        assert (H5 : (INR c * INR (seq idx) >= 1 * INR (seq idx))%R).
        {
          apply Rmult_ge_compat_r; lra; apply pos_INR.
        }
        assert (H6 : (1 * INR (seq idx) = INR (seq idx))%R) by ring.
        rewrite H6 in H5.
        lra.
      }
      assert (Hseq_S_R_gt2 : (INR (seq (S idx)) > 2)%R).
      {
        specialize (Hsparse idx).
        lra.
      }
      assert (H_INR2_eq : (INR 2 = 2)%R) by (simpl; lra).
      rewrite <- H_INR2_eq in Hseq_S_R_gt2.
      assert (H_nat_gt : (2 < seq (S idx))%nat).
      {
        apply INR_lt.
        lra.
      }
      lia.
  }
  assert (H_main : (seq i >= 2)%nat) by apply H_all.
  rewrite Heq in H_main.
  exact H_main.
Qed.

(* 严格递增函数必为单射函数 *)
Lemma strict_injective :
  forall (seq : nat -> nat),
    (forall i j : nat, i < j -> seq i < seq j) ->
    (forall x y : nat, seq x = seq y -> x = y).
Proof.
  intros seq Hstrict x y Heq.
  destruct (Nat.lt_trichotomy x y) as [Hxy_lt | [Hxy_eq | Hxy_gt]].
  - (* 情况1：x < y，导出矛盾 *)
    exfalso.
    assert (Hseq_lt : seq x < seq y).
      { apply Hstrict. exact Hxy_lt. }
    rewrite Heq in Hseq_lt.
    apply Nat.lt_irrefl with (seq y) in Hseq_lt.
    exact Hseq_lt.
  - (* 情况2：x = y，直接得证 *)
    exact Hxy_eq.
  - (* 情况3：x > y，导出矛盾 *)
    exfalso.
    assert (Hyx_lt : y < x) by lia.
    assert (Hseq_lt : seq y < seq x).
      { apply Hstrict. exact Hyx_lt. }
    rewrite <- Heq in Hseq_lt.
    apply Nat.lt_irrefl with (seq x) in Hseq_lt.
    exact Hseq_lt.
Qed.

(* 映射严格递增序列保持无重复 *)
Lemma map_seq_nodup :
  forall (seq : nat -> nat) (I : list nat),
    (forall i j, i < j -> seq i < seq j) ->
    NoDup I ->
    NoDup (map seq I).
Proof.
  intros seq I Hstrict Hndup.
  induction Hndup as [| h t Hnin Hndup IH].
  - constructor.
  - simpl.
    constructor.
    + intro Hcontra.
      apply in_map_iff in Hcontra as [x [Hseq_eq Hx_in_t]].
      assert (Hinj : forall x y, seq x = seq y -> x = y).
      { apply strict_injective. exact Hstrict. }
      assert (Hx_eq_h : x = h).
      { apply Hinj. exact Hseq_eq. }
      rewrite Hx_eq_h in Hx_in_t.
      contradiction.
    + exact IH.
Qed.

(* 共轭的范数相等 *)
Lemma Cnorm_conj_eq : forall z : Complex, Cnorm (Cconj z) = Cnorm z.
Proof.
  intros [x y].
  unfold Cnorm, Cnorm_sq, Cconj, Rsqr; simpl.
  f_equal.
  ring.
Qed.

(* 截断求和尾部为零引理 *)
Lemma Csum_trunc_tail :
  forall (f : nat -> Complex) (M N : nat),
    M <= N ->
    (forall k, M <= k < N -> f k = C0) ->
    Csum f N = Csum f M.
Proof.
  intros f M N Hle Hzero.
  assert (Hex : exists m : nat, N = M + m).
  { exists (N - M). lia. }
  destruct Hex as [m Heq].
  rewrite Heq.
  rewrite Csum_split'.
  assert (Htail_zero : Csum (fun i : nat => f (M + i)) m = C0).
  { apply sum_zero.
    intros j Hj.
    assert (H_ge : M <= M + j) by lia.
    assert (H_lt : M + j < M + m) by lia.
    assert (Hbound_raw : M <= M + j < M + m) by (split; [exact H_ge | exact H_lt]).
    assert (Hbound : M <= M + j < N).
    { rewrite Heq. exact Hbound_raw. }
    exact (Hzero (M + j) Hbound).
  }
  rewrite Htail_zero.
  rewrite Cadd_0_r.
  reflexivity.
Qed.

(* 尾部零值求和截断 *)
Lemma Csum_trunc_tail_original_form :
  forall (f : nat -> Complex) (M N : nat),
    M >= 1 ->
    N >= 1 ->
    M <= N ->
    (forall k, M-1 <= k < N-1 -> f k = C0) ->
    Csum f (N-1) = Csum f (M-1).
Proof.
  intros f M N Hm_ge1 Hn_ge1 Hle Hzero.
  apply Csum_trunc_tail with (M := M-1) (N := N-1).
  - lia.
  - exact Hzero.
Qed.

(* 大指标时psi为零 *)
Lemma psi_zero_for_ge_n :
  forall n k, (n <= k)%nat -> psi n k = C0.
Proof.
  intros n k Hle.
  unfold psi.
  assert (H_phi_eq : phi n k = C0).
  {
    apply phi_ge_n_zero.
    lia.
  }
  rewrite H_phi_eq.
  apply Cmul_0_r.
Qed.

Require Import Stdlib.Reals.Reals.
Local Open Scope R_scope.

(* psi 内积求和的常数提取与展开 *)
Lemma inner_expand :
  forall n1 n2 : nat,
    (n1 >= 2)%nat -> (n2 >= 2)%nat -> (n1 <= n2)%nat ->
    Csum (fun k => psi n1 k *c Cconj (psi n2 k)) (n1 - 1) =
    (Cof_real (1 / sqrt (INR n1)) *c Cof_real (1 / sqrt (INR n2))) *c
    Csum (fun k => Cexp (0 +i (INR k * (2 * PI * (1 / INR n1 - 1 / INR n2))))) (n1 - 1).
Proof.
  intros n1 n2 Hn1_ge2 Hn2_ge2 Hn1_le_n2.

  assert (Cconj_mul : forall a b : Complex, Cconj (a *c b) = Cconj a *c Cconj b).
  {
    intros [x y] [u v].
    unfold Cconj, Cmul.
    simpl.
    apply Complex_eq; simpl; ring.
  }

  assert (Cconj_Cof_real : forall r : R, Cconj (Cof_real r) = Cof_real r).
  {
    intros r.
    unfold Cof_real, Cconj.
    simpl.
    apply Complex_eq; simpl; ring.
  }

  assert (Cconj_exp_iθ : forall θ : R, Cconj (Cexp (0 +i θ)) = Cexp (0 +i (Ropp θ))).
  {
    intros θ.
    unfold Cexp, Cconj.
    simpl.
    rewrite cos_neg, sin_neg.
    simpl.
    apply Complex_eq; simpl; ring.
  }

  assert (Cadd_pure_imag : forall θ1 θ2 : R, (0 +i θ1) +c (0 +i θ2) = (0 +i (θ1 + θ2))).
  {
    intros θ1 θ2.
    unfold Cadd.
    simpl.
    apply Complex_eq; simpl; ring.
  }

  assert (Cexp_mul_i : forall θ1 θ2 : R,
    Cexp (0 +i θ1) *c Cexp (0 +i θ2) = Cexp (0 +i (θ1 + θ2))).
  {
    intros θ1 θ2.
    rewrite <- Cexp_add.
    rewrite Cadd_pure_imag.
    reflexivity.
  }

  assert (Csum_scal_l : forall (c : Complex) (f : nat -> Complex) (n : nat),
    Csum (fun k => c *c f k) n = c *c Csum f n).
  {
    intros c f n.
    induction n as [|n IH].
    - simpl; rewrite Cmul_0_r; reflexivity.
    - simpl; rewrite IH, Cmul_add_distr_l; reflexivity.
  }

  assert (Csum_ext' : forall (f g : nat -> Complex) (n : nat),
    (forall i, (i < n)%nat -> f i = g i) -> Csum f n = Csum g n).
  {
    induction n as [|n IH]; intros H.
    - simpl; reflexivity.
    - simpl; rewrite IH; [f_equal; apply H; lia | intros; apply H; lia].
  }

  assert (H_phi_n1 : forall k : nat, (k < n1)%nat ->
    phi n1 k = Cexp (0 +i (2 * PI * INR k / INR n1))).
  {
    intros k Hk.
    unfold phi.
    assert (Hltb1 : (k <? n1) = true) by (apply Nat.ltb_lt; exact Hk).
    rewrite Hltb1.
    reflexivity.
  }

  assert (H_phi_n2 : forall k : nat, (k < n1)%nat ->
    phi n2 k = Cexp (0 +i (2 * PI * INR k / INR n2))).
  {
    intros k Hk.
    unfold phi.
    assert (Hk_lt_n2 : (k < n2)%nat) by lia.
    assert (Hltb2 : (k <? n2) = true) by (apply Nat.ltb_lt; exact Hk_lt_n2).
    rewrite Hltb2.
    reflexivity.
  }

  assert (H_INR_n1_nonzero : INR n1 <> 0).
  {
    apply Rgt_not_eq, lt_0_INR.
    lia.
  }
  assert (H_INR_n2_nonzero : INR n2 <> 0).
  {
    apply Rgt_not_eq, lt_0_INR.
    lia.
  }

  assert (H_sqrt_n1_nonzero : sqrt (INR n1) <> 0).
  {
    apply Rgt_not_eq.
    apply sqrt_lt_R0_c.
    apply lt_0_INR.
    lia.
  }
  assert (H_sqrt_n2_nonzero : sqrt (INR n2) <> 0).
  {
    apply Rgt_not_eq.
    apply sqrt_lt_R0_c.
    apply lt_0_INR.
    lia.
  }

  assert (H_theta_eq : forall k : nat,
    2 * PI * INR k / INR n1 + Ropp (2 * PI * INR k / INR n2) =
    INR k * (2 * PI * (1 / INR n1 - 1 / INR n2))).
  {
    intros k.
    field.
    all: auto.
  }

  assert (Cmul_assoc : forall a b c : Complex, (a *c b) *c c = a *c (b *c c)).
  {
    intros [x1 y1] [x2 y2] [x3 y3].
    unfold Cmul, Cadd.
    simpl.
    apply Complex_eq; simpl; ring.
  }

  assert (Cmul_comm : forall a b : Complex, a *c b = b *c a).
  {
    intros [x1 y1] [x2 y2].
    unfold Cmul.
    simpl.
    apply Complex_eq; simpl; ring.
  }

  assert (H_term_eq : forall k : nat, (k < n1 - 1)%nat ->
    psi n1 k *c Cconj (psi n2 k) =
    (Cof_real (1 / sqrt (INR n1)) *c Cof_real (1 / sqrt (INR n2))) *c
    Cexp (0 +i (INR k * (2 * PI * (1 / INR n1 - 1 / INR n2))))).
  {
    intros k Hk.
    set (c1 := Cof_real (1 / sqrt (INR n1))).
    set (c2 := Cof_real (1 / sqrt (INR n2))).
    set (phi1 := phi n1 k).
    set (phi2 := phi n2 k).

    assert (H_psi1 : psi n1 k = c1 *c phi1) by reflexivity.
    assert (H_psi2 : psi n2 k = c2 *c phi2) by reflexivity.
    rewrite H_psi1, H_psi2.
    rewrite Cconj_mul.
    assert (Hc2_conj : Cconj c2 = c2) by (unfold c2; apply Cconj_Cof_real).
    rewrite Hc2_conj.

    assert (Hk_lt_n1 : (k < n1)%nat) by lia.
    assert (Hphi1_eq : phi1 = Cexp (0 +i (2 * PI * INR k / INR n1)))
      by (unfold phi1; apply H_phi_n1; exact Hk_lt_n1).
    assert (Hphi2_eq : phi2 = Cexp (0 +i (2 * PI * INR k / INR n2)))
      by (unfold phi2; apply H_phi_n2; exact Hk_lt_n1).
    assert (Hconj_phi2 : Cconj phi2 = Cexp (0 +i - (2 * PI * INR k / INR n2)))
      by (rewrite Hphi2_eq; apply Cconj_exp_iθ).

    assert (Hphi_mul : phi1 *c Cconj phi2 = Cexp (0 +i (INR k * (2 * PI * (1 / INR n1 - 1 / INR n2))))).
    {
      rewrite Hphi1_eq, Hconj_phi2.
      rewrite Cexp_mul_i.
      rewrite H_theta_eq.
      reflexivity.
    }

    assert (Hmul_rearrange : (c1 *c phi1) *c (c2 *c Cconj phi2) = (c1 *c c2) *c (phi1 *c Cconj phi2)).
    {
      rewrite Cmul_assoc.
      assert (Htmp : phi1 *c (c2 *c Cconj phi2) = c2 *c (phi1 *c Cconj phi2)).
      {
        rewrite <- Cmul_assoc.
        rewrite (Cmul_comm phi1 c2).
        rewrite Cmul_assoc.
        reflexivity.
      }
      rewrite Htmp.
      rewrite <- Cmul_assoc.
      reflexivity.
    }

    rewrite Hmul_rearrange.
    rewrite Hphi_mul.
    reflexivity.
  }

  assert (H_sum_eq : Csum (fun k => psi n1 k *c Cconj (psi n2 k)) (n1 - 1) =
    Csum (fun k => (Cof_real (1 / sqrt (INR n1)) *c Cof_real (1 / sqrt (INR n2))) *c
      Cexp (0 +i (INR k * (2 * PI * (1 / INR n1 - 1 / INR n2))))) (n1 - 1)).
  {
    apply Csum_ext'.
    intros i Hi.
    apply H_term_eq.
    exact Hi.
  }

  rewrite H_sum_eq.
  rewrite Csum_scal_l.
  reflexivity.
Qed.

(* 余弦的整数倍周期 *)

(* 余弦整数倍周期恒等定理 *)
Theorem cos_periodic_int : forall (x : R) (k : Z), cos (x + 2 * PI * IZR k) = cos x.
Proof.
  intros x k.
  (* 自然数倍正周期成立 *)
  assert (H_nat_pos : forall (n : nat), cos (x + 2 * PI * INR n) = cos x).
  {
    intros n.
    induction n as [|n IH].
    - (* 基例 n=0 *)
      assert (H_INR0 : INR 0 = 0) by reflexivity.
      rewrite H_INR0.
      rewrite Rmult_0_r.
      rewrite Rplus_0_r.
      reflexivity.
    - (* 归纳步 *)
      assert (H_expand : 2 * PI * INR (S n) = 2 * PI * INR n + 2 * PI).
      { rewrite S_INR. rewrite Rmult_plus_distr_l. ring. }
      rewrite H_expand.
      assert (H_plus_assoc : x + (2 * PI * INR n + 2 * PI) = (x + 2 * PI * INR n) + 2 * PI).
      { ring. }
      rewrite H_plus_assoc.
      rewrite cos_plus.
      rewrite cos_2PI, sin_2PI.
      rewrite Rmult_1_r, Rmult_0_r, Rminus_0_r.
      exact IH.
  }
  (* 自然数倍负周期成立 *)
  assert (H_nat_neg : forall (n : nat), cos (x + 2 * PI * (- INR n)) = cos x).
  {
    intros n.
    induction n as [|n IH].
    - (* 基例 n=0 *)
      assert (H_INR0 : INR 0 = 0) by reflexivity.
      rewrite H_INR0.
      assert (H_ropp0 : - (0 : R) = 0) by ring.
      rewrite H_ropp0.
      assert (H_mul0 : 2 * PI * 0 = 0) by ring.
      rewrite H_mul0.
      assert (H_add0 : x + 0 = x) by ring.
      rewrite H_add0.
      reflexivity.
    - (* 归纳步 *)
      assert (H_expand : 2 * PI * (- INR (S n)) = 2 * PI * (- INR n) - 2 * PI).
      { rewrite S_INR. rewrite Ropp_plus_distr. rewrite Rmult_plus_distr_l. ring. }
      rewrite H_expand.
      assert (H_plus_assoc : x + (2 * PI * (- INR n) - 2 * PI) = (x + 2 * PI * (- INR n)) + (-2 * PI)).
      { ring. }
      rewrite H_plus_assoc.
      set (A := x + 2 * PI * (- INR n)) in *.
      rewrite (cos_plus A (-2 * PI)).
      assert (H_opp_eq : -2 * PI = Ropp (2 * PI)) by ring.
      assert (H_cos_neg2PI : cos (-2 * PI) = 1).
      { rewrite H_opp_eq. rewrite cos_neg. rewrite cos_2PI. reflexivity. }
      assert (H_sin_neg2PI : sin (-2 * PI) = 0).
      { rewrite H_opp_eq. rewrite sin_neg. rewrite sin_2PI. ring. }
      rewrite H_cos_neg2PI, H_sin_neg2PI.
      rewrite IH.
      ring.
  }
  (* 自然数到整数的映射一致性 *)
  assert (H_nat_IZR_eq : forall (n : nat), IZR (Z.of_nat n) = INR n).
  {
    intros n.
    induction n as [|n IH].
    - (* 基例 *)
      reflexivity.
    - (* 归纳步 *)
      assert (H_step : Z.of_nat (S n) = (Z.of_nat n + 1)%Z).
      { lia. }
      rewrite H_step.
      rewrite plus_IZR.
      rewrite IH.
      rewrite S_INR.
      reflexivity.
  }
  (* 根据 k 的符号分类讨论 *)
  destruct (Z_le_dec 0 k) as [H_nonneg | H_neg].
  - (* 情况1：k ≥ 0 *)
    assert (H_k_eq : Z.of_nat (Z.to_nat k) = k).
    { apply Z2Nat.id; exact H_nonneg. }
    rewrite <- H_k_eq.
    rewrite H_nat_IZR_eq.
    apply H_nat_pos.
  - (* 情况2：k < 0 *)
    assert (H_neg_k : (0 <= -k)%Z) by lia.
    assert (H_neg_k_eq : Z.of_nat (Z.to_nat (-k)) = (- k)%Z).
    { apply Z2Nat.id; exact H_neg_k. }
    assert (H_IZR_eq : IZR (Z.of_nat (Z.to_nat (-k))) = IZR (-k)).
    { f_equal; exact H_neg_k_eq. }
    rewrite H_nat_IZR_eq in H_IZR_eq.
    rewrite opp_IZR in H_IZR_eq.
    replace (IZR k) with (- INR (Z.to_nat (-k))).
    2:{ rewrite H_IZR_eq; ring. }
    apply H_nat_neg.
Qed.

(* 正弦整数倍周期恒等定理 *)
Theorem sin_periodic_int : forall (x : R) (k : Z), sin (x + 2 * PI * IZR k) = sin x.
Proof.
  intros x k.
  (* 自然数倍正周期成立 *)
  assert (H_nat_pos : forall (n : nat), sin (x + 2 * PI * INR n) = sin x).
  {
    intros n.
    induction n as [|n IH].
    - (* 基例 n=0 *)
      assert (H_INR0 : INR 0 = 0) by reflexivity.
      rewrite H_INR0.
      rewrite Rmult_0_r.
      rewrite Rplus_0_r.
      reflexivity.
    - (* 归纳步 *)
      assert (H_expand : 2 * PI * INR (S n) = 2 * PI * INR n + 2 * PI).
      { rewrite S_INR. rewrite Rmult_plus_distr_l. ring. }
      rewrite H_expand.
      assert (H_plus_assoc : x + (2 * PI * INR n + 2 * PI) = (x + 2 * PI * INR n) + 2 * PI).
      { ring. }
      rewrite H_plus_assoc.
      rewrite sin_plus.
      rewrite sin_2PI, cos_2PI.
      rewrite Rmult_0_r, Rmult_1_r, Rplus_0_r.
      exact IH.
  }
  (* 自然数倍负周期成立 *)
  assert (H_nat_neg : forall (n : nat), sin (x + 2 * PI * (- INR n)) = sin x).
  {
    intros n.
    induction n as [|n IH].
    - (* 基例 n=0 *)
      assert (H_INR0 : INR 0 = 0) by reflexivity.
      rewrite H_INR0.
      assert (H_ropp0 : - (0 : R) = 0) by ring.
      rewrite H_ropp0.
      assert (H_mul0 : 2 * PI * 0 = 0) by ring.
      rewrite H_mul0.
      assert (H_add0 : x + 0 = x) by ring.
      rewrite H_add0.
      reflexivity.
    - (* 归纳步 *)
      assert (H_expand : 2 * PI * (- INR (S n)) = 2 * PI * (- INR n) - 2 * PI).
      { rewrite S_INR. rewrite Ropp_plus_distr. rewrite Rmult_plus_distr_l. ring. }
      rewrite H_expand.
      assert (H_plus_assoc : x + (2 * PI * (- INR n) - 2 * PI) = (x + 2 * PI * (- INR n)) + (-2 * PI)).
      { ring. }
      rewrite H_plus_assoc.
      set (A := x + 2 * PI * (- INR n)) in *.
      rewrite sin_plus.
      assert (H_sin_neg2PI : sin (-2 * PI) = 0).
      { replace (-2 * PI) with (- (2 * PI)) by ring.
        rewrite sin_neg. rewrite sin_2PI. ring. }
      assert (H_cos_neg2PI : cos (-2 * PI) = 1).
      { replace (-2 * PI) with (- (2 * PI)) by ring.
        rewrite cos_neg. rewrite cos_2PI. reflexivity. }
      rewrite H_sin_neg2PI, H_cos_neg2PI.
      rewrite Rmult_0_r, Rmult_1_r, Rplus_0_r.
      exact IH.
  }
  (* 自然数→整数→实数的映射一致性 *)
  assert (H_nat_IZR_eq : forall (n : nat), IZR (Z.of_nat n) = INR n).
  {
    intros n.
    induction n as [|n IH].
    - reflexivity.
    - assert (H_step : Z.of_nat (S n) = (Z.of_nat n + 1)%Z) by lia.
      rewrite H_step.
      rewrite plus_IZR.
      rewrite IH.
      rewrite S_INR.
      reflexivity.
  }
  (* 根据 k 的符号分类讨论 *)
  destruct (Z_le_dec 0 k) as [H_nonneg | H_neg].
  - (* 情况1：k ≥ 0 *)
    assert (H_k_eq : Z.of_nat (Z.to_nat k) = k).
    { apply Z2Nat.id; exact H_nonneg. }
    rewrite <- H_k_eq.
    rewrite H_nat_IZR_eq.
    apply H_nat_pos.
  - (* 情况2：k < 0 *)
    assert (H_neg_k : (0 <= -k)%Z) by lia.
    assert (H_neg_k_eq : Z.of_nat (Z.to_nat (-k)) = (- k)%Z).
    { apply Z2Nat.id; exact H_neg_k. }
    assert (H_IZR_eq : IZR (Z.of_nat (Z.to_nat (-k))) = IZR (-k)).
    { f_equal; exact H_neg_k_eq. }
    rewrite H_nat_IZR_eq in H_IZR_eq.
    rewrite opp_IZR in H_IZR_eq.
    replace (IZR k) with (- INR (Z.to_nat (-k))).
    2:{ rewrite H_IZR_eq; ring. }
    apply H_nat_neg.
Qed.

(* 复指数为一时余弦为一正弦为零 *)
Lemma cexp_eq_1_implies_cos1_sin0 :
  forall θ : R,
    (1 +i 0) -c Cexp (0 +i θ) = C0 ->
    cos θ = 1 /\ sin θ = 0.
Proof.
  intros θ H_contra.
  set (z := Cexp (0 +i θ)).
  assert (H_add : (1 +i 0) +c (-c z) = C0) by (rewrite Csub_def in H_contra; exact H_contra).
  assert (H_step1 : ((1 +i 0) +c (-c z)) +c z = C0 +c z) by (apply f_equal with (f := fun x => x +c z); exact H_add).
  assert (H_assoc : ((1 +i 0) +c (-c z)) +c z = (1 +i 0) +c ((-c z) +c z)) by apply Cadd_assoc.
  assert (H_opp : (-c z) +c z = C0) by (rewrite Cadd_comm; apply Cadd_opp_r).
  assert (H_left : (1 +i 0) +c C0 = (1 +i 0)) by apply Cadd_0_r.
  assert (H_right : C0 +c z = z) by apply Cadd_0_l.
  rewrite H_assoc in H_step1.
  rewrite H_opp in H_step1.
  rewrite H_left in H_step1.
  rewrite H_right in H_step1.
  symmetry in H_step1.
  unfold z, Cexp in H_step1; simpl in H_step1.
  rewrite exp_0 in H_step1; simpl in H_step1.
  injection H_step1 as H_cos_raw H_sin_raw.
  split.
  - ring_simplify in H_cos_raw; exact H_cos_raw.
  - ring_simplify in H_sin_raw; exact H_sin_raw.
Qed.

(* 余弦为1的角度归约 *)
Lemma reduce_angle_to_0_2pi :
  forall θ : R,
    cos θ = 1 ->
    exists (r : R) (k : Z),
      0 <= r < 2 * PI /\
      θ = 2 * PI * IZR k + r /\
      cos r = 1.
Proof.
  intros θ H_cos.
  set (q := θ / (2 * PI)).
  assert (H_PI_neq0 : PI <> 0) by (apply Rgt_not_eq, PI_RGT_0).
  assert (Heq : 2 * PI * q = θ) by (unfold q; field; exact H_PI_neq0).
  destruct (archimed q) as [Hq_lt Hq_le].
  set (k := (up q - 1)%Z).
  exists (θ - 2 * PI * IZR k), k.
  assert (H_r_bounds : 0 <= θ - 2 * PI * IZR k < 2 * PI).
  {
    rewrite <- Heq.
    unfold k.
    replace (IZR (up q - 1)) with (IZR (up q) - 1)
      by (rewrite <- minus_IZR; reflexivity).
    rewrite <- Rmult_minus_distr_l.
    replace (q - (IZR (up q) - 1)) with ((q + 1) - IZR (up q)) by ring.
    split.
    - apply Rmult_le_pos.
      { left. apply Rmult_lt_0_compat; [lra | apply PI_RGT_0]. }
      apply Rplus_le_compat_r with (r := q) in Hq_le.
      ring_simplify in Hq_le.
      apply Rplus_le_reg_l with (IZR (up q)).
      rewrite Rplus_0_r.
      ring_simplify (IZR (up q) + ((q + 1) - IZR (up q))).
      exact Hq_le.
    - apply Rmult_lt_reg_l with (/ (2 * PI)).
      { apply Rinv_0_lt_compat.
        apply Rmult_lt_0_compat; [lra | apply PI_RGT_0]. }
      rewrite <- (Rmult_assoc (/ (2 * PI)) (2 * PI) ((q + 1) - IZR (up q))).
      rewrite Rinv_l.
      2: { apply Rgt_not_eq. apply Rmult_lt_0_compat; [lra | apply PI_RGT_0]. }
      rewrite Rmult_1_l.
      apply Rminus_lt.
      ring_simplify.
      lra.
  }
  assert (H_r_cos : cos (θ - 2 * PI * IZR k) = 1).
  {
    rewrite <- (cos_periodic_int (θ - 2 * PI * IZR k) k).
    replace (θ - 2 * PI * IZR k + 2 * PI * IZR k) with θ by ring.
    exact H_cos.
  }
  split; [exact H_r_bounds | split; [ring | exact H_r_cos]].
Qed.

(* 余弦为一正弦为零则角度为零 *)
Lemma cos1_sin0_in_0_2pi_implies_0 :
  forall r : R,
    0 <= r < 2 * PI ->
    cos r = 1 ->
    sin r = 0 ->
    r = 0.
Proof.
  intros r [Hr_ge0 Hr_lt2π] H_cos H_sin.
  destruct (Rle_lt_or_eq_dec 0 r Hr_ge0) as [Hr_pos | Hr_zero].
  - destruct (sin_eq_0_0 r H_sin) as [k Hk].
    assert (Hk_gt0 : (0 < k)%Z).
      apply lt_IZR.
      apply (Rmult_lt_reg_l PI).
      apply PI_RGT_0.
      rewrite Rmult_0_r.
      rewrite (Rmult_comm PI (IZR k)).
      rewrite <- Hk.
      exact Hr_pos.
    assert (Hk_lt2 : (k < 2)%Z).
      apply lt_IZR.
      apply (Rmult_lt_reg_l PI).
      apply PI_RGT_0.
      rewrite (Rmult_comm PI (IZR k)).
      rewrite <- Hk.
      apply Rlt_le_trans with (2 * PI).
      exact Hr_lt2π.
      right. unfold IZR. simpl. ring.
    assert (k = 1)%Z by lia.
    subst k.
    rewrite Hk in H_cos.
    replace (IZR 1 * PI) with PI in H_cos by (rewrite Rmult_1_l; reflexivity).
    rewrite cos_PI in H_cos.
    lra.
  - symmetry. exact Hr_zero.
Qed.

(* 非周期角复指数非幺元定理 *)
Theorem geometric_denom_nonzero_simple :
  forall θ : R,
    (forall k : Z, θ <> 2 * PI * IZR k) ->
    (1 +i 0) -c Cexp (0 +i θ) <> C0.
Proof.
  intros θ H_theta H_contra.
  apply cexp_eq_1_implies_cos1_sin0 in H_contra.
  destruct H_contra as [H_cos H_sin].
  apply reduce_angle_to_0_2pi in H_cos.
  destruct H_cos as [r [k [Hr_bounds [Heq Hr_cos]]]].

  assert (Hr_neq0 : r <> 0).
  { intro Hr0. subst r.
    rewrite Rplus_0_r in Heq.
    apply (H_theta k). exact Heq. }

  assert (H_cos_2PIk : cos (2 * PI * IZR k) = 1).
  { rewrite <- cos_0.
    replace (2 * PI * IZR k) with (0 + 2 * PI * IZR k) by ring.
    rewrite cos_periodic_int with (x := 0) (k := k).
    reflexivity. }

  assert (Hr_sin : sin r = 0).
  { rewrite Heq in H_sin.
    rewrite sin_plus in H_sin.
    assert (H_sin_2PIk : sin (2 * PI * IZR k) = 0).
    { rewrite <- sin_0.
      replace (2 * PI * IZR k) with (0 + 2 * PI * IZR k) by ring.
      rewrite sin_periodic_int with (x := 0) (k := k).
      reflexivity. }
    rewrite H_sin_2PIk, H_cos_2PIk in H_sin.
    rewrite Rmult_0_l, Rmult_1_l, Rplus_0_l in H_sin.
    exact H_sin. }

  assert (r = 0) by (apply (cos1_sin0_in_0_2pi_implies_0 r Hr_bounds Hr_cos Hr_sin)).
  contradiction.
Qed.

Import ComplexNumbers.

(* 复几何级数求和 *)
Lemma Csum_geometric_complex :
  forall (z : Complex) (n : nat),
    z <> C1 ->
    forall (H_nz : Cnorm_sq (C1 -c z) <> 0),
    Csum (fun k => z ^ k) n = 
    Cdiv (C1 -c z ^ n) (C1 -c z) H_nz.
Proof.
  intros z n Hz H_nz.
  unfold Cdiv.
  apply (Csum_geometric z n Hz).
Qed.

(* θ角绝对值有界 *)
Lemma theta_bound_pi :
  forall n1 n2 : nat,
    (n1 >= 2)%nat -> (n2 >= 2)%nat -> (n1 <= n2)%nat ->
    let θ := 2 * PI * (/ INR n1 - / INR n2) in
    Rabs θ <= PI.
Proof.
  intros n1 n2 H1 H2 Hle.
  set (θ := 2 * PI * (/ INR n1 - / INR n2)).
  unfold θ.
  rewrite Rabs_mult.
  rewrite (Rabs_right (2 * PI)).
  2: { apply Rle_ge; apply Rmult_le_pos; [lra | apply Rlt_le; apply PI_RGT_0]. }
  rewrite Rabs_pos_eq.
  2: {
    apply Rle_minus_swap.            (* 复用框架中的 Rle_minus_swap *)
    apply Rinv_le_contravar with (x := INR n1).
    - apply lt_0_INR; lia.
    - apply le_INR; exact Hle.
  }
  apply Rle_trans with (2 * PI * /2).
  - apply Rmult_le_compat_l.
    + left. apply Rmult_lt_0_compat; [lra | apply PI_RGT_0].
    + apply Rle_trans with (/ INR n1).
      * (* 证明 / INR n1 - / INR n2 <= / INR n1 *)
        apply Rlt_le.
        apply Rminus_lt.
        replace (/ INR n1 - / INR n2 - / INR n1) with (- / INR n2) by ring.
        rewrite <- Ropp_0.
        apply Ropp_lt_contravar.
        apply Rinv_0_lt_compat.
        apply lt_0_INR; lia.
      * (* 证明 / INR n1 <= /2 *)
        apply Rinv_le_contravar.
        -- lra.
        -- replace 2 with (INR 2) by (simpl; ring).
           apply le_INR; lia.
  - right. field; lra.               (* 2 * PI * /2 = PI *)
Qed.

(** 复数模长恒等式 *)
Lemma Cnorm_one_minus_exp_i_theta_eq :
  forall θ : R,
    Cnorm (C1 -c Cexp (0 +i θ)) = 2 * Rabs (sin (θ / 2)).
Proof.
  intros θ.
  set (a := θ / 2).
  replace θ with (2 * a) by (subst a; field).
  unfold Csub, C1, Cexp, Cnorm, Cnorm_sq; simpl.
  rewrite exp_0, Rmult_1_l.
  rewrite cos_2a, sin_2a.
  unfold Rsqr.

  ring_simplify.
  rewrite ?Rmult_1_l.
  unfold Rminus.
  rewrite ?Ropp_mult_distr_l, ?Ropp_mult_distr_r.
  ring_simplify.

  assert (Haux : 2 * sin a * cos a * (2 * sin a * cos a) +
                 2 * sin a * sin a * (2 * sin a * sin a)
                 = 4 * sin a * sin a).
  {
    set (s := sin a).
    set (c := cos a).
    replace (2 * s * c * (2 * s * c) + 2 * s * s * (2 * s * s))
      with (4 * s * s * c * c + 4 * s * s * s * s) by ring.
    replace (4 * s * s * c * c + 4 * s * s * s * s)
      with (4 * s * s * (c * c + s * s)) by ring.
    replace (c * c + s * s) with 1.
    - ring.
    - rewrite <- sin2_cos2 with (x := a).
      subst s c; unfold Rsqr; ring.
  }

  assert (Hreal : 2 * sin a * sin a = 1 + - (cos a * cos a + - sin a * sin a)).
  {
    replace (1 + - (cos a * cos a + - sin a * sin a))
      with (1 - (cos a * cos a - sin a * sin a)) by ring.
    rewrite <- (sin2_cos2 a) at 1.
    unfold Rsqr.
    ring.
  }
  rewrite <- Hreal.

  replace ((0 + - (2) * sin a * cos a) *
           (0 + - (2) * sin a * cos a))
    with ((2 * sin a * cos a) * (2 * sin a * cos a))
    by ring.

  rewrite Rplus_comm.
  rewrite Haux.

  replace (4 * sin a * sin a) with ((2 * sin a) * (2 * sin a)) by ring.
  replace ((2 * sin a) * (2 * sin a)) with ((2 * sin a)²) by (unfold Rsqr; ring).
  rewrite sqrt_Rsqr_abs.
  rewrite Rabs_mult.
  rewrite Rabs_pos_eq; [| lra].          (* |2| = 2 *)
  reflexivity.
Qed.

(* 绝对值与除法交换律（除以2） *)
Lemma Rabs_div_2 : forall x : R, Rabs (x / 2) = Rabs x / 2.
Proof.
  intros x.
  unfold Rdiv.
  rewrite Rabs_mult.
  rewrite Rabs_inv.
  - replace (Rabs 2) with 2 by (symmetry; apply Rabs_right; lra).
    reflexivity.
Qed.

(* 正弦绝对值等于绝对值正弦 *)
Lemma Rabs_sin_eq : forall x : R, Rabs x <= PI / 2 -> Rabs (sin x) = sin (Rabs x).
Proof.
  intros x H.
  destruct (Rcase_abs x) as [Hneg|Hpos].
  - (* x < 0 *)
    rewrite (Rabs_left _ Hneg).
    replace (Rabs (sin x)) with (Rabs (sin (-x))).
    2: { rewrite sin_neg, Rabs_Ropp; reflexivity. }
    assert (H' : 0 <= -x <= PI / 2).
    { split; [lra | rewrite Rabs_left in H; assumption]. }
    rewrite (Rabs_pos_eq (sin (-x))).
    2: { apply sin_ge_0; lra. }
    reflexivity.
  - (* x >= 0 *)
    rewrite (Rabs_right _ Hpos).
    assert (H' : 0 <= x <= PI / 2).
    { split; [apply Rge_le; exact Hpos | rewrite Rabs_right in H; assumption]. }
    rewrite (Rabs_pos_eq (sin x)).
    2: { apply sin_ge_0; lra. }
    reflexivity.
Qed.

(* 余弦函数在[0, π]上严格递减 *)
Lemma cos_decreasing : forall x y : R, 0 <= x -> x < y -> y <= PI -> cos x > cos y.
Proof.
  intros x y Hx Hxy Hy.
  apply Rminus_gt.
  replace (cos x - cos y) with (-2 * sin ((x + y) / 2) * sin ((x - y) / 2)).
  2: { symmetry; apply cos_minus_cos. }
  set (u := (x + y) / 2).
  set (v := (x - y) / 2).

  (* 0 < u *)
  assert (Hu1 : 0 < u).
  { unfold u.
    apply Rmult_lt_0_compat.
    - assert (Hy_pos : 0 < y) by (apply Rle_lt_trans with x; assumption).
      apply Rplus_le_lt_0_compat; [assumption | exact Hy_pos].
    - apply Rinv_0_lt_compat; lra. }

  (* u < PI *)
  assert (Hu2 : u < PI).
  { unfold u.
    apply Rmult_lt_reg_l with 2; [lra |].
    rewrite Rmult_comm.
    replace ((x + y) / 2 * 2) with (x + y) by (field; lra).
    apply Rlt_le_trans with (y + y).
    - apply Rplus_lt_compat_r; assumption.
    - replace (y + y) with (2 * y) by ring.
      apply Rmult_le_compat_l; [lra | assumption]. }

  (* v < 0 *)
  assert (Hv1 : v < 0).
  { unfold v.
    replace ((x - y) / 2) with ((x - y) * /2) by (field; lra).
    apply Rmult_neg_pos.
    - apply Rplus_lt_compat_r with (r := - y) in Hxy.
      rewrite Rplus_opp_r in Hxy. exact Hxy.
    - apply Rinv_0_lt_compat; lra. }

  (* -PI/2 <= v *)
  assert (Hv2 : -PI/2 <= v).
  { unfold v.
    apply Rmult_le_reg_r with 2; [lra |].
    rewrite Rmult_comm.
    replace ((x - y) / 2 * 2) with (x - y) by (field; lra).
    replace (2 * (- PI / 2)) with (-PI) by field.
    assert (H1 : -PI <= -y) by (apply Ropp_le_contravar; assumption).
    apply Rle_trans with (-y).
    - exact H1.
    - apply Rplus_le_compat_r with (r := -y) in Hx.
      rewrite Rplus_0_l in Hx. assumption. }

  (* 正弦符号判定 *)
  assert (Hsin_u : 0 < sin u).
  { apply sin_gt_0; [exact Hu1 | exact Hu2]. }

  assert (Hv2' : -v <= PI/2).
  { apply Ropp_le_contravar in Hv2.
    replace (- (- PI / 2)) with (PI/2) in Hv2 by field.
    exact Hv2. }

  assert (Hsin_v : sin v < 0).
  { apply Ropp_lt_cancel.
    rewrite <- Ropp_0.
    replace (- sin v) with (sin (-v)) by (rewrite sin_neg; ring).
    replace (- - 0) with 0 by ring.
    apply sin_gt_0.
    - apply Ropp_lt_cancel; rewrite Ropp_0, Ropp_involutive; exact Hv1.
    - apply Rle_lt_trans with (PI/2); [|lra]. exact Hv2'. }

  (* 乘积为负 *)
  assert (Hprod : sin u * sin v < 0).
  { rewrite Rmult_comm.
    apply Rmult_neg_pos; [exact Hsin_v | exact Hsin_u]. }

  (* 消去负号 *)
  replace (-2 * sin u * sin v) with (- (2 * sin u * sin v)) by ring.
  cut (2 * sin u * sin v < 0).
  { intros H. rewrite <- Ropp_0. apply Ropp_lt_contravar. exact H. }
  replace (2 * sin u * sin v) with (2 * (sin u * sin v)) by ring.
  replace 0 with (2 * 0) by ring.
  apply Rmult_lt_compat_l; [lra | exact Hprod].
Qed.

(* 定理：Jordan 不等式 前置引理 *)

(** * 辅助函数 *)
Definition h (t : R) : R := sin t - (2 / PI) * t.

(* 端点值为零 *)
Lemma h_endpoints : h 0 = 0 /\ h (PI/2) = 0.
Proof.
  split.
  - unfold h; rewrite sin_0; ring.
  - unfold h; rewrite sin_PI2; field; apply Rgt_not_eq, PI_RGT_0.
Qed.

(* h 的导数 *)
Lemma h_derivative_lim : forall t, derivable_pt_lim h t (cos t - 2 / PI).
Proof.
  intros t.
  unfold h.
  apply derivable_pt_lim_minus.
  - apply derivable_pt_lim_sin.
  - apply derivable_pt_lim_ext with (f := fun x : R => (2 / PI) * x).
    + intros z.
      unfold mult_real_fct, id.
      reflexivity.
    + assert (H1 : derivable_pt_lim (fun _ : R => 2 / PI) t 0).
      { apply derivable_pt_lim_const. }
      assert (H2 : derivable_pt_lim (fun x : R => x) t 1).
      { apply derivable_pt_lim_id. }
      assert (H3 : derivable_pt_lim (fun x : R => (2 / PI) * x) t (0 * t + (2 / PI) * 1)).
      { apply derivable_pt_lim_mult with (1 := H1) (2 := H2). }
      assert (H4 : (0 * t + (2 / PI) * 1) = (2 / PI)).
      { ring. }
      rewrite H4 in H3.
      exact H3.
Qed.

(* 可导性证明 *)
Lemma h_derivable : forall t, derivable_pt h t.
Proof.
  intros t; exists (cos t - 2 / PI); apply h_derivative_lim.
Qed.

(* 导数表达式 *)
Lemma h_derive_eq : forall t, derive_pt h t (h_derivable t) = cos t - 2 / PI.
Proof.
  intros t; apply derive_pt_eq_0; apply h_derivative_lim.
Qed.

(* 导数在 [0,π/2] 上严格递减 *)
Lemma h_deriv_strictly_decreasing :
  forall t1 t2,
    0 <= t1 /\ t1 < t2 /\ t2 <= PI/2 ->
    derive_pt h t1 (h_derivable t1) > derive_pt h t2 (h_derivable t2).
Proof.
  intros t1 t2 [H1 [H2 H3]].
  rewrite !h_derive_eq.          (* 将导数替换为 cos t - 2/PI *)
  apply (Rplus_gt_compat_r (- (2 / PI))).  (* 两边同时加上 -2/PI 等价于消去该项 *)
  apply cos_decreasing.
  - exact H1.                    (* 0 <= t1 *)
  - exact H2.                    (* t1 < t2 *)
  - apply Rle_trans with (PI/2); [exact H3 | lra].  (* t2 <= PI/2 <= PI *)
Qed.

(* 存在一点 c∈(0,π/2) 使得导数为零 *)
Lemma exists_zero_derivative :
  exists c, 0 < c < PI/2 /\ derive_pt h c (h_derivable c) = 0.
Proof.
  destruct h_endpoints as [H0 Hpi2].
  assert (Hcont : forall t, 0 <= t <= PI/2 -> continuity_pt h t).
  { intros t H; apply derivable_continuous_pt; apply h_derivable. }
  assert (Hder : forall t, 0 < t < PI/2 -> derivable_pt h t).
  { intros; apply h_derivable. }
  apply Rolle with (a:=0) (b:=PI/2) (pr := Hder) in Hcont.
  - destruct Hcont as [c [Hc Hder0]].
    exists c; split; auto.
    rewrite <- (pr_nu h c (Hder c Hc) (h_derivable c)).
    rewrite Hder0.
    reflexivity.
  - apply PI2_RGT_0.               (* 证明 0 < PI/2 *)
  - rewrite H0, Hpi2; reflexivity. (* 证明 h 0 = h (PI/2) *)
Qed.

(* h 在 [0,c] 上非递减（即 h(t) ≥ h(0)）*)
Lemma h_increasing_on_left : forall c,
  0 < c < PI/2 ->
  derive_pt h c (h_derivable c) = 0 ->
  forall t, 0 <= t <= c -> h t >= h 0.
Proof.
  intros c Hc Hc' t Ht.
  destruct Ht as [Ht_low Ht_up].
  destruct (Rle_lt_or_eq 0 t Ht_low) as [Ht_pos | Ht_zero].
  - (* t > 0 *)
    (* 证明在 (0, c) 上导数严格为正 *)
    assert (Hpos_deriv : forall x, 0 < x < c -> 0 < derive_pt h x (h_derivable x)).
    { intros x Hx.
      assert (Hgt : derive_pt h x (h_derivable x) > derive_pt h c (h_derivable c)).
      { apply h_deriv_strictly_decreasing with (t1:=x) (t2:=c).
        split; [| split].
        - apply Rlt_le; apply Hx.      (* 0 <= x *)
        - apply Hx.                    (* x < c *)
        - apply Rlt_le; apply Hc.      (* c <= PI/2 *)
      }
      rewrite Hc' in Hgt.
      exact Hgt.
    }
    (* 拉格朗日中值定理 *)
    assert (Hder_lim : forall z, 0 <= z <= t -> derivable_pt_lim h z (cos z - 2/PI)).
    { intros z Hz; apply h_derivative_lim. }
    destruct (MVT_cor2 h (fun x => cos x - 2/PI) 0 t Ht_pos Hder_lim) as [xi [Hxi Hder]].
    destruct h_endpoints as [H0 _].  (* h 0 = 0 *)
    rewrite H0 in Hxi.                (* 代入 h 0 = 0 *)
    replace (t - 0) with t in Hxi by ring.  (* 简化 t - 0 为 t *)
    (* 现在 Hxi : h t = (cos xi - 2/PI) * t *)
    destruct Hder as [Hxi_pos Hxi_lt_t].  (* 0 < xi < t *)
    assert (0 < xi < c).
    { split; [exact Hxi_pos | apply Rlt_le_trans with t; [exact Hxi_lt_t | exact Ht_up]]. }
    pose proof (Hpos_deriv xi H) as Hpos.
    rewrite h_derive_eq in Hpos.      (* cos xi - 2/PI > 0 *)
    assert (Hprod : 0 < (cos xi - 2/PI) * t).
    { apply Rmult_gt_0_compat; [exact Hpos | exact Ht_pos]. }
    rewrite <- Hxi in Hprod.          (* 将乘积替换为 h t，得到 0 < h t *)
    rewrite Rminus_0_r in Hprod.      (* 简化 Hprod: 0 < h t *)
    rewrite H0.                       (* 将目标中的 h 0 替换为 0，得到 h t >= 0 *)
    lra.                              (* 由 0 < h t 推出 h t >= 0 *)
  - (* t = 0 *)
    subst.
    rewrite (proj1 h_endpoints).      (* h 0 = 0 *)
    apply Rle_refl.                   (* 0 >= 0 成立 *)
Qed.

(* h 在 [c,π/2] 上非递增（即 h(t) ≥ h(π/2)）*)
Lemma h_decreasing_on_right : forall c,
  0 < c < PI/2 ->
  derive_pt h c (h_derivable c) = 0 ->
  forall t, c <= t <= PI/2 -> h t >= h (PI/2).
Proof.
  intros c Hc Hc' t Ht.
  destruct h_endpoints as [H0 Hpi2].  (* 提前获取 h(0)=0 和 h(PI/2)=0 *)
  destruct Ht as [Hc_le_t Ht_le_pi2].
  destruct (Rle_lt_or_eq t (PI/2) Ht_le_pi2) as [Ht_lt_pi2 | Ht_eq_pi2].
  - (* t < PI/2 *)
    assert (Hder_lim : forall z, t <= z <= PI/2 -> derivable_pt_lim h z (cos z - 2/PI)).
    { intros z Hz; apply h_derivative_lim. }
    assert (Ht_lt_pi2' : t < PI/2) by exact Ht_lt_pi2.
    destruct (MVT_cor2 h (fun x => cos x - 2/PI) t (PI/2) Ht_lt_pi2' Hder_lim) as [xi [Hxi Hder]].
    rewrite Hpi2 in Hxi.                (* Hxi : 0 - h t = (cos xi - 2/PI) * (PI/2 - t) *)
    (* 两边取负 *)
    apply (f_equal (fun x => - x)) in Hxi.   (* Hxi : - (0 - h t) = - ((cos xi - 2/PI) * (PI/2 - t)) *)
    assert (H_rm : forall x, - (0 - x) = x) by (intros; ring).
    rewrite H_rm in Hxi.                     (* Hxi : h t = - ((cos xi - 2/PI) * (PI/2 - t)) *)
    rewrite Ropp_mult_distr_l in Hxi.        (* Hxi : h t = (- (cos xi - 2/PI)) * (PI/2 - t) *)
    assert (Hxi_range : t < xi < PI/2) by (destruct Hder as [H1 H2]; split; auto).
    assert (Hc_lt_xi : c < xi).
    { apply Rle_lt_trans with t; [exact Hc_le_t | exact (proj1 Hxi_range)]. }
    assert (Hxi_le_pi2 : xi <= PI/2) by (apply Rlt_le; exact (proj2 Hxi_range)).
    assert (Hc_ge_0 : 0 <= c) by lra.
    assert (Hder_gt : derive_pt h c (h_derivable c) > derive_pt h xi (h_derivable xi)).
    { apply h_deriv_strictly_decreasing with (t1 := c) (t2 := xi).
      split; [| split]; auto. }
    rewrite Hc' in Hder_gt.
    assert (Hder_xi_neg : derive_pt h xi (h_derivable xi) < 0) by lra.
    rewrite h_derive_eq in Hder_xi_neg.   (* cos xi - 2/PI < 0 *)
    assert (H_factor_pos : PI/2 - t > 0) by lra.
    assert (Hneg_pos : 0 < - (cos xi - 2/PI)).
    { rewrite <- Ropp_0. apply Ropp_lt_contravar; exact Hder_xi_neg. }
    assert (Hprod_pos : 0 < (- (cos xi - 2/PI)) * (PI/2 - t)).
    { apply Rmult_lt_0_compat; auto. }
    rewrite <- Hxi in Hprod_pos.          (* h t > 0 *)
    rewrite Hpi2.                         (* 目标：h t >= 0 *)
    lra.                                  (* 由 h t > 0 得 h t >= 0 *)
  - (* t = PI/2 *)
    subst.
    rewrite Hpi2.
    apply Rle_refl.
Qed.

(** 定理：Jordan 不等式 *)
(* ============================================================
   [构造性轨道 S2-20260818] Jordan 不等式构造性证明
   完全替代原 Rolle+MVT 路线（携带 classic），本证明零经典逻辑。
   路线：中点凹性（纯代数）→ 二进弦归纳 → dyad_below 逼近 → ε-δ 挤压
   ============================================================ *)

Lemma pow2_ge1 : forall n : nat, (1 <= 2^n)%nat.
Proof. induction n as [|n IH]; simpl; lia. Qed.

Lemma pow2_exponent : forall M : nat, exists n : nat, (M <= 2^n)%nat.
Proof.
  intros M. induction M as [|M [n Hn]].
  - exists 0%nat. simpl. lia.
  - exists (S n). pose proof (pow2_ge1 n) as H1.
    rewrite Nat.pow_succ_r by lia. lia.
Qed.

Lemma div_le_cancel : forall a b d, 0 < d -> a <= b * d -> a / d <= b.
Proof.
  intros a b d Hd Hab. unfold Rdiv.
  apply (Rmult_le_reg_r d (a * / d) b Hd).
  replace (a * / d * d) with a by (field; lra).
  exact Hab.
Qed.

Lemma sin_midpoint_concave : forall a b, 0 <= a <= PI/2 -> 0 <= b <= PI/2 ->
  sin ((a+b)/2) >= (sin a + sin b) / 2.
Proof.
  intros a b Ha Hb.
  destruct Ha as [Ha1 Ha2]. destruct Hb as [Hb1 Hb2].
  assert (Hid : sin a + sin b = 2 * sin ((a+b)/2) * cos ((a-b)/2)).
  { pose proof (sin_plus ((a+b)/2) ((a-b)/2)) as H1.
    pose proof (sin_minus ((a+b)/2) ((a-b)/2)) as H2.
    replace (((a+b)/2) + ((a-b)/2)) with a in H1 by field.
    replace (((a+b)/2) - ((a-b)/2)) with b in H2 by field.
    rewrite H1, H2. ring. }
  assert (Hsm : 0 <= sin ((a+b)/2)) by (apply sin_ge_0; lra).
  assert (Hcos : cos ((a-b)/2) <= 1)
    by (pose proof (COS_bound ((a-b)/2)) as H; destruct H as [_ H]; exact H).
  apply Rle_ge. rewrite Hid.
  replace (2 * sin ((a+b)/2) * cos ((a-b)/2) / 2)
    with (sin ((a+b)/2) * cos ((a-b)/2)) by field.
  apply Rle_trans with (sin ((a+b)/2) * 1).
  - apply Rmult_le_compat_l; [exact Hsm | exact Hcos].
  - rewrite Rmult_1_r. apply Rle_refl.
Qed.

(* ===== 构件 3：二进弦不等式 ===== *)

Lemma sin_dyadic_chord : forall n k : nat, (k <= 2^n)%nat ->
  INR k / INR (2^n) <= sin (INR k / INR (2^n) * (PI/2)).
Proof.
  induction n as [|n IH]; intros k Hk.
  - simpl in Hk. assert (Hk01 : k = 0%nat \/ k = 1%nat) by lia.
    destruct Hk01 as [-> | ->].
    + replace (INR 0 / INR (2^0)) with 0 by (simpl; field).
      replace (0 * (PI/2)) with 0 by ring.
      rewrite sin_0. lra.
    + replace (INR 1 / INR (2^0)) with 1 by (simpl; field).
      replace (1 * (PI/2)) with (PI/2) by ring.
      rewrite sin_PI2. lra.
  - assert (HPI : (0 < PI)%R) by apply PI_RGT_0.
    assert (Hpi2 : (0 <= PI/2)%R) by lra.
    assert (HpowS : (2^(S n) = 2 * 2^n)%nat) by (rewrite Nat.pow_succ_r; lia).
    assert (Hpos : 0 < INR (2^n)) by (apply lt_0_INR; pose proof (pow2_ge1 n); lia).
    rewrite HpowS in Hk.
    assert (Hk' : (k = 2 * (k / 2) + k mod 2)%nat) by apply Nat.div_mod_eq.
    assert (Hmb : (k mod 2 < 2)%nat) by (apply Nat.mod_upper_bound; lia).
    assert (Hmod : k mod 2 = 0%nat \/ k mod 2 = 1%nat) by lia.
    assert (Hkn : (k / 2 <= 2^n)%nat) by (apply Nat.Div0.div_le_upper_bound; lia).
    rewrite HpowS.
    destruct Hmod as [Hm0 | Hm1].
    + (* 偶：k = 2*(k/2) *)
      assert (Hkm : (k = 2 * (k / 2))%nat) by lia.
      rewrite Hkm, !mult_INR.
      replace (INR 2) with 2 by (simpl; ring).
      replace (2 * INR (k/2) / (2 * INR (2^n)))
        with (INR (k/2) / INR (2^n)) by (field; lra).
      apply IH. exact Hkn.
    + (* 奇：k = 2*(k/2)+1，中点凹性 *)
      assert (Hkm1 : (k = 2 * (k / 2) + 1)%nat) by lia.
      assert (Hkn1 : (k / 2 + 1 <= 2^n)%nat) by lia.
      assert (HINm1 : INR (k/2 + 1) = INR (k/2) + 1)
        by (rewrite plus_INR; reflexivity).
      rewrite Hkm1, !mult_INR.
      replace (INR 2) with 2 by (simpl; ring).
      assert (HINk : 2 * INR (k/2) + 1 = 2 * INR (k/2) + 1) by ring.
      set (D := INR (2^n)).
      set (A := INR (k/2) / D).
      set (B := INR (k/2 + 1) / D).
      assert (HINm : INR (k/2) <= INR (2^n)) by (apply le_INR; lia).
      assert (HINm1D : INR (k/2 + 1) <= INR (2^n)) by (apply le_INR; lia).
      idtac "MARK_HA01".
      assert (HA01 : 0 <= A <= 1).
      { split.
        - unfold A, Rdiv. apply Rmult_le_pos;
            [apply pos_INR | apply Rlt_le, Rinv_0_lt_compat, Hpos].
        - unfold A. apply (div_le_cancel (INR (k/2)) 1 D Hpos).
          rewrite Rmult_1_l. exact HINm. }
      idtac "MARK_HB01".
      assert (HB01 : 0 <= B <= 1).
      { split.
        - unfold B, Rdiv. apply Rmult_le_pos;
            [apply pos_INR | apply Rlt_le, Rinv_0_lt_compat, Hpos].
        - unfold B. apply (div_le_cancel (INR (k/2+1)) 1 D Hpos).
          rewrite Rmult_1_l. exact HINm1D. }
      set (sa := A * (PI/2)).
      set (sb := B * (PI/2)).
      idtac "MARK_HSA".
      assert (Hsa : 0 <= sa <= PI/2).
      { split.
        - unfold sa. apply Rmult_le_pos; [apply (proj1 HA01) | lra].
        - unfold sa. apply Rle_trans with (1 * (PI/2)).
          + apply Rmult_le_compat_r; [lra | apply (proj2 HA01)].
          + rewrite Rmult_1_l. apply Rle_refl. }
      idtac "MARK_HSB".
      assert (Hsb : 0 <= sb <= PI/2).
      { split.
        - unfold sb. apply Rmult_le_pos; [apply (proj1 HB01) | lra].
        - unfold sb. apply Rle_trans with (1 * (PI/2)).
          + apply Rmult_le_compat_r; [lra | apply (proj2 HB01)].
          + rewrite Rmult_1_l. apply Rle_refl. }
      idtac "M_HCA".
      pose proof (IH ((k/2)%nat) Hkn) as HcA.
      idtac "M_HCB".
      pose proof (IH ((k/2 + 1)%nat) Hkn1) as HcB.
      idtac "MARK_HK".
      idtac "M_HK".
      assert (HD : 0 < D) by (unfold D; exact Hpos).
      assert (HINk2 : INR (2 * (k/2) + 1) = 2 * INR (k/2) + 1)
        by (rewrite plus_INR, mult_INR; simpl; ring).
      rewrite HINk2.
      assert (HK : (2 * INR (k/2) + 1) / (2 * D) = (A + B) / 2).
      { unfold A, B. rewrite HINm1. field. lra. }
      idtac "M_HMID".
      assert (Hmid : (A + B) / 2 * (PI/2) = (A * (PI/2) + B * (PI/2)) / 2) by field.
      idtac "M_REWHK".
      match goal with |- ?G => idtac "GOALHK:" G end.
      rewrite HK.
      rewrite Hmid.
      apply Rle_trans with ((sin (A * (PI/2)) + sin (B * (PI/2))) / 2).
      * replace ((A + B) / 2) with ((A + B) * (/2)) by field.
        replace ((sin (A * (PI/2)) + sin (B * (PI/2))) / 2)
          with ((sin (A * (PI/2)) + sin (B * (PI/2))) * (/2)) by field.
        apply Rmult_le_compat_r.
        -- apply Rlt_le, Rinv_0_lt_compat. lra.
        -- apply Rplus_le_compat; [exact HcA | exact HcB].
      * pose proof (sin_midpoint_concave (A * (PI/2)) (B * (PI/2)) Hsa Hsb) as Hconc.
        apply Rge_le in Hconc. exact Hconc.
Qed.


(* ===== 构件 4：二进逼近 ===== *)

Lemma dyad_below : forall t n, 0 <= t <= 1 ->
  exists k, (k <= 2^n)%nat /\ INR k <= t * INR (2^n) /\ t * INR (2^n) - INR k < 1.
Proof.
  intros t n Ht. destruct Ht as [Ht1 Ht2].
  induction n as [|n [k [Hk1 [Hk2 Hk3]]]].
  - destruct (Req_dec t 1) as [He1 | Hne1].
    + exists 1%nat. simpl. split; [lia | split; lra].
    + exists 0%nat. simpl. split; [lia | split; lra].
  - assert (HpowS : (2^(S n) = 2 * 2^n)%nat) by (rewrite Nat.pow_succ_r; lia).
    rewrite HpowS, !mult_INR.
    replace (INR 2) with 2 by (simpl; ring).
    idtac "M_SETD".
    set (D := INR (2^n)) in *.
    assert (Hstep : t * (2 * D) = 2 * (t * D)) by ring.
    destruct (Rlt_dec (t * (2 * D)) (2 * INR k + 1)) as [Hlt | Hnlt].
    idtac "M_BR1".
    + exists (2 * k)%nat. rewrite mult_INR.
      replace (INR 2) with 2 by (simpl; ring).
      match goal with |- ?G => idtac "B1GOAL:" G end.
      split; [lia |].
      split; [| lra].
      match goal with |- ?G => idtac "B1MAIN:" G end.
      idtac "B1S1".
      assert (HG1 : 2 * INR k <= 2 * (t * D)).
      { apply Rmult_le_compat_l; [lra | exact Hk2]. }
      idtac "B1S2".
      assert (HG2 : 2 * (t * D) <= t * (2 * D)).
      { rewrite Hstep. apply Rle_refl. }
      idtac "B1S3".
      exact (Rle_trans _ _ _ HG1 HG2).
    + exists (2 * k + 1)%nat.
      assert (HIN : INR (2 * k + 1) = 2 * INR k + 1)
        by (rewrite plus_INR, mult_INR; simpl; ring).
      assert (Hle1' : 2 * INR k + 1 <= t * (2 * D))
        by (apply Rnot_lt_le; exact Hnlt).
      assert (Hpos : 0 < INR (2^n)) by (apply lt_0_INR; pose proof (pow2_ge1 n); lia).
      assert (H0D : 0 < D) by (unfold D; exact Hpos).
      assert (Hup : t * (2 * D) <= 2 * D).
      { apply Rle_trans with (1 * (2 * D)).
        - apply Rmult_le_compat_r; [lra | exact Ht2].
        - rewrite Rmult_1_l. apply Rle_refl. }
      assert (HDdef : D = INR (2^n)) by reflexivity.
      assert (HkltR : INR k < INR (2^n)).
      { assert (H2 : 2 * INR k + 1 <= 2 * D)
          by (apply Rle_trans with (t * (2 * D)); [exact Hle1' | exact Hup]).
        rewrite <- HDdef. lra. }
      assert (HkS : (S k <= 2^n)%nat).
      { assert (Hklt : (k < 2^n)%nat) by (apply INR_lt; exact HkltR). lia. }
      split.
      * apply Nat.le_trans with (2 * S k)%nat.
        -- lia.
        -- apply Nat.mul_le_mono_l. exact HkS.
      * split; [rewrite HIN; apply Rnot_lt_le; exact Hnlt |].
        assert (Hb : t * D < INR k + 1) by lra.
        assert (H2' : 2 * (t * D) < 2 * (INR k + 1))
          by (apply Rmult_lt_compat_l; [lra | exact Hb]).
        rewrite <- Hstep in H2'.
        replace (2 * (INR k + 1)) with (2 * INR k + 2) in H2' by ring.
        lra.

Qed.

(* ===== 主定理：构造性 Jordan 不等式 ===== *)

Theorem jordan_constructive : forall x, 0 <= x <= PI/2 -> sin x >= (2 / PI) * x.
Proof.
  intros x Hx. destruct Hx as [Hx1 Hx2].
  assert (HPI : (0 < PI)%R) by apply PI_RGT_0.
  assert (Hpi2 : (0 <= PI/2)%R) by lra.
  set (lam := 2 / PI * x).
  assert (Hlam : lam = 2 / PI * x) by reflexivity.
  assert (H2PI : 0 <= 2 / PI).
  { apply Rmult_le_pos; [lra | apply Rlt_le, Rinv_0_lt_compat; lra]. }
  assert (Hlam01 : 0 <= lam <= 1).
  { split.
    - unfold lam. apply Rmult_le_pos; [exact H2PI | exact Hx1].
    - unfold lam. apply Rle_trans with (2 / PI * (PI / 2)).
      + apply Rmult_le_compat_l; [apply Rmult_le_pos; [lra | apply Rlt_le, Rinv_0_lt_compat; lra] | exact Hx2].
      + replace (2 / PI * (PI / 2)) with 1 by (field; lra). apply Rle_refl. }
  destruct (Rlt_dec (sin x) lam) as [Hlt | Hnlt].
  - exfalso.
    set (e := (lam - sin x) / 2).
    assert (He : 0 < e) by (unfold e, lam in *; lra).
    (* sin 连续性 *)
    pose proof (continuity_sin x) as Hcont.
    unfold continuity_pt in Hcont.
    destruct (Hcont e He) as [d [Hd1 Hd2]].
    (* 取 n 使 1/2^n < Rmin e (d/(PI/2)) *)
    set (r := Rmin e (d / (PI/2))).
    assert (Hdpi : 0 < d / (PI/2)) by (apply Rdiv_lt_0_compat; [exact Hd1 | lra]).
    assert (Hr : 0 < r).
    { unfold r. apply (Rmin_case e (d / (PI/2)) (fun z => 0 < z)); [exact He | exact Hdpi]. }
    (* 阿基米德：存在 M，1/r < INR M *)
    assert (H1r : 0 < 1 / r).
    { replace (1 / r) with (/ r) by (field; lra). apply Rinv_0_lt_compat; exact Hr. }
    assert (HM : exists M : nat, 1 / r < INR M).
    { destruct (INR_archimed 1 (1 / r) (Rlt_0_1)) as [M HM'].
      exists M. lra. }
    destruct HM as [M HM].
    destruct (pow2_exponent M) as [n Hn].
    set (D := INR (2^n)).
    assert (H0D : 0 < D) by (unfold D; apply lt_0_INR; pose proof (pow2_ge1 n); lia).
    assert (HnD : INR M <= D) by (unfold D; apply le_INR; exact Hn).
    assert (HDbig : 1 / r < D) by lra.
    assert (Hinv : / (1 / r) = r) by (field; lra).
    assert (Hstep : 1 / D < r).
    { assert (HDne : D <> 0) by lra.
      assert (Hr_ne : r <> 0) by lra.
      replace (1 / D) with (/ D) by (field; exact HDne).
      replace r with (/ (/ r)) by (field; exact Hr_ne).
      apply Rinv_lt_contravar;
        [ apply Rmult_lt_0_compat;
            [ apply Rinv_0_lt_compat; exact Hr
            | exact H0D ]
        | replace (/ r) with (1 / r) by (field; exact Hr_ne); exact HDbig ]. }
    (* 二进逼近 *)
    destruct (dyad_below lam n Hlam01) as [k [Hk1 [Hk2 Hk3]]].
    set (u := INR k / D).
    assert (Hu_le : u <= lam) by (unfold u; apply div_le_cancel; [exact H0D | exact Hk2]).
    assert (Hu_diff : lam - u < 1 / D).
    { assert (Hd3 : lam * D - INR k < 1) by (unfold D in *; exact Hk3).
      unfold u. replace (lam - INR k / D) with ((lam * D - INR k) / D) by (field; lra).
      apply Rmult_lt_reg_r with D;
        [ exact H0D
        | replace ((lam * D - INR k) / D * D) with (lam * D - INR k) by (field; lra);
          replace (1 / D * D) with 1 by (field; lra); lra ]. }
    (* y := u * PI/2 *)
    set (y := u * (PI/2)).
    assert (Hlam_x : lam * (PI/2) = x) by (unfold lam; field; lra).
    assert (Hy_le : y <= x).
    { unfold y. apply Rle_trans with (lam * (PI/2)).
      - apply Rmult_le_compat_r; [lra | exact Hu_le].
      - rewrite Hlam_x. apply Rle_refl. }
    (* |y - x| < d *)
    assert (Hyx : Rabs (y - x) < d).
    { assert (Hsub : y - x = -((lam - u) * (PI/2))).
      { unfold y, lam. field. lra. }
      rewrite Hsub, Rabs_Ropp.
      rewrite Rabs_mult.
      assert (Hpi_pos : 0 < PI/2) by lra.
      assert (Hpi_ge : 0 <= PI/2) by lra.
      rewrite (Rabs_pos_eq (PI/2) Hpi_ge).
      assert (Hlam_u_pos : 0 <= lam - u) by lra.
      rewrite (Rabs_pos_eq (lam - u) Hlam_u_pos).
      (* (lam - u) * PI/2 < d *)
      assert (Hr_le : Rmin e (d / (PI/2)) <= d / (PI/2)) by apply Rmin_r.
      unfold r in Hstep.
      apply Rlt_le_trans with ((d / (PI/2)) * (PI/2)).
      - apply (Rmult_lt_compat_r (PI/2) (lam - u) (d / (PI/2)));
          [ lra
          | apply Rlt_le_trans with (1 / D);
              [ exact Hu_diff
              | apply Rle_trans with (Rmin e (d / (PI/2)));
                  [ apply Rlt_le; exact Hstep | apply Rmin_r ] ] ].
      - replace ((d / (PI/2)) * (PI/2)) with d by (field; lra).
        lra. }
    (* sin 连续性应用于 y *)
    (* 先证 sin y >= u *)
    pose proof (sin_dyadic_chord n k Hk1) as Hchord.
    assert (Hsin_y : u <= sin y).
    { unfold u, y. exact Hchord. }
    assert (Hr_le_e : Rmin e (d / (PI/2)) <= e) by apply Rmin_l.
    assert (Hu_ge : u >= lam - e).
    { assert (H1 : lam - u < 1 / D) by exact Hu_diff.
      assert (H2 : 1 / D < Rmin e (d / (PI/2))) by exact Hstep.
      assert (H3 : Rmin e (d / (PI/2)) <= e) by exact Hr_le_e.
      unfold u, D, lam, e, r in *. lra. }
    (* y ≠ x：若 y = x 则 sin y = sin x，但 sin y >= u >= lam - e = (lam + sin x)/2 > sin x，矛盾 *)
    assert (Hyne : y <> x).
    { intros Heq. rewrite Heq in Hsin_y.
      unfold e, lam in *. lra. }
    assert (Hsy : Rabs (sin y - sin x) < e).
    { apply Hd2. split.
      - unfold D_x, no_cond. split.
        + exact I.
        + intro Hxy. apply Hyne. symmetry. exact Hxy.
      - exact Hyx. }
    (* 从绝对值不等式提取 sin y - sin x < e *)
    destruct (Rabs_def2 (sin y - sin x) e Hsy) as [Hsin_lt _].
    unfold e in *.
    lra.
  - (* sin x >= lam *)
    apply Rle_ge. apply Rnot_lt_le. exact Hnlt.
Qed.

(* 原定理陈述保留，证明改为构造性版本 *)
Theorem jordan_standard : forall x, 0 <= x <= PI / 2 -> sin x >= (2 / PI) * x.
Proof.
  exact jordan_constructive.
Qed.

(* 绝对值 Jordan 不等式 *)
Lemma jordan_inequality_half_abs :
  forall θ : R,
    Rabs θ <= PI ->
    Rabs (sin (θ / 2)) >= Rabs θ / PI.
Proof.
  intros θ Hbound.
  set (t := Rabs θ).
  assert (Ht_ge0 : 0 <= t) by apply Rabs_pos.
  assert (Ht_le_pi : t <= PI) by auto.
  assert (Ht2_le_pi2 : t / 2 <= PI / 2) by lra.
  
  (* 关键恒等式：|sin(θ/2)| = sin(t/2) *)
  assert (Habs_theta2 : Rabs (θ / 2) = t / 2).
  { unfold t; rewrite Rabs_div_2; reflexivity. }
  assert (Habs_eq : Rabs (sin (θ / 2)) = sin (t / 2)).
  {
    assert (H : Rabs (θ / 2) <= PI / 2) by lra.
    rewrite Rabs_sin_eq; [| exact H].
    rewrite Habs_theta2; reflexivity.
  }
  
  (* 应用标准Jordan不等式 *)
  assert (Hjordan : sin (t / 2) >= (2 / PI) * (t / 2)).
  { apply jordan_standard; split; lra. }
  assert (Hmain : (2 / PI) * (t / 2) = t / PI).
  { field; apply Rgt_not_eq, PI_RGT_0. }
  
  rewrite Habs_eq.
  rewrite <- Hmain.
  apply Hjordan.
Qed.

(* 定理：复指数差的模长下界 *)
Theorem exp_diff_lower_bound :
  forall θ : R,
    Rabs θ <= PI ->
    Cnorm ((1 +i 0) -c Cexp (0 +i θ)) >= 2 * Rabs θ / PI.
Proof.
  intros θ Hbound.
  rewrite Cnorm_one_minus_exp_i_theta_eq.
  rewrite Rabs_sin_eq.
  - rewrite Rabs_div_2.
    assert (PI_neq0 : PI <> 0) by (apply Rgt_not_eq, PI_RGT_0).
    replace (2 * Rabs θ / PI) with (2 * (Rabs θ / PI)) by (field; auto).
    apply Rmult_ge_compat_l with (r := 2); [lra |].
    assert (H_jordan : sin (Rabs θ / 2) >= (2 / PI) * (Rabs θ / 2)).
    { apply jordan_standard.
      split.
      - apply Rmult_le_pos; [apply Rabs_pos | lra].
      - lra. }
    replace ((2 / PI) * (Rabs θ / 2)) with (Rabs θ / PI) in H_jordan by (field; auto).
    exact H_jordan.
  - rewrite Rabs_div_2.
    lra.
Qed.

Lemma sparse_implies_ge :
  forall (seq : nat -> nat) (c : nat) (idx1 idx2 : nat),
    (forall i, INR (seq (S i)) > INR c * INR (seq i))%R ->
    (idx1 < idx2)%nat -> (seq idx1 <= seq idx2)%nat ->
    (INR (seq idx2) >= INR c * INR (seq idx1))%R.
Proof.
  intros seq c idx1 idx2 Hsparse Hlt Hle.
  destruct c as [|c'].
  - (* c = 0 *)
    simpl. rewrite Rmult_0_l. apply Rle_ge, pos_INR.
  - (* c = S c' > 0 *)
    (* 证明序列严格递增 *)
    assert (Hinc : forall i, (seq i < seq (S i))%nat).
    { intros i.
      apply INR_lt.
      assert (H1 : INR (seq i) <= INR (S c') * INR (seq i)).
      { apply Rle_trans with (1 * INR (seq i)).
        - rewrite Rmult_1_l; apply Rle_refl.
        - apply Rmult_le_compat_r.
          + change (INR 0 <= INR (seq i)). apply le_INR; lia.
          + change (INR 1 <= INR (S c')). apply le_INR; lia.
      }
      apply Rle_lt_trans with (INR (S c') * INR (seq i)).
      - exact H1.
      - apply Rgt_lt; exact (Hsparse i).
    }
    (* 由 idx1 < idx2 和严格递增推出 seq (S idx1) ≤ seq idx2 *)
    assert (Hseq_ge : (seq (S idx1) <= seq idx2)%nat).
    {
      (* 证明对于任意 k > 0，seq (idx1 + k) >= seq (S idx1) *)
      assert (Haux : forall k, (k > 0)%nat -> (seq (S idx1) <= seq (idx1 + k))%nat).
      {
        intros k Hk.
        replace (idx1 + k)%nat with (S idx1 + (k - 1))%nat by lia.
        clear Hk.
        induction (k - 1)%nat as [|d IH].
        - (* base: k-1 = 0 *)
          rewrite Nat.add_0_r.
          apply Nat.le_refl.
        - (* step: k-1 = S d *)
          simpl in *.
          replace (idx1 + S d)%nat with (S (idx1 + d))%nat by lia.
          replace (S idx1 + S d)%nat with (S (S idx1 + d))%nat by lia.
          apply Nat.le_trans with (seq (S idx1 + d))%nat.
          + apply IH.
          + apply Nat.lt_le_incl, Hinc.
      }
      specialize (Haux (idx2 - idx1)%nat).
      assert (Hk_gt0 : (idx2 - idx1 > 0)%nat) by lia.
      apply Haux in Hk_gt0.
      replace (idx1 + (idx2 - idx1))%nat with idx2 in Hk_gt0 by lia.
      exact Hk_gt0.
    }
    (* 最终不等式 *)
    apply Rle_ge.
    apply Rle_trans with (INR (seq (S idx1))).
    + (* 第一个子目标：INR c * INR (seq idx1) <= INR (seq (S idx1)) *)
      apply Rlt_le. exact (Hsparse idx1).
    + (* 第二个子目标：INR (seq (S idx1)) <= INR (seq idx2) *)
      apply le_INR. exact Hseq_ge.
Qed.

(* ====================================================
   辅助引理：用于 algebraic_inequality 的拆分证明
   ==================================================== *)

(* 引理 1：自然数 n >= 2 时，INR n > 0 且 sqrt (INR n) > 0 *)
Lemma INR_pos_ge2 : forall n, (n >= 2)%nat -> INR n > 0.
Proof.
  intros. apply Rlt_le_trans with (INR 2); [simpl; lra | apply le_INR; lia].
Qed.

Lemma sqrt_INR_pos_ge2 : forall n, (n >= 2)%nat -> sqrt (INR n) > 0.
Proof.
  intros. apply sqrt_lt_R0_c. apply INR_pos_ge2; auto.
Qed.

(* 引理 2：c >= 2 时，sqrt (INR c) - 1 > 0 *)
Lemma sqrt_c_minus_1_pos : forall c, (c >= 2)%nat -> sqrt (INR c) - 1 > 0.
Proof.
  intros. apply Rgt_minus. apply Rlt_le_trans with (sqrt 2).
  - assert (1 < sqrt 2). { rewrite <- sqrt_1. apply sqrt_lt_1; lra. }
    lra.
  - apply sqrt_le_1_c; apply le_INR in H; simpl in H; lra.
Qed.

(* 引理 3：核心放缩：INR n2 * (INR c - 1) <= 4 * (INR n2 - INR n1) *)
Lemma core_inequality :
  forall n1 n2 c : nat,
    (n1 >= 2)%nat -> (n2 >= 2)%nat -> (n1 < n2)%nat -> (2 <= c <= 4)%nat ->
    INR n2 >= INR c * INR n1 ->
    INR n2 * (INR c - 1) <= 4 * (INR n2 - INR n1).
Proof.
  intros n1 n2 c H1 H2 Hlt [Hc_ge2 Hc_le4] Hge.
  set (a := INR n1); set (b := INR n2); set (k := INR c).
  assert (a > 0) by (apply lt_0_INR; lia).
  assert (b > 0) by (apply lt_0_INR; lia).
  assert (b > a) by (apply lt_INR; exact Hlt).
  assert (k > 0) by (apply lt_0_INR; lia).

  assert (k <= 4).
  { apply le_INR in Hc_le4. simpl in Hc_le4. replace 4 with (1+1+1+1) by ring. exact Hc_le4. }
  assert (2 <= k).
  { apply le_INR in Hc_ge2. simpl in Hc_ge2. replace 2 with (1+1) by ring. exact Hc_ge2. }

  assert (a <= b / k).
  { apply Rmult_le_reg_l with k; [lra |].
    replace (k * (b / k)) with b by (field; lra).
    apply Rge_le in Hge. exact Hge. }

  assert (b - a >= b * (1 - /k)) by lra.

  assert (k - 1 <= 4 * (1 - /k)).
  { apply Rmult_le_reg_l with k; [lra |].
    replace (k * (4 * (1 - /k))) with (4 * (k - 1)) by (field; lra).
    apply Rmult_le_compat_r; [lra | apply H5]. }

  assert (b * (k - 1) <= 4 * b * (1 - /k)).
  {
    rewrite Rmult_comm.
    apply Rle_trans with (4 * (1 - /k) * b).
    - apply Rmult_le_compat_r; [apply Rlt_le; exact H0 | exact H9].
    - assert (Heq : 4 * (1 - /k) * b = 4 * b * (1 - /k)) by ring.
      rewrite Heq; apply Rle_refl.
  }

  apply Rle_trans with (4 * b * (1 - /k)).
  - exact H10.
  - replace (4 * b * (1 - /k)) with (4 * (b * (1 - /k))) by ring.
    apply Rmult_le_compat_l; [lra | apply Rge_le; exact H8].
Qed.

(* 引理 4：sqrt (INR c) - 1 <= INR c - 1 *)
Lemma sqrt_le_self_minus_1 : forall c, (c >= 2)%nat -> sqrt (INR c) - 1 <= INR c - 1.
Proof.
  intros c Hc.
  apply Rplus_le_compat_r with (r := -1).
  assert (H0 : 0 <= INR c) by (apply pos_INR; lia).
  assert (H1 : INR c <= INR c * INR c).
  { apply Rle_trans with (INR c * 1).
    - rewrite Rmult_1_r; apply Rle_refl.
    - apply Rmult_le_compat_l; [apply H0 | apply (le_INR 1 c); lia]. }
  assert (H2 : 0 <= INR c * INR c) by apply Rle_0_sqr.
  apply (Rle_trans _ (sqrt (INR c * INR c))).
  - apply sqrt_le_1_c; auto.
- rewrite sqrt_square with (x := INR c); [| apply H0].
  reflexivity.
Qed.

(* 引理 5：平方根分式单调性 *)
Lemma algebraic_inequality_reduced :
  forall n1 n2 c : nat,
    (n1 >= 2)%nat -> (n2 >= 2)%nat -> (n1 < n2)%nat -> (c >= 2)%nat ->
    INR n2 * (sqrt (INR c) - 1) <= 4 * (INR n2 - INR n1) ->
    sqrt (INR n1 * INR n2) / (4 * (INR n2 - INR n1)) <=
    sqrt (INR n1 / INR n2) / (sqrt (INR c) - 1).
Proof.
  intros n1 n2 c H1 H2 Hlt Hc Hred.
  assert (Hdiff_pos : INR n2 - INR n1 > 0).
  { apply Rgt_minus. apply lt_INR; exact Hlt. }
  assert (Hpos1 : 4 * (INR n2 - INR n1) > 0).
  { apply Rmult_lt_0_compat; [lra | exact Hdiff_pos]. }
  assert (Hpos2 : sqrt (INR c) - 1 > 0).
  { apply sqrt_c_minus_1_pos; auto. }
  assert (Hpos_total : 4 * (INR n2 - INR n1) * (sqrt (INR c) - 1) > 0).
  { apply Rmult_lt_0_compat; assumption. }

  apply (Rmult_le_reg_l (4 * (INR n2 - INR n1) * (sqrt (INR c) - 1))); auto.

  replace (4 * (INR n2 - INR n1) * (sqrt (INR c) - 1) *
           (sqrt (INR n1 * INR n2) / (4 * (INR n2 - INR n1))))
    with (sqrt (INR n1 * INR n2) * (sqrt (INR c) - 1)).
  2: { unfold Rdiv; field; try lra; apply Rgt_not_eq; assumption. }

  replace (4 * (INR n2 - INR n1) * (sqrt (INR c) - 1) *
           (sqrt (INR n1 / INR n2) / (sqrt (INR c) - 1)))
    with (4 * (INR n2 - INR n1) * sqrt (INR n1 / INR n2)).
  2: { unfold Rdiv; field; try lra; apply Rgt_not_eq; assumption. }

  assert (Hsqrt_mult : sqrt (INR n1 * INR n2) = sqrt (INR n1) * sqrt (INR n2)).
  {
    rewrite <- sqrt_mult.
    - reflexivity.
    - apply Rlt_le; apply INR_pos_ge2; auto.
    - apply Rlt_le; apply INR_pos_ge2; auto.
  }
  rewrite Hsqrt_mult.

  assert (Hsqrt_div : sqrt (INR n1 / INR n2) = sqrt (INR n1) / sqrt (INR n2)).
  {
    rewrite <- sqrt_div.
    - reflexivity.
    - apply Rlt_le; apply INR_pos_ge2; auto.
    - apply INR_pos_ge2; auto.
  }
  rewrite Hsqrt_div.

  assert (Hsq1 : sqrt (INR n1) * sqrt (INR n1) = INR n1).
  { apply sqrt_sqrt; apply Rlt_le; apply INR_pos_ge2; auto. }
  assert (Hsq2 : sqrt (INR n2) * sqrt (INR n2) = INR n2).
  { apply sqrt_sqrt; apply Rlt_le; apply INR_pos_ge2; auto. }

  apply (Rmult_le_reg_l (sqrt (INR n2))).
  { apply sqrt_INR_pos_ge2; auto. }

  replace (sqrt (INR n2) * (sqrt (INR n1) * sqrt (INR n2) * (sqrt (INR c) - 1)))
    with (sqrt (INR n1) * INR n2 * (sqrt (INR c) - 1)).
  2: { ring [Hsq2]. }

  replace (sqrt (INR n2) * (4 * (INR n2 - INR n1) * (sqrt (INR n1) / sqrt (INR n2))))
    with (4 * (INR n2 - INR n1) * sqrt (INR n1)).
  2: { unfold Rdiv; field; apply Rgt_not_eq, sqrt_INR_pos_ge2; auto. }

  apply (Rmult_le_reg_l (sqrt (INR n1))).
  { apply sqrt_INR_pos_ge2; auto. }

  replace (sqrt (INR n1) * (sqrt (INR n1) * INR n2 * (sqrt (INR c) - 1)))
    with (INR n1 * INR n2 * (sqrt (INR c) - 1)).
  2: { ring [Hsq1]. }

  replace (sqrt (INR n1) * (4 * (INR n2 - INR n1) * sqrt (INR n1)))
    with (INR n1 * (4 * (INR n2 - INR n1))).
  2: { ring [Hsq1]. }

  replace (INR n1 * INR n2 * (sqrt (INR c) - 1))
    with (INR n1 * (INR n2 * (sqrt (INR c) - 1))) by ring.

  apply (Rmult_le_reg_l (INR n1)).
  { apply Rlt_gt, lt_0_INR; lia. }

  nra.
Qed.

(* 定理：核心代数不等式 *)
Theorem algebraic_inequality :
  forall n1 n2 c : nat,
    (n1 >= 2)%nat -> (n2 >= 2)%nat -> (n1 < n2)%nat -> (c >= 2)%nat -> (c <= 4)%nat ->
    (INR n2 >= INR c * INR n1)%R ->
    sqrt (INR n1 * INR n2) / (4 * (INR n2 - INR n1)) <=
    sqrt (INR n1 / INR n2) / (sqrt (INR c) - 1).
Proof.
  intros n1 n2 c H1 H2 Hlt Hc Hc_le4 Hge.
  set (a := INR n1); set (b := INR n2); set (k := INR c).

  assert (a > 0) by (unfold a; apply Rlt_le_trans with (INR 2); [simpl; lra | apply le_INR; lia]).
  assert (b > a) by (unfold a, b; apply lt_INR; exact Hlt).
  assert (k >= 2) by (unfold k; apply le_INR in Hc; simpl in Hc; lra).

  unfold a, b, k in *; clear a b k.

  assert (Hdiff : INR n2 - INR n1 >= (INR c - 1) * INR n1).
  { apply Rle_ge.
    apply Rplus_le_reg_r with (r := INR n1).
    ring_simplify.
    apply Rge_le in Hge.
    exact Hge. }

  assert (Hsqrt : sqrt (INR n1 * INR n2) = sqrt (INR n1) * sqrt (INR n2))
    by (apply sqrt_mult; lra).

  rewrite Hsqrt.

  assert (Hcore : INR n2 * (INR c - 1) <= 4 * (INR n2 - INR n1)).
  { apply core_inequality with (n1 := n1) (n2 := n2) (c := c); auto. }

  assert (Hsqrt_le : sqrt (INR c) - 1 <= INR c - 1).
  { apply sqrt_le_self_minus_1; auto. }

  assert (Hred : INR n2 * (sqrt (INR c) - 1) <= 4 * (INR n2 - INR n1)).
  { apply Rle_trans with (INR n2 * (INR c - 1)).
    - apply Rmult_le_compat_l; [apply Rlt_le, lt_0_INR; lia | exact Hsqrt_le].
    - exact Hcore. }

  rewrite <- Hsqrt.
  apply algebraic_inequality_reduced; auto.
Qed.

(* 定理：广义代数不等式 *)
Theorem algebraic_inequality_general :
  forall n1 n2 c : nat,
    (n1 >= 2)%nat -> (n2 >= 2)%nat -> (n1 < n2)%nat -> (c >= 2)%nat ->
    (INR n2 >= INR c * INR n1)%R ->
    sqrt (INR n1 * INR n2) / (INR c * (INR n2 - INR n1)) <=
    sqrt (INR n1 / INR n2) / (sqrt (INR c) - 1).
Proof.
  intros n1 n2 c H1 H2 Hlt Hc Hge.
  assert (Hn1_pos : 0 < INR n1) by (apply lt_0_INR; lia).
  assert (Hn2_pos : 0 < INR n2) by (apply lt_0_INR; lia).
  assert (Hc_ge2 : 2 <= INR c) by (apply le_INR in Hc; simpl in Hc; lra).
  assert (Hdiff_pos : 0 < INR n2 - INR n1) by (apply Rgt_minus; apply lt_INR; lia).
  set (a := INR n1). set (b := INR n2). set (k := INR c).

  assert (Hk_pos : 0 < k) by (apply lt_0_INR; lia).
  assert (Hsqrt_k_minus_pos : 0 < sqrt k - 1).
  { apply Rgt_minus. rewrite <- sqrt_1. apply sqrt_lt_1;
      [apply Rle_0_1 | apply Rle_trans with 2; [lra | exact Hc_ge2] |
       apply Rlt_le_trans with 2; [lra | exact Hc_ge2]]. }

  rewrite (sqrt_mult a b); [| apply Rlt_le; exact Hn1_pos | apply Rlt_le; exact Hn2_pos].
  rewrite (sqrt_div a b); [| apply Rlt_le; exact Hn1_pos | exact Hn2_pos].

  apply (Rmult_le_reg_r (k * (b - a) * (sqrt k - 1) * sqrt b)).
  { repeat apply Rmult_lt_0_compat; auto;
    try apply Hk_pos; try apply Hdiff_pos;
    try apply Hsqrt_k_minus_pos; try apply sqrt_lt_R0_c; auto. }

  replace (sqrt a * sqrt b / (k * (b - a)) * (k * (b - a) * (sqrt k - 1) * sqrt b))
    with (sqrt a * sqrt b * (sqrt k - 1) * sqrt b).
  2: { field. repeat split; apply Rgt_not_eq; auto. }

  assert (Hsqrt_b_pos : 0 < sqrt b) by (apply sqrt_lt_R0_c; exact Hn2_pos).
  replace ((sqrt a / sqrt b) / (sqrt k - 1) * (k * (b - a) * (sqrt k - 1) * sqrt b))
    with (sqrt a * k * (b - a)).
  2: { field. repeat split; apply Rgt_not_eq; auto. }

  apply (Rmult_le_reg_l (sqrt a)).
  { apply sqrt_lt_R0_c; exact Hn1_pos. }

  replace (sqrt a * (sqrt a * sqrt b * (sqrt k - 1) * sqrt b))
    with ((sqrt a * sqrt a) * (sqrt b * sqrt b) * (sqrt k - 1)).
  2: { ring. }
  replace (sqrt a * (sqrt a * k * (b - a))) with ((sqrt a * sqrt a) * k * (b - a)).
  2: { ring. }

  replace (sqrt a * sqrt a) with a.
  2: { symmetry; apply sqrt_sqrt; apply Rlt_le; exact Hn1_pos. }
  replace (sqrt b * sqrt b) with b.
  2: { symmetry; apply sqrt_sqrt; apply Rlt_le; exact Hn2_pos. }

  apply (Rmult_le_reg_l a); [exact Hn1_pos |].

  replace (a * (a * b * (sqrt k - 1))) with (a * a * b * (sqrt k - 1)) by ring.
  replace (a * (a * k * (b - a))) with (a * a * k * (b - a)) by ring.

  apply (Rmult_le_reg_l (a * a)); [ apply Rmult_lt_0_compat; auto with real | ].
  replace (a * a * (a * a * b * (sqrt k - 1))) with (a * a * a * a * b * (sqrt k - 1)) by ring.
  replace (a * a * (a * a * k * (b - a))) with (a * a * a * a * k * (b - a)) by ring.

  apply (Rmult_le_reg_r (/ (a * a * a * a))).
  { apply Rinv_0_lt_compat; repeat apply Rmult_lt_0_compat; auto with real. }

  replace (a * a * a * a * b * (sqrt k - 1) * / (a * a * a * a))
    with (b * (sqrt k - 1)).
  2: { field. repeat split; apply Rgt_not_eq; auto with real. }
  replace (a * a * a * a * k * (b - a) * / (a * a * a * a))
    with (k * (b - a)).
  2: { field. repeat split; apply Rgt_not_eq; auto with real. }

  apply Rle_trans with (b * (k - 1)).
  - apply Rmult_le_compat_l; [ apply Rlt_le; exact Hn2_pos | ].
    apply sqrt_le_self_minus_1; auto.
  - assert (H_main : b * (k - 1) <= k * (b - a)).
    {
      rewrite Rmult_minus_distr_l.
      rewrite Rmult_minus_distr_l.
      apply Rplus_le_reg_r with b.
      ring_simplify.
      apply Rplus_le_reg_l with (- (b * k)).
      ring_simplify.
      apply Rplus_le_reg_l with (k * a).
      rewrite Rplus_0_r.
      rewrite Rplus_comm.
      replace (b - k * a + k * a) with b by ring.
      apply Rge_le. exact Hge.
    }
    exact H_main.
Qed.

(* ============================================================
   模块：UnconditionalBasisLemmas
   目的：为 psi_unconditional_basis 定理提供辅助引理
   ============================================================ *)

Local Open Scope complex_scope.
Local Open Scope R_scope.
Local Close Scope R_scope.
Local Open Scope nat_scope.




Local Open Scope R_scope.

(* 稀疏序列项保底二 *)
Lemma seq_ge_2_from_base :
  forall (seq : nat -> nat) (c : nat),
    (c >= 1)%nat ->
    (seq 0 >= 2)%nat ->
    (forall idx : nat, (INR (seq (S idx)) > INR c * INR (seq idx))%R) ->
    forall i : nat, (seq i >= 2)%nat.
Proof.
  intros seq c Hc_ge1 Hseq0_ge2 Hbase.
  induction i as [|i IH].
  - exact Hseq0_ge2.
  - assert (H4 : (INR (seq (S i)) > INR c * INR (seq i))%R) by apply Hbase.
    (* 从 c >= 1 推出 INR c >= 1 *)
    assert (Hc_INR_ge1 : (INR c >= 1)%R).
    {
      assert (H1_le_c : (1 <= c)%nat) by lia.
      apply le_INR in H1_le_c.
      simpl in H1_le_c.
      lra.
    }
    (* 从 seq i >= 2 推出 INR (seq i) >= 2 *)
    assert (H_seq_i_ge2 : (INR (seq i) >= 2)%R).
    {
      apply le_INR in IH.
      simpl in IH.
      lra.
    }
    assert (H_seq_i_pos : (0 < INR (seq i))%R) by lra.
    (* 乘积不等式：INR c * INR (seq i) >= INR (seq i) *)
assert (Hprod_ge : (INR c * INR (seq i) >= INR (seq i))%R).
{
  apply Rle_ge.
  replace (INR (seq i)) with (1 * INR (seq i)) at 1 by ring.
  apply Rmult_le_compat_r; [lra | lra].
}
    (* 结合 H4 得到 INR (seq (S i)) > INR (seq i) *)
    assert (H5 : (INR (seq (S i)) > INR (seq i))%R) by lra.
    apply INR_lt in H5. lia.
Qed.

(* 序列严格递增步长 *)
Lemma seq_strict_inc_step :
  forall (seq : nat -> nat) (c : nat),
    (c >= 1)%nat ->
    (forall i, (seq i >= 2)%nat) ->
    (forall idx, (INR (seq (S idx)) > INR c * INR (seq idx))%R) ->
    forall i, (seq i < seq (S i))%nat.
Proof.
  intros seq c Hc_ge1 Hall_ge2 Hbase i.
  assert (H1 : (seq i >= 2)%nat) by apply Hall_ge2.
  assert (H2 : (INR (seq i) > 0)%R) by (apply lt_0_INR; lia).
  (* 直接断言 1 <= INR c，以匹配 Rmult_le_compat_r 的前提 *)
  assert (Hc_INR_le : 1 <= INR c).
  {
    assert (H1_le_c : (1 <= c)%nat) by lia.
    apply le_INR in H1_le_c.
    simpl in H1_le_c.
    exact H1_le_c.
  }
  assert (H4 : (INR (seq (S i)) > INR c * INR (seq i))%R) by apply Hbase.
  assert (H5 : (INR c * INR (seq i) >= INR (seq i))%R).
  {
    apply Rle_ge.
    replace (INR (seq i)) with (1 * INR (seq i)) at 1 by ring.
    apply (Rmult_le_compat_r (INR (seq i)) 1 (INR c)).
    - apply Rlt_le; exact H2.
    - exact Hc_INR_le.
  }
  assert (H6 : (INR (seq (S i)) > INR (seq i))%R) by lra.
  apply INR_lt. exact H6.
Qed.

Close Scope R_scope.

(* 配对索引的取值性质 *)
Lemma nth_pair_properties :
  forall (vals : list nat) (I : list nat) (idx1 idx2 : nat)
    (H_len : length vals = length I)
    (Hidx1 : idx1 < length I)
    (Hidx2 : idx2 < length I)
    (Hneq : idx1 <> idx2)
    (Hvals_ge2 : forall n, In n vals -> n >= 2)
    (Hnodup_vals : NoDup vals),
  let n1 := nth idx1 vals 0 in
  let n2 := nth idx2 vals 0 in
  n1 >= 2 /\ n2 >= 2 /\ n1 <> n2.
Proof.
  intros vals I idx1 idx2 H_len Hidx1 Hidx2 Hneq Hvals_ge2 Hnodup_vals.
  simpl.
  split.
  - (* n1 >= 2 *)
    apply (Hvals_ge2 (nth idx1 vals 0)).
    apply nth_In.
    rewrite H_len.
    exact Hidx1.
  - split.
    + (* n2 >= 2 *)
      apply (Hvals_ge2 (nth idx2 vals 0)).
      apply nth_In.
      rewrite H_len.
      exact Hidx2.
    + (* n1 <> n2 *)
      intros Heq.
      apply Hneq.
      (* 使用 NoDup_nth 从 nth 相等推导索引相等 *)
      eapply NoDup_nth; eauto.
      - rewrite H_len; exact Hidx1.
      - rewrite H_len; exact Hidx2.
Qed.

(* 无重复列表不同索引元素相异 *)
Lemma NoDup_nth_neq_std : forall {A : Type} (l : list A) (d : A) (i j : nat),
  NoDup l ->
  (i < length l)%nat ->
  (j < length l)%nat ->
  i <> j ->
  nth i l d <> nth j l d.
Proof.
  intros A l d i j Hdup Hi Hj Hneq Heq.
  apply Hneq.
  eapply NoDup_nth; eauto.
Qed.

Close Scope R_scope.

(* 序列映射的基本性质 *)
Lemma basic_properties :
  forall (seq : nat -> nat) (I : list nat) (c : nat)
    (Hc_ge1 : (c >= 1)%nat)
    (Hseq0_ge2 : (seq 0 >= 2)%nat)
    (Hbase : forall idx : nat, (INR (seq (S idx)) > INR c * INR (seq idx))%R)
    (HI : NoDup I)
    (idx1 idx2 : nat)
    (Hneq : (idx1 <> idx2)%nat)
    (Hidx1 : idx1 < length I)
    (Hidx2 : idx2 < length I),
  let vals := map seq I in
  let n1 := nth idx1 vals 0%nat in
  let n2 := nth idx2 vals 0%nat in
  (forall i : nat, (seq i < seq (S i))%nat) /\
  (forall i j : nat, (i < j)%nat -> (seq i < seq j)%nat) /\
  (forall n : nat, In n vals -> (n >= 2)%nat) /\
  NoDup vals /\
  (n1 >= 2)%nat /\ (n2 >= 2)%nat /\ (n1 <> n2)%nat.
Proof.
  intros seq I c Hc_ge1 Hseq0_ge2 Hbase HI idx1 idx2 Hneq Hidx1 Hidx2.
  set (vals := map seq I).
  set (n1 := nth idx1 vals 0%nat).
  set (n2 := nth idx2 vals 0%nat).

  (* 1. 所有序列项均不小于 2 *)
  pose proof (seq_ge_2_from_base seq c Hc_ge1 Hseq0_ge2 Hbase) as Hall_ge2.

  (* 2. 相邻项严格递增 *)
  assert (Hinc : forall i, (seq i < seq (S i))%nat).
  { apply seq_strict_inc_step with (c:=c); assumption. }

  (* 3. 全局严格递增 *)
  assert (Hstrict : forall i j, i < j -> seq i < seq j).
  { apply seq_strictly_increasing_aux; exact Hinc. }

  (* 4. 映射后的列表 vals 中所有元素均不小于 2 *)
  assert (Hvals_ge2 : forall n : nat, In n vals -> (n >= 2)%nat).
  {
    intros n Hin.
    apply in_map_iff in Hin.
    destruct Hin as [i [Heq Hi]].
    subst n.
    exact (Hall_ge2 i).
  }

  (* 5. vals 无重复元素 *)
  assert (Hnodup_vals : NoDup vals).
  { apply map_seq_nodup; [exact Hstrict | exact HI]. }

  (* 6. 获取 n1 与 n2 的性质 *)
  assert (H_len_eq : length vals = length I).
  { subst vals; rewrite length_map; reflexivity. }
  specialize (nth_pair_properties vals I idx1 idx2 H_len_eq
                                  Hidx1 Hidx2 Hneq Hvals_ge2 Hnodup_vals)
    as [Hn1_ge2 [Hn2_ge2 Hn1_neq_n2]].

  (* 7. 综合所有结论 *)
  repeat split;
    [ exact Hinc
    | exact Hstrict
    | exact Hvals_ge2
    | exact Hnodup_vals
    | exact Hn1_ge2
    | exact Hn2_ge2
    | exact Hn1_neq_n2 ].
Qed.

(* psi 在索引大于等于 n 时为零 *)
Lemma psi_ge_n_zero : forall n k, (n <= k)%nat -> psi n k = C0.
Proof.
  intros n k Hle. unfold psi. apply psi_zero_for_ge_n; lia.
Qed.

(* 定理：Psi 内积求和尾部截断 *)
Theorem truncate_inner_sum_correct :
  forall (n1 n2 : nat) (N : nat),
    n1 >= 2 ->
    n1 <= N ->
    independent.Csum (fun k => psi n1 k *c Cconj (psi n2 k)) N =
    independent.Csum (fun k => psi n1 k *c Cconj (psi n2 k)) n1.
Proof.
  intros n1 n2 N Hge2 Hle.
  assert (Hzero : forall k, (k >= n1)%nat -> psi n1 k = C0).
  { intros k Hk. apply psi_ge_n_zero; lia. }
  destruct (le_lt_dec N n1) as [HleN | HgtN].
  - assert (Heq : N = n1) by lia. subst; reflexivity.
  - set (M := n1).
    assert (HN : (N = M + (N - M))%nat) by lia.
    rewrite HN; clear HN.
    induction (N - M)%nat as [|d IH].
    + rewrite Nat.add_0_r; reflexivity.
    + replace (M + S d)%nat with (S (M + d))%nat by lia.
      simpl independent.Csum.
      rewrite IH.
      subst M.
      assert (Hterm_zero : psi n1 (n1 + d) *c Cconj (psi n2 (n1 + d)) = C0).
      { assert (Hge : (n1 + d >= n1)%nat) by lia.
        rewrite Hzero by exact Hge.
        apply Cmul_0_l. }
      rewrite Hterm_zero.
      rewrite Cadd_0_r.
      reflexivity.
Qed.

Open Scope R_scope.

(* 内积几何级数展开 *)
Lemma inner_geometric_expansion :
  forall n1 n2,
    (n1 >= 2)%nat -> (n2 >= 2)%nat -> (n1 <= n2)%nat ->
  let θ := 2 * PI * (1 / INR n1 - 1 / INR n2) in
  Csum (fun k => psi n1 k *c Cconj (psi n2 k)) (n1 - 1) =
    (Cof_real (1 / sqrt (INR n1)) *c Cof_real (1 / sqrt (INR n2))) *c
    Csum (fun k => Cexp (0 +i (INR k * θ))) (n1 - 1).
Proof.
  intros n1 n2 H1 H2 Hle.
  apply inner_expand; auto.
Qed.

(* 减法分解：a = b + (a - b) *)
Lemma Csub_add : forall a b, a = b +c (a -c b).
Proof.
  intros a b; destruct a, b; unfold Cadd, Csub; simpl; f_equal; ring.
Qed.

(* 一减复数非零：若 z ≠ 1，则 1 - z ≠ 0 *)
Lemma C1_minus_z_neq0 (z : Complex) (Hz : z <> C1) : C1 -c z <> C0.
Proof.
  intros H.
  apply Hz.
  rewrite (Csub_add C1 z).   (* 将 C1 重写为 z +c (C1 -c z) *)
  rewrite H.
  rewrite Cadd_0_r.
  reflexivity.
Qed.

Local Open Scope complex_scope.

Close Scope R_scope.

(* 几何级数求和公式 *)
Lemma geometric_series_sum (z : Complex) (n : nat) (Hz : z <> C1) :
  Csum (fun k => z ^ k) n =
    Cdiv (C1 -c z ^ n) (C1 -c z)
         (nonzero_norm_sq_nonzero (C1 -c z) (C1_minus_z_nonzero z Hz)).
Proof.
  apply Csum_geometric_complex; assumption.
Qed.

Open Scope R_scope.

(* 复数范数的倒数恒等式 *)
Lemma norm_of_inverse (w : Complex) (Hw : w <> C0) (Hnz : Cnorm_sq w <> 0) :
  Cnorm (Cinv w Hnz) = / Cnorm w.
Proof.
  apply Rmult_eq_reg_l with (Cnorm w).
  - rewrite <- Cnorm_mult.
    rewrite (Cinv_mult_r w Hnz).  (* w *c Cinv w Hnz = C1 *)
    rewrite Cnorm_one.
    field.
    apply Rgt_not_eq, Cnorm_pos; auto.
  - apply Rgt_not_eq, Cnorm_pos; auto.
Qed.

(* 复数幂的模等于模的幂 *)
Lemma Cnorm_pow : forall z n, Cnorm (z ^ n) = (Cnorm z) ^ n.
Proof.
  intros z n; induction n as [|n IH]; simpl.
  - rewrite Cnorm_one; reflexivity.
  - rewrite Cnorm_mult, IH; reflexivity.
Qed.

(* 定理：几何级数范数上界 *)
Theorem geometric_sum_norm_bound :
  forall (z : Complex) (n : nat),
    z <> C1 ->
    Cnorm z = 1 ->
    let S := Csum (fun k => Cpow z k) n in
    Cnorm S <= 2 / Cnorm (C1 -c z).
Proof.
  intros z n Hz Hnorm.
  assert (Hdiff_neq0 : C1 -c z <> C0) by (apply C1_minus_z_nonzero; auto).
  rewrite (geometric_series_sum z n Hz).
  unfold Cdiv.
  rewrite Cnorm_mult.

  (* 1. 计算逆元的范数 *)
  assert (Hinv_norm : Cnorm (Cinv (C1 -c z) (nonzero_norm_sq_nonzero (C1 -c z) Hdiff_neq0)) =
                      / Cnorm (C1 -c z)).
  { apply Rmult_eq_reg_l with (Cnorm (C1 -c z)).
    - rewrite <- Cnorm_mult.
      rewrite (Cinv_mult_r (C1 -c z) (nonzero_norm_sq_nonzero (C1 -c z) Hdiff_neq0)).
      rewrite Cnorm_one.
      field.
      apply Rgt_not_eq, Cnorm_pos; auto.
    - apply Rgt_not_eq, Cnorm_pos; auto. }

  (* 2. 将目标中的逆元范数暂存并替换 *)
  set (inv_norm := ∥ (C1 -c z) ⁻¹ ∥).
  assert (Hinv_eq : inv_norm = / ∥ C1 -c z ∥) by (subst inv_norm; apply Hinv_norm).
  rewrite Hinv_eq.
  clear inv_norm Hinv_eq.

  (* 3. 将目标整理为除法形式以便消去公因子 *)
  replace (∥ C1 -c z ^ n ∥ * / ∥ C1 -c z ∥) with (∥ C1 -c z ^ n ∥ / ∥ C1 -c z ∥) by reflexivity.
  replace (2 / ∥ C1 -c z ∥) with (2 * / ∥ C1 -c z ∥) by reflexivity.

  (* 4. 利用乘法单调性，两边乘以 / ∥ C1 -c z ∥（正数）*)
  apply Rmult_le_compat_r with (r := / ∥ C1 -c z ∥).
  - apply Rlt_le, Rinv_0_lt_compat, Cnorm_pos; auto.
  - (* 只需证明 ∥ C1 -c z ^ n ∥ ≤ 2 *)
    (* 将减法转化为加法：C1 -c z^n = C1 +c (-c z^n) *)
    replace (C1 -c z ^ n) with (C1 +c (-c z ^ n)).
    2: {
      (* 使用 Complex_eq 将等式转化为实部虚部等式，然后用 ring 处理实数部分 *)
      apply Complex_eq; simpl.
      - (* 实部 *) ring.
      - (* 虚部 *) ring.
    }
    (* 应用库中专门针对 C1 +c z 的范数不等式 *)
    rewrite Cnorm_add_1.
    rewrite Cnorm_neg.
    rewrite Cnorm_pow, Hnorm.
    rewrite pow1.
    lra.
Qed.

(* 分母下界（Jordan 不等式） *)
Lemma denom_lower_bound :
  forall θ : R,
    Rabs θ <= PI ->
    Cnorm (C1 -c Cexp (0 +i θ)) >= 2 * Rabs θ / PI.
Proof.
  intros θ Hbound.
  rewrite Cnorm_one_minus_exp_i_theta_eq.
  rewrite Rabs_sin_eq.
  - rewrite Rabs_div_2.
    set (x := Rabs θ / 2).
    assert (Hx_low : 0 <= x) by (unfold x; apply Rmult_le_pos; [apply Rabs_pos | lra]).
    assert (Hx_high : x <= PI / 2) by (unfold x; apply Rmult_le_compat_r; [lra | exact Hbound]).
    pose proof (jordan_standard x (conj Hx_low Hx_high)) as Hj.
    simpl in Hj.
    replace (2 / PI * x) with (Rabs θ / PI) in Hj by (unfold x; field; apply Rgt_not_eq, PI_RGT_0).
    apply (Rmult_ge_compat_l 2) in Hj; [| lra].
    replace (2 * Rabs θ / PI) with (2 * (Rabs θ / PI)) by (field; apply Rgt_not_eq, PI_RGT_0).
    exact Hj.
  - rewrite Rabs_div_2; apply Rmult_le_compat_r; [lra | exact Hbound].
Qed.

(* θ 的绝对值表达式 *)
Lemma theta_abs_expr :
  forall n1 n2 : nat,
    (0 < n1)%nat -> (0 < n2)%nat -> (n1 <= n2)%nat ->
    Rabs (2 * PI * (/ INR n1 - / INR n2)) = 2 * PI * (INR n2 - INR n1) / (INR n1 * INR n2).
Proof.
  intros n1 n2 H1 H2 Hle.
  set (a := INR n1) in *; set (b := INR n2) in *.
  assert (Ha : a > 0) by (apply lt_0_INR; lia).
  assert (Hb : b > 0) by (apply lt_0_INR; lia).
  assert (Hab : a <= b) by (apply le_INR; exact Hle).
  rewrite Rabs_mult.
  rewrite (Rabs_right (2 * PI)).
  - replace (/ a - / b) with ((b - a) / (a * b)) by (field; lra).
    assert (Hfrac_ge0 : 0 <= (b - a) / (a * b)).
    { apply Rmult_le_pos.
      - lra.
      - apply Rlt_le, Rinv_0_lt_compat, Rmult_lt_0_compat; assumption. }
    rewrite (Rabs_pos_eq _ Hfrac_ge0).
    field; split; apply Rgt_not_eq; assumption.
  - apply Rle_ge, Rmult_le_pos; [lra | apply Rlt_le, PI_RGT_0].
Qed.

(* 稀疏性不等式 *)
Lemma sparse_inequality :
  forall (seq : nat -> nat) (c : nat) (idx1 idx2 : nat),
    (forall i, INR (seq (S i)) > INR c * INR (seq i))%R ->
    (idx1 < idx2)%nat ->
    INR (seq idx2) >= INR c * INR (seq idx1).
Proof.
  intros seq c idx1 idx2 Hsparse Hlt.
  (* 情况 1: c = 0 *)
  destruct c as [|c'].
  - (* INR 0 = 0，不等式平凡成立 *)
    rewrite Rmult_0_l.
    apply Rle_ge, pos_INR.
  - (* 情况 2: c = S c' ≥ 1 *)
    set (k := (idx2 - idx1)%nat).
    assert (Hk_ge1 : (k >= 1)%nat) by lia.
    replace idx2 with (idx1 + k)%nat by lia.
    clear Hlt.
    (* 对 k 进行归纳 *)
    induction k as [|k' IH].
    + exfalso; lia.
    + destruct k' as [|k''].
      * (* 基础情形：k = 1 *)
        replace (idx1 + 1)%nat with (S idx1) by lia.
        apply Rle_ge, Rlt_le, Hsparse.
      * (* 归纳情形：k = S (S k'') ≥ 2 *)
        replace (idx1 + S (S k''))%nat with (S (idx1 + S k''))%nat by lia.
        pose proof (Hsparse (idx1 + S k'')%nat) as Hstep.
        assert (IH_inst : INR (seq (idx1 + S k'')%nat) >= INR (S c') * INR (seq idx1)).
        { apply IH; lia. }
        (* 先证明序列严格递增（用于单调性） *)
        assert (Hstrict_inc : forall i, (seq i < seq (S i))%nat).
        {
          intros i.
          apply INR_lt.
          apply Rle_lt_trans with (r2 := INR (S c') * INR (seq i)).
          - (* INR (seq i) ≤ INR (S c') * INR (seq i) *)
            rewrite <- (Rmult_1_l (INR (seq i))) at 1.
            apply Rmult_le_compat_r.
            + apply pos_INR.
            + change 1 with (INR 1). apply le_INR; lia. (* 1 ≤ S c' *)
          - apply Hsparse.
        }
        (* 由严格递增推出单调性 *)
        assert (Hmono : forall i j, (i <= j)%nat -> (seq i <= seq j)%nat).
        {
          intros i j Hle.
          induction Hle.
          - apply Nat.le_refl.
          - apply Nat.le_trans with (seq m); [exact IHHle | apply Nat.lt_le_incl, Hstrict_inc].
        }
        assert (Hge : (seq idx1 <= seq (idx1 + S k''))%nat).
        { apply Hmono; lia. }
        (* 最终不等式 *)
        apply Rle_ge.
        apply Rle_trans with (r2 := INR (S c') * INR (seq (idx1 + S k'')%nat)).
        - apply Rmult_le_compat_l.
          + apply pos_INR.
          + apply le_INR, Hge.
        - apply Rlt_le, Hstep.
Qed.

(** 核心代数不等式（稀疏因子受限于4的情形） *)
Lemma core_algebraic_inequality :
  forall n1 n2 c : nat,
    (n1 >= 2)%nat -> (n2 >= 2)%nat -> (n1 < n2)%nat -> (c >= 2)%nat -> (c <= 4)%nat ->
    INR n2 >= INR c * INR n1 ->
    sqrt (INR n1 * INR n2) / (4 * (INR n2 - INR n1)) <=
    sqrt (INR n1 / INR n2) / (sqrt (INR c) - 1).
Proof.
  intros. apply algebraic_inequality; auto.
Qed.

(* 通用版本（无上界限制）：分母为 INR c * Δ *)
Lemma core_algebraic_inequality_general :
  forall n1 n2 c : nat,
    (n1 >= 2)%nat -> (n2 >= 2)%nat -> (n1 < n2)%nat -> (c >= 2)%nat ->
    INR n2 >= INR c * INR n1 ->
    sqrt (INR n1 * INR n2) / (INR c * (INR n2 - INR n1)) <=
    sqrt (INR n1 / INR n2) / (sqrt (INR c) - 1).
Proof.
  intros. apply algebraic_inequality_general; auto.
Qed.

(* ----------------------------------------------------
   版本 1：常用小常数优化版（c = 2 或 3）
   ----------------------------------------------------
   当 c=2 或 c=3 时，无需 c≤4 的限制，且分母保持 4·Δ 的紧界。
   应用：黎曼猜想证明中稀疏序列的典型倍数因子。
*)
Lemma core_algebraic_inequality_small_c :
  forall (n1 n2 c : nat),
    (n1 >= 2)%nat -> (n2 >= 2)%nat -> (n1 < n2)%nat ->
    (c = 2 \/ c = 3)%nat ->
    INR n2 >= INR c * INR n1 ->
    sqrt (INR n1 * INR n2) / (4 * (INR n2 - INR n1)) <=
    sqrt (INR n1 / INR n2) / (sqrt (INR c) - 1).
Proof.
  intros n1 n2 c H1 H2 Hlt Hc Hge.
  assert (c <= 4)%nat by (destruct Hc as [-> | ->]; lia).
  assert (c >= 2)%nat by (destruct Hc as [-> | ->]; lia).
  apply core_algebraic_inequality with (c := c); auto.
Qed.

(* 25的平方根等于5 *)
Lemma sqrt_25_eq_5 : sqrt (INR 25) = 5.
Proof.
  assert (H : 0 <= 5) by lra.
  rewrite <- (sqrt_square 5 H).
  f_equal.
  simpl; ring.
Qed.

(* 2的n次幂不小于n *)
Lemma pow2_ge_INR : forall n : nat, 2 ^ n >= INR n.
Proof.
  intros n; apply Rle_ge.
  induction n as [|n IH].
  - simpl; lra.
  - destruct n as [|n'].
    + simpl; lra.
    + simpl pow. rewrite S_INR.
      apply Rle_trans with (2 * INR (S n')).
      * (* 2 * INR (S n') >= INR (S n') + 1 *)
        assert (INR (S n') >= 1) by (change 1 with (INR 1); apply Rle_ge; apply le_INR; lia).
        lra.
      * apply Rmult_le_compat_l; [lra | exact IH].
Qed.

(* 2的n次幂不小于1 *)
Lemma pow2_ge_1 : forall n, 1 <= 2^n.
Proof.
  induction n as [|n IH]; simpl.
  - lra.
  - apply (Rle_trans _ (1 * 2 ^ n) _).
    + rewrite Rmult_1_l; apply IH.
    + apply Rmult_le_compat_r.
      * apply pow_le; lra.
      * lra.
Qed.

(* 平方根除法拆分恒等式 *)
Lemma INR_div_sqrt_eq (n1 n2 : nat) :
  (0 < n1)%nat -> (0 < n2)%nat ->
  INR n1 / sqrt (INR n2) = sqrt (INR n1 / INR n2) * sqrt (INR n1).
Proof.
  intros Hn1 Hn2.
  (* 将自然数正性转换为实数正性 *)
  assert (Hn1_pos : 0 < INR n1) by (apply lt_0_INR; exact Hn1).
  assert (Hn2_pos : 0 < INR n2) by (apply lt_0_INR; exact Hn2).
  (* sqrt 正性与非零 *)
  assert (H_sqrt_n2_gt0 : 0 < sqrt (INR n2)) by (apply sqrt_lt_R0_c; exact Hn2_pos).
  assert (H_sqrt_n2_neq0 : sqrt (INR n2) <> 0) by (apply Rgt_not_eq; exact H_sqrt_n2_gt0).
  
  (* 两边同乘 sqrt (INR n2) *)
  apply (Rmult_eq_reg_r (sqrt (INR n2))); [| exact H_sqrt_n2_neq0].
  
  (* 左边化简 *)
  unfold Rdiv.
  rewrite Rmult_assoc.
  rewrite Rinv_l; [| exact H_sqrt_n2_neq0].
  rewrite Rmult_1_r.
  
  (* 右边：用 replace 显式合并 sqrt 因子 *)
  (* 第一次合并前两个因子 *)
  replace (sqrt (INR n1 * / INR n2) * sqrt (INR n1) * sqrt (INR n2))
    with (sqrt ((INR n1 * / INR n2) * INR n1) * sqrt (INR n2)).
  2: {
    rewrite <- (sqrt_mult (INR n1 * / INR n2) (INR n1)).
    - reflexivity.
    - (* 证明 INR n1 * / INR n2 >= 0 *)
      apply Rmult_le_pos.
      + apply Rlt_le; exact Hn1_pos.
      + apply Rlt_le; apply Rinv_0_lt_compat; exact Hn2_pos.
    - apply Rlt_le; exact Hn1_pos.
  }
  
  (* 第二次合并剩余的因子 *)
  replace (sqrt ((INR n1 * / INR n2) * INR n1) * sqrt (INR n2))
    with (sqrt (((INR n1 * / INR n2) * INR n1) * INR n2)).
  2: {
    rewrite <- (sqrt_mult ((INR n1 * / INR n2) * INR n1) (INR n2)).
    - reflexivity.
    - (* 证明乘积非负 *)
      apply Rmult_le_pos.
      + apply Rmult_le_pos.
        * apply Rlt_le; exact Hn1_pos.
        * apply Rlt_le; apply Rinv_0_lt_compat; exact Hn2_pos.
      + apply Rlt_le; exact Hn1_pos.
    - apply Rlt_le; exact Hn2_pos.
  }
  
  (* 化简根号内部 *)
  replace (((INR n1 * / INR n2) * INR n1) * INR n2) with (INR n1 * INR n1)
    by (field; apply Rgt_not_eq; exact Hn2_pos).
  
  (* 消去平方根 *)
  rewrite sqrt_square; [| apply Rlt_le; exact Hn1_pos].
  reflexivity.
Qed.

(* 分式不等式线性归约 *)
Lemma reduce_to_linear_inequality :
  forall (n1 n2 c : nat) (Hn1_pos : INR n1 > 0) (Hn2_pos : INR n2 > 0)
         (H_diff_pos : INR n2 - INR n1 > 0) (Hc : (c >= 2)%nat),
    (sqrt (INR n1 * INR n2) / (4 * (INR n2 - INR n1)) <=
     sqrt (INR n1 / INR n2) / (sqrt (INR c) - 1)) <->
    (INR n2 * (sqrt (INR c) - 1) <= 4 * (INR n2 - INR n1)).
Proof.
  intros n1 n2 c Hn1_pos Hn2_pos H_diff_pos Hc.
  split.

  - (* 正向：原不等式 ⇒ 线性不等式 *)
    intros H. unfold Rdiv in H.
    assert (H4_pos : 0 < 4 * (INR n2 - INR n1)) by lra.
    assert (H4_nonzero : 4 * (INR n2 - INR n1) <> 0) by lra.
    assert (H5_pos : 0 < sqrt (INR c) - 1) by (apply sqrt_c_minus_1_pos; lia).
    assert (H5_nonzero : sqrt (INR c) - 1 <> 0) by lra.
    assert (H_pos : 0 < (4 * (INR n2 - INR n1)) * (sqrt (INR c) - 1))
      by (apply Rmult_lt_0_compat; lra).
    assert (H_sqrt_n1_pos : 0 < sqrt (INR n1)) by (apply sqrt_lt_R0_c; lra).
    assert (H_sqrt_n2_pos : 0 < sqrt (INR n2)) by (apply sqrt_lt_R0_c; lra).

    apply Rmult_le_compat_r with (r := (4 * (INR n2 - INR n1)) * (sqrt (INR c) - 1)) in H;
      [| lra].
    assert (H_left1 : sqrt (INR n1 * INR n2) * / (4 * (INR n2 - INR n1)) *
                      (4 * (INR n2 - INR n1) * (sqrt (INR c) - 1))
                    = sqrt (INR n1 * INR n2) * (sqrt (INR c) - 1)).
    { field; lra. }
    rewrite H_left1 in H; clear H_left1.

    assert (H_right1 : sqrt (INR n1 * / INR n2) * / (sqrt (INR c) - 1) *
                       (4 * (INR n2 - INR n1) * (sqrt (INR c) - 1))
                     = sqrt (INR n1 * / INR n2) * (4 * (INR n2 - INR n1))).
    { field; lra. }
    rewrite H_right1 in H; clear H_right1.

    apply Rmult_le_compat_r with (r := sqrt (INR n1)) in H; [| lra].
    assert (H_left2 : sqrt (INR n1 * INR n2) * (sqrt (INR c) - 1) * sqrt (INR n1)
                    = INR n1 * sqrt (INR n2) * (sqrt (INR c) - 1)).
    {
      rewrite Rmult_assoc.
      rewrite (Rmult_comm (sqrt (INR c) - 1) (sqrt (INR n1))).
      rewrite <- Rmult_assoc.
      rewrite <- sqrt_mult with (x := INR n1 * INR n2) (y := INR n1).
      - replace (INR n1 * INR n2 * INR n1) with (INR n1 * INR n1 * INR n2) by ring.
        rewrite sqrt_mult with (x := INR n1 * INR n1) (y := INR n2).
        + rewrite sqrt_square; [| lra]. ring.
        + apply Rmult_le_pos; lra.
        + lra.
      - apply Rmult_le_pos; lra.
      - lra.
    }
    rewrite H_left2 in H; clear H_left2.

    assert (H_right2 : sqrt (INR n1 * / INR n2) * (4 * (INR n2 - INR n1)) * sqrt (INR n1)
                     = (INR n1 / sqrt (INR n2)) * (4 * (INR n2 - INR n1))).
    {
      replace (sqrt (INR n1 * / INR n2) * (4 * (INR n2 - INR n1)) * sqrt (INR n1))
        with ((sqrt (INR n1 * / INR n2) * sqrt (INR n1)) * (4 * (INR n2 - INR n1))) by ring.
      rewrite <- sqrt_mult with (x := INR n1 * / INR n2) (y := INR n1).
      2: apply Rmult_le_pos; [lra | apply Rlt_le, Rinv_0_lt_compat; lra].
      2: lra.
      replace (INR n1 * / INR n2 * INR n1) with (INR n1 * INR n1 * / INR n2) by ring.
      rewrite sqrt_mult with (x := INR n1 * INR n1) (y := / INR n2).
      2: apply Rmult_le_pos; lra.
      2: apply Rlt_le, Rinv_0_lt_compat; lra.
      rewrite sqrt_square; [| lra].
      rewrite sqrt_inv with (x := INR n2). nra.
    }
    rewrite H_right2 in H; clear H_right2.

    apply Rmult_le_compat_r with (r := sqrt (INR n2)) in H; [| lra].
    assert (H_left3 : INR n1 * sqrt (INR n2) * (sqrt (INR c) - 1) * sqrt (INR n2)
                    = INR n1 * (INR n2 * (sqrt (INR c) - 1))).
    {
      replace (INR n1 * sqrt (INR n2) * (sqrt (INR c) - 1) * sqrt (INR n2))
        with (INR n1 * (sqrt (INR n2) * sqrt (INR n2)) * (sqrt (INR c) - 1)) by ring.
      rewrite <- sqrt_mult with (x := INR n2) (y := INR n2); [| lra | lra].
      rewrite sqrt_square; [| lra]. ring.
    }
    rewrite H_left3 in H; clear H_left3.

    assert (H_right3 : (INR n1 / sqrt (INR n2)) * (4 * (INR n2 - INR n1)) * sqrt (INR n2)
                     = INR n1 * (4 * (INR n2 - INR n1))).
    {
      replace ((INR n1 / sqrt (INR n2)) * (4 * (INR n2 - INR n1)) * sqrt (INR n2))
        with ((INR n1 / sqrt (INR n2) * sqrt (INR n2)) * (4 * (INR n2 - INR n1))) by ring.
      field_simplify (INR n1 / sqrt (INR n2) * sqrt (INR n2)).
      - field; lra.
      - lra.
    }
    rewrite H_right3 in H; clear H_right3.

    apply Rmult_le_reg_l with (r := INR n1) in H; [| lra].
    lra.

  - (* 反向：线性不等式 ⇒ 原不等式 *)
    intros H. unfold Rdiv.
    assert (H4_pos : 0 < 4 * (INR n2 - INR n1)) by lra.
    assert (H4_nonzero : 4 * (INR n2 - INR n1) <> 0) by lra.
    assert (H5_pos : 0 < sqrt (INR c) - 1) by (apply sqrt_c_minus_1_pos; lia).
    assert (H5_nonzero : sqrt (INR c) - 1 <> 0) by lra.
    assert (H_pos : 0 < (4 * (INR n2 - INR n1)) * (sqrt (INR c) - 1))
      by (apply Rmult_lt_0_compat; lra).
    assert (H_sqrt_n1_pos : 0 < sqrt (INR n1)) by (apply sqrt_lt_R0_c; lra).
    assert (H_sqrt_n2_pos : 0 < sqrt (INR n2)) by (apply sqrt_lt_R0_c; lra).

    apply Rmult_le_compat_l with (r := INR n1) in H; [| lra].
    apply Rmult_le_compat_r with (r := sqrt (INR n2)) in H; [| lra].

    assert (H_left3_rev : INR n1 * (INR n2 * (sqrt (INR c) - 1))
                        = INR n1 * sqrt (INR n2) * (sqrt (INR c) - 1) * sqrt (INR n2)).
    {
      rewrite <- (sqrt_square (INR n2)) at 1; [| lra].
      rewrite sqrt_mult; [| lra | lra]. ring.
    }
    rewrite H_left3_rev in H.

    assert (H_right3_rev : INR n1 * (4 * (INR n2 - INR n1))
                         = (INR n1 / sqrt (INR n2)) * (4 * (INR n2 - INR n1)) * sqrt (INR n2)).
    {
      rewrite Rmult_assoc.
      rewrite (Rmult_comm (4 * (INR n2 - INR n1)) (sqrt (INR n2))).
      rewrite <- Rmult_assoc.
      field_simplify; [| lra].
      field; lra.
    }
    rewrite H_right3_rev in H.

    apply Rmult_le_reg_r with (r := sqrt (INR n2)) in H; [| lra].

    assert (H_left2_rev : INR n1 * sqrt (INR n2) * (sqrt (INR c) - 1)
                        = sqrt (INR n1 * INR n2) * (sqrt (INR c) - 1) * sqrt (INR n1)).
    {
      symmetry.
      rewrite Rmult_assoc.
      rewrite (Rmult_comm (sqrt (INR c) - 1) (sqrt (INR n1))).
      rewrite <- Rmult_assoc.
      rewrite <- sqrt_mult with (x := INR n1 * INR n2) (y := INR n1).
      - replace (INR n1 * INR n2 * INR n1) with (INR n1 * INR n1 * INR n2) by ring.
        rewrite sqrt_mult with (x := INR n1 * INR n1) (y := INR n2).
        + rewrite sqrt_square; [| lra]. ring.
        + apply Rmult_le_pos; lra.
        + lra.
      - apply Rmult_le_pos; lra.
      - lra.
    }
    rewrite H_left2_rev in H.

    assert (H_right2_rev : (INR n1 / sqrt (INR n2)) * (4 * (INR n2 - INR n1))
                         = sqrt (INR n1 / INR n2) * (4 * (INR n2 - INR n1)) * sqrt (INR n1)).
    {
      assert (Hn1_nat_pos : (0 < n1)%nat).
      { apply Nat.neq_0_lt_0. intro H1; subst n1. simpl in Hn1_pos. lra. }
      assert (Hn2_nat_pos : (0 < n2)%nat).
      { apply Nat.neq_0_lt_0. intro H1; subst n2. simpl in Hn2_pos. lra. }
      rewrite INR_div_sqrt_eq; [| exact Hn1_nat_pos | exact Hn2_nat_pos].
      rewrite Rmult_assoc.
      rewrite (Rmult_comm (sqrt (INR n1)) (4 * (INR n2 - INR n1))).
      rewrite <- Rmult_assoc. reflexivity.
    }
    rewrite H_right2_rev in H.

    replace (sqrt (INR n1 * INR n2) * (sqrt (INR c) - 1) * sqrt (INR n1) * sqrt (INR n2))
      with ((sqrt (INR n1 * INR n2) * (sqrt (INR c) - 1) * sqrt (INR n2)) * sqrt (INR n1)) in H
      by ring.
    replace (sqrt (INR n1 / INR n2) * (4 * (INR n2 - INR n1)) * sqrt (INR n1) * sqrt (INR n2))
      with ((sqrt (INR n1 / INR n2) * (4 * (INR n2 - INR n1)) * sqrt (INR n2)) * sqrt (INR n1)) in H
      by ring.
    apply Rmult_le_reg_r with (r := sqrt (INR n1)) in H; [| lra].

    replace (sqrt (INR n1 * INR n2) * (sqrt (INR c) - 1) * sqrt (INR n2))
      with ((sqrt (INR n1 * INR n2) * (sqrt (INR c) - 1)) * sqrt (INR n2)) in H by ring.
    replace (sqrt (INR n1 / INR n2) * (4 * (INR n2 - INR n1)) * sqrt (INR n2))
      with ((sqrt (INR n1 / INR n2) * (4 * (INR n2 - INR n1))) * sqrt (INR n2)) in H by ring.
    apply Rmult_le_reg_r with (r := sqrt (INR n2)) in H; [| lra].

    assert (H_left1_rev : sqrt (INR n1 * INR n2) * (sqrt (INR c) - 1)
                        = sqrt (INR n1 * INR n2) * / (4 * (INR n2 - INR n1)) *
                          (4 * (INR n2 - INR n1) * (sqrt (INR c) - 1))).
    { field; lra. }
    rewrite H_left1_rev in H.

    assert (H_right1_rev : sqrt (INR n1 / INR n2) * (4 * (INR n2 - INR n1))
                         = sqrt (INR n1 / INR n2) * / (sqrt (INR c) - 1) *
                           (4 * (INR n2 - INR n1) * (sqrt (INR c) - 1))).
    { field; lra. }
    rewrite H_right1_rev in H.

    apply Rmult_le_reg_r with (r := (4 * (INR n2 - INR n1)) * (sqrt (INR c) - 1)) in H;
      [| lra].
    lra.
Qed.

(* 线性不等式等价变换 *)
Lemma linear_inequality_equiv :
  forall (n1 n2 c : nat) (H_n2_pos : INR n2 > 0),
    (INR n2 * (sqrt (INR c) - 1) <= 4 * (INR n2 - INR n1)) <->
    (INR n2 * (5 - sqrt (INR c)) >= 4 * INR n1).
Proof.
  intros. split.
  - intros H. apply Rle_ge. lra.
  - intros H. apply Rge_le in H. lra.
Qed.

(* 线性下界推导 *)
Lemma final_linear_bound :
  forall (c n1 n2 k : nat) (A : R),
    (c >= 2)%nat ->
    (c <= 24)%nat ->
    (5 - sqrt (INR c) > 0) ->
    (A > 0) ->
    (A * (5 - sqrt (INR c)) >= 4) ->
    ((INR c)^k >= A) ->
    (INR n2 >= (INR c)^k * INR n1) ->
    INR n2 * (5 - sqrt (INR c)) >= 4 * INR n1.
Proof.
  intros c n1 n2 k A Hc Hc24 Hden_pos HA HA_bound Hpow Hineq.
  apply Rle_ge.
  apply Rle_trans with ((INR c)^k * INR n1 * (5 - sqrt (INR c))).
  - (* 第一部分：4 * INR n1 <= (INR c)^k * INR n1 * (5 - sqrt (INR c)) *)
    assert (H_core : 4 <= (INR c)^k * (5 - sqrt (INR c))).
    {
      apply Rle_trans with (A * (5 - sqrt (INR c))).
      - apply Rge_le in HA_bound. exact HA_bound.
      - apply Rmult_le_compat_r.
        + apply Rlt_le, Hden_pos.
        + apply Rge_le in Hpow. exact Hpow.
    }
    (* 两边乘以 INR n1 *)
    assert (H_core_mult : INR n1 * 4 <= INR n1 * ((INR c)^k * (5 - sqrt (INR c)))).
    {
      apply Rmult_le_compat_l.
      - apply pos_INR.
      - exact H_core.
    }
    (* 将目标表达式通过 ring 等价替换为 H_core_mult 的形式 *)
    replace (INR c ^ k * INR n1 * (5 - sqrt (INR c)))
      with (INR n1 * ((INR c)^k * (5 - sqrt (INR c)))).
    2: { ring. }
    replace (4 * INR n1) with (INR n1 * 4).
    2: { ring. }
    exact H_core_mult.
  - (* 第二部分：(INR c)^k * INR n1 * (5 - sqrt (INR c)) <= INR n2 * (5 - sqrt (INR c)) *)
    apply Rmult_le_compat_r.
    + apply Rlt_le, Hden_pos.
    + apply Rge_le, Hineq.
Qed.

(* 定理：稀疏核心代数不等式存在性 *)
Theorem core_algebraic_inequality_sparse_gen_exist :
  forall (c : nat),
    (c >= 2)%nat -> (c <= 24)%nat ->
    exists K : nat,
    forall (n1 n2 : nat) (k : nat),
      (n1 >= 2)%nat -> (n2 >= 2)%nat -> (n1 < n2)%nat ->
      (k >= K)%nat ->
      INR n2 >= (INR c)^k * INR n1 ->
      sqrt (INR n1 * INR n2) / (4 * (INR n2 - INR n1)) <=
      sqrt (INR n1 / INR n2) / (sqrt (INR c) - 1).
Proof.
  intros c Hc Hc_le24.
  assert (H_sqrt_lt5 : sqrt (INR c) < 5). {
    apply Rlt_le_trans with (sqrt (INR 25)).
    - apply sqrt_lt_1 with (x := INR c) (y := INR 25);
        [apply pos_INR; lia | apply pos_INR; lia | apply lt_INR; lia].
    - rewrite sqrt_25_eq_5; lra.
  }
  assert (H_den_pos : 5 - sqrt (INR c) > 0) by lra.
  set (A := 4 / (5 - sqrt (INR c))).
  assert (HA : A > 0) by (unfold A; apply Rdiv_lt_0_compat; [lra | exact H_den_pos]).

  set (K := Nat.max 2 (Z.to_nat (up A))).
  assert (HK_ge2 : (K >= 2)%nat) by apply Nat.le_max_l.
  assert (HK_ge_upA : (K >= Z.to_nat (up A))%nat) by apply Nat.le_max_r.

  exists K. intros n1 n2 k Hn1 Hn2 Hlt Hk Hpow.

  assert (Hc_pow_ge_A : (INR c)^k >= A). {
    assert (H_A_le_INRk : A <= INR k). {
      assert (H_A_le_upA : A <= IZR (up A)) by (apply Rlt_le; apply (proj1 (archimed A))).
      assert (H_upA_nat_le_k : (Z.to_nat (up A) <= k)%nat)
        by (eapply Nat.le_trans; [exact HK_ge_upA | exact Hk]).
      apply Rle_trans with (INR (Z.to_nat (up A))).
      - rewrite INR_IZR_INZ.
        assert (H_upA_ge0 : (0 <= up A)%Z). {
          apply Z.lt_le_incl, lt_IZR. simpl.
          apply Rlt_trans with A; [exact HA | apply (proj1 (archimed A))].
        }
        rewrite Z2Nat.id by exact H_upA_ge0. exact H_A_le_upA.
      - apply le_INR; exact H_upA_nat_le_k.
    }
    assert (H_INRk_le_2k : INR k <= 2 ^ k) by (apply Rge_le, pow2_ge_INR).
    assert (H_2k_le_ck : 2 ^ k <= (INR c) ^ k). {
      apply pow_incr. split; [lra | change 2 with (INR 2); apply le_INR; lia].
    }
    apply Rle_ge. eapply Rle_trans; [exact H_A_le_INRk |].
    eapply Rle_trans; [exact H_INRk_le_2k | exact H_2k_le_ck].
  }

  assert (H_n1_pos : INR n1 > 0) by (apply lt_0_INR; lia).
  assert (H_n2_pos : INR n2 > 0) by (apply lt_0_INR; lia).
  assert (H_diff_pos : INR n2 - INR n1 > 0) by (apply Rgt_minus; apply lt_INR; lia).

  assert (Hc_pow_ge_4 : INR c ^ k >= 4). {
    apply Rle_ge.
    assert (Hk2 : (k >= 2)%nat) by (eapply Nat.le_trans; [exact HK_ge2 | exact Hk]).
    assert (H4_le_2k : 4 <= 2 ^ k). {
      destruct k as [|k']; [lia|]. destruct k' as [|k'']; [lia|].
      replace (2 ^ (S (S k''))) with (4 * 2 ^ k'') by (simpl; ring).
      apply Rle_trans with (4 * 1); [lra | apply Rmult_le_compat_l; [lra | apply pow2_ge_1]].
    }
    assert (H2k_le_ck : 2 ^ k <= INR c ^ k). {
      apply pow_incr; split; [lra | change 2 with (INR 2); apply le_INR; lia].
    }
    eapply Rle_trans; [exact H4_le_2k | exact H2k_le_ck].
  }

  destruct (Nat.le_gt_cases c 4) as [Hc_le4 | Hc_gt4].
  - (* c ≤ 4 *)
    assert (Hc_ge2 : (c >= 2)%nat) by lia.
    assert (H_cpow_ge_c : (INR c)^k >= INR c). {
      apply Rle_ge. rewrite <- pow_INR. apply le_INR.
      replace c with (c ^ 1)%nat at 1 by (rewrite Nat.pow_1_r; reflexivity).
      apply Nat.pow_le_mono_r; lia.
    }
    assert (Hn2_ge_cn1 : INR n2 >= INR c * INR n1). {
      apply Rle_ge. apply Rle_trans with (INR c ^ k * INR n1).
      - apply Rmult_le_compat_r; [apply pos_INR | apply Rge_le; exact H_cpow_ge_c].
      - apply Rge_le; exact Hpow.
    }
    apply core_algebraic_inequality with (c := c); auto.

  - (* c > 4 *)
    assert (Hc_gt_4_R : INR c > 4). {
      assert (Htemp : INR 4 < INR c) by (apply lt_INR; exact Hc_gt4).
      replace (INR 4) with 4 in Htemp by (unfold INR; simpl; lra).
      apply Rlt_gt; exact Htemp.
    }
    apply reduce_to_linear_inequality; auto; try lia.
    apply linear_inequality_equiv with (1 := H_n2_pos).
    apply Rle_ge.
    apply Rle_trans with (r2 := INR n2 * (5 - sqrt (INR c))).
    - apply Rle_trans with (r2 := (INR c)^k * INR n1 * (5 - sqrt (INR c))).
      + replace ((INR c)^k * INR n1 * (5 - sqrt (INR c)))
          with ((INR c)^k * (5 - sqrt (INR c)) * INR n1) by ring.
        apply Rmult_le_compat_r.
        * apply Rlt_le, H_n1_pos.
        * apply Rle_trans with (r2 := A * (5 - sqrt (INR c))).
          -- replace (A * (5 - sqrt (INR c))) with 4.
             ++ apply Rle_refl.
             ++ unfold A; field; apply Rgt_not_eq, H_den_pos.
          -- apply Rmult_le_compat_r.
             ++ apply Rlt_le, H_den_pos.
             ++ apply Rge_le, Hc_pow_ge_A.
      + replace (INR n2 * (5 - sqrt (INR c))) with ((5 - sqrt (INR c)) * INR n2) by ring.
        replace ((INR c)^k * INR n1 * (5 - sqrt (INR c)))
          with ((5 - sqrt (INR c)) * ((INR c)^k * INR n1)) by ring.
        apply Rmult_le_compat_l.
        * apply Rlt_le, H_den_pos.
        * apply Rge_le, Hpow.
    - apply Rle_refl.
Qed.

(* 定理：可配置分母系数的核心代数不等式 *)
Theorem core_algebraic_inequality_sparse_const :
  forall (n1 n2 c : nat) (M : R),
    (n1 >= 2)%nat -> (n2 >= 2)%nat -> (n1 < n2)%nat -> (c >= 2)%nat ->
    M >= INR c ->
    INR n2 >= INR c * INR c * INR n1 ->
    sqrt (INR n1 * INR n2) / (M * (INR n2 - INR n1)) <=
    sqrt (INR n1 / INR n2) / (sqrt (INR c) - 1).
Proof.
  intros n1 n2 c M Hn1 Hn2 Hlt Hc HM Hineq.

  (* 基础正性条件 *)
  assert (Hn1_pos : 0 < INR n1) by (apply lt_0_INR; lia).
  assert (Hn2_pos : 0 < INR n2) by (apply lt_0_INR; lia).
  assert (Hc_pos  : 0 < INR c)  by (apply lt_0_INR; lia).

  (* 由 c ≥ 2 得到 INR c ≥ 1 *)
  assert (Hc_ge_1 : INR c >= 1). {
    apply Rle_ge.
    apply Rle_trans with (INR 2).
    - simpl; lra.
    - apply le_INR; lia.
  }

  (* 由 n2 ≥ c² n1 推出 n2 ≥ c n1 *)
  assert (Hn2_ge_c_n1 : INR n2 >= INR c * INR n1). {
    apply Rle_ge.
    apply Rle_trans with (INR c * INR c * INR n1).
    - apply Rmult_le_compat_r.
      + apply Rlt_le. exact Hn1_pos.
      + rewrite <- (Rmult_1_r (INR c)) at 1.
        apply Rmult_le_compat_l.
        * apply Rlt_le. exact Hc_pos.
        * apply Rge_le. exact Hc_ge_1.
    - apply Rge_le. exact Hineq.
  }

  (* 调用已有的通用代数不等式 *)
  pose proof (core_algebraic_inequality_general n1 n2 c Hn1 Hn2 Hlt Hc Hn2_ge_c_n1) as Hgen.

  (* 分母缩放：利用 M ≥ INR c 得到 M·Δ ≥ INR c·Δ *)
  assert (Hdiff_pos : 0 < INR n2 - INR n1). {
    apply Rgt_minus. apply lt_INR. exact Hlt.
  }
  assert (H_denom_ge : M * (INR n2 - INR n1) >= INR c * (INR n2 - INR n1)). {
    apply Rle_ge.
    apply Rmult_le_compat_r.
    - apply Rlt_le. exact Hdiff_pos.
    - apply Rge_le. exact HM.
  }

  (* 分母更大导致分式更小 *)
  assert (H_main : sqrt (INR n1 * INR n2) / (M * (INR n2 - INR n1)) <=
                   sqrt (INR n1 * INR n2) / (INR c * (INR n2 - INR n1))). {
    unfold Rdiv.
    apply Rmult_le_compat_l.
    - apply Rlt_le. apply sqrt_lt_R0_c.
      apply Rmult_lt_0_compat; assumption.
    - apply Rinv_le_contravar.
      + apply Rmult_lt_0_compat.
        * apply Rlt_le_trans with (INR c).
          -- exact Hc_pos.
          -- apply Rge_le. nra.
        * exact Hdiff_pos.
      + nra.
  }

  (* 传递性完成证明 *)
  eapply Rle_trans. apply H_main. apply Hgen.
Qed.

(* 平方根自乘等于原数（当非负时） *)
Lemma sqrt_square_eq (x : R) (H : 0 <= x) : sqrt x * sqrt x = x.
Proof. apply sqrt_sqrt; assumption. Qed.

(* 定理：反向下界不等式（要求 c ≥ 9） *)
Theorem core_algebraic_inequality_lower :
  forall (n1 n2 c : nat),
    (n1 >= 2)%nat -> (n2 >= 2)%nat -> (n1 < n2)%nat -> (c >= 9)%nat ->
    INR n2 >= INR c * INR c * INR n1 ->
    sqrt (INR n1 / INR n2) / (sqrt (INR c) + 1) <=
    sqrt (INR n1 * INR n2) / (4 * (INR n2 - INR n1)).
Proof.
  intros n1 n2 c Hn1 Hn2 Hlt Hc Hineq.
  assert (Hn1_pos : 0 < INR n1) by (apply lt_0_INR; lia).
  assert (Hn2_pos : 0 < INR n2) by (apply lt_0_INR; lia).
  assert (Hc_pos  : 0 < INR c)  by (apply lt_0_INR; lia).
  assert (Hdiff_pos : 0 < INR n2 - INR n1)
    by (apply Rgt_minus; apply lt_INR; exact Hlt).

  assert (H_denom1_pos : 0 < sqrt (INR c) + 1)
    by (apply Rplus_lt_0_compat; [apply sqrt_lt_R0_c; exact Hc_pos | lra]).
  assert (H_denom2_pos : 0 < 4 * (INR n2 - INR n1))
    by (apply Rmult_lt_0_compat; [lra | exact Hdiff_pos]).

  cut (sqrt (INR n1 / INR n2) * (4 * (INR n2 - INR n1)) <=
       sqrt (INR n1 * INR n2) * (sqrt (INR c) + 1)).
  {
    intros Hprod.
    unfold Rdiv.
    apply (Rmult_le_reg_r (sqrt (INR c) + 1)).
    { exact H_denom1_pos. }
    rewrite Rmult_assoc, Rinv_l, Rmult_1_r; [|apply Rgt_not_eq; exact H_denom1_pos].
    apply (Rmult_le_reg_l (4 * (INR n2 - INR n1))).
    { exact H_denom2_pos. }
    rewrite Rmult_comm.
    assert (Htmp : (4 * (INR n2 - INR n1)) *
                   (sqrt (INR n1 * INR n2) * / (4 * (INR n2 - INR n1)) *
                    (sqrt (INR c) + 1)) =
                   sqrt (INR n1 * INR n2) * (sqrt (INR c) + 1)).
    { field; lra. }
    rewrite Htmp.
    exact Hprod.
  }

  rewrite sqrt_div; [| apply Rlt_le; exact Hn1_pos | exact Hn2_pos].
  rewrite sqrt_mult; [| apply Rlt_le; exact Hn1_pos | apply Rlt_le; exact Hn2_pos].

  set (a := sqrt (INR n1)).
  set (b := sqrt (INR n2)).
  assert (Ha_pos : 0 < a) by (subst a; apply sqrt_lt_R0_c; exact Hn1_pos).
  assert (Hb_pos : 0 < b) by (subst b; apply sqrt_lt_R0_c; exact Hn2_pos).
  assert (Ha_sq : a * a = INR n1) by (subst a; apply sqrt_sqrt; apply Rlt_le; exact Hn1_pos).
  assert (Hb_sq : b * b = INR n2) by (subst b; apply sqrt_sqrt; apply Rlt_le; exact Hn2_pos).

  apply (Rmult_le_reg_l b); auto.
  rewrite Rmult_assoc.
  replace (b * (a / b * (4 * (INR n2 - INR n1)))) with (a * (4 * (INR n2 - INR n1))).
  2: { field; apply Rgt_not_eq; auto. }
  rewrite <- ?Rmult_assoc.
  replace (b * a * b * (sqrt (INR c) + 1)) with (a * b * b * (sqrt (INR c) + 1)).
  2: { ring. }
  rewrite ?Rmult_assoc.

  apply (Rmult_le_reg_l a); auto.
  rewrite <- ?Rmult_assoc.
  replace (a * (a * (4 * (INR n2 - INR n1)))) with (a * a * (4 * (INR n2 - INR n1))).
  2: { ring. }
  replace (a * (a * b * b * (sqrt (INR c) + 1))) with (a * a * b * b * (sqrt (INR c) + 1)).
  2: { ring. }

  replace (a * a * b * b * (sqrt (INR c) + 1)) with (a * a * (b * b) * (sqrt (INR c) + 1)).
  2: { ring. }
  replace (a * a * 4 * (INR n2 - INR n1)) with (a * a * (4 * (INR n2 - INR n1))).
  2: { ring. }

  rewrite Ha_sq, Hb_sq.
  replace (INR n1 * INR n2 * (sqrt (INR c) + 1))
    with (INR n1 * (INR n2 * (sqrt (INR c) + 1))).
  2: { ring. }

  apply Rmult_le_compat_l with (r := INR n1).
  - apply Rlt_le; exact Hn1_pos.
  - unfold Rminus.
    rewrite Rmult_plus_distr_l.
    apply Rle_trans with (4 * INR n2).
    + lra.
    + assert (Hc_R : INR 9 <= INR c) by (apply le_INR; exact Hc).
      assert (Hsqrt_ge_3 : sqrt (INR 9) <= sqrt (INR c)).
      { apply sqrt_le_1_c.
        - apply Rlt_le; apply lt_0_INR; lia.
        - apply Rlt_le; exact Hc_pos.
        - exact Hc_R. }
      assert (Hsqrt9_eq_3 : sqrt (INR 9) = 3).
      { replace (INR 9) with (3 * 3)%R.
        - rewrite sqrt_square; [reflexivity | lra].
        - unfold INR; simpl; ring. }
      rewrite Hsqrt9_eq_3 in Hsqrt_ge_3.
      assert (Hsum_ge_4 : 4 <= sqrt (INR c) + 1) by lra.
      apply Rmult_le_compat_l with (r := INR n2) in Hsum_ge_4.
      - rewrite Rmult_comm. exact Hsum_ge_4.
      - apply Rlt_le; exact Hn2_pos.
Qed.

(* ====================================================
   引理集：复数范数不等式转化为自然数不等式
   ==================================================== *)

(* 复数模长向上取整保序且不小于二 *)
Lemma up_Cnorm_ge2 (z : Complex) :
  Cnorm z >= 2 ->
  let n := Z.to_nat (up (Cnorm z)) in
  (n >= 2)%nat /\ INR n >= Cnorm z.
Proof.
  intros Hge2.
  set (x := Cnorm z).
  set (n := Z.to_nat (up x)).
  assert (Hx_pos : 0 < x) by (apply Rlt_le_trans with 2; [lra | apply Rge_le; exact Hge2]).
  destruct (archimed x) as [H_gt H_le].
  assert (H_up_gt0 : (0 < up x)%Z).
  { apply lt_IZR. apply Rlt_trans with x; [exact Hx_pos | exact H_gt]. }
  assert (Hn_eq : INR n = IZR (up x)).
  { unfold n. rewrite INR_IZR_INZ. rewrite Z2Nat.id by (apply Z.lt_le_incl; exact H_up_gt0). reflexivity. }
  assert (Hn_ge_x : INR n >= x).
  { rewrite Hn_eq. apply Rle_ge. apply Rlt_le. exact H_gt. }
  assert (Hn_ge2 : (n >= 2)%nat).
  { apply INR_le.
    apply Rle_trans with x.          (* 使用 x 作为中间值 *)
    - apply Rge_le; exact Hge2.      (* 2 <= x *)
    - apply Rge_le; exact Hn_ge_x.   (* x <= INR n *)
  }
  split; [exact Hn_ge2 | exact Hn_ge_x].
Qed.

(* 复数范数向上取整不等式传递 *)
Lemma transfer_inequality_to_up (z1 z2 : Complex) (c : nat) :
  (c >= 2)%nat ->
  Cnorm z1 >= 2 -> Cnorm z2 >= 2 ->
  Cnorm z2 >= INR c * INR c * Cnorm z1 + INR c ^ 2 ->
  let n1 := Z.to_nat (up (Cnorm z1)) in
  let n2 := Z.to_nat (up (Cnorm z2)) in
  INR n2 >= INR c * INR c * INR n1.
Proof.
  intros Hc Hge1 Hge2 Hineq.
  set (x := Cnorm z1).
  set (y := Cnorm z2).
  set (n1 := Z.to_nat (up x)).
  set (n2 := Z.to_nat (up y)).
  assert (Hx_pos : 0 < x) by (apply Rlt_le_trans with 2; [lra | apply Rge_le; exact Hge1]).
  assert (Hy_pos : 0 < y) by (apply Rlt_le_trans with 2; [lra | apply Rge_le; exact Hge2]).
  destruct (archimed x) as [Hx_gt Hx_le].
  destruct (archimed y) as [Hy_gt Hy_le].
  assert (H_upx_gt0 : (0 < up x)%Z) by (apply lt_IZR; eapply Rlt_trans; [exact Hx_pos|exact Hx_gt]).
  assert (H_upy_gt0 : (0 < up y)%Z) by (apply lt_IZR; eapply Rlt_trans; [exact Hy_pos|exact Hy_gt]).
  assert (Hn1_eq : INR n1 = IZR (up x)).
  { unfold n1; rewrite INR_IZR_INZ, Z2Nat.id; [reflexivity|apply Z.lt_le_incl; exact H_upx_gt0]. }
  assert (Hn2_eq : INR n2 = IZR (up y)).
  { unfold n2; rewrite INR_IZR_INZ, Z2Nat.id; [reflexivity|apply Z.lt_le_incl; exact H_upy_gt0]. }
  simpl. (* 展开 let 绑定 *)
  rewrite Hn1_eq, Hn2_eq.
  (* 后续证明保持不变 *)
  set (k := INR c).
  assert (Hk_ge2 : k >= 2) by (apply Rle_ge; apply le_INR in Hc; simpl in Hc; exact Hc).
  assert (Hx_lb : x >= IZR (up x) - 1) by lra.
  assert (H1 : IZR (up y) >= k * k * x + k ^ 2).
  { apply Rge_trans with y; [apply Rle_ge; apply Rlt_le; exact Hy_gt | exact Hineq]. }
  assert (H2 : k * k * x + k ^ 2 >= k * k * (IZR (up x) - 1) + k ^ 2).
  { apply Rplus_ge_compat_r. apply Rmult_ge_compat_l; [apply Rle_ge; apply Rle_0_sqr | exact Hx_lb]. }
  assert (H3 : IZR (up y) >= k * k * (IZR (up x) - 1) + k ^ 2).
  { eapply Rge_trans; [exact H1 | exact H2]. }
  replace (k * k * (IZR (up x) - 1) + k ^ 2) with (k * k * IZR (up x) - (k * k - k ^ 2)) in H3 by ring.
  replace (k * k - k ^ 2) with 0 in H3 by (unfold Rsqr; ring).
  rewrite Rminus_0_r in H3.
  exact H3.
Qed.

(* 复数模上取整的严格递增 *)
Lemma up_strict_lt (z1 z2 : Complex) (c : nat) :
  (c >= 2)%nat ->
  Cnorm z1 >= 2 -> Cnorm z2 >= 2 -> Cnorm z1 < Cnorm z2 ->
  Cnorm z2 >= INR c * INR c * Cnorm z1 + INR c ^ 2 ->
  let n1 := Z.to_nat (up (Cnorm z1)) in
  let n2 := Z.to_nat (up (Cnorm z2)) in
  (n1 < n2)%nat.
Proof.
  intros Hc Hge1 Hge2 Hlt Hineq n1 n2.
  set (x := Cnorm z1).
  set (y := Cnorm z2).
  assert (Hx_pos : 0 < x) by (apply Rlt_le_trans with 2; [lra | apply Rge_le; exact Hge1]).
  assert (Hy_pos : 0 < y) by (apply Rlt_le_trans with 2; [lra | apply Rge_le; exact Hge2]).
  destruct (archimed x) as [Hx_gt Hx_le].
  destruct (archimed y) as [Hy_gt Hy_le].
  assert (H_upx_gt0 : (0 < up x)%Z) by (apply lt_IZR; eapply Rlt_trans; [exact Hx_pos|exact Hx_gt]).
  assert (H_upy_gt0 : (0 < up y)%Z) by (apply lt_IZR; eapply Rlt_trans; [exact Hy_pos|exact Hy_gt]).
  assert (Hn1_eq : INR n1 = IZR (up x)).
  { unfold n1; rewrite INR_IZR_INZ, Z2Nat.id; [reflexivity|apply Z.lt_le_incl; exact H_upx_gt0]. }
  assert (Hn2_eq : INR n2 = IZR (up y)).
  { unfold n2; rewrite INR_IZR_INZ, Z2Nat.id; [reflexivity|apply Z.lt_le_incl; exact H_upy_gt0]. }
  apply INR_lt. rewrite Hn1_eq, Hn2_eq.
  apply Rlt_trans with y.
  - (* 证明 IZR (up x) < y *)
    assert (Hc_ge2_R : INR c >= 2) by (apply Rle_ge; apply le_INR in Hc; simpl in Hc; exact Hc).
    assert (Hc_sq_ge4 : INR c * INR c >= 4).
    { apply Rle_ge. apply Rle_trans with (2 * 2); [simpl; lra |].
      apply Rmult_le_compat; try lra; apply Rge_le; assumption. }
    assert (Hc_sq_x_ge_4x : INR c * INR c * x >= 4 * x).
    { apply Rmult_ge_compat_r with (r := x) in Hc_sq_ge4; [exact Hc_sq_ge4 | lra]. }
    assert (Hc_sq_ge4' : INR c ^ 2 >= 4).
    { rewrite <- Rsqr_pow2. apply Rle_ge. apply Rle_trans with (2 * 2); [simpl; lra |].
      apply Rsqr_incr_1; lra. }
    assert (Hy_ge_4x4 : y >= 4 * x + 4).
    { apply Rge_trans with (INR c * INR c * x + INR c ^ 2); [exact Hineq |].
      apply Rplus_ge_compat; [exact Hc_sq_x_ge_4x | exact Hc_sq_ge4']. }
    assert (H_x1_lt_4x4 : x + 1 < 4 * x + 4) by (assert (x >= 2) by assumption; lra).
    (* 修正：将 Hx_le 转换为期望的形式 *)
    assert (H_upx_le_x1 : IZR (up x) <= x + 1) by lra.
    apply Rle_lt_trans with (x + 1); [exact H_upx_le_x1 |].
    apply Rlt_le_trans with (4 * x + 4); [exact H_x1_lt_4x4 | apply Rge_le; exact Hy_ge_4x4].
  - apply Rlt_gt; exact Hy_gt.
Qed.

(* 上取整自然数的性质 *)
Lemma up_nat_properties (z : Complex) :
  let x := Cnorm z in
  let n := Z.to_nat (up x) in
  x >= 2 ->
  (n >= 2)%nat /\
  INR n = IZR (up x) /\
  x <= INR n /\
  INR n <= x + 1.
Proof.
  intros x n Hge.
  assert (H := up_Cnorm_ge2 z Hge).
  destruct H as [Hn_ge2 Hn_ge_x].
  assert (Hx_pos : 0 < x) by (apply Rlt_le_trans with 2; [lra | apply Rge_le; exact Hge]).
  destruct (archimed x) as [Hx_gt Hx_le].
  assert (H_upx_ge0 : (0 <= up x)%Z).
  { apply Z.lt_le_incl; apply lt_IZR; eapply Rlt_trans; [exact Hx_pos|exact Hx_gt]. }
  assert (Hn_eq : INR n = IZR (up x)).
  { unfold n; rewrite INR_IZR_INZ; rewrite Z2Nat.id; auto. }
  split; [exact Hn_ge2 |].
  split; [exact Hn_eq |].
  split.
  - rewrite Hn_eq; apply Rlt_le; exact Hx_gt.
  - rewrite Hn_eq; lra.
Qed.

(* 上取整倍数严格递增 *)
Lemma up_nat_strict_lt (z1 z2 : Complex) (c : nat) :
  let x := Cnorm z1 in
  let y := Cnorm z2 in
  let n1 := Z.to_nat (up x) in
  let n2 := Z.to_nat (up y) in
  (c >= 2)%nat ->
  x >= 2 -> y >= 2 -> x < y ->
  y >= INR c * x ->
  (n1 < n2)%nat.
Proof.
  intros x y n1 n2 Hc Hge1 Hge2 Hlt Hygap.
  assert (Hx_pos : 0 < x) by (apply Rlt_le_trans with 2; [lra | apply Rge_le; exact Hge1]).
  assert (Hy_pos : 0 < y) by (apply Rlt_le_trans with 2; [lra | apply Rge_le; exact Hge2]).
  destruct (archimed x) as [Hx_gt Hx_le].
  destruct (archimed y) as [Hy_gt Hy_le].
  assert (H_upx_ge0 : (0 <= up x)%Z)
    by (apply Z.lt_le_incl; apply lt_IZR; eapply Rlt_trans; [exact Hx_pos|exact Hx_gt]).
  assert (H_upy_ge0 : (0 <= up y)%Z)
    by (apply Z.lt_le_incl; apply lt_IZR; eapply Rlt_trans; [exact Hy_pos|exact Hy_gt]).
  assert (Hn1_eq : INR n1 = IZR (up x))
    by (unfold n1; rewrite INR_IZR_INZ; rewrite Z2Nat.id; auto).
  assert (Hn2_eq : INR n2 = IZR (up y))
    by (unfold n2; rewrite INR_IZR_INZ; rewrite Z2Nat.id; auto).

  (* 关键不等式：INR c * x > x + 1 *)
  assert (H_cx_gt_x1 : INR c * x > x + 1).
  {
    assert (H1 : x + 1 < 2 * x).
    { apply Rplus_lt_reg_l with (-x); ring_simplify; lra. }
    assert (H2 : 2 * x <= INR c * x).
    { apply Rmult_le_compat_r; [lra |]; change 2 with (INR 2); apply le_INR; lia. }
    eapply Rlt_le_trans; [exact H1 | exact H2].
  }

  assert (Hy_gt_x1 : y > x + 1).
  { apply Rge_gt_trans with (INR c * x); assumption. }

  assert (H_upx_le_x1 : IZR (up x) <= x + 1) by lra.
  assert (H_upx_lt_upy : IZR (up x) < IZR (up y)).
  { apply Rle_lt_trans with (x + 1); [exact H_upx_le_x1 |].
    apply Rlt_trans with y; [exact Hy_gt_x1 | exact Hy_gt]. }

  rewrite <- Hn1_eq, <- Hn2_eq in H_upx_lt_upy.
  apply INR_lt; assumption.
Qed.

(* 倍数差下界 *)
Lemma y_minus_x_ge_1 :
  forall (x y : R) (c : nat),
    (c >= 2)%nat ->
    x >= 2 -> y >= INR c * x ->
    y - x >= 1.
Proof.
  intros x y c Hc Hx Hy.
  assert (Hc1 : 1 <= INR c - 1).
  { apply (Rplus_le_reg_l 1); ring_simplify; change 2 with (INR 2); apply le_INR; lia. }
  assert (Hx2 : 2 <= x) by (apply Rge_le; exact Hx).

  (* 证明 1 <= (INR c - 1) * x *)
  assert (H1 : 1 <= (INR c - 1) * x).
  { apply Rle_trans with (1 * 2).
    - simpl; lra.
    - apply Rmult_le_compat.
      + lra.                (* 0 <= 1 *)
      + lra.                (* 0 <= 2 *)
      + exact Hc1.          (* 1 <= INR c - 1 *)
      + exact Hx2.          (* 2 <= x *)
  }

  (* 目标形式为 y - x >= 1，等价于 1 <= y - x *)
  apply Rle_ge.
  apply Rle_trans with (INR c * x - x).
  - (* 子目标 1: 1 <= INR c * x - x *)
    replace (INR c * x - x) with ((INR c - 1) * x) by ring.
    exact H1.
  - (* 子目标 2: INR c * x - x <= y - x *)
    apply Rplus_le_compat_r; apply Rge_le; exact Hy.
Qed.

(* 区间长度二倍不等式 *)
Lemma diff_bound_2 :
  forall (x y : R) (n1 n2 : nat),
    (n1 < n2)%nat ->
    x <= INR n1 -> INR n2 <= y + 1 ->
    y - x >= 1 ->
    INR n2 - INR n1 <= 2 * (y - x).
Proof.
  intros x y n1 n2 Hlt Hx_le Hn2_le H_yx_ge1.
  assert (H_le_diff : INR n2 - INR n1 <= (y + 1) - x).
  { apply (Rplus_le_compat _ _ _ _ Hn2_le).
    apply Ropp_le_contravar; exact Hx_le. }
  replace ((y + 1) - x) with ((y - x) + 1) in H_le_diff by ring.
  apply Rle_trans with ((y - x) + 1).
  - exact H_le_diff.
  - apply Rle_trans with ((y - x) + (y - x)).
    + apply Rplus_le_compat_l; apply Rge_le; exact H_yx_ge1.
    + right; ring.
Qed.

(* 平方根乘积的上界 *)
Lemma sqrt_prod_le :
  forall (x y : R) (n1 n2 : nat),
    0 <= x -> 0 <= y ->               (* 显式添加非负性前提 *)
    x <= INR n1 -> y <= INR n2 ->
    sqrt (x * y) <= sqrt (INR n1 * INR n2).
Proof.
  intros x y n1 n2 Hx0 Hy0 Hx Hy.
  apply sqrt_le_1_c.
  - (* 0 <= x * y *)
    apply Rmult_le_pos; [exact Hx0 | exact Hy0].
  - (* 0 <= INR n1 * INR n2 *)
    apply Rmult_le_pos; apply pos_INR.
  - (* x * y <= INR n1 * INR n2 *)
    apply Rmult_le_compat; assumption.
Qed.

(* 整数部分乘积不等式 *)
Lemma core_product_inequality_floor :
  forall (x y : R) (n1 n2 c : nat),
    (c >= 2)%nat ->
    x >= 2 -> y >= 2 -> x < y ->
    y >= INR c * INR c * x + INR c ^ 2 ->
    INR n2 >= INR c * INR c * INR n1 ->
    (n1 >= 2)%nat -> (n2 >= 2)%nat -> (n1 < n2)%nat ->
    INR n1 <= x -> x <= INR n1 + 1 ->
    INR n2 <= y -> y <= INR n2 + 1 ->
    y - INR n2 <= x - INR n1 -> 
    sqrt (INR n1 * INR n2) * (y - x) <= sqrt (x * y) * (INR n2 - INR n1).
Proof.
  intros x y n1 n2 c Hc Hx2 Hy2 Hxy Hygap Hineq Hn1 Hn2 Hlt
         Hx_le Hn1_le Hy_le Hn2_le H_frac_compat.

  (* 1. 定义局部缩写 *)
  set (a := INR n1) in *.
  set (b := INR n2) in *.

  (* 2. 基础正性与序关系 *)
  assert (Ha_pos : 0 < a) by (apply lt_0_INR; lia).
  assert (Hb_pos : 0 < b) by (apply lt_0_INR; lia).
  assert (Hx_pos : 0 < x) by lra.
  assert (Hy_pos : 0 < y) by lra.
  assert (H_ab_pos : 0 < a * b) by (apply Rmult_lt_0_compat; assumption).
  assert (H_xy_pos : 0 < x * y) by (apply Rmult_lt_0_compat; assumption).
  
  assert (H_ba_pos : 0 < b - a).
  { assert (H1 : (n1 < n2)%nat) by exact Hlt.
    assert (H2 : INR n1 < INR n2) by (apply lt_INR; exact H1).
    lra. }
  assert (H_yx_pos : 0 < y - x) by lra.

  (* 3. 关键序关系：y - x <= b - a *)
  assert (H_yx_le_ba : y - x <= b - a) by lra.

  (* 4. 乘积序关系：a * b <= x * y *)
  assert (H_ab_le_xy : a * b <= x * y).
  { assert (H1 : a <= x) by exact Hx_le.
    assert (H2 : b <= y) by exact Hy_le.
    assert (H3 : 0 <= a) by lra.
    assert (H4 : 0 <= b) by lra.
    nra. }

  (* 5. 平方不等式：修复后的标准证明 *)
  assert (H_sq1 : (y - x) * (y - x) <= (b - a) * (b - a)).
  { assert (H_nonneg_yx : 0 <= y - x) by lra.
    assert (H_nonneg_ba : 0 <= b - a) by lra.
    assert (H_step1 : (y - x) * (y - x) <= (y - x) * (b - a)).
    { apply Rmult_le_compat_l; lra. }
    assert (H_step2 : (y - x) * (b - a) <= (b - a) * (b - a)).
    { apply Rmult_le_compat_r; lra. }
    lra. }

  (* 6. 核心代数不等式：非负乘法单调性两步推导 *)
  assert (H_nonneg_ab : 0 <= a * b) by (apply Rmult_le_pos; lra).
  assert (H_nonneg_xy : 0 <= x * y) by (apply Rmult_le_pos; lra).
  assert (H_nonneg_yx_sq : 0 <= (y - x) * (y - x)) by (apply Rle_0_sqr).
  assert (H_nonneg_ba_sq : 0 <= (b - a) * (b - a)) by (apply Rle_0_sqr).

  assert (H_step1 : a * b * ((y - x) * (y - x)) <= x * y * ((y - x) * (y - x))).
  { apply Rmult_le_compat_r.
    - exact H_nonneg_yx_sq.
    - exact H_ab_le_xy. }

  assert (H_step2 : x * y * ((y - x) * (y - x)) <= x * y * ((b - a) * (b - a))).
  { apply Rmult_le_compat_l.
    - exact H_nonneg_xy.
    - exact H_sq1. }

  assert (H_main_algebra : a * b * ((y - x) * (y - x)) <= x * y * ((b - a) * (b - a))).
  { apply Rle_trans with (x * y * ((y - x) * (y - x))); assumption. }

  (* 7. 平方根单调性回推 *)
  assert (H_sqrt_nonneg1 : 0 <= a * b * ((y - x) * (y - x))) by (apply Rmult_le_pos; lra).
  assert (H_sqrt_nonneg2 : 0 <= x * y * ((b - a) * (b - a))) by (apply Rmult_le_pos; lra).

  assert (H_sqrt_le : sqrt (a * b * ((y - x) * (y - x))) <= sqrt (x * y * ((b - a) * (b - a)))).
  { apply sqrt_le_1_c; assumption. }

  (* 8. 化简平方根表达式 *)
  assert (H5 : sqrt (a * b * ((y - x) * (y - x))) = sqrt (a * b) * (y - x)).
  { rewrite sqrt_mult by lra.
    rewrite sqrt_square by lra.
    ring. }

  assert (H6 : sqrt (x * y * ((b - a) * (b - a))) = sqrt (x * y) * (b - a)).
  { rewrite sqrt_mult by lra.
    rewrite sqrt_square by lra.
    ring. }

  rewrite H5, H6 in H_sqrt_le.
  exact H_sqrt_le.
Qed.

(* 根号加权不等式 *)
Lemma core1 : forall (x y1 y2 : R),
  x > 0 -> y1 > x -> y2 > y1 ->
  sqrt y1 * (y2 - x) >= sqrt y2 * (y1 - x).
Proof.
  intros x y1 y2 Hx_pos Hy1_gt_x Hy2_gt_y1.
  assert (Hy1_pos : 0 < y1) by lra.
  assert (Hy2_pos : 0 < y2) by lra.
  assert (Hdiff1 : 0 <= y2 - x) by lra.
  assert (Hdiff2 : 0 <= y1 - x) by lra.
  apply Rle_ge.
  set (L := sqrt y2 * (y1 - x)).
  set (R := sqrt y1 * (y2 - x)).
  assert (H_L_nonneg : 0 <= L) by (unfold L; apply Rmult_le_pos; [apply Rlt_le, sqrt_lt_R0_c|]; lra).
  assert (H_R_nonneg : 0 <= R) by (unfold R; apply Rmult_le_pos; [apply Rlt_le, sqrt_lt_R0_c|]; lra).

  (* 先证明平方形式的不等式 *)
  assert (H_sq : L * L <= R * R).
  { unfold L, R.
    (* 将平方展开，消去 sqrt *)
    replace (sqrt y2 * (y1 - x) * (sqrt y2 * (y1 - x)))
      with (y2 * (y1 - x) * (y1 - x)).
    2: { replace (sqrt y2 * (y1 - x) * (sqrt y2 * (y1 - x)))
           with ((y1 - x) * (y1 - x) * (sqrt y2 * sqrt y2)) by ring.
         rewrite sqrt_sqrt by lra.
         ring. }
    replace (sqrt y1 * (y2 - x) * (sqrt y1 * (y2 - x)))
      with (y1 * (y2 - x) * (y2 - x)).
    2: { replace (sqrt y1 * (y2 - x) * (sqrt y1 * (y2 - x)))
           with ((y2 - x) * (y2 - x) * (sqrt y1 * sqrt y1)) by ring.
         rewrite sqrt_sqrt by lra.
         ring. }
    (* 目标变为: y2 * (y1 - x)^2 <= y1 * (y2 - x)^2 *)
    cut (y1 * y2 >= x * x).
    - intros Hmain. nra.
    - apply Rle_ge.
      apply Rmult_le_compat; try lra.
  }
  (* 平方单调性推出原不等式 *)
  apply Rsqr_incr_0 in H_sq; auto.
Qed.

(* 平方根加权差单调递增 *)
Lemma core2 : forall (x1 x2 y : R),
  y > 0 -> x1 > 0 -> x2 > x1 -> y > x2 ->
  sqrt x2 * (y - x1) >= sqrt x1 * (y - x2).
Proof.
  intros x1 x2 y Hy_pos Hx1_pos Hx2_gt_x1 Hy_gt_x2.
  assert (Hx2_pos : 0 < x2) by lra.
  assert (H_sqrt1_nonneg : 0 <= sqrt x1) by apply sqrt_pos.
  assert (H_sqrt2_nonneg : 0 <= sqrt x2) by apply sqrt_pos.
  assert (H_sqrt1_pos : 0 < sqrt x1) by (apply sqrt_lt_R0_c; lra).
  assert (H_sqrt2_pos : 0 < sqrt x2) by (apply sqrt_lt_R0_c; lra).
  assert (H_sq1 : (sqrt x1)² = x1) by (rewrite Rsqr_sqrt; lra).
  assert (H_sq2 : (sqrt x2)² = x2) by (rewrite Rsqr_sqrt; lra).
  assert (H1 : 0 < y - x1) by lra.
  assert (H2 : 0 < y - x2) by lra.
  (* 平方后的不等式 *)
  assert (H_main : (sqrt x2 * (y - x1))² >= (sqrt x1 * (y - x2))²).
  {
    rewrite !Rsqr_mult, H_sq1, H_sq2.
    apply Rminus_ge; ring_simplify.
    replace (x2 * (y - x1)² - x1 * (y - x2)²)
      with ((x2 - x1) * (y * y - x1 * x2)).
    2: { unfold Rsqr; ring. }
    apply Rle_ge.
    apply Rmult_le_pos.
    - lra.                     (* 0 <= x2 - x1 *)
    - cut (0 <= y * y - x1 * x2).
      + intros H; lra.
      + nra.                   (* nra 直接证明 y² ≥ x1·x2 *)
  }
  (* 两边非负，准备应用平方单调性 *)
  assert (H_nonneg1 : 0 <= sqrt x2 * (y - x1))
    by (apply Rmult_le_pos; [apply Rlt_le; exact H_sqrt2_pos | lra]).
  assert (H_nonneg2 : 0 <= sqrt x1 * (y - x2))
    by (apply Rmult_le_pos; [apply Rlt_le; exact H_sqrt1_pos | lra]).
  (* 将 H_main 从 >= 转换为 <= 形式，并显式指定参数 *)
  apply Rge_le in H_main.
  apply Rsqr_incr_0 with (x := sqrt x1 * (y - x2)) (y := sqrt x2 * (y - x1)) in H_main;
    [| exact H_nonneg2 | exact H_nonneg1].
  (* 最后将结论转回 >= 形式 *)
  apply Rle_ge; exact H_main.
Qed.

(* 平方根的非负性（sqrt 保持非负性） *)
Lemma sqrt_pos_nonneg : forall x, 0 <= x -> 0 <= sqrt x.
Proof.
  intros x Hx.
  (* 分x=0和x>0两种情况 *)
  destruct (Rle_lt_or_eq_dec 0 x Hx) as [Hx_pos | Hx_eq].
  - (* 情况1：x > 0 *)
    apply Rlt_le.
    apply sqrt_lt_R0_c.  (* x>0 ⇒ sqrt x>0 *)
    exact Hx_pos.
  - (* 情况2：x = 0 *)
    (* 关键修正：利用对称性将 0 = x 转为 x = 0 *)
    rewrite <- Hx_eq. 
    (* 现在目标变为 0 <= sqrt 0 *)
    rewrite sqrt_0.    (* sqrt 0 = 0 *)
    (* 现在目标变为 0 <= 0，自动证明 *)
    apply Rle_refl.
Qed.

(* 正数的平方根为正 *)
Lemma sqrt_pos_pos : forall x, 0 < x -> 0 < sqrt x.
Proof.
  intros x Hx.
  (* 直接应用标准库引理：sqrt_lt_R0_c *)
  apply sqrt_lt_R0_c.
  exact Hx.
Qed.

(* 实数平方根乘性分配律 *)
Lemma sqrt_mult : forall x y, 0 <= x -> 0 <= y -> sqrt (x * y) = sqrt x * sqrt y.
Proof. intros x y Hx Hy. apply sqrt_mult_alt. exact Hx. Qed.

(* 平方根自乘恒等式 *)
Lemma sqrt_sqrt : forall x, 0 <= x -> sqrt x * sqrt x = x.
Proof.
  intros x Hx.
  (* 第一步：将 sqrt x * sqrt x 转化为 sqrt(x * x) *)
  rewrite <- sqrt_mult; auto.
  (* 第二步：将 (x * x) 替换为标准库的实数平方 (Rsqr x) *)
  replace (x * x) with (Rsqr x) by (unfold Rsqr; ring).
  (* 第三步：应用标准库引理 sqrt_square *)
  apply sqrt_square.
  exact Hx.
Qed.

(* 正实数乘法右消去律（严格） *)
Lemma Rmult_le_reg_r : forall r r1 r2, 0 < r -> r1 * r <= r2 * r -> r1 <= r2.
Proof.
  intros r r1 r2 H H0.
  rewrite (Rmult_comm r1 r) in H0.
  rewrite (Rmult_comm r2 r) in H0.
  apply Rmult_le_reg_l with (r := r); auto.
Qed.

(* 正实数乘法右消去律（非严格） *)
Lemma Rmult_lt_reg_r : forall r r1 r2, 0 < r -> r1 * r < r2 * r -> r1 < r2.
Proof.
  intros r r1 r2 H H0.
  rewrite (Rmult_comm r1 r) in H0.
  rewrite (Rmult_comm r2 r) in H0.
  apply Rmult_lt_reg_l with (r := r); auto.
Qed.

(* 非负实数平方的单调性 *)
Lemma Rsqr_incr_0' : forall x y : R, 0 <= x -> 0 <= y -> x <= y -> x^2 <= y^2.
Proof. intros; nra. Qed.

(* 非负实数平方单调性的逆命题 *)
Lemma Rsqr_le_abs_0 : forall x y : R, 0 <= x -> 0 <= y -> x^2 <= y^2 -> x <= y.
Proof. intros; nra. Qed.

(* 定理：实数向自然数不等式传递（带平方增长因子） *)
Theorem real_to_nat_inequality_step_general :
  forall (X Y : R) (N1 N2 C : nat),
    (C >= 2)%nat ->
    X >= 2 -> Y >= 2 -> X < Y ->
    Y >= INR C * INR C * X ->
    INR N2 <= INR C * INR C * INR N1 ->
    (N1 >= 2)%nat -> (N2 >= 2)%nat -> (N1 < N2)%nat ->
    X <= INR N1 -> INR N1 <= X + 1 ->
    Y <= INR N2 -> INR N2 <= Y + 1 ->
    sqrt (X * Y) / (INR C * INR C * (Y - X)) <=
    sqrt (INR N1 * INR N2) / (INR C * INR C * (INR N2 - INR N1)).
Proof.
  intros X Y N1 N2 C HC HX2 HY2 HXY H_Y_ge_C2X H_N2_le_C2N1
         HN1_ge2 HN2_ge2 H_N1_lt_N2 HX_le_N1 HN1_le_X1 HY_le_N2 HN2_le_Y1.

  assert (HX_pos : 0 < X) by lra.
  assert (HY_pos : 0 < Y) by lra.
  assert (HN1_pos : 0 < INR N1) by (apply lt_0_INR; lia).
  assert (HN2_pos : 0 < INR N2) by (apply lt_0_INR; lia).
  assert (H_diff_pos : 0 < Y - X) by lra.
  assert (H_diff_n_pos : 0 < INR N2 - INR N1)
    by (apply Rgt_minus; apply lt_INR; auto).
  assert (HC_pos : 0 < INR C) by (apply lt_0_INR; lia).
  assert (HC2_pos : 0 < INR C * INR C)
    by (apply Rmult_lt_0_compat; auto).
  assert (HXY_nonneg : 0 <= X * Y) by (apply Rmult_le_pos; lra).
  assert (HN1N2_nonneg : 0 <= INR N1 * INR N2) by (apply Rmult_le_pos; lra).

  apply (Rmult_le_reg_l (INR C * INR C)); [exact HC2_pos |].
  unfold Rdiv.

  assert (H_main_mult : sqrt (X * Y) * (INR N2 - INR N1) <= sqrt (INR N1 * INR N2) * (Y - X)).
  {
    assert (H_left_nonneg : 0 <= sqrt (X * Y) * (INR N2 - INR N1)).
    {
      apply Rmult_le_pos.
      - apply sqrt_positivity; assumption.
      - left; exact H_diff_n_pos.
    }
    assert (H_right_nonneg : 0 <= sqrt (INR N1 * INR N2) * (Y - X)).
    {
      apply Rmult_le_pos.
      - apply sqrt_positivity; assumption.
      - left; exact H_diff_pos.
    }

    assert (H_factor1 : INR N2 * X - INR N1 * Y <= 0).
    {
      assert (H1 : INR N2 * X <= INR C * INR C * INR N1 * X).
      { apply Rmult_le_compat_r; [lra | exact H_N2_le_C2N1]. }
      assert (H2 : INR C * INR C * INR N1 * X <= INR N1 * Y).
      {
        replace (INR C * INR C * INR N1 * X) with (INR N1 * (INR C * INR C * X)) by ring.
        apply Rmult_le_compat_l; [lra |].
        apply Rge_le; exact H_Y_ge_C2X.
      }
      lra.
    }

    assert (H_factor2 : INR N2 * Y - INR N1 * X >= 0).
    {
      apply Rle_ge.
      assert (H3 : INR N1 * Y <= INR N2 * Y).
      { apply Rmult_le_compat_r; [lra | apply le_INR; lia]. }
      assert (H4 : INR N1 * X <= INR N1 * Y).
      { apply Rmult_le_compat_l; [lra | lra]. }
      lra.
    }

    assert (H_sq_ineq : (X * Y) * (INR N2 - INR N1)^2 <= (INR N1 * INR N2) * (Y - X)^2).
    {
      assert (H_alg : (INR N1 * INR N2) * (Y - X)^2 - (X * Y) * (INR N2 - INR N1)^2 =
                      (INR N2 * Y - INR N1 * X) * (INR N1 * Y - INR N2 * X)).
      { ring. }
      cut ((INR N2 * Y - INR N1 * X) * (INR N1 * Y - INR N2 * X) >= 0).
      - intros H_prod. lra.
      - apply Rle_ge.
        apply Rmult_le_pos.
        + apply Rge_le; exact H_factor2.
        + assert (H5 : 0 <= INR N1 * Y - INR N2 * X). { lra. } exact H5.
    }

    assert (H_sqrt1 : (sqrt (X * Y))² = X * Y) by (apply Rsqr_sqrt; exact HXY_nonneg).
    assert (H_sqrt2 : (sqrt (INR N1 * INR N2))² = INR N1 * INR N2)
      by (apply Rsqr_sqrt; exact HN1N2_nonneg).
    apply Rsqr_incr_0.
    - replace ((sqrt (X * Y) * (INR N2 - INR N1))²)
        with ((sqrt (X * Y))² * (INR N2 - INR N1)²).
      2: { symmetry; apply Rsqr_mult. }
      replace ((sqrt (INR N1 * INR N2) * (Y - X))²)
        with ((sqrt (INR N1 * INR N2))² * (Y - X)²).
      2: { symmetry; apply Rsqr_mult. }
      rewrite H_sqrt1, H_sqrt2.
      rewrite !Rsqr_pow2.
      exact H_sq_ineq.
    - exact H_left_nonneg.
    - exact H_right_nonneg.
  }

  assert (H_inv_pos1 : 0 < INR C * INR C * (Y - X))
    by (repeat apply Rmult_lt_0_compat; assumption).
  assert (H_inv_pos2 : 0 < INR C * INR C * (INR N2 - INR N1))
    by (repeat apply Rmult_lt_0_compat; assumption).

  apply (Rmult_le_reg_l (INR C * INR C * (Y - X) * (INR N2 - INR N1))).
  { repeat apply Rmult_lt_0_compat; assumption. }

  assert (H_left_eq : (INR N2 - INR N1) * (INR C * INR C * (Y - X)) *
                      (INR C * INR C * (sqrt (X * Y) * / (INR C * INR C * (Y - X)))) =
                      INR C * INR C * (sqrt (X * Y) * (INR N2 - INR N1))).
  { field; repeat split; try apply Rgt_not_eq; try assumption. }

  assert (H_right_eq : (INR N2 - INR N1) * (INR C * INR C * (Y - X)) *
                       (INR C * INR C * (sqrt (INR N1 * INR N2) * / (INR C * INR C * (INR N2 - INR N1)))) =
                       INR C * INR C * (sqrt (INR N1 * INR N2) * (Y - X))).
  { field; repeat split; try apply Rgt_not_eq; try assumption. }

  assert (H_left_target_eq :
    INR C * INR C * (Y - X) * (INR N2 - INR N1) *
    (INR C * INR C * (sqrt (X * Y) * / (INR C * INR C * (Y - X)))) =
    (INR N2 - INR N1) * (INR C * INR C * (Y - X)) *
    (INR C * INR C * (sqrt (X * Y) * / (INR C * INR C * (Y - X))))).
  { ring. }
  rewrite H_left_target_eq, H_left_eq.

  assert (H_right_target_eq :
    INR C * INR C * (Y - X) * (INR N2 - INR N1) *
    (INR C * INR C * (sqrt (INR N1 * INR N2) * / (INR C * INR C * (INR N2 - INR N1)))) =
    (INR N2 - INR N1) * (INR C * INR C * (Y - X)) *
    (INR C * INR C * (sqrt (INR N1 * INR N2) * / (INR C * INR C * (INR N2 - INR N1))))).
  { ring. }
  rewrite H_right_target_eq, H_right_eq.

  apply Rmult_le_compat_l with (r := INR C * INR C) in H_main_mult;
    [| apply Rlt_le; exact HC2_pos].
  rewrite Rmult_assoc.
  rewrite Rmult_assoc.
  nra.
Qed.

(* 定理：上取整范数不等式传递 *)
Theorem up_inequality_to_original (z1 z2 : Complex) (c : nat) :
  let x := Cnorm z1 in
  let y := Cnorm z2 in
  let n1 := Z.to_nat (up x) in
  let n2 := Z.to_nat (up y) in
  (c >= 2)%nat ->
  x >= 2 -> y >= 2 -> x < y ->
  y >= INR c * x ->
  INR n2 >= INR c * INR c * INR n1 ->
  sqrt (x * y) / (INR c * (y - x)) <= sqrt (x / y) / (sqrt (INR c) - 1).
Proof.
  intros x y n1 n2 Hc Hge1 Hge2 Hlt Hygap Hineq_n.
  assert (Hx0 : 0 <= x) by lra.
  assert (Hy0 : 0 <= y) by lra.
  assert (Hy_pos : 0 < y) by lra.
  assert (Hx_pos : 0 < x) by lra.
  assert (H_pos1 : 0 < INR c * (y - x)).
  { apply Rmult_lt_0_compat.
    - apply lt_0_INR; lia.
    - apply Rgt_minus; lra. }
  assert (H_pos2 : 0 < sqrt (INR c) - 1).
  { apply Rgt_minus.
    rewrite <- sqrt_1.
    apply sqrt_lt_1.
    - apply Rle_0_1.
    - apply pos_INR; lia.
    - apply Rlt_le_trans with (INR 2).
      + simpl; lra.
      + apply le_INR; lia. }
  assert (Hc_pos : 0 < INR c) by (apply lt_0_INR; lia).
  unfold Rdiv.
  apply (Rmult_le_reg_l (INR c * (y - x))); [assumption|].
  apply (Rmult_le_reg_l (sqrt (INR c) - 1)); [assumption|].
  replace ((sqrt (INR c) - 1) * (INR c * (y - x)) * (sqrt (x * y) * / (INR c * (y - x))))
    with ((sqrt (INR c) - 1) * sqrt (x * y)).
  { replace ((sqrt (INR c) - 1) * (INR c * (y - x)) * (sqrt (x / y) * / (sqrt (INR c) - 1)))
      with (INR c * (y - x) * sqrt (x / y)).
    2: { field; apply Rgt_not_eq; assumption. }
    rewrite sqrt_mult by lra.
    replace (sqrt (x / y)) with (sqrt x / sqrt y).
    2: { symmetry; apply sqrt_div; lra. }
    apply (Rmult_le_reg_l (sqrt y)); [apply sqrt_lt_R0_c; lra|].
    replace (sqrt y * ((sqrt (INR c) - 1) * (sqrt x * sqrt y)))
      with ((sqrt (INR c) - 1) * sqrt x * y).
    { replace (sqrt y * (INR c * (y - x) * (sqrt x * / sqrt y)))
        with (INR c * (y - x) * sqrt x).
      2: { field; apply Rgt_not_eq; apply sqrt_lt_R0_c; lra. }
      apply (Rmult_le_reg_l (/ sqrt x)); [apply Rinv_0_lt_compat; apply sqrt_lt_R0_c; lra|].
      replace (/ sqrt x * ((sqrt (INR c) - 1) * sqrt x * y))
        with ((sqrt (INR c) - 1) * y).
      { replace (/ sqrt x * (INR c * (y - x) * sqrt x))
          with (INR c * (y - x)).
        2: { field; apply Rgt_not_eq; apply sqrt_lt_R0_c; lra. }
        replace (/ sqrt x *
                 (sqrt y *
                  ((sqrt (INR c) - 1) *
                   (INR c * (y - x) *
                    (sqrt (x * y) * / (INR c * (y - x)))))))
          with ((sqrt (INR c) - 1) * y).
        2: { rewrite sqrt_mult by lra.
             field_simplify.
             - replace (sqrt y ^ 2) with (sqrt y * sqrt y) by ring.
               rewrite sqrt_sqrt by lra.
               reflexivity.
             - repeat split; try apply Rgt_not_eq; try apply sqrt_lt_R0_c; lra. }
        replace (/ sqrt x *
                 (sqrt y *
                  ((sqrt (INR c) - 1) *
                   (INR c * (y - x) *
                    (sqrt (x * / y) * / (sqrt (INR c) - 1))))))
          with (INR c * (y - x)).
        2: { assert (H_inv_y_pos : 0 < / y) by (apply Rinv_0_lt_compat; lra).
             rewrite sqrt_mult by lra.
             rewrite sqrt_inv by lra.
             field_simplify.
             - field.
               repeat split;
                 try apply Rgt_not_eq;
                 try apply sqrt_lt_R0_c;
                 lra.
             - repeat split;
                 try apply Rgt_not_eq;
                 try apply sqrt_lt_R0_c;
                 lra. }
        set (sx := sqrt x).
        set (sy := sqrt y).
        set (sc := sqrt (INR c)).
        replace (sqrt x) with sx by reflexivity.
        replace (sqrt y) with sy by reflexivity.
        replace (sqrt (INR c)) with sc by reflexivity.
        field_simplify.
        - assert (H_sy2_eq : sy^2 = y).
          { rewrite <- Rsqr_pow2.
            unfold Rsqr.
            rewrite <- sqrt_sqrt; [| lra].
            reflexivity. }
          rewrite H_sy2_eq.
          replace (y * sc - y) with (y * (sc - 1)) by ring.
          apply Rle_trans with (y * (INR c - 1)).
          + apply Rmult_le_compat_l.
            * left; exact Hy_pos.
            * apply Rplus_le_reg_l with 1.
              ring_simplify.
              apply Rle_trans with (sqrt (INR c * INR c)).
              -- apply sqrt_le_1_c.
                 ++ apply pos_INR; lia.
                 ++ apply Rle_0_sqr.
                 ++ rewrite <- Rmult_1_r at 1.
                    apply Rmult_le_compat_l.
                    ** apply pos_INR; lia.
                    ** change 1 with (INR 1); apply le_INR; lia.
              -- rewrite sqrt_square; [apply Rle_refl | apply pos_INR; lia].
          + rewrite Rmult_comm.
            rewrite Rmult_minus_distr_r.
            rewrite Rmult_1_l.
            apply Rplus_le_compat_l.
            apply Ropp_le_contravar.
            apply Rge_le; exact Hygap.
        - repeat split;
            try apply Rgt_not_eq;
            try apply sqrt_lt_R0_c;
            lra. }
      replace (sqrt x * / sqrt x) with 1.
      2: { symmetry; apply Rinv_r; apply Rgt_not_eq; apply sqrt_lt_R0_c; lra. }
      field; apply Rgt_not_eq; apply sqrt_lt_R0_c; lra. }
    replace y with (sqrt y * sqrt y) by (apply sqrt_sqrt; lra).
    replace (sqrt (sqrt y * sqrt y)) with (sqrt y) by (rewrite sqrt_sqrt; lra).
    ring. }
  - assert (H_pos1' : INR c * (y - x) <> 0).
    { apply Rgt_not_eq; exact H_pos1. }
    replace ((sqrt (INR c) - 1) * (INR c * (y - x)) * (sqrt (x * y) * / (INR c * (y - x))))
      with ((sqrt (INR c) - 1) * sqrt (x * y) * ((INR c * (y - x)) * / (INR c * (y - x)))).
    + rewrite Rinv_r; [ring|exact H_pos1'].
    + ring.
Qed.

(* 定理：复数范数的核心代数不等式 *)
Theorem core_algebraic_inequality_complex :
  forall (z1 z2 : Complex) (c : nat),
    (c >= 2)%nat ->
    Cnorm z1 >= 2 -> Cnorm z2 >= 2 -> Cnorm z1 < Cnorm z2 ->
    Cnorm z2 >= INR c * INR c * Cnorm z1 + INR c ^ 2 ->
    sqrt (Cnorm z1 * Cnorm z2) / (INR c * (Cnorm z2 - Cnorm z1)) <=
    sqrt (Cnorm z1 / Cnorm z2) / (sqrt (INR c) - 1).
Proof.
  intros z1 z2 c Hc Hge1 Hge2 Hlt Hineq.
  set (x := Cnorm z1).
  set (y := Cnorm z2).
  set (n1 := Z.to_nat (up x)).
  set (n2 := Z.to_nat (up y)).

  assert (Hineq_n : INR n2 >= INR c * INR c * INR n1).
  { eapply transfer_inequality_to_up; eassumption. }

  (* 补充前提：y >= INR c * x *)
  assert (Hy_ge_cx : y >= INR c * x).
  {
    apply Rge_trans with (INR c * INR c * x).
    - (* y >= INR c * INR c * x *)
      apply Rge_trans with (INR c * INR c * x + INR c ^ 2).
      + exact Hineq.
      + apply Rle_ge.
        replace (INR c * INR c * x) with (INR c * INR c * x + 0) at 1 by ring.
        apply Rplus_le_compat_l.
        replace (INR c ^ 2) with (Rsqr (INR c)) by (unfold Rsqr; ring).
        apply Rle_0_sqr.
    - (* INR c * INR c * x >= INR c * x *)
      apply Rle_ge.
      apply Rmult_le_compat_r.
      + (* 0 <= x *) apply Rlt_le, (Rlt_le_trans _ 2 _); [lra | apply Rge_le; auto].
      + (* INR c * INR c >= INR c *)
        cut (INR c >= 1).
        * intros Hc1.
          replace (INR c) with (INR c * 1) at 2 by ring.
          replace (INR c * INR c) with (INR c * INR c) at 1 by ring.
          nra.
        * apply Rle_ge. apply Rle_trans with (INR 2); [simpl; lra | apply le_INR; lia].
  }

  (* 直接调用已证明的上取整版本不等式 *)
  apply up_inequality_to_original with (z1 := z1) (z2 := z2) (c := c); auto.
Qed.

(* 带正数缩放的通用核心代数不等式 *)
Lemma core_algebraic_inequality_vector_general :
  forall (n1 n2 c : nat) (d : nat),
    (n1 >= 2)%nat -> (n2 >= 2)%nat -> (n1 < n2)%nat ->
    (c >= 2)%nat ->
    INR n2 >= INR c * INR c * INR n1 ->
    sqrt (INR n1 * INR n2) / (INR c * (INR n2 - INR n1)) * INR d <=
    sqrt (INR n1 / INR n2) / (sqrt (INR c) - 1) * INR d.
Proof.
  intros n1 n2 c d Hn1 Hn2 Hlt Hc Hineq.
  (* 弱化条件：由 INR n2 >= c^2 * INR n1 推出 INR n2 >= c * INR n1 *)
  assert (Hweak : INR n2 >= INR c * INR n1).
  { apply Rle_ge.
    eapply Rle_trans; [ | apply Rge_le; exact Hineq ].
    apply Rmult_le_compat_r.
    - apply pos_INR.
    - replace (INR c) with (INR c * 1) at 1 by ring.
      apply Rmult_le_compat_l; [ apply pos_INR | ].
      replace 1 with (INR 1) by (simpl; ring).
      apply le_INR; lia. }
  (* 调用已证明的基础不等式 *)
  pose proof (core_algebraic_inequality_general n1 n2 c Hn1 Hn2 Hlt Hc Hweak) as H.
  (* 两边同乘正数 INR d 保序 *)
  apply Rmult_le_compat_r with (r := INR d) in H.
  - exact H.
  - apply pos_INR.
Qed.

(* 可调参数向量形式的通用核心代数不等式 *)
Lemma core_algebraic_inequality_vector_with_M :
  forall (n1 n2 c : nat) (M : R) (d : nat),
    (n1 >= 2)%nat -> (n2 >= 2)%nat -> (n1 < n2)%nat ->
    (c >= 2)%nat ->
    M >= INR c ->
    INR n2 >= INR c * INR c * INR n1 ->
    sqrt (INR n1 * INR n2) / (M * (INR n2 - INR n1)) * INR d <=
    sqrt (INR n1 / INR n2) / (sqrt (INR c) - 1) * INR d.
Proof.
  intros. apply Rmult_le_compat_r; [apply pos_INR |].
  apply core_algebraic_inequality_sparse_const with (M := M); auto.
Qed.

(* 带正数缩放的核心代数不等式（小常数优化版） *)
Lemma core_algebraic_inequality_vector :
  forall (n1 n2 c : nat) (d : nat),
    (n1 >= 2)%nat -> (n2 >= 2)%nat -> (n1 < n2)%nat -> 
    (c >= 2)%nat -> (c <= 4)%nat ->
    INR n2 >= INR c * INR n1 ->
    sqrt (INR n1 * INR n2) / (4 * (INR n2 - INR n1)) * INR d <=
    sqrt (INR n1 / INR n2) / (sqrt (INR c) - 1) * INR d.
Proof.
  intros n1 n2 c d Hn1 Hn2 Hlt Hc Hc_le4 Hineq.
  pose proof (core_algebraic_inequality n1 n2 c Hn1 Hn2 Hlt Hc Hc_le4 Hineq) as H.
  apply Rmult_le_compat_r with (r := INR d) in H.
  - exact H.
  - apply pos_INR.
Qed.

(* 正自然数的 INR 严格正 *)
Lemma INR_pos : forall n, (n > 0)%nat -> 0 < INR n.
Proof. intros; apply lt_0_INR; assumption. Qed.

(* 两正数之积的倒数通分等式 *)
Lemma inv_diff_eq : forall a b : R,
  a <> 0 -> b <> 0 -> 1 / a - 1 / b = (b - a) / (a * b).
Proof.
  intros; field; split; assumption.
Qed.

(* 正数倒数为正 *)
Lemma inv_pos : forall x, 0 < x -> 0 < 1 / x.
Proof.
  intros; unfold Rdiv; rewrite Rmult_1_l; apply Rinv_0_lt_compat; auto.
Qed.

(* 当 n1>=2 且 n1<n2 时，分子小于分母（乘积） *)
Lemma INR_diff_lt_prod : forall n1 n2 : nat,
  (n1 >= 2)%nat -> (n1 < n2)%nat -> INR n2 - INR n1 < INR n1 * INR n2.
Proof.
  intros n1 n2 Hge Hlt.
  assert (H1 : INR n1 >= 2). 
  { apply le_INR in Hge. simpl in Hge. lra. }
  assert (H2 : INR n2 > INR n1) by (apply lt_INR; exact Hlt).
  nra.
Qed.

(* 正分数小于 1 的判定条件 *)
Lemma frac_lt_one : forall a b : R, 0 < b -> a < b -> a / b < 1.
Proof.
  intros a b Hb Hab.
  apply (Rmult_lt_reg_r b); auto.
  rewrite Rmult_1_l.
  assert (Hb_neq0 : b <> 0) by (apply Rgt_not_eq; exact Hb).
  field_simplify; auto.
Qed.

(* n >= 2 时 1/n <= 1/2 *)
Lemma inv_INR_le_inv2 : forall n, (n >= 2)%nat -> 1 / INR n <= 1 / 2.
Proof.
  intros n Hge.
  unfold Rdiv; rewrite !Rmult_1_l.
  apply Rinv_le_contravar.
  - lra.
  - apply le_INR in Hge; simpl in Hge; exact Hge.
Qed.

(* 两正数乘积为正 *)
Lemma prod_pos : forall a b : R, 0 < a -> 0 < b -> 0 < a * b.
Proof.
  intros; apply Rmult_lt_0_compat; assumption.
Qed.

(* 倒数的差为正（上半部分） *)
Lemma diff_inv_INR_pos : forall n1 n2 : nat,
  (n1 < n2)%nat ->
  (n1 > 0)%nat -> (n2 > 0)%nat ->
  0 < 1 / INR n1 - 1 / INR n2.
Proof.
  intros n1 n2 Hlt Hgt1 Hgt2.
  assert (Hpos1 : 0 < INR n1) by (apply INR_pos; exact Hgt1).
  assert (Hpos2 : 0 < INR n2) by (apply INR_pos; exact Hgt2).
  assert (Hlt_INR : INR n1 < INR n2) by (apply lt_INR; exact Hlt).
  apply Rgt_minus.
  unfold Rdiv.
  rewrite !Rmult_1_l.
  apply Rinv_lt_contravar; auto.
  nra.
Qed.

(* 倒数的差的分式表示 *)
Lemma diff_inv_INR_as_frac : forall n1 n2 : nat,
  (n1 > 0)%nat -> (n2 > 0)%nat ->
  1 / INR n1 - 1 / INR n2 = (INR n2 - INR n1) / (INR n1 * INR n2).
Proof.
  intros n1 n2 Hgt1 Hgt2.
  assert (Hpos1 : 0 < INR n1) by (apply INR_pos; exact Hgt1).
  assert (Hpos2 : 0 < INR n2) by (apply INR_pos; exact Hgt2).
  assert (Hn1_neq0 : INR n1 <> 0) by (apply Rgt_not_eq; auto).
  assert (Hn2_neq0 : INR n2 <> 0) by (apply Rgt_not_eq; auto).
  apply inv_diff_eq; auto.
Qed.

(* 倒数的差小于 1（下半部分） *)
Lemma diff_inv_INR_lt_1 : forall n1 n2 : nat,
  (n1 >= 2)%nat -> (n1 < n2)%nat ->
  1 / INR n1 - 1 / INR n2 < 1.
Proof.
  intros n1 n2 Hge Hlt.
  assert (Hgt1 : (n1 > 0)%nat) by lia.
  assert (Hgt2 : (n2 > 0)%nat) by lia.
  assert (Hpos1 : 0 < INR n1) by (apply INR_pos; exact Hgt1).
  assert (Hpos2 : 0 < INR n2) by (apply INR_pos; exact Hgt2).
  
  (* 使用分式表示 *)
  rewrite (diff_inv_INR_as_frac n1 n2 Hgt1 Hgt2).
  
  (* 证明分母为正 *)
  assert (Hdenom_pos : 0 < INR n1 * INR n2).
  { apply prod_pos; assumption. }
  
  (* 证明分子小于分母 *)
  assert (Hnum_lt_denom : INR n2 - INR n1 < INR n1 * INR n2).
  { apply INR_diff_lt_prod; assumption. }
  
  (* 应用分数小于 1 的判定 *)
  apply frac_lt_one; assumption.
Qed.

(* 倒数的差介于 0 与 1 之间 *)
Lemma diff_inv_INR_between_0_1 :
  forall (n1 n2 : nat),
    (n1 >= 2)%nat -> (n2 >= 2)%nat -> (n1 < n2)%nat ->
    0 < 1 / INR n1 - 1 / INR n2 < 1.
Proof.
  intros n1 n2 Hge1 Hge2 Hlt.
  assert (Hgt1 : (n1 > 0)%nat) by lia.
  assert (Hgt2 : (n2 > 0)%nat) by lia.
  split.
  - (* 正性部分 *)
    apply diff_inv_INR_pos; assumption.
  - (* 小于 1 部分 *)
    apply diff_inv_INR_lt_1; assumption.
Qed.

(* 复指数零参数为单位元 *)
Lemma Cexp_0_eq_1 : Cexp (0 +i 0) = C1.
Proof.
  unfold Cexp; simpl.
  rewrite exp_0, cos_0, sin_0.
  apply Complex_eq; simpl; ring.
Qed.

(* 定理：内积范数上界 *)
Theorem inner_product_norm_bound :
  forall (n1 n2 : nat),
    (n1 >= 2)%nat -> (n2 >= 2)%nat -> (n1 < n2)%nat ->
    let inner_sum := Csum (fun k => psi n1 k *c Cconj (psi n2 k)) (n1 - 1) in
    Cnorm inner_sum <= sqrt (INR n1 * INR n2) / (2 * (INR n2 - INR n1)).
Proof.
  intros n1 n2 Hn1 Hn2 Hlt.
  set (inner_sum := Csum (fun k => psi n1 k *c Cconj (psi n2 k)) (n1 - 1)).
  set (θ := 2 * PI * (1 / INR n1 - 1 / INR n2)).
  set (geom_sum := Csum (fun k => Cexp (0 +i (INR k * θ))) (n1 - 1)).

  pose proof (inner_geometric_expansion n1 n2 Hn1 Hn2 (Nat.lt_le_incl _ _ Hlt)) as H_exp.
  assert (H_inner_eq : inner_sum = (Cof_real (1 / sqrt (INR n1)) *c Cof_real (1 / sqrt (INR n2))) *c geom_sum).
  {
    unfold inner_sum, geom_sum, θ.
    rewrite H_exp.
    reflexivity.
  }
  rewrite H_inner_eq. clear H_inner_eq.

  set (c1 := Cof_real (1 / sqrt (INR n1))).
  set (c2 := Cof_real (1 / sqrt (INR n2))).
  assert (Hnorm_c1 : Cnorm c1 = 1 / sqrt (INR n1)).
  {
    unfold c1, Cof_real, Cnorm, Cnorm_sq; simpl.
    unfold Rsqr. rewrite Rmult_0_l, Rplus_0_r.
    rewrite sqrt_square.
    - reflexivity.
    - apply Rlt_le.
      replace (1 / sqrt (INR n1)) with (/ sqrt (INR n1))
        by (field; apply Rgt_not_eq; apply sqrt_lt_R0_c; apply lt_0_INR; lia).
      apply Rinv_0_lt_compat; apply sqrt_lt_R0_c; apply lt_0_INR; lia.
  }
  assert (Hnorm_c2 : Cnorm c2 = 1 / sqrt (INR n2)).
  {
    unfold c2, Cof_real, Cnorm, Cnorm_sq; simpl.
    unfold Rsqr. rewrite Rmult_0_l, Rplus_0_r.
    rewrite sqrt_square.
    - reflexivity.
    - apply Rlt_le.
      replace (1 / sqrt (INR n2)) with (/ sqrt (INR n2))
        by (field; apply Rgt_not_eq; apply sqrt_lt_R0_c; apply lt_0_INR; lia).
      apply Rinv_0_lt_compat; apply sqrt_lt_R0_c; apply lt_0_INR; lia.
  }

  unfold inner_sum.
  rewrite (Cnorm_mult (c1 *c c2) geom_sum).
  rewrite (Cnorm_mult c1 c2).
  rewrite Hnorm_c1, Hnorm_c2.

  assert (H_prod : 1 / sqrt (INR n1) * (1 / sqrt (INR n2)) = 1 / sqrt (INR n1 * INR n2)).
  {
    replace (1 / sqrt (INR n1)) with (/ sqrt (INR n1))
      by (field; apply Rgt_not_eq, sqrt_lt_R0_c, lt_0_INR; lia).
    replace (1 / sqrt (INR n2)) with (/ sqrt (INR n2))
      by (field; apply Rgt_not_eq, sqrt_lt_R0_c, lt_0_INR; lia).
    rewrite <- Rinv_mult.
    rewrite <- sqrt_mult;
      [| apply Rlt_le; apply lt_0_INR; lia
       | apply Rlt_le; apply lt_0_INR; lia].
    unfold Rdiv. rewrite Rmult_1_l. reflexivity.
  }
  rewrite H_prod.

  assert (Hθ_abs : Rabs θ = 2 * PI * (INR n2 - INR n1) / (INR n1 * INR n2)).
  {
    unfold θ.
    replace (1 / INR n1) with (/ INR n1) by (unfold Rdiv; rewrite Rmult_1_l; reflexivity).
    replace (1 / INR n2) with (/ INR n2) by (unfold Rdiv; rewrite Rmult_1_l; reflexivity).
    apply theta_abs_expr; lia.
  }

  assert (H_denom_neq0 : C1 -c Cexp (0 +i θ) <> C0).
  {
    apply geometric_denom_nonzero_simple.
    intros k Hk.
    unfold θ in Hk.
    assert (Hpi_nonzero : 2 * PI <> 0).
    { apply Rgt_not_eq, Rmult_lt_0_compat; [lra | apply PI_RGT_0]. }
    apply (Rmult_eq_reg_l (2 * PI)) in Hk; [| exact Hpi_nonzero].
    assert (H_lt : 0 < 1 / INR n1 - 1 / INR n2 < 1).
    { apply diff_inv_INR_between_0_1; auto with arith. }
    rewrite Hk in H_lt.
    destruct (Z_lt_le_dec 0 k) as [Hpos|Hnpos].
    - assert (Hge1 : (k >= 1)%Z) by lia.
      apply IZR_ge in Hge1.
      apply Rge_le in Hge1.
      simpl (IZR 1) in Hge1.
      exfalso.
      apply (Rlt_irrefl (IZR k)).
      apply Rlt_le_trans with 1.
      + exact (proj2 H_lt).
      + exact Hge1.
    - assert (Hle0 : (k <= 0)%Z) by lia.
      apply IZR_le in Hle0.
      simpl (IZR 0) in Hle0.
      exfalso.
      apply (Rlt_irrefl 0).
      apply (Rlt_le_trans 0 (IZR k) 0).
      - exact (proj1 H_lt).
      - exact Hle0.
  }

  assert (Hz_neq1 : Cexp (0 +i θ) <> C1).
  {
    intros Heq.
    rewrite Heq in H_denom_neq0.
    rewrite Csub_self in H_denom_neq0.
    apply H_denom_neq0.
    reflexivity.
  }

  assert (Hnorm_exp : Cnorm (Cexp (0 +i θ)) = 1).
  {
    unfold Cexp, Cnorm, Cnorm_sq; simpl.
    rewrite exp_0, Rmult_1_l, Rmult_1_l.
    rewrite Rplus_comm.
    rewrite sin2_cos2.
    apply sqrt_1.
  }

  assert (H_exp_pow : forall k, Cexp (0 +i (INR k * θ)) = (Cexp (0 +i θ) ^ k)%C).
  {
    induction k as [|k IH].
    - simpl. rewrite Rmult_0_l. apply Cexp_0_eq_1.
    - simpl Cexp.
      change (match k with 0%nat => 1 | S _ => INR k + 1 end) with (INR (S k)).
      rewrite S_INR.
      rewrite Rmult_plus_distr_r.
      rewrite Rmult_1_l.
      replace (0 +i (INR k * θ + θ)) with ((0 +i (INR k * θ)) +c (0 +i θ)).
      2: { unfold Cadd; simpl. f_equal; ring. }
      rewrite Cexp_add.
      rewrite IH.
      simpl. rewrite Cmul_comm. reflexivity.
  }

  unfold geom_sum.
  rewrite (Csum_ext' (fun k => Cexp (0 +i (INR k * θ))) (fun k => (Cexp (0 +i θ) ^ k)%C) (n1 - 1)).
  2: { intros i _. apply H_exp_pow. }
  clear H_exp_pow.

  pose proof (geometric_sum_norm_bound (Cexp (0 +i θ)) (n1 - 1) Hz_neq1 Hnorm_exp) as H_bound.

  pose proof (theta_bound_pi n1 n2 Hn1 Hn2 (Nat.lt_le_incl _ _ Hlt)) as Hθ_le_pi'.
  assert (Hθ_eq : θ = 2 * PI * (/ INR n1 - / INR n2)).
  {
    unfold θ.
    replace (1 / INR n1) with (/ INR n1) by (unfold Rdiv; rewrite Rmult_1_l; reflexivity).
    replace (1 / INR n2) with (/ INR n2) by (unfold Rdiv; rewrite Rmult_1_l; reflexivity).
    reflexivity.
  }
  assert (Hθ_le_pi : Rabs θ <= PI).
  {
    rewrite Hθ_eq.
    exact Hθ_le_pi'.
  }

  pose proof (denom_lower_bound θ Hθ_le_pi) as H_denom_lb.

  assert (Hθ_neq0 : θ <> 0).
  {
    unfold θ.
    apply Rgt_not_eq.
    apply Rmult_gt_0_compat.
    - apply Rmult_lt_0_compat; [lra | apply PI_RGT_0].
    - apply Rgt_minus.
      replace (1 / INR n1) with (/ INR n1)
        by (field; apply Rgt_not_eq, lt_0_INR; lia).
      replace (1 / INR n2) with (/ INR n2)
        by (field; apply Rgt_not_eq, lt_0_INR; lia).
      apply Rinv_lt_contravar.
      + apply Rmult_lt_0_compat; apply lt_0_INR; lia.
      + apply lt_INR; exact Hlt.
  }
  assert (H_abs_θ_pos : 0 < Rabs θ) by (apply Rabs_pos_lt; assumption).

  assert (H_denom_pos : 0 < Cnorm (C1 -c Cexp (0 +i θ))).
  {
    apply Rlt_le_trans with (2 * Rabs θ / PI).
    - unfold Rdiv.
      replace (2 * Rabs θ * / PI) with ((2 * Rabs θ) * / PI) by ring.
      apply Rmult_lt_0_compat.
      + apply Rmult_lt_0_compat; [lra | exact H_abs_θ_pos].
      + apply Rinv_0_lt_compat, PI_RGT_0.
    - apply Rge_le, H_denom_lb.
  }

  assert (H_inv_bound : / Cnorm (C1 -c Cexp (0 +i θ)) <= PI / (2 * Rabs θ)).
  {
    replace (PI / (2 * Rabs θ)) with (/ (2 * Rabs θ / PI)).
    2: { field; split; [apply Rgt_not_eq; lra | apply Rgt_not_eq, PI_RGT_0]. }
    apply Rinv_le_contravar.
    - apply Rdiv_lt_0_compat.
      + apply Rmult_lt_0_compat; [lra | exact H_abs_θ_pos].
      + exact PI_RGT_0.
    - apply Rge_le, H_denom_lb.
  }

  apply Rle_trans with (1 / sqrt (INR n1 * INR n2) * (2 / Cnorm (C1 -c Cexp (0 +i θ)))).
  - apply Rmult_le_compat_l.
    + apply Rlt_le.
      apply Rdiv_lt_0_compat.
      * lra.
      * apply sqrt_lt_R0_c.
        apply Rmult_lt_0_compat; apply lt_0_INR; lia.
    + exact H_bound.
  - rewrite (Rmult_comm 2).
    apply Rle_trans with (1 / sqrt (INR n1 * INR n2) * (PI / Rabs θ)).
    + apply Rmult_le_compat_l.
      * apply Rlt_le.
        apply Rdiv_lt_0_compat.
        -- lra.
        -- apply sqrt_lt_R0_c.
           apply Rmult_lt_0_compat; apply lt_0_INR; lia.
      * assert (H2 : 2 * / ∥ C1 -c Cexp (0 +i θ) ∥ <= PI / Rabs θ).
        { apply Rle_trans with (2 * (PI / (2 * Rabs θ))).
          - apply Rmult_le_compat_l; [lra | exact H_inv_bound].
          - right. field; auto with real. }
        exact H2.
    + rewrite Hθ_abs.
      replace (PI / (2 * PI * (INR n2 - INR n1) / (INR n1 * INR n2)))
        with (INR n1 * INR n2 / (2 * (INR n2 - INR n1))).
      2: {
        field.
        repeat split.
        - apply Rgt_not_eq. apply lt_0_INR. lia.
        - apply Rgt_not_eq. apply lt_0_INR. lia.
        - apply Rgt_not_eq.
          apply Rgt_minus.
          apply Rlt_gt.
          apply lt_INR. exact Hlt.
        - apply Rgt_not_eq. apply PI_RGT_0.
      }
      unfold Rdiv.
      rewrite Rmult_1_l.
      set (s := sqrt (INR n1 * INR n2)).
      assert (Hs_pos : s > 0).
      { subst s; apply sqrt_lt_R0_c; apply Rmult_lt_0_compat; apply lt_0_INR; lia. }
      assert (Hs_sq : s * s = INR n1 * INR n2).
      { subst s; apply sqrt_sqrt; apply Rlt_le; apply Rmult_lt_0_compat; apply lt_0_INR; lia. }
      rewrite <- Hs_sq.
      assert (H_eq : / s * (s * s * / (2 * (INR n2 - INR n1))) =
                    s * / (2 * (INR n2 - INR n1))).
      {
        field.
        split.
        - apply Rgt_not_eq.
          apply Rgt_minus.
          apply Rlt_gt.
          apply lt_INR. exact Hlt.
        - apply Rgt_not_eq. exact Hs_pos.
      }
      rewrite H_eq.
      rewrite (Rmult_comm 2 (INR n2 - INR n1)).
      apply Rle_refl.
Qed.

(* 大数减小数非负 *)
Lemma Rminus_ge_0 : forall a b, a >= b -> a - b >= 0.
Proof. intros; lra. Qed.

(* 两实数不小于则差非负 *)

(* 不同频率复指数不等于一 *)
Lemma Cexp_diff_not_one :
  forall (n1 n2 : nat),
    (n1 >= 2)%nat -> (n2 >= 2)%nat -> (n1 < n2)%nat ->
    Cexp (0 +i (2 * PI * (1 / INR n1 - 1 / INR n2))) <> C1.
Proof.
  intros n1 n2 Hn1 Hn2 Hlt.
  set (θ := 2 * PI * (1 / INR n1 - 1 / INR n2)).
  assert (H_01 : 0 < 1 / INR n1 - 1 / INR n2 < 1)
    by (apply diff_inv_INR_between_0_1; auto).
  assert (Hθ_pos : 0 < θ). {
    apply Rmult_lt_0_compat.
    - apply Rmult_lt_0_compat; [lra | apply PI_RGT_0].
    - apply H_01.
  }
  assert (Hθ_lt_2π : θ < 2 * PI). {
    rewrite <- (Rmult_1_r (2 * PI)).
    apply Rmult_lt_compat_l.
    - apply Rmult_lt_0_compat; [lra | apply PI_RGT_0].
    - apply H_01.
  }

  (* 证明 θ 不是 2π 的整数倍 *)
  assert (H_not_periodic : forall k : Z, θ <> 2 * PI * IZR k). {
    intros k Heq.
    apply Rmult_eq_reg_l in Heq;
      [ | apply Rgt_not_eq, Rmult_lt_0_compat; [lra | apply PI_RGT_0] ].
    (* 此时 Heq : 1 / INR n1 - 1 / INR n2 = IZR k *)
    assert (H_range : 0 < IZR k < 1) by (rewrite <- Heq; exact H_01).
    destruct (Z_lt_le_dec 0 k) as [Hpos|Hnpos].
    - assert (k >= 1)%Z by lia. apply IZR_ge in H; simpl in H; lra.
    - assert (k <= 0)%Z by lia. apply IZR_le in H; simpl in H; lra.
  }

  (* 直接应用已证引理 *)
  apply geometric_denom_nonzero_simple in H_not_periodic.
  intro Heq. apply H_not_periodic. rewrite Heq. apply Csub_self.
Qed.

(* 主定理：几何级数范数稀疏上界 *)
Theorem geometric_sum_norm_bound_sparse :
  forall (θ : R) (n1 n2 c : nat),
    (n1 >= 2)%nat -> (n2 >= 2)%nat -> (c >= 2)%nat ->
    (n1 < n2)%nat ->
    θ = 2 * PI * (1 / INR n1 - 1 / INR n2) ->
    INR n2 >= INR c * INR c * INR n1 ->
    Cnorm (Csum (fun k => Cexp (0 +i (INR k * θ))) (n1 - 1)) <=
    INR c / Cnorm (C1 -c Cexp (0 +i θ)).
Proof.
  intros θ n1 n2 c Hn1 Hn2 Hc Hlt Hθ Hsparse.
  set (z := Cexp (0 +i θ)).
  
  (* z ≠ 1 *)
  assert (Hz1 : z <> C1). {
    unfold z; rewrite Hθ; apply Cexp_diff_not_one; assumption.
  }
  
  (* 范数为 1 *)
  assert (Hnorm1 : Cnorm z = 1). {
    unfold z, Cexp, Cnorm, Cnorm_sq; simpl.
    rewrite exp_0, Rmult_1_l, Rmult_1_l.
    rewrite Rplus_comm, sin2_cos2, sqrt_1; reflexivity.
  }
  
  (* 指数函数与幂函数的对应关系 *)
  assert (H_pow_eq : forall k, Cexp (0 +i (INR k * θ)) = (z ^ k)%C). {
    intros k; induction k as [|k IH].
    - simpl; rewrite Rmult_0_l; apply Cexp_0_eq_1.
    - simpl Cexp.
      change (match k with 0%nat => 1 | S _ => INR k + 1 end) with (INR (S k)).
      rewrite S_INR, Rmult_plus_distr_r, Rmult_1_l.
      replace (0 +i (INR k * θ + θ)) with ((0 +i (INR k * θ)) +c (0 +i θ))
        by (unfold Cadd; simpl; f_equal; ring).
      rewrite Cexp_add, IH.
      unfold z.
      rewrite Cmul_comm; reflexivity.
  }
  
  (* 将求和转化为幂级数形式 —— 使用 Csum_ext' 避免命名冲突 *)
  assert (Heq_sum : Csum (fun k => Cexp (0 +i (INR k * θ))) (n1 - 1) =
                    Csum (fun k => (z ^ k)%C) (n1 - 1)). {
    apply Csum_ext'.          (* 注意这里是 Csum_ext' *)
    intros i Hi.
    apply H_pow_eq.
  }
  rewrite Heq_sum.
  
  (* 应用几何级数范数上界 *)
  pose proof (geometric_sum_norm_bound z (n1 - 1) Hz1 Hnorm1) as Hbound.
  simpl in Hbound.            (* 消去 let S := ... *)
  
  (* 将常数 2 放大为 INR c *)
  assert (Hc2 : 2 <= INR c). {
    apply le_INR in Hc; simpl in Hc; exact Hc.
  }
  
  assert (Hden_neq0 : C1 -c z <> C0) by (apply C1_minus_z_nonzero; auto).
  assert (Hden_pos : 0 < Cnorm (C1 -c z)) by (apply Cnorm_pos; auto).
  
  apply Rle_trans with (2 / Cnorm (C1 -c z)).
  - exact Hbound.
  - unfold Rdiv; apply Rmult_le_compat_r.
    + apply Rlt_le, Rinv_0_lt_compat, Hden_pos.
    + exact Hc2.
Qed.

(* 代数边界归约 *)
Lemma algebraic_bound_step_final :
  forall (n1 n2 : nat),
    (n1 >= 2)%nat -> (n2 >= 2)%nat -> (n1 < n2)%nat ->
    let θ := 2 * PI * (1 / INR n1 - 1 / INR n2) in
    1 / sqrt (INR n1 * INR n2) * (2 * (PI / (2 * Rabs θ))) <=
    sqrt (INR n1 * INR n2) / (2 * (INR n2 - INR n1)).
Proof.
  intros n1 n2 Hn1 Hn2 Hlt θ.

  (* 建立基础正性条件 *)
  assert (H_diff_pos : 0 < INR n2 - INR n1)
    by (apply Rgt_minus; apply lt_INR; auto).
  assert (H_prod_pos : 0 < INR n1 * INR n2)
    by (apply Rmult_lt_0_compat; apply lt_0_INR; lia).
  assert (H_sqrt_pos : 0 < sqrt (INR n1 * INR n2))
    by (apply sqrt_lt_R0_c; exact H_prod_pos).
  assert (H_pi_pos : 0 < PI) by apply PI_RGT_0.

  (* 展开 Rabs θ 并化简 *)
  unfold θ.
  rewrite Rabs_mult.
  rewrite (Rabs_right (2 * PI)).
  2: { apply Rle_ge; apply Rmult_le_pos; [lra | apply Rlt_le; exact H_pi_pos]. }
  replace (1 / INR n1 - 1 / INR n2) with ((INR n2 - INR n1) / (INR n1 * INR n2)).
  2: { field; split; apply Rgt_not_eq; apply lt_0_INR; lia. }
  rewrite Rabs_pos_eq.
  2: { apply Rlt_le; apply Rdiv_lt_0_compat; [exact H_diff_pos | exact H_prod_pos]. }

  (* 化简内部分式 *)
  assert (H_inner_eq : PI / (2 * (2 * PI * ((INR n2 - INR n1) / (INR n1 * INR n2)))) =
                       (INR n1 * INR n2) / (4 * (INR n2 - INR n1))).
  {
    field.
    repeat split.
    - apply Rgt_not_eq; exact H_diff_pos.
    - apply Rgt_not_eq; apply lt_0_INR; lia.
    - apply Rgt_not_eq; apply lt_0_INR; lia.
    - apply Rgt_not_eq; exact H_pi_pos.
  }
  rewrite H_inner_eq.

  (* 引入平方根变量 s 并利用 s² = INR n1 * INR n2 *)
  set (s := sqrt (INR n1 * INR n2)).
  assert (Hs_sq : s * s = INR n1 * INR n2).
  { apply sqrt_sqrt; apply Rlt_le; exact H_prod_pos. }
  assert (Hs_pos : 0 < s) by (subst s; exact H_sqrt_pos).

  (* 将目标表达式改写为 s 的形式 *)
  replace (1 / s * (2 * (INR n1 * INR n2 / (4 * (INR n2 - INR n1)))))
    with (s / (2 * (INR n2 - INR n1))).
  2: {
    rewrite <- Hs_sq.
    field.
    repeat split;
      try (apply Rgt_not_eq; [exact H_diff_pos | exact Hs_pos | apply lt_0_INR; lia]).
    lra.
    lra.
  }

  (* 最终目标退化为平凡不等式 *)
  unfold s; apply Rle_refl.
Qed.

(* 定理：基于几何级数与 Jordan 不等式的内积范数界 *)
Theorem inner_product_norm_bound_general :
  forall (n1 n2 : nat),
    (n1 >= 2)%nat -> (n2 >= 2)%nat -> (n1 < n2)%nat ->
    Cnorm (Csum (fun k => psi n1 k *c Cconj (psi n2 k)) (n1 - 1)) <=
    sqrt (INR n1 * INR n2) / (2 * (INR n2 - INR n1)).
Proof.
  intros n1 n2 Hn1 Hn2 Hlt.
  set (θ := 2 * PI * (1 / INR n1 - 1 / INR n2)).

  assert (H_exp : Csum (fun k => psi n1 k *c Cconj (psi n2 k)) (n1 - 1) =
          (Cof_real (1 / sqrt (INR n1)) *c Cof_real (1 / sqrt (INR n2))) *c
          Csum (fun k => Cexp (0 +i (INR k * θ))) (n1 - 1)).
  { apply inner_geometric_expansion; auto. lia. }
  rewrite H_exp.

  rewrite Cnorm_mult, (Cnorm_mult (Cof_real (1 / sqrt (INR n1))) (Cof_real (1 / sqrt (INR n2)))).

  assert (Hnorm1 : Cnorm (Cof_real (1 / sqrt (INR n1))) = 1 / sqrt (INR n1)).
  { unfold Cof_real, Cnorm, Cnorm_sq; simpl.
    unfold Rsqr; rewrite Rmult_0_l, Rplus_0_r.
    rewrite sqrt_square.
    - reflexivity.
    - unfold Rdiv; rewrite Rmult_1_l.
      apply Rlt_le, Rinv_0_lt_compat, sqrt_lt_R0_c, lt_0_INR; lia. }

  assert (Hnorm2 : Cnorm (Cof_real (1 / sqrt (INR n2))) = 1 / sqrt (INR n2)).
  { unfold Cof_real, Cnorm, Cnorm_sq; simpl.
    unfold Rsqr; rewrite Rmult_0_l, Rplus_0_r.
    rewrite sqrt_square.
    - reflexivity.
    - unfold Rdiv; rewrite Rmult_1_l.
      apply Rlt_le, Rinv_0_lt_compat, sqrt_lt_R0_c, lt_0_INR; lia. }

  rewrite Hnorm1, Hnorm2.
  
  assert (H_prod : 1 / sqrt (INR n1) * (1 / sqrt (INR n2)) = 1 / sqrt (INR n1 * INR n2)).
  { unfold Rdiv at 1 2; rewrite !Rmult_1_l.
    rewrite <- Rinv_mult.
    - rewrite <- sqrt_mult.
      + unfold Rdiv; rewrite Rmult_1_l; reflexivity.
      + apply Rlt_le; apply lt_0_INR; lia.
      + apply Rlt_le; apply lt_0_INR; lia.
   }
  rewrite H_prod.

  assert (Hz_neq1 : Cexp (0 +i θ) <> C1).
  { apply Cexp_diff_not_one; assumption. }

  assert (Hnorm_exp : Cnorm (Cexp (0 +i θ)) = 1).
  { unfold Cexp, Cnorm, Cnorm_sq; simpl.
    rewrite exp_0.
    rewrite !Rmult_1_l.
    rewrite Rplus_comm.
    rewrite sin2_cos2.
    apply sqrt_1. }

  assert (H_pow_eq : forall k, Cexp (0 +i (INR k * θ)) = (Cexp (0 +i θ) ^ k)%C).
  { intros k; induction k as [|k IH].
    - simpl. rewrite Rmult_0_l. apply Cexp_0_eq_1.
    - simpl Cexp.
      change (match k with 0%nat => 1 | S _ => INR k + 1 end) with (INR (S k)).
      rewrite S_INR.
      rewrite Rmult_plus_distr_r.
      rewrite Rmult_1_l.
      replace (0 +i (INR k * θ + θ)) with ((0 +i (INR k * θ)) +c (0 +i θ)).
      2: { unfold Cadd; simpl. f_equal; ring. }
      rewrite Cexp_add.
      rewrite IH.
      simpl. rewrite Cmul_comm. reflexivity. }

  rewrite (Csum_ext' _ (fun k => (Cexp (0 +i θ) ^ k)%C) (n1 - 1)).
  2: { intros; apply H_pow_eq. }

  pose proof (geometric_sum_norm_bound (Cexp (0 +i θ)) (n1 - 1) Hz_neq1 Hnorm_exp) as H_geom_bound_raw.
  simpl in H_geom_bound_raw.

  assert (Hθ_bound : Rabs θ <= PI).
  { unfold θ. unfold Rdiv. rewrite !Rmult_1_l. apply theta_bound_pi; auto. lia. }
  assert (Hθ_neq0 : θ <> 0).
  { unfold θ. apply Rgt_not_eq.
    apply Rmult_gt_0_compat.
    - apply Rmult_lt_0_compat; [lra | apply PI_RGT_0].
    - unfold Rdiv; rewrite !Rmult_1_l.
      apply Rgt_minus.
      apply Rinv_lt_contravar with (r1 := INR n1) (r2 := INR n2).
      + apply Rmult_lt_0_compat; apply lt_0_INR; lia.
      + apply lt_INR; exact Hlt. }
  assert (H_abs_θ_pos : 0 < Rabs θ) by (apply Rabs_pos_lt; exact Hθ_neq0).

  assert (H_inv_denom : / Cnorm (C1 -c Cexp (0 +i θ)) <= PI / (2 * Rabs θ)).
  {
    replace (PI / (2 * Rabs θ)) with (/ (2 * Rabs θ / PI)).
    2: { field; split; [apply Rgt_not_eq; lra | apply Rgt_not_eq, PI_RGT_0]. }
    apply Rinv_le_contravar.
    - apply Rdiv_lt_0_compat.
      + apply Rmult_lt_0_compat; [lra | exact H_abs_θ_pos].
      + apply PI_RGT_0.
    - apply Rge_le.
      apply denom_lower_bound; assumption.
  }

  assert (H_scale_pos : 0 < 1 / sqrt (INR n1 * INR n2)).
  { apply Rdiv_lt_0_compat.
    - lra.
    - apply sqrt_lt_R0_c; apply Rmult_lt_0_compat; apply lt_0_INR; lia. }
  assert (H_scale_nonneg : 0 <= 1 / sqrt (INR n1 * INR n2))
    by (apply Rlt_le; exact H_scale_pos).

  apply Rmult_le_compat_l with (r := 1 / sqrt (INR n1 * INR n2)) in H_geom_bound_raw;
    [| exact H_scale_nonneg].

  assert (H_right_bound : 
    1 / sqrt (INR n1 * INR n2) * (2 / Cnorm (C1 -c Cexp (0 +i θ))) <=
    1 / sqrt (INR n1 * INR n2) * (2 * (PI / (2 * Rabs θ)))).
  {
    apply Rmult_le_compat_l.
    - exact H_scale_nonneg.
    - replace (2 / Cnorm (C1 -c Cexp (0 +i θ))) 
        with (2 * (/ Cnorm (C1 -c Cexp (0 +i θ)))) 
        by (unfold Rdiv; reflexivity).
      replace (2 * (PI / (2 * Rabs θ))) 
        with (2 * (PI * / (2 * Rabs θ))) 
        by (unfold Rdiv; reflexivity).
      apply Rmult_le_compat_l; [lra |].
      replace (/ (2 * Rabs θ) * PI) with (PI * / (2 * Rabs θ)) by ring.
      exact H_inv_denom.
  }

  apply Rle_trans with (1 / sqrt (INR n1 * INR n2) * (2 / Cnorm (C1 -c Cexp (0 +i θ)))).
  - exact H_geom_bound_raw.
  - apply Rle_trans with (1 / sqrt (INR n1 * INR n2) * (2 * (PI / (2 * Rabs θ)))).
    + exact H_right_bound.
    + apply algebraic_bound_step_final; auto.
Qed.

(* 定理：内积范数广义上界 *)
Theorem inner_product_norm_bound_general_corrected :
  forall (n1 n2 c : nat),
    (n1 >= 2)%nat -> (n2 >= 2)%nat -> (n1 < n2)%nat ->
    (c >= 2)%nat ->
    INR n2 >= INR c * INR c * INR n1 ->
    Cnorm (Csum (fun k => psi n1 k *c Cconj (psi n2 k)) (n1 - 1)) <=
    INR c * sqrt (INR n1 * INR n2) / (4 * (INR n2 - INR n1)).
Proof.
  intros n1 n2 c Hn1 Hn2 Hlt Hc Hsparse.
  set (θ := 2 * PI * (1 / INR n1 - 1 / INR n2)).

  (* 1. 内积展开 *)
  assert (H_exp : Csum (fun k => psi n1 k *c Cconj (psi n2 k)) (n1 - 1) =
          (Cof_real (1 / sqrt (INR n1)) *c Cof_real (1 / sqrt (INR n2))) *c
          Csum (fun k => Cexp (0 +i (INR k * θ))) (n1 - 1)).
  { apply inner_geometric_expansion; auto. lia. }
  rewrite H_exp.

  (* 2. 范数乘法与常数提取 *)
  rewrite Cnorm_mult, (Cnorm_mult (Cof_real (1 / sqrt (INR n1))) (Cof_real (1 / sqrt (INR n2)))).

  assert (Hnorm1 : Cnorm (Cof_real (1 / sqrt (INR n1))) = 1 / sqrt (INR n1)).
  { unfold Cof_real, Cnorm, Cnorm_sq; simpl.
    unfold Rsqr; rewrite Rmult_0_l, Rplus_0_r.
    rewrite sqrt_square.
    - reflexivity.
    - unfold Rdiv; rewrite Rmult_1_l.
      apply Rlt_le, Rinv_0_lt_compat, sqrt_lt_R0_c, lt_0_INR; lia. }
  assert (Hnorm2 : Cnorm (Cof_real (1 / sqrt (INR n2))) = 1 / sqrt (INR n2)).
  { unfold Cof_real, Cnorm, Cnorm_sq; simpl.
    unfold Rsqr; rewrite Rmult_0_l, Rplus_0_r.
    rewrite sqrt_square.
    - reflexivity.
    - unfold Rdiv; rewrite Rmult_1_l.
      apply Rlt_le, Rinv_0_lt_compat, sqrt_lt_R0_c, lt_0_INR; lia. }
  rewrite Hnorm1, Hnorm2.

  assert (H_prod : 1 / sqrt (INR n1) * (1 / sqrt (INR n2)) = 1 / sqrt (INR n1 * INR n2)).
  { unfold Rdiv at 1 2; rewrite !Rmult_1_l.
    rewrite <- Rinv_mult.
    rewrite <- sqrt_mult.
    - unfold Rdiv; rewrite Rmult_1_l; reflexivity.
    - apply Rlt_le; apply lt_0_INR; lia.
    - apply Rlt_le; apply lt_0_INR; lia. }
  rewrite H_prod.

  (* 3. 几何级数非退化 *)
  assert (Hz_neq1 : Cexp (0 +i θ) <> C1)
    by (apply Cexp_diff_not_one; assumption).
  assert (Hnorm_exp : Cnorm (Cexp (0 +i θ)) = 1).
  { unfold Cexp, Cnorm, Cnorm_sq; simpl.
    rewrite exp_0, !Rmult_1_l, Rplus_comm, sin2_cos2; apply sqrt_1. }

  (* 4. 稀疏几何级数范数上界 *)
  assert (Hθ_eq : θ = 2 * PI * (1 / INR n1 - 1 / INR n2)) by reflexivity.
  pose proof (geometric_sum_norm_bound_sparse θ n1 n2 c Hn1 Hn2 Hc Hlt Hθ_eq Hsparse) as H_geom_sparse.
  simpl in H_geom_sparse.

  (* 5. 分母下界 (Jordan 不等式) *)
  assert (Hθ_bound : Rabs θ <= PI).
  { unfold θ, Rdiv; rewrite !Rmult_1_l; apply theta_bound_pi; auto. lia. }
  assert (Hθ_neq0 : θ <> 0).
  { unfold θ; apply Rgt_not_eq.
    apply Rmult_gt_0_compat.
    - apply Rmult_lt_0_compat; [lra | apply PI_RGT_0].
    - unfold Rdiv; rewrite !Rmult_1_l; apply Rgt_minus.
      apply Rinv_lt_contravar; [apply Rmult_lt_0_compat; apply lt_0_INR; lia | apply lt_INR; auto]. }
  assert (H_abs_θ_pos : 0 < Rabs θ) by (apply Rabs_pos_lt; exact Hθ_neq0).

  assert (H_inv_denom : / Cnorm (C1 -c Cexp (0 +i θ)) <= PI / (2 * Rabs θ)).
  { replace (PI / (2 * Rabs θ)) with (/ (2 * Rabs θ / PI)).
    - apply Rinv_le_contravar.
      + apply Rdiv_lt_0_compat; [apply Rmult_lt_0_compat; lra | apply PI_RGT_0].
      + apply Rge_le; apply denom_lower_bound; assumption.
    - field; split; [apply Rgt_not_eq; lra | apply Rgt_not_eq, PI_RGT_0]. }

  (* 6. 组合上界 *)
  assert (H_scale_nonneg : 0 <= 1 / sqrt (INR n1 * INR n2)).
  { apply Rlt_le; apply Rdiv_lt_0_compat; [lra | apply sqrt_lt_R0_c; apply Rmult_lt_0_compat; apply lt_0_INR; lia]. }

  apply Rmult_le_compat_l with (r := 1 / sqrt (INR n1 * INR n2)) in H_geom_sparse;
    [| exact H_scale_nonneg].

  assert (H_right_bound : 
    1 / sqrt (INR n1 * INR n2) * (INR c / Cnorm (C1 -c Cexp (0 +i θ))) <=
    1 / sqrt (INR n1 * INR n2) * (INR c * (PI / (2 * Rabs θ)))).
  { apply Rmult_le_compat_l; [exact H_scale_nonneg |].
    unfold Rdiv.
    replace (INR c / Cnorm (C1 -c Cexp (0 +i θ))) 
      with (INR c * / Cnorm (C1 -c Cexp (0 +i θ))) by reflexivity.
    replace (INR c * (PI / (2 * Rabs θ))) 
      with (INR c * (PI * / (2 * Rabs θ))) by reflexivity.
    apply Rmult_le_compat_l.
    - apply Rlt_le, lt_0_INR; lia.
    - exact H_inv_denom.
  }

  apply Rle_trans with (1 / sqrt (INR n1 * INR n2) * (INR c * (PI / (2 * Rabs θ)))).
  - eapply Rle_trans; [exact H_geom_sparse | exact H_right_bound].
  - (* 7. 代数化简 *)
    set (a := INR n1); set (b := INR n2).
    assert (Ha : 0 < a) by (apply lt_0_INR; lia).
    assert (Hb : 0 < b) by (apply lt_0_INR; lia).
    assert (Hdiff : 0 < b - a) by (apply Rgt_minus; apply lt_INR; auto).

    replace (INR n1) with a by reflexivity.
    replace (INR n2) with b by reflexivity.
    unfold θ.
    replace (INR n1) with a by reflexivity.
    replace (INR n2) with b by reflexivity.

    replace (Rabs (2 * PI * (1 / a - 1 / b)))
      with (2 * PI * ((b - a) / (a * b))).
    2: { replace (2 * PI * (1 / a - 1 / b)) with (2 * PI * ((b - a) / (a * b))).
         2: { field; split; apply Rgt_not_eq; assumption. }
         rewrite Rabs_pos_eq.
         - reflexivity.
         - apply Rmult_le_pos; [lra | ].
           apply Rlt_le.
           apply Rdiv_lt_0_compat; [exact Hdiff | apply Rmult_lt_0_compat; assumption]. }

    set (s := sqrt (a * b)).
    assert (Hs : s * s = a * b).
    { subst s; apply sqrt_sqrt; apply Rlt_le; apply Rmult_lt_0_compat; assumption. }
    assert (Hs_pos : 0 < s).
    { subst s; apply sqrt_lt_R0_c; apply Rmult_lt_0_compat; assumption. }

    rewrite <- Hs.
    change (s²) with (s * s) in *.
    
    replace (1 / s * (INR c * (PI / (2 * (2 * PI * ((b - a) / (s * s)))))))
      with (INR c * s / (4 * (b - a))).
    - apply Rle_refl.
    - symmetry.
      field; try lra.
Qed.

(* 稀疏序列 (类) *)
Class SparseSequence (f : nat -> nat) (c : nat) := {
  c_ge_2 : (c >= 2)%nat;
  seq_ge_2 : forall i, (f i >= 2)%nat;
  growth_condition : forall i, (INR (f (S i)) >= INR c * INR c * INR (f i))%R
}.

(* 稀疏序列单步严格递增性 *)
Lemma SparseSequence_strict_inc_step (c : nat) {f : nat -> nat} `{SparseSequence f c} :
  forall k : nat, (f k < f (S k))%nat.
Proof.
  destruct H as [Hc_ge2 Hseq_ge2 Hgrowth].
  intros k.
  apply INR_lt.
  pose proof (Hseq_ge2 k) as Hk.
  (* 使用 INR (f k) < INR c² * INR (f k) ≤ INR (f (S k)) *)
  apply Rlt_le_trans with (INR c * INR c * INR (f k)).
  - (* INR (f k) < INR c * INR c * INR (f k) *)
    rewrite <- (Rmult_1_l (INR (f k))) at 1.
    apply Rmult_lt_compat_r.
    + apply lt_0_INR; lia.               (* 0 < INR (f k) *)
    + (* 1 < INR c * INR c *)
      apply Rlt_le_trans with 4; [lra |].
      assert (Hc_ge2_R : 2 <= INR c). {
        apply le_INR in Hc_ge2. simpl in Hc_ge2. lra.
      }
      replace 4 with (2 * 2) by ring.
      apply Rmult_le_compat; lra.
  - apply Rge_le, Hgrowth.               (* INR c² * INR (f k) ≤ INR (f (S k)) *)
Qed.

(* 稀疏序列严格递增性 *)
Lemma SparseSequence_strict_inc (c : nat) {f : nat -> nat} `{SparseSequence f c} :
  forall p q : nat, (p < q)%nat -> (f p < f q)%nat.
Proof.
  intros p q Hlt.
  destruct H as [Hc_ge2 Hseq_ge2 Hgrowth].
  induction Hlt as [| m Hlt IH].
  - (* base: q = S p *)
    apply INR_lt.
    apply Rlt_le_trans with (INR c * INR c * INR (f p)).
    + (* 证明 INR (f p) < INR c² * INR (f p) *)
      rewrite <- (Rmult_1_l (INR (f p))) at 1.
      apply Rmult_lt_compat_r.
      * apply lt_0_INR. specialize (Hseq_ge2 p). lia.
      * (* 证明 1 < INR c² *)
        apply Rlt_le_trans with 4; [lra |].
        assert (Hc_ge2_R : 2 <= INR c). {
          apply le_INR in Hc_ge2. simpl in Hc_ge2. lra.
        }
        replace 4 with (2 * 2) by ring.
        apply Rmult_le_compat; lra.
    + apply Rge_le, Hgrowth.
  - (* inductive step: p < S m *)
    apply Nat.lt_trans with (f m).
    + apply IH.
    + apply INR_lt.
      apply Rlt_le_trans with (INR c * INR c * INR (f m)).
      * rewrite <- (Rmult_1_l (INR (f m))) at 1.
        apply Rmult_lt_compat_r.
        -- apply lt_0_INR. specialize (Hseq_ge2 m). lia.
        -- apply Rlt_le_trans with 4; [lra |].
           assert (Hc_ge2_R : 2 <= INR c). {
             apply le_INR in Hc_ge2. simpl in Hc_ge2. lra.
           }
           replace 4 with (2 * 2) by ring.
           apply Rmult_le_compat; lra.
      * apply Rge_le, Hgrowth.
Qed.

(* 定理：稀疏内积范数不等式 *)
Theorem sparse_inner_bound (c : nat) {f : nat -> nat} `{SparseSequence f c}
      (i j : nat) (i_lt_j : (i < j)%nat) (d : nat) :
  let n1 := f i in
  let n2 := f j in
  (sqrt (INR n1 * INR n2) / (INR c * (INR n2 - INR n1)) * INR d <=
   sqrt (INR n1 / INR n2) / (sqrt (INR c) - 1) * INR d)%R.
Proof.
  pose proof (SparseSequence_strict_inc c) as Hstrict_inc.
  destruct H as [Hc_ge2 Hseq_ge2 Hgrowth].
  intros n1 n2.
  assert (n1_lt_n2 : (n1 < n2)%nat) by (apply Hstrict_inc; auto).
  assert (Hn1_ge2 : (n1 >= 2)%nat) by apply Hseq_ge2.
  assert (Hn2_ge2 : (n2 >= 2)%nat) by apply Hseq_ge2.

  assert (Hineq : INR n2 >= INR c * INR c * INR n1).
  {
    induction i_lt_j as [| m Hlt IH].
    - exact (Hgrowth i).
    - destruct (Nat.eq_dec i m) as [-> | Hne].
      + exact (Hgrowth m).
      + assert (i_lt_m : (i < m)%nat).
        { apply Nat.lt_le_trans with (S i); [apply Nat.lt_succ_diag_r | exact Hlt]. }
        assert (Hfm_ge_fi : INR (f m) >= INR (f i)).
        { apply Rle_ge. apply le_INR. apply Nat.lt_le_incl. now apply Hstrict_inc. }
        (* 转换为 <= 形式用于乘法单调性 *)
        assert (Hfi_le_fm : INR (f i) <= INR (f m)) by (apply Rge_le; exact Hfm_ge_fi).
        apply Rge_trans with (INR c * INR c * INR (f m)).
        * apply Hgrowth.
        * apply Rle_ge.
          apply Rmult_le_compat_l.
          -- apply Rmult_le_pos; apply pos_INR; lia.
          -- exact Hfi_le_fm.
  }

  apply core_algebraic_inequality_vector_general with (c := c); auto.
Qed.

(* 平方增长蕴含线性增长 *)
Lemma square_implies_linear : forall (c n1 n2 : nat),
  (c >= 2)%nat ->
  INR n2 >= INR c * INR c * INR n1 ->
  INR n2 >= INR c * INR n1.
Proof.
  intros c n1 n2 Hc Hsq.
  apply Rge_le in Hsq.
  apply Rle_ge.
  eapply Rle_trans; [| apply Hsq].
  apply Rmult_le_compat_r.
  - apply pos_INR.
  - replace (INR c) with (INR c * 1) at 1 by ring.
    apply Rmult_le_compat_l.
    + apply pos_INR.
    + change 1 with (INR 1). apply le_INR; lia.
Qed.

(* 自适应增长因子的核心代数不等式 *)
Lemma core_algebraic_inequality_growing_c_corrected :
  forall (f : nat -> nat) (n1 n2 : nat),
    (n1 >= 2)%nat -> (n2 >= 2)%nat -> (n1 < n2)%nat ->
    (f n1 >= 2)%nat ->
    INR n2 >= INR (f n1) * INR (f n1) * INR n1 ->
    sqrt (INR n1 * INR n2) / (INR (f n1) * (INR n2 - INR n1)) <=
    sqrt (INR n1 / INR n2) / (sqrt (INR (f n1)) - 1).
Proof.
  intros f n1 n2 Hn1 Hn2 Hlt Hf_ge2 Hsq.
  assert (Hlinear : INR n2 >= INR (f n1) * INR n1).
  { apply square_implies_linear with (c := f n1); assumption. }
  apply core_algebraic_inequality_general with (c := f n1); assumption.
Qed.

(* 平方增长蕴含索引严格递增 *)
Lemma square_growth_implies_lt :
  forall (n1 n2 : nat) (f : nat -> nat),
    (n1 >= 2)%nat ->
    (f n1 >= 2)%nat ->
    INR n2 >= INR (f n1) * INR (f n1) * INR n1 ->
    (n1 < n2)%nat.
Proof.
intros n1 n2 f Hn1_ge2 Hf_ge2 Hsq.
assert (Hn1_pos : 0 < INR n1) by (apply lt_0_INR; lia).
apply INR_lt.
apply Rlt_le_trans with (INR (f n1) * INR (f n1) * INR n1).
- replace (INR n1) with (1 * INR n1) at 1 by ring.
  apply Rmult_lt_compat_r; [exact Hn1_pos |].
  replace 1 with (INR 1) by (simpl; ring).
  apply Rlt_le_trans with (INR 2 * INR 2).
  + simpl; lra.
  + assert (Hf_ge2_R : INR 2 <= INR (f n1)) by (apply le_INR; lia).
    apply Rle_trans with (INR (f n1) * INR 2).
    * apply Rmult_le_compat_r; [apply pos_INR; lia | exact Hf_ge2_R].
    * apply Rmult_le_compat_l; [apply pos_INR; lia | exact Hf_ge2_R].
- apply Rge_le; exact Hsq.
Qed.

(* 无界序列超越实数阈值 *)
Lemma unbounded_exists_ge_up :
  forall (f : nat -> nat) (threshold : R),
    (forall M : nat, exists N : nat, forall n : nat, (n >= N)%nat -> (f n >= M)%nat) ->
    exists N : nat, forall n : nat, (n >= N)%nat -> INR (f n) >= threshold.
Proof.
intros f threshold Hunbounded.
destruct (Rlt_dec threshold 0) as [Hneg | Hnneg].
- exists 0%nat.
  intros n _.
  apply Rle_ge.
  apply Rle_trans with 0; [lra | apply pos_INR].
- pose (M := Z.to_nat (up threshold)).
  destruct (Hunbounded M) as [N HN].
  exists N.
  intros n Hn.
  specialize (HN n Hn).
  assert (Hup : INR M >= threshold).
  {
    destruct (archimed threshold) as [H_gt H_le].
    unfold M.
    rewrite INR_IZR_INZ.
    assert (H_up_ge_0 : (0 <= up threshold)%Z).
    {
      apply le_IZR.
      simpl.
      lra.
    }
    rewrite Z2Nat.id by exact H_up_ge_0.
    lra.
  }
  apply Rle_ge.
  apply Rle_trans with (INR M);
    [ apply Rge_le; exact Hup
    | apply le_INR; exact HN ].
Qed.

(* 平方根下界阈值保持 *)
Lemma sqrt_ge_threshold :
  forall (eps : R) (x : R),
    0 < eps <= 2 ->
    x >= Rsqr ((2 - eps) / eps) ->
    sqrt x >= (2 - eps) / eps.
Proof.
  intros eps x [Heps_pos Heps_le2] Hx.
  set (rhs := (2 - eps) / eps).
  assert (H_rhs_nonneg : 0 <= rhs).
  { unfold rhs. apply Rmult_le_pos; [lra | apply Rlt_le, Rinv_0_lt_compat; lra]. }
  assert (H_sq_nonneg : 0 <= rhs²) by apply Rle_0_sqr.
  assert (Hx_nonneg : 0 <= x).
  { apply Rle_trans with rhs²; [apply H_sq_nonneg | apply Rge_le; exact Hx]. }
  apply Rle_ge.
  rewrite <- (sqrt_square rhs H_rhs_nonneg).
  apply sqrt_le_1_c; [exact H_sq_nonneg | exact Hx_nonneg | apply Rge_le; exact Hx].
Qed.

(* 折扣因子不等式 *)
Lemma discount_factor_inequality :
  forall (eps c : R),
    0 < eps -> eps < 1 ->
    c >= (2 - eps) / eps ->
    (1 - eps) / (c - 1) <= 1 / (c + 1).
Proof.
  intros eps c Heps Heps_lt1 Hc_ge.

  (* 1. 基本区间推导 *)
  assert (H_ratio_gt1 : 1 < (2 - eps) / eps). {
    apply (Rmult_lt_reg_l eps); [lra|].
    replace (eps * 1) with eps by ring.
    replace (eps * ((2 - eps) / eps)) with (2 - eps) by (field; lra).
    lra.
  }
  assert (Hc_gt1 : c > 1). {
    eapply Rlt_le_trans; [exact H_ratio_gt1 | apply Rge_le; exact Hc_ge].
  }
  assert (Hc_minus_pos : c - 1 > 0) by lra.
  assert (Hc_plus_pos  : c + 1 > 0) by lra.

  (* 2. 去分母：两边同乘 (c-1)*(c+1) *)
  apply (Rmult_le_reg_l ((c - 1) * (c + 1))).
  { apply Rmult_lt_0_compat; lra. }

  replace ((c - 1) * (c + 1) * ((1 - eps) / (c - 1)))
    with ((1 - eps) * (c + 1))
    by (field; lra).
  replace ((c - 1) * (c + 1) * (1 / (c + 1)))
    with (c - 1)
    by (field; lra).

  (* 3. 化简后目标：(1 - eps) * (c + 1) <= c - 1 *)
  assert (H_eps_c1 : eps * (c + 1) >= 2). {
    apply Rge_le in Hc_ge.
    apply Rmult_le_compat_l with (r := eps) in Hc_ge; [|lra].
    replace (eps * ((2 - eps) / eps)) with (2 - eps) in Hc_ge by (field; lra).
    apply (Rplus_le_compat_r eps) in Hc_ge.
    replace (2 - eps + eps) with 2 in Hc_ge by ring.
    replace (eps * c + eps) with (eps * (c + 1)) in Hc_ge by ring.
    lra.
  }

  apply Rplus_le_reg_l with (eps * (c + 1) - c + 1).
  ring_simplify.
  replace (c - 1 + (eps * (c + 1) - c + 1)) with (eps * (c + 1)) by ring.
  replace ((1 - eps) * (c + 1) + (eps * (c + 1) - c + 1)) with 2 by ring.
  lra.
Qed.

(* 乘积形式的传递性 *)
Lemma combine_bounds :
  forall (eps A B C D : R),
    0 <= eps ->               (* 新增前提 *)
    0 <= 1 - eps ->
    0 <= A -> 0 < C -> 0 < D ->
    A / C <= B / D ->
    (1 - eps) * (A / C) <= B / D.
Proof.
  intros eps A B C D Heps_ge0 Heps_le1 HA HC HD Hineq.
  assert (Hdiv_nonneg : 0 <= A / C).
  { unfold Rdiv; apply Rmult_le_pos; [exact HA | apply Rlt_le, Rinv_0_lt_compat; exact HC]. }
  apply Rle_trans with (1 * (A / C)).
  - apply Rmult_le_compat_r; [exact Hdiv_nonneg |].
    (* 由 eps >= 0 得 1 - eps <= 1 *)
    lra.
  - rewrite Rmult_1_l; exact Hineq.
Qed.

(* 平方增长蕴含索引严格递增 *)
Lemma n2_gt_n1_from_growth :
  forall (n1 n2 : nat) (f : nat -> nat),
    (n1 >= 2)%nat ->
    (f n1 >= 9)%nat ->
    INR n2 >= INR (f n1) * INR (f n1) * INR n1 ->
    (n1 < n2)%nat.
Proof.
  intros n1 n2 f Hn1_ge2 Hf_ge9 Hsq.
  apply (square_growth_implies_lt n1 n2 f).
  - exact Hn1_ge2.
  - (* (f n1 >= 2)%nat *)
    apply Nat.le_trans with (m := 9%nat); [lia | exact Hf_ge9].
  - exact Hsq.
Qed.

(* 折扣因子平方根下界不等式 *)
Lemma discount_factor_from_sqrt_ge :
  forall (eps : R) (s : R),
    0 < eps <= 1 ->
    s >= (2 - eps) / eps ->
    (1 - eps) / (s - 1) <= 1 / (s + 1).
Proof.
  intros eps s [Heps_pos Heps_le1] Hs_ge.
  destruct (Req_dec eps 1) as [Heps_eq1 | Heps_neq1].
  - (* eps = 1 *)
    rewrite Heps_eq1.
    replace (1 - 1) with 0 by lra.
    rewrite Rdiv_0_l.
    apply Rlt_le.
    apply Rdiv_lt_0_compat; [lra |].
    apply Rlt_le_trans with 2; [lra |].
    apply Rplus_le_compat_r.
    rewrite Heps_eq1 in Hs_ge.
    replace (2 - 1) with 1 in Hs_ge by lra.
    replace (1 / 1) with 1 in Hs_ge by (field; lra).
    lra.
  - (* eps < 1 *)
    assert (Heps_lt1 : eps < 1) by lra.   (* 由 eps <= 1 且 eps <> 1 自动推出 *)
    apply (discount_factor_inequality eps s);
      [exact Heps_pos | exact Heps_lt1 | exact Hs_ge].
Qed.

(* 折现因子分式不等式 *)

(* 自然数平方根大于一 *)
Lemma sqrt_INR_minus_1_pos :
  forall (n : nat),
    (n >= 9)%nat ->
    0 < sqrt (INR n) - 1.
Proof.
intros n Hn.
apply Rgt_minus.
rewrite <- sqrt_1.
apply sqrt_lt_1;
  [ lra
  | apply Rlt_le, lt_0_INR; lia
  | apply (lt_INR 1); lia ].
Qed.

(* 定理：自适应下界优化 *)
Theorem adaptive_lower_bound_optimized :
  forall (eps : R) (f : nat -> nat),
    0 < eps <= 1 ->
    (forall n, (f n >= 9)%nat) ->
    (forall M : nat, exists N : nat, forall n : nat, (n >= N)%nat -> (f n >= M)%nat) ->
    exists N : nat, forall (n1 n2 : nat),
      (n1 >= N)%nat ->
      INR n2 >= INR (f n1) * INR (f n1) * INR n1 ->
      (1 - eps) * sqrt (INR n1 / INR n2) / (sqrt (INR (f n1)) - 1) <=
      sqrt (INR n1 * INR n2) / (4 * (INR n2 - INR n1)).
Proof.
  intros eps f [Heps_pos Heps_le1] Hf_ge9 Hf_unbounded.
  pose (threshold := Rsqr ((2 - eps) / eps)).
  assert (Hthresh_nonneg : 0 <= threshold) by apply Rle_0_sqr.
  destruct (unbounded_exists_ge_up f threshold Hf_unbounded) as [N0 HN0].
  exists (max N0 2).
  intros n1 n2 Hn1 Hsq.
  assert (Hn1_ge2 : (n1 >= 2)%nat)
    by (apply Nat.le_trans with (max N0 2); [apply Nat.le_max_r | exact Hn1]).
  assert (Hf_ge9_n1 : (f n1 >= 9)%nat) by apply Hf_ge9.
  assert (Hlt : (n1 < n2)%nat)
    by (apply n2_gt_n1_from_growth with (f := f);
        [exact Hn1_ge2 | exact Hf_ge9_n1 | exact Hsq]).
  assert (Hn2_ge2 : (n2 >= 2)%nat)
    by (apply Nat.le_trans with (m := n1); [exact Hn1_ge2 | lia]).
  pose proof (core_algebraic_inequality_lower n1 n2 (f n1)
                Hn1_ge2 Hn2_ge2 Hlt Hf_ge9_n1 Hsq) as Hcore.
  assert (Hf_large_INR : INR (f n1) >= threshold).
  { apply HN0. eapply Nat.le_trans; [| exact Hn1]. apply Nat.le_max_l. }
  assert (Hsqrt_ge : sqrt (INR (f n1)) >= (2 - eps) / eps).
  { apply sqrt_ge_threshold with (eps := eps) (x := INR (f n1)).
    - split; [exact Heps_pos |]. apply Rlt_le; lra.
    - exact Hf_large_INR. }
  assert (Hdiscount := discount_factor_from_sqrt_ge eps (sqrt (INR (f n1))) (conj Heps_pos Heps_le1) Hsqrt_ge).
  set (A := sqrt (INR n1 / INR n2)).
  set (B := sqrt (INR n1 * INR n2) / (4 * (INR n2 - INR n1))).
  set (C1 := sqrt (INR (f n1)) - 1).
  set (C2 := sqrt (INR (f n1)) + 1).
  assert (HA_nonneg : 0 <= A).
  { apply sqrt_positivity. unfold Rdiv. apply Rmult_le_pos.
    - apply pos_INR.
    - left. apply Rinv_0_lt_compat. apply lt_0_INR; lia. }
  assert (HC1_pos : 0 < C1) by apply (sqrt_INR_minus_1_pos (f n1) Hf_ge9_n1).
  assert (HC2_pos : 0 < C2) by (apply Rplus_lt_0_compat; [apply sqrt_lt_R0_c; apply lt_0_INR; lia | lra]).
  assert (HB_nonneg : 0 <= B).
  { unfold B, Rdiv.
    apply Rmult_le_pos.
    - apply sqrt_positivity. apply Rmult_le_pos; apply pos_INR.
    - left. apply Rinv_0_lt_compat.
      apply Rmult_lt_0_compat; [lra |].
      apply Rgt_minus. apply lt_INR. exact Hlt. }
  apply Rle_trans with (A / C2).
  - assert (Hleft_eq : (1 - eps) * A / C1 = A * ((1 - eps) / C1)).
    { unfold A, C1, Rdiv.
      rewrite <- Rmult_assoc.
      rewrite (Rmult_comm (1 - eps) (sqrt (INR n1 * / INR n2))).
      rewrite Rmult_assoc.
      reflexivity. }
    rewrite Hleft_eq.
    assert (Hright_eq : A / C2 = A * (1 / C2)).
    { unfold Rdiv.
      rewrite <- Rmult_assoc.
      rewrite <- (Rmult_1_r A) at 1.
      rewrite Rmult_assoc.
      reflexivity. }
    rewrite Hright_eq.
    apply Rmult_le_compat_l.
    + exact HA_nonneg.
    + exact Hdiscount.
  - exact Hcore.
Qed.

(* 平方增长蕴含索引严格递增且第二数不小于 2 *)
Lemma growth_implies_lt_and_ge2 :
  forall (c n1 n2 : nat),
    (c >= 2)%nat ->
    (n1 >= 2)%nat ->
    INR n2 >= INR c * INR c * INR n1 ->
    (n1 < n2)%nat /\ (n2 >= 2)%nat.
Proof.
  intros c n1 n2 Hc Hn1 Hineq.
  split.
  - apply INR_lt.
    apply Rlt_le_trans with (INR c * INR c * INR n1).
    + replace (INR n1) with (1 * INR n1) at 1 by ring.
      apply Rmult_lt_compat_r.
      * apply lt_0_INR; lia.
      * apply Rlt_le_trans with 4; [lra |].
        assert (Hc_ge2_R : 2 <= INR c) by (apply le_INR in Hc; simpl in Hc; lra).
        replace 4 with (2 * 2) by ring.
        apply Rmult_le_compat; lra.
    + apply Rge_le; exact Hineq.
  - destruct (Nat.le_gt_cases 2 n2) as [Hle | Hgt].
    + exact Hle.
    + exfalso.
      assert (Hn2_le_1 : (n2 <= 1)%nat) by lia.
      apply le_INR in Hn2_le_1.
      simpl in Hn2_le_1.
      assert (Hc_ge2_R : 2 <= INR c) by (apply le_INR in Hc; simpl in Hc; lra).
      assert (Hn1_ge2_R : 2 <= INR n1) by (apply le_INR in Hn1; simpl in Hn1; lra).
      assert (Hprod_ge8 : 8 <= INR c * INR c * INR n1).
      { replace 8 with (2 * 2 * 2) by ring.
        apply Rmult_le_compat; try nra. }
      apply Rge_le in Hineq.
      assert (INR n2 >= 8).
      { apply Rle_ge. eapply Rle_trans; [exact Hprod_ge8 | exact Hineq]. }
      lra.
Qed.

(* 缩放因子M不小于c引理：对c≥2和0<ε≤1，有c²/(1+ε) ≥ c *)
Lemma M_ge_c_construction :
  forall (c : nat) (eps : R),
    (c >= 2)%nat -> eps > 0 -> eps <= 1 ->
    let M := INR c * INR c / (1 + eps) in
    M >= INR c.
Proof.
  intros c eps Hc Heps Heps_le1 M.
  apply Rle_ge.
  unfold M, Rdiv.
  apply Rmult_le_reg_r with (1 + eps); [lra |].
  rewrite Rmult_assoc, Rinv_l; [| lra].
  rewrite Rmult_1_r.
  apply Rmult_le_reg_l with (/ INR c).
  - apply Rinv_0_lt_compat. apply lt_0_INR; lia.
  - replace (/ INR c * (INR c * (1 + eps))) with (1 + eps).
    2: { field. apply Rgt_not_eq. apply lt_0_INR; lia. }
    replace (/ INR c * (INR c * INR c)) with (INR c).
    2: { field. apply Rgt_not_eq. apply lt_0_INR; lia. }
    apply Rle_trans with 2.
    + lra.
    + apply le_INR in Hc. simpl in Hc. exact Hc.
Qed.

(* 从 eps 小于 c-1 推出 c² / (1+eps) ≥ c *)
Lemma M_ge_c_from_eps_lt_c_minus_1 :
  forall c eps,
    (c >= 2)%nat -> eps > 0 -> eps < INR c - 1 ->
    INR c * INR c / (1 + eps) >= INR c.
Proof.
  intros c eps Hc Heps Heps_lt.
  apply Rle_ge.
  unfold Rdiv.
  apply Rmult_le_reg_r with (1 + eps); [lra |].
  rewrite Rmult_assoc, Rinv_l; [| lra].
  rewrite Rmult_1_r.
  apply Rmult_le_compat_l.
  - apply pos_INR; lia.
  - apply Rle_trans with (INR c - 1 + 1).
    + rewrite (Rplus_comm 1 eps).
      apply Rplus_le_compat_r with (r := 1).
      apply Rlt_le; exact Heps_lt.
    + generalize (INR c); intro x; lra.
Qed.

(* 稀疏常数版本导出中间不等式（分母含 ε） *)
Lemma intermediate_inequality_from_sparse_const :
  forall (c n1 n2 : nat) (eps : R),
    (c >= 2)%nat -> eps > 0 -> eps < INR c - 1 ->
    (n1 >= 2)%nat ->
    INR n2 >= INR c * INR c * INR n1 ->
    let M := INR c * INR c / (1 + eps) in
    sqrt (INR n1 * INR n2) / (M * (INR n2 - INR n1)) <=
    sqrt (INR n1 / INR n2) / (sqrt (INR c) - 1).
Proof.
  intros c n1 n2 eps Hc Heps Heps_small Hn1 Hineq M.
  assert (Hlt_and_ge2 := growth_implies_lt_and_ge2 c n1 n2 Hc Hn1 Hineq).
  destruct Hlt_and_ge2 as [Hlt Hn2_ge2].
  assert (HM : M >= INR c).
  {
    apply Rle_ge.
    unfold M, Rdiv.
    apply Rmult_le_reg_r with (1 + eps); [lra |].
    rewrite Rmult_assoc, Rinv_l; [| lra].
    rewrite Rmult_1_r.
    apply Rmult_le_compat_l.
    - apply pos_INR; lia.
    - apply Rle_trans with (INR c - 1 + 1).
      + rewrite (Rplus_comm 1 eps).
        apply Rplus_le_compat_r with (r := 1).
        apply Rlt_le; exact Heps_small.
      + replace (INR c - 1 + 1) with (INR c) by ring.
        apply Rle_refl.
  }
  apply core_algebraic_inequality_sparse_const with (M := M); auto.
Qed.

(* 消去分母，转化为纯乘积形式的不等式 *)
Lemma eliminate_denominators :
  forall (c n1 n2 : nat) (M : R),
    (c >= 2)%nat -> (n1 >= 2)%nat -> (n1 < n2)%nat -> 0 < M ->
    sqrt (INR n1 * INR n2) / (M * (INR n2 - INR n1)) <=
    sqrt (INR n1 / INR n2) / (sqrt (INR c) - 1) ->
    sqrt (INR n1 * INR n2) * (sqrt (INR c) - 1) <=
    sqrt (INR n1 / INR n2) * M * (INR n2 - INR n1).
Proof.
  intros c n1 n2 M Hc Hn1 Hlt HM_pos H_main.
  assert (H_denom1_pos : 0 < sqrt (INR c) - 1)
    by (apply sqrt_c_minus_1_pos; lia).
  assert (H_diff_pos : 0 < INR n2 - INR n1)
    by (apply Rgt_minus; apply lt_INR; auto).
  assert (H_prod_pos : 0 < M * (INR n2 - INR n1) * (sqrt (INR c) - 1)).
  { repeat apply Rmult_lt_0_compat; assumption. }
  apply Rmult_le_compat_r
    with (r := M * (INR n2 - INR n1) * (sqrt (INR c) - 1)) in H_main;
    [| apply Rlt_le; exact H_prod_pos].
  assert (H_left_eq :
    sqrt (INR n1 * INR n2) / (M * (INR n2 - INR n1)) *
    (M * (INR n2 - INR n1) * (sqrt (INR c) - 1)) =
    sqrt (INR n1 * INR n2) * (sqrt (INR c) - 1)).
  { field. repeat split; try apply Rgt_not_eq; lra. }
  rewrite H_left_eq in H_main.
  assert (H_right_eq :
    sqrt (INR n1 / INR n2) / (sqrt (INR c) - 1) *
    (M * (INR n2 - INR n1) * (sqrt (INR c) - 1)) =
    sqrt (INR n1 / INR n2) * M * (INR n2 - INR n1)).
  { field. repeat split; try apply Rgt_not_eq; lra. }
  rewrite H_right_eq in H_main.
  exact H_main.
Qed.

(* 定理：核心代数不等式的渐近常数形式 *)
Theorem core_algebraic_inequality_asymptotic_constant :
  forall (c : nat) (eps : R),
    (c >= 2)%nat -> eps > 0 ->
    exists K : nat, forall (n1 n2 : nat),
      (n1 >= 2)%nat ->
      INR n2 >= (INR c)^K * INR n1 ->
      sqrt (INR n1 * INR n2) / (INR c * INR c * (INR n2 - INR n1)) <=
      (1 + eps) * sqrt (INR n1 / INR n2) / (sqrt (INR c) - 1).
Proof.
  intros c eps Hc Heps.
  exists 2%nat.
  intros n1 n2 Hn1 Hineq.
  assert (Hsq : INR n2 >= INR c * INR c * INR n1).
  { rewrite <- Rsqr_pow2 in Hineq; exact Hineq. }
  assert (Hlt : (n1 < n2)%nat).
  { apply (growth_implies_lt_and_ge2 c n1 n2); auto. }
  assert (Hn2 : (n2 >= 2)%nat) by lia.
  assert (HM : INR c * INR c >= INR c).
  { apply Rle_ge.
    transitivity (INR c * 1).
    - rewrite Rmult_1_r; apply Rle_refl.
    - apply Rmult_le_compat_l.
      + apply pos_INR; lia.
      + change 1 with (INR 1). apply le_INR; lia. }
  pose proof (core_algebraic_inequality_sparse_const n1 n2 c (INR c * INR c)
                Hn1 Hn2 Hlt Hc HM Hsq) as Hmain.
  eapply Rle_trans; [exact Hmain |].
  unfold Rdiv.
  apply Rmult_le_compat_r.
  - apply Rlt_le, Rinv_0_lt_compat, sqrt_c_minus_1_pos; auto.
  - rewrite <- Rmult_1_l at 1.
    apply Rmult_le_compat_r.
    + apply sqrt_positivity.
      apply Rlt_le.
      apply Rmult_lt_0_compat.
      * apply lt_0_INR; lia.
      * apply Rinv_0_lt_compat, lt_0_INR; lia.
    + apply Rlt_le; lra.
Qed.

(* 缩放不等式：正数乘法保持不等号方向 *)
Lemma scale_inequality (r a b : R) : 0 < r -> a <= b -> a * r <= b * r.
Proof.
  intros Hr Hab.
  apply Rmult_le_compat_r.
  - left; exact Hr.
  - exact Hab.
Qed.

(* 非负实数乘法右保序性 *)
Lemma Rmult_le_compat_r_nonneg (r a b : R) :
  0 <= r -> a <= b -> a * r <= b * r.
Proof.
  exact (Rmult_le_compat_r r a b).
Qed.

(* 正实数乘法右单调性（严格正乘数） *)
Lemma Rmult_le_compat_r_pos (r a b : R) : 
  0 < r -> a <= b -> a * r <= b * r.
Proof.
  intros Hr Hle.
  apply Rmult_le_compat_r.
  - left; exact Hr.
  - exact Hle.
Qed.

(* 列表正实数乘积保正 *)
Lemma Rmult_list_pos : forall l : list R,
  Forall (fun x => 0 < x) l -> 0 < fold_right Rmult 1 l.
Proof.
  induction l as [|x xs IH]; simpl; intros H.
  - lra.
  - inversion H; subst.
    apply Rmult_lt_0_compat; auto.
Qed.

(* 缩放不等式（带参数M） *)
Lemma scale_inequality_with_M (c n1 n2 : nat) (eps : R) (M : R) :
  (c >= 2)%nat ->
  (n1 >= 2)%nat ->
  (n1 < n2)%nat ->
  eps > 0 ->
  M = INR c * INR c / (1 + eps) ->
  sqrt (INR n1 * INR n2) * (sqrt (INR c) - 1) <=
  sqrt (INR n1 / INR n2) * M * (INR n2 - INR n1) ->
  sqrt (INR n1 * INR n2) * (sqrt (INR c) - 1) <=
  sqrt (INR n1 / INR n2) * (INR c * INR c) * (INR n2 - INR n1) * (1 + eps).
Proof.
  intros Hc Hn1 Hlt Heps HM_eq Hmain.
  set (A := sqrt (INR n1 / INR n2) * (INR n2 - INR n1)).
  assert (HA_nonneg : 0 <= A).
  { unfold A.
    apply Rmult_le_pos.
    - apply sqrt_positivity.
      apply Rlt_le.
      apply Rmult_lt_0_compat.
      + apply lt_0_INR; lia.
      + apply Rinv_0_lt_compat; apply lt_0_INR; lia.
    - apply Rlt_le.
      apply Rgt_minus.
      apply lt_INR; exact Hlt.
  }
  replace (sqrt (INR n1 / INR n2) * M * (INR n2 - INR n1))
    with (A * M) in Hmain by (unfold A; ring).
  replace (sqrt (INR n1 / INR n2) * (INR c * INR c) * (INR n2 - INR n1) * (1 + eps))
    with (A * (INR c * INR c * (1 + eps))) by (unfold A; ring).
  assert (HM_bound : M <= INR c * INR c * (1 + eps)).
  { rewrite HM_eq.
    unfold Rdiv.
    apply Rmult_le_compat_l.
    - apply Rmult_le_pos; apply pos_INR; lia.
    - apply Rle_trans with 1.
      + apply (Rmult_le_reg_l (1 + eps)).
        * lra.
        * rewrite Rinv_r by lra.
          rewrite Rmult_1_r.
          lra.
      + lra.
  }
  apply Rle_trans with (A * M).
  - exact Hmain.
  - apply Rmult_le_compat_l.
    + exact HA_nonneg.
    + exact HM_bound.
Qed.

(* 定理：核心代数不等式的渐近常数形式 *)

(* 定理：自适应分母核心代数不等式 *)
Theorem core_algebraic_inequality_adaptive_denom :
  forall (c : nat) (eps : R),
    (c >= 2)%nat -> 0 < eps < INR c - 1 ->
    exists K : nat, forall (n1 n2 : nat),
      (n1 >= 2)%nat ->
      INR n2 >= (INR c)^K * INR n1 ->
      sqrt (INR n1 * INR n2) / ((INR c * INR c / (1 + eps)) * (INR n2 - INR n1)) <=
      sqrt (INR n1 / INR n2) / (sqrt (INR c) - 1).
Proof.
  intros c eps Hc Heps_range.
  destruct Heps_range as [Heps_pos Heps_lt].
  exists 2%nat.
  intros n1 n2 Hn1 Hineq.
  assert (Hsq : INR n2 >= INR c * INR c * INR n1).
  { rewrite <- Rsqr_pow2 in Hineq; exact Hineq. }
  assert (Hlt_and_ge2 := growth_implies_lt_and_ge2 c n1 n2 Hc Hn1 Hsq).
  destruct Hlt_and_ge2 as [Hlt Hn2].
  set (M := INR c * INR c / (1 + eps)).
  assert (HM : M >= INR c).
  { apply M_ge_c_from_eps_lt_c_minus_1; auto. }
  apply (core_algebraic_inequality_sparse_const n1 n2 c M Hn1 Hn2 Hlt Hc HM Hsq).
Qed.

(* 自然数指数单调性——平方不超过高次幂 *)
Lemma INR_pow_2_le_K :
  forall (c K : nat),
    (c >= 2)%nat -> (K >= 2)%nat ->
    (INR c)^2 <= (INR c)^K.
Proof.
  intros c K Hc HK.
  apply (Rle_pow (INR c) 2 K).
  - (* 1 <= INR c *)
    cut (INR 1 <= INR c).
    + rewrite INR_1; auto.
    + apply le_INR; lia.
  - exact HK.
Qed.

(* 定理：自适应分母的通用K阶核心代数不等式 *)
Theorem adaptive_denom_general_K :
  forall (c K : nat) (eps : R),
    (c >= 2)%nat -> (K >= 2)%nat -> 0 < eps < INR c - 1 ->
    forall (n1 n2 : nat),
      (n1 >= 2)%nat ->
      INR n2 >= (INR c)^K * INR n1 ->
      sqrt (INR n1 * INR n2) / ((INR c)^K / (1 + eps) * (INR n2 - INR n1)) <=
      sqrt (INR n1 / INR n2) / (sqrt (INR c) - 1).
Proof.
  intros c K eps Hc HK Heps_range n1 n2 Hn1 Hineq.

  (* 1. 将 (INR c)^K 放缩至 (INR c)^2 *)
  pose proof (INR_pow_2_le_K c K Hc HK) as H_pow_le.

  (* 2. 推导出 INR n2 >= INR c * INR c * INR n1 *)
  assert (Hsq : INR n2 >= INR c * INR c * INR n1).
  {
    apply Rle_ge.
    eapply Rle_trans; [| apply Rge_le; exact Hineq].
    apply Rmult_le_compat_r.
    - apply pos_INR; lia.
    - replace (INR c * INR c) with ((INR c) ^ 2) by (symmetry; apply Rsqr_pow2).
      exact H_pow_le.
  }

  (* 3. 获取 n1 < n2 以及 n2 >= 2 *)
  assert (Hlt_ge2 := growth_implies_lt_and_ge2 c n1 n2 Hc Hn1 Hsq).
  destruct Hlt_ge2 as [Hlt Hn2_ge2].

  (* 4. 比较分母缩放因子 *)
  assert (H_denom_le : (INR c)^2 / (1 + eps) <= (INR c)^K / (1 + eps)).
  {
    unfold Rdiv.
    apply Rmult_le_compat_r with (r := / (1 + eps)).
    - left; apply Rinv_0_lt_compat; lra.
    - exact H_pow_le.
  }

  (* 5. 各量的正性条件 *)
  assert (H_diff_pos : 0 < INR n2 - INR n1).
  { apply Rgt_minus; apply lt_INR; exact Hlt. }

  assert (H_c2_pos : 0 < (INR c)^2).
  { apply pow_lt; apply lt_0_INR; lia. }

  assert (H_cK_pos : 0 < (INR c)^K).
  { apply pow_lt; apply lt_0_INR; lia. }

  assert (H_inv_pos : 0 < / (1 + eps)).
  { apply Rinv_0_lt_compat; lra. }

  (* 6. 利用分母放大将问题归约到 K=2 的情形 *)
  apply Rle_trans with
    (sqrt (INR n1 * INR n2) / ((INR c)^2 / (1 + eps) * (INR n2 - INR n1))).
  - unfold Rdiv.
    apply Rmult_le_compat_l.
    + apply Rlt_le, sqrt_lt_R0_c; apply Rmult_lt_0_compat; apply lt_0_INR; lia.
    + apply Rinv_le_contravar.
      * apply Rmult_lt_0_compat.
        -- apply Rmult_lt_0_compat; [exact H_c2_pos | exact H_inv_pos].
        -- exact H_diff_pos.
      * apply Rmult_le_compat_r with (r := INR n2 - INR n1).
        -- apply Rlt_le, H_diff_pos.
        -- exact H_denom_le.
  - (* 7. 对于 K=2 的情形应用已有的常数不等式 *)
    destruct Heps_range as [Heps_pos Heps_lt].
    assert (HM : INR c * INR c / (1 + eps) >= INR c).
    { apply (M_ge_c_from_eps_lt_c_minus_1 c eps Hc Heps_pos Heps_lt). }
    pose proof (core_algebraic_inequality_sparse_const n1 n2 c
                  (INR c * INR c / (1 + eps)) Hn1 Hn2_ge2 Hlt Hc HM Hsq)
      as H_target.
    replace (INR c * INR c) with ((INR c)^2) in H_target by (symmetry; apply Rsqr_pow2).
    exact H_target.
Qed.

(* M不小于4（基于c≥9） *)

(* M不小于4（基于c≥9） *)
Lemma M_ge_4_from_c_ge_9 : forall c eps,
  (c >= 9)%nat -> 0 < eps < 1 ->
  INR c * INR c / (1 - eps) >= 4.
Proof.
  intros c eps Hc [Heps_pos Heps_lt1].
  apply Rle_ge.
  assert (Hc_le : INR 9 <= INR c) by (apply le_INR; exact Hc).
  assert (Hc2_ge_81 : INR c * INR c >= 81).
  { apply Rle_ge.
    replace 81 with (INR 9 * INR 9) by (simpl; ring).
    apply Rmult_le_compat.
    - apply pos_INR.
    - apply pos_INR.
    - exact Hc_le.
    - exact Hc_le. }
  assert (H_1_eps_pos : 0 < 1 - eps) by lra.
  assert (H_inv_ge_1 : 1 / (1 - eps) >= 1).
  { apply Rle_ge.
    apply (Rmult_le_reg_r (1 - eps)).
    - exact H_1_eps_pos.
    - unfold Rdiv; rewrite Rmult_assoc, Rinv_l, Rmult_1_r, Rmult_1_l.
      + lra.
      + apply Rgt_not_eq; exact H_1_eps_pos. }
  assert (H_81_inv : 81 * (1 / (1 - eps)) >= 81).
  { apply Rle_ge.
    rewrite <- (Rmult_1_r 81) at 1.
    apply Rmult_le_compat_l.
    - lra.
    - apply Rge_le, H_inv_ge_1. }
  apply Rle_trans with 81.
  - lra.
  - apply Rle_trans with (81 * (1 / (1 - eps))).
    + apply Rge_le in H_81_inv; exact H_81_inv.
    + unfold Rdiv at 2.
      unfold Rdiv.
      rewrite <- Rmult_assoc.
      rewrite Rmult_1_r.
      apply Rmult_le_compat_r.
      * left; apply Rinv_0_lt_compat; exact H_1_eps_pos.
      * apply Rge_le in Hc2_ge_81; exact Hc2_ge_81.
Qed.

(* 正性条件 *)
Lemma positivity_conditions :
  forall (c : nat) (eps : R) (n1 n2 : nat) (M : R),
    (c >= 9)%nat -> 0 < eps < 1 ->
    (n1 >= 2)%nat -> INR n2 >= INR c * INR c * INR n1 ->
    (0 < INR n1) /\ (0 < INR n2) /\ (0 < INR n2 - INR n1) /\
    (0 < INR c) /\ (0 < sqrt (INR c) + 1).
Proof.
  intros c eps n1 n2 M Hc Hep Hn1 Hineq.
  assert (Hc_pos : 0 < INR c) by (apply lt_0_INR; lia).
  assert (Hn1_pos : 0 < INR n1) by (apply lt_0_INR; lia).
  assert (Hlt : (n1 < n2)%nat).
  { apply (growth_implies_lt_and_ge2 c n1 n2); try lia; exact Hineq. }
  assert (Hn2_pos : 0 < INR n2) by (apply lt_0_INR; lia).
  assert (H_diff_pos : 0 < INR n2 - INR n1)
    by (apply Rgt_minus; apply lt_INR; auto).
  assert (H_sqrt_c_plus_1_pos : 0 < sqrt (INR c) + 1)
    by (apply Rplus_lt_0_compat; [apply sqrt_lt_R0_c; auto | lra]).
  repeat split; assumption.
Qed.

(* 正性条件（含M） *)
Lemma positivity_conditions_m :
  forall (c : nat) (eps : R) (n1 n2 : nat) (M : R),
    (c >= 9)%nat -> 0 < eps < 1 ->
    (n1 >= 2)%nat -> INR n2 >= INR c * INR c * INR n1 ->
    0 < M ->
    (0 < INR n1) /\ (0 < INR n2) /\ (0 < INR n2 - INR n1) /\
    (0 < INR c) /\ (0 < sqrt (INR c) + 1) /\ (0 < M).
Proof.
  intros c eps n1 n2 M Hc Hep Hn1 Hineq HM_pos.
  assert (Hc_pos : 0 < INR c) by (apply lt_0_INR; lia).
  assert (Hn1_pos : 0 < INR n1) by (apply lt_0_INR; lia).
  assert (Hlt : (n1 < n2)%nat).
  { apply (growth_implies_lt_and_ge2 c n1 n2); try lia; exact Hineq. }
  assert (Hn2_pos : 0 < INR n2) by (apply lt_0_INR; lia).
  assert (H_diff_pos : 0 < INR n2 - INR n1)
    by (apply Rgt_minus; apply lt_INR; auto).
  assert (H_sqrt_c_plus_1_pos : 0 < sqrt (INR c) + 1)
    by (apply Rplus_lt_0_compat; [apply sqrt_lt_R0_c; auto | lra]).
  repeat split; assumption.
Qed.

(* 平方根恒等式 *)
Lemma sqrt_identities :
  forall (n1 n2 : nat) (a b : R),
    a = sqrt (INR n1) -> b = sqrt (INR n2) ->
    0 < INR n1 -> 0 < INR n2 ->
    sqrt (INR n1 * INR n2) = a * b /\
    sqrt (INR n1 / INR n2) = a / b /\
    a * a = INR n1 /\ b * b = INR n2.
Proof.
  intros n1 n2 a b Ha Hb Hn1_pos Hn2_pos.
  subst a b.
  split; [| split; [| split]].
  - apply sqrt_mult; auto; apply Rlt_le; assumption.
  - apply sqrt_div; auto; apply Rlt_le; assumption.
  - apply sqrt_sqrt; apply Rlt_le; assumption.
  - apply sqrt_sqrt; apply Rlt_le; assumption.
Qed.

(* 消去分母第一步 *)
Lemma cancel_denominators_step1 :
  forall (c : nat) (eps : R) (n1 n2 : nat) (M : R),
    0 < M -> 0 < INR n2 - INR n1 -> 0 < sqrt (INR c) + 1 ->
    (sqrt (INR n1 * INR n2) * (sqrt (INR c) + 1) <=
     sqrt (INR n1 / INR n2) * M * (INR n2 - INR n1)) ->
    sqrt (INR n1 * INR n2) / (M * (INR n2 - INR n1)) <=
    sqrt (INR n1 / INR n2) / (sqrt (INR c) + 1).
Proof.
  intros c eps n1 n2 M HM_pos Hdiff_pos Hsqrt_pos H.
  apply (Rmult_le_reg_r (M * (INR n2 - INR n1))).
  { apply Rmult_lt_0_compat; assumption. }
  apply (Rmult_le_reg_l (sqrt (INR c) + 1)).
  { assumption. }
  replace ((sqrt (INR c) + 1) *
           (sqrt (INR n1 * INR n2) / (M * (INR n2 - INR n1)) *
            (M * (INR n2 - INR n1))))
    with (sqrt (INR n1 * INR n2) * (sqrt (INR c) + 1)).
  2: field; auto with real; try (apply Rgt_not_eq; auto).
  replace ((sqrt (INR c) + 1) *
           (sqrt (INR n1 / INR n2) / (sqrt (INR c) + 1) *
            (M * (INR n2 - INR n1))))
    with (sqrt (INR n1 / INR n2) * M * (INR n2 - INR n1)).
  2: field; auto with real; try (apply Rgt_not_eq; auto).
  exact H.
Qed.

(* 平方根不大于上取整自然数的平方根 *)
Lemma sqrt_le_INR_up : forall c : R,
  sqrt c <= sqrt (INR (Z.to_nat (up c))).
Proof.
  intros c.
  destruct (Rle_lt_dec 0 c) as [Hc_nonneg | Hc_neg].
  - assert (Hc_le : c <= INR (Z.to_nat (up c))).
    {
      apply Rle_trans with (IZR (up c)).
      - apply Rlt_le, (proj1 (archimed c)).
      - rewrite INR_IZR_INZ.
        rewrite Z2Nat.id.
        + apply Rle_refl.
        + apply Z.lt_le_incl.
          apply lt_0_IZR.
          eapply Rle_lt_trans.
          * exact Hc_nonneg.
          * apply (proj1 (archimed c)).
    }
    apply sqrt_le_1_c.
    + exact Hc_nonneg.
    + apply Rle_trans with c; [exact Hc_nonneg | exact Hc_le].
    + exact Hc_le.
  - rewrite sqrt_neg_0; [ | apply Rlt_le; exact Hc_neg ].
    apply sqrt_positivity.
    apply pos_INR.
Qed.

(* 消去a与b的第二步 *)
Lemma cancel_a_b_step2 :
  forall (a b M c : R),
    0 < a -> 0 < b ->
    a * a * (b * b) * (sqrt (INR (Z.to_nat (up c))) + 1) <=
    a * a * M * (b * b - a * a) ->
    a * (b * b) * (sqrt c + 1) <= a * M * (b * b - a * a).
Proof.
  intros a b M c Ha Hb Hineq.
  assert (Htmp : a * (a * (b * b) * (sqrt (INR (Z.to_nat (up c))) + 1)) <=
                 a * (a * M * (b * b - a * a))).
  { replace (a * a * (b * b) * (sqrt (INR (Z.to_nat (up c))) + 1))
      with (a * (a * (b * b) * (sqrt (INR (Z.to_nat (up c))) + 1))) in Hineq by ring.
    replace (a * a * M * (b * b - a * a))
      with (a * (a * M * (b * b - a * a))) in Hineq by ring.
    exact Hineq. }
  apply (Rmult_le_reg_l a) in Htmp; [| exact Ha].
  clear Hineq.
  assert (Hsqrt : sqrt c <= sqrt (INR (Z.to_nat (up c)))) by apply sqrt_le_INR_up.
  assert (Hsqrt_plus : sqrt c + 1 <= sqrt (INR (Z.to_nat (up c))) + 1)
    by (apply Rplus_le_compat_r; exact Hsqrt).
  assert (Hcoeff_nonneg : 0 <= a * (b * b)).
  { apply Rmult_le_pos; [left; exact Ha | apply Rle_0_sqr]. }
  apply Rmult_le_compat_l with (r := a * (b * b)) in Hsqrt_plus;
    [| exact Hcoeff_nonneg ].
  eapply Rle_trans.
  - exact Hsqrt_plus.
  - exact Htmp.
Qed.

(* 核心不等式归约到线性界 *)
Lemma core_inequality_to_linear_bound :
  forall (n1 n2 c : nat) (Hcore : sqrt (INR n1 / INR n2) / (sqrt (INR c) + 1) <=
                                 sqrt (INR n1 * INR n2) / (4 * (INR n2 - INR n1))),
    (n1 >= 2)%nat -> (n2 >= 2)%nat -> (n1 < n2)%nat -> (c >= 9)%nat ->
    4 * (INR n2 - INR n1) <= INR n2 * (sqrt (INR c) + 1).
Proof.
  intros n1 n2 c Hcore Hn1 Hn2 Hlt Hc.
  
  assert (Hn1_pos : 0 < INR n1) by (apply lt_0_INR; lia).
  assert (Hn2_pos : 0 < INR n2) by (apply lt_0_INR; lia).
  assert (Hc_pos  : 0 < INR c)  by (apply lt_0_INR; lia).
  assert (H_diff_pos : 0 < INR n2 - INR n1)
    by (apply Rgt_minus; apply lt_INR; exact Hlt).
  
  assert (H_denom1_pos : 0 < sqrt (INR c) + 1)
    by (apply Rplus_lt_0_compat; [apply sqrt_lt_R0_c; exact Hc_pos | lra]).
  assert (H_denom2_pos : 0 < 4 * (INR n2 - INR n1))
    by (apply Rmult_lt_0_compat; [lra | exact H_diff_pos]).

  set (a := sqrt (INR n1)).
  set (b := sqrt (INR n2)).
  assert (Ha_pos : 0 < a) by (subst a; apply sqrt_lt_R0_c; exact Hn1_pos).
  assert (Hb_pos : 0 < b) by (subst b; apply sqrt_lt_R0_c; exact Hn2_pos).
  
  assert (Ha_sq : a * a = INR n1) by (subst a; apply sqrt_sqrt; apply Rlt_le; exact Hn1_pos).
  assert (Hb_sq : b * b = INR n2) by (subst b; apply sqrt_sqrt; apply Rlt_le; exact Hn2_pos).
  
  assert (Hsqrt_mult : sqrt (INR n1 * INR n2) = a * b).
  {
    rewrite sqrt_mult with (x := INR n1) (y := INR n2).
    - subst a b; reflexivity.
    - apply Rlt_le; exact Hn1_pos.
    - apply Rlt_le; exact Hn2_pos.
  }
  assert (Hsqrt_div : sqrt (INR n1 / INR n2) = a / b).
  {
    rewrite sqrt_div with (x := INR n1) (y := INR n2).
    - subst a b; reflexivity.
    - apply Rlt_le; exact Hn1_pos.
    - exact Hn2_pos.
  }

  apply (Rmult_le_compat_r (4 * (INR n2 - INR n1))) in Hcore;
    [| apply Rlt_le; exact H_denom2_pos].
  apply (Rmult_le_compat_l (sqrt (INR c) + 1)) in Hcore;
    [| left; exact H_denom1_pos].

  rewrite <- (Rmult_assoc (sqrt (INR c) + 1)) in Hcore.
  rewrite <- (Rmult_assoc (sqrt (INR c) + 1)) in Hcore.
  rewrite Hsqrt_mult, Hsqrt_div in Hcore.

  replace ( (sqrt (INR c) + 1) * (a / b / (sqrt (INR c) + 1)) * (4 * (INR n2 - INR n1)) )
    with ( (a / b) * 4 * (INR n2 - INR n1) ) in Hcore.
  2: { field. repeat split; auto with real. }

  replace ( (sqrt (INR c) + 1) * (a * b / (4 * (INR n2 - INR n1))) * (4 * (INR n2 - INR n1)) )
    with ( a * b * (sqrt (INR c) + 1) ) in Hcore.
  2: { field. repeat split; auto with real. }

  apply (Rmult_le_compat_r b) in Hcore; [| left; exact Hb_pos].
  replace ( (a / b) * 4 * (INR n2 - INR n1) * b )
    with ( a * 4 * (INR n2 - INR n1) ) in Hcore.
  2: { field. auto with real. }
  replace ( a * b * (sqrt (INR c) + 1) * b )
    with ( a * (b * b) * (sqrt (INR c) + 1) ) in Hcore by ring.
  rewrite Hb_sq in Hcore.

  apply (Rmult_le_compat_r a) in Hcore; [| left; exact Ha_pos].
  replace ( a * 4 * (INR n2 - INR n1) * a )
    with ( (a * a) * 4 * (INR n2 - INR n1) ) in Hcore by ring.
  replace ( a * INR n2 * (sqrt (INR c) + 1) * a )
    with ( (a * a) * INR n2 * (sqrt (INR c) + 1) ) in Hcore by ring.
  rewrite Ha_sq in Hcore.

  replace (INR n1 * 4 * (INR n2 - INR n1)) with (INR n1 * (4 * (INR n2 - INR n1))) in Hcore by ring.
  replace (INR n1 * INR n2 * (sqrt (INR c) + 1)) with (INR n1 * (INR n2 * (sqrt (INR c) + 1))) in Hcore by ring.

  apply (Rmult_le_reg_l (INR n1)) in Hcore; auto.
Qed.

(* 反向不等号消去 *)
Lemma Ropp_le_cancel : forall r1 r2, - r1 <= - r2 -> r2 <= r1.
Proof.
  intros; apply Ropp_le_contravar in H; lra.
Qed.

(* 差值下界 *)
Lemma INR_diff_lower_bound : forall (n1 n2 c : nat),
  (0 < n1)%nat -> (0 < n2)%nat -> (0 < c)%nat ->
  INR n2 >= INR c * INR c * INR n1 ->
  INR n2 - INR n1 >= INR n2 * (1 - 1 / (INR c * INR c)).
Proof.
  intros n1 n2 c Hn1 Hn2 Hc Hineq.
  apply Rle_ge.
  assert (Hc_sq_pos : 0 < INR c * INR c) 
    by (apply Rmult_lt_0_compat; apply lt_0_INR; auto).
  apply (Rmult_le_reg_l (INR c * INR c)); auto.
  replace (INR c * INR c * (INR n2 - INR n1)) 
    with (INR c * INR c * INR n2 - INR c * INR c * INR n1) by ring.
  replace (INR c * INR c * (INR n2 * (1 - 1 / (INR c * INR c))))
    with (INR c * INR c * INR n2 - INR n2).
  2: { field. apply not_0_INR; lia. }
  apply Rplus_le_reg_l with (r := - INR c * INR c * INR n2).
  ring_simplify.
  lra.
Qed.

(* 平方根加一不超过分数 *)
Lemma sqrt_plus_one_le_frac :
  forall (c : nat) (eps : R),
    (c >= 9)%nat -> 0 < eps < 1 ->
    sqrt (INR c) + 1 <= (INR c * INR c - 1) / (1 - eps).
Proof.
  intros c eps Hc [Heps_pos Heps_lt1].
  apply Rle_trans with (INR c * INR c - 1).
  - cut (sqrt (INR c) <= INR c * INR c - 2).
    + intros H; lra.
    + assert (Hsqrt_le_c : sqrt (INR c) <= INR c).
      { apply Rle_trans with (sqrt (INR c * INR c)).
        - apply sqrt_le_1_c.
          + apply Rlt_le; apply lt_0_INR; lia.
          + apply Rle_0_sqr.
          + rewrite <- (Rmult_1_r (INR c)) at 1.
            apply Rmult_le_compat_l.
            * apply Rlt_le; apply lt_0_INR; lia.
            * apply Rle_trans with (INR 9); [simpl; lra | apply le_INR; lia].
        - rewrite sqrt_square.
          + right; reflexivity.
          + apply Rlt_le; apply lt_0_INR; lia. }
      assert (Hc_le_c2_minus_2 : INR c <= INR c * INR c - 2).
      { apply Rplus_le_reg_l with 2; ring_simplify.
        apply Rle_trans with (2 * INR c).
        - apply Rplus_le_reg_l with (- INR c); ring_simplify.
          apply Rle_trans with (INR 9); [simpl; lra | apply le_INR; lia].
        - replace (INR c ^ 2) with (INR c * INR c) by ring.
          apply (Rmult_le_compat_r (INR c) 2 (INR c)).
          + apply Rlt_le; apply lt_0_INR; lia.
          + apply le_INR in Hc; simpl in Hc; lra. }
      eapply Rle_trans; eassumption.
  - unfold Rdiv.
    rewrite <- (Rmult_1_r (INR c * INR c - 1)) at 1.
    apply Rmult_le_compat_l.
    + assert (INR c >= 9) by (apply le_INR in Hc; simpl in Hc; lra).
      nra.
    + rewrite <- Rinv_1.
      apply Rinv_le_contravar; lra.
Qed.

(* 定理：自适应分母下界 *)
Theorem adaptive_denom_lower :
  forall (c : nat) (eps : R),
    (c >= 9)%nat -> 0 < eps < 1 ->
    forall (n1 n2 : nat),
      (n1 >= 2)%nat ->
      INR n2 >= (INR c)^2 * INR n1 ->
      let M := INR c * INR c / (1 - eps) in
      sqrt (INR n1 * INR n2) / (M * (INR n2 - INR n1)) <=
      sqrt (INR n1 / INR n2) / (sqrt (INR c) + 1).
Proof.
  intros c eps Hc [Heps_pos Heps_lt1] n1 n2 Hn1 Hineq M.
  
  assert (Hineq' : INR n2 >= INR c * INR c * INR n1).
  { replace (INR c * INR c) with ((INR c)^2) by (symmetry; apply Rsqr_pow2). apply Hineq. }
  
  pose proof (positivity_conditions c eps n1 n2 M Hc (conj Heps_pos Heps_lt1) Hn1 Hineq')
    as (Hn1_pos & Hn2_pos & H_diff_pos & Hc_pos & H_sqrt_c_plus_1_pos).
  
  assert (HM_pos : 0 < M).
  { unfold M, Rdiv. apply Rmult_lt_0_compat; [apply Rmult_lt_0_compat; apply lt_0_INR; lia | apply Rinv_0_lt_compat; lra]. }
  
  set (a := sqrt (INR n1)).
  set (b := sqrt (INR n2)).
  assert (Ha_pos : 0 < a) by (subst a; apply sqrt_lt_R0_c; auto).
  assert (Hb_pos : 0 < b) by (subst b; apply sqrt_lt_R0_c; auto).
  
  assert (Ha_eq : a = sqrt (INR n1)) by reflexivity.
  assert (Hb_eq : b = sqrt (INR n2)) by reflexivity.
  pose proof (sqrt_identities n1 n2 a b Ha_eq Hb_eq Hn1_pos Hn2_pos)
    as (Hsqrt_mult & Hsqrt_div & Ha_sq & Hb_sq).

  apply cancel_denominators_step1 with (M := M); auto.
  rewrite Hsqrt_mult, Hsqrt_div.

  apply (Rmult_le_reg_l b); auto.
  replace (b * (a * b * (sqrt (INR c) + 1))) with (a * (b * b) * (sqrt (INR c) + 1)) by ring.
  replace (b * (a / b * M * (INR n2 - INR n1))) with (a * M * (INR n2 - INR n1)).
  2: { field; auto with real. }

  apply (Rmult_le_reg_l a); auto.
  replace (a * (a * (b * b) * (sqrt (INR c) + 1))) with ((a * a) * (b * b) * (sqrt (INR c) + 1)) by ring.
  replace (a * (a * M * (INR n2 - INR n1))) with ((a * a) * M * (INR n2 - INR n1)) by ring.
  rewrite Ha_sq, Hb_sq.

  replace (INR n1 * INR n2 * (sqrt (INR c) + 1))
    with (INR n1 * (INR n2 * (sqrt (INR c) + 1))) by ring.
  replace (INR n1 * M * (INR n2 - INR n1))
    with (INR n1 * (M * (INR n2 - INR n1))) by ring.
  
  enough (INR n2 * (sqrt (INR c) + 1) <= M * (INR n2 - INR n1))
    as H_target.
  { apply Rmult_le_compat_l; [left; exact Hn1_pos | exact H_target]. }
  clear a b Ha_pos Hb_pos Ha_eq Hb_eq Ha_sq Hb_sq Hsqrt_mult Hsqrt_div.

  assert (Hlt : (n1 < n2)%nat).
  { apply (growth_implies_lt_and_ge2 c n1 n2); auto. lia. }

  assert (H_lower_bound : INR n2 - INR n1 >= INR n2 * (1 - 1 / (INR c * INR c))).
  { apply INR_diff_lower_bound; try lia; auto. }

  assert (H_le : M * (INR n2 * (1 - 1 / (INR c * INR c))) <= M * (INR n2 - INR n1)).
  { apply Rmult_le_compat_l; [left; exact HM_pos | apply Rge_le; exact H_lower_bound]. }

  assert (H_c2_nonzero : INR c * INR c <> 0)
    by (apply Rgt_not_eq; apply Rmult_lt_0_compat; apply lt_0_INR; lia).
  assert (H_c_nonzero : INR c <> 0) by (apply Rgt_not_eq; exact Hc_pos).
  assert (H_1_eps_nonzero : 1 - eps <> 0) by (apply Rgt_not_eq; lra).

  assert (H_M_factor : M * (1 - 1 / (INR c * INR c)) = (INR c * INR c - 1) / (1 - eps)).
  { unfold M, Rdiv. field; repeat split; auto. }

  assert (H_eq : M * (INR n2 * (1 - 1 / (INR c * INR c))) = INR n2 * (M * (1 - 1 / (INR c * INR c)))).
  { ring. }
  rewrite H_eq in H_le.
  rewrite H_M_factor in H_le.

  assert (H_main_ineq : INR n2 * (sqrt (INR c) + 1) <= INR n2 * ((INR c * INR c - 1) / (1 - eps))).
  {
    apply Rmult_le_compat_l; [left; exact Hn2_pos |].
    apply sqrt_plus_one_le_frac; [assumption | split; assumption].
  }
  eapply Rle_trans; [exact H_main_ineq | exact H_le].
Qed.

(* 合并左加权平方根分式 *)
Lemma combine_left_weighted_sqrt_div :
  forall (n1 n2 : nat) (w1 w2 M : R),
    0 < w1 -> 0 < w2 ->
    0 < INR n1 -> 0 < INR n2 ->
    0 < M -> 0 < INR n2 - INR n1 ->
    / (M * (INR n2 - INR n1)) * (sqrt (INR n1 * INR n2) * sqrt (w1 * w2)) =
    sqrt (w1 * w2 * INR n1 * INR n2) / (M * (INR n2 - INR n1)).
Proof.
  intros n1 n2 w1 w2 M Hw1 Hw2 Hn1 Hn2 HM Hdiff.
  rewrite <- sqrt_mult.
  - replace (INR n1 * INR n2 * (w1 * w2))
      with (w1 * w2 * INR n1 * INR n2) by ring.
    unfold Rdiv.
    rewrite Rmult_assoc.
    rewrite (Rmult_comm (sqrt _) (/ _)).
    reflexivity.
  - apply Rmult_le_pos; apply Rlt_le; assumption.
  - apply Rlt_le; apply Rmult_lt_0_compat; assumption.
Qed.

(* 平方根乘积提取 *)
Lemma sqrt_product_extract_w2 :
  forall (n1 n2 : nat) (w1 w2 : R),
    0 < w1 -> 0 < w2 ->
    0 < INR n1 -> 0 < INR n2 ->
    sqrt (w1 * w2 * (INR n1 / INR n2)) =
    sqrt ((w1 / w2) * (INR n1 / INR n2)) * w2.
Proof.
  intros n1 n2 w1 w2 Hw1 Hw2 Hn1 Hn2.
  assert (Hw2_neq0 : w2 <> 0) by (apply Rgt_not_eq; auto).
  assert (H_div_n_pos : 0 < INR n1 / INR n2).
  { unfold Rdiv; apply Rmult_lt_0_compat; [exact Hn1 | apply Rinv_0_lt_compat; exact Hn2]. }
  assert (Hw1_div_w2_pos : 0 <= w1 / w2).
  { apply Rmult_le_pos; [left; auto | left; apply Rinv_0_lt_compat; auto]. }
  assert (H_prod_pos : 0 <= (w1 / w2) * (INR n1 / INR n2)).
  { apply Rmult_le_pos; [exact Hw1_div_w2_pos | left; exact H_div_n_pos]. }
  replace (w1 * w2) with ((w1 / w2) * w2 * w2).
  2: { field; auto. }
  replace ((w1 / w2) * w2 * w2 * (INR n1 / INR n2))
    with (w2 * w2 * ((w1 / w2) * (INR n1 / INR n2))) by ring.
  rewrite sqrt_mult.
  - rewrite sqrt_square.
    + ring.
    + left; exact Hw2.
  - apply Rle_0_sqr.
  - exact H_prod_pos.
Qed.

(* 加权平方根分式右侧合并 *)
Lemma combine_right_weighted_sqrt_div :
  forall (n1 n2 : nat) (w1 w2 C : R),
    0 < w1 -> 0 < w2 ->
    0 < INR n1 -> 0 < INR n2 ->
    C >= 2 ->
    / (sqrt C - 1) * sqrt (INR n1 / INR n2) * sqrt (w1 * w2) =
    sqrt ((w1 / w2) * (INR n1 / INR n2)) * w2 / (sqrt C - 1).
Proof.
  intros n1 n2 w1 w2 C Hw1 Hw2 Hn1 Hn2 HC.
  assert (H_div_pos : 0 < INR n1 / INR n2).
  { unfold Rdiv; apply Rmult_lt_0_compat; [exact Hn1 | apply Rinv_0_lt_compat; exact Hn2]. }
  assert (H_sqrt_pos : 0 < sqrt C - 1).
  { apply Rgt_minus.
    rewrite <- sqrt_1.
    apply sqrt_lt_1; try lra. }

  replace (/ (sqrt C - 1) * sqrt (INR n1 / INR n2) * sqrt (w1 * w2))
    with (/ (sqrt C - 1) * (sqrt (INR n1 / INR n2) * sqrt (w1 * w2)))
    by (rewrite Rmult_assoc; reflexivity).
  rewrite (Rmult_comm (sqrt (INR n1 / INR n2)) (sqrt (w1 * w2))).
  rewrite <- sqrt_mult.
  2: { apply Rmult_le_pos; apply Rlt_le; auto. }
  2: { apply Rlt_le; exact H_div_pos. }

  rewrite (sqrt_product_extract_w2 n1 n2 w1 w2); auto.

  unfold Rdiv at 1 2.

  assert (H_arg_eq : w1 * / w2 * (INR n1 * / INR n2) = 
                     (w1 / w2) * (INR n1 / INR n2)).
  { field; repeat split; try (apply Rgt_not_eq; auto). }
  rewrite H_arg_eq.

  field; repeat split; try (apply Rgt_not_eq; lra).
Qed.

(* 定理：加权自适应分母核心不等式 *)
Theorem weighted_adaptive_denom :
  forall (c : nat) (eps : R) (w : nat -> R),
    (c >= 2)%nat -> 0 < eps < INR c - 1 ->
    (forall i, 0 < w i <= 1) ->
    forall (n1 n2 : nat),
      (n1 >= 2)%nat ->
      INR n2 >= (INR c)^2 * INR n1 ->
      let M := INR c * INR c / (1 + eps) in
      sqrt (w n1 * w n2 * INR n1 * INR n2) / (M * (INR n2 - INR n1)) <=
      sqrt (w n1 / w n2 * (INR n1 / INR n2)) / (sqrt (INR c) - 1).
Proof.
  intros c eps w Hc Heps_range Hw_bound n1 n2 Hn1 Hineq M.
  assert (Hsq : INR n2 >= INR c * INR c * INR n1)
    by (rewrite <- Rsqr_pow2 in Hineq; exact Hineq).
  destruct (growth_implies_lt_and_ge2 c n1 n2 Hc Hn1 Hsq) as [Hlt Hn2_ge2].
  pose proof (intermediate_inequality_from_sparse_const
                c n1 n2 eps Hc (proj1 Heps_range) (proj2 Heps_range) Hn1 Hsq)
       as H_base.

  assert (H_w_pos1 : 0 < w n1) by apply Hw_bound.
  assert (H_w_pos2 : 0 < w n2) by apply Hw_bound.
  assert (H_w_le1_2 : w n2 <= 1) by apply Hw_bound.

  assert (Hn1_pos : 0 < INR n1) by (apply lt_0_INR; lia).
  assert (Hn2_pos : 0 < INR n2) by (apply lt_0_INR; lia).
  assert (H_diff_pos : 0 < INR n2 - INR n1)
    by (apply Rgt_minus; apply lt_INR; exact Hlt).
  assert (HD_pos : 0 < sqrt (INR c) - 1)
    by (apply sqrt_c_minus_1_pos; lia).
  assert (HM_pos : 0 < M).
  { unfold M, Rdiv. apply Rmult_lt_0_compat.
    - apply Rmult_lt_0_compat; apply lt_0_INR; lia.
    - apply Rinv_0_lt_compat; lra. }

  assert (H_weighted : sqrt (w n1 * w n2) * 
         (sqrt (INR n1 * INR n2) / (M * (INR n2 - INR n1))) <=
         sqrt (w n1 * w n2) *
         (sqrt (INR n1 / INR n2) / (sqrt (INR c) - 1))).
  { apply Rmult_le_compat_l.
    - apply Rlt_le, sqrt_lt_R0_c; apply Rmult_lt_0_compat; lra.
    - exact H_base. }

  unfold Rdiv in H_weighted.
  rewrite Rmult_comm in H_weighted.
  repeat rewrite <- Rmult_assoc in H_weighted.
  rewrite (Rmult_comm _ (/ (M * (INR n2 - INR n1)))) in H_weighted.
  repeat rewrite Rmult_assoc in H_weighted.
  rewrite (Rmult_comm _ (/ (sqrt (INR c) - 1))) in H_weighted.

  rewrite (combine_left_weighted_sqrt_div n1 n2 (w n1) (w n2) M
            H_w_pos1 H_w_pos2 Hn1_pos Hn2_pos HM_pos H_diff_pos)
    in H_weighted.

  assert (Hc_ge2 : INR c >= 2).
  { apply Rle_ge. apply le_INR in Hc. simpl in Hc. exact Hc. }

  apply Rle_trans with (sqrt (w n1 * w n2) *
                        (/ (sqrt (INR c) - 1) * sqrt (INR n1 * / INR n2))).
  - exact H_weighted.
  - clear H_weighted.
    replace (sqrt (w n1 * w n2) * (/ (sqrt (INR c) - 1) * sqrt (INR n1 * / INR n2)))
      with (/ (sqrt (INR c) - 1) * sqrt (INR n1 / INR n2) * sqrt (w n1 * w n2)).
    2: { rewrite Rmult_assoc. rewrite (Rmult_comm (sqrt (w n1 * w n2))).
         rewrite <- Rmult_assoc. unfold Rdiv; reflexivity. }
    rewrite combine_right_weighted_sqrt_div with (C := INR c); auto.
    apply Rmult_le_compat_r.
    + apply Rlt_le, Rinv_0_lt_compat; exact HD_pos.
    + rewrite <- (Rmult_1_r (sqrt (w n1 / w n2 * (INR n1 / INR n2)))) at 2.
      apply Rmult_le_compat_l.
      * apply sqrt_positivity; apply Rmult_le_pos.
        -- apply Rlt_le; apply Rmult_lt_0_compat;
           [exact H_w_pos1 | apply Rinv_0_lt_compat; exact H_w_pos2].
        -- apply Rlt_le; unfold Rdiv; apply Rmult_lt_0_compat;
           [exact Hn1_pos | apply Rinv_0_lt_compat; exact Hn2_pos].
      * exact H_w_le1_2.
Qed.

(* 定理：自适应分母二维乘积不等式 *)
Theorem adaptive_denom_2D :
  forall (c : nat) (eps : R),
    (c >= 2)%nat -> 0 < eps < INR c - 1 ->
    forall (n1x n1y n2x n2y : nat),
      (n1x >= 2)%nat -> (n1y >= 2)%nat ->
      INR n2x >= (INR c)^2 * INR n1x ->
      INR n2y >= (INR c)^2 * INR n1y ->
      let M := INR c * INR c / (1 + eps) in
      sqrt (INR n1x * INR n1y * INR n2x * INR n2y) /
        (M * M * (INR n2x - INR n1x) * (INR n2y - INR n1y)) <=
      sqrt ((INR n1x * INR n1y) / (INR n2x * INR n2y)) /
        ((sqrt (INR c) - 1) * (sqrt (INR c) - 1)).
Proof.
  intros c eps Hc Heps_range n1x n1y n2x n2y Hn1x Hn1y Hx Hy M.
  assert (Hsqx : INR n2x >= INR c * INR c * INR n1x).
  { rewrite <- Rsqr_pow2 in Hx; exact Hx. }
  assert (Hsqy : INR n2y >= INR c * INR c * INR n1y).
  { rewrite <- Rsqr_pow2 in Hy; exact Hy. }

  pose proof (intermediate_inequality_from_sparse_const c n1x n2x eps
                Hc (proj1 Heps_range) (proj2 Heps_range) Hn1x Hsqx) as H_adaptx.
  pose proof (intermediate_inequality_from_sparse_const c n1y n2y eps
                Hc (proj1 Heps_range) (proj2 Heps_range) Hn1y Hsqy) as H_adapty.
  simpl in H_adaptx, H_adapty.

  set (A1 := sqrt (INR n1x * INR n2x)).
  set (B1 := M * (INR n2x - INR n1x)).
  set (C1 := sqrt (INR n1x / INR n2x)).
  set (D1 := sqrt (INR c) - 1).
  set (A2 := sqrt (INR n1y * INR n2y)).
  set (B2 := M * (INR n2y - INR n1y)).
  set (C2 := sqrt (INR n1y / INR n2y)).
  set (D2 := sqrt (INR c) - 1).

  assert (Hn1x_pos : 0 < INR n1x) by (apply lt_0_INR; lia).
  assert (Hn1y_pos : 0 < INR n1y) by (apply lt_0_INR; lia).
  assert (Hn2x_pos : 0 < INR n2x).
  { apply Rlt_le_trans with (INR c * INR c * INR n1x).
    - apply Rmult_lt_0_compat; [apply Rmult_lt_0_compat; apply lt_0_INR; lia | apply lt_0_INR; lia].
    - apply Rge_le; exact Hsqx. }
  assert (Hn2y_pos : 0 < INR n2y).
  { apply Rlt_le_trans with (INR c * INR c * INR n1y).
    - apply Rmult_lt_0_compat; [apply Rmult_lt_0_compat; apply lt_0_INR; lia | apply lt_0_INR; lia].
    - apply Rge_le; exact Hsqy. }

  assert (Hltx : (n1x < n2x)%nat).
  { eapply growth_implies_lt_and_ge2 with (c := c); eauto. }
  assert (Hlty : (n1y < n2y)%nat).
  { eapply growth_implies_lt_and_ge2 with (c := c); eauto. }

  assert (H_diff_x_pos : 0 < INR n2x - INR n1x).
  { apply Rgt_minus; apply lt_INR; exact Hltx. }
  assert (H_diff_y_pos : 0 < INR n2y - INR n1y).
  { apply Rgt_minus; apply lt_INR; exact Hlty. }

  assert (H_M_pos : 0 < M).
  { unfold M, Rdiv; apply Rmult_lt_0_compat.
    - apply Rmult_lt_0_compat; apply lt_0_INR; lia.
    - apply Rinv_0_lt_compat; lra. }

  assert (H_D_pos : 0 < D1).
  { apply sqrt_c_minus_1_pos; lia. }

  assert (H_pos1 : 0 <= A1 / B1).
  { apply Rmult_le_pos.
    - apply sqrt_positivity; apply Rmult_le_pos; left; assumption.
    - left; apply Rinv_0_lt_compat; unfold B1; apply Rmult_lt_0_compat; [exact H_M_pos | exact H_diff_x_pos]. }
  assert (H_pos2 : 0 <= A2 / B2).
  { apply Rmult_le_pos.
    - apply sqrt_positivity; apply Rmult_le_pos; left; assumption.
    - left; apply Rinv_0_lt_compat; unfold B2; apply Rmult_lt_0_compat; [exact H_M_pos | exact H_diff_y_pos]. }
  assert (H_pos3 : 0 <= C1 / D1).
  { apply Rmult_le_pos.
    - apply sqrt_positivity; apply Rmult_le_pos; [left; exact Hn1x_pos | left; apply Rinv_0_lt_compat; exact Hn2x_pos].
    - left; apply Rinv_0_lt_compat; exact H_D_pos. }
  assert (H_pos4 : 0 <= C2 / D2).
  { apply Rmult_le_pos.
    - apply sqrt_positivity; apply Rmult_le_pos; [left; exact Hn1y_pos | left; apply Rinv_0_lt_compat; exact Hn2y_pos].
    - left; apply Rinv_0_lt_compat; exact H_D_pos. }

  assert (H_prod1 : (A1 / B1) * (A2 / B2) <= (C1 / D1) * (A2 / B2)).
  { apply Rmult_le_compat_r; [exact H_pos2 | exact H_adaptx]. }
  assert (H_prod2 : (C1 / D1) * (A2 / B2) <= (C1 / D1) * (C2 / D2)).
  { apply Rmult_le_compat_l; [exact H_pos3 | exact H_adapty]. }
  assert (H_prod : (A1 / B1) * (A2 / B2) <= (C1 / D1) * (C2 / D2)).
  { eapply Rle_trans; [exact H_prod1 | exact H_prod2]. }
  clear H_adaptx H_adapty H_prod1 H_prod2.

  replace (A1 / B1 * (A2 / B2)) with (A1 * A2 / (B1 * B2)) in H_prod.
  2: { field; repeat split; try apply Rgt_not_eq;
       try (unfold B1, B2; apply Rmult_lt_0_compat; [exact H_M_pos | auto]). }
  replace (C1 / D1 * (C2 / D2)) with (C1 * C2 / (D1 * D2)) in H_prod.
  2: { field; repeat split; try apply Rgt_not_eq; try exact H_D_pos. }

  unfold A1, A2, C1, C2 in H_prod.

  replace (sqrt (INR n1x * INR n2x) * sqrt (INR n1y * INR n2y))
    with (sqrt (INR n1x * INR n1y * INR n2x * INR n2y)) in H_prod.
  2: { rewrite <- sqrt_mult.
       - f_equal; ring.
       - apply Rmult_le_pos; apply Rlt_le; assumption.
       - apply Rmult_le_pos; apply Rlt_le; assumption. }

  replace (sqrt (INR n1x / INR n2x) * sqrt (INR n1y / INR n2y))
    with (sqrt ((INR n1x * INR n1y) / (INR n2x * INR n2y))) in H_prod.
  2: { rewrite <- sqrt_mult.
       - f_equal; field; repeat split; try apply Rgt_not_eq; auto.
       - apply Rmult_le_pos; [apply Rlt_le; exact Hn1x_pos | apply Rlt_le; apply Rinv_0_lt_compat; exact Hn2x_pos].
       - apply Rmult_le_pos; [apply Rlt_le; exact Hn1y_pos | apply Rlt_le; apply Rinv_0_lt_compat; exact Hn2y_pos]. }

  unfold B1, B2, D1, D2 in H_prod.
  replace (M * (INR n2x - INR n1x) * (M * (INR n2y - INR n1y)))
    with (M * M * (INR n2x - INR n1x) * (INR n2y - INR n1y)) in H_prod by ring.
  replace (D1 * D2) with ((sqrt (INR c) - 1) * (sqrt (INR c) - 1)) in H_prod by reflexivity.

  exact H_prod.
Qed.

(* 定理：逐点自适应分母不等式 *)
Theorem pointwise_adaptive_denom :
  forall (c : nat) (f : R -> R),
    (c >= 2)%nat ->
    (forall x, x >= 2 -> 0 < f x < INR c - 1) ->
    forall (n1 n2 : nat),
      (n1 >= 2)%nat ->
      INR n2 >= (INR c)^2 * INR n1 ->
      let eps := f (INR n1) in
      let M := INR c * INR c / (1 + eps) in
      sqrt (INR n1 * INR n2) / (M * (INR n2 - INR n1)) <=
      sqrt (INR n1 / INR n2) / (sqrt (INR c) - 1).
Proof.
  intros c f Hc Hf_bound n1 n2 Hn1 Hineq eps M.
  assert (Heps_range : 0 < eps < INR c - 1).
  { unfold eps; apply Hf_bound.
    apply Rle_ge.
    change 2 with (INR 2).
    apply le_INR.
    exact Hn1. }
  destruct Heps_range as [Heps_pos Heps_lt].
  assert (Hsq : INR n2 >= INR c * INR c * INR n1).
  { rewrite <- Rsqr_pow2 in Hineq; exact Hineq. }
  apply (intermediate_inequality_from_sparse_const c n1 n2 eps Hc Heps_pos Heps_lt Hn1 Hsq).
Qed.

(* ==================================================== *)
(* 概率版的确定性组合版本                                *)
(* ==================================================== *)

(* 定义：索引子集 I 是 c-稀疏的 *)
Definition c_sparse_subset (f : nat -> nat) (c : nat) (I : list nat) : Prop :=
  NoDup I /\
  forall (i j : nat),
    (i < length I)%nat -> (j < length I)%nat -> (i < j)%nat ->
    (INR (f (nth j I 0%nat)) >= INR c * INR c * INR (f (nth i I 0%nat)))%R.

(* 稀疏子集元素保底二 *)
Lemma c_sparse_subset_ge2 :
  forall (c : nat) (f : nat -> nat) (I : list nat),
    (c >= 2)%nat ->
    (forall i, (f i >= 2)%nat) ->
    c_sparse_subset f c I ->
    forall i, (i < length I)%nat -> (f (nth i I 0%nat) >= 2)%nat.
Proof.
  intros. apply H0.
Qed.

(* 稀疏子集项严格递增 *)
Lemma c_sparse_subset_lt :
  forall (c : nat) (f : nat -> nat) (I : list nat) (i j : nat),
    (c >= 2)%nat ->
    (forall k, (f k >= 2)%nat) ->
    c_sparse_subset f c I ->
    (i < length I)%nat -> (j < length I)%nat -> (i < j)%nat ->
    (f (nth i I 0%nat) < f (nth j I 0%nat))%nat.
Proof.
  intros c f I i j Hc Hf_ge2 Hsparse Hi Hj Hij.
  destruct Hsparse as [Hnodup Hineq].
  apply INR_lt.
  assert (Hf_pos : 0 < INR (f (nth i I 0%nat))).
  { apply lt_0_INR. specialize (Hf_ge2 (nth i I 0%nat)). lia. }
  assert (H_1_lt_c2 : 1 < INR c * INR c).
  { replace 1 with (INR 1) by (simpl; ring).
    apply Rlt_le_trans with 4.
    - simpl; lra.
    - assert (2 <= INR c). 
      { change 2 with (INR 2). apply le_INR. lia. }
      replace 4 with (2 * 2) by ring.
      apply Rmult_le_compat; lra. }
  apply Rlt_le_trans with (INR c * INR c * INR (f (nth i I 0%nat))).
  - rewrite <- Rmult_1_l at 1.
    apply Rmult_lt_compat_r; [exact Hf_pos | exact H_1_lt_c2].
  - apply Rge_le. apply Hineq; assumption.
Qed.

(* 共轭复数零元 *)
Lemma Cconj_0 : Cconj C0 = C0.
Proof.
  unfold Cconj, C0; simpl.
  apply Complex_eq; simpl; ring.
Qed.

(* 截断大指标处为零的内积求和 *)
Lemma Csum_psi_conj_truncate :
  forall (n_large n_small : nat),
    (n_small >= 1)%nat -> (n_large >= 1)%nat ->
    (n_small < n_large)%nat ->
    psi n_large (n_small - 1) *c Cconj (psi n_small (n_small - 1)) = C0 ->
    Csum (fun k => psi n_large k *c Cconj (psi n_small k)) (n_large - 1) =
    Csum (fun k => psi n_large k *c Cconj (psi n_small k)) (n_small - 1).
Proof.
  intros n_large n_small Hsmall_ge1 Hlarge_ge1 Hlt Hzero.
  set (f := fun k => psi n_large k *c Cconj (psi n_small k)).

  assert (Hsplit : (n_large - 1 = (n_small - 1) + (n_large - n_small))%nat) by lia.
  rewrite Hsplit.
  rewrite (Csum_split' f (n_small - 1)%nat (n_large - n_small)%nat).

  enough (Csum (fun i => f (n_small - 1 + i)%nat) (n_large - n_small)%nat = C0) as ->.
  - rewrite Cadd_0_r. reflexivity.
  - clear - Hsmall_ge1 Hlt Hzero.
    induction (n_large - n_small)%nat as [| d IH].
    + simpl. reflexivity.
    + simpl. rewrite IH, Cadd_0_l.
      unfold f.
      destruct d as [|d'] eqn:Hd.
      * simpl.
        rewrite Nat.add_0_r.
        exact Hzero.
      * assert (Hk_small : (n_small - 1 + S d' >= n_small)%nat) by lia.
        assert (H_phi_small : phi n_small (n_small - 1 + S d') = C0).
        { unfold phi. rewrite (proj2 (Nat.ltb_ge _ _) Hk_small). reflexivity. }
        assert (H_psi_small : psi n_small (n_small - 1 + S d') = C0).
        { unfold psi. rewrite H_phi_small. apply Cmul_0_r. }
        simpl. rewrite H_psi_small.
        rewrite Cconj_0.
        rewrite Cmul_0_r.
        reflexivity.
Qed.

(* 定理：确定性稀疏内积界 *)
Theorem deterministic_sparse_inner_bound :
  forall (c : nat) (f : nat -> nat),
    (c >= 2)%nat ->
    (forall i, (f i >= 2)%nat) ->
    (forall i, (INR (f (S i)) >= INR c * INR c * INR (f i))%R) ->
    forall (I : list nat),
      c_sparse_subset f c I ->
      forall (i j : nat),
        (i < length I)%nat -> (j < length I)%nat -> i <> j ->
        let n_small := min (f (nth i I 0%nat)) (f (nth j I 0%nat)) in
        let n_large := max (f (nth i I 0%nat)) (f (nth j I 0%nat)) in
        (Cnorm (Csum (fun k => psi n_small k *c Cconj (psi n_large k)) (n_small - 1)%nat) <=
         INR c * sqrt (INR n_small * INR n_large) / (4 * (INR n_large - INR n_small)))%R.
Proof.
  intros c f Hc Hf_ge2 Hf_growth I [Hnodup Hineq] i j Hi Hj Hneq.
  pose (ni := f (nth i I 0%nat)).
  pose (nj := f (nth j I 0%nat)).
  assert (Hni_ge2 : (ni >= 2)%nat) by apply Hf_ge2.
  assert (Hnj_ge2 : (nj >= 2)%nat) by apply Hf_ge2.

  destruct (Nat.lt_trichotomy i j) as [Hij | [Hij_eq | Hji]].
  - assert (H_ineq : INR nj >= INR c * INR c * INR ni) by (apply Hineq; auto).
    assert (Hlt : (ni < nj)%nat). {
      apply (c_sparse_subset_lt c f I i j Hc Hf_ge2).
      - split; assumption.
      - exact Hi.
      - exact Hj.
      - exact Hij.
    }
    simpl min; simpl max.
    rewrite Nat.min_l by lia.
    rewrite Nat.max_r by lia.
    apply inner_product_norm_bound_general_corrected with (c := c); auto.
  - exfalso; apply Hneq; assumption.
  - assert (H_ineq : INR ni >= INR c * INR c * INR nj) by (apply Hineq; auto).
    assert (Hlt : (nj < ni)%nat). {
      apply (c_sparse_subset_lt c f I j i Hc Hf_ge2).
      - split; assumption.
      - exact Hj.
      - exact Hi.
      - exact Hji.
    }
    simpl min; simpl max.
    rewrite Nat.min_r by lia.
    rewrite Nat.max_l by lia.
    apply inner_product_norm_bound_general_corrected with (c := c); auto.
Qed.

End UnconditionalBasisLemmas.
Export UnconditionalBasisLemmas.


(* ===== 紧化手术：全和内积紧界（n1 项）===== *)
Lemma inner_expand_full :
  forall n1 n2 : nat,
    (n1 >= 2)%nat -> (n2 >= 2)%nat -> (n1 <= n2)%nat ->
    Csum (fun k => psi n1 k *c Cconj (psi n2 k)) n1 =
    (Cof_real (1 / sqrt (INR n1)) *c Cof_real (1 / sqrt (INR n2))) *c
    Csum (fun k => Cexp (0 +i (INR k * (2 * PI * (1 / INR n1 - 1 / INR n2))))) n1.
Proof.
  intros n1 n2 Hn1_ge2 Hn2_ge2 Hn1_le_n2.

  assert (Cconj_mul : forall a b : Complex, Cconj (a *c b) = Cconj a *c Cconj b).
  {
    intros [x y] [u v].
    unfold Cconj, Cmul.
    simpl.
    apply Complex_eq; simpl; ring.
  }

  assert (Cconj_Cof_real : forall r : R, Cconj (Cof_real r) = Cof_real r).
  {
    intros r.
    unfold Cof_real, Cconj.
    simpl.
    apply Complex_eq; simpl; ring.
  }

  assert (Cconj_exp_iθ : forall θ : R, Cconj (Cexp (0 +i θ)) = Cexp (0 +i (Ropp θ))).
  {
    intros θ.
    unfold Cexp, Cconj.
    simpl.
    rewrite cos_neg, sin_neg.
    simpl.
    apply Complex_eq; simpl; ring.
  }

  assert (Cadd_pure_imag : forall θ1 θ2 : R, (0 +i θ1) +c (0 +i θ2) = (0 +i (θ1 + θ2))).
  {
    intros θ1 θ2.
    unfold Cadd.
    simpl.
    apply Complex_eq; simpl; ring.
  }

  assert (Cexp_mul_i : forall θ1 θ2 : R,
    Cexp (0 +i θ1) *c Cexp (0 +i θ2) = Cexp (0 +i (θ1 + θ2))).
  {
    intros θ1 θ2.
    rewrite <- Cexp_add.
    rewrite Cadd_pure_imag.
    reflexivity.
  }

  assert (Csum_scal_l : forall (c : Complex) (f : nat -> Complex) (n : nat),
    Csum (fun k => c *c f k) n = c *c Csum f n).
  {
    intros c f n.
    induction n as [|n IH].
    - simpl; rewrite Cmul_0_r; reflexivity.
    - simpl; rewrite IH, Cmul_add_distr_l; reflexivity.
  }

  assert (Csum_ext' : forall (f g : nat -> Complex) (n : nat),
    (forall i, (i < n)%nat -> f i = g i) -> Csum f n = Csum g n).
  {
    induction n as [|n IH]; intros H.
    - simpl; reflexivity.
    - simpl; rewrite IH; [f_equal; apply H; lia | intros; apply H; lia].
  }

  assert (H_phi_n1 : forall k : nat, (k < n1)%nat ->
    phi n1 k = Cexp (0 +i (2 * PI * INR k / INR n1))).
  {
    intros k Hk.
    unfold phi.
    assert (Hltb1 : (k <? n1) = true) by (apply Nat.ltb_lt; exact Hk).
    rewrite Hltb1.
    reflexivity.
  }

  assert (H_phi_n2 : forall k : nat, (k < n1)%nat ->
    phi n2 k = Cexp (0 +i (2 * PI * INR k / INR n2))).
  {
    intros k Hk.
    unfold phi.
    assert (Hk_lt_n2 : (k < n2)%nat) by lia.
    assert (Hltb2 : (k <? n2) = true) by (apply Nat.ltb_lt; exact Hk_lt_n2).
    rewrite Hltb2.
    reflexivity.
  }

  assert (H_INR_n1_nonzero : INR n1 <> 0).
  {
    apply Rgt_not_eq, lt_0_INR.
    lia.
  }
  assert (H_INR_n2_nonzero : INR n2 <> 0).
  {
    apply Rgt_not_eq, lt_0_INR.
    lia.
  }

  assert (H_sqrt_n1_nonzero : sqrt (INR n1) <> 0).
  {
    apply Rgt_not_eq.
    apply sqrt_lt_R0_c.
    apply lt_0_INR.
    lia.
  }
  assert (H_sqrt_n2_nonzero : sqrt (INR n2) <> 0).
  {
    apply Rgt_not_eq.
    apply sqrt_lt_R0_c.
    apply lt_0_INR.
    lia.
  }

  assert (H_theta_eq : forall k : nat,
    2 * PI * INR k / INR n1 + Ropp (2 * PI * INR k / INR n2) =
    INR k * (2 * PI * (1 / INR n1 - 1 / INR n2))).
  {
    intros k.
    field.
    all: auto.
  }

  assert (Cmul_assoc : forall a b c : Complex, (a *c b) *c c = a *c (b *c c)).
  {
    intros [x1 y1] [x2 y2] [x3 y3].
    unfold Cmul, Cadd.
    simpl.
    apply Complex_eq; simpl; ring.
  }

  assert (Cmul_comm : forall a b : Complex, a *c b = b *c a).
  {
    intros [x1 y1] [x2 y2].
    unfold Cmul.
    simpl.
    apply Complex_eq; simpl; ring.
  }

  assert (H_term_eq : forall k : nat, (k < n1)%nat ->
    psi n1 k *c Cconj (psi n2 k) =
    (Cof_real (1 / sqrt (INR n1)) *c Cof_real (1 / sqrt (INR n2))) *c
    Cexp (0 +i (INR k * (2 * PI * (1 / INR n1 - 1 / INR n2))))).
  {
    intros k Hk.
    set (c1 := Cof_real (1 / sqrt (INR n1))).
    set (c2 := Cof_real (1 / sqrt (INR n2))).
    set (phi1 := phi n1 k).
    set (phi2 := phi n2 k).

    assert (H_psi1 : psi n1 k = c1 *c phi1) by reflexivity.
    assert (H_psi2 : psi n2 k = c2 *c phi2) by reflexivity.
    rewrite H_psi1, H_psi2.
    rewrite Cconj_mul.
    assert (Hc2_conj : Cconj c2 = c2) by (unfold c2; apply Cconj_Cof_real).
    rewrite Hc2_conj.

    assert (Hk_lt_n1 : (k < n1)%nat) by lia.
    assert (Hphi1_eq : phi1 = Cexp (0 +i (2 * PI * INR k / INR n1)))
      by (unfold phi1; apply H_phi_n1; exact Hk_lt_n1).
    assert (Hphi2_eq : phi2 = Cexp (0 +i (2 * PI * INR k / INR n2)))
      by (unfold phi2; apply H_phi_n2; exact Hk_lt_n1).
    assert (Hconj_phi2 : Cconj phi2 = Cexp (0 +i - (2 * PI * INR k / INR n2)))
      by (rewrite Hphi2_eq; apply Cconj_exp_iθ).

    assert (Hphi_mul : phi1 *c Cconj phi2 = Cexp (0 +i (INR k * (2 * PI * (1 / INR n1 - 1 / INR n2))))).
    {
      rewrite Hphi1_eq, Hconj_phi2.
      rewrite Cexp_mul_i.
      rewrite H_theta_eq.
      reflexivity.
    }

    assert (Hmul_rearrange : (c1 *c phi1) *c (c2 *c Cconj phi2) = (c1 *c c2) *c (phi1 *c Cconj phi2)).
    {
      rewrite Cmul_assoc.
      assert (Htmp : phi1 *c (c2 *c Cconj phi2) = c2 *c (phi1 *c Cconj phi2)).
      {
        rewrite <- Cmul_assoc.
        rewrite (Cmul_comm phi1 c2).
        rewrite Cmul_assoc.
        reflexivity.
      }
      rewrite Htmp.
      rewrite <- Cmul_assoc.
      reflexivity.
    }

    rewrite Hmul_rearrange.
    rewrite Hphi_mul.
    reflexivity.
  }

  assert (H_sum_eq : Csum (fun k => psi n1 k *c Cconj (psi n2 k)) n1 =
    Csum (fun k => (Cof_real (1 / sqrt (INR n1)) *c Cof_real (1 / sqrt (INR n2))) *c
      Cexp (0 +i (INR k * (2 * PI * (1 / INR n1 - 1 / INR n2))))) n1).
  {
    apply Csum_ext'.
    intros i Hi.
    apply H_term_eq.
    exact Hi.
  }

  rewrite H_sum_eq.
  rewrite Csum_scal_l.
  reflexivity.
Qed.

Lemma inner_geometric_expansion_full :
  forall n1 n2,
    (n1 >= 2)%nat -> (n2 >= 2)%nat -> (n1 <= n2)%nat ->
  let θ := 2 * PI * (1 / INR n1 - 1 / INR n2) in
  Csum (fun k => psi n1 k *c Cconj (psi n2 k)) n1 =
    (Cof_real (1 / sqrt (INR n1)) *c Cof_real (1 / sqrt (INR n2))) *c
    Csum (fun k => Cexp (0 +i (INR k * θ))) n1.
Proof.
  intros n1 n2 H1 H2 Hle.
  apply inner_expand_full; auto.
Qed.

Theorem inner_product_norm_bound_full :
  forall (n1 n2 : nat),
    (n1 >= 2)%nat -> (n2 >= 2)%nat -> (n1 < n2)%nat ->
    Cnorm (Csum (fun k => psi n1 k *c Cconj (psi n2 k)) n1) <=
    sqrt (INR n1 * INR n2) / (2 * (INR n2 - INR n1)).
Proof.
  intros n1 n2 Hn1 Hn2 Hlt.
  set (θ := 2 * PI * (1 / INR n1 - 1 / INR n2)).

  assert (H_exp : Csum (fun k => psi n1 k *c Cconj (psi n2 k)) n1 =
          (Cof_real (1 / sqrt (INR n1)) *c Cof_real (1 / sqrt (INR n2))) *c
          Csum (fun k => Cexp (0 +i (INR k * θ))) n1).
  { apply inner_geometric_expansion_full; auto. lia. }
  rewrite H_exp.

  rewrite Cnorm_mult, (Cnorm_mult (Cof_real (1 / sqrt (INR n1))) (Cof_real (1 / sqrt (INR n2)))).

  assert (Hnorm1 : Cnorm (Cof_real (1 / sqrt (INR n1))) = 1 / sqrt (INR n1)).
  { unfold Cof_real, Cnorm, Cnorm_sq; simpl.
    unfold Rsqr; rewrite Rmult_0_l, Rplus_0_r.
    rewrite sqrt_square.
    - reflexivity.
    - unfold Rdiv; rewrite Rmult_1_l.
      apply Rlt_le, Rinv_0_lt_compat, sqrt_lt_R0_c, lt_0_INR; lia. }

  assert (Hnorm2 : Cnorm (Cof_real (1 / sqrt (INR n2))) = 1 / sqrt (INR n2)).
  { unfold Cof_real, Cnorm, Cnorm_sq; simpl.
    unfold Rsqr; rewrite Rmult_0_l, Rplus_0_r.
    rewrite sqrt_square.
    - reflexivity.
    - unfold Rdiv; rewrite Rmult_1_l.
      apply Rlt_le, Rinv_0_lt_compat, sqrt_lt_R0_c, lt_0_INR; lia. }

  rewrite Hnorm1, Hnorm2.
  
  assert (H_prod : 1 / sqrt (INR n1) * (1 / sqrt (INR n2)) = 1 / sqrt (INR n1 * INR n2)).
  { unfold Rdiv at 1 2; rewrite !Rmult_1_l.
    rewrite <- Rinv_mult.
    - rewrite <- sqrt_mult.
      + unfold Rdiv; rewrite Rmult_1_l; reflexivity.
      + apply Rlt_le; apply lt_0_INR; lia.
      + apply Rlt_le; apply lt_0_INR; lia.
   }
  rewrite H_prod.

  assert (Hz_neq1 : Cexp (0 +i θ) <> C1).
  { apply Cexp_diff_not_one; assumption. }

  assert (Hnorm_exp : Cnorm (Cexp (0 +i θ)) = 1).
  { unfold Cexp, Cnorm, Cnorm_sq; simpl.
    rewrite exp_0.
    rewrite !Rmult_1_l.
    rewrite Rplus_comm.
    rewrite sin2_cos2.
    apply sqrt_1. }

  assert (H_pow_eq : forall k, Cexp (0 +i (INR k * θ)) = (Cexp (0 +i θ) ^ k)%C).
  { intros k; induction k as [|k IH].
    - simpl. rewrite Rmult_0_l. apply Cexp_0_eq_1.
    - simpl Cexp.
      change (match k with 0%nat => 1 | S _ => INR k + 1 end) with (INR (S k)).
      rewrite S_INR.
      rewrite Rmult_plus_distr_r.
      rewrite Rmult_1_l.
      replace (0 +i (INR k * θ + θ)) with ((0 +i (INR k * θ)) +c (0 +i θ)).
      2: { unfold Cadd; simpl. f_equal; ring. }
      rewrite Cexp_add.
      rewrite IH.
      simpl. rewrite Cmul_comm. reflexivity. }

  rewrite (Csum_ext' _ (fun k => (Cexp (0 +i θ) ^ k)%C) n1).
  2: { intros; apply H_pow_eq. }

  pose proof (geometric_sum_norm_bound (Cexp (0 +i θ)) n1 Hz_neq1 Hnorm_exp) as H_geom_bound_raw.
  simpl in H_geom_bound_raw.

  assert (Hθ_bound : Rabs θ <= PI).
  { unfold θ. unfold Rdiv. rewrite !Rmult_1_l. apply theta_bound_pi; auto. lia. }
  assert (Hθ_neq0 : θ <> 0).
  { unfold θ. apply Rgt_not_eq.
    apply Rmult_gt_0_compat.
    - apply Rmult_lt_0_compat; [lra | apply PI_RGT_0].
    - unfold Rdiv; rewrite !Rmult_1_l.
      apply Rgt_minus.
      apply Rinv_lt_contravar with (r1 := INR n1) (r2 := INR n2).
      + apply Rmult_lt_0_compat; apply lt_0_INR; lia.
      + apply lt_INR; exact Hlt. }
  assert (H_abs_θ_pos : 0 < Rabs θ) by (apply Rabs_pos_lt; exact Hθ_neq0).

  assert (H_inv_denom : / Cnorm (C1 -c Cexp (0 +i θ)) <= PI / (2 * Rabs θ)).
  {
    replace (PI / (2 * Rabs θ)) with (/ (2 * Rabs θ / PI)).
    2: { field; split; [apply Rgt_not_eq; lra | apply Rgt_not_eq, PI_RGT_0]. }
    apply Rinv_le_contravar.
    - apply Rdiv_lt_0_compat.
      + apply Rmult_lt_0_compat; [lra | exact H_abs_θ_pos].
      + apply PI_RGT_0.
    - apply Rge_le.
      apply denom_lower_bound; assumption.
  }

  assert (H_scale_pos : 0 < 1 / sqrt (INR n1 * INR n2)).
  { apply Rdiv_lt_0_compat.
    - lra.
    - apply sqrt_lt_R0_c; apply Rmult_lt_0_compat; apply lt_0_INR; lia. }
  assert (H_scale_nonneg : 0 <= 1 / sqrt (INR n1 * INR n2))
    by (apply Rlt_le; exact H_scale_pos).

  apply Rmult_le_compat_l with (r := 1 / sqrt (INR n1 * INR n2)) in H_geom_bound_raw;
    [| exact H_scale_nonneg].

  assert (H_right_bound : 
    1 / sqrt (INR n1 * INR n2) * (2 / Cnorm (C1 -c Cexp (0 +i θ))) <=
    1 / sqrt (INR n1 * INR n2) * (2 * (PI / (2 * Rabs θ)))).
  {
    apply Rmult_le_compat_l.
    - exact H_scale_nonneg.
    - replace (2 / Cnorm (C1 -c Cexp (0 +i θ))) 
        with (2 * (/ Cnorm (C1 -c Cexp (0 +i θ)))) 
        by (unfold Rdiv; reflexivity).
      replace (2 * (PI / (2 * Rabs θ))) 
        with (2 * (PI * / (2 * Rabs θ))) 
        by (unfold Rdiv; reflexivity).
      apply Rmult_le_compat_l; [lra |].
      replace (/ (2 * Rabs θ) * PI) with (PI * / (2 * Rabs θ)) by ring.
      exact H_inv_denom.
  }

  apply Rle_trans with (1 / sqrt (INR n1 * INR n2) * (2 / Cnorm (C1 -c Cexp (0 +i θ)))).
  - exact H_geom_bound_raw.
  - apply Rle_trans with (1 / sqrt (INR n1 * INR n2) * (2 * (PI / (2 * Rabs θ)))).
    + exact H_right_bound.
    + apply algebraic_bound_step_final; auto.
Qed.

