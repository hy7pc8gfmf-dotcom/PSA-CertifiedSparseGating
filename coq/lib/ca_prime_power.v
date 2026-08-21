(* 拆分自 Riemann_Hypothesis_Proof_Framework.v（复分析证明库 v6.0）*)
(* 库: ca_prime_power  原文行区间: 25248-25793  机械拆分，未改动内容 *)

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

Require Import ca_base ca_algebra ca_primes ca_complex_analysis ca_fourier ca_zeta_scaffold ca_trig ca_gamma ca_taylor ca_zeta_axioms ca_complex_log ca_complex_foundation ca_log_bounds ca_independence.

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

(* ====================================================
   模块：PrimePowerIndependent
   目的：质数幂特征序列的线性无关性定理
   基于：NewTheorems.phi_linear_independent
   作者：王宝军（根据叙述生成）
   ==================================================== *)

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

Module PrimePowerIndependent.

(* ---------- 质数幂类型 ---------- *)
(* 一个质数幂由质数 p 和指数 t (t >= 1) 构成 *)
Record prime_power : Type := mk_prime_power {
  prime_of : Prime;
  expo : nat;
  expo_pos : (expo > 0)%nat   (* 使用 %nat 注解，强制 nat 比较 *)
}.

(* 质数幂的数值：p^t *)
Definition prime_power_value (q : prime_power) : nat :=
  (prime_value (prime_of q)) ^ (expo q).

(* 默认质数幂（用于 nth 的默认值）*)
Definition default_prime_power : prime_power :=
  mk_prime_power prime_2 1 (Nat.lt_0_succ 0).

(* ---------- 质数幂特征序列 ---------- *)
Definition prime_power_characteristic_sequence (q : prime_power) (k : nat) : Complex :=
  let n := prime_power_value q in
  if Nat.ltb k n then
    Cexp (0 +i (2 * PI * INR k / INR n))
  else C0.

(* ---------- 辅助引理 ---------- *)

(* 质数幂值至少为二 *)
Lemma prime_power_value_ge_2 : forall q, (prime_power_value q >= 2)%nat.
Proof.
  intros [p t Ht].
  unfold prime_power_value.
  apply Nat.le_trans with (prime_value p).
  - apply prime_value_ge_2.
  - destruct t as [|t'].
    + inversion Ht.
    + simpl.
      rewrite Nat.mul_comm.
      apply Nat.le_mul_l.
      apply Nat.pow_nonzero.
      apply Nat.neq_0_lt_0.
      apply Nat.lt_le_trans with (2%nat); [lia | apply prime_value_ge_2].
Qed.

(* 质数幂数值为正 *)
Lemma prime_power_value_pos : forall q, (0 < prime_power_value q)%nat.
Proof.
  intros q. apply Nat.lt_le_trans with (2%nat); [lia | apply prime_power_value_ge_2].
Qed.

(* 质数幂特征序列非零引理 *)
Lemma prime_power_characteristic_nonzero : forall q k,
  (k < prime_power_value q)%nat ->
  prime_power_characteristic_sequence q k <> C0.
Proof.
  intros q k Hlt.
  unfold prime_power_characteristic_sequence.
  assert (Hltb : (k <? prime_power_value q)%nat = true).
  { apply Nat.ltb_lt. exact Hlt. }
  rewrite Hltb.
  apply Cexp_neq_0.
Qed.

(* 质数幂特征序列末项非零引理 *)
Lemma prime_power_characteristic_pred_nonzero : forall q,
  prime_power_characteristic_sequence q (prime_power_value q - 1) <> C0.
Proof.
  intros q.
  set (n := prime_power_value q).
  assert (Hn_ge2 : (2 <= n)%nat) by apply prime_power_value_ge_2.
  assert (Hk_lt_n : (n - 1 < n)%nat) by lia.
  apply prime_power_characteristic_nonzero; exact Hk_lt_n.
Qed.

(* 质数幂列表中最大值的索引存在性 *)
Lemma max_prime_power_index_exists : forall (q_list : list prime_power),
  q_list <> nil ->
  exists i0, (i0 < length q_list)%nat /\
    (forall j, (j < length q_list)%nat ->
      (prime_power_value (nth j q_list default_prime_power) <=
       prime_power_value (nth i0 q_list default_prime_power))%nat).
Proof.
  intros q_list Hnonnil.
  set (vals := map prime_power_value q_list).
  set (max_val := fold_right Init.Nat.max 0%nat vals).
  assert (In max_val vals).
  { apply max_fold_right_in. destruct q_list; [contradiction | simpl; discriminate]. }
  apply in_map_iff in H as [q [Hq Hin]].
  assert (exists i, nth i q_list default_prime_power = q /\ (i < length q_list)%nat) as H_idx.
  { clear - Hin. induction q_list as [|h t IH]; [inversion Hin |].
    destruct Hin as [Heq|Hin'].
    - subst h. exists 0%nat. split; [reflexivity | simpl; lia].
    - destruct (IH Hin') as [i [Heq' Hi]]. exists (S i). split; [simpl; rewrite Heq'; reflexivity | simpl; lia]. }
  destruct H_idx as [i0 [Heq_i0 Hi0]].
  exists i0. split; [exact Hi0 |].
  intros j Hj.
  rewrite Heq_i0.
  assert (H_in_vals : In (prime_power_value (nth j q_list default_prime_power)) vals).
  { apply in_map_iff. exists (nth j q_list default_prime_power). split; [reflexivity | apply nth_In; auto]. }
  apply Nat.le_trans with max_val.
  - apply fold_right_max_ge with (l := vals); exact H_in_vals.
  - rewrite Hq; apply Nat.le_refl.
Qed.

(* 无重复质数幂列表中，不同索引对应不同数值 *)
Lemma NoDup_nth_neq_pp : forall (l : list prime_power) (i j : nat),
  NoDup (map prime_power_value l) ->
  (i < length l)%nat -> (j < length l)%nat -> i <> j ->
  prime_power_value (nth i l default_prime_power) <> prime_power_value (nth j l default_prime_power).
Proof.
  intros l i j Hdup Hi Hj Hneq.
  assert (Heq : nth i (map prime_power_value l) (prime_power_value default_prime_power) =
                nth j (map prime_power_value l) (prime_power_value default_prime_power) ->
                i = j).
  { apply NoDup_nth with (A := nat) (l := map prime_power_value l) (d := prime_power_value default_prime_power); auto.
    - rewrite length_map; exact Hi.
    - rewrite length_map; exact Hj. }
  intro Hcontra.
  apply Hneq.
  apply Heq.
  rewrite !map_nth; simpl.
  exact Hcontra.
Qed.

(* 最大值严格不等式 *)
Lemma max_prime_power_strict_ineq : forall (q_list : list prime_power) (i0 : nat),
  NoDup (map prime_power_value q_list) ->
  (i0 < length q_list)%nat ->
  (forall j, (j < length q_list)%nat ->
    (prime_power_value (nth j q_list default_prime_power) <=
     prime_power_value (nth i0 q_list default_prime_power))%nat) ->
  forall j, j <> i0 -> (j < length q_list)%nat ->
    (prime_power_value (nth j q_list default_prime_power) <
     prime_power_value (nth i0 q_list default_prime_power))%nat.
Proof.
  intros q_list i0 Hdup Hi0 Hmax j Hneq Hj.
  specialize (Hmax j Hj).
  destruct (Nat.lt_ge_cases (prime_power_value (nth j q_list default_prime_power))
                            (prime_power_value (nth i0 q_list default_prime_power))) as [Hlt|Hge].
  - exact Hlt.
  - assert (Heq : prime_power_value (nth j q_list default_prime_power) =
                  prime_power_value (nth i0 q_list default_prime_power)) by lia.
    exfalso.
    pose proof (NoDup_nth_neq_pp q_list j i0 Hdup Hj Hi0 Hneq) as Hneq_val.
    rewrite Heq in Hneq_val.
    contradiction.
Qed.

(* 对于非最大质数幂，在 k = M-1 处特征序列为零 *)
Lemma term_zero_for_others_pp : forall (q_list : list prime_power) (coeffs : list Complex) (i0 : nat),
  (forall j, (j < length q_list)%nat ->
    (prime_power_value (nth j q_list default_prime_power) <=
     prime_power_value (nth i0 q_list default_prime_power))%nat) ->
  (forall j, j <> i0 -> (j < length q_list)%nat ->
    (prime_power_value (nth j q_list default_prime_power) <
     prime_power_value (nth i0 q_list default_prime_power))%nat) ->
  let M := prime_power_value (nth i0 q_list default_prime_power) in
  let k0 := (M - 1)%nat in
  forall j, (j < length q_list)%nat -> j <> i0 ->
    nth j coeffs C0 *c prime_power_characteristic_sequence (nth j q_list default_prime_power) k0 = C0.
Proof.
  intros q_list coeffs i0 Hle Hlt M k0 j Hj Hneq.
  unfold prime_power_characteristic_sequence.
  assert (Hlt_j : (prime_power_value (nth j q_list default_prime_power) < M)%nat) by (apply Hlt; auto).
  apply Nat.lt_le_pred in Hlt_j.
  assert (Hk0_ge : (k0 >= prime_power_value (nth j q_list default_prime_power))%nat).
  { apply Nat.le_trans with (Nat.pred M); [exact Hlt_j | unfold k0; lia]. }
  assert (Hfalse : (k0 <? prime_power_value (nth j q_list default_prime_power))%nat = false).
  { apply Nat.ltb_ge. assumption. }
  rewrite Hfalse.
  rewrite Cmul_0_r.
  reflexivity.
Qed.

(* 删除元素相关引理（复用 independent' 中的定义）*)
Definition removelist_pp (i : nat) (l : list prime_power) : list prime_power :=
  firstn i l ++ skipn (S i) l.

(* 删除元素后列表长度减一引理 *)
Lemma length_removelist_pp : forall (l : list prime_power) i,
  (i < length l)%nat -> length (removelist_pp i l) = pred (length l).
Proof.
  intros l i Hi. unfold removelist_pp.
  rewrite length_app, length_firstn, length_skipn.
  rewrite min_l by lia. lia.
Qed.

(* 删除元素前缀不变引理 *)
Lemma nth_removelist_lt_pp : forall (l : list prime_power) i j d,
  (i < length l)%nat -> (j < i)%nat ->
  nth j (removelist_pp i l) d = nth j l d.
Proof.
  intros l i j d Hi Hj.
  unfold removelist_pp.
  rewrite nth_app_left.
  - rewrite nth_firstn by lia.
    destruct (Nat.ltb_spec j i) as [Hlt|Hge].
    + reflexivity.
    + lia.  (* 因为 Hj 保证 j < i，所以 Hge 分支不可能，但 lia 可解决 *)
  - rewrite length_firstn. rewrite min_l by lia. lia.
Qed.

(* 质数幂列表删除元素后索引右移引理 *)
Lemma nth_removelist_ge_pp : forall (l : list prime_power) i j d,
  (i < length l)%nat -> (j >= i)%nat ->
  nth j (removelist_pp i l) d = nth (S j) l d.
Proof.
  intros l i j d Hi Hj. unfold removelist_pp.
  rewrite nth_app_right; [| rewrite length_firstn; rewrite min_l by lia; lia].
  rewrite nth_skipn.
  rewrite length_firstn, min_l by lia.
  replace (S i + (j - i))%nat with (S j) by lia.
  reflexivity.
Qed.

(* 约化系统保持无重复 *)
Lemma reduced_system_nodup_pp : forall (q_list : list prime_power) (i0 : nat),
  NoDup (map prime_power_value q_list) ->
  (i0 < length q_list)%nat ->
  NoDup (map prime_power_value (removelist_pp i0 q_list)).
Proof.
  intros q_list i0 Hdup Hi0.
  unfold removelist_pp.
  rewrite map_app, map_firstn, map_skipn.
  apply NoDup_remove_at with (A := nat) (l := map prime_power_value q_list) (i := i0).
  - exact Hdup.
  - rewrite length_map. exact Hi0.
Qed.

(* 约化系统长度保持 *)
Lemma reduced_system_length_pp : forall (q_list : list prime_power) (coeffs : list Complex) (i0 : nat),
  length q_list = length coeffs ->
  length (removelist_pp i0 q_list) = length (removelist Complex i0 coeffs).
Proof.
  intros q_list coeffs i0 Hlen.
  unfold removelist_pp, removelist.
  rewrite !length_app, !length_firstn, !length_skipn.
  rewrite Hlen.
  reflexivity.
Qed.

(* 约化系统的方程保持 *)
Lemma reduced_sum_eq_zero_pp :
  forall (q_list : list prime_power) (coeffs : list Complex) i0
    (Hlen : length q_list = length coeffs)
    (Hi0 : (i0 < length q_list)%nat)
    (Hc0 : nth i0 coeffs C0 = C0)
    (Heq : forall k,
        Csum (fun i => nth i coeffs C0 *c
                       prime_power_characteristic_sequence (nth i q_list default_prime_power) k)
             (length q_list) = C0),
    forall k,
    Csum (fun i =>
            let q := nth i (removelist_pp i0 q_list) default_prime_power in
            let c := nth i (removelist Complex i0 coeffs) C0 in
            c *c prime_power_characteristic_sequence q k)
         (length (removelist_pp i0 q_list)) = C0.
Proof.
  intros q_list coeffs i0 Hlen Hi0 Hc0 Heq k.
  set (N := length q_list).
  set (q_list' := removelist_pp i0 q_list).
  set (coeffs' := removelist Complex i0 coeffs).
  set (F := fun i => nth i coeffs C0 *c prime_power_characteristic_sequence (nth i q_list default_prime_power) k).
  set (G := fun i => let q := nth i q_list' default_prime_power in
                     let c := nth i coeffs' C0 in
                     c *c prime_power_characteristic_sequence q k).

  assert (Hlen_p' : length q_list' = pred N) by (apply length_removelist_pp; exact Hi0).
  rewrite Hlen_p'.

  specialize (Heq k).
  fold F in Heq.
  change (length q_list) with N in Heq.

  set (m := (N - i0)%nat) in *.
  assert (Hadd : N = (i0 + m)%nat) by lia.
  assert (Hm_pos : (1 <= m)%nat) by lia.
  assert (Hm_split : m = (1 + (m - 1))%nat) by lia.

  assert (Hsplit1 : Csum F (i0 + m)%nat = Csum F i0 +c Csum (fun j => F (i0 + j)%nat) m).
  { apply Csum_split'. }
  rewrite Hadd in Heq.
  rewrite Hsplit1 in Heq.

  assert (Hsplit2 : Csum (fun j => F (i0 + j)%nat) m =
                    Csum (fun j => F (i0 + j)%nat) 1 +c
                    Csum (fun i => F (i0 + (1 + i))%nat) (m - 1)).
  { rewrite Hm_split.
    rewrite (Csum_split' (fun j => F (i0 + j)%nat) 1 (m - 1)).
    replace (1 + (m - 1) - 1)%nat with (m - 1)%nat by lia.
    reflexivity. }
  rewrite Hsplit2 in Heq.

  assert (Hsum1_eq : Csum (fun j => F (i0 + j)%nat) 1 = F i0).
  { simpl. rewrite Nat.add_0_r. rewrite Cadd_0_l. reflexivity. }
  rewrite Hsum1_eq in Heq.

  assert (F_i0_zero : F i0 = C0).
  { unfold F. rewrite Hc0. apply Cmul_0_l. }
  rewrite F_i0_zero in Heq.
  rewrite Cadd_0_l in Heq.

  replace (pred N) with (i0 + (m - 1))%nat by (unfold N; lia).
  rewrite Csum_split'.

  (* 前缀相等 – 正确化简 *)
  assert (Hprefix : forall i, (i < i0)%nat -> G i = F i).
  { intros i Hi. unfold G, F, q_list', coeffs', removelist_pp, removelist.
    (* 处理 coeffs' *)
    rewrite (nth_app_left Complex (firstn i0 coeffs) (skipn (S i0) coeffs) i C0).
    - (* 处理 q_list' *)
      rewrite (nth_app_left prime_power (firstn i0 q_list) (skipn (S i0) q_list) i default_prime_power).
      + rewrite (nth_firstn_lt Complex i0 coeffs i C0 Hi).
        rewrite (nth_firstn_lt prime_power i0 q_list i default_prime_power Hi).
        reflexivity.
      + (* 证明 q_list 的索引条件 *)
        rewrite length_firstn.
        rewrite (Nat.min_l i0 (length q_list)).
        * lia.
        * apply lt_le_incl, Hi0.
    - (* 证明 coeffs 的索引条件 *)
      rewrite length_firstn.
      rewrite (Nat.min_l i0 (length coeffs)).
      * lia.
      * rewrite <- Hlen; apply lt_le_incl, Hi0. }

  (* 后缀相等 *)
  assert (Hsuffix : forall j, (j < m - 1)%nat -> G (i0 + j)%nat = F (i0 + 1 + j)%nat).
  { intros j Hj. unfold G, F, q_list', coeffs', removelist_pp, removelist.
    assert (Hlen_firstn_q : length (firstn i0 q_list) = i0).
    { rewrite length_firstn. apply Nat.min_l. lia. }
    assert (Hlen_firstn_c : length (firstn i0 coeffs) = i0).
    { rewrite length_firstn. apply Nat.min_l. rewrite <- Hlen; lia. }
    assert (Hge_q : (i0 + j >= length (firstn i0 q_list))%nat) by lia.
    assert (Hge_c : (i0 + j >= length (firstn i0 coeffs))%nat) by lia.
    rewrite (nth_app_right _ (firstn i0 q_list) (skipn (S i0) q_list) (i0 + j)%nat default_prime_power Hge_q).
    rewrite nth_skipn.
    rewrite Hlen_firstn_q.
    replace (i0 + j - i0)%nat with j by lia.
    rewrite (nth_app_right _ (firstn i0 coeffs) (skipn (S i0) coeffs) (i0 + j)%nat C0 Hge_c).
    rewrite nth_skipn.
    rewrite Hlen_firstn_c.
    replace (i0 + j - i0)%nat with j by lia.
    rewrite Nat.add_1_r.
    replace (S i0 + j)%nat with (i0 + 1 + j)%nat by lia.
    reflexivity. }

  (* 使用 Csum_ext' 证明前缀部分相等 *)
  assert (Heq1 : Csum G i0 = Csum F i0).
  { apply Csum_ext'. intros i Hi. apply Hprefix. exact Hi. }

  (* 使用 Csum_ext' 证明后缀部分相等 *)
  assert (Heq2 : Csum (fun j => G (i0 + j)%nat) (m - 1) = Csum (fun j => F (i0 + 1 + j)%nat) (m - 1)).
  { apply Csum_ext'. intros j Hj. rewrite Hsuffix; auto. }

  rewrite Heq1, Heq2.
  assert (Heq3 : Csum (fun j => F (i0 + 1 + j)%nat) (m - 1) = Csum (fun i => F (i0 + (1 + i))%nat) (m - 1)).
  { apply Csum_ext'. intros j Hj. f_equal. lia. }
  rewrite Heq3.
  exact Heq.
Qed.

(* 单点求和化简（与类型无关，直接复用 independent 中的 Csum_reduce_to_single）*)
Lemma Csum_reduce_to_single_pp : forall (f : nat -> Complex) (n : nat) (idx : nat),
  (idx < n)%nat ->
  (forall j, (j < n)%nat -> (j = idx -> f j = f idx) /\ (j <> idx -> f j = C0)) ->
  Csum f n = f idx.
Proof.
  exact Csum_reduce_to_single.
Qed.

(* 质数幂特征序列线性无关定理 *)
Theorem prime_power_phi_linear_independent :
  forall (q_list : list prime_power) (coeffs : list Complex),
    NoDup (map prime_power_value q_list) ->
    length q_list = length coeffs ->
    (forall k : nat,
        Csum (fun i =>
                let q := nth i q_list default_prime_power in
                let c := nth i coeffs C0 in
                c *c prime_power_characteristic_sequence q k)
             (length q_list) = C0) ->
    forall idx, (idx < length q_list)%nat -> nth idx coeffs C0 = C0.
Proof.
  assert (H_main : forall (n : nat),
    forall (q_list : list prime_power) (coeffs : list Complex),
      length q_list = n ->
      NoDup (map prime_power_value q_list) ->
      length q_list = length coeffs ->
      (forall k, Csum (fun i => nth i coeffs C0 *c
                         prime_power_characteristic_sequence (nth i q_list default_prime_power) k)
                      (length q_list) = C0) ->
      forall idx, (idx < length q_list)%nat -> nth idx coeffs C0 = C0).
  {
    intros n.
    induction n as [n IH] using lt_wf_ind.
    intros q_list coeffs Hlen_n Hdup Hlen Heq idx Hid.

    destruct n as [|m'].
    - simpl in Hlen_n. subst. simpl in Hid. lia.
    - assert (Hnonnil : q_list <> nil).
      { intro Hcontra. rewrite Hcontra in Hlen_n. simpl in Hlen_n. lia. }

      destruct (max_prime_power_index_exists q_list Hnonnil) as [i0 [Hi0_lt_m Hmax_le]].
      assert (Hmax_strict : forall j, j <> i0 -> (j < length q_list)%nat ->
        (prime_power_value (nth j q_list default_prime_power) <
         prime_power_value (nth i0 q_list default_prime_power))%nat).
      { apply max_prime_power_strict_ineq with (q_list:=q_list) (i0:=i0); auto. }

      set (M := prime_power_value (nth i0 q_list default_prime_power)).
      set (k0 := Nat.pred M).
      assert (Hk0_alt : k0 = (prime_power_value (nth i0 q_list default_prime_power) - 1)%nat).
      { unfold k0, M. assert (Hp_ge2 : (prime_power_value (nth i0 q_list default_prime_power) >= 2)%nat) by apply prime_power_value_ge_2. lia. }

      assert (Heq_k0 : Csum (fun i => nth i coeffs C0 *c
                               prime_power_characteristic_sequence (nth i q_list default_prime_power) k0)
                           (length q_list) = C0).
      { apply Heq. }

      set (f := fun j => nth j coeffs C0 *c prime_power_characteristic_sequence (nth j q_list default_prime_power) k0).

      assert (Hterm_zero : forall j, (j < length q_list)%nat -> j <> i0 -> f j = C0).
      { intros j Hj Hneq. unfold f. rewrite Hk0_alt.
        apply term_zero_for_others_pp with (q_list:=q_list) (coeffs:=coeffs) (i0:=i0); auto. }

      assert (Hsum_reduce : Csum f (length q_list) = f i0).
      {
        rewrite Hlen_n.
        apply Csum_reduce_to_single_pp with (f := f) (n := S m') (idx := i0).
        - rewrite Hlen_n in Hi0_lt_m. exact Hi0_lt_m.
        - intros j Hj. split.
          + intros ->. reflexivity.
          + intros Hneq. apply Hterm_zero; [rewrite Hlen_n; exact Hj | exact Hneq].
      }

      assert (Hfi0 : nth i0 coeffs C0 = C0).
      {
        assert (Hfi0_eq : f i0 = C0).
        { rewrite <- Hsum_reduce. exact Heq_k0. }
        unfold f in Hfi0_eq.
        assert (Hnonzero : prime_power_characteristic_sequence (nth i0 q_list default_prime_power) k0 <> C0).
        { rewrite Hk0_alt. apply prime_power_characteristic_pred_nonzero. }
        apply Cmult_zero_r_inv in Hfi0_eq; auto.
      }

      set (q_list' := removelist_pp i0 q_list).
      set (coeffs' := removelist Complex i0 coeffs).
      assert (Hlen' : length q_list' = length coeffs').
      { apply reduced_system_length_pp; auto. }
      assert (Hdup' : NoDup (map prime_power_value q_list')).
      { apply reduced_system_nodup_pp; [exact Hdup | exact Hi0_lt_m]. }

      assert (Hlen_lt : (length q_list' < length q_list)%nat).
      { unfold q_list', removelist_pp.
        rewrite length_app, length_firstn, length_skipn.
        rewrite Nat.min_l by lia. lia. }

      assert (Hlen_lt_Sm' : (length q_list' < S m')%nat).
      { rewrite Hlen_n in Hlen_lt. exact Hlen_lt. }
      assert (Hlen_p'_eq : length q_list' = pred (length q_list)).
      { apply length_removelist_pp. exact Hi0_lt_m. }

      assert (Heq' : forall k, Csum (fun i =>
                 let q := nth i q_list' default_prime_power in
                 let c := nth i coeffs' C0 in
                 c *c prime_power_characteristic_sequence q k) (length q_list') = C0).
      {
        intros k.
        apply reduced_sum_eq_zero_pp with (q_list:=q_list) (coeffs:=coeffs) (i0:=i0); auto.
      }

      assert (H_ind : forall j, (j < length q_list')%nat -> nth j coeffs' C0 = C0).
      {
        apply (IH (length q_list') Hlen_lt_Sm' q_list' coeffs' (eq_refl (length q_list')) Hdup' Hlen' Heq').
      }

      assert (Hi0_lt_len : (i0 < length q_list)%nat) by exact Hi0_lt_m.
      assert (Hi0_lt_coeffs : (i0 < length coeffs)%nat).
      { rewrite <- Hlen. exact Hi0_lt_len. }
      destruct (eq_nat_dec idx i0) as [->|Hne].
      + exact Hfi0.
      + destruct (lt_dec idx i0) as [Hlt | Hgt].
        * assert (Hi' : (idx < length q_list')%nat).
          { rewrite Hlen_p'_eq. lia. }
          assert (Hnth_eq : nth idx coeffs' C0 = nth idx coeffs C0).
          { unfold coeffs', removelist. apply nth_removelist_lt; auto. }
          rewrite <- Hnth_eq. apply H_ind; exact Hi'.
        * assert (Hineq : (idx > i0)%nat) by lia.
          assert (Hi' : ((idx - 1) < length q_list')%nat).
          { rewrite Hlen_p'_eq. lia. }
          assert (Hnth_eq : nth (idx - 1) coeffs' C0 = nth idx coeffs C0).
          {
            assert (Hj_ge_i0 : ((idx - 1) >= i0)%nat) by lia.
            assert (H_Sj_eq : S (idx - 1) = idx) by lia.
            assert (H_lemma : nth (idx - 1) coeffs' C0 = nth (S (idx - 1)) coeffs C0).
            {
              apply nth_removelist_ge with (A := Complex) (l := coeffs) (i := i0) (j := (idx - 1)%nat) (d := C0).
              - exact Hi0_lt_coeffs.
              - exact Hj_ge_i0.
            }
            rewrite H_lemma. rewrite H_Sj_eq. reflexivity.
          }
          rewrite <- Hnth_eq. apply H_ind; exact Hi'.
  }
  intros q_list coeffs Hdup Hlen Heq idx Hid.
  assert (Heq_simple : forall k,
    Csum (fun i => nth i coeffs C0 *c prime_power_characteristic_sequence (nth i q_list default_prime_power) k)
         (length q_list) = C0).
  { intros k.
    transitivity (Csum (fun i => let q := nth i q_list default_prime_power in
                                 let c := nth i coeffs C0 in
                                 c *c prime_power_characteristic_sequence q k)
                       (length q_list)).
    - apply Csum_ext'. intros i _. simpl. reflexivity.
    - apply Heq. }
  apply (H_main (length q_list) q_list coeffs (eq_refl (length q_list)) Hdup Hlen Heq_simple idx Hid).
Qed.

End PrimePowerIndependent.

Export PrimePowerIndependent.
