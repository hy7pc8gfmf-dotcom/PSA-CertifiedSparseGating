(* 拆分自 Riemann_Hypothesis_Proof_Framework.v（复分析证明库 v6.0）*)
(* 库: ca_probabilistic  原文行区间: 33544-36341  机械拆分，未改动内容 *)

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

Require Import ca_base ca_algebra ca_primes ca_complex_analysis ca_fourier ca_zeta_scaffold ca_trig ca_gamma ca_taylor ca_zeta_axioms ca_complex_log ca_complex_foundation ca_log_bounds ca_independence ca_prime_power ca_basis ca_basis_lemmas.

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

(* ==================================================== *)
(* 模块：ProbabilisticSparseBasis (构造性版本)           *)
(* 目的：将确定性稀疏内积界推广到概率版本              *)
(* ==================================================== *)
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lra.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.NArith.NArith.
Require Import Stdlib.Sorting.Sorted.
Require Import Stdlib.Reals.Reals.
Require Import Stdlib.Lists.List.
Import ListNotations.
Local Open Scope R_scope.

(* 导入确定性部分 *)
Import independent.
Import independent'.
Import UnconditionalBasisLemmas.

Module ProbabilisticSparseBasis.

(* 有限概率空间定义（基于组合权重） *)

(* 子集的权重 *)
Definition weight_of_subset (p : R) (N : nat) (I : list nat) : R :=
  p ^ (length I) * (1 - p) ^ (N - length I).

(* 所有子集的列表（至 n） *)
Fixpoint all_subsets_upto (n : nat) : list (list nat) :=
  match n with
  | 0 => [ [] ]
  | S n' => 
      let prev := all_subsets_upto n' in
      map (fun l => n' :: l) prev ++ prev
  end.

(* 所有子集的列表 *)
Definition all_subsets (N : nat) : list (list nat) := all_subsets_upto N.

(* 按权重求和（布尔谓词版） *)
Definition sum_over_subsets_weight (p : R) (N : nat) (P : list nat -> bool) : R :=
  List.fold_right Rplus 0%R
    (List.map (fun I => if P I then weight_of_subset p N I else 0%R)
              (all_subsets N)).

(* 布尔谓词：坏事件与稀疏性检测 *)
Section BooleanPredicates.
  Variable (c : nat) (f : nat -> nat).

(* 实数小于比较（构造性） *)
Definition Rlt_bool (r1 r2 : R) : bool :=
  if Rlt_dec r1 r2 then true else false.

(* 实数大于等于比较（构造性） *)
Definition Rge_bool (r1 r2 : R) : bool :=
  if Rle_dec r2 r1 then true else false.

(* 实数小于判定等价 *)
Lemma Rlt_bool_lt : forall r1 r2, Rlt_bool r1 r2 = true <-> r1 < r2.
Proof.
  intros r1 r2; unfold Rlt_bool; destruct Rlt_dec; split; intro H; auto; discriminate.
Qed.

(* 实数大于等于判定等价 *)
Lemma Rge_bool_ge : forall r1 r2, Rge_bool r1 r2 = true <-> r1 >= r2.
Proof.
  intros r1 r2; unfold Rge_bool.
  destruct (Rle_dec r2 r1) as [Hle | Hnotle].
  - split; intro H; [apply Rle_ge; exact Hle | reflexivity].
  - split; intro H.
    + discriminate H.
    + exfalso; apply Hnotle; apply Rge_le; exact H.
Qed.

(* 判定一对索引是否为坏对 *)
Definition is_bad_pair_b (i j : nat) (I : list nat) : bool :=
  (i <? length I) && (j <? length I) && (i <? j) &&
  Rlt_bool (INR (f (nth j I 0%nat))) (INR c * INR c * INR (f (nth i I 0%nat))).

(* 稀疏条件（所有索引对都满足增长不等式） *)
Definition sparse_cond_b (I : list nat) : bool :=
  forallb (fun i => forallb (fun j =>
    if i <? j then
      Rge_bool (INR (f (nth j I 0%nat))) (INR c * INR c * INR (f (nth i I 0%nat)))
    else true
  ) (seq 0 (length I))) (seq 0 (length I)).

(* 坏事件判定（存在坏对） *)
Definition bad_event_b (I : list nat) : bool :=
  existsb (fun i => existsb (fun j => is_bad_pair_b i j I) (seq 0 (length I))) (seq 0 (length I)).

End BooleanPredicates.

Require Import Stdlib.Bool.Bool.

Section PairwiseInnerCondition.
  Variable (c : nat) (f : nat -> nat).

  (* 判定单对不等式：左 <= 右 等价于 右 >= 左 *)
  Definition check_pair (I : list nat) (i j : nat) : bool :=
    let fi := INR (f (nth i I 0%nat)) in
    let fj := INR (f (nth j I 0%nat)) in
    Rge_bool
      (sqrt (fi / fj) / (sqrt (INR c) - 1))          (* 右端 *)
      (sqrt (fi * fj) / (INR c * (fj - fi))).         (* 左端 *)

  (* 对所有 i<j<length I 检查 *)
  Definition pairwise_inner_condition_b (I : list nat) : bool :=
    forallb (fun i =>
      forallb (fun j =>
        if (i <? j) && (j <? length I) then check_pair I i j else true
      ) (seq 0 (length I))
    ) (seq 0 (length I)).



  (* 反射引理：布尔值为真 ↔ 原不等式成立 *)
Lemma pairwise_inner_condition_bP (I : list nat) :
  reflect
    (forall i j, (i < j)%nat -> (j < length I)%nat ->
      (sqrt (INR (f (nth i I 0%nat)) * INR (f (nth j I 0%nat))) /
       (INR c * (INR (f (nth j I 0%nat)) - INR (f (nth i I 0%nat)))) <=
       sqrt (INR (f (nth i I 0%nat)) / INR (f (nth j I 0%nat))) /
       (sqrt (INR c) - 1))%R)
    (pairwise_inner_condition_b I).
Proof.
  unfold pairwise_inner_condition_b.
  set (F := fun i : nat =>
    forallb (fun j : nat =>
      if (i <? j) && (j <? length I) then check_pair I i j else true)
      (seq 0 (length I))).
  remember (forallb F (seq 0 (length I))) as b eqn:Hb.
  destruct b.
  - (* b = true *)
    symmetry in Hb.
    destruct (forallb_forall F (seq 0 (length I))) as [Hforward _].
    specialize (Hforward Hb).
    apply ReflectT.
    intros i j Hij Hjlen.                                  (* 修正处 *)
    assert (Hi_in : In i (seq 0 (length I))) by (apply in_seq; lia).
    assert (Hj_in : In j (seq 0 (length I))) by (apply in_seq; lia).
    specialize (Hforward i Hi_in).
    unfold F in Hforward.
    destruct (forallb_forall (fun j : nat =>
      if (i <? j) && (j <? length I) then check_pair I i j else true)
      (seq 0 (length I))) as [Hinner_forward _].
    specialize (Hinner_forward Hforward).
    specialize (Hinner_forward j Hj_in).
    destruct ((i <? j) && (j <? length I)) eqn:Hcond.
    + apply andb_prop in Hcond as [Hij_bool Hjlen_bool].
      apply Nat.ltb_lt in Hij_bool.
      apply Nat.ltb_lt in Hjlen_bool.
      unfold check_pair in Hinner_forward.
      apply Rge_bool_ge in Hinner_forward.
      apply Rge_le in Hinner_forward.
      exact Hinner_forward.
    + exfalso.
      assert (Hij_true : (i <? j) = true) by (apply Nat.ltb_lt; exact Hij). (* 修正处 *)
      assert (Hjlen_true : (j <? length I) = true) by (apply Nat.ltb_lt; exact Hjlen). (* 修正处 *)
      rewrite Hij_true, Hjlen_true, Bool.andb_true_r in Hcond.
      discriminate.
  - (* b = false *)
    apply ReflectF.
    intro H.
    destruct (forallb_forall F (seq 0 (length I))) as [_ Hbackward].
    assert (Htrue : forallb F (seq 0 (length I)) = true).
    { apply Hbackward.
      intros i Hi_seq. apply in_seq in Hi_seq. destruct Hi_seq as [_ Hi_len].
      unfold F.
      destruct (forallb_forall (fun j : nat =>
        if (i <? j) && (j <? length I) then check_pair I i j else true)
        (seq 0 (length I))) as [_ Hinner_backward].
      apply Hinner_backward.
      intros j Hj_seq. apply in_seq in Hj_seq. destruct Hj_seq as [_ Hj_len].
      destruct ((i <? j) && (j <? length I)) eqn:Hcond.
      - apply andb_prop in Hcond as [Hij_bool Hj_len_bool].
        apply Nat.ltb_lt in Hij_bool.
        apply Nat.ltb_lt in Hj_len_bool.
        apply Rge_bool_ge.
        apply Rle_ge, H with (i:=i) (j:=j); assumption.
      - reflexivity. }
    rewrite Htrue in Hb. discriminate.
Qed.

End PairwiseInnerCondition.

Require Import Stdlib.Bool.Bool.

Section Equivalences.
  Variable (c : nat) (f : nat -> nat).

(* 坏事件布尔判定 *)
Lemma bad_event_bP (I : list nat) :
  reflect
    (exists i j, (i < length I)%nat /\ (j < length I)%nat /\ (i < j)%nat /\
                (INR (f (nth j I 0%nat)) < INR c * INR c * INR (f (nth i I 0%nat)))%R)
    (bad_event_b c f I).
Proof.
  unfold bad_event_b, is_bad_pair_b.
  remember (existsb (fun i => existsb (fun j =>
    (i <? length I) && (j <? length I) && (i <? j) &&
    Rlt_bool (INR (f (nth j I 0%nat))) (INR c * INR c * INR (f (nth i I 0%nat))))
    (seq 0 (length I))) (seq 0 (length I))) as b eqn:Hb.
  destruct b.
  - symmetry in Hb.
    apply ReflectT.
    apply existsb_exists in Hb as (i & Hi_seq & Hj_ex).
    apply in_seq in Hi_seq. destruct Hi_seq as [Hi_low Hi_high].
    apply existsb_exists in Hj_ex as (j & Hj_seq & Hcheck).
    apply in_seq in Hj_seq. destruct Hj_seq as [Hj_low Hj_high].
    apply andb_prop in Hcheck as [Hcheck123 Hlt_bool].
    apply andb_prop in Hcheck123 as [Hcheck12 Hij_bool].
    apply andb_prop in Hcheck12 as [Hi_lt_len_bool Hj_lt_len_bool].
    rewrite Nat.ltb_lt in Hi_lt_len_bool, Hj_lt_len_bool, Hij_bool.
    apply Rlt_bool_lt in Hlt_bool.
    exists i, j; repeat split; assumption.
  - apply ReflectF.
    intro H. destruct H as (i & j & Hi & Hj & Hij & Hlt).
    assert (Htrue : existsb (fun i => existsb (fun j =>
      (i <? length I) && (j <? length I) && (i <? j) &&
      Rlt_bool (INR (f (nth j I 0%nat))) (INR c * INR c * INR (f (nth i I 0%nat))))
      (seq 0 (length I))) (seq 0 (length I)) = true).
    {
      apply existsb_exists. exists i; split.
      { apply in_seq; split; [apply Nat.le_0_l | exact Hi]. }
      apply existsb_exists. exists j; split.
      { apply in_seq; split; [apply Nat.le_0_l | exact Hj]. }
      repeat (apply andb_true_iff; split);
        [apply Nat.ltb_lt; exact Hi| apply Nat.ltb_lt; exact Hj|
         apply Nat.ltb_lt; exact Hij| apply Rlt_bool_lt; exact Hlt].
    }
    rewrite Htrue in Hb; discriminate.
Qed.

(* 稀疏条件布尔判定 *)
Lemma sparse_cond_bP (I : list nat) :
  reflect
    (forall i j, (i < length I)%nat -> (j < length I)%nat -> (i < j)%nat ->
       (INR (f (nth j I 0%nat)) >= INR c * INR c * INR (f (nth i I 0%nat)))%R)
    (sparse_cond_b c f I).
Proof.
  unfold sparse_cond_b.
  set (F := fun i : nat =>
    forallb (fun j : nat =>
      if i <? j then
        Rge_bool (INR (f (nth j I 0%nat))) (INR c * INR c * INR (f (nth i I 0%nat)))
      else true) (seq 0 (length I))).
  remember (forallb F (seq 0 (length I))) as b eqn:Hb.
  destruct b.
  - symmetry in Hb.
    destruct (forallb_forall F (seq 0 (length I))) as [Hforward _].
    specialize (Hforward Hb).
    apply ReflectT.
    intros i j Hi Hj Hij.
    assert (Hi_in : In i (seq 0 (length I))) by (apply in_seq; lia).
    assert (Hj_in : In j (seq 0 (length I))) by (apply in_seq; lia).
    specialize (Hforward i Hi_in).
    unfold F in Hforward.
    destruct (forallb_forall (fun j : nat =>
               if i <? j then
                 Rge_bool (INR (f (nth j I 0%nat))) (INR c * INR c * INR (f (nth i I 0%nat)))
               else true) (seq 0 (length I))) as [Hinner_forward _].
    specialize (Hinner_forward Hforward).
    specialize (Hinner_forward j Hj_in).
    destruct (i <? j) eqn:Hij_bool.
    + apply Nat.ltb_lt in Hij_bool.
      apply Rge_bool_ge in Hinner_forward.
      exact Hinner_forward.
    + apply Nat.ltb_ge in Hij_bool. exfalso; lia.
  - apply ReflectF.
    intro H.
    destruct (forallb_forall F (seq 0 (length I))) as [_ Hbackward].
    assert (Htrue : forallb F (seq 0 (length I)) = true).
    { apply Hbackward.
      intros i Hi_seq. apply in_seq in Hi_seq.
      unfold F.
      destruct (forallb_forall (fun j : nat =>
                 if i <? j then
                   Rge_bool (INR (f (nth j I 0%nat))) (INR c * INR c * INR (f (nth i I 0%nat)))
                 else true) (seq 0 (length I))) as [_ Hinner_backward].
      apply Hinner_backward.
      intros j Hj_seq. apply in_seq in Hj_seq.
      destruct (i <? j) eqn:Hij_bool.
      - apply Nat.ltb_lt in Hij_bool.
        destruct Hi_seq as [_ Hi_len].
        destruct Hj_seq as [_ Hj_len].
        apply Rge_bool_ge.
        apply H with (i:=i) (j:=j); auto.
      - reflexivity. }
    rewrite Htrue in Hb; discriminate.
Qed.

(* 坏事件布尔值真当且仅当存在坏对 *)
Corollary bad_event_b_true_iff (I : list nat) :
  bad_event_b c f I = true <->
  exists i j, (i < length I)%nat /\ (j < length I)%nat /\ (i < j)%nat /\
             (INR (f (nth j I 0%nat)) < INR c * INR c * INR (f (nth i I 0%nat)))%R.
Proof.
  pose proof (bad_event_bP I) as Hreflect.
  destruct Hreflect as [Htrue | Hfalse].
  - split; intros _; auto.
  - split.
    + intro H; discriminate H.
    + intro H; exfalso; exact (Hfalse H).
Qed.

(* 稀疏条件布尔值真当且仅当所有指标对满足增长条件 *)
Corollary sparse_cond_b_true_iff (I : list nat) :
  sparse_cond_b c f I = true <->
  (forall i j, (i < length I)%nat -> (j < length I)%nat -> (i < j)%nat ->
     (INR (f (nth j I 0%nat)) >= INR c * INR c * INR (f (nth i I 0%nat)))%R).
Proof.
  pose proof (sparse_cond_bP I) as Hreflect.
  destruct Hreflect as [Htrue | Hfalse].
  - split; intros _; auto.
  - split.
    + intro H; discriminate H.
    + intro H; exfalso; exact (Hfalse H).
Qed.

End Equivalences.

Section ProbabilisticGeneration.

Variable (c : nat) (f : nat -> nat) (p : R) (N : nat).
Hypothesis Hc_ge2 : (c >= 2)%nat.
Hypothesis Hf_ge2 : forall i, (f i >= 2)%nat.
Hypothesis Hf_growth : forall i, (INR (f (S i)) >= INR c * INR c * INR (f i))%R.
Hypothesis Hp_bounds : (0 < p < 1)%R.

Let q := (1 - p)%R.
Let Hp_pos : (0 < p)%R := proj1 Hp_bounds.
Let Hp_lt1 : (p < 1)%R := proj2 Hp_bounds.

(* 以下定义提供与旧模块兼容的 Prop 接口，完全由构造性布尔判定反射得到 *)

Definition is_bad_pair (i j : nat) (I : list nat) : Prop :=
  is_bad_pair_b c f i j I = true.

Definition bad_event (I : list nat) : Prop :=
  bad_event_b c f I = true.

Definition c_sparse_subset (I : list nat) : Prop :=
  NoDup I /\ sparse_cond_b c f I = true.

(* 概率事件的别名（直接使用布尔谓词的加权和） *)
Definition probability_of_event (P : list nat -> bool) : R :=
  sum_over_subsets_weight p N P.

(* INR c 大于等于 2 *)
Lemma Hc_INR_ge_2 : INR c >= 2%R.
Proof.
  apply Rle_ge.
  apply (le_INR 2 c). lia.
Qed.

(* c的实数表示不小于2 *)
Let Hc_INR_ge_2 : INR c >= 2%R.
Proof.
  apply Rle_ge.
  apply (le_INR 2 c). lia.
Qed.

(* 概率参数范围 *)
Lemma Hp_range : 0 <= p <= 1.
Proof.
  split; lra.
Qed.

(* 子集权重非负 *)
Lemma weight_of_subset_nonneg : forall I, 0 <= p <= 1 -> 0 <= weight_of_subset p N I.
Proof.
  intros I [Hp_low Hp_high].
  unfold weight_of_subset.
  apply Rmult_le_pos.
  - apply pow_le; exact Hp_low.
  - apply pow_le; lra.
Qed.

(* 列表拼接与求和 *)
Lemma fold_right_Rplus_app (l1 l2 : list R) :
  fold_right Rplus 0 (l1 ++ l2) = fold_right Rplus 0 l1 + fold_right Rplus 0 l2.
Proof.
  induction l1 as [|x xs IH]; simpl; [ring | rewrite IH; ring].
Qed.

(* 常数因子提取 *)
Lemma fold_right_Rplus_factor (a : R) (g : list nat -> R) (l : list (list nat)) :
  fold_right Rplus 0 (map (fun I => a * g I) l) = a * fold_right Rplus 0 (map g l).
Proof.
  induction l as [|I l IH]; simpl; [ring | rewrite IH; ring].
Qed.

(* 条件分支下的因子提取 *)
Lemma fold_right_map_factor (a : R) (prev : list (list nat)) (P : list nat -> bool) (w : list nat -> R) :
  fold_right Rplus 0 (map (fun I => if P I then a * w I else 0) prev) =
  a * fold_right Rplus 0 (map (fun I => if P I then w I else 0) prev).
Proof.
  induction prev as [|I prev IH]; simpl.
  - ring.
  - destruct (P I); simpl; rewrite IH; ring.
Qed.

(* 子集长度上界 *)
Lemma all_subsets_upto_length_le : forall n I,
  In I (all_subsets_upto n) -> (length I <= n)%nat.
Proof.
  induction n; intros I Hin; simpl in *.
  - destruct Hin; subst; simpl; lia.
  - apply in_app_iff in Hin as [Hin' | Hin].
    + apply in_map_iff in Hin' as [J [Heq HinJ]]; subst.
      simpl; apply le_n_S; apply IHn; exact HinJ.
    + apply le_S; apply IHn; exact Hin.
Qed.

(* 所有子集权重和为1 *)
Lemma sum_weights_all_true' :
  sum_over_subsets_weight p N (fun _ => true) = 1%R.
Proof.
  induction N as [| m IH].
  - unfold sum_over_subsets_weight, all_subsets, all_subsets_upto, weight_of_subset; simpl; ring.
  - unfold sum_over_subsets_weight, all_subsets, all_subsets_upto; fold (all_subsets_upto m).
    set (prev := all_subsets_upto m).
    rewrite map_app, fold_right_Rplus_app.
    assert (Hlen_prev : forall I, In I prev -> (length I <= m)%nat)
      by (intros; apply all_subsets_upto_length_le; auto).

    assert (Hcons : fold_right Rplus 0
      (map (fun I => if true then weight_of_subset p (S m) I else 0)
           (map (fun l => m :: l) prev))
      = p * sum_over_subsets_weight p m (fun _ => true)).
    {
      rewrite map_map. simpl.
      assert (Haux : forall I, In I prev ->
        weight_of_subset p (S m) (m :: I) = p * weight_of_subset p m I).
      {
        intros I Hin.
        unfold weight_of_subset; rewrite length_cons.
        assert (HlenI : (length I <= m)%nat) by (apply Hlen_prev; auto).
        replace (S m - S (length I))%nat with (m - length I)%nat by lia.
        simpl; ring.
      }
      rewrite (map_ext_in (fun I : list nat => weight_of_subset p (S m) (m :: I))
                         (fun I : list nat => p * weight_of_subset p m I) prev Haux).
      rewrite fold_right_Rplus_factor.
      unfold sum_over_subsets_weight, all_subsets; fold prev.
      reflexivity.
    }

    assert (Hold : fold_right Rplus 0
      (map (fun I => if true then weight_of_subset p (S m) I else 0) prev)
      = (1-p) * sum_over_subsets_weight p m (fun _ => true)).
    {
      simpl.
      assert (Haux : forall I, In I prev ->
        weight_of_subset p (S m) I = (1-p) * weight_of_subset p m I).
      {
        intros I Hin.
        unfold weight_of_subset.
        assert (HlenI : (length I <= m)%nat) by (apply Hlen_prev; auto).
        replace (S m - length I)%nat with (S (m - length I))%nat by lia.
        simpl; ring.
      }
      rewrite (map_ext_in (fun I : list nat => weight_of_subset p (S m) I)
                         (fun I : list nat => (1-p) * weight_of_subset p m I) prev Haux).
      rewrite fold_right_Rplus_factor.
      unfold sum_over_subsets_weight, all_subsets; fold prev.
      reflexivity.
    }

    rewrite Hcons, Hold.
    rewrite IH; ring.
Qed.

(* 列表成员布尔判定 *)
Definition inb (a : nat) (l : list nat) : bool :=
  existsb (Nat.eqb a) l.

(* 成员判定正确性 *)
Lemma inb_true_iff : forall a l, inb a l = true <-> In a l.
Proof.
  intros a l; unfold inb; rewrite existsb_exists; split.
  - intros (b & Hb_in & Hb_eq).
    apply Nat.eqb_eq in Hb_eq; subst b; exact Hb_in.
  - intro H; exists a; split; [exact H | apply Nat.eqb_refl].
Qed.

(* 子集列表中的元素均小于上界 *)
Lemma all_subsets_upto_Forall_lt : forall n I,
  In I (all_subsets_upto n) -> Forall (fun x : nat => (x < n)%nat) I.
Proof.
  induction n; intros I Hin; simpl in *.
  - destruct Hin as [<- | []]; constructor.
  - apply in_app_iff in Hin as [Hin' | Hin].
    + apply in_map_iff in Hin' as [J [Heq HinJ]]; subst.
      constructor; [lia |].
      apply Forall_impl with (P := fun x : nat => (x < n)%nat); [| apply IHn; exact HinJ].
      intros a Ha; simpl; lia.
    + apply Forall_impl with (P := fun x : nat => (x < n)%nat); [| apply IHn; exact Hin].
      intros a Ha; simpl; lia.
Qed.

(* 子集列表中不包含其编号自身 *)
Lemma all_subsets_upto_not_contains : forall n I,
  In I (all_subsets_upto n) -> ~ In n I.
Proof.
  intros n I Hin Hn.
  apply all_subsets_upto_Forall_lt in Hin.
  apply Forall_forall with (x := n) in Hin; auto.
  simpl in Hin; lia.
Qed.

(* 所有权重和的泛化版本 *)
Lemma sum_weights_all_true_general : forall n : nat,
  sum_over_subsets_weight p n (fun _ => true) = 1%R.
Proof.
  induction n as [| m IH].
  - unfold sum_over_subsets_weight, all_subsets, all_subsets_upto, weight_of_subset; simpl; ring.
  - unfold sum_over_subsets_weight, all_subsets, all_subsets_upto; fold (all_subsets_upto m).
    set (prev := all_subsets_upto m).
    rewrite map_app, fold_right_Rplus_app.
    assert (Hlen_prev : forall I, In I prev -> (length I <= m)%nat)
      by (intros; apply all_subsets_upto_length_le; auto).
    assert (Hcons : fold_right Rplus 0
      (map (fun I => if true then weight_of_subset p (S m) I else 0)
           (map (fun l => m :: l) prev))
      = p * sum_over_subsets_weight p m (fun _ => true)).
    {
      rewrite map_map. simpl.
      assert (Haux : forall I, In I prev ->
        weight_of_subset p (S m) (m :: I) = p * weight_of_subset p m I).
      {
        intros I Hin.
        unfold weight_of_subset; rewrite length_cons.
        assert (HlenI : (length I <= m)%nat) by (apply Hlen_prev; auto).
        replace (S m - S (length I))%nat with (m - length I)%nat by lia.
        simpl; ring.
      }
      rewrite (map_ext_in (fun I : list nat => weight_of_subset p (S m) (m :: I))
                         (fun I : list nat => p * weight_of_subset p m I) prev Haux).
      rewrite fold_right_Rplus_factor.
      unfold sum_over_subsets_weight, all_subsets; fold prev; reflexivity.
    }
    assert (Hold : fold_right Rplus 0
      (map (fun I => if true then weight_of_subset p (S m) I else 0) prev)
      = (1-p) * sum_over_subsets_weight p m (fun _ => true)).
    {
      simpl.
      assert (Haux : forall I, In I prev ->
        weight_of_subset p (S m) I = (1-p) * weight_of_subset p m I).
      {
        intros I Hin.
        unfold weight_of_subset.
        assert (HlenI : (length I <= m)%nat) by (apply Hlen_prev; auto).
        replace (S m - length I)%nat with (S (m - length I))%nat by lia.
        simpl; ring.
      }
      rewrite (map_ext_in (fun I : list nat => weight_of_subset p (S m) I)
                         (fun I : list nat => (1-p) * weight_of_subset p m I) prev Haux).
      rewrite fold_right_Rplus_factor.
      unfold sum_over_subsets_weight, all_subsets; fold prev; reflexivity.
    }
    rewrite Hcons, Hold.
    rewrite IH; ring.
Qed.

(* 单点包含概率 *)
Lemma prob_single_inclusion (x : nat) (Hx : (x < N)%nat) :
  sum_over_subsets_weight p N (fun I => inb x I) = p.
Proof.
  revert x Hx.
  induction N as [| M IH]; intros x Hx; [lia|].
  destruct (Nat.eq_dec x M) as [-> | Hne].
  - (* x = M *)
    unfold sum_over_subsets_weight, all_subsets, all_subsets_upto; fold (all_subsets_upto M).
    set (prev := all_subsets_upto M).
    rewrite map_app, fold_right_Rplus_app.
    assert (Hlen_prev : forall I, In I prev -> (length I <= M)%nat)
      by (intros; apply all_subsets_upto_length_le; auto).

    assert (Hcons : fold_right Rplus 0
      (map (fun I => if inb M I then weight_of_subset p (S M) I else 0)
           (map (fun l => M :: l) prev)) = p).
    {
      rewrite map_map.
      assert (H_aux : forall I, In I prev ->
        (if inb M (M :: I) then weight_of_subset p (S M) (M :: I) else 0)
        = (if true then p * weight_of_subset p M I else 0)).
      {
        intros I Hin.
        unfold inb. simpl (existsb (Nat.eqb M) (M :: I)).
        rewrite Nat.eqb_refl. simpl.
        unfold weight_of_subset; rewrite length_cons.
        assert (HlenI : (length I <= M)%nat) by (apply Hlen_prev; auto).
        replace (S M - S (length I))%nat with (M - length I)%nat by lia.
        simpl; ring.
      }
      rewrite (map_ext_in (fun I => if inb M (M :: I) then weight_of_subset p (S M) (M :: I) else 0)
                         (fun I => if true then p * weight_of_subset p M I else 0) prev H_aux).
      simpl (if true then _ else _).
      rewrite fold_right_Rplus_factor.
      replace (fold_right Rplus 0 (map (weight_of_subset p M) prev))
        with (sum_over_subsets_weight p M (fun _ => true)).
      - rewrite sum_weights_all_true_general; ring.
      - unfold sum_over_subsets_weight, all_subsets; fold prev; reflexivity.
    }

    assert (Hold : fold_right Rplus 0
      (map (fun I => if inb M I then weight_of_subset p (S M) I else 0) prev) = 0).
    {
      assert (H_aux : forall I, In I prev ->
        (if inb M I then weight_of_subset p (S M) I else 0) = 0).
      {
        intros I Hin. destruct (inb M I) eqn:Hinb; auto.
        apply inb_true_iff in Hinb.
        exfalso; eapply all_subsets_upto_not_contains; eauto.
      }
      rewrite (map_ext_in (fun I => if inb M I then weight_of_subset p (S M) I else 0)
                         (fun _ => 0) prev H_aux).
      clear -prev.
      induction prev as [|I prev IHprev]; simpl; auto.
      rewrite IHprev; auto.
    lra.
    }
    rewrite Hcons, Hold; ring.

  - (* x < M *)
    assert (Hx_lt_M : (x < M)%nat) by lia.
    unfold sum_over_subsets_weight, all_subsets, all_subsets_upto; fold (all_subsets_upto M).
    set (prev := all_subsets_upto M).
    rewrite map_app, fold_right_Rplus_app.
    assert (Hlen_prev : forall I, In I prev -> (length I <= M)%nat)
      by (intros; apply all_subsets_upto_length_le; auto).

    assert (Hcons : fold_right Rplus 0
      (map (fun I => if inb x I then weight_of_subset p (S M) I else 0)
           (map (fun l => M :: l) prev))
      = p * sum_over_subsets_weight p M (fun I => inb x I)).
    {
      rewrite map_map.
      assert (H_aux : forall I, In I prev ->
        (if inb x (M :: I) then weight_of_subset p (S M) (M :: I) else 0)
        = (if inb x I then p * weight_of_subset p M I else 0)).
      {
        intros I Hin.
        simpl (inb x (M :: I)).
        destruct (Nat.eqb_spec x M) as [Heq | Hneq].
        - exfalso; apply Hne; auto.
        - simpl.
          case_eq (inb x I); intros Hxb; [|auto].
          unfold weight_of_subset; rewrite length_cons.
          assert (HlenI : (length I <= M)%nat) by (apply Hlen_prev; auto).
          replace (S M - S (length I))%nat with (M - length I)%nat by lia.
          simpl; ring.
      }
      rewrite (map_ext_in (fun I => if inb x (M :: I) then weight_of_subset p (S M) (M :: I) else 0)
                         (fun I => if inb x I then p * weight_of_subset p M I else 0) prev H_aux).
      rewrite fold_right_map_factor.
      unfold sum_over_subsets_weight, all_subsets; fold prev.
      reflexivity.
    }

    assert (Hold : fold_right Rplus 0
      (map (fun I => if inb x I then weight_of_subset p (S M) I else 0) prev)
      = (1-p) * sum_over_subsets_weight p M (fun I => inb x I)).
    {
      assert (H_aux : forall I, In I prev ->
        (if inb x I then weight_of_subset p (S M) I else 0)
        = (if inb x I then (1-p) * weight_of_subset p M I else 0)).
      {
        intros I Hin.
        case_eq (inb x I); intros Hxb; auto.
        unfold weight_of_subset.
        assert (HlenI : (length I <= M)%nat) by (apply Hlen_prev; auto).
        replace (S M - length I)%nat with (S (M - length I))%nat by lia.
        simpl; ring.
      }
      rewrite (map_ext_in (fun I => if inb x I then weight_of_subset p (S M) I else 0)
                         (fun I => if inb x I then (1-p) * weight_of_subset p M I else 0) prev H_aux).
      rewrite fold_right_map_factor.
      unfold sum_over_subsets_weight, all_subsets; fold prev.
      reflexivity.
    }
    rewrite Hcons, Hold.
    rewrite IH with (x := x); [| exact Hx_lt_M]; ring.
Qed.

(* 列表中包含自身首元素 *)
Lemma inb_cons_eq : forall a l, inb a (a :: l) = true.
Proof. intros a l; unfold inb; simpl; rewrite Nat.eqb_refl; auto. Qed.

(* 列表中不包含自身首元素时，判定结果不变 *)
Lemma inb_cons_neq : forall a b l, a <> b -> inb a (b :: l) = inb a l.
Proof. intros a b l Hneq; unfold inb; simpl; destruct (Nat.eqb_spec a b); [contradiction|reflexivity]. Qed.

(* 单点包含概率的泛化版本 *)
Lemma prob_single_inclusion_general : forall n x, (x < n)%nat ->
  sum_over_subsets_weight p n (fun I => inb x I) = p.
Proof.
  induction n as [| m IH]; intros x Hx.
  - lia.
  - destruct (Nat.eq_dec x m) as [-> | Hne].
    + (* x = m *)
      unfold sum_over_subsets_weight, all_subsets, all_subsets_upto; fold (all_subsets_upto m).
      set (prev := all_subsets_upto m).
      rewrite map_app, fold_right_Rplus_app.
      assert (Hlen_prev : forall I, In I prev -> (length I <= m)%nat)
        by (intros; apply all_subsets_upto_length_le; auto).
      assert (Hcons : fold_right Rplus 0
        (map (fun I => if inb m I then weight_of_subset p (S m) I else 0)
             (map (fun l => m :: l) prev)) = p).
      {
        rewrite map_map.
        assert (H_aux : forall I, In I prev ->
          (if inb m (m :: I) then weight_of_subset p (S m) (m :: I) else 0)
          = (if true then p * weight_of_subset p m I else 0)).
        {
          intros I Hin.
          unfold inb. simpl (existsb (Nat.eqb m) (m :: I)).
          rewrite Nat.eqb_refl. simpl.
          unfold weight_of_subset; rewrite length_cons.
          assert (HlenI : (length I <= m)%nat) by (apply Hlen_prev; auto).
          replace (S m - S (length I))%nat with (m - length I)%nat by lia.
          simpl; ring.
        }
        rewrite (map_ext_in (fun I => if inb m (m :: I) then weight_of_subset p (S m) (m :: I) else 0)
                           (fun I => if true then p * weight_of_subset p m I else 0) prev H_aux).
        simpl (if true then _ else _).
        rewrite fold_right_Rplus_factor.
        replace (fold_right Rplus 0 (map (weight_of_subset p m) prev))
          with (sum_over_subsets_weight p m (fun _ => true)).
        - rewrite sum_weights_all_true_general; ring.
        - unfold sum_over_subsets_weight, all_subsets; fold prev; reflexivity.
      }
      assert (Hold : fold_right Rplus 0
        (map (fun I => if inb m I then weight_of_subset p (S m) I else 0) prev) = 0).
      {
        assert (H_aux : forall I, In I prev ->
          (if inb m I then weight_of_subset p (S m) I else 0) = 0).
        {
          intros I Hin. destruct (inb m I) eqn:Hinb; auto.
          apply inb_true_iff in Hinb.
          exfalso; eapply all_subsets_upto_not_contains; eauto.
        }
        rewrite (map_ext_in (fun I => if inb m I then weight_of_subset p (S m) I else 0)
                           (fun _ => 0) prev H_aux).
        clear -prev.
        induction prev as [|I prev IHprev]; simpl; [lra |].
        rewrite IHprev; lra.
      }
      rewrite Hcons, Hold; ring.
    + (* x < m *)
      assert (Hx_lt_m : (x < m)%nat) by lia.
      unfold sum_over_subsets_weight, all_subsets, all_subsets_upto; fold (all_subsets_upto m).
      set (prev := all_subsets_upto m).
      rewrite map_app, fold_right_Rplus_app.
      assert (Hlen_prev : forall I, In I prev -> (length I <= m)%nat)
        by (intros; apply all_subsets_upto_length_le; auto).
      assert (Hcons : fold_right Rplus 0
        (map (fun I => if inb x I then weight_of_subset p (S m) I else 0)
             (map (fun l => m :: l) prev))
        = p * sum_over_subsets_weight p m (fun I => inb x I)).
      {
        rewrite map_map.
        assert (H_aux : forall I, In I prev ->
          (if inb x (m :: I) then weight_of_subset p (S m) (m :: I) else 0)
          = (if inb x I then p * weight_of_subset p m I else 0)).
        {
          intros I Hin.
          simpl (inb x (m :: I)).
          destruct (Nat.eqb_spec x m) as [Heq | Hneq].
          - exfalso; apply Hne; auto.
          - simpl.
            case_eq (inb x I); intros Hxb; [|auto].
            unfold weight_of_subset; rewrite length_cons.
            assert (HlenI : (length I <= m)%nat) by (apply Hlen_prev; auto).
            replace (S m - S (length I))%nat with (m - length I)%nat by lia.
            simpl; ring.
        }
        rewrite (map_ext_in (fun I => if inb x (m :: I) then weight_of_subset p (S m) (m :: I) else 0)
                           (fun I => if inb x I then p * weight_of_subset p m I else 0) prev H_aux).
        rewrite fold_right_map_factor.
        unfold sum_over_subsets_weight, all_subsets; fold prev.
        reflexivity.
      }
      assert (Hold : fold_right Rplus 0
        (map (fun I => if inb x I then weight_of_subset p (S m) I else 0) prev)
        = (1-p) * sum_over_subsets_weight p m (fun I => inb x I)).
      {
        assert (H_aux : forall I, In I prev ->
          (if inb x I then weight_of_subset p (S m) I else 0)
          = (if inb x I then (1-p) * weight_of_subset p m I else 0)).
        {
          intros I Hin.
          case_eq (inb x I); intros Hxb; auto.
          unfold weight_of_subset.
          assert (HlenI : (length I <= m)%nat) by (apply Hlen_prev; auto).
          replace (S m - length I)%nat with (S (m - length I))%nat by lia.
          simpl; ring.
        }
        rewrite (map_ext_in (fun I => if inb x I then weight_of_subset p (S m) I else 0)
                           (fun I => if inb x I then (1-p) * weight_of_subset p m I else 0) prev H_aux).
        rewrite fold_right_map_factor.
        unfold sum_over_subsets_weight, all_subsets; fold prev.
        reflexivity.
      }
      rewrite Hcons, Hold.
      rewrite IH with (x := x); [| exact Hx_lt_m]; ring.
Qed.

(* 无序对包含概率 *)
Lemma prob_pair_inclusion (a b : nat) (Ha : (a < N)%nat) (Hb : (b < N)%nat) (Hneq : a <> b) :
  sum_over_subsets_weight p N (fun I => (inb a I) && (inb b I)) = p * p.
Proof.
  revert a b Ha Hb Hneq.
  induction N as [| M IH]; intros a b Ha Hb Hneq; [lia|].
  destruct (Nat.eq_dec a M) as [-> | Hne_a],
           (Nat.eq_dec b M) as [-> | Hne_b].
  - exfalso; auto.
  - (* a = M, b < M *)
    assert (Hb_lt_M : (b < M)%nat) by lia.
    unfold sum_over_subsets_weight, all_subsets, all_subsets_upto; fold (all_subsets_upto M).
    set (prev := all_subsets_upto M).
    rewrite map_app, fold_right_Rplus_app.
    assert (Hlen_prev : forall I, In I prev -> (length I <= M)%nat)
      by (intros; apply all_subsets_upto_length_le; auto).
    assert (Hcons : fold_right Rplus 0
      (map (fun I => if (inb M I) && (inb b I) then weight_of_subset p (S M) I else 0)
           (map (fun l => M :: l) prev))
      = p * sum_over_subsets_weight p M (fun I => inb b I)).
    {
      rewrite map_map.
      assert (H_aux : forall I, In I prev ->
        (if (inb M (M :: I)) && (inb b (M :: I)) then weight_of_subset p (S M) (M :: I) else 0) =
        (if inb b I then p * weight_of_subset p M I else 0)).
      {
        intros I Hin.
        rewrite inb_cons_eq.
        rewrite (inb_cons_neq b M I); [|auto].
        case_eq (inb b I); intros Hb_in; [|auto].
        unfold weight_of_subset; rewrite length_cons.
        assert (HlenI : (length I <= M)%nat) by (apply Hlen_prev; auto).
        replace (S M - S (length I))%nat with (M - length I)%nat by lia.
        simpl; ring.
      }
      rewrite (map_ext_in (fun I => if (inb M (M :: I)) && (inb b (M :: I)) then weight_of_subset p (S M) (M :: I) else 0)
                         (fun I => if inb b I then p * weight_of_subset p M I else 0) prev H_aux).
      rewrite fold_right_map_factor.
      unfold sum_over_subsets_weight, all_subsets; fold prev.
      reflexivity.
    }
    assert (Hold : fold_right Rplus 0
      (map (fun I => if (inb M I) && (inb b I) then weight_of_subset p (S M) I else 0) prev) = 0).
    {
      assert (H_aux : forall I, In I prev ->
        (if (inb M I) && (inb b I) then weight_of_subset p (S M) I else 0) = 0).
      {
        intros I Hin. destruct (inb M I) eqn:HinM; simpl; auto.
        apply inb_true_iff in HinM.
        exfalso; eapply all_subsets_upto_not_contains; eauto.
      }
      rewrite (map_ext_in (fun I => if (inb M I) && (inb b I) then weight_of_subset p (S M) I else 0)
                         (fun _ => 0) prev H_aux).
      clear -prev.
      induction prev as [|I prev IHprev]; simpl; [lra |].
      rewrite IHprev; lra.
    }
    rewrite Hcons, Hold, Rplus_0_r.
    rewrite (prob_single_inclusion_general M b Hb_lt_M); ring.
  - (* b = M, a < M *)
    assert (Ha_lt_M : (a < M)%nat) by lia.
    unfold sum_over_subsets_weight, all_subsets, all_subsets_upto; fold (all_subsets_upto M).
    set (prev := all_subsets_upto M).
    rewrite map_app, fold_right_Rplus_app.
    assert (Hlen_prev : forall I, In I prev -> (length I <= M)%nat)
      by (intros; apply all_subsets_upto_length_le; auto).
    assert (Hcons : fold_right Rplus 0
      (map (fun I => if (inb a I) && (inb M I) then weight_of_subset p (S M) I else 0)
           (map (fun l => M :: l) prev))
      = p * sum_over_subsets_weight p M (fun I => inb a I)).
    {
      rewrite map_map.
      assert (H_aux : forall I, In I prev ->
        (if (inb a (M :: I)) && (inb M (M :: I)) then weight_of_subset p (S M) (M :: I) else 0) =
        (if inb a I then p * weight_of_subset p M I else 0)).
      {
        intros I Hin.
        rewrite inb_cons_eq.
        rewrite (inb_cons_neq a M I); [|auto].
        case_eq (inb a I); intros Ha_in; [|auto].
        unfold weight_of_subset; rewrite length_cons.
        assert (HlenI : (length I <= M)%nat) by (apply Hlen_prev; auto).
        replace (S M - S (length I))%nat with (M - length I)%nat by lia.
        simpl; ring.
      }
      rewrite (map_ext_in (fun I => if (inb a (M :: I)) && (inb M (M :: I)) then weight_of_subset p (S M) (M :: I) else 0)
                         (fun I => if inb a I then p * weight_of_subset p M I else 0) prev H_aux).
      rewrite fold_right_map_factor.
      unfold sum_over_subsets_weight, all_subsets; fold prev.
      reflexivity.
    }
    assert (Hold : fold_right Rplus 0
      (map (fun I => if (inb a I) && (inb M I) then weight_of_subset p (S M) I else 0) prev) = 0).
    {
      assert (H_aux : forall I, In I prev ->
        (if (inb a I) && (inb M I) then weight_of_subset p (S M) I else 0) = 0).
      {
        intros I Hin. destruct (inb M I) eqn:HinM; simpl.
        - apply inb_true_iff in HinM.
          exfalso; eapply all_subsets_upto_not_contains; eauto.
        - rewrite Bool.andb_false_r; reflexivity.
      }
      rewrite (map_ext_in (fun I => if (inb a I) && (inb M I) then weight_of_subset p (S M) I else 0)
                         (fun _ => 0) prev H_aux).
      clear -prev.
      induction prev as [|I prev IHprev]; simpl; [lra |].
      rewrite IHprev; lra.
    }
    rewrite Hcons, Hold, Rplus_0_r.
    rewrite (prob_single_inclusion_general M a Ha_lt_M); ring.
  - (* both < M *)
    assert (Ha_lt_M : (a < M)%nat) by lia.
    assert (Hb_lt_M : (b < M)%nat) by lia.
    unfold sum_over_subsets_weight, all_subsets, all_subsets_upto; fold (all_subsets_upto M).
    set (prev := all_subsets_upto M).
    rewrite map_app, fold_right_Rplus_app.
    assert (Hlen_prev : forall I, In I prev -> (length I <= M)%nat)
      by (intros; apply all_subsets_upto_length_le; auto).
    assert (Hcons : fold_right Rplus 0
      (map (fun I => if (inb a I) && (inb b I) then weight_of_subset p (S M) I else 0)
           (map (fun l => M :: l) prev))
      = p * sum_over_subsets_weight p M (fun I => (inb a I) && (inb b I))).
    {
      rewrite map_map.
      assert (H_aux : forall I, In I prev ->
        (if (inb a (M :: I)) && (inb b (M :: I)) then weight_of_subset p (S M) (M :: I) else 0) =
        (if (inb a I) && (inb b I) then p * weight_of_subset p M I else 0)).
      {
        intros I Hin.
        rewrite (inb_cons_neq a M I); [|auto].
        rewrite (inb_cons_neq b M I); [|auto].
        case_eq ((inb a I) && (inb b I)); intros Hab; [|auto].
        apply andb_prop in Hab as (Ha_in & Hb_in).
        unfold weight_of_subset; rewrite length_cons.
        assert (HlenI : (length I <= M)%nat) by (apply Hlen_prev; auto).
        replace (S M - S (length I))%nat with (M - length I)%nat by lia.
        simpl; ring.
      }
      rewrite (map_ext_in (fun I => if (inb a (M :: I)) && (inb b (M :: I)) then weight_of_subset p (S M) (M :: I) else 0)
                         (fun I => if (inb a I) && (inb b I) then p * weight_of_subset p M I else 0) prev H_aux).
      rewrite fold_right_map_factor.
      unfold sum_over_subsets_weight, all_subsets; fold prev.
      reflexivity.
    }
    assert (Hold : fold_right Rplus 0
      (map (fun I => if (inb a I) && (inb b I) then weight_of_subset p (S M) I else 0) prev)
      = (1-p) * sum_over_subsets_weight p M (fun I => (inb a I) && (inb b I))).
    {
      assert (H_aux : forall I, In I prev ->
        (if (inb a I) && (inb b I) then weight_of_subset p (S M) I else 0) =
        (if (inb a I) && (inb b I) then (1-p) * weight_of_subset p M I else 0)).
      {
        intros I Hin.
        case_eq ((inb a I) && (inb b I)); intros Hab; auto.
        unfold weight_of_subset.
        assert (HlenI : (length I <= M)%nat) by (apply Hlen_prev; auto).
        replace (S M - length I)%nat with (S (M - length I))%nat by lia.
        simpl; ring.
      }
      rewrite (map_ext_in (fun I => if (inb a I) && (inb b I) then weight_of_subset p (S M) I else 0)
                         (fun I => if (inb a I) && (inb b I) then (1-p) * weight_of_subset p M I else 0) prev H_aux).
      rewrite fold_right_map_factor.
      unfold sum_over_subsets_weight, all_subsets; fold prev.
      reflexivity.
    }
    rewrite Hcons, Hold.
    rewrite IH with (a:=a) (b:=b); auto; ring.
Qed.

(* 所有严格递增对列表的辅助定义 *)
Definition all_pairs_lt_aux (start M : nat) : list (nat * nat) :=
  flat_map (fun i => map (fun j => (i, j)) (seq (S i) (M - S i)%nat))
           (seq start (M - start)%nat).

(* 所有严格递增对列表 *)
Definition all_pairs_lt (K : nat) : list (nat * nat) := all_pairs_lt_aux 0 K.

(* 对列表成员判定 *)
Lemma in_all_pairs_lt_iff (K i j : nat) :
  In (i, j) (all_pairs_lt K) <-> (i < j < K)%nat.
Proof.
  split.
  - intros Hin. unfold all_pairs_lt, all_pairs_lt_aux in Hin.
    apply in_flat_map in Hin as (k & Hk_seq & Hin_map).
    apply in_map_iff in Hin_map as (m & Hpair & Hm_seq).
    inversion Hpair; clear Hpair; subst.
    apply in_seq in Hk_seq; apply in_seq in Hm_seq.
    lia.
  - intros (Hij & HjK).
    unfold all_pairs_lt, all_pairs_lt_aux.
    apply in_flat_map.
    exists i; split.
    + apply in_seq; lia.
    + apply in_map_iff; exists j; split; [reflexivity |].
      apply in_seq; lia.
Qed.

(* all_subsets_upto 中所有子集无重复 *)
Lemma all_subsets_upto_NoDup : forall n I,
  In I (all_subsets_upto n) -> NoDup I.
Proof.
  induction n; intros I Hin; simpl in *.
  - destruct Hin as [<- | []]; constructor.
  - apply in_app_iff in Hin as [Hin' | Hin].
    + apply in_map_iff in Hin' as [J [Heq HinJ]]; subst.
      constructor; [| apply IHn; exact HinJ].
      intro H; apply all_subsets_upto_not_contains in HinJ; apply HinJ; exact H.
    + apply IHn; exact Hin.
Qed.

(* all_subsets 中所有子集无重复 *)
Lemma all_subsets_NoDup : forall I,
  In I (all_subsets N) -> NoDup I.
Proof.
  apply all_subsets_upto_NoDup.
Qed.

(* 子集加权和单调性 *)
Lemma sum_over_subsets_weight_mono_in (P Q : list nat -> bool) :
  (forall I, In I (all_subsets N) -> P I = true -> Q I = true) ->
  sum_over_subsets_weight p N P <= sum_over_subsets_weight p N Q.
Proof.
  intros Hmono.
  unfold sum_over_subsets_weight.
  set (l := all_subsets N) in *.
  assert (Hnonneg : forall I : list nat, 0 <= weight_of_subset p N I).
  { intros I; apply weight_of_subset_nonneg; apply Hp_range. }
  induction l as [| I l IH]; simpl.
  - lra.
  - assert (H_I_in : In I (I :: l)) by (left; reflexivity).
    destruct (P I) eqn:HP, (Q I) eqn:HQ; simpl.
    + apply Rplus_le_compat_l; apply IH.
      intros I0 Hin; apply Hmono; right; exact Hin.
    + exfalso.
      assert (Q I = true) by (apply Hmono; [exact H_I_in | exact HP]).
      rewrite HQ in H; discriminate.
    + assert (Hmono_l : forall I0, In I0 l -> P I0 = true -> Q I0 = true).
      { intros I0 Hin; apply Hmono; right; exact Hin. }
      assert (Hstep1 : fold_right Rplus 0
                         (map (fun I0 : list nat => if P I0 then weight_of_subset p N I0 else 0) l)
                       <= fold_right Rplus 0
                         (map (fun I0 : list nat => if Q I0 then weight_of_subset p N I0 else 0) l)).
      { apply IH; exact Hmono_l. }
      rewrite Rplus_0_l.
      set (S_Q := fold_right Rplus 0
                   (map (fun I0 : list nat => if Q I0 then weight_of_subset p N I0 else 0) l)).
      apply Rle_trans with S_Q.
      + exact Hstep1.
      + assert (Hpos : 0 <= weight_of_subset p N I) by exact (Hnonneg I).
        lra.
    + assert (Hmono_l : forall I0, In I0 l -> P I0 = true -> Q I0 = true).
      { intros I0 Hin; apply Hmono; right; exact Hin. }
      apply Rplus_le_compat_l; apply IH; exact Hmono_l.
Qed.

(* 布尔或的加权和不超过两部分加权和之和 *)
Lemma fold_right_or_le (F G : list nat -> bool) (w : list nat -> R) (l : list (list nat)) :
  (forall I, 0 <= w I) ->
  fold_right Rplus 0 (map (fun I => if F I || G I then w I else 0) l)
  <= fold_right Rplus 0 (map (fun I => if F I then w I else 0) l)
   + fold_right Rplus 0 (map (fun I => if G I then w I else 0) l).
Proof.
  intros Hpos. induction l as [| x xs IH]; simpl.
  - lra.
  - destruct (F x) eqn:HF, (G x) eqn:HG; simpl;
    pose proof (Hpos x) as Hwx; lra.
Qed.

(* 求和函数对布尔谓词的外延相等 *)
Lemma sum_over_subsets_weight_ext (P Q : list nat -> bool) :
  (forall I, P I = Q I) -> sum_over_subsets_weight p N P = sum_over_subsets_weight p N Q.
Proof.
  intros H. unfold sum_over_subsets_weight. f_equal. apply map_ext; intro I; rewrite H; reflexivity.
Qed.

(* 存在配对加权和的上界 *)
Lemma sum_over_subsets_weight_exists_pair_le (pairs : list (nat * nat)) :
  let events := map (fun '(a,b) => (fun I : list nat => (inb a I) && (inb b I))) pairs in
  sum_over_subsets_weight p N
    (fun I => existsb (fun '(a,b) => (inb a I) && (inb b I)) pairs)
  <= fold_right Rplus 0 (map (sum_over_subsets_weight p N) events).
Proof.
  intros events.
  set (E := fun I => existsb (fun '(a,b) => (inb a I) && (inb b I)) pairs).
  assert (H_nonneg : forall I, 0 <= weight_of_subset p N I).
  { intros I; apply weight_of_subset_nonneg; apply Hp_range. }
  unfold sum_over_subsets_weight, events.
  induction pairs as [| (a,b) pairs IH]; simpl.
  - induction (all_subsets N); simpl; lra.
  - lazy beta in IH.
    set (F := (fun I : list nat => (inb a I) && (inb b I))).
    set (G := fun I : list nat => existsb (fun '(a0,b0) => (inb a0 I) && (inb b0 I)) pairs).
    pose proof (sum_over_subsets_weight_mono_in
                  (fun I => (inb a I) && (inb b I) || G I)
                  (fun I => F I || G I)) as Hle.
    apply Rle_trans with
      (fold_right Rplus 0
         (map (fun I => if F I || G I then weight_of_subset p N I else 0) (all_subsets N))).
    + apply sum_over_subsets_weight_mono_in.
      intros I Hin H_exists.
      apply existsb_exists in H_exists as ((a0,b0) & Hin_pair & Hab).
      simpl in Hab; apply andb_prop in Hab as (Ha_in & Hb_in).
      destruct (Nat.eq_dec a a0), (Nat.eq_dec b b0); subst.
      * unfold F; rewrite Ha_in, Hb_in; reflexivity.
      * apply in_inv in Hin_pair.
        destruct Hin_pair as [Heq | Hin_pairs].
        -- injection Heq; intros; subst; exfalso; apply n; reflexivity.
        -- apply Bool.orb_true_iff; right.
           apply existsb_exists; exists (a0,b0); split; [exact Hin_pairs|].
           simpl; rewrite Ha_in, Hb_in; reflexivity.
      * apply in_inv in Hin_pair.
        destruct Hin_pair as [Heq | Hin_pairs].
        -- injection Heq; intros; subst; exfalso; apply n; reflexivity.
        -- apply Bool.orb_true_iff; right.
           apply existsb_exists; exists (a0,b0); split; [exact Hin_pairs|].
           simpl; rewrite Ha_in, Hb_in; reflexivity.
      * apply in_inv in Hin_pair.
        destruct Hin_pair as [Heq | Hin_pairs].
        -- injection Heq; intros; subst; exfalso; apply n0; reflexivity.
        -- apply Bool.orb_true_iff; right.
           apply existsb_exists; exists (a0,b0); split; [exact Hin_pairs|].
           simpl; rewrite Ha_in, Hb_in; reflexivity.
    + apply Rle_trans with
        (fold_right Rplus 0 (map (fun I => if F I then weight_of_subset p N I else 0) (all_subsets N))
         + fold_right Rplus 0 (map (fun I => if G I then weight_of_subset p N I else 0) (all_subsets N))).
      * apply fold_right_or_le; exact H_nonneg.
      * apply Rplus_le_compat.
        -- unfold F; apply Rle_refl.
        -- set (E' := fun I : list nat => existsb (fun '(a0,b0) => inb a0 I && inb b0 I) pairs).
           assert (G_eq_E' : forall I, G I = E' I) by reflexivity.
           assert (Hmap : map (fun I => if G I then weight_of_subset p N I else 0) (all_subsets N)
                        = map (fun I => if E' I then weight_of_subset p N I else 0) (all_subsets N)).
           { apply map_ext; intro I; rewrite G_eq_E'; reflexivity. }
           rewrite Hmap.
           cbv beta in IH.
           exact IH.
Qed.

(* 扁平映射长度上界 *)
Lemma length_flat_map_bound (A B : Type) (g : A -> list B) (l : list A) (M : nat) :
  (forall x, In x l -> length (g x) <= M)%nat ->
  (length (flat_map g l) <= length l * M)%nat.
Proof.
  induction l as [|x xs IH]; simpl; intros H.
  - simpl; lia.
  - rewrite length_app.
    assert (Hx : (length (g x) <= M)%nat) by (apply H; left; reflexivity).
    assert (Hxs : forall x0, In x0 xs -> (length (g x0) <= M)%nat)
      by (intros x0 Hx0; apply H; right; exact Hx0).
    assert (IHxs : (length (flat_map g xs) <= length xs * M)%nat) by (apply IH; exact Hxs).
    lia.
Qed.

(* 有序对列表长度上界 *)
Lemma length_all_pairs_lt_bound : forall N, (length (all_pairs_lt N) <= N * N)%nat.
Proof.
  intro N0.
  unfold all_pairs_lt, all_pairs_lt_aux.
  induction N0 as [|m IH].
  - simpl; lia.
  - simpl flat_map at 1.
    rewrite length_app, length_map.
    replace (S m - 1)%nat with m by lia.
    assert (Hflat : (length (flat_map (fun i => map (fun j => (i, j)) (seq (S i) (m - i))) (seq 1 m))
                    <= length (seq 1 m) * m)%nat).
    {
      apply length_flat_map_bound with (M := m).
      intros i Hi. apply in_seq in Hi. destruct Hi as [Hi1 Hi2].
      rewrite length_map, length_seq.
      lia.
    }
    rewrite length_seq in Hflat.
    simpl (S m * S m)%nat.
    rewrite length_seq.
    rewrite Nat.sub_0_r.
    lia.
Qed.

(* 常值映射的右折叠求和公式 *)
Lemma fold_right_const (l : list (nat * nat)) (r : R) :
  fold_right Rplus 0 (map (fun _ => r) l) = INR (length l) * r.
Proof.
  induction l as [| a l IH].
  - cbn; ring.
  - cbn [map fold_right].
    rewrite IH.
    rewrite length_cons, S_INR.
    ring.
Qed.

(* 任意类型常值映射的右折叠求和公式 *)
Lemma fold_right_const_any {A : Type} (r : R) (l : list A) :
  fold_right Rplus 0 (map (fun _ => r) l) = INR (length l) * r.
Proof.
  induction l as [|x l IH].
  - simpl. ring.
  - simpl fold_right. simpl map. rewrite IH.
    rewrite length_cons, S_INR. ring.
Qed.

(* 坏事件权重上界 *)
Theorem bad_event_weight_bound :
  let delta := INR N * INR N * p * p in
  sum_over_subsets_weight p N (bad_event_b c f) <= delta.
Proof.
  intro delta.
  set (pairs := all_pairs_lt N).

  assert (H_bad_alt : sum_over_subsets_weight p N (bad_event_b c f) <=
                      sum_over_subsets_weight p N
                        (fun I => existsb (fun '(a,b) => (inb a I) && (inb b I)) pairs)).
  {
    apply sum_over_subsets_weight_mono_in.
    intros I Hin Hb.
    apply bad_event_b_true_iff in Hb.
    destruct Hb as (i & j & Hi & Hj & Hij & Hlt).
    set (a := nth i I 0%nat).
    set (b := nth j I 0%nat).

    assert (H_bound : Forall (fun x : nat => (x < N)%nat) I).
    { apply all_subsets_upto_Forall_lt; exact Hin. }

    assert (Ha_lt_N : (a < N)%nat).
    { unfold a; apply Forall_nth; [apply H_bound | exact Hi]. }
    assert (Hb_lt_N : (b < N)%nat).
    { unfold b; apply Forall_nth; [apply H_bound | exact Hj]. }

    assert (H_NoDup : NoDup I) by (apply all_subsets_NoDup; exact Hin).

    assert (Hneq : a <> b).
    {
      unfold a, b; intro Heq.
      apply (Nat.lt_neq i j Hij).
      eapply NoDup_nth with (d := 0%nat) in H_NoDup; eauto.
    }

    assert (Ha_in : inb a I = true) by (apply inb_true_iff; apply nth_In; exact Hi).
    assert (Hb_in : inb b I = true) by (apply inb_true_iff; apply nth_In; exact Hj).

    destruct (Nat.lt_trichotomy a b) as [H_lt | [Heq | H_gt]].
    - assert (Hpair_in : In (a, b) pairs).
      { apply in_all_pairs_lt_iff; split; assumption. }
      apply existsb_exists; exists (a, b); split; [exact Hpair_in |].
      simpl; rewrite Ha_in, Hb_in; reflexivity.
    - exfalso; exact (Hneq Heq).
    - assert (Hpair_in : In (b, a) pairs).
      { apply in_all_pairs_lt_iff; split; assumption. }
      apply existsb_exists; exists (b, a); split; [exact Hpair_in |].
      simpl; rewrite Ha_in, Hb_in; apply Bool.andb_comm.
  }

  apply Rle_trans with (fold_right Rplus 0
    (map (sum_over_subsets_weight p N)
         (map (fun '(a,b) => (fun I : list nat => (inb a I) && (inb b I))) pairs))).
  {
    apply Rle_trans with (sum_over_subsets_weight p N
      (fun I => existsb (fun '(a,b) => (inb a I) && (inb b I)) pairs)).
    - exact H_bad_alt.
    - apply sum_over_subsets_weight_exists_pair_le.
  }
  {
    rewrite map_map.
    assert (H_all_pairs_eq : forall a b, (a < N)%nat -> (b < N)%nat -> a <> b ->
      sum_over_subsets_weight p N (fun I => (inb a I) && (inb b I)) = p * p).
    { intros a b Ha Hb Hneq; apply prob_pair_inclusion; assumption. }
    assert (H_map_eq : map (sum_over_subsets_weight p N)
                         (map (fun '(a,b) => (fun I : list nat => (inb a I) && (inb b I))) pairs)
                     = map (fun _ => p * p) pairs).
    {
      rewrite map_map.
      apply map_ext_in; intros (a,b) Hin.
      apply in_all_pairs_lt_iff in Hin as (Hlt & HN).
      assert (HaN : (a < N)%nat) by lia.
      assert (HbN : (b < N)%nat) by exact HN.
      assert (Hneq : a <> b) by lia.
      apply H_all_pairs_eq; assumption.
    }
    rewrite <- map_map.
    rewrite H_map_eq.

    rewrite fold_right_const_any.

    assert (H_len_bound_nat : (length pairs <= N * N)%nat).
    { apply length_all_pairs_lt_bound. }
    assert (H_len_real : INR (length pairs) <= INR (N * N)).
    { apply le_INR; exact H_len_bound_nat. }

    assert (Hp_sq_nonneg : 0 <= p * p).
    { apply Rmult_le_pos; apply Rlt_le; exact Hp_pos. }

    apply Rle_trans with (INR (N * N) * (p * p)).
    - apply Rmult_le_compat_r; [exact Hp_sq_nonneg | exact H_len_real].
    - assert (H_eq : INR (N * N) * (p * p) = delta).
      { rewrite mult_INR. unfold delta. ring. }
      rewrite H_eq.
      apply Rle_refl.
  }
Qed.

(* 布尔谓词权重和的互补分解 *)
Lemma sum_over_subsets_weight_complement (P : list nat -> bool) :
  sum_over_subsets_weight p N (fun _ => true) =
  sum_over_subsets_weight p N P + sum_over_subsets_weight p N (fun I => negb (P I)).
Proof.
  unfold sum_over_subsets_weight.
  set (w := weight_of_subset p N).
  induction (all_subsets N) as [|I l IH]; simpl.
  - ring.
  - destruct (P I) eqn:HP; simpl; rewrite IH; ring.
Qed.

(* 权重和为正则存在满足谓词且权重大于0的子集 *)
Lemma sum_positive_exists (P : list nat -> bool) :
  sum_over_subsets_weight p N P > 0 ->
  exists I, In I (all_subsets N) /\ P I = true /\ weight_of_subset p N I > 0.
Proof.
  unfold sum_over_subsets_weight.
  intros Hsum.
  induction (all_subsets N) as [|I l IH]; simpl in Hsum.
  - lra.
  - destruct (P I) eqn:HP; simpl in Hsum.
    + assert (Hw_nonneg : 0 <= weight_of_subset p N I)
          by (apply weight_of_subset_nonneg, Hp_range).
      destruct (Rlt_le_dec 0 (weight_of_subset p N I)) as [Hpos | Hzero].
      * exists I; split; [left; reflexivity | split; [exact HP | exact Hpos]].
      * assert (Hpos_tail : fold_right Rplus 0
              (map (fun I0 => if P I0 then weight_of_subset p N I0 else 0) l) > 0).
          { lra. }
        apply IH in Hpos_tail as [J [Hin [HPJ HposJ]]].
        exists J; split; [right; exact Hin | split; [exact HPJ | exact HposJ]].
    + rewrite Rplus_0_l in Hsum.
      apply IH in Hsum as [J [Hin [HPJ HposJ]]].
      exists J; split; [right; exact Hin | split; [exact HPJ | exact HposJ]].
Qed.

(* 原所有权重和引理，由泛化版本直接得到 *)
Lemma sum_weights_all_true :
  sum_over_subsets_weight p N (fun _ => true) = 1%R.
Proof. apply sum_weights_all_true_general. Qed.

(* 定理：概率下界与存在性 *)
Theorem sparse_subset_exists_constructive :
  (INR N * INR N * p * p < 1)%R ->
  exists I : list nat,
    In I (all_subsets N) /\
    NoDup I /\
    (forall (i j : nat), (i < length I)%nat -> (j < length I)%nat -> (i < j)%nat ->
       INR (f (nth j I 0%nat)) >= INR c * INR c * INR (f (nth i I 0%nat))) /\
    weight_of_subset p N I > 0.
Proof.
  intros Hdelta.
  set (delta := INR N * INR N * p * p) in *.

  assert (H_all : sum_over_subsets_weight p N (fun _ => true) = 1%R).
  { apply sum_weights_all_true. }

  assert (H_bad_bound : sum_over_subsets_weight p N (bad_event_b c f) <= delta).
  { apply bad_event_weight_bound. }

  assert (H_good_pos : sum_over_subsets_weight p N (fun I => negb (bad_event_b c f I)) > 0).
  {
    pose proof (sum_over_subsets_weight_complement (bad_event_b c f)) as H_split.
    rewrite H_all in H_split.
    lra.
  }

  apply sum_positive_exists with (P := fun I => negb (bad_event_b c f I)) in H_good_pos.
  destruct H_good_pos as [I [Hin [Hgood Hweight_pos]]].

  apply negb_true_iff in Hgood.

  assert (Hnot_exists : ~ (exists i j, (i < length I)%nat /\ (j < length I)%nat /\ (i < j)%nat /\
                              INR (f (nth j I 0%nat)) < INR c * INR c * INR (f (nth i I 0%nat)))).
  {
    intro Hex.
    apply (bad_event_b_true_iff c f I) in Hex.
    rewrite Hgood in Hex. discriminate.
  }

  assert (H_sparse : forall i j, (i < length I)%nat -> (j < length I)%nat -> (i < j)%nat ->
                    INR (f (nth j I 0%nat)) >= INR c * INR c * INR (f (nth i I 0%nat))).
  {
    intros i j Hi Hj Hij.
    apply Rle_ge.
    apply Rnot_lt_le.
    intro Hlt. apply Hnot_exists.
    exists i, j; repeat split; assumption.
  }

  assert (H_NoDup : NoDup I) by (apply all_subsets_NoDup; exact Hin).

  exists I.
  split; [exact Hin |].
  split; [exact H_NoDup |].
  split; [exact H_sparse | exact Hweight_pos].
Qed.

(* 序列 f 弱递增性证明 *)
Lemma f_inc : forall i, (f i <= f (S i))%nat.
Proof.
  intros i.
  apply INR_le.           (* 转换成实数比较 *)
  apply Rge_le.           (* 从 >= 转换为 <= *)
  eapply Rge_trans.
  - apply Hf_growth.      (* 假设：INR (f(S i)) >= INR c * INR c * INR (f i) *)
  - clear Hf_growth.
    assert (Hc2_ge_1 : (INR c * INR c >= 1)%R).
    {
      apply Rle_ge.
      apply Rle_trans with (2 * 2)%R; [lra |].
      apply Rmult_le_compat; try (apply Rle_0_1); try (apply Rge_le, Hc_R); lra.
    }
    apply Rle_ge.
    replace (INR (f i)) with (1 * INR (f i))%R at 1 by ring.
    replace (INR c * INR c * INR (f i)) with ((INR c * INR c) * INR (f i))%R by ring.
    apply Rmult_le_compat_r.
    - apply Rlt_le, lt_0_INR. specialize (Hf_ge2 i). lia.
    - apply Rge_le. exact Hc2_ge_1.
Qed.

(* 间隔两步的稀疏增长条件 *)
Lemma growth_after_two_steps :
  forall i, (INR (f (i + 2)) >= INR c * INR c * INR (f i))%R.
Proof.
  intros i.
  replace (i + 2)%nat with (S (S i)) by lia.
  pose proof (Hf_growth (S i)) as H1.
  pose proof (Hf_growth i) as H2.
  assert (Hc2_ge_1 : INR c * INR c >= 1).
  { apply Rle_ge. nra. }
  assert (H_ge : INR (f (S i)) >= INR (f i)).
  { apply Rge_trans with (INR c * INR c * INR (f i)); auto.
    apply Rle_ge.
    rewrite <- (Rmult_1_l (INR (f i))) at 1.
    apply Rmult_le_compat_r with (r := INR (f i)) (r1 := 1) (r2 := INR c * INR c).
    - apply pos_INR.
    - apply Rge_le. exact Hc2_ge_1. }
  eapply Rge_trans.
  - exact H1.
  - apply Rle_ge.
    apply Rmult_le_compat_l with (r := INR c * INR c).
    + apply Rmult_le_pos; apply pos_INR; lia.
    + apply Rge_le. exact H_ge.
Qed.

(* 稀疏条件对大间隙成立 *)
Lemma sparse_condition_holds_for_large_gap :
  forall i j, (i + 2 <= j)%nat ->
    (INR (f j) >= INR c * INR c * INR (f i))%R.
Proof.
  intros i j Hle.
  remember (j - i)%nat as d eqn:Hd.
  assert (d >= 2)%nat by lia.
  revert i j Hle Hd.
  induction d as [|d IH]; intros i j Hle Hd.
  - lia.
  - destruct d as [|d'].
    + exfalso; lia.
    + destruct d' as [|d''].
      * replace j with (i + 2)%nat by lia.
        apply growth_after_two_steps.
      * destruct j as [|j'].
        { exfalso; lia. }
        set (k := j').
        assert (Hk_diff : (k - i = S (S d''))%nat).
        { rewrite Nat.sub_succ_l in Hd by lia.
          apply eq_add_S in Hd.
          symmetry. exact Hd. }
        assert (Hk_le : (i + 2 <= k)%nat) by lia.
        assert (Hd_ge2 : (S (S d'') >= 2)%nat) by lia.
        symmetry in Hk_diff.
        specialize (IH Hd_ge2 i k Hk_le Hk_diff).
        assert (H_growth : INR (f (S k)) >= INR c * INR c * INR (f k)).
        { apply Hf_growth. }
        assert (Hc2_ge1 : INR c * INR c >= 1).
        { apply Rle_ge.
          apply Rle_trans with (r2 := 4); [lra |].
          apply Rle_trans with (r2 := 2 * 2); [lra |].
          apply Rmult_le_compat; try (apply Rle_0_1); try (apply Rge_le; apply Hc_R); lra. }
        assert (H_fk_ge_fi : INR (f k) >= INR (f i)).
        { eapply Rge_trans.
          - exact IH.
          - apply Rle_ge.
            apply Rle_trans with (r2 := INR c * INR c * INR (f i)).
            + rewrite <- Rmult_1_l at 1.
              apply Rmult_le_compat_r.
              * apply pos_INR. specialize (Hf_ge2 i). nra.
              * apply Rge_le. nra. }
        assert (H_mul : INR c * INR c * INR (f k) >= INR c * INR c * INR (f i)).
        { apply Rle_ge.
          apply Rmult_le_compat_l.
          - apply Rmult_le_pos; apply pos_INR; lia.
          - apply Rge_le. exact H_fk_ge_fi. }
        eapply Rge_trans.
        - exact H_growth.
        - exact H_mul.
Qed.

(* 用于将布尔“坏对”转换为命题并取 *)
Lemma is_bad_pair_b_true_iff (i j : nat) (I : list nat) :
  is_bad_pair_b c f i j I = true <->
  (i < length I)%nat /\
  (j < length I)%nat /\
  (i < j)%nat /\
  (INR (f (nth j I 0%nat)) < INR c * INR c * INR (f (nth i I 0%nat)))%R.
Proof.
  unfold is_bad_pair_b.
  repeat rewrite andb_true_iff.
  repeat rewrite Nat.ltb_lt.
  rewrite Rlt_bool_lt.
  firstorder.
Qed.

(* 间隙防止坏对 *)
Lemma gap_prevents_bad_pair :
  forall (I : list nat) (i j : nat),
    NoDup I -> Sorted Nat.lt I ->
    (forall k, In k I -> (k < N)%nat) ->
    is_bad_pair i j I ->
    (nth j I 0%nat - nth i I 0%nat <= 1)%nat.
Proof.
  intros I i j Hdup Hsorted Hbound Hbad_pair.
  unfold is_bad_pair in Hbad_pair.               (* 展开为布尔等式 *)
  apply is_bad_pair_b_true_iff in Hbad_pair.      (* 转换为四元组 *)
  destruct Hbad_pair as [Hi [Hj [Hij Hbad]]].     (* 析构出四个假设 *)
  apply Nat.nlt_ge. intros Hgap.
  assert (Hgap_ge2 : (nth i I 0%nat + 2 <= nth j I 0%nat)%nat) by lia.
  specialize (sparse_condition_holds_for_large_gap (nth i I 0%nat) (nth j I 0%nat) Hgap_ge2) as Hsparse.
  apply Rge_le in Hsparse.
  exfalso. apply (Rlt_not_le _ _ Hbad Hsparse).
Qed.

(* 过滤子集权重和的上界 *)
Lemma sum_weights_filter_le (P : list nat -> bool) :
  sum_over_subsets_weight p N P <= sum_over_subsets_weight p N (fun _ => true).
Proof.
  apply sum_over_subsets_weight_mono_in.
  intros I _ _. reflexivity.
Qed.

(* 拼接列表的右折叠分解 *)
Lemma fold_right_app (A : Type) (op : A -> R -> R) (a : R) (l1 l2 : list A) :
  fold_right op a (l1 ++ l2) = fold_right op (fold_right op a l2) l1.
Proof.
  induction l1 as [|x xs IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

(* 列表求和与标量乘法的分配律 *)
Lemma fold_right_Rplus_mult (a : R) (l : list R) :
  fold_right Rplus 0 (map (fun x => a * x) l) = a * fold_right Rplus 0 l.
Proof.
  induction l as [|x l IH]; simpl.
  - ring.
  - rewrite IH. ring.
Qed.

(* 序列长度恒等式 *)
Lemma length_seq : forall start len, length (seq start len) = len.
Proof.
  intros start len.
  revert start.
  induction len as [|len IH]; intros start.
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(* 自然数减法结合律 *)
Lemma sub_sub_1_eq : forall n m, (n - m - 1)%nat = (n - (m + 1))%nat.
Proof. intros; lia. Qed.

(* 所有严格递增对列表的空基例 *)
Lemma all_pairs_lt_aux_nil : forall start M, (start >= M)%nat -> all_pairs_lt_aux start M = [].
Proof.
  intros start M Hge.
  unfold all_pairs_lt_aux.
  replace (M - start)%nat with 0%nat by lia.
  simpl. (* seq start 0 化简为 []，flat_map 作用于 [] 得 [] *)
  reflexivity.
Qed.

(* 闭区间无序对数量辅助函数 *)
Definition length_all_pairs_lt_aux_closed (start N : nat) : nat :=
  if le_lt_dec start N then Nat.div2 ((N - start) * (N - start - 1)) else 0.

(* 自然数的奇偶分解公式 *)
Lemma div2_odd_spec : forall n,
  n = (2 * Nat.div2 n + (if odd n then 1 else 0))%nat.
Proof.
  exact Nat.div2_odd.
Qed.

(* 自然数除以二的加法分配律 *)
Lemma Nat_div2_add_distr : forall a b : nat,
  (Nat.div2 (a + b) = Nat.div2 a + Nat.div2 b +
    (if (odd a && odd b)%bool then 1 else 0))%nat.
Proof.
  intros a b.
  pose proof (Nat.div2_odd a) as Ha.
  pose proof (Nat.div2_odd b) as Hb.
  rewrite Ha, Hb.
  set (da := Nat.div2 a). set (db := Nat.div2 b).
  set (oa := odd a). set (ob := odd b).
  destruct oa, ob.
  - (* 情况：a 奇，b 奇 *)
    change (b2n true) with 1%nat.
    change (b2n true) with 1%nat.
    replace ((2%nat * da + 1%nat + (2%nat * db + 1%nat))%nat)
      with ((2%nat * (da + db + 1%nat))%nat) by lia.
    rewrite Nat.div2_double.
    replace ((2%nat * da + 1%nat)%nat) with (S (2%nat * da))%nat by lia.
    rewrite Nat.div2_succ_double.
    replace ((2%nat * db + 1%nat)%nat) with (S (2%nat * db))%nat by lia.
    rewrite Nat.div2_succ_double.
    rewrite (Nat.odd_succ (2%nat * da)%nat).
    rewrite (Nat.odd_succ (2%nat * db)%nat).
    rewrite !Nat.even_mul. simpl (Nat.even 2%nat).
    rewrite !Bool.orb_true_l.
    reflexivity.
  - (* 情况：a 奇，b 偶 *)
    change (b2n true) with 1%nat.
    change (b2n false) with 0%nat.
    rewrite !Nat.add_0_r.
    replace ((2%nat * da + 1%nat + 2%nat * db)%nat)
      with (S (2%nat * (da + db)))%nat by lia.
    rewrite Nat.div2_succ_double.
    replace ((2%nat * da + 1%nat)%nat) with (S (2%nat * da))%nat by lia.
    rewrite Nat.div2_succ_double.
    rewrite Nat.div2_double.
    rewrite (Nat.odd_succ (2%nat * da)%nat).
    rewrite Nat.even_mul. simpl (Nat.even 2%nat). rewrite Bool.orb_true_l.
    rewrite Nat.odd_mul. simpl (Nat.odd 2%nat). rewrite Bool.andb_false_r.
    rewrite Nat.add_0_r.
    reflexivity.
  - (* 情况：a 偶，b 奇 *)
    change (b2n false) with 0%nat.
    change (b2n true) with 1%nat.
    rewrite !Nat.add_0_r.
    replace ((2%nat * da + (2%nat * db + 1%nat))%nat)
      with (S (2%nat * (da + db)))%nat by lia.
    rewrite Nat.div2_succ_double.
    rewrite Nat.div2_double.
    replace ((2%nat * db + 1%nat)%nat) with (S (2%nat * db))%nat by lia.
    rewrite Nat.div2_succ_double.
    rewrite (Nat.odd_succ (2%nat * db)%nat).
    rewrite Nat.even_mul. simpl (Nat.even 2%nat). rewrite Bool.orb_true_l.
    rewrite Nat.odd_mul. simpl (Nat.odd 2%nat). rewrite Bool.andb_false_l.
    rewrite Nat.add_0_r.
    reflexivity.
  - (* 情况：a 偶，b 偶 *)
    change (b2n false) with 0%nat.
    change (b2n false) with 0%nat.
    rewrite !Nat.add_0_r.
    replace ((2%nat * da + 2%nat * db)%nat)
      with ((2%nat * (da + db))%nat) by lia.
    rewrite Nat.div2_double.
    rewrite Nat.div2_double.
    rewrite Nat.div2_double.
    rewrite !Nat.odd_mul. simpl (Nat.odd 2%nat). rewrite Bool.andb_false_r.
    rewrite Nat.add_0_r.
    reflexivity.
Qed.

(* 偶数二项式系数后继等式 *)
Lemma binomial2_succ_even (m : nat) :
  Nat.div2 ((2 * m * (2 * m) + 2 * m)%nat) = (2 * m + Nat.div2 (2 * m * (2 * m - 1)))%nat.
Proof.
  replace ((2 * m * (2 * m) + 2 * m)%nat)
    with (2 * (m * (2 * m) + m))%nat by ring.
  rewrite Nat.div2_double.
  replace ((2 * m * (2 * m - 1))%nat)
    with ((2 * m * (2 * m) - 2 * m)%nat).
  2: { rewrite Nat.mul_sub_distr_l, Nat.mul_1_r. reflexivity. }
  replace ((2 * m * (2 * m) - 2 * m)%nat)
    with (2 * (m * (2 * m) - m))%nat.
  2: { rewrite Nat.mul_sub_distr_l. f_equal; ring. }
  rewrite Nat.div2_double.
  replace ((2 * m + (m * (2 * m) - m))%nat)
    with ((2 * m + m * (2 * m) - m)%nat).
  2: { symmetry. apply Nat.add_sub_assoc. nia. }
  replace ((2 * m + m * (2 * m) - m)%nat)
    with ((m * (2 * m) + m)%nat).
  2: {
    transitivity ((m * (2 * m) + 2 * m - m)%nat).
    - rewrite Nat.add_comm. nia.
    - nia.
  }
  reflexivity.
Qed.

(* 奇数二项式系数后继等式 *)
Lemma binomial2_succ_odd (m : nat) :
  Nat.div2 ((2 * m + 1) * (2 * m + 1) + (2 * m + 1))%nat =
  (2 * m + 1 + Nat.div2 ((2 * m + 1) * ((2 * m + 1) - 1)))%nat.
Proof.
  replace (((2 * m + 1) * (2 * m + 1) + (2 * m + 1))%nat)
    with (2 * (m * (2 * m + 1) + (2 * m + 1)))%nat by ring.
  rewrite Nat.div2_double.
  replace ((2 * m + 1 - 1)%nat) with (2 * m)%nat by lia.
  replace (((2 * m + 1) * (2 * m))%nat) with (2 * (m * (2 * m + 1)))%nat by ring.
  rewrite Nat.div2_double.
  ring.
Qed.

(* 二项式系数后继一般形式 *)
Lemma binomial2_succ : forall k,
  Nat.div2 (Nat.mul (S k) k) = (k + Nat.div2 (Nat.mul k (k - 1)))%nat.
Proof.
  induction k as [|k IH].
  - reflexivity.
  - simpl (S (S k)).
    rewrite Nat.mul_succ_l.
    destruct (Nat.Even_or_Odd (S k)) as [[m Hm] | [m Hm]].
    + rewrite Hm; apply binomial2_succ_even.
    + rewrite Hm; apply binomial2_succ_odd.
Qed.

(* 扁平映射长度求和公式 *)
Lemma length_flat_map_aux {A B : Type} (g : A -> list B) (l : list A) :
  length (flat_map g l) = fold_right plus 0%nat (map (fun x => length (g x)) l).
Proof.
  induction l as [|a l IH].
  - simpl. reflexivity.
  - simpl flat_map.
    rewrite length_app.
    rewrite IH.
    reflexivity.
Qed.

(* 序列起始索引加一映射 *)
Lemma seq_S : forall start len, seq (S start) len = map S (seq start len).
Proof.
  intros start len. revert start. induction len; intros start; simpl.
  - reflexivity.
  - rewrite IHlen. reflexivity.
Qed.

(* 序列平移等价于映射加法 *)
Lemma seq_shift_manual (start len : nat) :
  seq start len = map (fun i => (start + i)%nat) (seq 0 len).
Proof.
  revert start. induction len as [|len IH]; intros start.
  - reflexivity.
  - simpl. rewrite IH.
    rewrite (seq_S 0 len).
    rewrite map_map.
    replace (start + 0)%nat with start by lia.
    f_equal.
    apply map_ext. intros i; lia.
Qed.

(* 序列映射与平移交换律 *)
Lemma map_length_seq_aux {A : Type} (g : nat -> list A) (start len : nat) :
  map (fun i => length (g i)) (seq start len) =
  map (fun i => length (g (start + i)%nat)) (seq 0 len).
Proof.
  rewrite (seq_shift_manual start len).
  rewrite map_map.
  reflexivity.
Qed.

(* 映射序列折叠求和逐点相等条件 *)
Lemma eq_fold_right_plus_map_seq (h1 h2 : nat -> nat) (len : nat) :
  (forall i, (i < len)%nat -> h1 i = h2 i) ->
  fold_right plus 0%nat (map h1 (seq 0 len)) =
  fold_right plus 0%nat (map h2 (seq 0 len)).
Proof.
  intros Heq.
  assert (Hmap : map h1 (seq 0 len) = map h2 (seq 0 len)).
  { apply map_ext_in. intros i Hin.
    apply in_seq in Hin.
    apply Heq. lia. }
  rewrite Hmap. reflexivity.
Qed.

(* 全序对辅助长度平移递推 *)
Lemma length_all_pairs_lt_aux_shift (start M : nat) :
  length (all_pairs_lt_aux (S start) (S M)) = length (all_pairs_lt_aux start M).
Proof.
  unfold all_pairs_lt_aux.
  rewrite !length_flat_map_aux.
  rewrite (seq_shift_manual (S start) (S M - S start)%nat).
  rewrite map_map.
  rewrite (seq_shift_manual start (M - start)%nat).
  rewrite map_map.
  assert (Heq_len : (S M - S start)%nat = (M - start)%nat) by lia.
  rewrite Heq_len.
  apply eq_fold_right_plus_map_seq.
  intros i Hi. simpl.
  replace (S (S start + i))%nat with (S (start + i) + 1)%nat by lia.
  replace (S M - S (S start + i))%nat with (M - S (start + i))%nat by lia.
  rewrite !length_map, !length_seq.
  reflexivity.
Qed.

(* 闭合长度递推公式 *)
Lemma length_all_pairs_lt_aux_closed_succ (M : nat) :
  length_all_pairs_lt_aux_closed 0 (S M) =
  (M + length_all_pairs_lt_aux_closed 0 M)%nat.
Proof.
  unfold length_all_pairs_lt_aux_closed.
  destruct (le_lt_dec 0 (S M)) as [_|H]; [|lia].
  replace (S M - 0)%nat with (S M) by lia.
  replace (S M - 1)%nat with M by lia.
  rewrite binomial2_succ with (k:=M).
  destruct (le_lt_dec 0 M) as [_|H']; [|exfalso; lia].
  replace (M - 0)%nat with M by lia.
  replace (M - 0 - 1)%nat with (M - 1)%nat by lia.
  ring_simplify. reflexivity.
Qed.

(* 全序对辅助长度与闭合形式一致（起点为零） *)
Lemma length_all_pairs_lt_aux_eq_start0 (M : nat) :
  length (all_pairs_lt_aux 0 M) = length_all_pairs_lt_aux_closed 0 M.
Proof.
  induction M as [|M IH].
  - reflexivity.
  - unfold all_pairs_lt_aux at 1.
    rewrite Nat.sub_0_r.
    simpl flat_map.
    rewrite length_app, length_map, length_seq.
    replace (S M - 1)%nat with M by lia.
    assert (H_eq : flat_map (fun i => map (fun j => (i, j)) (seq (S i) (M - i)%nat)) (seq 1 M) =
                   all_pairs_lt_aux 1 (S M)).
    {
      unfold all_pairs_lt_aux.
      replace (S M - 1)%nat with M by lia.
      f_equal.
    }
    rewrite H_eq.
    replace (length (all_pairs_lt_aux 1 (S M)))
      with (length (all_pairs_lt_aux 0 M)).
    2: { symmetry. apply length_all_pairs_lt_aux_shift. }
    rewrite Nat.sub_0_r.
    rewrite IH.
    symmetry.
    apply length_all_pairs_lt_aux_closed_succ.
Qed.

(* 全序对辅助长度与闭合形式一致（起点大于零） *)
Lemma length_all_pairs_lt_aux_eq_start_gt0 :
  forall start M,
    (start > 0)%nat ->
    length (all_pairs_lt_aux start M) = length_all_pairs_lt_aux_closed start M.
Proof.
  intros start M Hpos.
  remember (M - start)%nat as d eqn:Hd.
  revert start M Hpos Hd.
  induction d as [|d IH]; intros start M Hpos Hd.
  - assert (Hle : (M <= start)%nat) by lia.
    destruct (le_lt_dec start M) as [Hle' | Hlt'].
    + assert (M = start) by lia.
      subst M.
      unfold all_pairs_lt_aux.
      rewrite Nat.sub_diag.
      simpl.
      unfold length_all_pairs_lt_aux_closed.
      destruct (le_lt_dec start start) as [| ?]; [| lia].
      rewrite Nat.sub_diag.
      simpl.
      reflexivity.
    + unfold all_pairs_lt_aux.
      replace (M - start)%nat with 0%nat by lia.
      simpl.
      unfold length_all_pairs_lt_aux_closed.
      destruct (le_lt_dec start M) as [Hle'' | ?]; [lia|].
      reflexivity.
  - assert (Hlt : (start < M)%nat) by lia.
    assert (Heq_S_diff : (M - S start)%nat = d) by lia.
    unfold all_pairs_lt_aux.
    replace (M - start)%nat with (S d) by lia.
    simpl.
    rewrite length_app.
    rewrite length_map, length_seq.
    replace (M - S start)%nat with d by lia.
    assert (H_rest_eq : 
      flat_map (fun i => map (fun j => (i, j)) (seq (S i) (M - S i)%nat))
               (seq (S start) d) = 
      all_pairs_lt_aux (S start) M).
    {
      unfold all_pairs_lt_aux.
      rewrite Heq_S_diff.
      reflexivity.
    }
    rewrite H_rest_eq.
    rewrite (IH (S start) M).
    - unfold length_all_pairs_lt_aux_closed.
      destruct (le_lt_dec start M) as [| HltM]; [| lia].
      destruct (le_lt_dec (S start) M) as [| HSlM]; [| lia].
      replace (M - start)%nat with (S d) by lia.
      replace (M - S start)%nat with d by lia.
      simpl.
      rewrite !Nat.sub_0_r.
      replace (d + d * d)%nat with (S d * d)%nat by lia.
      symmetry.
      apply binomial2_succ.
    - lia.
    - symmetry; exact Heq_S_diff.
Qed.

(* 全序对辅助长度与闭合形式一致 *)
Lemma length_all_pairs_lt_aux_eq :
  forall start M,
    length (all_pairs_lt_aux start M) = length_all_pairs_lt_aux_closed start M.
Proof.
  intros start M.
  destruct (Nat.eq_dec start 0) as [-> | Hpos].
  - apply length_all_pairs_lt_aux_eq_start0.
  - apply length_all_pairs_lt_aux_eq_start_gt0.
    lia.
Qed.

(* 闭合长度平移恒等式 *)
Lemma length_all_pairs_lt_aux_closed_shift :
  forall start n,
    length_all_pairs_lt_aux_closed start n =
    length_all_pairs_lt_aux_closed 0 (n - start)%nat.
Proof.
  intros start n.
  unfold length_all_pairs_lt_aux_closed.
  destruct (le_lt_dec start n) as [Hle | Hgt].
  - destruct (le_lt_dec 0 (n - start)%nat) as [H0 | H0];
      [| exfalso; lia].
    rewrite Nat.sub_0_r.
    reflexivity.
  - assert ((n - start)%nat = 0%nat) by lia.
    rewrite H.
    destruct (le_lt_dec 0 0); [reflexivity | lia].
Qed.

(* n与n-1的乘积为偶数 *)
Lemma even_mul_pred : forall n : nat, exists k : nat, (n * (n - 1) = 2 * k)%nat.
Proof.
  intro n.
  destruct (Nat.Even_or_Odd n) as [[k Hk] | [k Hk]].
  - (* n = 2k *)
    rewrite Hk.
    exists (k * (2 * k - 1))%nat.
    rewrite <- Nat.mul_assoc.
    reflexivity.
  - (* n = 2k+1 *)
    rewrite Hk.
    exists ((2 * k + 1) * k)%nat.
    replace ((2 * k + 1 - 1))%nat with (2 * k)%nat by lia.
    rewrite (Nat.mul_comm (2 * k + 1) (2 * k)).
    rewrite <- Nat.mul_assoc.
    rewrite (Nat.mul_comm k (2 * k + 1)).
    reflexivity.
Qed.

(* 全序对列表长度与完全图边数关系 *)
Lemma length_all_pairs_lt_aux_0_double :
  forall M,
    2%R * INR (length (all_pairs_lt_aux 0 M)) = INR (M * (M - 1))%nat.
Proof.
  intro M.
  rewrite length_all_pairs_lt_aux_eq.
  unfold length_all_pairs_lt_aux_closed.
  destruct (le_lt_dec 0 M) as [Hle | Hnle]; [| exfalso; lia].
  rewrite (Nat.sub_0_r M).
  replace (M - 0 - 1)%nat with (M - 1)%nat by lia.
  destruct (even_mul_pred M) as [k Hk].
  rewrite Hk.
  rewrite Nat.div2_double.
  rewrite mult_INR.
  simpl (INR 2).
  ring.
Qed.

(* 全序对辅助长度加倍恒等式 *)
Lemma length_all_pairs_lt_aux_double :
  forall start M,
    2 * INR (length (all_pairs_lt_aux start M)) =
    INR ((M - start) * (M - start - 1)).
Proof.
  intros start M.
  rewrite length_all_pairs_lt_aux_eq.
  unfold length_all_pairs_lt_aux_closed.
  destruct (le_lt_dec start M) as [Hle | Hgt].
  - set (d := (M - start)%nat).
    assert (Hd_times : exists k, (d * (d - 1) = 2 * k)%nat) by apply even_mul_pred.
    destruct Hd_times as [k Hk].
    rewrite Hk.
    rewrite Nat.div2_double.
    rewrite mult_INR.
    simpl (INR 2).
    ring.
  - assert (Hd0 : (M - start)%nat = 0%nat) by lia.
    rewrite Hd0.
    simpl.
    ring.
Qed.

(* INR单射性 *)
Lemma INR_inj_manual : forall n m : nat, INR n = INR m -> n = m.
Proof.
  induction n; intros m H.
  - destruct m as [|m].
    + reflexivity.
    + rewrite (S_INR m) in H; simpl in H.
      destruct (pos_INR m) as [Hpos | Heq0]; exfalso; lra.
  - destruct m as [|m].
    + rewrite (S_INR n) in H; simpl in H.
      destruct (pos_INR n) as [Hpos | Heq0]; exfalso; lra.
    + rewrite !S_INR in H.
      assert (H_eq : INR n = INR m) by lra.
      apply eq_S.
      apply (IHn m H_eq).
Qed.

(* 全序对列表长度的二次公式 *)
Lemma length_all_pairs_lt : forall N,
  (2 * length (all_pairs_lt N))%nat = (N * N - N)%nat.
Proof.
  intros N0.
  apply INR_inj_manual.
  rewrite mult_INR.
  change (INR 2) with 2%R.
  unfold all_pairs_lt.
  rewrite length_all_pairs_lt_aux_double with (start := 0%nat).
  replace (N0 - 0)%nat with N0 by lia.
  replace (N0 - 0 - 1)%nat with (N0 - 1)%nat by lia.
  assert (H_nat_eq : (N0 * N0 - N0 = N0 * (N0 - 1))%nat).
  { destruct N0 as [|N0']; lia. }
  rewrite H_nat_eq.
  reflexivity.
Qed.

(* 将上限提升一阶时，新元素为上限的权重递推公式 *)
Lemma weight_of_subset_Sn_cons n I :
  (length I <= n)%nat ->
  weight_of_subset p (S n) (n :: I) = p * weight_of_subset p n I.
Proof.
  intros Hlen.
  unfold weight_of_subset.
  rewrite length_cons.
  replace (S n - S (length I))%nat with (n - length I)%nat by lia.
  simpl.
  ring.
Qed.

(* 保持旧元素权重递推 *)
Lemma weight_of_subset_Sn_old n I :
  (length I <= n)%nat ->
  weight_of_subset p (S n) I = (1 - p) * weight_of_subset p n I.
Proof.
  intros Hlen.
  unfold weight_of_subset.
  replace (S n - length I)%nat with (S (n - length I))%nat by lia.
  simpl.
  ring.
Qed.

(* 右折叠的外延相等 *)
Lemma fold_right_ext (l : list (list nat)) (h1 h2 : list nat -> R) :
  (forall I, In I l -> h1 I = h2 I) ->
  fold_right Rplus 0 (map h1 l) = fold_right Rplus 0 (map h2 l).
Proof.
  induction l as [|I l IH]; simpl; intros H.
  - reflexivity.
  - rewrite H; [| left; reflexivity].
    rewrite IH; [reflexivity | intros J Hin; apply H; right; exact Hin].
Qed.

(* 子集权重和的并集上界 *)
Lemma sum_over_subsets_weight_union (A B : list nat -> bool) :
  sum_over_subsets_weight p N (fun I => A I || B I) <=
  sum_over_subsets_weight p N A + sum_over_subsets_weight p N B.
Proof.
  unfold sum_over_subsets_weight.
  apply fold_right_or_le.
  intros I; apply weight_of_subset_nonneg, Hp_range.
Qed.

(* 子集权重和或运算的上界 *)
Lemma sum_over_subsets_weight_or_le (E1 E2 : list nat -> bool) :
  sum_over_subsets_weight p N (fun I => E1 I || E2 I) <=
  sum_over_subsets_weight p N E1 + sum_over_subsets_weight p N E2.
Proof.
  unfold sum_over_subsets_weight.
  apply fold_right_or_le.
  intros I; apply weight_of_subset_nonneg, Hp_range.
Qed.

(* 恒假谓词的子集权重和为零 *)
Lemma sum_over_subsets_weight_false :
  sum_over_subsets_weight p N (fun _ => false) = 0%R.
Proof.
  unfold sum_over_subsets_weight.
  induction (all_subsets N) as [|I l IH]; simpl; [reflexivity |].
  rewrite IH; ring.
Qed.

(* 有限事件并集的子集权重和上界 *)
Lemma sum_over_subsets_weight_finite_union (events : list (list nat -> bool)) :
  sum_over_subsets_weight p N (fun I => existsb (fun P => P I) events) <=
  fold_right Rplus 0 (map (sum_over_subsets_weight p N) events).
Proof.
  induction events as [|E events IH]; simpl.
  - rewrite sum_over_subsets_weight_false. apply Rle_refl.
  - etransitivity.
    + apply sum_over_subsets_weight_union.
    + simpl. apply Rplus_le_compat_l. exact IH.
Qed.

(* 列表元素均小于上界 *)
Lemma all_subsets_upto_elt_lt : forall n I,
  In I (all_subsets_upto n) -> Forall (fun x => (x < n)%nat) I.
Proof.
  induction n; intros I Hin; simpl in Hin.
  - destruct Hin as [<- | []]; constructor.
  - apply in_app_iff in Hin as [Hin' | Hin].
    + apply in_map_iff in Hin' as [J [Heq HinJ]]; subst.
      constructor; [lia |].
      apply Forall_impl with (P := fun a : nat => (a < n)%nat) (Q := fun a : nat => (a < S n)%nat).
      * intros m Hm; lia.
      * apply IHn; exact HinJ.
    + apply Forall_impl with (P := fun a : nat => (a < n)%nat) (Q := fun a : nat => (a < S n)%nat).
      * intros m Hm; lia.
      * apply IHn; exact Hin.
Qed.

(* 映射求和单调性 *)
Lemma fold_right_map_le (l : list (list nat)) (F G : list nat -> R) :
  (forall x : list nat, In x l -> F x <= G x) ->
  fold_right Rplus 0 (map F l) <= fold_right Rplus 0 (map G l).
Proof.
  induction l as [|x l IH]; simpl; intros Hle.
  - lra.
  - apply Rplus_le_compat.
    + apply Hle; left; reflexivity.
    + apply IH; intros y Hy; apply Hle; right; exact Hy.
Qed.

(* 坏事件蕴含存在一对元素 *)
Lemma bad_event_implies_ex_pair :
  sum_over_subsets_weight p N (bad_event_b c f) <=
  sum_over_subsets_weight p N
    (fun I => existsb (fun '(a,b) => (inb a I) && (inb b I)) (all_pairs_lt N)).
Proof.
  apply sum_over_subsets_weight_mono_in.
  intros I Hin Hbad.
  apply bad_event_b_true_iff in Hbad.
  destruct Hbad as (i & j & Hi & Hj & Hij & Hlt).
  set (a := nth i I 0%nat).
  set (b := nth j I 0%nat).
  assert (Ha_in : In a I) by (apply nth_In; exact Hi).
  assert (Hb_in : In b I) by (apply nth_In; exact Hj).
  assert (H_forall : Forall (fun x => (x < N)%nat) I)
    by (apply all_subsets_upto_Forall_lt; exact Hin).
  pose proof (proj1 (Forall_forall (fun x => (x < N)%nat) I) H_forall) as H_all.
  assert (Ha_lt_N : (a < N)%nat) by (apply H_all; exact Ha_in).
  assert (Hb_lt_N : (b < N)%nat) by (apply H_all; exact Hb_in).
  assert (H_NoDup : NoDup I) by (apply all_subsets_NoDup; exact Hin).
  assert (Hneq : a <> b).
  { intro Heq. subst a. assert (i = j) by
      (eapply NoDup_nth with (d := 0%nat); eauto). lia. }
  assert (Ha_inb : inb a I = true) by (apply inb_true_iff; exact Ha_in).
  assert (Hb_inb : inb b I = true) by (apply inb_true_iff; exact Hb_in).
  destruct (Nat.lt_trichotomy a b) as [H_lt | [Heq | H_gt]]; [| contradiction |].
  - assert (Hpair : In (a, b) (all_pairs_lt N)).
    { apply in_all_pairs_lt_iff; split; assumption. }
    apply existsb_exists; exists (a, b); split; [exact Hpair |].
    simpl; rewrite Ha_inb, Hb_inb; reflexivity.
  - assert (Hpair : In (b, a) (all_pairs_lt N)).
    { apply in_all_pairs_lt_iff; split; assumption. }
    apply existsb_exists; exists (b, a); split; [exact Hpair |].
    simpl; rewrite Ha_inb, Hb_inb; apply Bool.andb_comm.
Qed.

(* 添加新元素时的权重递推 *)
Lemma weight_Sn_cons : forall n I,
  (length I <= n)%nat ->
  weight_of_subset p (S n) (n :: I) = p * weight_of_subset p n I.
Proof.
  intros n I Hlen.
  unfold weight_of_subset; simpl.
  replace (S n - S (length I))%nat with (n - length I)%nat by lia.
  simpl; ring.
Qed.

(* 保留旧子集时的权重递推 *)
Lemma weight_Sn_old : forall n I,
  (length I <= n)%nat ->
  weight_of_subset p (S n) I = (1 - p) * weight_of_subset p n I.
Proof.
  intros n I Hlen.
  unfold weight_of_subset.
  replace (S n - length I)%nat with (S (n - length I))%nat by lia.
  simpl; ring.
Qed.

(* 固定尺寸全部子集权重和恒为一 *)
Lemma weight_sum_one : forall k : nat,
  fold_right Rplus 0 (map (weight_of_subset p k) (all_subsets_upto k)) = 1.
Proof.
  intro k; induction k as [|k IHk].
  - simpl; unfold weight_of_subset; simpl; ring.
  - simpl all_subsets_upto; rewrite map_app, fold_right_Rplus_app.
    set (prev_k := all_subsets_upto k) in *.
    assert (Hlen_k : forall I, In I prev_k -> (length I <= k)%nat)
      by (intros; apply all_subsets_upto_length_le; auto).

    assert (Hcons_w : fold_right Rplus 0
      (map (weight_of_subset p (S k)) (map (fun l => k :: l) prev_k)) = p).
    { rewrite map_map.
      assert (H_map_eq : map (fun I : list nat => weight_of_subset p (S k) (k :: I)) prev_k
                         = map (fun I => p * weight_of_subset p k I) prev_k).
      { apply map_ext_in; intros I Hin; apply weight_Sn_cons, Hlen_k; auto. }
      rewrite H_map_eq.
      rewrite fold_right_Rplus_factor.
      rewrite IHk; ring.
    }

    assert (Hold_w : fold_right Rplus 0 (map (weight_of_subset p (S k)) prev_k) = 1-p).
    { assert (H_map_eq : map (weight_of_subset p (S k)) prev_k
                         = map (fun I => (1-p) * weight_of_subset p k I) prev_k).
      { apply map_ext_in; intros I Hin; apply weight_Sn_old, Hlen_k; auto. }
      rewrite H_map_eq.
      rewrite fold_right_Rplus_factor.
      rewrite IHk; ring.
    }

    rewrite Hcons_w, Hold_w; ring.
Qed.

(* 序列 f 严格递增 *)
Lemma f_strict_inc : forall i j, (i < j)%nat -> (f i < f j)%nat.
Proof.
  intros i j Hlt.
  assert (Hf_inc : forall k, (f k < f (S k))%nat).
  { intro k.
    apply INR_lt.
    pose proof (Hf_growth k) as Hg.
    apply Rge_le in Hg.
    assert (H_one_lt_sq : 1 < INR c * INR c).
    { apply Rlt_le_trans with 4; [lra |].
      change 4 with (2 * 2).
      apply Rmult_le_compat; lra. }
    assert (H_lt: INR (f k) < INR c * INR c * INR (f k)).
    { rewrite <- (Rmult_1_r (INR (f k))) at 1.
      change (INR c * INR c * INR (f k)) with ((INR c * INR c) * INR (f k)).
      rewrite (Rmult_comm (INR c * INR c) (INR (f k))).
      apply Rmult_lt_compat_l; [| exact H_one_lt_sq].
      apply lt_0_INR; specialize (Hf_ge2 k); lia. }
    eapply Rlt_le_trans; eauto. }
  induction Hlt.
  - apply Hf_inc.
  - apply Nat.lt_trans with (f m); [apply IHHlt | apply Hf_inc].
Qed.

(* 函数值小则索引小 *)

(* 序列值嵌入严格界 *)
Lemma INR_f_strict_bound : forall a b,
  (f a >= 2)%nat ->
  INR (f b) >= INR c * INR c * INR (f a) ->
  INR (f a) < INR (f b).
Proof.
  intros a b Hge2 Hineq.
  assert (INR_fa_pos : INR (f a) > 0).
  { apply INR_pos; lia. }
  assert (INR_c_sq_gt_1 : INR c * INR c > 1).
  {
    assert (Hc_ge2' : INR c >= 2).
    {
      apply le_INR in Hc_ge2; simpl in Hc_ge2.
      lra.
    }
    nra.
  }
  apply Rlt_le_trans with (INR c * INR c * INR (f a)).
  - rewrite <- (Rmult_1_l (INR (f a))) at 1.
    apply Rmult_lt_compat_r.
    + exact INR_fa_pos.
    + exact INR_c_sq_gt_1.
  - now apply Rge_le.
Qed.

(* 序列 f 一步严格递增 *)
Lemma f_S_strict_inc : forall i, (f i < f (S i))%nat.
Proof.
  intro i.
  apply INR_lt.
  apply INR_f_strict_bound with (a := i) (b := S i).
  - apply Hf_ge2.
  - apply Hf_growth.
Qed.

(* 值严格递增蕴含索引严格递增 *)
Lemma f_lt_implies_lt : forall i j, (f i < f j)%nat -> (i < j)%nat.
Proof.
  intros i j Hfj.
  destruct (Nat.lt_trichotomy i j) as [Hlt | [Heq | Hgt]]; auto.
  - subst. lia.
  - apply f_strict_inc in Hgt. lia.
Qed.


(* 求和与该映射的加法分配律 *)
Lemma fold_right_add_map (l : list (list nat)) (F G : list nat -> R) :
  fold_right Rplus 0 (map (fun I => F I + G I) l) =
  fold_right Rplus 0 (map F l) + fold_right Rplus 0 (map G l).
Proof.
  induction l as [|a l IH]; simpl.
  - ring.
  - rewrite IH; ring.
Qed.

(* 稀疏子集蕴含有序性 *)
Lemma c_sparse_subset_impl_Sorted : forall I,
  c_sparse_subset I -> Sorted Nat.lt I.
Proof.
  intros I [Hnodup Hsp_eq].
  pose proof (proj1 (sparse_cond_b_true_iff c f I) Hsp_eq) as Hsp_forall.
  clear Hsp_eq.
  induction I as [|a I' IH].
  - constructor.
  - inversion Hnodup as [|? ? Hnotin Hnodup']; subst.
    assert (Hsp_I' : sparse_cond_b c f I' = true).
    {
      apply (proj2 (sparse_cond_b_true_iff c f I')).
      intros i j Hi Hj Hij.
      apply (Hsp_forall (S i) (S j)); simpl; lia.
    }
    assert (H_csparse_I' : c_sparse_subset I')
      by (split; [exact Hnodup' | exact Hsp_I']).
    destruct H_csparse_I' as [Hnodup_I' Hsp_eq_I'].
    assert (Hsp_forall_I' : forall i j, (i < length I')%nat -> (j < length I')%nat -> (i < j)%nat ->
      INR (f (nth j I' 0%nat)) >= INR c * INR c * INR (f (nth i I' 0%nat))).
    { apply (proj1 (sparse_cond_b_true_iff c f I') Hsp_eq_I'). }
    specialize (IH Hnodup_I' Hsp_forall_I').
    constructor.
    - exact IH.
    - destruct I' as [|b I''].
      + constructor.
      + constructor.
        assert (H_bound: INR (f (nth 1 (a :: b :: I'') 0%nat)) >=
                        INR c * INR c * INR (f (nth 0 (a :: b :: I'') 0%nat))).
        { apply (Hsp_forall 0%nat 1%nat); simpl; lia. }
        simpl in H_bound.
        assert (H_fa_lt_fb : INR (f a) < INR (f b)).
        { apply INR_f_strict_bound; [apply Hf_ge2 | exact H_bound]. }
        apply INR_lt in H_fa_lt_fb.
        apply f_lt_implies_lt; exact H_fa_lt_fb.
Qed.

(* 事件等价时的权重和不变性（列表内相等） *)
Lemma sum_over_subsets_weight_morphism_in (E1 E2 : list nat -> bool) :
  (forall I, In I (all_subsets N) -> E1 I = E2 I) ->
  sum_over_subsets_weight p N E1 = sum_over_subsets_weight p N E2.
Proof.
  intros Heq.
  unfold sum_over_subsets_weight.
  f_equal.
  apply map_ext_in; intros I Hin.
  rewrite (Heq I Hin).
  reflexivity.
Qed.

(* 事件等价时的权重和不变性（全局相等） *)
Lemma sum_over_subsets_weight_morphism (E1 E2 : list nat -> bool) :
  (forall I, E1 I = E2 I) ->
  sum_over_subsets_weight p N E1 = sum_over_subsets_weight p N E2.
Proof.
  intros Heq.
  apply sum_over_subsets_weight_morphism_in; intros I _; apply Heq.
Qed.

(* 互补命题的权重和 *)
Lemma single_case_sum (I : list nat) (w : R) (P : list nat -> bool) :
  (if P I then w else 0) + (if negb (P I) then w else 0) = w.
Proof.
  destruct (P I) eqn:HP.
  - simpl; ring.
  - simpl; ring.
Qed.

(* 构造性不小于关系 *)
Lemma Rnot_lt_ge_constructive : forall r1 r2, ~ (r1 < r2) -> r1 >= r2.
Proof.
  intros r1 r2 Hlt.
  destruct (Rtotal_order r1 r2) as [Hcase|[Heq|Hgt]].
  - exfalso; apply Hlt, Hcase.
  - subst; unfold Rge; right; reflexivity.
  - unfold Rge; left; apply Hgt.
Qed.

(* 实数≥与<的布尔互补关系（版本1） *)
Lemma Rge_bool_negb_Rlt_bool1 : forall x y : R, Rge_bool x y = negb (Rlt_bool x y).
Proof.
  intros x y.
  unfold Rge_bool, Rlt_bool.
  destruct (Rle_or_lt y x) as [Hle | Hlt].
  - destruct (Rle_dec y x); [| contradiction].
    destruct (Rlt_dec x y); simpl; auto.
    exfalso; eapply Rlt_not_le; eassumption.
  - destruct (Rlt_dec x y); [| contradiction].
    destruct (Rle_dec y x); simpl; auto.
    exfalso; eapply Rlt_not_le; eassumption.
Qed.

(* 实数≥与<的布尔互补关系（版本2） *)
Lemma Rge_bool_negb_Rlt_bool : forall x y : R,
  Rge_bool x y = negb (Rlt_bool x y).
Proof.
  intros x y.
  unfold Rge_bool, Rlt_bool.
  destruct (Rle_or_lt y x) as [Hle | Hlt].
  - destruct (Rle_dec y x); [| contradiction].
    destruct (Rlt_dec x y); simpl; auto.
    exfalso; eapply Rlt_not_le; eassumption.
  - destruct (Rlt_dec x y); [| contradiction].
    destruct (Rle_dec y x); simpl; auto.
    exfalso; eapply Rlt_not_le; eassumption.
Qed.

(* 全称量词与存在量词在否定下的关系（单列表） *)
Lemma forallb_negb_existsb {A : Type} (l : list A) (P : A -> bool) :
  forallb (fun x => negb (P x)) l = negb (existsb P l).
Proof.
  induction l as [|a l IH]; simpl; auto.
  destruct (P a) eqn:Pa.
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(* 全称量词与存在量词在否定下的关系（双列表） *)
Lemma forallb_forallb_negb_existsb {A B : Type} (lA : list A) (lB : list B) (P : A -> B -> bool) :
  forallb (fun i => forallb (fun j => negb (P i j)) lB) lA =
  negb (existsb (fun i => existsb (fun j => P i j) lB) lA).
Proof.
  induction lA as [|a lA IH]; simpl; auto.
  rewrite forallb_negb_existsb with (l := lB) (P := P a).
  rewrite IH.
  destruct (existsb (P a) lB); simpl; auto.
Qed.

(* 全称量词的外延相等性 *)
Lemma forallb_ext {A : Type} (F G : A -> bool) (l : list A) :
  (forall x, In x l -> F x = G x) -> forallb F l = forallb G l.
Proof.
  induction l as [|a l IH]; simpl; auto.
  intros H. rewrite H; [| left; reflexivity].
  f_equal; apply IH; intros x Hx; apply H; right; exact Hx.
Qed.

(* 稀疏条件与坏事件的否定等价 *)
Lemma sparse_neg_bad_event_equiv I :
  In I (all_subsets N) ->
  sparse_cond_b c f I = negb (bad_event_b c f I).
Proof.
  intros Hin.
  unfold sparse_cond_b, bad_event_b, is_bad_pair_b.
  set (len := length I).
  set (s := seq 0 len).
  assert (Hs_in : forall k, In k s <-> (k < len)%nat).
  { intros k; unfold s; rewrite in_seq; split; [intros [? ?]|intro]; lia. }
  set (cond_sparse := fun i j =>
    if i <? j then Rge_bool (INR (f (nth j I 0%nat))) (INR c * INR c * INR (f (nth i I 0%nat)))
    else true).
  set (cond_bad := fun i j : nat =>
    (i <? length I) && (j <? length I) && (i <? j) &&
    Rlt_bool (INR (f (nth j I 0%nat))) (INR c * INR c * INR (f (nth i I 0%nat)))).
  assert (H_equiv_pair : forall i j, In i s -> In j s -> cond_sparse i j = negb (cond_bad i j)).
  {
    intros i j Hi Hj.
    apply Hs_in in Hi; apply Hs_in in Hj.
    unfold cond_sparse, cond_bad.
    destruct (i <? j) eqn:Hij.
    - assert (Hi_len : (i <? length I) = true) by (apply Nat.ltb_lt; exact Hi).
      assert (Hj_len : (j <? length I) = true) by (apply Nat.ltb_lt; exact Hj).
      rewrite Hi_len, Hj_len; simpl.
      rewrite Rge_bool_negb_Rlt_bool; reflexivity.
    - rewrite Bool.andb_false_r; reflexivity.
  }
  assert (H_main : forallb (fun i => forallb (fun j => cond_sparse i j) s) s =
                   negb (existsb (fun i => existsb (fun j => cond_bad i j) s) s)).
  {
    rewrite (forallb_ext (fun i => forallb (fun j => cond_sparse i j) s)
                         (fun i => forallb (fun j => negb (cond_bad i j)) s) s).
    - apply forallb_forallb_negb_existsb with (P := cond_bad).
    - intros i Hi. apply forallb_ext; intros j Hj. apply H_equiv_pair; auto.
  }
  unfold len.
  exact H_main.
Qed.

(* 定理：稀疏子集高概率下界 *)
Theorem sparse_subset_high_probability_sum :
  let delta := INR N * INR N * p * p in
  sum_over_subsets_weight p N (sparse_cond_b c f) >= 1 - delta.
Proof.
  intro delta.
  assert (H_all : sum_over_subsets_weight p N (fun _ => true) = 1).
  { apply sum_weights_all_true_general. }
  assert (H_bad : sum_over_subsets_weight p N (bad_event_b c f) <= delta).
  { apply bad_event_weight_bound. }
  assert (H_equiv : sum_over_subsets_weight p N (sparse_cond_b c f) =
                   sum_over_subsets_weight p N (fun I => negb (bad_event_b c f I))).
  {
    apply sum_over_subsets_weight_morphism_in.
    intros I Hin. apply sparse_neg_bad_event_equiv, Hin.
  }
  rewrite H_equiv.
  pose proof (sum_over_subsets_weight_complement (bad_event_b c f)) as H_comp_eq.
  rewrite H_all in H_comp_eq.
  assert (H_nonneg_bad : 0 <= sum_over_subsets_weight p N (bad_event_b c f)).
  {
    unfold sum_over_subsets_weight.
    induction (all_subsets N) as [|I l IH]; simpl; [lra|].
    destruct (bad_event_b c f I) eqn:Hbad; simpl.
    - assert (Hw : 0 <= weight_of_subset p N I) by apply weight_of_subset_nonneg, Hp_range.
      assert (Hfold : 0 <= fold_right Rplus 0
        (map (fun I0 => if bad_event_b c f I0 then weight_of_subset p N I0 else 0) l)).
      { exact IH. }
      lra.
    - rewrite Rplus_0_l; exact IH.
  }
  lra.
Qed.

(* 论文定理 5.2：高概率稀疏内积界保障与设计准则 *)
Theorem probabilistic_sparse_inner_bound (δ : R) :
  0 < δ ->
  (INR N * INR N * p * p < δ) ->
  sum_over_subsets_weight p N (sparse_cond_b c f) >= 1 - δ.
Proof.
  intros Hδ_pos Hdelta_lt.
  pose proof sparse_subset_high_probability_sum as Hsp.
  assert (Hge : sum_over_subsets_weight p N (sparse_cond_b c f) >=
                1 - (INR N * INR N * p * p)).
  { exact Hsp. }
  lra.
Qed.

(* 稀疏子集存在性 *)
Theorem sparse_subset_exists :
    (INR N * INR N * p * p < 1)%R ->
    exists I : list nat,
      In I (all_subsets N) /\
      NoDup I /\
      (forall (i j : nat), (i < length I)%nat -> (j < length I)%nat -> (i < j)%nat ->
         INR (f (nth j I 0%nat)) >= INR c * INR c * INR (f (nth i I 0%nat))) /\
      weight_of_subset p N I > 0.
Proof.
  exact sparse_subset_exists_constructive.
Qed.

(* 良好事件布尔判定 *)
Definition good_event_b (I : list nat) : bool :=
  let len := length I in
  forallb (fun i =>
    forallb (fun j =>
      if (i <? len) && (j <? len) && (negb (i =? j)) then
        let ni := f (nth i I 0%nat) in
        let nj := f (nth j I 0%nat) in
        let n_small := Nat.min ni nj in
        let n_large := Nat.max ni nj in
        Rge_bool
          (INR c * sqrt (INR n_small * INR n_large) / (4 * (INR n_large - INR n_small)))
          (Cnorm (Csum (fun k => psi n_small k *c Cconj (psi n_large k)) (n_small - 1)%nat))
      else true
    ) (seq 0 len)
  ) (seq 0 len).

(* 良好事件布尔等价性 *)
Lemma good_event_bP (I : list nat) :
  reflect
    (forall i j, (i < length I)%nat -> (j < length I)%nat -> i <> j ->
      let ni := f (nth i I 0%nat) in
      let nj := f (nth j I 0%nat) in
      let n_small := Nat.min ni nj in
      let n_large := Nat.max ni nj in
      Cnorm (Csum (fun k => psi n_small k *c Cconj (psi n_large k)) (n_small - 1)%nat)
        <= INR c * sqrt (INR n_small * INR n_large) / (4 * (INR n_large - INR n_small)))
    (good_event_b I).
Proof.
  unfold good_event_b.
  set (len := length I). set (s := seq 0 len).
  apply iff_reflect; split.
  - intros H_prop.
    apply forallb_forall; intros i Hi_s.
    apply forallb_forall; intros j Hj_s.
    apply in_seq in Hi_s; destruct Hi_s as [_ Hi_len].
    apply in_seq in Hj_s; destruct Hj_s as [_ Hj_len].
    simpl.
    destruct ((i <? len) && (j <? len) && negb (i =? j)) eqn:Hcond.
    + apply andb_prop in Hcond; destruct Hcond as [Hcond12 Hneq].
      apply andb_prop in Hcond12; destruct Hcond12 as [Hi_lt Hj_lt].
      apply Nat.ltb_lt in Hi_lt; apply Nat.ltb_lt in Hj_lt.
      apply negb_true_iff, Nat.eqb_neq in Hneq.
      simpl.
      apply Rge_bool_ge.
      apply Rle_ge, H_prop; assumption.
    + reflexivity.
  - intros H_bool i j Hi Hj Hij.
    assert (Hi_s : In i s) by (subst s; apply in_seq; lia).
    assert (Hj_s : In j s) by (subst s; apply in_seq; lia).
    pose proof (proj1 (forallb_forall
      (fun i0 => forallb (fun j0 =>
        if (i0 <? len) && (j0 <? len) && negb (i0 =? j0) then
          Rge_bool
            (INR c * sqrt (INR (min (f (nth i0 I 0%nat)) (f (nth j0 I 0%nat))) *
                           INR (max (f (nth i0 I 0%nat)) (f (nth j0 I 0%nat)))) /
             (4 * (INR (max (f (nth i0 I 0%nat)) (f (nth j0 I 0%nat))) -
                   INR (min (f (nth i0 I 0%nat)) (f (nth j0 I 0%nat))))))
            (Cnorm (Csum (fun k => psi (min (f (nth i0 I 0%nat)) (f (nth j0 I 0%nat))) k *c
                                 Cconj (psi (max (f (nth i0 I 0%nat)) (f (nth j0 I 0%nat))) k))
                         (min (f (nth i0 I 0%nat)) (f (nth j0 I 0%nat)) - 1)%nat))
        else true) s) s) H_bool i Hi_s) as Hi_forall.
    pose proof (proj1 (forallb_forall (fun j0 =>
      if (i <? len) && (j0 <? len) && negb (i =? j0) then
        Rge_bool
          (INR c * sqrt (INR (min (f (nth i I 0%nat)) (f (nth j0 I 0%nat))) *
                         INR (max (f (nth i I 0%nat)) (f (nth j0 I 0%nat)))) /
           (4 * (INR (max (f (nth i I 0%nat)) (f (nth j0 I 0%nat))) -
                 INR (min (f (nth i I 0%nat)) (f (nth j0 I 0%nat))))))
          (Cnorm (Csum (fun k => psi (min (f (nth i I 0%nat)) (f (nth j0 I 0%nat))) k *c
                               Cconj (psi (max (f (nth i I 0%nat)) (f (nth j0 I 0%nat))) k))
                       (min (f (nth i I 0%nat)) (f (nth j0 I 0%nat)) - 1)%nat))
      else true) s) Hi_forall j Hj_s) as Hj_check.
    assert (Hi_lt_len : (i <? len) = true) by (apply Nat.ltb_lt; exact Hi).
    assert (Hj_lt_len : (j <? len) = true) by (apply Nat.ltb_lt; exact Hj).
    assert (Hneqb : negb (i =? j) = true) by (apply negb_true_iff, Nat.eqb_neq; exact Hij).
    rewrite Hi_lt_len, Hj_lt_len, Hneqb in Hj_check.
    simpl in Hj_check.
    apply Rge_bool_ge in Hj_check.
    apply Rge_le. exact Hj_check.
Qed.

(* 稀疏条件蕴含良好事件 *)
Lemma sparse_cond_impl_good_event I :
  In I (all_subsets N) -> sparse_cond_b c f I = true -> good_event_b I = true.
Proof.
  intros Hin Hsp.
  destruct (good_event_bP I) as [Hprop | Hnot].
  - reflexivity.
  - exfalso. apply Hnot.
    intros i j Hi Hj Hij.
    refine (deterministic_sparse_inner_bound c f Hc_ge2 Hf_ge2 Hf_growth I _ i j Hi Hj Hij).
    split.
    + apply all_subsets_NoDup; exact Hin.
    + apply (proj1 (sparse_cond_b_true_iff c f I) Hsp).
Qed.

End ProbabilisticGeneration.


(* 子集权重递推：新增首元 *)
Lemma weight_of_subset_Sn_cons_explicit (p : R) (n : nat) (I : list nat) :
  (length I <= n)%nat ->
  weight_of_subset p (S n) (n :: I) = p * weight_of_subset p n I.
Proof.
  intros Hlen.
  unfold weight_of_subset.
  rewrite length_cons.
  replace (S n - S (length I))%nat with (n - length I)%nat by lia.
  simpl.
  ring.
Qed.

(* 子集权重递推：旧列表不变 *)
Lemma weight_of_subset_Sn_old_explicit (p : R) (n : nat) (I : list nat) :
  (length I <= n)%nat ->
  weight_of_subset p (S n) I = (1 - p) * weight_of_subset p n I.
Proof.
  intros Hlen.
  unfold weight_of_subset.
  replace (S n - length I)%nat with (S (n - length I))%nat by lia.
  simpl; ring.
Qed.

(* 单点包含概率（通用） *)
Lemma prob_single_inclusion_general_P (p : R) (N i : nat) :
  0 <= p <= 1 -> (i < N)%nat ->
  sum_over_subsets_weight p N (fun I => inb i I) = p.
Proof.
  intros Hp Hi.
  eapply prob_single_inclusion; eauto; split; lra.
Qed.

(* 无序对包含概率（通用） *)
Lemma sum_over_subsets_weight_pair_inclusion (p : R) (N i j : nat) :
  0 <= p <= 1 -> i <> j -> (i < N)%nat -> (j < N)%nat ->
  sum_over_subsets_weight p N (fun I => (inb i I) && (inb j I)) = p * p.
Proof.
  intros Hp Hneq Hi Hj.
  eapply prob_pair_inclusion; eauto; split; lra.
Qed.

(* 全部子集权重求和归一（独立版本） *)
Lemma sum_weights_all_true_independent (p : R) (N : nat) :
  0 <= p <= 1 ->
  sum_over_subsets_weight p N (fun _ => true) = 1%R.
Proof.
  intros [Hp0 Hp1].
  induction N as [|m IH].
  - unfold sum_over_subsets_weight, all_subsets, all_subsets_upto, weight_of_subset; simpl; ring.
  - unfold sum_over_subsets_weight, all_subsets, all_subsets_upto; fold (all_subsets_upto m).
    set (prev := all_subsets_upto m).
    rewrite map_app, fold_right_Rplus_app.
    assert (Hlen_prev : forall I, In I prev -> (length I <= m)%nat).
    {
      clear -prev.
      induction m as [|k IHk]; intros I Hin; simpl in *.
      - destruct Hin; subst; simpl; lia.
      - apply in_app_iff in Hin as [Hin' | Hin].
        + apply in_map_iff in Hin' as [J [Heq HinJ]]; subst.
          simpl; apply le_n_S; apply IHk; exact HinJ.
        + apply le_S; apply IHk; exact Hin.
    }
    assert (Hcons : fold_right Rplus 0
      (map (fun I => if true then weight_of_subset p (S m) I else 0)
           (map (fun l => m :: l) prev))
      = p * sum_over_subsets_weight p m (fun _ => true)).
    {
      rewrite map_map; simpl.
      assert (Haux : forall I, In I prev ->
        weight_of_subset p (S m) (m :: I) = p * weight_of_subset p m I).
      { intros I Hin. apply weight_of_subset_Sn_cons_explicit; auto. }
      rewrite (map_ext_in _ (fun I => p * weight_of_subset p m I) prev Haux).
      rewrite fold_right_Rplus_factor.
      unfold sum_over_subsets_weight, all_subsets; fold prev; reflexivity.
    }
    assert (Hold : fold_right Rplus 0
      (map (fun I => if true then weight_of_subset p (S m) I else 0) prev)
      = (1-p) * sum_over_subsets_weight p m (fun _ => true)).
    {
      simpl.
      assert (Haux : forall I, In I prev ->
        weight_of_subset p (S m) I = (1-p) * weight_of_subset p m I).
      { intros I Hin. apply weight_of_subset_Sn_old_explicit; auto. }
      assert (H_eq : fold_right Rplus 0 (map (weight_of_subset p (S m)) prev) =
                     (1-p) * fold_right Rplus 0 (map (weight_of_subset p m) prev)).
      {
        clear -prev Haux.
        induction prev as [|I l IHl].
        - simpl; ring.
        - simpl. rewrite Haux; [| left; reflexivity].
          rewrite IHl; [| intros J Hj; apply Haux; right; exact Hj].
          ring.
      }
      change (fun I : list nat => weight_of_subset p (S m) I) with (weight_of_subset p (S m)).
      rewrite H_eq.
      unfold sum_over_subsets_weight, all_subsets; fold prev.
      reflexivity.
    }
    rewrite Hcons, Hold, IH.
    ring.
Qed.

(* 全部子集权重求和归一（通用版本） *)
Lemma sum_weights_all_true_general_P (p : R) (N : nat) :
  0 <= p <= 1 -> sum_over_subsets_weight p N (fun _ => true) = 1%R.
Proof.
  intros Hp. apply sum_weights_all_true_independent; assumption.
Qed.

(* 子集长度不超过上限 *)
Lemma all_subsets_upto_length_le' : forall n I,
  In I (all_subsets_upto n) -> (length I <= n)%nat.
Proof.
  induction n; intros I Hin; simpl in *.
  - destruct Hin; [subst I; simpl; lia | contradiction].
  - apply in_app_iff in Hin as [Hin' | Hin].
    + apply in_map_iff in Hin' as [J [Heq HinJ]]; subst.
      simpl; apply le_n_S; apply IHn; exact HinJ.
    + apply le_S; apply IHn; exact Hin.
Qed.

(* 列表元素和不超出长度乘最大值 *)
Lemma sum_list_le_times_max : forall (l : list R) (M : R),
  (forall x, In x l -> 0 <= x <= M) ->
  fold_right Rplus 0 l <= INR (length l) * M.
Proof.
  induction l as [|x xs IH]; intros M H.
  - rewrite Rmult_0_l; apply Rle_refl.
  - assert (Hx : 0 <= x <= M) by (apply H; left; reflexivity).
    assert (Hxs : forall y, In y xs -> 0 <= y <= M)
      by (intros y Hy; apply H; right; auto).
    specialize (IH M Hxs).
    rewrite length_cons, S_INR, Rmult_plus_distr_r, Rmult_1_l.
    simpl fold_right.
    destruct Hx as [_ HxM].
    lra.
Qed.

End ProbabilisticSparseBasis.

Export ProbabilisticSparseBasis.
