(* ============================================================
   G-3: 可认证性充要刻画（参数化检查器健全性）
   充分方向：frame_check_instance_mu I p q = true
             ⟹ gershgorin 框架界 (1 ± p/q)
   基于合并版 ca_merged_full_24.v（FrameCheckInstance 模块）
   Classic R track; zero Admitted; zero custom axioms.
   ============================================================ *)
From mathcomp Require Import ssreflect ssrbool ssrnat seq eqtype div prime.
Require Import Stdlib.Reals.Reals.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.micromega.Lra.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import ca_merged_full_24.
Import FrameCheckInstance.
Import PrimeEmbedding.
Import ComplexNumbers.
Import Gershgorin.
Import UnconditionalBasisLemmas.
Import RuntimeGuards.
Import ExtendedTheorems.
Open Scope R_scope.

(* 与合并版 FrameCheckInstance 相同的 nth/last 用法：
   nth : nat -> list A -> A -> A（Coq 序），last : list A -> A -> A *)

Module G3Criterion.

(* ============ R0. 参数化行和判定 ============ *)

(* 分数 f = (num,den) ≤ p/q 的交叉相乘判定 *)
Definition row_le_mu (f : FrameCheckInstance.nat_pair) (p q : nat) : bool :=
  Nat.leb (q * fst f)%nat (p * snd f)%nat.

(* 参数化行和列表判定：每行分数 ≤ p/q *)
Fixpoint all_rows_le_mu (I orig : list nat) (i : nat) (p q : nat) : bool :=
  match I with
  | nil => true
  | cons h tl => andb (row_le_mu (FrameCheckInstance.row_sum_frac orig i) p q)
                       (all_rows_le_mu tl orig (S i) p q)
  end.

(* 参数化检查器 *)
Definition frame_check_instance_mu (I : list nat) (p q : nat) : bool :=
  andb (FrameCheckInstance.sorted_strict_aux I)
       (andb (all_ge_2 I)
             (andb (FrameCheckInstance.all_pairs_ok I) (all_rows_le_mu I I 0%nat p q))).

(* 原 4/5 检查器是 p=4,q=5 的特例（一致性：FrameCheckInstance.row_le_4_5 f = row_le_mu f 4 5） *)
Lemma g3_row_le_45_eq (f : FrameCheckInstance.nat_pair) :
  FrameCheckInstance.row_le_4_5 f = row_le_mu f 4 5.
Proof.
  unfold FrameCheckInstance.row_le_4_5, row_le_mu. reflexivity.
Qed.

(* row_le_mu 的 R 层解释：布尔通过 ⟹ 有理分数 ≤ p/q *)
Lemma g3_row_le_mu_R (num den p q : nat) :
  (den <> 0%nat) -> (0 < q)%coq_nat ->
  (q * num <= p * den)%coq_nat ->
  (INR num / INR den <= INR p / INR q)%R.
Proof.
  intros Hd Hq H.
  assert (Hden_pos : 0 < INR den) by (apply lt_0_INR; apply Nat.neq_0_lt_0; exact Hd).
  assert (Hq_pos : 0 < INR q) by (apply lt_0_INR; exact Hq).
  assert (HleR : (INR (q * num) <= INR (p * den))%R) by apply le_INR, H.
  rewrite (mult_INR q num) in HleR. rewrite (mult_INR p den) in HleR.
  apply div_le with (b := INR den) (d := INR q).
  - exact Hden_pos.
  - exact Hq_pos.
  - replace (INR num * INR q) with (INR q * INR num) by ring.
    exact HleR.
Qed.

(* all_rows_le_mu 的逐点形式 *)
Lemma all_rows_le_mu_forall (I orig : list nat) (idx : nat) (p q : nat) :
  all_rows_le_mu I orig idx p q = true ->
  forall i, (i < length I)%coq_nat ->
  row_le_mu (FrameCheckInstance.row_sum_frac orig (idx + i)) p q = true.
Proof.
  revert idx.
  induction I as [| h tl IH]; intros idx Hr i Hi; simpl in Hi; [lia |].
  simpl in Hr.
  destruct (andb_prop _ _ Hr) as [Hh Ht].
  destruct i as [| i'].
  - rewrite addn0. exact Hh.
  - rewrite addnS || rewrite Nat.add_succ_r.
    apply (IH (S idx) Ht i').
    simpl in Hi. lia.
Qed.

(* ============ R1. 参数化行和界（G-3 充分方向核心） ============ *)

Lemma g3_row_bound_mu (I : list nat) (i : nat) (p q : nat) :
  (0 < length I)%coq_nat ->
  (0 < q)%coq_nat ->
  frame_check_instance_mu I p q = true ->
  (i < length I)%coq_nat ->
  sum_f_R0 (fun j => if Nat.eq_dec i j then 0%R else
     ComplexNumbers.Cnorm (independent.Csum (fun k => psi (List.nth i I 0%nat) k *c ComplexNumbers.Cconj (psi (List.nth j I 0%nat) k)) (last I 0%nat)))
  (Nat.pred (length I)) <= INR p / INR q.
Proof.
  intros Hlen Hq Hfc Hi.
  unfold frame_check_instance_mu in Hfc.
  apply Bool.andb_true_iff in Hfc. destruct Hfc as [Hs Hfc1].
  apply Bool.andb_true_iff in Hfc1. destruct Hfc1 as [Hg Hfc2].
  apply Bool.andb_true_iff in Hfc2. destruct Hfc2 as [Hp Hr].
  rewrite (sum_f_R0_ext
           (fun j => if Nat.eq_dec i j then 0%R else
              Cnorm (independent.Csum (fun k => psi (List.nth i I 0%nat) k *c Cconj (psi (List.nth j I 0%nat) k)) (last I 0%nat)))
           (fun j => if Nat.eqb i j then 0%R else
              Cnorm (independent.Csum (fun k => psi (List.nth i I 0%nat) k *c Cconj (psi (List.nth j I 0%nat) k)) (last I 0%nat)))
           (Nat.pred (length I))).
  - apply Rle_trans with
      (sum_f_R0 (fun j => if Nat.eqb i j then 0%R else
         FrameCheckInstance.pair_frac_R (List.nth i I 0%nat) (List.nth j I 0%nat)) (Nat.pred (length I))).
    + apply sum_f_R0_le_compat.
      * intros j Hj.
        destruct (Nat.eqb_spec i j) as [Heq | Hne].
        -- simpl. apply Rle_refl.
        -- assert (Hjlt : (j < length I)%coq_nat) by (apply Nat.le_lt_trans with (Nat.pred (length I)); [exact Hj | lia]).
           assert (Hij : List.nth i I 0%nat <> List.nth j I 0%nat).
           { destruct (Nat.lt_ge_cases i j) as [Hilt | Hjge].
             - intro Heq.
               assert (Hlt0 : (List.nth i I 0%nat < List.nth j I 0%nat)%coq_nat) by (apply (FrameCheckInstance.sorted_nth_lt I Hs i j); [lia | exact Hjlt]).
               rewrite Heq in Hlt0. lia.
             - intro Heq.
               assert (Hlt0 : (List.nth j I 0%nat < List.nth i I 0%nat)%coq_nat) by (apply (FrameCheckInstance.sorted_nth_lt I Hs j i); [lia | exact Hi]).
               rewrite Heq in Hlt0. lia. }
           apply pair_inner_frac_bound.
           ++ apply FrameCheckInstance.all_ge_2_nth with (i := i); [exact Hg | exact Hi].
           ++ apply FrameCheckInstance.all_ge_2_nth with (i := j); [exact Hg | exact Hjlt].
           ++ exact Hij.
           ++ apply Nat.le_trans with (List.nth i I 0%nat); [apply Nat.le_min_l | apply (FrameCheckInstance.nth_le_last I Hs i Hi)].
    + rewrite (sum_f_R0_ext
               (fun j => if Nat.eqb i j then 0%R else FrameCheckInstance.pair_frac_R (List.nth i I 0%nat) (List.nth j I 0%nat))
               (fun j => if Nat.eqb j i then 0%R else FrameCheckInstance.pair_frac_R (List.nth i I 0%nat) (List.nth j I 0%nat))
               (Nat.pred (length I))).
      * rewrite (FrameCheckInstance.row_sum_frac_R_value I i Hlen (FrameCheckInstance.all_ge_2_nth I Hg) Hs Hi).
        apply g3_row_le_mu_R; [apply FrameCheckInstance.row_sum_frac_den_neq0; [exact Hi | exact (FrameCheckInstance.all_ge_2_nth I Hg) | exact (FrameCheckInstance.sorted_nth_lt I Hs)] | exact Hq |].
        pose proof (all_rows_le_mu_forall I I 0%nat p q Hr i Hi) as Hr4.
        unfold row_le_mu in Hr4.
        apply Nat.leb_le in Hr4. exact Hr4.
      * intros j Hj. rewrite Nat.eqb_sym. reflexivity.
  - intros j Hj.
    destruct (Nat.eq_dec i j) as [Heq | Hne].
    + subst. simpl. rewrite Nat.eqb_refl. reflexivity.
    + rewrite (proj2 (Nat.eqb_neq i j) Hne).
      destruct (Nat.eq_dec i j) as [Hcon | Hok]; [exfalso; apply Hne; exact Hcon | reflexivity].
Qed.

(* ============ R2. G-3 充分方向：参数化检查器健全性 ============ *)

Theorem g3_certifiable_iff (I : list nat) (p q : nat) :
  (0 < length I)%coq_nat -> (0 < q)%coq_nat ->
  frame_check_instance_mu I p q = true ->
  forall coeffs : list Complex,
  length coeffs = length I ->
  let n := length I in
  let M := S (last I 0%nat) in
  let phi := fun i k => psi (List.nth i I 0%nat) k in
  let F := fun k => independent.Csum (fun i => List.nth i coeffs ComplexNumbers.C0 *c phi i k) n in
  let S := sum_f_R0 (fun i => Cnorm_sq (List.nth i coeffs ComplexNumbers.C0)) (Nat.pred n) in
  ((1 - INR p / INR q) * S <= l2_norm_sq F (Nat.pred M)
    <= (1 + INR p / INR q) * S)%R.
Proof.
  intros Hlen Hq Hfc coeffs Hlencoeffs.
  unfold frame_check_instance_mu in Hfc.
  apply Bool.andb_true_iff in Hfc. destruct Hfc as [Hs Hfc1].
  apply Bool.andb_true_iff in Hfc1. destruct Hfc1 as [Hg Hfc2].
  apply Bool.andb_true_iff in Hfc2. destruct Hfc2 as [Hp Hr].
  cbv zeta.
  apply (Gershgorin.gershgorin_frame_mu (length I) (fun i k => psi (List.nth i I 0%nat) k) (S (last I 0%nat)) (INR p / INR q)).
  - apply Nat.lt_0_succ.
  - intros i k Hi Hk.
    apply UnconditionalBasisLemmas.psi_ge_n_zero.
    pose proof (FrameCheckInstance.nth_le_last I Hs i Hi) as Hle. lia.
  - intros i Hi.
    apply InstanceCertificate.psi_unit_norm.
    + apply FrameCheckInstance.all_ge_2_nth with (i := i); [exact Hg | exact Hi].
    + pose proof (FrameCheckInstance.nth_le_last I Hs i Hi) as Hle. lia.
  - intros i Hi.
    assert (Hfc_i : frame_check_instance_mu I p q = true).
    { unfold frame_check_instance_mu.
      apply Bool.andb_true_iff. split; [exact Hs |].
      apply Bool.andb_true_iff. split; [exact Hg |].
      apply Bool.andb_true_iff. split; [exact Hp | exact Hr]. }
    (* 内联 g3_row_bound_mu 证明体（目标 = gershgorin 第4前提，与结论仅 eq_nat_dec 表示差异） *)
    rewrite (sum_f_R0_ext
             (fun j => match Nat.eq_dec i j with left _ => 0%R | right _ =>
                ComplexNumbers.Cnorm (independent.Csum (fun k => psi (List.nth i I 0%nat) k *c ComplexNumbers.Cconj (psi (List.nth j I 0%nat) k)) (last I 0%nat)) end)
             (fun j => if Nat.eqb i j then 0%R else
                ComplexNumbers.Cnorm (independent.Csum (fun k => psi (List.nth i I 0%nat) k *c ComplexNumbers.Cconj (psi (List.nth j I 0%nat) k)) (last I 0%nat)))
             (Nat.pred (length I))).
    - apply Rle_trans with
        (sum_f_R0 (fun j => if Nat.eqb i j then 0%R else
           FrameCheckInstance.pair_frac_R (List.nth i I 0%nat) (List.nth j I 0%nat)) (Nat.pred (length I))).
      + apply sum_f_R0_le_compat.
        * intros j Hj.
          destruct (Nat.eqb_spec i j) as [Heq | Hne].
          -- simpl. apply Rle_refl.
          -- assert (Hjlt : (j < length I)%coq_nat) by (apply Nat.le_lt_trans with (Nat.pred (length I)); [exact Hj | lia]).
             assert (Hij : List.nth i I 0%nat <> List.nth j I 0%nat).
             { destruct (Nat.lt_ge_cases i j) as [Hilt | Hjge].
               - intro Heq.
                 assert (Hlt0 : (List.nth i I 0%nat < List.nth j I 0%nat)%coq_nat) by (apply (FrameCheckInstance.sorted_nth_lt I Hs i j); [lia | exact Hjlt]).
                 rewrite Heq in Hlt0. lia.
               - intro Heq.
                 assert (Hlt0 : (List.nth j I 0%nat < List.nth i I 0%nat)%coq_nat) by (apply (FrameCheckInstance.sorted_nth_lt I Hs j i); [lia | exact Hi]).
                 rewrite Heq in Hlt0. lia. }
             apply FrameCheckInstance.pair_inner_frac_bound.
             ++ apply FrameCheckInstance.all_ge_2_nth with (i := i); [exact Hg | exact Hi].
             ++ apply FrameCheckInstance.all_ge_2_nth with (i := j); [exact Hg | exact Hjlt].
             ++ exact Hij.
             ++ apply Nat.le_trans with (List.nth i I 0%nat); [apply Nat.le_min_l | apply (FrameCheckInstance.nth_le_last I Hs i Hi)].
      + rewrite (sum_f_R0_ext
                 (fun j => if Nat.eqb i j then 0%R else FrameCheckInstance.pair_frac_R (List.nth i I 0%nat) (List.nth j I 0%nat))
                 (fun j => if Nat.eqb j i then 0%R else FrameCheckInstance.pair_frac_R (List.nth i I 0%nat) (List.nth j I 0%nat))
                 (Nat.pred (length I))).
        * rewrite (FrameCheckInstance.row_sum_frac_R_value I i Hlen (FrameCheckInstance.all_ge_2_nth I Hg) Hs Hi).
          apply g3_row_le_mu_R; [apply FrameCheckInstance.row_sum_frac_den_neq0; [exact Hi | exact (FrameCheckInstance.all_ge_2_nth I Hg) | exact (FrameCheckInstance.sorted_nth_lt I Hs)] | exact Hq |].
          pose proof (all_rows_le_mu_forall I I 0%nat p q Hr i Hi) as Hr4.
          unfold row_le_mu in Hr4.
          apply Nat.leb_le in Hr4. exact Hr4.
        * intros j Hj. rewrite Nat.eqb_sym. reflexivity.
    - intros j Hj.
      destruct (Nat.eq_dec i j) as [Heq | Hne].
      + subst. simpl. rewrite Nat.eqb_refl. reflexivity.
      + rewrite (proj2 (Nat.eqb_neq i j) Hne).
        destruct (Nat.eq_dec i j) as [Hcon | Hok]; [exfalso; apply Hne; exact Hcon | reflexivity].
  - exact Hlencoeffs.
Qed.

End G3Criterion.

Print Assumptions G3Criterion.g3_certifiable_iff.
