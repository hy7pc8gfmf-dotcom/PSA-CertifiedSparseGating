(* ============================================================
   部署级实例化（发布仓库增活分析 §3 首推项）：
     逐出 = 核矩阵的列删除——evict_K K ev i j = 0（ev j）/ K i j。
     KV1 kv_drift_exact：|logit − logit'| ≤ Σ_{被逐 j} |c_j·K_ij|
        （精确分账：差恰为被逐列和，sum_filter_compl 分割 + 三角）。
     KV2 kv_eviction_drift：|K| ≤ 1 ⟹ 漂移 ≤ dropped_mass = Σ_{被逐} |c_j|。
     KV3 kv_eviction_controls_attention（主定理）：
        softmax ℓ1 TVD ≤ e^{2·dropped_mass} − 1——逐出代价 = 被逐质量的
        显式函数（T4 核漂移链的部署级实例，无新数学、结构非平凡）。
     KV4 kv_dropped_le_total：被逐质量 ≤ ‖c‖₁（先验界）。
     KV5 kv_evict_none_zero：零逐出 ⟹ 界 = 0 端点。
   依赖：PSA_framework 的 RowTruncation（list_sum_R/sum_filter_compl）+
   SoftmaxStability（softmax_l/softmax_l1_bound_exp）+ PhaseCoherence
   （list_sum_R_ext/abs）——全部已 Qed 基线。
   审计：Print Assumptions 尾部。
   ============================================================ *)
Require Import Stdlib.Reals.Reals.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.micromega.Lra.
Require Import Stdlib.Lists.List.
Import ListNotations.
Require Import PSA_framework.
Import PSA_framework.RowTruncation.
Import PSA_framework.SoftmaxStability.
Import PSA_framework.PhaseCoherence.

Open Scope R_scope.
Open Scope nat_scope.

Module KVEvict.

(* ---------- KV0：逐出结构与基础件 ---------- *)

Definition evict_K (K : nat -> nat -> R) (ev : nat -> bool) (i j : nat) : R :=
  if ev j then 0%R else K i j.

Definition logit (K : nat -> nat -> R) (c : nat -> R) (i n : nat) : R :=
  list_sum_R (fun j => (c j * K i j)%R) (seq 0%nat n).

Definition dropped_mass (c : nat -> R) (ev : nat -> bool) (n : nat) : R :=
  list_sum_R (fun j => Rabs (c j)) (filter ev (seq 0%nat n)).

Lemma filter_none_zero (l : list nat) :
  filter (fun _ => false) l = [].
Proof.
  induction l as [| x xs IH]; simpl; [ reflexivity | exact IH ].
Qed.

Lemma sum_evict_on_kept (K : nat -> nat -> R) (c : nat -> R) (ev : nat -> bool)
        (i : nat) (l : list nat) :
  (forall j, In j l -> ev j = false) ->
  (list_sum_R (fun j => (c j * evict_K K ev i j)%R) l
   = list_sum_R (fun j => (c j * K i j)%R) l)%R.
Proof.
  intros H. apply list_sum_R_ext. intros j Hj.
  destruct (ev j) eqn:E;
    [ exfalso; pose proof (H j Hj) as HF; rewrite E in HF; discriminate HF
    | unfold evict_K; rewrite E; reflexivity ].
Qed.

Lemma sum_evict_on_evicted (K : nat -> nat -> R) (c : nat -> R) (ev : nat -> bool)
        (i : nat) (l : list nat) :
  (forall j, In j l -> ev j = true) ->
  (list_sum_R (fun j => (c j * evict_K K ev i j)%R) l = 0)%R.
Proof.
  intros H. induction l as [| x xs IH]; [ reflexivity | ].
  assert (Hex : ev x = true) by (apply H; left; reflexivity).
  assert (Hz : ((c x * evict_K K ev i x)%R = 0)%R)
    by (unfold evict_K; rewrite Hex; apply Rmult_0_r).
  change (list_sum_R (fun j => (c j * evict_K K ev i j)%R) (x :: xs))%R
    with ((c x * evict_K K ev i x)%R
          + list_sum_R (fun j => (c j * evict_K K ev i j)%R) xs)%R.
  rewrite Hz.
  rewrite IH by (intros j Hj; apply H; right; exact Hj).
  ring.
Qed.

(* ---------- KV1：精确漂移 = 被逐列和的绝对值上界 ---------- *)

Lemma kv_drift_exact (K : nat -> nat -> R) (c : nat -> R) (ev : nat -> bool)
      (i n : nat) :
  (Rabs (logit K c i n - logit (evict_K K ev) c i n)
   <= list_sum_R (fun j => Rabs (c j * K i j)) (filter ev (seq 0%nat n)))%R.
Proof.
  pose proof (sum_filter_compl (fun j => (c j * K i j)%R) (seq 0%nat n) ev) as H1.
  pose proof (sum_filter_compl
                (fun j => (c j * evict_K K ev i j)%R) (seq 0%nat n) ev) as H2.
  assert (Hkept :
     (list_sum_R (fun j => (c j * evict_K K ev i j)%R)
                    (filter (fun j => negb (ev j)) (seq 0%nat n))
      = list_sum_R (fun j => (c j * K i j)%R) (filter (fun j => negb (ev j)) (seq 0%nat n)))%R).
  { apply (sum_evict_on_kept K c ev i). intros j Hj.
    apply filter_In in Hj. destruct Hj as [_ Hnj].
    destruct (ev j) eqn:E; [ discriminate Hnj | reflexivity ]. }
  assert (Hdrop0 :
     (list_sum_R (fun j => (c j * evict_K K ev i j)%R) (filter ev (seq 0%nat n))
      = 0)%R).
  { apply (sum_evict_on_evicted K c ev i). intros j Hj.
    apply filter_In in Hj. exact (proj2 Hj). }
  unfold logit in *.
  assert (Hdiff :
     (list_sum_R (fun j => (c j * K i j)%R) (seq 0%nat n)
      - list_sum_R (fun j => (c j * evict_K K ev i j)%R) (seq 0%nat n)
      = list_sum_R (fun j => (c j * K i j)%R) (filter ev (seq 0%nat n)))%R) by lra.
  rewrite Hdiff. apply list_sum_R_abs.
Qed.

(* ---------- KV2：|K| ≤ 1 ⟹ 漂移 ≤ 被逐质量 ---------- *)

Lemma kv_eviction_drift (K : nat -> nat -> R) (c : nat -> R) (ev : nat -> bool)
      (i n : nat) :
  (forall i0 j, (Rabs (K i0 j) <= 1)%R) ->
  (Rabs (logit K c i n - logit (evict_K K ev) c i n)
   <= dropped_mass c ev n)%R.
Proof.
  intros HK.
  apply (Rle_trans _
           (list_sum_R (fun j => Rabs (c j * K i j)) (filter ev (seq 0%nat n)))).
  - apply kv_drift_exact.
  - unfold dropped_mass. apply list_sum_R_le_compat. intros j Hj.
    rewrite Rabs_mult.
    apply (Rle_trans _ (Rabs (c j) * 1)).
    + apply (Rmult_le_compat_l (Rabs (c j)) (Rabs (K i j)) 1);
        [ apply Rabs_pos | exact (HK i j) ].
    + rewrite Rmult_1_r. apply Rle_refl.
Qed.

(* ---------- KV3：主定理——逐出 TVD ≤ e^{2·m} − 1 ---------- *)

Theorem kv_eviction_controls_attention (K : nat -> nat -> R) (c : nat -> R)
        (ev : nat -> bool) (n : nat) :
  (0 < n)%nat ->
  (forall i0 j, (Rabs (K i0 j) <= 1)%R) ->
  (list_sum_R (fun i => Rabs
     (softmax_l (fun i0 => logit K c i0 n) n i
      - softmax_l (fun i0 => logit (evict_K K ev) c i0 n) n i))
     (seq 0%nat n) <= exp (2 * dropped_mass c ev n) - 1)%R.
Proof.
  intros Hn HK.
  assert (Hm : (0 <= dropped_mass c ev n)%R).
  { unfold dropped_mass. apply list_sum_R_pos. intros i _. apply Rabs_pos. }
  apply (softmax_l1_bound_exp
           (fun i0 => logit K c i0 n)
           (fun i0 => logit (evict_K K ev) c i0 n)
           n (dropped_mass c ev n) Hn).
  - exact Hm.
  - intros k Hk. apply kv_eviction_drift. exact HK.
Qed.

(* ---------- KV4：被逐质量 ≤ 总质量（先验界） ---------- *)

Lemma kv_dropped_le_total (c : nat -> R) (ev : nat -> bool) (n : nat) :
  (dropped_mass c ev n
   <= list_sum_R (fun j => Rabs (c j)) (seq 0%nat n))%R.
Proof.
  pose proof (sum_filter_compl (fun j => Rabs (c j)) (seq 0%nat n) ev) as H.
  unfold dropped_mass.
  assert (Hkept :
     (0 <= list_sum_R (fun j => Rabs (c j))
             (filter (fun j => negb (ev j)) (seq 0%nat n)))%R).
  { apply list_sum_R_pos. intros i _. apply Rabs_pos. }
  lra.
Qed.

(* ---------- KV5：零逐出端点 ---------- *)

Lemma dropped_none (c : nat -> R) (n : nat) :
  (dropped_mass c (fun _ => false) n = 0)%R.
Proof.
  unfold dropped_mass. rewrite filter_none_zero. reflexivity.
Qed.

Corollary kv_evict_none_zero (K : nat -> nat -> R) (c : nat -> R) (n : nat) :
  (0 < n)%nat ->
  (list_sum_R (fun i => Rabs
     (softmax_l (fun i0 => logit K c i0 n) n i
      - softmax_l (fun i0 => logit (evict_K K (fun _ => false)) c i0 n) n i))
     (seq 0%nat n) <= exp (2 * 0) - 1)%R.
Proof.
  intros Hn.
  assert (Hz : (list_sum_R (fun _ => 0)%R (seq 0%nat n) = 0)%R).
  { induction (seq 0%nat n) as [| x xs IHx]; simpl;
      [ reflexivity | rewrite IHx; ring ]. }
  apply (Rle_trans _ (list_sum_R (fun _ => 0)%R (seq 0%nat n))).
  - apply list_sum_R_le_compat. intros i _.
    assert (Hzz :
      ((softmax_l (fun i0 => logit K c i0 n) n i
        - softmax_l (fun i0 => logit (evict_K K (fun _ => false)) c i0 n) n i)%R = 0)%R).
    { change (softmax_l (fun i0 => logit (evict_K K (fun _ => false)) c i0 n) n i)
        with (softmax_l (fun i0 => logit K c i0 n) n i). ring. }
    rewrite Hzz. rewrite Rabs_R0. apply Rle_refl.
  - rewrite Hz. replace (2 * 0)%R with 0%R by ring.
    rewrite exp_0. lra.
Qed.

End KVEvict.

Print Assumptions KVEvict.kv_drift_exact.
Print Assumptions KVEvict.kv_eviction_drift.
Print Assumptions KVEvict.kv_eviction_controls_attention.
Print Assumptions KVEvict.kv_dropped_le_total.
Print Assumptions KVEvict.kv_evict_none_zero.
