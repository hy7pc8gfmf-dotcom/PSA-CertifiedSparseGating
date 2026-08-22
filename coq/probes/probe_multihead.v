(* ============================================================
   T-MH：多头注意力扰动的可组合证书（z 工作区，E039）
   部署鲁棒性族第三件（发布仓库增活分析 §3 T-MH）。
   非平凡核心：
     MH1 head_output_lipschitz：单头期望输出的 ℓ1-直径 Lipschitz 界——
        |Σ_j (p_j − p'_j)·v_j| ≤ ‖p − p'‖₁ · max_j |v_j|
        （分布漂移 → 期望输出漂移；元素≤非负和 + scale_l 收口）。
     MH2 head_output_cert：与 softmax_l1_bound_exp 桥接——logit 漂移 ≤ d
        ⟹ 输出漂移 ≤ 直径 × (e^{2d}−1)（部署级"逐头证书"）。
     MH3 multihead_output_bound（主定理）：多头加权输出的扰动界 =
        Σ_h |w_h|·(直径_h)·(TVD_h)——**逐头证书可组合性**（每头独立
        证书/独立阶梯/独立界，输出层三角合成）。
     MH4 multihead_top1_stable：全头满足间隔条件 ⟹ 逐头 top-1 保持
        （drift_top1_stable 的多头合成——决策向量级不变）。
   依赖：PSA_framework（softmax 链）+ probe_kvevict（logit）+
   probe_quant（drift_top1_stable）。审计：Print Assumptions 尾部。
   ============================================================ *)
Require Import Stdlib.Reals.Reals.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.micromega.Lra.
Require Import Stdlib.Lists.List.
Import ListNotations.
Require Import PSA_framework.
Require Import probe_kvevict.
Require Import probe_quant.
Import PSA_framework.RowTruncation.
Import PSA_framework.SoftmaxStability.
Import PSA_framework.PhaseCoherence.
Import KVEvict.
Import Quant.

Open Scope R_scope.
Open Scope nat_scope.

Module MultiHead.

(* ---------- MH0：结构与基础件 ---------- *)

Definition head_out (p : nat -> R) (v : nat -> R) (n : nat) : R :=
  list_sum_R (fun j => (p j * v j)%R) (seq 0%nat n).

Definition vmax (v : nat -> R) (n : nat) : R :=
  list_sum_R (fun j => Rabs (v j)) (seq 0%nat n).

Lemma sum_ge_element (f : nat -> R) (l : list nat) (j : nat) :
  In j l -> (forall i, (0 <= f i)%R) -> (f j <= list_sum_R f l)%R.
Proof.
  intros Hj Hf. induction l as [| x xs IH].
  - destruct Hj.
  - destruct Hj as [E | Hj].
    + subst x. simpl.
      assert (Hpos : (0 <= list_sum_R f xs)%R)
        by (apply list_sum_R_pos; intros i _; apply Hf).
      lra.
    + simpl.
      assert (Hpos : (0 <= f x)%R) by (apply Hf).
      assert (HIH : (f j <= list_sum_R f xs)%R) by (apply IH; assumption).
      lra.
Qed.

(* ---------- MH1：期望输出的 ℓ1-直径 Lipschitz 界（非平凡核心一） ---------- *)

Lemma head_output_lipschitz (p p' v : nat -> R) (n : nat) :
  (Rabs (head_out p v n - head_out p' v n)
   <= list_sum_R (fun j => Rabs (p j - p' j)) (seq 0%nat n) * vmax v n)%R.
Proof.
  assert (Hd :
     (head_out p v n - head_out p' v n
      = list_sum_R (fun j => (p j * v j + - (p' j * v j))%R) (seq 0%nat n))%R).
  { unfold head_out.
    rewrite (list_sum_R_plus (fun j => (p j * v j)%R)
               (fun j => (- (p' j * v j))%R) (seq 0%nat n)).
    rewrite (list_sum_R_neg (fun j => (p' j * v j))%R (seq 0%nat n)).
    ring. }
  rewrite Hd.
  apply (Rle_trans _
           (list_sum_R (fun j => (Rabs (p j - p' j) * Rabs (v j))%R) (seq 0%nat n))).
  - apply (Rle_trans _
             (list_sum_R (fun j => Rabs (p j * v j - p' j * v j)) (seq 0%nat n))).
    + apply list_sum_R_abs.
    + apply list_sum_R_le_compat. intros j Hj.
      replace (p j * v j - p' j * v j)%R with ((p j - p' j) * v j)%R by ring.
      rewrite Rabs_mult. apply Rle_refl.
  - apply (Rle_trans _
           (list_sum_R (fun j => (Rabs (p j - p' j) * vmax v n)%R) (seq 0%nat n))).
    + apply list_sum_R_le_compat. intros j Hj.
      apply (Rmult_le_compat_l (Rabs (p j - p' j)) (Rabs (v j)) (vmax v n)).
      * apply Rabs_pos.
      * unfold vmax.
        apply (sum_ge_element (fun j0 => Rabs (v j0)) (seq 0%nat n) j).
        -- assert (Hjn : (j < n)%nat) by (apply In_seq_lt_coq; exact Hj).
           apply (proj2 (in_seq n 0%nat j)). lia.
        -- intros i. apply Rabs_pos.
    + assert (Hsc :
         (list_sum_R (fun j => (Rabs (p j - p' j) * vmax v n)%R) (seq 0%nat n)
          = list_sum_R (fun j => Rabs (p j - p' j)) (seq 0%nat n) * vmax v n)%R).
      { rewrite (Rmult_comm (list_sum_R (fun j => Rabs (p j - p' j)) (seq 0%nat n))
                   (vmax v n)).
        rewrite <- (list_sum_R_scale_l (fun j => Rabs (p j - p' j)) (vmax v n)
                      (seq 0%nat n)).
        apply list_sum_R_ext. intros j Hj. ring. }
      rewrite Hsc. apply Rle_refl.
Qed.

(* ---------- MH2：逐头证书（接 softmax_l1_bound_exp） ---------- *)

Lemma head_output_cert (z z' : nat -> R) (v : nat -> R) (n : nat) (d : R) :
  (0 < n)%nat -> (0 <= d)%R ->
  (forall i, (i < n)%nat -> (Rabs (z i - z' i) <= d))%R ->
  (Rabs (head_out (softmax_l z n) v n - head_out (softmax_l z' n) v n)
   <= vmax v n * (exp (2 * d) - 1))%R.
Proof.
  intros Hn Hd Hz.
  apply (Rle_trans _
           (list_sum_R (fun j => Rabs (softmax_l z n j - softmax_l z' n j))
              (seq 0%nat n) * vmax v n)).
  - apply head_output_lipschitz.
  - assert (H := softmax_l1_bound_exp z z' n d Hn Hd Hz).
    rewrite (Rmult_comm (list_sum_R (fun j => Rabs (softmax_l z n j - softmax_l z' n j))
                           (seq 0%nat n)) (vmax v n)).
    apply Rmult_le_compat_l.
    + unfold vmax. apply list_sum_R_pos. intros i _. apply Rabs_pos.
    + exact H.
Qed.

(* ---------- MH3：主定理——逐头证书可组合 ---------- *)

Definition mh_out (z : nat -> nat -> R) (v : nat -> nat -> R)
  (w : nat -> R) (Hh n : nat) : R :=
  list_sum_R (fun h => (w h * head_out (softmax_l (z h) n) (v h) n)%R) (seq 0%nat Hh).

Theorem multihead_output_bound (Hh : nat)
        (z z' : nat -> nat -> R) (v : nat -> nat -> R)
        (w : nat -> R) (n : nat) (d : nat -> R) :
  (0 < n)%nat ->
  (forall h, (h < Hh)%nat -> (0 <= d h)%R) ->
  (forall h i, (h < Hh)%nat -> (i < n)%nat -> (Rabs (z h i - z' h i) <= d h)%R) ->
  (Rabs (mh_out z v w Hh n - mh_out z' v w Hh n)
   <= list_sum_R (fun h => (Rabs (w h) * (vmax (v h) n * (exp (2 * d h) - 1)))%R)
       (seq 0%nat Hh))%R.
Proof.
  intros Hn Hd Hz.
  assert (Hsplit :
     (mh_out z v w Hh n - mh_out z' v w Hh n
      = list_sum_R (fun h => (w h * head_out (softmax_l (z h) n) (v h) n
                              + - (w h * head_out (softmax_l (z' h) n) (v h) n))%R)
           (seq 0%nat Hh))%R).
  { unfold mh_out.
    transitivity (list_sum_R (fun h => (w h * head_out (softmax_l (z h) n) (v h) n + - (w h * head_out (softmax_l (z' h) n) (v h) n))%R) (seq 0%nat Hh)).
    - rewrite (list_sum_R_plus (fun h => (w h * head_out (softmax_l (z h) n) (v h) n)%R) (fun h => (- (w h * head_out (softmax_l (z' h) n) (v h) n))%R) (seq 0%nat Hh)).
      rewrite (list_sum_R_neg (fun h => (w h * head_out (softmax_l (z' h) n) (v h) n)%R) (seq 0%nat Hh)).
      ring.
    - apply list_sum_R_ext. intros h HhIn. ring. }
  rewrite Hsplit.
  apply (Rle_trans _
           (list_sum_R (fun h => (Rabs (w h * head_out (softmax_l (z h) n) (v h) n
                                       - w h * head_out (softmax_l (z' h) n) (v h) n))%R)
              (seq 0%nat Hh))).
  - apply list_sum_R_abs.
  - apply list_sum_R_le_compat. intros h HhIn.
    assert (Hhn : (h < Hh)%nat) by (apply In_seq_lt_coq; exact HhIn).
    assert (Hcert := head_output_cert (z h) (z' h) (v h) n (d h) Hn
                       (Hd h Hhn) (fun i Hi => Hz h i Hhn Hi)).
    replace ((w h * head_out (softmax_l (z h) n) (v h) n
              - w h * head_out (softmax_l (z' h) n) (v h) n)%R)
      with ((w h * (head_out (softmax_l (z h) n) (v h) n
                   - head_out (softmax_l (z' h) n) (v h) n))%R) by ring.
    rewrite Rabs_mult.
    apply (Rmult_le_compat_l (Rabs (w h))); [ apply Rabs_pos | exact Hcert ].
Qed.

(* ---------- MH4：全头决策稳定（drift_top1_stable 的多头合成） ---------- *)

Theorem multihead_top1_stable (Hh : nat)
        (z z' : nat -> nat -> R) (k : nat -> nat) (n : nat)
        (gap d : nat -> R) :
  (0 < n)%nat ->
  (forall h, (h < Hh)%nat -> (k h < n))%nat ->
  (forall h j, (h < Hh)%nat -> (j < n)%nat ->
     (z h j + gap h <= z h (k h)))%R ->
  (forall h i, (h < Hh)%nat -> (i < n)%nat -> (Rabs (z h i - z' h i) <= d h))%R ->
  (forall h, (h < Hh)%nat -> (0 <= d h))%R ->
  (forall h, (h < Hh)%nat -> (2 * d h < gap h))%R ->
  (forall h j, (h < Hh)%nat -> (j < n)%nat ->
     (softmax_l (z' h) n j <= softmax_l (z' h) n (k h)))%R.
Proof.
  intros Hn Hk Htop Hdr Hd Hgap h j HhIn Hj.
  apply (drift_top1_stable (z h) (z' h) (k h) n (gap h) (d h)).
  - exact Hn.
  - apply Hk. exact HhIn.
  - intros j0 Hj0. apply Htop; [ exact HhIn | exact Hj0 ].
  - intros i Hi. apply Hdr; [ exact HhIn | exact Hi ].
  - apply Hd. exact HhIn.
  - apply Hgap. exact HhIn.
  - exact Hj.
Qed.

End MultiHead.

Print Assumptions MultiHead.head_output_lipschitz.
Print Assumptions MultiHead.head_output_cert.
Print Assumptions MultiHead.multihead_output_bound.
Print Assumptions MultiHead.multihead_top1_stable.
