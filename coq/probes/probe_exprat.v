(* ============================================================
   部署鲁棒性族收官件（发布仓库增活分析 §3 T-EXP / 包 B）。
   非平凡核心：
     E1 exp_poly_upper（非平凡）：0 ≤ x ≤ 1 ⟹
        exp x ≤ 1 + x + x²/2 + x³/2
        ——经 ca_taylor.exp_taylor_3_direct（MVT 显式余项
          exp x = 1+x+x²/2+e^ξ·x³/6）+ e^ξ ≤ e ≤ 3（stdlib exp_le_3
          + 单调）组合，把超越常数 e 压成有理多项式。
     E2 tvd_rational_bound（主定理）：逐点 logit 漂移 ≤ d 且 2d ≤ 1 ⟹
        softmax ℓ1 TVD ≤ 2d + 2d² + 4d³ ——**全有理、检查器可判定**
        （softmax_l1_bound_exp 的 e^{2d}−1 端有理化）。
     E3/E4 部署实例化：KV 逐出（dropped_mass）与 per-key 量化的
        有理 TVD 证书（T-KV/T-QUANT 的可判版）。
   意义：检查器"全有理可判定"叙事补上最后一厘米——TVD 界不再含 e；
   ca_taylor 的沉没 Taylor 机器（exp_taylor_3_direct）首次承重。
   依赖：ca_taylor + PSA_framework + probe_kvevict + probe_quant。
   审计：Print Assumptions 尾部。
   ============================================================ *)
Require Import Stdlib.Reals.Reals.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.micromega.Lra.
Require Import Stdlib.Lists.List.
Import ListNotations.
Require Import ca_taylor.
Import TaylorTheorem.
Require Import PSA_framework.
Require Import probe_kvevict.
Require Import probe_quant.
Import PSA_framework.RowTruncation.
Import PSA_framework.SoftmaxStability.
Import PSA_framework.PhaseCoherence.
Import PSA_framework.ExpSeries.
Import KVEvict.
Import Quant.

Open Scope R_scope.
Open Scope nat_scope.

Module ExpRat.

(* ---------- E1：exp 的有理多项式上界（非平凡核心） ---------- *)

Lemma exp_poly_upper (x : R) : (0 <= x <= 1)%R -> (exp x <= 1 + x + x ^ 2 / 2 + x ^ 3 / 2)%R.
Proof.
  intros Hx.
  destruct (exp_taylor_3_direct x Hx) as [xi [Hxi Heq]].
  destruct Hxi as [Hxi1 Hxi2].
  assert (Hexi : (exp xi <= 3)%R).
  { apply (Rle_trans _ (exp 1));
      [ apply exp_mono_le_noclassic; lra | apply exp_le_3 ]. }
  assert (Hx3 : (0 <= x ^ 3)%R) by (apply pow_nonneg_mine; lra).
  rewrite Heq. nra.
Qed.

(* ---------- E2：主定理——TVD 的全有理界 ---------- *)

Theorem tvd_rational_bound (z z' : nat -> R) (n : nat) (d : R) :
  (0 < n)%nat -> (0 <= d)%R -> (2 * d <= 1)%R ->
  (forall i, (i < n)%nat -> (Rabs (z i - z' i) <= d))%R ->
  (list_sum_R (fun i => Rabs (softmax_l z n i - softmax_l z' n i)) (seq 0%nat n)
   <= 2 * d + (2 * d) ^ 2 / 2 + (2 * d) ^ 3 / 2)%R.
Proof.
  intros Hn Hd H2d Hz.
  assert (Hbound := softmax_l1_bound_exp z z' n d Hn Hd Hz).
  apply (Rle_trans _ (exp (2 * d) - 1)).
  - exact Hbound.
  - assert (H2d0 : (0 <= 2 * d)%R) by lra.
    assert (Hpoly := exp_poly_upper (2 * d) (conj H2d0 H2d)).
    lra.
Qed.

(* ---------- E3：KV 逐出的有理 TVD 证书 ---------- *)

Theorem kv_eviction_tvd_rational (K : nat -> nat -> R) (c : nat -> R)
        (ev : nat -> bool) (n : nat) :
  (0 < n)%nat ->
  (forall i0 j, (Rabs (K i0 j) <= 1))%R ->
  (2 * dropped_mass c ev n <= 1)%R ->
  (list_sum_R (fun i => Rabs
     (softmax_l (fun i0 => logit K c i0 n) n i
      - softmax_l (fun i0 => logit (evict_K K ev) c i0 n) n i))
     (seq 0%nat n)
   <= 2 * dropped_mass c ev n
      + (2 * dropped_mass c ev n) ^ 2 / 2
      + (2 * dropped_mass c ev n) ^ 3 / 2)%R.
Proof.
  intros Hn HK H2m.
  assert (Hm : (0 <= dropped_mass c ev n)%R).
  { unfold dropped_mass. apply list_sum_R_pos. intros i _. apply Rabs_pos. }
  apply (tvd_rational_bound
           (fun i0 => logit K c i0 n)
           (fun i0 => logit (evict_K K ev) c i0 n)
           n (dropped_mass c ev n) Hn Hm H2m).
  intros i Hi. apply kv_eviction_drift. exact HK.
Qed.

(* ---------- E4：per-key 量化的有理 TVD 证书 ---------- *)

Theorem quant_tvd_rational (K K' : nat -> nat -> R) (c e : nat -> R) (n : nat) :
  (0 < n)%nat ->
  (forall j, (0 <= e j))%R ->
  (forall i j, (i < n)%nat -> (j < n)%nat -> (Rabs (K i j - K' i j) <= e j))%R ->
  (2 * list_sum_R (fun j => (Rabs (c j) * e j)%R) (seq 0%nat n) <= 1)%R ->
  (list_sum_R (fun i => Rabs
     (softmax_l (fun i0 => logit K c i0 n) n i
      - softmax_l (fun i0 => logit K' c i0 n) n i))
     (seq 0%nat n)
   <= 2 * list_sum_R (fun j => (Rabs (c j) * e j)%R) (seq 0%nat n)
      + (2 * list_sum_R (fun j => (Rabs (c j) * e j)%R) (seq 0%nat n)) ^ 2 / 2
      + (2 * list_sum_R (fun j => (Rabs (c j) * e j)%R) (seq 0%nat n)) ^ 3 / 2)%R.
Proof.
  intros Hn He HK H2M.
  assert (HM : (0 <= list_sum_R (fun j => (Rabs (c j) * e j)%R) (seq 0%nat n))%R).
  { apply list_sum_R_pos. intros i _. apply Rmult_le_pos; [ apply Rabs_pos | apply He ]. }
  apply (tvd_rational_bound
           (fun i0 => logit K c i0 n)
           (fun i0 => logit K' c i0 n)
           n (list_sum_R (fun j => (Rabs (c j) * e j)%R) (seq 0%nat n)) Hn HM H2M).
  intros i Hi. apply quant_column_drift; [ exact Hi | exact HK ].
Qed.

End ExpRat.

Print Assumptions ExpRat.exp_poly_upper.
Print Assumptions ExpRat.tvd_rational_bound.
Print Assumptions ExpRat.kv_eviction_tvd_rational.
Print Assumptions ExpRat.quant_tvd_rational.
