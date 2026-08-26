(* ============================================================================
   ca_basis_4d_asm —— 四维张量积无条件基组装定理
   内容：tensor_product_unconditional_basis_4d（4D 张量积无条件基主定理）。
   依赖：ca_basis_4d（展平族 + 四重行和分解，全部 Qed）。
   纪律：零 Admitted、零活动 Axiom、零 classic。
   ============================================================================ *)
Require Import Stdlib.Reals.Reals.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Sorting.Sorted.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.micromega.Lra.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Arith.Peano_dec.
Require Import ca_base.
Require Import ca_basis.
Require Import ca_basis_lemmas.
Require Import ca_char_ortho.
Require Import ca_complex_analysis.
Require Import ca_complex_foundation.
Require Import ca_independence.
Require Import ca_sparse_ext.
Require Import ca_decay.
Require Import ca_basis_3d.
Require Import ca_basis_4d.
Import ComplexNumbers.
Import ExtendedTheorems.
Open Scope C_scope.
Open Scope R_scope.

Theorem tensor_product_unconditional_basis_4d :
  forall (C : nat) (HCgt2 : (C > 2)%nat)
    (seq1 seq2 seq3 seq4 : nat -> nat)
    (Hsparse1 : forall i : nat, (INR (seq1 (S i)) > INR C * INR (seq1 i))%R)
    (Hsparse2 : forall i : nat, (INR (seq2 (S i)) > INR C * INR (seq2 i))%R)
    (Hsparse3 : forall i : nat, (INR (seq3 (S i)) > INR C * INR (seq3 i))%R)
    (Hsparse4 : forall i : nat, (INR (seq4 (S i)) > INR C * INR (seq4 i))%R)
    (Hge2_1 : forall i : nat, (seq1 i >= 2)%nat)
    (Hge2_2 : forall i : nat, (seq2 i >= 2)%nat)
    (Hge2_3 : forall i : nat, (seq3 i >= 2)%nat)
    (Hge2_4 : forall i : nat, (seq4 i >= 2)%nat)
    (I1 I2 I3 I4 : list nat)
    (Hdup1 : NoDup I1) (Hsorted1 : Sorted Nat.lt I1)
    (Hdup2 : NoDup I2) (Hsorted2 : Sorted Nat.lt I2)
    (Hdup3 : NoDup I3) (Hsorted3 : Sorted Nat.lt I3)
    (Hdup4 : NoDup I4) (Hsorted4 : Sorted Nat.lt I4)
    (coeffs_flat : list Complex)
    (n1 n2 n3 n4 : nat) (Hn1 : n1 = length I1) (Hn2 : n2 = length I2) (Hn3 : n3 = length I3) (Hn4 : n4 = length I4)
    (Hn1_pos : (n1 > 0)%nat) (Hn2_pos : (n2 > 0)%nat) (Hn3_pos : (n3 > 0)%nat) (Hn4_pos : (n4 > 0)%nat)
    (Hlen_flat : length coeffs_flat = (n1 * n2 * n3 * n4)%nat)
    (HI1 : I1 = seq 0 n1)
    (HI2 : I2 = seq 0 n2)
    (HI3 : I3 = seq 0 n3)
    (HI4 : I4 = seq 0 n4)
    (H_dom : forall idx1 idx2 : nat,
        ((idx1 / (n2 * n3 * n4))%nat = (idx2 / (n2 * n3 * n4))%nat ->
         (seq1 ((idx1 / (n2 * n3 * n4))%nat) >=
          Nat.max (seq2 (((idx1 mod (n2 * n3 * n4))%nat) / (n3 * n4))%nat)
                  (seq2 (((idx2 mod (n2 * n3 * n4))%nat) / (n3 * n4))%nat))%nat) /\
        (((idx1 mod (n2 * n3 * n4))%nat / (n3 * n4))%nat = (((idx2 mod (n2 * n3 * n4))%nat) / (n3 * n4))%nat ->
         (seq2 (((idx1 mod (n2 * n3 * n4))%nat) / (n3 * n4))%nat >=
          Nat.max (seq1 ((idx1 / (n2 * n3 * n4))%nat)) (seq1 ((idx2 / (n2 * n3 * n4))%nat)))%nat) /\
        ((((idx1 mod (n2 * n3 * n4)) mod (n3 * n4)) / n4)%nat = (((idx2 mod (n2 * n3 * n4)) mod (n3 * n4)) / n4)%nat ->
         (seq3 (((idx1 mod (n2 * n3 * n4)) mod (n3 * n4)) / n4)%nat >=
          Nat.max (seq1 ((idx1 / (n2 * n3 * n4))%nat)) (seq1 ((idx2 / (n2 * n3 * n4))%nat)))%nat) /\
        ((idx1 mod n4)%nat = (idx2 mod n4)%nat ->
         (seq4 (idx1 mod n4)%nat >=
          Nat.max (seq1 ((idx1 / (n2 * n3 * n4))%nat)) (seq1 ((idx2 / (n2 * n3 * n4))%nat)))%nat))
    (H_index_bound : forall idx1 idx2 : nat,
        (idx1 < n1 * n2 * n3 * n4)%nat -> (idx2 < n1 * n2 * n3 * n4)%nat ->
        (Z.abs_nat (Z.of_nat (idx1 / (n2 * n3 * n4)) - Z.of_nat (idx2 / (n2 * n3 * n4))) +
         Z.abs_nat (Z.of_nat (idx1 mod (n2 * n3 * n4) / (n3 * n4)) - Z.of_nat (idx2 mod (n2 * n3 * n4) / (n3 * n4))) +
         Z.abs_nat (Z.of_nat ((idx1 mod (n2 * n3 * n4)) mod (n3 * n4) / n4) - Z.of_nat ((idx2 mod (n2 * n3 * n4)) mod (n3 * n4) / n4)) +
         Z.abs_nat (Z.of_nat (idx1 mod n4) - Z.of_nat (idx2 mod n4)) <= 6)%nat),
  let vals1 := map seq1 I1 in
  let vals2 := map seq2 I2 in
  let vals3 := map seq3 I3 in
  let vals4 := map seq4 I4 in
  let a i := nth i vals1 0%nat in
  let b j := nth j vals2 0%nat in
  let c k := nth k vals3 0%nat in
  let d l := nth l vals4 0%nat in
  let maxIdx1 := fold_right Nat.max 0%nat I1 in
  let maxIdx2 := fold_right Nat.max 0%nat I2 in
  let maxIdx3 := fold_right Nat.max 0%nat I3 in
  let maxIdx4 := fold_right Nat.max 0%nat I4 in
  let M := S (max (max (max (seq1 maxIdx1) (seq2 maxIdx2)) (seq3 maxIdx3)) (seq4 maxIdx4)) in
  let phi_flat idx k :=
    phi4D_norm (a (idx / (n2 * n3 * n4))%nat)
               (b (idx mod (n2 * n3 * n4) / (n3 * n4))%nat)
               (c ((idx mod (n2 * n3 * n4)) mod (n3 * n4) / n4)%nat)
               (d (idx mod n4)%nat) k in
  let F_4D k :=
    Csum (fun i => Csum (fun j => Csum (fun k2 => Csum (fun l =>
      nth (flatten_4d n2 n3 n4 i j k2 l) coeffs_flat C0 *c
      phi4D_norm (a i) (b j) (c k2) (d l) k) n4) n3) n2) n1 in
  let S := sum_f_R0 (fun i => sum_f_R0 (fun j => sum_f_R0 (fun k2 => sum_f_R0 (fun l =>
      Cnorm_sq (nth (flatten_4d n2 n3 n4 i j k2 l) coeffs_flat C0)) (n4 - 1)) (n3 - 1)) (n2 - 1)) (n1 - 1) in
  let K_C := K (INR C) in
  let K0 := (Rmax 8 ((INR C) ^ 3)) / 2 in
  let M_bound := K0 * ((1 + 4 * K_C) * (1 + 4 * K_C) * (1 + 4 * K_C) * (1 + 4 * K_C) - 1) in
  ((1 - M_bound) * S <= l2_norm_sq F_4D (M - 1) <= (1 + M_bound) * S)%R.
Proof.
  intros C HCgt2 seq1 seq2 seq3 seq4 Hsparse1 Hsparse2 Hsparse3 Hsparse4
         Hge2_1 Hge2_2 Hge2_3 Hge2_4 I1 I2 I3 I4 Hdup1 Hsorted1 Hdup2 Hsorted2 Hdup3 Hsorted3 Hdup4 Hsorted4
         coeffs_flat n1 n2 n3 n4 Hn1 Hn2 Hn3 Hn4 Hn1_pos Hn2_pos Hn3_pos Hn4_pos Hlen_flat
         HI1 HI2 HI3 HI4 H_dom H_index_bound.
  assert (Hc_ge2 : (C >= 2)%nat) by lia.
  assert (HCgt1_R : 1 < INR C) by (change 1 with (INR 1); apply lt_INR; lia).
  set (r := sqrt (INR C)).
  set (K0 := (Rmax 8 ((INR C) ^ 3)) / 2).
  assert (Hr_gt1 : r > 1).
  { unfold r; rewrite <- sqrt_1. apply sqrt_lt_1; [lra | apply pos_INR | exact HCgt1_R]. }
  assert (Hr_pos : r > 0) by (apply sqrt_lt_R0; apply lt_0_INR; lia).
  set (K_C := K (INR C)).
  assert (HK_pos : 0 < K_C) by (apply K_pos; exact HCgt2).
  set (M_bound := K0 * ((1 + 4 * K_C) * (1 + 4 * K_C) * (1 + 4 * K_C) * (1 + 4 * K_C) - 1)).
  assert (HK0_nonneg : 0 <= K0).
  { unfold K0, Rdiv.
    apply Rmult_le_pos.
    - apply Rle_trans with 8%R.
      + lra.
      + apply Rmax_l.
    - apply Rlt_le.
      apply Rinv_0_lt_compat.
      lra. }

  set (n := (n1 * n2 * n3 * n4)%nat).
  assert (Hn_pos : (n > 0)%nat) by (apply Nat.mul_pos_pos; [apply Nat.mul_pos_pos; [apply Nat.mul_pos_pos |] |]; assumption).
  assert (Hlen_flat' : length coeffs_flat = n).
  { subst n; exact Hlen_flat. }

  assert (Hseq1_inc : forall x y, (x <= y)%nat -> (seq1 x <= seq1 y)%nat).
  { intros x y Hle; destruct (Nat.eq_dec x y) as [Heq | Hne].
    - subst; apply Nat.le_refl.
    - apply Nat.lt_le_incl; eapply seq_strict_growth_lt; eauto; lia. }
  assert (Hseq2_inc : forall x y, (x <= y)%nat -> (seq2 x <= seq2 y)%nat).
  { intros x y Hle; destruct (Nat.eq_dec x y) as [Heq | Hne].
    - subst; apply Nat.le_refl.
    - apply Nat.lt_le_incl; eapply seq_strict_growth_lt; eauto; lia. }
  assert (Hseq3_inc : forall x y, (x <= y)%nat -> (seq3 x <= seq3 y)%nat).
  { intros x y Hle; destruct (Nat.eq_dec x y) as [Heq | Hne].
    - subst; apply Nat.le_refl.
    - apply Nat.lt_le_incl; eapply seq_strict_growth_lt; eauto; lia. }
  assert (Hseq4_inc : forall x y, (x <= y)%nat -> (seq4 x <= seq4 y)%nat).
  { intros x y Hle; destruct (Nat.eq_dec x y) as [Heq | Hne].
    - subst; apply Nat.le_refl.
    - apply Nat.lt_le_incl; eapply seq_strict_growth_lt; eauto; lia. }
  set (vals1 := map seq1 I1).
  set (vals2 := map seq2 I2).
  set (vals3 := map seq3 I3).
  set (vals4 := map seq4 I4).
  set (a := fun i : nat => nth i vals1 0%nat).
  set (b := fun j : nat => nth j vals2 0%nat).
  set (c := fun k : nat => nth k vals3 0%nat).
  set (d := fun l : nat => nth l vals4 0%nat).
  set (maxIdx1 := fold_right Nat.max 0%nat I1).
  set (maxIdx2 := fold_right Nat.max 0%nat I2).
  set (maxIdx3 := fold_right Nat.max 0%nat I3).
  set (maxIdx4 := fold_right Nat.max 0%nat I4).
  assert (Hmax1 : maxIdx1 = fold_right Nat.max 0%nat I1) by reflexivity.
  assert (Hmax2 : maxIdx2 = fold_right Nat.max 0%nat I2) by reflexivity.
  assert (Hmax3 : maxIdx3 = fold_right Nat.max 0%nat I3) by reflexivity.
  assert (Hmax4 : maxIdx4 = fold_right Nat.max 0%nat I4) by reflexivity.
  assert (HI1' : I1 = seq 0 n1) by exact HI1.
  assert (HI2' : I2 = seq 0 n2) by exact HI2.
  assert (HI3' : I3 = seq 0 n3) by exact HI3.
  assert (HI4' : I4 = seq 0 n4) by exact HI4.
  set (M := S (max (max (max (seq1 maxIdx1) (seq2 maxIdx2)) (seq3 maxIdx3)) (seq4 maxIdx4))).
  pose (phi_flat := fun idx k =>
    phi4D_norm (a (idx / (n2 * n3 * n4))%nat)
               (b (idx mod (n2 * n3 * n4) / (n3 * n4))%nat)
               (c ((idx mod (n2 * n3 * n4)) mod (n3 * n4) / n4)%nat)
               (d (idx mod n4)%nat) k).

  set (d1 := d_factor r).
  set (delta_quad := fun idx1 idx2 : nat =>
    let i1 := (idx1 / (n2 * n3 * n4))%nat in
    let j1 := (idx1 mod (n2 * n3 * n4) / (n3 * n4))%nat in
    let k1 := ((idx1 mod (n2 * n3 * n4)) mod (n3 * n4) / n4)%nat in
    let l1 := (idx1 mod n4)%nat in
    let i2 := (idx2 / (n2 * n3 * n4))%nat in
    let j2 := (idx2 mod (n2 * n3 * n4) / (n3 * n4))%nat in
    let k2 := ((idx2 mod (n2 * n3 * n4)) mod (n3 * n4) / n4)%nat in
    let l2 := (idx2 mod n4)%nat in
    K0 * (d1 i1 i2 * d1 j1 j2 * d1 k1 k2 * d1 l1 l2)).

  (* ---- 截断：k >= pred M 时 phi_flat idx k = C0 ---- *)
  assert (Htrunc : forall idx k, (idx < n)%nat -> (k >= Nat.pred M)%nat -> phi_flat idx k = C0).
  { intros idx k Hidx Hk; unfold phi_flat.
    set (i := (idx / (n2 * n3 * n4))%nat); set (rem := (idx mod (n2 * n3 * n4))%nat);
    set (j := (rem / (n3 * n4))%nat); set (rem' := (rem mod (n3 * n4))%nat);
    set (kk := (rem' / n4)%nat); set (ll := (idx mod n4)%nat).
    assert (Hi : (i < n1)%nat) by (apply Nat.Div0.div_lt_upper_bound; nia).
    assert (Hrem_lt : (rem < n2 * n3 * n4)%nat)
      by (apply Nat.mod_upper_bound; nia).
    assert (Hj : (j < n2)%nat).
    { apply (Nat.Div0.div_lt_upper_bound rem (n3 * n4) n2).
      apply Nat.lt_le_trans with (n2 * n3 * n4)%nat; [exact Hrem_lt | nia]. }
    assert (Hrem'_lt : (rem' < n3 * n4)%nat)
      by (apply Nat.mod_upper_bound; nia).
    assert (Hkk : (kk < n3)%nat).
    { apply (Nat.Div0.div_lt_upper_bound rem' n4 n3).
      apply Nat.lt_le_trans with (n3 * n4)%nat; [exact Hrem'_lt | nia]. }
    assert (Hll : (ll < n4)%nat) by (apply Nat.mod_upper_bound; lia).
    unfold phi4D_norm.
    assert (Ha_le_max : (a i <= max (max (max (seq1 maxIdx1) (seq2 maxIdx2)) (seq3 maxIdx3)) (seq4 maxIdx4))%nat).
    { unfold a, vals1.
      assert (Hi_len : (i < length I1)%nat) by (rewrite <- Hn1; exact Hi).
      rewrite (H_nth_map nat nat seq1 I1 0%nat 0%nat i Hi_len).
      apply Nat.le_trans with (seq1 maxIdx1).
      - apply Hseq1_inc; eapply fold_right_max_ge; apply nth_In; exact Hi_len.
      - apply Nat.le_trans with (max (seq1 maxIdx1) (seq2 maxIdx2)).
        + apply Nat.le_max_l.
        + apply Nat.le_trans with (max (max (seq1 maxIdx1) (seq2 maxIdx2)) (seq3 maxIdx3)).
          * apply Nat.le_max_l.
          * apply Nat.le_max_l. }
    assert (Hb_le_max : (b j <= max (max (max (seq1 maxIdx1) (seq2 maxIdx2)) (seq3 maxIdx3)) (seq4 maxIdx4))%nat).
    { unfold b, vals2.
      assert (Hj_len : (j < length I2)%nat) by (rewrite <- Hn2; exact Hj).
      rewrite (H_nth_map nat nat seq2 I2 0%nat 0%nat j Hj_len).
      apply Nat.le_trans with (seq2 maxIdx2).
      - apply Hseq2_inc; eapply fold_right_max_ge; apply nth_In; exact Hj_len.
      - apply Nat.le_trans with (max (seq1 maxIdx1) (seq2 maxIdx2)).
        + apply Nat.le_max_r.
        + apply Nat.le_trans with (max (max (seq1 maxIdx1) (seq2 maxIdx2)) (seq3 maxIdx3)).
          * apply Nat.le_max_l.
          * apply Nat.le_max_l. }
    assert (Hc_le_max : (c kk <= max (max (max (seq1 maxIdx1) (seq2 maxIdx2)) (seq3 maxIdx3)) (seq4 maxIdx4))%nat).
    { unfold c, vals3.
      assert (Hk_len : (kk < length I3)%nat) by (rewrite <- Hn3; exact Hkk).
      rewrite (H_nth_map nat nat seq3 I3 0%nat 0%nat kk Hk_len).
      apply Nat.le_trans with (seq3 maxIdx3).
      - apply Hseq3_inc; eapply fold_right_max_ge; apply nth_In; exact Hk_len.
      - apply Nat.le_trans with (max (max (seq1 maxIdx1) (seq2 maxIdx2)) (seq3 maxIdx3)).
        + apply Nat.le_max_r.
        + apply Nat.le_max_l. }
    assert (Hd_le_max : (d ll <= max (max (max (seq1 maxIdx1) (seq2 maxIdx2)) (seq3 maxIdx3)) (seq4 maxIdx4))%nat).
    { unfold d, vals4.
      assert (Hl_len : (ll < length I4)%nat) by (rewrite <- Hn4; exact Hll).
      rewrite (H_nth_map nat nat seq4 I4 0%nat 0%nat ll Hl_len).
      apply Nat.le_trans with (seq4 maxIdx4).
      - apply Hseq4_inc; eapply fold_right_max_ge; apply nth_In; exact Hl_len.
      - apply Nat.le_max_r. }
    assert (Hmax_le_k : (max (max (max (seq1 maxIdx1) (seq2 maxIdx2)) (seq3 maxIdx3)) (seq4 maxIdx4) <= k)%nat).
    { unfold M in Hk; lia. }
    assert (Ha_le_k : (a i <= k)%nat) by lia.
    assert (Hb_le_k : (b j <= k)%nat) by lia.
    assert (Hc_le_k : (c kk <= k)%nat) by lia.
    assert (Hd_le_k : (d ll <= k)%nat) by lia.
    rewrite (psi_ge_n_zero (d ll) k Hd_le_k).
    rewrite (psi_ge_n_zero (c kk) k Hc_le_k).
    rewrite (psi_ge_n_zero (b j) k Hb_le_k).
    rewrite (psi_ge_n_zero (a i) k Ha_le_k).
    repeat rewrite Cmul_0_l.
    apply Cmul_0_r. }

  (* ---- 自归一：l2_norm_sq (phi_flat idx) (pred M) = 1 ---- *)
  assert (Hnorm1 : forall idx, (idx < n)%nat -> l2_norm_sq (phi_flat idx) (Nat.pred M) = 1%R).
  { intros idx Hlt; unfold phi_flat.
    set (i := (idx / (n2 * n3 * n4))%nat); set (rem := (idx mod (n2 * n3 * n4))%nat);
    set (j := (rem / (n3 * n4))%nat); set (rem' := (rem mod (n3 * n4))%nat);
    set (kk := (rem' / n4)%nat); set (ll := (idx mod n4)%nat).
    assert (Hi : (i < n1)%nat) by (apply Nat.Div0.div_lt_upper_bound; nia).
    assert (Hrem_lt : (rem < n2 * n3 * n4)%nat)
      by (apply Nat.mod_upper_bound; nia).
    assert (Hj : (j < n2)%nat).
    { apply (Nat.Div0.div_lt_upper_bound rem (n3 * n4) n2).
      apply Nat.lt_le_trans with (n2 * n3 * n4)%nat; [exact Hrem_lt | nia]. }
    assert (Hrem'_lt : (rem' < n3 * n4)%nat)
      by (apply Nat.mod_upper_bound; nia).
    assert (Hkk : (kk < n3)%nat).
    { apply (Nat.Div0.div_lt_upper_bound rem' n4 n3).
      apply Nat.lt_le_trans with (n3 * n4)%nat; [exact Hrem'_lt | nia]. }
    assert (Hll : (ll < n4)%nat) by (apply Nat.mod_upper_bound; lia).
    unfold phi4D_norm.
    assert (Ha_ge2 : (a i >= 2)%nat).
    { unfold a, vals1. rewrite Hn1 in Hi.
      rewrite (H_nth_map nat nat seq1 I1 0%nat 0%nat i Hi). apply Hge2_1. }
    assert (Hb_ge2 : (b j >= 2)%nat).
    { unfold b, vals2. rewrite Hn2 in Hj.
      rewrite (H_nth_map nat nat seq2 I2 0%nat 0%nat j Hj). apply Hge2_2. }
    assert (Hc3_ge2 : (c kk >= 2)%nat).
    { unfold c, vals3. rewrite Hn3 in Hkk.
      rewrite (H_nth_map nat nat seq3 I3 0%nat 0%nat kk Hkk). apply Hge2_3. }
    assert (Hd_ge2 : (d ll >= 2)%nat).
    { unfold d, vals4. rewrite Hn4 in Hll.
      rewrite (H_nth_map nat nat seq4 I4 0%nat 0%nat ll Hll). apply Hge2_4. }
    set (g := gamma4 (a i) (b j) (c kk) (d ll)).
    assert (Hg_pos : 0 < g) by (apply gamma4_pos; assumption).
    assert (Ha_le_max : (a i <= max (max (max (seq1 maxIdx1) (seq2 maxIdx2)) (seq3 maxIdx3)) (seq4 maxIdx4))%nat).
    { unfold a, vals1. rewrite Hn1 in Hi.
      rewrite (H_nth_map nat nat seq1 I1 0%nat 0%nat i Hi).
      apply Nat.le_trans with (seq1 maxIdx1).
      - apply Hseq1_inc; eapply fold_right_max_ge; apply nth_In; exact Hi.
      - apply Nat.le_trans with (max (seq1 maxIdx1) (seq2 maxIdx2)).
        + apply Nat.le_max_l.
        + apply Nat.le_trans with (max (max (seq1 maxIdx1) (seq2 maxIdx2)) (seq3 maxIdx3)).
          * apply Nat.le_max_l.
          * apply Nat.le_max_l. }
    assert (Hb_le_max : (b j <= max (max (max (seq1 maxIdx1) (seq2 maxIdx2)) (seq3 maxIdx3)) (seq4 maxIdx4))%nat).
    { unfold b, vals2. rewrite Hn2 in Hj.
      rewrite (H_nth_map nat nat seq2 I2 0%nat 0%nat j Hj).
      apply Nat.le_trans with (seq2 maxIdx2).
      - apply Hseq2_inc; eapply fold_right_max_ge; apply nth_In; exact Hj.
      - apply Nat.le_trans with (max (seq1 maxIdx1) (seq2 maxIdx2)).
        + apply Nat.le_max_r.
        + apply Nat.le_trans with (max (max (seq1 maxIdx1) (seq2 maxIdx2)) (seq3 maxIdx3)).
          * apply Nat.le_max_l.
          * apply Nat.le_max_l. }
    assert (Hc_le_max : (c kk <= max (max (max (seq1 maxIdx1) (seq2 maxIdx2)) (seq3 maxIdx3)) (seq4 maxIdx4))%nat).
    { unfold c, vals3. rewrite Hn3 in Hkk.
      rewrite (H_nth_map nat nat seq3 I3 0%nat 0%nat kk Hkk).
      apply Nat.le_trans with (seq3 maxIdx3).
      - apply Hseq3_inc; eapply fold_right_max_ge; apply nth_In; exact Hkk.
      - apply Nat.le_trans with (max (max (seq1 maxIdx1) (seq2 maxIdx2)) (seq3 maxIdx3)).
        + apply Nat.le_max_r.
        + apply Nat.le_max_l. }
    assert (Hd_le_max : (d ll <= max (max (max (seq1 maxIdx1) (seq2 maxIdx2)) (seq3 maxIdx3)) (seq4 maxIdx4))%nat).
    { unfold d, vals4. rewrite Hn4 in Hll.
      rewrite (H_nth_map nat nat seq4 I4 0%nat 0%nat ll Hll).
      apply Nat.le_trans with (seq4 maxIdx4).
      - apply Hseq4_inc; eapply fold_right_max_ge; apply nth_In; exact Hll.
      - apply Nat.le_max_r. }
    assert (Ha_lt_M : (a i < M)%nat) by (unfold M; apply Nat.lt_succ_r; exact Ha_le_max).
    assert (Hb_lt_M : (b j < M)%nat) by (unfold M; apply Nat.lt_succ_r; exact Hb_le_max).
    assert (Hc_lt_M : (c kk < M)%nat) by (unfold M; apply Nat.lt_succ_r; exact Hc_le_max).
    assert (Hd_lt_M : (d ll < M)%nat) by (unfold M; apply Nat.lt_succ_r; exact Hd_le_max).
    assert (Hmin4_lt_M : (Nat.min (Nat.min (Nat.min (a i) (b j)) (c kk)) (d ll) < M)%nat).
    { apply Nat.le_lt_trans with (a i).
      - apply Nat.le_trans with (Nat.min (Nat.min (a i) (b j)) (c kk)).
        + apply Nat.le_min_l.
        + apply Nat.le_trans with (Nat.min (a i) (b j)).
          * apply Nat.le_min_l.
          * apply Nat.le_min_l.
      - exact Ha_lt_M. }
    set (min4 := Nat.min (Nat.min (Nat.min (a i) (b j)) (c kk)) (d ll)).
    set (F m := Cof_real (/ g) *c (psi (a i) m *c psi (b j) m *c psi (c kk) m *c psi (d ll) m)).
    assert (HnormF : l2_norm_sq F (Nat.pred M) = 1%R).
    { unfold l2_norm_sq, F.
      assert (Heq : forall m, Cnorm_sq (Cof_real (/ g) *c (psi (a i) m *c psi (b j) m *c psi (c kk) m *c psi (d ll) m))
                     = (/ g) ^ 2 * (Cnorm_sq (psi (a i) m) * Cnorm_sq (psi (b j) m) * Cnorm_sq (psi (c kk) m) * Cnorm_sq (psi (d ll) m))).
      { intro m.
        rewrite Cnorm_sq_mult,
                (Cnorm_sq_mult ((psi (a i) m *c psi (b j) m) *c psi (c kk) m) (psi (d ll) m)),
                (Cnorm_sq_mult (psi (a i) m *c psi (b j) m) (psi (c kk) m)),
                (Cnorm_sq_mult (psi (a i) m) (psi (b j) m)).
        assert (Hcof_sq : Cnorm_sq (Cof_real ((/ g)%R)) = ((/ g) ^ 2)%R).
        { unfold Cof_real, Cnorm_sq, Rsqr; simpl; ring. }
        rewrite Hcof_sq; reflexivity. }
      rewrite (sum_f_R0_ext _ (fun m => (/ g) ^ 2 *
                 (Cnorm_sq (psi (a i) m) * Cnorm_sq (psi (b j) m) * Cnorm_sq (psi (c kk) m) * Cnorm_sq (psi (d ll) m)))).
      - rewrite (sum_f_R0_scal_l ((/ g) ^ 2)
                   (fun m => Cnorm_sq (psi (a i) m) * Cnorm_sq (psi (b j) m) * Cnorm_sq (psi (c kk) m) * Cnorm_sq (psi (d ll) m))
                   (Nat.pred M)).
        set (f4 := fun m => Cnorm_sq (psi (a i) m) * Cnorm_sq (psi (b j) m) * Cnorm_sq (psi (c kk) m) * Cnorm_sq (psi (d ll) m)).
        (* 截断到 min4：m >= min4 时至少一个 psi 为 0 *)
        assert (Hzero_above : forall m, (min4 <= m)%nat -> f4 m = 0%R).
        { intros m Hm.
          unfold min4 in Hm.
          destruct (Nat.min_spec (a i) (b j)) as [[Hlt_ab Hmin_ab] | [Hle_ba Hmin_ba]];
            destruct (Nat.min_spec (Nat.min (a i) (b j)) (c kk)) as [[Hlt_abc Hmin_abc] | [Hle_c Hmin_c]];
            destruct (Nat.min_spec (Nat.min (Nat.min (a i) (b j)) (c kk)) (d ll)) as [[Hlt_abcd Hmin_abcd] | [Hle_d Hmin_d]];
            try rewrite Hmin_abcd in Hm;
            try rewrite Hmin_abc in Hm;
            try rewrite Hmin_ab in Hm;
            try rewrite Hmin_ba in Hm;
            try rewrite Hmin_c in Hm;
            try rewrite Hmin_d in Hm;
            unfold f4.
          - assert (H : (a i <= m)%nat) by lia.
            rewrite (psi_ge_n_zero (a i) m H), Cnorm_sq_zero; simpl; ring.
          - assert (H : (d ll <= m)%nat) by lia.
            rewrite (psi_ge_n_zero (d ll) m H), Cnorm_sq_zero; simpl; ring.
          - assert (H : (c kk <= m)%nat) by lia.
            rewrite (psi_ge_n_zero (c kk) m H), Cnorm_sq_zero; simpl; ring.
          - assert (H : (d ll <= m)%nat) by lia.
            rewrite (psi_ge_n_zero (d ll) m H), Cnorm_sq_zero; simpl; ring.
          - assert (H : (b j <= m)%nat) by lia.
            rewrite (psi_ge_n_zero (b j) m H), Cnorm_sq_zero; simpl; ring.
          - assert (H : (d ll <= m)%nat) by lia.
            rewrite (psi_ge_n_zero (d ll) m H), Cnorm_sq_zero; simpl; ring.
          - assert (H : (c kk <= m)%nat) by lia.
            rewrite (psi_ge_n_zero (c kk) m H), Cnorm_sq_zero; simpl; ring.
          - assert (H : (d ll <= m)%nat) by lia.
            rewrite (psi_ge_n_zero (d ll) m H), Cnorm_sq_zero; simpl; ring. }
        assert (Hmin4_pos : (0 < min4)%nat).
        { unfold min4; apply Nat.min_glb_lt; [| lia]. apply Nat.min_glb_lt; [| lia]. apply Nat.min_glb_lt; lia. }
        assert (Hsum_trunc : sum_f_R0 f4 (Nat.pred M) = sum_f_R0 f4 (Nat.pred min4)).
        { assert (Ht : sum_f_R0 f4 (Nat.pred M) = sum_f_R0 f4 min4).
          { apply sum_f_R0_trunc_tail with (M := min4) (N := Nat.pred M); [lia |].
            intros m [Hm1 Hm2]; apply Hzero_above; lia. }
          rewrite Ht.
          assert (Hf4_min4 : f4 min4 = 0%R) by (apply Hzero_above; lia).
          assert (Hsucc : min4 = S (Nat.pred min4)) by (symmetry; apply Nat.succ_pred; apply Nat.neq_0_lt_0; exact Hmin4_pos).
          rewrite Hsucc, (sum_f_R0_S f4 (Nat.pred min4)).
          rewrite <- Hsucc, Hf4_min4; ring. }
        rewrite Hsum_trunc.
        set (cst4 := (1 / INR (a i)) * (1 / INR (b j)) * (1 / INR (c kk)) * (1 / INR (d ll))).
        assert (Hterm_eq : forall m, (m < min4)%nat -> f4 m = cst4).
        { intros m Hm_min.
          assert (Hm_ai : (m < a i)%nat) by (unfold min4 in Hm_min; nia).
          assert (Hm_bj : (m < b j)%nat) by (unfold min4 in Hm_min; nia).
          assert (Hm_ck : (m < c kk)%nat) by (unfold min4 in Hm_min; nia).
          assert (Hm_dl : (m < d ll)%nat) by (unfold min4 in Hm_min; nia).
          unfold f4.
          rewrite (Cnorm_sq_psi_exact (a i) m), (Cnorm_sq_psi_exact (b j) m), (Cnorm_sq_psi_exact (c kk) m), (Cnorm_sq_psi_exact (d ll) m).
          assert (Hltb_ai : (m <? a i)%nat = true) by (apply Nat.ltb_lt; exact Hm_ai).
          assert (Hltb_bj : (m <? b j)%nat = true) by (apply Nat.ltb_lt; exact Hm_bj).
          assert (Hltb_ck : (m <? c kk)%nat = true) by (apply Nat.ltb_lt; exact Hm_ck).
          assert (Hltb_dl : (m <? d ll)%nat = true) by (apply Nat.ltb_lt; exact Hm_dl).
          rewrite Hltb_ai, Hltb_bj, Hltb_ck, Hltb_dl.
          unfold cst4, Rdiv; field.
          split; [| split; [| split]]; apply Rgt_not_eq; apply lt_0_INR; lia. }
        assert (Hsum_cst : sum_f_R0 f4 (Nat.pred min4) = sum_f_R0 (fun _ => cst4) (Nat.pred min4)).
        { apply sum_f_R0_ext; intros m Hm; apply Hterm_eq; lia. }
        rewrite Hsum_cst.
        rewrite (sum_f_R0_const cst4 (Nat.pred min4)).
          unfold cst4, min4, g.
          field_simplify.
          set (m4 := Nat.min (Nat.min (Nat.min (a i) (b j)) (c kk)) (d ll)).
          assert (Hm4_pos : (0 < m4)%nat) by (unfold m4; apply Nat.min_glb_lt; [| lia]; apply Nat.min_glb_lt; [| lia]; apply Nat.min_glb_lt; lia).
          rewrite (Nat.succ_pred m4 (proj2 (Nat.neq_0_lt_0 m4) Hm4_pos)).
          subst m4.
          assert (Hpow2 : (gamma4 (a i) (b j) (c kk) (d ll) ^ 2)%R = gamma4 (a i) (b j) (c kk) (d ll) * gamma4 (a i) (b j) (c kk) (d ll)).
          { unfold pow; simpl; ring. }
          rewrite Hpow2.
          rewrite (gamma4_sq (a i) (b j) (c kk) (d ll) Ha_ge2 Hb_ge2 Hc3_ge2 Hd_ge2).
          field.
          all: try (repeat split).
          all: try (apply Rgt_not_eq; apply lt_0_INR; lia).
          all: try (apply Rgt_not_eq; apply gamma4_pos; [exact Ha_ge2 | exact Hb_ge2 | exact Hc3_ge2 | exact Hd_ge2]).
          all: try (intros i0 Hle; apply Heq). }
    exact HnormF. }

  (* ---- delta 对称 / 非负 ---- *)
  assert (d_factor_sym : forall i j, d_factor r i j = d_factor r j i).
  { intros i j; unfold d_factor.
    destruct (Nat.eq_dec i j) as [Heq | Hneq].
    - subst i; reflexivity.
    - assert (Hij : (i =? j)%nat = false) by (apply Nat.eqb_neq; exact Hneq).
      assert (Hji : (j =? i)%nat = false) by (apply Nat.eqb_neq; auto).
      rewrite Hij, Hji.
      f_equal; f_equal.
      replace (Z.of_nat j - Z.of_nat i)%Z with (- (Z.of_nat i - Z.of_nat j))%Z by lia.
      rewrite Z_abs_nat_opp; reflexivity. }
  assert (d_factor_nonneg : forall i j, 0 <= d_factor r i j).
  { intros i j; unfold d_factor.
    destruct (Nat.eqb_spec i j) as [Heq | Hneq].
    - subst i; lra.
    - apply Rlt_le; apply Rdiv_lt_0_compat; [lra | apply pow_lt; exact Hr_pos]. }

  assert (Hdelta_sym : forall (i j : nat), (i < n)%nat -> (j < n)%nat -> delta_quad i j = delta_quad j i).
  { intros idx1 idx2 Hi Hj; unfold delta_quad.
    repeat (f_equal; try (apply d_factor_sym); try reflexivity). }
  assert (Hdelta_nonneg : forall (i j : nat), (i < n)%nat -> (j < n)%nat -> 0 <= delta_quad i j).
  { intros idx1 idx2 Hi Hj; unfold delta_quad, d1.
    apply Rmult_le_pos.
    - exact HK0_nonneg.
    - repeat (apply Rmult_le_pos; try apply d_factor_nonneg). }

  (* ---- 衰减：由 phi_flat_decay_general_4d 供给 ---- *)
  assert (Hdecay : forall idx1 idx2, idx1 <> idx2 -> (idx1 < n)%nat -> (idx2 < n)%nat ->
              Cnorm (Csum (fun k => phi_flat idx1 k *c Cconj (phi_flat idx2 k)) (Nat.pred M))
              <= delta_quad idx1 idx2).
  { intros idx1 idx2 Hneq Hlt1 Hlt2.
    unfold delta_quad, phi_flat.
    apply (phi_flat_decay_general_4d C HCgt2 seq1 seq2 seq3 seq4 Hsparse1 Hsparse2 Hsparse3 Hsparse4
             Hge2_1 Hge2_2 Hge2_3 Hge2_4 I1 I2 I3 I4 n1 n2 n3 n4 Hn1 Hn2 Hn3 Hn4
             idx1 idx2 Hneq Hlt1 Hlt2
             (H_index_bound idx1 idx2 Hlt1 Hlt2)). }

  (* ---- 行和：sum_f_R0_flatten_4d + quad_prod_row_sum_decomp + d_factor_row_sum_le_4K ---- *)
  assert (Hrow_sum : forall idx, (idx < n)%nat ->
              sum_f_R0 (fun jdx => if Nat.eq_dec idx jdx then 0%R else delta_quad idx jdx) (Nat.pred n)
              <= M_bound).
  { intros idx Hidx.
    set (i0 := (idx / (n2 * n3 * n4))%nat); set (rem0 := (idx mod (n2 * n3 * n4))%nat);
    set (j0 := (rem0 / (n3 * n4))%nat); set (rem0' := (rem0 mod (n3 * n4))%nat);
    set (k0 := (rem0' / n4)%nat); set (l0 := (idx mod n4)%nat).
    assert (Hi0 : (i0 < n1)%nat) by (apply Nat.Div0.div_lt_upper_bound; nia).
    assert (Hrem0_lt : (rem0 < n2 * n3 * n4)%nat)
      by (apply Nat.mod_upper_bound; nia).
    assert (Hj0 : (j0 < n2)%nat).
    { apply (Nat.Div0.div_lt_upper_bound rem0 (n3 * n4) n2).
      apply Nat.lt_le_trans with (n2 * n3 * n4)%nat; [exact Hrem0_lt | nia]. }
    assert (Hrem0'_lt : (rem0' < n3 * n4)%nat)
      by (apply Nat.mod_upper_bound; nia).
    assert (Hk0 : (k0 < n3)%nat).
    { apply (Nat.Div0.div_lt_upper_bound rem0' n4 n3).
      apply Nat.lt_le_trans with (n3 * n4)%nat; [exact Hrem0'_lt | nia]. }
    assert (Hl0 : (l0 < n4)%nat) by (apply Nat.mod_upper_bound; lia).
    assert (Hd1_diag : forall i, d1 i i = 1%R).
    { intros i; unfold d1, d_factor, r; rewrite Nat.eqb_refl; reflexivity. }
    assert (Hflat : sum_f_R0 (fun jdx => if Nat.eq_dec idx jdx then 0%R else delta_quad idx jdx) (Nat.pred n)
        = K0 * sum_f_R0 (fun i => sum_f_R0 (fun j => sum_f_R0 (fun k => sum_f_R0 (fun l =>
              if andb (andb (andb (i =? i0)%nat (j =? j0)%nat)%nat (k =? k0)%nat)%nat (l =? l0)%nat
              then 0%R
              else d1 i0 i * d1 j0 j * d1 k0 k * d1 l0 l) (n4 - 1)) (n3 - 1)) (n2 - 1)) (n1 - 1)).
    { rewrite (sum_f_R0_ext (fun jdx => if Nat.eq_dec idx jdx then 0%R else delta_quad idx jdx)
                            (fun jdx => K0 * (if Nat.eq_dec idx jdx then 0%R
                                              else d1 i0 (jdx / (n2 * n3 * n4))%nat
                                                   * d1 j0 ((jdx mod (n2 * n3 * n4)) / (n3 * n4))%nat
                                                   * d1 k0 (((jdx mod (n2 * n3 * n4)) mod (n3 * n4)) / n4)%nat
                                                   * d1 l0 (jdx mod n4)%nat))
                            (Nat.pred n))
        by (intros jdx Hjdx; destruct (Nat.eq_dec idx jdx) as [Heq | Hne];
            [ subst jdx; simpl; rewrite Rmult_0_r; reflexivity
            | simpl; unfold delta_quad, d1; cbv zeta; reflexivity ]).
      rewrite (sum_f_R0_scal_l K0
            (fun jdx => if Nat.eq_dec idx jdx then 0%R
                        else d1 i0 (jdx / (n2 * n3 * n4))%nat
                             * d1 j0 ((jdx mod (n2 * n3 * n4)) / (n3 * n4))%nat
                             * d1 k0 (((jdx mod (n2 * n3 * n4)) mod (n3 * n4)) / n4)%nat
                             * d1 l0 (jdx mod n4)%nat)
            (Nat.pred n)).
      rewrite (sum_f_R0_ext (fun jdx => if Nat.eq_dec idx jdx then 0%R
                                        else d1 i0 (jdx / (n2 * n3 * n4))%nat
                                             * d1 j0 ((jdx mod (n2 * n3 * n4)) / (n3 * n4))%nat
                                             * d1 k0 (((jdx mod (n2 * n3 * n4)) mod (n3 * n4)) / n4)%nat
                                             * d1 l0 (jdx mod n4)%nat)
                            (fun jdx => if andb (andb (andb (jdx / (n2 * n3 * n4) =? i0)%nat
                                                            ((jdx mod (n2 * n3 * n4)) / (n3 * n4) =? j0)%nat)%nat
                                                   (((jdx mod (n2 * n3 * n4)) mod (n3 * n4)) / n4 =? k0)%nat)%nat
                                          (((jdx mod (n2 * n3 * n4)) mod (n3 * n4)) mod n4 =? l0)%nat
                                        then 0%R
                                        else d1 i0 (jdx / (n2 * n3 * n4))%nat
                                             * d1 j0 ((jdx mod (n2 * n3 * n4)) / (n3 * n4))%nat
                                             * d1 k0 (((jdx mod (n2 * n3 * n4)) mod (n3 * n4)) / n4)%nat
                                             * d1 l0 (((jdx mod (n2 * n3 * n4)) mod (n3 * n4)) mod n4)%nat)
                            (Nat.pred n))
        by (intros jdx Hjdx; destruct (Nat.eq_dec idx jdx) as [Heq | Hne];
            [ subst jdx; unfold i0, j0, k0, l0, rem0, rem0';
              rewrite (nat_mod_n4_of_mod_n234 idx n2 n3 n4 Hn2_pos Hn3_pos Hn4_pos);
              rewrite !Nat.eqb_refl; simpl; reflexivity
            | assert (Hcf : andb (andb (andb (jdx / (n2 * n3 * n4) =? i0)%nat
                                             ((jdx mod (n2 * n3 * n4)) / (n3 * n4) =? j0)%nat)%nat
                                    (((jdx mod (n2 * n3 * n4)) mod (n3 * n4)) / n4 =? k0)%nat)%nat
                                   (((jdx mod (n2 * n3 * n4)) mod (n3 * n4)) mod n4 =? l0)%nat = false);
              [ destruct (Nat.eq_dec (jdx / (n2 * n3 * n4))%nat i0) as [Ha | Hna];
                [ rewrite Ha, Nat.eqb_refl
                | rewrite (proj2 (Nat.eqb_neq (jdx / (n2 * n3 * n4))%nat i0) Hna); simpl; reflexivity ];
                destruct (Nat.eq_dec ((jdx mod (n2 * n3 * n4)) / (n3 * n4))%nat j0) as [Hb | Hnb];
                [ rewrite Hb, Nat.eqb_refl
                | rewrite (proj2 (Nat.eqb_neq ((jdx mod (n2 * n3 * n4)) / (n3 * n4))%nat j0) Hnb); simpl; reflexivity ];
                destruct (Nat.eq_dec (((jdx mod (n2 * n3 * n4)) mod (n3 * n4)) / n4)%nat k0) as [Hc | Hnc];
                [ rewrite Hc, Nat.eqb_refl
                | rewrite (proj2 (Nat.eqb_neq (((jdx mod (n2 * n3 * n4)) mod (n3 * n4)) / n4)%nat k0) Hnc); simpl; reflexivity ];
                destruct (Nat.eq_dec (((jdx mod (n2 * n3 * n4)) mod (n3 * n4)) mod n4)%nat l0) as [Hd | Hnd];
                [ rewrite Hd, Nat.eqb_refl
                | rewrite (proj2 (Nat.eqb_neq (((jdx mod (n2 * n3 * n4)) mod (n3 * n4)) mod n4)%nat l0) Hnd); simpl; reflexivity ];
                assert (Heq_quad : jdx = idx);
                [ rewrite (nat_div_mod_4d jdx n2 n3 n4 Hn2_pos Hn3_pos Hn4_pos);
                  rewrite (nat_div_mod_4d idx n2 n3 n4 Hn2_pos Hn3_pos Hn4_pos);
                  rewrite Ha, Hb, Hc, Hd;
                  rewrite (nat_mod_n4_of_mod_n234 idx n2 n3 n4 Hn2_pos Hn3_pos Hn4_pos);
                  reflexivity
                | exfalso; apply Hne; exact (eq_sym Heq_quad) ]
              | rewrite Hcf; rewrite <- (nat_mod_n4_of_mod_n234 jdx n2 n3 n4 Hn2_pos Hn3_pos Hn4_pos);
                reflexivity ] ]).
      rewrite (sum_f_R0_ext (fun jdx => if andb (andb (andb (jdx / (n2 * n3 * n4) =? i0)%nat
                                                            ((jdx mod (n2 * n3 * n4)) / (n3 * n4) =? j0)%nat)%nat
                                                   (((jdx mod (n2 * n3 * n4)) mod (n3 * n4)) / n4 =? k0)%nat)%nat
                                          (((jdx mod (n2 * n3 * n4)) mod (n3 * n4)) mod n4 =? l0)%nat
                                        then 0%R
                                        else d1 i0 (jdx / (n2 * n3 * n4))%nat
                                             * d1 j0 ((jdx mod (n2 * n3 * n4)) / (n3 * n4))%nat
                                             * d1 k0 (((jdx mod (n2 * n3 * n4)) mod (n3 * n4)) / n4)%nat
                                             * d1 l0 (((jdx mod (n2 * n3 * n4)) mod (n3 * n4)) mod n4)%nat)
                            (fun jdx => let i := (jdx / (n2 * n3 * n4))%nat in
                                        let rem := (jdx mod (n2 * n3 * n4))%nat in
                                        let j := (rem / (n3 * n4))%nat in
                                        let rem' := (rem mod (n3 * n4))%nat in
                                        let k := (rem' / n4)%nat in
                                        let l := (rem' mod n4)%nat in
                                        if andb (andb (andb (i =? i0)%nat (j =? j0)%nat)%nat (k =? k0)%nat)%nat (l =? l0)%nat
                                        then 0%R
                                        else d1 i0 i * d1 j0 j * d1 k0 k * d1 l0 l)
                            (Nat.pred n))
        by (intros jdx Hjdx; cbv beta zeta; reflexivity).
      assert (Hbound : (Nat.pred n = n1 * n2 * n3 * n4 - 1)%nat).
      { subst n. rewrite <- Nat.sub_1_r. reflexivity. }
      rewrite Hbound.
      rewrite (sum_f_R0_flatten_4d n1 n2 n3 n4 Hn1_pos Hn2_pos Hn3_pos Hn4_pos
            (fun i j k l => if andb (andb (andb (i =? i0)%nat (j =? j0)%nat)%nat (k =? k0)%nat)%nat (l =? l0)%nat
                            then 0%R
                            else d1 i0 i * d1 j0 j * d1 k0 k * d1 l0 l)).
      reflexivity. }
    rewrite Hflat.
    rewrite !Nat.sub_1_r.
    pose proof (quad_prod_row_sum_decomp n1 n2 n3 n4 i0 j0 k0 l0 d1 d1 d1 d1 Hi0 Hj0 Hk0 Hl0 Hd1_diag Hd1_diag Hd1_diag Hd1_diag) as H_decomp.
    rewrite H_decomp.
    set (S1 := sum_f_R0 (fun i => if (i =? i0)%nat then 1%R else d1 i0 i) (Nat.pred n1)).
    set (S2 := sum_f_R0 (fun j => if (j =? j0)%nat then 1%R else d1 j0 j) (Nat.pred n2)).
    set (S3 := sum_f_R0 (fun k => if (k =? k0)%nat then 1%R else d1 k0 k) (Nat.pred n3)).
    set (S4 := sum_f_R0 (fun l => if (l =? l0)%nat then 1%R else d1 l0 l) (Nat.pred n4)).
    assert (HS1 : S1 <= 1 + 4 * K_C).
    { unfold S1.
      assert (Htmp : sum_f_R0 (fun i => if Nat.eq_dec i0 i then 0%R else d1 i0 i) (Nat.pred n1) <= 4 * K_C)
        by (apply d_factor_row_sum_le_4K with (C := C); assumption).
      assert (Hrel : sum_f_R0 (fun i => if (i =? i0)%nat then 1%R else d1 i0 i) (Nat.pred n1)
                    = sum_f_R0 (fun i => if Nat.eq_dec i0 i then 0%R else d1 i0 i) (Nat.pred n1) + 1%R).
      { rewrite (sum_f_R0_eq_1_plus_rest n1 i0 (fun i => if (i =? i0)%nat then 1%R else d1 i0 i)).
        - assert (Heq : forall i, (i <= Nat.pred n1)%nat ->
                    (if eq_nat_dec i0 i then 0%R else (if (i =? i0)%nat then 1%R else d1 i0 i))
                    = (if Nat.eq_dec i0 i then 0%R else d1 i0 i)).
          { intros i _. destruct (Nat.eq_dec i0 i) as [-> | Hne]; simpl; [reflexivity |].
            assert (Hb : (i =? i0)%nat = false) by (apply Nat.eqb_neq; intro Heq; apply Hne; symmetry; exact Heq).
            rewrite Hb. reflexivity. }
          rewrite (sum_f_R0_ext
                     (fun i => if eq_nat_dec i0 i then 0%R
                               else (if (i =? i0)%nat then 1%R else d1 i0 i))
                     (fun i => if Nat.eq_dec i0 i then 0%R else d1 i0 i)
                     (Nat.pred n1)).
          + ring.
          + exact Heq.
        - exact Hi0.
        - simpl. rewrite Nat.eqb_refl. reflexivity. }
      rewrite Hrel. replace (1 + 4 * K_C) with (4 * K_C + 1) by ring.
      apply Rplus_le_compat_r; exact Htmp. }
    assert (HS2 : S2 <= 1 + 4 * K_C).
    { unfold S2.
      assert (Htmp : sum_f_R0 (fun j => if Nat.eq_dec j0 j then 0%R else d1 j0 j) (Nat.pred n2) <= 4 * K_C)
        by (apply d_factor_row_sum_le_4K with (C := C); assumption).
      assert (Hrel : sum_f_R0 (fun j => if (j =? j0)%nat then 1%R else d1 j0 j) (Nat.pred n2)
                    = sum_f_R0 (fun j => if Nat.eq_dec j0 j then 0%R else d1 j0 j) (Nat.pred n2) + 1%R).
      { rewrite (sum_f_R0_eq_1_plus_rest n2 j0 (fun j => if (j =? j0)%nat then 1%R else d1 j0 j)).
        - assert (Heq : forall j, (j <= Nat.pred n2)%nat ->
                    (if eq_nat_dec j0 j then 0%R else (if (j =? j0)%nat then 1%R else d1 j0 j))
                    = (if Nat.eq_dec j0 j then 0%R else d1 j0 j)).
          { intros j _. destruct (Nat.eq_dec j0 j) as [-> | Hne]; simpl; [reflexivity |].
            assert (Hb : (j =? j0)%nat = false) by (apply Nat.eqb_neq; intro Heq; apply Hne; symmetry; exact Heq).
            rewrite Hb. reflexivity. }
          rewrite (sum_f_R0_ext
                     (fun j => if eq_nat_dec j0 j then 0%R
                               else (if (j =? j0)%nat then 1%R else d1 j0 j))
                     (fun j => if Nat.eq_dec j0 j then 0%R else d1 j0 j)
                     (Nat.pred n2)).
          + ring.
          + exact Heq.
        - exact Hj0.
        - simpl. rewrite Nat.eqb_refl. reflexivity. }
      rewrite Hrel. replace (1 + 4 * K_C) with (4 * K_C + 1) by ring.
      apply Rplus_le_compat_r; exact Htmp. }
    assert (HS3 : S3 <= 1 + 4 * K_C).
    { unfold S3.
      assert (Htmp : sum_f_R0 (fun k => if Nat.eq_dec k0 k then 0%R else d1 k0 k) (Nat.pred n3) <= 4 * K_C)
        by (apply d_factor_row_sum_le_4K with (C := C); assumption).
      assert (Hrel : sum_f_R0 (fun k => if (k =? k0)%nat then 1%R else d1 k0 k) (Nat.pred n3)
                    = sum_f_R0 (fun k => if Nat.eq_dec k0 k then 0%R else d1 k0 k) (Nat.pred n3) + 1%R).
      { rewrite (sum_f_R0_eq_1_plus_rest n3 k0 (fun k => if (k =? k0)%nat then 1%R else d1 k0 k)).
        - assert (Heq : forall k, (k <= Nat.pred n3)%nat ->
                    (if eq_nat_dec k0 k then 0%R else (if (k =? k0)%nat then 1%R else d1 k0 k))
                    = (if Nat.eq_dec k0 k then 0%R else d1 k0 k)).
          { intros k _. destruct (Nat.eq_dec k0 k) as [-> | Hne]; simpl; [reflexivity |].
            assert (Hb : (k =? k0)%nat = false) by (apply Nat.eqb_neq; intro Heq; apply Hne; symmetry; exact Heq).
            rewrite Hb. reflexivity. }
          rewrite (sum_f_R0_ext
                     (fun k => if eq_nat_dec k0 k then 0%R
                               else (if (k =? k0)%nat then 1%R else d1 k0 k))
                     (fun k => if Nat.eq_dec k0 k then 0%R else d1 k0 k)
                     (Nat.pred n3)).
          + ring.
          + exact Heq.
        - exact Hk0.
        - simpl. rewrite Nat.eqb_refl. reflexivity. }
      rewrite Hrel. replace (1 + 4 * K_C) with (4 * K_C + 1) by ring.
      apply Rplus_le_compat_r; exact Htmp. }
    assert (HS4 : S4 <= 1 + 4 * K_C).
    { unfold S4.
      assert (Htmp : sum_f_R0 (fun l => if Nat.eq_dec l0 l then 0%R else d1 l0 l) (Nat.pred n4) <= 4 * K_C)
        by (apply d_factor_row_sum_le_4K with (C := C); assumption).
      assert (Hrel : sum_f_R0 (fun l => if (l =? l0)%nat then 1%R else d1 l0 l) (Nat.pred n4)
                    = sum_f_R0 (fun l => if Nat.eq_dec l0 l then 0%R else d1 l0 l) (Nat.pred n4) + 1%R).
      { rewrite (sum_f_R0_eq_1_plus_rest n4 l0 (fun l => if (l =? l0)%nat then 1%R else d1 l0 l)).
        - assert (Heq : forall l, (l <= Nat.pred n4)%nat ->
                    (if eq_nat_dec l0 l then 0%R else (if (l =? l0)%nat then 1%R else d1 l0 l))
                    = (if Nat.eq_dec l0 l then 0%R else d1 l0 l)).
          { intros l _. destruct (Nat.eq_dec l0 l) as [-> | Hne]; simpl; [reflexivity |].
            assert (Hb : (l =? l0)%nat = false) by (apply Nat.eqb_neq; intro Heq; apply Hne; symmetry; exact Heq).
            rewrite Hb. reflexivity. }
          rewrite (sum_f_R0_ext
                     (fun l => if eq_nat_dec l0 l then 0%R
                               else (if (l =? l0)%nat then 1%R else d1 l0 l))
                     (fun l => if Nat.eq_dec l0 l then 0%R else d1 l0 l)
                     (Nat.pred n4)).
          + ring.
          + exact Heq.
        - exact Hl0.
        - simpl. rewrite Nat.eqb_refl. reflexivity. }
      rewrite Hrel. replace (1 + 4 * K_C) with (4 * K_C + 1) by ring.
      apply Rplus_le_compat_r; exact Htmp. }
    unfold M_bound, K0.

    (* 局部引理：有限和逐项非负，则和为非负 *)
    assert (sum_f_R0_nonneg_local :
      forall (f : nat -> R) (N : nat),
        (forall i, 0 <= f i) -> 0 <= sum_f_R0 f N).
    {
      intros f N Hf.
      induction N as [| m IH].
      - simpl; apply Hf.
      - rewrite sum_f_R0_S.
        apply Rle_trans with (0 + 0).
        + lra.
        + apply Rplus_le_compat.
          * apply IH.
          * apply Hf.
    }

    assert (HS1_nonneg : 0 <= S1).
    {
      unfold S1.
      apply sum_f_R0_nonneg_local.
      intros m.
      unfold d1.
      destruct (Nat.eq_dec m i0) as [-> | Hm].
      - rewrite Nat.eqb_refl; lra.
      - assert (Hb : (m =? i0)%nat = false) by (apply Nat.eqb_neq; exact Hm).
        rewrite Hb.
        apply d_factor_nonneg.
    }

    assert (HS2_nonneg : 0 <= S2).
    {
      unfold S2.
      apply sum_f_R0_nonneg_local.
      intros m.
      unfold d1.
      destruct (Nat.eq_dec m j0) as [-> | Hm].
      - rewrite Nat.eqb_refl; lra.
      - assert (Hb : (m =? j0)%nat = false) by (apply Nat.eqb_neq; exact Hm).
        rewrite Hb.
        apply d_factor_nonneg.
    }

    assert (HS3_nonneg : 0 <= S3).
    {
      unfold S3.
      apply sum_f_R0_nonneg_local.
      intros m.
      unfold d1.
      destruct (Nat.eq_dec m k0) as [-> | Hm].
      - rewrite Nat.eqb_refl; lra.
      - assert (Hb : (m =? k0)%nat = false) by (apply Nat.eqb_neq; exact Hm).
        rewrite Hb.
        apply d_factor_nonneg.
    }

    assert (HS4_nonneg : 0 <= S4).
    {
      unfold S4.
      apply sum_f_R0_nonneg_local.
      intros m.
      unfold d1.
      destruct (Nat.eq_dec m l0) as [-> | Hm].
      - rewrite Nat.eqb_refl; lra.
      - assert (Hb : (m =? l0)%nat = false) by (apply Nat.eqb_neq; exact Hm).
        rewrite Hb.
        apply d_factor_nonneg.
    }

    assert (Hprod_le :
      S1 * S2 * S3 * S4 - 1
      <= (1 + 4 * K_C) * (1 + 4 * K_C) * (1 + 4 * K_C) * (1 + 4 * K_C) - 1).
    {
      apply Rplus_le_compat_r.
      assert (H123 :
        S1 * S2 * S3 <= (1 + 4 * K_C) * (1 + 4 * K_C) * (1 + 4 * K_C)).
      {
        assert (H12 :
          S1 * S2 <= (1 + 4 * K_C) * (1 + 4 * K_C)).
        { apply Rmult_le_compat; [exact HS1_nonneg | exact HS2_nonneg | exact HS1 | exact HS2]. }
        apply Rmult_le_compat.
        - apply Rmult_le_pos; [exact HS1_nonneg | exact HS2_nonneg].
        - exact HS3_nonneg.
        - exact H12.
        - exact HS3.
      }
      apply Rmult_le_compat.
      - apply Rmult_le_pos; [apply Rmult_le_pos; [exact HS1_nonneg | exact HS2_nonneg] | exact HS3_nonneg].
      - exact HS4_nonneg.
      - exact H123.
      - exact HS4.
    }

    apply Rmult_le_compat_l.
    - exact HK0_nonneg.
    - exact Hprod_le.
    }

  (* ---- 调用维度无关骨架 ---- *)
  assert (HM_pos : (M > 0)%nat) by (unfold M; lia).
  pose proof (abstract_unconditional_basis n phi_flat M M_bound delta_quad HM_pos Htrunc Hnorm1
                Hdelta_sym Hdelta_nonneg Hdecay Hrow_sum coeffs_flat Hlen_flat') as H_abs.

  (* ---- 收尾：把扁平 F / S 重排成四维嵌套形式 ---- *)
  assert (HF_flat_eq : forall k,
    Csum (fun i => Csum (fun j => Csum (fun k2 => Csum (fun l =>
      nth (flatten_4d n2 n3 n4 i j k2 l) coeffs_flat C0 *c
      phi4D_norm (a i) (b j) (c k2) (d l) k) n4) n3) n2) n1
    = Csum (fun idx : nat => nth idx coeffs_flat C0 *c phi_flat idx k) n).
  { intros k.
    rewrite <- (Csum_flatten_4d n1 n2 n3 n4 Hn2_pos Hn3_pos Hn4_pos
                  (fun i j k2 l => nth (flatten_4d n2 n3 n4 i j k2 l) coeffs_flat C0 *c
                              phi4D_norm (a i) (b j) (c k2) (d l) k)).
    apply Csum_ext; intros idx Hidx.
    unfold phi_flat.

    assert (Hflat_idx : flatten_4d n2 n3 n4 (idx / (n2 * n3 * n4))%nat
                                      ((idx mod (n2 * n3 * n4)) / (n3 * n4))%nat
                                      (((idx mod (n2 * n3 * n4)) mod (n3 * n4)) / n4)%nat
                                      (idx mod n4)%nat = idx).
    {
      Open Scope nat_scope.
      unfold flatten_4d.
      rewrite <- (nat_mod_n4_of_mod_n234 idx n2 n3 n4 Hn2_pos Hn3_pos Hn4_pos).
      assert (Hexpand : (((idx / (n2 * n3 * n4))%nat * n2 + (idx mod (n2 * n3 * n4) / (n3 * n4))%nat) * n3
                          + ((idx mod (n2 * n3 * n4)) mod (n3 * n4) / n4)%nat) * n4
                          + (((idx mod (n2 * n3 * n4)) mod (n3 * n4)) mod n4)%nat
                        = (idx / (n2 * n3 * n4))%nat * (n2 * n3 * n4)
                          + (idx mod (n2 * n3 * n4) / (n3 * n4))%nat * (n3 * n4)
                          + ((idx mod (n2 * n3 * n4)) mod (n3 * n4) / n4)%nat * n4
                          + (((idx mod (n2 * n3 * n4)) mod (n3 * n4)) mod n4)%nat) by ring.
      rewrite Hexpand.
      symmetry.
      exact (nat_div_mod_4d idx n2 n3 n4 Hn2_pos Hn3_pos Hn4_pos).
      Close Scope nat_scope.
    }
    rewrite !(nat_mod_n4_of_mod_n234 idx n2 n3 n4 Hn2_pos Hn3_pos Hn4_pos).
    rewrite Hflat_idx.
    reflexivity.
  }


  assert (HS_flat_eq :
    sum_f_R0 (fun i => sum_f_R0 (fun j => sum_f_R0 (fun k2 => sum_f_R0
      (fun l => Cnorm_sq (nth (flatten_4d n2 n3 n4 i j k2 l) coeffs_flat C0)) (n4 - 1)) (n3 - 1)) (n2 - 1)) (n1 - 1)
    = sum_f_R0 (fun idx : nat => Cnorm_sq (nth idx coeffs_flat C0)) (Nat.pred (n1 * n2 * n3 * n4))).
  {
    rewrite <- (sum_f_R0_flatten_4d n1 n2 n3 n4 Hn1_pos Hn2_pos Hn3_pos Hn4_pos
                  (fun i j k2 l => Cnorm_sq (nth (flatten_4d n2 n3 n4 i j k2 l) coeffs_flat C0))).

    (* 统一求和上界 *)
    rewrite (Nat.sub_1_r (n1 * n2 * n3 * n4)%nat).

    apply sum_f_R0_ext; intros idx0 Hlt.
    assert (Hflat_idx0 : flatten_4d n2 n3 n4 (idx0 / (n2 * n3 * n4))%nat
                                      ((idx0 mod (n2 * n3 * n4)) / (n3 * n4))%nat
                                      (((idx0 mod (n2 * n3 * n4)) mod (n3 * n4)) / n4)%nat
                                      (idx0 mod n4)%nat = idx0).
    {
      Open Scope nat_scope.
      unfold flatten_4d.
      rewrite <- (nat_mod_n4_of_mod_n234 idx0 n2 n3 n4 Hn2_pos Hn3_pos Hn4_pos).
      assert (Hexpand0 : (((idx0 / (n2 * n3 * n4))%nat * n2 + (idx0 mod (n2 * n3 * n4) / (n3 * n4))%nat) * n3
                          + ((idx0 mod (n2 * n3 * n4)) mod (n3 * n4) / n4)%nat) * n4
                          + (((idx0 mod (n2 * n3 * n4)) mod (n3 * n4)) mod n4)%nat
                        = (idx0 / (n2 * n3 * n4))%nat * (n2 * n3 * n4)
                          + (idx0 mod (n2 * n3 * n4) / (n3 * n4))%nat * (n3 * n4)
                          + ((idx0 mod (n2 * n3 * n4)) mod (n3 * n4) / n4)%nat * n4
                          + (((idx0 mod (n2 * n3 * n4)) mod (n3 * n4)) mod n4)%nat) by ring.
      rewrite Hexpand0.
      symmetry.
      exact (nat_div_mod_4d idx0 n2 n3 n4 Hn2_pos Hn3_pos Hn4_pos).
      Close Scope nat_scope.
    }
    simpl.
    rewrite (nat_mod_n4_of_mod_n234 idx0 n2 n3 n4 Hn2_pos Hn3_pos Hn4_pos).
    rewrite Hflat_idx0.
    reflexivity.
    }

  assert (HM_pred_eq : Nat.pred M = (M - 1)%nat) by (unfold M; lia).

  assert (H_final : (1 - M_bound) *
      (sum_f_R0 (fun i => sum_f_R0 (fun j => sum_f_R0 (fun k2 => sum_f_R0 (fun l => Cnorm_sq (nth (flatten_4d n2 n3 n4 i j k2 l) coeffs_flat C0)) (n4 - 1)) (n3 - 1)) (n2 - 1)) (n1 - 1))
      <= l2_norm_sq (fun k : nat =>
           Csum (fun i => Csum (fun j => Csum (fun k2 => Csum (fun l => nth (flatten_4d n2 n3 n4 i j k2 l) coeffs_flat C0 *c
                                             phi4D_norm (a i) (b j) (c k2) (d l) k) n4) n3) n2) n1) (M - 1)
      <= (1 + M_bound) *
      (sum_f_R0 (fun i => sum_f_R0 (fun j => sum_f_R0 (fun k2 => sum_f_R0 (fun l => Cnorm_sq (nth (flatten_4d n2 n3 n4 i j k2 l) coeffs_flat C0)) (n4 - 1)) (n3 - 1)) (n2 - 1)) (n1 - 1))).
  { set (F := fun k : nat => Csum (fun idx : nat => nth idx coeffs_flat C0 *c phi_flat idx k) n).
    cbv zeta in H_abs.
    destruct H_abs as [H_low H_high].
    assert (H_eq : l2_norm_sq (fun k : nat =>
        Csum (fun i => Csum (fun j => Csum (fun k2 => Csum (fun l => nth (flatten_4d n2 n3 n4 i j k2 l) coeffs_flat C0 *c
                                             phi4D_norm (a i) (b j) (c k2) (d l) k) n4) n3) n2) n1) (M - 1)
        = l2_norm_sq F (Nat.pred M)).
    { unfold l2_norm_sq.
      rewrite <- HM_pred_eq.
      apply sum_f_R0_ext; intros k Hk.
      rewrite (HF_flat_eq k); reflexivity. }
    rewrite H_eq, HS_flat_eq.
    unfold F.
    exact (conj H_low H_high). }
  apply H_final.
Qed.

