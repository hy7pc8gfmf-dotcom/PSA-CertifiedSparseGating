(* ============================================================
   库 ca_2d_wide_asm —— 2D 宽轨（2D-wide）组装定理
   内容：tensor_product_unconditional_basis_2d_wide（无 H_dom，K0=C³/2）
   + M_bound_2d_wide 定义与 C=4 数值裁决（768）。
   前置：ca_2d_wide_engine（衰减引擎）。
   纪律：零 Admitted、零活动 Axiom、零 classic。
   ============================================================ *)
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
Import ComplexNumbers.
Import ExtendedTheorems.
Import UnconditionalBasisLemmas.

Open Scope R_scope.
Require Import ca_2d_wide_engine.
(* ============ 3. 组装：tensor_product_unconditional_basis_2d_wide ============ *)
(* 无 H_dom；K0 = Rmax 8 C³ / 2；M_bound = K0·((1+4K_C)² − 1)。
   其余前提与 corrected / 3D 模板同构。 *)
Theorem tensor_product_unconditional_basis_2d_wide :
  forall (C : nat) (HCgt2 : (C > 2)%nat)
    (seq1 seq2 : nat -> nat)
    (Hsparse1 : forall i : nat, (INR (seq1 (S i)) > INR C * INR (seq1 i))%R)
    (Hsparse2 : forall i : nat, (INR (seq2 (S i)) > INR C * INR (seq2 i))%R)
    (Hge2_1 : forall i : nat, (seq1 i >= 2)%nat)
    (Hge2_2 : forall i : nat, (seq2 i >= 2)%nat)
    (I1 I2 : list nat)
    (Hdup1 : NoDup I1) (Hsorted1 : Sorted Nat.lt I1)
    (Hdup2 : NoDup I2) (Hsorted2 : Sorted Nat.lt I2)
    (coeffs_flat : list Complex)
    (n1 n2 : nat) (Hn1 : n1 = length I1) (Hn2 : n2 = length I2)
    (Hn1_pos : (n1 > 0)%nat) (Hn2_pos : (n2 > 0)%nat)
    (Hlen_flat : length coeffs_flat = (n1 * n2)%nat)
    (HI1 : I1 = seq 0 n1)
    (HI2 : I2 = seq 0 n2)
    (H_index_bound : forall idx1 idx2 : nat,
        (idx1 < n1 * n2)%nat -> (idx2 < n1 * n2)%nat ->
        (Z.abs_nat (Z.of_nat (idx1 / n2) - Z.of_nat (idx2 / n2)) +
         Z.abs_nat (Z.of_nat (idx1 mod n2) - Z.of_nat (idx2 mod n2)) <= 6)%nat),
  let vals1 := map seq1 I1 in
  let vals2 := map seq2 I2 in
  let a i := nth i vals1 0%nat in
  let b j := nth j vals2 0%nat in
  let maxIdx1 := fold_right Nat.max 0%nat I1 in
  let maxIdx2 := fold_right Nat.max 0%nat I2 in
  let M := S (max (seq1 maxIdx1) (seq2 maxIdx2)) in
  let phi2D_norm (i j : nat) (k : nat) : Complex :=
    Cof_real (/ sqrt (INR (Nat.min (a i) (b j)) / (INR (a i) * INR (b j)))) *c
    (psi (a i) k *c psi (b j) k) in
  let phi_flat idx k :=
    phi2D_norm (idx / n2)%nat (idx mod n2)%nat k in
  let F_2D_wide k :=
    Csum (fun idx => nth idx coeffs_flat C0 *c phi_flat idx k) (n1 * n2) in
  let S := sum_f_R0 (fun idx => Cnorm_sq (nth idx coeffs_flat C0)) (n1 * n2 - 1) in
  let K_C := K (INR C) in
  let K0 := (Rmax 8 ((INR C) ^ 3)) / 2 in
  let M_bound := K0 * ((1 + 4 * K_C) * (1 + 4 * K_C) - 1) in
  ((1 - M_bound) * S <= l2_norm_sq F_2D_wide (M - 1) <= (1 + M_bound) * S)%R.
Proof.
  intros C HCgt2 seq1 seq2 Hsparse1 Hsparse2 Hge2_1 Hge2_2
         I1 I2 Hdup1 Hsorted1 Hdup2 Hsorted2 coeffs_flat n1 n2 Hn1 Hn2 Hn1_pos Hn2_pos Hlen_flat
         HI1 HI2 H_index_bound.
  assert (Hc_ge2 : (C >= 2)%nat) by lia.
  assert (HCgt1_R : 1 < INR C) by (change 1 with (INR 1); apply lt_INR; lia).
  set (r := sqrt (INR C)).
  assert (Hr_gt1 : r > 1).
  { unfold r; rewrite <- sqrt_1. apply sqrt_lt_1; [lra|apply pos_INR|exact HCgt1_R]. }
  assert (Hr_pos : r > 0) by (apply sqrt_lt_R0_c; apply lt_0_INR; lia).
  set (K_C := K (INR C)).
  assert (HK_pos : 0 < K_C) by (apply K_pos; exact HCgt2).
  set (n := (n1 * n2)%nat).
  assert (Hn_pos : (n > 0)%nat) by (apply Nat.mul_pos_pos; assumption).
  assert (Hlen_flat' : length coeffs_flat = n) by (subst n; exact Hlen_flat).

  set (vals1 := map seq1 I1).
  set (vals2 := map seq2 I2).
  set (a := fun i : nat => nth i vals1 0%nat).
  set (b := fun j : nat => nth j vals2 0%nat).
  set (gamma := fun i j : nat => sqrt (INR (Nat.min (a i) (b j)) / (INR (a i) * INR (b j)))).
  set (phi2D_norm := fun (i j k : nat) => Cof_real (/ gamma i j) *c (psi (a i) k *c psi (b j) k)).
  pose (phi_flat := fun idx k => phi2D_norm (idx / n2)%nat (idx mod n2)%nat k).
  set (maxIdx1 := fold_right Nat.max 0%nat I1).
  set (maxIdx2 := fold_right Nat.max 0%nat I2).
  set (M := S (max (seq1 maxIdx1) (seq2 maxIdx2))).

  (* 截断、归一、delta、衰减、行和——全部照抄 corrected/点态变体，仅常数 /2 *)
  assert (Hseq1_inc : forall x y, (x <= y)%nat -> (seq1 x <= seq1 y)%nat).
  { intros x y Hle; destruct (Nat.eq_dec x y) as [Heq | Hne].
    - subst; apply Nat.le_refl.
    - apply Nat.lt_le_incl; eapply seq_strict_growth_lt; eauto; lia. }
  assert (Hseq2_inc : forall x y, (x <= y)%nat -> (seq2 x <= seq2 y)%nat).
  { intros x y Hle; destruct (Nat.eq_dec x y) as [Heq | Hne].
    - subst; apply Nat.le_refl.
    - apply Nat.lt_le_incl; eapply seq_strict_growth_lt; eauto; lia. }

  assert (Htrunc : forall idx k, (idx < n)%nat -> (k >= Nat.pred M)%nat -> phi_flat idx k = C0).
  { intros idx k Hidx Hk; unfold phi_flat.
    set (i := (idx / n2)%nat); set (j := (idx mod n2)%nat).
    assert (Hi : (i < n1)%nat) by (apply Nat.Div0.div_lt_upper_bound; lia).
    assert (Hj : (j < n2)%nat) by (apply Nat.mod_upper_bound; lia).
    unfold phi2D_norm.
    assert (Ha_le_max : (a i <= max (seq1 maxIdx1) (seq2 maxIdx2))%nat).
    { unfold a, vals1.
      assert (Hi_len : (i < length I1)%nat) by (rewrite <- Hn1; exact Hi).
      rewrite (H_nth_map nat nat seq1 I1 0%nat 0%nat i Hi_len).
      apply Nat.le_trans with (seq1 maxIdx1).
      - apply Hseq1_inc.
        eapply fold_right_max_ge.
        apply nth_In; exact Hi_len.
      - apply Nat.le_max_l. }
    assert (Hb_le_max : (b j <= max (seq1 maxIdx1) (seq2 maxIdx2))%nat).
    { unfold b, vals2.
      assert (Hj_len : (j < length I2)%nat) by (rewrite <- Hn2; exact Hj).
      rewrite (H_nth_map nat nat seq2 I2 0%nat 0%nat j Hj_len).
      apply Nat.le_trans with (seq2 maxIdx2).
      - apply Hseq2_inc.
        eapply fold_right_max_ge.
        apply nth_In; exact Hj_len.
      - apply Nat.le_max_r. }
    assert (Hmax_le_k : (max (seq1 maxIdx1) (seq2 maxIdx2) <= k)%nat).
    { unfold M in Hk; lia. }
    assert (Ha_le_k : (a i <= k)%nat) by lia.
    assert (Hb_le_k : (b j <= k)%nat) by lia.
    rewrite (psi_ge_n_zero (a i) k Ha_le_k).
    rewrite (psi_ge_n_zero (b j) k Hb_le_k).
    rewrite Cmul_0_l.
    rewrite Cmul_0_r.
    reflexivity. }

  assert (Hnorm1 : forall idx, (idx < n)%nat -> l2_norm_sq (phi_flat idx) (Nat.pred M) = 1%R).
  { intros idx Hlt; unfold phi_flat.
    set (i := (idx / n2)%nat); set (j := (idx mod n2)%nat).
    assert (Hi : (i < n1)%nat) by (apply Nat.Div0.div_lt_upper_bound; lia).
    assert (Hj : (j < n2)%nat) by (apply Nat.mod_upper_bound; lia).
    unfold phi2D_norm.
    assert (Ha_ge2 : (a i >= 2)%nat).
    { unfold a, vals1.
      assert (Hi_len : (i < length I1)%nat) by (rewrite <- Hn1; exact Hi).
      rewrite (H_nth_map nat nat seq1 I1 0%nat 0%nat i Hi_len).
      apply Hge2_1. }
    assert (Hb_ge2 : (b j >= 2)%nat).
    { unfold b, vals2.
      assert (Hj_len : (j < length I2)%nat) by (rewrite <- Hn2; exact Hj).
      rewrite (H_nth_map nat nat seq2 I2 0%nat 0%nat j Hj_len).
      apply Hge2_2. }
    set (g := gamma i j).
    assert (Hg_pos : 0 < g).
    { unfold g, gamma.
      assert (Hmin_pos : (0 < Nat.min (a i) (b j))%nat) by lia.
      apply sqrt_lt_R0_c.
      apply Rdiv_lt_0_compat.
      - apply lt_0_INR; exact Hmin_pos.
      - apply Rmult_lt_0_compat; apply lt_0_INR; lia. }
    assert (Ha_le_max : (a i <= max (seq1 maxIdx1) (seq2 maxIdx2))%nat).
    { unfold a, vals1.
      assert (Hi_len : (i < length I1)%nat) by (rewrite <- Hn1; exact Hi).
      rewrite (H_nth_map nat nat seq1 I1 0%nat 0%nat i Hi_len).
      apply Nat.le_trans with (seq1 maxIdx1).
      - apply Hseq1_inc. eapply fold_right_max_ge. apply nth_In; exact Hi_len.
      - apply Nat.le_max_l. }
    assert (Hb_le_max : (b j <= max (seq1 maxIdx1) (seq2 maxIdx2))%nat).
    { unfold b, vals2.
      assert (Hj_len : (j < length I2)%nat) by (rewrite <- Hn2; exact Hj).
      rewrite (H_nth_map nat nat seq2 I2 0%nat 0%nat j Hj_len).
      apply Nat.le_trans with (seq2 maxIdx2).
      - apply Hseq2_inc. eapply fold_right_max_ge. apply nth_In; exact Hj_len.
      - apply Nat.le_max_r. }
    assert (Ha_lt_M : (a i < M)%nat) by (unfold M; apply Nat.lt_succ_r; exact Ha_le_max).
    assert (Hb_lt_M : (b j < M)%nat) by (unfold M; apply Nat.lt_succ_r; exact Hb_le_max).
    set (F k := Cof_real (/ g) *c (psi (a i) k *c psi (b j) k)).
    assert (HnormF : l2_norm_sq F (Nat.pred M) = 1%R).
    { unfold l2_norm_sq, F.
      assert (Heq : forall k, Cnorm_sq (Cof_real (/ g) *c (psi (a i) k *c psi (b j) k))
                     = (/ g)^2 * (Cnorm_sq (psi (a i) k) * Cnorm_sq (psi (b j) k))).
      { intro k.
        rewrite Cnorm_sq_mult, (Cnorm_sq_mult (psi (a i) k) (psi (b j) k)).
        assert (Hcof_sq : Cnorm_sq (Cof_real (/ g)) = (/ g)^2).
        { unfold Cof_real, Cnorm_sq, Rsqr; simpl; ring. }
        rewrite Hcof_sq; reflexivity. }
      rewrite (sum_f_R0_ext _ (fun k => (/ g)^2 * (Cnorm_sq (psi (a i) k) * Cnorm_sq (psi (b j) k)))).
      - rewrite (sum_f_R0_scal_l ((/ g)^2) (fun k => Cnorm_sq (psi (a i) k) * Cnorm_sq (psi (b j) k)) (Nat.pred M)).
        destruct (Nat.min_spec (a i) (b j)) as [(Hle_ab & Hmin_ab) | (Hle_ba & Hmin_ba)].
        * assert (Ha_le_predM : (a i <= Nat.pred M)%nat) by lia.
          assert (Htrunc_full : sum_f_R0 (fun k => Cnorm_sq (psi (a i) k) * Cnorm_sq (psi (b j) k)) (Nat.pred M)
                              = sum_f_R0 (fun k => Cnorm_sq (psi (a i) k) * Cnorm_sq (psi (b j) k)) (a i)).
          { apply sum_f_R0_trunc_tail with (M := a i) (N := Nat.pred M); auto.
            intros k [Hk1 Hk2]; assert (Hk_ge_ai : (a i <= k)%nat) by exact Hk1;
            rewrite (Cnorm_sq_psi_exact (a i) k), (proj2 (Nat.ltb_ge k (a i)) Hk_ge_ai); ring. }
          rewrite Htrunc_full.
          assert (Ha_i_pos : (a i > 0)%nat) by lia.
          replace (a i) with (S (a i - 1))%nat by lia.
          rewrite sum_f_R0_S.
          replace (S (a i - 1)) with (a i) by lia.
          assert (Hlast_zero : Cnorm_sq (psi (a i) (a i)) * Cnorm_sq (psi (b j) (a i)) = 0%R).
          { rewrite (Cnorm_sq_psi_exact (a i) (a i)).
            replace (Nat.ltb (a i) (a i)) with false by (symmetry; apply Nat.ltb_ge; apply Nat.le_refl).
            ring. }
          rewrite Hlast_zero, Rplus_0_r.
          set (cst := (1 / INR (a i)) * (1 / INR (b j))).
          assert (Hterm_eq : forall k, (k < a i)%nat ->
                       Cnorm_sq (psi (a i) k) * Cnorm_sq (psi (b j) k) = cst).
          { intros k Hk_ai.
            assert (Hk_bj : (k < b j)%nat) by (apply Nat.lt_trans with (a i); auto).
            assert (Htb_ai : Nat.ltb k (a i) = true) by (apply Nat.ltb_lt; exact Hk_ai).
            assert (Htb_bj : Nat.ltb k (b j) = true) by (apply Nat.ltb_lt; exact Hk_bj).
            rewrite Cnorm_sq_psi_exact, Htb_ai, Cnorm_sq_psi_exact, Htb_bj.
            unfold cst, Rdiv; field; split; apply Rgt_not_eq; apply lt_0_INR; lia. }
          rewrite (sum_f_R0_ext _ (fun _ => cst) (a i - 1)).
          { rewrite (sum_f_R0_const cst (a i - 1)).
            replace (S (a i - 1))%nat with (a i)%nat by lia.
            unfold g, gamma; rewrite Hmin_ab.
            field_simplify.
            - set (s := sqrt (INR (a i) / (INR (a i) * INR (b j)))).
              assert (H_sqrt_sq : s ^ 2 = INR (a i) / (INR (a i) * INR (b j))).
              { replace (s ^ 2) with (s * s) by ring.
                apply sqrt_sqrt.
                apply Rmult_le_pos; [apply pos_INR; lia | left; apply Rinv_0_lt_compat; apply Rmult_lt_0_compat; apply lt_0_INR; lia]. }
              subst s.
              rewrite H_sqrt_sq.
              unfold cst; field; split; apply Rgt_not_eq; apply lt_0_INR; lia.
            - apply Rgt_not_eq, sqrt_lt_R0_c.
              apply Rdiv_lt_0_compat; [apply lt_0_INR; lia | apply Rmult_lt_0_compat; apply lt_0_INR; lia]. }
          { intros k Hk; apply Hterm_eq; lia. }
        * assert (Hb_le_predM : (b j <= Nat.pred M)%nat) by lia.
          assert (Htrunc_full : sum_f_R0 (fun k => Cnorm_sq (psi (a i) k) * Cnorm_sq (psi (b j) k)) (Nat.pred M)
                              = sum_f_R0 (fun k => Cnorm_sq (psi (a i) k) * Cnorm_sq (psi (b j) k)) (b j)).
          { apply sum_f_R0_trunc_tail with (M := b j) (N := Nat.pred M); auto.
            intros k [Hk1 Hk2]; assert (Hk_ge_bj : (b j <= k)%nat) by exact Hk1;
            rewrite (Cnorm_sq_psi_exact (b j) k), (proj2 (Nat.ltb_ge k (b j)) Hk_ge_bj); ring. }
          rewrite Htrunc_full.
          assert (Hb_j_pos : (b j > 0)%nat) by lia.
          replace (b j) with (S (b j - 1))%nat by lia.
          rewrite sum_f_R0_S.
          replace (S (b j - 1)) with (b j) by lia.
          assert (Hlast_zero : Cnorm_sq (psi (a i) (b j)) * Cnorm_sq (psi (b j) (b j)) = 0%R).
          { rewrite (Cnorm_sq_psi_exact (b j) (b j)).
            replace (Nat.ltb (b j) (b j)) with false by (symmetry; apply Nat.ltb_ge; apply Nat.le_refl).
            ring. }
          rewrite Hlast_zero, Rplus_0_r.
          set (cst := (1 / INR (a i)) * (1 / INR (b j))).
          assert (Hterm_eq : forall k, (k < b j)%nat ->
                       Cnorm_sq (psi (a i) k) * Cnorm_sq (psi (b j) k) = cst).
          { intros k Hk_bj.
            assert (Hk_ai : (k < a i)%nat) by (apply Nat.lt_le_trans with (b j); auto).
            assert (Htb_ai : Nat.ltb k (a i) = true) by (apply Nat.ltb_lt; exact Hk_ai).
            assert (Htb_bj : Nat.ltb k (b j) = true) by (apply Nat.ltb_lt; exact Hk_bj).
            rewrite Cnorm_sq_psi_exact, Htb_ai, Cnorm_sq_psi_exact, Htb_bj.
            unfold cst, Rdiv; field; split; apply Rgt_not_eq; apply lt_0_INR; lia. }
          rewrite (sum_f_R0_ext _ (fun _ => cst) (b j - 1)).
          { rewrite (sum_f_R0_const cst (b j - 1)).
            replace (S (b j - 1))%nat with (b j)%nat by lia.
            unfold g, gamma; rewrite Hmin_ba.
            field_simplify.
            - set (s := sqrt (INR (b j) / (INR (a i) * INR (b j)))).
              assert (H_sqrt_sq : s ^ 2 = INR (b j) / (INR (a i) * INR (b j))).
              { replace (s ^ 2) with (s * s) by ring.
                apply sqrt_sqrt.
                apply Rmult_le_pos; [apply pos_INR; lia | left; apply Rinv_0_lt_compat; apply Rmult_lt_0_compat; apply lt_0_INR; lia]. }
              subst s.
              rewrite H_sqrt_sq.
              unfold cst; field; split; apply Rgt_not_eq; apply lt_0_INR; lia.
            - apply Rgt_not_eq, sqrt_lt_R0_c.
              apply Rdiv_lt_0_compat; [apply lt_0_INR; lia | apply Rmult_lt_0_compat; apply lt_0_INR; lia]. }
          { intros k Hk; apply Hterm_eq; lia. }
      - intros k Hk; apply Heq. }
    exact HnormF. }

  set (d1 := d_factor r).
  pose (delta_pair := fun (idx1 idx2 : nat) =>
    d1 (idx1 / n2)%nat (idx2 / n2)%nat * d1 (idx1 mod n2)%nat (idx2 mod n2)%nat).

  assert (d_factor_sym : forall i j, d_factor r i j = d_factor r j i).
  { intros i j; unfold d_factor.
    destruct (Nat.eq_dec i j) as [Heq | Hneq].
    - subst i; reflexivity.
    - assert (Hij_false : (i =? j)%nat = false) by (apply Nat.eqb_neq; exact Hneq).
      assert (Hji_false : (j =? i)%nat = false) by (apply Nat.eqb_neq; auto).
      rewrite Hij_false, Hji_false.
      f_equal. f_equal.
      replace (Z.of_nat j - Z.of_nat i)%Z with (- (Z.of_nat i - Z.of_nat j))%Z by lia.
      rewrite Z_abs_nat_opp.
      reflexivity. }

  assert (Hdelta_sym : forall (i j : nat), (i < n)%nat -> (j < n)%nat -> delta_pair i j = delta_pair j i).
  { intros i j Hi Hj; unfold delta_pair, d1.
    rewrite (d_factor_sym (i / n2)%nat (j / n2)%nat).
    rewrite (d_factor_sym (i mod n2)%nat (j mod n2)%nat).
    reflexivity. }

  assert (d_factor_nonneg : forall i j, 0 <= d_factor r i j).
  { intros i j; unfold d_factor.
    destruct (Nat.eqb_spec i j) as [Heq | Hneq].
    - subst i; lra.
    - apply Rlt_le; apply Rdiv_lt_0_compat; [lra | apply pow_lt; exact Hr_pos]. }

  assert (Hdelta_nonneg : forall (i j : nat), (i < n)%nat -> (j < n)%nat -> 0 <= delta_pair i j).
  { intros i j Hi Hj; unfold delta_pair; apply Rmult_le_pos; apply d_factor_nonneg. }

  set (K0 := (Rmax 8 ((INR C) ^ 3)) / 2).

  assert (Hdecay : forall idx1 idx2, idx1 <> idx2 -> (idx1 < n)%nat -> (idx2 < n)%nat ->
    Cnorm (Csum (fun k => phi_flat idx1 k *c Cconj (phi_flat idx2 k)) (Nat.pred M))
    <= K0 * delta_pair idx1 idx2).
  {
    intros idx1 idx2 Hneq Hlt1 Hlt2.
    assert (Ha_eq : a = (fun i => nth i (map seq1 I1) 0%nat)).
    { unfold a, vals1; reflexivity. }
    assert (Hb_eq : b = (fun j => nth j (map seq2 I2) 0%nat)).
    { unfold b, vals2; reflexivity. }
    assert (Hgamma_eq : gamma = (fun i j => sqrt (INR (Nat.min (a i) (b j)) / (INR (a i) * INR (b j))))).
    { unfold gamma; reflexivity. }
    assert (Hphi2D_norm_eq : phi2D_norm = (fun i j k => Cof_real (/ gamma i j) *c (psi (a i) k *c psi (b j) k))).
    { unfold phi2D_norm; reflexivity. }
    assert (Hphi_flat_eq : phi_flat = (fun idx k => phi2D_norm ((idx / n2)%nat) ((idx mod n2)%nat) k)).
    { unfold phi_flat; reflexivity. }
    assert (Hdelta_pair_eq : delta_pair = (fun idx1 idx2 => d_factor r ((idx1 / n2)%nat) ((idx2 / n2)%nat) * d_factor r ((idx1 mod n2)%nat) ((idx2 mod n2)%nat))).
    { unfold delta_pair, d1; reflexivity. }
    assert (HmaxIdx1_eq : maxIdx1 = fold_right Nat.max 0%nat I1).
    { unfold maxIdx1; reflexivity. }
    assert (HmaxIdx2_eq : maxIdx2 = fold_right Nat.max 0%nat I2).
    { unfold maxIdx2; reflexivity. }
    assert (HM_eq : M = S (max (seq1 maxIdx1) (seq2 maxIdx2))).
    { unfold M; reflexivity. }
    assert (Hr_eq : r = sqrt (INR C)).
    { unfold r; reflexivity. }

    pose proof (phi_flat_decay_general_2d_wide C HCgt2 Hc_ge2 seq1 seq2
                  Hsparse1 Hsparse2 Hge2_1 Hge2_2
                  I1 I2 Hdup1 Hsorted1 Hdup2 Hsorted2
                  n1 n2 Hn1 Hn2 HI1 HI2
                  a b Ha_eq Hb_eq
                  gamma Hgamma_eq
                  phi2D_norm Hphi2D_norm_eq
                  maxIdx1 maxIdx2 HmaxIdx1_eq HmaxIdx2_eq
                  M HM_eq r Hr_eq
                  phi_flat Hphi_flat_eq
                  delta_pair Hdelta_pair_eq
                  idx1 idx2 Hneq Hlt1 Hlt2
                  (H_index_bound idx1 idx2 Hlt1 Hlt2)) as Hbound.
    unfold K0; exact Hbound.
  }

  set (M_bound' := K0 * ((1 + 4 * K_C) * (1 + 4 * K_C) - 1)).

  assert (Hc_ge2_R : INR C >= 2) by (apply Rle_ge; change 2 with (INR 2); apply le_INR; exact Hc_ge2).

  assert (Hrow_sum_U : forall idx : nat, (idx < n)%nat ->
    sum_f_R0 (fun jdx : nat => if eq_nat_dec idx jdx then 0 else delta_pair idx jdx) (Nat.pred n)
    <= (1 + 4 * K_C) * (1 + 4 * K_C) - 1).
  {
    intros idx Hlt.
    set (i0 := (idx / n2)%nat); set (j0 := (idx mod n2)%nat).
    assert (Hi0 : (i0 < n1)%nat) by (apply Nat.Div0.div_lt_upper_bound; lia).
    assert (Hj0 : (j0 < n2)%nat) by (apply Nat.mod_upper_bound; lia).
    set (S1 := sum_f_R0 (fun i' => if eq_nat_dec i0 i' then 0 else d1 i0 i') (Nat.pred n1)).
    set (S2 := sum_f_R0 (fun j' => if eq_nat_dec j0 j' then 0 else d1 j0 j') (Nat.pred n2)).
    assert (HS1 : S1 <= 4 * K_C).
    { unfold S1, d1, r, K_C. apply (d_factor_row_sum_le_4K C HCgt2 n1 i0 Hi0). }
    assert (HS2 : S2 <= 4 * K_C).
    { unfold S2, d1, r, K_C. apply (d_factor_row_sum_le_4K C HCgt2 n2 j0 Hj0). }
    assert (HS1_nonneg : 0 <= S1) by (unfold S1; apply sum_f_R0_nonneg; intros i'; destruct (eq_nat_dec i0 i'); [apply Rle_refl | unfold d1; apply d_factor_nonneg]).
    assert (HS2_nonneg : 0 <= S2) by (unfold S2; apply sum_f_R0_nonneg; intros j'; destruct (eq_nat_dec j0 j'); [apply Rle_refl | unfold d1; apply d_factor_nonneg]).
    assert (Hrow_decomp : sum_f_R0 (fun jdx : nat => if eq_nat_dec idx jdx then 0
      else delta_pair idx jdx) (Nat.pred n) = (1 + S1) * (1 + S2) - 1).
    {
      subst n; unfold delta_pair, d1, S1, S2.
      replace (idx / n2)%nat with i0 by (unfold i0; reflexivity).
      replace (idx mod n2)%nat with j0 by (unfold j0; reflexivity).
      assert (Hidx_form : idx = (i0 * n2 + j0)%nat) by (unfold i0, j0; rewrite Nat.mul_comm; apply Nat.div_mod; lia).
      rewrite Hidx_form.
      apply (prod_row_sum_decomp_eq n1 n2 i0 j0 (d_factor r) Hi0 Hj0 (d_factor_diag r)).
    }
    rewrite Hrow_decomp.
    assert (Hprod_ub : (1 + S1) * (1 + S2) - 1 <= (1 + 4 * K_C) * (1 + 4 * K_C) - 1) by nra.
    exact Hprod_ub.
  }

  assert (Hrow_sum : forall idx : nat, (idx < n)%nat ->
    sum_f_R0 (fun jdx : nat => if eq_nat_dec idx jdx then 0
      else delta_pair idx jdx) (Nat.pred n) <= M_bound').
  {
    intros idx Hlt.
    apply Rle_trans with ((1 + 4 * K_C) * (1 + 4 * K_C) - 1).
    - apply Hrow_sum_U; auto.
    - assert (H_K0_ge1 : 1 <= K0).
      {
        unfold K0.
        assert (H_cube_ge_8 : (INR C)^3 >= 8).
        {
          apply Rle_ge. transitivity (2^3).
          - assert (H23 : 2^3 = 8) by (unfold pow; simpl; ring). rewrite H23; lra.
          - apply pow_incr with (x := 2) (y := INR C) (n := 3%nat);
              split; [lra | apply Rge_le; exact Hc_ge2_R].
        }
        assert (Hmax_eq : Rmax 8 ((INR C)^3) = (INR C)^3) by (apply Rmax_right; apply Rge_le; exact H_cube_ge_8).
        rewrite Hmax_eq; lra.
      }
      assert (H_nonneg : 0 <= (1 + 4 * K_C) * (1 + 4 * K_C) - 1) by nra.
      unfold M_bound'.
      apply Rmult_le_compat_r with (r := (1 + 4 * K_C) * (1 + 4 * K_C) - 1) in H_K0_ge1.
      -- rewrite Rmult_1_l in H_K0_ge1.
         exact H_K0_ge1.
      -- exact H_nonneg.
  }

  set (delta_pair_K0 := fun i j : nat => K0 * delta_pair i j).

  assert (Hdelta_sym_K0 : forall i j : nat, (i < n)%nat -> (j < n)%nat ->
    delta_pair_K0 i j = delta_pair_K0 j i).
  { intros i j Hi Hj; unfold delta_pair_K0; rewrite (Hdelta_sym i j Hi Hj); reflexivity. }

  assert (Hdelta_nonneg_K0 : forall i j : nat, (i < n)%nat -> (j < n)%nat ->
    0 <= delta_pair_K0 i j).
  { intros i j Hi Hj; unfold delta_pair_K0; apply Rmult_le_pos.
    - assert (H_K0_nonneg : 0 <= K0).
      { apply Rlt_le; unfold K0; apply Rdiv_lt_0_compat.
        - apply Rlt_le_trans with 8; [lra | apply Rmax_l].
        - lra. }
      exact H_K0_nonneg.
    - apply Hdelta_nonneg; auto. }

  assert (Hdecay_K0 : forall idx1 idx2, idx1 <> idx2 -> (idx1 < n)%nat -> (idx2 < n)%nat ->
    Cnorm (Csum (fun k => phi_flat idx1 k *c Cconj (phi_flat idx2 k)) (Nat.pred M))
    <= delta_pair_K0 idx1 idx2).
  { intros idx1 idx2 Hneq Hlt1 Hlt2; unfold delta_pair_K0; apply Hdecay; auto. }

  assert (Hrow_sum_K0 : forall idx : nat, (idx < n)%nat ->
    sum_f_R0 (fun jdx : nat => if eq_nat_dec idx jdx then 0
      else delta_pair_K0 idx jdx) (Nat.pred n) <= M_bound').
  {
    intros idx Hlt.
    unfold delta_pair_K0.
    assert (Hsum_mult : forall (c : R) (f : nat -> R) (m : nat),
      sum_f_R0 (fun i => c * f i) m = c * sum_f_R0 f m).
    { intros c f m; induction m; simpl; [ring | rewrite IHm; ring]. }
    assert (H_if_eq : forall jdx, (if eq_nat_dec idx jdx then 0 else K0 * delta_pair idx jdx)
      = K0 * (if eq_nat_dec idx jdx then 0 else delta_pair idx jdx)).
    { intros jdx; destruct (eq_nat_dec idx jdx); ring. }
    assert (Hgoal_eq : sum_f_R0 (fun jdx : nat => if eq_nat_dec idx jdx then 0 else K0 * delta_pair idx jdx) (Nat.pred n)
                     = sum_f_R0 (fun jdx : nat => K0 * (if eq_nat_dec idx jdx then 0 else delta_pair idx jdx)) (Nat.pred n)).
    { apply sum_f_R0_ext; intros i Hi; apply H_if_eq. }
    rewrite Hgoal_eq.
    rewrite (Hsum_mult K0 (fun jdx : nat => if eq_nat_dec idx jdx then 0 else delta_pair idx jdx) (Nat.pred n)).
    apply Rmult_le_compat_l.
    { apply Rlt_le; unfold K0; apply Rdiv_lt_0_compat.
      - apply Rlt_le_trans with 8; [lra | apply Rmax_l].
      - lra. }
    apply Hrow_sum_U; auto.
  }

  assert (HM_pos : (M > 0)%nat) by (unfold M; lia).
  pose proof (abstract_unconditional_basis n phi_flat M M_bound'
    delta_pair_K0 HM_pos Htrunc Hnorm1 Hdelta_sym_K0 Hdelta_nonneg_K0 Hdecay_K0 Hrow_sum_K0
    coeffs_flat Hlen_flat') as H_abs.

  (* 收尾：扁平 F/S 直接就是目标形式（本题以扁平系数列表陈述） *)
  assert (HM_pred_eq : Nat.pred M = (M - 1)%nat) by (unfold M; lia).
  cbv zeta in H_abs.
  destruct H_abs as [H_low H_high].
  set (F := fun k : nat => Csum (fun idx : nat => nth idx coeffs_flat C0 *c phi_flat idx k) n).
  assert (H_eq : l2_norm_sq (fun k : nat =>
      Csum (fun idx => nth idx coeffs_flat C0 *c phi_flat idx k) n) (M - 1)
      = l2_norm_sq F (Nat.pred M)).
  { unfold l2_norm_sq, F.
    rewrite <- HM_pred_eq.
    reflexivity. }
  assert (H_S_eq : sum_f_R0 (fun idx => Cnorm_sq (nth idx coeffs_flat C0)) (n - 1)
                 = sum_f_R0 (fun idx => Cnorm_sq (nth idx coeffs_flat C0)) (Nat.pred n)).
  { apply f_equal. lia. }
  assert (H_final : (1 - M_bound') *
      sum_f_R0 (fun idx => Cnorm_sq (nth idx coeffs_flat C0)) (n - 1)
      <= l2_norm_sq (fun k : nat =>
           Csum (fun idx => nth idx coeffs_flat C0 *c phi_flat idx k) n) (M - 1)
      <= (1 + M_bound') *
      sum_f_R0 (fun idx => Cnorm_sq (nth idx coeffs_flat C0)) (n - 1)).
  { rewrite H_eq, H_S_eq. unfold F. exact (conj H_low H_high). }
  cbv zeta in |- *.
  change M_bound' with (K0 * ((1 + 4 * K_C) * (1 + 4 * K_C) - 1)).
  change M_bound' with (K0 * ((1 + 4 * K_C) * (1 + 4 * K_C) - 1)) in H_final.
  exact H_final.
Qed.

(* ============ 4. M_bound_2d_wide 定义与 C=4 数值裁决 ============ *)

Definition M_bound_2d_wide (C : nat) : R :=
  (Rmax 8 ((INR C) ^ 3) / 2) *
  ((1 + 4 * K (INR C)) * (1 + 4 * K (INR C)) - 1).

Lemma K_INR4_eq_2d : K (INR 4) = 1%R.
Proof.
  unfold K.
  assert (Hsqrt : sqrt (INR 4) = 2%R).
  { replace (INR 4) with 4%R by (simpl; ring).
    replace 4%R with (2 * 2)%R by ring.
    rewrite sqrt_square; [reflexivity | lra]. }
  rewrite Hsqrt. field.
Qed.

(* 数值裁决：K0 = Rmax 8 64 / 2 = 32；(1+4·1)² − 1 = 24；M_bound = 32 × 24 = 768 *)
Lemma M_bound_2d_wide_C4_value : M_bound_2d_wide 4 = 768%R.
Proof.
  unfold M_bound_2d_wide.
  rewrite K_INR4_eq_2d.
  replace ((INR 4) ^ 3)%R with 64%R by (simpl; ring).
  assert (Hrmax : Rmax 8 64 = 64%R).
  { apply Rle_antisym.
    - apply Rmax_lub; lra.
    - apply Rmax_r. }
  rewrite Hrmax.
  field.
Qed.
