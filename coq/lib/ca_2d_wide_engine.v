(* ============================================================
   库 ca_2d_wide_engine —— 2D 宽轨（2D-wide）衰减引擎
   内容：phi_flat_decay_general_2d_wide —— 无 H_dom 的 2D 离对角衰减
   （K0 = Rmax·8C³/2，覆盖全部 idx1≠idx2 对）。
   前置：ca_2d_wide_const（常数层）。
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
Require Import ca_2d_wide_const.
(* ============ 2. 衰减引擎：phi_flat_decay_general_2d_wide ============ *)
(* 与 corrected 的 phi_flat_decay_general 结构相同，但：
   - 无 H_dom（宽轨 K0=C³/2 覆盖全部离对角对）
   - 常数 K0 = Rmax 8 C³ / 2（非 /4）
   - 内积界复用 inner_product_single_tensor_bound（Hineq 由稀疏增长给出） *)
Theorem phi_flat_decay_general_2d_wide :
  forall (C : nat) (HCgt2 : (C > 2)%nat) (HC : (C >= 2)%nat)
    (seq1 seq2 : nat -> nat)
    (Hsparse1 : forall i, (INR (seq1 (S i)) > INR C * INR (seq1 i))%R)
    (Hsparse2 : forall i, (INR (seq2 (S i)) > INR C * INR (seq2 i))%R)
    (Hge2_1 : forall i, (seq1 i >= 2)%nat) (Hge2_2 : forall i, (seq2 i >= 2)%nat)
    (I1 I2 : list nat)
    (Hdup1 : NoDup I1) (Hsorted1 : Sorted Nat.lt I1)
    (Hdup2 : NoDup I2) (Hsorted2 : Sorted Nat.lt I2)
    (n1 n2 : nat) (Hn1 : n1 = length I1) (Hn2 : n2 = length I2)
    (HI1 : I1 = seq 0 n1) (HI2 : I2 = seq 0 n2)
    (a b : nat -> nat)
    (Ha : a = fun i => nth i (map seq1 I1) 0%nat)
    (Hb : b = fun j => nth j (map seq2 I2) 0%nat)
    (gamma : nat -> nat -> R)
    (Hgamma : gamma = fun i j => sqrt (INR (Nat.min (a i) (b j)) / (INR (a i) * INR (b j))))
    (phi2D_norm : nat -> nat -> nat -> Complex)
    (Hphi2D_norm : phi2D_norm = fun i j k => Cof_real (/ gamma i j) *c (psi (a i) k *c psi (b j) k))
    (maxIdx1 maxIdx2 : nat)
    (HmaxIdx1 : maxIdx1 = fold_right Nat.max 0%nat I1)
    (HmaxIdx2 : maxIdx2 = fold_right Nat.max 0%nat I2)
    (M : nat) (HM : M = S (max (seq1 maxIdx1) (seq2 maxIdx2)))
    (r : R) (Hr : r = sqrt (INR C))
    (phi_flat : nat -> nat -> Complex)
    (Hphi_flat : phi_flat = fun idx k => phi2D_norm ((idx / n2)%nat) ((idx mod n2)%nat) k)
    (delta_pair : nat -> nat -> R)
    (Hdelta_pair : delta_pair = fun idx1 idx2 =>
        d_factor r ((idx1 / n2)%nat) ((idx2 / n2)%nat) *
        d_factor r ((idx1 mod n2)%nat) ((idx2 mod n2)%nat))
    (idx1 idx2 : nat) (Hneq : idx1 <> idx2)
    (Hlt1 : (idx1 < n1 * n2)%nat) (Hlt2 : (idx2 < n1 * n2)%nat)
    (H_index_bound : (Z.abs_nat (Z.of_nat (idx1 / n2) - Z.of_nat (idx2 / n2)) +
                      Z.abs_nat (Z.of_nat (idx1 mod n2) - Z.of_nat (idx2 mod n2)) <= 6)%nat),
  Cnorm (Csum (fun k => phi_flat idx1 k *c Cconj (phi_flat idx2 k)) (Nat.pred M))
  <= (Rmax 8 ((INR C) ^ 3) / 2) * delta_pair idx1 idx2.
Proof.
  intros; subst a b gamma phi2D_norm phi_flat delta_pair M r; simpl.
  rename Hsparse1 into Hsp1, Hsparse2 into Hsp2.
  rename Hge2_1 into Hg1, Hge2_2 into Hg2.
  rename Hn1 into Hlen1, Hn2 into Hlen2.
  rename HI1 into HI1', HI2 into HI2'.
  rename HmaxIdx1 into Hmax1, HmaxIdx2 into Hmax2.
  rename Hlt1 into Hlt1', Hlt2 into Hlt2'.
  rename Hneq into Hneq'.

  assert (Hsp1_2 : forall i, (INR (seq1 (S i)) > INR 2 * INR (seq1 i))%R). {
    intros i; specialize (Hsp1 i).
    assert (HC_ge_2_INR : INR 2 <= INR C) by (apply le_INR; exact HC).
    eapply Rle_lt_trans; [| exact Hsp1].
    apply Rmult_le_compat_r; [apply pos_INR; specialize (Hg1 i); lia | exact HC_ge_2_INR].
  }
  assert (Hsp2_2 : forall i, (INR (seq2 (S i)) > INR 2 * INR (seq2 i))%R). {
    intros i; specialize (Hsp2 i).
    assert (HC_ge_2_INR : INR 2 <= INR C) by (apply le_INR; exact HC).
    eapply Rle_lt_trans; [| exact Hsp2].
    apply Rmult_le_compat_r; [apply pos_INR; specialize (Hg2 i); lia | exact HC_ge_2_INR].
  }

  (* 解码：i1/j1/i2/j2 *)
  set (i1 := (idx1 / n2)%nat); set (j1 := (idx1 mod n2)%nat).
  set (i2 := (idx2 / n2)%nat); set (j2 := (idx2 mod n2)%nat).
  assert (Hi1 : (i1 < n1)%nat) by (apply Nat.Div0.div_lt_upper_bound; lia).
  assert (Hj1 : (j1 < n2)%nat) by (apply Nat.mod_upper_bound; lia).
  assert (Hi2 : (i2 < n1)%nat) by (apply Nat.Div0.div_lt_upper_bound; lia).
  assert (Hj2 : (j2 < n2)%nat) by (apply Nat.mod_upper_bound; lia).
  assert (Hi1_len : (i1 < length I1)%nat) by (rewrite <- Hlen1; exact Hi1).
  assert (Hi2_len : (i2 < length I1)%nat) by (rewrite <- Hlen1; exact Hi2).
  assert (Hj1_len : (j1 < length I2)%nat) by (rewrite <- Hlen2; exact Hj1).
  assert (Hj2_len : (j2 < length I2)%nat) by (rewrite <- Hlen2; exact Hj2).
  set (a1 := nth i1 (map seq1 I1) 0%nat).
  set (a2 := nth i2 (map seq1 I1) 0%nat).
  set (b1 := nth j1 (map seq2 I2) 0%nat).
  set (b2 := nth j2 (map seq2 I2) 0%nat).
  assert (Ha1_len_seq : (i1 < length (seq 0 n1))%nat) by (rewrite <- HI1'; exact Hi1_len).
  assert (Ha2_len_seq : (i2 < length (seq 0 n1))%nat) by (rewrite <- HI1'; exact Hi2_len).
  assert (Hb1_len_seq : (j1 < length (seq 0 n2))%nat) by (rewrite <- HI2'; exact Hj1_len).
  assert (Hb2_len_seq : (j2 < length (seq 0 n2))%nat) by (rewrite <- HI2'; exact Hj2_len).
  assert (Ha1 : a1 = seq1 i1).
  { unfold a1. rewrite HI1'.
    rewrite (H_nth_map nat nat seq1 (seq 0 n1) 0%nat 0%nat i1 Ha1_len_seq).
    rewrite nth_seq_general; [reflexivity | exact Hi1]. }
  assert (Ha2 : a2 = seq1 i2).
  { unfold a2. rewrite HI1'.
    rewrite (H_nth_map nat nat seq1 (seq 0 n1) 0%nat 0%nat i2 Ha2_len_seq).
    rewrite nth_seq_general; [reflexivity | exact Hi2]. }
  assert (Hb1 : b1 = seq2 j1).
  { unfold b1. rewrite HI2'.
    rewrite (H_nth_map nat nat seq2 (seq 0 n2) 0%nat 0%nat j1 Hb1_len_seq).
    rewrite nth_seq_general; [reflexivity | exact Hj1]. }
  assert (Hb2 : b2 = seq2 j2).
  { unfold b2. rewrite HI2'.
    rewrite (H_nth_map nat nat seq2 (seq 0 n2) 0%nat 0%nat j2 Hb2_len_seq).
    rewrite nth_seq_general; [reflexivity | exact Hj2]. }
  assert (Ha1_ge2 : (a1 >= 2)%nat) by (rewrite Ha1; apply Hg1).
  assert (Ha2_ge2 : (a2 >= 2)%nat) by (rewrite Ha2; apply Hg1).
  assert (Hb1_ge2 : (b1 >= 2)%nat) by (rewrite Hb1; apply Hg2).
  assert (Hb2_ge2 : (b2 >= 2)%nat) by (rewrite Hb2; apply Hg2).

  (* Hdiff：i1≠i2 ∨ j1≠j2（由 Hneq + div/mod 解码唯一性） *)
  assert (Hdiff : i1 <> i2 \/ j1 <> j2).
  { destruct (Nat.eq_dec i1 i2) as [Heq_i | Hne_i].
    - right. intro Heq_j.
      apply Hneq'.
      unfold i1, i2, j1, j2 in *.
      pose proof (Nat.div_mod_eq idx1 n2) as Hdiv1.
      pose proof (Nat.div_mod_eq idx2 n2) as Hdiv2.
      rewrite Heq_i, Heq_j in Hdiv1.
      rewrite <- Hdiv2 in Hdiv1.
      exact Hdiv1.
    - left. exact Hne_i. }

  (* 稀疏增长 → Hineq（inner_product_single_tensor_bound 前提） *)
  assert (Hineq1 : INR (max a1 a2) >= (INR C) ^ (Z.abs_nat (Z.of_nat i1 - Z.of_nat i2)) * INR (min a1 a2)).
  { destruct (Nat.eq_dec i1 i2) as [Heq_i | Hne_i].
    - (* i1 = i2：d=0，max≥min 平凡 *)
      assert (Hd0 : Z.abs_nat (Z.of_nat i1 - Z.of_nat i2) = 0%nat).
      { rewrite Heq_i. rewrite Z.sub_diag. reflexivity. }
      rewrite Hd0.
      replace ((INR C) ^ 0)%R with 1%R by (simpl; ring).
      rewrite Rmult_1_l.
      rewrite Ha1, Ha2.
      apply Rle_ge. apply le_INR.
      apply Nat.le_trans with (seq1 i1); [apply Nat.le_min_l | apply Nat.le_max_l].
    - (* i1 ≠ i2：sparse_index_growth_lower *)
      rewrite Ha1, Ha2.
      apply (sparse_index_growth_lower seq1 C HC Hsp1 Hg1 i1 i2 Hne_i). }
  assert (Hineq2 : INR (max b1 b2) >= (INR C) ^ (Z.abs_nat (Z.of_nat j1 - Z.of_nat j2)) * INR (min b1 b2)).
  { destruct (Nat.eq_dec j1 j2) as [Heq_j | Hne_j].
    - assert (Hd0 : Z.abs_nat (Z.of_nat j1 - Z.of_nat j2) = 0%nat).
      { rewrite Heq_j. rewrite Z.sub_diag. reflexivity. }
      rewrite Hd0.
      replace ((INR C) ^ 0)%R with 1%R by (simpl; ring).
      rewrite Rmult_1_l.
      rewrite Hb1, Hb2.
      apply Rle_ge. apply le_INR.
      apply Nat.le_trans with (seq2 j1); [apply Nat.le_min_l | apply Nat.le_max_l].
    - rewrite Hb1, Hb2.
      apply (sparse_index_growth_lower seq2 C HC Hsp2 Hg2 j1 j2 Hne_j). }

  (* 截断到 N0 = min 4 值 + 纯量分解 + 单张量界 + 常数收尾 *)
  set (N0 := Nat.min (Nat.min a1 a2) (Nat.min b1 b2)).
  set (g := fun x y : nat => sqrt (INR (Nat.min x y) / (INR x * INR y))).
  set (G1 := g a1 b1). set (G2 := g a2 b2).

  (* seq 单调（截断界 a1 ≤ pred M 用） *)
  assert (Hseq1_inc : forall x y, (x <= y)%nat -> (seq1 x <= seq1 y)%nat).
  { intros x y Hle; destruct (Nat.eq_dec x y) as [Heq | Hne].
    - subst; apply Nat.le_refl.
    - apply Nat.lt_le_incl. apply (seq_strict_growth_lt seq1 C x y);
        [exact HC | exact Hsp1 | exact Hg1 | lia]. }
  assert (Hseq2_inc : forall x y, (x <= y)%nat -> (seq2 x <= seq2 y)%nat).
  { intros x y Hle; destruct (Nat.eq_dec x y) as [Heq | Hne].
    - subst; apply Nat.le_refl.
    - apply Nat.lt_le_incl. apply (seq_strict_growth_lt seq2 C x y);
        [exact HC | exact Hsp2 | exact Hg2 | lia]. }
  assert (Ha1_le_M : (a1 <= max (seq1 maxIdx1) (seq2 maxIdx2))%nat).
  { assert (Ha1_eq2 : a1 = seq1 i1) by exact Ha1.
    assert (Hi1_le_max : (i1 <= maxIdx1)%nat).
    { rewrite Hmax1.
      eapply fold_right_max_ge.
      rewrite HI1'. apply in_seq. lia. }
    apply (Nat.le_trans _ (seq1 maxIdx1)).
    - rewrite Ha1_eq2. apply Hseq1_inc. exact Hi1_le_max.
    - apply Nat.le_max_l. }

  assert (Htrunc_eq :
    Csum (fun k => (Cof_real (/ g a1 b1) *c (psi a1 k *c psi b1 k)) *c
                  Cconj (Cof_real (/ g a2 b2) *c (psi a2 k *c psi b2 k)))
         (max (seq1 maxIdx1) (seq2 maxIdx2))
    = Csum (fun k => (Cof_real (/ g a1 b1) *c (psi a1 k *c psi b1 k)) *c
                    Cconj (Cof_real (/ g a2 b2) *c (psi a2 k *c psi b2 k))) N0).
  { apply (Csum_trunc_tail _ N0 (max (seq1 maxIdx1) (seq2 maxIdx2))).
    - (* N0 ≤ pred M：Nat.min 链 + a1 ≤ pred M 链，不用 lia 展开 min *)
      apply (Nat.le_trans _ a1).
      + apply min4_le_a1.
      + exact Ha1_le_M.
    - intros k [Hk1 Hk2].
      assert (Hk_ge_N0 : (k >= N0)%nat) by lia.
      assert (HN0_is : N0 = a1 \/ N0 = a2 \/ N0 = b1 \/ N0 = b2) by (unfold N0; apply min4_is_one).
      destruct HN0_is as [H|[H|[H|H]]]; rewrite H in Hk_ge_N0.
      + (* N0 = a1：psi a1 k = C0 *)
        rewrite (psi_ge_n_zero a1 k Hk_ge_N0).
        rewrite C0_mul_eq_C0. rewrite C0_mul_eq_C0_r. rewrite C0_mul_eq_C0. reflexivity.
      + (* N0 = a2：psi a2 k = C0 *)
        rewrite (psi_ge_n_zero a2 k Hk_ge_N0).
        rewrite C0_mul_eq_C0. rewrite C0_mul_eq_C0_r. rewrite Cconj_0. rewrite C0_mul_eq_C0_r. reflexivity.
      + (* N0 = b1：psi b1 k = C0 *)
        rewrite (psi_ge_n_zero b1 k Hk_ge_N0).
        rewrite C0_mul_eq_C0_r. rewrite C0_mul_eq_C0_r. rewrite C0_mul_eq_C0. reflexivity.
      + (* N0 = b2：psi b2 k = C0 *)
        rewrite (psi_ge_n_zero b2 k Hk_ge_N0).
        rewrite C0_mul_eq_C0_r. rewrite C0_mul_eq_C0_r. rewrite Cconj_0. rewrite C0_mul_eq_C0_r. reflexivity. }
  unfold g in Htrunc_eq.
  rewrite Htrunc_eq.
  assert (Hdec : Csum (fun k => (Cof_real (/ sqrt (INR (Nat.min a1 b1) / (INR a1 * INR b1))) *c (psi a1 k *c psi b1 k)) *c
                               Cconj (Cof_real (/ sqrt (INR (Nat.min a2 b2) / (INR a2 * INR b2))) *c (psi a2 k *c psi b2 k))) N0
               = Cof_real (/ sqrt (INR (Nat.min a1 b1) / (INR a1 * INR b1)) * / sqrt (INR (Nat.min a2 b2) / (INR a2 * INR b2))) *c
                 Csum (fun k => (psi a1 k *c Cconj (psi a2 k)) *c (psi b1 k *c Cconj (psi b2 k))) N0).
  { apply (phi2D_inner_scalar_decomposition a1 b1 a2 b2 g); unfold g; reflexivity. }
  rewrite Hdec.
  fold G1 G2.

  (* 单张量界（E064：合并环境 eq_refl 位置参数 elaboration 不稳——先 assert by reflexivity 再传） *)
  assert (Hr_sqrt : sqrt (INR C) = sqrt (INR C)) by reflexivity.
  pose proof (inner_product_single_tensor_bound C (sqrt (INR C)) Hr_sqrt
                i1 i2 j1 j2 a1 a2 b1 b2
                (Z.abs_nat (Z.of_nat i1 - Z.of_nat i2))
                (Z.abs_nat (Z.of_nat j1 - Z.of_nat j2))
                HC Ha1_ge2 Ha2_ge2 Hb1_ge2 Hb2_ge2 Hineq1 Hineq2) as Hinner.
  cbv beta zeta in Hinner.
  simpl in Hinner.
  assert (Hinner_bound :
    Cnorm (Csum (fun k : nat =>
      (psi a1 k *c Cconj (psi a2 k)) *c (psi b1 k *c Cconj (psi b2 k))) N0)
    <= G1 * G2).
  { unfold G1, G2, g in Hinner |- *. exact Hinner. }

  assert (HG1_pos : 0 < G1) by (unfold G1, g; apply sqrt_lt_R0_c; apply Rmult_lt_0_compat;
    [apply lt_0_INR; lia | apply Rinv_0_lt_compat; apply Rmult_lt_0_compat; apply lt_0_INR; lia]).
  assert (HG2_pos : 0 < G2) by (unfold G2, g; apply sqrt_lt_R0_c; apply Rmult_lt_0_compat;
    [apply lt_0_INR; lia | apply Rinv_0_lt_compat; apply Rmult_lt_0_compat; apply lt_0_INR; lia]).
  assert (Hsc_nonneg : 0 <= / G1 * / G2)
    by (apply Rlt_le; apply Rmult_lt_0_compat;
        [apply Rinv_0_lt_compat; exact HG1_pos | apply Rinv_0_lt_compat; exact HG2_pos]).

  rewrite Cnorm_mult.
  rewrite (Cnorm_Cof_real_pos
    (/ sqrt (INR (Nat.min a1 b1) / (INR a1 * INR b1)) *
     / sqrt (INR (Nat.min a2 b2) / (INR a2 * INR b2)))) by
      (unfold G1, G2, g in Hsc_nonneg; exact Hsc_nonneg).
  assert (Hinner2 : / G1 * / G2 * Cnorm (Csum (fun k =>
      (psi a1 k *c Cconj (psi a2 k)) *c (psi b1 k *c Cconj (psi b2 k))) N0) <= 1).
  { apply Rle_trans with (/ G1 * / G2 * (G1 * G2)).
    - apply Rmult_le_compat_l; [exact Hsc_nonneg | exact Hinner_bound].
    - replace (/ G1 * / G2 * (G1 * G2)) with 1.
      + apply Rle_refl.
      + field. split; apply Rgt_not_eq; assumption. }
  eapply Rle_trans; [exact Hinner2 |].

  (* 常数引理收尾：1 <= (Rmax 8 C³/2) · d_i · d_j *)
  assert (Hlt1b : (idx1 < n1 * n2)%nat) by exact Hlt1'.
  assert (Hlt2b : (idx2 < n1 * n2)%nat) by exact Hlt2'.
  pose proof (one_le_half_K0_2dprod C HCgt2 (sqrt (INR C)) Hr_sqrt
                i1 i2 j1 j2 Hdiff H_index_bound) as Hconst.
  eapply Rle_trans; [exact Hconst |].
  unfold G1, G2, g.
  replace (INR C * (INR C * (INR C * 1))) with ((INR C) ^ 3) by (simpl; ring).
  apply Rle_refl.
Qed.
