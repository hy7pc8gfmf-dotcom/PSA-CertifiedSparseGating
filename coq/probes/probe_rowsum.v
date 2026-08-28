(* ============================================================
   定理：C-稀疏梯子（逐对比率 ≥ C ≥ 2）的任意行
     Σ_{j≠i} |⟨ψ_{v_i}, ψ_{v_j}⟩| ≤ 2π·q/(1−q)，q = C^{−3/2} < 1/2
   ——C=4 时 ≤ 2π/7 ≈ 0.898 < 1：**1D 无条件基定理在 C=4 从
   空洞（2K(4)=2 > 1，仅存在性）变为真实框架界**。
   证明：PB4 逐对界 + sin ≤ x（sin_bound n=0 上界）+ Jordan 分母
   ⟹ 逐对 ≤ π·(a√a)/(b√b) ≤ π·C^{−3d/2}（d=索引距离，链式比率累积）
   ⟹ 两侧几何级数求和。

   RS0 lsum 求和 + lsum_le + geo_exact/geo_bound（几何级数闭式）。
   RS1 sin_le_x：0 ≤ x ≤ π/2 ⟹ sin x ≤ x（sin_bound 交替级数）。
   RS2 pair_le_crude：PB4 + RS1 + b ≥ 2a ⟹ 逐对 ≤ π·(a√a)/(b√b)。
   RS3 chain_pow：v(i+k) ≥ C^k·v i（nat 归纳）。
   RS4 oneside：单侧行和 ≤ πq/(1−q)（归纳 + 几何级数）。
   RS5 row_sum_3halfs（主定理）：两侧 ⟹ ≤ 2πq/(1−q)。
   审计：Print Assumptions 尾部。
   ============================================================ *)
From mathcomp Require Import ssreflect ssrbool ssrnat seq eqtype div prime.
Require Import Stdlib.Reals.Reals.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.micromega.Lra.
Require Import Stdlib.ZArith.ZArith.
Require Import ca_base.
Require Import ca_complex_foundation.
Require Import ca_basis.
Require Import ca_independence.
Require Import ca_fourier.
Require Import ca_char_ortho.
Require Import ca_zeta_scaffold.
Require Import probe_grid_ortho.
Require Import probe_partial.
Require Import probe_pairbound.
Import ComplexNumbers.
Import FourierAnalysis.
Import GridOrtho.
Import TPartial.
Import PairBound.

Open Scope R_scope.
Open Scope complex_scope.
Open Scope nat_scope.

Module RowSum.

(* ---------- RS0：求和与几何级数 ---------- *)

Fixpoint lsum (f : nat -> R) (m : nat) : R :=
  match m with
  | O => 0%R
  | S m' => (lsum f m' + f m')%R
  end.

Lemma lsum_le (f g : nat -> R) (m : nat) :
  (forall k, (k < m)%nat -> (f k <= g k)%R) -> (lsum f m <= lsum g m)%R.
Proof.
  intros H. induction m as [| m IH]; simpl.
  - apply Rle_refl.
  - apply Rplus_le_compat; [apply IH; intros k Hk; apply H; exact (ltn_trans Hk (ltnSn m)) | apply H; exact (ltnSn m)].
Qed.

Lemma pow_S (x : R) (n : nat) : (x ^ (S n))%R = (x * x ^ n)%R.
Proof. intros. simpl. ring. Qed.

Lemma pow_nonneg (x : R) (n : nat) : (0 <= x)%R -> (0 <= x ^ n)%R.
Proof.
  intros Hx. induction n as [| n IH].
  - simpl. lra.
  - rewrite pow_S. apply Rmult_le_pos; [ lra | exact IH ].
Qed.

Lemma geo_exact (x : R) (m : nat) :
  ((1 - x) * lsum (fun k => x ^ (S k)) m = x * (1 - x ^ m))%R.
Proof.
  induction m as [| m IH]; cbn [lsum].
  - ring.
  - replace ((1 - x) * (lsum (fun k => x ^ S k) m + x ^ S m))%R
      with ((1 - x) * lsum (fun k => x ^ S k) m + (1 - x) * x ^ S m)%R
      by ring.
    rewrite IH.
    rewrite !pow_S.
    ring.
Qed.

Lemma geo_bound (x : R) (m : nat) :
  (0 < x < 1)%R -> (lsum (fun k => x ^ (S k)) m <= x / (1 - x))%R.
Proof.
  intros [Hx1 Hx2].
  assert (Hpos : (0 < 1 - x)%R) by lra.
  apply (Rmult_le_reg_r (1 - x) _ _ Hpos).
  replace (lsum (fun k => x ^ S k) m * (1 - x))%R with ((1 - x) * lsum (fun k => x ^ S k) m)%R by ring.
  rewrite geo_exact.
  replace (x / (1 - x) * (1 - x))%R with x%R by (field; lra).
  replace (x * (1 - x ^ m))%R with (x - x * x ^ m)%R by ring.
  assert (Hple : (x ^ m <= 1)%R).
  { induction m as [| m IHm].
    - simpl. apply Rle_refl.
    - rewrite pow_S.
      apply (Rle_trans _ (x * 1)%R).
      + apply Rmult_le_compat_l; [apply Rlt_le; lra | exact IHm].
      + rewrite Rmult_1_r. lra. }
  assert (Hnn : (0 <= x ^ m)%R) by (apply pow_nonneg; lra).
  assert (Hxt : (0 <= x * x ^ m)%R) by (apply Rmult_le_pos; [ lra | exact Hnn ]).
  lra.
Qed.

(* ---------- RS1：sin x ≤ x on [0, π/2] ---------- *)

Lemma sin_le_x (x : R) : (0 <= x <= PI / 2)%R -> (sin x <= x)%R.
Proof.
  intros [H1 H2].
  assert (Hx2 : (x <= 7 / 4)%R).
  { apply (Rle_trans _ (PI / 2)); [ exact H2 | ].
    replace (PI / 2)%R with PI2 by (unfold PI; field).
    apply (proj2 pi2_int). }
  assert (HPI : (7 / 4 <= PI)%R).
  { unfold PI. apply (Rle_trans _ (2 * (7 / 8))).
    - lra.
    - apply Rmult_le_compat_l; [ lra | apply (proj1 pi2_int) ]. }
  assert (Hsq : (x * x <= 20)%R).
  { apply (Rle_trans _ ((7 / 4) * (7 / 4))).
    - apply Rmult_le_compat; [ lra | lra | exact Hx2 | exact Hx2 ].
    - lra. }
  assert (Hxp : (x <= PI)%R) by lra.
  assert (Hb := sin_bound x 0%nat H1 Hxp).
  apply (Rle_trans _ (sin_approx x 2)); [ exact (proj2 Hb) | ].
  replace (sin_approx x 2)%R
    with (x + (x * x * x * (x * x)) / 120 - (x * x * x) / 6)%R
    by (unfold sin_approx, sin_term; simpl; field; lra).
  assert (Hc : (0 <= x * x * x)%R)
    by (apply (Rmult_le_pos (x * x) x); [ apply (Rmult_le_pos x x); lra | lra ]).
  assert (Hkey : (x * x * x * (x * x) <= x * x * x * 20)%R)
    by (apply Rmult_le_compat_l; [ exact Hc | exact Hsq ]).
  nra.
Qed.

(* ---------- RS2：逐对 crude 界 π·(a√a)/(b√b) ---------- *)

Definition Fpair (a b : nat) : R :=
  Cnorm (PrimeEmbedding.Csum
           (fun k => rot_atom ((2 * PI * (INR b - INR a) / (INR a * INR b))%R) k) a)
  / sqrt (INR a * INR b).

Lemma pair_le_crude (a b : nat) :
  (2 <= a)%nat -> (2 * a <= b)%nat ->
  (Fpair a b <= PI * (INR a * sqrt (INR a)) / (INR b * sqrt (INR b)))%R.
Proof.
  intros Ha Hb.
  assert (Hab : (a < b)%nat).
  { apply/ltP. apply (Nat.lt_le_trans _ (2 * a) _).
    - apply/ltP. rewrite -[a in a < _]mul1n. rewrite (@ltn_pmul2r a 1 2 (ltnW Ha)). exact (ltn0Sn 1).
    - apply/leP. exact Hb. }
  pose proof (pair_inner_norm a b Ha Hab) as H.
  assert (HA : (0 < INR a)%R).
  { apply lt_0_INR. case: (@ltP 0 a) => [Hp | Hn].
    - exact Hp.
    - exfalso. apply Hn. move: (ltnW Ha) => /ltP. exact. }
  assert (HB : (0 < INR b)%R).
  { apply lt_0_INR. case: (@ltP 0 b) => [Hp | Hn].
    - exact Hp.
    - exfalso. apply Hn. move: (ltnW (ltn_trans Ha Hab)) => /ltP. exact. }
  assert (HIs : (INR (b - a) = INR b - INR a)%R).
  { assert (Hs : (INR (b - a) + INR a = INR b)%R)
      by (rewrite <- plus_INR; f_equal; exact (subnK (ltnW Hab))).
    lra. }
  assert (Hba : (0 < INR (b - a))%R) by (apply lt_0_INR; apply/ltP; rewrite subn_gt0; exact Hab).
  assert (Hsin : (sin (PI * INR a / INR b) <= PI * INR a / INR b)%R).
  { apply sin_le_x. split.
    - unfold Rdiv. apply Rmult_le_pos.
      + apply Rmult_le_pos; [apply Rlt_le; apply PI_RGT_0 | apply Rlt_le; exact HA].
      + apply Rlt_le; apply Rinv_0_lt_compat; exact HB.
    - replace (PI * INR a / INR b)%R with (PI * (INR a / INR b))%R by (field; lra).
      apply Rmult_le_compat_l; [apply Rlt_le; apply PI_RGT_0 | ].
      apply (Rle_trans _ (1 / 2)); [ | lra ].
      apply (Rmult_le_reg_r (2 * INR b)); [ nra | ].
      replace (INR a / INR b * (2 * INR b))%R with (2 * INR a)%R by (field; lra).
      replace ((2 * INR a))%R with (INR (2 * a))%R by (rewrite mult_INR; simpl; ring).
      apply (Rle_trans _ (INR b)); [apply le_INR; apply/leP; exact Hb | ].
      replace ((1 / 2 * (2 * INR b)))%R with (INR b)%R by (field; lra).
      apply Rle_refl. }
  unfold Fpair.
  apply (Rle_trans _
      ((PI * INR a / INR b) * sqrt (INR a * INR b) / (2 * (INR b - INR a)))).
  - apply (Rle_trans _
      (sin (PI * INR a / INR b) * sqrt (INR a * INR b) / (2 * (INR b - INR a)))).
    + exact H.
    + unfold Rdiv.
      assert (HK : (sin (PI * INR a / INR b) * sqrt (INR a * INR b)
                     * / (2 * (INR b - INR a))
                     <= (PI * INR a / INR b) * sqrt (INR a * INR b)
                        * / (2 * (INR b - INR a)))%R).
      { apply (Rmult_le_compat_r (/ (2 * (INR b - INR a))%R)
                (sin (PI * INR a / INR b) * sqrt (INR a * INR b))
                ((PI * INR a / INR b) * sqrt (INR a * INR b))).
        - apply Rlt_le. apply Rinv_0_lt_compat. rewrite <- HIs.
          apply Rmult_lt_0_compat; [ lra | exact Hba ].
        - apply (Rmult_le_compat_r (sqrt (INR a * INR b))).
          + apply sqrt_pos'.
            apply Rmult_le_pos; [ apply Rlt_le; exact HA | apply Rlt_le; exact HB ].
          + exact Hsin. }
      lra.
  - apply (Rle_trans _ ((PI * INR a / INR b) * sqrt (INR a * INR b) / (INR b))).
    + assert (HAge : (0 <= (PI * INR a / INR b) * sqrt (INR a * INR b))%R).
      { apply Rmult_le_pos.
        - unfold Rdiv. apply Rmult_le_pos.
          + apply Rmult_le_pos.
            * apply Rlt_le; apply PI_RGT_0.
            * apply Rlt_le; exact HA.
          + apply Rlt_le; apply Rinv_0_lt_compat; exact HB.
        - apply sqrt_pos'. apply Rmult_le_pos; [ apply Rlt_le; exact HA | apply Rlt_le; exact HB ]. }
      apply (Rmult_le_reg_r ((2 * (INR b - INR a)) * INR b)).
      * rewrite <- HIs. nra.
      * replace ((PI * INR a / INR b * sqrt (INR a * INR b) / (2 * (INR b - INR a)))
                  * ((2 * (INR b - INR a)) * INR b))%R
          with ((PI * INR a / INR b * sqrt (INR a * INR b)) * INR b)%R
          by (field; nra).
        replace ((PI * INR a / INR b * sqrt (INR a * INR b) / (INR b))
                  * ((2 * (INR b - INR a)) * INR b))%R
          with ((PI * INR a / INR b * sqrt (INR a * INR b)) * (2 * (INR b - INR a)))%R
          by (field; nra).
        assert (H2D : (INR b <= 2 * INR (b - a))%R).
        { assert (HbR : (2 * INR a <= INR b)%R).
          { replace (2 * INR a)%R with (INR (2 * a))%R by (rewrite mult_INR; reflexivity).
            apply le_INR. case: (@leP (2 * a) b) => [Hbp | Hnot].
            - exact Hbp.
            - exfalso. apply Hnot. apply/leP. exact Hb. }
          rewrite HIs. nra. }
        apply Rmult_le_compat_l; [ exact HAge | rewrite <- HIs; exact H2D ].
    + rewrite (sqrt_mult (INR a) (INR b) (Rlt_le _ _ HA) (Rlt_le _ _ HB)).
      assert (Hsa : (sqrt (INR a) * sqrt (INR a) = INR a)%R)
        by (apply sqrt_sqrt; apply Rlt_le; exact HA).
      assert (Hsb : (sqrt (INR b) * sqrt (INR b) = INR b)%R)
        by (apply sqrt_sqrt; apply Rlt_le; exact HB).
      assert (Hpb : (0 < sqrt (INR b))%R).
        { apply sqrt_pos_strict. exact HB. }
      apply Req_le.
      apply (Rmult_eq_reg_r (INR b * INR b * sqrt (INR b))).
      * unfold Rdiv in *.
        replace (PI * INR a * Rinv (INR b) * (sqrt (INR a) * sqrt (INR b))
                 * Rinv (INR b) * (INR b * INR b * sqrt (INR b)))%R
          with ((PI * INR a * sqrt (INR a) * (sqrt (INR b) * sqrt (INR b)))
                * (Rinv (INR b) * INR b) * (Rinv (INR b) * INR b))%R
          by ring.
        replace (PI * (INR a * sqrt (INR a)) * Rinv (INR b * sqrt (INR b))
                 * (INR b * INR b * sqrt (INR b)))%R
          with ((PI * INR a * sqrt (INR a) * INR b)
                * (Rinv (INR b * sqrt (INR b)) * (INR b * sqrt (INR b))))%R
          by ring.
        rewrite (Rmult_inv_l (INR b) ltac:(lra)).
        rewrite Rmult_1_r.
        rewrite (Rmult_inv_l (INR b * sqrt (INR b)) ltac:(nra)).
        rewrite Rmult_1_r.
        rewrite Hsb.
        ring.
      * intros H0.
        assert (HB0 : (INR b <> 0)%R) by lra.
        destruct (Rmult_integral _ _ H0) as [E | E].
        -- destruct (Rmult_integral _ _ E) as [E1 | E1]; apply HB0; exact E1.
        -- exfalso. nra.
Qed.

(* ---------- RS3：链式比率累积 ---------- *)

Lemma chain_pow (C : nat) (v : nat -> nat) (i k : nat) :
  (forall j, (v j * C <= v (S j)))%nat ->
  (v i * C ^ k <= v (i + k))%nat.
Proof.
  intros Hchain. induction k as [| k IH].
  - rewrite Nat.pow_0_r muln1 addn0. apply leqnn.
  - rewrite Nat.pow_succ_r.
    assert (Hs : (v (i + k) * C <= v (S (i + k)))%nat) by apply Hchain.
    rewrite (addnS i k) || rewrite (Nat.add_succ_r i k).
    rewrite mulnCA mulnC.
    apply (leq_trans (n := v (i + k) * C)).
    + apply (leq_mul (n1 := v (i + k)) (n2 := C)). exact IH. by apply leqnn.
    + exact Hs.
    + by apply Nat.le_0_l.
Qed.

Lemma v_incr (C : nat) (v : nat -> nat) :
  (2 <= C)%nat -> (forall j, (v j * C <= v (S j)))%nat ->
  forall j j', (j <= j')%nat -> (v j <= v j')%nat.
Proof.
  intros HC Hchain j j' Hjj'.
  assert (Hmono : forall m, (v m * C <= v (S m))%nat) by exact Hchain.
  induction j' as [| j' IH].
  - move: Hjj' => /leP Hj. assert (j = 0)%nat by lia. subst j.
    by apply leqnn.
  - destruct (Nat.eq_dec j (S j')) as [E | E].
    + rewrite E. by apply leqnn.
    + assert (H1 : (v j <= v j')%nat)
        by (apply IH; apply/leP; move: Hjj' => /leP Hj; lia).
      assert (H2 : (v j' * C <= v (S j'))%nat) by apply Hchain.
      assert (H3 : (v j' * 2 <= v j' * C)%nat)
        by (apply (leq_mul (leqnn (v j')) HC)).
      apply (leq_trans (n := v j')).
      * exact H1.
      * apply (leq_trans (n := v j' * 2)).
        - apply (leq_trans (n := v j' * 1)).
          + rewrite muln1. by apply leqnn.
          + apply (leq_mul (leqnn (v j')) (ltnW (ltnSn 1))).
        - apply (leq_trans (n := v j' * C)).
          + exact H3.
          + exact H2.
Qed.

(* ---------- RS4：几何衰减 ---------- *)

Definition qval (C : nat) : R :=
  (/ sqrt (INR C)) * (/ sqrt (INR C)) * (/ sqrt (INR C)).

Lemma sqrt_posnat (n : nat) : (1 <= n)%nat -> (0 < sqrt (INR n))%R.
Proof. intros Hn. apply sqrt_pos_strict. apply lt_0_INR. move: Hn => /leP Hn. lia. Qed.

Lemma pow_ge1 (C : nat) : (1 <= C)%nat -> forall m, (1 <= C ^ m)%nat.
Proof.
  intros H m. induction m as [| m IH]; simpl.
  - by apply leqnn.
  - apply (leq_trans (n := C)).
    + exact H.
    + rewrite -[C in C <= _]muln1. apply (leq_mul (leqnn C) IH).
Qed.

Lemma q_eq (C : nat) : (2 <= C)%nat ->
  (qval C * (INR C * sqrt (INR C)) = 1)%R.
Proof.
  intros HC.
  assert (Hsp : (0 < sqrt (INR C))%R) by (move: HC => /leP HCp; apply sqrt_posnat; apply/leP; lia).
  assert (Hss : (sqrt (INR C) * sqrt (INR C) = INR C)%R)
    by (apply sqrt_sqrt; apply Rlt_le; move: HC => /leP HCp; apply lt_0_INR; lia).
  assert (Hne : (sqrt (INR C) <> 0)%R) by lra.
  unfold qval.
  replace (INR C * sqrt (INR C))%R
    with (sqrt (INR C) * (sqrt (INR C) * sqrt (INR C)))%R
    by (transitivity (sqrt (INR C) * sqrt (INR C) * sqrt (INR C))%R;
        [ring | rewrite Hss; reflexivity]).
  field; (exact Hne || nra || assumption).
Qed.

Lemma q_pow (C : nat) : (2 <= C)%nat -> forall k : nat,
  (qval C ^ (S k) * (INR (C ^ (S k)) * sqrt (INR (C ^ (S k)))) = 1)%R.
Proof.
  intros HC. induction k as [| k IH].
  - assert (Hq1 : (qval C ^ 1 = qval C)%R) by (simpl; ring).
    rewrite Hq1 Nat.pow_1_r. exact (q_eq C HC).
  - assert (HC1 : (1 <= C)%nat) by exact (ltnW HC).
    pose proof (pow_ge1 C HC1 (S k)) as Hpp.
    rewrite pow_S Nat.pow_succ_r.
    rewrite (mult_INR C (C ^ (S k))).
    rewrite (sqrt_mult (INR C) (INR (C ^ (S k)))
              (pos_INR C) (pos_INR (C ^ (S k)))).
    rewrite <- (q_eq C HC).
    transitivity ((qval C ^ (S k) * (INR (C ^ (S k)) * sqrt (INR (C ^ (S k)))))
                  * (qval C * (INR C * sqrt (INR C))))%R.
    + ring.
    + rewrite IH (q_eq C HC). ring.
    + lia.
Qed.

Lemma q_inv (C : nat) : (2 <= C)%nat -> forall k : nat,
  (qval C ^ (S k) = / (INR (C ^ (S k)) * sqrt (INR (C ^ (S k)))))%R.
Proof.
  intros HC k.
  pose proof (q_pow C HC k) as HQ.
  assert (H1 : (1 <= C ^ (S k))%nat) by (apply pow_ge1; exact (ltnW HC)).
  assert (H2 : (0 < INR (C ^ (S k)))%R)
    by (apply lt_0_INR; move: H1 => /ltP H1p; exact H1p).
  assert (H3 : (0 < sqrt (INR (C ^ (S k))))%R)
    by (apply sqrt_posnat; apply pow_ge1; exact (ltnW HC)).
  apply (Rmult_eq_reg_r (INR (C ^ (S k)) * sqrt (INR (C ^ (S k))))).
  - rewrite HQ.
    replace ((/ (INR (C ^ (S k)) * sqrt (INR (C ^ (S k))))
               * (INR (C ^ (S k)) * sqrt (INR (C ^ (S k)))))%R) with 1%R
      by (field; split; lra).
    reflexivity.
  - intro H0.
    assert (H4 : (0 < INR (C ^ (S k)) * sqrt (INR (C ^ (S k))))%R) by nra.
    lra.
Qed.

Lemma q_range (C : nat) : (2 <= C)%nat -> (0 < qval C < 1)%R.
Proof.
  intros HC. split.
  - unfold qval.
    assert (Hi : (0 < / sqrt (INR C))%R)
      by (apply Rinv_0_lt_compat; apply sqrt_posnat; exact (ltnW HC)).
    apply (Rmult_lt_0_compat (/ sqrt (INR C) * / sqrt (INR C)) (/ sqrt (INR C)));
      [ | exact Hi ].
    apply (Rmult_lt_0_compat (/ sqrt (INR C)) (/ sqrt (INR C))); exact Hi.
  - assert (H1p : (qval C ^ 1 = qval C)%R) by (simpl; ring).
    rewrite <- H1p. rewrite (q_inv C HC 0%nat) Nat.pow_1_r.
    assert (Hsp : (0 < sqrt (INR C))%R) by (apply sqrt_posnat; exact (ltnW HC)).
    assert (Hs : (1 <= sqrt (INR C))%R).
    { destruct (Rlt_or_le (sqrt (INR C)) 1) as [Hlt | Hle]; [ | exact Hle ].
      exfalso.
      assert (Hsq : (sqrt (INR C) * sqrt (INR C) < sqrt (INR C) * 1)%R)
        by (apply Rmult_lt_compat_l; lra).
      rewrite Rmult_1_r in Hsq.
      assert (Hss : (sqrt (INR C) * sqrt (INR C) = INR C)%R)
        by (apply sqrt_sqrt; apply Rlt_le; apply lt_0_INR; move: HC => /leP HCp; lia).
      rewrite Hss in Hsq.
      move: HC => /leP HCp.
      assert (H2 : (INR 1 <= INR C)%R) by (apply le_INR; lia).
      simpl in H2. lra. }
    assert (Ha : (INR 2 <= INR C)%R) by (apply le_INR; move: HC => /leP HCp; lia).
    assert (H4 : (INR 2 * 1 <= INR C * sqrt (INR C))%R)
      by (apply Rmult_le_compat;
          [ apply Rlt_le, lt_0_INR; move: HC => /leP HCp; lia | lra | exact Ha | lra ]).
    rewrite Rmult_1_r in H4.
    simpl in H4.
    assert (HX : (1 < INR C * sqrt (INR C))%R) by lra.
    unfold Rdiv.
    apply (Rmult_lt_reg_r (INR C * sqrt (INR C))).
    + nra.
    + assert (Hnz : (INR C * sqrt (INR C) <> 0)%R) by nra.
      rewrite (Rmult_inv_l (INR C * sqrt (INR C)) Hnz).
      rewrite Rmult_1_l.
      exact HX.
Qed.

Lemma pair_decay (C : nat) (v : nat -> nat) (i k : nat) :
  (2 <= C)%nat -> (2 <= v i)%nat ->
  (forall j, (v j * C <= v (S j)))%nat ->
  (Fpair (v i) (v ((i + S k)%nat)) <= PI * qval C ^ (S k))%R.
Proof.
  intros HC Hvi Hchain.
  assert (Hab2 : (2 * v i <= v ((i + S k)%nat))%nat).
  { assert (H1 : (v i * C <= v (S i))%nat) by apply Hchain.
    assert (H2 : (v i * 2 <= v i * C)%nat)
      by (apply (leq_mul (leqnn (v i)) HC)).
    assert (H3 : (v (S i) <= v ((i + S k)%nat))%nat)
      by (apply (v_incr C v HC Hchain); rewrite addnS || rewrite Nat.add_succ_r; rewrite ltnS; apply leq_addr).
    apply (leq_trans (n := v i * C)).
    - rewrite mulnC. exact H2.
    - apply (leq_trans (n := v (S i))).
      + exact H1.
      + exact H3. }
  apply (Rle_trans _
           (PI * (INR (v i) * sqrt (INR (v i)))
              / (INR (v ((i + S k)%nat)) * sqrt (INR (v ((i + S k)%nat)))))).
  - apply pair_le_crude; [ exact Hvi | exact Hab2 ].
  - assert (Hpp : (1 <= C ^ (S k))%nat) by (apply pow_ge1; exact (ltnW HC)).
    assert (HIC : (0 < INR (C ^ (S k)))%R)
      by (apply lt_0_INR; move: Hpp => /ltP Hppp; exact Hppp).
    assert (HISC : (0 < sqrt (INR (C ^ (S k))))%R) by (apply sqrt_posnat; exact Hpp).
    assert (Hia : (0 < INR (v i))%R)
      by (apply lt_0_INR; move: Hvi => /ltP Hvp; lia).
    assert (Hib : (0 < INR (v ((i + S k)%nat)))%R).
    { apply (Rlt_le_trans _ (INR (v i)) _); [ exact Hia | ].
      apply le_INR. apply/leP.
      apply (v_incr C v HC Hchain). rewrite addnS || rewrite Nat.add_succ_r.
      apply (leq_trans (n := i + k)).
      - apply leq_addr.
      - by apply leqnSn. }
    assert (Hsa : (0 < sqrt (INR (v i)))%R) by (apply sqrt_posnat; exact (ltnW Hvi)).
    assert (Hsb : (0 < sqrt (INR (v ((i + S k)%nat))))%R).
    { apply sqrt_posnat.
      apply (leq_trans (n := 2 * v i)).
      - apply (leq_trans (n := 2)).
        + exact (ltnW (ltnSn 1)).
        + exact (leq_mul (leqnn 2) (ltnW Hvi)).
      - exact Hab2. }
    rewrite (q_inv C HC k).
    unfold Rdiv.
    replace ((PI * (INR (v i) * sqrt (INR (v i))))
             * Rinv (INR (v ((i + S k)%nat)) * sqrt (INR (v ((i + S k)%nat)))))%R
      with (PI * ((INR (v i) * sqrt (INR (v i)))
                  * Rinv (INR (v ((i + S k)%nat)) * sqrt (INR (v ((i + S k)%nat))))))%R
      by ring.
    apply Rmult_le_compat_l; [ apply Rlt_le, PI_RGT_0 | ].
    apply (Rmult_le_reg_r (INR (C ^ (S k)) * sqrt (INR (C ^ (S k))))).
    + apply Rmult_lt_0_compat; [ exact HIC | exact HISC ].
    + assert (HnzD : (INR (C ^ (S k)) * sqrt (INR (C ^ (S k))) <> 0)%R) by nra.
      rewrite (Rmult_inv_l (INR (C ^ (S k)) * sqrt (INR (C ^ (S k)))) HnzD).
      apply (Rmult_le_reg_r (INR (v ((i + S k)%nat)) * sqrt (INR (v ((i + S k)%nat))))).
      * apply Rmult_lt_0_compat; [ exact Hib | exact Hsb ].
      * replace ((INR (v i) * sqrt (INR (v i)) * Rinv (INR (v ((i + S k)%nat)) * sqrt (INR (v ((i + S k)%nat))))
                 * (INR (C ^ (S k)) * sqrt (INR (C ^ (S k)))))
                * (INR (v ((i + S k)%nat)) * sqrt (INR (v ((i + S k)%nat)))))%R
          with ((INR (v i) * sqrt (INR (v i))) * (INR (C ^ (S k)) * sqrt (INR (C ^ (S k)))))%R
          by (field; split; lra).
        replace (1 * (INR (v ((i + S k)%nat)) * sqrt (INR (v ((i + S k)%nat)))))%R
          with (INR (v ((i + S k)%nat)) * sqrt (INR (v ((i + S k)%nat))))%R by ring.
        assert (HIN : (INR (v i) * INR (C ^ (S k)) <= INR (v ((i + S k)%nat)))%R).
        { rewrite <- (mult_INR (v i) (C ^ (S k))). apply le_INR. apply/leP.
          apply chain_pow. exact Hchain. }
        assert (HP0 : (0 <= INR (v i) * INR (C ^ (S k)))%R)
          by (apply Rmult_le_pos; apply pos_INR).
        assert (HQ0 : (0 <= INR (v ((i + S k)%nat)))%R) by apply pos_INR.
        assert (Hsq : (sqrt (INR (v i) * INR (C ^ (S k))) <= sqrt (INR (v ((i + S k)%nat))))%R)
          by (apply sqrt_le_1; [ exact HP0 | exact HQ0 | exact HIN ]).
        replace ((INR (v i) * sqrt (INR (v i))) * (INR (C ^ (S k)) * sqrt (INR (C ^ (S k)))))%R
          with ((INR (v i) * INR (C ^ (S k))) * sqrt (INR (v i) * INR (C ^ (S k))))%R
          by (rewrite (sqrt_mult (INR (v i)) (INR (C ^ (S k)))
                        (pos_INR (v i)) (pos_INR (C ^ (S k)))); ring).
        assert (HPg : (0 < INR (v i) * INR (C ^ (S k)))%R)
          by (apply Rmult_lt_0_compat; [ exact Hia | exact HIC ]).
        apply (Rle_trans _ (INR (v ((i + S k)%nat)) * sqrt (INR (v i) * INR (C ^ (S k))))).
        { apply Rmult_le_compat_r; [ apply Rlt_le, sqrt_pos_strict; exact HPg | exact HIN ]. }
        { apply Rmult_le_compat_l; [ exact HQ0 | exact Hsq ]. }
Qed.

(* ---------- RS5：行和收口 ---------- *)

Lemma lsum_scal (c : R) (f : nat -> R) (m : nat) :
  (lsum (fun k => c * f k) m = c * lsum f m)%R.
Proof.
  induction m as [| m IH]; cbn [lsum].
  - ring.
  - rewrite IH. ring.
Qed.

Lemma geo_scaled (C : nat) (m : nat) : (2 <= C)%nat ->
  (lsum (fun d => PI * qval C ^ (S d)) m <= PI * qval C / (1 - qval C))%R.
Proof.
  intros HC.
  destruct (q_range C HC) as [Hq0 Hq1].
  rewrite (lsum_scal PI (fun d => (qval C ^ (S d))%R) m).
  replace (PI * qval C / (1 - qval C))%R
    with (PI * (qval C / (1 - qval C)))%R by (unfold Rdiv; ring).
  apply Rmult_le_compat_l; [ apply Rlt_le, PI_RGT_0 | ].
  apply (Rle_trans _ (qval C / (1 - qval C))).
  - apply geo_bound; split; [exact Hq0 | exact Hq1].
  - unfold Rdiv. apply Rmult_le_compat_r.
    + left. apply Rinv_0_lt_compat. lra.
    + lra.
Qed.

Lemma oneside (C : nat) (v : nat -> nat) (i m : nat) :
  (2 <= C)%nat -> (2 <= v i)%nat ->
  (forall j, (v j * C <= v (S j)))%nat ->
  (lsum (fun d => Fpair (v i) (v ((i + S d)%nat))) m
   <= PI * qval C / (1 - qval C))%R.
Proof.
  intros HC Hvi Hchain.
  apply (Rle_trans _ (lsum (fun d => (PI * qval C ^ (S d))%R) m)).
  - apply lsum_le. intros d Hd.
    exact (pair_decay C v i d HC Hvi Hchain).
  - apply geo_scaled. exact HC.
Qed.

Lemma row_sum_3halfs (C : nat) (v : nat -> nat) (i m : nat) :
  (2 <= C)%nat -> (m <= i)%nat ->
  (forall j, (2 <= v j)%nat) ->
  (forall j, (v j * C <= v (S j)))%nat ->
  (lsum (fun d => Fpair (v i) (v ((i + S d)%nat))) m
   + lsum (fun d => Fpair (v ((i - S d)%nat)) (v i)) m
   <= 2 * (PI * qval C / (1 - qval C)))%R.
Proof.
  intros HC Hmi Hv2 Hchain.
  assert (Hvi : (2 <= v i)%nat) by apply Hv2.
  apply (Rle_trans _
           (PI * qval C / (1 - qval C) + PI * qval C / (1 - qval C))).
  - apply Rplus_le_compat.
    + apply oneside; assumption.
    + apply (Rle_trans _ (lsum (fun d => (PI * qval C ^ (S d))%R) m)).
      * apply lsum_le. intros d Hd.
        assert (Hsd : (S d <= i)%nat) by exact (leq_trans Hd Hmi).
        assert (Heq : (((i - S d)%nat + S d)%nat = i)%nat)
          by (rewrite (subnK Hsd); reflexivity).
        pose proof (pair_decay C v ((i - S d)%nat) d HC (Hv2 _) Hchain) as HP.
        rewrite Heq in HP. exact HP.
      * apply geo_scaled. exact HC.
  - ring_simplify. apply Rle_refl.
Qed.

(* ---------- 数值实例：C = 4 ---------- *)

Lemma sqrt_INR_4 : (sqrt (INR 4) = 2)%R.
Proof.
  assert (H4 : (INR 4 = 4)%R) by (simpl; ring).
  assert (Hsp : (0 < sqrt (INR 4))%R) by (apply sqrt_posnat; by []).
  assert (Hss : (sqrt (INR 4) * sqrt (INR 4) = INR 4)%R)
    by (rewrite H4; apply sqrt_sqrt; lra).
  assert (E : ((sqrt (INR 4) - 2) * (sqrt (INR 4) + 2) = 0)%R).
  { replace ((sqrt (INR 4) - 2) * (sqrt (INR 4) + 2))%R
      with (sqrt (INR 4) * sqrt (INR 4) - 2 * 2)%R by ring.
    rewrite Hss H4. ring. }
  destruct (Rmult_integral _ _ E) as [E1 | E2].
  - lra.
  - exfalso. lra.
Qed.

Lemma qval4_eq : (qval 4 = 1 / 8)%R.
Proof.
  assert (HC4 : (2 <= 4)%nat) by by [].
  assert (H := q_eq 4 HC4).
  assert (H4 : (INR 4 = 4)%R) by (simpl; ring).
  rewrite sqrt_INR_4 H4 in H.
  replace (4 * 2)%R with 8%R in H by ring.
  apply (Rmult_eq_reg_r 8); (rewrite H; field; lra) || lra.
Qed.

Lemma row_bound_C4 : (2 * (PI * qval 4 / (1 - qval 4)) <= 1)%R.
Proof.
  rewrite qval4_eq.
  assert (Hb : (PI <= 7 / 2)%R).
  { unfold PI. replace (7 / 2)%R with (2 * (7 / 4))%R by (field; lra).
    apply (Rmult_le_compat_l 2 PI2 (7 / 4)); [ lra | apply (proj2 pi2_int) ]. }
  replace (1 - 1 / 8)%R with (7 / 8)%R by (field; lra).
  apply (Rle_trans _ (2 * ((7 / 2) * (1 / 8) / (7 / 8)))).
  - apply Rmult_le_compat_l; [ lra | ].
    unfold Rdiv. apply Rmult_le_compat_r; [ left; apply Rinv_0_lt_compat; lra | ].
    apply Rmult_le_compat_r; [ lra | exact Hb ].
  - replace ((7 / 2) * (1 / 8) / (7 / 8))%R with (1 / 2)%R
      by (unfold Rdiv; field).
    replace (2 * (1 / 2))%R with 1%R by (field; lra).
    apply Rle_refl.
Qed.

End RowSum.

Print Assumptions RowSum.row_sum_3halfs.
Print Assumptions RowSum.oneside.
Print Assumptions RowSum.pair_decay.
Print Assumptions RowSum.pair_le_crude.
Print Assumptions RowSum.row_bound_C4.
