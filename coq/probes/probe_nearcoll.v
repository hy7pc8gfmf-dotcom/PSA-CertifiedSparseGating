(* ============================================================
   定理：β = (√5 − 1)/2（黄金比小数部分），∀ d ≥ 1（nat）、∀ m（Z）：
        |d·β − m| ≥ 1/(3d)
   ——近碰撞不能快于 O(1/d) 聚集（Fibonacci 三距离的初等常数版），
     offset-grid 的定量护城河：精确碰撞永不发生（C5/T2）之外，
     近碰撞也被多项式下界挡住。

   证明（代数数范数路线，全程初等）：
   NC1 five_divides_square：5 | x² ⟹ 5 | x（div_mod 展开 + nia）。
   NC2 square5_zero：x² = 5y² ⟹ x = y = 0（无穷递降，|y| 的 nat 度量：
       解除以 5 仍是解，非零解 ⟹ |y| ≥ 5 ⟹ 度量严格下降）。
   NC3 no_quadratic_solution：d² − dm − m² = 0 ⟹ d = 0 ∧ m = 0
       （配方 (2d−m)² = 5m² 到 NC2）。
   NC4 golden_near_collision（主定理）：e := dβ − m 满足
       e·(m + d + dβ) = d² − dm − m²（用 β² = 1 − β，nra 消解）；
       右端是非零整数 ⟹ |·| ≥ 1；|m + d + dβ| = |2dβ + d − e|
       ≤ 2·(5/8)d + d + 1/2 ≤ 3d（β ≤ 5/8；|e| ≥ 1/2 大情形单独处理）；
       故 |e| ≥ 1/(3d)。
   NC5 实例化：phi_gold := (sqrt 5 − 1)/2，验证二次方程与界 7/5 ≤ √5 ≤ 9/4。
   审计：Print Assumptions 尾部（预期 ≤ Dedekind 两件）。
   ============================================================ *)
Require Import Stdlib.Reals.Reals.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.micromega.Lra.
Open Scope R_scope.

Module NearColl.

(* ---------- NC1：5 | x² ⟹ 5 | x ---------- *)

Lemma mod5_cases : forall r : Z, (0 <= r < 5)%Z ->
  (r = 0 \/ r = 1 \/ r = 2 \/ r = 3 \/ r = 4)%Z.
Proof. intros r Hr. lia. Qed.

Lemma five_divides_square : forall x : Z, ((5 | x * x)%Z -> (5 | x)%Z).
Proof.
  intros x H.
  assert (H5 : (5 <> 0)%Z) by lia.
  destruct (Z.eq_dec (x mod 5)%Z 0%Z) as [E | E].
  - apply (proj1 (Z.mod_divide x 5 H5)). exact E.
  - exfalso.
    assert (H0 : ((x * x) mod 5 = 0)%Z)
      by (apply (proj2 (Z.mod_divide (x * x) 5 H5)); exact H).
    rewrite <- Z.mul_mod_idemp_l in H0 by lia.
    rewrite <- Z.mul_mod_idemp_r in H0 by lia.
    assert (Hr : (0 <= x mod 5 < 5)%Z) by (apply Z.mod_pos_bound; lia).
    destruct (mod5_cases (x mod 5)%Z Hr) as [E1 | [E1 | [E1 | [E1 | E1]]]];
      try contradiction;
      rewrite E1 in H0; vm_compute in H0; discriminate.
Qed.

(* ---------- NC2：x² = 5y² ⟹ x = y = 0（无穷递降） ---------- *)

Lemma square5_zero : forall x y : Z, (x * x = 5 * y * y)%Z -> (x = 0 /\ y = 0)%Z.
Proof.
  assert (Haux : forall (n : nat) (x y : Z),
            ((Z.abs y <= Z.of_nat n)%Z) -> (x * x = 5 * y * y)%Z -> (x = 0 /\ y = 0)%Z).
  { induction n as [| n IH]; intros x y Hn Heq.
    - assert (Hy0 : (y = 0)%Z) by lia. subst y.
      rewrite Z.mul_0_r in Heq. split; [nia | reflexivity].
    - destruct (Z.eq_dec y 0) as [Hy0 | HyN].
      + subst y. rewrite Z.mul_0_r in Heq. split; [nia | reflexivity].
      + (* 5 | x 与 5 | y，解缩小 1/5 仍是解 *)
        assert (Hdx : (5 | x * x)%Z).
        { exists (y * y)%Z. rewrite (Z.mul_comm (y * y) 5%Z). nia. }
        destruct (five_divides_square x Hdx) as [x1 Hx1].
        assert (Hy2 : (y * y = 5 * (x1 * x1))%Z).
        { rewrite Hx1 in Heq. nia. }
        assert (Hdy : (5 | y * y)%Z).
        { exists (x1 * x1)%Z. rewrite (Z.mul_comm (x1 * x1) 5%Z). nia. }
        destruct (five_divides_square y Hdy) as [y1 Hy1].
        assert (HyN1 : (y1 <> 0)%Z) by lia.
        assert (Hrec : (Z.abs y1 <= Z.of_nat n)%Z).
        { rewrite Hy1 in Hn. rewrite Z.abs_mul in Hn.
          replace (Z.abs (5%Z)) with (5%Z) in Hn by reflexivity. nia. }
        assert (Heq1 : (x1 * x1 = 5 * y1 * y1)%Z).
        { rewrite Hx1 in Heq. rewrite Hy1 in Heq. nia. }
        destruct (IH x1 y1 Hrec Heq1) as [Hx0 Hy01].
        rewrite Hx0 in Hy2. rewrite !Z.mul_0_l in Hy2. nia. }
  intros x y Heq.
  assert (Hz : (Z.abs y <= Z.of_nat (Z.abs_nat (Z.abs y)))%Z).
  { destruct (Z.abs y) as [|p|p]; simpl.
    - lia.
    - rewrite <- (Z2Nat.id (Z.pos p)) by lia. lia.
    - pose proof (Nat2Z.is_nonneg (Pos.to_nat p)). lia. }
  apply (Haux (Z.abs_nat (Z.abs y)) x y); [exact Hz | exact Heq].
Qed.

(* ---------- NC3：d² − dm − m² = 0 只有零解 ---------- *)

Lemma no_quadratic_solution :
  forall d m : Z, (d * d - d * m - m * m = 0)%Z -> (d = 0 /\ m = 0)%Z.
Proof.
  intros d m H.
  assert (Hsq : ((2 * d - m) * (2 * d - m) = 5 * m * m)%Z) by nia.
  destruct (square5_zero _ _ Hsq) as [H2 _].
  nia.
Qed.

Lemma Rabs_IZR (k : Z) : (Rabs (IZR k) = IZR (Z.abs k))%R.
Proof.
  destruct (Z_le_gt_dec 0 k) as [Hlk | Hlk].
  - rewrite (Z.abs_eq k Hlk).
    assert (Hge : (IZR k >= 0)%R) by (apply Rle_ge; apply IZR_le; exact Hlk).
    rewrite (Rabs_right (IZR k) Hge).
    reflexivity.
  - rewrite (Z.abs_neq k (Z.lt_le_incl k 0 (Z.gt_lt 0 k Hlk))).
    assert (Hlt : (IZR k < 0)%R) by (apply IZR_lt; exact (Z.gt_lt 0 k Hlk)).
    rewrite (Rabs_left (IZR k) Hlt).
    rewrite opp_IZR. reflexivity.
Qed.

(* ---------- NC4：主定理 ---------- *)

Theorem golden_near_collision (phi : R)
        (Hphi : (phi * phi + phi - 1 = 0)%R)
        (Hpos : (0 < phi)%R) (Hb : (phi <= 5 / 8)%R) :
  forall (d : nat) (m : Z), (1 <= d)%nat ->
  ((/ (3 * INR d) <= Rabs (INR d * phi - IZR m)))%R.
Proof.
  intros d m Hd.
  assert (Hd1 : (1 <= INR d)%R).
  { rewrite <- (INR_1). apply le_INR. lia. }
  assert (H3D : (0 < 3 * INR d)%R) by lra.
  destruct (Rle_or_lt (1 / 2) (Rabs (INR d * phi - IZR m))) as [Hbig | Hsmall].
  - (* 大情形：|e| ≥ 1/2 ≥ 1/(3d) *)
    apply (Rle_trans _ (1 / 2)); [ | exact Hbig].
    replace (1 / 2) with (/ 2) by (unfold Rdiv; ring).
    apply Rinv_le_contravar; [lra | lra].
  - (* 小情形：范数论证 *)
    set (D := INR d) in *.
    set (M := IZR m) in *.
    set (e := D * phi - M) in *.
    assert (HD : (0 < D)%R) by lra.
    (* 范数恒等式 *)
    assert (Hnorm : (e * (M + D + D * phi) = D * D - D * M - M * M)%R)
      by (unfold e; nra).
    (* 右端是非零整数 *)
    assert (Hk : (D * D - D * M - M * M
                  = IZR (Z.of_nat d * Z.of_nat d - Z.of_nat d * m - m * m))%R).
    { unfold D, M.
      rewrite !INR_IZR_INZ. rewrite !minus_IZR. rewrite !mult_IZR. ring. }
    destruct (Z.eq_dec (Z.of_nat d * Z.of_nat d - Z.of_nat d * m - m * m) 0%Z)
      as [Hz | Hnz].
    + exfalso. destruct (no_quadratic_solution _ _ Hz) as [Hd0 _].
      assert ((1 <= Z.of_nat d)%Z) by lia. lia.
    + assert (Hge1 : (1 <= Rabs (IZR (Z.of_nat d * Z.of_nat d
                                      - Z.of_nat d * m - m * m)))%R).
      { assert (Hap : (0 < Z.abs (Z.of_nat d * Z.of_nat d
                                   - Z.of_nat d * m - m * m))%Z).
        { apply Z.abs_pos. exact Hnz. }
        assert (H1 : (1 <= Z.abs (Z.of_nat d * Z.of_nat d
                                   - Z.of_nat d * m - m * m))%Z) by lia.
        rewrite Rabs_IZR. apply IZR_le. exact H1. }
      rewrite <- Hk in Hge1.
      (* |e| · |m + d + dφ| = |K| ≥ 1 *)
      assert (Hprod : ((Rabs e) * (Rabs (M + D + D * phi))
                       = Rabs (D * D - D * M - M * M))%R).
      { rewrite <- Rabs_mult. rewrite Hnorm. reflexivity. }
      (* |m + d + dφ| ≤ 3D *)
      assert (Hbound : (Rabs (M + D + D * phi) <= 3 * D)%R).
      { replace M with (D * phi - e) by (unfold e; ring).
        assert (H1 : (Rabs (2 * D * phi + D - e)
                       <= Rabs (2 * D * phi + D) + Rabs e)%R).
        { apply (Rle_trans _ (Rabs (2 * D * phi + D) + Rabs (- e))).
          - apply Rabs_triang.
          - rewrite Rabs_Ropp. apply Rle_refl. }
        assert (H2 : (Rabs (2 * D * phi + D) <= 2 * D * phi + D)%R).
        { assert (Hge : (2 * D * phi + D >= 0)%R) by nra.
  rewrite (Rabs_right (2 * D * phi + D) Hge). apply Rle_refl. }
        assert (H3 : (2 * D * phi + D + Rabs e <= 9 / 4 * D + 1 / 2)%R).
        { apply Rplus_le_compat.
          - assert (HphiD : (2 * D * phi <= 2 * D * (5 / 8))%R).
            { apply Rmult_le_compat_l; [nra | exact Hb]. }
            lra.
          - lra. }
        assert (H4 : (9 / 4 * D + 1 / 2 <= 3 * D)%R) by nra.
        replace ((D * phi - e) + D + D * phi) with (2 * D * phi + D - e) by ring.
        apply (Rle_trans _ (Rabs (2 * D * phi + D) + Rabs e)).
        { exact H1. }
        apply (Rle_trans _ ((2 * D * phi + D) + Rabs e)).
        { apply Rplus_le_compat; [exact H2 | apply Rle_refl]. }
        apply (Rle_trans _ (9 / 4 * D + 1 / 2)).
        { exact H3. }
        exact H4. }
      (* 收口 *)
      assert (Hfin : (1 <= Rabs e * (3 * D))%R).
      { apply (Rle_trans _ (Rabs e * Rabs (M + D + D * phi))).
        - rewrite Hprod. exact Hge1.
        - apply Rmult_le_compat_l; [apply Rabs_pos | exact Hbound]. }
      apply (Rmult_le_reg_r (3 * D)); [exact H3D | ].
      assert (Hnz2 : (3 * D <> 0)%R) by lra.
      rewrite (Rinv_l (3 * D) Hnz2).
      exact Hfin.
Qed.

(* ---------- NC5：黄金比实例化 ---------- *)

Definition phi_gold : R := (sqrt 5 - 1) / 2.

Lemma sqrt5_bounds : ((7 / 5 <= sqrt 5) /\ (sqrt 5 <= 9 / 4))%R.
Proof.
  set (s := sqrt 5).
  assert (Hs : (s * s = 5)%R) by (apply sqrt_sqrt; lra).
  assert (Hn : (0 <= s)%R) by apply sqrt_pos.
  split.
  - destruct (Rle_or_lt (7 / 5) s) as [H | H]; [exact H | exfalso].
    assert (Hlt : (s * s <= 7 / 5 * (7 / 5))%R).
    { apply (Rle_trans _ (s * (7 / 5))%R).
      - apply Rmult_le_compat_l; lra.
      - apply Rmult_le_compat_r; lra. }
    lra.
  - destruct (Rle_or_lt s (9 / 4)) as [H | H]; [exact H | exfalso].
    assert (Hlt : (9 / 4 * (9 / 4) <= s * s)%R).
    { apply (Rle_trans _ (s * (9 / 4))%R).
      - apply Rmult_le_compat_r; lra.
      - apply Rmult_le_compat_l; lra. }
    lra.
Qed.

Lemma phi_gold_spec :
  (phi_gold * phi_gold + phi_gold - 1 = 0 /\ (0 < phi_gold /\ phi_gold <= 5 / 8)).
Proof.
  unfold phi_gold.
  destruct sqrt5_bounds as [Hlo Hhi].
  set (s := sqrt 5) in *.
  assert (Hs : (s * s = 5)%R) by (apply sqrt_sqrt; lra).
  assert (Hn : (0 <= s)%R) by apply sqrt_pos.
  repeat split; nra.
Qed.

(* 主定理实例化：黄金比的近碰撞半径 *)
Theorem golden_near_collision_gold :
  forall (d : nat) (m : Z), (1 <= d)%nat ->
  ((/ (3 * INR d) <= Rabs (INR d * phi_gold - IZR m)))%R.
Proof.
  intros d m Hd.
  destruct phi_gold_spec as [H1 [H2 H3]].
  apply (golden_near_collision phi_gold H1 H2 H3 d m Hd).
Qed.

End NearColl.

Print Assumptions NearColl.golden_near_collision.
Print Assumptions NearColl.golden_near_collision_gold.
Print Assumptions NearColl.square5_zero.
