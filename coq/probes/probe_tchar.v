(* ============================================================
   T1 rational_min_period_coprime：θ = 2π·P/Q（gcd(P,Q)=1）⟹
      kernel_collides ⟺ Q ∣ D —— 最小碰撞周期恰为 Q（Nat.gauss 核心）。
   T2 collides_iff_rational_witness：∃精确碰撞 ⟺ θ/2π 有理见证
      （正存在形式，双向全构造性，显式见证）。
   T3 rational_offset_collides：偏移网格角 2π(p/q + m/N) 在 q·N 处碰撞。
   T4 offset_min_period_coprime：分数既约时最小碰撞距离 = q·N（闭式）。

   ============================================================ *)
Require Import Stdlib.Reals.Reals.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.micromega.Lra.
Require Import Stdlib.ZArith.ZArith.
Require Import ca_base.
Require Import ca_complex_foundation.
Require Import ca_independence.
Require Import ca_fourier.
Require Import ca_char_ortho.
Require Import ca_zeta_scaffold.
Require Import probe_collision.
Import ComplexNumbers.
Import FourierAnalysis.
Import CollisionDistance.

Open Scope R_scope.
Open Scope complex_scope.
Open Scope nat_scope.

Module TChar.

(* ---------- 辅助 ---------- *)

Lemma IZR_opp (z : Z) : (IZR (Z.opp z))%R = (- (IZR z))%R.
Proof.
  destruct z as [| q | q].
  - replace (IZR (Z.opp 0))%R with 0%R by reflexivity.
    replace (IZR 0)%R with 0%R by reflexivity.
    rewrite Ropp_0. reflexivity.
  - reflexivity.
  - change (IZR (Z.neg q)) with (- (IZR (Z.pos q)))%R.
    rewrite Ropp_involutive. reflexivity.
Qed.

Lemma INR_eq_0 (n : nat) : (INR n = 0)%R -> (n = 0)%nat.
Proof.
  intro H. destruct n as [| n']; [reflexivity | ].
  rewrite S_INR in H.
  assert (Hge : (0 <= INR n')%R) by (apply (le_INR 0 n'); lia).
  lra.
Qed.

(* ---------- T1：既约有理角的最小碰撞周期 = Q ---------- *)

Theorem rational_min_period_coprime (P Q D : nat) :
  (0 < Q)%nat -> (Nat.gcd P Q = 1)%nat ->
  (kernel_collides (2 * PI * INR P / INR Q) D <-> Nat.divide Q D).
Proof.
  intros HQ Hgcd.
  assert (HQz : (0 < INR Q)%R) by (apply lt_0_INR; lia).
  assert (HPI : (2 * PI <> 0)%R)
    by (apply Rgt_not_eq, Rmult_lt_0_compat; [lra | apply PI_RGT_0]).
  rewrite kernel_collides_iff.
  split.
  - (* 碰撞 ⟹ Q ∣ D：消 2π、乘 Q、符号分析、Gauss *)
    intros [k Hk].
    assert (Hfrac : (INR D * (INR P / INR Q))%R = (IZR k)%R).
    { apply (Rmult_eq_reg_l (2 * PI)); [ | exact HPI].
      replace ((2 * PI) * (INR D * (INR P / INR Q)))%R
        with (INR D * (2 * PI * INR P / INR Q))%R by (field; apply Rgt_not_eq; assumption).
      exact Hk. }
    assert (Hmul : (INR (D * P))%R = (IZR k * INR Q)%R).
    { rewrite mult_INR. rewrite <- Hfrac.
      field. apply Rgt_not_eq; exact HQz. }
    destruct k as [| p | p].
    + (* k = 0：D*P = 0；P=0 时 gcd(0,Q)=Q=1；否则 D=0 *)
      replace (IZR 0)%R with 0%R in Hmul by reflexivity.
      assert (HDhP : (D * P = 0)%nat)
        by (apply INR_eq_0; rewrite Hmul; ring).
      destruct (Nat.eq_dec P 0) as [HP0 | HPne].
      * rewrite HP0 in Hgcd. rewrite Nat.gcd_0_l in Hgcd.
        rewrite Hgcd. exists D. ring.
      * assert (HD0 : (D = 0)%nat) by lia.
        rewrite HD0. exists 0%nat. ring.
    + (* k > 0：Q ∣ D*P，Gauss（gcd(Q,P)=1）⟹ Q ∣ D *)
      rewrite <- (positive_nat_Z p) in Hmul.
      rewrite <- (INR_IZR_INZ (Pos.to_nat p)) in Hmul.
      rewrite <- (mult_INR (Pos.to_nat p) Q) in Hmul.
      assert (Hnat : (D * P = Pos.to_nat p * Q)%nat)
        by (apply INR_eq; exact Hmul).
      assert (HQd : Nat.divide Q (D * P)).
      { exists (Pos.to_nat p). rewrite Hnat. reflexivity. }
      apply (Nat.gauss Q P D);
        [rewrite (Nat.mul_comm P D); exact HQd |].
      rewrite (Nat.gcd_comm Q P). exact Hgcd.
    + (* k < 0：非负 = 严格负，矛盾 *)
      exfalso.
      replace (IZR (Z.neg p)) with (- (IZR (Z.pos p)))%R in Hmul by reflexivity.
      rewrite <- (positive_nat_Z p) in Hmul.
      rewrite <- (INR_IZR_INZ (Pos.to_nat p)) in Hmul.
      assert (Hpos : (0 < INR (Pos.to_nat p))%R)
        by (apply lt_0_INR; destruct p; simpl; lia).
      assert (Hge : (0 <= INR (D * P))%R)
        by (apply (le_INR 0 (D * P)); lia).
      nra.
  - (* Q ∣ D ⟹ 碰撞：显式见证 k = q*P *)
    intros [q Hq].
    exists (Z.of_nat (q * P)).
    rewrite <- (INR_IZR_INZ (q * P)).
    replace (INR (q * P))%R with (INR D * (INR P / INR Q))%R
      by (rewrite Hq; rewrite (mult_INR q P), (mult_INR q Q);
          field; apply Rgt_not_eq; exact HQz).
    field. apply Rgt_not_eq; assumption.
Qed.

(* ---------- T2：总量刻画（正存在形式，全构造性 iff） ---------- *)

Definition R_rational_witness (x : R) : Prop :=
  exists (p q : Z), (q <> 0)%Z /\ ((IZR q * x)%R = (IZR p)%R).

Theorem collides_iff_rational_witness (theta : R) :
  ((exists D, (0 < D)%nat /\ kernel_collides theta D)
   <-> R_rational_witness (theta / (2 * PI))).
Proof.
  assert (HPI : (2 * PI <> 0)%R)
    by (apply Rgt_not_eq, Rmult_lt_0_compat; [lra | apply PI_RGT_0]).
  (* 正向桥：消 2π *)
  assert (Hfwd : forall (D : nat) (k : Z),
    ((INR D * theta)%R = (2 * PI * IZR k)%R) ->
    ((INR D * (theta / (2 * PI)))%R = (IZR k)%R)).
  { intros D k H.
    apply (Rmult_eq_reg_l (2 * PI)); [ | exact HPI].
    rewrite <- H. field. apply Rgt_not_eq, PI_RGT_0. }
  (* 逆向桥：乘 2π *)
  assert (Hbwd : forall (D : nat) (k : Z),
    ((INR D * (theta / (2 * PI)))%R = (IZR k)%R) ->
    ((INR D * theta)%R = (2 * PI * IZR k)%R)).
  { intros D k H.
    replace ((INR D * theta)%R)
      with ((INR D * (theta / (2 * PI))) * (2 * PI))%R
      by (field; apply Rgt_not_eq, PI_RGT_0).
    rewrite H. ring. }
  split.
  - intros [D [HD Hcol]].
    apply (proj1 (kernel_collides_iff theta D)) in Hcol.
    destruct Hcol as [k Hk].
    specialize (Hfwd D k Hk).
    destruct k as [| p | p].
    + replace (IZR 0)%R with 0%R in Hfwd by reflexivity.
      assert (HxD : (0 < INR D)%R) by (apply lt_0_INR; lia).
      assert (Hx0 : ((theta / (2 * PI)) = 0)%R).
      { apply (Rmult_eq_reg_l (INR D)); [ | apply Rgt_not_eq; exact HxD].
        replace ((INR D * 0)%R) with 0%R by ring. exact Hfwd. }
      exists 0%Z, 1%Z. split; [lia | ].
      replace ((IZR 1 * (theta / (2 * PI))))%R with (theta / (2 * PI))%R by ring.
      exact Hx0.
    + exists (Z.pos p), (Z.of_nat D). split; [lia | ].
      rewrite <- (INR_IZR_INZ D). exact Hfwd.
    + exists (Z.neg p), (Z.of_nat D). split; [lia | ].
      rewrite <- (INR_IZR_INZ D). exact Hfwd.
  - intros [p [q [Hq Heq]]].
    destruct q as [| p' | p'].
    + lia.
    + (* q = Z.pos p'：D 见证 = Pos.to_nat p'，k = p *)
      exists (Pos.to_nat p').
      assert (HDp : (0 < Pos.to_nat p')%nat) by (destruct p'; simpl; lia).
      split; [exact HDp | ].
      apply (proj2 (kernel_collides_iff theta (Pos.to_nat p'))).
      exists p.
      apply Hbwd.
      rewrite (INR_IZR_INZ (Pos.to_nat p')), (positive_nat_Z p').
      exact Heq.
    + (* q = Z.neg p'：D 见证 = Pos.to_nat p'，k = Z.neg p *)
      exists (Pos.to_nat p').
      assert (HDp : (0 < Pos.to_nat p')%nat) by (destruct p'; simpl; lia).
      split; [exact HDp | ].
      apply (proj2 (kernel_collides_iff theta (Pos.to_nat p'))).
      exists (Z.opp p).
      apply Hbwd.
      rewrite (INR_IZR_INZ (Pos.to_nat p')), (positive_nat_Z p').
      rewrite IZR_opp.
      replace (IZR (Z.neg p')) with (- (IZR (Z.pos p')))%R in Heq by reflexivity.
      rewrite <- Heq.
      field. apply Rgt_not_eq, PI_RGT_0.
Qed.

(* ---------- T3：偏移网格碰撞存在性（C5 逆向，显式 lag = q·N） ---------- *)

Theorem rational_offset_collides (p q N m : nat) :
  (0 < q)%nat -> (2 <= N)%nat ->
  kernel_collides (2 * PI * (INR p / INR q + INR m / INR N)) (q * N).
Proof.
  intros Hq HN.
  assert (HQz : (0 < INR q)%R) by (apply lt_0_INR; lia).
  assert (HNz : (0 < INR N)%R) by (apply lt_0_INR; lia).
  apply (proj2 (kernel_collides_iff _ _)).
  exists (Z.of_nat (N * p + q * m)).
  rewrite <- (INR_IZR_INZ (N * p + q * m)).
  assert (Hkey : (INR (q * N) * (INR p / INR q + INR m / INR N))%R
                  = (INR (N * p + q * m))%R).
  { rewrite (mult_INR q N), (plus_INR (N * p) (q * m)),
          (mult_INR N p), (mult_INR q m).
    field; (split; apply Rgt_not_eq; assumption)
           || (apply Rgt_not_eq; assumption). }
  replace ((INR (q * N) * (2 * PI * (INR p / INR q + INR m / INR N))))%R
    with ((2 * PI) * (INR (q * N) * (INR p / INR q + INR m / INR N)))%R by ring.
  rewrite Hkey. reflexivity.
Qed.

(* ---------- T4：偏移网格最小碰撞距离闭式（既约形式） ---------- *)

Lemma offset_angle_frac (p q N m : nat) :
  (0 < q)%nat -> (2 <= N)%nat ->
  (2 * PI * (INR p / INR q + INR m / INR N))%R
  = (2 * PI * INR (N * p + q * m) / INR (q * N))%R.
Proof.
  intros Hq HN.
  assert (HQz : (0 < INR q)%R) by (apply lt_0_INR; lia).
  assert (HNz : (0 < INR N)%R) by (apply lt_0_INR; lia).
  rewrite (mult_INR q N), (plus_INR (N * p) (q * m)),
          (mult_INR N p), (mult_INR q m).
  field; (split; apply Rgt_not_eq; assumption)
         || (apply Rgt_not_eq; assumption).
Qed.

Theorem offset_min_period_coprime (p q N m D : nat) :
  (0 < q)%nat -> (2 <= N)%nat -> (Nat.gcd (N * p + q * m) (q * N) = 1)%nat ->
  (kernel_collides (2 * PI * (INR p / INR q + INR m / INR N)) D
   <-> Nat.divide (q * N) D).
Proof.
  intros Hq HN Hgcd.
  rewrite (offset_angle_frac p q N m Hq HN).
  apply rational_min_period_coprime; [lia | exact Hgcd].
Qed.

End TChar.

(* ---------- 构造性审计（Print Assumptions，2026-08-22） ---------- *)

Print Assumptions TChar.rational_min_period_coprime.
Print Assumptions TChar.collides_iff_rational_witness.
Print Assumptions TChar.rational_offset_collides.
Print Assumptions TChar.offset_min_period_coprime.
