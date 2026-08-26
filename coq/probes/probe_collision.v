(* ============================================================
   碰撞距离框架探针（probe_collision）
   定理族：
   C1  kernel_collides_iff：相对核精确碰撞 ⟺ D·θ ∈ 2πℤ
   C2  grid_band_collision：θ=2πm/N 碰撞 ⟺ N ∣ D·m
       （推论 grid_first_collision_at_N：m=1 时 0<D<N 无碰撞）
   C3  linear_bias_no_collision：ALiBi 线性偏置任意 lag 无碰撞（∞ 端点）
   C4  tau / trained_collision_pair_charac：训练内可观测碰撞质量 τ(n)=T−n
   C5  irrational_offset_no_collision：θ=2π(β+m/N)，β 无理 ⟹ 永无精确碰撞
       —— 与 GridOrtho.off_grid_ortho 合成偏移网格设计证书。
   实验对应：--ogrid：theta = 2π·(β + m/N)，β 黄金比 (√5−1)/2。
   纪律：零 Admitted、零自定义公理；五定理零 classic（脚印仅 Dedekind 三件套）。
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
Import ComplexNumbers.
Import FourierAnalysis.

Open Scope R_scope.
Open Scope complex_scope.
Open Scope nat_scope.

Module CollisionDistance.

Lemma i_split (x y : R) : (0 +i (x + y)) = (0 +i x) +c (0 +i y).
Proof.
  unfold Cadd. apply Complex_eq; simpl; ring.
Qed.

(* ---------- 相位与碰撞定义 ---------- *)

Definition phase_rot (theta : R) (d : nat) : Complex :=
  Cexp (0 +i (INR d * theta)).

Definition kernel_collides (theta : R) (D : nat) : Prop :=
  forall d, phase_rot theta (d + D) = phase_rot theta d.

(* ---------- C1：碰撞刻画 ---------- *)

Theorem kernel_collides_iff (theta : R) (D : nat) :
  kernel_collides theta D <-> exists k : Z, (INR D * theta)%R = (2 * PI * IZR k)%R.
Proof.
  split.
  - intros H.
    assert (HC1 : Cexp (0 +i (INR D * theta)) = C1).
    { specialize (H 0%nat).
      rewrite Nat.add_0_l in H.
      unfold phase_rot in H.
      replace ((INR 0 * theta)%R) with 0%R in H by (rewrite INR_0; ring).
      replace (0 +i 0%R) with C0 in H by reflexivity.
      rewrite Cexp_0 in H. exact H. }
    apply (proj2 (Cexp_eq_1_iff (INR D * theta))).
    exact HC1.
  - intros [k Hk] d.
    unfold phase_rot.
    rewrite plus_INR.
    replace ((INR d + INR D) * theta)%R with ((INR d * theta + INR D * theta)%R) by ring.
    rewrite Hk.
    rewrite i_split.
    rewrite Cexp_add.
    rewrite (Cexp_2PI_int k).
    apply Cmul_1_r.
Qed.

(* ---------- C2：网格带碰撞 ⟺ N ∣ D·m ---------- *)

Theorem grid_band_collision (N m D : nat) :
  (2 <= N)%nat ->
  (kernel_collides (2 * PI * INR m / INR N) D <-> Nat.divide N (D * m)).
Proof.
  intros HN.
  assert (Hp : (0 < INR N)%R) by (apply lt_0_INR; lia).
  assert (HPI : (2 * PI <> 0)%R)
    by (apply Rgt_not_eq, Rmult_lt_0_compat; [lra | apply PI_RGT_0]).
  rewrite kernel_collides_iff.
  split.
  - intros [k Hk].
    assert (HL : (INR D * (2 * PI * INR m / INR N))%R
                 = ((2 * PI) * (INR (D * m) / INR N))%R).
    { rewrite mult_INR. field. apply Rgt_not_eq. exact Hp. }
    rewrite HL in Hk.
    assert (Hk' : (INR (D * m) / INR N)%R = (IZR k)%R)
      by (apply (Rmult_eq_reg_l (2 * PI)); [exact Hk | exact HPI]).
    assert (HkN : (INR (D * m))%R = (IZR k * INR N)%R).
    { apply (Rmult_eq_reg_l (2 * PI)); [ | exact HPI].
      rewrite <- Hk'.
      field. apply Rgt_not_eq. exact Hp. }
    destruct k as [| p | p].
    + simpl in HkN.
      assert (HDm0 : (D * m = 0)%nat)
        by (apply INR_eq; rewrite HkN, Rmult_0_l; symmetry; exact INR_0).
      exists 0%nat. rewrite Nat.mul_0_l. exact HDm0.
    + rewrite <- (positive_nat_Z p) in HkN.
      rewrite <- (INR_IZR_INZ (Pos.to_nat p)) in HkN.
      exists (Pos.to_nat p).
      apply INR_eq.
      rewrite (mult_INR (Pos.to_nat p) N).
      exact HkN.
    + exfalso.
      replace (IZR (Z.neg p)) with (- IZR (Z.pos p))%R in HkN by reflexivity.
      rewrite <- (positive_nat_Z p) in HkN.
      rewrite <- (INR_IZR_INZ (Pos.to_nat p)) in HkN.
      assert (Hpos : (0 < INR (Pos.to_nat p))%R)
        by (apply lt_0_INR; destruct p; simpl; lia).
      assert (Hge : (0 <= INR (D * m))%R) by (apply (le_INR 0 (D * m)); lia).
      nra.
  - intros [q Hq].
    exists (Z.of_nat q).
    assert (Hdm : (INR D * INR m)%R = (INR N * INR q)%R)
      by (rewrite <- (mult_INR D m), <- (mult_INR N q); f_equal;
          rewrite (Nat.mul_comm N q); exact Hq).
    rewrite <- (INR_IZR_INZ q).
    replace (INR q) with (INR D * INR m / INR N)%R
      by (rewrite Hdm; field; apply Rgt_not_eq; exact Hp).
    field. apply Rgt_not_eq. exact Hp.
Qed.

(* C2 推论：单位频率带 m=1 在 lag < N 内无碰撞（首次精确碰撞恰在 N） *)
Corollary grid_first_collision_at_N (N D : nat) :
  (2 <= N)%nat -> (0 < D)%nat -> (D < N)%nat ->
  ~ kernel_collides (2 * PI * INR 1 / INR N) D.
Proof.
  intros HN HD Dlt Hcol.
  apply (proj1 (grid_band_collision N 1 D HN)) in Hcol.
  destruct Hcol as [q Hq].
  rewrite Nat.mul_1_r in Hq.
  destruct q as [|q'].
  - lia.
  - assert (Hle : (N <= (S q') * N)%nat) by nia.
    lia.
Qed.

(* ---------- C3：ALiBi 线性偏置无碰撞 ---------- *)

Definition linear_bias (slope : R) (d : nat) : R := slope * INR d.

Theorem linear_bias_no_collision (slope : R) (D : nat) :
  (slope <> 0)%R -> (0 < D)%nat ->
  exists d, linear_bias slope (d + D) <> linear_bias slope d.
Proof.
  intros Hs HD.
  exists 0%nat.
  unfold linear_bias.
  rewrite Nat.add_0_l, INR_0.
  replace ((slope * 0)%R) with 0%R by ring.
  intro Heq.
  assert (HD0 : (0 < INR D)%R) by (apply lt_0_INR; lia).
  nra.
Qed.

(* ---------- C4：训练内可观测碰撞质量 τ ---------- *)

(* τ(n) = T − n：窗口 T 内位置对 (k, k+n) 的数目——带 n 的碰撞结构
   在训练中可观测的样本量（覆盖梯度 / 碰撞距离二分机制的定量变量，
   见框架文档 §8 的回测表与预登记预测） *)
Definition tau (T n : nat) : nat := T - n.

Lemma trained_collision_pair_charac (T n k : nat) :
  ((k + n < T)%nat <-> (k < tau T n)%nat).
Proof.
  unfold tau. lia.
Qed.

(* ---------- C5：无理偏移零碰撞 ---------- *)

(* 无理性以线性形式陈述（避开除法）：q·x = p 的整数解不存在 *)
Definition R_irrational (x : R) : Prop :=
  forall (p q : Z), (q <> 0)%Z -> ((IZR q * x <> IZR p)%R).

(* β 无理 ⟹ 偏移网格角 θ = 2π(β + m/N) 在任意 lag 上无精确碰撞。
   与 GridOrtho.off_grid_ortho 合成：μ=0 全长度证书 + 零精确碰撞。 *)
Theorem irrational_offset_no_collision (beta : R) (N m D : nat) :
  R_irrational beta -> (2 <= N)%nat -> (0 < D)%nat ->
  ~ kernel_collides (2 * PI * (beta + INR m / INR N)) D.
Proof.
  intros Hirr HN HD Hcol.
  apply (proj1 (kernel_collides_iff (2 * PI * (beta + INR m / INR N)) D)) in Hcol.
  destruct Hcol as [k Hk].
  assert (Hp : (0 < INR N)%R) by (apply lt_0_INR; lia).
  assert (HPI : (2 * PI <> 0)%R)
    by (apply Rgt_not_eq, Rmult_lt_0_compat; [lra | apply PI_RGT_0]).
  (* 消 2π *)
  assert (H2 : (INR D * (beta + INR m / INR N))%R = (IZR k)%R).
  { apply (Rmult_eq_reg_l (2 * PI)); [ | exact HPI].
    replace ((2 * PI) * (INR D * (beta + INR m / INR N)))%R
      with (INR D * (2 * PI * (beta + INR m / INR N)))%R by ring.
    rewrite Hk. reflexivity. }
  (* 两边乘 INR N，整理为无理性的线性形式 *)
  assert (H3 : (INR N * (INR D * beta) + INR D * INR m)%R = (INR N * IZR k)%R).
  { assert (H2N : (INR N * (INR D * beta + INR D * (INR m / INR N)))%R
                  = (INR N * IZR k)%R)
      by (apply (f_equal (fun x : R => (INR N * x)%R));
          replace ((INR D * beta + INR D * (INR m / INR N)))%R
            with ((INR D * (beta + INR m / INR N)))%R by ring;
          exact H2).
    rewrite Rmult_plus_distr_l in H2N.
    assert (Hx : (INR N * (INR D * (INR m / INR N)))%R = (INR D * INR m)%R)
      by (field; apply Rgt_not_eq; exact Hp).
    rewrite Hx in H2N. exact H2N. }
  apply (Hirr ((k * Z.of_nat N - Z.of_nat D * Z.of_nat m)%Z)
              ((Z.of_nat N * Z.of_nat D)%Z)).
  - assert (HNz : (Z.of_nat N <> 0)%Z) by lia.
    assert (HDz : (Z.of_nat D <> 0)%Z) by lia.
    nia.
  - rewrite (mult_IZR (Z.of_nat N) (Z.of_nat D)).
    rewrite <- (INR_IZR_INZ N), <- (INR_IZR_INZ D).
    rewrite minus_IZR.
    rewrite (mult_IZR k (Z.of_nat N)), (mult_IZR (Z.of_nat D) (Z.of_nat m)).
    rewrite <- (INR_IZR_INZ N), <- (INR_IZR_INZ D), <- (INR_IZR_INZ m).
    nra.
Qed.

End CollisionDistance.

(* ---------- 构造性审计（Print Assumptions，2026-08-22） ---------- *)

Print Assumptions CollisionDistance.kernel_collides_iff.
Print Assumptions CollisionDistance.grid_band_collision.
Print Assumptions CollisionDistance.grid_first_collision_at_N.
Print Assumptions CollisionDistance.linear_bias_no_collision.
Print Assumptions CollisionDistance.irrational_offset_no_collision.
