(* ============================================================
     {θ_t} 在窗 N 上两两正交 ⟺ ∃公共偏移 θ₀ 与 mod N 互异整数 j_t
     使 θ_t = θ₀ + 2π·j_t/N ——**没有第三种正交家族**。
   分件：
     OC1 pair_ortho_rot：正交对逐点 = 差频旋转原子（conj+mul 归约）。
     OC2 csum_ones：N 个 C1 之和 = Complex (INR N) 0 ≠ C0（N ≥ 1）。
     OC3 rot_all_one：rot θ 1 = C1 ⟹ rot θ k = C1（lag_add 归纳）。
     OC4 rot_C1_iff_collides：rot θ D = C1 ⟺ kernel_collides θ D
        （桥梁——接 probe_collision 的 C1 iff）。
     OC5 ortho_pair_grid_offset（⟹ 新证）：两两正交 ⟹
        a − b = 2π·m/N 且 m mod N ≠ 0（几何恒等式 + 2πℤ 见证 +
        csum_ones 反证）。
     OC6 grid_offset_ortho_pair（⟸）：2π·m/N（m mod N ≠ 0）⟹ 正交
        ——经 Cexp_2pi_shift 化 m 到 [0,N) 后复用 grid_pair_ortho。
     OC7 window_ortho_charac（主定理）：族级 iff 合成。
   审计：Print Assumptions 尾部。
   ============================================================ *)
From mathcomp Require Import ssreflect ssrnat.
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
Require Import probe_parseval.
Require Import probe_partial.
Require Import probe_pairdirichlet.
Require Import probe_collision.
Require Import probe_tchar.
(* E138①：Notation 注册（8 项，Nat.*——覆盖 mathcomp 劫持，独立环境仅 warning） *)
Notation "a + b" := (Nat.add a b) (at level 50, left associativity) : nat_scope.
Notation "a - b" := (Nat.sub a b) (at level 50, left associativity) : nat_scope.
Notation "a * b" := (Nat.mul a b) (at level 40, left associativity) : nat_scope.
Notation "a / b" := (Nat.div a b) (at level 40, left associativity) : nat_scope.
Notation "a <= b" := (Nat.le a b) (at level 70, no associativity) : nat_scope.
Notation "a < b" := (Nat.lt a b) (at level 70, no associativity) : nat_scope.
Notation "a >= b" := (Nat.le b a) (at level 70, no associativity) : nat_scope.
Notation "a > b" := (Nat.lt b a) (at level 70, no associativity) : nat_scope.

(* E089 双向桥：mathcomp bool 层 ⟷ Stdlib Prop 层（leq m n 展开为 Nat.eqb (m-n) 0） *)
Lemma le_mc_to_Prop (m n : nat) : is_true (ssrnat.leq m n) -> (m <= n)%nat.
Proof.
  intros H. unfold ssrnat.leq, is_true in H.
  unfold eqtype.eq_op in H. simpl in H.
  apply Nat.eqb_eq in H. apply Nat.sub_0_le in H. exact H.
Qed.
Lemma lt_mc_to_Prop (m n : nat) : is_true (ssrnat.leq (S m) n) -> (m < n)%nat.
Proof. intros H. apply le_mc_to_Prop in H. exact H. Qed.
Lemma le_Prop_to_mc (m n : nat) : (m <= n)%nat -> is_true (ssrnat.leq m n).
Proof.
  intros H. unfold ssrnat.leq, is_true, eqtype.eq_op. simpl.
  apply Nat.eqb_eq. apply Nat.sub_0_le. exact H.
Qed.
Lemma lt_Prop_to_mc (m n : nat) : (m < n)%nat -> is_true (ssrnat.leq (S m) n).
Proof. intros H. apply le_Prop_to_mc. exact H. Qed.
Import ComplexNumbers.
Import FourierAnalysis.
Import GridOrtho.
Import TPartial.
Import PairDirichlet.
Import CollisionDistance.
Import TChar.

Open Scope R_scope.
Open Scope complex_scope.
Open Scope nat_scope.

Module OrthoCharac.

(* ---------- OC1：正交对逐点归约 ---------- *)

Lemma pair_ortho_rot (a b : R) (k : nat) :
  (rot_atom a k *c Cconj (rot_atom b k) = rot_atom (a - b) k)%C.
Proof.
  rewrite rot_conj_rot. rewrite rot_mul_rot.
  replace (a + - b)%R with (a - b)%R by (ring). reflexivity.
Qed.

(* ---------- OC2：N 个 1 之和 ≠ 0 ---------- *)

Lemma csum_ones (N : nat) :
  (PrimeEmbedding.Csum (fun _ => C1) N = (INR N +i 0))%C.
Proof.
  induction N as [| N IH].
  - reflexivity.
  - replace (INR (S N))%R with (INR N + 1)%R by (destruct N; simpl; lra).
    simpl. rewrite IH. unfold C1, C0, Cadd. simpl.
    f_equal; ring.
Qed.

Lemma csum_ones_neq_0 (N : nat) :
  (1 <= N)%nat -> (PrimeEmbedding.Csum (fun _ => C1) N <> C0)%C.
Proof.
  intros HN H0. rewrite csum_ones in H0.
  unfold C0 in H0. injection H0. intros H1.
  assert (Hn : (N = 0)%nat) by (apply INR_eq_0; exact H1).
  lia.
Qed.

(* ---------- OC3：rot 1 = C1 ⟹ 全部 = C1 ---------- *)

Lemma rot_all_one (theta : R) (K : nat) :
  (rot_atom theta 1 = C1)%C -> (rot_atom theta K = C1)%C.
Proof.
  intros H1. induction K as [| K IH].
  - apply rot_atom_zero.
  - replace (S K)%nat with (K + 1)%nat by (lia).
    rewrite rot_atom_lag_add.
    rewrite IH. rewrite H1. unfold C1, Cmul. simpl. f_equal; ring.
Qed.

(* ---------- OC4：桥梁 ---------- *)

Lemma rot_C1_iff_collides (theta : R) (D : nat) :
  (rot_atom theta D = C1)%C <-> kernel_collides theta D.
Proof.
  split.
  - intros HD d.
    change (phase_rot theta (d + D)) with (rot_atom theta (d + D)).
    change (phase_rot theta d) with (rot_atom theta d).
    rewrite rot_atom_lag_add. rewrite HD. rewrite Cmul_1_r.
    reflexivity.
  - intros H.
    assert (H0 := H 0%nat).
    change (phase_rot theta (0 + D)) with (rot_atom theta (0 + D)) in H0.
    change (phase_rot theta 0) with (rot_atom theta 0) in H0.
    replace (0 + D)%nat with D%nat in H0 by (lia).
    rewrite rot_atom_zero in H0. exact H0.
Qed.

(* ---------- OC5：⟹ 新证 ---------- *)

Theorem ortho_pair_grid_offset (a b : R) (N : nat) :
  (2 <= N)%nat ->
  (PrimeEmbedding.Csum (fun k => rot_atom a k *c Cconj (rot_atom b k)) N = C0)%C ->
  exists m : Z, ((a - b = 2 * PI * IZR m / INR N))%R /\ ((m mod Z.of_nat N <> 0)%Z).
Proof.
  intros HN Hortho.
  assert (Hpt2 : (forall i, is_true (ssrnat.leq (S i) N) ->
       (rot_atom (a - b) i = rot_atom a i *c Cconj (rot_atom b i)))%C).
  { intros i _Hi. symmetry. apply pair_ortho_rot. }
  assert (Hsum : (PrimeEmbedding.Csum (fun k => rot_atom (a - b) k) N = C0)%C).
  { rewrite (Csum_ext (fun k => rot_atom (a - b) k)
                      (fun k => rot_atom a k *c Cconj (rot_atom b k)) N Hpt2).
    exact Hortho. }
  pose proof (geom_sum_identity (a - b) N) as Hg.
  rewrite Hsum in Hg. rewrite Cmul_0_r in Hg.
  assert (HrotN : (rot_atom (a - b) N = C1)%C).
  { unfold Csub, C1, C0, Cadd in Hg. simpl in Hg.
    injection Hg. intros Him Hre.
    unfold C1, rot_atom, Cexp. simpl. f_equal; lra. }
  apply rot_C1_iff_collides in HrotN.
  destruct (proj1 (kernel_collides_iff (a - b) N) HrotN) as [m Hm].
  exists m. split.
  - assert (Hgoal : ((INR N * (a - b) = INR N * (2 * PI * IZR m / INR N)))%R).
    { rewrite Hm. field. intros Hc; assert (Hpos : (0 < INR N)%R) by (apply lt_0_INR; lia); lra. }
    apply (Rmult_eq_reg_l (INR N));
      [ exact Hgoal
      | intros Hc; assert (Hpos : (0 < INR N)%R) by (apply lt_0_INR; lia); lra ].
  - intro Hm0.
    assert (HNz : (Z.of_nat N <> 0)%Z) by (lia).
    pose proof (Z.div_mod m (Z.of_nat N) HNz) as Hq.
    rewrite Hm0 in Hq.
    remember (Z.div m (Z.of_nat N)) as q eqn:Hqdef.
    (* m = N·q, 故 a−b = 2π·IZR q *)
    assert (Habq : (a - b = 2 * PI * IZR q)%R).
    { assert (HmI : (IZR m = INR N * IZR q)%R).
      { rewrite Hq. rewrite plus_IZR. rewrite mult_IZR. rewrite INR_IZR_INZ. simpl. ring. }
      apply (Rmult_eq_reg_l (INR N)).
      * rewrite Hm. rewrite HmI. ring.
      * intros Hc. assert (Hpos : (0 < INR N)%R) by (apply lt_0_INR; lia). lra. }
    assert (Hrot1 : (rot_atom (a - b) 1 = C1)%C).
    { apply (proj2 (rot_C1_iff_collides (a - b) 1)).
      apply (proj2 (kernel_collides_iff (a - b) 1)).
      exists q. rewrite INR_1.
      replace (a - b)%R with (1 * (a - b))%R by (ring).
      rewrite Habq. ring. }
    (* ⟹ 所有 k, rot k = C1 *)
    assert (Hall : (forall k, (k < N)%nat -> (rot_atom (a - b) k = C1))%C).
    { intros k Hk. apply rot_all_one. exact Hrot1. }
    (* ⟹ 和 = N·C1 ≠ C0，与 Hsum 矛盾 *)
    assert (HsumC : (PrimeEmbedding.Csum (fun k => rot_atom (a - b) k) N
                      = PrimeEmbedding.Csum (fun _ => C1) N)%C).
    assert (Hall2 : (forall i, is_true (ssrnat.leq (S i) N) ->
                      (rot_atom (a - b) i = C1))%C).
    { intros i _Hi. apply rot_all_one. exact Hrot1. }
    { apply Csum_ext. exact Hall2. }
    assert (H1N : (1 <= N)%nat) by (lia).
    exact (csum_ones_neq_0 N H1N (eq_trans (eq_sym HsumC) Hsum)).
Qed.

(* ---------- OC6：⟸ ——网格偏移 ⟹ 正交 ---------- *)

Theorem grid_offset_ortho_pair (a b : R) (N : nat) (m : Z) :
  (2 <= N)%nat ->
  ((a - b = 2 * PI * IZR m / INR N))%R ->
  (m mod Z.of_nat N <> 0)%Z ->
  (PrimeEmbedding.Csum (fun k => rot_atom a k *c Cconj (rot_atom b k)) N = C0)%C.
Proof.
  intros HN Hdiff Hm0.
  assert (HNzb : (0 < Z.of_nat N)%Z) by (lia).
  assert (HNz : (Z.of_nat N <> 0)%Z) by (lia).
  pose proof (Z.div_mod m (Z.of_nat N) HNz) as Hq.
  destruct (Z.mod_pos_bound m (Z.of_nat N) HNzb) as [Hp1 Hp2].
  remember (Z.div m (Z.of_nat N)) as q eqn:Hqdef.
  remember ((m mod Z.of_nat N)%Z) as r eqn:Hrdef.
  assert (Hrpos : (0 < r)%Z) by (lia).
  assert (HrN : (r < Z.of_nat N)%Z) by (lia).
  assert (HmI : (IZR m = INR N * IZR q + IZR r)%R).
  { rewrite Hq. rewrite plus_IZR. rewrite mult_IZR. rewrite INR_IZR_INZ. simpl. ring. }
  assert (HrI : (IZR r = INR (Z.to_nat r))%R).
  { rewrite INR_IZR_INZ. f_equal. symmetry. apply Z2Nat.id. lia. }
  assert (Hnrpos : (0 < Z.to_nat r)%nat) by (lia).
  assert (HnrN : (Z.to_nat r < N)%nat) by (lia).
  assert (Hmodne : (Z.to_nat r mod N <> 0)%nat).
  { intro H0. assert (Hs : (Z.to_nat r mod N = Z.to_nat r)%nat)
      by (apply Nat.mod_small; lia). lia. }
  assert (Hmodne' : (Z.to_nat r mod N <> 0 mod N)%nat)
    by (rewrite Nat.mod_0_l; [ exact Hmodne | lia ]).
  pose proof (off_grid_ortho 0%R N (Z.to_nat r) 0%nat (le_Prop_to_mc 2 N HN) Hmodne') as Hoff.
  transitivity (PrimeEmbedding.Csum
                  (fun k => rot_atom (2 * PI * INR (Z.to_nat r) / INR N) k) N).
  - apply Csum_ext. intros i Hi.
    transitivity (rot_atom (a - b) i).
    + apply pair_ortho_rot.
    + replace (a - b)%R
        with (2 * PI * IZR q + 2 * PI * INR (Z.to_nat r) / INR N)%R.
      * assert (Hq1 : (rot_atom (2 * PI * IZR q) i = C1)%C).
        { unfold rot_atom.
          replace (INR i * (2 * PI * IZR q))%R
            with (0 + 2 * PI * IZR (Z.of_nat i * q))%R.
          - rewrite Cexp_2pi_shift. exact Cexp_0.
          - rewrite mult_IZR. rewrite <- INR_IZR_INZ. ring. }
        rewrite (rot_atom_add (2 * PI * IZR q)
                   (2 * PI * INR (Z.to_nat r) / INR N) i).
        rewrite Hq1. apply Cmul_1_l.
      * rewrite Hdiff. rewrite HmI. rewrite HrI. field.
        intros Hc. assert (Hpos : (0 < INR N)%R) by (apply lt_0_INR; lia). lra.
  - transitivity (PrimeEmbedding.Csum
                    (fun k => rot_atom (0 + 2 * PI * INR (Z.to_nat r) / INR N) k
                               *c Cconj (rot_atom (0 + 2 * PI * INR 0 / INR N) k)) N).
    + apply Csum_ext. intros k Hk.
      replace ((0 + 2 * PI * INR (Z.to_nat r) / INR N))%R
        with ((2 * PI * INR (Z.to_nat r) / INR N))%R by (ring).
      replace ((0 + 2 * PI * INR 0 / INR N))%R with 0%R
        by (rewrite INR_0; field; intros Hc; assert (Hpos : (0 < INR N)%R) by (apply lt_0_INR; lia); lra).
      replace (rot_atom 0%R k) with C1.
      * replace (Cconj C1) with C1 by (unfold Cconj, C1; apply Complex_eq; simpl; ring).
        symmetry. apply Cmul_1_r.
      * unfold rot_atom.
        replace (INR k * 0)%R with 0%R by (ring).
        apply (eq_sym Cexp_0).
    + exact Hoff.
Qed.

(* ---------- OC7：逐对 iff（完备刻证的逐对形态，主定理一） ---------- *)

Theorem window_ortho_pairwise_iff (M N : nat) (theta : nat -> R) :
  (2 <= N)%nat ->
  ((forall t u, (t < M)%nat -> (u < M)%nat -> t <> u ->
      (PrimeEmbedding.Csum
         (fun k => rot_atom (theta t) k *c Cconj (rot_atom (theta u) k)) N = C0)%C)
   <-> (forall t u, (t < M)%nat -> (u < M)%nat -> t <> u ->
          exists m : Z, ((theta t - theta u = 2 * PI * IZR m / INR N))%R
                        /\ ((m mod Z.of_nat N <> 0)%Z))).
Proof.
  intros HN. split.
  - intros Hortho t u Ht Hu Htu.
    apply (ortho_pair_grid_offset (theta t) (theta u) N HN).
    apply Hortho; assumption.
  - intros Hdiff t u Ht Hu Htu.
    destruct (Hdiff t u Ht Hu Htu) as [m [Hm Hm0]].
    apply (grid_offset_ortho_pair (theta t) (theta u) N m HN Hm Hm0).
Qed.

(* ---------- OC8：公共偏移形态（⟹，构造性 ∀∃） ---------- *)

Theorem ortho_family_common_offset (M N : nat) (theta : nat -> R) :
  (2 <= N)%nat ->
  (1 <= M)%nat ->
  (forall t u, (t < M)%nat -> (u < M)%nat -> t <> u ->
     (PrimeEmbedding.Csum
        (fun k => rot_atom (theta t) k *c Cconj (rot_atom (theta u) k)) N = C0)%C) ->
  (forall t, (t < M)%nat -> exists mt : Z,
     ((theta t = theta 0%nat + 2 * PI * IZR mt / INR N))%R
     /\ ((t <> 0%nat -> (mt mod Z.of_nat N <> 0)%Z))).
Proof.
  intros HN HM Hortho t Ht.
  assert (H0M : (0 < M)%nat) by (lia).
  destruct (Nat.eq_dec t 0) as [Et | Et].
  - subst t. exists 0%Z. split.
    + replace (2 * PI * IZR Z0 / INR N)%R with 0%R
        by (replace (IZR Z0)%R with 0%R by (reflexivity); field; intros Hc; assert (Hpos : (0 < INR N)%R) by (apply lt_0_INR; lia); lra).
      ring.
    + intros Hne. lia.
  - destruct (ortho_pair_grid_offset (theta t) (theta 0%nat) N HN
                (Hortho t 0%nat Ht H0M Et)) as [mt [Hmt Hmt0]].
    exists mt. split.
    + replace (theta t)%R with ((theta t - theta 0%nat) + theta 0%nat)%R by (ring).
      rewrite Hmt. ring.
    + intros Hne. exact Hmt0.
Qed.

(* ---------- OC9：见证互异（⟹ 补件） ---------- *)

Theorem ortho_family_witness_distinct (M N : nat) (theta : nat -> R) :
  (2 <= N)%nat ->
  (1 <= M)%nat ->
  (forall t u, (t < M)%nat -> (u < M)%nat -> t <> u ->
     (PrimeEmbedding.Csum
        (fun k => rot_atom (theta t) k *c Cconj (rot_atom (theta u) k)) N = C0)%C) ->
  (forall t u, (t < M)%nat -> (u < M)%nat -> t <> u ->
     forall mt mu : Z,
       ((theta t = theta 0%nat + 2 * PI * IZR mt / INR N))%R ->
       ((theta u = theta 0%nat + 2 * PI * IZR mu / INR N))%R ->
       ((mt mod Z.of_nat N <> mu mod Z.of_nat N)%Z)).
Proof.
  intros HN HM Hortho t u Ht Hu Htu mt mu Hmt Hmu.
  assert (H0M : (0 < M)%nat) by (lia).
  destruct (ortho_pair_grid_offset (theta t) (theta u) N HN
              (Hortho t u Ht Hu Htu)) as [d [Hd Hd0]].
  (* θt − θu = 2π·(mt − mu)/N = 2π·d/N ⟹ mt − mu = d ⟹ mod ≠ *)
  assert (Heq : ((mt - mu = d)%Z)).
  { assert (Hr : (2 * PI * IZR (mt - mu) = 2 * PI * IZR d)%R).
    { assert (Ht1 : (INR N * (theta t - theta u) = 2 * PI * IZR d)%R).
      { rewrite Hd. field; intros Hc; assert (Hpos : (0 < INR N)%R) by (apply lt_0_INR; lia); lra. }
      apply (Rmult_eq_reg_l (INR N)).
      * rewrite minus_IZR. rewrite <- Ht1.
        replace (theta t - theta u)%R
          with ((theta 0%nat + 2 * PI * IZR mt / INR N)
                - (theta 0%nat + 2 * PI * IZR mu / INR N))%R by (rewrite Hmt; rewrite Hmu; ring).
        field; intros Hc; assert (Hpos : (0 < INR N)%R) by (apply lt_0_INR; lia); lra.
      * intros Hc; assert (Hpos : (0 < INR N)%R) by (apply lt_0_INR; lia); lra. }
    apply eq_IZR. apply (Rmult_eq_reg_l (2 * PI)).
    + exact Hr.
    + intros Hc; assert (Hp : (0 < 2 * PI)%R)
        by (apply Rmult_lt_0_compat; [ lra | apply PI_RGT_0 ]); lra. }
  intro Hmod.
  assert (Hdm : ((mt - mu) mod Z.of_nat N = 0)%Z).
  { rewrite Zminus_mod. rewrite Hmod. rewrite Z.sub_diag. apply Zmod_0_l. }
  rewrite Heq in Hdm.
  exact (Hd0 Hdm).
Qed.

End OrthoCharac.

Print Assumptions OrthoCharac.ortho_pair_grid_offset.
Print Assumptions OrthoCharac.grid_offset_ortho_pair.
Print Assumptions OrthoCharac.window_ortho_pairwise_iff.
Print Assumptions OrthoCharac.ortho_family_common_offset.
Print Assumptions OrthoCharac.ortho_family_witness_distinct.
