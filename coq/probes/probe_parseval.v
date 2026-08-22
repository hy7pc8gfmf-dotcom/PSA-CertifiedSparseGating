(* ============================================================
   U2 T-PARSEVAL 探针：μ=0 ⟹ 能量守恒等式（z 工作区，E039 纪律）
   前置：probe_grid_ortho（G1-G3、rot_atom/grid_atom、rot_conj_eq_1）。
   库约定（本轮发现，重要）：sum_f_R0 为含端点和（Σ_{k=0}^{N}，N+1 项），
   PE.Csum 为不含端点和（k ∈ [0,N)）——l2_norm_sq 用前者。故窗口以
   "位置 0..n−1" 计时 l2_norm_sq 取 (pred n)，能量值 = INR n。

   主定理 parseval_pair（通用双原子）：
     单位范数原子 + 正交（Csum 口径，n 项窗口）⟹
     l2_norm_sq (c1*u1 + c2*u2) (pred n) = (|c1|²+|c2|²) · INR n
   实例 parseval_two（网格）：窗口 a·N（含全部 2^a 外推长度）。
   —— 等式而非界：框架界定理的退化端点 = Parseval 恒等式。
   ============================================================ *)
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
Import ComplexNumbers.
Import FourierAnalysis.
Import GridOrtho.

Open Scope R_scope.
Open Scope complex_scope.
Open Scope nat_scope.

Module TParseval.

(* ---------- 求和基础设施（sum_f_R0：含端点 Σ_{k=0}^{n}） ---------- *)

Lemma sum_f_R0_ext (f g : nat -> R) (n : nat) :
  (forall k, (f k)%R = (g k)%R) -> (sum_f_R0 f n)%R = (sum_f_R0 g n)%R.
Proof.
  intros H. induction n as [| n IH]; simpl.
  - apply H.
  - rewrite H, IH. reflexivity.
Qed.

Lemma sum_f_R0_plus (f g : nat -> R) (n : nat) :
  (sum_f_R0 (fun k => ((f k) + (g k))%R) n)%R
  = ((sum_f_R0 f n) + (sum_f_R0 g n))%R.
Proof.
  induction n as [| n IH]; simpl; [reflexivity | ].
  rewrite IH. ring.
Qed.

Lemma sum_f_R0_scal (cst : R) (f : nat -> R) (n : nat) :
  (sum_f_R0 (fun k => (cst * (f k))%R) n)%R = ((cst) * (sum_f_R0 f n))%R.
Proof.
  induction n as [| n IH]; simpl; [ring | ].
  rewrite IH. ring.
Qed.

Lemma sum_f_R0_const (n : nat) : (sum_f_R0 (fun _ => 1) n)%R = (INR (S n))%R.
Proof.
  induction n as [| n IH].
  - reflexivity.
  - assert (Hl : (sum_f_R0 (fun _ => 1) (S n))%R
                 = ((sum_f_R0 (fun _ => 1) n) + 1)%R) by reflexivity.
    assert (Hr : (INR (S (S n)))%R = ((INR (S n)) + 1)%R) by reflexivity.
    rewrite Hl, Hr, IH. ring.
Qed.

(* ---------- B1：re-桥（PE.Csum (S n)（k∈[0,n]）↔ sum_f_R0 n） ---------- *)

Lemma re_add (z1 z2 : Complex) : (re (z1 +c z2))%R = ((re z1) + (re z2))%R.
Proof. unfold Cadd. reflexivity. Qed.

Lemma re_Csum_S (f : nat -> Complex) (n : nat) :
  (re (PrimeEmbedding.Csum f (S n)))%R = (sum_f_R0 (fun k => (re (f k))) n)%R.
Proof.
  induction n as [| n IH].
  - assert (Hc0 : PrimeEmbedding.Csum f 1 = Cadd (f 0) C0) by reflexivity.
    assert (Hr0 : (sum_f_R0 (fun k => re (f k)) 0%nat)%R = (re (f 0%nat))%R) by reflexivity.
    assert (H0 : (re C0)%R = 0%R) by reflexivity.
    rewrite Hc0, re_add, Hr0, H0. ring.
  - assert (Hc : PrimeEmbedding.Csum f (S (S n))
                 = Cadd (f (S n)) (PrimeEmbedding.Csum f (S n))) by reflexivity.
    assert (Hs : (sum_f_R0 (fun k => re (f k)) (S n))%R
                 = ((sum_f_R0 (fun k => re (f k)) n) + (re (f (S n))))%R) by reflexivity.
    rewrite Hc, re_add, IH, Hs. ring.
Qed.

(* ---------- Csum 纯量齐次（PE 版） ---------- *)

Lemma Csum_scal (cc : Complex) (f : nat -> Complex) (n : nat) :
  PrimeEmbedding.Csum (fun k => cc *c f k) n = cc *c PrimeEmbedding.Csum f n.
Proof.
  induction n as [| n IH]; simpl.
  - rewrite Cmul_0_r. reflexivity.
  - rewrite Cmul_add_distr_l, IH. reflexivity.
Qed.

(* ---------- A1：原子范数 ---------- *)

Lemma Cnorm_sq_conj (z : Complex) : (Cnorm_sq (Cconj z))%R = (Cnorm_sq z)%R.
Proof.
  unfold Cnorm_sq, Cconj. simpl. unfold Rsqr. ring.
Qed.

Lemma Cnorm_sq_one : (Cnorm_sq C1)%R = 1%R.
Proof. unfold Cnorm_sq. simpl. unfold Rsqr. ring. Qed.

Lemma rot_norm_sq (theta : R) (k : nat) : (Cnorm_sq (rot_atom theta k))%R = 1%R.
Proof.
  assert (H := rot_conj_eq_1 theta k).
  assert (Hs : (Cnorm_sq (rot_atom theta k *c Cconj (rot_atom theta k)))%R = 1%R)
    by (rewrite H; apply Cnorm_sq_one).
  rewrite Cnorm_sq_mult in Hs.
  rewrite Cnorm_sq_conj in Hs.
  assert (Hge : (0 <= Cnorm_sq (rot_atom theta k))%R) by apply Cnorm_sq_ge_0.
  nra.
Qed.

Lemma rot_Cnorm (theta : R) (k : nat) : (Cnorm (rot_atom theta k))%R = 1%R.
Proof.
  unfold Cnorm. rewrite rot_norm_sq, sqrt_1. reflexivity.
Qed.

Lemma grid_norm_sq (N m k : nat) : (2 <= N)%nat -> (Cnorm_sq (grid_atom N m k))%R = 1%R.
Proof.
  intros HN. rewrite <- (rot_grid N m k HN). apply rot_norm_sq.
Qed.

(* ---------- A2/A3：单位原子能量与缩放（l2 口径：W+1 项） ---------- *)

Lemma unit_energy (u : nat -> Complex) (W : nat) :
  (forall k, (Cnorm_sq (u k))%R = 1%R) -> (l2_norm_sq u W)%R = (INR (S W))%R.
Proof.
  intros H. unfold l2_norm_sq.
  rewrite (sum_f_R0_ext _ (fun _ => (1)%R) W) by (intro k; apply H).
  apply sum_f_R0_const.
Qed.

Lemma l2_norm_sq_scale (cc : Complex) (u : nat -> Complex) (W : nat) :
  (l2_norm_sq (fun k => cc *c u k) W)%R
  = ((Cnorm_sq cc) * (l2_norm_sq u W))%R.
Proof.
  unfold l2_norm_sq. induction W as [| W IH]; simpl.
  - rewrite Cnorm_sq_mult. reflexivity.
  - rewrite IH, Cnorm_sq_mult. ring.
Qed.

(* ---------- A4：Cnorm_sq 加法展开 ---------- *)

Lemma re_mul_conj (z1 z2 : Complex) :
  (re (z1 *c Cconj z2))%R = ((re z1) * (re z2) + (im z1) * (im z2))%R.
Proof.
  unfold Cmul, Cconj. simpl. unfold Rsqr. ring.
Qed.

Lemma Cnorm_sq_add (z1 z2 : Complex) :
  (Cnorm_sq (z1 +c z2))%R
  = ((Cnorm_sq z1) + (Cnorm_sq z2)
     + 2 * ((re z1) * (re z2) + (im z1) * (im z2)))%R.
Proof.
  unfold Cnorm_sq, Cadd. simpl. unfold Rsqr. ring.
Qed.

(* ---------- A5：Pythagoras（通用单位范数原子版） ---------- *)

Theorem l2_pythagoras (F u : nat -> Complex) (cc : Complex) (W : nat) :
  (forall k, (Cnorm_sq (u k))%R = 1%R) ->
  (PrimeEmbedding.Csum (fun k => F k *c Cconj (u k)) (S W) = C0) ->
  (l2_norm_sq (fun k => F k +c cc *c u k) W)%R
  = ((l2_norm_sq F W) + (Cnorm_sq cc) * (INR (S W)))%R.
Proof.
  intros Hunit Horth. unfold l2_norm_sq.
  assert (Hpt : forall k, (Cnorm_sq (F k +c cc *c u k))%R
    = ((Cnorm_sq (F k)) + ((Cnorm_sq (cc *c u k))
        + (2 * re (F k *c Cconj (cc *c u k))))%R)%R).
  { intro k. rewrite Cnorm_sq_add, re_mul_conj. ring. }
  rewrite (sum_f_R0_ext (fun k => Cnorm_sq (F k +c cc *c u k))
                 (fun k => ((Cnorm_sq (F k) + (Cnorm_sq (cc *c u k)
                   + 2 * re (F k *c Cconj (cc *c u k)))))%R) W)
    by (intro k; apply Hpt).
  rewrite (sum_f_R0_plus (fun k => (Cnorm_sq (F k))%R)
                 (fun k => ((Cnorm_sq (cc *c u k) + 2 * re (F k *c Cconj (cc *c u k))))%R) W).
  rewrite (sum_f_R0_plus (fun k => (Cnorm_sq (cc *c u k))%R)
                 (fun k => ((2 * re (F k *c Cconj (cc *c u k))))%R) W).
  assert (Hscale : (sum_f_R0 (fun k => Cnorm_sq (cc *c u k)) W)%R
                   = ((Cnorm_sq cc) * (INR (S W)))%R).
  { rewrite <- (unit_energy u W Hunit).
    exact (l2_norm_sq_scale cc u W). }
  rewrite Hscale.
  assert (Hcross : (sum_f_R0 (fun k => 2 * re (F k *c Cconj (cc *c u k))) W)%R
                   = 0%R).
  { rewrite (sum_f_R0_ext _ (fun k => ((2 * re (Cconj cc *c (F k *c Cconj (u k)))))%R) W)
      by (intro k; rewrite Cconj_mul; f_equal; f_equal; apply Cmul_middle_comm).
    rewrite (sum_f_R0_scal (2)%R (fun k => re (Cconj cc *c (F k *c Cconj (u k)))) W).
    rewrite <- (re_Csum_S (fun k => Cconj cc *c (F k *c Cconj (u k))) W).
    rewrite Csum_scal, Horth, Cmul_0_r.
    simpl. ring. }
  rewrite Hcross. ring.
Qed.

(* ---------- A6：双原子 Parseval（通用版 + 网格实例） ---------- *)

Theorem parseval_pair (n : nat) (u1 u2 : nat -> Complex) (c1 c2 : Complex) :
  (0 < n)%nat ->
  (forall k, (Cnorm_sq (u1 k))%R = 1%R) ->
  (forall k, (Cnorm_sq (u2 k))%R = 1%R) ->
  (PrimeEmbedding.Csum (fun k => u1 k *c Cconj (u2 k)) n = C0) ->
  (l2_norm_sq (fun k => c1 *c u1 k +c c2 *c u2 k) (Nat.pred n))%R
  = ((Cnorm_sq c1 + Cnorm_sq c2) * INR n)%R.
Proof.
  intros Hn Hu1 Hu2 Horth.
  destruct n as [| W]; [lia | ].
  change (Nat.pred (S W)) with W.
  (* W = pred n；正交假设在 S W = n 窗口 *)
  assert (HForth : PrimeEmbedding.Csum (fun k => (c1 *c u1 k) *c Cconj (u2 k)) (S W) = C0).
  { rewrite (Csum_ext _ (fun k => c1 *c (u1 k *c Cconj (u2 k))) (S W)).
    - rewrite Csum_scal, Horth, Cmul_0_r. reflexivity.
    - intros k Hk. apply Cmul_assoc. }
  rewrite (l2_pythagoras (fun k => c1 *c u1 k) u2 c2 W Hu2 HForth).
  rewrite (l2_norm_sq_scale c1 u1 W).
  rewrite (unit_energy u1 W Hu1).
  ring.
Qed.

(* 网格实例：窗口 a·N（a=1 训练窗，a=2,4,8 外推长度） *)
Theorem parseval_two (N a m1 m2 : nat) (c1 c2 : Complex) :
  (2 <= N)%nat -> (0 < a)%nat -> (m1 mod N <> m2 mod N)%nat ->
  (l2_norm_sq (fun k => c1 *c grid_atom N m1 k +c c2 *c grid_atom N m2 k)
              (Nat.pred (a * N)))%R
  = ((Cnorm_sq c1 + Cnorm_sq c2) * INR (a * N))%R.
Proof.
  intros HN Ha Hneq.
  apply (parseval_pair (a * N) (grid_atom N m1) (grid_atom N m2) c1 c2);
    [lia | intro k; apply grid_norm_sq; exact HN
          | intro k; apply grid_norm_sq; exact HN | ].
  rewrite (Csum_ext _ (grid_pair N m1 m2) (a * N)).
  - apply grid_ortho_mult; [exact HN | exact Hneq].
  - intros k Hk. unfold grid_pair. reflexivity.
Qed.

End TParseval.

(* ---------- 构造性审计 ---------- *)

Print Assumptions TParseval.l2_pythagoras.
Print Assumptions TParseval.parseval_pair.
Print Assumptions TParseval.parseval_two.
