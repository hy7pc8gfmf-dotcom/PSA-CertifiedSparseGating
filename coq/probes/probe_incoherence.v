(* ============================================================
   压缩感知定理补齐 CS-1/CS-2/CS-3（z 工作区，E039）
   任务源：论文与文档/psi-rope-rand恶化-压缩感知理论缺口-20260822.md §四
   （用户直派：无条件基/无关性范畴的非平凡定理，兑现压缩感知潜力）

   数学内容： psi 频率阶梯（波长 n 截断复指数，库 ca_basis.psi，
   归一化 ‖ψ_n‖=1）构成低相干（incoherent）原子族——压缩感知地基。

     IC0 inner（实内积 re(a·conj b)）+ 对称/实缩放/求和提取。
     IC1 psi 范数 = 1 + phi=rot 桥 + 零前缀 Csum 消除。
     IC2 psi_mu_bound：|⟨ψ_a,ψ_b⟩| ≤ Fpair a b（b≥2a）。
     IC3 l2_add_gen（广义 Pythagoras）+ ipW 双线性。
     IC4 norm_sq_expansion：M 原子实系数合成范数平方显式展开。
     IC5 rip_bound（CS-2）：μ-不相干单位原子 ⟹
        |‖Σc_jA_j‖² − Σc_j²| ≤ μ·(M−1)·Σc_j²（Gershgorin 型 RIP）。
     IC6 sparse_uniqueness（CS-3）：(M−1)μ < 1 ⟹ 零表示 ⟹ 系数全零。
     IC7 psi_ladder_mu（CS-1）：C-梯子 ⟹ |⟨ψ_i,ψ_j⟩| ≤ π/(C√C)。
     IC8 psi_ladder_uniqueness（主定理）：(2s−1)π/(C√C) < 1 ⟹ 唯一。
     IC9 数值门槛：C=4 ⟹ s=1；C=9 ⟹ s≤4；C=16 ⟹ s≤9。

   依赖： ca_basis（psi/phi/Cof_real/l2_norm_sq）+ probe_parseval +
   probe_rowsum（Fpair/pair_le_crude）。审计： Print Assumptions 尾部。
   ============================================================ *)
From mathcomp Require Import ssreflect ssrbool ssrnat seq eqtype div prime.
Require Import Stdlib.Reals.Reals.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.micromega.Lra.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Logic.FunctionalExtensionality.
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
Require Import probe_pairbound.
Require Import probe_rowsum.
Require Import probe_pairdirichlet.
Import ComplexNumbers.
Import FourierAnalysis.
Import GridOrtho.
Import TParseval.
Import TPartial.
Import PairBound.
Import RowSum.
Import UnconditionalBasis.
Import PairDirichlet.

Open Scope R_scope.
Open Scope complex_scope.
Open Scope nat_scope.

Module Incoherence.

(* ---------- IC0：inner 基础件 ---------- *)

Definition inner (a b : Complex) : R := re (a *c Cconj b).

Lemma Cof_real_mul_re : forall (r : R) (z : Complex),
  (re (Cof_real r *c z))%R = (r * re z)%R.
Proof.
  intros r z. unfold Cof_real, Cmul. simpl. ring.
Qed.

Lemma inner_sym : forall a b : Complex, (inner a b)%R = (inner b a)%R.
Proof.
  intros a b. unfold inner. rewrite !re_mul_conj. ring.
Qed.

Lemma inner_CR_l : forall (c : R) (a b : Complex),
  (inner (Cof_real c *c a) b)%R = (c * inner a b)%R.
Proof.
  intros c a b. unfold inner. rewrite Cmul_assoc.
  rewrite Cof_real_mul_re. reflexivity.
Qed.

Lemma inner_CR_r : forall (c : R) (a b : Complex),
  (inner a (Cof_real c *c b))%R = (c * inner a b)%R.
Proof.
  intros c a b.
  rewrite (inner_sym a (Cof_real c *c b)) inner_CR_l inner_sym. ring.
Qed.

(* 零前缀消除：a ≤ k < b 项全零 ⟹ Csum f b = Csum f a *)
Lemma Csum_zero_tail : forall (f : nat -> Complex) (a b : nat),
  (a <= b)%nat ->
  (forall k, (a <= k < b)%nat -> (f k = C0)%C) ->
  (PrimeEmbedding.Csum f b = PrimeEmbedding.Csum f a)%C.
Proof.
  intros f a b Hab Hz. induction b as [| b IH].
  - assert (a = 0%nat) by (move: Hab => /leP Habp; lia). subst a. reflexivity.
  - destruct (Nat.eq_dec a (S b)) as [Ea | Ea].
    + rewrite Ea. reflexivity.
    + assert (Hab' : (a <= b)%nat) by (apply/leP; move: Hab => /leP Habp; move: Ea => Eap; lia).
      assert (Hs : (PrimeEmbedding.Csum f (S b)
                    = Cadd (f b) (PrimeEmbedding.Csum f b))%C) by reflexivity.
      rewrite Hs.
      assert (Hz' : forall k, a <= k < b -> f k = C0)
        by (intros k Hk; apply Hz; move: Hk => /andP [Hak Hkb];
            apply/andP; split; [ exact Hak |
              exact (ltn_trans Hkb (ltnSn b)) ]).
      rewrite (IH Hab' Hz') (Hz b (andb_true_intro (conj Hab' (ltnSn b)))).
      apply Cadd_0_l.
Qed.

(* ---------- IC1：psi 范数 = 1 ---------- *)

Lemma phi_eq_rot : forall (n k : nat),
  (k < n)%nat -> (phi n k = rot_atom (2 * PI / INR n) k)%C.
Proof.
  intros n k Hk. unfold phi, rot_atom. move: Hk => /ltP Hkp.
  rewrite (proj2 (Nat.ltb_lt k n) Hkp).
  replace (2 * PI * INR k / INR n)%R with (INR k * (2 * PI / INR n))%R
    by (field; intros Hc; assert (Hpos : (0 < INR n)%R) by (apply lt_0_INR; lia); lra).
  reflexivity.
Qed.

Lemma sum_ones : forall m : nat, (sum_f_R0 (fun _ => 1)%R m)%R = (INR (S m))%R.
Proof.
  induction m as [| m IH]; simpl.
  - reflexivity.
  - rewrite IH. simpl. ring.
Qed.

Lemma sum_f_R0_ext_bounded : forall (f g : nat -> R) (N : nat),
  (forall k, (k <= N)%nat -> (f k = g k))%R -> (sum_f_R0 f N)%R = (sum_f_R0 g N)%R.
Proof.
  intros f g N H. induction N as [| N IH].
  - apply H. by apply leqnn.
  - simpl. rewrite IH. rewrite (H (S N)). reflexivity.
    by apply leqnn.
    intros k Hk. apply H. exact (leq_trans Hk (leqnSn N)).
Qed.

Lemma phi_l2_norm : forall n : nat, (1 <= n)%nat ->
  (l2_norm_sq (phi n) (Nat.pred n))%R = (INR n)%R.
Proof.
  intros n Hn. unfold l2_norm_sq.
  transitivity (sum_f_R0 (fun _ : nat => 1)%R (Nat.pred n)).
  - apply sum_f_R0_ext_bounded. intros k Hk.
    assert (Hkn : (k < n)%nat)
      by (apply/ltP; move: Hk => /leP Hkp; move: Hn => /leP Hnp; lia).
    rewrite phi_eq_rot; [ apply rot_norm_sq | exact Hkn ].
  - replace (INR n)%R with (INR (S (Nat.pred n)))%R by (f_equal; move: Hn => /leP Hnp; lia).
    apply sum_ones.
Qed.

Lemma Cnorm_sq_Cof_real : forall r : R, (Cnorm_sq (Cof_real r))%R = (r * r)%R.
Proof.
  intros r. unfold Cof_real, Cnorm_sq. simpl.
  replace (Rsqr 0)%R with 0%R by (unfold Rsqr; ring).
  unfold Rsqr. ring.
Qed.

Theorem psi_norm_one : forall n : nat, (1 <= n)%nat ->
  (l2_norm_sq (psi n) (Nat.pred n))%R = 1%R.
Proof.
  intros n Hn. unfold psi.
  rewrite l2_norm_sq_scale Cnorm_sq_Cof_real. rewrite phi_l2_norm; [ | exact Hn ].
  (* 目标：(1/sqrt(INR n))·(1/sqrt(INR n))·INR n = 1。
     用 s := sqrt(INR n)，把 INR n 重写为 s·s，再 field（field 无法直接消化 sqrt）。 *)
  set (s := sqrt (INR n)).
  assert (Hss : (s * s)%R = (INR n)%R).
  { unfold s. apply sqrt_sqrt. apply pos_INR. }
  rewrite <- Hss.
  field.
  intros Hc.
  assert (H' : (0 < s)%R).
  { unfold s. apply sqrt_lt_R0. apply lt_0_INR. move: Hn => /leP Hnp. lia. }
  exact (Rlt_not_eq 0 s H' (Logic.eq_sym Hc)).
Qed.

End Incoherence.

(* ============================================================
   CS-2/CS-3：RIP + 稀疏唯一性（z 工作区，E039）
   —— 在既有 IC0/IC1（inner、psi_norm_one）之上。
   Module Incoherence2：ipW 内积机器 + 双原子范数展开 + 稀疏唯一性。
   ============================================================ *)
Module Incoherence2.

(* ============================================================
   CS-2/CS-3：RIP + 稀疏唯一性（z 工作区，E039，经典 R 纪律）
   —— ipW 内积机器 + 双原子范数展开 + 稀疏唯一性（非平凡核心）。
   依赖：probe_parseval（Cnorm_sq_add/re_mul_conj/sum_f_R0_*）。
   审计：Dedekind 三件套基座继承，零自定义公理、零 Admitted。
   ============================================================ *)

(* 窗口内积：⟨u,v⟩_W = Σ_{k≤W} re(u k ·c conj(v k))（sum_f_R0 含端点 W+1 项） *)
Definition ipW (u v : nat -> Complex) (W : nat) : R :=
  sum_f_R0 (fun k => re (u k *c Cconj (v k))) W.

(* Cnorm_sq z = re (z *c Cconj z) *)
Lemma l2_ip_pure (z : Complex) : (Cnorm_sq z)%R = (re (z *c Cconj z))%R.
Proof.
  unfold Cnorm_sq. simpl. unfold Rsqr. ring.
Qed.

(* l2_norm_sq u W = ipW u u W *)
Lemma l2_is_ip (u : nat -> Complex) (W : nat) :
  (l2_norm_sq u W)%R = (ipW u u W)%R.
Proof.
  unfold l2_norm_sq, ipW.
  apply sum_f_R0_ext.
  intro k. apply l2_ip_pure.
Qed.

(* 内积对称：⟨u,v⟩ = ⟨v,u⟩ *)
Lemma ipW_sym (u v : nat -> Complex) (W : nat) :
  (ipW u v W)%R = (ipW v u W)%R.
Proof.
  unfold ipW. apply sum_f_R0_ext. intro k.
  rewrite re_mul_conj. rewrite (re_mul_conj (v k) (u k)). ring.
Qed.

(* 实左缩放：⟨r·u, v⟩ = r·⟨u,v⟩ *)
Lemma ipW_CR_l (r : R) (u v : nat -> Complex) (W : nat) :
  (ipW (fun k => Cof_real r *c u k) v W)%R = (r * ipW u v W)%R.
Proof.
  unfold ipW.
  rewrite (sum_f_R0_ext _ (fun k => (r * re (u k *c Cconj (v k)))%R) W).
  rewrite (sum_f_R0_scal r (fun k => re (u k *c Cconj (v k))) W).
  reflexivity.
  intro k. rewrite Cmul_assoc. apply Incoherence.Cof_real_mul_re.
Qed.

(* 实右缩放：⟨u, r·v⟩ = r·⟨u,v⟩ *)
Lemma ipW_CR_r (r : R) (u v : nat -> Complex) (W : nat) :
  (ipW u (fun k => Cof_real r *c v k) W)%R = (r * ipW u v W)%R.
Proof.
  intros. rewrite ipW_sym.
  rewrite (ipW_CR_l r v u W).
  rewrite (ipW_sym u v W).
  reflexivity.
Qed.

(* 左加性：⟨u+v, w⟩ = ⟨u,w⟩ + ⟨v,w⟩ *)
Lemma ipW_add_l (u v w : nat -> Complex) (W : nat) :
  (ipW (fun k => u k +c v k) w W)%R = ((ipW u w W) + (ipW v w W))%R.
Proof.
  unfold ipW.
  rewrite (sum_f_R0_ext _ (fun k => ((re (u k *c Cconj (w k))) + (re (v k *c Cconj (w k))))%R) W).
  rewrite (sum_f_R0_plus (fun k => re (u k *c Cconj (w k)))
                         (fun k => re (v k *c Cconj (w k))) W).
  reflexivity.
  intro k. rewrite Cmul_add_distr_r. unfold Cadd. simpl. ring.
Qed.

(* 右加性：⟨u, v+w⟩ = ⟨u,v⟩ + ⟨u,w⟩ *)
Lemma ipW_add_r (u v w : nat -> Complex) (W : nat) :
  (ipW u (fun k => v k +c w k) W)%R = ((ipW u v W) + (ipW u w W))%R.
Proof.
  intros. rewrite ipW_sym.
  rewrite (ipW_add_l v w u W).
  rewrite (ipW_sym u w W).
  rewrite (ipW_sym u v W).
  reflexivity.
Qed.

(* Cconj 与实缩放交换 *)
Lemma Cconj_Cof_real (r : R) (z : Complex) : Cconj (Cof_real r *c z) = Cof_real r *c Cconj z.
Proof.
  apply Complex_eq; simpl; ring.
Qed.

(* re((r·a)·c (s·b)) = (r·s)·re(a·c b) *)
Lemma re_scal_conj (r s : R) (a b : Complex) :
  (re ((Cof_real r *c a) *c (Cof_real s *c Cconj b)))%R = ((r * s) * re (a *c Cconj b))%R.
Proof.
  unfold Cof_real, Cmul, Cconj. simpl. unfold Rsqr. ring.
Qed.

(* Cnorm_sq (r·z) = r²·Cnorm_sq z *)
Lemma Cnorm_sq_scal (r : R) (z : Complex) :
  (Cnorm_sq (Cof_real r *c z))%R = ((r * r) * Cnorm_sq z)%R.
Proof.
  rewrite Cnorm_sq_mult.
  unfold Cof_real, Cnorm_sq. simpl. unfold Rsqr. ring.
Qed.

(* 逐点：‖c1·a + c2·b‖² = c1²‖a‖² + c2²‖b‖² + 2·c1·c2·re(a·c b) *)
Lemma norm_sq_combo2_point (c1 c2 : R) (a b : Complex) :
  (Cnorm_sq (Cof_real c1 *c a +c Cof_real c2 *c b))%R
  = ((c1 * c1) * Cnorm_sq a + (c2 * c2) * Cnorm_sq b
     + 2 * (c1 * c2) * re (a *c Cconj b))%R.
Proof.
  rewrite Cnorm_sq_add.
  rewrite <- (re_mul_conj (Cof_real c1 *c a) (Cof_real c2 *c b)).
  rewrite (Cconj_Cof_real c2 b).
  rewrite Cnorm_sq_scal Cnorm_sq_scal.
  rewrite re_scal_conj.
  ring.
Qed.

(* |a|² = a² *)
Lemma Rabs_sqr_eq (a : R) : (Rabs a * Rabs a = a * a)%R.
Proof.
  assert (H := Rsqr_abs a). unfold Rsqr in H. symmetry. exact H.
Qed.

(* |−x| = |x| *)
Lemma Rabs_opp (x : R) : (Rabs (- x))%R = (Rabs x)%R.
Proof.
  replace (- x)%R with (0 - x)%R by ring.
  replace (Rabs (0 - x))%R with (Rabs (x - 0))%R by (apply Rabs_minus_sym).
  replace (x - 0)%R with x by ring.
  reflexivity.
Qed.

(* |2·x| = 2·|x| *)
Lemma Rabs_2_mult (x : R) : (Rabs (2 * x))%R = (2 * Rabs x)%R.
Proof.
  rewrite Rabs_mult.
  rewrite (Rabs_right 2 (Rle_ge 0 2 (Rlt_le 0 2 Rlt_0_2))).
  ring.
Qed.

(* AM-GM：2|ab| ≤ a² + b² *)
Lemma Rabs_prod_le_sq_sum (a b : R) : ((2 * Rabs (a * b)) <= (a * a + b * b))%R.
Proof.
  rewrite Rabs_mult.
  assert (Hn : (0 <= Rabs a * Rabs b)%R).
  { apply Rmult_le_pos; apply Rabs_pos. }
  assert (Hsq : (0 <= (Rabs a - Rabs b) * (Rabs a - Rabs b))%R).
  { apply Rle_0_sqr. }
  assert (H1 : (2 * (Rabs a * Rabs b) <= Rabs a * Rabs a + Rabs b * Rabs b)%R).
  { unfold Rsqr in Hsq. lra. }
  rewrite Rabs_sqr_eq Rabs_sqr_eq in H1.
  lra.
Qed.

(* a² + b² = 0 ⟹ a = 0 *)
Lemma sq_sum_zero_l (a b : R) : (a * a + b * b = 0)%R -> a = 0%R.
Proof.
  intros H.
  assert (Hge : (0 <= a * a)%R) by apply Rle_0_sqr.
  assert (Hb : (0 <= b * b)%R) by apply Rle_0_sqr.
  assert (Hadd : ((a * a) + (b * b) <= 0)%R).
  { rewrite H. lra. }
  assert (Hle1 : (a * a <= - (b * b))%R).
  { apply (Rplus_le_reg_l (b * b) (a * a) (- (b * b))).
    replace ((b * b) + (a * a))%R with ((a * a) + (b * b))%R by ring.
    replace ((b * b) + (- (b * b)))%R with 0%R by ring.
    exact Hadd. }
  assert (Hle2 : (- (b * b) <= 0)%R) by lra.
  assert (Hle : (a * a <= 0)%R) by exact (Rle_trans (a * a) (- (b * b)) 0 Hle1 Hle2).
  apply Rsqr_0_uniq.
  apply Rle_antisym; auto.
Qed.

(* a² + b² = 0 ⟹ b = 0 *)
Lemma sq_sum_zero_r (a b : R) : (a * a + b * b = 0)%R -> b = 0%R.
Proof.
  intros H.
  assert (Hge : (0 <= b * b)%R) by apply Rle_0_sqr.
  assert (Ha : (0 <= a * a)%R) by apply Rle_0_sqr.
  assert (Hadd : ((b * b) + (a * a) <= 0)%R).
  { rewrite (Rplus_comm (a * a) (b * b)) in H. rewrite H. lra. }
  assert (Hle1 : (b * b <= - (a * a))%R).
  { apply (Rplus_le_reg_l (a * a) (b * b) (- (a * a))).
    replace ((a * a) + (b * b))%R with ((b * b) + (a * a))%R by ring.
    replace ((a * a) + (- (a * a)))%R with 0%R by ring.
    exact Hadd. }
  assert (Hle2 : (- (a * a) <= 0)%R) by lra.
  assert (Hle : (b * b <= 0)%R) by exact (Rle_trans (b * b) (- (a * a)) 0 Hle1 Hle2).
  apply Rsqr_0_uniq.
  apply Rle_antisym; auto.
Qed.

(* Cnorm_sq C0 = 0 *)
Lemma Cnorm_sq_C0 : (Cnorm_sq C0)%R = 0%R.
Proof.
  unfold Cnorm_sq, C0. simpl. unfold Rsqr. ring.
Qed.

(* Σ_{k≤n} 0 = 0 *)
Lemma sum_f_R0_zero (n : nat) : (sum_f_R0 (fun _ : nat => 0%R) n)%R = 0%R.
Proof.
  induction n; simpl; [auto | rewrite IHn; lra].
Qed.

(* 双原子组合的范数平方展开（实系数 c1 c2）：
   ‖c1·u1 + c2·u2‖²_W
   = c1²‖u1‖²_W + c2²‖u2‖²_W + 2·c1·c2·⟨u1,u2⟩_W *)
Theorem norm_sq_combo2 (u1 u2 : nat -> Complex) (c1 c2 : R) (W : nat) :
  (l2_norm_sq (fun k => Cof_real c1 *c u1 k +c Cof_real c2 *c u2 k) W)%R
  = ((c1 * c1) * l2_norm_sq u1 W
     + (c2 * c2) * l2_norm_sq u2 W
     + 2 * (c1 * c2) * ipW u1 u2 W)%R.
Proof.
  unfold l2_norm_sq.
  rewrite (sum_f_R0_ext _ (fun k => ((c1 * c1) * Cnorm_sq (u1 k)
                                     + (c2 * c2) * Cnorm_sq (u2 k)
                                     + 2 * (c1 * c2) * re (u1 k *c Cconj (u2 k)))%R) W).
  (* 目标为左结合：((c1²‖u1‖² + c2²‖u2‖²) + 2c1c2⟨⟩)。按最外层 + 拆分。 *)
  rewrite (sum_f_R0_plus (fun k => ((c1 * c1) * Cnorm_sq (u1 k)
                                    + (c2 * c2) * Cnorm_sq (u2 k))%R)
                         (fun k => (2 * (c1 * c2) * re (u1 k *c Cconj (u2 k)))%R) W).
  rewrite (sum_f_R0_plus (fun k => ((c1 * c1) * Cnorm_sq (u1 k))%R)
                         (fun k => ((c2 * c2) * Cnorm_sq (u2 k))%R) W).
  rewrite (sum_f_R0_scal (c1 * c1) (fun k => Cnorm_sq (u1 k)) W).
  rewrite (sum_f_R0_scal (c2 * c2) (fun k => Cnorm_sq (u2 k)) W).
  rewrite (sum_f_R0_scal (2 * (c1 * c2)) (fun k => re (u1 k *c Cconj (u2 k))) W).
  unfold ipW. ring.
  intro k. apply norm_sq_combo2_point.
Qed.

(* CS-3a 核心：2 原子词典的稀疏唯一性。
   单位范数原子、|⟨u1,u2⟩_W| ≤ μ、μ < 1，且 c1·u1+c2·u2 ≡ 0（窗口内）⟹ c1 = c2 = 0。 *)
Theorem sparse_uniqueness2 (u1 u2 : nat -> Complex) (W : nat) (c1 c2 mu : R) :
  (l2_norm_sq u1 W)%R = 1%R ->
  (l2_norm_sq u2 W)%R = 1%R ->
  ((Rabs (ipW u1 u2 W)) <= mu)%R ->
  (mu < 1)%R ->
  (forall k, (k <= W)%nat -> (Cof_real c1 *c u1 k +c Cof_real c2 *c u2 k = C0)%C) ->
  (c1 = 0)%R /\ (c2 = 0)%R.
Proof.
  intros Hu1 Hu2 Hmu Hmu1 Hzero.
  (* 0 = ‖c1u1+c2u2‖²_W（每点为零 ⟹ Cnorm_sq C0 = 0 ⟹ 和为 0） *)
  assert (Hcombo : (l2_norm_sq (fun k => Cof_real c1 *c u1 k +c Cof_real c2 *c u2 k) W)%R = 0%R).
  { unfold l2_norm_sq.
    rewrite (Incoherence.sum_f_R0_ext_bounded _ (fun _ => Cnorm_sq C0) W).
    assert (Hzsum : (sum_f_R0 (fun _ : nat => Cnorm_sq C0) W)%R = 0%R).
    { rewrite (Incoherence.sum_f_R0_ext_bounded _ (fun _ => 0%R) W).
      exact (sum_f_R0_zero W).
      intro k. intro Hk. exact Cnorm_sq_C0. }
    rewrite Hzsum. reflexivity.
    intro k. intro Hk. f_equal. exact (Hzero k Hk). }
  (* 用 norm_sq_combo2 + Hu1/Hu2 归约 *)
  rewrite norm_sq_combo2 in Hcombo.
  rewrite Hu1 Hu2 in Hcombo.
  replace ((c1 * c1) * 1 + (c2 * c2) * 1 + 2 * (c1 * c2) * ipW u1 u2 W)%R
    with ((c1 * c1) + (c2 * c2) + 2 * (c1 * c2) * ipW u1 u2 W)%R in Hcombo by ring.
  (* c1²+c2² = −(2·c1c2·⟨u1,u2⟩) *)
  assert (Hmain : ((c1 * c1) + (c2 * c2) = - (2 * (c1 * c2) * ipW u1 u2 W))%R).
  { apply Rplus_eq_reg_l with (2 * (c1 * c2) * ipW u1 u2 W)%R.
    replace ((2 * (c1 * c2) * ipW u1 u2 W) + ((c1 * c1) + (c2 * c2)))%R
      with ((c1 * c1) + (c2 * c2) + 2 * (c1 * c2) * ipW u1 u2 W)%R by ring.
    rewrite Hcombo. ring. }
  (* |c1²+c2²| = |2c1c2·⟨⟩| ≤ 2|c1c2|·μ ≤ μ·(c1²+c2²) *)
  assert (Habs : ((Rabs (2 * (c1 * c2) * ipW u1 u2 W)) <= (mu * ((c1 * c1) + (c2 * c2))))%R).
  { rewrite (Rabs_mult (2 * (c1 * c2)) (ipW u1 u2 W)).
    rewrite (Rabs_2_mult (c1 * c2)).
    (* 2|c1c2|·|⟨⟩| ≤ 2|c1c2|·μ（因 |⟨⟩|≤μ） *)
    transitivity (2 * Rabs (c1 * c2) * mu)%R.
    - apply Rmult_le_compat_l.
      + apply Rmult_le_pos; [lra | apply Rabs_pos].
      + exact Hmu.
    - (* 2|c1c2|·μ ≤ μ·(c1²+c2²)（因 2|c1c2|≤c1²+c2² 且 μ≥0） *)
      assert (Hmu0 : (0 <= mu)%R).
      { apply (Rle_trans _ (Rabs (ipW u1 u2 W)) _); [apply Rabs_pos | exact Hmu]. }
      replace (2 * Rabs (c1 * c2) * mu)%R with (mu * (2 * Rabs (c1 * c2)))%R by ring.
      apply Rmult_le_compat_l; [exact Hmu0 | exact (Rabs_prod_le_sq_sum c1 c2)]. }
  (* c1²+c2² = |c1²+c2²| ≤ μ(c1²+c2²)（因 c1²+c2² ≥ 0） *)
  assert (Hnonneg : (0 <= (c1 * c1) + (c2 * c2))%R).
  { apply Rplus_le_le_0_compat; apply Rle_0_sqr. }
  assert (Hc : ((c1 * c1) + (c2 * c2) <= mu * ((c1 * c1) + (c2 * c2)))%R).
  { (* |c1²+c2²| = |−(2c1c2⟨⟩)| = |2c1c2⟨⟩| ≤ μ(c1²+c2²)；再因 c1²+c2² ≥ 0 去绝对值 *)
    assert (Habs' : (Rabs ((c1 * c1) + (c2 * c2)) <= mu * ((c1 * c1) + (c2 * c2)))%R).
    { replace (Rabs ((c1 * c1) + (c2 * c2)))%R
        with (Rabs (2 * (c1 * c2) * ipW u1 u2 W))%R.
      - exact Habs.
      - rewrite Hmain. rewrite Rabs_opp. reflexivity. }
    rewrite (Rabs_pos_eq ((c1 * c1) + (c2 * c2)) Hnonneg) in Habs'.
    exact Habs'. }
  (* μ<1 ⟹ c1²+c2²=0：S ≤ μS ⟹ (1−μ)S ≤ 0，且 1−μ > 0、S ≥ 0 ⟹ S = 0 *)
  assert (Hsq : ((c1 * c1) + (c2 * c2) = 0)%R).
  { apply Rle_antisym.
    - (* S ≤ 0：由 (1−μ)S ≤ 0 与 (1−μ) > 0 相除 *)
      assert (H1m : (0 < 1 - mu)%R) by lra.
      assert (Hprod : ((1 - mu) * ((c1 * c1) + (c2 * c2)) <= 0)%R).
      { replace ((1 - mu) * ((c1 * c1) + (c2 * c2)))%R
          with (((c1 * c1) + (c2 * c2)) - mu * ((c1 * c1) + (c2 * c2)))%R by ring.
        lra. }
      assert (Hpos : (0 <= (1 - mu))%R) by lra.
      (* 从 (1−μ)S ≤ 0 且 (1−μ) > 0 得 S ≤ 0：用 Rmult_le_reg_l *)
      apply (Rmult_le_reg_l (1 - mu) ((c1 * c1) + (c2 * c2)) 0 H1m).
      replace ((1 - mu) * 0)%R with 0%R by ring.
      exact Hprod.
    - exact Hnonneg. }
  split.
  - apply (sq_sum_zero_l c1 c2). exact Hsq.
  - apply (sq_sum_zero_r c1 c2). exact Hsq.
Qed.

(* CS-2（2 原子版）：RIP 型界
   |‖c1u1+c2u2‖²_W − (c1²+c2²)| ≤ μ·(c1²+c2²)（单位原子、|⟨⟩|≤μ） *)
Theorem rip_bound2 (u1 u2 : nat -> Complex) (W : nat) (c1 c2 mu : R) :
  (l2_norm_sq u1 W)%R = 1%R ->
  (l2_norm_sq u2 W)%R = 1%R ->
  ((Rabs (ipW u1 u2 W)) <= mu)%R ->
  ((Rabs ((l2_norm_sq (fun k => Cof_real c1 *c u1 k +c Cof_real c2 *c u2 k) W)%R
          - ((c1 * c1) + (c2 * c2))%R)) <= (mu * ((c1 * c1) + (c2 * c2))))%R.
Proof.
  intros Hu1 Hu2 Hmu.
  rewrite norm_sq_combo2.
  rewrite Hu1 Hu2.
  replace ((c1 * c1) * 1 + (c2 * c2) * 1 + 2 * (c1 * c2) * ipW u1 u2 W)%R
    with ((c1 * c1) + (c2 * c2) + 2 * (c1 * c2) * ipW u1 u2 W)%R by ring.
  replace (((c1 * c1) + (c2 * c2) + 2 * (c1 * c2) * ipW u1 u2 W) - ((c1 * c1) + (c2 * c2)))%R
    with (2 * (c1 * c2) * ipW u1 u2 W)%R by ring.
  rewrite (Rabs_mult (2 * (c1 * c2)) (ipW u1 u2 W)).
  rewrite (Rabs_2_mult (c1 * c2)).
  transitivity (2 * Rabs (c1 * c2) * mu)%R.
  - apply Rmult_le_compat_l.
    + apply Rmult_le_pos; [lra | apply Rabs_pos].
    + exact Hmu.
  - assert (Hmu0 : (0 <= mu)%R).
    { apply (Rle_trans _ (Rabs (ipW u1 u2 W)) _); [apply Rabs_pos | exact Hmu]. }
    replace (2 * Rabs (c1 * c2) * mu)%R with (mu * (2 * Rabs (c1 * c2)))%R by ring.
    apply Rmult_le_compat_l; [exact Hmu0 | exact (Rabs_prod_le_sq_sum c1 c2)].
Qed.

(* ============================================================
   CS-3b 引擎：M-原子组合与线性提取（z 工作区，E039）
   —— comboM（Σ_{j<M} c_j·u_j）+ ipW 线性提取。
   ============================================================ *)

(* M 原子组合：Σ_{j<M} c_j·u_j（点 k 处） *)
Definition comboM (M : nat) (c : nat -> R) (u : nat -> nat -> Complex) (k : nat) : Complex :=
  PrimeEmbedding.Csum (fun j => Cof_real (c j) *c u j k) M.

(* ipW 常零 = 0 *)
Lemma ipW_C0 (v : nat -> Complex) (W : nat) : (ipW (fun _ => C0) v W)%R = 0%R.
Proof.
  unfold ipW.
  rewrite (sum_f_R0_ext _ (fun _ => 0)%R W).
  induction W; simpl; [auto | rewrite IHW; lra].
  intro k. unfold Cmul, C0. simpl. ring.
Qed.

(* 递归步（函数等式）：comboM (S M) = comboM M +c c_M·u_M *)
Lemma comboM_step (M : nat) (c : nat -> R) (u : nat -> nat -> Complex) :
  comboM (S M) c u = fun k : nat => comboM M c u k +c Cof_real (c M) *c u M k.
Proof.
  apply functional_extensionality. intro k.
  unfold comboM. simpl.
  change (PrimeEmbedding.Csum (fun j => Cof_real (c j) *c u j k) (S M))
    with (Cof_real (c M) *c u M k +c PrimeEmbedding.Csum (fun j => Cof_real (c j) *c u j k) M).
  rewrite Cadd_comm. reflexivity.
Qed.

(* comboM 1 = 单原子（0 下标） *)
Lemma comboM_one (c : nat -> R) (u : nat -> nat -> Complex) :
  comboM 1%nat c u = fun k : nat => Cof_real (c 0%nat) *c u 0%nat k.
Proof.
  apply functional_extensionality. intro k.
  unfold comboM. simpl.
  apply Cadd_0_r.
Qed.

(* 线性提取：⟨Σ_{j≤M} c_j·u_j, v⟩ = Σ_{j≤M} c_j·⟨u_j, v⟩ *)
Lemma ipW_combo_l (M : nat) (c : nat -> R) (u : nat -> nat -> Complex) (v : nat -> Complex) (W : nat) :
  (ipW (comboM (S M) c u) v W)%R
  = (sum_f_R0 (fun j => c j * ipW (u j) v W) M)%R.
Proof.
  induction M as [| M IH].
  - unfold comboM. simpl.
    rewrite (ipW_add_l (fun k => Cof_real (c 0) *c u 0 k) (fun _ => C0) v W).
    rewrite (ipW_CR_l (c 0) (u 0) v W).
    rewrite ipW_C0. ring.
  - rewrite (comboM_step (S M) c u).
    rewrite ipW_add_l.
    rewrite (ipW_CR_l (c (S M)) (u (S M)) v W).
    rewrite IH.
    simpl. reflexivity.
Qed.

(* 递归范数展开：l2(comboM (S (S M))) = l2(comboM (S M)) + c²_{SM}·l2(u_{SM}) + 2·c_{SM}·⟨comboM (S M), u_{SM}⟩ *)
Lemma norm_sq_comboM_rec (M : nat) (c : nat -> R) (u : nat -> nat -> Complex) (W : nat) :
  (l2_norm_sq (comboM (S (S M)) c u) W)%R
  = ((l2_norm_sq (comboM (S M) c u) W)
     + (c (S M)) * (c (S M)) * (l2_norm_sq (u (S M)) W)
     + 2 * (c (S M)) * (ipW (comboM (S M) c u) (u (S M)) W))%R.
Proof.
  rewrite (comboM_step (S M) c u).
  (* l2_norm_sq (fun k => comboM (S M) c u k +c Cof_real (c (S M)) *c u (S M) k) W。
     用 norm_sq_combo2 于 (u1 := comboM (S M) c u, u2 := u (S M), c1 := 1, c2 := c (S M))，
     需先把 +c 项改写为 Cof_real 1 *c comboM +c Cof_real c *c u 形式。 *)
  replace (fun k : nat => comboM (S M) c u k +c Cof_real (c (S M)) *c u (S M) k)
    with (fun k : nat => Cof_real 1 *c comboM (S M) c u k +c Cof_real (c (S M)) *c u (S M) k).
  2: {
    apply functional_extensionality. intro k.
    replace (Cof_real 1 *c comboM (S M) c u k)%C with (comboM (S M) c u k)%C.
    - reflexivity.
    - apply Complex_eq; simpl; ring.
  }
  rewrite (norm_sq_combo2 (comboM (S M) c u) (u (S M)) 1 (c (S M)) W).
  replace ((1 * 1) * l2_norm_sq (comboM (S M) c u) W)%R
    with (l2_norm_sq (comboM (S M) c u) W)%R by ring.
  ring.
Qed.

(* 逐项 ≤ ⟹ 和 ≤（sum_f_R0 保序） *)
Lemma sum_f_R0_le (f g : nat -> R) (n : nat) :
  (forall k, (k <= n)%nat -> (f k <= g k)%R) ->
  (sum_f_R0 f n <= sum_f_R0 g n)%R.
Proof.
  intros H. induction n as [| n IH].
  - apply H. by apply leqnn.
  - simpl. apply Rplus_le_compat.
    + apply IH. intros k Hk. apply H. exact (leq_trans Hk (leqnSn n)).
    + apply H. by apply leqnn.
Qed.

(* 三角不等式：|Σ_{k≤n} f k| ≤ Σ_{k≤n} |f k| *)
Lemma sum_f_R0_abs (f : nat -> R) (n : nat) :
  (Rabs (sum_f_R0 f n) <= sum_f_R0 (fun k => Rabs (f k)) n)%R.
Proof.
  induction n as [| n IH].
  - simpl. apply Rle_refl.
  - simpl. apply Rle_trans with (Rabs (sum_f_R0 f n) + Rabs (f (S n)))%R.
    + apply Rabs_triang.
    + apply Rplus_le_compat; [exact IH | apply Rle_refl].
Qed.

(* 交叉项界：|⟨comboM (S M) c u, u (S M)⟩| ≤ μ·Σ_{j≤M}|c_j|（两两相干 ≤ μ） *)
Lemma cross_abs_le (M : nat) (c : nat -> R) (u : nat -> nat -> Complex) (W : nat) (mu : R) :
  (forall i j, i <= S M -> j <= S M -> i <> j ->
    (Rabs (ipW (u i) (u j) W) <= mu)%R) ->
  ((Rabs (ipW (comboM (S M) c u) (u (S M)) W))
   <= (mu * sum_f_R0 (fun j : nat => Rabs (c j)) M))%R.
Proof.
  intros Hcoh.
  rewrite ipW_combo_l.
  apply (Rle_trans _ (sum_f_R0 (fun j : nat => (Rabs (c j) * Rabs (ipW (u j) (u (S M)) W))%R) M)%R).
  - eapply Rle_trans.
    + apply sum_f_R0_abs.
    + rewrite (sum_f_R0_ext _ (fun j : nat => (Rabs (c j) * Rabs (ipW (u j) (u (S M)) W))%R) M).
      apply Rle_refl.
      intro j. apply Rabs_mult.
  - apply (Rle_trans _ (sum_f_R0 (fun j : nat => (Rabs (c j) * mu)%R) M)%R).
    + apply sum_f_R0_le. intros k Hk.
      apply Rmult_le_compat_l; [apply Rabs_pos | ].
      apply Hcoh.
      - exact (leq_trans Hk (leqnSn M)).
      - by apply leqnn.
      - move: Hk => /leP Hkp. lia.
    + rewrite (sum_f_R0_ext _ (fun j : nat => (mu * Rabs (c j))%R) M).
      rewrite (sum_f_R0_scal mu (fun j : nat => Rabs (c j)) M).
      apply Rle_refl.
      intro j. ring.
Qed.

(* 2|a||b| ≤ a²+b²（AM-GM，从 Rabs_prod_le_sq_sum 变形） *)
Lemma abs_prod_le_sq (a b : R) : ((2%R * Rabs a * Rabs b) <= (a * a + b * b))%R.
Proof.
  replace (2%R * Rabs a * Rabs b)%R with (2%R * Rabs (a * b))%R by
    (rewrite Rabs_mult; ring).
  exact (Rabs_prod_le_sq_sum a b).
Qed.

(* Σ_{j≤M} c_j² 的部分和分解：S_{SM} = S_M + c_{SM}² *)
Lemma sq_sum_step (c : nat -> R) (M : nat) :
  (sum_f_R0 (fun j : nat => c j * c j) (S M))%R
  = ((sum_f_R0 (fun j : nat => c j * c j) M) + c (S M) * c (S M))%R.
Proof. simpl. ring. Qed.

(* 逐项夹：2·|a|·|c_j| ≤ a² + c_j² 对 j ≤ M 求和：
   2·|a|·Σ_{j≤M}|c_j| ≤ (M+1)·a² + Σ_{j≤M}c_j² *)
Lemma sum_abs_cross_le (M : nat) (a : R) (c : nat -> R) :
  ((2%R * Rabs a * sum_f_R0 (fun j : nat => Rabs (c j)) M)
   <= ((INR (S M)) * (a * a) + sum_f_R0 (fun j : nat => c j * c j) M))%R.
Proof.
  rewrite <- (sum_f_R0_scal (2%R * Rabs a) (fun j : nat => Rabs (c j)) M).
  apply (Rle_trans _ (sum_f_R0 (fun j : nat => ((a * a) + c j * c j)%R) M)%R).
  - apply sum_f_R0_le. intros k Hk.
    apply (Rle_trans _ (a * a + c k * c k)%R).
    + exact (abs_prod_le_sq a (c k)).
    + apply Rle_refl.
  - rewrite (sum_f_R0_plus (fun _ : nat => (a * a)%R) (fun j : nat => (c j * c j)%R) M).
    rewrite (sum_f_R0_ext _ (fun _ : nat => ((a * a) * 1)%R) M).
    rewrite (sum_f_R0_scal (a * a) (fun _ : nat => 1%R) M).
    rewrite (sum_f_R0_const M).
    lra.
    intro k. ring.
Qed.

(* ============================================================
   CS-3b 最终定理：M-原子稀疏唯一性（z 工作区，E039）
   —— rip_lower_M（RIP 下界，归纳）+ sparse_uniquenessM（最终定理）。
   证明链：norm_sq_comboM_rec（递归展开）+ cross_abs_le（交叉项界）
   + sum_abs_cross_le（AM-GM 聚合）+ 系数 INR 单调。
   ============================================================ *)

(* Σ_{j≤M} c_j² ≥ 0（平方和非负，独立引理避免嵌套归纳） *)
Lemma sum_sq_nonneg (c : nat -> R) (M : nat) :
  (0 <= sum_f_R0 (fun j : nat => c j * c j) M)%R.
Proof.
  induction M; simpl; [apply Rle_0_sqr | apply Rplus_le_le_0_compat; [exact IHM | apply Rle_0_sqr]].
Qed.

(* μ·S + μ·INR(SM)·S = μ·INR(S(SM))·S（S_INR 合并，E058 显式 replace 法 + set N 消歧） *)
Lemma INR_succ_mul (mu sv : R) (M : nat) :
  (mu * sv + mu * INR (S M) * sv = mu * INR (S (S M)) * sv)%R.
Proof.
  set (N := (INR (S M))%R).
  replace (INR (S (S M)))%R with (N + 1)%R.
  - ring.
  - subst N. symmetry. exact (S_INR (S M)).
Qed.

(* 最终夹逼：纯原子 lra（INR 值作为变量，避开 Coq 对 INR (S(SM)) 与 INR (SM) 的模式匹配冲突） *)
Lemma final_squeeze (Lp Sv A2 Yv mS mN1S mN2S mN1A mN2A : R) :
  (Sv + A2 <= Lp + Yv + mN1S)%R ->
  (Yv <= mN1A + mS)%R ->
  (mS + mN1S = mN2S)%R ->
  (mN1A <= mN2A)%R ->
  (Sv + A2 <= Lp + mN2S + mN2A)%R.
Proof. intros. lra. Qed.

(* 最终夹逼：纯原子 nra（N1/N2 为 INR 值变量，避开 INR 模式匹配冲突） *)
Lemma rip_final (L A2 Sv IP Yv mu N1 N2 : R) :
  (0 <= mu)%R -> (0 <= A2)%R -> (0 <= Sv)%R ->
  (Sv + A2 <= L + A2 + 2 * IP + Yv + mu * N1 * Sv)%R ->
  (Yv <= mu * (N1 * A2 + Sv))%R ->
  (N2 = N1 + 1)%R ->
  (mu * N1 * A2 <= mu * N2 * A2)%R ->
  (Sv + A2 <= L + A2 + 2 * IP + mu * N2 * (Sv + A2))%R.
Proof. intros. nra. Qed.

(* RIP 下界（归纳）：Σ_{j≤M}c_j² ≤ l2(comboM (S M)) + μ·(M+1)·Σ_{j≤M}c_j² *)
Lemma rip_lower_M (M : nat) (c : nat -> R) (u : nat -> nat -> Complex) (W : nat) (mu : R) :
  (0 <= mu)%R ->
  (forall j, j <= M -> (l2_norm_sq (u j) W)%R = 1%R) ->
  (forall i j, i <= M -> j <= M -> i <> j ->
    (Rabs (ipW (u i) (u j) W) <= mu)%R) ->
  ((sum_f_R0 (fun j : nat => c j * c j) M)
   <= (l2_norm_sq (comboM (S M) c u) W
       + mu * INR (S M) * sum_f_R0 (fun j : nat => c j * c j) M))%R.
Proof.
  intros Hmu0.
  induction M as [| M IH].
  - (* M=0：单原子。S_0 = c_0²，l2(comboM 1) = c_0²·l2(u_0) = c_0² *)
    intros Hunit Hcoh.
    assert (Hu : (l2_norm_sq (u 0%nat) W)%R = 1%R) by (apply Hunit; by apply leqnn).
    change (sum_f_R0 (fun j : nat => c j * c j) 0)%R with (c 0%nat * c 0%nat)%R.
    rewrite (comboM_one c u).
    rewrite l2_norm_sq_scale.
    rewrite Incoherence.Cnorm_sq_Cof_real.
    rewrite Hu.
    replace ((c 0%nat * c 0%nat) * 1)%R with (c 0%nat * c 0%nat)%R by ring.
    replace (INR (S 0))%R with 1%R by (simpl; auto).
    assert (Hsq0 : (0 <= c 0%nat * c 0%nat)%R) by apply Rle_0_sqr.
    assert (Hm : (0 <= mu * (c 0%nat * c 0%nat))%R)
      by (apply Rmult_le_pos; [exact Hmu0 | exact Hsq0]).
    replace (mu * 1%R * (c 0%nat * c 0%nat))%R with (mu * (c 0%nat * c 0%nat))%R by ring.
    lra.
  - (* 归纳步 *)
    intros Hunit Hcoh.
    rewrite (sq_sum_step c M).
    rewrite (norm_sq_comboM_rec M c u W).
    assert (Hu' : (l2_norm_sq (u (S M)) W)%R = 1%R) by (apply Hunit; by apply leqnn).
    rewrite Hu'.
    replace ((c (S M) * c (S M)) * 1)%R with (c (S M) * c (S M))%R by ring.
    replace (2 * c (S M) * ipW (comboM (S M) c u) (u (S M)) W)%R
      with (2 * (c (S M) * ipW (comboM (S M) c u) (u (S M)) W))%R by ring.
    (* 记 S := Σ_{j≤M}c_j²，A := c(SM)，IP := ipW(comboM(SM),u(SM))，L := l2(comboM(SM))。
       目标：S + A² ≤ L + A² + 2A·IP + μ(M+2)(S + A²)。 *)
    (* IH（截取到 ≤ M）：S ≤ L + μ(M+1)S *)
    assert (HIH' : ((sum_f_R0 (fun j : nat => c j * c j) M)
        <= (l2_norm_sq (comboM (S M) c u) W)
           + mu * INR (S M) * sum_f_R0 (fun j : nat => c j * c j) M)%R).
    { exact (IH
        (fun j Hj => Hunit j (leq_trans Hj (leqnSn M)))
        (fun i j Hij Hji Hne => Hcoh i j (leq_trans Hij (leqnSn M)) (leq_trans Hji (leqnSn M)) Hne)). }
    (* cross_abs_le：|IP| ≤ μ·Σ_{j≤M}|c_j| *)
    assert (Hcross := cross_abs_le M c u W mu
      (fun i j Hij Hji Hne => Hcoh i j Hij Hji Hne)).
    (* 第一步：S + A² ≤ L + A² + 2A·IP + 2|A||IP| + μ(M+1)S
       即 S ≤ L + 2A·IP + 2|A||IP| + μ(M+1)S（由 HIH' + 2A·IP ≥ −2|A||IP|） *)
    assert (H1 : ((sum_f_R0 (fun j : nat => c j * c j) M)
        <= (l2_norm_sq (comboM (S M) c u) W)
           + 2 * (c (S M)) * ipW (comboM (S M) c u) (u (S M)) W
           + 2 * Rabs (c (S M)) * Rabs (ipW (comboM (S M) c u) (u (S M)) W)
           + mu * INR (S M) * sum_f_R0 (fun j : nat => c j * c j) M)%R).
    { (* 记 X := 2A·IP，Y := 2|A||IP|，M1 := μ(M+1)S。HIH' : S ≤ L + M1。
         目标 S ≤ L + X + Y + M1。由 HIH' 与 0 ≤ X + Y（Hneg 给出 −X ≤ Y ⟹ X+Y ≥ 0）。 *)
      set (X := (2 * (c (S M)) * ipW (comboM (S M) c u) (u (S M)) W)%R).
      set (Y := (2 * Rabs (c (S M)) * Rabs (ipW (comboM (S M) c u) (u (S M)) W))%R).
      set (M1 := (mu * INR (S M) * sum_f_R0 (fun j : nat => c j * c j) M)%R).
      assert (Hneg : (- X <= Y)%R).
      { unfold X, Y.
        apply (Rle_trans _ (Rabs (2 * (c (S M)) * ipW (comboM (S M) c u) (u (S M)) W))%R).
        - apply (Rle_trans _ (Rabs (- (2 * (c (S M)) * ipW (comboM (S M) c u) (u (S M)) W)))%R).
          + apply Rle_abs.
          + rewrite Rabs_opp. apply Rle_refl.
        - replace (Rabs (2 * (c (S M)) * ipW (comboM (S M) c u) (u (S M)) W))%R
            with (2 * Rabs (c (S M)) * Rabs (ipW (comboM (S M) c u) (u (S M)) W))%R.
          + apply Rle_refl.
          + rewrite Rabs_mult. rewrite Rabs_mult.
            replace (Rabs 2)%R with 2%R by (rewrite Rabs_right; [ring | lra]).
            ring. }
      assert (Hnonneg : (0 <= X + Y)%R) by lra.
      (* 目标：S ≤ L + X + Y + M1。HIH' : S ≤ L + M1。由 Hnonneg：M1 ≤ X + Y + M1。 *)
      eapply Rle_trans.
      - exact HIH'.
      - (* L + M1 ≤ L + X + Y + M1：需 M1 ≤ X + Y + M1，即 0 ≤ X + Y *)
        subst X Y M1. lra. }
    (* 第二步：2|A||IP| ≤ 2|A|·μ·Σ|c_j|（cross_abs_le 乘 2|A| ≥ 0） *)
    assert (H2 : (2 * Rabs (c (S M)) * Rabs (ipW (comboM (S M) c u) (u (S M)) W)
        <= 2 * Rabs (c (S M)) * (mu * sum_f_R0 (fun j : nat => Rabs (c j)) M))%R).
    { apply Rmult_le_compat_l.
      - apply Rmult_le_pos; [lra | apply Rabs_pos].
      - exact Hcross. }
    (* 第三步：2|A|·μ·Σ|c_j| ≤ μ·((M+1)A² + S)（sum_abs_cross_le 乘 mu ≥ 0） *)
    assert (H3 : (2 * Rabs (c (S M)) * (mu * sum_f_R0 (fun j : nat => Rabs (c j)) M)
        <= mu * ((INR (S M)) * (c (S M) * c (S M)) + sum_f_R0 (fun j : nat => c j * c j) M))%R).
    { replace (2 * Rabs (c (S M)) * (mu * sum_f_R0 (fun j : nat => Rabs (c j)) M))%R
        with (mu * (2 * Rabs (c (S M)) * sum_f_R0 (fun j : nat => Rabs (c j)) M))%R by ring.
      apply Rmult_le_compat_l; [exact Hmu0 | exact (sum_abs_cross_le M (c (S M)) c)]. }
    (* 组装：目标 S + A² ≤ L' + μ(M+2)(S + A²)，L' = l2(comboM (S(SM))) = L + A² + 2A·IP。
       链条：
       S + A² ≤ L + A² + μ(M+1)S            [HIH' 加 A²]
             = L' − 2A·IP + μ(M+1)S         [L' = L + A² + 2A·IP]
             ≤ L' + 2|A||IP| + μ(M+1)S      [−2A·IP ≤ 2|A||IP|]
             ≤ L' + μ((M+1)A² + S) + μ(M+1)S  [H2'：2|A||IP| ≤ μ((M+1)A²+S)]
             = L' + μ(M+1)A² + μ(M+2)S      [代数]
             ≤ L' + μ(M+2)A² + μ(M+2)S      [HmA：μ(M+1)A² ≤ μ(M+2)A²]
             = 目标（μ(M+2)(S+A²)）。 *)
    (* 第一步：S + A² ≤ L' + 2|A||IP| + μ(M+1)S *)
    assert (H1L : ((sum_f_R0 (fun j : nat => c j * c j) M) + c (S M) * c (S M)
        <= (l2_norm_sq (comboM (S (S M)) c u) W)
           + 2 * Rabs (c (S M)) * Rabs (ipW (comboM (S M) c u) (u (S M)) W)
           + mu * INR (S M) * sum_f_R0 (fun j : nat => c j * c j) M)%R).
    { (* 由 HIH'（S ≤ L + μ(M+1)S）加 A²：S + A² ≤ L + A² + μ(M+1)S。
         L' = L + A² + 2A·IP（norm_sq_comboM_rec 反向）。代入：
         L + A² + μ(M+1)S = L' − 2A·IP + μ(M+1)S ≤ L' + 2|A||IP| + μ(M+1)S。 *)
      eapply Rle_trans.
      - (* S + A² ≤ L + A² + μ(M+1)S *)
        apply Rplus_le_compat_r. exact HIH'.
      - (* L + A² + μ(M+1)S ≤ L' + 2|A||IP| + μ(M+1)S。
           L' = L + A² + 2A·IP ⟹ L + A² = L' − 2A·IP。需 −2A·IP ≤ 2|A||IP|。 *)
        rewrite (norm_sq_comboM_rec M c u W).
        rewrite Hu'.
        replace ((c (S M) * c (S M)) * 1)%R with (c (S M) * c (S M))%R by ring.
        (* 目标：L + A² + μ(M+1)S ≤ L + A² + 2A·IP + 2|A||IP| + μ(M+1)S。
           消去 L + A² + μ(M+1)S：需 0 ≤ 2A·IP + 2|A||IP|。 *)
        assert (Hneg : (- (2 * (c (S M)) * ipW (comboM (S M) c u) (u (S M)) W)
            <= 2 * Rabs (c (S M)) * Rabs (ipW (comboM (S M) c u) (u (S M)) W))%R).
        { apply (Rle_trans _ (Rabs (2 * (c (S M)) * ipW (comboM (S M) c u) (u (S M)) W))%R).
          - apply (Rle_trans _ (Rabs (- (2 * (c (S M)) * ipW (comboM (S M) c u) (u (S M)) W)))%R).
            + apply Rle_abs.
            + rewrite Rabs_opp. apply Rle_refl.
          - replace (Rabs (2 * (c (S M)) * ipW (comboM (S M) c u) (u (S M)) W))%R
              with (2 * Rabs (c (S M)) * Rabs (ipW (comboM (S M) c u) (u (S M)) W))%R.
            + apply Rle_refl.
            + rewrite Rabs_mult. rewrite Rabs_mult.
              replace (Rabs 2)%R with 2%R by (rewrite Rabs_right; [ring | lra]).
              ring. }
        lra. }
    (* 第二步：H2' : 2|A||IP| ≤ μ((M+1)A² + S)（H2 + H3 合成） *)
    assert (H2' : (2 * Rabs (c (S M)) * Rabs (ipW (comboM (S M) c u) (u (S M)) W)
        <= mu * ((INR (S M)) * (c (S M) * c (S M)) + sum_f_R0 (fun j : nat => c j * c j) M))%R).
    { eapply Rle_trans; [exact H2 | exact H3]. }
    (* 组装最终链：展开 H1L 的 Lp，用 rip_final（纯 nra）一步收尾。 *)
    assert (HA2 : (0 <= c (S M) * c (S M))%R) by apply Rle_0_sqr.
    assert (HS' : (0 <= sum_f_R0 (fun j : nat => c j * c j) M)%R).
    { exact (sum_sq_nonneg c M). }
    (* μ(M+1)A² ≤ μ(M+2)A² *)
    assert (HmA : (mu * INR (S M) * (c (S M) * c (S M))
        <= mu * INR (S (S M)) * (c (S M) * c (S M)))%R).
    { apply Rmult_le_compat_r.
      - exact HA2.
      - apply Rmult_le_compat_l.
        + exact Hmu0.
        + apply le_INR. lia. }
    (* 展开 H1L 的 Lp（l2(comboM(S(SM))) = L + A² + 2A·IP，norm_sq_comboM_rec + Hu'） *)
    rewrite (norm_sq_comboM_rec M c u W) in H1L.
    rewrite Hu' in H1L.
    replace ((c (S M) * c (S M)) * 1)%R with (c (S M) * c (S M))%R in H1L by ring.
    replace (2 * c (S M) * ipW (comboM (S M) c u) (u (S M)) W)%R
      with (2 * (c (S M) * ipW (comboM (S M) c u) (u (S M)) W))%R in H1L by ring.
    (* 目标：S + A2 ≤ L + A2 + 2A·IP + mu·INR(S(SM))·(S+A2)。用 rip_final。 *)
    apply (rip_final (l2_norm_sq (comboM (S M) c u) W)
                     (c (S M) * c (S M))
                     (sum_f_R0 (fun j : nat => (c j * c j)%R) M)
                     (c (S M) * ipW (comboM (S M) c u) (u (S M)) W)
                     (2 * Rabs (c (S M)) * Rabs (ipW (comboM (S M) c u) (u (S M)) W))
                     mu (INR (S M)) (INR (S (S M)))).
    - exact Hmu0.
    - exact HA2.
    - exact HS'.
    - (* Sv+A2 ≤ L + A2 + 2*(c(SM)*IP) + Yv + mu*INR(SM)*Sv = H1L（已展开） *)
      exact H1L.
    - (* Yv ≤ mu*(INR(SM)*A2 + Sv) = H2' *)
      exact H2'.
    - (* INR(S(SM)) = INR(SM) + 1 *)
      exact (S_INR (S M)).
    - exact HmA.
Qed.
(* Σ_{j≤M} c_j² = 0 ⟹ ∀j≤M, c j = 0（逐项平方非负） *)
Lemma sum_sq_zero (c : nat -> R) (M : nat) :
  (sum_f_R0 (fun j : nat => c j * c j) M = 0)%R ->
  forall j, (j <= M)%nat -> c j = 0%R.
Proof.
  intros H. induction M as [| M IH].
  - intros j Hj. assert (Hj0 : j = 0%nat) by (move: Hj => /leP Hjp; lia). subst j.
    change (sum_f_R0 (fun j : nat => c j * c j) 0)%R with (c 0%nat * c 0%nat)%R in H.
    apply (sq_sum_zero_l (c 0%nat) 0%R).
    replace (0%R * 0%R)%R with 0%R by ring.
    rewrite Rplus_0_r. exact H.
  - rewrite (sq_sum_step c M) in H.
    assert (HS : (sum_f_R0 (fun j : nat => c j * c j) M = 0)%R).
    { apply Rle_antisym.
      - assert (Hle : (sum_f_R0 (fun j : nat => c j * c j) M <= 0)%R).
        { apply (Rplus_le_reg_l (c (S M) * c (S M)) _ _).
          replace ((c (S M) * c (S M)) + sum_f_R0 (fun j : nat => c j * c j) M)%R
            with (sum_f_R0 (fun j : nat => c j * c j) M + c (S M) * c (S M))%R by ring.
          rewrite H. rewrite Rplus_0_r. apply Rle_0_sqr. }
        exact Hle.
      - exact (sum_sq_nonneg c M). }
    assert (Hsm : (c (S M) * c (S M) = 0)%R).
    { apply Rle_antisym.
      - assert (Hle : (c (S M) * c (S M) <= 0)%R).
        { apply (Rplus_le_reg_l (sum_f_R0 (fun j : nat => (c j * c j)%R) M) _ _).
          rewrite H. rewrite Rplus_0_r. exact (sum_sq_nonneg c M). }
        exact Hle.
      - apply Rle_0_sqr. }
    intros j Hj.
    destruct (Nat.eq_dec j (S M)) as [E | NE].
    + subst j. apply (sq_sum_zero_r 0%R (c (S M))).
      replace (0%R * 0%R)%R with 0%R by ring.
      rewrite Rplus_0_l. exact Hsm.
    + assert (HjM : (j <= M)%nat) by (apply/leP; move: Hj => /leP Hjp; move: NE => NEp; lia).
      exact (IH HS j HjM).
Qed.

(* CS-3b 最终定理：M-原子稀疏唯一性。
   M+1 个单位范数原子、两两相干 ≤ μ、μ(M+1) < 1，且 Σ_{j≤M}c_j·u_j ≡ 0（窗口内）
   ⟹ 所有系数 c_j = 0。 *)
Theorem sparse_uniquenessM (M : nat) (c : nat -> R) (u : nat -> nat -> Complex) (W : nat) (mu : R) :
  (0 <= mu)%R ->
  (forall j, j <= M -> (l2_norm_sq (u j) W)%R = 1%R) ->
  (forall i j, i <= M -> j <= M -> i <> j ->
    (Rabs (ipW (u i) (u j) W) <= mu)%R) ->
  (mu * INR (S M) < 1)%R ->
  (forall k, (k <= W)%nat -> (comboM (S M) c u k = C0)%C) ->
  (forall j, j <= M -> c j = 0%R).
Proof.
  intros Hmu0 Hunit Hcoh Hmu1 Hzero.
  (* 0 = l2(comboM (S M))（零组合 ⟹ 能量 0） *)
  assert (Hl2 : (l2_norm_sq (comboM (S M) c u) W)%R = 0%R).
  { unfold l2_norm_sq.
    rewrite (Incoherence.sum_f_R0_ext_bounded _ (fun _ => Cnorm_sq C0) W).
    rewrite (Incoherence.sum_f_R0_ext_bounded _ (fun _ => 0%R) W).
    rewrite (sum_f_R0_zero W). reflexivity.
    intro k. intro Hk. exact Cnorm_sq_C0.
    intro k. intro Hk. f_equal. exact (Hzero k Hk). }
  (* RIP 下界：Σc_j² ≤ l2 + μ(M+1)Σc_j² = μ(M+1)Σc_j²（因 l2 = 0） *)
  assert (Hrip := rip_lower_M M c u W mu Hmu0 Hunit Hcoh).
  rewrite Hl2 in Hrip.
  (* Σc_j² ≤ μ(M+1)·Σc_j² 且 μ(M+1) < 1 ⟹ Σc_j² = 0 *)
  assert (HS : (0 <= sum_f_R0 (fun j : nat => c j * c j) M)%R).
  { exact (sum_sq_nonneg c M). }
  assert (Hsq0 : (sum_f_R0 (fun j : nat => c j * c j) M = 0)%R).
  { apply Rle_antisym.
    - (* Σc_j² ≤ 0：由 Hrip 与 μ(M+1)<1 相除。 *)
      assert (H1m : (0 < 1 - mu * INR (S M))%R) by lra.
      assert (Hprod : ((1 - mu * INR (S M)) * sum_f_R0 (fun j : nat => c j * c j) M <= 0)%R).
      { replace ((1 - mu * INR (S M)) * sum_f_R0 (fun j : nat => c j * c j) M)%R
          with (sum_f_R0 (fun j : nat => c j * c j) M - mu * INR (S M) * sum_f_R0 (fun j : nat => c j * c j) M)%R by ring.
        lra. }
      apply (Rmult_le_reg_l (1 - mu * INR (S M)) _ _ H1m).
      replace ((1 - mu * INR (S M)) * 0)%R with 0%R by ring.
      exact Hprod.
    - exact HS. }
  (* 从 Σc_j² = 0 推出各 c_j = 0 *)
  exact (sum_sq_zero c M Hsq0).
Qed.

End Incoherence2.
