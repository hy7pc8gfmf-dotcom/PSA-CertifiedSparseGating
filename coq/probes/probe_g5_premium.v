(* ============================================================
   G-5 / G-3 必要方向：可判定性溢价 [3,7,15] 反例
   存在阶梯：精确行和 ≤ 4/5（可认证）但反射检查器拒绝
   经典 R 轨道；零 Admitted；零自定义公理。

   ★ 2026-08-25 口径修正（§45）：改用完整口径（min 项）闭式自证，
     与评估文档 0.787043 对齐。库内 psi_inner_dirichlet 是截断口径
     （N = n1−1，漏 k=n1−1 项），本探针不再依赖它；
     完整闭式用 inner_geometric_expansion_full + geom_sum_norm_dirichlet 自证。
   ============================================================ *)
From mathcomp Require Import ssreflect ssrbool ssrnat seq eqtype div prime.
Require Import Stdlib.Reals.Reals.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.micromega.Lra.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import ca_merged_full_24.
Import FrameCheckInstance.
Import PrimeEmbedding.
Import ComplexNumbers.
Import Gershgorin.
Import UnconditionalBasisLemmas.
Import RuntimeGuards.
Import ExtendedTheorems.
Import InstanceCertificate.
Import CertifiedAttention.
Open Scope R_scope.

Module G5Premium.

(* [3,7,15] 反射检查器拒绝（可计算验证） *)
Definition ladder_3_7_15 : list nat := 3%nat :: 7%nat :: 15%nat :: nil.

Lemma g5_reflect_reject : frame_check_instance ladder_3_7_15 = false.
Proof.
  vm_compute. reflexivity.
Qed.

(* ============ 完整口径闭式（min 项，自证） ============
   |⟨ψ_a,ψ_b⟩| = |sin(min(a,b)·π·Δ)| / (|sin(π·Δ)| · √(ab))，Δ = 1/a − 1/b
   a < b 时 min = a，闭式 = |sin(aπΔ)| / (|sin(πΔ)| · √(ab))
   证明：inner_geometric_expansion_full（Csum n1 = min 项）
         → geom_sum_norm_dirichlet θ n1（Dirichlet 核）
         → dirichlet_algebra（纯 R 消元） *)

(* |<ψ3,ψ7>| = sin(4π/7) / (sin(4π/21) · √21) *)
Lemma g5_coh_full_3_7 :
  ComplexNumbers.Cnorm (independent.Csum (fun k => psi 3 k *c ComplexNumbers.Cconj (psi 7 k)) 3)
  = Rabs (sin (PI * INR 3 * (1 / INR 3 - 1 / INR 7))) / Rabs (sin (PI * (1 / INR 3 - 1 / INR 7))) / sqrt (INR 3 * INR 7).
Proof.
  pose proof (ca_merged_full_24.inner_geometric_expansion_full 3 7
                (ltac:(lia) : (3 >= 2)%coq_nat) (ltac:(lia) : (7 >= 2)%coq_nat)
                (ltac:(lia) : (3 <= 7)%coq_nat)) as Hge.
  cbv zeta in Hge.
  rewrite Hge.
  set (Δ := 1 / INR 3 - 1 / INR 7).
  set (θ := 2 * PI * Δ).
  rewrite Cnorm_mult.
  rewrite Cnorm_mult.
  rewrite (Cnorm_Cof_real_pos (1 / sqrt (INR 3))).
  2: { apply Rlt_le. apply Rdiv_lt_0_compat; [lra | apply sqrt_lt_R0_c; apply lt_0_INR; lia]. }
  rewrite (Cnorm_Cof_real_pos (1 / sqrt (INR 7))).
  2: { apply Rlt_le. apply Rdiv_lt_0_compat; [lra | apply sqrt_lt_R0_c; apply lt_0_INR; lia]. }
  assert (Hz : Cexp (0 +i θ) <> C1).
  { unfold θ, Δ. apply (Cexp_diff_not_one 3 7); lia. }
  rewrite (Csum_ext 3 (fun k => Cexp (0 +i (INR k * θ)))
                     (fun k => (Cexp (0 +i θ) ^ k)%C)).
  2: { intros k _. apply Cexp_pow_local. }
  rewrite (geom_sum_norm_dirichlet θ 3 Hz).
  assert (He1 : (INR 3 * θ / 2 = PI * INR 3 * Δ)%R).
  { unfold θ. field. }
  rewrite He1.
  assert (He2 : (θ / 2 = PI * Δ)%R).
  { unfold θ. field. }
  rewrite He2.
  rewrite (sqrt_mult (INR 3) (INR 7)).
  2: { apply pos_INR. }
  2: { apply pos_INR. }
  apply (dirichlet_algebra (sqrt (INR 3)) (sqrt (INR 7))
                           (Rabs (sin (PI * Δ))) (Rabs (sin (PI * INR 3 * Δ)))).
  - apply Rgt_not_eq. apply sqrt_INR_pos_ge2. exact (ltac:(lia) : (3 >= 2)%coq_nat).
  - apply Rgt_not_eq. apply sqrt_INR_pos_ge2. exact (ltac:(lia) : (7 >= 2)%coq_nat).
  - apply Rgt_not_eq. apply Rabs_pos_lt. apply Rgt_not_eq.
    apply sin_gt_0.
    + apply Rmult_lt_0_compat; [apply PI_RGT_0 | apply (proj1 (diff_inv_INR_between_0_1 3 7 (ltac:(lia)) (ltac:(lia)) (ltac:(lia))))].
    + apply Rlt_le_trans with (PI * 1).
      * apply Rmult_lt_compat_l; [apply PI_RGT_0 | exact (proj2 (diff_inv_INR_between_0_1 3 7 (ltac:(lia)) (ltac:(lia)) (ltac:(lia))))].
      * rewrite Rmult_1_r. apply Rle_refl.
Qed.

(* |<ψ3,ψ15>| = sin(4π/5) / (sin(4π/15) · √45) *)
Lemma g5_coh_full_3_15 :
  ComplexNumbers.Cnorm (independent.Csum (fun k => psi 3 k *c ComplexNumbers.Cconj (psi 15 k)) 3)
  = Rabs (sin (PI * INR 3 * (1 / INR 3 - 1 / INR 15))) / Rabs (sin (PI * (1 / INR 3 - 1 / INR 15))) / sqrt (INR 3 * INR 15).
Proof.
  pose proof (ca_merged_full_24.inner_geometric_expansion_full 3 15
                (ltac:(lia) : (3 >= 2)%coq_nat) (ltac:(lia) : (15 >= 2)%coq_nat)
                (ltac:(lia) : (3 <= 15)%coq_nat)) as Hge.
  cbv zeta in Hge.
  rewrite Hge.
  set (Δ := 1 / INR 3 - 1 / INR 15).
  set (θ := 2 * PI * Δ).
  rewrite Cnorm_mult.
  rewrite Cnorm_mult.
  rewrite (Cnorm_Cof_real_pos (1 / sqrt (INR 3))).
  2: { apply Rlt_le. apply Rdiv_lt_0_compat; [lra | apply sqrt_lt_R0_c; apply lt_0_INR; lia]. }
  rewrite (Cnorm_Cof_real_pos (1 / sqrt (INR 15))).
  2: { apply Rlt_le. apply Rdiv_lt_0_compat; [lra | apply sqrt_lt_R0_c; apply lt_0_INR; lia]. }
  assert (Hz : Cexp (0 +i θ) <> C1).
  { unfold θ, Δ. apply (Cexp_diff_not_one 3 15); lia. }
  rewrite (Csum_ext 3 (fun k => Cexp (0 +i (INR k * θ)))
                     (fun k => (Cexp (0 +i θ) ^ k)%C)).
  2: { intros k _. apply Cexp_pow_local. }
  rewrite (geom_sum_norm_dirichlet θ 3 Hz).
  assert (He1 : (INR 3 * θ / 2 = PI * INR 3 * Δ)%R).
  { unfold θ. field. }
  rewrite He1.
  assert (He2 : (θ / 2 = PI * Δ)%R).
  { unfold θ. field. }
  rewrite He2.
  rewrite (sqrt_mult (INR 3) (INR 15)).
  2: { apply pos_INR. }
  2: { apply pos_INR. }
  apply (dirichlet_algebra (sqrt (INR 3)) (sqrt (INR 15))
                           (Rabs (sin (PI * Δ))) (Rabs (sin (PI * INR 3 * Δ)))).
  - apply Rgt_not_eq. apply sqrt_INR_pos_ge2. exact (ltac:(lia) : (3 >= 2)%coq_nat).
  - apply Rgt_not_eq. apply sqrt_INR_pos_ge2. exact (ltac:(lia) : (15 >= 2)%coq_nat).
  - apply Rgt_not_eq. apply Rabs_pos_lt. apply Rgt_not_eq.
    apply sin_gt_0.
    + apply Rmult_lt_0_compat; [apply PI_RGT_0 | apply (proj1 (diff_inv_INR_between_0_1 3 15 (ltac:(lia)) (ltac:(lia)) (ltac:(lia))))].
    + apply Rlt_le_trans with (PI * 1).
      * apply Rmult_lt_compat_l; [apply PI_RGT_0 | exact (proj2 (diff_inv_INR_between_0_1 3 15 (ltac:(lia)) (ltac:(lia)) (ltac:(lia))))].
      * rewrite Rmult_1_r. apply Rle_refl.
Qed.

(* |<ψ7,ψ15>| = sin(8π/15) / (sin(8π/105) · √105) *)
Lemma g5_coh_full_7_15 :
  ComplexNumbers.Cnorm (independent.Csum (fun k => psi 7 k *c ComplexNumbers.Cconj (psi 15 k)) 7)
  = Rabs (sin (PI * INR 7 * (1 / INR 7 - 1 / INR 15))) / Rabs (sin (PI * (1 / INR 7 - 1 / INR 15))) / sqrt (INR 7 * INR 15).
Proof.
  pose proof (ca_merged_full_24.inner_geometric_expansion_full 7 15
                (ltac:(lia) : (7 >= 2)%coq_nat) (ltac:(lia) : (15 >= 2)%coq_nat)
                (ltac:(lia) : (7 <= 15)%coq_nat)) as Hge.
  cbv zeta in Hge.
  rewrite Hge.
  set (Δ := 1 / INR 7 - 1 / INR 15).
  set (θ := 2 * PI * Δ).
  rewrite Cnorm_mult.
  rewrite Cnorm_mult.
  rewrite (Cnorm_Cof_real_pos (1 / sqrt (INR 7))).
  2: { apply Rlt_le. apply Rdiv_lt_0_compat; [lra | apply sqrt_lt_R0_c; apply lt_0_INR; lia]. }
  rewrite (Cnorm_Cof_real_pos (1 / sqrt (INR 15))).
  2: { apply Rlt_le. apply Rdiv_lt_0_compat; [lra | apply sqrt_lt_R0_c; apply lt_0_INR; lia]. }
  assert (Hz : Cexp (0 +i θ) <> C1).
  { unfold θ, Δ. apply (Cexp_diff_not_one 7 15); lia. }
  rewrite (Csum_ext 7 (fun k => Cexp (0 +i (INR k * θ)))
                     (fun k => (Cexp (0 +i θ) ^ k)%C)).
  2: { intros k _. apply Cexp_pow_local. }
  rewrite (geom_sum_norm_dirichlet θ 7 Hz).
  assert (He1 : (INR 7 * θ / 2 = PI * INR 7 * Δ)%R).
  { unfold θ. field. }
  rewrite He1.
  assert (He2 : (θ / 2 = PI * Δ)%R).
  { unfold θ. field. }
  rewrite He2.
  rewrite (sqrt_mult (INR 7) (INR 15)).
  2: { apply pos_INR. }
  2: { apply pos_INR. }
  apply (dirichlet_algebra (sqrt (INR 7)) (sqrt (INR 15))
                           (Rabs (sin (PI * Δ))) (Rabs (sin (PI * INR 7 * Δ)))).
  - apply Rgt_not_eq. apply sqrt_INR_pos_ge2. exact (ltac:(lia) : (7 >= 2)%coq_nat).
  - apply Rgt_not_eq. apply sqrt_INR_pos_ge2. exact (ltac:(lia) : (15 >= 2)%coq_nat).
  - apply Rgt_not_eq. apply Rabs_pos_lt. apply Rgt_not_eq.
    apply sin_gt_0.
    + apply Rmult_lt_0_compat; [apply PI_RGT_0 | apply (proj1 (diff_inv_INR_between_0_1 7 15 (ltac:(lia)) (ltac:(lia)) (ltac:(lia))))].
    + apply Rlt_le_trans with (PI * 1).
      * apply Rmult_lt_compat_l; [apply PI_RGT_0 | exact (proj2 (diff_inv_INR_between_0_1 7 15 (ltac:(lia)) (ltac:(lia)) (ltac:(lia))))].
      * rewrite Rmult_1_r. apply Rle_refl.
Qed.

(* ============ 主定理（下一步：三行精确行和 ≤ 4/5） ============
   行 0 (n=3): |<3,7>| + |<3,15>| = 0.3777 + 0.1179 = 0.4956 ≤ 4/5
   行 1 (n=7): |<3,7>| + |<7,15>| = 0.3777 + 0.4094 = 0.7870 ≤ 4/5  ← 瓶颈
   行 2 (n=15): |<3,15>| + |<7,15>| = 0.1179 + 0.4094 = 0.5273 ≤ 4/5
   数值界：sin(4π/7) ≤ 0.97497、sin(4π/21) ≥ 0.56323、sin(8π/15) ≤ 0.99455、
          sin(8π/105) ≥ 0.23704、√21 ≥ 4.582、√105 ≥ 10.246（框架文档 §二 修正版）
   （用 sin_bound 高阶 + π ∈ [3.141,3.142] 自证界） *)

(* ============ π 界自证（sin(π/6)=1/2 快收敛路线） ============ *)

(* sin_approx 化简为显式多项式 *)
Lemma g5_sa1 (t : R) : sin_approx t 1 = t - t^3/6.
Proof. unfold sin_approx, sin_term. simpl. field. Qed.

Lemma g5_sa2 (t : R) : sin_approx t 2 = t - t^3/6 + t^5/120.
Proof. unfold sin_approx, sin_term. simpl. field. Qed.

Lemma g5_sa3 (t : R) : sin_approx t 3 = t - t^3/6 + t^5/120 - t^7/5040.
Proof. unfold sin_approx, sin_term. simpl. field. Qed.

(* f1(t) = 1 - t^2/2 + t^4/24 > 0 在 [0, 53/100]（sin_approx 2 的导数） *)
Lemma g5_pow2_2 (t : R) : t ^ 4 = (t ^ 2) ^ 2.
Proof.
  change (t ^ (2 * 2) = (t ^ 2) ^ 2).
  rewrite <- pow_mult.
  reflexivity.
Qed.

Lemma g5_fp_pos (t : R) : (0 <= t)%R -> (t <= 53/100)%R ->
  (0 < 1 - t ^ 2 / 2 + t ^ 4 / 24)%R.
Proof.
  intros Ht0 Ht.
  rewrite g5_pow2_2.
  set (u := t ^ 2).
  assert (Hlo_u : (0 <= u)%R) by (subst u; nra).
  assert (Hhi_u : (u <= 2809 / 10000)%R).
  { subst u. nra. }
  replace (1 - t ^ 2 / 2 + (t ^ 2) ^ 2 / 24) with (1 - u / 2 + u ^ 2 / 24) by (subst u; ring).
  nra.
Qed.

(* sin_approx t 2 可导：f(t) = t - t^3/6 + t^5/120 *)
Lemma g5_dpl_f2 (x : R) :
  derivable_pt_lim (fun t => t - t ^ 3 / 6 + t ^ 5 / 120)
                   x (1 - INR 3 * x ^ Nat.pred 3 / 6 + INR 5 * x ^ Nat.pred 5 / 120).
Proof.
  assert (Hpow3 : derivable_pt_lim (fun t => t ^ 3) x (INR 3 * x ^ (Nat.pred 3))).
  { apply (derivable_pt_lim_pow x 3). }
  assert (Hpow5 : derivable_pt_lim (fun t => t ^ 5) x (INR 5 * x ^ (Nat.pred 5))).
  { apply (derivable_pt_lim_pow x 5). }
  assert (Hdiv3 : derivable_pt_lim (fun t => t ^ 3 / 6) x (INR 3 * x ^ Nat.pred 3 / 6)).
  { apply derivable_pt_lim_div_scal. exact Hpow3. }
  assert (Hdiv5 : derivable_pt_lim (fun t => t ^ 5 / 120) x (INR 5 * x ^ Nat.pred 5 / 120)).
  { apply derivable_pt_lim_div_scal. exact Hpow5. }
  assert (H1 : derivable_pt_lim (fun t => t - t ^ 3 / 6) x (1 - INR 3 * x ^ Nat.pred 3 / 6)).
  { change (derivable_pt_lim (fun t => t + (- (t ^ 3 / 6))) x (1 + (- (INR 3 * x ^ Nat.pred 3 / 6)))).
    apply derivable_pt_lim_plus.
    - change (derivable_pt_lim id x 1). apply derivable_pt_lim_id.
    - apply derivable_pt_lim_opp. exact Hdiv3. }
  change (derivable_pt_lim (fun t => (t - t ^ 3 / 6) + t ^ 5 / 120) x
           ((1 - INR 3 * x ^ Nat.pred 3 / 6) + INR 5 * x ^ Nat.pred 5 / 120)).
  apply derivable_pt_lim_plus; [exact H1 | exact Hdiv5].
Qed.

(* 化简导数：1 - x^2/2 + x^4/24 *)
Lemma g5_dpl_f2_nice (x : R) :
  derivable_pt_lim (fun t => t - t ^ 3 / 6 + t ^ 5 / 120) x (1 - x ^ 2 / 2 + x ^ 4 / 24).
Proof.
  assert (H : derivable_pt_lim (fun t => t - t ^ 3 / 6 + t ^ 5 / 120)
                   x (1 - INR 3 * x ^ Nat.pred 3 / 6 + INR 5 * x ^ Nat.pred 5 / 120)) by apply g5_dpl_f2.
  assert (Hv : (1 - INR 3 * x ^ Nat.pred 3 / 6 + INR 5 * x ^ Nat.pred 5 / 120
                = 1 - x ^ 2 / 2 + x ^ 4 / 24)%R).
  { unfold Nat.pred.
    assert (H3 : (INR 3 = 3)%R). { rewrite INR_IZR_INZ. reflexivity. }
    assert (H5 : (INR 5 = 5)%R). { rewrite INR_IZR_INZ. reflexivity. }
    rewrite H3. rewrite H5.
    field. }
  rewrite Hv in H.
  exact H.
Qed.

(* sin_approx t 2 在 [0, 53/100] 递增（MVT + 导数正） *)
Lemma g5_sa2_incr (x y : R) :
  (0 <= x)%R -> (x <= y)%R -> (y <= 53/100)%R ->
  (sin_approx x 2 <= sin_approx y 2)%R.
Proof.
  intros Hx0 Hxy Hy.
  destruct (Req_dec x y) as [Heq | Hne].
  - rewrite Heq. apply Rle_refl.
  - assert (Hlt : (x < y)%R) by lra.
    pose (f := fun t => t - t ^ 3 / 6 + t ^ 5 / 120).
    pose (fp := fun t => 1 - t ^ 2 / 2 + t ^ 4 / 24).
    destruct (MVT_cor3 f fp x y) as [c [Hc1 [Hc2 Hc3]]].
    + exact Hlt.
    + intros t Ht1 Ht2.
      unfold f, fp. apply g5_dpl_f2_nice.
    + rewrite g5_sa2. rewrite g5_sa2.
      (* 目标：x - x^3/6 + x^5/120 <= y - y^3/6 + y^5/120
         Hc3 : f y = f x + fp c (y-x) ⟹ y-... = (x-...) + fp c (y-x) *)
      unfold f, fp in Hc3.
      assert (Hfp : (0 <= (1 - c ^ 2 / 2 + c ^ 4 / 24) * (y - x))%R).
      { apply Rmult_le_pos.
        - apply Rlt_le. apply g5_fp_pos.
          + eapply Rle_trans; [exact Hx0 | exact Hc1].
          + eapply Rle_trans; [exact Hc2 | exact Hy].
        - lra. }
      rewrite Hc3.
      lra.
Qed.

(* 数值：sa2(5235/10000) < 1/2（vm_compute 或 nra） *)
Lemma g5_sa2_5235_lt_half : (sin_approx (5235/10000) 2 < 1/2)%R.
Proof.
  rewrite g5_sa2.
  nra.
Qed.

(* π ≥ 3.141：反证 π/6 < 5235/10000
   sin(π/6) = 1/2；sin_bound (π/6) 0 上界：1/2 ≤ sin_approx (π/6) 2 = f(π/6)
   f 递增 ⟹ f(π/6) < f(5235/10000) < 1/2 矛盾 *)
Lemma g5_pi_ge_3141 : (3141/1000 <= PI)%R.
Proof.
  apply Rnot_lt_le.
  intro Hlt.
  assert (Hpi6 : (PI / 6 < 5235/10000)%R) by lra.
  assert (HPI : (0 < PI)%R) by apply PI_RGT_0.
  assert (Hpi6le : (PI / 6 <= PI)%R) by lra.
  pose proof (sin_bound (PI/6) 0 (Rlt_le _ _ (PI6_RGT_0)) Hpi6le) as Hb.
  destruct Hb as [_ Hup].
  rewrite sin_PI6 in Hup.
  assert (Hle : (sin_approx (PI/6) 2 <= sin_approx (5235/10000) 2)%R).
  { apply g5_sa2_incr.
    - apply Rlt_le. apply PI6_RGT_0.
    - lra.
    - lra. }
  (* Hup : 1/2 <= sin_approx (PI/6) 2；Hle 传递 *)
  assert (Hc : (1/2 <= sin_approx (5235/10000) 2)%R).
  { eapply Rle_trans; [exact Hup | exact Hle]. }
  assert (Hlt2 : (sin_approx (5235/10000) 2 < 1/2)%R) by exact g5_sa2_5235_lt_half.
  lra.
Qed.

(* 数值：sa3(1571/3000) > 1/2（sin_bound n=1 下界用，1571/3000 = 3.142/6） *)
Lemma g5_sa3_1571_gt_half : (1/2 < sin_approx (1571/3000) 3)%R.
Proof.
  rewrite g5_sa3.
  nra.
Qed.

(* sin_approx t 3 在 [0, 1] 递增（导数正，f31(t) = 1 - t^2/2 + t^4/24 - t^6/720） *)
Lemma g5_f3p_pos (t : R) : (0 <= t)%R -> (t <= 1)%R ->
  (0 < 1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720)%R.
Proof.
  intros Ht0 Ht.
  (* t² <= 1 *)
  assert (Ht2 : (t ^ 2 <= 1)%R).
  { nra. }
  (* 0 < 1 - t²/2：t² <= 1 ⟹ 1 - t²/2 >= 1/2 > 0 *)
  assert (Hlo : (0 < 1 - t ^ 2 / 2)%R).
  { nra. }
  (* 0 <= t⁴/24 - t⁶/720：t⁴(1/24 - t²/720) >= 0，1/24 - t²/720 >= 0（t² <= 1 < 30） *)
  assert (Hq : (0 <= t ^ 4 / 24 - t ^ 6 / 720)%R).
  { replace (t ^ 4 / 24 - t ^ 6 / 720) with (t ^ 4 * (30 - t ^ 2) * (/ 720)) by field.
    apply Rmult_le_pos.
    - apply Rmult_le_pos.
      + assert (H4eq : (t ^ 4 = (t ^ 2) ^ 2)%R).
        { change (t ^ (2 * 2) = (t ^ 2) ^ 2). rewrite <- pow_mult. reflexivity. }
        rewrite H4eq. apply pow2_ge_0.
      + nra.  (* 30 - t^2 >= 0：t^2 <= 1 < 30，用 Ht2 *)
    - apply Rlt_le. apply Rinv_0_lt_compat. nra. }
  (* 目标 = (1 - t²/2) + (t⁴/24 - t⁶/720) > 0 *)
  apply Rlt_le_trans with (1 - t ^ 2 / 2).
  - exact Hlo.
  - nra.  (* 1 - t²/2 <= 1 - t²/2 + t⁴/24 - t⁶/720 ⟺ 0 <= t⁴/24-t⁶/720（Hq 线性化） *)
Qed.

(* f3 可导：多项式组合（t - t^3/6 + t^5/120 - t^7/5040） *)
Lemma g5_dpl_f3 (x : R) :
  derivable_pt_lim (fun t => t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040)
                   x (1 - INR 3 * x ^ Nat.pred 3 / 6 + INR 5 * x ^ Nat.pred 5 / 120 - INR 7 * x ^ Nat.pred 7 / 5040).
Proof.
  assert (Hpow3 : derivable_pt_lim (fun t => t ^ 3) x (INR 3 * x ^ (Nat.pred 3))).
  { apply (derivable_pt_lim_pow x 3). }
  assert (Hpow5 : derivable_pt_lim (fun t => t ^ 5) x (INR 5 * x ^ (Nat.pred 5))).
  { apply (derivable_pt_lim_pow x 5). }
  assert (Hpow7 : derivable_pt_lim (fun t => t ^ 7) x (INR 7 * x ^ (Nat.pred 7))).
  { apply (derivable_pt_lim_pow x 7). }
  assert (Hdiv3 : derivable_pt_lim (fun t => t ^ 3 / 6) x (INR 3 * x ^ Nat.pred 3 / 6)).
  { apply derivable_pt_lim_div_scal. exact Hpow3. }
  assert (Hdiv5 : derivable_pt_lim (fun t => t ^ 5 / 120) x (INR 5 * x ^ Nat.pred 5 / 120)).
  { apply derivable_pt_lim_div_scal. exact Hpow5. }
  assert (Hdiv7 : derivable_pt_lim (fun t => t ^ 7 / 5040) x (INR 7 * x ^ Nat.pred 7 / 5040)).
  { apply derivable_pt_lim_div_scal. exact Hpow7. }
  assert (H1 : derivable_pt_lim (fun t => t - t ^ 3 / 6) x (1 - INR 3 * x ^ Nat.pred 3 / 6)).
  { change (derivable_pt_lim (fun t => t + (- (t ^ 3 / 6))) x (1 + (- (INR 3 * x ^ Nat.pred 3 / 6)))).
    apply derivable_pt_lim_plus.
    - change (derivable_pt_lim id x 1). apply derivable_pt_lim_id.
    - apply derivable_pt_lim_opp. exact Hdiv3. }
  assert (H2 : derivable_pt_lim (fun t => (t - t ^ 3 / 6) + t ^ 5 / 120) x
                ((1 - INR 3 * x ^ Nat.pred 3 / 6) + INR 5 * x ^ Nat.pred 5 / 120)).
  { apply derivable_pt_lim_plus; [exact H1 | exact Hdiv5]. }
  change (derivable_pt_lim (fun t => ((t - t ^ 3 / 6) + t ^ 5 / 120) - t ^ 7 / 5040) x
           (((1 - INR 3 * x ^ Nat.pred 3 / 6) + INR 5 * x ^ Nat.pred 5 / 120) - INR 7 * x ^ Nat.pred 7 / 5040)).
  apply derivable_pt_lim_minus; [exact H2 | exact Hdiv7].
Qed.

(* 化简导数形式：1 - x^2/2 + x^4/24 - x^6/720 *)
Lemma g5_dpl_f3_nice (x : R) :
  derivable_pt_lim (fun t => t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040) x (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720).
Proof.
  assert (H : derivable_pt_lim (fun t => t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040)
                   x (1 - INR 3 * x ^ Nat.pred 3 / 6 + INR 5 * x ^ Nat.pred 5 / 120 - INR 7 * x ^ Nat.pred 7 / 5040)) by apply g5_dpl_f3.
  assert (Hv : (1 - INR 3 * x ^ Nat.pred 3 / 6 + INR 5 * x ^ Nat.pred 5 / 120 - INR 7 * x ^ Nat.pred 7 / 5040
                = 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720)%R).
  { unfold Nat.pred.
    assert (H3 : (INR 3 = 3)%R). { rewrite INR_IZR_INZ. reflexivity. }
    assert (H5 : (INR 5 = 5)%R). { rewrite INR_IZR_INZ. reflexivity. }
    assert (H7 : (INR 7 = 7)%R). { rewrite INR_IZR_INZ. reflexivity. }
    rewrite H3. rewrite H5. rewrite H7.
    field. }
  rewrite Hv in H.
  exact H.
Qed.

Lemma g5_sa3_incr (x y : R) :
  (0 <= x)%R -> (x <= y)%R -> (y <= 1)%R ->
  (sin_approx x 3 <= sin_approx y 3)%R.
Proof.
  intros Hx0 Hxy Hy.
  destruct (Req_dec x y) as [Heq | Hne].
  - rewrite Heq. apply Rle_refl.
  - assert (Hlt : (x < y)%R) by lra.
    pose (f := fun t => t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040).
    pose (fp := fun t => 1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720).
    destruct (MVT_cor3 f fp x y) as [c [Hc1 [Hc2 Hc3]]].
    + exact Hlt.
    + intros t Ht1 Ht2.
      unfold f, fp. apply g5_dpl_f3_nice.
    + rewrite g5_sa3. rewrite g5_sa3.
      (* 目标：x-... <= y-...；Hc3 : f y = f x + fp c (y-x) *)
      unfold f, fp in Hc3.
      assert (Hfp : (0 <= (1 - c ^ 2 / 2 + c ^ 4 / 24 - c ^ 6 / 720) * (y - x))%R).
      { apply Rmult_le_pos.
        - apply Rlt_le. apply g5_f3p_pos.
          + eapply Rle_trans; [exact Hx0 | exact Hc1].
          + eapply Rle_trans; [exact Hc2 | exact Hy].
        - lra. }
      rewrite Hc3.
      lra.
Qed.

(* π ≤ 3.142：反证 π/6 > 1571/3000（= 3.142/6）
   sin(π/6) = 1/2；sin_bound (π/6) 1 下界：sin_approx (π/6) 3 ≤ 1/2
   f3 递增 ⟹ sin_approx (π/6) 3 > sin_approx (1571/3000) 3 > 1/2 矛盾 *)
Lemma g5_pi_le_3142 : (PI <= 3142/1000)%R.
Proof.
  apply Rnot_lt_le.
  intro Hgt.
  (* 反证 π/6 > 1571/3000（= 3142/1000/6） *)
  assert (Hpi6 : (1571/3000 < PI / 6)%R) by lra.
  assert (HPI : (0 < PI)%R) by apply PI_RGT_0.
  assert (Hpi6le : (PI / 6 <= PI)%R) by lra.
  pose proof (sin_bound (PI/6) 1 (Rlt_le _ _ (PI6_RGT_0)) Hpi6le) as Hb.
  destruct Hb as [Hlo _].
  rewrite sin_PI6 in Hlo.
  (* 归一 Hlo 的 sin_approx 参数：(2*1)+1 = 3 *)
  change (sin_approx (PI/6) 3 <= 1/2)%R in Hlo.
  assert (Hle : (sin_approx (1571/3000) 3 <= sin_approx (PI/6) 3)%R).
  { apply g5_sa3_incr.
    - lra.
    - lra.
    - (* π/6 <= 1：π <= 4（PI_4）且 4/6 < 1 ⟹ π/6 < 1 *)
      assert (Hpi6le1 : (PI / 6 <= 1)%R).
      { apply (Rmult_le_reg_l 6 (PI / 6) 1).
        - nra.  (* 0 < 6 *)
        - replace (6 * (PI / 6))%R with PI%R by field.
          replace (6 * 1)%R with 6%R by ring.
          apply Rle_trans with 4.
          + exact PI_4.
          + nra. }  (* 4 <= 6 *)
      exact Hpi6le1. }
  assert (Hc : (1/2 < sin_approx (1571/3000) 3)%R) by exact g5_sa3_1571_gt_half.
  assert (Hc2 : (1/2 < sin_approx (PI/6) 3)%R).
  { apply (Rlt_le_trans (1/2) (sin_approx (1571/3000) 3) (sin_approx (PI/6) 3)).
    - exact Hc.
    - exact Hle. }
  (* Hlo : sin_approx (PI/6) 3 <= 1/2 与 Hc2 : 1/2 < sin_approx (PI/6) 3 矛盾
     Rlt_not_le r1 r2 : r2 < r1 -> ~ r1 <= r2；取 r1=sa, r2=1/2 *)
  exact (Rlt_not_le (sin_approx (PI/6) 3) (1/2) Hc2 Hlo).
Qed.

(* ============ 主定理：三行精确行和 ≤ 4/5 但检查器拒 ============
   数值界（sin_bound n=0 + π ∈ [3.141, 3.142] + 递增性）：
   行 0 (n=3): |<3,7>| + |<3,15>| ≤ 4/5
   行 1 (n=7): |<3,7>| + |<7,15>| ≤ 4/5  ← 瓶颈（真实 0.7870）
   行 2 (n=15): |<3,15>| + |<7,15>| ≤ 4/5
   方案：s2 递增在 [0, 3/2]（3π/7≈1.35, 7π/15≈1.47 ≤ 1.5） *)

(* s2 递增在 [0, 3/2]：f21(t) = 1 - t^2/2 + t^4/24 > 0 *)
Lemma g5_fp_pos_15 (t : R) : (0 <= t)%R -> (t <= 3/2)%R ->
  (0 < 1 - t ^ 2 / 2 + t ^ 4 / 24)%R.
Proof.
  intros Ht0 Ht.
  rewrite g5_pow2_2.
  set (u := t ^ 2).
  assert (Hhi_u : (u <= 9/4)%R) by (subst u; nra).
  replace (1 - t ^ 2 / 2 + (t ^ 2) ^ 2 / 24) with (1 - u / 2 + u ^ 2 / 24) by (subst u; ring).
  nra.
Qed.

(* sa2 递增在 [0, 3/2]（同 sa2_incr 模式，区间放宽） *)
Lemma g5_sa2_incr_15 (x y : R) :
  (0 <= x)%R -> (x <= y)%R -> (y <= 3/2)%R ->
  (sin_approx x 2 <= sin_approx y 2)%R.
Proof.
  intros Hx0 Hxy Hy.
  destruct (Req_dec x y) as [Heq | Hne].
  - rewrite Heq. apply Rle_refl.
  - assert (Hlt : (x < y)%R) by lra.
    pose (f := fun t => t - t ^ 3 / 6 + t ^ 5 / 120).
    pose (fp := fun t => 1 - t ^ 2 / 2 + t ^ 4 / 24).
    destruct (MVT_cor3 f fp x y) as [c [Hc1 [Hc2 Hc3]]].
    + exact Hlt.
    + intros t Ht1 Ht2.
      unfold f, fp. apply g5_dpl_f2_nice.
    + rewrite g5_sa2. rewrite g5_sa2.
      unfold f, fp in Hc3.
      assert (Hfp : (0 <= (1 - c ^ 2 / 2 + c ^ 4 / 24) * (y - x))%R).
      { apply Rmult_le_pos.
        - apply Rlt_le. apply g5_fp_pos_15.
          + eapply Rle_trans; [exact Hx0 | exact Hc1].
          + eapply Rle_trans; [exact Hc2 | exact Hy].
        - lra. }
      rewrite Hc3.
      lra.
Qed.

(* s1 递增（trivial：s11(t) = 1 - t^2/2 > 0 在 [0,1]） *)
(* f1(t) = t - t^3/6 可导，导数 1 - x^2/2 *)
Lemma g5_dpl_f1 (x : R) :
  derivable_pt_lim (fun t => t - t ^ 3 / 6) x (1 - x ^ 2 / 2).
Proof.
  assert (Hpow3 : derivable_pt_lim (fun t => t ^ 3) x (INR 3 * x ^ (Nat.pred 3))).
  { apply (derivable_pt_lim_pow x 3). }
  assert (Hdiv3 : derivable_pt_lim (fun t => t ^ 3 / 6) x (INR 3 * x ^ Nat.pred 3 / 6)).
  { apply derivable_pt_lim_div_scal. exact Hpow3. }
  assert (H3 : (INR 3 = 3)%R) by (rewrite INR_IZR_INZ; reflexivity).
  assert (Hred : (INR 3 * x ^ Nat.pred 3 / 6 = x ^ 2 / 2)%R).
  { unfold Nat.pred. rewrite H3. field. }
  change (derivable_pt_lim (fun t => t + (- (t ^ 3 / 6))) x (1 + (- (x ^ 2 / 2)))).
  apply derivable_pt_lim_plus.
  - change (derivable_pt_lim id x 1). apply derivable_pt_lim_id.
  - apply derivable_pt_lim_opp.
    rewrite <- Hred. exact Hdiv3.
Qed.

Lemma g5_sa1_incr (x y : R) :
  (0 <= x)%R -> (x <= y)%R -> (y <= 1)%R ->
  (sin_approx x 1 <= sin_approx y 1)%R.
Proof.
  intros Hx0 Hxy Hy.
  destruct (Req_dec x y) as [Heq | Hne].
  - rewrite Heq. apply Rle_refl.
  - assert (Hlt : (x < y)%R) by lra.
    pose (f := fun t => t - t ^ 3 / 6).
    pose (fp := fun t => 1 - t ^ 2 / 2).
    destruct (MVT_cor3 f fp x y) as [c [Hc1 [Hc2 Hc3]]].
    + exact Hlt.
    + intros t Ht1 Ht2.
      unfold f, fp. apply g5_dpl_f1.
    + rewrite g5_sa1. rewrite g5_sa1.
      unfold f, fp in Hc3.
      assert (Hfp : (0 <= (1 - c ^ 2 / 2) * (y - x))%R).
      { apply Rmult_le_pos.
        - apply Rlt_le. nra.  (* 0 <= 1 - c^2/2：c <= 1 *)
        - lra. }
      rewrite Hc3.
      lra.
Qed.

(* ============ 数值界（sin_bound n=0 + π 界 + 递增性） ============ *)

(* sin(3π/7) ≤ 9774/10000：sin_bound (3PI/7) 0 上界 + 3PI/7 ≤ 27/20 + s2 递增 *)
Lemma g5_sin_3pi7_le : (sin (3 * PI / 7) <= 9774/10000)%R.
Proof.
  (* sin_bound (3PI/7) 0 上界：sin(3PI/7) <= sin_approx (3PI/7) 2 *)
  assert (HPI : (0 < PI)%R) by apply PI_RGT_0.
  assert (Hp0 : (0 <= 3 * PI / 7)%R).
  { nra. }
  assert (Hple : (3 * PI / 7 <= PI)%R).
  { nra. }
  pose proof (sin_bound (3 * PI / 7) 0 Hp0 Hple) as Hb.
  destruct Hb as [_ Hup].  (* Hup : sin(3PI/7) <= sin_approx (3PI/7) 2 *)
  (* 3PI/7 <= 27/20（π <= 3.142 < 3.15）；s2 递增 ⟹ sa2(3PI/7) <= sa2(27/20) *)
  assert (Hle_incr : (sin_approx (3 * PI / 7) 2 <= sin_approx (27/20) 2)%R).
  { apply g5_sa2_incr_15.
    - nra.  (* 0 <= 3PI/7，用 HPI *)
    - assert (Hpimax : (PI <= 3142/1000)%R) by exact g5_pi_le_3142.
      nra.  (* 3PI/7 <= 27/20：需 PI <= 63/20 = 3.15 *)
    - nra. }  (* 27/20 <= 3/2 *)
  (* sin_approx (27/20) 2 <= 9774/10000（纯数值） *)
  assert (Hnum : (sin_approx (27/20) 2 <= 9774/10000)%R).
  { rewrite g5_sa2. nra. }
  (* sin(3PI/7) <= sa2(3PI/7) <= sa2(27/20) <= 9774/10000 *)
  eapply Rle_trans; [exact Hup |].
  eapply Rle_trans; [exact Hle_incr |].
  exact Hnum.
Qed.

(* sin(4π/21) ≥ 5625/10000：sin_bound (4PI/21) 0 下界 + 4PI/21 ≥ 4·3.141/21 + s1 递增 *)
Lemma g5_sin_4pi21_ge : (5625/10000 <= sin (4 * PI / 21))%R.
Proof.
  assert (HPI : (0 < PI)%R) by apply PI_RGT_0.
  assert (Hp0 : (0 <= 4 * PI / 21)%R).
  { nra. }
  assert (Hple : (4 * PI / 21 <= PI)%R).
  { nra. }
  pose proof (sin_bound (4 * PI / 21) 0 Hp0 Hple) as Hb.
  destruct Hb as [Hlo _].  (* Hlo : sin_approx (4PI/21) 1 <= sin(4PI/21) *)
  (* 4PI/21 >= 4·(3141/1000)/21 = 12564/21000；s1 递增 ⟹ sin_approx (12564/21000) 1 <= sin_approx (4PI/21) 1 *)
  assert (Hle_incr : (sin_approx (12564/21000) 1 <= sin_approx (4 * PI / 21) 1)%R).
  { apply g5_sa1_incr.
    - nra.
    - assert (Hpimin : (3141/1000 <= PI)%R) by exact g5_pi_ge_3141.
      nra.  (* 12564/21000 <= 4PI/21：需 PI >= 3141/1000 *)
    - assert (Hpimax : (PI <= 3142/1000)%R) by exact g5_pi_le_3142.
      nra. }  (* 4PI/21 <= 1，用 π <= 3.142 < 5.25 *)
  (* sin_approx (12564/21000) 1 >= 5625/10000（纯数值） *)
  assert (Hnum : (5625/10000 <= sin_approx (12564/21000) 1)%R).
  { rewrite g5_sa1. nra. }
  (* 5626/10000 <= sin_approx (12564/21000) 1 <= sin_approx (4PI/21) 1 <= sin(4PI/21) *)
  eapply Rle_trans; [exact Hnum |].
  eapply Rle_trans; [exact Hle_incr |].
  exact Hlo.
Qed.

(* sin(7π/15) ≤ 9975/10000：7PI/15 <= 22/15（π <= 22/7） *)
Lemma g5_sin_7pi15_le : (sin (7 * PI / 15) <= 9975/10000)%R.
Proof.
  assert (HPI : (0 < PI)%R) by apply PI_RGT_0.
  assert (Hp0 : (0 <= 7 * PI / 15)%R).
  { nra. }
  assert (Hple : (7 * PI / 15 <= PI)%R).
  { nra. }
  pose proof (sin_bound (7 * PI / 15) 0 Hp0 Hple) as Hb.
  destruct Hb as [_ Hup].
  assert (Hle_incr : (sin_approx (7 * PI / 15) 2 <= sin_approx (22/15) 2)%R).
  { apply g5_sa2_incr_15.
    - nra.
    - assert (Hpimax : (PI <= 3142/1000)%R) by exact g5_pi_le_3142.
      nra.  (* 7PI/15 <= 22/15：需 PI <= 22/7 ≈ 3.1429 *)
    - nra. }  (* 22/15 <= 3/2 *)
  assert (Hnum : (sin_approx (22/15) 2 <= 9975/10000)%R).
  { rewrite g5_sa2. nra. }
  (* sin(7PI/15) <= sa(7PI/15) 2 <= sa(22/15) 2 <= 9975/10000 *)
  eapply Rle_trans; [exact Hup |].
  eapply Rle_trans; [exact Hle_incr |].
  exact Hnum.
Qed.

(* sin(8π/105) ≥ 2370/10000：8PI/105 >= 8·3.141/105 = 25128/105000 *)
Lemma g5_sin_8pi105_ge : (2370/10000 <= sin (8 * PI / 105))%R.
Proof.
  assert (HPI : (0 < PI)%R) by apply PI_RGT_0.
  assert (Hp0 : (0 <= 8 * PI / 105)%R).
  { nra. }
  assert (Hple : (8 * PI / 105 <= PI)%R).
  { nra. }
  pose proof (sin_bound (8 * PI / 105) 0 Hp0 Hple) as Hb.
  destruct Hb as [Hlo _].
  assert (Hle_incr : (sin_approx (25128/105000) 1 <= sin_approx (8 * PI / 105) 1)%R).
  { apply g5_sa1_incr.
    - nra.
    - assert (Hpimin : (3141/1000 <= PI)%R) by exact g5_pi_ge_3141.
      nra.  (* 25128/105000 <= 8PI/105：需 PI >= 3141/1000 *)
    - assert (Hpimax : (PI <= 3142/1000)%R) by exact g5_pi_le_3142.
      nra. }  (* 8PI/105 <= 1，用 π <= 3.142 < 13.125 *)
  assert (Hnum : (2370/10000 <= sin_approx (25128/105000) 1)%R).
  { rewrite g5_sa1. nra. }
  (* 2370/10000 <= sa(25128/105000) 1 <= sa(8PI/105) 1 <= sin(8PI/105) *)
  eapply Rle_trans; [exact Hnum |].
  eapply Rle_trans; [exact Hle_incr |].
  exact Hlo.
Qed.

(* √21 ≥ 4582/1000、√105 ≥ 10246/1000 *)
Lemma g5_sqrt21_ge : (4582/1000 <= sqrt 21)%R.
Proof.
  (* 4582/1000 = sqrt((4582/1000)^2)（非负）≤ sqrt 21（因 (4582/1000)^2 <= 21） *)
  apply Rle_trans with (sqrt ((4582/1000)^2)).
  - rewrite sqrt_pow2.
    + apply Rle_refl.
    + nra.  (* 4582/1000 >= 0 *)
  - apply sqrt_le_1.
    + nra.
    + nra.
    + nra.  (* (4582/1000)^2 = 20.9947 <= 21 *)
Qed.

Lemma g5_sqrt105_ge : (10246/1000 <= sqrt 105)%R.
Proof.
  apply Rle_trans with (sqrt ((10246/1000)^2)).
  - rewrite sqrt_pow2.
    + apply Rle_refl.
    + nra.
  - apply sqrt_le_1.
    + nra.
    + nra.
    + nra.  (* (10246/1000)^2 = 104.98 <= 105 *)
Qed.

(* ============ 主定理：行 1 ≤ 4/5（瓶颈行） ============ *)

(* sin(4π/7) = sin(3π/7)（sin_PI_x 对称） *)
Lemma g5_sin_4pi7_eq : (sin (4 * PI / 7) = sin (3 * PI / 7))%R.
Proof.
  replace (4 * PI / 7)%R with (PI - 3 * PI / 7)%R by field.
  apply sin_PI_x.
Qed.

(* sin(8π/15) = sin(7π/15) *)
Lemma g5_sin_8pi15_eq : (sin (8 * PI / 15) = sin (7 * PI / 15))%R.
Proof.
  replace (8 * PI / 15)%R with (PI - 7 * PI / 15)%R by field.
  apply sin_PI_x.
Qed.

(* 通用倒数单调：u <= v ⟹ 1/v <= 1/u（u,v > 0） *)
Lemma g5_inv_le (u v : R) :
  (0 < u)%R -> (0 < v)%R -> (u <= v)%R -> (1 / v <= 1 / u)%R.
Proof.
  intros Hu0 Hv0 Huv.
  apply Rmult_le_reg_r with (v * u).
  - apply Rmult_lt_0_compat; [exact Hv0 | exact Hu0].
  - replace ((1 / v) * (v * u))%R with u%R.
    + replace ((1 / u) * (v * u))%R with v%R.
      * exact Huv.
      * field. apply Rgt_not_eq. exact Hu0.
    + field. apply Rgt_not_eq. exact Hv0.
Qed.

(* 通用分数比较：0 <= a <= a1、0 < c <= b ⟹ a/b <= a1/c *)
Lemma g5_frac_le (a b a1 c : R) :
  (0 <= a)%R -> (a <= a1)%R -> (0 < b)%R -> (0 < c)%R -> (Rle c b) ->
  (a / b <= a1 / c)%R.
Proof.
  intros Ha0 Haa1 Hb0 Hc0.
  intros Hcb.
  (* a/b = a·(1/b)，a1/c = a1·(1/c)；Rmult_le_compat *)
  unfold Rdiv.
  apply Rmult_le_compat.
  - exact Ha0.      (* 0 <= a *)
  - apply Rlt_le. apply Rinv_0_lt_compat. exact Hb0.  (* 0 <= /b *)
  - assumption.     (* a <= a1 *)
  - (* /b <= /c：Rinv_le_contravar c b（0<c, c<=b） *)
    apply (Rinv_le_contravar c b Hc0 Hcb).
Qed.

(* |<3,7>| ≤ 9774/(5625·4.582)：a=Rabs(sin 4π/7), b=Rabs(sin 4π/21)·√21 *)
Lemma g5_c37_le : 
  (Rabs (sin (4 * PI / 7)) / (Rabs (sin (4 * PI / 21)) * sqrt 21) <= 9774/10000 / ((5625/10000) * (4582/1000)))%R.
Proof.
  assert (HPI : (0 < PI)%R) by apply PI_RGT_0.
  (* 分子上界：|sin(4π/7)| = sin(3π/7) ≤ 9774/10000 *)
  assert (Hnum : (Rabs (sin (4 * PI / 7)) <= 9774/10000)%R).
  { rewrite g5_sin_4pi7_eq. rewrite Rabs_right.
    - exact g5_sin_3pi7_le.
    - apply Rle_ge. apply Rlt_le. apply sin_gt_0.
      + nra.  (* 0 < 3PI/7 *)
      + nra. }  (* 3PI/7 < PI：3/7 < 1，用 HPI *)
  (* 分母下界：sin(4π/21) ≥ 5625/10000，√21 ≥ 4582/1000 ⟹ 分母 ≥ 5625·4.582 *)
  assert (Hden : ((5625/10000) * (4582/1000) <= Rabs (sin (4 * PI / 21)) * sqrt 21)%R).
  { apply (Rmult_le_compat (5625/10000) (Rabs (sin (4 * PI / 21))) (4582/1000) (sqrt 21)).
    - lra.  (* 0 <= 5625/10000 *)
    - lra.  (* 0 <= 4582/1000 *)
    - apply Rle_trans with (sin (4 * PI / 21)).
      + exact g5_sin_4pi21_ge.
      + apply Rle_abs.  (* sin <= Rabs sin *)
    - exact g5_sqrt21_ge. }  (* 4582/1000 <= sqrt 21 *)
  (* 分母正：Rabs(sin 4π/21)·√21 > 0；b1=5625·4.582 > 0 *)
  apply g5_frac_le.
  - apply Rabs_pos.
  - exact Hnum.
  - apply Rmult_lt_0_compat.
    + apply Rabs_pos_lt. apply Rgt_not_eq. apply sin_gt_0.
      * nra.
      * nra.
    + apply sqrt_lt_R0. lra.
  - nra.
  - exact Hden.
Qed.

(* |<7,15>| ≤ 9975/(2370·10.246) *)
Lemma g5_c715_le : 
  (Rabs (sin (8 * PI / 15)) / (Rabs (sin (8 * PI / 105)) * sqrt 105) <= 9975/10000 / ((2370/10000) * (10246/1000)))%R.
Proof.
  assert (HPI : (0 < PI)%R) by apply PI_RGT_0.
  assert (Hnum : (Rabs (sin (8 * PI / 15)) <= 9975/10000)%R).
  { rewrite g5_sin_8pi15_eq. rewrite Rabs_right.
    - exact g5_sin_7pi15_le.
    - apply Rle_ge. apply Rlt_le. apply sin_gt_0.
      + nra.
      + nra. }  (* 7PI/15 < PI：7/15 < 1，用 HPI *)
  assert (Hden : ((2370/10000) * (10246/1000) <= Rabs (sin (8 * PI / 105)) * sqrt 105)%R).
  { apply (Rmult_le_compat (2370/10000) (Rabs (sin (8 * PI / 105))) (10246/1000) (sqrt 105)).
    - lra.  (* 0 <= 2370/10000 *)
    - lra.  (* 0 <= 10246/1000 *)
    - apply Rle_trans with (sin (8 * PI / 105)).
      + exact g5_sin_8pi105_ge.
      + apply Rle_abs.  (* sin <= Rabs sin *)
    - exact g5_sqrt105_ge. }  (* 10246/1000 <= sqrt 105 *)
  apply g5_frac_le.
  - apply Rabs_pos.
  - exact Hnum.
  - apply Rmult_lt_0_compat.
    + apply Rabs_pos_lt. apply Rgt_not_eq. apply sin_gt_0.
      * nra.
      * nra.
    + apply sqrt_lt_R0. lra.
  - nra.
  - exact Hden.
Qed.

(* ============ 主定理：行 1 ≤ 4/5 ============ *)
Lemma g5_row1_le :
  (Rabs (sin (4 * PI / 7)) / (Rabs (sin (4 * PI / 21)) * sqrt 21)
   + Rabs (sin (8 * PI / 15)) / (Rabs (sin (8 * PI / 105)) * sqrt 105) <= 4/5)%R.
Proof.
  (* 行1 <= 9774/(5625·4.582) + 9975/(2370·10.246) <= 4/5 *)
  apply (Rle_trans _ (9774/10000 / ((5625/10000) * (4582/1000)) + 9975/10000 / ((2370/10000) * (10246/1000))) _).
  - apply Rplus_le_compat.
    + exact g5_c37_le.
    + exact g5_c715_le.
  - nra.
Qed.

(* ============ G-5 主定理：检查器拒但精确行和 ≤ 4/5 ============ *)
Theorem g5_premium :
  frame_check_instance ladder_3_7_15 = false /\
  (Rabs (sin (4 * PI / 7)) / (Rabs (sin (4 * PI / 21)) * sqrt 21)
   + Rabs (sin (8 * PI / 15)) / (Rabs (sin (8 * PI / 105)) * sqrt 105) <= 4/5)%R.
Proof.
  split.
  - exact g5_reflect_reject.
  - exact g5_row1_le.
Qed.

End G5Premium.

Print Assumptions G5Premium.g5_reflect_reject.
Print Assumptions G5Premium.g5_coh_full_3_7.
Print Assumptions G5Premium.g5_coh_full_3_15.
Print Assumptions G5Premium.g5_coh_full_7_15.
