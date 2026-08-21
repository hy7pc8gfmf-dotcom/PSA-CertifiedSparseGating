(* PSA 框架公理审计（会话 3 扩展：覆盖全部新证引理 + P2 两条路线） *)
Require Import Stdlib.Reals.Reals.
Require Import Stdlib.micromega.Lra.
Require Import Stdlib.Bool.Bool.
Require Import ca_base ca_complex_foundation ca_independence ca_basis ca_basis_lemmas ca_decay.
Import ComplexNumbers.
Require Import PSA.PSA_framework.

(* 管线定理（原审计项） *)
Print Assumptions PSA_Pipeline.psa_pipeline_decay.
Print Assumptions PSA_Pipeline.psa_pipeline_linindep.
Print Assumptions RuntimeGuards.all_ge_2P.

(* 会话 3 新证：守护断言反射层（应为零公理 / 仅 Reals 基础公理，零 classic） *)
Print Assumptions RuntimeGuards.forallb_adjacent_nth.
Print Assumptions RuntimeGuards.forallb_adjacent_from_nth.
Print Assumptions RuntimeGuards.forallb_adjacent_sorted_implies.
Print Assumptions RuntimeGuards.sparse_growth_trans.
Print Assumptions RuntimeGuards.square_le_trans.
Print Assumptions RuntimeGuards.sorted_of_strict_adjacent.
Print Assumptions RuntimeGuards.nth_incr.
Print Assumptions RuntimeGuards.check_sparse_growthP.
Print Assumptions RuntimeGuards.check_c_sparse_growthP.
Print Assumptions RuntimeGuards.check_c_sparse_on_valsP.

(* 会话 3 新证：生成器正确性（应为零公理） *)
Print Assumptions SeqProps.rev_cons.
Print Assumptions SeqProps.gen_aux_tail.
Print Assumptions SeqProps.generate_rec.
Print Assumptions SeqProps.generate_nth0.
Print Assumptions SeqProps.generate_indices_spec.
Print Assumptions SeqProps.generate_correct.

(* 会话 3 新证：P2 内部序列路线（应为零公理） *)
Print Assumptions SeqProps.base_seq_global_growth.
Print Assumptions SeqProps.base_seq_shift.
Print Assumptions SeqProps.seq_shift_gen.
Print Assumptions SeqProps.generate_eq_map.

(* 会话 3 新证：P2 外部守卫路线（桥梁/链/有限化，应为零公理或仅 sig_forall_dec+fext） *)
Print Assumptions PSA_Pipeline.guard_adjacent_growth.
Print Assumptions PSA_Pipeline.guard_ge2_map.
Print Assumptions PSA_Pipeline.nth_lt_backward.
Print Assumptions PSA_Pipeline.fold_right_max_In.
Print Assumptions PSA_Pipeline.I_chain_strict.
Print Assumptions PSA_Pipeline.I_chain_compound.
Print Assumptions PSA_Pipeline.Csum_psi_conj_truncate_fin.
Print Assumptions PSA_Pipeline.decay_bound_finite_one_factor.
Print Assumptions PSA_Pipeline.psa_guard_decay.
Print Assumptions PSA_Pipeline.decay_bound_finite_one_factor_tight.
Print Assumptions PSA_Pipeline.psa_guard_decay_tight.

(* 会话 4 续：P0 确定性贪心门控（应为零公理；仅 c_sparse_subset 推论继承 sig_forall_dec+fext） *)
Print Assumptions GreedyGate.greedy_aux_In.
Print Assumptions GreedyGate.greedy_selected_In.
Print Assumptions GreedyGate.greedy_aux_all_ge_2.
Print Assumptions GreedyGate.greedy_selected_all_ge_2.
Print Assumptions GreedyGate.greedy_aux_NoDup.
Print Assumptions GreedyGate.greedy_selected_NoDup.
Print Assumptions GreedyGate.sorted_lt_all.
Print Assumptions GreedyGate.greedy_Sorted_NoDup.
Print Assumptions GreedyGate.greedy_aux_Sorted.
Print Assumptions GreedyGate.greedy_selected_Sorted.
Print Assumptions GreedyGate.greedy_aux_head_growth.
Print Assumptions GreedyGate.greedy_aux_adjacent_growth.
Print Assumptions GreedyGate.greedy_selected_adjacent_growth.
Print Assumptions GreedyGate.greedy_selected_strict_growth.
Print Assumptions GreedyGate.greedy_selected_c_sparse_check.
Print Assumptions GreedyGate.greedy_selected_correct.
Print Assumptions GreedyGate.greedy_selected_c_sparse_subset.
Print Assumptions GreedyGate.mask_aux_length.
Print Assumptions GreedyGate.fallback_mask_length.
Print Assumptions GreedyGate.mask_aux_correct.
Print Assumptions GreedyGate.fallback_mask_correct.
Print Assumptions GreedyGate.fallback_mask_linear_sparse.
Print Assumptions GreedyGate.greedy_selected_guard_pass.

(* 会话 5 续：P0→P2 实例化桥 + P1a（零公理；psa_gated_decay 继承 psa_guard_decay 的 sig_not_dec+sig_forall_dec+fext） *)
Print Assumptions SeqProps.map_nth_seq.
Print Assumptions SeqProps.base_seq_list_Sorted.
Print Assumptions SeqProps.construct_base_sequence.
Print Assumptions SeqProps.construct_base_sequence_map.
Print Assumptions GreedyGate.greedy_idx_aux_In.
Print Assumptions GreedyGate.greedy_idx_aux_Sorted.
Print Assumptions GreedyGate.greedy_indices_Sorted.
Print Assumptions GreedyGate.greedy_idx_aux_map.
Print Assumptions GreedyGate.greedy_indices_map.
Print Assumptions GreedyGate.psa_gated_decay.
Print Assumptions GreedyGate.psa_gated_decay_base_seq.

(* 会话 5 续：P1b 行截断误差（R 级引理经 Reals 继承 sig_forall_dec+fext，零 classic） *)
Print Assumptions RowTruncation.list_sum_R.
Print Assumptions RowTruncation.sum_filter_compl.
Print Assumptions RowTruncation.complement_sum_bound.
Print Assumptions RowTruncation.row_score.
Print Assumptions RowTruncation.row_energy_bound.
Print Assumptions RowTruncation.row_truncation_error.
Print Assumptions RowTruncation.row_dropped_energy_bound.

(* 会话 5 续：端到端管线定理 + P3（R 级经 Reals / 库内定理继承，零 classic） *)
Print Assumptions SeqProps.base_seq_strictly_increasing.
Print Assumptions PipelineEndToEnd.psa_low_coherence.
Print Assumptions PipelineEndToEnd.psa_pipeline_guard.
Print Assumptions PipelineEndToEnd.row_energy_bound_wide.
Print Assumptions PipelineEndToEnd.psa_frame_bounds.
Print Assumptions PipelineEndToEnd.psa_low_coherence_tight.

(* 会话 5 终轮：A1 softmax 敏感性引理（M1，R 级经 Reals 继承）
   ⚠️ 勘误（2026-08-19）：softmax_ratio_le2 / softmax_diff_i / softmax_l1_bound_exp
   经 exp_mono_le ← exp_increasing（Rpower，导数/MVT 路线）继承 Classical_Prop.classic——
   此前交接文档称"85 项全部零 classic"不准确；softmax_sum_one 本身零公理。
   消除路线（后续）：用 exp_plus + exp_pos + exp_form（全部零 classic）重证 exp 单调性。 *)
Print Assumptions SoftmaxStability.softmax_sum_one.
Print Assumptions SoftmaxStability.softmax_ratio_le2.
Print Assumptions SoftmaxStability.softmax_diff_i.
Print Assumptions SoftmaxStability.softmax_l1_bound_exp.

(* M2（2026-08-19）：T3 认证低秩链条
   14/15 项零 classic（纯列表/复代数/Reals 无 classic 部分）；
   certified_attention_approx 经 softmax_l1_bound_exp 继承 Classical_Prop.classic
   （同 M1 勘误，exp 单调性路线；链条数学不受影响）。 *)
Print Assumptions CertifiedAttention.Complex_eq_local.
Print Assumptions CertifiedAttention.list_sum_R_map.
Print Assumptions CertifiedAttention.sum_f_R0_shift_head.
Print Assumptions CertifiedAttention.list_sum_R_seq_eq_sum_f_R0.
Print Assumptions CertifiedAttention.Rsqr_le_list_sum.
Print Assumptions CertifiedAttention.linf_le_sqrt_sqsum.
Print Assumptions CertifiedAttention.Csum_norm_le_sum_pred.
Print Assumptions CertifiedAttention.Cnorm_Cof_real_abs.
Print Assumptions CertifiedAttention.Cof_real_minus.
Print Assumptions CertifiedAttention.Csub_add_distr.
Print Assumptions CertifiedAttention.Cmul_sub_distr_l.
Print Assumptions CertifiedAttention.Csum_minus.
Print Assumptions CertifiedAttention.attention_output_diff.
Print Assumptions CertifiedAttention.weighted_avg_lipschitz.
Print Assumptions CertifiedAttention.certified_attention_approx.

(* M3（2026-08-19）：B1 Gershgorin 框架 + B2 Dirichlet 闭式
   全部零 classic（R 级经 Reals 继承 sig_forall_dec+fext；sin 等 Rtrigo 引理无 classic）。 *)
Print Assumptions Gershgorin.gershgorin_frame.
Print Assumptions Gershgorin.gershgorin_frame_mu.
Print Assumptions Gershgorin.Cexp_pow_local.
Print Assumptions Gershgorin.geom_sum_norm_dirichlet.
Print Assumptions Gershgorin.dirichlet_algebra.
Print Assumptions Gershgorin.psi_inner_dirichlet.

(* M4 Tier 1（2026-08-19）：C=4 实例证书（零 classic，R 级经 Reals 继承） *)
Print Assumptions InstanceCertificate.psi_inner_cons_bound.
Print Assumptions InstanceCertificate.cons_bound_floor.
Print Assumptions InstanceCertificate.INR_sqrt_le.
Print Assumptions InstanceCertificate.psi_unit_norm.
Print Assumptions InstanceCertificate.certified_c4_frame_bounds.

(* M4 收尾①（会话 9）：长度一致性——certified_c4_frame_bounds_anyN ∀N≥214
   （零 classic：4 窗口参数化行和 + 证书定理，全部零 classic） *)
Print Assumptions M4bLengthConsistency.c4_row0_gen.
Print Assumptions M4bLengthConsistency.c4_row1_gen.
Print Assumptions M4bLengthConsistency.c4_row2_gen.
Print Assumptions M4bLengthConsistency.c4_row3_gen.
Print Assumptions M4bLengthConsistency.certified_c4_frame_bounds_anyN.

(* M4 T8 复合证书（会话 9）：[3,15,63,255] 核 μ=4/5
   （零 classic：6 对界 + 4 行和 + 证书定理，全部零 classic） *)
Print Assumptions T8CoreCertificate.pair_3_15.
Print Assumptions T8CoreCertificate.pair_3_63.
Print Assumptions T8CoreCertificate.pair_3_255.
Print Assumptions T8CoreCertificate.pair_15_63.
Print Assumptions T8CoreCertificate.pair_15_255.
Print Assumptions T8CoreCertificate.pair_63_255.
Print Assumptions T8CoreCertificate.t8_row0.
Print Assumptions T8CoreCertificate.t8_row1.
Print Assumptions T8CoreCertificate.t8_row2.
Print Assumptions T8CoreCertificate.t8_row3.
Print Assumptions T8CoreCertificate.certified_t8_core_frame_bounds.

(* M4 收尾②：反射框架检查器 soundness（会话 9）——pair_sound 等零 classic
   （反射有理界 = psi 内积保守界的上界；未证毕部分见 frame_check_instance_sound TODO） *)
Print Assumptions FrameCheckInstance.pair_sound.
Print Assumptions FrameCheckInstance.div_le.
Print Assumptions FrameCheckInstance.frac_add_R.
Print Assumptions FrameCheckInstance.row_le_R.

(* M4 收尾③（会话 9 续）：frame_check_instance_sound 主定理装配完成——零 classic
   (a) pair_bound_ok (pair_sound + psi_inner_cons_bound + Cnorm_Csum_conj_sym)
   (b) row_sum_frac_aux_R (frac_add_R) + row_sum_frac_R_value
   (c) row_le_R  (d) psi_unit_norm + psi_ge_n_zero  (e) gershgorin_frame_mu 通用实例化 *)
Print Assumptions FrameCheckInstance.pair_bound_ok.
Print Assumptions FrameCheckInstance.pair_inner_frac_bound.
Print Assumptions FrameCheckInstance.row_sum_frac_aux_R.
Print Assumptions FrameCheckInstance.row_sum_frac_R_value.
Print Assumptions FrameCheckInstance.all_rows_le_forall.
Print Assumptions FrameCheckInstance.row_sum_frac_den_neq0.
Print Assumptions FrameCheckInstance.frame_check_instance_row_bound.
Print Assumptions FrameCheckInstance.frame_check_instance_sound.

(* M4 E5'' 复合证书（会话 14）：七带 [3,7,15,31,63,127,255] 端到端复合界
   （零 classic：15 个新 pair 界 + coh_delta_bound（42 方向）+ term_bound_upper/lower
    + champion_e5_composite_certificate；axiom 集 = Stdlib Reals 基底
    sig_not_dec/sig_forall_dec/fext，与 3D/4D 同款） *)
Print Assumptions ChampionCertificate.pair_3_7.
Print Assumptions ChampionCertificate.pair_3_31.
Print Assumptions ChampionCertificate.pair_3_127.
Print Assumptions ChampionCertificate.pair_7_15.
Print Assumptions ChampionCertificate.pair_7_63.
Print Assumptions ChampionCertificate.pair_7_127.
Print Assumptions ChampionCertificate.pair_7_255.
Print Assumptions ChampionCertificate.pair_15_31.
Print Assumptions ChampionCertificate.pair_15_127.
Print Assumptions ChampionCertificate.pair_7_31.
Print Assumptions ChampionCertificate.pair_31_63.
Print Assumptions ChampionCertificate.pair_31_127.
Print Assumptions ChampionCertificate.pair_31_255.
Print Assumptions ChampionCertificate.pair_63_127.
Print Assumptions ChampionCertificate.pair_127_255.
Print Assumptions ChampionCertificate.inner_diag_one.
Print Assumptions ChampionCertificate.coh_delta_bound.
Print Assumptions ChampionCertificate.term_bound_upper.
Print Assumptions ChampionCertificate.term_bound_lower.
Print Assumptions ChampionCertificate.champion_e5_composite_certificate.

(* 2D 窄轨反射检查器（会话 15）：独立前置链 + 点态 H_dom 组装
   （零 classic：axiom 集 = sig_not_dec + sig_forall_dec + functional_extensionality_dep，
    与 3D/4D/E5'' 同款；hdom_2d_narrow / index_bound_2d 为纯算术后闭） *)
Print Assumptions FrameCheck2DNarrow.seq_ext_growth_R.
Print Assumptions FrameCheck2DNarrow.seq_ext_tail_first_R.
Print Assumptions FrameCheck2DNarrow.hdom_2d_narrow.
Print Assumptions FrameCheck2DNarrow.index_bound_2d.
Print Assumptions FrameCheck2DNarrow.tensor_product_unconditional_basis_pointwise.
Print Assumptions FrameCheck2DNarrow.frame_check_2d_narrow_sound.
