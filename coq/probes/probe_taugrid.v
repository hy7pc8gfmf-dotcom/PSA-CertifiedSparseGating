(* ============================================================
   CS-4：τ 裁剪最优性（z 工作区，E039；双对话框 §4 z-main 认领项）
   任务书：psi-rope-rand恶化-压缩感知理论缺口-20260822.md §四 CS-4
   侦察：z/压缩感知定理补齐-CS侦察-20260822.md §2 CA 组

   数学内容（τ 感知频率选择的定理化——randmax256/384 实验的定理侧）：
     TA0 基础件：psi 逐点模方 = 1/n（k < n）/ filter 和单调（子族行和 ≤ 全族）。
     TA1 `support_classification`（支撑分类 iff）：n ≤ T ⟺ psi n 完全
         支撑在训练窗 [0,T]（∀k ≥ T, psi n k = C0）；n > T ⟹ psi n T ≠ 0。
     TA2 `coverage_fraction`（★覆盖率定理/τ 债量化）：S T < n ⟹ 窗内能量
         l2_norm_sq (psi n) T = (INR T + 1)/INR n < 1——**带 n 携带
         1 − (INR T + 1)/INR n 的能量在训练窗外（不可训练 OOD 部分）**。
     TA3 `prune_row_le`（★证书单调）：子族行和 ≤ 全族行和——
         rand-max 裁剪不损可证性（μ ≤ μ_full 传递任何上界型证书）。
     TA4 `thinning_preserves_ratio`（稀疏化保 C-比）：C-梯子 thinning 后
         仍是 C-梯子（kept 连续项比率 ≥ C）——RIP 证书可迁移。
     CA5 `tau_prune_optimality`（★主定理合成）：τ 感知裁剪 = 证书单调 +
         kept 带完全支撑 + pruned 严格超窗带覆盖债 ∈ (0,1)。
   依赖：ca_basis（psi/phi/l2_norm_sq/phi_ge_n_zero）+ ca_zeta_scaffold
   （unit_root_norm/Csum）+ probe_rowsum（sqrt_posnat，经 E152 桥）。
   审计：Print Assumptions 尾部。
   ============================================================ *)
Require Import Stdlib.Reals.Reals.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.micromega.Lra.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Import ListNotations.
Require Import ca_base.
Require Import ca_complex_foundation.
Require Import ca_basis.
Import UnconditionalBasis.
Require Import ca_independence.
Require Import Stdlib.Reals.RIneq.
Require Import ca_fourier.
Require Import ca_char_ortho.
Require Import ca_zeta_scaffold.
Require Import ca_log_bounds.
Require Import ca_complex_log.
Require Import probe_grid_ortho.
Require Import probe_parseval.
Require Import probe_partial.
Require Import probe_pairbound.
Require Import probe_rowsum.
Import ComplexNumbers.
Import PrimeEmbedding.
Import FourierAnalysis.
Import GridOrtho.
Import TPartial.
Import PairBound.
Import RowSum.

(* E138①：Notation 注册（8 项，恢复 Stdlib nat 记号——防 mathcomp 污染） *)
Notation "a + b" := (Nat.add a b) (at level 50, left associativity) : nat_scope.
Notation "a - b" := (Nat.sub a b) (at level 50, left associativity) : nat_scope.
Notation "a * b" := (Nat.mul a b) (at level 40, left associativity) : nat_scope.
Notation "a <= b" := (Nat.le a b) (at level 70, no associativity) : nat_scope.
Notation "a < b" := (Nat.lt a b) (at level 70, no associativity) : nat_scope.
Notation "a >= b" := (Nat.le b a) (at level 70, no associativity) : nat_scope.
Notation "a > b" := (Nat.lt b a) (at level 70, no associativity) : nat_scope.

(* E152：跨 flavor 桥——Stdlib ≤ → mathcomp leq bool（rowsum 的 mathcomp 前提专用） *)
Lemma le_Prop_to_mc (w1 w2 : nat) : (w1 <= w2)%nat -> ssrnat.leq w1 w2 = true.
Proof.
  intros H. unfold ssrnat.leq, eqtype.eq_op. simpl.
  apply Nat.eqb_eq. apply Nat.sub_0_le. exact H.
Qed.

Open Scope R_scope.
Open Scope complex_scope.
Open Scope nat_scope.

(* Stdlib 风味的 sqrt 正性（本地版——probe_rowsum 的 sqrt_posnat 已是
   mathcomp 风味前提，跨 flavor 桥成本高，按 E152 自包含绕开） *)
Lemma sqrt_pos_local (n : nat) : (1 <= n)%nat -> (0 < sqrt (INR n))%R.
Proof.
  intros Hn. apply sqrt_posnat. apply le_Prop_to_mc. exact Hn.
Qed.

(* INR 单射（Stdlib 无现名，本地自证：le_INR + S_INR + lra） *)
Lemma INR_eq_0 (n : nat) : (INR n = 0)%R -> (n = 0)%nat.
Proof.
  intro H. destruct n as [| n']; [reflexivity | ].
  rewrite S_INR in H.
  assert (Hge : (0 <= INR n')%R) by (apply (le_INR 0 n'); lia).
  lra.
Qed.

Module TauGrid.

(* 求和（PSA 口径：fold_right）——自包含定义，与 CA5 的行和一致 *)
Fixpoint list_sum_R (f : nat -> R) (l : list nat) : R :=
  match l with
  | [] => 0%R
  | x :: xs => f x + list_sum_R f xs
  end.

(* ---------- TA0：基础件 ---------- *)

(* psi n k 的模方 = 1/n（k < n）；= 0（k ≥ n，phi 尾零） *)
Lemma psi_norm_sq_pt (n k : nat) : (k < n)%nat ->
  (Cnorm_sq (psi n k) = 1 / INR n)%R.
Proof.
  intros Hk. unfold psi.
  rewrite Cnorm_sq_mult.
  assert (Hcof : (Cnorm_sq (Cof_real (1 / sqrt (INR n)))
                  = (1 / sqrt (INR n)) * (1 / sqrt (INR n)))%R).
  { unfold Cof_real, Cnorm_sq, Rsqr; simpl; ring. }
  rewrite Hcof.
  unfold UnconditionalBasis.phi.
  rewrite (proj2 (Nat.ltb_lt k n) Hk).
  rewrite unit_root_norm.
  assert (Hss : (sqrt (INR n) * sqrt (INR n) = INR n)%R)
    by (apply sqrt_sqrt; apply Rlt_le, lt_0_INR; lia).
  assert (Hrec : (1 / INR n = 1 / (sqrt (INR n) * sqrt (INR n)))%R)
    by (unfold Rdiv; rewrite Hss; reflexivity).
  rewrite Hrec. unfold Rdiv in *.
  rewrite Rinv_mult_distr.
  { ring. }
  { intros Hs1. exfalso.
    assert (Hpos : (0 < sqrt (INR n))%R) by (apply sqrt_pos_local; lia). lra. }
  { intros Hs2. exfalso.
    assert (Hpos : (0 < sqrt (INR n))%R) by (apply sqrt_pos_local; lia). nra. }
Qed.

Lemma ltb_ge_false (k n : nat) : (n <= k)%nat -> (k <? n) = false.
Proof. intros Hk. apply Nat.ltb_ge. exact Hk. Qed.

Lemma psi_norm_sq_tail (n k : nat) : (n <= k)%nat ->
  (psi n k = ComplexNumbers.C0)%C.
Proof.
  intros Hk. unfold psi, UnconditionalBasis.phi.
  rewrite ltb_ge_false by exact Hk.
  apply Cmul_0_r.
Qed.

(* filter 和单调：非负项下，过滤子列的和 ≤ 全列的和 *)
Lemma filter_sum_le (g : nat -> R) (P : nat -> bool) (l : list nat) :
  (forall i, (0 <= g i))%R ->
  (list_sum_R g (filter P l) <= list_sum_R g l)%R.
Proof.
  intros Hg. induction l as [| x xs IH].
  - simpl. apply Rle_refl.
  - simpl. destruct (P x) eqn:E.
    + simpl. apply (Rplus_le_compat_l (g x)). exact IH.
    + simpl. assert (Hgx : (0 <= g x)%R) by exact (Hg x).
      lra.
Qed.

(* ---------- TA1：支撑分类 iff ---------- *)

Theorem support_classification (n T : nat) :
  (n <= T)%nat <-> (forall k, (T <= k)%nat -> (psi n k = ComplexNumbers.C0))%C.
Proof.
  split.
  - intros Hn k Hk. apply psi_norm_sq_tail. lia.
  - intros Hsup.
    destruct (Nat.le_gt_cases n T) as [Hle | Hgt]; [ exact Hle | ].
    exfalso.
    assert (Hz : (psi n T = ComplexNumbers.C0)%C) by (apply Hsup; lia).
    assert (Hn : (0 < n)%nat) by lia.
    assert (Hpt := psi_norm_sq_pt n T Hgt).
    rewrite Hz in Hpt.
    rewrite Cnorm_sq_C0 in Hpt.
    assert (Hpos : (0 < INR n)%R) by (apply lt_0_INR; lia).
    unfold Rdiv in Hpt.
    assert (Hinv : (0 < / INR n)%R) by (apply Rinv_0_lt_compat; exact Hpos).
    lra.
Qed.

(* ---------- TA2：覆盖率定理（τ 债量化，★非平凡计算） ---------- *)

Lemma l2_norm_sq_0 (f : nat -> Complex) :
  (l2_norm_sq f 0%nat = Cnorm_sq (f 0%nat))%R.
Proof. unfold l2_norm_sq. simpl. reflexivity. Qed.

Lemma l2_norm_sq_S (f : nat -> Complex) (N : nat) :
  (l2_norm_sq f (S N) = l2_norm_sq f N + Cnorm_sq (f (S N)))%R.
Proof. unfold l2_norm_sq. simpl. reflexivity. Qed.

(* 窗 [0,T]（T+1 项）内能量 = (INR T + 1)/INR n < 1——带 n 携带
   1 − (INR T + 1)/INR n 的窗外能量（不可训练 OOD 部分） *)
Theorem coverage_fraction (n T : nat) : (S T < n)%nat ->
  (l2_norm_sq (psi n) T = (INR T + 1) / INR n)%R.
Proof.
  (* 前提先留在目标里再归纳：Htn 依赖 T，先 intros 会绊住 induction 泛化 *)
  induction T as [| T IHT]; intro Htn.
  - unfold l2_norm_sq. simpl.
    assert (H0n : (0 < n)%nat) by lia.
    rewrite (psi_norm_sq_pt n 0 H0n).
    unfold INR. simpl. rewrite Rplus_0_l. reflexivity.
  - (* E114：带前提引理一律显式实例化前提，禁止 rewrite 自动生成 *)
    assert (Hpre : (S T < n)%nat) by lia.
    rewrite l2_norm_sq_S.
    rewrite (IHT Hpre).
    rewrite (psi_norm_sq_pt n (S T) Hpre).
    rewrite S_INR.
    unfold Rdiv. ring.
Qed.

(* 覆盖债：窗 [0,T] 的覆盖 (INR T + 1)/INR n < 1 ⟹ 债 ∈ (0,1) *)
Corollary coverage_debt (n T : nat) : (S T < n)%nat ->
  ((0 < 1 - (INR T + 1) / INR n) /\ (1 - (INR T + 1) / INR n < 1))%R.
Proof.
  intros Htn.
  assert (HnR : (0 < INR n)%R) by (apply lt_0_INR; lia).
  assert (Hs0 : (0 <= INR T)%R) by (apply (le_INR 0 T); lia).
  assert (Hne : (INR n <> 0)%R) by (intros Hc; apply INR_eq_0 in Hc; lia).
  assert (Hn1 : (INR n * / INR n = 1)%R) by (apply Rmult_inv_r; exact Hne).
  assert (Hlt : (INR T + 1 < INR n)%R).
  { replace ((INR T + 1)%R) with (INR (S T)) by (rewrite S_INR; reflexivity).
    apply lt_INR. exact Htn. }
  assert (Hinv : (0 < / INR n)%R) by (apply Rinv_pos; exact HnR).
  split; unfold Rdiv in *; nra.
Qed.

(* ---------- TA3：裁剪证书单调（★子族行和 ≤ 全族行和） ---------- *)

(* 相干行 g 的 kept 子列和 ≤ 全列和（非负项下，TA0 filter_sum_le 直推） *)
Lemma prune_row_le (g : nat -> R) (P : nat -> bool) (l : list nat) :
  (forall i, (0 <= g i))%R ->
  (list_sum_R g (filter P l) <= list_sum_R g l)%R.
Proof. intros Hg. apply filter_sum_le. exact Hg. Qed.

(* ---------- TA4：稀疏化保 C-比 ---------- *)

(* Stdlib 风味链式单调（rowsum 的 v_incr 是 mathcomp bool 风味，
   跨 flavor 前提失配——按 E152 本地自证绕开） *)
Lemma chain_step_std (C : nat) (v : nat -> nat) :
  (2 <= C)%nat -> (forall j, (v j * C <= v (S j)))%nat ->
  (forall j, (v j <= v (S j)))%nat.
Proof.
  intros HC Hv j. apply Nat.le_trans with (v j * C).
  - assert (H1 : (v j * 1 <= v j * C)%nat)
      by (apply Nat.mul_le_mono_l; lia).
    rewrite Nat.mul_1_r in H1. exact H1.
  - apply Hv.
Qed.

Lemma chain_mono_std (v : nat -> nat) :
  (forall j, (v j <= v (S j)))%nat ->
  forall a b, (a <= b)%nat -> (v a <= v b)%nat.
Proof.
  intros Hv a b Hab.
  assert (Hgen : forall d a0, (v a0 <= v (a0 + d))%nat).
  { intro d. induction d as [| d IH]; intro a0.
    - rewrite Nat.add_0_r. apply Nat.le_refl.
    - rewrite Nat.add_succ_r.
      apply Nat.le_trans with (v (a0 + d)); [ exact (IH a0) | apply Hv ]. }
  replace b with (a + (b - a))%nat by lia.
  apply Hgen.
Qed.

(* C-梯子（相邻比率 ≥ C）经 filter 稀疏化后仍是 C-梯子：
   kept 连续项 a < b 之间跨 (b − a) 步，每步 ×C 累积 ⟹ v a·C ≤ v b *)
Lemma thinning_preserves_ratio (C : nat) (v : nat -> nat) (P : nat -> bool)
        (a b : nat) :
  (2 <= C)%nat ->
  (forall j, (v j * C <= v (S j)))%nat ->
  In a (filter P (seq 0 (S b))) -> In b (filter P (seq 0 (S b))) ->
  (a < b)%nat ->
  (v a * C <= v b)%nat.
Proof.
  intros HC Hv Ha Hb Hab.
  apply Nat.le_trans with (v (S a)).
  - apply Hv.
  - assert (Hsa : (S a <= b)%nat) by lia.
    apply (chain_mono_std v (chain_step_std C v HC Hv)).
    exact Hsa.
Qed.

(* ---------- CA5：τ-裁剪最优性合成定理（★主定理） ---------- *)

(* 相干核：ψ_a 与 ψ_b 的内积模（窗取 min a b） *)
Definition coh (a b : nat) : R :=
  Cnorm (Csum (fun k => psi a k *c Cconj (psi b k)) (Nat.min a b)).

Theorem tau_prune_optimality (C T : nat) (v : nat -> nat) (I : list nat) :
  (2 <= C)%nat ->
  (forall j, (v j * C <= v (S j)))%nat ->
  ( (* (i) 证书单调：每个 kept 带的子族行和 ≤ 全族行和 *)
    forall j0, In j0 (filter (fun i => Nat.leb (v i) T) I) ->
      (list_sum_R (fun i => coh (v i) (v j0))
         (filter (fun i => Nat.leb (v i) T) (filter (fun x => Nat.eqb x j0) I))
       <= list_sum_R (fun i => coh (v i) (v j0))
         (filter (fun x => Nat.eqb x j0) I))%R )
  /\ ( (* (ii) kept 带完全支撑在训练窗 [0,T] *)
      forall j0, In j0 (filter (fun i => Nat.leb (v i) T) I) ->
        (forall k, (T <= k)%nat -> (psi (v j0) k = ComplexNumbers.C0))%C )
  /\ ( (* (iii) pruned 且严格超窗的带携带覆盖债：1 − (INR T + 1)/INR (v i) ∈ (0,1) *)
      forall i, In i (filter (fun i0 => negb (Nat.leb (v i0) T)) I) ->
        (S T < v i)%nat ->
        ((0 < 1 - (INR T + 1) / INR (v i)) /\
         (1 - (INR T + 1) / INR (v i) < 1))%R ).
Proof.
  intros HC Hv.
  split.
  - (* (i) 行和单调：TA3 实例化（kept 子列 ⊆ 去重全列，非负项） *)
    intros j0 Hj0.
    apply (prune_row_le (fun i => coh (v i) (v j0))
                        (fun i => Nat.leb (v i) T)
                        (filter (fun x => Nat.eqb x j0) I)).
    intros i. unfold coh. apply Cnorm_ge_0.
  - split.
    + (* (ii) 支撑分类：kept ⟹ v j0 ≤ T ⟹ TA1 *)
      intros j0 Hj0 k Hk.
      apply filter_In in Hj0. destruct Hj0 as [_ Hle].
      exact (proj1 (support_classification (v j0) T)
               (proj1 (Nat.leb_le (v j0) T) Hle) k Hk).
    + (* (iii) 覆盖债：TA2 系，前提与陈述严格同形 *)
      intros i Hi Hlt.
      exact (coverage_debt (v i) T Hlt).
Qed.

End TauGrid.

Print Assumptions TauGrid.support_classification.
Print Assumptions TauGrid.coverage_fraction.
Print Assumptions TauGrid.coverage_debt.
Print Assumptions TauGrid.thinning_preserves_ratio.
Print Assumptions TauGrid.tau_prune_optimality.
