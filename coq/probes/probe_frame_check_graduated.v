(* ============================================================
   CS-17 分级证书检查器：probe_frame_check_graduated.v
   （M2 venue 对齐扩展 T2——检查器方法论从二元升级为分层服务）

   背景：反射检查器 frame_check_instance 是二元判定——好族全过、
   坏族全拒。四轮评审共同攻击点：二元判定的假阴性（[3,7,15] 类
   近带阶梯被整族拒绝，尽管其稀疏恢复语义仍然成立）。本模块给出
   四级分级检查器 cert_level + 健全性定理——每级承诺不同强度的
   证书，假阴性从"拒绝"变"降级服务"：
     L1_tight        二元检查器全过 ⟹ Gershgorin 框架界 [1/5, 9/5]·S
                     （frame_check_instance_sound 原样通道）
     L2_composite    结构有效且逐对相干界非空洞（δ_ij ≤ 1，逐对优于
                     C-S 平凡界）⟹ 复合能量界 (S−coh, S+coh)——七带
                     冠军证书 champion_e5_composite_certificate 的
                     自动化（不再手工组装）
     L3_energy_only  结构有效但存在黑洞对（δ > 1，如 [2,3]）⟹ 仅上
                     半能量界 ‖F‖² ≤ S + coh
     L4_rejected     结构无效（乱序/含 <2/空）⟹ 无承诺

   数学内容：
     GC1 ★ 行对角拆分引理 sum_row_diag_off（sum_f_R0 头递归归纳）
     GC2 逐项界 term_bound_grad_upper/lower（对角 = Cnorm_sq 精确；
         非对角 = |c_i||c_j|·pair_frac_R，经 pair_inner_frac_bound）
     GC3 ★★ 复合界 composite_frame_bounds（L2/L3 数学核）：
         任意结构有效阶梯的 (S−coh, S+coh) 双侧界——champion_e5
         骨架的泛化（具体 n=7 simpl+ring 拆分 → 通用索引拆分引理）
     GC4 分级健全性 frame_check_graduated_sound（最终定理）

   纪律（承 probe_robust / probe_c4_instance 经典 R 轨道先例）：
     - 经典 R 层（T2 依赖既有 R 层检查器，不属构造性轨道）
     - 零 Admitted / 零自定义 Axiom（审计 ≤ Dedekind 三公理）
     - 决策函数 nat/bool 层可计算可提取；非平凡核 = GC1+GC3
   依赖：ca_base/ca_complex_foundation/ca_independence/ca_basis/
         ca_basis_lemmas/ca_decay + PSA_framework（FrameCheckInstance/
         ChampionCertificate 模块）。
   提取：frame_check_graduated.ml（cert_level + 分级决策——nat 可执行）
   ============================================================ *)
Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.micromega.Lra.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Reals.Reals.
Require Import ca_base ca_complex_foundation ca_independence ca_basis ca_basis_lemmas ca_decay.
Require Import PSA_framework.
Import ComplexNumbers.
Import ExtendedTheorems.
Import ListNotations.
Open Scope nat_scope.
Open Scope R_scope.

(* ============ GC0：分级层与决策函数（可计算层） ============ *)

Inductive cert_level : Set :=
  | L1_tight
  | L2_composite
  | L3_energy_only
  | L4_rejected.

(* 逐对相干界非空洞：δ_ij ≤ 1（pair_frac = num/den，den > 0）。
   注意 pair_ok 的 sqrt 往返检查对 ≥2 带恒真——真正区分 L2/L3 的是
   逐对界是否打败 C-S 平凡界 |⟨u_i,u_j⟩| ≤ 1。 *)
Definition pair_le_1 (n1 n2 : nat) : bool :=
  Nat.leb (FrameCheckInstance.pair_num (Nat.min n1 n2) (Nat.max n1 n2))
          (FrameCheckInstance.pair_den (Nat.min n1 n2) (Nat.max n1 n2)).

Fixpoint all_pairs_le_1 (I : list nat) : bool :=
  match I with
  | nil => true
  | cons h tl => andb (forallb (fun m => pair_le_1 h m) tl) (all_pairs_le_1 tl)
  end.

(* 分级检查器（主入口）：
   空表 / 结构无效 → L4；二元检查器全过 → L1；
   结构有效（严格升序 + 全 ≥2）→ 逐对 δ≤1 ? L2 : L3 *)
Definition frame_check_graduated (I : list nat) : cert_level :=
  match I with
  | nil => L4_rejected
  | _ :: _ =>
      if FrameCheckInstance.frame_check_instance I then L1_tight
      else if andb (FrameCheckInstance.sorted_strict_aux I)
                    (FrameCheckInstance.all_ge_2 I) then
        (if all_pairs_le_1 I then L2_composite else L3_energy_only)
      else L4_rejected
  end.

(* ============ GC1：行对角拆分引理 ============ *)

(* 固定 i 的行拆分：第 i 项从和中提出，其余以 if-零形式保留 *)
Lemma sum_row_diag_off (f : nat -> R) (i n : nat) :
  (i <= n)%nat ->
  sum_f_R0 f n = f i + sum_f_R0 (fun j => if eq_nat_dec i j then 0 else f j) n.
Proof.
  induction n as [| n IH]; intros Hi.
  - assert (Hi0 : (i = 0)%nat) by lia. subst i.
    simpl. destruct (eq_nat_dec 0 0) as [He | Hn].
    + ring.
    + exfalso. exact (Hn eq_refl).
  - destruct (Nat.eq_dec i (S n)) as [Hlast | Hnotlast].
    + subst i.
      assert (Hpre : sum_f_R0 (fun j => if eq_nat_dec (S n) j then 0 else f j) n = sum_f_R0 f n).
      { apply sum_f_R0_ext. intros k Hk.
        destruct (eq_nat_dec (S n) k) as [He | Hne]; [exfalso; lia | reflexivity]. }
      assert (Hlast0 : (fun j => if eq_nat_dec (S n) j then 0 else f j) (S n) = 0).
      { destruct (eq_nat_dec (S n) (S n)) as [He | Hne].
        - reflexivity.
        - exfalso. exact (Hne eq_refl). }
      rewrite sum_f_R0_S. rewrite sum_f_R0_S. rewrite Hpre, Hlast0. ring.
    + assert (Hlastf : (fun j => if eq_nat_dec i j then 0 else f j) (S n) = f (S n)).
      { destruct (eq_nat_dec i (S n)) as [He | Hne].
        - exfalso. apply Hnotlast. exact He.
        - reflexivity. }
      rewrite sum_f_R0_S. rewrite sum_f_R0_S. rewrite Hlastf.
      assert (Hin : (i <= n)%nat) by lia.
      assert (IH1 := IH Hin).
      lra.
Qed.

(* 负号进出有限和 *)
Lemma sum_f_R0_opp_l (f : nat -> R) (n : nat) :
  - sum_f_R0 f n = sum_f_R0 (fun i => - f i) n.
Proof.
  revert f. induction n as [| n IH]; intros f.
  - simpl. lra.
  - rewrite FrameCheckInstance.sum_f_R0_shift.
    rewrite FrameCheckInstance.sum_f_R0_shift.
    cbv beta.
    rewrite <- (IH (fun k => f (S k))).
    ring.
Qed.

(* ============ GC2：逐项界（对角精确 / 非对角逐对相干） ============ *)

Lemma term_bound_grad_upper (c : nat -> Complex) (v : nat -> nat) (M i j : nat) :
  (2 <= v i)%nat -> (2 <= v j)%nat ->
  (v i <= M)%nat -> (v j <= M)%nat ->
  (i <> j -> v i <> v j) ->
  re (c i *c Cconj (c j) *c
      Csum (fun k => psi (v i) k *c Cconj (psi (v j) k)) M)
  <= if eq_nat_dec i j then Cnorm_sq (c i)
     else Cnorm (c i) * Cnorm (c j) * FrameCheckInstance.pair_frac_R (v i) (v j).
Proof.
  intros H2i H2j HMi HMj Hdist.
  destruct (eq_nat_dec i j) as [Heq | Hne].
  - subst j.
    rewrite (ChampionCertificate.inner_diag_one (v i) M H2i HMi).
    change (Cof_real 1) with C1.
    rewrite Cmul_1_r.
    rewrite Cnorm_sq_eq_re_mul.
    apply Rle_refl.
  - eapply Rle_trans; [apply ChampionCertificate.re_le_cnorm |].
    rewrite (Cnorm_mult (c i *c Cconj (c j))
              (Csum (fun k => psi (v i) k *c Cconj (psi (v j) k)) M)).
    rewrite (Cnorm_mult (c i) (Cconj (c j))).
    rewrite Cnorm_conj_eq.
    apply Rmult_le_compat_l.
    + apply Rmult_le_pos; apply ChampionCertificate.cnorm_ge0.
    + apply FrameCheckInstance.pair_inner_frac_bound; [exact H2i | exact H2j | apply Hdist; exact Hne |].
      pose proof (Nat.le_min_l (v i) (v j)). lia.
Qed.

Lemma term_bound_grad_lower (c : nat -> Complex) (v : nat -> nat) (M i j : nat) :
  (2 <= v i)%nat -> (2 <= v j)%nat ->
  (v i <= M)%nat -> (v j <= M)%nat ->
  (i <> j -> v i <> v j) ->
  - re (c i *c Cconj (c j) *c
        Csum (fun k => psi (v i) k *c Cconj (psi (v j) k)) M)
    <= if eq_nat_dec i j then - Cnorm_sq (c i)
       else Cnorm (c i) * Cnorm (c j) * FrameCheckInstance.pair_frac_R (v i) (v j).
Proof.
  intros H2i H2j HMi HMj Hdist.
  destruct (eq_nat_dec i j) as [Heq | Hne].
  - subst j.
    rewrite (ChampionCertificate.inner_diag_one (v i) M H2i HMi).
    change (Cof_real 1) with C1.
    rewrite Cmul_1_r.
    rewrite Cnorm_sq_eq_re_mul.
    apply Rle_refl.
  - eapply Rle_trans; [apply ChampionCertificate.neg_re_le_cnorm |].
    rewrite (Cnorm_mult (c i *c Cconj (c j))
              (Csum (fun k => psi (v i) k *c Cconj (psi (v j) k)) M)).
    rewrite (Cnorm_mult (c i) (Cconj (c j))).
    rewrite Cnorm_conj_eq.
    apply Rmult_le_compat_l.
    + apply Rmult_le_pos; apply ChampionCertificate.cnorm_ge0.
    + apply FrameCheckInstance.pair_inner_frac_bound; [exact H2i | exact H2j | apply Hdist; exact Hne |].
      pose proof (Nat.le_min_l (v i) (v j)). lia.
Qed.

(* ============ GC3：复合界（L2/L3 数学核——champion 骨架的泛化） ============ *)

(* 分级相干量：Σ_{i≠j} |c_i||c_j|·δ_ij（δ = pair_frac_R，天然对称取 min/max） *)
Definition coh_ladder (I : list nat) (c : nat -> Complex) : R :=
  sum_f_R0 (fun i => sum_f_R0 (fun j =>
    if eq_nat_dec i j then 0
    else Cnorm (c i) * Cnorm (c j) * FrameCheckInstance.pair_frac_R (nth i I 0%nat) (nth j I 0%nat))
    (Nat.pred (length I))) (Nat.pred (length I)).

Theorem composite_frame_bounds (I : list nat) (coeffs : list Complex) :
  FrameCheckInstance.sorted_strict_aux I = true ->
  FrameCheckInstance.all_ge_2 I = true ->
  (0 < length I)%nat ->
  length coeffs = length I ->
  let n := length I in
  let c := fun i => nth i coeffs C0 in
  let F := fun k => Csum (fun i => c i *c psi (nth i I 0%nat) k) n in
  ((sum_f_R0 (fun i => Cnorm_sq (c i)) (Nat.pred n) - coh_ladder I c
    <= l2_norm_sq F (S (last I 0%nat) - 1)
    <= sum_f_R0 (fun i => Cnorm_sq (c i)) (Nat.pred n) + coh_ladder I c)%R).
Proof.
  intros Hs Hg Hne Hlc n c F.
  assert (Hnp : (Nat.pred n < n)%nat) by lia.
  assert (Hin : forall k, (k <= Nat.pred n)%nat -> (k < n)%nat) by (intros k Hk; lia).
  assert (HlenI : length I = n) by reflexivity.
  (* 带内事实 *)
  assert (Hge2 : forall i, (i <= Nat.pred n)%nat -> (2 <= nth i I 0%nat)%nat).
  { intros i Hi. apply (FrameCheckInstance.all_ge_2_nth I Hg i). lia. }
  assert (Hlelast : forall i, (i <= Nat.pred n)%nat -> (nth i I 0%nat <= last I 0%nat)%nat).
  { intros i Hi. apply (FrameCheckInstance.nth_le_last I Hs i). lia. }
  assert (Hvne : forall i j, (i < n)%nat -> (j < n)%nat -> i <> j -> nth i I 0%nat <> nth j I 0%nat).
  { intros i j Hi Hj Hij.
    destruct (Nat.lt_trichotomy i j) as [Hlt | [Heq | Hgt]].
    - intro Hz. pose proof (FrameCheckInstance.sorted_nth_lt I Hs i j Hlt Hj). lia.
    - exfalso. exact (Hij Heq).
    - intro Hz. pose proof (FrameCheckInstance.sorted_nth_lt I Hs j i Hgt Hi). lia. }
  assert (HMi : forall i, (i <= Nat.pred n)%nat -> (nth i I 0%nat <= S (last I 0%nat))%nat).
  { intros i Hi. pose proof (Hlelast i Hi). lia. }
  (* 双和展开（l2_expand_double_sum，vals := I，窗口 M = S (last I 0%nat)） *)
  pose proof (l2_expand_double_sum coeffs I n (S (last I 0%nat))
                Hlc HlenI (Nat.lt_0_succ (last I 0%nat))) as H0.
  cbv zeta in H0.
  assert (Hpm : forall k : nat, (k - 1)%nat = Nat.pred k) by (intros k; lia).
  rewrite (Hpm n) in H0.
  assert (Hnorm : l2_norm_sq F (S (last I 0%nat) - 1)
      = sum_f_R0 (fun i => sum_f_R0 (fun j =>
          re (c i *c Cconj (c j) *c
              Csum (fun k => psi (nth i I 0%nat) k *c Cconj (psi (nth j I 0%nat) k)) (S (last I 0%nat))))
          (Nat.pred n)) (Nat.pred n)).
  { exact H0. }
  rewrite Hnorm.
  set (m := Nat.pred n).
  (* 逐项上界 / 下界 *)
  assert (Hup1 : sum_f_R0 (fun i => sum_f_R0 (fun j =>
            re (c i *c Cconj (c j) *c
                Csum (fun k => psi (nth i I 0%nat) k *c Cconj (psi (nth j I 0%nat) k)) (S (last I 0%nat)))) m) m
          <= sum_f_R0 (fun i => sum_f_R0 (fun j =>
            if eq_nat_dec i j then Cnorm_sq (c i)
            else Cnorm (c i) * Cnorm (c j)
                 * FrameCheckInstance.pair_frac_R (nth i I 0%nat) (nth j I 0%nat)) m) m).
  { apply sum_f_R0_le_compat; intros i Hi.
    apply sum_f_R0_le_compat; intros j Hj.
    apply (term_bound_grad_upper c (fun x => nth x I 0%nat) (S (last I 0%nat)) i j
             (Hge2 i Hi) (Hge2 j Hj) (HMi i Hi) (HMi j Hj)
             (fun Hij => Hvne i j (Hin i Hi) (Hin j Hj) Hij)). }
  assert (Hlo1 : sum_f_R0 (fun i => sum_f_R0 (fun j =>
            - re (c i *c Cconj (c j) *c
                  Csum (fun k => psi (nth i I 0%nat) k *c Cconj (psi (nth j I 0%nat) k)) (S (last I 0%nat)))) m) m
          <= sum_f_R0 (fun i => sum_f_R0 (fun j =>
            if eq_nat_dec i j then - Cnorm_sq (c i)
            else Cnorm (c i) * Cnorm (c j)
                 * FrameCheckInstance.pair_frac_R (nth i I 0%nat) (nth j I 0%nat)) m) m).
  { apply sum_f_R0_le_compat; intros i Hi.
    apply sum_f_R0_le_compat; intros j Hj.
    apply (term_bound_grad_lower c (fun x => nth x I 0%nat) (S (last I 0%nat)) i j
             (Hge2 i Hi) (Hge2 j Hj) (HMi i Hi) (HMi j Hj)
             (fun Hij => Hvne i j (Hin i Hi) (Hin j Hj) Hij)). }
  (* 拆分：if-对角/非对角双和 = 对角和 + coh_ladder *)
  assert (Hsplit : sum_f_R0 (fun i => sum_f_R0 (fun j =>
            if eq_nat_dec i j then Cnorm_sq (c i)
            else Cnorm (c i) * Cnorm (c j)
                 * FrameCheckInstance.pair_frac_R (nth i I 0%nat) (nth j I 0%nat)) m) m
          = sum_f_R0 (fun i => Cnorm_sq (c i)) m + coh_ladder I c).
{ unfold coh_ladder.
    set (Frow := fun i j => if eq_nat_dec i j then Cnorm_sq (c i)
                            else Cnorm (c i) * Cnorm (c j)
                            * FrameCheckInstance.pair_frac_R (nth i I 0%nat) (nth j I 0%nat)).
    transitivity (sum_f_R0 (fun i =>
        Frow i i + sum_f_R0 (fun j => if eq_nat_dec i j then 0 else Frow i j) m) m).
    - apply sum_f_R0_ext. intros i Hi.
      apply sum_row_diag_off. exact Hi.
    - rewrite sum_f_R0_add. f_equal.
      + apply sum_f_R0_ext. intros i Hi.
        unfold Frow. cbv beta.
        destruct (eq_nat_dec i i) as [He | Hn]; [reflexivity | exfalso; exact (Hn eq_refl)].
      + apply sum_f_R0_ext. intros i Hi.
        apply sum_f_R0_ext. intros j Hj.
        unfold Frow. cbv beta.
        destruct (eq_nat_dec i j) as [He | Hn]; [reflexivity | reflexivity]. }
  assert (Hsplit1 : sum_f_R0 (fun i => sum_f_R0 (fun j =>
            if eq_nat_dec i j then - Cnorm_sq (c i)
            else Cnorm (c i) * Cnorm (c j)
                 * FrameCheckInstance.pair_frac_R (nth i I 0%nat) (nth j I 0%nat)) m) m
          = - sum_f_R0 (fun i => Cnorm_sq (c i)) m + coh_ladder I c).
{ unfold coh_ladder.
    set (Frow := fun i j => if eq_nat_dec i j then - Cnorm_sq (c i)
                            else Cnorm (c i) * Cnorm (c j)
                            * FrameCheckInstance.pair_frac_R (nth i I 0%nat) (nth j I 0%nat)).
    transitivity (sum_f_R0 (fun i =>
        Frow i i + sum_f_R0 (fun j => if eq_nat_dec i j then 0 else Frow i j) m) m).
    - apply sum_f_R0_ext. intros i Hi.
      apply sum_row_diag_off. exact Hi.
    - rewrite sum_f_R0_add. f_equal.
      + rewrite (sum_f_R0_opp_l (fun i => Cnorm_sq (c i)) m).
        apply sum_f_R0_ext. intros i Hi.
        unfold Frow. cbv beta.
        destruct (eq_nat_dec i i) as [He | Hn]; [reflexivity | exfalso; exact (Hn eq_refl)].
      + apply sum_f_R0_ext. intros i Hi.
        apply sum_f_R0_ext. intros j Hj.
        unfold Frow. cbv beta.
        destruct (eq_nat_dec i j) as [He | Hn]; [reflexivity | reflexivity]. }
  (* 汇编：上界直接；下界经取负链（ΣΣ(-re) = -ΣΣ(re) 桥） *)
  assert (Hneg : sum_f_R0 (fun i => sum_f_R0 (fun j =>
            - re (c i *c Cconj (c j) *c
                  Csum (fun k => psi (nth i I 0%nat) k *c Cconj (psi (nth j I 0%nat) k)) (S (last I 0%nat)))) m) m
         
      = - sum_f_R0 (fun i => sum_f_R0 (fun j =>
            re (c i *c Cconj (c j) *c
                  Csum (fun k => psi (nth i I 0%nat) k *c Cconj (psi (nth j I 0%nat) k)) (S (last I 0%nat)))) m) m
         ).
  { rewrite (sum_f_R0_opp_l (fun i => sum_f_R0 (fun j =>
            re (c i *c Cconj (c j) *c
                  Csum (fun k => psi (nth i I 0%nat) k *c Cconj (psi (nth j I 0%nat) k)) (S (last I 0%nat)))) m) m).
    apply sum_f_R0_ext. intros i Hi.
    symmetry. apply sum_f_R0_opp_l. }
  rewrite Hneg in Hlo1.
  split; lra.
Qed.

Lemma sub1_pred (k : nat) : (k - 1)%nat = Nat.pred k.
Proof. lia. Qed.

(* ============ GC4：分级健全性（最终定理） ============ *)

Theorem frame_check_graduated_sound (I : list nat) (lvl : cert_level)
        (coeffs : list Complex) (Hlc : length coeffs = length I)
        (Hg : frame_check_graduated I = lvl) :
  match lvl with
  | L1_tight =>
      let n := length I in
      let F := fun k => Csum (fun i => nth i coeffs C0 *c psi (nth i I 0%nat) k) n in
      ((1 - 4 / 5) * sum_f_R0 (fun i => Cnorm_sq (nth i coeffs C0)) (Nat.pred n)
       <= l2_norm_sq F (S (last I 0%nat) - 1)
       <= (1 + 4 / 5) * sum_f_R0 (fun i => Cnorm_sq (nth i coeffs C0)) (Nat.pred n))%R
  | L2_composite =>
      let n := length I in
      let c := fun i => nth i coeffs C0 in
      let F := fun k => Csum (fun i => c i *c psi (nth i I 0%nat) k) n in
      ((sum_f_R0 (fun i => Cnorm_sq (c i)) (Nat.pred n) - coh_ladder I c
        <= l2_norm_sq F (S (last I 0%nat) - 1)
        <= sum_f_R0 (fun i => Cnorm_sq (c i)) (Nat.pred n) + coh_ladder I c)%R)
  | L3_energy_only =>
      let n := length I in
      let c := fun i => nth i coeffs C0 in
      let F := fun k => Csum (fun i => c i *c psi (nth i I 0%nat) k) n in
      (l2_norm_sq F (S (last I 0%nat) - 1)
       <= sum_f_R0 (fun i => Cnorm_sq (c i)) (Nat.pred n) + coh_ladder I c)%R
  | L4_rejected => True
  end.
Proof.
  destruct lvl.
  - (* L1_tight *)
    destruct I as [| h t].
    + compute in Hg. discriminate Hg.
    + assert (Hne : (0 < length (h :: t))%nat) by (simpl; lia).
      unfold frame_check_graduated in Hg.
      destruct (FrameCheckInstance.frame_check_instance (h :: t)) eqn:Hfc.
      * cbv zeta. rewrite sub1_pred.
        exact (FrameCheckInstance.frame_check_instance_sound (h :: t)
                 Hne Hfc coeffs Hlc).
      * destruct (andb (FrameCheckInstance.sorted_strict_aux (h :: t))
                       (FrameCheckInstance.all_ge_2 (h :: t))) eqn:Hst.
        -- destruct (all_pairs_le_1 (h :: t)) eqn:Hp1.
          ++ discriminate Hg.
          ++ discriminate Hg.
        -- discriminate Hg.
  - (* L2_composite *)
    destruct I as [| h t].
    + compute in Hg. discriminate Hg.
    + assert (Hne : (0 < length (h :: t))%nat) by (simpl; lia).
      unfold frame_check_graduated in Hg.
      destruct (FrameCheckInstance.frame_check_instance (h :: t)) eqn:Hfc.
      * discriminate Hg.
      * destruct (andb (FrameCheckInstance.sorted_strict_aux (h :: t))
                       (FrameCheckInstance.all_ge_2 (h :: t))) eqn:Hst.
        -- apply andb_true_iff in Hst. destruct Hst as [Hs Hg2].
           destruct (all_pairs_le_1 (h :: t)) eqn:Hp1.
          ++ cbv zeta.
             exact (composite_frame_bounds (h :: t) coeffs Hs Hg2 Hne Hlc).
          ++ discriminate Hg.
        -- discriminate Hg.
  - (* L3_energy_only *)
    destruct I as [| h t].
    + compute in Hg. discriminate Hg.
    + assert (Hne : (0 < length (h :: t))%nat) by (simpl; lia).
      unfold frame_check_graduated in Hg.
      destruct (FrameCheckInstance.frame_check_instance (h :: t)) eqn:Hfc.
      * discriminate Hg.
      * destruct (andb (FrameCheckInstance.sorted_strict_aux (h :: t))
                       (FrameCheckInstance.all_ge_2 (h :: t))) eqn:Hst.
        -- apply andb_true_iff in Hst. destruct Hst as [Hs Hg2].
           destruct (all_pairs_le_1 (h :: t)) eqn:Hp1.
          ++ discriminate Hg.
          ++ cbv zeta.
             exact (proj2 (composite_frame_bounds (h :: t) coeffs Hs Hg2 Hne Hlc)).
        -- discriminate Hg.
  - (* L4_rejected *)
    trivial.
Qed.

(* ============ 计算验证（分级分布示例——覆盖四级） ============ *)

(* [3,13]：二元检查器全过 → L1_tight（C4 类） *)
Example grad_3_13 : frame_check_graduated [3; 13]%nat = L1_tight.
Proof. vm_compute. reflexivity. Qed.

(* [3,7,15]：行和 22320/18432 > 4/5 被二元检查器拒绝，但逐对 δ≤1
   → L2_composite——评审 G-5"误拒"类阶梯获得降级服务（本战役主卖点） *)
Example grad_3_7_15 : frame_check_graduated [3; 7; 15]%nat = L2_composite.
Proof. vm_compute. reflexivity. Qed.

(* [2,3]：黑洞对 δ = 6/4 > 1 → L3_energy_only（仅上半能量界） *)
Example grad_2_3 : frame_check_graduated [2; 3]%nat = L3_energy_only.
Proof. vm_compute. reflexivity. Qed.

(* 乱序 → L4_rejected；空表 → L4_rejected *)
Example grad_unsorted : frame_check_graduated [7; 3]%nat = L4_rejected.
Proof. vm_compute. reflexivity. Qed.

Example grad_nil : frame_check_graduated []%nat = L4_rejected.
Proof. vm_compute. reflexivity. Qed.

(* ============ 审计 ============ *)
Print Assumptions composite_frame_bounds.
Print Assumptions frame_check_graduated_sound.

(* ============ 提取（决策函数 nat 可执行：psa_guard 侧分级入口） ============ *)
From Stdlib Require Import Extraction.

Extraction "frame_check_graduated.ml" cert_level frame_check_graduated pair_le_1.
