(* ============================================================
   CS 战役一体化模块：probe_cs.v（z 区，2026-08-29）
   任务书：压缩感知定理补齐-CS侦察-20260822.md §2 CS-1/2/3/6 + §四 CS4c

   数学内容（Candès–Tao 生产线定理化——"无条件基天然优势"的定理形式）：
     CS-2 `cs2_rip_uniform`（★一致 RIP，Candès–Tao 命名）：C-梯子合成映射
         的 restricted isometry 常数 δ = 4K(C) **不随稀疏阶 s 增长**
         （psi_unconditional_basis 的重述打包：|‖F(c)‖² − ‖c‖²| ≤ δ·‖c‖²，∀I）。
     CS-3 `cs3_energy_zero`（能量不丢失）+ `cs3_unique`（★s-sparse 唯一性，
     核心非平凡）：C ≥ 10（2K(C) < 1）时合成映射在 I 支撑系数上单射——
     测量 y = y' ⟹ 系数 c = c'。路线：下界半边 (1−2K(C))·S ≤ ‖F‖²，
     差列表 d := c − c' 的逐点线性（Csum_sub + map2_sub_nth + Csub 分配），
     ‖F_d‖² = 0 ⟹ S_d = 0 ⟹ d = 0。
     CS-6 `cs6_embedding`：M < 1 ⟹ ℓ²→ℓ² embedding（下有界 ⟹ 单射）——
     与 CS-3 合并陈述（embedding 常数命名）。
     CS-1b `cs1b_spark`：无平凡零组合 ⟹ n 列独立 ⟹ spark(Φ_I) ≥ n+1
         （CS-3 推论；侦察文档标注的 Gershgorin 冗余路径由此收编，
         Elad–Bruckstein 判据）。
     CS-1a `cs1a_pair_bound`：C-梯子逐对相干上界（PB4/Fpair 形）≤ 2πq/(1−q)
         ——row_sum_3halfs 的单项抽取（lsum_single_le + Fpair 非负；
         |⟨ψ_a,ψ_b⟩| ≤ Fpair a b 即 PB4 pair_inner_norm，已证）。
     CS4c `near_dup_coherence_12` + `cs4c_explosion`（★RIP 证书爆炸）：
         近重复对 {1,2} 的相干 = 1/√2（精确值，零相位 Cexp）⟹ 含近重复对
         的梯子 μ ≥ 1/√2 ⟹ s ≥ 3 时 (s−1)·μ ≥ √2 > 1——Gershgorin 型
         RIP 上界证书失效（"剪 503/255/127 应恶化"的定理侧镜像；
         高频带的定量 cos 下界版本列为未来工作）。
   依赖：ca_decay（ExtendedTheorems.psi_unconditional_basis[_tight]）+
   ca_basis_lemmas（K）+ ca_sparse_ext + ca_complex_log + probe_taugrid
   （TauGrid.l2_norm_sq_0/S）+ probe_rowsum（RowSum.row_sum_3halfs/qval/
   Fpair）+ probe_pairdirichlet（rot_atom）+ probe_grid_ortho（Csum_ext）。
   审计：Print Assumptions 尾部。
   ============================================================ *)
From Stdlib Require Import Reals.
From Stdlib Require Import QArith.
From Stdlib Require Import ZArith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.micromega.Lra.
From Stdlib Require Import Arith.
From Stdlib Require Import List.
From Stdlib Require Import Sorting.Sorted.
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
Require Import ca_basis_lemmas.
Require Import ca_decay.
Require Import ca_sparse_ext.
Require Import probe_pairdirichlet.
Require Import probe_parseval.
Require Import probe_partial.
Require Import probe_pairbound.
Require Import probe_taugrid.
Require Import probe_rowsum.
Require Import probe_grid_ortho.
Import UnconditionalBasisLemmas.
Import ComplexNumbers.
Import PrimeEmbedding.
Import independent.
Import FourierAnalysis.
Import GridOrtho.
Import TPartial.
Import TauGrid.
Import PairBound.
Import RowSum.
Import PairDirichlet.

(* E138①：Notation 注册（8 项，恢复 Stdlib nat 记号——防 mathcomp 污染） *)
Notation "a + b" := (Nat.add a b) (at level 50, left associativity) : nat_scope.
Notation "a - b" := (Nat.sub a b) (at level 50, left associativity) : nat_scope.
Notation "a * b" := (Nat.mul a b) (at level 40, left associativity) : nat_scope.
Notation "a <= b" := (Nat.le a b) (at level 70, no associativity) : nat_scope.
Notation "a < b" := (Nat.lt a b) (at level 70, no associativity) : nat_scope.
Notation "a >= b" := (Nat.le b a) (at level 70, no associativity) : nat_scope.
Notation "a > b" := (Nat.lt b a) (at level 70, no associativity) : nat_scope.

Local Open Scope nat_scope.
Local Open Scope complex_scope.
Local Open Scope R_scope.

Locate Csum.
Locate psi.
Module CSBattle.

(* ---------- 基础件 ---------- *)

Lemma rsqr_pos (x : R) : (0 <= Rsqr x)%R.
Proof. unfold Rsqr. nra. Qed.

Lemma rabs_eq0 (x : R) : Rabs x = 0%R -> x = 0%R.
Proof.
  intro H. destruct (Rle_or_lt 0 x) as [Hge|Hlt].
  - rewrite Rabs_right in H by lra. lra.
  - rewrite Rabs_left in H by lra. lra.
Qed.

(* 逐点相等 ⟹ 能量相等 *)
Lemma l2_norm_sq_ext (f g : nat -> Complex) (N : nat) :
  (forall k, (k <= N)%nat -> f k = g k) ->
  l2_norm_sq f N = l2_norm_sq g N.
Proof.
  intros H. induction N as [| N IH].
  - unfold l2_norm_sq. simpl. rewrite (H 0%nat) by lia. reflexivity.
  - rewrite l2_norm_sq_S, l2_norm_sq_S.
    rewrite IH by (intros k Hk; apply H; lia).
    rewrite (H (S N)) by lia. reflexivity.
Qed.

(* 零能量引理：逐点为零 ⟹ 能量为零 *)
Lemma l2_norm_sq_zero (f : nat -> Complex) (N : nat) :
  (forall k, (k <= N)%nat -> f k = C0) -> l2_norm_sq f N = 0%R.
Proof.
  intros H.
  rewrite (l2_norm_sq_ext f (fun _ => C0) N H).
  clear H f. induction N as [| N IH].
  - unfold l2_norm_sq. simpl. apply Cnorm_sq_C0.
  - rewrite l2_norm_sq_S, IH. unfold l2_norm_sq. simpl.
    rewrite Rplus_0_l. apply Cnorm_sq_C0.
Qed.

(* 能量单项控制：|c_i|² ≤ 总能量 *)
Lemma sum_cnormsq_pos (coeffs : list Complex) :
  forall N, (0 <= sum_f_R0 (fun j => Cnorm_sq (nth j coeffs C0)) N)%R.
Proof.
  induction N as [| N IHN]; simpl.
  - apply Cnorm_sq_ge_0.
  - pose proof (Cnorm_sq_ge_0 (nth (S N) coeffs C0)). lra.
Qed.

Lemma norm_sq_coeff_le (coeffs : list Complex) (N i : nat) :
  (i <= N)%nat ->
  Cnorm_sq (nth i coeffs C0)
  <= sum_f_R0 (fun j => Cnorm_sq (nth j coeffs C0)) N.
Proof.
  induction N as [| N IHn].
  - intro Hi. assert (i = 0%nat) by lia. subst. simpl. apply Rle_refl.
  - destruct (Nat.eq_dec i (S N)) as [->|Hne].
    + pose proof (sum_cnormsq_pos coeffs N) as Hpos. simpl. lra.
    + intro HiN. assert (Hle : (N >= i)%nat) by lia.
      specialize (IHn Hle). simpl.
      pose proof (sum_cnormsq_pos coeffs N) as Hpos.
      apply Rle_trans with
        (r2 := sum_f_R0 (fun j => Cnorm_sq (nth j coeffs C0)) N).
      * exact IHn.
      * pose proof (Cnorm_sq_ge_0 (nth (S N) coeffs C0)). lra.
Qed.

(* 模方为零 ⟹ 复数为零 *)
Lemma cnorm_sq_eq_C0 (z : Complex) : Cnorm_sq z = 0%R -> z = C0.
Proof.
  intro H. unfold Cnorm_sq in H.
  pose proof (rsqr_pos (re z)) as Hr0.
  pose proof (rsqr_pos (im z)) as Hi0.
  assert (Hre0 : Rsqr (re z) = 0%R) by lra.
  assert (Him0 : Rsqr (im z) = 0%R) by lra.
  assert (Hz0 : Rsqr 0 = 0%R) by (unfold Rsqr; ring).
  assert (Hprem : Rsqr (re z) = Rsqr 0%R) by (rewrite Hz0; exact Hre0).
  assert (Hqrem : Rsqr (im z) = Rsqr 0%R) by (rewrite Hz0; exact Him0).
  apply Rsqr_eq_abs_0 in Hprem. apply Rsqr_eq_abs_0 in Hqrem.
  rewrite Rabs_R0 in Hprem, Hqrem.
  apply Complex_eq.
  - apply rabs_eq0. exact Hprem.
  - apply rabs_eq0. exact Hqrem.
Qed.

(* Csub 代数三件 *)
Lemma csub_eq0 (a b : Complex) : a -c b = C0 -> a = b.
Proof.
  intros H.
  apply Complex_eq.
  - pose proof (f_equal (@re) H) as Hre. simpl in Hre. lra.
  - pose proof (f_equal (@im) H) as Him. simpl in Him. lra.
Qed.

Lemma csub_distr_r (a b z : Complex) :
  (a -c b) *c z = a *c z -c b *c z.
Proof.
  apply Complex_eq; unfold Csub, Cmul;
    destruct a; destruct b; destruct z; simpl; ring.
Qed.

Lemma Csum_sub (f g : nat -> Complex) (n : nat) :
  Csum (fun i => f i -c g i) n = Csum f n -c Csum g n.
Proof.
  induction n as [| n IH].
  - apply Complex_eq; unfold Csub, C0; simpl; ring.
  - cbn [Csum]. rewrite IH.
    apply Complex_eq; unfold Csub, Cadd;
      destruct (f 0%nat); destruct (g 0%nat); destruct (Csum f n);
        destruct (Csum g n); simpl; ring.
Qed.

Fixpoint map2_csub (a b : list Complex) : list Complex :=
  match a, b with
  | x :: xs, y :: ys => Csub x y :: map2_csub xs ys
  | _, _ => []
  end.

(* independent.Csum 版逐点扩展（Csum_ext 是 PrimeEmbedding.Csum 版） *)
Lemma csum_ext_indep (f g : nat -> Complex) (n : nat) :
  (forall i, (i < n)%nat -> f i = g i) ->
  independent.Csum f n = independent.Csum g n.
Proof.
  induction n as [| n IH]; intros H.
  - reflexivity.
  - replace (independent.Csum f (S n))
      with (Cadd (independent.Csum f n) (f n)) by reflexivity.
    replace (independent.Csum g (S n))
      with (Cadd (independent.Csum g n) (g n)) by reflexivity.
    rewrite IH by (intros i Hi; apply H; lia).
    rewrite (H n) by lia. reflexivity.
Qed.

Lemma map2_csub_length (a b : list Complex) :
  length a = length b -> length (map2_csub a b) = length a.
Proof.
  revert a.
  induction b as [| y ys IH]; intros a Hlen.
  - destruct a as [| x xs]; [ reflexivity | simpl in Hlen; lia ].
  - destruct a as [| x xs]; [ simpl in Hlen; lia | ].
    simpl in Hlen. assert (Hxs : length xs = length ys) by lia.
    simpl. rewrite (IH xs Hxs). reflexivity.
Qed.

Lemma map2_sub_nth (a b : list Complex) :
  length a = length b ->
  forall idx, nth idx (map2_csub a b) C0 = nth idx a C0 -c nth idx b C0.
Proof.
  revert a.
  induction b as [| y ys IH]; intros a Hlen idx.
  - destruct a as [| x xs].
    + destruct idx as [| idx].
      * apply Complex_eq; unfold Csub, C0; simpl; ring.
      * apply Complex_eq; unfold Csub, C0; simpl; ring.
    + simpl in Hlen. lia.
  - destruct a as [| x xs]; [ simpl in Hlen; lia | ].
    simpl in Hlen. assert (Hxs : length xs = length ys) by lia.
    destruct idx as [| idx].
    + apply Complex_eq; unfold Csub, C0; simpl;
        match goal with |- ?g => idtac "GOAL1:" g end; ring.
    + cbn [map2_csub nth]. exact (IH xs Hxs idx).
Qed.

Lemma lsum_pos (f : nat -> R) (m : nat) :
  (forall k, (0 <= f k)%R) -> (0 <= lsum f m)%R.
Proof.
  intros Hf. induction m as [| m IHm]; cbn [lsum].
  - apply Rle_refl.
  - pose proof (Hf m). lra.
Qed.

Lemma lsum_single_le (f : nat -> R) (m d : nat) :
  (forall k, (0 <= f k)%R) -> (d < m)%nat -> (f d <= lsum f m)%R.
Proof.
  intros Hf Hd.
  induction m as [| m IH].
  - lia.
  - cbn [lsum].
    pose proof (lsum_pos f m Hf) as Hsum.
    destruct (Nat.eq_dec d m) as [->|Hne].
    + lra.
    + assert (Hdm : (d < m)%nat) by lia.
      pose proof (Hf m) as Hfm0.
      specialize (IH Hdm). lra.
Qed.

(* ---------- CS-1a：C-梯子逐对相干（PB4/Fpair 形）≤ 2πq/(1−q) ---------- *)

Lemma fpair_pos (a b : nat) :
  (2 <= a)%nat -> (2 <= b)%nat -> (0 <= Fpair a b)%R.
Proof.
  intros Ha Hb. unfold Fpair.
  assert (Hs : (0 < sqrt (INR a * INR b))%R).
  { apply sqrt_pos_strict.
    assert (H1a : (1 < INR a)%R) by (apply (lt_INR 1 a); lia).
    assert (H1b : (1 < INR b)%R) by (apply (lt_INR 1 b); lia).
    nra. }
  replace 0%R with (0 * / sqrt (INR a * INR b))%R by ring.
  apply Rmult_le_compat_r.
  - apply Rlt_le. apply Rinv_0_lt_compat. exact Hs.
  - apply Cnorm_ge_0.
Qed.

Corollary cs1a_pair_bound (C : nat) (v : nat -> nat) (i m d : nat) :
  (2 <= C)%nat -> (m <= i)%nat ->
  (forall j, (2 <= v j)%nat) ->
  (forall j, (v j * C <= v (S j)))%nat ->
  (d < m)%nat ->
  Fpair (v i) (v (ssrnat.addn i (S d)))
  <= 2 * (PI * qval C / (1 - qval C))%R.
Proof.
  intros HC Hmi Hv2 Hchain Hd.
  pose proof (row_sum_3halfs C v i m (le_Prop_to_mc 2 C HC)
                (le_Prop_to_mc m i Hmi)
                (fun j => le_Prop_to_mc 2 (v j) (Hv2 j))
                (fun j => le_Prop_to_mc (v j * C)%nat (v (S j)) (Hchain j)))
    as Hrow.
  assert (Hp1 : (0 <= lsum (fun d0 => Fpair (v i) (v (ssrnat.addn i (S d0)))) m)%R).
  { apply lsum_pos. intros k. cbv beta. apply fpair_pos.
    - pose proof (Hv2 i); lia.
    - pose proof (Hv2 (ssrnat.addn i (S k))); lia. }
  assert (Hp2 : (0 <= lsum (fun d0 => Fpair (v (ssrnat.subn i (S d0))) (v i)) m)%R).
  { apply lsum_pos. intros k. cbv beta. apply fpair_pos.
    - pose proof (Hv2 (ssrnat.subn i (S k))); lia.
    - pose proof (Hv2 i); lia. }
  apply Rle_trans with
    (r2 := lsum (fun d0 => Fpair (v i) (v (ssrnat.addn i (S d0)))) m).
  - apply (lsum_single_le (fun d0 => Fpair (v i) (v (ssrnat.addn i (S d0)))) m d).
    + intros k. cbv beta. apply fpair_pos.
      * pose proof (Hv2 i); lia.
      * pose proof (Hv2 (ssrnat.addn i (S k))); lia.
    + exact Hd.
  - lra.
Qed.

(* ---------- CS-2：一致 RIP（Candès–Tao 命名，∀s 一致） ---------- *)

Definition rip_delta (C : nat) : R := 4 * UnconditionalBasisLemmas.K (INR C).

Theorem cs2_rip_uniform (seq : nat -> nat)
        (Hge2 : forall i, (seq i >= 2)%nat)
        (Hinc : forall i, (seq i < seq (S i))%nat)
        (C : nat) (HCgt2 : (C > 2)%nat)
        (Hsparse : forall i, (INR (seq (S i)) > INR C * INR (seq i))%R)
        (I : list nat) (coeffs : list Complex)
        (Hdup : NoDup I) (Hsorted : Sorted Nat.lt I)
        (Hlen : length I = length coeffs) :
  (* Candès–Tao 双侧 RIP：(1−δ)·‖c‖² ≤ ‖Φc‖² ≤ (1+δ)·‖c‖²，δ = 4K(C)，∀s 一致 *)
  (1 - rip_delta C) * sum_f_R0 (fun i => Cnorm_sq (nth i coeffs C0)) (length I - 1)
  <= l2_norm_sq
       (fun k => Csum (fun idx => nth idx coeffs C0
                                *c psi (nth idx (map seq I) 0%nat) k)
                (length I))
       (S (seq (fold_right Init.Nat.max 0%nat I)) - 1)
  <= (1 + rip_delta C) * sum_f_R0 (fun i => Cnorm_sq (nth i coeffs C0)) (length I - 1).
Proof.
  pose proof (ExtendedTheorems.psi_unconditional_basis
                seq Hge2 Hinc C HCgt2 Hsparse I coeffs Hdup Hsorted Hlen) as HT.
  cbv zeta in HT.
  unfold rip_delta.
  exact HT.
Qed.

Lemma twoK_lt_1 (C : nat) : (10 <= C)%nat -> (2 * K (INR C) < 1)%R.
Proof.
  intros HC. unfold K.
  assert (H9 : (INR 9 < INR C)%R).
  { apply Rlt_le_trans with (INR 10).
    - apply (lt_INR 9 10). lia.
    - apply (le_INR 10 C). lia. }
  assert (Hge : (0 <= INR 9)%R) by (apply pos_INR).
  assert (Hlt : (sqrt (INR 9) < sqrt (INR C))%R)
    by (apply sqrt_lt_1; [ exact Hge | apply (le_INR 0 C); lia | exact H9 ]).
  assert (Hs9 : (sqrt (INR 9) = 3)%R).
  { replace (INR 9) with (3 * 3)%R by (unfold INR; simpl; ring).
    apply sqrt_square. lra. }
  rewrite Hs9 in Hlt.
  assert (Hs : (0 < sqrt (INR C) - 1)%R) by lra.
  assert (Hnz : (sqrt (INR C) - 1 <> 0)%R) by lra.
  apply (Rmult_lt_reg_r (sqrt (INR C) - 1)).
  - exact Hs.
  - assert (Hkey : ((2 * (1 / (sqrt (INR C) - 1))) * (sqrt (INR C) - 1) = 2)%R)
      by (field; exact Hnz).
    rewrite Hkey. rewrite Rmult_1_l. lra.
Qed.

(* ---------- CS-6：embedding 常数（与 CS-3 合并陈述） ---------- *)

Corollary cs6_embedding (C : nat) (HC10 : (10 <= C)%nat) :
  (0 < 1 - 2 * K (INR C))%R.
Proof. apply twoK_lt_1 in HC10. lra. Qed.

(* ---------- CS-3：能量不丢失 + s-sparse 唯一性（★核心） ---------- *)

(* CS-6/CS-3 核心：能量不丢失——零能量合成 ⟹ 零系数 *)
Theorem cs3_energy_zero (seq : nat -> nat)
        (Hge2 : forall i, (seq i >= 2)%nat)
        (Hinc : forall i, (seq i < seq (S i))%nat)
        (C : nat) (HCgt2 : (C > 2)%nat)
        (Hsparse : forall i, (INR (seq (S i)) > INR C * INR (seq i))%R)
        (I : list nat) (coeffs : list Complex)
        (Hdup : NoDup I) (Hsorted : Sorted Nat.lt I)
        (Hlen : length I = length coeffs)
        (HC10 : (10 <= C)%nat)
        (Hzero : l2_norm_sq
                   (fun k => Csum (fun idx => nth idx coeffs C0
                                            *c psi (nth idx (map seq I) 0%nat) k)
                            (length I))
                   (S (seq (fold_right Init.Nat.max 0%nat I)) - 1) = 0%R) :
  forall i, (i < length I)%nat -> nth i coeffs C0 = C0.
Proof.
  intros i Hi.
  pose proof (ExtendedTheorems.psi_unconditional_basis_tight
                seq Hge2 Hinc C HCgt2 Hsparse I coeffs Hdup Hsorted Hlen)
    as HT.
  cbv zeta in HT.
  destruct HT as [Hlo Hhi].
  pose proof (sum_cnormsq_pos coeffs (length I - 1)) as Hpos.
  pose proof (twoK_lt_1 C HC10) as HK.
  (* 把 Hlo 的 l2F（ca_decay 形态）经 change（convertibility）归零——绕开
     rewrite 的语法匹配盲区（E154） *)
  assert (Hlo0 : ((1 - 2 * UnconditionalBasisLemmas.K (INR C)) *
                  sum_f_R0 (fun i0 => Cnorm_sq (nth i0 coeffs C0))
                    (length I - 1) <= 0)%R).
  { match goal with H : ((1 - _) * _ <= ?c)%R |- _ =>
      (assert (Hc0 : c = 0%R)
         by (change (l2_norm_sq
                       (fun k : nat =>
                        Csum (fun idx : nat =>
                                nth idx coeffs C0
                                *c psi (nth idx (map seq I) 0%nat) k)
                        (length I))
                      (S (seq (fold_right Init.Nat.max 0%nat I)) - 1) = 0%R);
              exact Hzero);
       rewrite Hc0 in H;
       exact H)
    end. }
  assert (Hge : (0 <= (1 - 2 * UnconditionalBasisLemmas.K (INR C)) *
                       sum_f_R0 (fun i0 => Cnorm_sq (nth i0 coeffs C0))
                         (length I - 1))%R) by nra.
  assert (Hprod : ((1 - 2 * UnconditionalBasisLemmas.K (INR C)) *
                   sum_f_R0 (fun i0 => Cnorm_sq (nth i0 coeffs C0))
                     (length I - 1) = 0)%R) by lra.
  assert (HS0 : (sum_f_R0 (fun i0 => Cnorm_sq (nth i0 coeffs C0))
                             (length I - 1) = 0)%R).
  { destruct (Rmult_integral (1 - 2 * UnconditionalBasisLemmas.K (INR C))
                (sum_f_R0 (fun i0 => Cnorm_sq (nth i0 coeffs C0))
                   (length I - 1)) Hprod) as [Hbad | Hgood].
    - lra.
    - exact Hgood. }
  assert (Hzip : Cnorm_sq (nth i coeffs C0) = 0%R).
  { apply Rle_antisym.
    - apply Rle_trans with
        (r2 := sum_f_R0 (fun j => Cnorm_sq (nth j coeffs C0)) (length I - 1)).
      + apply norm_sq_coeff_le. lia.
      + rewrite HS0. apply Rle_refl.
    - apply Cnorm_sq_ge_0. }
  apply (cnorm_sq_eq_C0 (nth i coeffs C0) Hzip).
Qed.

(* ★CS-3 主定理：s-sparse 唯一性——测量端信息不丢失 ⟹ 系数唯一 *)
Theorem cs3_unique (seq : nat -> nat)
        (Hge2 : forall i, (seq i >= 2)%nat)
        (Hinc : forall i, (seq i < seq (S i))%nat)
        (C : nat) (HCgt2 : (C > 2)%nat)
        (Hsparse : forall i, (INR (seq (S i)) > INR C * INR (seq i))%R)
        (I : list nat) (Hdup : NoDup I) (Hsorted : Sorted Nat.lt I)
        (HC10 : (10 <= C)%nat)
        (coeffs coeffs' : list Complex)
        (Hlen : length coeffs = length I)
        (Hlen' : length coeffs' = length I)
        (Hpt : forall k, (k <= seq (fold_right Init.Nat.max 0%nat I))%nat ->
          Csum (fun idx => nth idx coeffs C0 *c psi (nth idx (map seq I) 0%nat) k)
            (length I)
          = Csum (fun idx => nth idx coeffs' C0 *c psi (nth idx (map seq I) 0%nat) k)
            (length I)) :
  forall i, (i < length I)%nat -> nth i coeffs C0 = nth i coeffs' C0.
Proof.
  assert (Hab : length coeffs = length coeffs')
    by exact (eq_trans Hlen (eq_sym Hlen')).
  assert (Hdlen : length I = length (map2_csub coeffs coeffs')).
  { rewrite (map2_csub_length coeffs coeffs' Hab). symmetry. exact Hlen. }
  assert (Hzerod :
    l2_norm_sq
      (fun k => Csum (fun idx =>
                nth idx (map2_csub coeffs coeffs') C0
                *c psi (nth idx (map seq I) 0%nat) k)
              (length I))
      (S (seq (fold_right Init.Nat.max 0%nat I)) - 1) = 0%R).
  { apply l2_norm_sq_zero. intros k Hk.
    transitivity (Csum (fun idx =>
                nth idx coeffs C0 *c psi (nth idx (map seq I) 0%nat) k
                -c nth idx coeffs' C0 *c psi (nth idx (map seq I) 0%nat) k)
              (length I)).
    - apply csum_ext_indep. intros idx Hidx.
      rewrite (map2_sub_nth coeffs coeffs' Hab idx).
      apply csub_distr_r.
    - rewrite Csum_sub. rewrite (Hpt k); [ | lia ].
      apply Complex_eq; unfold Csub, C0; simpl; ring. }
  intros idx Hidx.
  pose proof (cs3_energy_zero seq Hge2 Hinc C HCgt2 Hsparse I
                (map2_csub coeffs coeffs') Hdup Hsorted Hdlen HC10 Hzerod
                idx Hidx) as Hd0.
  rewrite (map2_sub_nth coeffs coeffs' Hab idx) in Hd0.
  apply (csub_eq0 _ _ Hd0).
Qed.

(* ---------- CS-6/CS-1b：embedding 单射 + spark 下界（CS-3 推论） ---------- *)

Corollary cs1b_spark (seq : nat -> nat)
        (Hge2 : forall i, (seq i >= 2)%nat)
        (Hinc : forall i, (seq i < seq (S i))%nat)
        (C : nat) (HCgt2 : (C > 2)%nat)
        (Hsparse : forall i, (INR (seq (S i)) > INR C * INR (seq i))%R)
        (I : list nat) (Hdup : NoDup I) (Hsorted : Sorted Nat.lt I)
        (HC10 : (10 <= C)%nat)
        (d : list Complex) (Hdn : length d = length I)
        (Hzerod : l2_norm_sq
                    (fun k => Csum (fun idx => nth idx d C0
                                             *c psi (nth idx (map seq I) 0%nat) k)
                             (length I))
                    (S (seq (fold_right Init.Nat.max 0%nat I)) - 1) = 0%R) :
  forall i, (i < length I)%nat -> nth i d C0 = C0.
Proof.
  apply (cs3_energy_zero seq Hge2 Hinc C HCgt2 Hsparse I d Hdup Hsorted
           (eq_sym Hdn) HC10 Hzerod).
Qed.

(* ---------- CS4c：近重复对精确相干 + RIP 证书爆炸（★"剪 503/255/127 应恶化"的定理侧镜像） ---------- *)

(* ψ₁ 的 k=0 项 = 1（1/√1 归一 + 零相位单位根） *)
Lemma cs4c_psi10 : psi 1 0 = C1.
Proof.
  unfold psi, UnconditionalBasis.phi.
  cbn [Nat.ltb Nat.leb].
  replace (2 * PI * INR 0 / INR 1) with 0%R
    by (rewrite INR_0, INR_1; unfold Rdiv; rewrite Rmult_0_r, Rmult_0_l; reflexivity).
  replace (Cexp (0 +i 0)) with C1
    by (unfold Cexp, C1; simpl; rewrite exp_0, cos_0, sin_0; f_equal; ring).
  replace (1 / sqrt (INR 1)) with 1%R
    by (rewrite INR_1, sqrt_1; unfold Rdiv;
        rewrite Rinv_1, Rmult_1_l; reflexivity).
  apply Complex_eq; unfold Cof_real, Cmul, C1, C0; simpl; ring.
Qed.

(* ψ₂ 的 k=0 项 = 1/√2（实数归一系数） *)
Lemma cs4c_psi20 : psi 2 0 = Cof_real (1 / sqrt 2).
Proof.
  unfold psi, UnconditionalBasis.phi.
  cbn [Nat.ltb Nat.leb].
  replace (2 * PI * INR 0 / INR 2) with 0%R
    by (rewrite INR_0; unfold Rdiv; rewrite Rmult_0_r, Rmult_0_l; reflexivity).
  replace (Cexp (0 +i 0)) with C1
    by (unfold Cexp, C1; simpl; rewrite exp_0, cos_0, sin_0; f_equal; ring).
  replace (INR 2) with 2%R by (rewrite S_INR, INR_1; ring).
  apply Complex_eq; unfold Cof_real, Cmul, C1; simpl; ring.
Qed.

(* 实复数共轭不变 *)
Lemma cconj_cof_real (r : R) : Cconj (Cof_real r) = Cof_real r.
Proof. apply Complex_eq; unfold Cconj, Cof_real; simpl; ring. Qed.

(* 实复数模 = 绝对值（正实数时为自身）——经 Cnorm_sq 分量计算 *)
Lemma cnorm_cof_real (r : R) : (0 <= r)%R -> Cnorm (Cof_real r) = r.
Proof.
  intros Hr. unfold Cnorm, Cof_real, Cnorm_sq.
  simpl. replace (Rsqr r + Rsqr 0) with (Rsqr r) by (unfold Rsqr; simpl; ring).
  apply sqrt_Rsqr. exact Hr.
Qed.

(* ★近重复对 {1,2} 的相干 = 1/√2（精确值——零相位使内积为纯实正数） *)
Theorem near_dup_coherence_12 : coh 1 2 = (1 / sqrt 2)%R.
Proof.
  unfold coh.
  replace (Nat.min 1 2) with 1%nat by reflexivity.
  assert (Hstep : PrimeEmbedding.Csum
                    (fun k : nat => psi 1 k *c Cconj (psi 2 k)) 1%nat
                = psi 1 0 *c Cconj (psi 2 0)).
  { change (PrimeEmbedding.Csum
              (fun k : nat => psi 1 k *c Cconj (psi 2 k)) 1%nat)
      with (Cadd (psi 1 0 *c Cconj (psi 2 0))
                 (PrimeEmbedding.Csum
                    (fun k : nat => psi 1 k *c Cconj (psi 2 k)) 0%nat)).
    change (PrimeEmbedding.Csum
              (fun k : nat => psi 1 k *c Cconj (psi 2 k)) 0%nat) with C0.
    apply Cadd_0_r. }
  rewrite Hstep, cs4c_psi10, cs4c_psi20, cconj_cof_real.
  (* C1 *c Cof_real r = Cof_real r *)
  replace (C1 *c Cof_real (1 / sqrt 2)) with (Cof_real (1 / sqrt 2))
    by (apply Complex_eq; unfold C1, Cmul, Cof_real; simpl; ring).
  apply cnorm_cof_real.
  assert (Hs2 : (0 < sqrt 2)%R) by (apply sqrt_pos_strict; lra).
  unfold Rdiv. rewrite Rmult_1_l. apply Rlt_le, Rinv_0_lt_compat. exact Hs2.
Qed.

(* ★CS4c 主定理：s = 3 时 (s−1)·μ ≥ 2·(1/√2) = √2 > 1——Gershgorin 型
   RIP 上界证书在含近重复对的梯子上必然失效（"剪 503/255/127 应恶化"的定理侧） *)
Theorem cs4c_explosion : (1 < 2 * coh 1 2)%R.
Proof.
  rewrite near_dup_coherence_12.
  assert (Hs2 : (0 < sqrt 2)%R) by (apply sqrt_pos_strict; lra).
  assert (Hnz : (sqrt 2 <> 0)%R) by (apply Rgt_not_eq; exact Hs2).
  assert (H1 : (1 < sqrt 2)%R).
  { rewrite <- sqrt_1. apply sqrt_lt_1; lra. }
  assert (Hsqrt2 : (sqrt 2 * sqrt 2 = 2)%R) by (apply sqrt_sqrt; lra).
  assert (Ht : (2 * / sqrt 2 = sqrt 2)%R).
  { rewrite <- Hsqrt2 at 1.
    rewrite Rmult_assoc.
    rewrite Rinv_r by exact Hnz.
    rewrite Rmult_1_r. reflexivity. }
  unfold Rdiv. rewrite Rmult_1_l.
  rewrite Ht. exact H1.
Qed.

End CSBattle.

Print Assumptions CSBattle.cs2_rip_uniform.
Print Assumptions CSBattle.cs3_energy_zero.
Print Assumptions CSBattle.cs3_unique.
Print Assumptions CSBattle.cs1b_spark.
Print Assumptions CSBattle.cs1a_pair_bound.
Print Assumptions CSBattle.near_dup_coherence_12.
Print Assumptions CSBattle.cs4c_explosion.
