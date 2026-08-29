(* ============================================================

   数学内容（Welch 界，经典 R 轨道）：
     M 个单位范数向量 u_0..u_{M-1} ∈ R^N（N < M），互相干上界 μ：
       ∀i≠j: |⟨u_i,u_j⟩| ≤ μ  ⟹  (M−N) ≤ N·(M−1)·μ²
     ——任何 M 个 N 维单位向量的字典，最大相干不能低于 Welch 下界；
       与频率阶梯原子族的相干紧性（witness_sandwich，Θ(C^{−3/2})）对比，
       证明该族在低相干意义下接近理论最优。

   证明路线（初等，避免特征值理论——行向量 Cauchy-Schwarz）：
         add / opp / one / sq_expand / factor / sum4_swap / split_diag / ge_diag。
     R1. Gram 重排：Σ_{i,j}⟨u_i,u_j⟩² = Σ_{k,l}(Σ_i u_ik·u_il)²。
     R2. Σ_{k,l}(Σ_i u_ik·u_il)² ≥ (Σ_k Σ_i u_ik²)²/N（对角截断 + CS 幂平均）。
     R3. Σ_k Σ_i u_ik² = M（单位范数）⟹ Gram ≥ M²/N。
     R4. Gram ≤ M + M(M−1)μ²（对角 1 + 非对角 μ² 计数）。
     R5. nra 收尾：(M−N) ≤ N(M−1)μ²。

   依赖：仅 Stdlib Reals + mathcomp（ssreflect 记法）；sum_f_R0 全套自证。
   审计：零 Admitted / 零自定义公理（同 probe_incoherence 脚印）。
   ============================================================ *)
From mathcomp Require Import ssreflect ssrbool ssrnat seq eqtype div prime.
Require Import Stdlib.Reals.Reals.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.micromega.Lra.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Logic.FunctionalExtensionality.
Require Import ca_taylor.   (* TaylorTheorem.sum_f_R0_const（双参数版）；合并再生时随 ca_* Require 剔除 *)

Open Scope R_scope.

(* ============ R0. 求和工具（本地自证，防合并重名） ============ *)

Lemma wl_sum_swap (A B : nat) (h : nat -> nat -> R) :
  sum_f_R0 (fun i => sum_f_R0 (h i) B) A =
  sum_f_R0 (fun j => sum_f_R0 (fun i => h i j) A) B.
Proof.
  revert B h. induction A as [| A IH]; intros B h; simpl.
  - induction B as [| B IHB]; simpl; lra.
  - rewrite IH. induction B as [| B IHB]; simpl; lra.
Qed.

Lemma wl_sum_scal_l (c : R) (f : nat -> R) (n : nat) :
  sum_f_R0 (fun i => c * f i) n = c * sum_f_R0 f n.
Proof.
  induction n as [| n IH]; simpl; [ring | rewrite IH; ring].
Qed.

Lemma wl_sum_scal_r (c : R) (f : nat -> R) (n : nat) :
  sum_f_R0 (fun i => f i * c) n = sum_f_R0 f n * c.
Proof.
  induction n as [| n IH]; simpl; [ring | rewrite IH; ring].
Qed.

Lemma wl_sum_one (n : nat) : sum_f_R0 (fun _ : nat => 1) n = INR (S n).
Proof.
  induction n as [| n IH]; simpl.
  - reflexivity.
  - rewrite IH. simpl. ring.
Qed.

(* 常数和：Σ_{i≤n} c = (S n)·c *)
Lemma wl_sum_const (c : R) (n : nat) : sum_f_R0 (fun _ : nat => c) n = INR (S n) * c.
Proof.
  induction n as [| n IH]; simpl.
  - ring.
  - rewrite IH. simpl. ring.
Qed.

Lemma wl_sum_ext (f g : nat -> R) (n : nat) :
  (forall k, le k n -> f k = g k) -> sum_f_R0 f n = sum_f_R0 g n.
Proof.
  intros H. induction n as [| n IH]; simpl.
  - apply H. lia.
  - assert (Hn : forall k : nat, le k n -> f k = g k).
    { intros k Hk. apply H. lia. }
    rewrite (IH Hn).
    assert (Hsn : f (S n) = g (S n)) by (apply H; lia).
    rewrite Hsn. reflexivity.
Qed.

Lemma wl_sum_le (f g : nat -> R) (n : nat) :
  (forall k, le k n -> f k <= g k) -> sum_f_R0 f n <= sum_f_R0 g n.
Proof.
  intros H. induction n as [| n IH]; simpl.
  - apply H. lia.
  - assert (Hn : forall k : nat, le k n -> f k <= g k).
    { intros k Hk. apply H. lia. }
    apply Rplus_le_compat; [exact (IH Hn) | apply H; lia].
Qed.

Lemma wl_sum_nonneg (f : nat -> R) (n : nat) :
  (forall k, le k n -> 0 <= f k) -> 0 <= sum_f_R0 f n.
Proof.
  intros H. induction n as [| n IH]; simpl.
  - apply H. lia.
  - assert (Hn : forall k : nat, le k n -> 0 <= f k).
    { intros k Hk. apply H. lia. }
    apply Rplus_le_le_0_compat; [exact (IH Hn) | apply H; lia].
Qed.

Lemma wl_sum_add (f g : nat -> R) (n : nat) :
  sum_f_R0 (fun k => f k + g k) n = sum_f_R0 f n + sum_f_R0 g n.
Proof.
  induction n as [| n IH]; simpl; [ring | rewrite IH; ring].
Qed.

Lemma wl_sum_opp (f : nat -> R) (n : nat) :
  sum_f_R0 (fun k => - f k) n = - sum_f_R0 f n.
Proof.
  induction n as [| n IH]; simpl; [ring | rewrite IH; ring].
Qed.

(* (Σ_{k≤n} a k)·(Σ_{k≤n} a k) = Σ_{k≤n}Σ_{l≤n} a k·a l *)
Lemma wl_sum_sq_expand (a : nat -> R) (n : nat) :
  sum_f_R0 (fun k => sum_f_R0 (fun l => a k * a l) n) n
  = (sum_f_R0 a n) * (sum_f_R0 a n).
Proof.
  transitivity (sum_f_R0 (fun k => a k * sum_f_R0 a n) n).
  - apply wl_sum_ext. intros k Hk.
    transitivity (a k * sum_f_R0 a n).
    + rewrite (wl_sum_scal_l (a k) a n). reflexivity.
    + reflexivity.
  - rewrite (wl_sum_scal_r (sum_f_R0 a n) (fun k => a k) n). reflexivity.
Qed.

(* Σ_{i≤n}Σ_{j≤n} a i·b j = (Σa)·(Σb) *)
Lemma wl_sum_factor (a b : nat -> R) (n : nat) :
  sum_f_R0 (fun i => sum_f_R0 (fun j => a i * b j) n) n
  = (sum_f_R0 a n) * (sum_f_R0 b n).
Proof.
  transitivity (sum_f_R0 (fun i => a i * sum_f_R0 b n) n).
  - apply wl_sum_ext. intros i Hi.
    transitivity (a i * sum_f_R0 b n).
    + rewrite (wl_sum_scal_l (a i) b n). reflexivity.
    + reflexivity.
  - rewrite (wl_sum_scal_r (sum_f_R0 b n) (fun i => a i) n). reflexivity.
Qed.

(* 三重和换序：Σ_i Σ_k Σ_l h = Σ_k Σ_l Σ_i h（i 上限 A；k,l 上限 B） *)
Lemma wl_sum3_swap (A B : nat) (h : nat -> nat -> nat -> R) :
  sum_f_R0 (fun i => sum_f_R0 (fun k => sum_f_R0 (fun l => h i k l) B) B) A
  = sum_f_R0 (fun k => sum_f_R0 (fun l => sum_f_R0 (fun i => h i k l) A) B) B.
Proof.
  revert B h. induction A as [| A IH]; intros B h.
  - simpl. reflexivity.
  - (* 拆出 i = S A 项 *)
    assert (Hsn : sum_f_R0 (fun i : nat => sum_f_R0 (fun k => sum_f_R0 (fun l => h i k l) B) B) (S A)
                 = sum_f_R0 (fun i : nat => sum_f_R0 (fun k => sum_f_R0 (fun l => h i k l) B) B) A
                   + sum_f_R0 (fun k => sum_f_R0 (fun l => h (S A) k l) B) B).
    { simpl. ring. }
    rewrite Hsn.
    replace (sum_f_R0 (fun i : nat => sum_f_R0 (fun k => sum_f_R0 (fun l => h i k l) B) B) A)
      with (sum_f_R0 (fun k => sum_f_R0 (fun l => sum_f_R0 (fun i : nat => h i k l) A) B) B)
      by (symmetry; exact (IH B h)).
    (* 目标：[Σ_k Σ_l Σ_{i≤A} h i k l] + [Σ_k Σ_l h (S A) k l] = Σ_k Σ_l Σ_{i≤S A} h i k l *)
    transitivity (sum_f_R0 (fun k => sum_f_R0 (fun l => sum_f_R0 (fun i : nat => h i k l) A) B
                                        + sum_f_R0 (fun l => h (S A) k l) B) B).
    - rewrite <- (wl_sum_add (fun k => sum_f_R0 (fun l => sum_f_R0 (fun i : nat => h i k l) A) B)
                             (fun k => sum_f_R0 (fun l => h (S A) k l) B) B).
      reflexivity.
    - apply wl_sum_ext. intros k Hk.
      rewrite <- (wl_sum_add (fun l => sum_f_R0 (fun i : nat => h i k l) A)
                             (fun l => h (S A) k l) B).
      reflexivity.
Qed.

(* 四重和换序：Σ_{i,j}Σ_{k,l} f = Σ_{k,l}Σ_{i,j} f（i,j 上限 A；k,l 上限 B） *)
Lemma wl_sum4_swap (A B : nat) (f : nat -> nat -> nat -> nat -> R) :
  sum_f_R0 (fun i => sum_f_R0 (fun j =>
    sum_f_R0 (fun k => sum_f_R0 (fun l => f i j k l) B) B) A) A
  = sum_f_R0 (fun k => sum_f_R0 (fun l =>
    sum_f_R0 (fun i => sum_f_R0 (fun j => f i j k l) A) A) B) B.
Proof.
  revert B f. induction A as [| A IH]; intros B f.
  - simpl. reflexivity.
  - (* 拆出 i = S A 层 *)
    assert (Hsn : sum_f_R0 (fun i : nat =>
                  sum_f_R0 (fun j => sum_f_R0 (fun k => sum_f_R0 (fun l => f i j k l) B) B) (S A)) (S A)
                 = sum_f_R0 (fun i : nat =>
                   sum_f_R0 (fun j => sum_f_R0 (fun k => sum_f_R0 (fun l => f i j k l) B) B) (S A)) A
                   + sum_f_R0 (fun j => sum_f_R0 (fun k => sum_f_R0 (fun l => f (S A) j k l) B) B) (S A)).
    { simpl. ring. }
    rewrite Hsn.
    (* 第一块再拆 j = S A 项 *)
    assert (Hsn2 : sum_f_R0 (fun i : nat =>
                   sum_f_R0 (fun j => sum_f_R0 (fun k => sum_f_R0 (fun l => f i j k l) B) B) (S A)) A
                 = sum_f_R0 (fun i : nat =>
                   sum_f_R0 (fun j => sum_f_R0 (fun k => sum_f_R0 (fun l => f i j k l) B) B) A) A
                   + sum_f_R0 (fun i => sum_f_R0 (fun k => sum_f_R0 (fun l => f i (S A) k l) B) B) A).
    { rewrite <- (wl_sum_add (fun i => sum_f_R0 (fun j => sum_f_R0 (fun k => sum_f_R0 (fun l => f i j k l) B) B) A)
                             (fun i => sum_f_R0 (fun k => sum_f_R0 (fun l => f i (S A) k l) B) B) A).
      apply wl_sum_ext. intros i Hi. simpl. ring. }
    rewrite Hsn2.
    (* 三块：①Σ_{i,j≤A}（IH）②Σ_{i≤A}·(j=S A)（sum3 换序）③Σ_{j≤S A}·(i=S A)（sum3 换序） *)
    replace (sum_f_R0 (fun i : nat => sum_f_R0 (fun j => sum_f_R0 (fun k => sum_f_R0 (fun l => f i j k l) B) B) A) A)
      with (sum_f_R0 (fun k => sum_f_R0 (fun l => sum_f_R0 (fun i => sum_f_R0 (fun j => f i j k l) A) A) B) B)
      by (symmetry; exact (IH B f)).
    rewrite (wl_sum3_swap A B (fun i k l => f i (S A) k l)).
    rewrite (wl_sum3_swap (S A) B (fun j k l => f (S A) j k l)).
    (* 合并：Σ_k Σ_l (Σ_{i,j≤A} + Σ_{i≤A} + Σ_{j≤S A}) = Σ_k Σ_l Σ_{i,j≤S A} *)
    transitivity (sum_f_R0 (fun k => sum_f_R0 (fun l => sum_f_R0 (fun i => sum_f_R0 (fun j => f i j k l) A) A) B
                                        + sum_f_R0 (fun l => sum_f_R0 (fun i => f i (S A) k l) A) B) B
                  + sum_f_R0 (fun k => sum_f_R0 (fun l => sum_f_R0 (fun j => f (S A) j k l) (S A)) B) B).
    - (* 第一块 + 第二块 合并 *)
      rewrite <- (wl_sum_add (fun k => sum_f_R0 (fun l => sum_f_R0 (fun i => sum_f_R0 (fun j => f i j k l) A) A) B)
                             (fun k => sum_f_R0 (fun l => sum_f_R0 (fun i => f i (S A) k l) A) B) B).
      reflexivity.
    - transitivity (sum_f_R0 (fun k => sum_f_R0 (fun l => sum_f_R0 (fun i => sum_f_R0 (fun j => f i j k l) A) A) B
                                        + sum_f_R0 (fun l => sum_f_R0 (fun i => f i (S A) k l) A) B
                                        + sum_f_R0 (fun l => sum_f_R0 (fun j => f (S A) j k l) (S A)) B) B).
      + (* (X+Y) + Z 合并 *)
        rewrite <- (wl_sum_add (fun k => sum_f_R0 (fun l => sum_f_R0 (fun i => sum_f_R0 (fun j => f i j k l) A) A) B
                                          + sum_f_R0 (fun l => sum_f_R0 (fun i => f i (S A) k l) A) B)
                               (fun k => sum_f_R0 (fun l => sum_f_R0 (fun j => f (S A) j k l) (S A)) B) B).
        reflexivity.
      + apply wl_sum_ext. intros k Hk.
        rewrite <- (wl_sum_add (fun l => sum_f_R0 (fun i => sum_f_R0 (fun j => f i j k l) A) A)
                               (fun l => sum_f_R0 (fun i => f i (S A) k l) A) B).
        rewrite <- (wl_sum_add (fun l => sum_f_R0 (fun i => sum_f_R0 (fun j => f i j k l) A) A
                                         + sum_f_R0 (fun i => f i (S A) k l) A)
                               (fun l => sum_f_R0 (fun j => f (S A) j k l) (S A)) B).
        apply wl_sum_ext. intros l Hl.
        rewrite <- (wl_sum_add (fun i => sum_f_R0 (fun j : nat => f i j k l) A)
                               (fun i => f i (S A) k l) A).
        simpl.
        reflexivity.
Qed.

(* 零函数和 = 0 *)
Lemma wl_sum_zero (n : nat) : sum_f_R0 (fun _ : nat => 0) n = 0.
Proof. induction n; simpl; [reflexivity | rewrite IHn; ring]. Qed.

(* ============ R2b. 计数引理（对角/非对角项数） ============ *)

(* 计数：Σ_{j≤Nat.pred M} (if j=?i then 1 else 0) = 1（i < M ⟹ i 在求和范围内） *)
Lemma wl_count_diag (M i : nat) :
  lt i M ->
  sum_f_R0 (fun j => if Nat.eqb j i then 1 else 0) (Nat.pred M) = 1.
Proof.
  intro Hi.
  induction M as [| M IHm].
  - simpl in Hi. lia.
  - destruct M as [| M'].
    + (* M = 1：Nat.pred (S 0) = 0，i < 1 ⟹ i = 0 *)
      simpl in Hi. assert (Hi0 : i = 0%nat) by lia. subst i. simpl. reflexivity.
    + (* M = S (S M')：Nat.pred = S M' *)
      simpl. destruct (Nat.eqb_spec (S M') i) as [Hi' | Hi'].
      * subst i.
        assert (Hext : forall j : nat, le j M' -> ((if Nat.eqb j (S M') then 1 else 0) = 0)%R)
          by (intros j Hj; destruct (Nat.eqb_spec j (S M')) as [Hjs | Hjs]; [exfalso; lia | simpl; reflexivity]).
        rewrite (wl_sum_ext (fun j => if Nat.eqb j (S M') then 1 else 0) (fun _ => 0) M' Hext).
        rewrite wl_sum_zero. rewrite Nat.eqb_refl. ring.
      * assert (Hilt : lt i (S M')) by lia.
        rewrite (IHm Hilt).
        -- destruct i as [| i'].
           ++ simpl. ring.
           ++ assert (Hmi : M' <> i') by (intro Hm; apply Hi'; f_equal; exact Hm).
              rewrite (proj2 (Nat.eqb_neq M' i') Hmi). simpl. ring.
Qed.

(* 计数：非对角项数 = M−1：Σ_{j≤Nat.pred M} (if j=?i then 0 else 1) = M−1（i < M） *)
Lemma wl_count_offdiag (M i : nat) :
  lt i M ->
  sum_f_R0 (fun j => if Nat.eqb j i then 0 else 1) (Nat.pred M) = INR (M - 1).
Proof.
  intro Hi.
  (* 把 if 展开为 1 − (if j=?i then 1 else 0) *)
  assert (Heq : forall j, ((if Nat.eqb j i then 0 else 1) : R) = (1 - (if Nat.eqb j i then 1 else 0))%R).
  { intros j. case (Nat.eqb j i) eqn:E.
    - apply Nat.eqb_eq in E. subst j. simpl. ring.
    - simpl. ring. }
  assert (Hext2 : forall k : nat, le k (Nat.pred M) -> ((if Nat.eqb k i then 0 else 1) = (1 - (if Nat.eqb k i then 1 else 0)))%R)
    by (intros k Hk; apply Heq).
  rewrite (wl_sum_ext (fun j => if Nat.eqb j i then 0 else 1)
                      (fun j => (1 - (if Nat.eqb j i then 1 else 0))%R) (Nat.pred M) Hext2).
  setoid_rewrite (wl_sum_add (fun _ : nat => 1%R)
                             (fun j => (- (if Nat.eqb j i then 1 else 0))%R) (Nat.pred M)).
  setoid_rewrite wl_sum_opp.
  setoid_rewrite wl_sum_one.
  rewrite (wl_count_diag M i Hi).
  replace (INR (S (Nat.pred M)))%R with (INR M)%R by (f_equal; lia).
  assert (HM1 : le 1 M) by lia.
  rewrite (minus_INR M 1 HM1); simpl; ring.
Qed.

(* Gram 平方和 ≤ M + M(M−1)μ² *)

(* 对角项 ≤ 全和（非负）：x k ≤ Σ_{j≤n} x j（k ≤ n 且各 x j ≥ 0） *)
Lemma wl_sum_ge_diag (x : nat -> R) (n k : nat) :
  le k n -> (forall j, le j n -> 0 <= x j) ->
  x k <= sum_f_R0 x n.
Proof.
  intros Hk Hx.
  replace (sum_f_R0 x n)
    with (sum_f_R0 (fun j => (if Nat.eqb j k then x k else 0) + (if Nat.eqb j k then 0 else x j)) n).
      2: { apply wl_sum_ext. intros j0 Hj0.
       destruct (Nat.eqb_spec j0 k) as [Hjk | Hjk].
       - subst. simpl. ring.
       - simpl. ring. }
  rewrite wl_sum_add.
  assert (HsumA : x k <= sum_f_R0 (fun j => if Nat.eqb j k then x k else 0) n).
  { replace (sum_f_R0 (fun j => if Nat.eqb j k then x k else 0) n)
      with (x k * sum_f_R0 (fun j => if Nat.eqb j k then 1 else 0) n).
    2: { rewrite <- (wl_sum_scal_l (x k) (fun j => if Nat.eqb j k then 1 else 0) n).
         apply wl_sum_ext. intros j Hj.
         destruct (Nat.eqb_spec j k); simpl; ring. }
    assert (Hlt : lt k (S n)) by (first [lia | rewrite ltnS; apply/leP; exact Hk]).
    rewrite (wl_count_diag (S n) k Hlt). rewrite Rmult_1_r. apply Rle_refl. }
  assert (HsumB : 0 <= sum_f_R0 (fun j => if Nat.eqb j k then 0 else x j) n).
  { apply wl_sum_nonneg. intros j Hj.
     destruct (Nat.eqb_spec j k) as [Hjk | Hjk].
    - subst. simpl. apply Rle_refl.
    - simpl. apply Hx; exact Hj. }
  lra.
Qed.

(* 幂平均（Cauchy-Schwarz）：(Σ_{k≤n} x k)² ≤ (S n)·Σ_{k≤n} x k²（x ≥ 0） *)
Lemma wl_sum_sq_ge_mean_sq (x : nat -> R) (n : nat) :
  (forall k, le k n -> 0 <= x k) ->
  (sum_f_R0 x n) * (sum_f_R0 x n)
  <= INR (S n) * sum_f_R0 (fun k => x k * x k) n.
Proof.
  intros Hx.
  (* D := Σ_{i,j≤n} (x_i − x_j)² ≥ 0 *)
  assert (HD : 0 <= sum_f_R0 (fun i => sum_f_R0 (fun j => (x i - x j) * (x i - x j)) n) n).
  { apply wl_sum_nonneg. intros i Hi.
    apply wl_sum_nonneg. intros j Hj.
    apply Rle_0_sqr. }
  (* 展开 D = 2·(S n)·Σx² − 2·(Σx)² *)
  assert (HD_eq : sum_f_R0 (fun i => sum_f_R0 (fun j => (x i - x j) * (x i - x j)) n) n
                  = 2 * INR (S n) * sum_f_R0 (fun k => x k * x k) n
                    - 2 * (sum_f_R0 x n) * (sum_f_R0 x n)).
  { (* 逐 (i,j) 展开 ring *)
    transitivity (sum_f_R0 (fun i => sum_f_R0 (fun j =>
        x i * x i - 2 * (x i * x j) + x j * x j) n) n).
    { apply wl_sum_ext. intros i Hi.
      apply wl_sum_ext. intros j Hj. ring. }
    (* 逐 i 层线性拆解 *)
    transitivity (sum_f_R0 (fun i =>
        INR (S n) * (x i * x i) - 2 * (x i * sum_f_R0 x n) + sum_f_R0 (fun j => x j * x j) n) n).
    { apply wl_sum_ext. intros i Hi.
      (* Σ_j (x_i² − 2x_ix_j + x_j²) = (S n)x_i² − 2x_iΣx + Σx² *)
      transitivity (sum_f_R0 (fun j => x i * x i) n
                    - sum_f_R0 (fun j => 2 * (x i * x j)) n
                    + sum_f_R0 (fun j => x j * x j) n).
      { rewrite (wl_sum_add (fun j => x i * x i - 2 * (x i * x j)) (fun j => x j * x j) n).
        rewrite (wl_sum_add (fun j => x i * x i) (fun j => - (2 * (x i * x j))) n).
        rewrite wl_sum_opp. ring. }
      replace (sum_f_R0 (fun j : nat => x i * x i) n)
        with (INR (S n) * (x i * x i)).
      2: { symmetry. rewrite (TaylorTheorem.sum_f_R0_const (x i * x i) n). ring. }
      replace (sum_f_R0 (fun j : nat => 2 * (x i * x j)) n)
        with (2 * (x i * sum_f_R0 x n)).
      2: { transitivity (2 * sum_f_R0 (fun j => x i * x j) n).
           - f_equal. symmetry. exact (wl_sum_scal_l (x i) x n).
           - symmetry. exact (wl_sum_scal_l 2 (fun j => x i * x j) n). }
      ring. }
    (* 外层线性拆解 *)
    transitivity (INR (S n) * sum_f_R0 (fun i => x i * x i) n
                  - 2 * (sum_f_R0 x n) * (sum_f_R0 x n)
                  + INR (S n) * sum_f_R0 (fun i => x i * x i) n).
    { (* Σ_i (A_i − B_i + C_i) = Σ_i (A_i − B_i) + Σ_i C_i *)
      transitivity (sum_f_R0 (fun i => INR (S n) * (x i * x i) - 2 * (x i * sum_f_R0 x n)) n
                    + sum_f_R0 (fun i => sum_f_R0 (fun j => x j * x j) n) n).
      - rewrite <- (wl_sum_add (fun i0 => INR (S n) * (x i0 * x i0) - 2 * (x i0 * sum_f_R0 x n))
                               (fun _ : nat => sum_f_R0 (fun j => x j * x j) n) n).
        apply wl_sum_ext. intros i Hi. reflexivity.
      - transitivity (sum_f_R0 (fun i => INR (S n) * (x i * x i) - 2 * (x i * sum_f_R0 x n)) n
                      + INR (S n) * sum_f_R0 (fun i => x i * x i) n).
        + apply Rplus_eq_compat_l.
          replace (sum_f_R0 (fun i : nat => sum_f_R0 (fun j : nat => x j * x j) n) n)
            with (INR (S n) * sum_f_R0 (fun i : nat => x i * x i) n).
          2: { transitivity (sum_f_R0 (fun _ : nat => sum_f_R0 (fun j : nat => x j * x j) n) n).
               - symmetry. apply wl_sum_const.
               - apply wl_sum_ext. intros i Hi. reflexivity. }
          reflexivity.
        + transitivity (INR (S n) * sum_f_R0 (fun i => x i * x i) n
                        - 2 * (sum_f_R0 x n) * (sum_f_R0 x n)
                        + INR (S n) * sum_f_R0 (fun i => x i * x i) n).
          * apply Rplus_eq_compat_r.
            assert (HAB : sum_f_R0 (fun i => INR (S n) * (x i * x i) - 2 * (x i * sum_f_R0 x n)) n
                          = INR (S n) * sum_f_R0 (fun i => x i * x i) n
                            - 2 * (sum_f_R0 x n) * (sum_f_R0 x n)).
            { transitivity (sum_f_R0 (fun i => INR (S n) * (x i * x i)) n
                            - sum_f_R0 (fun i => 2 * (x i * sum_f_R0 x n)) n).
              - change (sum_f_R0 (fun i => INR (S n) * (x i * x i) - 2 * (x i * sum_f_R0 x n)) n
                        = sum_f_R0 (fun i => INR (S n) * (x i * x i)) n
                          + (- sum_f_R0 (fun i => 2 * (x i * sum_f_R0 x n)) n)).
                rewrite <- (wl_sum_opp (fun i0 => 2 * (x i0 * sum_f_R0 x n)) n).
                rewrite <- (wl_sum_add (fun i0 : nat => INR (S n) * (x i0 * x i0))
                                       (fun i0 => - (2 * (x i0 * sum_f_R0 x n))) n).
                apply wl_sum_ext. intros i Hi. reflexivity.
              - transitivity (INR (S n) * sum_f_R0 (fun i => x i * x i) n
                              - sum_f_R0 (fun i => 2 * (x i * sum_f_R0 x n)) n).
                + apply Rplus_eq_compat_r.
                  replace (sum_f_R0 (fun i => INR (S n) * (x i * x i)) n)
                    with (INR (S n) * sum_f_R0 (fun i => x i * x i) n) by (symmetry; apply wl_sum_scal_l).
                  reflexivity.
                + apply Rplus_eq_compat_l.
                  replace (sum_f_R0 (fun i => 2 * (x i * sum_f_R0 x n)) n)
                    with (2 * (sum_f_R0 x n) * (sum_f_R0 x n)).
                  2: { symmetry.
                       rewrite (wl_sum_scal_l 2 (fun i => x i * sum_f_R0 x n) n).
                       rewrite (wl_sum_scal_r (sum_f_R0 x n) x n). ring. }
                  reflexivity. }
            rewrite HAB. reflexivity.
          * reflexivity.
    }
    ring.
  }
  (* 0 ≤ 2(S n)Σx² − 2(Σx)² ⟹ (Σx)² ≤ (S n)Σx² *)
  rewrite HD_eq in HD.
  nra.
Qed.

(* ============ R1. 内积与 Gram 重排 ============ *)

Definition wl_dot (u : nat -> nat -> R) (i j : nat) (n : nat) : R :=
  sum_f_R0 (fun k => u i k * u j k) n.

(* Gram 平方和（i,j 于 0..A；k,l 于 0..B）：
   Σ_{i,j≤A} (Σ_{k≤B} u_ik·u_jk)² = Σ_{k,l≤B} (Σ_{i≤A} u_ik·u_il)²  *)
Lemma wl_gram_rearrange (u : nat -> nat -> R) (A B : nat) :
  sum_f_R0 (fun i => sum_f_R0 (fun j =>
    (wl_dot u i j B) * (wl_dot u i j B)) A) A
  = sum_f_R0 (fun k => sum_f_R0 (fun l =>
    (sum_f_R0 (fun i => u i k * u i l) A)
    * (sum_f_R0 (fun i => u i k * u i l) A)) B) B.
Proof.
  (* 第一段：X = Σ_{i,j}Σ_{k,l} u_ik·u_jk·u_il·u_jl（内积平方展开） *)
  transitivity (sum_f_R0 (fun i => sum_f_R0 (fun j =>
    sum_f_R0 (fun k => sum_f_R0 (fun l => u i k * u j k * u i l * u j l) B) B) A) A).
  - apply wl_sum_ext. intros i Hi.
    apply wl_sum_ext. intros j Hj.
    unfold wl_dot.
    rewrite <- (wl_sum_sq_expand (fun k => u i k * u j k) B).
    apply wl_sum_ext. intros k Hk.
    apply wl_sum_ext. intros l Hl.
    ring.
  - (* 第二段：M = Σ_{k,l} (Σ_i u_ik·u_il)·(Σ_i u_ik·u_il)（换序 + 因式分解） *)
    transitivity (sum_f_R0 (fun k => sum_f_R0 (fun l =>
      (sum_f_R0 (fun i => u i k * u i l) A)
      * (sum_f_R0 (fun i => u i k * u i l) A)) B) B).
    + (* M = M'：sum4_swap + 内层因式分解 *)
      rewrite (wl_sum4_swap A B (fun i j k l => u i k * u j k * u i l * u j l)).
      apply wl_sum_ext. intros k Hk.
      apply wl_sum_ext. intros l Hl.
      rewrite <- (wl_sum_factor (fun i => u i k * u i l) (fun j => u j k * u j l) A).
      apply wl_sum_ext. intros i Hi.
      apply wl_sum_ext. intros j Hj.
      ring.
    + reflexivity.
Qed.

(* ============ R2. 对角截断 ============ *)

(* Σ_{k,l≤n} x_kl ≥ Σ_{k≤n} x_kk（x ≥ 0） *)
Lemma wl_dsum_diag_le (x : nat -> nat -> R) (n : nat) :
  (forall k l, le k n -> le l n -> 0 <= x k l) ->
  sum_f_R0 (fun k => x k k) n
  <= sum_f_R0 (fun k => sum_f_R0 (x k) n) n.
Proof.
  intros Hx.
  apply wl_sum_le. intros k Hk.
  apply (wl_sum_ge_diag (x k) n k).
  - exact Hk.
  - intros j Hj. apply Hx; [exact Hk | exact Hj].
Qed.

(* ============ R3. 单位范数 ============ *)

(* Σ_{i≤A} Σ_{k≤B} u_ik² = M（每个向量范数平方 1，共 S A 个） *)
Lemma wl_sum_unit_norm (u : nat -> nat -> R) (A B : nat) :
  (forall j, le j A -> sum_f_R0 (fun k => u j k * u j k) B = 1) ->
  sum_f_R0 (fun i => sum_f_R0 (fun k => u i k * u i k) B) A = INR (S A).
Proof.
  intros Hunit.
  transitivity (sum_f_R0 (fun _ : nat => 1) A).
  - apply wl_sum_ext. intros i Hi.
    apply Hunit. exact Hi.
  - apply wl_sum_one.
Qed.

(* ============ R4. Gram 上界（对角 1 + 非对角 μ²） ============ *)

(* |d| ≤ μ ⟹ d² ≤ μ²（Rabs 平方单调） *)
Lemma wl_sq_le_mu_sq (d mu : R) :
  Rabs d <= mu -> d * d <= mu * mu.
Proof.
  intros Habs.
  assert (Hmu0 : 0 <= mu) by (apply (Rle_trans _ (Rabs d)); [apply Rabs_pos | exact Habs]).
  replace (d * d)%R with ((Rabs d) * (Rabs d))%R.
  - apply (Rle_trans _ (mu * Rabs d)).
    + apply Rmult_le_compat_r; [apply Rabs_pos | exact Habs].
    + apply Rmult_le_compat_l; [exact Hmu0 | exact Habs].
  - replace (Rabs d * Rabs d)%R with (Rabs (d * d))%R by apply Rabs_mult.
    apply Rabs_pos_eq. apply Rle_0_sqr.
Qed.

Lemma wl_gram_upper (u : nat -> nat -> R) (M N : nat) (mu : R) :
  (lt N M) ->
  (forall j, lt j M -> sum_f_R0 (fun k => u j k * u j k) (Nat.pred N) = 1) ->
  (forall i j, lt i M -> lt j M -> i <> j ->
    Rabs (wl_dot u i j (Nat.pred N)) <= mu) ->
  sum_f_R0 (fun i => sum_f_R0 (fun j =>
    (wl_dot u i j (Nat.pred N)) * (wl_dot u i j (Nat.pred N))) (Nat.pred M)) (Nat.pred M)
  <= INR M + INR M * INR (M - 1) * (mu * mu).
Proof.
  intros HN Hunit Hcoh.
  (* 逐 i：Σ_j ⟨u_i,u_j⟩² ≤ 1 + (M−1)μ² *)
  assert (Hrow : forall i, lt i M ->
    sum_f_R0 (fun j => (wl_dot u i j (Nat.pred N)) * (wl_dot u i j (Nat.pred N))) (Nat.pred M)
    <= 1 + INR (M - 1) * (mu * mu)).
  { intros i Hi.
    (* 上界函数 b j = if j=?i then 1 else μ² *)
    apply (Rle_trans _ (sum_f_R0 (fun j => if Nat.eqb j i then 1 else mu * mu) (Nat.pred M))).
    - (* 逐项：⟨u_i,u_j⟩² ≤ b j *)
      apply wl_sum_le. intros j Hj.
      destruct (Nat.eqb_spec j i) as [Hji | Hji].
      + subst. simpl.
        (* ⟨u_i,u_i⟩² = 1：单位范数 *)
        unfold wl_dot.
        replace ((sum_f_R0 (fun k : nat => u i k * u i k) (Nat.pred N))
                 * (sum_f_R0 (fun k : nat => u i k * u i k) (Nat.pred N)))%R
          with 1%R.
        * reflexivity.
        * rewrite (Hunit i Hi). ring.
      + simpl.
        (* ⟨u_i,u_j⟩² ≤ μ²：由 |⟨⟩| ≤ μ（Rabs 平方单调，无需 0 ≤ ⟨⟩） *)
        assert (Habs : Rabs (wl_dot u i j (Nat.pred N)) <= mu).
        { apply Hcoh.
          - exact Hi.
          - lia.
          - intro Hij. apply Hji. symmetry. exact Hij. }
        assert (Hmu0 : 0 <= mu).
        { apply (Rle_trans _ (Rabs (wl_dot u i j (Nat.pred N)))); [apply Rabs_pos | exact Habs]. }
        assert (Hsq := wl_sq_le_mu_sq (wl_dot u i j (Nat.pred N)) mu Habs).
        exact Hsq.
    - (* Σ_j b j = 1 + (M−1)μ²（拆 i 项：1 + μ²·非对角项数） *)
      replace (sum_f_R0 (fun j => if Nat.eqb j i then 1 else mu * mu) (Nat.pred M))
        with (sum_f_R0 (fun j =>
                (if Nat.eqb j i then 0 else mu * mu) + (if Nat.eqb j i then 1 else 0)) (Nat.pred M)).
      2: { apply wl_sum_ext. intros j0 Hj0.
           destruct (Nat.eqb_spec j0 i); simpl; ring. }
      (* Σ_j [(if 0 else μ²)+(if 1 else 0)] = μ²·(M−1) + 1 *)
      replace (sum_f_R0 (fun j =>
              (if Nat.eqb j i then 0 else mu * mu) + (if Nat.eqb j i then 1 else 0)) (Nat.pred M))
        with (INR (M - 1) * (mu * mu) + 1).
      2: { assert (Hsplit : sum_f_R0 (fun j : nat => (if Nat.eqb j i then 0 else mu * mu) + (if Nat.eqb j i then 1 else 0)) (Nat.pred M)
                        = sum_f_R0 (fun j : nat => if Nat.eqb j i then 0 else mu * mu) (Nat.pred M)
                          + sum_f_R0 (fun j : nat => if Nat.eqb j i then 1 else 0) (Nat.pred M)).
           { exact (wl_sum_add (fun j => if Nat.eqb j i then 0 else mu * mu)
                               (fun j => if Nat.eqb j i then 1 else 0) (Nat.pred M)). }
           assert (H1 : sum_f_R0 (fun j : nat => if Nat.eqb j i then 0 else mu * mu) (Nat.pred M)
                           = (mu * mu) * INR (M - 1)).
           { transitivity (sum_f_R0 (fun j : nat => (mu * mu) * (if Nat.eqb j i then 0 else 1)) (Nat.pred M)).
             - apply wl_sum_ext. intros j Hj. destruct (Nat.eqb_spec j i); simpl; ring.
             - transitivity ((mu * mu) * sum_f_R0 (fun j : nat => if Nat.eqb j i then 0 else 1) (Nat.pred M)).
               + exact (wl_sum_scal_l (mu * mu) (fun j : nat => if Nat.eqb j i then 0 else 1) (Nat.pred M)).
               + f_equal. apply wl_count_offdiag. exact Hi. }
           assert (H2 : sum_f_R0 (fun j : nat => if Nat.eqb j i then 1 else 0) (Nat.pred M) = 1).
           { exact (wl_count_diag M i Hi). }
           rewrite Hsplit H1 H2. ring. }
      lra. }
  (* 汇总：Σ_i [1 + (M−1)μ²] = M + M(M−1)μ² *)
  apply (Rle_trans _ (sum_f_R0 (fun i => 1 + INR (M - 1) * (mu * mu)) (Nat.pred M))).
  - apply wl_sum_le. intros i Hi.
    apply Hrow. lia.
  - rewrite (wl_sum_add (fun _ => 1) (fun _ => INR (M - 1) * (mu * mu)) (Nat.pred M)).
    rewrite wl_sum_one.
    rewrite (wl_sum_const (INR (M - 1) * (mu * mu)) (Nat.pred M)).
    replace (INR (S (Nat.pred M)))%R with (INR M)%R by (f_equal; lia).
    lra.
Qed.

(* ============ R5. ★ 主定理：Welch 界 ============ *)

Theorem wl_welch_bound (M N : nat) (u : nat -> nat -> R) (mu : R) :
  (le 1 N) -> (lt N M) ->
  (forall j, lt j M -> sum_f_R0 (fun k => u j k * u j k) (Nat.pred N) = 1) ->
  (forall i j, lt i M -> lt j M -> i <> j ->
    Rabs (wl_dot u i j (Nat.pred N)) <= mu) ->
  (INR M - INR N <= INR N * INR (M - 1) * (mu * mu))%R.
Proof.
  intros HN1 HN Hunit Hcoh.
  (* Gram 平方和 G *)
  set (G := sum_f_R0 (fun i => sum_f_R0 (fun j =>
    (wl_dot u i j (Nat.pred N)) * (wl_dot u i j (Nat.pred N))) (Nat.pred M)) (Nat.pred M)).
  (* 上界：G ≤ M + M(M−1)μ² *)
  assert (HGhi : G <= INR M + INR M * INR (M - 1) * (mu * mu)).
  { unfold G. exact (wl_gram_upper u M N mu HN Hunit Hcoh). }
  (* 下界：INR N·G ≥ (INR M)² *)
  assert (HGlo : (INR M) * (INR M) <= INR N * G).
  { unfold G.
    rewrite (wl_gram_rearrange u (Nat.pred M) (Nat.pred N)).
    (* x_k := Σ_{i≤Nat.pred M} u_ik²（行向量范数平方） *)
    set (x := fun k => sum_f_R0 (fun i => u i k * u i k) (Nat.pred M)).
    (* a) 对角截断：Σ_k x_k² ≤ Σ_{k,l}(Σ_i u_ik u_il)²（= G 行向量 Gram） *)
    assert (Hdiag : sum_f_R0 (fun k => x k * x k) (Nat.pred N)
                    <= sum_f_R0 (fun k => sum_f_R0 (fun l =>
                        (sum_f_R0 (fun i => u i k * u i l) (Nat.pred M))
                        * (sum_f_R0 (fun i => u i k * u i l) (Nat.pred M))) (Nat.pred N)) (Nat.pred N)).
    { apply (wl_dsum_diag_le (fun k l => (sum_f_R0 (fun i => u i k * u i l) (Nat.pred M))
                                       * (sum_f_R0 (fun i => u i k * u i l) (Nat.pred M))) (Nat.pred N)).
      intros k l Hk Hl. apply Rle_0_sqr. }
    (* b) CS 幂平均：N·Σ_k x_k² ≥ (Σ_k x_k)²（N = S(Nat.pred N) ≥ 1） *)
    assert (Hcs : (sum_f_R0 x (Nat.pred N)) * (sum_f_R0 x (Nat.pred N))
                  <= INR N * sum_f_R0 (fun k => x k * x k) (Nat.pred N)).
    { replace (INR N)%R with (INR (S (Nat.pred N)))%R by (f_equal; lia).
      apply wl_sum_sq_ge_mean_sq. intros k Hk.
      unfold x. apply wl_sum_nonneg. intros i Hi. apply Rle_0_sqr. }
    (* c) Σ_k x_k = M（单位范数） *)
    assert (Hxsum : sum_f_R0 x (Nat.pred N) = INR M).
    { unfold x.
      rewrite (wl_sum_swap (Nat.pred N) (Nat.pred M) (fun k i => u i k * u i k)).
      transitivity (sum_f_R0 (fun i => sum_f_R0 (fun k => u i k * u i k) (Nat.pred N)) (Nat.pred M)).
      - apply wl_sum_ext. intros i Hi. apply wl_sum_ext. intros k Hk. ring.
      - assert (Hunit' : forall j : nat, le j (Nat.pred M) -> sum_f_R0 (fun k => u j k * u j k) (Nat.pred N) = 1)
          by (intros j Hj; apply Hunit; lia).
        rewrite (wl_sum_unit_norm u (Nat.pred M) (Nat.pred N) Hunit').
        replace (INR (S (Nat.pred M)))%R with (INR M)%R by (f_equal; lia).
        reflexivity. }
    (* 组装：M² ≤ N·Σx² ≤ N·G *)
    rewrite Hxsum in Hcs.
    apply (Rle_trans _ (INR N * sum_f_R0 (fun k => x k * x k) (Nat.pred N))).
    - exact Hcs.
    - apply Rmult_le_compat_l.
      + apply pos_INR.
      + exact Hdiag. }
  (* 收尾：M² ≤ N·G ≤ N·(M + M(M−1)μ²) ⟹ M(M−N) ≤ NM(M−1)μ² ⟹ M−N ≤ N(M−1)μ² *)
  assert (Hprod : (INR M) * (INR M - INR N)
                  <= INR N * INR M * INR (M - 1) * (mu * mu)).
  { assert (Hmid : (INR M) * (INR M)
                   <= INR N * (INR M + INR M * INR (M - 1) * (mu * mu))).
    { apply (Rle_trans _ (INR N * G)); [exact HGlo | ].
      apply Rmult_le_compat_l; [apply pos_INR | exact HGhi]. }
    nra. }
  assert (HMpos : 0 < INR M).
  { apply lt_0_INR. lia. }
  apply (Rmult_le_reg_l (INR M) (INR M - INR N)
         (INR N * INR (M - 1) * (mu * mu)) HMpos).
  replace (INR M * (INR N * INR (M - 1) * (mu * mu)))%R
    with (INR N * INR M * INR (M - 1) * (mu * mu))%R by ring.
  exact Hprod.
Qed.



























