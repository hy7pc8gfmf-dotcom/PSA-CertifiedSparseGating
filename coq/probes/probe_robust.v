(* ============================================================
   U6 T-ROBUST 容错 Gershgorin（z 工作区，E039；2026-08-22 第二批 ⑤）
   动机：检查器太二元——好族全过、坏族全拒。容错版：
   坏对占比 ≤ δ 的族获得"分级证书"：
     行和 ≤ INR n · (mu + δ)
   即干净相干界 mu 上加 δ 加权罚项。激活考古热点
   ca_decay.v:228 sparse_subset_exists_with_tolerance_corrected
   （δN² 容错坏对存在性定理）的下游 Gershgorin 半边。

   RR1 list_sum_R 基础件（与 probe_kerneldrift 同款自包含复制）。
   RR2 sum_split_bound：布尔划分计数求和界（归纳主引擎）。
   RR3 robust_gershgorin（主定理）：
     全核 |K_ij| ≤ 1、好对 |K_ij| ≤ mu、坏对每行 ≤ δ·n 个
     ⟹ 每行绝对行和 ≤ INR n·(mu+δ)。
   RR4 robust_certificate（分级证书系）：
     mu + δ ≤ 4/5 ⟹ 行和 ≤ INR n·4/5
     ——P2 帕累托阈值的容错通道：干净界不达标但 mu+δ 达标
     的族仍可获证书（回应"检查器太二元"）。
   审计：Print Assumptions 尾部（预期 ≤ Dedekind 两件）。
   ============================================================ *)
Require Import Stdlib.Reals.Reals.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.micromega.Lra.
Import ListNotations.

Open Scope R_scope.
Open Scope nat_scope.

Module RobustGershgorin.

(* ---------- RR1：list_sum_R 基础件 ---------- *)

Fixpoint list_sum_R (f : nat -> R) (l : list nat) : R :=
  match l with
  | nil => 0%R
  | h :: t => (f h + list_sum_R f t)%R
  end.

Lemma list_sum_R_le (f g : nat -> R) (l : list nat) :
  (forall i, In i l -> (f i <= g i)%R) -> ((list_sum_R f l) <= (list_sum_R g l))%R.
Proof.
  intros H. induction l as [| h t IH]; simpl.
  - apply Rle_refl.
  - apply Rplus_le_compat.
    + apply H. left. reflexivity.
    + apply IH. intros i Hi. apply H. right. exact Hi.
Qed.

(* INR 逐 successor 展开（INR 不计算，见教训 20） *)
Lemma INR_S (k : nat) : (INR (S k) = 1 + INR k)%R.
Proof.
  destruct k as [|k1]; simpl; ring.
Qed.

Lemma length_cons_inr (l : list nat) (x : nat) :
  (INR (length (x :: l)) = 1 + INR (length l))%R.
Proof.
  cbn [length]. apply INR_S.
Qed.

(* ---------- RR2：布尔划分计数求和界（主引擎） ---------- *)
(* 好项（g j = false）各 ≤ m、坏项各 ≤ b ⟹ 总和按各自计数分账：
   sum ≤ m·#good + b·#bad ——好项走 negb 过滤计数，坏项走 g 过滤计数。 *)

Lemma filter_negb_length_le (g : nat -> bool) (l : list nat) :
  ((length (filter (fun x => negb (g x)) l)) <= (length l))%nat.
Proof.
  induction l as [| h t IH]; simpl; [lia | ].
  destruct (g h); simpl; lia.
Qed.

Lemma sum_split_bound (f : nat -> R) (g : nat -> bool) (l : list nat) (b m : R) :
  (forall j, In j l -> (g j = false)%bool -> (f j <= m)%R) ->
  (forall j, In j l -> (f j <= b)%R) ->
  ((list_sum_R f l)
   <= (m * INR (length (filter (fun x => negb (g x)) l))
       + b * INR (length (filter g l))))%R.
Proof.
  intros Hgood Hbad. induction l as [| h t IH].
  - cbn [list_sum_R filter length].
    assert (INR0 : (INR 0 = 0)%R) by reflexivity.
    rewrite INR0. rewrite Rmult_0_r, Rmult_0_r. lra.
  - assert (IH' : ((list_sum_R f t)
      <= (m * INR (length (filter (fun x => negb (g x)) t))
          + b * INR (length (filter g t))))%R).
    { apply IH.
      - intros j Hj Hg. apply Hgood; [right; exact Hj | exact Hg].
      - intros j Hj. apply Hbad. right. exact Hj. }
    cbn [list_sum_R].
    destruct (g h) eqn:Egh.
    + (* h 是坏项：f h ≤ b；好计数不变，坏计数 +1 *)
      cbn [filter length].
      rewrite Egh.
      cbn [filter length negb].
      rewrite INR_S.
      apply (Rle_trans _ (b + (m * INR (length (filter (fun x => negb (g x)) t))
                               + b * INR (length (filter g t))))%R).
      * assert (Hfh : (f h <= b)%R) by (apply Hbad; left; reflexivity).
        apply Rplus_le_compat; [exact Hfh | exact IH'].
      * (* 代数：b + X ≤ X_bad 计数版（ring 等式） *)
        apply Req_le. ring.
    + (* h 是好项：f h ≤ m；好计数 +1，坏计数不变 *)
      cbn [filter length].
      rewrite Egh.
      cbn [filter length negb].
      rewrite INR_S.
      apply (Rle_trans _ (m + (m * INR (length (filter (fun x => negb (g x)) t))
                           + b * INR (length (filter g t))))%R).
      * assert (Hfh : (f h <= m)%R) by (apply Hgood; [left; reflexivity | exact Egh]).
        apply Rplus_le_compat; [exact Hfh | exact IH'].
      * apply Req_le. ring.
Qed.

(* ---------- RR3：容错 Gershgorin 主定理 ---------- *)

Theorem robust_gershgorin (K : nat -> nat -> R) (bad : nat -> nat -> bool)
          (n : nat) (mu delta : R) :
  (0 < n)%nat -> (0 <= mu)%R ->
  (forall i j, (i < n)%nat -> (j < n)%nat -> ((Rabs (K i j)) <= 1)%R) ->
  (forall i j, (i < n)%nat -> (j < n)%nat -> ((bad i j) = false)%bool -> ((Rabs (K i j)) <= mu)%R) ->
  (forall i, (i < n)%nat ->
     ((INR (length (filter (fun j => bad i j) (seq 0 n)))) <= (delta * INR n))%R) ->
  (forall i, (i < n)%nat ->
     ((list_sum_R (fun j => Rabs (K i j)) (seq 0 n)) <= (INR n * (mu + delta)))%R).
Proof.
  intros Hn Hmu Hone Hgood Hbadc i Hi.
  (* In j (seq 0 n) ⟹ j < n 的共用侧条件 *)
  assert (Hin : forall j, In j (seq 0 n) -> (j < n)%nat).
  { intros j Hj.
    destruct (In_nth (seq 0 n) j 0%nat Hj) as [k [Hk Hkth]].
    rewrite length_seq in Hk.
    assert (Hkseq : (nth k (seq 0 n) 0%nat = k)%nat)
      by (rewrite (@seq_nth n 0%nat k 0%nat Hk); lia).
    rewrite Hkth in Hkseq. lia. }
  assert (Hgn : ((INR (length (filter (fun x => negb (bad i x)) (seq 0 n)))) <= (INR n))%R).
  { apply le_INR.
    apply (Nat.le_trans _ (length (seq 0 n))).
    - apply filter_negb_length_le.
    - rewrite length_seq. lia. }
  apply (Rle_trans _ ((mu * INR (length (filter (fun x => negb (bad i x)) (seq 0 n))))
                      + (1 * INR (length (filter (fun j => bad i j) (seq 0 n)))))%R).
  - apply sum_split_bound.
    + intros j Hj Hg. apply Hgood; [exact Hi | apply Hin; exact Hj | exact Hg].
    + intros j Hj. apply Hone; [exact Hi | apply Hin; exact Hj].
  - (* mu·#good + 1·#bad ≤ mu·n + delta·n = INR n·(mu+delta) *)
    assert (Hbc := Hbadc i Hi).
    apply (Rle_trans _ ((mu * INR n) + (delta * INR n))%R).
    + apply Rplus_le_compat.
      * apply Rmult_le_compat_l; [exact Hmu | exact Hgn].
      * rewrite Rmult_1_l. exact Hbc.
    + apply Req_le. ring.
Qed.

(* ---------- RR4：分级证书系（P2 帕累托阈值通道） ---------- *)

Corollary robust_certificate (K : nat -> nat -> R) (bad : nat -> nat -> bool)
          (n : nat) (mu delta : R) :
  (0 < n)%nat -> (0 <= mu)%R -> (0 <= delta)%R -> ((mu + delta) <= (4 / 5))%R ->
  (forall i j, (i < n)%nat -> (j < n)%nat -> ((Rabs (K i j)) <= 1)%R) ->
  (forall i j, (i < n)%nat -> (j < n)%nat -> ((bad i j) = false)%bool -> ((Rabs (K i j)) <= mu)%R) ->
  (forall i, (i < n)%nat ->
     ((INR (length (filter (fun j => bad i j) (seq 0 n)))) <= (delta * INR n))%R) ->
  (forall i, (i < n)%nat ->
     ((list_sum_R (fun j => Rabs (K i j)) (seq 0 n)) <= (INR n * (4 / 5)))%R).
Proof.
  intros Hn Hmu Hdelta Hsum Hone Hgood Hbadc i Hi.
  apply (Rle_trans _ (INR n * (mu + delta))%R).
  - apply (robust_gershgorin K bad n mu delta); assumption.
  - apply Rmult_le_compat_l; [rewrite <- INR_0; apply le_INR; lia | exact Hsum].
Qed.

End RobustGershgorin.

Print Assumptions RobustGershgorin.sum_split_bound.
Print Assumptions RobustGershgorin.robust_gershgorin.
Print Assumptions RobustGershgorin.robust_certificate.
