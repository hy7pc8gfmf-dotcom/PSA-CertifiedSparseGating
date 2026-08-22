(* ============================================================
   T2b 组合层完整化：9-箱鸽笼定理（z 工作区，E039）
   定理：任意 10 条 [3,511] 内的频率带（不必互异）必含一对
   (a,b) 使 b − a < (5/8)·√(a·b)——即 P2 触发条件
   （接 ParetoLaw.pair_bound_gt_4_5 ⟹ B > 4/5 ⟹ 检查器必拒）。
   这是 P3 主定理（m≥10 必拒，几何增长链式归纳）的**初等替代**：
   排序 + 相邻比率爆炸——纯鸽笼，不需要增长假设。

   PG1 插入排序存在性（Permutation + Sorted le）。
   PG2 adjacent_sorted / geo_chain_lower：排序链相邻有序 +
       "全部相邻比率 ≥ 9/5 ⟹ 第 10 元素 ≥ 3·(9/5)^9 > 511"
       （3·9^9 = 1162261467 > 511·5^9 = 998671875，纯 nat）。
   PG3 bounded_exists_dec：有限枚举的构造性决策。
   PG4 ten_bands_reject（主定理）：输出 P2 触发对（R 层），
       严格相邻对经 ParetoRandom.same_bin_triggers，
       重复对（a=b）单独处理（d=0 平凡触发）。
   依赖：src/ParetoRandom（same_bin_triggers，纯 Stdlib）。
   审计：Print Assumptions 尾部。
   ============================================================ *)
From Stdlib Require Import Reals.Reals.
From Stdlib Require Import micromega.Lra.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Sorting.Sorted.
From Stdlib Require Import Sorting.Permutation.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import ZArith.ZArith.
Require Import ParetoRandom.
Import ListNotations.

Open Scope R_scope.
Open Scope nat_scope.

Module PigeonTen.

(* ---------- PG1：插入排序存在性 ---------- *)

Fixpoint insert (x : nat) (l : list nat) : list nat :=
  match l with
  | [] => [x]
  | y :: t => if x <=? y then x :: (y :: t) else y :: insert x t
  end.

Fixpoint isort (l : list nat) : list nat :=
  match l with
  | [] => []
  | x :: t => insert x (isort t)
  end.

Lemma insert_perm : forall (x : nat) (l : list nat),
  Permutation (x :: l) (insert x l).
Proof.
  intros x l. induction l as [| y t IH]; simpl.
  - apply Permutation_refl.
  - destruct (x <=? y) eqn:E.
    + apply Permutation_refl.
    + apply Permutation_trans with (y :: x :: t).
      * apply perm_swap.
      * simpl. apply perm_skip. exact IH.
Qed.

Lemma isort_perm : forall l : list nat, Permutation l (isort l).
Proof.
  induction l as [| x t IH]; simpl.
  - apply Permutation_refl.
  - apply Permutation_trans with (x :: isort t).
    * apply perm_skip. exact IH.
    * apply insert_perm.
Qed.

Lemma insert_sorted : forall (l : list nat) (x : nat),
  Sorted le l -> Sorted le (insert x l).
Proof.
  induction l as [| y s IH]; intros x Hs; simpl.
  - constructor; constructor.
  - inversion Hs as [| y' s' Hs' Hyw]; subst.
    destruct (Nat.leb_spec x y) as [Hxy | Hxy].
    + (* x ≤ y：insert = x::y::s *)
      constructor; [exact Hs | apply HdRel_cons; exact Hxy].
    + (* y < x：insert = y::insert x s *)
      simpl. destruct s as [| w r].
      * constructor.
        -- constructor; constructor.
        -- apply HdRel_cons. apply Nat.lt_le_incl. exact Hxy.
      * destruct (Nat.leb_spec x w) as [Hxw | Hxw].
        -- (* x ≤ w：insert x (w::r) = x::w::r *)
           assert (Ew : ((x <=? w) = true)%bool) by (apply Nat.leb_le; exact Hxw).
           simpl. rewrite Ew. constructor.
           ++ constructor; [inversion Hs'; assumption | apply HdRel_cons; exact Hxw].
           ++ apply HdRel_cons. apply Nat.lt_le_incl. exact Hxy.
        -- (* w < x：insert x (w::r) = w::insert x r *)
           assert (Ew : ((x <=? w) = false)%bool) by (apply Nat.leb_gt; exact Hxw).
           specialize (IH x Hs'). simpl in IH. rewrite Ew in IH.
           inversion IH as [| ? ? Hs2 Hw2]; subst.
           simpl. rewrite Ew. constructor.
           ++ exact IH.
           ++ apply HdRel_cons. inversion Hyw; subst. assumption.
Qed.

Lemma isort_sorted : forall l : list nat, Sorted le (isort l).
Proof.
  induction l as [| x t IH]; simpl.
  - constructor.
  - apply insert_sorted. exact IH.
Qed.

(* ---------- PG2：排序链性质 ---------- *)

Lemma adjacent_sorted : forall (l : list nat), Sorted le l ->
  forall i, (S i < length l)%nat -> (nth i l 0 <= nth (S i) l 0)%nat.
Proof.
  induction l as [| y s IH]; intros Hs i Hi.
  - simpl in Hi. lia.
  - inversion Hs as [| y' s' Hs' Hyw]; subst.
    destruct i as [| i']; simpl.
    + destruct s as [| w r]; simpl in *; [lia | ].
      inversion Hyw; subst. assumption.
    + apply IH; [exact Hs' | simpl in Hi; lia].
Qed.

Lemma geo_key : forall (l : list nat) (k : nat),
  (k <= 9)%nat ->
  (forall i, (i < 9)%nat -> (nth i l 0 * 9 <= nth (S i) l 0 * 5)%nat) ->
  (nth 0 l 0 * 9 ^ k <= nth k l 0 * 5 ^ k)%nat.
Proof.
  intros l k. revert k. induction k as [| k IH]; intros Hk Hstep.
  - rewrite !Nat.pow_0_r. lia.
  - assert (Hk9 : (k <= 9)%nat) by lia. specialize (IH Hk9 Hstep).
    assert (Hst : (nth k l 0 * 9 <= nth (S k) l 0 * 5)%nat) by (apply Hstep; lia).
    rewrite !Nat.pow_succ_r by lia.
    apply (Nat.le_trans (nth 0 l 0 * (9 * 9 ^ k))
                        ((nth k l 0 * 5 ^ k) * 9)
                        (nth (S k) l 0 * (5 * 5 ^ k))).
    + replace (nth 0 l 0 * (9 * 9 ^ k)) with ((nth 0 l 0 * 9 ^ k) * 9)%nat by ring.
      apply Nat.mul_le_mono_r. exact IH.
    + replace ((nth k l 0 * 5 ^ k) * 9) with ((nth k l 0 * 9) * 5 ^ k)%nat by ring.
      replace (nth (S k) l 0 * (5 * 5 ^ k)) with ((nth (S k) l 0 * 5) * 5 ^ k)%nat by ring.
      apply Nat.mul_le_mono_r. exact Hst.
Qed.

Lemma geo_chain_lower : forall (l : list nat),
  (length l = 10)%nat ->
  (forall i, (i < 9)%nat -> (nth i l 0 * 9 <= nth (S i) l 0 * 5)%nat) ->
  (nth 0 l 0 * 9 ^ 9 <= nth 9 l 0 * 5 ^ 9)%nat.
Proof.
  intros l Hlen Hstep. apply (geo_key l 9). lia. exact Hstep.
Qed.

(* ---------- PG3：有限枚举构造性决策 ---------- *)

Lemma bounded_exists_dec : forall (n : nat) (P : nat -> Prop),
  (forall i, (i < n)%nat -> {P i} + {~ P i}) ->
  ({exists i, (i < n)%nat /\ P i} + {forall i, (i < n)%nat -> ~ P i})%type.
Proof.
  induction n as [| n IH]; intros P Hdec.
  - right. intros i Hi. lia.
  - destruct (Hdec n ltac:(lia)) as [Hn | Hn].
    + left. exists n. split; [lia | exact Hn].
    + assert (Hdec' : forall i, (i < n)%nat -> {P i} + {~ P i})
        by (intros i Hi; apply Hdec; lia).
      destruct (IH P Hdec') as [Hex | Hall].
      * left. destruct Hex as [i [Hi Hp]]. exists i. split; [lia | exact Hp].
      * right. intros i Hi.
        destruct (Nat.eq_dec i n) as [E | E]; [rewrite E; exact Hn | ].
        apply Hall. lia.
Qed.

(* ---------- PG4：主定理 ---------- *)

Theorem ten_bands_reject :
  forall l : list nat,
    (length l = 10)%nat ->
    (forall x, In x l -> (3 <= x <= 511)%nat) ->
    exists a b : nat,
      In a l /\ In b l /\
      ((INR b - INR a < 5 / 8 * sqrt (INR a * INR b)))%R.
Proof.
  intros l Hlen Hin.
  set (l' := isort l).
  assert (Hperm : Permutation l l') by (unfold l'; apply isort_perm).
  assert (Hsorted : Sorted le l') by (unfold l'; apply isort_sorted).
  assert (Hlen' : (length l' = 10)%nat).
  { rewrite <- (Permutation_length Hperm). exact Hlen. }
  assert (Hin' : forall x, In x l' -> (3 <= x <= 511)%nat).
  { intros x Hx. apply Hin.
    eapply Permutation_in. apply Permutation_sym. exact Hperm. exact Hx. }
  assert (Hback : forall x, In x l' -> In x l).
  { intros x Hx.
    eapply Permutation_in. apply Permutation_sym. exact Hperm. exact Hx. }
  destruct (bounded_exists_dec 9
              (fun i => (nth (S i) l' 0 * 5 < nth i l' 0 * 9)%nat)
              (fun i Hi => lt_dec (nth (S i) l' 0 * 5) (nth i l' 0 * 9)))
    as [Hex | Hall].
  - destruct Hex as [i [Hi Hlt]].
    set (a := nth i l' 0). set (b := nth (S i) l' 0).
    assert (HinA : In a l') by (unfold a; apply nth_In; lia).
    assert (HinB : In b l') by (unfold b; apply nth_In; lia).
    assert (Hmono : (a <= b)%nat)
      by (unfold a, b; apply adjacent_sorted; [exact Hsorted | lia]).
    destruct (Nat.eq_dec a b) as [Eab | Nab].
    + (* 重复对：d = 0 平凡触发 *)
      exists a. exists b. split; [apply Hback; exact HinA | split; [apply Hback; exact HinB | ]].
      replace ((INR b - INR a)%R) with 0%R by (rewrite Eab; ring).
      assert (Hap : (0 < INR a)%R) by (apply lt_0_INR; assert (H3a := Hin' a HinA); lia).
      set (X := (INR a * INR b)%R).
      assert (HX : (0 < X)%R) by (unfold X; rewrite <- Eab; nra).
      assert (Hsp : (0 < sqrt X)%R).
      { destruct (Req_dec (sqrt X) 0%R) as [Ez | Ez].
        - exfalso. assert (Hss : (sqrt X * sqrt X = X)%R)
            by (apply sqrt_sqrt; apply Rlt_le; exact HX).
          rewrite Ez in Hss. rewrite Rmult_0_l in Hss.
          rewrite <- Hss in HX. lra.
        - assert (Hz : (0 <= sqrt X)%R) by apply sqrt_pos. lra. }
      nra.
    + (* 严格相邻对：走 same_bin_triggers *)
      exists a. exists b. split; [apply Hback; exact HinA | split; [apply Hback; exact HinB | ]].
      assert (H3a : (3 <= a)%nat) by (apply Hin'; exact HinA).
      assert (H5b : (INR (5 * b) < INR (9 * a))%R) by (apply lt_INR; lia).
      rewrite !mult_INR in H5b.
      assert (H55 : (INR (5%nat) = 5)%R) by (simpl; ring).
      assert (H99 : (INR (9%nat) = 9)%R) by (simpl; ring).
      rewrite H55, H99 in H5b.
      apply (same_bin_triggers (INR a) (INR b)).
      * apply lt_0_INR. lia.
      * apply lt_INR. lia.
      * nra.
  - (* 全部相邻比率 ≥ 9/5：几何爆炸 ⟹ 第 10 元素 > 511 矛盾 *)
    exfalso.
    assert (Hstep : forall i, (i < 9)%nat -> (nth i l' 0 * 9 <= nth (S i) l' 0 * 5)%nat).
    { intros i Hi. specialize (Hall i Hi). lia. }
    pose proof (geo_chain_lower l' Hlen' Hstep) as Hgeo.
    assert (Hx0 : (3 <= nth 0 l' 0)%nat) by (apply Hin'; apply nth_In; lia).
    assert (Hx9 : (nth 9 l' 0 <= 511)%nat) by (apply Hin'; apply nth_In; lia).
    (* Z 层收口（nat 大字面量 vm_compute/lia 栈溢出，Z 二进制无碍） *)
    pose proof (proj1 (Nat2Z.inj_le _ _) Hgeo) as HZ1.
    rewrite !Nat2Z.inj_mul, !Nat2Z.inj_pow in HZ1.
    set (v0 := nth 0 l' 0). set (v9 := nth 9 l' 0).
    assert (Hz0 : (3 <= Z.of_nat v0)%Z) by lia.
    assert (Hz9 : (Z.of_nat v9 <= 511)%Z) by lia.
    lia.
Qed.

End PigeonTen.

Print Assumptions PigeonTen.ten_bands_reject.
