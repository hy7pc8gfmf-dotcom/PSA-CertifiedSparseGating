(* ============================================================
   定理：[3,511] 内不存在 9 元素素数阶梯（相邻比率 ≥ 37/20 < c_pareto）
   ——素数链 [3;7;13;29;59;127;251;503] 是该约束下 [3,511] 的极限（8 带）。
   PSA = Prime-Structured Attention 的"素数身份"从存在性升级为最优性。

   实现注记：素性用"无 1<d<n 的因子"（no_small_divisor，n≥2 时等价于素数）
   纯 stdlib 表述——mathcomp 的 leq 布尔重载会破坏 lia/intro 模式
   （本轮实测：chained <= 与析取 assert 在 Lra/Arith 同载时 lia 失效），
   故本探针零 mathcomp。

   LL0 贪心提升步合数封口（逐值显式除因子见证，vm_compute）。
   LL1 no_nine_band_ladder（主定理）：任意 f : nat→nat，若
       f 0..8 全素、f 0 ≥ 3、f 8 ≤ 511、20·f(i+1) ≥ 37·f i，则 False。
   证明（贪心交换论证）：逐步证 f i ≥ g_i，g = [3;7;13;29;59;113;211;397]
   为取 ⌈37g/20⌉ 上最小素数的贪心链；第 9 元素需 ≥ 735 > 511。
   注：贪心链与8 带链 [3;7;13;29;59;127;251;503] 不同（更紧：
   113/211/397 替代 127/251/503）——极限性结论与具体链选择无关。
   LL2 sqrt281_lower / c_pareto_gt：c = (153+5√281)/128 > 37/20
       （(1676/100)² = 2808976 < 2810000，compat 链自证）。
   LL3 ladder_limit_c（系）：相邻比率 ≥ c 的 9 带阶梯同样不可能。
   审计：Print Assumptions 尾部。
   ============================================================ *)
From Stdlib Require Import Lia.
From Stdlib Require Import Reals.Reals.
From Stdlib Require Import Lra.
From Stdlib Require Import Arith.Arith.

Module LadderLimit.

(* 素性（无 1<d<n 的因子；n≥2 时等价于素数） *)
Definition no_small_divisor (n : nat) : Prop :=
  forall d, (2 <= d < n)%nat -> (n mod d <> 0)%nat.

(* ---------- LL0：贪心提升步合数封口（显式除因子） ---------- *)

Lemma not_nsd_6 : ~ no_small_divisor 6.
Proof. intros H. assert (Hd := H 2 ltac:(lia)). vm_compute in Hd. lia. Qed.

Lemma not_nsd_25_28 : forall m, (25 <= m <= 28)%nat -> ~ no_small_divisor m.
Proof.
  intros m [H1 H2] H.
  destruct (Nat.eq_dec m 25) as [E | E];
    [rewrite E in H; assert (Hd := H 5 ltac:(lia)); vm_compute in Hd; lia | ].
  destruct (Nat.eq_dec m 26) as [E' | E'];
    [rewrite E' in H; assert (Hd := H 2 ltac:(lia)); vm_compute in Hd; lia | ].
  destruct (Nat.eq_dec m 27) as [E'' | E''];
    [rewrite E'' in H; assert (Hd := H 3 ltac:(lia)); vm_compute in Hd; lia | ].
  assert (Em : (m = 28)%nat) by lia. rewrite Em in H.
  assert (Hd := H 2 ltac:(lia)). vm_compute in Hd. lia.
Qed.

Lemma not_nsd_54_58 : forall m, (54 <= m <= 58)%nat -> ~ no_small_divisor m.
Proof.
  intros m [H1 H2] H.
  destruct (Nat.eq_dec m 54) as [E | E];
    [rewrite E in H; assert (Hd := H 2 ltac:(lia)); vm_compute in Hd; lia | ].
  destruct (Nat.eq_dec m 55) as [E' | E'];
    [rewrite E' in H; assert (Hd := H 5 ltac:(lia)); vm_compute in Hd; lia | ].
  destruct (Nat.eq_dec m 56) as [E'' | E''];
    [rewrite E'' in H; assert (Hd := H 2 ltac:(lia)); vm_compute in Hd; lia | ].
  destruct (Nat.eq_dec m 57) as [E3 | E3];
    [rewrite E3 in H; assert (Hd := H 3 ltac:(lia)); vm_compute in Hd; lia | ].
  assert (Em : (m = 58)%nat) by lia. rewrite Em in H.
  assert (Hd := H 2 ltac:(lia)). vm_compute in Hd. lia.
Qed.

Lemma not_nsd_110_112 : forall m, (110 <= m <= 112)%nat -> ~ no_small_divisor m.
Proof.
  intros m [H1 H2] H.
  destruct (Nat.eq_dec m 110) as [E | E];
    [rewrite E in H; assert (Hd := H 2 ltac:(lia)); vm_compute in Hd; lia | ].
  destruct (Nat.eq_dec m 111) as [E' | E'];
    [rewrite E' in H; assert (Hd := H 3 ltac:(lia)); vm_compute in Hd; lia | ].
  assert (Em : (m = 112)%nat) by lia. rewrite Em in H.
  assert (Hd := H 2 ltac:(lia)). vm_compute in Hd. lia.
Qed.

Lemma not_nsd_210 : ~ no_small_divisor 210.
Proof. intros H. assert (Hd := H 2 ltac:(lia)). vm_compute in Hd. lia. Qed.

Lemma not_nsd_391_396 : forall m, (391 <= m <= 396)%nat -> ~ no_small_divisor m.
Proof.
  intros m [H1 H2] H.
  destruct (Nat.eq_dec m 391) as [E | E];
    [rewrite E in H; assert (Hd := H 17 ltac:(lia)); vm_compute in Hd; lia | ].
  destruct (Nat.eq_dec m 392) as [E2 | E2];
    [rewrite E2 in H; assert (Hd := H 2 ltac:(lia)); vm_compute in Hd; lia | ].
  destruct (Nat.eq_dec m 393) as [E3 | E3];
    [rewrite E3 in H; assert (Hd := H 3 ltac:(lia)); vm_compute in Hd; lia | ].
  destruct (Nat.eq_dec m 394) as [E4 | E4];
    [rewrite E4 in H; assert (Hd := H 2 ltac:(lia)); vm_compute in Hd; lia | ].
  destruct (Nat.eq_dec m 395) as [E5 | E5];
    [rewrite E5 in H; assert (Hd := H 5 ltac:(lia)); vm_compute in Hd; lia | ].
  assert (Em : (m = 396)%nat) by lia. rewrite Em in H.
  assert (Hd := H 2 ltac:(lia)). vm_compute in Hd. lia.
Qed.

(* ---------- LL1：主定理——9 带不可能 ---------- *)

Theorem no_nine_band_ladder :
  forall f : nat -> nat,
    (forall i, (i < 9)%nat -> no_small_divisor (f i)) ->
    (3 <= f 0)%nat ->
    (f 8 <= 511)%nat ->
    (forall i, (i < 8)%nat -> (20 * f (S i) >= 37 * f i)%nat) ->
    False.
Proof.
  intros f Hpr Hf0 Hf8 Hr.
  (* 步 1：f1 ≥ 6，素，6 合 ⟹ f1 ≥ 7 *)
  assert (Hr0 : (20 * f 1 >= 37 * f 0)%nat) by (apply Hr; lia).
  assert (Hf1a : (f 1 >= 6)%nat) by lia.
  assert (Hf1 : (f 1 >= 7)%nat).
  { destruct (Nat.eq_dec (f 1) 6%nat) as [E | E]; [ | lia ].
    exfalso. apply (not_nsd_6). rewrite <- E. apply Hpr. lia. }
  (* 步 2：f2 ≥ ⌈259/20⌉ = 13（无间隙） *)
  assert (Hr1 : (20 * f 2 >= 37 * f 1)%nat) by (apply Hr; lia).
  assert (Hf2 : (f 2 >= 13)%nat) by lia.
  (* 步 3：f3 ≥ 25，素，[25,28] 合 ⟹ f3 ≥ 29 *)
  assert (Hr2 : (20 * f 3 >= 37 * f 2)%nat) by (apply Hr; lia).
  assert (Hf3a : (f 3 >= 25)%nat) by lia.
  assert (Hf3 : (f 3 >= 29)%nat).
  { destruct (Nat.le_gt_cases (f 3) 28) as [Hle | Hgt]; [ | lia ].
    exfalso. apply (not_nsd_25_28 (f 3) (conj Hf3a Hle)).
    apply Hpr. lia. }
  (* 步 4：f4 ≥ 54 ⟹ ≥ 59 *)
  assert (Hr3 : (20 * f 4 >= 37 * f 3)%nat) by (apply Hr; lia).
  assert (Hf4a : (f 4 >= 54)%nat) by lia.
  assert (Hf4 : (f 4 >= 59)%nat).
  { destruct (Nat.le_gt_cases (f 4) 58) as [Hle | Hgt]; [ | lia ].
    exfalso. apply (not_nsd_54_58 (f 4) (conj Hf4a Hle)).
    apply Hpr. lia. }
  (* 步 5：f5 ≥ 110 ⟹ ≥ 113 *)
  assert (Hr4 : (20 * f 5 >= 37 * f 4)%nat) by (apply Hr; lia).
  assert (Hf5a : (f 5 >= 110)%nat) by lia.
  assert (Hf5 : (f 5 >= 113)%nat).
  { destruct (Nat.le_gt_cases (f 5) 112) as [Hle | Hgt]; [ | lia ].
    exfalso. apply (not_nsd_110_112 (f 5) (conj Hf5a Hle)).
    apply Hpr. lia. }
  (* 步 6：f6 ≥ 210 ⟹ ≥ 211 *)
  assert (Hr5 : (20 * f 6 >= 37 * f 5)%nat) by (apply Hr; lia).
  assert (Hf6a : (f 6 >= 210)%nat) by lia.
  assert (Hf6 : (f 6 >= 211)%nat).
  { destruct (Nat.eq_dec (f 6) 210%nat) as [E | E]; [ | lia ].
    exfalso. apply not_nsd_210. rewrite <- E. apply Hpr. lia. }
  (* 步 7：f7 ≥ 391 ⟹ ≥ 397 *)
  assert (Hr6 : (20 * f 7 >= 37 * f 6)%nat) by (apply Hr; lia).
  assert (Hf7a : (f 7 >= 391)%nat) by lia.
  assert (Hf7 : (f 7 >= 397)%nat).
  { destruct (Nat.le_gt_cases (f 7) 396) as [Hle | Hgt]; [ | lia ].
    exfalso. apply (not_nsd_391_396 (f 7) (conj Hf7a Hle)).
    apply Hpr. lia. }
  (* 步 8：f8 ≥ ⌈14689/20⌉ = 735 > 511 *)
  assert (Hr7 : (20 * f 8 >= 37 * f 7)%nat) by (apply Hr; lia).
  assert (Hf9 : (f 8 >= 735)%nat) by lia.
  lia.
Qed.

(* ---------- LL2：c_pareto > 37/20 ---------- *)

Open Scope R_scope.

Lemma sqrt281_lower : (1676 / 100 < sqrt 281)%R.
Proof.
  set (s := sqrt 281).
  assert (Hs : (s * s = 281)%R) by (apply sqrt_sqrt; lra).
  assert (Hn : (0 <= s)%R) by apply sqrt_pos.
  destruct (Rle_or_lt s (1676 / 100)) as [Hle | Hgt]; [ | exact Hgt ].
  exfalso.
  assert (H1 : (s * s <= 1676 / 100 * s)%R)
    by (apply Rmult_le_compat_r; [lra | exact Hle]).
  assert (H2 : (1676 / 100 * s <= 1676 / 100 * (1676 / 100))%R)
    by (apply Rmult_le_compat_l; [lra | exact Hle]).
  lra.
Qed.

Lemma c_pareto_gt : (((153 + 5 * sqrt 281) / 128) > 37 / 20)%R.
Proof.
  pose proof sqrt281_lower as Hs.
  assert (Hs2 : (sqrt 281 * sqrt 281 = 281)%R) by (apply sqrt_sqrt; lra).
  nra.
Qed.

(* ---------- LL3：系——c 阈值版 9 带不可能 ---------- *)

Corollary ladder_limit_c :
  forall f : nat -> nat,
    (forall i, (i < 9)%nat -> no_small_divisor (f i)) ->
    (3 <= f 0)%nat ->
    (f 8 <= 511)%nat ->
    (forall i, (i < 8)%nat ->
       (INR (f (S i)) >= ((153 + 5 * sqrt 281) / 128) * INR (f i)))%R ->
    False.
Proof.
  intros f Hpr Hf0 Hf8 Hr.
  assert (Hall : forall j, (j <= 8)%nat -> (2 <= f j)%nat).
  { induction j as [| j IHj]; intros Hj.
    - lia.
    - assert (HRj := Hr j ltac:(lia)).
      assert (Hj8 : (j <= 8)%nat) by lia.
      specialize (IHj Hj8).
      assert (Hc := c_pareto_gt).
      assert (H2j : (2 <= INR (f j))%R).
      { assert (Hin2 : (INR (2%nat) = 2)%R) by (simpl; ring).
        rewrite <- Hin2. apply le_INR. lia. }
      assert (Hgt : (INR (f (S j)) > 37 / 20 * INR (f j))%R) by nra.
      assert (Hin3 : (INR (3%nat) = 3)%R) by (simpl; ring).
      assert (H3 : (3 < f (S j))%nat) by (apply INR_lt; rewrite Hin3; nra).
      lia. }
  apply (no_nine_band_ladder f Hpr Hf0 Hf8).
  intros i Hi.
  specialize (Hr i Hi).
  assert (Hpos : (0 < INR (f i))%R).
  { apply lt_0_INR. specialize (Hall i ltac:(lia)). lia. }
  assert (Hgt : ((153 + 5 * sqrt 281) / 128 * INR (f i) > 37 / 20 * INR (f i))%R).
  { apply Rmult_lt_compat_r; [exact Hpos | apply c_pareto_gt]. }
  assert (H20 : (20 * INR (f (S i)) > 37 * INR (f i))%R) by nra.
  assert (Hin37 : (INR (37%nat) = 37)%R) by (simpl; ring).
  assert (Hin20 : (INR (20%nat) = 20)%R) by (simpl; ring).
  assert (Hnat : (37 * f i < 20 * f (S i))%nat).
  { apply INR_lt. rewrite mult_INR, mult_INR, Hin37, Hin20. exact H20. }
  lia.
Qed.

End LadderLimit.

Print Assumptions LadderLimit.no_nine_band_ladder.
Print Assumptions LadderLimit.ladder_limit_c.
