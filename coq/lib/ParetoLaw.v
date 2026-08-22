(* ============================================================
   帕累托律模块（Pareto Law）—— 框架文档《定理框架-帕累托律与相边界》P2/P3
   状态：P2（单对触发引理）已 Qed（2026-08-21）；
         P3 几何增长引理（pair_bound_le_4_5_geometric）已 Qed（2026-08-22）；
         P3 完整主定理（pareto_law_main，鸽笼/几何增长序列）已 Qed（2026-08-22）。
   纪律：零 Admitted、零自定义公理；仅 Stdlib Reals（自包含，独立编译）。
   关联：框架文档 D:\ComplexAnalysis\Live_harness\定理框架-帕累托律与相边界-20260821.md
   定理：P2 若阶梯含一对 (n,n') 满足 d = n'-n < (5/8)·√(n·n')，
         则保守对界 B(n,n') = √(nn')/(2d) > 4/5 ⟹ 该行行和 > 4/5 ⟹ 检查器拒绝。
   定理：P3（增长引理）若相邻带 n < n' 不触发 P2（B(n,n') ≤ 4/5），
         则 n' ≥ c·n，c = ((5+√281)/16)² = (153+5√281)/128 ≈ 1.8501（几何增长）。
   定理：P3（完整主定理，鸽笼）m 个相完备带 f 0 < ... < f (m-1) ≤ N 且检查器通过
         ⟹ 3·c^(m-1) ≤ N。推论：N=511 时 m ≥ 10 个带必被检查器拒绝
         （3·c^9 ≈ 760 > 511）。
   注：nat 算术/比较按《合并友好编码规范》书写——比较 `(k+1<m)%nat`、
       nat 字面量 `f O`/`0%nat`（R_scope 打开时裸 `+`/`-`/`0` 会被解析为 R 的）。
   ============================================================ *)

From Stdlib Require Import Reals.
From Stdlib Require Import micromega.Lra.
From Stdlib Require Import Lia.
Open Scope R_scope.

(* ---------- 辅助：正数乘除法不等式 ---------- *)

Lemma lt_div_lt (r1 r2 r3 : R) : 0 < r3 -> r1 * r3 < r2 -> r1 < r2 / r3.
Proof.
  intros H3 H.
  unfold Rdiv.
  assert (Hinv : 0 < / r3) by (apply Rinv_0_lt_compat; exact H3).
  apply (Rmult_lt_compat_r (/ r3) (r1 * r3) r2 Hinv) in H.
  replace ((r1 * r3) * / r3) with r1 in H by (field; nra).
  exact H.
Qed.

(* ---------- 保守对界（window 无关，有理松弛版） ---------- *)

Definition pair_bound (n n' : R) : R := sqrt (n * n') / (2 * (n' - n)).

(* ---------- P2：单对触发引理 ---------- *)

(* B(n,n') > 4/5 当且仅当 d < (5/8)·√(nn')（d = n'-n） *)
Lemma pair_bound_gt_4_5 (n n' : R) :
  0 < n -> 0 < n' - n ->
  (n' - n) < (5/8) * sqrt (n * n') ->
  4/5 < pair_bound n n'.
Proof.
  intros Hn Hd Hlt.
  assert (Hsq : 0 < sqrt (n * n')).
  { apply sqrt_lt_R0. nra. }
  assert (H2d : 0 < 2 * (n' - n)) by nra.
  assert (Hm : (8/5) * (n' - n) < sqrt (n * n')).
  { replace (sqrt (n * n')) with ((8/5) * ((5/8) * sqrt (n * n'))) by field.
    apply Rmult_lt_compat_l; [nra | exact Hlt]. }
  unfold pair_bound.
  apply lt_div_lt; [exact H2d | ].
  replace ((4/5) * (2 * (n' - n))) with ((8/5) * (n' - n)) by field.
  exact Hm.
Qed.

(* ---------- P3：几何增长引理 ---------- *)

(* 子引理①：(√281)² = 281（乘法形式，供 field [sqrt281_sq] 作为环关系） *)
Lemma sqrt281_sq : sqrt 281 * sqrt 281 = 281.
Proof. apply sqrt_sqrt. nra. Qed.

(* 子引理②：√281 > 5（反证：√281 ≤ 5 平方得 281 ≤ 25 矛盾） *)
Lemma sqrt281_gt_5 : 5 < sqrt 281.
Proof.
  apply Rnot_le_lt.
  intro Hle.
  assert (Hsq : sqrt 281 * sqrt 281 <= 5 * 5).
  { apply (Rmult_le_compat (sqrt 281) 5 (sqrt 281) 5); [apply sqrt_pos | apply sqrt_pos | exact Hle | exact Hle]. }
  rewrite sqrt281_sq in Hsq.
  nra.
Qed.

(* 二次式两根（论文记号）：64n'² − 153nn' + 64n² = 64·(n'−r_hi·n)·(n'−r_lo·n) *)
Definition r_lo : R := (153 - 5 * sqrt 281) / 128.
Definition r_hi : R := (153 + 5 * sqrt 281) / 128.

(* 帕累托几何增长常数 c = ((5+√281)/16)² = r_hi ≈ 1.8501 *)
Definition c_pareto : R := ((5 + sqrt 281) / 16) ^ 2.

(* 子引理③：r_lo < 1（⟺ 25 < 5√281 ⟺ 5 < √281） *)
Lemma r_lo_lt_1 : r_lo < 1.
Proof.
  unfold r_lo.
  apply (Rmult_lt_reg_l 128 ((153 - 5 * sqrt 281) / 128) 1); [nra | ].
  replace (128 * ((153 - 5 * sqrt 281) / 128)) with (153 - 5 * sqrt 281) by (field; nra).
  assert (H5 : 5 < sqrt 281) by exact sqrt281_gt_5.
  nra.
Qed.

(* 子引理④：因式分解（field 以 sqrt281_sq 为环关系，避免 (√281)² 展开） *)
Lemma factor_quad (n n' : R) :
  64 * n' ^ 2 - 153 * n * n' + 64 * n ^ 2 =
  64 * (n' - r_hi * n) * (n' - r_lo * n).
Proof.
  unfold r_lo, r_hi.
  field [sqrt281_sq].
Qed.

(* 子引理⑤：c = r_hi 的闭式恒等 *)
Lemma c_pareto_eq_r_hi : c_pareto = r_hi.
Proof.
  unfold c_pareto, r_hi.
  field [sqrt281_sq].
Qed.

(* ---------- P3 主引理：几何增长 ---------- *)
(* B(n,n') ≤ 4/5（不触发 P2）且 0 < n < n' ⟹ n' ≥ c·n。
   证明路线：B ≤ 4/5 ⟹ √(nn') ≤ (8/5)(n'−n)（乘 2d>0）
     ⟹ 平方（非负）nn' ≤ (64/25)(n'−n)² ⟹ 0 ≤ 64n'²−153nn'+64n²
     ⟹ 因式分解 0 ≤ 64(n'−r_lo·n)(n'−r_hi·n)
     ⟹ (n'−r_lo·n) > 0（r_lo<1，n'>n）⟹ n'−r_hi·n ≥ 0 ⟹ n' ≥ c·n。 *)
Lemma pair_bound_le_4_5_geometric (n n' : R) :
  0 < n -> n < n' ->
  pair_bound n n' <= 4/5 ->
  c_pareto * n <= n'.
Proof.
  intros Hn Hlt Hbound.
  unfold pair_bound in Hbound.
  assert (H2d : 0 < 2 * (n' - n)) by nra.
  (* 1) √(nn') ≤ (8/5)(n'−n) *)
  assert (Hsq_le : sqrt (n * n') <= (8/5) * (n' - n)).
  {
    assert (Hmul : 2 * (n' - n) * (sqrt (n * n') / (2 * (n' - n))) <= 2 * (n' - n) * (4/5)).
    { apply Rmult_le_compat_l; [nra | exact Hbound]. }
    replace (2 * (n' - n) * (sqrt (n * n') / (2 * (n' - n)))) with (sqrt (n * n')) in Hmul by (field; nra).
    replace (2 * (n' - n) * (4/5)) with ((8/5) * (n' - n)) in Hmul by field.
    exact Hmul.
  }
  (* 2) 平方（乘法形式，避开 pow 记号与 Rsqr_incr_1 的不匹配） *)
  assert (Hnp : 0 < n') by nra.
  assert (Hnn : 0 < n * n') by (apply Rmult_lt_0_compat; [exact Hn | exact Hnp]).
  assert (Hnn0 : 0 <= n * n') by (apply Rlt_le; exact Hnn).
  assert (H8d : 0 <= (8/5) * (n' - n)) by nra.
  assert (Hsqr_mul : sqrt (n * n') * sqrt (n * n') <= ((8/5) * (n' - n)) * ((8/5) * (n' - n))).
  { apply (Rmult_le_compat (sqrt (n * n')) ((8/5) * (n' - n)) (sqrt (n * n')) ((8/5) * (n' - n)));
      [apply sqrt_pos | apply sqrt_pos | exact Hsq_le | exact Hsq_le]. }
  assert (Hsqr' : n * n' <= (64/25) * (n' - n) ^ 2).
  {
    assert (Hl : n * n' <= ((8/5) * (n' - n)) * ((8/5) * (n' - n))).
    { rewrite (sqrt_sqrt (n * n') Hnn0) in Hsqr_mul. exact Hsqr_mul. }
    replace (((8/5) * (n' - n)) * ((8/5) * (n' - n))) with ((64/25) * (n' - n) ^ 2) in Hl by field.
    exact Hl.
  }
  (* 3) 二次式 0 ≤ 64n'² − 153nn' + 64n² *)
  assert (H25 : 25 * (n * n') <= 25 * ((64/25) * ((n' - n) ^ 2))).
  { apply Rmult_le_compat_l; [nra | exact Hsqr']. }
  replace (25 * ((64/25) * ((n' - n) ^ 2))) with (64 * ((n' - n) ^ 2)) in H25 by (field; nra).
  assert (Hsub : 25 * (n * n') - 64 * ((n' - n) ^ 2) <= 0).
  { apply Rle_minus. exact H25. }
  assert (Hquad : 0 <= 64 * n' ^ 2 - 153 * n * n' + 64 * n ^ 2).
  {
    apply Ropp_le_cancel.
    replace (- (64 * n' ^ 2 - 153 * n * n' + 64 * n ^ 2)) with (25 * (n * n') - 64 * ((n' - n) ^ 2)) by ring.
    rewrite Ropp_0.
    exact Hsub.
  }
  (* 4) 因式分解：0 ≤ 64·(n'−r_lo·n)·(n'−r_hi·n) *)
  rewrite factor_quad in Hquad.
  assert (Hprod : 0 <= (n' - r_lo * n) * (n' - r_hi * n)).
  {
    apply (Rmult_le_reg_l 64 0 ((n' - r_lo * n) * (n' - r_hi * n))); [nra | ].
    rewrite Rmult_0_r.
    replace (64 * ((n' - r_lo * n) * (n' - r_hi * n))) with (64 * (n' - r_hi * n) * (n' - r_lo * n)) by ring.
    exact Hquad.
  }
  (* 5) n' − r_lo·n > 0（r_lo < 1 ⟹ (1−r_lo)·n ≥ 0，且 n'−n > 0） *)
  assert (Halo : 0 < n' - r_lo * n).
  {
    assert (Hrlo1 : r_lo < 1) by exact r_lo_lt_1.
    assert (Hpart : 0 <= (1 - r_lo) * n).
    { apply Rmult_le_pos; [nra | apply Rlt_le; exact Hn]. }
    replace (n' - r_lo * n) with ((n' - n) + (1 - r_lo) * n) by ring.
    nra.
  }
  (* 6) n' − r_hi·n ≥ 0（正因子消去） *)
  assert (Hhi : 0 <= n' - r_hi * n).
  {
    apply (Rmult_le_reg_l (n' - r_lo * n) 0 (n' - r_hi * n)); [exact Halo | ].
    rewrite Rmult_0_r.
    exact Hprod.
  }
  (* 7) 结论：c·n ≤ n'（c = r_hi） *)
  rewrite c_pareto_eq_r_hi.
  nra.
Qed.

(* ---------- P3 完整主定理（鸽笼/几何增长序列） ---------- *)

(* 辅助：c > 0（增长引理与主定理的乘子非负前提） *)
Lemma c_pareto_pos : 0 < c_pareto.
Proof.
  unfold c_pareto.
  assert (Hn : 0 < (5 + sqrt 281) / 16).
  {
    assert (Hs : 0 <= sqrt 281) by apply sqrt_pos.
    assert (Hsum : 0 < 5 + sqrt 281) by nra.
    assert (H16 : 0 < 16) by nra.
    apply (Rmult_lt_reg_l 16 0 ((5 + sqrt 281) / 16)); [exact H16 | ].
    rewrite Rmult_0_r.
    replace (16 * ((5 + sqrt 281) / 16)) with (5 + sqrt 281) by (field; nra).
    exact Hsum.
  }
  replace (((5 + sqrt 281) / 16) ^ 2) with (((5 + sqrt 281) / 16) * ((5 + sqrt 281) / 16)) by (unfold pow; ring).
  apply Rmult_lt_0_compat; [exact Hn | exact Hn].
Qed.

(* 几何增长序列：x_{k+1} ≥ c·x_k（k=0..m-2）⟹ x_{m-1} ≥ c^(m-1)·x_0 *)
Lemma geom_growth (f : nat -> R) (m : nat) :
  (forall (k : nat), (k + 1 < m)%nat -> c_pareto * f k <= f (S k)) ->
  c_pareto ^ (Nat.pred m) * f O <= f (Nat.pred m).
Proof.
  induction m as [| m' IH].
  - assert (Hp : Nat.pred 0 = 0%nat) by reflexivity.
    rewrite Hp. rewrite pow_O. rewrite Rmult_1_l. reflexivity.
  - destruct m' as [| m''].
    + assert (Hp : Nat.pred 1 = 0%nat) by reflexivity.
      rewrite Hp. rewrite pow_O. rewrite Rmult_1_l. reflexivity.
    + intros Hstep.
      assert (Hp : Nat.pred (S (S m'')) = S m'') by reflexivity.
      rewrite Hp.
      assert (Hpow : c_pareto ^ S m'' = c_pareto * c_pareto ^ m'').
      { symmetry. exact (tech_pow_Rmult c_pareto m''). }
      rewrite Hpow.
      assert (HIH : c_pareto ^ m'' * f O <= f m'').
      { apply IH. intros k Hk. apply Hstep. lia. }
      assert (Hlast : c_pareto * f m'' <= f (S m'')).
      { apply Hstep. lia. }
      rewrite Rmult_assoc.
      apply (Rle_trans (c_pareto * (c_pareto ^ m'' * f O)) (c_pareto * f m'') (f (S m''))).
      * apply Rmult_le_compat_l; [apply Rlt_le; exact c_pareto_pos | exact HIH].
      * exact Hlast.
Qed.

(* 递增序列 ⟹ 每项 ≥ 首项 *)
Lemma incr_ge_first (f : nat -> R) (m : nat) :
  (forall (k : nat), (k + 1 < m)%nat -> f k < f (S k)) ->
  forall (k : nat), (k < m)%nat -> f O <= f k.
Proof.
  intros Hinc k. induction k as [| k' IHk]; intros Hk.
  - apply Rle_refl.
  - apply (Rle_trans (f O) (f k') (f (S k'))).
    + apply IHk. lia.
    + apply Rlt_le. apply Hinc. lia.
Qed.

(* P3 完整主定理：m 个相完备带 f 0 < ... < f (m-1) ≤ N，检查器通过 ⟹ 3·c^(m-1) ≤ N *)
Theorem pareto_law_main (f : nat -> R) (m : nat) (N : R) :
  (1 <= m)%nat ->
  3 <= f O ->
  (forall (k : nat), (k + 1 < m)%nat -> f k < f (S k)) ->
  (forall (k : nat), (k + 1 < m)%nat -> pair_bound (f k) (f (S k)) <= 4/5) ->
  f (Nat.pred m) <= N ->
  3 * c_pareto ^ (Nat.pred m) <= N.
Proof.
  intros Hm Hf0 Hinc Hpass Htop.
  assert (Hg : forall (k : nat), (k + 1 < m)%nat -> c_pareto * f k <= f (S k)).
  { intros k Hk.
    apply pair_bound_le_4_5_geometric.
    - assert (Hf0pos : 0 < f O) by nra.
      assert (Hge : f O <= f k) by (apply incr_ge_first with (m := m); [exact Hinc | lia]).
      nra.
    - exact (Hinc k Hk).
    - exact (Hpass k Hk). }
  assert (Hgeom : c_pareto ^ (Nat.pred m) * f O <= f (Nat.pred m)).
  { apply geom_growth. exact Hg. }
  assert (Hpow : 0 <= c_pareto ^ (Nat.pred m)).
  { apply pow_le. apply Rlt_le. exact c_pareto_pos. }
  assert (Hprod : 3 * c_pareto ^ (Nat.pred m) <= c_pareto ^ (Nat.pred m) * f O).
  {
    rewrite Rmult_comm.
    apply (Rmult_le_compat_l (c_pareto ^ (Nat.pred m)) 3 (f O)); [exact Hpow | nra].
  }
  apply (Rle_trans (3 * c_pareto ^ (Nat.pred m)) (c_pareto ^ (Nat.pred m) * f O) N).
  - exact Hprod.
  - apply (Rle_trans (c_pareto ^ (Nat.pred m) * f O) (f (Nat.pred m)) N Hgeom Htop).
Qed.

(* ---------- P3 推论：N=511 时 m ≥ 10 必拒 ---------- *)

(* 辅助：√281 > 16.7（c 的有理下界） *)
Lemma sqrt281_gt_167_10 : 167 / 10 < sqrt 281.
Proof.
  apply Rnot_le_lt.
  intro Hle.
  assert (Hsq : sqrt 281 * sqrt 281 <= (167/10) * (167/10)).
  { apply (Rmult_le_compat (sqrt 281) (167/10) (sqrt 281) (167/10));
      [apply sqrt_pos | apply sqrt_pos | exact Hle | exact Hle]. }
  assert (H281 : 0 <= 281) by nra.
  rewrite (sqrt_sqrt 281 H281) in Hsq.
  nra.
Qed.

(* 辅助：√281 > 11（c > 1） *)
Lemma sqrt281_gt_11 : 11 < sqrt 281.
Proof.
  apply Rnot_le_lt.
  intro Hle.
  assert (Hsq : sqrt 281 * sqrt 281 <= 11 * 11).
  { apply (Rmult_le_compat (sqrt 281) 11 (sqrt 281) 11);
      [apply sqrt_pos | apply sqrt_pos | exact Hle | exact Hle]. }
  assert (H281 : 0 <= 281) by nra.
  rewrite (sqrt_sqrt 281 H281) in Hsq.
  nra.
Qed.

(* 辅助：c > 1（幂单调 c^k 随 k 不减） *)
Lemma c_gt_1 : 1 < c_pareto.
Proof.
  unfold c_pareto.
  assert (Hh : 1 < (5 + sqrt 281) / 16).
  {
    apply (Rmult_lt_reg_l 16 1 ((5 + sqrt 281) / 16)); [nra | ].
    replace (16 * 1) with 16 by ring.
    replace (16 * ((5 + sqrt 281) / 16)) with (5 + sqrt 281) by (field; nra).
    assert (H11 : 11 < sqrt 281) by exact sqrt281_gt_11.
    nra.
  }
  replace (((5 + sqrt 281) / 16) ^ 2) with (((5 + sqrt 281) / 16) * ((5 + sqrt 281) / 16)) by (unfold pow; ring).
  apply (Rlt_trans 1 (1 * ((5 + sqrt 281) / 16)) (((5 + sqrt 281) / 16) * ((5 + sqrt 281) / 16))).
  - rewrite Rmult_1_l. exact Hh.
  - apply (Rmult_lt_compat_r ((5 + sqrt 281) / 16) 1 ((5 + sqrt 281) / 16)); [nra | exact Hh].
Qed.

(* 辅助：幂严格单调（0 ≤ a < b ⟹ a^n < b^n，n ≥ 1） *)
Lemma pow_lt_compat (a b : R) (n : nat) :
  0 <= a -> a < b -> (0 < n)%nat -> a ^ n < b ^ n.
Proof.
  intros Ha Hab Hn.
  destruct n as [| n']; [lia | ].
  induction n' as [| n'' IH].
  - rewrite pow_1. rewrite pow_1. exact Hab.
  - rewrite <- (tech_pow_Rmult a (S n'')).
    rewrite <- (tech_pow_Rmult b (S n'')).
    apply (Rle_lt_trans (a * (a ^ S n'')) (b * (a ^ S n'')) (b * (b ^ S n''))).
    + apply Rmult_le_compat_r; [apply pow_le; exact Ha | apply Rlt_le; exact Hab].
    + apply (Rmult_lt_compat_l b (a ^ S n'') (b ^ S n'')); [nra | apply IH; lia].
Qed.

(* 辅助：c 的有理下界 (217/160)² < c *)
Lemma c_gt_217sq : (217 / 160) ^ 2 < c_pareto.
Proof.
  apply (pow_lt_compat (217 / 160) ((5 + sqrt 281) / 16) 2).
  - nra.
  - apply (Rmult_lt_reg_l 160 (217 / 160) ((5 + sqrt 281) / 16)); [nra | ].
    replace (160 * (217 / 160)) with 217 by field.
    replace (160 * ((5 + sqrt 281) / 16)) with (10 * (5 + sqrt 281)) by field.
    assert (H167 : 167 / 10 < sqrt 281) by exact sqrt281_gt_167_10.
    nra.
  - lia.
Qed.

(* 数值：511 < 3·c^9（c ≈ 1.8501 ⟹ 3·c^9 ≈ 760 > 511） *)
Lemma c9_gt_511 : 511 < 3 * c_pareto ^ 9.
Proof.
  assert (Hc : (217/160) ^ 2 < c_pareto) by exact c_gt_217sq.
  assert (Heq18 : (217 / 160) ^ 18 = ((217 / 160) ^ 2) ^ 9).
  {
    symmetry.
    rewrite <- (pow_mult (217 / 160) 2 9).
    reflexivity.
  }
  assert (Hpow9 : (217 / 160) ^ 18 < c_pareto ^ 9).
  {
    rewrite Heq18.
    apply (pow_lt_compat ((217 / 160) ^ 2) c_pareto 9).
    - apply pow_le. nra.
    - exact Hc.
    - lia.
  }
  assert (Hnum : 511 < 3 * (217 / 160) ^ 18).
  { vm_compute. lra. }
  apply (Rlt_trans 511 (3 * (217 / 160) ^ 18) (3 * c_pareto ^ 9) Hnum).
  apply Rmult_lt_compat_l; [nra | exact Hpow9].
Qed.

(* P3 推论：N=511 时 m ≥ 10 个相完备带，检查器通过 ⟹ 矛盾（必拒） *)
Theorem pareto_law_N511 (f : nat -> R) (m : nat) :
  (10 <= m)%nat ->
  3 <= f O ->
  (forall (k : nat), (k + 1 < m)%nat -> f k < f (S k)) ->
  (forall (k : nat), (k + 1 < m)%nat -> pair_bound (f k) (f (S k)) <= 4/5) ->
  f (Nat.pred m) <= 511 ->
  False.
Proof.
  intros Hm Hf0 Hinc Hpass Htop.
  assert (Hm1 : (1 <= m)%nat) by lia.
  assert (Hlaw := pareto_law_main f m 511 Hm1 Hf0 Hinc Hpass Htop).
  assert (Hc1 : 1 <= c_pareto) by (apply Rlt_le; exact c_gt_1).
  assert (Hpm : c_pareto ^ 9 <= c_pareto ^ (Nat.pred m)).
  { apply Rle_pow; [exact Hc1 | ]. lia. }
  assert (Hlow : 3 * c_pareto ^ 9 <= 511).
  {
    apply (Rle_trans (3 * c_pareto ^ 9) (3 * c_pareto ^ (Nat.pred m)) 511).
    - apply Rmult_le_compat_l; [nra | exact Hpm].
    - exact Hlaw.
  }
  assert (Hgt : 511 < 3 * c_pareto ^ 9) by exact c9_gt_511.
  nra.
Qed.
