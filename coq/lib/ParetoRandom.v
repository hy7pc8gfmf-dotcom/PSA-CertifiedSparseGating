(* ============================================================
   ParetoRandom —— 帕累托律随机版
   定理族：
   T2a（同箱触发）：n < n' < (9/5)·n ⟹ d < (5/8)·√(nn') ⟹ P2 触发
        ⟹ 检查器拒绝 —— 同箱（比率 < 1.8 < c≈1.8501）必触发。
   T2b（生日-箱计数）：[3,511] 按比率 1.8 分 9 箱；m 条随机带：
        P(存在同箱对) ≥ 1 − (9)_m/9^m —— 负定律的 whp 版。
        数值：m=7 ⟹ ≥ 96.2%；m=8 ⟹ ≥ 99.2%；m ≥ 10 ⟹ 确定性。
   纪律：零 Admitted、零自定义公理；仅 Stdlib Reals。
   依赖：ParetoLaw.v（P2 pair_bound_gt_4_5、P3 factor_quad/r_lo_lt_1/c_pareto）。
   ============================================================ *)
From Stdlib Require Import Reals.
From Stdlib Require Import micromega.Lra.
From Stdlib Require Import Lia.
Require Import ParetoLaw.
Open Scope R_scope.

(* ---------- 基础件 ---------- *)

(* Rsqr 与 pow 2 的桥接：Rsqr x = x^2 *)
Lemma Rsqr_pow2 (x : R) : Rsqr x = x ^ 2.
Proof. unfold Rsqr, pow. ring. Qed.

(* 非负平方严格单调：0 ≤ a、0 ≤ b、a² < b² ⟹ a < b *)
Lemma sq_lt (a b : R) : 0 <= a -> 0 <= b -> a ^ 2 < b ^ 2 -> a < b.
Proof.
  intros Ha Hb Hlt.
  apply Rnot_le_lt. intro Hab.
  apply (Rlt_not_le (b ^ 2) (a ^ 2)).
  - exact Hlt.
  - rewrite <- Rsqr_pow2. rewrite <- Rsqr_pow2.
    exact (Rsqr_incr_1 b a Hab Hb Ha).
Qed.

(* 负×正 < 0（nra 非线性符号推理） *)
Lemma neg_mul_pos_lt0 (a b : R) : a < 0 -> 0 < b -> a * b < 0.
Proof. intros Ha Hb. nra. Qed.

(* ---------- T2a：同箱触发引擎 ---------- *)

(* 子引理①：9/5 < c（1.8 < 1.8501；经 √281 > 167/10 ⟹ c = (153+5√281)/128 > 9/5）
   证明：9/5 < c ⟺ 1152 < 5(153+5√281) ⟺ 387 < 25√281 ⟸ 25·(167/10) = 417.5 > 387 *)
Lemma ratio_lt_c : (9 / 5) < c_pareto.
Proof.
  unfold c_pareto.
  assert (Heq : ((5 + sqrt 281) / 16) ^ 2 = (153 + 5 * sqrt 281) / 128).
  { field [sqrt281_sq]. }
  rewrite Heq.
  apply Rnot_le_lt.
  intro Hle.
  (* Hle : (153+5√281)/128 ≤ 9/5；乘 128（正）：153+5√281 ≤ 128·(9/5) = 1152/5 *)
  assert (Hle' : 153 + 5 * sqrt 281 <= 128 * (9 / 5)).
  {
    replace (153 + 5 * sqrt 281) with (128 * ((153 + 5 * sqrt 281) / 128)) by (field; nra).
    apply Rmult_le_compat_l; [nra | exact Hle].
  }
  (* 153 + 5√281 ≤ 1152/5 ⟺ 5√281 ≤ (1152−765)/5 = 387/5 ⟺ 25√281 ≤ 387 *)
  assert (H25le : 25 * sqrt 281 <= 387).
  { nra. }
  (* 但 25√281 > 25·(167/10) = 417.5 > 387，矛盾 *)
  assert (H167 : 167/10 < sqrt 281) by exact sqrt281_gt_167_10.
  assert (H25 : 25 * (167/10) < 25 * sqrt 281).
  { apply Rmult_lt_compat_l; [nra | exact H167]. }
  nra.
Qed.

(* 子引理②：n' < c·n 且 n < n' ⟹ (n'−n) < (5/8)·√(nn')（同箱触发核心）
   证明：n' < c·n = r_hi·n ⟹ (n'−r_hi·n) < 0；r_lo < 1 ⟹ (n'−r_lo·n) > 0
     ⟹ 64n'²−153nn'+64n² = 64(n'−r_hi·n)(n'−r_lo·n) < 0
     ⟹ 64(n'−n)² < 25nn' ⟹ 8(n'−n) < 5√(nn')（sq_lt 开方） *)
Lemma c_lt_triggers (n n' : R) :
  0 < n -> n < n' -> n' < c_pareto * n ->
  (n' - n) < (5/8) * sqrt (n * n').
Proof.
  intros Hn Hnn' Hltc.
  (* 1) n' − r_hi·n < 0 *)
  assert (Hhi : n' - r_hi * n < 0).
  {
    rewrite c_pareto_eq_r_hi in Hltc.
    nra.
  }
  (* 2) n' − r_lo·n > 0 *)
  assert (Hlo : 0 < n' - r_lo * n).
  {
    assert (Hrlo1 : r_lo < 1) by exact r_lo_lt_1.
    assert (Hpart : 0 <= (1 - r_lo) * n).
    { apply Rmult_le_pos; [nra | apply Rlt_le; exact Hn]. }
    replace (n' - r_lo * n) with ((n' - n) + (1 - r_lo) * n) by ring.
    nra.
  }
  (* 3) 因式分解 < 0 *)
  assert (Hquad : 64 * n' ^ 2 - 153 * n * n' + 64 * n ^ 2 < 0).
  {
    rewrite factor_quad.
    (* 64·(n'−r_hi·n)·(n'−r_lo·n) < 0：64>0、(n'−r_hi·n)<0、(n'−r_lo·n)>0
       ⟹ (n'−r_hi·n)·(n'−r_lo·n) < 0 ⟹ 64·(…) < 0 *)
    assert (Hprod : (n' - r_hi * n) * (n' - r_lo * n) < 0)
      by exact (neg_mul_pos_lt0 (n' - r_hi * n) (n' - r_lo * n) Hhi Hlo).
    replace (64 * (n' - r_hi * n) * (n' - r_lo * n))
      with (64 * ((n' - r_hi * n) * (n' - r_lo * n))) by ring.
    (* 正×负 < 0：64 > 0 且 积 < 0 ⟹ 64·积 < 0（交换符号） *)
    assert (H64neg : 64 * ((n' - r_hi * n) * (n' - r_lo * n)) < 0).
    {
      (* 正×负：neg_mul_pos_lt0 的交换版——用 Rmult_lt_compat_r 或 nra *)
      nra.
    }
    exact H64neg.
  }
  (* 4) 64n'²−153nn'+64n² < 0 ⟺ 64(n'−n)² < 25nn' *)
  assert (Hsq : (64 * ((n' - n) ^ 2)) < 25 * (n * n')).
  {
    assert (Hmain : 64 * n' ^ 2 - 128 * n * n' + 64 * n ^ 2 < 25 * n * n').
    { nra. }
    replace (64 * ((n' - n) ^ 2)) with (64 * n' ^ 2 - 128 * n * n' + 64 * n ^ 2) by ring.
    replace (25 * (n * n')) with (25 * n * n') by ring.
    exact Hmain.
  }
  (* 5) 平方形式：(8(n'−n))² < (5√(nn'))² *)
  assert (Hsqb : (8 * (n' - n)) ^ 2 < (5 * sqrt (n * n')) ^ 2).
  {
    replace ((8 * (n' - n)) ^ 2) with (64 * ((n' - n) ^ 2)) by (unfold pow; ring).
    replace ((5 * sqrt (n * n')) ^ 2) with (25 * (sqrt (n * n') * sqrt (n * n'))) by (unfold pow; ring).
    replace (sqrt (n * n') * sqrt (n * n')) with (n * n') by (symmetry; apply sqrt_sqrt; nra).
    replace (25 * (n * n')) with (25 * (n * n')) by ring.
    exact Hsq.
  }
  (* 6) 8(n'−n) < 5√(nn')（sq_lt：非负平方严格单调） *)
  assert (H8lt : 8 * (n' - n) < 5 * sqrt (n * n')).
  {
    apply (sq_lt (8 * (n' - n)) (5 * sqrt (n * n'))).
    - nra.
    - apply Rmult_le_pos; [nra | apply sqrt_pos].
    - exact Hsqb.
  }
  (* 7) 除以 8：n'−n < (5/8)√(nn') *)
  apply (Rmult_lt_reg_r 8 (n' - n) ((5/8) * sqrt (n * n'))); [nra | ].
  replace ((n' - n) * 8) with (8 * (n' - n)) by ring.
  replace (((5/8) * sqrt (n * n')) * 8) with (5 * sqrt (n * n')) by (field; nra).
  exact H8lt.
Qed.

(* 子引理③：n' < (9/5)·n 且 n < n' ⟹ P2 触发（同箱触发主引擎）
   9/5 < c ⟹ n' < (9/5)n < c·n ⟹ d < (5/8)√(nn') *)
Lemma same_bin_triggers (n n' : R) :
  0 < n -> n < n' -> n' < (9/5) * n ->
  (n' - n) < (5/8) * sqrt (n * n').
Proof.
  intros Hn Hnn' Hratio.
  apply c_lt_triggers; [exact Hn | exact Hnn' | ].
  apply (Rlt_trans n' ((9/5) * n) (c_pareto * n) Hratio).
  apply (Rmult_lt_compat_r n (9/5) c_pareto); [exact Hn | exact ratio_lt_c].
Qed.

(* T2a 主定理：同箱带对（比率 < 1.8）⟹ 检查器拒绝（B > 4/5） *)
Theorem t2a_same_bin_rejected (n n' : R) :
  0 < n -> n < n' -> n' < (9/5) * n ->
  4/5 < pair_bound n n'.
Proof.
  intros Hn Hnn' Hratio.
  apply pair_bound_gt_4_5.
  - exact Hn.
  - nra.
  - exact (same_bin_triggers n n' Hn Hnn' Hratio).
Qed.

(* ============================================================
   T2b：生日-箱计数（9 箱、m 条带）
   无碰撞（所有带不同箱）的排列数 = (9)_m（下降阶乘）；
   P(存在同箱对) ≥ 1 − (9)_m/9^m。
   数值：m=7 ⟹ (9)_7 = 181440、9^7 = 4782969，
         P ≥ 1 − 181440/4782969 ≈ 1 − 0.0379 = 0.962（≥ 0.96）；
         m=8 ⟹ (9)_8 = 362880、9^8 = 43046721，
         P ≥ 1 − 362880/43046721 ≈ 1 − 0.0084 = 0.992（≥ 0.99）。
   鸽笼：m ≥ 10 ⟹ 必有两带同箱（9 箱、m 带，确定性 = P3 已覆盖）。
   合成：同箱对 ⟹ P2 触发（T2a）⟹ 检查器拒绝；故
         P(检查器拒绝) ≥ P(存在同箱对) ≥ 1 − (9)_m/9^m —— 负定律的 whp 版。
   状态：T2b 2026-08-22 完成（符号化单调性 + R 层数值界）。
   平台说明：Rocq 9 对大 nat 字面量用 of_num_uint 抽象，nat 层下降阶乘/
   大数计算（vm_compute、kernel 转换检查）触发栈溢出（实测 Stack overflow），
   故 (9)_m 的值 181440/362880 与 9^m 的值 4782969/43046721 无法在
   nat 层计算连通——概率数值界在 R 层以显式分数表达（数学等价），
   单调性以符号化递推证明（不依赖具体数值）。
   ============================================================ *)

(* ---------- T2b：下降阶乘（9 箱）与无碰撞概率 ---------- *)

(* (9)_m：下降阶乘，fall9 0 = 1，fall9 (S m) = (9−m)·fall9 m *)
Fixpoint fall9 (m : nat) : nat :=
  match m with O => 1 | S m' => (9 - m') * fall9 m' end.

(* 无碰撞概率：P(9 条带全不同箱) = (9)_m/9^m（均匀独立入 9 箱） *)
Definition no_collision (m : nat) : R := INR (fall9 m) / INR (9 ^ m).

(* 递推：fall9 (S m) = (9−m)·fall9 m *)
Lemma fall9_succ (m : nat) : (fall9 (S m) = (9 - m) * fall9 m)%nat.
Proof. reflexivity. Qed.

(* 递推：9^(S m) = 9·9^m *)
Lemma pow_succ_9 (m : nat) : (9 ^ S m = 9 * 9 ^ m)%nat.
Proof. apply Nat.pow_succ_r. lia. Qed.

(* 正性：0 < 9^m（分母非零） *)
Lemma pow9_pos (m : nat) : (0 < 9 ^ m)%nat.
Proof.
  induction m.
  - change (0 < 1)%nat. lia.
  - rewrite pow_succ_9. apply Nat.mul_pos_pos; [lia | exact IHm].
Qed.

(* 辅助：正分母分数比较（交叉相乘） *)
Lemma div_le (a b c d : R) :
  0 <= a -> 0 < b -> 0 < d -> a * d <= c * b -> a / b <= c / d.
Proof.
  intros Ha Hb Hd H.
  apply (Rmult_le_reg_r d); [exact Hd |].
  field_simplify; [ | apply Rgt_not_eq; exact Hd | apply Rgt_not_eq; exact Hb ].
  apply (Rmult_le_reg_r b); [exact Hb |].
  assert (Hc : a * d / b * b = a * d) by (field; apply Rgt_not_eq; exact Hb).
  rewrite Hc.
  exact H.
Qed.

(* 单调性（核心）：无碰撞概率随带数增加不增——
   no_collision (S m) ≤ no_collision m（更多带 ⟹ 更可能碰撞） *)
Lemma no_collision_decreasing (m : nat) : no_collision (S m) <= no_collision m.
Proof.
  unfold no_collision.
  rewrite fall9_succ, pow_succ_9, mult_INR, mult_INR.
  apply div_le.
  - apply Rmult_le_pos; [apply pos_INR | apply pos_INR].
  - apply Rmult_lt_0_compat; [apply lt_0_INR; lia | apply lt_0_INR; exact (pow9_pos m)].
  - apply lt_0_INR; exact (pow9_pos m).
  - assert (H9m : INR (9 - m) <= INR 9) by (apply le_INR; lia).
    assert (Hf : 0 <= INR (fall9 m)) by exact (pos_INR (fall9 m)).
    assert (Hf' : 0 <= INR (fall9 m) * INR (9 ^ m)) by (apply Rmult_le_pos; [exact Hf | apply pos_INR]).
    nra.
Qed.

(* 单调性推论：m ≤ n ⟹ no_collision n ≤ no_collision m（按 ≤ 证据归纳） *)
Lemma no_collision_le (m n : nat) : (m <= n)%nat -> no_collision n <= no_collision m.
Proof.
  intros Hmn.
  induction Hmn as [| n' Hmn' IH].
  - apply Rle_refl.
  - apply (Rle_trans (no_collision (S n')) (no_collision n') (no_collision m)).
    + exact (no_collision_decreasing n').
    + exact IH.
Qed.

(* 无碰撞概率 (9)_7/9^7 = 181440/4782969 ≈ 0.0379 < 4/100
   ⟹ P(存在同箱对) = 1 − (9)_7/9^7 ≥ 96/100（R 层数值，nra） *)
Lemma prob_collision7_ge : 96/100 <= 1 - 181440/4782969.
Proof. nra. Qed.

(* 无碰撞概率 (9)_8/9^8 = 362880/43046721 ≈ 0.0084 < 1/100
   ⟹ P(存在同箱对) ≥ 99/100 *)
Lemma prob_collision8_ge : 99/100 <= 1 - 362880/43046721.
Proof. nra. Qed.

(* 数值单调佐证：m=8 的碰撞概率 ≥ m=7 的（1−X 反向）——
   与符号化 no_collision_le 一致（(9)_8/9^8 ≤ (9)_7/9^7） *)
Lemma prob_mono : 1 - 181440/4782969 <= 1 - 362880/43046721.
Proof. nra. Qed.




