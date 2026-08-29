(* ============================================================
   库: ca_tau —— τ 定理线：碰撞质量与裁剪单调性（T2a 形式化）
   ============================================================
   定位：τ 感知频率选择（论文 B / 剪枝规则逆向定理推导）的理论侧形式化。
   核心（T2a 裁剪单调，与欧拉「截断-尾部控制」同构）：
     - τ(n) = T − n：带 n 在训练窗 T 内的碰撞质量（max 0 (T−n)，subn 截断）
     - tau_tail_mass_le：Σ_{n∈F, n>N} τ(n) ≤ count·(T−N)——截断尾部碰撞质量可控
       （欧拉 zeta_tail_bound_list（Σ_{n>P} n^{-s} ≤ 1/P）的 τ 版）
     - tau_crop_mono：N1 ≤ N2 ⟹ 保留带总碰撞质量单调不减——裁剪点越大
       保留越多 ⟹ 碰撞负债越多；剪 n>N 释放的负债 = 总量 − 保留量
   红线：零 Admitted、零自定义 Axiom/Parameter；纯 mathcomp（无 CR）。
   探针：AI注意力算法\探针\zz_probe_tau_t2a.v（EXIT=0，Print Assumptions Closed）
   注：mathcomp 无 `[seq E | x <- s, P]` 记法——统一 map+filter 分开写；
       ssr elim 对 bool 目标/Type 归纳（subseq）有「No assumption」异常——
       裁剪单调直接对 F 归纳 + case: ifP 分支（绕开 subseq）。
   ============================================================ *)

From mathcomp Require Import ssreflect ssreflect.ssrbool ssreflect.ssrnat ssreflect.seq.

Local Open Scope nat_scope.

(* τ(n) = T − n（nat 截断减法 = max 0 (T−n)）：带 n 在训练窗 T 内的碰撞质量 *)
Definition tau_mass (T n : nat) : nat := T - n.

(* 逐项尾部界：n > N ⟹ τ(n) ≤ T − N
   —— @leq_sub2l T N n：N ≤ n ⟹ T−n ≤ T−N（减数大 ⟹ 差小）。 *)
Lemma tau_mass_le_crop (T N n : nat) (H : N < n) : tau_mass T n <= T - N.
Proof.
  unfold tau_mass.
  exact (@leq_sub2l T N n (ltnW H)).
Qed.

(* 通用求和界：逐项 ≤ c ⟹ Σ_{n∈F, P n} f n ≤ count P F · c（foldr 归纳） *)
Lemma sumn_map_count_le (f : nat -> nat) (F : seq nat) (P : pred nat) (c : nat)
  (H : forall n : nat, P n -> f n <= c) :
  sumn (map (fun n => f n) [seq n <- F | P n]) <= count P F * c.
Proof.
  elim: F => [|x F' IH].
  - rewrite /sumn /=. apply leqnn.
  - rewrite /sumn /map /filter /count /=.
    case: ifP => Px.
    + (* P x true：f x + Σ' ≤ (1+count')·c = c + count'·c *)
      apply (leq_trans (leq_add (H x Px) IH)).
      rewrite add1n mulSn. apply leqnn.   (* (1+count')·c = count'.+1·c = c + count'·c（mulSn） *)
    + (* P x false：Σ' ≤ (0+count')·c = count'·c（count 不增） *)
      rewrite add0n. exact IH.
Qed.

(* ★ T2a 核心：截断尾部碰撞质量可控
   Σ_{n∈F, n>N} τ(n) ≤ count (fun n => N < n) F · (T − N)
   —— 与欧拉 zeta_tail_bound_list（Σ_{n>P} n^{-s} ≤ 1/P）同构：截断尾部贡献 ≤ 可控量。 *)
Lemma tau_tail_mass_le (F : seq nat) (T N : nat) :
  sumn (map (fun n => tau_mass T n) [seq n <- F | N < n]) <=
  count (fun n => N < n) F * (T - N).
Proof.
  apply (sumn_map_count_le (tau_mass T) F (fun n => N < n) (T - N)).
  move => n Hn. exact (tau_mass_le_crop T N n Hn).
Qed.

(* ★ T2a 主引理：裁剪单调——N1 ≤ N2 ⟹ 保留带（n ≤ N）总碰撞质量单调不减
   —— 裁剪点越大保留越多 ⟹ 碰撞负债越多；剪 n>N 释放的负债 = 总量 − 保留量。
   —— 直接对 F 归纳 + case: ifP 四分支（x 是否 ≤ N1 / ≤ N2）。 *)
Lemma tau_crop_mono (F : seq nat) (T N1 N2 : nat) (H : N1 <= N2) :
  sumn (map (fun n => tau_mass T n) [seq n <- F | n <= N1]) <=
  sumn (map (fun n => tau_mass T n) [seq n <- F | n <= N2]).
Proof.
  elim: F => [|x F' IH]; rewrite /sumn /map /filter /=.
  - (* []：0 ≤ 0 *)
    apply leqnn.
  - (* x :: F'：case (x ≤ N1) 与 (x ≤ N2) *)
    case: ifP => Hx1.
    + (* x ≤ N1：x 加入 N1 侧；x ≤ N1 ≤ N2 ⟹ 也加入 N2 侧 *)
      case: ifP => Hx2.
      * (* 两侧都加 tau x：tau x + A ≤ tau x + B（IH） *)
        apply (leq_add (leqnn (tau_mass T x)) IH).
      * (* x≤N1 且 ¬(x≤N2)：矛盾（x ≤ N1 ≤ N2） *)
        exfalso. move: Hx2 => /negP Hx2'. apply Hx2'.
        apply (leq_trans Hx1 H).
    + (* ¬(x ≤ N1)：x 不在 N1 侧 *)
      case: ifP => Hx2.
      * (* x ≤ N2：x 在 N2 侧。A ≤ B ≤ tau x + B（leq_addl：B ≤ tau x + B） *)
        apply (leq_trans IH). apply leq_addl.
      * (* 两侧都不含 x：A ≤ B（IH） *)
        exact IH.
Qed.
