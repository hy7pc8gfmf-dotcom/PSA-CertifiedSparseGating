(* ============================================================
   probe_pareto_qtw.v —— C2：Pareto 碰撞/无碰撞界定理构造性孪生
   PSA/PSA-GSA z 区构造性轨道 · C 系列（2026-09-02）
   ============================================================

   使命（交接文档 §4 队列首 C2）：把主线库 src/ParetoRandom.v（R 层
   经典、依赖 ParetoLaw.v 的 √281）中的碰撞触发引擎与生日-箱无碰撞
   界实现为全 Q/nat 化的纯构造性孪生：零 Reals 零 sqrt 零经典。

   母库定理 → Q 层孪生对应表：
     sqrt281_gt_167_10 (167/10 < √281)  ↦ 假设 QleT s281_lo s
       （s281_lo := 167/10；上夹界 s281_hi := 84/5 为本孪生新增，
         16.8² = 282.24 > 281 为真界；√281 由 s²==281 (QeqT) + 夹界
         三件假设共同刻画，sqrt 不引入——铁律 5）
     ratio_lt_c (9/5 < c_pareto)        ↦ par_c_ratio_lt
       （c_q s := (153+5s)·(1/128) = r_hi 的 Q 化；除法全改乘字面量
         逆元——E251 坑①）
     （母库无，本孪生新增）              ↦ par_c_sandwich
       （上下夹逼链：9/5 < c_q s ≤ 237/128 = c_q s281_hi，And-of-Set）
     c_lt_triggers（开方收口
       n'−n < (5/8)√(nn')）             ↦ par_c_lt_triggers
       （√ 不引入：结论停在平方形式
         QltT (64(n'−n)²) (25·n·n')，即母库证明第 4 步 Hsq；
         因式分解 r_hi·r_lo = 1 需要 s² = 281，故带 QeqT (s*s) 281）
     same_bin_triggers                  ↦ par_same_bin_quad
       （9/5 比率版合成：ratio_lt + c_lt 链）
     fall9 : nat -> nat                 ↦ fall9q : nat -> Q
       （因子 (9−m)%nat 经 qnat 注入 Q；二进制 Z 免母库 nat 一元
         大数栈溢出——数值可真算，母库只能绕行显式分数）
     no_collision                       ↦ no_collision_q (Q 除法形态)
     div_le                             ↦ par_div_leT（field 证 Qeq 侧条件）
     no_collision_decreasing            ↦ par_nc_decreasing（QleT 结论）
     no_collision_le                    ↦ par_nc_le
     prob_collision7_ge / prob_collision8_ge ↦ par_prob7 / par_prob8
       （真数值：fall9q 7 == 181440、pow9q 7 == 4782969 可 kernel 计算）
     prob_mono                          ↦ par_prob_mono
     鸽笼 m ≥ 10 确定性（母库仅注释）    ↦ par_fall10_zero（截断减法归零）

   铁律对齐：① Require 链仅 QArith/Qabs/Lia/Lqa/Extraction/PeanoNat +
   qset_twin_base（不显式导入 Setoid/Morphisms——E258 坑②）；
   ② 核心结论全 Set 层（QltT/QleT/QeqT/And/sigT，零 Prop 结论）；
   ③ 非平凡核心定理：par_c_lt_triggers（二次触发引擎，含 s²=281 残差
   项消去装配）、par_nc_decreasing（交叉相乘单调性）、par_nc_le；
   ④ 终态零 Admitted 零 Axiom；⑤ 存在性件 par_ratio_gap 用 sigT 且
   Defined（可提取）。

   装配纪律（E258 八坑对照）：Qle/Qlt 目标上 Qeq 同一化一律
   setoid_replace（绝不裸 rewrite Qeq 引理）；QleT 目标上 QeqT 同一化
   一律 qtw_leT_congr_l/r + QeqT_of_Qeq；Qle 链显式 Qle_trans/
   Qmult_le_compat 系；lra 只喂 Qle/Qlt 前提（Qeq 前提先降级）；
   And := prod（split/fst/snd）。
   ============================================================ *)
Require Import Stdlib.QArith.QArith.
Require Import Stdlib.QArith.Qabs.
From Stdlib Require Import Lia.
From Stdlib Require Import Lqa.
From Stdlib Require Import Extraction.
From Stdlib Require Import PeanoNat.
Require Import qset_twin_base.

(* E138① 记号防御注册（合并环境 mathcomp 前序劫持覆盖；独立环境同义覆盖仅 warning） *)
Notation "x + y" := (Nat.add x y) : nat_scope.
Notation "x - y" := (Nat.sub x y) : nat_scope.
Notation "x * y" := (Nat.mul x y) : nat_scope.
Notation "x <= y" := (Peano.le x y) : nat_scope.
Notation "x < y" := (Peano.lt x y) : nat_scope.
(* Q 字面量 # 记号防御（mathcomp ssrnotations 的全局前缀 #[ x ] 会干扰
   Q_scope 中缀 # 的解析——合并模拟实测语法错，重注册恢复；记号声明
   照抄 QArith_base L41） *)
Notation "x # y" := (Qmake x y) (at level 55, no associativity) : Q_scope.

Local Open Scope Q_scope.

(* ############ §0 √281 有理夹界层（sqrt 不引入——铁律 5） ############ *)

(* √281 下夹界：母库 ParetoLaw.sqrt281_gt_167_10 : 167/10 < √281 *)
Definition s281_lo : Q := (167 # 10)%Q.

(* √281 上夹界：本孪生新增字面量（84/5 = 16.8，16.8² = 282.24 > 281） *)
Definition s281_hi : Q := (84 # 5)%Q.

(* r_hi = (153+5√281)/128 = c_pareto 的 Q 化（除法改乘字面量逆元——E251①） *)
Definition c_q (s : Q) : Q := (153 + 5 * s) * (1 # 128)%Q.

(* r_lo = (153−5√281)/128 的 Q 化 *)
Definition r_lo_q (s : Q) : Q := (153 - 5 * s) * (1 # 128)%Q.

(* ############ §A 比率夹逼链（母库 ratio_lt_c 孪生 + 新增夹逼链） ############ *)

(* 母库 ratio_lt_c：9/5 < c_pareto（经 √281 > 167/10）。
   孪生：s 带下夹界 ⟹ 9/5 < c_q s。c_q(lo) = 473/256 ≈ 1.8477，
   margin = 61/1280 > 0——QleT 弱假设即得严格结论。 *)
Theorem par_c_ratio_lt (s : Q) (Hlo : QleT s281_lo s) : QltT (9 # 5)%Q (c_q s).
Proof.
  apply Qlt_to_QltT.
  assert (HloLe : s281_lo <= s) by (apply QleT_to_Qle; exact Hlo).
  unfold c_q, s281_lo in *.
  lra.
Qed.

(* 新增：上下夹逼链（夹界层头牌）。c_q(lo) = 473/256 < 9/5 侧严格
   （margin 61/1280），c_q(hi) = 237/128 侧非严格。结论全 Set 层。 *)
Theorem par_c_sandwich (s : Q) (Hlo : QleT s281_lo s) (Hhi : QleT s s281_hi) :
  And (QltT (9 # 5)%Q (c_q s)) (QleT (c_q s) (237 # 128)%Q).
Proof.
  split.
  - apply (par_c_ratio_lt s Hlo).
  - apply Qle_to_QleT.
    assert (HhiLe : s <= s281_hi) by (apply QleT_to_Qle; exact Hhi).
    unfold c_q, s281_hi in *.
    lra.
Qed.

(* ★ sigT 数据件（铁律 2：存在性 sigT 打包且 Defined 可提取）：
   9/5 到 c_q s 的正 gap 见证 d := c_q s − 9/5（margin 证书对） *)
Definition par_ratio_gap (s : Q) (Hlo : QleT s281_lo s)
  : sigT (fun d : Q => And (QltT 0%Q d) (QleT ((9 # 5)%Q + d) (c_q s))).
Proof.
  exists ((c_q s - (9 # 5))%Q).
  split.
  - apply Qlt_to_QltT.
    assert (HloLe : s281_lo <= s) by (apply QleT_to_Qle; exact Hlo).
    unfold c_q, s281_lo in *.
    lra.
  - right. apply QeqT_of_Qeq. ring.
Defined.

(* ############ §B 同箱触发引擎（母库 c_lt_triggers / same_bin_triggers） ############ *)

(* ★ 核心定理（母库 c_lt_triggers 孪生，平方收口形态）：
   n < n' < c_q s · n，s 带 s²==281 与下夹界
   ⟹ 64·(n'−n)² < 25·n·n'
   （母库再开方得 n'−n < (5/8)√(nn')；Q 层 √ 不引入，结论停在此，
     与母库证明第 4 步 Hsq 逐字对应）。
   装配：A := n'−c_q s·n < 0；B := n'−r_lo_q s·n > 0（r_lo < 1 部分）；
   A·B < 0 ⟹ 64·A·B < 0；64·A·B == 64n'²−153nn'+64n² + R，
   R := (25/256)·(281−s²)·n² ≥ 0（此处用 s²==281 消残差）；
   故 64n'²−153nn'+64n² < 0 ⟺ 64(n'−n)² < 25nn'。 *)
Theorem par_c_lt_triggers (s n n1 : Q)
  (Hss : QeqT (s * s) (281 # 1)%Q)
  (Hlo : QleT s281_lo s)
  (Hn : QltT 0%Q n) (Hnn : QltT n n1)
  (Hc : QltT n1 (c_q s * n)) :
  QltT (64 * (n1 - n) * (n1 - n)) (25 * (n * n1)).
Proof.
  apply Qlt_to_QltT.
  assert (HssEq : s * s == (281 # 1)%Q) by (apply QeqT_to_Qeq; exact Hss).
  assert (HloLe : s281_lo <= s) by (apply QleT_to_Qle; exact Hlo).
  assert (HnPos : 0 < n) by (apply QltT_to_Qlt; exact Hn).
  assert (HnnLt : n < n1) by (apply QltT_to_Qlt; exact Hnn).
  assert (HcLt : n1 < c_q s * n) by (apply QltT_to_Qlt; exact Hc).
  (* 1) A := n' − c_q s·n < 0（线性） *)
  assert (HA : n1 - c_q s * n < 0) by lra.
  (* 2) B := n' − r_lo_q s·n > 0：B == (n'−n) + 5(s−5)·(1/128)·n，
        第二项 > 0 由 s > 167/10 > 5 与 n > 0（乘法一步用 compat 引理） *)
  assert (Hs5 : 0 < s - 5).
  { unfold s281_lo in HloLe. lra. }
  assert (Hk5 : 0 < 5 * (s - 5) * (1 # 128)%Q) by lra.
  assert (Hk : 0 < 5 * (s - 5) * (1 # 128)%Q * n).
  { apply (Qmult_lt_0_compat (5 * (s - 5) * (1 # 128)%Q) n).
    - exact Hk5.
    - exact HnPos. }
  assert (HB : 0 < n1 - r_lo_q s * n).
  { setoid_replace (n1 - r_lo_q s * n)
      with ((n1 - n) + 5 * (s - 5) * (1 # 128)%Q * n)
      by (unfold r_lo_q; ring).
    lra. }
  (* 3) A·B < 0（负×正） *)
  assert (HAB : (n1 - c_q s * n) * (n1 - r_lo_q s * n) < 0).
  { assert (Hstep : (n1 - c_q s * n) * (n1 - r_lo_q s * n)
                    < 0 * (n1 - r_lo_q s * n)).
    { apply (Qmult_lt_compat_r (n1 - c_q s * n) 0 (n1 - r_lo_q s * n)).
      - exact HB.
      - exact HA. }
    setoid_replace (0 * (n1 - r_lo_q s * n)) with 0%Q in Hstep by ring.
    exact Hstep. }
  (* 4) ×64 仍 < 0 *)
  assert (H64 : 64 * ((n1 - c_q s * n) * (n1 - r_lo_q s * n)) < 0).
  { assert (H1 : (n1 - c_q s * n) * (n1 - r_lo_q s * n) * 64 < 0 * 64).
    { apply (Qmult_lt_compat_r _ _ 64).
      - lra.
      - exact HAB. }
    setoid_replace (0 * 64) with 0%Q in H1 by ring.
    setoid_replace ((n1 - c_q s * n) * (n1 - r_lo_q s * n) * 64)
      with (64 * ((n1 - c_q s * n) * (n1 - r_lo_q s * n))) in H1 by ring.
    exact H1. }
  (* 5) 残差项 R = (25/256)·(281−s²)·n² ≥ 0（s²==281 消入） *)
  assert (Hres : 0 <= (25 * (1 # 256)%Q) * (((281 # 1)%Q - s * s) * (n * n))).
  { apply Qmult_le_0_compat.
    - lra.
    - apply Qmult_le_0_compat.
      + assert (Hge : (281 # 1)%Q <= s * s)
          by (rewrite <- HssEq; apply Qle_refl).
        lra.
      + apply QleT_to_Qle. apply (Qsqr_nonnegT n). }
  (* 6) 64·A·B == 二次式 + R；R ≥ 0 ⟹ 二次式 < 0 ⟺ 目标 *)
  setoid_replace (64 * ((n1 - c_q s * n) * (n1 - r_lo_q s * n)))
    with (64 * n1 * n1 - 153 * (n * n1) + 64 * n * n
          + (25 * (1 # 256)%Q) * ((281 # 1)%Q - s * s) * (n * n)) in H64
    by (unfold c_q, r_lo_q; ring).
  setoid_replace (64 * (n1 - n) * (n1 - n))
    with (64 * n1 * n1 - 128 * (n * n1) + 64 * n * n) by ring.
  lra.
Qed.

(* ★ 核心定理（母库 same_bin_triggers 孪生，9/5 比率版合成）：
   n < n' < (9/5)·n ⟹ 64·(n'−n)² < 25·n·n'
   （链：9/5·n < c_q s·n 〔par_c_ratio_lt + 乘正右单调〕⟹ c_lt） *)
Theorem par_same_bin_quad (s n n1 : Q)
  (Hss : QeqT (s * s) (281 # 1)%Q)
  (Hlo : QleT s281_lo s)
  (Hn : QltT 0%Q n) (Hnn : QltT n n1)
  (Hratio : QltT n1 ((9 # 5)%Q * n)) :
  QltT (64 * (n1 - n) * (n1 - n)) (25 * (n * n1)).
Proof.
  apply (par_c_lt_triggers s n n1 Hss Hlo Hn Hnn).
  apply (QltT_trans n1 ((9 # 5)%Q * n) (c_q s * n) Hratio).
  apply (Qmult_ltT_compat_r (9 # 5)%Q (c_q s) n).
  - exact Hn.
  - apply (par_c_ratio_lt s Hlo).
Qed.

(* ############ §C 生日-箱无碰撞界（母库 fall9 / no_collision 骨架） ############ *)

(* nat → Q 注入（二进制，免母库 nat 一元大数栈溢出） *)
Definition qnat (i : nat) : Q := (Z.of_nat i # 1)%Q.

(* (9)_m：下降阶乘，fall9q 0 = 1，fall9q (S m) = qnat(9−m)·fall9q m
   （因子用 nat 截断减法，忠实母库 fall9：m ≥ 10 时因子为 0） *)
Fixpoint fall9q (m : nat) : Q :=
  match m with
  | O => (1 # 1)%Q
  | S m1 => qnat (9 - m1)%nat * fall9q m1
  end.

(* 9^m（Q 形态） *)
Fixpoint pow9q (m : nat) : Q :=
  match m with
  | O => (1 # 1)%Q
  | S m1 => (9 # 1)%Q * pow9q m1
  end.

(* 无碰撞概率：(9)_m / 9^m *)
Definition no_collision_q (m : nat) : Q := fall9q m / pow9q m.

(* 母库 fall9_succ / pow_succ_9 孪生（定义性） *)
Lemma par_fall9_succ (m : nat) : fall9q (S m) == qnat (9 - m)%nat * fall9q m.
Proof. reflexivity. Qed.

Lemma par_pow9_succ (m : nat) : pow9q (S m) == (9 # 1)%Q * pow9q m.
Proof. reflexivity. Qed.

(* qnat 单调桥（nat ≤ → Qle；lia 管截断减法） *)
Lemma par_qnat_le (a b : nat) (Hab : (a <= b)%nat) : Qle (qnat a) (qnat b).
Proof.
  assert (HZ : (Z.of_nat a <= Z.of_nat b)%Z) by lia.
  unfold qnat, Qle. cbn [Qnum Qden]. repeat rewrite Zmult_1_r. exact HZ.
Qed.

(* 截断减法因子恒 ≤ 9 *)
Lemma par_qnat_le9 (m : nat) : QleT (qnat (9 - m)%nat) (9 # 1)%Q.
Proof. apply Qle_to_QleT. apply (par_qnat_le (9 - m)%nat 9%nat). lia. Qed.

Lemma par_qnat_nonnegT (i : nat) : QleT 0 (qnat i).
Proof.
  apply Qle_to_QleT.
  assert (HZ : (0 <= Z.of_nat i)%Z) by lia.
  unfold qnat, Qle. cbn [Qnum Qden]. repeat rewrite Zmult_1_r. exact HZ.
Qed.

Lemma par_pos9 : QltT 0 (9 # 1)%Q.
Proof. apply Qlt_to_QltT. lra. Qed.

(* 母库 pow9_pos 孪生 *)
Lemma par_pow9_posT (m : nat) : QltT 0 (pow9q m).
Proof.
  induction m as [| m IH].
  - apply Qlt_to_QltT. cbn [pow9q]. lra.
  - apply Qlt_to_QltT. apply (Qmult_lt_0_compat (9 # 1)%Q (pow9q m)).
    + apply QltT_to_Qlt. exact par_pos9.
    + apply QltT_to_Qlt. exact IH.
Qed.

(* fall9q ≥ 0（因子与归纳均非负） *)
Lemma par_fall9q_nonnegT (m : nat) : QleT 0 (fall9q m).
Proof.
  induction m as [| m IH].
  - left. apply Qlt_to_QltT. cbn [fall9q]. lra.
  - apply Qmult_leT_0_compat.
    + apply par_qnat_nonnegT.
    + exact IH.
Qed.

(* 母库 div_le 孪生（正分母分数比较，交叉相乘；field 证 Qeq 同一化） *)
Lemma par_div_leT (a b c d : Q)
  (Ha : QleT 0 a) (Hb : QltT 0 b) (Hd : QltT 0 d)
  (H : QleT (a * d) (c * b)) :
  QleT (a / b) (c / d).
Proof.
  apply Qle_to_QleT.
  apply (Qmult_lt_0_le_reg_r (a / b) (c / d) (b * d)).
  - apply (Qmult_lt_0_compat b d).
    + exact (QltT_to_Qlt 0 b Hb).
    + exact (QltT_to_Qlt 0 d Hd).
  - assert (E1 : (a / b) * (b * d) == a * d).
    { field. intro Heq.
      assert (HbLt : Qlt 0 b) by (apply QltT_to_Qlt; exact Hb).
      rewrite Heq in HbLt. apply (Qlt_irrefl 0). exact HbLt. }
    assert (E2 : (c / d) * (b * d) == c * b).
    { field. intro Heq.
      assert (HdLt : Qlt 0 d) by (apply QltT_to_Qlt; exact Hd).
      rewrite Heq in HdLt. apply (Qlt_irrefl 0). exact HdLt. }
    setoid_replace ((a / b) * (b * d)) with (a * d) by exact E1.
    setoid_replace ((c / d) * (b * d)) with (c * b) by exact E2.
    apply QleT_to_Qle. exact H.
Qed.

(* ★ 核心定理（母库 no_collision_decreasing 孪生）：
   无碰撞概率随带数增加不增——no_collision_q (S m) ≤ no_collision_q m *)
Theorem par_nc_decreasing (m : nat) :
  QleT (no_collision_q (S m)) (no_collision_q m).
Proof.
  unfold no_collision_q. cbn [fall9q pow9q].
  apply (par_div_leT (qnat (9 - m)%nat * fall9q m)
                     ((9 # 1)%Q * pow9q m) (fall9q m) (pow9q m)).
  - apply Qmult_leT_0_compat.
    + apply par_qnat_nonnegT.
    + apply par_fall9q_nonnegT.
  - apply Qlt_to_QltT. apply (Qmult_lt_0_compat (9 # 1)%Q (pow9q m)).
    + apply QltT_to_Qlt. exact par_pos9.
    + apply QltT_to_Qlt. exact (par_pow9_posT m).
  - apply Qlt_to_QltT. apply QltT_to_Qlt. exact (par_pow9_posT m).
  - (* (c·f)·p ≤ f·(9·p)：c ≤ 9 乘 (f·p) ≥ 0，两次 congr 对齐环形 *)
    apply (qtw_leT_congr_l
            (qnat (9 - m)%nat * (fall9q m * pow9q m))
            (fall9q m * ((9 # 1)%Q * pow9q m))
            (qnat (9 - m)%nat * fall9q m * pow9q m)).
    + apply (qtw_leT_congr_r
              (qnat (9 - m)%nat * (fall9q m * pow9q m))
              ((9 # 1)%Q * (fall9q m * pow9q m))
              (fall9q m * ((9 # 1)%Q * pow9q m))).
      * apply (Qmult_leT_compat_r (qnat (9 - m)%nat) (9 # 1)%Q
                 (fall9q m * pow9q m)).
        -- apply Qmult_leT_0_compat.
           ++ apply par_fall9q_nonnegT.
           ++ left. exact (par_pow9_posT m).
        -- apply par_qnat_le9.
      * apply QeqT_of_Qeq. ring.
    + apply QeqT_of_Qeq. ring.
Qed.

(* 母库 no_collision_le 孪生：m ≤ n ⟹ no_collision_q n ≤ no_collision_q m *)
Theorem par_nc_le (m n : nat) (Hmn : (m <= n)%nat) :
  QleT (no_collision_q n) (no_collision_q m).
Proof.
  (* binder 形式陈述在 Rocq 9 下 Proof 开始即已在 context（C1 同款，禁重复
     intros）；le 证据是 Prop 不能消去到 Set 结论——对 nat 归纳，
     依赖 n 的 Hmn 由 induction 自动 generalize，le 用 lia 重建 *)
  induction n as [| n IH].
  - assert (Hm0 : m = 0%nat) by lia. subst m. apply QleT_refl.
  - destruct (Nat.eq_dec m (S n)) as [He | Hne].
    + rewrite He. apply QleT_refl.
    + assert (Hmn2 : (m <= n)%nat) by lia.
      apply (QleT_trans (no_collision_q (S n)) (no_collision_q n)
               (no_collision_q m)).
      * apply par_nc_decreasing.
      * apply IH. exact Hmn2.
Qed.

(* 鸽笼确定性孪生（母库注释「m ≥ 10 ⟹ 确定性」）：截断减法归零 *)
Theorem par_fall10_zero : forall k : nat, QeqT (fall9q (10 + k)%nat) 0%Q.
Proof.
  intros k. induction k as [| k IH].
  - apply QeqT_of_Qeq. vm_compute. reflexivity.
  - apply QeqT_of_Qeq.
    replace (10 + S k)%nat with (S (10 + k))%nat by lia.
    cbn [fall9q].
    assert (Hik : fall9q (10 + k)%nat == 0%Q)
      by (apply QeqT_to_Qeq; exact IH).
    rewrite Hik. ring.
Qed.

(* 数值件（母库只能绕行显式分数；Q 层 kernel 直算） *)
Lemma par_nc7_val : QeqT (no_collision_q 7) (181440 # 4782969)%Q.
Proof. apply QeqT_of_Qeq. reflexivity. Qed.

Lemma par_nc8_val : QeqT (no_collision_q 8) (362880 # 43046721)%Q.
Proof. apply QeqT_of_Qeq. reflexivity. Qed.

(* 母库 prob_collision7_ge 孪生：P(存在同箱对) ≥ 96/100（m=7） *)
Theorem par_prob7 : QleT (96 # 100)%Q (1 - no_collision_q 7)%Q.
Proof.
  left. apply Qlt_to_QltT.
  assert (Hv : no_collision_q 7 == (181440 # 4782969)%Q)
    by (apply QeqT_to_Qeq; exact par_nc7_val).
  setoid_replace (no_collision_q 7) with (181440 # 4782969)%Q by exact Hv.
  lra.
Qed.

(* 母库 prob_collision8_ge 孪生：P(存在同箱对) ≥ 99/100（m=8） *)
Theorem par_prob8 : QleT (99 # 100)%Q (1 - no_collision_q 8)%Q.
Proof.
  left. apply Qlt_to_QltT.
  assert (Hv : no_collision_q 8 == (362880 # 43046721)%Q)
    by (apply QeqT_to_Qeq; exact par_nc8_val).
  setoid_replace (no_collision_q 8) with (362880 # 43046721)%Q by exact Hv.
  lra.
Qed.

(* 母库 prob_mono 孪生：1 − (9)_7/9^7 ≤ 1 − (9)_8/9^8 *)
Theorem par_prob_mono : QleT (1 - no_collision_q 7)%Q (1 - no_collision_q 8)%Q.
Proof.
  left. apply Qlt_to_QltT.
  assert (Hv7 : no_collision_q 7 == (181440 # 4782969)%Q)
    by (apply QeqT_to_Qeq; exact par_nc7_val).
  assert (Hv8 : no_collision_q 8 == (362880 # 43046721)%Q)
    by (apply QeqT_to_Qeq; exact par_nc8_val).
  setoid_replace (no_collision_q 7) with (181440 # 4782969)%Q by exact Hv7.
  setoid_replace (no_collision_q 8) with (362880 # 43046721)%Q by exact Hv8.
  lra.
Qed.

(* ############ §D 可执行冒烟实例 ############ *)

(* 下夹界点的 gap 数值：c_q(s281_lo) − 9/5 = 473/256 − 9/5 = 61/1280 *)
Definition par_smoke_gap : Q := c_q s281_lo - (9 # 5)%Q.
Definition par_smoke_gap_ok : bool :=
  Qeq_bool par_smoke_gap (61 # 1280)%Q.

(* 数值冒烟：无碰撞概率值对 + 概率界 *)
Definition par_smoke_nc : bool :=
  andb (Qeq_bool (no_collision_q 7) (181440 # 4782969)%Q)
       (Qeq_bool (no_collision_q 8) (362880 # 43046721)%Q).

Definition prt_qleb (x y : Q) : bool :=
  match Qcompare x y with
  | Eq => true
  | Lt => true
  | Gt => false
  end.

Definition par_smoke_prob : bool :=
  andb (prt_qleb (96 # 100)%Q (1 - no_collision_q 7)%Q)
       (prt_qleb (99 # 100)%Q (1 - no_collision_q 8)%Q).

(* Set 层证书数据（可提取）：单调性实例化 m=7 + gap 见证实例化 s := lo *)
Definition par_smoke_dec_cert : QleT (no_collision_q 8) (no_collision_q 7) :=
  par_nc_decreasing 7.

Definition par_smoke_gap_cert :
  sigT (fun d : Q => And (QltT 0%Q d) (QleT ((9 # 5)%Q + d) (c_q s281_lo))) :=
  par_ratio_gap s281_lo (QleT_refl s281_lo).

(* ############ §E 提取与审计 ############ *)

Extraction "pareto_qtw.ml" par_c_sandwich par_ratio_gap par_same_bin_quad
  par_nc_decreasing par_nc_le par_fall10_zero par_nc7_val par_prob7
  par_prob8 par_prob_mono par_smoke_dec_cert par_smoke_gap_cert
  par_smoke_gap par_smoke_gap_ok par_smoke_nc par_smoke_prob.

Print Assumptions par_fall9_succ.
Print Assumptions par_pow9_succ.
Print Assumptions par_qnat_le.
Print Assumptions par_qnat_le9.
Print Assumptions par_qnat_nonnegT.
Print Assumptions par_pos9.
Print Assumptions par_pow9_posT.
Print Assumptions par_fall9q_nonnegT.
Print Assumptions par_div_leT.
Print Assumptions par_nc_decreasing.
Print Assumptions par_nc_le.
Print Assumptions par_fall10_zero.
Print Assumptions par_nc7_val.
Print Assumptions par_nc8_val.
Print Assumptions par_prob7.
Print Assumptions par_prob8.
Print Assumptions par_prob_mono.
Print Assumptions par_c_ratio_lt.
Print Assumptions par_c_sandwich.
Print Assumptions par_ratio_gap.
Print Assumptions par_c_lt_triggers.
Print Assumptions par_same_bin_quad.
Print Assumptions par_smoke_dec_cert.
Print Assumptions par_smoke_gap_cert.
Print Assumptions par_smoke_gap_ok.
Print Assumptions par_smoke_nc.
Print Assumptions par_smoke_prob.
