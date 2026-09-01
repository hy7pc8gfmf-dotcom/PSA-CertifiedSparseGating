(* ============================================================
   #3b：检查器有效域双向刻画（充分性阈值）——probe_z3b_validregion.v
   （z 区构造性轨道，2026-09-01/02 收官——零 Admitted，Print Assumptions 全
   Closed，可提取 OCaml bench 实证；合并版分区 77）

   论文 A §5.2/§5.6.1：pareto_law_main 给必要性（检查器通过 ⟹ 几何
   增长比率 ≥ c ≈ 1.8501）；本模块给**充分性方向**——q-几何阶梯
   （n_k = n_0·q^k，实例 q = 8）**无条件通过** frame_check_instance：
   每行保守分数和 ≤ Σ e_d ≤ 4/5。与 P3 合成：假阴性只可能落在
   比率带 [c, 8) 内——「49.1% 假阴性」从经验数字升格为显式定理带。

   数学内容：
     D0 包络 e_d := 8^{⌈d/2⌉} / (2·(8^d − 1))（Q 层，n 无关）。
     D1 逐对支配 ★：pf(n_i, n_j) ≤ e_{|i−j|}——键：⌊√(n_i·n_j)⌋ ≥
        n_i·8^{⌊d/2⌋}（Nat.sqrt 单调 + 完全平方 (n_i·8^{⌊d/2⌋})²
        ≤ n_i·n_j），交叉相乘后纯 nat/Z 不等式。
     D2 尾部几何压缩 ★：e_{d+2} ≤ e_d/8（8·(8^d−1) < 8^{d+2}−1 恒真）
        + 同指标对 e_{2k+1} ≤ e_{2k} ⟹ 自 d = 9 起的尾和
        ≤ 2·8^{−4}·(8/7) = 1/1792。
     D3 头部：e_1..e_8 的 Q 精确和（vm_compute/Qle_bool 封口）。
     D4 ★★ 最终定理：n0 ≥ 2、m ≥ 1 ⟹ frame_check_instance
        (map (fun k => n0·8^k) (seq 0 m)) = true——q=8 几何阶梯
        全体通过检查器。合计数字闭环：0.5714 + 0.0635 + 0.0626 +
        0.0078 + 0.0078 + 0.001 + 0.001 + 0.000122 + 0.000558
        ≈ 0.7155 ≤ 4/5（穷余 ≈ 0.084）。

   纪律：纯 nat/Z/Q 构造性（零实数、零经典、零 Admitted 终态）；
   z3b_ 前缀防撞名（E144④）；审计块置尾（E207）；遇卡点检索
   经验卡（E208/E180/E114⑤）。
   依赖：PSA_framework（frame_check_instance/pair_num/pair_den/
   row_sum_frac/row_le_4_5/sorted_strict_aux/all_ge_2/all_pairs_ok——
   nat 层定义直接复用，c4_instance 跨探针先例）。
   ============================================================ *)
Require Import Stdlib.QArith.QArith.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Lists.List.
Require Import Stdlib.setoid_ring.ArithRing.
Import ListNotations.

Require Import PSA_framework.
Local Open Scope nat_scope.   (* 合并语境：前序分区可能 Open Z/Q scope——数字 match 模式防劫持（E227） *)
(* E190/E138① 同型注册块：前序 mathcomp 分区把 list 的 ++ 记号重声明为 ssr cat——
   本分区 list 拼接一律强制回 Datatypes.app（scoped 重声明同义无害，独立环境仅 warning） *)
Notation "x ++ y" := (Datatypes.app x y) : list_scope.

(* ============================================================
   D0：定义（envelope / pair fraction as Q / tail / budget）
   ============================================================ *)

(* nat 分数 → Q（退化容忍构造器，zfc_qmk 模式 E180；d > 0 时为精确形） *)
Definition z3b_qmk (n d : nat) : Q :=
  match Z.of_nat d with
  | Zpos p => Qmake (Z.of_nat n) p
  | _ => Qmake (Z.of_nat n) 1
  end.

(* 统一包络（E209 绕行的定型版）：E_D := 8^D / (2·(8^D − 1)·⌊√(8^D)⌋)。
   支配键：⌊√(n²·8^D)⌋ ≥ n·⌊√(8^D)⌋——奇偶距同一证明（⌊√8^D⌋ 因子
   替代旧分子系数 4/8，奇距界紧 2 倍：d=1 处 2/7 而非 4/7）。
   行和预算按双份计（行内每距 d 的左右两对各 ≤ E_d）：
   2·(E_1+…+E_8) + 4·E_9 ≈ 0.7676 ≤ 4/5（穷余 ≈ 0.032）。 *)
Definition z3b_E (D : nat) : Q :=
  z3b_qmk (8 ^ D)%nat (2 * (8 ^ D - 1) * Nat.sqrt (8 ^ D))%nat.

(* 成对索引视图：奇距 d=2t+1、偶距 d=2t+2（尾部 z3b_tail 沿用） *)
Definition z3b_e_even (t : nat) : Q := z3b_E (t + t + 2).
Definition z3b_e_odd (t : nat) : Q := z3b_E (t + t + 1).

(* 检查器逐对界（PSA_framework 的 pair_num/pair_den）的 Q 形 *)
Definition z3b_pf (n1 n2 : nat) : Q :=
  z3b_qmk (FrameCheckInstance.pair_num n1 n2) (FrameCheckInstance.pair_den n1 n2).

(* 尾部成对和：Σ_{i<t} (e_odd(4+i) + e_even(4+i))——自 d=9 起成对计数 *)
Fixpoint z3b_tail (t : nat) : Q :=
  match t with
  | 0 => 0%Q
  | S tx => z3b_tail tx + (z3b_e_odd (4 + tx) + z3b_e_even (4 + tx))%Q
  end.

(* 预算：t 对之后的剩余余项；z3b_R 0 = 1/500，逐步 /4 *)
Fixpoint z3b_R (t : nat) : Q :=
  match t with
  | 0 => Qmake 1 500
  | S tx => z3b_R tx / 4
  end.

(* q=8 几何阶梯（n_k = n0·8^k） *)
Definition z3b_bands (n0 m : nat) : list nat :=
  map (fun k : nat => (n0 * 8 ^ k)%nat) (seq 0 m).

(* ============================================================
   证明布局：包络与预算（E_le_qmk/tail_R/total_le）→ 相位拆分（left/right_le）
   → 装配（row_le）→ 分量扫描（all_rows_skipn）→ 收官（sufficiency）
   ============================================================ *)

(* P2b：sqrt 下界（完全平方 → 精确值） *)
Lemma z3b_sqrt_ge : forall x y, Nat.le (y * y) x -> Nat.le y (Nat.sqrt x).
Proof.
  intros x y H.
  rewrite <- (Nat.sqrt_square y).
  apply Nat.sqrt_le_mono. exact H.
Qed.

(* P2c：pair_den 正下界（有序对 n1 < n2、n1 ≥ 1）——Z 层证明（E209） *)
Lemma z3b_pair_den_lb : forall n1 n2, Nat.le 1 n1 -> Nat.lt n1 n2 ->
  Nat.le 2 (FrameCheckInstance.pair_den n1 n2).
Proof.
  intros n1 n2 H1 H2.
  assert (Hn2 : Nat.le n1 n2) by (apply Nat.lt_le_incl; exact H2).
  unfold FrameCheckInstance.pair_den.
  apply Nat2Z.inj_le.
  rewrite !Nat2Z.inj_mul.
  rewrite (Nat2Z.inj_sub _ _ Hn2).
  assert (H1Z : (1 <= Z.of_nat n1)%Z) by (apply (proj1 (Nat2Z.inj_le 1 n1)); exact H1).
  assert (H2Z : (Z.of_nat (S n1) <= Z.of_nat n2)%Z)
    by (apply (proj1 (Nat2Z.inj_le (S n1) n2)); exact H2).
  assert (HZ1 : (1 + Z.of_nat n1)%Z = Z.of_nat (S n1)).
  { change (Z.of_nat (S n1)) with (Z.of_nat (1 + n1)).
    rewrite Nat2Z.inj_add. reflexivity. }
  assert (Hpre : Nat.le (1 * 1) (n1 * n2)).
  { apply Nat.le_trans with (m := n1).
    - rewrite Nat.mul_1_l. exact H1.
    - apply Nat.le_trans with (m := n1 * 1).
      + rewrite Nat.mul_1_r. apply Nat.le_refl.
      + apply (Nat.mul_le_mono_l 1 n2 n1).
        apply Nat.le_trans with (m := S n1).
        * apply Nat.le_trans with (m := n1).
          -- exact H1.
          -- apply Nat.le_succ_diag_r.
        * exact H2. }
  assert (HsZ : (1 <= Z.of_nat (Nat.sqrt (n1 * n2)))%Z)
    by (apply (proj1 (Nat2Z.inj_le 1 (Nat.sqrt (n1 * n2))));
        apply z3b_sqrt_ge; exact Hpre).
  nia.
Qed.

(* ★ D1 逐对包络（E209 绕行后按偶/奇距成对；交叉相乘落 Z 层——Pass 2 填充） *)
(* Q 交叉乘桥：正分母下 Qle_bool ⟸ nat 交叉乘不等式 *)
Lemma z3b_qmk_le : forall a b c d : nat,
  Nat.lt 0 b -> Nat.lt 0 d -> Nat.le (a * d) (c * b) ->
  Qle_bool (z3b_qmk a b) (z3b_qmk c d) = true.
Proof.
  intros a b c d Hb Hd Hle.
  destruct b as [| bx]; [exfalso; exact (Nat.nle_succ_diag_l 0 Hb) |].
  destruct d as [| dx]; [exfalso; exact (Nat.nle_succ_diag_l 0 Hd) |].
  unfold z3b_qmk, Qle_bool.
  cbn [Z.of_nat Qnum Qden].
  apply Z.leb_le.
  change (Zpos (Pos.of_succ_nat bx)) with (Z.of_nat (S bx)).
  change (Zpos (Pos.of_succ_nat dx)) with (Z.of_nat (S dx)).
  rewrite <- !Nat2Z.inj_mul.
  apply (proj1 (Nat2Z.inj_le (a * S dx) (c * S bx))).
  exact Hle.
Qed.

(* —— Q 层辅助族：qmk 投影引理 / Qle 桥 / 加法单调（zfc 模式）—— *)

(* 正分母下 qmk 的分子投影 *)
Lemma z3b_qmk_num : forall a b : nat, Nat.lt 0 b ->
  Qnum (z3b_qmk a b) = Z.of_nat a.
Proof.
  intros a b Hb.
  destruct b as [| bx]; [exfalso; exact (Nat.nle_succ_diag_l 0 Hb) |].
  unfold z3b_qmk. cbn [Z.of_nat Qnum]. reflexivity.
Qed.

(* 正分母下 qmk 的分母投影（positive 规范形） *)
Lemma z3b_qmk_den : forall a b : nat, Nat.lt 0 b ->
  Qden (z3b_qmk a b) = Pos.of_succ_nat (Nat.pred b).
Proof.
  intros a b Hb.
  destruct b as [| bx]; [exfalso; exact (Nat.nle_succ_diag_l 0 Hb) |].
  unfold z3b_qmk. cbn [Z.of_nat Qden]. reflexivity.
Qed.

(* positive 规范形 ↔ Z.of_nat 桥（S n 的 defeq 展开） *)
Lemma z3b_Zpos_of : forall n : nat, Nat.lt 0 n ->
  Z.pos (Pos.of_succ_nat (Nat.pred n)) = Z.of_nat n.
Proof.
  intros n Hn.
  destruct n as [| nx]; [exfalso; exact (Nat.nle_succ_diag_l 0 Hn) |].
  cbn [Nat.pred Pos.of_succ_nat Z.of_nat]. reflexivity.
Qed.

(* Qle 版交叉乘（bool 版 + Qle_bool_imp_le 一行桥） *)
Lemma z3b_qmk_le_Q : forall a b c d : nat,
  Nat.lt 0 b -> Nat.lt 0 d -> Nat.le (a * d) (c * b) ->
  Qle (z3b_qmk a b) (z3b_qmk c d).
Proof.
  intros a b c d Hb Hd Hle.
  apply Qle_bool_imp_le.
  apply z3b_qmk_le; assumption.
Qed.

(* qmk 加法的 Qle 单调：分子和 × 目标分母 ≤ 目标分子 × 分母和（zfc：落 Z） *)
Lemma z3b_qmk_add_le : forall a b c d e f : nat,
  Nat.lt 0 b -> Nat.lt 0 d -> Nat.lt 0 f ->
  Nat.le ((a * d + c * b) * f) (e * (b * d)) ->
  Qle (z3b_qmk a b + z3b_qmk c d) (z3b_qmk e f).
Proof.
  intros a b c d e f Hb Hd Hf Hle.
  assert (Hbd : Nat.lt 0 (b * d)).
  { apply Nat.neq_0_lt_0.
    intros Hz.
    assert (H1 : Nat.le (1 * 1) (b * d))
      by (apply (Nat.mul_le_mono 1 b 1 d); assumption).
    rewrite !Nat.mul_1_l in H1.
    rewrite Hz in H1.
    exact (Nat.nle_succ_0 0 H1). }
  apply Qle_bool_imp_le.
  unfold Qle_bool, Qplus.
  cbn [Qnum Qden].
  rewrite (z3b_qmk_num a b Hb).
  rewrite (z3b_qmk_den a b Hb).
  rewrite (z3b_qmk_num c d Hd).
  rewrite (z3b_qmk_den c d Hd).
  rewrite (z3b_qmk_num e f Hf).
  rewrite (z3b_qmk_den e f Hf).
  rewrite (Pos2Z.inj_mul (Pos.of_succ_nat (Nat.pred b))
                         (Pos.of_succ_nat (Nat.pred d))).
  rewrite ?(z3b_Zpos_of b Hb).
  rewrite ?(z3b_Zpos_of d Hd).
  rewrite ?(z3b_Zpos_of f Hf).
  apply Z.leb_le.
  assert (HZ : (Z.of_nat ((a * d + c * b) * f) <= Z.of_nat (e * (b * d)))%Z)
    by (apply (proj1 (Nat2Z.inj_le ((a * d + c * b) * f) (e * (b * d))));
        exact Hle).
  rewrite Nat2Z.inj_mul in HZ.
  rewrite !Nat2Z.inj_mul in HZ.
  rewrite Nat2Z.inj_add in HZ.
  rewrite !Nat2Z.inj_mul in HZ.
  exact HZ.
Qed.

(* —— 8^D 正性辅助族（Phase C：E 步减半与 SP 预算界共用）—— *)

Lemma z3b_pow8_ge1 : forall D, Nat.le 1 (8 ^ D).
Proof.
  intros D.
  apply Nat.le_trans with (m := (8 ^ 0)%nat).
  - apply Nat.le_refl.
  - apply Nat.pow_le_mono_r.
    + intros Hc; discriminate Hc.
    + apply Nat.le_0_l.
Qed.

Lemma z3b_sqrt8_ge1 : forall D, Nat.le 1 (Nat.sqrt (8 ^ D)).
Proof.
  intros D.
  apply (proj1 (Nat.sqrt_le_square (8 ^ D) 1)).
  rewrite Nat.mul_1_l. apply z3b_pow8_ge1.
Qed.

Lemma z3b_E_den_ge1 : forall D, Nat.le 1 D ->
  Nat.le 1 (2 * (8 ^ D - 1) * Nat.sqrt (8 ^ D)).
Proof.
  intros D HD.
  assert (Hd1 : Nat.le 1 (8 ^ D - 1)).
  { rewrite Nat.sub_1_r. apply Nat.lt_le_pred.
    apply Nat.le_lt_trans with (m := D).
    - exact HD.
    - apply Nat.pow_gt_lin_r. apply Nat.leb_le. vm_compute. reflexivity. }
  apply Nat.lt_le_trans with (m := 1%nat); [apply Nat.lt_0_succ |].
  replace (2 * (8 ^ D - 1) * Nat.sqrt (8 ^ D))%nat
    with ((2 * (8 ^ D - 1)) * Nat.sqrt (8 ^ D))%nat by ring.
  apply (Nat.mul_le_mono 1 (2 * (8 ^ D - 1)) 1 (Nat.sqrt (8 ^ D))).
  - apply Nat.le_trans with (m := 2%nat).
    + apply Nat.leb_le. vm_compute. reflexivity.
    + assert (H2 : Nat.le (2 * 1) (2 * (8 ^ D - 1)))
        by (apply Nat.mul_le_mono_l; exact Hd1).
      rewrite Nat.mul_1_r in H2. exact H2.
  - apply z3b_sqrt8_ge1.
Qed.

(* sqrt 几何步：⌊√(8^{S D})⌋ ≥ 2·⌊√(8^D)⌋（(2S)² = 4S² ≤ 4·8^D ≤ 8·8^D） *)
Lemma z3b_sqrt_step : forall D, Nat.le 1 D ->
  Nat.le (2 * Nat.sqrt (8 ^ D)) (Nat.sqrt (8 ^ S D)).
Proof.
  intros D HD.
  apply (proj1 (Nat.sqrt_le_square (8 ^ S D) (2 * Nat.sqrt (8 ^ D)))).
  rewrite (Nat.pow_succ_r 8 D (Nat.le_0_l D)).
  replace ((2 * Nat.sqrt (8 ^ D)) * (2 * Nat.sqrt (8 ^ D)))%nat
    with (4 * (Nat.sqrt (8 ^ D) * Nat.sqrt (8 ^ D)))%nat by ring.
  apply Nat.le_trans with (m := (4 * 8 ^ D)%nat).
  - apply (Nat.mul_le_mono_l (Nat.sqrt (8 ^ D) * Nat.sqrt (8 ^ D)) (8 ^ D) 4).
    apply (proj2 (Nat.sqrt_le_square (8 ^ D) (Nat.sqrt (8 ^ D)))).
    apply Nat.le_refl.
  - apply (Nat.mul_le_mono_r 4 8 (8 ^ D)).
    apply Nat.leb_le. vm_compute. reflexivity.
Qed.

(* E 步减半：2·E_{D+1} ≤ E_D（尾部双份预算的递推基石）
   Z 层核心：16·(P−1)·s ≤ (8P−1)·ss ⟸ ss ≥ 2s ∧ 1 ≤ P（P := 8^D） *)Lemma z3b_E_step : forall D, Nat.le 1 D ->
  Qle (z3b_E (S D) + z3b_E (S D)) (z3b_E D).
Proof.
  intros D HD.
  assert (HdenD : Nat.lt 0 (2 * (8 ^ D - 1) * Nat.sqrt (8 ^ D)))
    by (apply Nat.lt_le_trans with (m := 1%nat);
        [apply Nat.lt_0_succ | apply z3b_E_den_ge1; exact HD]).
  assert (HdenSD : Nat.lt 0 (2 * (8 ^ S D - 1) * Nat.sqrt (8 ^ S D)))
    by (apply Nat.lt_le_trans with (m := 1%nat);
        [apply Nat.lt_0_succ | apply z3b_E_den_ge1;
         apply (proj1 (Nat.succ_le_mono 0 D)); apply Nat.le_0_l]).
  unfold z3b_E.
  apply z3b_qmk_add_le.
  - exact HdenSD.
  - exact HdenSD.
  - exact HdenD.
  - (* 交叉乘（E202：nat 手动链，弃 nia——大常数×3 原子乘积空间指数爆炸）
       LHS = 16·P·d·b，RHS = (P·b)·b（P := 8^D，d := den D，b := den(S D)）：
       两次消公共右因子（mul_le_mono_pos_r proj2）归结到
       32·(P−1) ≤ 2·(8P−1)（Z 线性封口）与 2·⌊√8^D⌋ ≤ ⌊√8^{S D}⌋（sqrt 步） *)
    assert (Hnat : Nat.le (2 * Nat.sqrt (8 ^ D)) (Nat.sqrt (8 * 8 ^ D))).
    { rewrite <- (Nat.pow_succ_r 8 D (Nat.le_0_l D)).
      apply z3b_sqrt_step. exact HD. }
    rewrite (Nat.pow_succ_r 8 D (Nat.le_0_l D)).
    replace (((8 * 8 ^ D) * (2 * (8 * 8 ^ D - 1) * Nat.sqrt (8 * 8 ^ D))
              + (8 * 8 ^ D) * (2 * (8 * 8 ^ D - 1) * Nat.sqrt (8 * 8 ^ D)))
             * (2 * (8 ^ D - 1) * Nat.sqrt (8 ^ D)))%nat
      with ((16 * (8 ^ D) * (2 * (8 ^ D - 1) * Nat.sqrt (8 ^ D)))
            * (2 * (8 * 8 ^ D - 1) * Nat.sqrt (8 * 8 ^ D)))%nat
      by ring.
    replace ((8 ^ D) * ((2 * (8 * 8 ^ D - 1) * Nat.sqrt (8 * 8 ^ D))
                        * (2 * (8 * 8 ^ D - 1) * Nat.sqrt (8 * 8 ^ D))))%nat
      with (((8 ^ D) * (2 * (8 * 8 ^ D - 1) * Nat.sqrt (8 * 8 ^ D)))
            * (2 * (8 * 8 ^ D - 1) * Nat.sqrt (8 * 8 ^ D)))%nat
      by ring.
    apply (proj1 (Nat.mul_le_mono_pos_r
                    (16 * (8 ^ D) * (2 * (8 ^ D - 1) * Nat.sqrt (8 ^ D)))
                    ((8 ^ D) * (2 * (8 * 8 ^ D - 1) * Nat.sqrt (8 * 8 ^ D)))
                    (2 * (8 * 8 ^ D - 1) * Nat.sqrt (8 * 8 ^ D))
                    HdenSD)).
    replace (16 * (8 ^ D) * (2 * (8 ^ D - 1) * Nat.sqrt (8 ^ D)))%nat
      with ((16 * (2 * (8 ^ D - 1) * Nat.sqrt (8 ^ D))) * (8 ^ D))%nat by ring.
    replace ((8 ^ D) * (2 * (8 * 8 ^ D - 1) * Nat.sqrt (8 * 8 ^ D)))%nat
      with ((2 * (8 * 8 ^ D - 1) * Nat.sqrt (8 * 8 ^ D)) * (8 ^ D))%nat by ring.
    apply (proj1 (Nat.mul_le_mono_pos_r
                    (16 * (2 * (8 ^ D - 1) * Nat.sqrt (8 ^ D)))
                    (2 * (8 * 8 ^ D - 1) * Nat.sqrt (8 * 8 ^ D))
                    (8 ^ D)
                    (z3b_pow8_ge1 D))).
    apply Nat.le_trans with
      (m := ((2 * (8 * 8 ^ D - 1)) * (2 * Nat.sqrt (8 ^ D)))%nat).
    + replace (16 * (2 * (8 ^ D - 1) * Nat.sqrt (8 ^ D)))%nat
        with ((16 * (8 ^ D - 1)) * (2 * Nat.sqrt (8 ^ D)))%nat by ring.
      assert (H02 : Nat.lt 0 (2 * Nat.sqrt (8 ^ D))).
      { apply Nat.lt_le_trans with (m := 2%nat).
        - apply Nat.leb_le. vm_compute. reflexivity.
        - apply (Nat.mul_le_mono_l 1 (Nat.sqrt (8 ^ D)) 2).
          apply z3b_sqrt8_ge1. }
      apply (proj1 (Nat.mul_le_mono_pos_r
                      (16 * (8 ^ D - 1))
                      (2 * (8 * 8 ^ D - 1))
                      (2 * Nat.sqrt (8 ^ D))
                      H02)).
      assert (HZ : (Z.of_nat (16 * (8 ^ D - 1))
                    <= Z.of_nat (2 * (8 * 8 ^ D - 1)))%Z).
      { rewrite !Nat2Z.inj_mul.
        rewrite (Nat2Z.inj_sub (8 ^ D) 1 (z3b_pow8_ge1 D)).
        rewrite (Nat2Z.inj_sub (8 * 8 ^ D) 1 (z3b_pow8_ge1 (S D))).
        change (Z.of_nat 16) with 16%Z.
        change (Z.of_nat 2) with 2%Z.
        change (Z.of_nat 1) with 1%Z.
        assert (HZP1 : (1 <= Z.of_nat (8 ^ D))%Z)
          by (apply (proj1 (Nat2Z.inj_le 1 (8 ^ D))); apply z3b_pow8_ge1).
        lia. }
      exact (proj2 (Nat2Z.inj_le (16 * (8 ^ D - 1))
                                 (2 * (8 * 8 ^ D - 1))) HZ).
    + apply (Nat.mul_le_mono_l (2 * Nat.sqrt (8 ^ D))
                               (Nat.sqrt (8 * 8 ^ D))
                               (2 * (8 * 8 ^ D - 1))).
      exact Hnat.
Qed.

(* 辅助：1 ≤ n ⟹ n < n·8^D（pair_den 下界的 n2 > n1 分支） *)
(* —— Phase D 前置件（E202/E209 手动链：数值核保持原子线性，禁 nia/大目标）—— *)

(* 通用幂下界：1 ≤ b ⟹ 1 ≤ b^t *)
Lemma z3b_pow_ge1 : forall b t : nat, Nat.le 1 b -> Nat.le 1 (b ^ t).
Proof.
  intros b t Hb. induction t as [| t IH].
  - apply Nat.le_refl.
  - rewrite (Nat.pow_succ_r' b t).
    apply Nat.le_trans with (m := (1 * 1)%nat).
    + apply Nat.le_refl.
    + apply (Nat.mul_le_mono 1 b 1 (b ^ t)); assumption.
Qed.

(* 4^t ≤ 8^t（同幂基增） *)
Lemma z3b_pow4_le_pow8 : forall t, Nat.le (4 ^ t) (8 ^ t).
Proof.
  intros t. induction t as [| t IH].
  - apply Nat.le_refl.
  - rewrite (Nat.pow_succ_r 4 t (Nat.le_0_l t)).
    rewrite (Nat.pow_succ_r 8 t (Nat.le_0_l t)).
    apply Nat.le_trans with (m := (4 * 8 ^ t)%nat).
    + apply (Nat.mul_le_mono_l (4 ^ t) (8 ^ t) 4). exact IH.
    + apply (Nat.mul_le_mono_r 4 8 (8 ^ t)).
      apply Nat.leb_le. vm_compute. reflexivity.
Qed.

(* c ≥ 1 ⟹ c·4^t > 0 *)
Lemma z3b_pos_mul4 : forall c t : nat, Nat.le 1 c -> Nat.lt 0 (c * 4 ^ t).
Proof.
  intros c t Hc.
  apply Nat.lt_le_trans with (m := c%nat).
  - apply Nat.lt_le_trans with (m := 1%nat);
      [apply Nat.leb_le; vm_compute; reflexivity | exact Hc].
  - assert (Hs : Nat.le (c * 1) (c * 4 ^ t))
      by (apply (Nat.mul_le_mono_l 1 (4 ^ t) c);
          apply (z3b_pow_ge1 4); apply Nat.leb_le; vm_compute; reflexivity).
    rewrite Nat.mul_1_r in Hs. exact Hs.
Qed.

(* 2 ≤ P ⟹ P ≤ 2·(P−1)：E 上界的分母支配核（Z 线性，E209 路线） *)
Lemma z3b_sub_lb : forall P : nat, Nat.le 2 P -> Nat.le P (2 * (P - 1)).
Proof.
  intros P HP.
  apply (proj2 (Nat2Z.inj_le P (2 * (P - 1)))).
  rewrite Nat2Z.inj_mul.
  assert (H1P : 1 <= P)
    by (apply Nat.le_trans with (m := 2%nat);
        [apply Nat.leb_le; vm_compute; reflexivity | exact HP]).
  rewrite (Nat2Z.inj_sub P 1 H1P).
  change (Z.of_nat 2) with 2%Z.
  assert (HPZ : (2 <= Z.of_nat P)%Z)
    by (apply (proj1 (Nat2Z.inj_le 2 P)); exact HP).
  lia.
Qed.

Lemma z3b_P_ge2 : forall D, Nat.le 1 D -> Nat.le 2 (8 ^ D).
Proof.
  intros D HD.
  apply Nat.le_trans with (m := 8%nat).
  - apply Nat.leb_le. vm_compute. reflexivity.
  - rewrite <- (Nat.pow_1_r 8). apply Nat.pow_le_mono_r.
    + intros Hc; discriminate Hc.
    + exact HD.
Qed.

(* E 上界（E202 整项链）：1 ≤ D、K ≥ 1、K² ≤ 8^D ⟹ E_D ≤ 1/K。
   交叉乘 8^D·K ≤ 2·(8^D−1)·s 归结为 K ≤ s（sqrt 精确性）与
   8^D ≤ 2·(8^D−1)（线性封口），两次 mul 单调显式接——无 nia *)
Lemma z3b_E_le_qmk : forall D K : nat,
  Nat.le 1 D -> Nat.le 1 K -> Nat.le (K * K) (8 ^ D) ->
  Qle (z3b_E D) (z3b_qmk 1 K).
Proof.
  intros D K HD HK1 HKK.
  unfold z3b_E.
  apply (z3b_qmk_le_Q (8 ^ D) (2 * (8 ^ D - 1) * Nat.sqrt (8 ^ D)) 1 K).
  - apply Nat.lt_le_trans with (m := 1%nat);
      [apply Nat.lt_0_succ | apply z3b_E_den_ge1; exact HD].
  - exact HK1.
  - rewrite Nat.mul_1_l.
    apply Nat.le_trans with (m := (8 ^ D * Nat.sqrt (8 ^ D))%nat).
    + apply (Nat.mul_le_mono_l K (Nat.sqrt (8 ^ D)) (8 ^ D)).
      apply z3b_sqrt_ge. exact HKK.
    + apply (Nat.mul_le_mono_r (8 ^ D) (2 * (8 ^ D - 1)) (Nat.sqrt (8 ^ D))).
      apply z3b_sub_lb. apply z3b_P_ge2. exact HD.
Qed.

Lemma z3b_n_lt_nq8 : forall (n D : nat), Nat.le 1 n -> Nat.le 1 D ->
  Nat.lt n (n * 8 ^ D).
Proof.
  intros n D Hn HD.
  assert (Hn0 : Nat.lt 0 n)
    by (apply Nat.lt_le_trans with (m := 1%nat); [apply Nat.le_refl | exact Hn]).
  assert (Hlt8 : Nat.lt 1 (8 ^ D)).
  { apply Nat.le_lt_trans with (m := D).
    - exact HD.
    - apply Nat.pow_gt_lin_r. apply Nat.leb_le. vm_compute. reflexivity. }
  assert (Hstep : Nat.lt (n * 1) (n * 8 ^ D)).
  { apply (proj1 (Nat.mul_lt_mono_pos_l n 1 (8 ^ D) Hn0)). exact Hlt8. }
  rewrite Nat.mul_1_r in Hstep. exact Hstep.
Qed.

(* ★ D1 统一逐对包络：任意 n ≥ 1、距 D ≥ 1，
   pf(n, n·8^D) ≤ E_D（奇偶距同一证明——sqrt 因子配方） *)
Lemma z3b_env_uni : forall (n D : nat), Nat.le 1 n -> Nat.le 1 D ->
  Qle_bool (z3b_pf n (n * 8 ^ D)) (z3b_E D) = true.
Proof.
  intros n D Hn HD.
  unfold z3b_pf, z3b_E, FrameCheckInstance.pair_num, FrameCheckInstance.pair_den.
  apply z3b_qmk_le.
  - (* pair_den > 0：2 ≤ 2·(n·8^D − n)·√ ⟸ n < n·8^D（z3b_pair_den_lb） *)
    apply Nat.lt_le_trans with (m := 2%nat); [apply Nat.lt_0_succ |].
    apply z3b_pair_den_lb; [exact Hn |].
    apply z3b_n_lt_nq8; assumption.
  - (* 2·(8^D−1)·⌊√8^D⌋ > 0：两因子各 ≥ 1 *)
    assert (H8ge1 : Nat.le 1 (8 ^ D)).
    { rewrite <- (Nat.pow_0_r 8). apply Nat.pow_le_mono_r.
      - intros Hc. discriminate Hc.
      - apply Nat.le_0_l. }
    assert (Hs8ge1 : Nat.le 1 (Nat.sqrt (8 ^ D))).
    { apply (proj1 (Nat.sqrt_le_square (8 ^ D) 1)).
      rewrite Nat.mul_1_l. exact H8ge1. }
    assert (Hd1 : Nat.le 1 (8 ^ D - 1)).
    { rewrite Nat.sub_1_r. apply Nat.lt_le_pred.
      apply Nat.le_lt_trans with (m := D).
      - exact HD.
      - apply Nat.pow_gt_lin_r. apply Nat.leb_le. vm_compute. reflexivity. }
    apply Nat.lt_le_trans with (m := 1%nat); [apply Nat.lt_0_succ |].
    replace (2 * (8 ^ D - 1) * Nat.sqrt (8 ^ D))%nat
      with ((2 * (8 ^ D - 1)) * Nat.sqrt (8 ^ D))%nat by ring.
    apply (Nat.mul_le_mono 1 (2 * (8 ^ D - 1)) 1 (Nat.sqrt (8 ^ D))).
    + apply Nat.le_trans with (m := 2%nat).
      * apply Nat.leb_le. vm_compute. reflexivity.
      * assert (H2 : Nat.le (2 * 1) (2 * (8 ^ D - 1)))
          by (apply Nat.mul_le_mono_l; exact Hd1).
        rewrite Nat.mul_1_r in H2. exact H2.
    + exact Hs8ge1.
  - (* 交叉乘 a·d ≤ c·b：键 n·⌊√8^D⌋ ≤ ⌊√(n·(n·8^D))⌋，K := 8^D·2·(8^D−1)·n 消元 *)
    assert (Hsub : (n * 8 ^ D - n)%nat = (n * (8 ^ D - 1))%nat).
    { rewrite Nat.mul_sub_distr_l. rewrite Nat.mul_1_r. reflexivity. }
    rewrite Hsub.
    assert (Hsqrt_lb : Nat.le (Nat.sqrt (8 ^ D) * Nat.sqrt (8 ^ D)) (8 ^ D))
      by (apply (proj2 (Nat.sqrt_le_square (8 ^ D) (Nat.sqrt (8 ^ D))));
          apply Nat.le_refl).
    assert (HSQ : Nat.le (n * Nat.sqrt (8 ^ D)) (Nat.sqrt (n * (n * 8 ^ D)))).
    { apply (proj1 (Nat.sqrt_le_square (n * (n * 8 ^ D)) (n * Nat.sqrt (8 ^ D)))).
      replace ((n * Nat.sqrt (8 ^ D)) * (n * Nat.sqrt (8 ^ D)))%nat
        with ((n * n) * (Nat.sqrt (8 ^ D) * Nat.sqrt (8 ^ D)))%nat by ring.
      replace (n * (n * 8 ^ D))%nat with ((n * n) * 8 ^ D)%nat by ring.
      apply Nat.mul_le_mono; [apply Nat.le_refl | exact Hsqrt_lb]. }
    replace ((n * (n * 8 ^ D)) * (2 * (8 ^ D - 1) * Nat.sqrt (8 ^ D)))%nat
      with ((8 ^ D * (2 * (8 ^ D - 1)) * n) * (n * Nat.sqrt (8 ^ D)))%nat by ring.
    replace (8 ^ D * (2 * (n * (8 ^ D - 1)) * Nat.sqrt (n * (n * 8 ^ D))))%nat
      with ((8 ^ D * (2 * (8 ^ D - 1)) * n) * Nat.sqrt (n * (n * 8 ^ D)))%nat by ring.
    apply Nat.mul_le_mono_l. exact HSQ.
Qed.

(* —— Phase C：SP 前缀和 + 预算界（total_le 定型为装配所需形态）—— *)

(* Q 右平移单调（PSA 环境 Q setoid 实例失效——E190 同族，禁 setoid_rewrite；
   z ≤ z 用 Qle_refl，无需非负前提） *)
Lemma z3b_Qplus_le_r : forall x y z : Q, Qle x y -> Qle (x + z) (y + z).
Proof.
  intros x y z H. apply Qplus_le_compat.
  - exact H.
  - apply Qle_refl.
Qed.

(* qmk 非负（分母正时）：0 ≡ qmk 0 1，交叉乘 0·1 ≤ a·b 恒真 *)
Lemma z3b_qmk_ge0 : forall a b : nat, Nat.lt 0 b -> (0 <= z3b_qmk a b)%Q.
Proof.
  intros a b Hb.
  apply Qle_bool_imp_le.
  change 0%Q with (z3b_qmk 0 1).
  apply z3b_qmk_le.
  - apply Nat.leb_le. vm_compute. reflexivity.
  - exact Hb.
  - apply Nat.le_0_l.
Qed.

(* E_D ≥ 0（D ≥ 1；E 0 走 qmk 退化分支不在使用集） *)
Lemma z3b_E_ge0 : forall D, Nat.le 1 D -> (0 <= z3b_E D)%Q.
Proof.
  intros D HD. unfold z3b_E. apply z3b_qmk_ge0.
  apply Nat.lt_le_trans with (m := 1%nat);
    [apply Nat.lt_0_succ | apply z3b_E_den_ge1; exact HD].
Qed.

(* ★ Qeq 传导桥（PSA 环境 Q setoid/morphism 实例失效的替代基建）：
   Qeq x y（Z 层交叉积相等）+ Qle x z ⟹ Qle y z。
   Z 层证明：目标 yn·zd ≤ zn·yd ⟸ 乘 xd>0 后链
   yn·zd·xd = xn·yd·zd（Hxy）≤ zn·xd·yd = zn·yd·xd（Hxz 平移） *)
Lemma z3b_Qeq_le_l : forall x y z : Q, Qeq x y -> Qle x z -> Qle y z.
Proof.
  intros x y z Hxy Hxz.
  unfold Qeq in Hxy.
  unfold Qle in Hxz |- *.
  destruct x as [xn xd]; destruct y as [yn yd]; destruct z as [zn zd].
  cbn [Qnum Qden] in *.
  apply Z.eqb_eq in Hxy.
  assert (Heq : (xn * Z.pos yd = yn * Z.pos xd)%Z) by (apply Z.eqb_eq; exact Hxy).
  assert (Hxyx : (yn * Z.pos xd = xn * Z.pos yd)%Z) by (rewrite Heq; reflexivity).
  assert (Hxd : (0 <= Z.pos xd)%Z)
    by exact (Z.lt_le_incl 0 (Z.pos xd) (Pos2Z.is_pos xd)).
  assert (Hyd : (0 <= Z.pos yd)%Z)
    by exact (Z.lt_le_incl 0 (Z.pos yd) (Pos2Z.is_pos yd)).
  assert (Hyd_pos : (0 < Z.pos yd)%Z) by exact (Pos2Z.is_pos yd).
  (* 链：yn·zd·xd = xn·zd·yd（Hxy）≤ zn·xd·yd（Hxz）= zn·yd·xd（消去） *)
  assert (Hmono := proj1 (Z.mul_le_mono_pos_r (xn * Z.pos zd) (zn * Z.pos xd)
                                              (Z.pos yd) Hyd_pos) Hxz).
  assert (Hxd_pos : (0 < Z.pos xd)%Z) by exact (Pos2Z.is_pos xd).
  apply (proj2 (Z.mul_le_mono_pos_r (yn * Z.pos zd) (zn * Z.pos yd) (Z.pos xd) Hxd_pos)).
  apply Z.le_trans with (m := (xn * Z.pos zd * Z.pos yd)%Z).
  - replace ((yn * Z.pos zd) * Z.pos xd)%Z with (xn * Z.pos zd * Z.pos yd)%Z by (rewrite <- (Z.mul_assoc yn (Z.pos zd) (Z.pos xd));
      rewrite (Z.mul_comm (Z.pos zd) (Z.pos xd));
      rewrite (Z.mul_assoc yn (Z.pos xd) (Z.pos zd));
      rewrite Hxyx;
      rewrite <- (Z.mul_assoc xn (Z.pos yd) (Z.pos zd));
      rewrite (Z.mul_comm (Z.pos yd) (Z.pos zd));
      rewrite <- (Z.mul_assoc xn (Z.pos zd) (Z.pos yd));
      reflexivity).
    apply Z.le_refl.
  - replace ((zn * Z.pos yd) * Z.pos xd)%Z with (zn * Z.pos xd * Z.pos yd)%Z by ring.
    exact Hmono.
Qed.

(* 对偶传导：Qeq x y + Qle y z ⟹ Qle x z *)
Lemma z3b_Qeq_le_r : forall x y z : Q, Qeq x y -> Qle y z -> Qle x z.
Proof.
  intros x y z Hxy Hyz.
  apply (z3b_Qeq_le_l y x z (Qeq_sym x y Hxy)).
  exact Hyz.
Qed.

(* Q 右注入：y ≤ y + z（0 ≤ z 时） *)
Lemma z3b_Qle_add_r : forall y z : Q, Qle 0 z -> Qle y (y + z).
Proof.
  intros y z Hz.
  apply (z3b_Qeq_le_r y (y + 0)%Q (y + z)%Q (Qeq_sym (y + 0)%Q y (Qplus_0_r y))).
  apply Qplus_le_compat.
  - apply Qle_refl.
  - exact Hz.
Qed.

(* E202 换形引理（整项入库）：左结合 (x+y)+z == 右结合 x+(y+z)。
   nat/Q 变量积的两种结合形态 syntactic 不等、转换归约不闭合（E202 根因3）——
   凡 Q 加法形状失配一律调用本引理显式换形，禁止跨形状 exact/apply
   （unifier 对 Qle 的 Z 投影展开旋转 = run145/149/150 超时根因） *)
Lemma z3b_Qplus_assoc_r : forall x y z : Q, Qeq (x + y + z) (x + (y + z)).
Proof.
  intros x y z. apply Qeq_sym. apply (Qplus_assoc x y z).
Qed.

(* —— Phase D：D2 尾部几何压缩（自 d = 9 起成对，余项 1/500/4^t）——
   E202/E125 手动链纪律：eo/ee 各 ≤ 1/K（K := 8^{t+4}，z3b_E_le_qmk），
   对和 ≤ 2/K；数值核 (2/K + 1/(2000·A))·(500·A) ≤ K·(2000·A)（A := 4^t）
   在原子 A/B 上线性、Z 层 lia 封口——全程无 nia、无 vm_compute 大项、
   无跨形状 exact（换形一律走 z3b_Qplus_assoc_r / Qeq 传导桥） *)

(* R 的分子投影（Qdiv 一步 destruct 配平） *)
Lemma z3b_R_num : forall t, Qnum (z3b_R t) = 1%Z.
Proof.
  intros t. induction t as [| t IH].
  - reflexivity.
  - cbn [z3b_R]. unfold Qdiv, Qmult, Qinv.
    cbn [Qnum Qden Qinv].
    destruct (z3b_R t) as [rn rd].
    cbn [Qnum] in IH.
    cbn [Qnum Qden].
    rewrite IH. reflexivity.
Qed.

(* R 的分母投影：den(R t) = 500·4^t *)
Lemma z3b_R_den : forall t, Z.pos (Qden (z3b_R t)) = Z.of_nat (500 * 4 ^ t).
Proof.
  intros t. induction t as [| t IH].
  - cbn [z3b_R]. reflexivity.
  - cbn [z3b_R]. unfold Qdiv, Qmult, Qinv.
    cbn [Qnum Qden Qinv].
    destruct (z3b_R t) as [rn rd].
    cbn [Qden] in IH.
    cbn [Qnum Qden].
    rewrite (Nat.pow_succ_r 4 t (Nat.le_0_l t)).
    replace (500 * (4 * 4 ^ t))%nat with ((500 * 4 ^ t) * 4)%nat
      by (rewrite <- (Nat.mul_assoc 500 (4 ^ t) 4); rewrite (Nat.mul_comm (4 ^ t) 4);
          reflexivity).
    rewrite Nat2Z.inj_mul.
    rewrite <- IH.
    rewrite (Pos2Z.inj_mul rd 4).
    change (Z.of_nat 4) with 4%Z.
    reflexivity.
Qed.

(* R 的 qmk 规范形：R t == 1/(500·4^t) *)
Lemma z3b_R_qmk : forall t, Qeq (z3b_R t) (z3b_qmk 1 (500 * 4 ^ t)).
Proof.
  intros t.
  assert (HD : Nat.lt 0 (500 * 4 ^ t))
    by (apply (z3b_pos_mul4 500); apply Nat.leb_le; vm_compute; reflexivity).
  unfold Qeq.
  rewrite (z3b_R_num t).
  rewrite (z3b_R_den t).
  rewrite (z3b_qmk_num 1 (500 * 4 ^ t) HD).
  rewrite (z3b_qmk_den 1 (500 * 4 ^ t) HD).
  change (Z.of_nat 1) with 1%Z.
  rewrite (z3b_Zpos_of (500 * 4 ^ t) HD).
  reflexivity.
Qed.

(* R (S t) == 1/(2000·4^t) *)
Lemma z3b_R_S_qmk : forall t, Qeq (z3b_R (S t)) (z3b_qmk 1 (2000 * 4 ^ t)).
Proof.
  intros t.
  assert (HD : Nat.lt 0 (2000 * 4 ^ t))
    by (apply (z3b_pos_mul4 2000); apply Nat.leb_le; vm_compute; reflexivity).
  unfold Qeq.
  rewrite (z3b_R_num (S t)).
  rewrite (z3b_R_den (S t)).
  rewrite (z3b_qmk_num 1 (2000 * 4 ^ t) HD).
  rewrite (z3b_qmk_den 1 (2000 * 4 ^ t) HD).
  change (Z.of_nat 1) with 1%Z.
  rewrite (z3b_Zpos_of (2000 * 4 ^ t) HD).
  rewrite (Nat.pow_succ_r 4 t (Nat.le_0_l t)).
  replace (2000 * 4 ^ t)%nat with (4 * (500 * 4 ^ t))%nat
    by (rewrite (Nat.mul_assoc 4 500 (4 ^ t)); change (4 * 500) with 2000;
        reflexivity).
  replace (500 * (4 * 4 ^ t))%nat with ((500 * 4 ^ t) * 4)%nat
    by (rewrite <- (Nat.mul_assoc 500 (4 ^ t) 4); rewrite (Nat.mul_comm (4 ^ t) 4);
        reflexivity).
  rewrite !Nat2Z.inj_mul.
  change (Z.of_nat 4) with 4%Z.
  ring.
Qed.

(* 数值核：2/K + 1/(2000·A) ≤ 1/(500·A) 的 qmk 交叉乘（A := 4^t，K := 8^{t+4}）。
   线性封口 2000000·A + 2048000·B ≤ 8192000·B ⟸ A ≤ B、1 ≤ A（Z 层 lia） *)
Lemma z3b_tail_core : forall t : nat,
  Nat.le ((2 * (2000 * 4 ^ t) + 1 * 8 ^ (t + 4)) * (500 * 4 ^ t))
         (1 * (8 ^ (t + 4) * (2000 * 4 ^ t))).
Proof.
  intros t.
  remember (4 ^ t)%nat as A eqn:HAr.
  remember (8 ^ (t + 4))%nat as B eqn:HBr.
  (* E227 续：nat ring 对 ^t 变量幂元 20-40s/次——remember+clearbody 原子化
     再 ring（ms 级）；不 clearbody 则 ring zeta 展开 sees ^ → not a valid ring equation *)
  assert (HA1 : Nat.le 1 A)
    by (rewrite HAr; apply (z3b_pow_ge1 4);
        apply Nat.leb_le; vm_compute; reflexivity).
  assert (H48 : Nat.le (4 ^ t) (8 ^ t)) by (apply z3b_pow4_le_pow8).
  assert (Hpow : B = (8 ^ t * 4096)%nat).
  { rewrite HBr. rewrite (Nat.pow_add_r 8 t 4). change (8 ^ 4) with 4096. reflexivity. }
  (* E227 续：nat ring 随字面量一元展开爆炸（2000 → 42s）——换形一律显式链 *)
  assert (E1 : (1 * (B * (2000 * A)))%nat = (A * (2000 * B))%nat).
  { rewrite Nat.mul_1_l. rewrite (Nat.mul_comm B (2000 * A)).
    rewrite <- (Nat.mul_assoc 2000 A B). rewrite (Nat.mul_comm A B).
    rewrite (Nat.mul_assoc 2000 B A). rewrite (Nat.mul_comm (2000 * B) A).
    reflexivity. }
  (* E2x 小字面量形：百万级 nat 字面量的 change/conv 也栈溢出，系数保持 ≤4000 *)
  assert (E2 : ((2 * (2000 * A) + 1 * B) * (500 * A))%nat
               = (A * (4000 * (500 * A) + 500 * B))%nat).
  { rewrite Nat.mul_add_distr_r. rewrite !Nat.mul_1_l.
    rewrite <- (Nat.mul_assoc 2 (2000 * A) (500 * A)).
    rewrite <- (Nat.mul_assoc 2000 A (500 * A)).
    rewrite (Nat.mul_comm A (500 * A)).
    rewrite <- (Nat.mul_assoc 500 A A).
    rewrite (Nat.mul_assoc 2 2000 (500 * (A * A))).
    change (2 * 2000) with 4000.
    rewrite (Nat.mul_assoc 500 A A).
    rewrite (Nat.mul_assoc 4000 (500 * A) A).
    rewrite (Nat.mul_comm (4000 * (500 * A)) A).
    rewrite (Nat.mul_comm B (500 * A)).
    rewrite <- (Nat.mul_assoc 500 A B).
    rewrite (Nat.mul_comm A B).
    rewrite (Nat.mul_assoc 500 B A).
    rewrite (Nat.mul_comm (500 * B) A).
    rewrite <- (Nat.mul_add_distr_l A (4000 * (500 * A)) (500 * B)).
    reflexivity. }
  rewrite E1.
  rewrite E2.
  apply (Nat.mul_le_mono_l (4000 * (500 * A) + 500 * B) (2000 * B) A).
  apply (proj2 (Nat2Z.inj_le (4000 * (500 * A) + 500 * B) (2000 * B))).
  rewrite Hpow.
  rewrite Nat2Z.inj_add.
  rewrite !Nat2Z.inj_mul.
  assert (HA1Z : (1 <= Z.of_nat A)%Z)
    by (apply (proj1 (Nat2Z.inj_le 1 A)); exact HA1).
  assert (H48Z : (Z.of_nat A <= Z.of_nat (8 ^ t))%Z)
    by (apply (proj1 (Nat2Z.inj_le A (8 ^ t)));
        rewrite HAr; exact H48).
  lia.
Qed.

(* 小字面量 nat ring 引理（1/2 系数 ring 实测 0.02s——大字面量才爆炸） *)
Lemma z3b_twoKK : forall K : nat, (1 * K + 1 * K) * K = 2 * (K * K).
Proof. intros K. ring. Qed.

(* ★ D2 尾部几何压缩：z3b_tail t + R t ≤ R 0 = 1/500
   （S 情形：对和 ≤ 2/K 与 R(S t) + 对和 ≤ R t 的显式链，assoc 换形接 IH） *)
Lemma z3b_tail_R : forall t, Qle (z3b_tail t + z3b_R t) (z3b_R 0).
Proof.
  intros t. induction t as [| t IH].
  - cbn [z3b_tail].
    apply (z3b_Qeq_le_r (0 + z3b_R 0)%Q (z3b_R 0)%Q (z3b_R 0)%Q
                        (Qplus_0_l (z3b_R 0)) (Qle_refl (z3b_R 0))).
  - cbn [z3b_tail]. unfold z3b_e_odd, z3b_e_even.
    assert (Hd11 : Nat.le 1 ((4 + t) + (4 + t) + 1))
      by (apply (proj2 (Nat2Z.inj_le 1 ((4 + t) + (4 + t) + 1)));
          rewrite !Nat2Z.inj_add; lia).
    assert (Hd21 : Nat.le 1 ((4 + t) + (4 + t) + 2))
      by (apply (proj2 (Nat2Z.inj_le 1 ((4 + t) + (4 + t) + 2)));
          rewrite !Nat2Z.inj_add; lia).
    assert (Hidx1 : Nat.le ((t + 4) + (t + 4)) ((4 + t) + (4 + t) + 1))
      by (apply (proj2 (Nat2Z.inj_le ((t + 4) + (t + 4))
                                      ((4 + t) + (4 + t) + 1)));
          rewrite !Nat2Z.inj_add; lia).
    assert (Hidx2 : Nat.le ((t + 4) + (t + 4)) ((4 + t) + (4 + t) + 2))
      by (apply (proj2 (Nat2Z.inj_le ((t + 4) + (t + 4))
                                      ((4 + t) + (4 + t) + 2)));
          rewrite !Nat2Z.inj_add; lia).
    assert (HK1 : Nat.le 1 (8 ^ (t + 4))) by (apply z3b_pow8_ge1).
    assert (HKK1 : Nat.le (8 ^ (t + 4) * 8 ^ (t + 4))
                          (8 ^ ((4 + t) + (4 + t) + 1))).
    { rewrite <- (Nat.pow_add_r 8 (t + 4) (t + 4)).
      apply Nat.pow_le_mono_r.
      - intros Hc; discriminate Hc.
      - exact Hidx1. }
    assert (HKK2 : Nat.le (8 ^ (t + 4) * 8 ^ (t + 4))
                          (8 ^ ((4 + t) + (4 + t) + 2))).
    { rewrite <- (Nat.pow_add_r 8 (t + 4) (t + 4)).
      apply Nat.pow_le_mono_r.
      - intros Hc; discriminate Hc.
      - exact Hidx2. }
    assert (Heo : Qle (z3b_E ((4 + t) + (4 + t) + 1))
                      (z3b_qmk 1 (8 ^ (t + 4))))
      by (apply (z3b_E_le_qmk ((4 + t) + (4 + t) + 1) (8 ^ (t + 4)));
          [exact Hd11 | exact HK1 | exact HKK1]).
    assert (Hee : Qle (z3b_E ((4 + t) + (4 + t) + 2))
                      (z3b_qmk 1 (8 ^ (t + 4))))
      by (apply (z3b_E_le_qmk ((4 + t) + (4 + t) + 2) (8 ^ (t + 4)));
          [exact Hd21 | exact HK1 | exact HKK2]).
    (* 对和 ≤ 2/K *)
    assert (Hw : Qle (z3b_E ((4 + t) + (4 + t) + 1) + z3b_E ((4 + t) + (4 + t) + 2))
                     (z3b_qmk 2 (8 ^ (t + 4)))).
    { apply (Qle_trans
               (z3b_E ((4 + t) + (4 + t) + 1) + z3b_E ((4 + t) + (4 + t) + 2))
               (z3b_qmk 1 (8 ^ (t + 4)) + z3b_E ((4 + t) + (4 + t) + 2))
               (z3b_qmk 2 (8 ^ (t + 4)))).
      - apply (z3b_Qplus_le_r (z3b_E ((4 + t) + (4 + t) + 1))
                              (z3b_qmk 1 (8 ^ (t + 4)))
                              (z3b_E ((4 + t) + (4 + t) + 2))).
        exact Heo.
      - apply (Qle_trans
                 (z3b_qmk 1 (8 ^ (t + 4)) + z3b_E ((4 + t) + (4 + t) + 2))
                 (z3b_qmk 1 (8 ^ (t + 4)) + z3b_qmk 1 (8 ^ (t + 4)))
                 (z3b_qmk 2 (8 ^ (t + 4)))).
        + apply (Qplus_le_compat (z3b_qmk 1 (8 ^ (t + 4)))
                                 (z3b_qmk 1 (8 ^ (t + 4)))
                                 (z3b_E ((4 + t) + (4 + t) + 2))
                                 (z3b_qmk 1 (8 ^ (t + 4)))).
          * apply Qle_refl.
          * exact Hee.
        + apply (z3b_qmk_add_le 1 (8 ^ (t + 4)) 1 (8 ^ (t + 4)) 2 (8 ^ (t + 4))).
          * exact HK1.
          * exact HK1.
          * exact HK1.
          * replace (2 * (8 ^ (t + 4) * 8 ^ (t + 4)))%nat
              with ((1 * 8 ^ (t + 4) + 1 * 8 ^ (t + 4)) * 8 ^ (t + 4))%nat
              by (apply z3b_twoKK).
            apply Nat.le_refl. }
    (* 对和 + R(S t) ≤ R t *)
    assert (Hmid : Qle (z3b_qmk 2 (8 ^ (t + 4)) + z3b_qmk 1 (2000 * 4 ^ t))
                       (z3b_qmk 1 (500 * 4 ^ t))).
    { apply (z3b_qmk_add_le 2 (8 ^ (t + 4)) 1 (2000 * 4 ^ t) 1 (500 * 4 ^ t)).
      - exact HK1.
      - apply (z3b_pos_mul4 2000). apply Nat.leb_le. vm_compute. reflexivity.
      - apply (z3b_pos_mul4 500). apply Nat.leb_le. vm_compute. reflexivity.
      - exact (z3b_tail_core t). }
    assert (HRt_le : Qle (z3b_qmk 1 (500 * 4 ^ t)) (z3b_R t))
      by (apply (z3b_Qeq_le_l (z3b_R t) (z3b_qmk 1 (500 * 4 ^ t))
                              (z3b_R t)
                              (z3b_R_qmk t)
                              (Qle_refl (z3b_R t)))).
    assert (Hstep : Qle (z3b_E ((4 + t) + (4 + t) + 1) + z3b_E ((4 + t) + (4 + t) + 2)
                         + z3b_R (S t))
                        (z3b_R t)).
    { apply (Qle_trans
               (z3b_E ((4 + t) + (4 + t) + 1) + z3b_E ((4 + t) + (4 + t) + 2)
                + z3b_R (S t))
               (z3b_qmk 2 (8 ^ (t + 4)) + z3b_R (S t))
               (z3b_R t)).
      - apply (z3b_Qplus_le_r
                 (z3b_E ((4 + t) + (4 + t) + 1) + z3b_E ((4 + t) + (4 + t) + 2))
                 (z3b_qmk 2 (8 ^ (t + 4)))
                 (z3b_R (S t))).
        exact Hw.
      - apply (Qle_trans
                 (z3b_qmk 2 (8 ^ (t + 4)) + z3b_R (S t))
                 (z3b_qmk 1 (500 * 4 ^ t))
                 (z3b_R t)).
        + apply (Qle_trans
                   (z3b_qmk 2 (8 ^ (t + 4)) + z3b_R (S t))
                   (z3b_qmk 2 (8 ^ (t + 4)) + z3b_qmk 1 (2000 * 4 ^ t))
                   (z3b_qmk 1 (500 * 4 ^ t))).
          * apply (Qplus_le_compat (z3b_qmk 2 (8 ^ (t + 4)))
                                   (z3b_qmk 2 (8 ^ (t + 4)))
                                   (z3b_R (S t))
                                   (z3b_qmk 1 (2000 * 4 ^ t))).
            -- apply Qle_refl.
            -- apply (z3b_Qeq_le_r (z3b_R (S t))
                                   (z3b_qmk 1 (2000 * 4 ^ t))
                                   (z3b_qmk 1 (2000 * 4 ^ t))
                                   (z3b_R_S_qmk t)
                                   (Qle_refl (z3b_qmk 1 (2000 * 4 ^ t)))).
          * exact Hmid.
        + exact HRt_le. }
    (* 装配：((tail + w) + R(S t)) 换形为 tail + (w + R(S t)) ≤ tail + R t ≤ R 0 *)
    apply (z3b_Qeq_le_r
             ((z3b_tail t
               + (z3b_E ((4 + t) + (4 + t) + 1) + z3b_E ((4 + t) + (4 + t) + 2)))
              + z3b_R (S t))%Q
             (z3b_tail t
              + ((z3b_E ((4 + t) + (4 + t) + 1) + z3b_E ((4 + t) + (4 + t) + 2))
                 + z3b_R (S t)))%Q
             (z3b_R 0)).
    + apply (z3b_Qplus_assoc_r (z3b_tail t)
                               (z3b_E ((4 + t) + (4 + t) + 1)
                                + z3b_E ((4 + t) + (4 + t) + 2))
                               (z3b_R (S t))).
    + apply (Qle_trans
               (z3b_tail t
                + (z3b_E ((4 + t) + (4 + t) + 1) + z3b_E ((4 + t) + (4 + t) + 2)
                   + z3b_R (S t)))
               (z3b_tail t + z3b_R t)
               (z3b_R 0)).
      * apply (Qplus_le_compat (z3b_tail t) (z3b_tail t)
                               (z3b_E ((4 + t) + (4 + t) + 1)
                                + z3b_E ((4 + t) + (4 + t) + 2)
                                + z3b_R (S t))
                               (z3b_R t)).
        -- apply Qle_refl.
        -- exact Hstep.
      * exact IH.
Qed.

(* SP t := E_1 + E_2 + … + E_t（距离前缀和，Q 层） *)
Fixpoint z3b_SP (t : nat) : Q :=
  match t with
  | 0 => 0%Q
  | S tx => z3b_SP tx + z3b_E (S tx)
  end.

Lemma z3b_SP_mono : forall i j, Nat.le i j -> Qle (z3b_SP i) (z3b_SP j).
Proof.
  intros i j H. induction H as [| j Hle IH].
  - apply Qle_refl.
  - cbn [z3b_SP].
    eapply Qle_trans.
    + exact IH.
    + apply z3b_Qle_add_r.
      apply z3b_E_ge0.
      apply (proj1 (Nat.succ_le_mono 0 j)). apply Nat.le_0_l.
Qed.

(* 倒序不变式（平移起点规避 nat 减法；左结合形与 SP 展开句法精确对齐）：
   ((SP(8+t) + E(9+t)) + E(9+t)) ≤ ((SP 8 + E 9) + E 9)
   S 情形：zx := E(S(9+t))+E(S(9+t)) ≤ E(9+t)（E_step），右平移两次接 IH *)
Lemma z3b_SP_tail_inv : forall t,
  Qle ((z3b_SP (8 + t) + z3b_E (9 + t)) + z3b_E (9 + t))
      ((z3b_SP 8 + z3b_E 9) + z3b_E 9).
Proof.
  intros t. induction t as [| t IH].
  - apply Qle_refl.
  - rewrite !Nat.add_succ_r.
    (* SP 单步展开（ι 一步即停），禁 cbn——递归展开会把 SP 8 炸成九项长链
       与显式项失配 → Qle 投影 unify 指数爆炸（run136-145 超时根因） *)
    replace (z3b_SP (S (8 + t)))%Q with (z3b_SP (8 + t) + z3b_E (S (8 + t)))%Q
      by reflexivity.
    replace (z3b_E (S (8 + t)))%nat with (z3b_E (9 + t))
      by (rewrite <- Nat.add_succ_l; reflexivity).
    (* E125 教训：assert 直接落目标最终形状（左结合）——配平在 assert 内部
       用 z3b_Qplus_assoc_r 整项换形完成，主链 exact 全形状全等 *)
    assert (Hzx : Qle (z3b_E (S (9 + t)) + z3b_E (S (9 + t))) (z3b_E (9 + t))).
    { apply (z3b_E_step (9 + t)).
      apply (proj1 (Nat.succ_le_mono 0 (8 + t))). apply Nat.le_0_l. }
    assert (Hcompat : Qle ((z3b_SP (8 + t) + z3b_E (9 + t))
                           + z3b_E (S (9 + t)) + z3b_E (S (9 + t)))
                          ((z3b_SP (8 + t) + z3b_E (9 + t)) + z3b_E (9 + t))).
    { apply (z3b_Qeq_le_r
               ((z3b_SP (8 + t) + z3b_E (9 + t))
                + z3b_E (S (9 + t)) + z3b_E (S (9 + t)))%Q
               ((z3b_SP (8 + t) + z3b_E (9 + t))
                + (z3b_E (S (9 + t)) + z3b_E (S (9 + t))))%Q
               ((z3b_SP (8 + t) + z3b_E (9 + t)) + z3b_E (9 + t))%Q).
      - apply (z3b_Qplus_assoc_r (z3b_SP (8 + t) + z3b_E (9 + t))
                                 (z3b_E (S (9 + t))) (z3b_E (S (9 + t)))).
      - apply (Qplus_le_compat
                 (z3b_SP (8 + t) + z3b_E (9 + t))
                 (z3b_SP (8 + t) + z3b_E (9 + t))
                 (z3b_E (S (9 + t)) + z3b_E (S (9 + t)))
                 (z3b_E (9 + t))).
        + apply Qle_refl.
        + exact Hzx. }
    exact (Qle_trans _ _ _ Hcompat IH).
Qed.

(* ★ total_le（定型）：任意前缀和 ≤ 预算头 (SP 8 + E 9) + E 9 ≈ 0.38378
   （row_le 装配：行和 ≤ 2·SP(m−1) ≤ 2·预算头 ≈ 0.76755 ≤ 4/5） *)
Lemma z3b_total_le : forall t,
  Qle (z3b_SP t) ((z3b_SP 8 + z3b_E 9) + z3b_E 9).
Proof.
  intros t.
  destruct (Nat.le_gt_cases 8 t) as [Hge | Hlt].
  - assert (Hinv := z3b_SP_tail_inv (t - 8)).
    assert (Hidx2 : (8 + (t - 8))%nat = t).
    { rewrite Nat.add_comm. apply Nat.sub_add. exact Hge. }
    rewrite Hidx2 in Hinv.
    assert (Hidx : (9 + (t - 8))%nat = S t).
    { change (9 + (t - 8))%nat with (S (8 + (t - 8))).
      rewrite Nat.add_comm. f_equal. apply Nat.sub_add. exact Hge. }
    rewrite Hidx in Hinv.
    assert (Hs1 : Qle (z3b_SP t) (z3b_SP t + z3b_E (S t))).
    { apply z3b_Qle_add_r. apply z3b_E_ge0.
      apply (proj1 (Nat.succ_le_mono 0 t)). apply Nat.le_0_l. }
    assert (Hs2 : Qle (z3b_SP t + z3b_E (S t))
                       ((z3b_SP t + z3b_E (S t)) + z3b_E (S t))).
    { apply z3b_Qle_add_r. apply z3b_E_ge0.
      apply (proj1 (Nat.succ_le_mono 0 t)). apply Nat.le_0_l. }
    apply (Qle_trans
             (z3b_SP t)
             ((z3b_SP t + z3b_E (S t)) + z3b_E (S t))
             ((z3b_SP 8 + z3b_E 9) + z3b_E 9)).
    - exact (Qle_trans _ _ _ Hs1 Hs2).
    - exact Hinv.
  - assert (Hm : Qle (z3b_SP t) (z3b_SP 8))
      by (apply z3b_SP_mono; exact (Nat.lt_le_incl _ _ Hlt)).
    assert (Hinj : Qle (z3b_SP 8) ((z3b_SP 8 + z3b_E 9) + z3b_E 9)).
    { apply (Qle_trans (z3b_SP 8) (z3b_SP 8 + z3b_E 9)
                         ((z3b_SP 8 + z3b_E 9) + z3b_E 9)).
      - apply z3b_Qle_add_r. apply z3b_E_ge0.
        apply Nat.leb_le. vm_compute. reflexivity.
      - apply z3b_Qle_add_r. apply z3b_E_ge0.
        apply Nat.leb_le. vm_compute. reflexivity. }
    exact (Qle_trans _ _ _ Hm Hinj).
Qed.

(* ============================================================
   Phase E：row_le 填充基建（累加器 Q 表示 + 相位边界）
   ============================================================ *)

(* 累加器 (num, den) 的 Q 值 *)
Definition z3b_accQ (f : FrameCheckInstance.nat_pair) : Q :=
  z3b_qmk (fst f) (snd f).

(* 表示引理：frac_add 一步的 Q 值 == 两分数 Q 和（精确等式，投影路线） *)
Lemma z3b_frac_add_Qeq : forall num den a b : nat,
  Nat.lt 0 den -> Nat.lt 0 a -> Nat.lt 0 b ->
  Qeq (z3b_accQ (FrameCheckInstance.frac_add num den a b))
      (z3b_qmk num den + z3b_qmk a b).
Proof.
  intros num den a b Hd Ha Hb.
  assert (Hs : Nat.lt 0 (num * b + a * den)).
  { apply Nat.lt_le_trans with (m := (a * den)%nat).
    - apply (Nat.mul_le_mono 1 a 1 den); assumption.
    - apply Nat.le_add_l. }
  assert (Hdb : Nat.lt 0 (den * b))
    by (apply (proj2 (Nat2Z.inj_lt 0 (den * b))); rewrite Nat2Z.inj_mul;
        assert (HdZ : (0 < Z.of_nat den)%Z)
          by (apply (proj1 (Nat2Z.inj_lt 0 den)); exact Hd);
        assert (HbZ : (0 < Z.of_nat b)%Z)
          by (apply (proj1 (Nat2Z.inj_lt 0 b)); exact Hb);
        lia).
  assert (Hn1 : Qnum (z3b_qmk num den) = Z.of_nat num) by (apply z3b_qmk_num; exact Hd).
  assert (Hd1 : Z.pos (Qden (z3b_qmk num den)) = Z.of_nat den)
    by (rewrite (z3b_qmk_den num den Hd); apply z3b_Zpos_of; exact Hd).
  assert (Hn2 : Qnum (z3b_qmk a b) = Z.of_nat a) by (apply z3b_qmk_num; exact Hb).
  assert (Hd2 : Z.pos (Qden (z3b_qmk a b)) = Z.of_nat b)
    by (rewrite (z3b_qmk_den a b Hb); apply z3b_Zpos_of; exact Hb).
  unfold FrameCheckInstance.frac_add, z3b_accQ, Qeq, Qplus.
  cbn [fst snd Qnum Qden Qplus].
  rewrite (z3b_qmk_num (num * b + a * den) (den * b) Hdb).
  rewrite (z3b_qmk_den (num * b + a * den) (den * b) Hdb).
  rewrite (z3b_Zpos_of (den * b) Hdb).
  rewrite Hn1.
  rewrite Hd1.
  rewrite Hn2.
  rewrite Hd2.
  rewrite Nat2Z.inj_add.
  rewrite !Nat2Z.inj_mul.
  rewrite (Pos2Z.inj_mul (Qden (z3b_qmk num den)) (Qden (z3b_qmk a b))).
  rewrite Hd1.
  rewrite Hd2.
  ring.
Qed.

(* bands 长度 = 分区数 m *)
Lemma z3b_bands_length : forall n0 m : nat, length (z3b_bands n0 m) = m.
Proof.
  intros n0 m. unfold z3b_bands.
  rewrite length_map.
  rewrite length_seq. reflexivity.
Qed.

(* bands 取值：nth-of-map-seq 泛化引理（f/s 双参数化归纳——绕开
   nth_indep/map_nth/seq_nth 三件套的隐式参数与签名漂移面，E218/E228） *)
Lemma z3b_map_seq_nth : forall (f : nat -> nat) (m s j : nat),
  Nat.lt j m -> nth j (map f (seq s m)) 0%nat = f (s + j).
Proof.
  intros f m.
  induction m as [| m IH]; intros s j Hj.
  - inversion Hj.
  - destruct j as [| jx].
    + cbn [map seq nth]. rewrite Nat.add_0_r. reflexivity.
    + cbn [map seq nth].
      rewrite (IH _ _ (proj2 (Nat.succ_lt_mono jx m) Hj)).
      f_equal.
      rewrite Nat.add_succ_l.
      rewrite Nat.add_succ_r.
      reflexivity.
Qed.

Lemma z3b_bands_nth : forall n0 m j : nat,
  Nat.lt j m -> nth j (z3b_bands n0 m) 0%nat = (n0 * 8 ^ j)%nat.
Proof.
  intros n0 m j Hj.
  unfold z3b_bands.
  rewrite (z3b_map_seq_nth (fun k : nat => (n0 * 8 ^ k)%nat) m 0 j Hj).
  reflexivity.
Qed.

(* bands 单调：j < i ⟹ n_j < n_i（取值 + n_lt_nq8） *)
Lemma z3b_bands_lt : forall n0 i j : nat,
  Nat.le 2 n0 -> Nat.lt j i ->
  Nat.lt (nth j (z3b_bands n0 (S i)) 0%nat) (nth i (z3b_bands n0 (S i)) 0%nat).
Proof.
  intros n0 i j Hn0 Hj.
  assert (Hpow : (8 ^ i)%nat = (8 ^ j * 8 ^ (i - j))%nat).
  { rewrite <- (Nat.pow_add_r 8 j (i - j)).
    f_equal.
    rewrite (Nat.add_comm j (i - j)).
    symmetry.
        apply (Nat.sub_add j i (Nat.lt_le_incl j i Hj)). }
  rewrite (z3b_bands_nth n0 (S i) j (proj2 (Nat.lt_succ_r j i) (Nat.lt_le_incl j i Hj))).
  rewrite (z3b_bands_nth n0 (S i) i (Nat.lt_succ_diag_r i)).
  replace (n0 * 8 ^ i)%nat with ((n0 * 8 ^ j) * 8 ^ (i - j))%nat
    by (rewrite Hpow; ring).
  assert (H8j : Nat.le 1 (8 ^ j))
    by (rewrite <- (Nat.pow_0_r 8); apply Nat.pow_le_mono_r;
        [intros Hc; discriminate Hc | apply Nat.le_0_l]).
  assert (Hge1 : Nat.le 1 (n0 * 8 ^ j)).
  { apply (Nat.mul_le_mono 1 n0 1 (8 ^ j)).
    - apply Nat.le_trans with (m := 2%nat);
        [apply Nat.leb_le; vm_compute; reflexivity | exact Hn0].
    - exact H8j. }
  apply z3b_n_lt_nq8.
  * exact Hge1.
  * apply (proj2 (Nat2Z.inj_le 1 (i - j))).
    rewrite (Nat2Z.inj_sub i j (Nat.lt_le_incl j i Hj)).
    change (Z.of_nat 1) with 1%Z.
    assert (HZlt : (Z.of_nat j < Z.of_nat i)%Z)
      by (apply (proj1 (Nat2Z.inj_lt j i)); exact Hj).
    lia.
Qed.

(* SP 正性 *)
Lemma z3b_SP_ge0 : forall t : nat, (0 <= z3b_SP t)%Q.
Proof.
  intros t. induction t as [| t IH].
  - cbn [z3b_SP]. apply (z3b_Qeq_le_l (0 + 0)%Q 0%Q 0%Q (Qplus_0_l 0%Q) (Qle_refl 0%Q)).
  - cbn [z3b_SP].
    assert (HA : (0 <= z3b_SP t)%Q) by exact IH.
    assert (HB : (0 <= z3b_E (S t))%Q)
      by (apply z3b_E_ge0; apply (proj1 (Nat.succ_le_mono 0 t)); apply Nat.le_0_l).
    unfold Qle in HA, HB |- *.
    destruct (z3b_SP t) as [an ad], (z3b_E (S t)) as [bn bd].
    cbn [Qnum Qden Qplus] in *.
    unfold Qle, Qplus. cbn [Qnum Qden].
    nia.
Qed.

(* 累加器 den > 0 不变式（2026-09-01 位置去重修正版 2）。
   ⚠️ 旧值比较陈述为假：pair_den n n = 0，aux 在 j ≠ i 且头元素 = n_i 时
   else 分支加 pair_den n_i n_i = 0（反例 orig = [5;5], i = 0, j = 1）。
   修正：按位置去重——枢轴下标 i 之外的所有位置元素 ≠ n_i（row_le 调用点
   由 bands 严格递增供给）。L 与 orig 以偏移值恒等式 Hsub 绑定
   （nth k L = nth (j+k) orig），前缀（firstn）与后缀（skipn）两用。 *)
Lemma z3b_aux_den_pos : forall (L orig : list nat) (i j : nat) (acc : FrameCheckInstance.nat_pair),
  (j + length L <= length orig)%nat ->
  (forall k : nat, Nat.lt k (length L) -> nth k L 0%nat = nth (j + k) orig 0%nat) ->
  Nat.lt i (length orig) ->
  (forall k : nat, Nat.lt k (length orig) -> k <> i ->
     nth k orig 0%nat <> nth i orig 0%nat) ->
  Nat.le 1 (nth i orig 0%nat) ->
  (forall e : nat, In e orig -> Nat.le 1 e) ->
  (forall e : nat, In e orig -> e <> nth i orig 0%nat -> e < nth i orig 0%nat \/ nth i orig 0%nat < e) ->
  Nat.lt 0 (snd acc) ->
  Nat.lt 0 (snd (FrameCheckInstance.row_sum_frac_aux L orig i acc j)).
Proof.
  intros L orig. induction L as [| h tl IH]; intros i j acc Hjl Hsub Hli Hne H1i H1L Htot Hacc.
  - cbn [FrameCheckInstance.row_sum_frac_aux]. exact Hacc.
  - destruct acc as [num den].
    cbn [FrameCheckInstance.row_sum_frac_aux].
    assert (Hjlx : S j + length tl <= length orig).
    { cbn [length] in Hjl.
      replace (S j + length tl)%nat with (j + S (length tl))%nat
        by (rewrite Nat.add_succ_l; rewrite Nat.add_succ_r; reflexivity).
      exact Hjl. }
    assert (Hsubx : forall k : nat, Nat.lt k (length tl) ->
              nth k tl 0%nat = nth (S j + k) orig 0%nat).
    { intros k Hk.
      replace (S j + k)%nat with (j + S k)%nat
        by (rewrite Nat.add_succ_r; rewrite Nat.add_succ_l; reflexivity).
      assert (HSk : Nat.lt (S k) (length (h :: tl))).
      { cbn [length]. apply (proj1 (Nat.succ_lt_mono k (length tl))). exact Hk. }
      rewrite <- (Hsub (S k) HSk).
      reflexivity. }
    assert (H0lt : Nat.lt 0 (length (h :: tl)))
      by (cbn [length]; apply Nat.lt_0_succ).
    assert (Hhj : h = nth j orig 0%nat).
    { rewrite <- (Nat.add_0_r j). rewrite <- (Hsub 0 H0lt). reflexivity. }
    assert (Hjlt : Nat.lt j (length orig)).
    { apply Nat.lt_le_trans with (m := (S (j + length tl))%nat).
      - apply Nat.lt_succ_r. apply Nat.le_add_r.
      - replace (S (j + length tl))%nat with (j + length (h :: tl))%nat
          by (cbn [length]; rewrite Nat.add_succ_r; reflexivity).
        exact Hjl. }
    assert (Hin : In h orig).
    { rewrite Hhj. exact (@nth_In nat j orig 0%nat Hjlt). }
    assert (H1h : Nat.le 1 h) by (apply H1L; exact Hin).
    destruct (Nat.eqb j i) eqn:Hji.
    + exact (IH i (S j) (num, den) Hjlx Hsubx Hli Hne H1i H1L Htot Hacc).
    + (* j ≠ i：位置去重给出头元素 ≠ n_i *)
      assert (Hjni : j <> i) by (apply (proj1 (Nat.eqb_neq j i)); exact Hji).
      assert (Hhne : h <> nth i orig 0%nat).
      { intros Hc. apply (Hne j Hjlt Hjni). rewrite <- Hc. symmetry. exact Hhj. }
      destruct (Nat.ltb h (nth i orig 0%nat)) eqn:Hlt.
      * (* h < n_i：加 pair (h, n_i) *)
        assert (Haccx : Nat.lt 0 (snd (FrameCheckInstance.frac_add num den
                          (FrameCheckInstance.pair_num h (nth i orig 0%nat))
                          (FrameCheckInstance.pair_den h (nth i orig 0%nat))))).
        { cbn [FrameCheckInstance.frac_add snd].
          apply (proj2 (Nat2Z.inj_lt 0 (den * FrameCheckInstance.pair_den h (nth i orig 0%nat)))).
          rewrite Nat2Z.inj_mul.
          assert (HdZ : (0 < Z.of_nat den)%Z)
            by (apply (proj1 (Nat2Z.inj_lt 0 den)); exact Hacc).
          assert (Hlt2 : Nat.lt h (nth i orig 0%nat)) by (apply Nat.ltb_lt; exact Hlt).
          assert (HpdZ : (0 < Z.of_nat (FrameCheckInstance.pair_den h (nth i orig 0%nat)))%Z).
          { apply (proj1 (Nat2Z.inj_lt 0 (FrameCheckInstance.pair_den h (nth i orig 0%nat)))).
            apply Nat.lt_le_trans with (m := 2%nat).
            - apply Nat.leb_le. vm_compute. reflexivity.
            - exact (z3b_pair_den_lb h (nth i orig 0%nat) H1h Hlt2). }
          lia. }
        exact (IH i (S j) _ Hjlx Hsubx Hli Hne H1i H1L Htot Haccx).
      * (* n_i ≤ h + 去重 ⟹ n_i < h：加 pair (n_i, h) *)
        assert (Hge : Nat.le (nth i orig 0%nat) h) by (apply Nat.ltb_ge; exact Hlt).
        assert (Hgt : Nat.lt (nth i orig 0%nat) h).
        { destruct (proj1 (Nat.lt_eq_cases (nth i orig 0%nat) h) Hge) as [Hltx | Heq].
          - exact Hltx.
          - exfalso. apply Hhne. symmetry. exact Heq. }
        assert (Haccx : Nat.lt 0 (snd (FrameCheckInstance.frac_add num den
                          (FrameCheckInstance.pair_num (nth i orig 0%nat) h)
                          (FrameCheckInstance.pair_den (nth i orig 0%nat) h)))).
        { cbn [FrameCheckInstance.frac_add snd].
          apply (proj2 (Nat2Z.inj_lt 0 (den * FrameCheckInstance.pair_den (nth i orig 0%nat) h))).
          rewrite Nat2Z.inj_mul.
          assert (HdZ : (0 < Z.of_nat den)%Z)
            by (apply (proj1 (Nat2Z.inj_lt 0 den)); exact Hacc).
          assert (HpdZ : (0 < Z.of_nat (FrameCheckInstance.pair_den (nth i orig 0%nat) h))%Z).
          { apply (proj1 (Nat2Z.inj_lt 0 (FrameCheckInstance.pair_den (nth i orig 0%nat) h))).
            apply Nat.lt_le_trans with (m := 2%nat).
            - apply Nat.leb_le. vm_compute. reflexivity.
            - exact (z3b_pair_den_lb (nth i orig 0%nat) h H1i Hgt). }
          lia. }
        exact (IH i (S j) _ Hjlx Hsubx Hli Hne H1i H1L Htot Haccx).
Qed.

(* —— Phase E2：行和支配基础件（幂单调 / 元素下界 / 去重 / E≤SP / 融合）—— *)

Lemma z3b_bands_elem_ge1 : forall (n0 a : nat), Nat.le 2 n0 ->
  Nat.le 1 (n0 * 8 ^ a).
Proof.
  intros n0 a Hn0.
  apply (Nat.mul_le_mono 1 n0 1 (8 ^ a)).
  - apply Nat.le_trans with (m := 2%nat);
      [apply Nat.leb_le; vm_compute; reflexivity | exact Hn0].
  - rewrite <- (Nat.pow_0_r 8). apply Nat.pow_le_mono_r.
    + intros Hc; discriminate Hc.
    + apply Nat.le_0_l.
Qed.

Lemma z3b_bands_pow_lt : forall (n0 a b : nat), Nat.le 2 n0 -> Nat.lt a b ->
  Nat.lt (n0 * 8 ^ a) (n0 * 8 ^ b).
Proof.
  intros n0 a b Hn0 Hab.
  replace (n0 * 8 ^ b)%nat with ((n0 * 8 ^ a) * 8 ^ (b - a))%nat
    by (rewrite <- (Nat.mul_assoc n0 (8 ^ a) (8 ^ (b - a)));
        rewrite <- (Nat.pow_add_r 8 a (b - a)); f_equal;
        rewrite (Nat.add_comm a (b - a)); f_equal;
        apply (Nat.sub_add a b (Nat.lt_le_incl a b Hab))).
  apply z3b_n_lt_nq8.
  - apply (z3b_bands_elem_ge1 n0 a Hn0).
  - apply (proj2 (Nat2Z.inj_le 1 (b - a))).
    rewrite (Nat2Z.inj_sub b a (Nat.lt_le_incl a b Hab)).
    change (Z.of_nat 1) with 1%Z.
    assert (HZlt : (Z.of_nat a < Z.of_nat b)%Z)
      by (apply (proj1 (Nat2Z.inj_lt a b)); exact Hab).
    lia.
Qed.

Lemma z3b_bands_nth_ne : forall (n0 m k i : nat), Nat.le 2 n0 ->
  Nat.lt k m -> Nat.lt i m -> k <> i ->
  nth k (z3b_bands n0 m) 0%nat <> nth i (z3b_bands n0 m) 0%nat.
Proof.
  intros n0 m k i Hn0 Hk Hi Hki.
  rewrite (z3b_bands_nth n0 m k Hk).
  rewrite (z3b_bands_nth n0 m i Hi).
  destruct (Nat.lt_trichotomy k i) as [Hc | [Heq | Hc]].
  - apply Nat.lt_neq.
    apply (z3b_bands_pow_lt n0 k i Hn0 Hc).
  - exfalso. exact (Hki Heq).
  - symmetry. apply Nat.lt_neq.
    apply (z3b_bands_pow_lt n0 i k Hn0 Hc).
Qed.

Lemma z3b_bands_pair_cmp : forall (n0 m i e : nat), Nat.le 2 n0 -> Nat.lt i m ->
  In e (z3b_bands n0 m) -> e <> nth i (z3b_bands n0 m) 0%nat ->
  Nat.lt e (nth i (z3b_bands n0 m) 0%nat) \/ Nat.lt (nth i (z3b_bands n0 m) 0%nat) e.
Proof.
  intros n0 m i e Hn0 Hi Hin Hne.
  unfold z3b_bands in Hin.
  apply in_map_iff in Hin.
  destruct Hin as [k [Hk Hin]].
  apply in_seq in Hin. destruct Hin as [_ Hlt].
  rewrite (z3b_bands_nth n0 m i Hi) in Hne |- *.
  destruct (Nat.lt_trichotomy k i) as [Hc | [Heq | Hc]].
  - left. rewrite <- Hk. apply (z3b_bands_pow_lt n0 k i Hn0 Hc).
  - exfalso. apply Hne. rewrite <- Hk. do 2 f_equal. exact Heq.
  - right. rewrite <- Hk. apply (z3b_bands_pow_lt n0 i k Hn0 Hc).
Qed.

(* Qeq→Qle 桥（Qplus_comm/assoc 是 Qeq 值——次序翻转后回 Qle 的标准口） *)
Lemma z3b_Qeq_le : forall x y : Q, Qeq x y -> Qle x y.
Proof.
  intros x y H. unfold Qle, Qeq in *.
  cbn [Qnum Qden] in *.
  rewrite H. apply Z.le_refl.
Qed.

Lemma z3b_E_le_SP : forall t : nat, Nat.le 1 t -> Qle (z3b_E t) (z3b_SP t).
Proof.
  intros t Ht. destruct t as [| tx].
  - exfalso. exact (Nat.nle_succ_diag_l 0 Ht).
  - cbn [z3b_SP].
    apply (Qle_trans (z3b_E (S tx)) (z3b_E (S tx) + z3b_SP tx)).
    + apply (z3b_Qle_add_r (z3b_E (S tx)) (z3b_SP tx)). apply z3b_SP_ge0.
    + apply z3b_Qeq_le.
      apply (Qplus_comm (z3b_E (S tx)) (z3b_SP tx)).
Qed.

(* 泛化微引理：firstn 保位取值（k < n） *)
Lemma z3b_nth_firstn : forall (n k : nat) (l : list nat) (d : nat),
  Nat.lt k n -> nth k (firstn n l) d = nth k l d.
Proof.
  intros n. induction n as [| n IH]; intros k l d Hk.
  - inversion Hk.
  - destruct l as [| a tl].
    + reflexivity.
    + destruct k as [| kx].
      * reflexivity.
      * cbn [firstn nth]. apply (IH kx tl d).
        apply (proj2 (Nat.succ_lt_mono kx n)); exact Hk.
Qed.

(* 融合：aux 对拼接表的两次累加 = 一次累加（左相位/右相位拆分的桥） *)
Lemma z3b_aux_fusion : forall (L1 L2 orig : list nat) (i : nat) (acc : FrameCheckInstance.nat_pair) (j : nat),
  FrameCheckInstance.row_sum_frac_aux (L1 ++ L2)%list orig i acc j =
  FrameCheckInstance.row_sum_frac_aux L2 orig i
    (FrameCheckInstance.row_sum_frac_aux L1 orig i acc j) (j + length L1).
Proof.
  intros L1. induction L1 as [| h tl IH]; intros L2 orig i acc j.
  - cbn [Datatypes.app Datatypes.length FrameCheckInstance.row_sum_frac_aux].
    rewrite Nat.add_0_r. reflexivity.
  - destruct acc as [num den].
    cbn [Datatypes.app Datatypes.length FrameCheckInstance.row_sum_frac_aux].
    replace (j + S (length tl))%nat with (S j + length tl)%nat
      by (rewrite Nat.add_succ_r; rewrite Nat.add_succ_l; reflexivity).
    destruct (Nat.eqb j i) eqn:Hji.
    + exact (IH L2 orig i (num, den) (S j)).
    + destruct (Nat.ltb h (nth i orig 0%nat)); exact (IH L2 orig i _ (S j)).
Qed.

(* —— E202 换形引理族补遗（Ring 直证，禁跨形状 exact）—— *)

(* Qeq→Qle 的次序传导（Qeq 改右元） *)
Lemma z3b_Qle_Qeq_r : forall x y z : Q, Qeq y z -> Qle x y -> Qle x z.
Proof.
  intros x y z Hyz Hxy.
  apply (Qle_trans x y z Hxy).
  apply z3b_Qeq_le. exact Hyz.
Qed.

Lemma z3b_Qplus_swap_r : forall (a E S : Q), Qeq ((a + E)%Q + S) (a + (S + E))%Q.
Proof.
  intros a E S.
  apply (Qeq_trans _ (a + (E + S))%Q).
  - apply Qeq_sym. apply (Qplus_assoc a E S).
  - apply (Qplus_comp a a (Qeq_refl a) (E + S)%Q (S + E)%Q (Qplus_comm E S)).
Qed.

Lemma z3b_Qplus_swap_l : forall (a E S : Q), Qeq ((a + E)%Q + S) ((a + S)%Q + E)%Q.
Proof.
  intros a E S.
  apply (Qeq_trans _ (a + (E + S))%Q).
  - apply Qeq_sym. apply (Qplus_assoc a E S).
  - apply (Qeq_trans _ (a + (S + E))%Q).
    + apply (Qplus_comp a a (Qeq_refl a) (E + S)%Q (S + E)%Q (Qplus_comm E S)).
    + apply (Qplus_assoc a S E).
Qed.

(* ★ E2 左相位：枢轴左侧（firstn i 部分）按消耗序（大距在先）累加，
   预算恰为 SP c（c = 剩余左元素数，j + c = i）——纯递减 SP 形，无 Q 减法 *)
Lemma z3b_left_le : forall (c : nat) (L orig : list nat) (i j N : nat)
  (acc : FrameCheckInstance.nat_pair),
  length L = c ->
  j + c = i ->
  nth i orig 0%nat = N ->
  (forall k : nat, Nat.lt k c -> N = (nth k L 0%nat * 8 ^ (i - (j + k)))%nat) ->
  (forall k : nat, Nat.lt k c -> Nat.le 1 (nth k L 0%nat)) ->
  Nat.lt 0 (snd acc) ->
  Qle (z3b_accQ (FrameCheckInstance.row_sum_frac_aux L orig i acc j))
      (z3b_accQ acc + z3b_SP c)%Q.
Proof.
  intros c. induction c as [| c IH]; intros L orig i j N acc Hlen Hjc Hpi HR Hge Hacc.
  - destruct L as [| a tl].
    + cbn [FrameCheckInstance.row_sum_frac_aux z3b_SP].
      rewrite Qplus_0_r. apply Qle_refl.
    + cbn [length] in Hlen. discriminate Hlen.
  - destruct L as [| h tl].
    + cbn [length] in Hlen. discriminate Hlen.
    + destruct acc as [num den]. cbn [snd] in Hacc.
      cbn [FrameCheckInstance.row_sum_frac_aux].
      assert (Hlenx : length tl = c) by (cbn [length] in Hlen; injection Hlen; intros Heq; exact Heq).
      assert (Hjcx : S j + c = i).
      { replace (S j + c)%nat with (j + S c)%nat
          by (rewrite Nat.add_succ_l; rewrite Nat.add_succ_r; reflexivity).
        exact Hjc. }
      assert (HRx : forall k : nat, Nat.lt k c ->
                N = (nth k tl 0%nat * 8 ^ (i - (S j + k)))%nat).
      { intros k Hk.
        replace (S j + k)%nat with (j + S k)%nat
          by (rewrite Nat.add_succ_r; rewrite Nat.add_succ_l; reflexivity).
        exact (HR (S k) (proj1 (Nat.succ_lt_mono k c) Hk)). }
      assert (Hgex : forall k : nat, Nat.lt k c -> Nat.le 1 (nth k tl 0%nat)).
      { intros k Hk. exact (Hge (S k) (proj1 (Nat.succ_lt_mono k c) Hk)). }
      assert (H1h : Nat.le 1 h) by (exact (Hge 0 (Nat.lt_0_succ c))).
      assert (HZ : (Z.of_nat j + Z.of_nat (S c) = Z.of_nat i)%Z).
      { rewrite <- (proj2 (Nat2Z.inj_iff (j + S c) i) Hjc).
        rewrite Nat2Z.inj_add. rewrite Nat2Z.inj_succ. reflexivity. }
      assert (Hjix : Nat.lt j i) by (apply (proj2 (Nat2Z.inj_lt j i)); lia).
      assert (Hjni : j <> i).
      { intros He. rewrite He in Hjix. exact (Nat.lt_irrefl i Hjix). }
      assert (HD : (i - j)%nat = S c).
      { assert (Hji_le : Nat.le j i) by (apply (proj2 (Nat2Z.inj_le j i)); lia).
        assert (Hsa : ((i - j) + j)%nat = i) by (apply Nat.sub_add; exact Hji_le).
        apply (proj1 (Nat.add_cancel_r (i - j)%nat (S c)%nat j)).
        rewrite Hsa. rewrite <- Hjc. rewrite (Nat.add_comm (S c) j). reflexivity. }
      assert (HN0 : N = (h * 8 ^ S c)%nat).
      { rewrite (HR 0 (Nat.lt_0_succ c)). rewrite Nat.add_0_r. rewrite HD. reflexivity. }
      assert (HhN : Nat.lt h N).
      { rewrite HN0. apply z3b_n_lt_nq8.
        - exact H1h.
        - apply Nat.leb_le. vm_compute. reflexivity. }
      assert (HN1 : Nat.le 1 N).
      { rewrite HN0. apply (Nat.mul_le_mono 1 h 1 (8 ^ S c)).
        - exact H1h.
        - rewrite <- (Nat.pow_0_r 8). apply Nat.pow_le_mono_r.
          + intros Hc2; discriminate Hc2.
          + apply Nat.le_0_l. }
      (* 路由：j ≠ i（左相位 j < i）⟹ else 分支；h < N ⟹ ltb 真 ⟹ 加 pair (h, N) *)
      rewrite Hpi.
      destruct (Nat.eqb j i) eqn:Hji.
      * exfalso. exact (Hjni (proj1 (Nat.eqb_eq j i) Hji)).
      * destruct (Nat.ltb h N) eqn:Hltb.
        -- assert (Hpn : Nat.lt 0 (FrameCheckInstance.pair_num h N)).
        { unfold FrameCheckInstance.pair_num.
          apply (proj2 (Nat2Z.inj_lt 0 (h * N)%nat)).
          rewrite Nat2Z.inj_mul.
          assert (HZ1 : (0 < Z.of_nat h)%Z)
            by (apply (proj1 (Nat2Z.inj_lt 0 h)); exact H1h).
          assert (HZ2 : (0 < Z.of_nat N)%Z).
          { apply (proj1 (Nat2Z.inj_lt 0 N)).
            apply Nat.lt_le_trans with (m := 1%nat);
              [apply Nat.leb_le; vm_compute; reflexivity | exact HN1]. }
          lia. }
        assert (Hpd : Nat.lt 0 (FrameCheckInstance.pair_den h N)).
        { apply Nat.lt_le_trans with (m := 2%nat); [apply Nat.lt_0_succ |].
          apply z3b_pair_den_lb; [exact H1h | exact HhN]. }
        assert (Haccx : Nat.lt 0 (snd (FrameCheckInstance.frac_add num den
                          (FrameCheckInstance.pair_num h N)
                          (FrameCheckInstance.pair_den h N)))).
        { cbn [FrameCheckInstance.frac_add snd].
          apply (proj2 (Nat2Z.inj_lt 0 (den * FrameCheckInstance.pair_den h N))).
          rewrite Nat2Z.inj_mul.
          assert (HZd : (0 < Z.of_nat den)%Z)
            by (apply (proj1 (Nat2Z.inj_lt 0 den)); exact Hacc).
          assert (HZp : (0 < Z.of_nat (FrameCheckInstance.pair_den h N))%Z)
            by (apply (proj1 (Nat2Z.inj_lt 0 (FrameCheckInstance.pair_den h N)));
                exact Hpd).
          lia. }
        assert (Henv : Qle (z3b_pf h N) (z3b_E (S c))).
        { unfold z3b_pf. rewrite HN0.
          apply Qle_bool_imp_le. apply z3b_env_uni.
          - exact H1h.
          - apply Nat.leb_le. vm_compute. reflexivity. }
        assert (HA : Qle (z3b_accQ (FrameCheckInstance.frac_add num den
                          (FrameCheckInstance.pair_num h N)
                          (FrameCheckInstance.pair_den h N)))
                         (z3b_accQ (num, den) + z3b_E (S c))%Q).
        { apply (z3b_Qeq_le_r _ _ _ (z3b_frac_add_Qeq num den
              (FrameCheckInstance.pair_num h N) (FrameCheckInstance.pair_den h N)
              Hacc Hpn Hpd)).
          apply Qplus_le_compat.
          - apply Qle_refl.
          exact Henv. }
        cbn [z3b_SP].
        eapply Qle_trans.
        ++ exact (IH tl orig i (S j) N (FrameCheckInstance.frac_add num den
                (FrameCheckInstance.pair_num h N) (FrameCheckInstance.pair_den h N))
                Hlenx Hjcx Hpi HRx Hgex Haccx).
        ++ eapply Qle_trans.
           ** eapply Qplus_le_compat.
              -- exact HA.
              -- apply Qle_refl.
           ** apply (z3b_Qle_Qeq_r _ _ _ (z3b_Qplus_swap_r (z3b_accQ (num, den))
                   (z3b_E (S c)) (z3b_SP c))).
              apply Qle_refl.
        -- exfalso.
           assert (Hge2 : Nat.le N h) by (apply Nat.ltb_ge; exact Hltb).
           exact (Nat.lt_irrefl N (Nat.le_lt_trans _ _ _ Hge2 HhN)).
Qed.

(* ★ E2 右相位：枢轴右侧按距离序（t 偏移起）累加，
   不变式 accQ(aux) + SP t ≤ accQ acc + SP (t + c)——E (S t) 头部相消 *)
Lemma z3b_right_le : forall (c : nat) (R orig : list nat) (i j0 t N : nat)
  (acc : FrameCheckInstance.nat_pair),
  length R = c ->
  nth i orig 0%nat = N ->
  (forall k : nat, Nat.lt k c -> nth k R 0%nat = (N * 8 ^ (S t + k))%nat) ->
  Nat.le 1 N ->
  Nat.lt i j0 ->
  Nat.lt 0 (snd acc) ->
  Qle (z3b_accQ (FrameCheckInstance.row_sum_frac_aux R orig i acc j0) + z3b_SP t)
      (z3b_accQ acc + z3b_SP (t + c))%Q.
Proof.
  intros c. induction c as [| c IH]; intros R orig i j0 t N acc Hlen Hpi HR HN Hlt Hacc.
  - destruct R as [| a tl].
    + cbn [FrameCheckInstance.row_sum_frac_aux].
      rewrite Nat.add_0_r. apply Qle_refl.
    + cbn [length] in Hlen. discriminate Hlen.
  - destruct R as [| h tl].
    + cbn [length] in Hlen. discriminate Hlen.
    + destruct acc as [num den]. cbn [snd] in Hacc.
      cbn [FrameCheckInstance.row_sum_frac_aux].
      assert (Hlenx : length tl = c) by (cbn [length] in Hlen; injection Hlen; intros Heq; exact Heq).
      assert (HRx : forall k : nat, Nat.lt k c ->
                nth k tl 0%nat = (N * 8 ^ (S (S t) + k))%nat).
      { intros k Hk.
        replace (S (S t) + k)%nat with (S t + S k)%nat
          by (rewrite ?Nat.add_succ_r; rewrite ?Nat.add_succ_l; reflexivity).
        exact (HR (S k) (proj1 (Nat.succ_lt_mono k c) Hk)). }
      assert (Hh0 : h = (N * 8 ^ S t)%nat).
      { transitivity (nth 0 (h :: tl) 0%nat).
        - reflexivity.
        - rewrite (HR 0 (Nat.lt_0_succ c)). rewrite Nat.add_0_r. reflexivity. }
      assert (HhN : Nat.lt N h).
      { rewrite Hh0. apply z3b_n_lt_nq8.
        - exact HN.
        - apply Nat.leb_le. vm_compute. reflexivity. }
      assert (H1h : Nat.le 1 h).
      { rewrite Hh0. apply (Nat.mul_le_mono 1 N 1 (8 ^ S t)).
        - exact HN.
        - rewrite <- (Nat.pow_0_r 8). apply Nat.pow_le_mono_r.
          + intros Hc2; discriminate Hc2.
          + apply Nat.le_0_l. }
      assert (Hjni0 : j0 <> i).
      { intros He. rewrite He in Hlt. exact (Nat.lt_irrefl i Hlt). }
      (* 路由：j0 ≠ i（右相位 i < j0）⟹ else 分支；N < h ⟹ ltb 假 ⟹ 加 pair (N, h) *)
      rewrite Hpi.
      destruct (Nat.eqb j0 i) eqn:Hji.
      * exfalso. exact (Hjni0 (proj1 (Nat.eqb_eq j0 i) Hji)).
      * destruct (Nat.ltb h N) eqn:Hltb.
        -- exfalso.
           assert (Hlt2 : Nat.lt h N) by (apply Nat.ltb_lt; exact Hltb).
           exact (Nat.lt_irrefl N (Nat.lt_trans _ _ _ HhN Hlt2)).
        -- assert (Hpn : Nat.lt 0 (FrameCheckInstance.pair_num N h)).
        { unfold FrameCheckInstance.pair_num.
          apply (proj2 (Nat2Z.inj_lt 0 (N * h)%nat)).
          rewrite Nat2Z.inj_mul.
          assert (HZ1 : (0 < Z.of_nat N)%Z)
            by (apply (proj1 (Nat2Z.inj_lt 0 N)); exact HN).
          assert (HZ2 : (0 < Z.of_nat h)%Z)
            by (apply (proj1 (Nat2Z.inj_lt 0 h)); exact H1h).
          lia. }
        assert (Hpd : Nat.lt 0 (FrameCheckInstance.pair_den N h)).
        { apply Nat.lt_le_trans with (m := 2%nat); [apply Nat.lt_0_succ |].
          apply z3b_pair_den_lb; [exact HN | exact HhN]. }
        assert (Haccx : Nat.lt 0 (snd (FrameCheckInstance.frac_add num den
                          (FrameCheckInstance.pair_num N h)
                          (FrameCheckInstance.pair_den N h)))).
        { cbn [FrameCheckInstance.frac_add snd].
          apply (proj2 (Nat2Z.inj_lt 0 (den * FrameCheckInstance.pair_den N h))).
          rewrite Nat2Z.inj_mul.
          assert (HZd : (0 < Z.of_nat den)%Z)
            by (apply (proj1 (Nat2Z.inj_lt 0 den)); exact Hacc).
          assert (HZp : (0 < Z.of_nat (FrameCheckInstance.pair_den N h))%Z)
            by (apply (proj1 (Nat2Z.inj_lt 0 (FrameCheckInstance.pair_den N h)));
                exact Hpd).
          lia. }
        assert (Henv : Qle (z3b_pf N h) (z3b_E (S t))).
        { unfold z3b_pf. rewrite Hh0.
          apply Qle_bool_imp_le. apply z3b_env_uni.
          - exact HN.
          - apply Nat.leb_le. vm_compute. reflexivity. }
        assert (HA : Qle (z3b_accQ (FrameCheckInstance.frac_add num den
                          (FrameCheckInstance.pair_num N h)
                          (FrameCheckInstance.pair_den N h)))
                         (z3b_accQ (num, den) + z3b_E (S t))%Q).
        { apply (z3b_Qeq_le_r _ _ _ (z3b_frac_add_Qeq num den
              (FrameCheckInstance.pair_num N h) (FrameCheckInstance.pair_den N h)
              Hacc Hpn Hpd)).
          apply Qplus_le_compat.
          - apply Qle_refl.
          exact Henv. }
        assert (Hlt1 : Nat.lt i (S j0))
          by (apply Nat.lt_succ_r; apply Nat.lt_le_incl; exact Hlt).
        assert (Hstep : Qle (z3b_accQ (FrameCheckInstance.row_sum_frac_aux tl orig i
                            (FrameCheckInstance.frac_add num den
                              (FrameCheckInstance.pair_num N h)
                              (FrameCheckInstance.pair_den N h)) (S j0))
                            + z3b_SP (S t))%Q
                            ((z3b_accQ (num, den) + z3b_E (S t))%Q
                             + z3b_SP (S t + c))%Q).
        { eapply Qle_trans.
          - exact (IH tl orig i (S j0) (S t) N (FrameCheckInstance.frac_add num den
                  (FrameCheckInstance.pair_num N h) (FrameCheckInstance.pair_den N h))
                  Hlenx Hpi HRx HN Hlt1 Haccx).
          - eapply Qplus_le_compat.
            + exact HA.
            + apply Qle_refl. }
        replace (z3b_SP (S t))%Q with (z3b_SP t + z3b_E (S t))%Q in Hstep
          by reflexivity.
        (* 消去头部 E (S t)：先两侧换形到同加 E 形，再 Qplus_le_l 消去 *)
        assert (HA2 : Qle (((z3b_accQ (FrameCheckInstance.row_sum_frac_aux tl orig i
                          (FrameCheckInstance.frac_add num den
                            (FrameCheckInstance.pair_num N h)
                            (FrameCheckInstance.pair_den N h)) (S j0)))
                         + z3b_SP t)%Q + z3b_E (S t))%Q
                        ((z3b_accQ (num, den) + z3b_SP (S t + c))%Q
                         + z3b_E (S t))%Q).
        { apply (z3b_Qle_Qeq_r _ _ _
            (z3b_Qplus_swap_l (z3b_accQ (num, den)) (z3b_E (S t)) (z3b_SP (S t + c)))).
          apply (z3b_Qeq_le_r _ _ _
            (z3b_Qplus_assoc_r (z3b_accQ
              (FrameCheckInstance.row_sum_frac_aux tl orig i
                (FrameCheckInstance.frac_add num den
                  (FrameCheckInstance.pair_num N h)
                  (FrameCheckInstance.pair_den N h)) (S j0)))
              (z3b_SP t) (z3b_E (S t)))).
          exact Hstep. }
        replace (t + S c)%nat with (S t + c)%nat
          by (rewrite Nat.add_succ_r; rewrite Nat.add_succ_l; reflexivity).
        apply (Qplus_le_l _ _ (z3b_E (S t))).
        exact HA2.
Qed.

(* —— E125 无 vm_compute 预算封口 v3：Z 字面量改写 + Qeq 传导链（沙箱 mini4 验证配方）—— *)
Lemma z3b_sqrt_Z : forall (x s : nat) (zs : Z),
  Z.of_nat s = zs ->
  (zs * zs <= Z.of_nat x < Z.succ zs * Z.succ zs)%Z ->
  Z.of_nat (Nat.sqrt x) = zs.
Proof.
  intros x s zs Heq Hb. destruct Hb as [Hlb Hub].
  assert (Hs : Nat.sqrt x = s).
  { apply Nat.sqrt_unique.
    split.
    - apply (proj2 (Nat2Z.inj_le (s * s) x)).
      rewrite !Nat2Z.inj_mul.
      rewrite Heq. exact Hlb.
    - apply (proj2 (Nat2Z.inj_lt x (S s * S s)%nat)).
      rewrite Nat2Z.inj_mul. rewrite !Nat2Z.inj_succ. rewrite Heq. exact Hub. }
  rewrite Hs. exact Heq.
Qed.

Lemma z3b_cap_4_5 :
  Qle ((z3b_SP 8 + z3b_E 9) + z3b_E 9
       + ((z3b_SP 8 + z3b_E 9) + z3b_E 9)) (Qmake 4 5).
Proof.
  assert (Hp1 : Z.of_nat (8 ^ 1)%nat = 8%Z) by (rewrite Nat2Z.inj_pow; reflexivity).
  assert (Hp2 : Z.of_nat (8 ^ 2)%nat = 64%Z) by (rewrite Nat2Z.inj_pow; reflexivity).
  assert (Hp3 : Z.of_nat (8 ^ 3)%nat = 512%Z) by (rewrite Nat2Z.inj_pow; reflexivity).
  assert (Hp4 : Z.of_nat (8 ^ 4)%nat = 4096%Z) by (rewrite Nat2Z.inj_pow; reflexivity).
  assert (Hp5 : Z.of_nat (8 ^ 5)%nat = 32768%Z) by (rewrite Nat2Z.inj_pow; reflexivity).
  assert (Hp6 : Z.of_nat (8 ^ 6)%nat = 262144%Z) by (rewrite Nat2Z.inj_pow; reflexivity).
  assert (Hp7 : Z.of_nat (8 ^ 7)%nat = 2097152%Z) by (rewrite Nat2Z.inj_pow; reflexivity).
  assert (Hp8 : Z.of_nat (8 ^ 8)%nat = 16777216%Z) by (rewrite Nat2Z.inj_pow; reflexivity).
  assert (Hp9 : Z.of_nat (8 ^ 9)%nat = 134217728%Z) by (rewrite Nat2Z.inj_pow; reflexivity).
  assert (Hs1 : Z.of_nat (Nat.sqrt (8 ^ 1)%nat) = 2%Z).
  { assert (Hpre1 : Z.of_nat 2 = 2%Z) by reflexivity.
    assert (Hb1 : (2 * 2 <= Z.of_nat (8 ^ 1) < Z.succ 2 * Z.succ 2)%Z).
    { rewrite Nat2Z.inj_pow.
      replace (8 ^ Z.of_nat 1)%Z with 8%Z by reflexivity.
      lia. }
    exact (z3b_sqrt_Z (8 ^ 1)%nat 2%nat 2%Z Hpre1 Hb1). }
  assert (Hs2 : Z.of_nat (Nat.sqrt (8 ^ 2)%nat) = 8%Z).
  { assert (Hpre2 : Z.of_nat 8 = 8%Z) by reflexivity.
    assert (Hb2 : (8 * 8 <= Z.of_nat (8 ^ 2) < Z.succ 8 * Z.succ 8)%Z).
    { rewrite Nat2Z.inj_pow.
      replace (8 ^ Z.of_nat 2)%Z with 64%Z by reflexivity.
      lia. }
    exact (z3b_sqrt_Z (8 ^ 2)%nat 8%nat 8%Z Hpre2 Hb2). }
  assert (Hs3 : Z.of_nat (Nat.sqrt (8 ^ 3)%nat) = 22%Z).
  { assert (Hpre3 : Z.of_nat 22 = 22%Z) by reflexivity.
    assert (Hb3 : (22 * 22 <= Z.of_nat (8 ^ 3) < Z.succ 22 * Z.succ 22)%Z).
    { rewrite Nat2Z.inj_pow.
      replace (8 ^ Z.of_nat 3)%Z with 512%Z by reflexivity.
      lia. }
    exact (z3b_sqrt_Z (8 ^ 3)%nat 22%nat 22%Z Hpre3 Hb3). }
  assert (Hs4 : Z.of_nat (Nat.sqrt (8 ^ 4)%nat) = 64%Z).
  { assert (Hpre4 : Z.of_nat 64 = 64%Z) by reflexivity.
    assert (Hb4 : (64 * 64 <= Z.of_nat (8 ^ 4) < Z.succ 64 * Z.succ 64)%Z).
    { rewrite Nat2Z.inj_pow.
      replace (8 ^ Z.of_nat 4)%Z with 4096%Z by reflexivity.
      lia. }
    exact (z3b_sqrt_Z (8 ^ 4)%nat 64%nat 64%Z Hpre4 Hb4). }
  assert (Hs5 : Z.of_nat (Nat.sqrt (8 ^ 5)%nat) = 181%Z).
  { assert (Hpre5 : Z.of_nat 181 = 181%Z) by reflexivity.
    assert (Hb5 : (181 * 181 <= Z.of_nat (8 ^ 5) < Z.succ 181 * Z.succ 181)%Z).
    { rewrite Nat2Z.inj_pow.
      replace (8 ^ Z.of_nat 5)%Z with 32768%Z by reflexivity.
      lia. }
    exact (z3b_sqrt_Z (8 ^ 5)%nat 181%nat 181%Z Hpre5 Hb5). }
  assert (Hs6 : Z.of_nat (Nat.sqrt (8 ^ 6)%nat) = 512%Z).
  { assert (Hpre6 : Z.of_nat 512 = 512%Z) by reflexivity.
    assert (Hb6 : (512 * 512 <= Z.of_nat (8 ^ 6) < Z.succ 512 * Z.succ 512)%Z).
    { rewrite Nat2Z.inj_pow.
      replace (8 ^ Z.of_nat 6)%Z with 262144%Z by reflexivity.
      lia. }
    exact (z3b_sqrt_Z (8 ^ 6)%nat 512%nat 512%Z Hpre6 Hb6). }
  assert (Hs7 : Z.of_nat (Nat.sqrt (8 ^ 7)%nat) = 1448%Z).
  { assert (Hpre7 : Z.of_nat 1448 = 1448%Z) by reflexivity.
    assert (Hb7 : (1448 * 1448 <= Z.of_nat (8 ^ 7) < Z.succ 1448 * Z.succ 1448)%Z).
    { rewrite Nat2Z.inj_pow.
      replace (8 ^ Z.of_nat 7)%Z with 2097152%Z by reflexivity.
      lia. }
    exact (z3b_sqrt_Z (8 ^ 7)%nat 1448%nat 1448%Z Hpre7 Hb7). }
  assert (Hs8 : Z.of_nat (Nat.sqrt (8 ^ 8)%nat) = 4096%Z).
  { assert (Hpre8 : Z.of_nat 4096 = 4096%Z) by reflexivity.
    assert (Hb8 : (4096 * 4096 <= Z.of_nat (8 ^ 8) < Z.succ 4096 * Z.succ 4096)%Z).
    { rewrite Nat2Z.inj_pow.
      replace (8 ^ Z.of_nat 8)%Z with 16777216%Z by reflexivity.
      lia. }
    exact (z3b_sqrt_Z (8 ^ 8)%nat 4096%nat 4096%Z Hpre8 Hb8). }
  assert (Hs9 : Z.of_nat (Nat.sqrt (8 ^ 9)%nat) = 11585%Z).
  { assert (Hpre9 : Z.of_nat 11585 = 11585%Z) by reflexivity.
    assert (Hb9 : (11585 * 11585 <= Z.of_nat (8 ^ 9) < Z.succ 11585 * Z.succ 11585)%Z).
    { rewrite Nat2Z.inj_pow.
      replace (8 ^ Z.of_nat 9)%Z with 134217728%Z by reflexivity.
      lia. }
    exact (z3b_sqrt_Z (8 ^ 9)%nat 11585%nat 11585%Z Hpre9 Hb9). }
  assert (Hd1 : Nat.lt 0 (2 * (8 ^ 1 - 1) * Nat.sqrt (8 ^ 1))%nat).
  { apply (proj2 (Nat2Z.inj_lt 0 (2 * (8 ^ 1 - 1) * Nat.sqrt (8 ^ 1))%nat)).
    rewrite !Nat2Z.inj_mul.
    rewrite (Nat2Z.inj_sub _ _ (z3b_pow8_ge1 1)).
    rewrite Hs1. rewrite Hp1. lia. }
  assert (Hd2 : Nat.lt 0 (2 * (8 ^ 2 - 1) * Nat.sqrt (8 ^ 2))%nat).
  { apply (proj2 (Nat2Z.inj_lt 0 (2 * (8 ^ 2 - 1) * Nat.sqrt (8 ^ 2))%nat)).
    rewrite !Nat2Z.inj_mul.
    rewrite (Nat2Z.inj_sub _ _ (z3b_pow8_ge1 2)).
    rewrite Hs2. rewrite Hp2. lia. }
  assert (Hd3 : Nat.lt 0 (2 * (8 ^ 3 - 1) * Nat.sqrt (8 ^ 3))%nat).
  { apply (proj2 (Nat2Z.inj_lt 0 (2 * (8 ^ 3 - 1) * Nat.sqrt (8 ^ 3))%nat)).
    rewrite !Nat2Z.inj_mul.
    rewrite (Nat2Z.inj_sub _ _ (z3b_pow8_ge1 3)).
    rewrite Hs3. rewrite Hp3. lia. }
  assert (Hd4 : Nat.lt 0 (2 * (8 ^ 4 - 1) * Nat.sqrt (8 ^ 4))%nat).
  { apply (proj2 (Nat2Z.inj_lt 0 (2 * (8 ^ 4 - 1) * Nat.sqrt (8 ^ 4))%nat)).
    rewrite !Nat2Z.inj_mul.
    rewrite (Nat2Z.inj_sub _ _ (z3b_pow8_ge1 4)).
    rewrite Hs4. rewrite Hp4. lia. }
  assert (Hd5 : Nat.lt 0 (2 * (8 ^ 5 - 1) * Nat.sqrt (8 ^ 5))%nat).
  { apply (proj2 (Nat2Z.inj_lt 0 (2 * (8 ^ 5 - 1) * Nat.sqrt (8 ^ 5))%nat)).
    rewrite !Nat2Z.inj_mul.
    rewrite (Nat2Z.inj_sub _ _ (z3b_pow8_ge1 5)).
    rewrite Hs5. rewrite Hp5. lia. }
  assert (Hd6 : Nat.lt 0 (2 * (8 ^ 6 - 1) * Nat.sqrt (8 ^ 6))%nat).
  { apply (proj2 (Nat2Z.inj_lt 0 (2 * (8 ^ 6 - 1) * Nat.sqrt (8 ^ 6))%nat)).
    rewrite !Nat2Z.inj_mul.
    rewrite (Nat2Z.inj_sub _ _ (z3b_pow8_ge1 6)).
    rewrite Hs6. rewrite Hp6. lia. }
  assert (Hd7 : Nat.lt 0 (2 * (8 ^ 7 - 1) * Nat.sqrt (8 ^ 7))%nat).
  { apply (proj2 (Nat2Z.inj_lt 0 (2 * (8 ^ 7 - 1) * Nat.sqrt (8 ^ 7))%nat)).
    rewrite !Nat2Z.inj_mul.
    rewrite (Nat2Z.inj_sub _ _ (z3b_pow8_ge1 7)).
    rewrite Hs7. rewrite Hp7. lia. }
  assert (Hd8 : Nat.lt 0 (2 * (8 ^ 8 - 1) * Nat.sqrt (8 ^ 8))%nat).
  { apply (proj2 (Nat2Z.inj_lt 0 (2 * (8 ^ 8 - 1) * Nat.sqrt (8 ^ 8))%nat)).
    rewrite !Nat2Z.inj_mul.
    rewrite (Nat2Z.inj_sub _ _ (z3b_pow8_ge1 8)).
    rewrite Hs8. rewrite Hp8. lia. }
  assert (Hd9 : Nat.lt 0 (2 * (8 ^ 9 - 1) * Nat.sqrt (8 ^ 9))%nat).
  { apply (proj2 (Nat2Z.inj_lt 0 (2 * (8 ^ 9 - 1) * Nat.sqrt (8 ^ 9))%nat)).
    rewrite !Nat2Z.inj_mul.
    rewrite (Nat2Z.inj_sub _ _ (z3b_pow8_ge1 9)).
    rewrite Hs9. rewrite Hp9. lia. }
  assert (HE1 : Qeq (z3b_E 1) (Qmake 8 28)%Q).
  { unfold z3b_E, Qeq. cbn [Qnum Qden].
    rewrite (z3b_qmk_num (8 ^ 1)%nat (2 * (8 ^ 1 - 1) * Nat.sqrt (8 ^ 1))%nat Hd1).
    rewrite (z3b_qmk_den (8 ^ 1)%nat (2 * (8 ^ 1 - 1) * Nat.sqrt (8 ^ 1))%nat Hd1).
    rewrite (z3b_Zpos_of (2 * (8 ^ 1 - 1) * Nat.sqrt (8 ^ 1))%nat Hd1).
    rewrite !Nat2Z.inj_mul.
    rewrite (Nat2Z.inj_sub _ _ (z3b_pow8_ge1 1)).
    rewrite Hs1. rewrite Hp1. lia. }
  assert (HE2 : Qeq (z3b_E 2) (Qmake 64 1008)%Q).
  { unfold z3b_E, Qeq. cbn [Qnum Qden].
    rewrite (z3b_qmk_num (8 ^ 2)%nat (2 * (8 ^ 2 - 1) * Nat.sqrt (8 ^ 2))%nat Hd2).
    rewrite (z3b_qmk_den (8 ^ 2)%nat (2 * (8 ^ 2 - 1) * Nat.sqrt (8 ^ 2))%nat Hd2).
    rewrite (z3b_Zpos_of (2 * (8 ^ 2 - 1) * Nat.sqrt (8 ^ 2))%nat Hd2).
    rewrite !Nat2Z.inj_mul.
    rewrite (Nat2Z.inj_sub _ _ (z3b_pow8_ge1 2)).
    rewrite Hs2. rewrite Hp2. lia. }
  assert (HE3 : Qeq (z3b_E 3) (Qmake 512 22484)%Q).
  { unfold z3b_E, Qeq. cbn [Qnum Qden].
    rewrite (z3b_qmk_num (8 ^ 3)%nat (2 * (8 ^ 3 - 1) * Nat.sqrt (8 ^ 3))%nat Hd3).
    rewrite (z3b_qmk_den (8 ^ 3)%nat (2 * (8 ^ 3 - 1) * Nat.sqrt (8 ^ 3))%nat Hd3).
    rewrite (z3b_Zpos_of (2 * (8 ^ 3 - 1) * Nat.sqrt (8 ^ 3))%nat Hd3).
    rewrite !Nat2Z.inj_mul.
    rewrite (Nat2Z.inj_sub _ _ (z3b_pow8_ge1 3)).
    rewrite Hs3. rewrite Hp3. lia. }
  assert (HE4 : Qeq (z3b_E 4) (Qmake 4096 524160)%Q).
  { unfold z3b_E, Qeq. cbn [Qnum Qden].
    rewrite (z3b_qmk_num (8 ^ 4)%nat (2 * (8 ^ 4 - 1) * Nat.sqrt (8 ^ 4))%nat Hd4).
    rewrite (z3b_qmk_den (8 ^ 4)%nat (2 * (8 ^ 4 - 1) * Nat.sqrt (8 ^ 4))%nat Hd4).
    rewrite (z3b_Zpos_of (2 * (8 ^ 4 - 1) * Nat.sqrt (8 ^ 4))%nat Hd4).
    rewrite !Nat2Z.inj_mul.
    rewrite (Nat2Z.inj_sub _ _ (z3b_pow8_ge1 4)).
    rewrite Hs4. rewrite Hp4. lia. }
  assert (HE5 : Qeq (z3b_E 5) (Qmake 32768 11861654)%Q).
  { unfold z3b_E, Qeq. cbn [Qnum Qden].
    rewrite (z3b_qmk_num (8 ^ 5)%nat (2 * (8 ^ 5 - 1) * Nat.sqrt (8 ^ 5))%nat Hd5).
    rewrite (z3b_qmk_den (8 ^ 5)%nat (2 * (8 ^ 5 - 1) * Nat.sqrt (8 ^ 5))%nat Hd5).
    rewrite (z3b_Zpos_of (2 * (8 ^ 5 - 1) * Nat.sqrt (8 ^ 5))%nat Hd5).
    rewrite !Nat2Z.inj_mul.
    rewrite (Nat2Z.inj_sub _ _ (z3b_pow8_ge1 5)).
    rewrite Hs5. rewrite Hp5. lia. }
  assert (HE6 : Qeq (z3b_E 6) (Qmake 262144 268434432)%Q).
  { unfold z3b_E, Qeq. cbn [Qnum Qden].
    rewrite (z3b_qmk_num (8 ^ 6)%nat (2 * (8 ^ 6 - 1) * Nat.sqrt (8 ^ 6))%nat Hd6).
    rewrite (z3b_qmk_den (8 ^ 6)%nat (2 * (8 ^ 6 - 1) * Nat.sqrt (8 ^ 6))%nat Hd6).
    rewrite (z3b_Zpos_of (2 * (8 ^ 6 - 1) * Nat.sqrt (8 ^ 6))%nat Hd6).
    rewrite !Nat2Z.inj_mul.
    rewrite (Nat2Z.inj_sub _ _ (z3b_pow8_ge1 6)).
    rewrite Hs6. rewrite Hp6. lia. }
  assert (HE7 : Qeq (z3b_E 7) (Qmake 2097152 6073349296)%Q).
  { unfold z3b_E, Qeq. cbn [Qnum Qden].
    rewrite (z3b_qmk_num (8 ^ 7)%nat (2 * (8 ^ 7 - 1) * Nat.sqrt (8 ^ 7))%nat Hd7).
    rewrite (z3b_qmk_den (8 ^ 7)%nat (2 * (8 ^ 7 - 1) * Nat.sqrt (8 ^ 7))%nat Hd7).
    rewrite (z3b_Zpos_of (2 * (8 ^ 7 - 1) * Nat.sqrt (8 ^ 7))%nat Hd7).
    rewrite !Nat2Z.inj_mul.
    rewrite (Nat2Z.inj_sub _ _ (z3b_pow8_ge1 7)).
    rewrite Hs7. rewrite Hp7. lia. }
  assert (HE8 : Qeq (z3b_E 8) (Qmake 16777216 137438945280)%Q).
  { unfold z3b_E, Qeq. cbn [Qnum Qden].
    rewrite (z3b_qmk_num (8 ^ 8)%nat (2 * (8 ^ 8 - 1) * Nat.sqrt (8 ^ 8))%nat Hd8).
    rewrite (z3b_qmk_den (8 ^ 8)%nat (2 * (8 ^ 8 - 1) * Nat.sqrt (8 ^ 8))%nat Hd8).
    rewrite (z3b_Zpos_of (2 * (8 ^ 8 - 1) * Nat.sqrt (8 ^ 8))%nat Hd8).
    rewrite !Nat2Z.inj_mul.
    rewrite (Nat2Z.inj_sub _ _ (z3b_pow8_ge1 8)).
    rewrite Hs8. rewrite Hp8. lia. }
  assert (HE9 : Qeq (z3b_E 9) (Qmake 134217728 3109824734590)%Q).
  { unfold z3b_E, Qeq. cbn [Qnum Qden].
    rewrite (z3b_qmk_num (8 ^ 9)%nat (2 * (8 ^ 9 - 1) * Nat.sqrt (8 ^ 9))%nat Hd9).
    rewrite (z3b_qmk_den (8 ^ 9)%nat (2 * (8 ^ 9 - 1) * Nat.sqrt (8 ^ 9))%nat Hd9).
    rewrite (z3b_Zpos_of (2 * (8 ^ 9 - 1) * Nat.sqrt (8 ^ 9))%nat Hd9).
    rewrite !Nat2Z.inj_mul.
    rewrite (Nat2Z.inj_sub _ _ (z3b_pow8_ge1 9)).
    rewrite Hs9. rewrite Hp9. lia. }
  assert (HA1 : Qeq (0%Q + z3b_E 1) (Qmake 8 28)%Q).
  { apply (Qeq_trans _ (z3b_E 1)%Q).
    - apply Qplus_0_l.
    - exact HE1. }
  assert (HA2 : Qeq ((0%Q + z3b_E 1) + z3b_E 2) (Qmake 9856 28224)%Q).
  { apply (Qeq_trans _ (Qmake 8 28 + Qmake 64 1008)%Q).
    - exact (Qplus_comp _ _ HA1 _ _ HE2).
    - unfold Qeq. cbn [Qplus Qnum Qden]. reflexivity. }
  assert (HA3 : Qeq ((0%Q + z3b_E 1) + z3b_E 2 + z3b_E 3) (Qmake 236052992 634588416)%Q).
  { apply (Qeq_trans _ (Qmake 9856 28224 + Qmake 512 22484)%Q).
    - exact (Qplus_comp _ _ HA2 _ _ HE3).
    - unfold Qeq. cbn [Qplus Qnum Qden]. reflexivity. }
  assert (HA4 : Qeq ((0%Q + z3b_E 1) + z3b_E 2 + z3b_E 3 + z3b_E 4) (Qmake 126328810438656 332625864130560)%Q).
  { apply (Qeq_trans _ (Qmake 236052992 634588416 + Qmake 4096 524160)%Q).
    - exact (Qplus_comp _ _ HA3 _ _ HE4).
    - unfold Qeq. cbn [Qplus Qnum Qden]. reflexivity. }
  assert (HA5 : Qeq ((0%Q + z3b_E 1) + z3b_E 2 + z3b_E 3 + z3b_E 4 + z3b_E 5) (Qmake 1509368123970755887104 3945492911767713546240)%Q).
  { apply (Qeq_trans _ (Qmake 126328810438656 332625864130560 + Qmake 32768 11861654)%Q).
    - exact (Qplus_comp _ _ HA4 _ _ HE5).
    - unfold Qeq. cbn [Qplus Qnum Qden]. reflexivity. }
  assert (HA6 : Qeq ((0%Q + z3b_E 1) + z3b_E 2 + z3b_E 3 + z3b_E 4 + z3b_E 5 + z3b_E 6) (Qmake 406200662330857876665283903488 1059106148730392301723640135680)%Q).
  { apply (Qeq_trans _ (Qmake 1509368123970755887104 3945492911767713546240 + Qmake 262144 268434432)%Q).
    - exact (Qplus_comp _ _ HA5 _ _ HE6).
    - unfold Qeq. cbn [Qplus Qnum Qden]. reflexivity. }
  assert (HA7 : Qeq ((0%Q + z3b_E 1) + z3b_E 2 + z3b_E 3 + z3b_E 4 + z3b_E 5 + z3b_E 6 + z3b_E 7) (Qmake 2469219613179871643997501158246798327808 6432321582780999379477089404589472481280)%Q).
  { apply (Qeq_trans _ (Qmake 406200662330857876665283903488 1059106148730392301723640135680 + Qmake 2097152 6073349296)%Q).
    - exact (Qplus_comp _ _ HA6 _ _ HE7).
    - unfold Qeq. cbn [Qplus Qnum Qden]. reflexivity. }
  assert (HA8 : Qeq ((0%Q + z3b_E 1) + z3b_E 2 + z3b_E 3 + z3b_E 4 + z3b_E 5 + z3b_E 6 + z3b_E 7 + z3b_E 8) (Qmake 339474855748706924384081555241010445081943704862720 884051494039200763939665645691040289218707744358400)%Q).
  { apply (Qeq_trans _ (Qmake 2469219613179871643997501158246798327808 6432321582780999379477089404589472481280 + Qmake 16777216 137438945280)%Q).
    - exact (Qplus_comp _ _ HA7 _ _ HE8).
    - unfold Qeq. cbn [Qplus Qnum Qden]. reflexivity. }
  assert (HA9 : Qeq (z3b_SP 8 + z3b_E 9) (Qmake 1055825958561665993927893468000334035277948750624573305651200000 2749245202814350482774395959384480344560564649562138849837056000)%Q).
  { apply (Qeq_trans _ (Qmake 339474855748706924384081555241010445081943704862720 884051494039200763939665645691040289218707744358400 + Qmake 134217728 3109824734590)%Q).
    - exact (Qplus_comp _ _ HA8 _ _ HE9).
    - unfold Qeq. cbn [Qplus Qnum Qden]. reflexivity. }
  assert (HA10 : Qeq ((z3b_SP 8 + z3b_E 9) + z3b_E 9) (Qmake 3283802678802101929042633538284174414519898246436347123449987649941536768000 8549670733164968211137124281240410007288129711505114808407250539946967040000)%Q).
  { apply (Qeq_trans _ (Qmake 1055825958561665993927893468000334035277948750624573305651200000 2749245202814350482774395959384480344560564649562138849837056000 + Qmake 134217728 3109824734590)%Q).
    - exact (Qplus_comp _ _ HA9 _ _ HE9).
    - unfold Qeq. cbn [Qplus Qnum Qden]. reflexivity. }
  assert (HcapQ : Qeq (((z3b_SP 8 + z3b_E 9) + z3b_E 9) + ((z3b_SP 8 + z3b_E 9) + z3b_E 9)) (Qmake 56150863312886106830535852263704648841359603767225415649741290328875640177378683236922357073919819898495305200014859595362488208316022396488253440000000 73096869645537605062296086744895371568203864253649365414421610452005197882868268979785712358091748637861659117875721055470952836807215694846361600000000)%Q).
  { apply (Qeq_trans _ (Qmake 3283802678802101929042633538284174414519898246436347123449987649941536768000 8549670733164968211137124281240410007288129711505114808407250539946967040000 + Qmake 3283802678802101929042633538284174414519898246436347123449987649941536768000 8549670733164968211137124281240410007288129711505114808407250539946967040000)%Q).
    - exact (Qplus_comp _ _ HA10 _ _ HA10).
    - unfold Qeq. cbn [Qplus Qnum Qden]. reflexivity. }
  assert (Hle : Qle (Qmake 56150863312886106830535852263704648841359603767225415649741290328875640177378683236922357073919819898495305200014859595362488208316022396488253440000000 73096869645537605062296086744895371568203864253649365414421610452005197882868268979785712358091748637861659117875721055470952836807215694846361600000000) (Qmake 4 5)) by (unfold Qle; cbn [Qnum Qden]; lia).
  exact (z3b_Qeq_le_r _ _ _ HcapQ Hle).
Qed.

(* ★★ D4 行和支配：q=8 阶梯任意行的检查器行和 ≤ 4/5
   （融合拆分 + 左相位 SP i + 右相位 SP (m−1−i) + 预算封口 + 分母正性反演） *)
Lemma z3b_row_le : forall (n0 m i : nat),
  Nat.le 2 n0 -> Nat.lt i m ->
  FrameCheckInstance.row_le_4_5 (FrameCheckInstance.row_sum_frac (z3b_bands n0 m) i) = true.
Proof.
  intros n0 m i Hn0 Hi.
  assert (Hm1 : Nat.le 1 m).
  { apply (proj2 (Nat2Z.inj_le 1 m)).
    assert (HZi : (Z.of_nat i < Z.of_nat m)%Z)
      by (apply (proj1 (Nat2Z.inj_lt i m)); exact Hi).
    assert (HZ0 : (0 <= Z.of_nat i)%Z) by apply Nat2Z.is_nonneg.
    lia. }
  assert (Him1 : Nat.le i (m - 1)).
  { apply (proj2 (Nat2Z.inj_le i (m - 1))).
    rewrite (Nat2Z.inj_sub m 1 Hm1).
    change (Z.of_nat 1) with 1%Z.
    assert (HZi : (Z.of_nat i < Z.of_nat m)%Z)
      by (apply (proj1 (Nat2Z.inj_lt i m)); exact Hi).
    lia. }
  assert (HBlen : length (z3b_bands n0 m) = m) by (apply z3b_bands_length).
  assert (Hpi : nth i (z3b_bands n0 m) 0%nat = (n0 * 8 ^ i)%nat)
    by (apply z3b_bands_nth; exact Hi).
  assert (HN1 : Nat.le 1 (n0 * 8 ^ i)) by (apply z3b_bands_elem_ge1; exact Hn0).
  assert (Hfl : length (firstn i (z3b_bands n0 m)) = i).
  { rewrite firstn_length. rewrite HBlen. apply Nat.min_l. apply Nat.lt_le_incl; exact Hi. }
  assert (Htails : length (skipn (S i) (z3b_bands n0 m)) = (m - S i)%nat).
  { rewrite length_skipn. rewrite HBlen. reflexivity. }
  assert (Hmeq : (m - 1 - i)%nat = (m - S i)%nat).
  { apply (proj1 (Nat2Z.inj_iff (m - 1 - i) (m - S i))).
    rewrite (Nat2Z.inj_sub (m - 1) i Him1).
    rewrite (Nat2Z.inj_sub m 1 Hm1).
    rewrite (Nat2Z.inj_sub m (S i) Hi).
    change (Z.of_nat 1) with 1%Z.
    assert (HSi : (Z.of_nat (S i) = 1 + Z.of_nat i)%Z)
      by (rewrite Nat2Z.inj_succ; rewrite <- Z.add_1_l; reflexivity).
    lia. }
  (* --- 融合拆分：row_sum_frac = 右相位 aux 作用在左相位结果上 --- *)
  assert (Hsplit : FrameCheckInstance.row_sum_frac (z3b_bands n0 m) i =
    FrameCheckInstance.row_sum_frac_aux
      (skipn (S i) (z3b_bands n0 m)) (z3b_bands n0 m) i
      (FrameCheckInstance.row_sum_frac_aux (firstn i (z3b_bands n0 m))
         (z3b_bands n0 m) i (0%nat, 1%nat) 0) (S i)).
  { unfold FrameCheckInstance.row_sum_frac.
    transitivity (FrameCheckInstance.row_sum_frac_aux
      (firstn i (z3b_bands n0 m) ++ skipn i (z3b_bands n0 m))%list
      (z3b_bands n0 m) i (0%nat, 1%nat) 0).
    - apply (f_equal (fun l : list nat =>
              FrameCheckInstance.row_sum_frac_aux l (z3b_bands n0 m) i (0%nat, 1%nat) 0)).
      symmetry. apply firstn_skipn.
    - rewrite (z3b_aux_fusion (firstn i (z3b_bands n0 m))
                (skipn i (z3b_bands n0 m)) (z3b_bands n0 m) i (0%nat, 1%nat) 0).
      rewrite Nat.add_0_l.
      rewrite firstn_length.
      rewrite HBlen.
      rewrite (Nat.min_l _ _ (Nat.lt_le_incl _ _ Hi)).
      replace (skipn i (z3b_bands n0 m)) with
        (nth i (z3b_bands n0 m) 0%nat :: skipn (S i) (z3b_bands n0 m)).
      + destruct (FrameCheckInstance.row_sum_frac_aux (firstn i (z3b_bands n0 m))
              (z3b_bands n0 m) i (0%nat, 1%nat) 0) as [lnum lden] eqn:HLdef.
        cbn [FrameCheckInstance.row_sum_frac_aux].
        rewrite Nat.eqb_refl.
        cbn [FrameCheckInstance.row_sum_frac_aux].
        rewrite <- HLdef. reflexivity.
      + destruct (skipn i (z3b_bands n0 m)) as [| p tlx] eqn:Es.
        * exfalso.
          assert (Hlenle : Nat.le (length (z3b_bands n0 m)) i)
            by (apply (proj2 (skipn_all_iff i (z3b_bands n0 m))); exact Es).
          rewrite HBlen in Hlenle.
          exact (Nat.lt_irrefl m (Nat.le_lt_trans _ _ _ Hlenle Hi)).
        * assert (Hp : nth i (z3b_bands n0 m) 0%nat = p).
          { transitivity (nth 0 (skipn i (z3b_bands n0 m)) 0%nat).
            - rewrite (nth_skipn i (z3b_bands n0 m) 0%nat 0%nat). rewrite Nat.add_0_r.
              reflexivity.
            - rewrite Es. reflexivity. }
          assert (Ht : skipn (S i) (z3b_bands n0 m) = tlx).
          { replace (S i) with (1 + i)%nat by reflexivity.
            rewrite <- (skipn_skipn 1 i (z3b_bands n0 m)). rewrite Es. reflexivity. }
          rewrite Hp. rewrite Ht. reflexivity. }
  (* --- 左相位界 --- *)
  assert (HL : Qle (z3b_accQ (FrameCheckInstance.row_sum_frac_aux
                    (firstn i (z3b_bands n0 m)) (z3b_bands n0 m) i (0%nat, 1%nat) 0))
                   (z3b_accQ (0%nat, 1%nat) + z3b_SP i)%Q).
  { apply (z3b_left_le i (firstn i (z3b_bands n0 m)) (z3b_bands n0 m) i 0
        (n0 * 8 ^ i)%nat (0%nat, 1%nat)).
    - exact Hfl.
    - reflexivity.
    - exact Hpi.
    - intros k Hk.
      assert (Hkm : Nat.lt k m) by (apply Nat.lt_le_trans with (m := i%nat);
          [exact Hk | apply Nat.lt_le_incl; exact Hi]).
      rewrite (z3b_nth_firstn _ _ _ _ Hk).
      rewrite (z3b_bands_nth _ _ _ Hkm).
      rewrite Nat.add_0_l.
      rewrite <- (Nat.mul_assoc n0 (8 ^ k) (8 ^ (i - k))).
      rewrite <- (Nat.pow_add_r 8 k (i - k)).
      do 2 f_equal.
      rewrite (Nat.add_comm k (i - k)).
      symmetry.
      apply (Nat.sub_add k i (Nat.lt_le_incl k i Hk)).
    - intros k Hk.
      assert (Hkm : Nat.lt k m) by (apply Nat.lt_le_trans with (m := i%nat);
          [exact Hk | apply Nat.lt_le_incl; exact Hi]).
      rewrite (z3b_nth_firstn _ _ _ _ Hk).
      rewrite (z3b_bands_nth _ _ _ Hkm).
      apply (z3b_bands_elem_ge1 n0 k Hn0).
    - cbn [snd]. apply Nat.leb_le. vm_compute. reflexivity. }
  (* --- 左相位结果分母正性（右相位前提） --- *)
  assert (HLEFTpos : Nat.lt 0 (snd (FrameCheckInstance.row_sum_frac_aux
                     (firstn i (z3b_bands n0 m)) (z3b_bands n0 m) i (0%nat, 1%nat) 0))).
  { apply (z3b_aux_den_pos (firstn i (z3b_bands n0 m)) (z3b_bands n0 m) i 0 (0%nat, 1%nat)).
    - rewrite Nat.add_0_l. rewrite Hfl. rewrite HBlen. apply Nat.lt_le_incl; exact Hi.
    - intros k Hk.
      assert (Hki : Nat.lt k i).
      { apply Nat.lt_le_trans with (m := (length (firstn i (z3b_bands n0 m)))).
        - exact Hk.
        - rewrite Hfl. apply Nat.le_refl. }
      rewrite (z3b_nth_firstn _ _ _ _ Hki).
      rewrite Nat.add_0_l. reflexivity.
    - rewrite HBlen. exact Hi.
    - intros k Hk Hki.
      rewrite HBlen in Hk.
      apply (z3b_bands_nth_ne n0 m k i Hn0).
      + exact Hk.
      + exact Hi.
      + exact Hki.
    - rewrite Hpi. apply (z3b_bands_elem_ge1 n0 i Hn0).
    - intros e He.
      apply in_map_iff in He. destruct He as [k [Hk Hin]].
      apply in_seq in Hin. destruct Hin as [_ Hlt].
      rewrite <- Hk. apply (z3b_bands_elem_ge1 n0 k Hn0).
    - intros e He Heq.
      apply (z3b_bands_pair_cmp n0 m i e Hn0 Hi He Heq).
    - cbn [snd]. apply Nat.leb_le. vm_compute. reflexivity. }
  (* --- 右相位界 --- *)
  assert (HRw : Qle (z3b_accQ (FrameCheckInstance.row_sum_frac_aux
                    (skipn (S i) (z3b_bands n0 m)) (z3b_bands n0 m) i
                    (FrameCheckInstance.row_sum_frac_aux (firstn i (z3b_bands n0 m))
                       (z3b_bands n0 m) i (0%nat, 1%nat) 0) (S i)) + z3b_SP 0)
                   (z3b_accQ (FrameCheckInstance.row_sum_frac_aux (firstn i (z3b_bands n0 m))
                      (z3b_bands n0 m) i (0%nat, 1%nat) 0) + z3b_SP (0 + (m - 1 - i)))%Q).
  { apply (z3b_right_le (m - 1 - i) (skipn (S i) (z3b_bands n0 m)) (z3b_bands n0 m)
        i (S i) 0 (n0 * 8 ^ i)%nat).
    - rewrite Hmeq. exact Htails.
    - exact Hpi.
    - intros k Hk.
      rewrite (nth_skipn (S i) (z3b_bands n0 m) k 0%nat).
      rewrite z3b_bands_nth.
      * replace (S 0 + k)%nat with (S k)%nat by reflexivity.
        rewrite <- (Nat.mul_assoc n0 (8 ^ i) (8 ^ S k)).
        rewrite <- (Nat.pow_add_r 8 i (S k)).
        replace (S i + k)%nat with (i + S k)%nat
          by (rewrite Nat.add_succ_r; rewrite Nat.add_succ_l; reflexivity).
        reflexivity.
      * assert (HZk : (Z.of_nat (S i + k) < Z.of_nat m)%Z).
        { assert (HZ1 : (Z.of_nat (S i + k) = 1 + Z.of_nat i + Z.of_nat k)%Z).
          { rewrite Nat2Z.inj_add. rewrite Nat2Z.inj_succ. rewrite <- Z.add_1_l. reflexivity. }
          assert (HZsub : (Z.of_nat (m - 1 - i) = Z.of_nat m - 1 - Z.of_nat i)%Z).
          { rewrite (Nat2Z.inj_sub (m - 1) i Him1). rewrite (Nat2Z.inj_sub m 1 Hm1).
            change (Z.of_nat 1) with 1%Z. reflexivity. }
          assert (HZk2 : (Z.of_nat k < Z.of_nat (m - 1 - i))%Z)
            by (apply (proj1 (Nat2Z.inj_lt k (m - 1 - i))); exact Hk).
          assert (HZ0 : (0 <= Z.of_nat i)%Z) by apply Nat2Z.is_nonneg.
          lia. }
        apply (proj2 (Nat2Z.inj_lt (S i + k) m)); exact HZk.
    - exact HN1.
    - apply Nat.lt_succ_diag_r.
    - exact HLEFTpos. }
  assert (HRw2 : Qle (z3b_accQ (FrameCheckInstance.row_sum_frac_aux
                    (skipn (S i) (z3b_bands n0 m)) (z3b_bands n0 m) i
                    (FrameCheckInstance.row_sum_frac_aux (firstn i (z3b_bands n0 m))
                       (z3b_bands n0 m) i (0%nat, 1%nat) 0) (S i)))
                   (z3b_accQ (FrameCheckInstance.row_sum_frac_aux (firstn i (z3b_bands n0 m))
                      (z3b_bands n0 m) i (0%nat, 1%nat) 0) + z3b_SP (0 + (m - 1 - i)))%Q).
  { apply (z3b_Qeq_le_r _ _ _ (Qeq_sym _ _ (Qplus_0_r (z3b_accQ
        (FrameCheckInstance.row_sum_frac_aux (skipn (S i) (z3b_bands n0 m))
          (z3b_bands n0 m) i
          (FrameCheckInstance.row_sum_frac_aux (firstn i (z3b_bands n0 m))
             (z3b_bands n0 m) i (0%nat, 1%nat) 0) (S i)))))).
    exact HRw. }
  (* --- 主链 --- *)
  assert (Haux : Qle (z3b_accQ (FrameCheckInstance.row_sum_frac (z3b_bands n0 m) i))
                     (z3b_accQ (0%nat, 1%nat) + z3b_SP i
                      + z3b_SP (0 + (m - 1 - i)))%Q).
  { rewrite Hsplit.
    eapply Qle_trans.
    - exact HRw2.
    - eapply Qplus_le_compat.
      + exact HL.
      + apply Qle_refl. }
  (* --- 预算封口 --- *)
  assert (Hstep : Qle (z3b_accQ (0%nat, 1%nat) + z3b_SP i
                       + z3b_SP (0 + (m - 1 - i))%nat)
                      (z3b_SP (m - 1) + z3b_SP (m - 1))%Q).
  { apply Qplus_le_compat.
    - apply (z3b_Qeq_le_r _ _ _ (Qplus_0_l (z3b_SP i))).
      apply z3b_SP_mono. exact Him1.
    - apply z3b_SP_mono.
      replace (0 + (m - 1 - i))%nat with (m - 1 - i)%nat by reflexivity.
      apply Nat.le_sub_l. }
  assert (Hcapx : Qle (z3b_SP (m - 1) + z3b_SP (m - 1))
                      ((z3b_SP 8 + z3b_E 9) + z3b_E 9
                       + ((z3b_SP 8 + z3b_E 9) + z3b_E 9))%Q).
  { apply Qplus_le_compat; apply z3b_total_le. }
  assert (Hcap : Qle ((z3b_SP 8 + z3b_E 9) + z3b_E 9
                      + ((z3b_SP 8 + z3b_E 9) + z3b_E 9)) (Qmake 4 5)).
  { exact z3b_cap_4_5. }
  assert (Hchain : Qle (z3b_accQ (FrameCheckInstance.row_sum_frac (z3b_bands n0 m) i))
                       (Qmake 4 5)).
  { eapply Qle_trans.
    - exact Haux.
    - eapply Qle_trans.
      + exact Hstep.
      + eapply Qle_trans.
        * exact Hcapx.
        * exact Hcap. }
  (* --- 行分母正性 --- *)
  assert (Hrowpos : Nat.lt 0 (snd (FrameCheckInstance.row_sum_frac (z3b_bands n0 m) i))).
  { apply (z3b_aux_den_pos (z3b_bands n0 m) (z3b_bands n0 m) i 0 (0%nat, 1%nat)).
    - rewrite Nat.add_0_l. apply Nat.le_refl.
    - intros k Hk. rewrite Nat.add_0_l. reflexivity.
    - rewrite HBlen. exact Hi.
    - intros k Hk Hki.
      rewrite HBlen in Hk.
      apply (z3b_bands_nth_ne n0 m k i Hn0).
      + exact Hk.
      + exact Hi.
      + exact Hki.
    - rewrite Hpi. apply (z3b_bands_elem_ge1 n0 i Hn0).
    - intros e He.
      apply in_map_iff in He. destruct He as [k [Hk Hin]].
      apply in_seq in Hin. destruct Hin as [_ Hlt].
      rewrite <- Hk. apply (z3b_bands_elem_ge1 n0 k Hn0).
    - intros e He Heq.
      apply (z3b_bands_pair_cmp n0 m i e Hn0 Hi He Heq).
    - cbn [snd]. apply Nat.leb_le. vm_compute. reflexivity. }
  (* --- 反演：Qle (num/den) (4/5) ⟹ 5·num ≤ 4·den = true
     （E202/E227：apply 实例与目标形状逐括号全等，乘序 5·num 在前）--- *)
  unfold FrameCheckInstance.row_le_4_5.
  apply Nat.leb_le.
  apply (proj2 (Nat2Z.inj_le
    (5 * fst (FrameCheckInstance.row_sum_frac (z3b_bands n0 m) i))%nat
    (4 * snd (FrameCheckInstance.row_sum_frac (z3b_bands n0 m) i))%nat)).
  rewrite Nat2Z.inj_mul.
  rewrite Nat2Z.inj_mul.
  assert (Hq : (Z.of_nat 5 * Z.of_nat (fst (FrameCheckInstance.row_sum_frac (z3b_bands n0 m) i)) <=
                Z.of_nat 4 * Z.of_nat (snd (FrameCheckInstance.row_sum_frac (z3b_bands n0 m) i)))%Z).
  { unfold Qle, z3b_accQ in Hchain.
    cbn [Qnum Qden] in Hchain.
    rewrite (z3b_qmk_num _ _ Hrowpos) in Hchain.
    rewrite (z3b_qmk_den _ _ Hrowpos) in Hchain.
    rewrite (z3b_Zpos_of _ Hrowpos) in Hchain.
    lia. }
  exact Hq.
Qed.

(* 周边结构分量 *)
(* —— Phase B：bands 结构三分量（sorted / ge2 / pairs_ok）—— *)

(* 相邻带严格递增：n0·8^k < n0·8^{k+1}（8^k ≥ 1 + 乘法右单调） *)
Lemma z3b_adjacent_lt : forall (n0 k : nat), Nat.le 1 n0 ->
  Nat.lt (n0 * 8 ^ k) (n0 * 8 ^ S k).
Proof.
  intros n0 k Hn.
  rewrite (Nat.pow_succ_r 8 k (Nat.le_0_l k)).
  assert (Hn0pos : Nat.lt 0 n0).
  { apply Nat.lt_le_trans with (m := 1%nat);
      [apply Nat.leb_le; vm_compute; reflexivity | exact Hn]. }
  assert (Hpos : Nat.le 1 (8 ^ k)).
  { rewrite <- (Nat.pow_0_r 8). apply Nat.pow_le_mono_r.
    - intros Hc; discriminate Hc.
    - apply Nat.le_0_l. }
  assert (Hstep : Nat.lt (1 * 8 ^ k) (8 * 8 ^ k)).
  { apply (proj1 (Nat.mul_lt_mono_pos_r (8 ^ k) 1 8 Hpos)).
    apply Nat.leb_le. vm_compute. reflexivity. }
  rewrite Nat.mul_1_l in Hstep.
  exact (proj1 (Nat.mul_lt_mono_pos_l n0 (8 ^ k) (8 * 8 ^ k) Hn0pos) Hstep).
Qed.

(* 泛化扫描：严格递增序列的 map/seq sorted_aux（对 len 归纳，s/prev 泛化） *)
Lemma z3b_map_seq_sorted : forall (f : nat -> nat) len s prev,
  (forall k : nat, Nat.lt (f k) (f (S k))) ->
  Nat.lt prev (f s) ->
  FrameCheckInstance.sorted_aux prev (map f (seq s len)) = true.
Proof.
  intros f len. induction len as [| len IH]; intros s prev Hstep Hhead.
  - reflexivity.
  - cbn [seq map FrameCheckInstance.sorted_aux].
    apply Bool.andb_true_iff. split.
    + apply Nat.ltb_lt. exact Hhead.
    + apply IH.
      * exact Hstep.
      * apply Hstep.
Qed.

(* 周边结构分量 1：严格升序 *)
Lemma z3b_bands_sorted : forall n0 m, Nat.le 1 n0 ->
  FrameCheckInstance.sorted_strict_aux (z3b_bands n0 m) = true.
Proof.
  intros n0 m Hn.
  unfold z3b_bands.
  destruct m as [| mx].
  - reflexivity.
  - cbn [FrameCheckInstance.sorted_strict_aux map seq].
    apply z3b_map_seq_sorted.
    + intros k. apply z3b_adjacent_lt. exact Hn.
    + apply z3b_adjacent_lt. exact Hn.
Qed.

(* 泛化扫描：逐元素 ≥ 2 的 map/seq all_ge_2 *)
Lemma z3b_map_seq_ge : forall (f : nat -> nat) len s,
  (forall k : nat, Nat.le 2 (f k)) ->
  FrameCheckInstance.all_ge_2 (map f (seq s len)) = true.
Proof.
  intros f len. induction len as [| len IH]; intros s Hf.
  - reflexivity.
  - cbn [seq map FrameCheckInstance.all_ge_2].
    apply Bool.andb_true_iff. split.
    + apply Nat.leb_le. apply Hf.
    + apply IH. exact Hf.
Qed.

(* 周边结构分量 2：全 ≥ 2 *)
Lemma z3b_bands_ge2 : forall n0 m, Nat.le 2 n0 ->
  FrameCheckInstance.all_ge_2 (z3b_bands n0 m) = true.
Proof.
  intros n0 m Hn0.
  unfold z3b_bands. apply z3b_map_seq_ge.
  intros k.
  assert (H1 : Nat.le 1 (8 ^ k)).
  { rewrite <- (Nat.pow_0_r 8). apply Nat.pow_le_mono_r.
    - intros Hc; discriminate Hc.
    - apply Nat.le_0_l. }
  assert (H2 : Nat.le (n0 * 1) (n0 * 8 ^ k))
    by (apply (Nat.mul_le_mono_l 1 (8 ^ k) n0); exact H1).
  apply Nat.le_trans with (m := n0).
  - exact Hn0.
  - rewrite Nat.mul_1_r in H2. exact H2.
Qed.

(* 泛化扫描：逐元素 ≥ 1 的 map/seq all_pairs_ok
   （pair_ok 两支均只依赖两因子 ≥ 1：sqrt 下界恒真 + sqrt ≥ 1） *)
Lemma z3b_map_seq_pairs_ok : forall (f : nat -> nat) len s,
  (forall x : nat, Nat.le 1 (f x)) ->
  FrameCheckInstance.all_pairs_ok (map f (seq s len)) = true.
Proof.
  intros f len. induction len as [| len IH]; intros s Hge.
  - reflexivity.
  - cbn [seq map FrameCheckInstance.all_pairs_ok].
    apply Bool.andb_true_iff. split.
    + apply forallb_forall.
      intros y Hy.
      destruct (proj1 (in_map_iff f (seq (S s) len) y) Hy) as [z [Hz Hzy]].
      rewrite <- Hz.
      unfold FrameCheckInstance.pair_ok.
      apply Bool.andb_true_iff. split.
      * apply Nat.leb_le.
        apply (proj2 (Nat.sqrt_le_square ((f s) * (f z))
                       (Nat.sqrt ((f s) * (f z))))).
        apply Nat.le_refl.
      * apply Nat.ltb_lt.
        apply (proj1 (Nat.sqrt_le_square ((f s) * (f z)) 1)).
        rewrite Nat.mul_1_l.
        apply (Nat.mul_le_mono 1 (f s) 1 (f z)); apply Hge.
    + apply IH. exact Hge.
Qed.

(* 周边结构分量 3：所有对界有效 *)
Lemma z3b_bands_pairs_ok : forall n0 m, Nat.le 2 n0 ->
  FrameCheckInstance.all_pairs_ok (z3b_bands n0 m) = true.
Proof.
  intros n0 m Hn0.
  unfold z3b_bands. apply z3b_map_seq_pairs_ok.
  intros k.
  assert (H1 : Nat.le 1 (8 ^ k)).
  { rewrite <- (Nat.pow_0_r 8). apply Nat.pow_le_mono_r.
    - intros Hc; discriminate Hc.
    - apply Nat.le_0_l. }
  assert (H2 : Nat.le (n0 * 1) (n0 * 8 ^ k))
    by (apply (Nat.mul_le_mono_l 1 (8 ^ k) n0); exact H1).
  apply Nat.le_trans with (m := n0).
  - apply Nat.le_trans with (m := 2%nat).
    + apply Nat.le_succ_diag_r.
    + exact Hn0.
  - rewrite Nat.mul_1_r in H2. exact H2.
Qed.
(* all_rows_le 分量：skipn 视图扫描（j 行起，对表结构归纳） *)
Lemma z3b_all_rows_skipn : forall (L : list nat) (n0 m j : nat),
  Nat.le 2 n0 -> L = skipn j (z3b_bands n0 m) -> j + length L = m ->
  FrameCheckInstance.all_rows_le L (z3b_bands n0 m) j = true.
Proof.
  intros L. induction L as [| h tl IH]; intros n0 m j Hn0 Heq Hlen.
  - reflexivity.
  - cbn [FrameCheckInstance.all_rows_le].
    apply Bool.andb_true_iff. split.
    + assert (Hjm : Nat.lt j m).
      { apply (proj2 (Nat2Z.inj_lt j m)).
        assert (HZlen : (Z.of_nat (length (h :: tl)) = 1 + Z.of_nat (length tl))%Z)
          by (cbn [length]; rewrite Nat2Z.inj_succ; lia).
        assert (HZ : (Z.of_nat j + Z.of_nat (length (h :: tl)) = Z.of_nat m)%Z).
        { rewrite <- (proj2 (Nat2Z.inj_iff (j + length (h :: tl)) m) Hlen).
          rewrite Nat2Z.inj_add. rewrite HZlen. reflexivity. }
        assert (HZ0 : (0 <= Z.of_nat (length tl))%Z) by apply Nat2Z.is_nonneg.
        lia. }
      apply z3b_row_le; [exact Hn0 | exact Hjm].
    + apply (IH n0 m (S j) Hn0).
      * transitivity (skipn 1 (h :: tl)%list); [reflexivity | rewrite Heq; apply skipn_skipn].
      * rewrite (Nat.add_succ_comm j (length tl)). exact Hlen.
Qed.

(* ★★ 最终定理：q=8 几何阶梯全体通过检查器 *)
Theorem z3b_sufficiency : forall n0 m, Nat.le 2 n0 -> Nat.le 1 m ->
  FrameCheckInstance.frame_check_instance (z3b_bands n0 m) = true.
Proof.
  intros n0 m Hn0 Hm.
  assert (H1 : Nat.le 1 n0)
    by (apply Nat.le_trans with (m := 2%nat); [apply Nat.le_succ_diag_r | exact Hn0]).
  unfold FrameCheckInstance.frame_check_instance.
  rewrite (z3b_bands_sorted n0 m H1).
  rewrite (z3b_bands_ge2 n0 m Hn0).
  rewrite (z3b_bands_pairs_ok n0 m Hn0).
  apply z3b_all_rows_skipn with (n0 := n0) (m := m) (j := 0%nat).
  - exact Hn0.
  - apply skipn_0.
  - rewrite Nat.add_0_l. rewrite z3b_bands_length. reflexivity.
Qed.

(* ============================================================
   审计（终态全 Closed）
   ============================================================ *)
Print Assumptions z3b_env_uni.
Print Assumptions z3b_tail_R.
Print Assumptions z3b_total_le.
Print Assumptions z3b_row_le.
Print Assumptions z3b_sufficiency.
