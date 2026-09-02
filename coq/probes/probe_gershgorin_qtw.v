(* ============================================================
   probe_gershgorin_qtw.v —— C1：Gershgorin 框架能量界构造性孪生
   PSA/PSA-GSA z 区构造性轨道 · C 系列（2026-09-02）
   ============================================================

   使命（交接文档 §3 C1 设计）：把论文 A 的 Gershgorin 框架能量界
   (1−μ)·S ≤ ‖Vᵀc‖² ≤ (1+μ)·S（经典实数 Prop 层定理）实现为纯构造性
   孪生：Q 层全量化 + Set 层信息性证据，零 Reals 零经典。

   铁律对齐（用户四条硬约束）：
     ① 纯构造性：Require 链仅 QArith/Qabs/Setoid/Lia/Lqa/Extraction/
        PeanoNat + qset_twin_base；零 Reals 零经典实数公理；
        Print Assumptions 全部字面 Closed。
     ② 非平凡核心定理：gtw_qsum_sq_expand（方块积展开）、
        gtw_Fsq_expand（三层和重排 F² = Σ_i Σ_j c_i c_j ⟨v_i,v_j⟩）、
        gtw_W_bound（AM–GM 装配 |offdiag| ≤ μ·S，含 B=A 对称化）——
        最终定理 gershgorin_frame_mu_qtw 双侧能量界全链实现。
     ③ Set 层 + sigT：结论全 Set 层（And-of-QleT，非 Prop）；
        gtw_gap_witness 给 sigT 正 gap 数据件（μ<1 时 1−μ 的正性
        见证 + 下界证书对，Defined 可提取）。
     ④ 可提取：Extraction gershgorin_qtw.ml + ocamlc（DkMLNative）
        编译验证；冒烟实例 gtw_smoke_* 数值可执行。

   数学骨架：
     ‖Vᵀc‖² = Σ_k (Σ_i c_i v_ik)²                       [sq_expand]
            = Σ_i Σ_j c_i c_j ⟨v_i,v_j⟩                  [Fsq_expand]
            = S + offdiag                                [Fsq_split，单位对角]
     |offdiag| ≤ W ≤ Σ_{i≠j} (c_i²+c_j²)/2·w_ij = μ·S    [W_abs/A_bound/W_bound]
       其中 w_ij := |⟨v_i,v_j⟩|，行界 row_i ≤ μ 经 swap+内积交换律
       双向使用（B == A 对称化）。

   provenance：主线经典版 = 论文 A Gershgorin 框架引理；Q 层孪生为
   本项目非平凡改造（基座 qset_twin_base qsum 工具包装配）。
   实测坑（本轮沉淀）：
     – Qle 目标上 rewrite 无 Proper 实例（基座 Qmult_leT_compat_l
       注释同款）：Qeq 引理 rewrite 被展开成 Z 交叉乘积模式匹配，
       嵌套位置必挂——Qle/QleT 目标一律 setoid_replace；
     – rewrite 高阶 unify 脆性：qtw_qsum_scale 的 ?a * ?f k 模式对
       fun k => u k * 常数 形（?a 解到绑定变量被拒）不稳——全部
       显式实例，两个方向（scale/scale_r）各配其形；
     – QleT 0 (x+y) 上 Qplus_leT_compat 无法从 0 拆出 a+c——改
       Prop 层 Qmult_le_0_compat + lra（平方和线性化靠 assert）。
   ============================================================ *)
Require Import Stdlib.QArith.QArith.
Require Import Stdlib.QArith.Qabs.
From Stdlib Require Import Lia.
From Stdlib Require Import Lqa.
From Stdlib Require Import Extraction.
From Stdlib Require Import PeanoNat.
Require Import qset_twin_base.

(* E259① 记号防御补块（本文件自含，独立于基座合并顺序；独立环境同义覆盖仅 warning） *)
Notation "x + y" := (Nat.add x y) : nat_scope.
Notation "x - y" := (Nat.sub x y) : nat_scope.
Notation "x * y" := (Nat.mul x y) : nat_scope.
Notation "x <= y" := (Peano.le x y) : nat_scope.
Notation "x < y" := (Peano.lt x y) : nat_scope.
Notation "x # y" := (Qmake x y) (at level 55, no associativity) : Q_scope.

Local Open Scope Q_scope.

(* ############ §0 框架数据定义 ############ *)

(* 内积 ⟨v_i, v_j⟩（求和含端点，界 Nat.pred m） *)
Definition gtw_ip (v : nat -> nat -> Q) (i j m : nat) : Q :=
  qtw_qsum (fun k => v i k * v j k) (Nat.pred m).

(* 能量 S(c) = Σ_i c_i² *)
Definition gtw_S (c : nat -> Q) (n : nat) : Q :=
  qtw_qsum (fun i => c i * c i) (Nat.pred n).

(* 框架能量 F²(c) = Σ_k (Σ_i c_i v_ik)² *)
Definition gtw_Fsq (v : nat -> nat -> Q) (c : nat -> Q) (n m : nat) : Q :=
  qtw_qsum (fun k => qtw_qsum (fun i => c i * v i k) (Nat.pred n) *
             qtw_qsum (fun i => c i * v i k) (Nat.pred n)) (Nat.pred m).

(* 离对角双和 Σ_{i≠j} c_i c_j ⟨v_i,v_j⟩ *)
Definition gtw_offdiag (v : nat -> nat -> Q) (c : nat -> Q) (n m : nat) : Q :=
  qtw_qsum (fun i => qtw_qsum (fun j =>
    if Nat.eq_dec i j then 0%Q else c i * c j * gtw_ip v i j m) (Nat.pred n)) (Nat.pred n).

(* 绝对值控制量 W = Σ_{i≠j} |c_i||c_j||⟨v_i,v_j⟩| *)
Definition gtw_W (v : nat -> nat -> Q) (c : nat -> Q) (n m : nat) : Q :=
  qtw_qsum (fun i => qtw_qsum (fun j =>
    if Nat.eq_dec i j then 0%Q else Qabs (c i) * Qabs (c j) * Qabs (gtw_ip v i j m)) (Nat.pred n)) (Nat.pred n).

(* ############ §G0 求和支持 ############ *)

(* 右数乘分配（基座 qtw_qsum_scale 的镜像） *)
Lemma gtw_qsum_scale_r : forall (f : nat -> Q) (a : Q) (n : nat),
  qtw_qsum (fun k => f k * a) n == qtw_qsum f n * a.
Proof.
  intros f a n.
  induction n as [| n IH].
  - reflexivity.
  - cbn [qtw_qsum]. rewrite IH. ring.
Qed.

(* ★ 核心件 1：方块积展开 (Σu)² = Σ_i Σ_j u_i u_j *)
Lemma gtw_qsum_sq_expand : forall (u : nat -> Q) (n : nat),
  qtw_qsum u n * qtw_qsum u n
  == qtw_qsum (fun i => qtw_qsum (fun j => u i * u j) n) n.
Proof.
  intros u n.
  induction n as [| n IH].
  - reflexivity.
  - cbn [qtw_qsum].
    (* Σ_i (内和 + u_i·b) 拆 plus *)
    rewrite qtw_qsum_plus.
    (* Σ_j b·u_j → b·A（scale）；Σ_i u_i·b → A·b（scale_r）：
       两处形状互为镜像，各配一个方向，规避 ?a 解到绑定变量的
       高阶 unify 脆性 *)
    rewrite qtw_qsum_scale.
    rewrite gtw_qsum_scale_r.
    rewrite <- IH.
    ring.
Qed.

(* ############ §G1 内积/绝对值辅助 ############ *)

Lemma gtw_ip_comm : forall (v : nat -> nat -> Q) (i j m : nat),
  gtw_ip v i j m == gtw_ip v j i m.
Proof.
  intros v i j m. unfold gtw_ip.
  apply qtw_qsum_ext. intros k _.
  ring.
Qed.

(* 本平台 9.1 stdlib Qabs.v 已有 Qabs_Qmult（9.0 无，交接旧况） *)
Lemma gtw_abs_mult : forall a b : Q, Qabs (a * b) == Qabs a * Qabs b.
Proof. intros a b. apply Qabs_Qmult. Qed.

Lemma gtw_abs_ge : forall x : Q, Qle x (Qabs x).
Proof. intros x. apply Qle_Qabs. Qed.

(* −|x| ≤ x：Qle 目标上禁 rewrite、lra 不吃 Qeq 前提——
   Qopp_le_compat 两跳，前提用 setoid_replace 同一化至 Qle_refl *)
Lemma gtw_neg_abs_le : forall x : Q, Qle (- Qabs x) x.
Proof.
  intros x.
  destruct (qtw_tri x 0) as [Hn | [He | Hp]].
  - (* x < 0：|x| = −x ⟹ −|x| ≤ −(−x) ≤ x *)
    assert (Habs : Qabs x == - x)
      by (apply Qabs_neg; apply Qlt_le_weak; apply QltT_to_Qlt; exact Hn).
    apply (Qle_trans (- Qabs x) (- (- x)) x).
    + apply (Qopp_le_compat (- x) (Qabs x)).
      setoid_replace (Qabs x) with (- x)%Q by exact Habs.
      apply Qle_refl.
    + lra.
  - (* x == 0：|x| = x ⟹ −|x| ≤ −x ≤ x *)
    assert (Hx0 : x == 0) by (apply QeqT_to_Qeq; exact He).
    assert (Hle0 : (0 <= x)%Q)
      by (setoid_replace x with 0%Q by exact Hx0; apply Qle_refl).
    assert (Habs : Qabs x == x) by (apply Qabs_pos; exact Hle0).
    apply (Qle_trans (- Qabs x) (- x) x).
    + apply (Qopp_le_compat x (Qabs x)).
      setoid_replace (Qabs x) with x by exact Habs.
      apply Qle_refl.
    + lra.
  - (* x > 0：|x| = x ⟹ −|x| ≤ −x ≤ x *)
    assert (Hpos : (0 < x)%Q) by (apply QltT_to_Qlt; exact Hp).
    assert (Habs : Qabs x == x) by (apply Qabs_pos; apply Qlt_le_weak; exact Hpos).
    apply (Qle_trans (- Qabs x) (- x) x).
    + apply (Qopp_le_compat x (Qabs x)).
      setoid_replace (Qabs x) with x by exact Habs.
      apply Qle_refl.
    + lra.
Qed.

(* ############ §G2 展开链：F² = S + offdiag ############ *)

(* ★ 核心件 2：三层和重排 F² = Σ_i Σ_j c_i c_j ⟨v_i,v_j⟩ *)
Lemma gtw_Fsq_expand : forall (v : nat -> nat -> Q) (c : nat -> Q) (n m : nat),
  gtw_Fsq v c n m
  == qtw_qsum (fun i => qtw_qsum (fun j =>
       c i * c j * gtw_ip v i j m) (Nat.pred n)) (Nat.pred n).
Proof.
  intros v c n m.
  unfold gtw_Fsq.
  (* a. 逐点方块展开（sq_expand 实例） *)
  setoid_replace
    (qtw_qsum (fun k => qtw_qsum (fun i => c i * v i k) (Nat.pred n) *
                qtw_qsum (fun i => c i * v i k) (Nat.pred n)) (Nat.pred m))
    with (qtw_qsum (fun k => qtw_qsum (fun i => qtw_qsum (fun j =>
            (c i * v i k) * (c j * v j k)) (Nat.pred n)) (Nat.pred n)) (Nat.pred m))
    by (apply qtw_qsum_ext; intros k Hk;
        exact (gtw_qsum_sq_expand (fun i => c i * v i k) (Nat.pred n))).
  (* b1. 外层 k↔i 换序（显式实例） *)
  setoid_replace
    (qtw_qsum (fun k => qtw_qsum (fun i => qtw_qsum (fun j =>
        (c i * v i k) * (c j * v j k)) (Nat.pred n)) (Nat.pred n)) (Nat.pred m))
    with (qtw_qsum (fun i => qtw_qsum (fun k => qtw_qsum (fun j =>
        (c i * v i k) * (c j * v j k)) (Nat.pred n)) (Nat.pred m)) (Nat.pred n))
    by exact (qtw_qsum_swap (fun k i => qtw_qsum (fun j =>
         (c i * v i k) * (c j * v j k)) (Nat.pred n)) (Nat.pred m) (Nat.pred n)).
  (* b2. 逐 i 内层 k↔j 换序 *)
  setoid_replace
    (qtw_qsum (fun i => qtw_qsum (fun k => qtw_qsum (fun j =>
        (c i * v i k) * (c j * v j k)) (Nat.pred n)) (Nat.pred m)) (Nat.pred n))
    with (qtw_qsum (fun i => qtw_qsum (fun j => qtw_qsum (fun k =>
        (c i * v i k) * (c j * v j k)) (Nat.pred m)) (Nat.pred n)) (Nat.pred n))
    by (apply qtw_qsum_ext; intros i Hi;
        exact (qtw_qsum_swap (fun k j => (c i * v i k) * (c j * v j k))
                 (Nat.pred m) (Nat.pred n))).
  (* c. 逐 (i,j) 收 k 成内积 *)
  setoid_replace
    (qtw_qsum (fun i => qtw_qsum (fun j => qtw_qsum (fun k =>
        (c i * v i k) * (c j * v j k)) (Nat.pred m)) (Nat.pred n)) (Nat.pred n))
    with (qtw_qsum (fun i => qtw_qsum (fun j =>
        c i * c j * gtw_ip v i j m) (Nat.pred n)) (Nat.pred n))
    by (apply qtw_qsum_ext; intros i Hi;
        apply qtw_qsum_ext; intros j Hj;
        unfold gtw_ip;
        rewrite <- (qtw_qsum_scale (c i * c j) (fun k => v i k * v j k)
                      (Nat.pred m));
        apply qtw_qsum_ext; intros k Hk; ring).
  (* setoid_replace by 只闭侧目标，主目标（末步形态==结论）需收口 *)
  reflexivity.
Qed.

(* 对角收取：单位行 ⟹ c_i²⟨v_i,v_i⟩ = c_i² *)
Lemma gtw_Fsq_split : forall (v : nat -> nat -> Q) (c : nat -> Q) (n m : nat),
  (1 <= n)%nat ->
  (forall i : nat, (i < n)%nat ->
     QeqT (qtw_qsum (fun k => v i k * v i k) (Nat.pred m)) (1#1)%Q) ->
  gtw_Fsq v c n m == gtw_S c n + gtw_offdiag v c n m.
Proof.
  intros v c n m Hn1 Hunit.
  assert (Hdiag : qtw_qsum (fun i => c i * c i * gtw_ip v i i m) (Nat.pred n)
                  == qtw_qsum (fun i => c i * c i) (Nat.pred n)).
  { apply qtw_qsum_ext. intros i Hi.
    assert (Hin : (i < n)%nat) by lia.
    assert (Hd : gtw_ip v i i m == (1#1)%Q).
    { unfold gtw_ip. apply QeqT_to_Qeq. apply Hunit. exact Hin. }
    rewrite Hd. ring. }
  rewrite gtw_Fsq_expand.
  unfold gtw_S, gtw_offdiag.
  transitivity (qtw_qsum (fun i => c i * c i * gtw_ip v i i m) (Nat.pred n)
                + qtw_qsum (fun i => qtw_qsum (fun j =>
                    if Nat.eq_dec i j then 0%Q
                    else c i * c j * gtw_ip v i j m) (Nat.pred n)) (Nat.pred n)).
  - exact (qtw_qsum2_split_dec (fun i j => c i * c j * gtw_ip v i j m)
             (Nat.pred n)).
  - rewrite Hdiag. reflexivity.
Qed.

(* ############ §G3 离对角界 |offdiag| ≤ μ·S ############ *)

(* |offdiag| ≤ W：两层三角不等式 + 逐点积绝对值分裂 *)
Lemma gtw_W_abs : forall (v : nat -> nat -> Q) (c : nat -> Q) (n m : nat),
  QleT (Qabs (gtw_offdiag v c n m)) (gtw_W v c n m).
Proof.
  intros v c n m.
  unfold gtw_offdiag, gtw_W.
  eapply QleT_trans with (y := qtw_qsum (fun i =>
      Qabs (qtw_qsum (fun j =>
        if Nat.eq_dec i j then 0%Q else c i * c j * gtw_ip v i j m)
        (Nat.pred n))) (Nat.pred n)).
  - apply qtw_qsum_abs_le.
  - apply qtw_qsum_le. intros i Hi.
    (* QleT 目标无 Proper 实例（setoid_replace 参数位置失败）——
       用基座 qtw_leT_congr_r：|Σ dec F| ≤ Σ Qabs(dec F) 且
       Σ Qabs(dec F) == W 行和，拼接即得 *)
    apply (qtw_leT_congr_r
             (Qabs (qtw_qsum (fun j => if Nat.eq_dec i j then 0%Q
                        else c i * c j * gtw_ip v i j m) (Nat.pred n)))
             (qtw_qsum (fun j => Qabs (if Nat.eq_dec i j then 0%Q
                        else c i * c j * gtw_ip v i j m)) (Nat.pred n))
             (qtw_qsum (fun j => if Nat.eq_dec i j then 0%Q
                         else Qabs (c i) * Qabs (c j) * Qabs (gtw_ip v i j m))
                (Nat.pred n))).
    + apply qtw_qsum_abs_le.
    + apply QeqT_of_Qeq. apply qtw_qsum_ext. intros j Hj.
      destruct (Nat.eq_dec i j) as [He | Hne].
      * reflexivity.
      * rewrite gtw_abs_mult. rewrite gtw_abs_mult. reflexivity.
Qed.

(* ★ 核心件 3a：A = Σ_{i≠j} c_i²·w_ij ≤ μ·S（收 c_i² 后逐行用 Hrow） *)
Lemma gtw_A_bound : forall (v : nat -> nat -> Q) (c : nat -> Q) (n m : nat) (mu : Q),
  (1 <= n)%nat ->
  (forall i : nat, (i < n)%nat ->
     QleT (qtw_qsum (fun j => if Nat.eq_dec i j then 0%Q
             else Qabs (gtw_ip v i j m)) (Nat.pred n)) mu) ->
  QleT (qtw_qsum (fun i => qtw_qsum (fun j =>
          if Nat.eq_dec i j then 0%Q
          else c i * c i * Qabs (gtw_ip v i j m)) (Nat.pred n)) (Nat.pred n))
    (mu * gtw_S c n).
Proof.
  intros v c n m mu Hn1 Hrow.
  eapply QleT_trans with (y := qtw_qsum (fun i => mu * (c i * c i)) (Nat.pred n)).
  - (* 收 c_i² 入行和：QleT 目标无 Proper 实例，走 qtw_leT_congr_l *)
    apply (qtw_leT_congr_l
             (qtw_qsum (fun i => c i * c i *
                  qtw_qsum (fun j => if Nat.eq_dec i j then 0%Q
                              else Qabs (gtw_ip v i j m)) (Nat.pred n)) (Nat.pred n))
             (qtw_qsum (fun i => mu * (c i * c i)) (Nat.pred n))
             (qtw_qsum (fun i => qtw_qsum (fun j =>
                  if Nat.eq_dec i j then 0%Q
                  else c i * c i * Qabs (gtw_ip v i j m)) (Nat.pred n)) (Nat.pred n))).
    + apply qtw_qsum_le. intros i Hi.
      assert (Hin : (i < n)%nat) by lia.
      specialize (Hrow i Hin).
      apply (qtw_leT_congr_r
               (c i * c i * qtw_qsum (fun j => if Nat.eq_dec i j then 0%Q
                                else Qabs (gtw_ip v i j m)) (Nat.pred n))
               (c i * c i * mu) (mu * (c i * c i))).
      * apply (Qmult_leT_compat_l
                 (qtw_qsum (fun j => if Nat.eq_dec i j then 0%Q
                           else Qabs (gtw_ip v i j m)) (Nat.pred n))
                 mu (c i * c i)).
        -- apply Qsqr_nonnegT.
        -- exact Hrow.
      * apply QeqT_of_Qeq. ring.
    + apply QeqT_of_Qeq. apply qtw_qsum_ext. intros i Hi.
      rewrite <- (qtw_qsum_scale (c i * c i)
                    (fun j => if Nat.eq_dec i j then 0%Q
                              else Qabs (gtw_ip v i j m)) (Nat.pred n)).
      apply qtw_qsum_ext. intros j Hj.
      destruct (Nat.eq_dec i j); ring.
  - (* Σ μ·c_i² = μ·S：congr_r + QeqT *)
    apply (qtw_leT_congr_r
             (qtw_qsum (fun i => mu * (c i * c i)) (Nat.pred n))
             (qtw_qsum (fun i => mu * (c i * c i)) (Nat.pred n))
             (mu * gtw_S c n)).
    + apply QleT_refl.
    + apply QeqT_of_Qeq.
      exact (qtw_qsum_scale mu (fun i => c i * c i) (Nat.pred n)).
Qed.

(* ★ 核心件 3b：W ≤ μ·S（AM–GM 装配 + B==A 对称化 + 2W 正因子消去）
   装配纪律：大和项 remember 成 XQ/YQ/AQ/BQ（Leibniz eqn），Qle 目标
   上的同等化一律 Leibniz rewrite / setoid_replace，绝不裸 rewrite Qeq *)
Lemma gtw_W_bound : forall (v : nat -> nat -> Q) (c : nat -> Q) (n m : nat) (mu : Q),
  (1 <= n)%nat ->
  (forall i : nat, (i < n)%nat ->
     QleT (qtw_qsum (fun j => if Nat.eq_dec i j then 0%Q
             else Qabs (gtw_ip v i j m)) (Nat.pred n)) mu) ->
  QleT (gtw_W v c n m) (mu * gtw_S c n).
Proof.
  intros v c n m mu Hn1 Hrow.
  apply Qle_to_QleT.
  assert (H2le : Qle (gtw_W v c n m * 2) ((mu * gtw_S c n) * 2)).
  { (* 第 1 步：2·W == X，X = Σ_{i≠j} (2|c_i||c_j|)·w_ij *)
    assert (H2W0 : (2 * gtw_W v c n m)%Q ==
            qtw_qsum (fun i => qtw_qsum (fun j =>
              if Nat.eq_dec i j then 0%Q
              else (2 * (Qabs (c i) * Qabs (c j))) * Qabs (gtw_ip v i j m))
              (Nat.pred n)) (Nat.pred n)).
    { unfold gtw_W.
      rewrite <- (qtw_qsum_scale 2 (fun i => qtw_qsum (fun j =>
          if Nat.eq_dec i j then 0%Q
          else Qabs (c i) * Qabs (c j) * Qabs (gtw_ip v i j m))
          (Nat.pred n)) (Nat.pred n)).
      apply qtw_qsum_ext. intros i Hi.
      rewrite <- (qtw_qsum_scale 2 (fun j =>
          if Nat.eq_dec i j then 0%Q
          else Qabs (c i) * Qabs (c j) * Qabs (gtw_ip v i j m))
          (Nat.pred n)).
      apply qtw_qsum_ext. intros j Hj.
      destruct (Nat.eq_dec i j); ring. }
    assert (H2W : (gtw_W v c n m * 2)%Q ==
            qtw_qsum (fun i => qtw_qsum (fun j =>
              if Nat.eq_dec i j then 0%Q
              else (2 * (Qabs (c i) * Qabs (c j))) * Qabs (gtw_ip v i j m))
              (Nat.pred n)) (Nat.pred n)).
    { apply (Qeq_trans (gtw_W v c n m * 2) (2 * gtw_W v c n m)).
      - ring.
      - exact H2W0. }
    remember (qtw_qsum (fun i => qtw_qsum (fun j =>
        if Nat.eq_dec i j then 0%Q
        else (2 * (Qabs (c i) * Qabs (c j))) * Qabs (gtw_ip v i j m))
        (Nat.pred n)) (Nat.pred n)) as XQ eqn:HdX.
    remember (qtw_qsum (fun i => qtw_qsum (fun j =>
        if Nat.eq_dec i j then 0%Q
        else (c i * c i + c j * c j) * Qabs (gtw_ip v i j m))
        (Nat.pred n)) (Nat.pred n)) as YQ eqn:HdY.
    remember (qtw_qsum (fun i => qtw_qsum (fun j =>
        if Nat.eq_dec i j then 0%Q
        else c i * c i * Qabs (gtw_ip v i j m)) (Nat.pred n)) (Nat.pred n))
      as AQ eqn:HdA.
    remember (qtw_qsum (fun i => qtw_qsum (fun j =>
        if Nat.eq_dec i j then 0%Q
        else c j * c j * Qabs (gtw_ip v i j m)) (Nat.pred n)) (Nat.pred n))
      as BQ eqn:HdB.
    (* remember 同时抽象了目标与既有假设：H2W 已是 W*2 == XQ 形态 *)
    (* 第 2 步：X ≤ Y，逐点 AM–GM *)
    assert (HXY : Qle XQ YQ).
    { rewrite HdX. rewrite HdY.
      apply QleT_to_Qle. apply qtw_qsum_le. intros i Hi.
      apply qtw_qsum_le. intros j Hj.
      destruct (Nat.eq_dec i j) as [He | Hne].
      - (* 对角位：dec 包两侧，两边同为 0 *)
        apply QleT_refl.
      - (* AM–GM：2|c_i||c_j| ≤ c_i²+c_j²，乘 w ≥ 0 *)
        apply Qle_to_QleT.
        apply (Qmult_le_compat_r (2 * (Qabs (c i) * Qabs (c j)))
                 (c i * c i + c j * c j) (Qabs (gtw_ip v i j m))).
        + apply qtw_amgm_abs.
        + apply Qabs_nonneg. }
    (* 第 3 步：Y == A + B（qsum 函数参数位无 pointwise morphism 实例，
       嵌套 rewrite 不可用——显式实例 exact + 顶层 plus apply） *)
    assert (HY : YQ == AQ + BQ).
    { rewrite HdY. rewrite HdA. rewrite HdB.
      transitivity (qtw_qsum (fun i => qtw_qsum (fun j =>
            (if Nat.eq_dec i j then 0%Q else c i * c i * Qabs (gtw_ip v i j m))
            + (if Nat.eq_dec i j then 0%Q else c j * c j * Qabs (gtw_ip v i j m)))
            (Nat.pred n)) (Nat.pred n)).
      - apply qtw_qsum_ext. intros i Hi. apply qtw_qsum_ext. intros j Hj.
        destruct (Nat.eq_dec i j); ring.
      - transitivity (qtw_qsum (fun i => qtw_qsum (fun j =>
              if Nat.eq_dec i j then 0%Q else c i * c i * Qabs (gtw_ip v i j m))
              (Nat.pred n)
            + qtw_qsum (fun j =>
              if Nat.eq_dec i j then 0%Q else c j * c j * Qabs (gtw_ip v i j m))
              (Nat.pred n)) (Nat.pred n)).
        + exact (qtw_qsum_ext
                   (fun i => qtw_qsum (fun j =>
                      (if Nat.eq_dec i j then 0%Q else c i * c i * Qabs (gtw_ip v i j m))
                      + (if Nat.eq_dec i j then 0%Q else c j * c j * Qabs (gtw_ip v i j m)))
                      (Nat.pred n))
                   (fun i => qtw_qsum (fun j =>
                      if Nat.eq_dec i j then 0%Q else c i * c i * Qabs (gtw_ip v i j m))
                      (Nat.pred n)
                    + qtw_qsum (fun j =>
                      if Nat.eq_dec i j then 0%Q else c j * c j * Qabs (gtw_ip v i j m))
                      (Nat.pred n))
                   (Nat.pred n)
                   (fun i _ => qtw_qsum_plus
                       (fun j => if Nat.eq_dec i j then 0%Q
                                 else c i * c i * Qabs (gtw_ip v i j m))
                       (fun j => if Nat.eq_dec i j then 0%Q
                                 else c j * c j * Qabs (gtw_ip v i j m))
                       (Nat.pred n))).
        + apply qtw_qsum_plus. }
    (* 第 4 步：B == A（swap + dec 对齐 + 内积交换律） *)
    assert (HBA : BQ == AQ).
    { rewrite HdB. rewrite HdA.
      transitivity (qtw_qsum (fun j => qtw_qsum (fun i =>
          if Nat.eq_dec i j then 0%Q
          else c j * c j * Qabs (gtw_ip v i j m)) (Nat.pred n)) (Nat.pred n)).
      - exact (qtw_qsum_swap (fun i j => if Nat.eq_dec i j then 0%Q
                   else c j * c j * Qabs (gtw_ip v i j m))
                 (Nat.pred n) (Nat.pred n)).
      - apply qtw_qsum_ext. intros i Hi. apply qtw_qsum_ext. intros j Hj.
        destruct (Nat.eq_dec j i) as [He1 | Hne1];
          destruct (Nat.eq_dec i j) as [He2 | Hne2].
        + reflexivity.
        + exfalso. lia.
        + exfalso. lia.
        + rewrite gtw_ip_comm. reflexivity. }
    (* 第 5 步：A ≤ μS *)
    assert (HA : Qle AQ (mu * gtw_S c n)).
    { rewrite HdA. apply QleT_to_Qle. apply (gtw_A_bound v c n m mu Hn1 Hrow). }
    (* 链：2W == X ≤ Y == A + B ≤ μS + μS == (μS)·2（Qle 无 transitivity
       战术注册——显式 Qle_trans） *)
    apply (Qle_trans (gtw_W v c n m * 2) XQ).
    - setoid_replace (gtw_W v c n m * 2) with XQ by exact H2W.
      apply Qle_refl.
    - apply (Qle_trans XQ YQ).
      + exact HXY.
      + setoid_replace YQ with (AQ + BQ) by exact HY.
        setoid_replace ((mu * gtw_S c n) * 2)
          with (mu * gtw_S c n + mu * gtw_S c n) by ring.
        apply Qplus_le_compat.
        * exact HA.
        * setoid_replace BQ with AQ by exact HBA.
          exact HA. }
  apply (Qmult_lt_0_le_reg_r (gtw_W v c n m) (mu * gtw_S c n) 2).
  - unfold Qlt. simpl. lia.
  - exact H2le.
Qed.

Lemma gtw_offdiag_abs_bound :
  forall (v : nat -> nat -> Q) (c : nat -> Q) (n m : nat) (mu : Q),
  (1 <= n)%nat ->
  (forall i : nat, (i < n)%nat ->
     QleT (qtw_qsum (fun j => if Nat.eq_dec i j then 0%Q
             else Qabs (gtw_ip v i j m)) (Nat.pred n)) mu) ->
  QleT (Qabs (gtw_offdiag v c n m)) (mu * gtw_S c n).
Proof.
  intros v c n m mu Hn1 Hrow.
  apply QleT_trans with (y := gtw_W v c n m).
  - apply gtw_W_abs.
  - apply gtw_W_bound.
    + exact Hn1.
    + exact Hrow.
Qed.

(* ############ §G4 最终定理（Set 层结论）与 sigT 正 gap 见证 ############ *)

(* ★ 最终定理：Gershgorin 框架能量界，结论 Set 层 And-of-QleT *)
Theorem gershgorin_frame_mu_qtw (n m : nat) (v : nat -> nat -> Q) (mu : Q)
  (Hn1 : (1 <= n)%nat) (Hm1 : (1 <= m)%nat)
  (Hunit : forall i : nat, (i < n)%nat ->
     QeqT (qtw_qsum (fun k => v i k * v i k) (Nat.pred m)) (1#1)%Q)
  (Hrow : forall i : nat, (i < n)%nat ->
     QleT (qtw_qsum (fun j => if Nat.eq_dec i j then 0%Q
             else Qabs (gtw_ip v i j m)) (Nat.pred n)) mu)
  (c : nat -> Q) :
  And (QleT ((1 - mu) * gtw_S c n)%Q (gtw_Fsq v c n m))
      (QleT (gtw_Fsq v c n m) ((1 + mu) * gtw_S c n)%Q).
Proof.
  assert (Hsplit : gtw_Fsq v c n m == gtw_S c n + gtw_offdiag v c n m)
    by (apply (gtw_Fsq_split v c n m Hn1 Hunit)).
  assert (Hb : Qle (Qabs (gtw_offdiag v c n m)) (mu * gtw_S c n))
    by (apply QleT_to_Qle; apply (gtw_offdiag_abs_bound v c n m mu Hn1 Hrow)).
  split.
  - (* 下界：(1−μ)·S = S − μS ≤ S + offdiag *)
    apply Qle_to_QleT.
    setoid_replace ((1 - mu) * gtw_S c n)%Q
      with (gtw_S c n + (- (mu * gtw_S c n))) by ring.
    setoid_replace (gtw_Fsq v c n m)
      with (gtw_S c n + gtw_offdiag v c n m) by exact Hsplit.
    apply Qplus_le_compat.
    + apply Qle_refl.
    + apply (Qle_trans (- (mu * gtw_S c n)) (- Qabs (gtw_offdiag v c n m))).
      * apply Qopp_le_compat. exact Hb.
      * apply gtw_neg_abs_le.
  - (* 上界：S + offdiag ≤ S + μS = (1+μ)·S *)
    apply Qle_to_QleT.
    setoid_replace ((1 + mu) * gtw_S c n)%Q
      with (gtw_S c n + (mu * gtw_S c n)) by ring.
    setoid_replace (gtw_Fsq v c n m)
      with (gtw_S c n + gtw_offdiag v c n m) by exact Hsplit.
    apply Qplus_le_compat.
    + apply Qle_refl.
    + apply (Qle_trans (gtw_offdiag v c n m) (Qabs (gtw_offdiag v c n m))).
      * apply gtw_abs_ge.
      * exact Hb.
Defined.

(* ★ sigT 数据件：μ < 1 时正 gap d := 1−μ 的见证 + 下界证书对 *)
Definition gtw_gap_witness (n m : nat) (v : nat -> nat -> Q) (mu : Q)
  (Hn1 : (1 <= n)%nat) (Hm1 : (1 <= m)%nat)
  (Hunit : forall i : nat, (i < n)%nat ->
     QeqT (qtw_qsum (fun k => v i k * v i k) (Nat.pred m)) (1#1)%Q)
  (Hrow : forall i : nat, (i < n)%nat ->
     QleT (qtw_qsum (fun j => if Nat.eq_dec i j then 0%Q
             else Qabs (gtw_ip v i j m)) (Nat.pred n)) mu)
  (Hmu1 : QltT mu (1#1)%Q)
  (c : nat -> Q) :
  sigT (fun d : Q => And (QltT 0%Q d) (QleT (d * gtw_S c n)%Q (gtw_Fsq v c n m))).
Proof.
  exists ((1 - mu)%Q).
  split.
  - assert (Hlt : mu < (1#1)%Q) by (apply QltT_to_Qlt; exact Hmu1).
    apply Qlt_to_QltT. lra.
  - exact (fst (gershgorin_frame_mu_qtw n m v mu Hn1 Hm1 Hunit Hrow c)).
Defined.

(* ############ §G5 可执行冒烟实例 + 提取 + 审计 ############ *)

(* 2×2 恒等框架（单位行、零离对角）→ μ = 0 时 F² == S、W == 0 *)
Definition gtw_smoke_v (i k : nat) : Q :=
  if Nat.eq_dec i k then (1#1)%Q else (0#1)%Q.
Definition gtw_smoke_c (i : nat) : Q := ((Z.of_nat i + 1) # 1)%Q.

Definition gtw_smoke_data : bool :=
  Qeq_bool (gtw_Fsq gtw_smoke_v gtw_smoke_c 2 3) (gtw_S gtw_smoke_c 2)
  && Qeq_bool (gtw_W gtw_smoke_v gtw_smoke_c 2 3) (0#1)%Q.

Definition gtw_smoke_eval : bool :=
  Qeq_bool ((1 - (0#1))%Q * gtw_S gtw_smoke_c 2) (gtw_Fsq gtw_smoke_v gtw_smoke_c 2 3).

Definition gtw_smoke_hunit (i : nat) (Hi : (i < 2)%nat) :
  QeqT (qtw_qsum (fun k => gtw_smoke_v i k * gtw_smoke_v i k) (Nat.pred 3)) (1#1)%Q.
Proof.
  destruct i as [|[|i]].
  - apply qtw_eqT_of_eq_true. vm_compute. reflexivity.
  - apply qtw_eqT_of_eq_true. vm_compute. reflexivity.
  - exfalso. lia.
Defined.

Definition gtw_smoke_hrow (i : nat) (Hi : (i < 2)%nat) :
  QleT (qtw_qsum (fun j => if Nat.eq_dec i j then 0%Q
          else Qabs (gtw_ip gtw_smoke_v i j 3)) (Nat.pred 2)) (0#1)%Q.
Proof.
  destruct i as [|[|i]].
  - right. apply qtw_eqT_of_eq_true. vm_compute. reflexivity.
  - right. apply qtw_eqT_of_eq_true. vm_compute. reflexivity.
  - exfalso. lia.
Defined.

(* 主定理实例化出的 Set 层证书数据（2×3 恒等框架、μ=0、c = 1,2） *)
Definition gtw_smoke_cert :
  And (QleT ((1 - (0#1))%Q * gtw_S gtw_smoke_c 2)%Q (gtw_Fsq gtw_smoke_v gtw_smoke_c 2 3))
      (QleT (gtw_Fsq gtw_smoke_v gtw_smoke_c 2 3) ((1 + (0#1))%Q * gtw_S gtw_smoke_c 2)%Q) :=
  gershgorin_frame_mu_qtw 2 3 gtw_smoke_v (0#1)%Q
    (Nat.le_succ_diag_r 1)
    (Nat.le_trans 1 2 3 (Nat.le_succ_diag_r 1) (Nat.le_succ_diag_r 2))
    gtw_smoke_hunit gtw_smoke_hrow gtw_smoke_c.

Extraction "gershgorin_qtw.ml" gershgorin_frame_mu_qtw gtw_gap_witness
  gtw_ip gtw_S gtw_Fsq gtw_offdiag gtw_W gtw_smoke_data gtw_smoke_eval.

Print Assumptions gershgorin_frame_mu_qtw.
Print Assumptions gtw_gap_witness.
Print Assumptions gtw_qsum_scale_r.
Print Assumptions gtw_qsum_sq_expand.
Print Assumptions gtw_ip_comm.
Print Assumptions gtw_abs_mult.
Print Assumptions gtw_abs_ge.
Print Assumptions gtw_neg_abs_le.
Print Assumptions gtw_Fsq_expand.
Print Assumptions gtw_Fsq_split.
Print Assumptions gtw_W_abs.
Print Assumptions gtw_A_bound.
Print Assumptions gtw_W_bound.
Print Assumptions gtw_offdiag_abs_bound.
Print Assumptions gtw_smoke_cert.
