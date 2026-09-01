(* ============================================================
   Z2b：Zarith 第二阶段——int63 镜像一致性组合定理
   probe_z2b_int63mirror.v（z 区构造性轨道，2026-09-01）

   组合 CS-16 安全域（probe_safe_domain：zprod / W63 / in_w63 /
   no_overflow_consistent）× CS-22 Z 版检查器（probe_z_frame_check：
   zfc_zdots / zfc_check / zfc_qsum / zfc_check_spec），给论文 A §6
   威胁模型的「运行时 int 镜像信任鸿沟」以机器检查闭合：
   安全域内，mod-2^63 镜像判定与 Z 精确判定**布尔相等**，且
   运行时通过 ⟹ Q 层行和 ≤ 4/5（Coq 健全性穿透到运行时语义）。

   数学内容：
     M1 63-bit 语义模型：z2b_wrap x := x mod W63（OCaml int 逐操作
        回绕的 Coq 侧模型；安全域保持全部中间量 ∈ [0, 2^63)，
        带符号/无符号回绕之别不进入——如实声明）。
        除法：模型取 Z.div（下取整）；OCaml / 为向零截断——
        两者在非负域一致，安全域前提恰好排除负数分支。
     M2 镜像判定器：z2b_dots63 / z2b_check63——zfc 逐操作回绕同构
        （每步乘/加/除后 wrap）。
     M3 ★ 非平凡核：累加器级 mod 一致性——z2b_step_ok（每项
        乘积与每级部分和全部 ∈ [0, W63) 的精确逐点前提）下，
        镜像逐层 wrap 消去 ⟹ z2b_dots63 = 精确 zdots（shift 引理
        把带累加器的逐点前提平移到零基）。
     M4 ★★ 最终定理：z2b_safety nums dens ->
        z2b_check63 nums dens = zfc_check nums dens（镜像布尔 ≡ 精确布尔）。
     M5 端到端健全性推论：安全域内 z2b_check63 = true -> Qle qsum 4/5
        （经 zfc_check_spec——运行时判定携带 Coq 证明的语义承诺）。
     M6 sigT 决策证书（Set 层，可提取）：z2b_decision_cert——
        { r : bool & r = true <-> Qle qsum (4/5) }，r 即运行时判定。
     M7 实例：C=4 行和 [39;159;639]/[120;1200;10500]——safety 封口 +
        镜像/精确双 true + 端到端 Qle；溢出发散演示
        [2^63]/[4]——安全域外镜像判 true / 精确判 false（§6 的
        15.7% 分歧叙事的第一个机器实证）。
     M8 静态成员 bool 判定 z2b_safe_bool（分母/连乘 in_w63，可提取；
        全量 z2b_safety 对具体实例由计算反射封口——M7）。

   纪律：纯 nat/Z/Q 构造性（零实数、零经典公理、零 Admitted 终态）；
   z2b_ 前缀防合并撞名（E144④）；审计块全部置尾（E207）。
   依赖：probe_safe_domain + probe_z_frame_check（同区跨探针 Require，
   probe_g8<-probe_uncertainty_cr 先例）。
   提取：z2b_int63mirror.ml（z2b_check63 / z2b_safe_bool /
   z2b_c4_runtime / z2b_overflow_demo）。
   ============================================================ *)
Require Import Stdlib.QArith.QArith.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Lists.List.
Import ListNotations.

Require Import probe_safe_domain.
Require Import probe_z_frame_check.

Local Open Scope Z_scope.

(* ============================================================
   M1：63-bit 语义模型
   ============================================================ *)

Definition z2b_wrap (x : Z) : Z := x mod W63.

Lemma z2b_wrap_id : forall x, (0 <= x < W63)%Z -> z2b_wrap x = x.
Proof. intros x H. unfold z2b_wrap. apply no_overflow_consistent. lia. Qed.

(* 除法入界：正除数下 P/d 不超过 P *)
Lemma z2b_div_in : forall P d, (0 <= P < W63)%Z -> (0 < d)%Z ->
  (0 <= P / d < W63)%Z.
Proof.
  intros P d HP Hd.
  assert (H1 : (P / d <= P)%Z).
  { apply Z.div_le_upper_bound; try lia. nia. }
  assert (H2 : (0 <= P / d)%Z) by (apply Z.div_pos; lia).
  lia.
Qed.

(* ============================================================
   M2：镜像判定器（zfc 逐操作回绕同构）
   ============================================================ *)

(* P 按调用方传入「已回绕」的连乘值（z2b_check63 传 wrap(zprod dens)）；
   递归传递同一 P——OCaml 侧 P 存于寄存器、已是回绕值，不重复回绕 *)
Fixpoint z2b_dots63 (P : Z) (nums dens : list Z) : Z :=
  match nums, dens with
  | n :: ns, d :: ds =>
      z2b_wrap (z2b_wrap (z2b_wrap n * z2b_wrap (P / d)) + z2b_dots63 P ns ds)
  | _, _ => 0
  end.

Definition z2b_check63 (nums dens : list Z) : bool :=
  Z.leb (z2b_wrap (5 * z2b_dots63 (z2b_wrap (zprod dens)) nums dens))
        (z2b_wrap (4 * z2b_wrap (zprod dens))).

(* ============================================================
   M3 ★ 非平凡核：累加器级 mod 一致性
   ============================================================ *)

(* 安全逐点前提：每项乘积与每级部分和都落在 [0, W63) *)
Fixpoint z2b_step_ok (P acc : Z) (nums dens : list Z) : Prop :=
  match nums, dens with
  | n :: ns, d :: ds =>
      (0 < d < W63)%Z /\ (0 <= acc < W63)%Z /\ (0 <= n < W63)%Z
      /\ (0 <= n * (P / d) < W63)%Z
      /\ (0 <= acc + n * (P / d) < W63)%Z
      /\ z2b_step_ok P (acc + n * (P / d)) ns ds
  | _, _ => (0 <= acc < W63)%Z
  end.

(* 总量入界：acc + 精确全和 ∈ [0, W63)（逐级前提链的收口） *)
Lemma z2b_step_ok_total : forall P nums acc dens,
  z2b_step_ok P acc nums dens ->
  (0 <= acc + zfc_zdots P nums dens < W63)%Z.
Proof.
  intros P nums. induction nums as [| n ns IH]; intros acc dens H.
  - destruct dens as [| d ds]; simpl in H |- *; lia.
  - destruct dens as [| d ds].
    + simpl in H |- *. lia.
    + simpl in H. cbn [zfc_zdots].
      destruct H as (Hd & Hacc & Hn & Hterm & Hsum & Hrest).
      specialize (IH (acc + n * (P / d)) ds Hrest).
      lia.
Qed.

(* 前提平移（双累加器单调版）：零基部分和恒不超过带累加器部分和，
   故入界继承 *)
Lemma z2b_step_ok_shift : forall P nums a b dens,
  (0 <= a)%Z -> (a <= b)%Z ->
  z2b_step_ok P b nums dens -> z2b_step_ok P a nums dens.
Proof.
  intros P nums. induction nums as [| n ns IH]; intros a b dens Ha Hab H.
  - destruct dens as [| d ds]; cbn [z2b_step_ok] in H |- *;
      assert (HW : (0 < W63)%Z) by (unfold W63; lia); lia.
  - destruct dens as [| d ds].
    + cbn [z2b_step_ok] in H |- *;
      assert (HW : (0 < W63)%Z) by (unfold W63; lia); lia.
    + cbn [z2b_step_ok] in H |- *.
      destruct H as (Hd & Hb & Hn & Hterm & Hsum & Hrest).
      assert (HW : (0 < W63)%Z) by (unfold W63; lia).
      split; [exact Hd |].
      split; [lia |].
      split; [exact Hn |].
      split; [lia |].
      split; [lia |].
      apply (IH (a + n * (P / d)) (b + n * (P / d)) ds); [lia | lia | exact Hrest].
Qed.

(* ★ 核心引理：安全逐点前提下，镜像 zdots 的逐层 wrap 全部消去，
   镜像 = 精确 *)
Lemma z2b_dots63_exact : forall P nums dens,
  (0 < P < W63)%Z -> z2b_step_ok P 0 nums dens ->
  z2b_dots63 P nums dens = zfc_zdots P nums dens.
Proof.
  intros P nums. induction nums as [| n ns IH]; intros dens HP H.
  - destruct dens as [| d ds]; reflexivity.
  - destruct dens as [| d ds].
    + reflexivity.
    + pose proof (z2b_step_ok_total P (n :: ns) 0 (d :: ds) H) as Ht.
      cbn [z2b_step_ok] in H.
      destruct H as (Hd & Hacc & Hn & Hterm & Hsum & Hrest).
      assert (Hnw : z2b_wrap n = n) by (apply z2b_wrap_id; lia).
      assert (Hdw : z2b_wrap (P / d) = P / d).
      { apply z2b_wrap_id. apply z2b_div_in; lia. }
      assert (Htw : z2b_wrap (n * (P / d)) = n * (P / d))
        by (apply z2b_wrap_id; lia).
      assert (Hshift : z2b_step_ok P 0 ns ds).
      { apply (z2b_step_ok_shift P ns 0 (0 + n * (P / d)) ds);
          [lia | lia | exact Hrest]. }
      assert (HIH : z2b_dots63 P ns ds = zfc_zdots P ns ds)
        by (apply IH; [exact HP | exact Hshift]).
      cbn [z2b_dots63]. rewrite Hnw. rewrite Hdw. rewrite Htw. rewrite HIH.
      cbn [zfc_zdots] in Ht.
      assert (Hzw : (0 <= n * (P / d) + zfc_zdots P ns ds < W63)%Z) by lia.
      rewrite (z2b_wrap_id (n * (P / d) + zfc_zdots P ns ds) Hzw).
      reflexivity.
Qed.

(* ============================================================
   M4 ★★ 最终定理：镜像布尔 ≡ 精确布尔（安全域内）
   ============================================================ *)

Lemma z2b_zprod_zfc : forall l, zprod l = zfc_zprod l.
Proof. induction l as [| d r IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

(* 安全域全前提：静态入界 + 逐点动态入界 + 终判操作数入界 +
   zfc_check_spec 的可除性前提 *)
Definition z2b_safety (nums dens : list Z) : Prop :=
  Forall (fun d => (0 < d < W63)%Z) dens
  /\ (forall e, In e dens -> exists k, zprod dens = e * k)
  /\ (0 < zprod dens < W63)%Z
  /\ z2b_step_ok (zprod dens) 0 nums dens
  /\ (0 <= 5 * zfc_zdots (zprod dens) nums dens < W63)%Z
  /\ (0 <= 4 * zprod dens < W63)%Z.

Theorem z2b_check63_eq : forall nums dens,
  z2b_safety nums dens ->
  z2b_check63 nums dens = zfc_check nums dens.
Proof.
  intros nums dens Hs.
  destruct Hs as [Hd [Hdiv [HP [Hstep [H5 H4]]]]].
  unfold z2b_check63, zfc_check.
  assert (HPw : z2b_wrap (zprod dens) = zprod dens) by (apply z2b_wrap_id; lia).
  rewrite HPw.
  assert (HDOTS : z2b_dots63 (zprod dens) nums dens
                  = zfc_zdots (zprod dens) nums dens).
  { apply z2b_dots63_exact; [lia | exact Hstep]. }
  rewrite HDOTS.
  assert (H5w : z2b_wrap (5 * zfc_zdots (zprod dens) nums dens)
                = 5 * zfc_zdots (zprod dens) nums dens) by (apply z2b_wrap_id; lia).
  assert (H4w : z2b_wrap (4 * zprod dens) = 4 * zprod dens)
    by (apply z2b_wrap_id; lia).
  rewrite H5w. rewrite H4w. rewrite z2b_zprod_zfc. reflexivity.
Qed.

(* ============================================================
   M5：端到端健全性推论——运行时判定携带 Coq 语义承诺
   ============================================================ *)

(* 安全域 ⟹ zfc_check_spec 的纯正性前提 *)
Lemma z2b_safety_pos : forall nums dens, z2b_safety nums dens ->
  Forall (fun d : Z => (0 < d)%Z) dens.
Proof.
  intros nums dens Hs. destruct Hs as [Hd _].
  induction dens as [| d ds IHd].
  - constructor.
  - inversion Hd as [| d0 ds0 Hd0 Hdr]; subst.
    constructor.
    + destruct Hd0 as [H1 _]. exact H1.
    + exact (IHd Hdr).
Qed.

Theorem z2b_end_to_end_sound : forall nums dens,
  z2b_safety nums dens ->
  z2b_check63 nums dens = true ->
  Qle (zfc_qsum nums dens) (Qmake 4 5).
Proof.
  intros nums dens Hs Hchk.
  destruct Hs as [Hd [Hdiv [HP [Hstep [H5 H4]]]]].
  assert (Hs' : z2b_safety nums dens)
    by (exact (conj Hd (conj Hdiv (conj HP (conj Hstep (conj H5 H4)))))).
  assert (Hdivf : forall e, In e dens -> exists k, zfc_zprod dens = e * k).
  { intros e He. destruct (Hdiv e He) as [k Hk]. exists k.
    rewrite <- z2b_zprod_zfc. exact Hk. }
  assert (HPf : (0 < zfc_zprod dens)%Z) by (rewrite <- z2b_zprod_zfc; lia).
  rewrite (z2b_check63_eq nums dens Hs') in Hchk.
  apply (proj2 (zfc_check_spec nums dens (z2b_safety_pos nums dens Hs') Hdivf HPf)).
  exact Hchk.
Qed.

(* ============================================================
   M6：sigT 决策证书（Set 层，可提取）
   ============================================================ *)

Definition z2b_decision (nums dens : list Z) : bool :=
  z2b_check63 nums dens.

Theorem z2b_decision_cert : forall nums dens,
  z2b_safety nums dens ->
  { r : bool & (r = true <-> Qle (zfc_qsum nums dens) (Qmake 4 5)) }.
Proof.
  intros nums dens Hs.
  destruct Hs as [Hd [Hdiv [HP [Hstep [H5 H4]]]]].
  assert (Hs' : z2b_safety nums dens)
    by (exact (conj Hd (conj Hdiv (conj HP (conj Hstep (conj H5 H4)))))).
  assert (Hdivf : forall e, In e dens -> exists k, zfc_zprod dens = e * k).
  { intros e He. destruct (Hdiv e He) as [k Hk]. exists k.
    rewrite <- z2b_zprod_zfc. exact Hk. }
  assert (HPf : (0 < zfc_zprod dens)%Z) by (rewrite <- z2b_zprod_zfc; lia).
  exists (z2b_decision nums dens). split.
  - intro Hr. unfold z2b_decision in Hr.
    rewrite (z2b_check63_eq nums dens Hs') in Hr.
    apply (proj2 (zfc_check_spec nums dens (z2b_safety_pos nums dens Hs') Hdivf HPf)).
    exact Hr.
  - intro Hq. unfold z2b_decision.
    rewrite (z2b_check63_eq nums dens Hs').
    apply (proj1 (zfc_check_spec nums dens (z2b_safety_pos nums dens Hs') Hdivf HPf)).
    exact Hq.
Qed.

(* ============================================================
   M8：静态成员 bool 判定（可提取；动态逐点前提由实例计算反射封口）
   ============================================================ *)

Definition z2b_safe_bool (nums dens : list Z) : bool :=
  forallb (fun d => andb (Z.ltb 0 d) (in_w63 d)) dens
  && in_w63 (zprod dens).

(* ============================================================
   M7：实例——C=4 行和 + 溢出发散演示
   ============================================================ *)

Lemma z2b_c4_safety : z2b_safety [39; 159; 639] [120; 1200; 10500].
Proof.
  assert (Hz : zprod [120; 1200; 10500] = 1512000000) by reflexivity.
  assert (Hd1 : (1512000000 / 120)%Z = 12600000) by reflexivity.
  assert (Hd2 : (1512000000 / 1200)%Z = 1260000) by reflexivity.
  assert (Hd3 : (1512000000 / 10500)%Z = 144000) by reflexivity.
  assert (Hzd : zfc_zdots (zprod [120; 1200; 10500]) [39; 159; 639] [120; 1200; 10500]
                = 783756000) by reflexivity.
  assert (HW : (0 < W63)%Z) by (unfold W63; lia).
  assert (HA : Forall (fun d : Z => (0 < d < W63)%Z) [120; 1200; 10500]).
  { constructor.
    - unfold W63. lia.
    - constructor.
      + unfold W63. lia.
      + constructor.
        * unfold W63. lia.
        * constructor. }
  assert (HDIV : forall e, In e [120; 1200; 10500] ->
             exists k, zprod [120; 1200; 10500] = e * k).
  { intros e He. simpl in He.
    destruct He as [He | [He | [He | []]]]; subst.
    - exists 12600000. rewrite Hz. lia.
    - exists 1260000. rewrite Hz. lia.
    - exists 144000. rewrite Hz. lia. }
  assert (HP : (0 < zprod [120; 1200; 10500] < W63)%Z)
    by (rewrite Hz; unfold W63; lia).
  assert (HST : z2b_step_ok (zprod [120; 1200; 10500]) 0 [39; 159; 639] [120; 1200; 10500]).
  { cbn [z2b_step_ok]. rewrite Hz. rewrite Hd1. rewrite Hd2. rewrite Hd3.
    unfold W63. repeat split; lia. }
  assert (H5 : (0 <= 5 * zfc_zdots (zprod [120; 1200; 10500]) [39; 159; 639]
                     [120; 1200; 10500] < W63)%Z)
    by (rewrite Hzd; unfold W63; lia).
  assert (H4 : (0 <= 4 * zprod [120; 1200; 10500] < W63)%Z)
    by (rewrite Hz; unfold W63; lia).
  unfold z2b_safety.
  exact (conj HA (conj HDIV (conj HP (conj HST (conj H5 H4))))).
Qed.

Lemma z2b_c4_check63 : z2b_check63 [39; 159; 639] [120; 1200; 10500] = true.
Proof. vm_compute. reflexivity. Qed.

(* 端到端：运行时镜像判定 true ⟹ Q 层行和 ≤ 4/5（C=4 行实例） *)
Corollary z2b_c4_row3_bound : Qle (zfc_qsum [39; 159; 639] [120; 1200; 10500]) (Qmake 4 5).
Proof.
  apply (z2b_end_to_end_sound [39; 159; 639] [120; 1200; 10500] z2b_c4_safety).
  exact z2b_c4_check63.
Qed.

(* 镜像 ≡ 精确（实例封口，与 zfc_c4_row3_check 对账） *)
Corollary z2b_c4_agree : z2b_check63 [39; 159; 639] [120; 1200; 10500]
                         = zfc_check [39; 159; 639] [120; 1200; 10500].
Proof. rewrite z2b_c4_check63. rewrite zfc_c4_row3_check. reflexivity. Qed.

(* 溢出发散演示：累加器越过 2^63 时 wrap 失真——
   镜像判 true（5·2^63 项回绕），精确判 false。
   安全域前提（z2b_step_ok）恰在此处失效——§6 分歧叙事的机器实证。 *)
Definition z2b_overflow_demo : bool * bool :=
  (z2b_check63 [9223372036854775808] [4],
   zfc_check [9223372036854775808] [4]).

Lemma z2b_overflow_fst : fst z2b_overflow_demo = true.
Proof. vm_compute. reflexivity. Qed.

Lemma z2b_overflow_snd : snd z2b_overflow_demo = false.
Proof. vm_compute. reflexivity. Qed.

(* 可运行对（提取后即运行时入口；两布尔相等 = 镜像一致性实例） *)
Definition z2b_c4_runtime : bool * bool :=
  (z2b_check63 [39; 159; 639] [120; 1200; 10500],
   zfc_check [39; 159; 639] [120; 1200; 10500]).

(* ---------- 审计（E207：全部置尾） ---------- *)
Print Assumptions z2b_dots63_exact.
Print Assumptions z2b_check63_eq.
Print Assumptions z2b_end_to_end_sound.
Print Assumptions z2b_decision_cert.
Print Assumptions z2b_c4_safety.
Print Assumptions z2b_c4_row3_bound.
Print Assumptions z2b_c4_agree.
Print Assumptions z2b_overflow_fst.

(* ---------- 提取（Set 层可执行：运行时镜像入口 + 双实例 + 发散演示） ---------- *)
From Stdlib Require Import Extraction.

Extraction "z2b_int63mirror.ml" z2b_wrap z2b_dots63 z2b_check63 z2b_safe_bool
  z2b_c4_runtime z2b_overflow_demo.
