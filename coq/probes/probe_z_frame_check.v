(* ============================================================
   CS-22 Z 版检查器第一阶段：probe_z_frame_check.v
   （z 区构造性轨道，2026-08-30，待办 #2 Zarith 提取第一阶段——
   衔接 CS-16 安全域（probe_safe_domain.v））

   背景：反射检查器 frame_check_instance（nat 判定器）的运行时镜像
   此前依赖 63-bit int（CS-16 给出溢出自由安全域 + mod 一致性）。
   本模块给出 **Z 版检查器**：行和 <= 4/5 的交叉相乘判定在 Z 精确
   算术上实现（无舍入、无溢出概念），并证明其与 Q 层分数不等式的
   **健全性 + 完备性（iff）**——Zarith 提取路线（big-int 无溢出）
   的地基。第二阶段（后续）组合 CS-16 安全域给出 int63 镜像
   一致性推论。

   数学内容：
     Z0 连乘 zprod：非零性 + 按构造整除 + 正性。
     Z1 ★ 精确分摊（正分母）：Qeq (Qmake n (Z.pos pd))
        (Qmake (n * (Z.pos pP / Z.pos pd)) pP)（pd·kd = pP 时）；
        同分母合并：Qplus (Qmake n pP) (Qmake a pP) ≡ Qmake (n+a) pP。
     Z2 ★ 表示定理：全因子正 + P=zprod dens 公共倍数 ⟹
        Qeq (zfc_qsum nums dens) (zfc_qmk acc P)（acc = zdots P）。
     Z3 ★★ 检查器定理（iff）：全因子正 ⟹
        Qle qsum (Qmake 4 5) ↔ Z.leb (5·acc) (4·P) = true
        ——Z 布尔判定 ⟺ 数学命题（健全 + 完备）。
     Z4 可运行实例：C=4 行和 [39;159;639]/[120;1200;10500] -> true
        （vm_compute 反射封口）+ 健全/完备双推论。

   纪律（承 probe_safe_domain.v）：纯构造性 Z/Q 层（零实数、零经典
   公理、零 Admitted 终态）；Set 层 Fixpoint 可提取；zfc_ 前缀防合并
   撞名（E144④）。Q 分母是 positive 而 dens 是 Z——退化容忍构造器
   zfc_qmk + 全正前提桥接（正向支由前提排除，负向支不进证明路径）。
   提取：z_frame_check.ml。
   ============================================================ *)
Require Import Stdlib.QArith.QArith.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Lists.List.
Import ListNotations.

Local Open Scope Z_scope.

(* ============================================================
   Z0：连乘、非零性、按构造整除、正性
   ============================================================ *)

Fixpoint zfc_zprod (l : list Z) : Z :=
  match l with
  | [] => 1
  | d :: r => d * zfc_zprod r
  end.

Lemma zfc_zprod_neq0 : forall l : list Z,
  Forall (fun d : Z => d <> 0) l -> zfc_zprod l <> 0.
Proof.
  induction l as [| d r IH]; intros H.
  - simpl. discriminate.
  - inversion H as [| ? ? Hd Hr]; subst.
    simpl. assert (Hr0 : zfc_zprod r <> 0) by (apply IH; exact Hr).
    intro Hz. apply Hd.
    destruct (proj1 (Z.mul_eq_0 d (zfc_zprod r)) Hz) as [Hz1 | Hz2].
    + exact Hz1.
    + exfalso. apply Hr0. exact Hz2.
Qed.

Lemma zfc_zprod_divides : forall (dens : list Z) (d : Z),
  (forall e, In e dens -> e <> 0) -> In d dens ->
  exists k : Z, zfc_zprod dens = d * k.
Proof.
  intros dens d Hne Hd.
  induction dens as [| e r IH].
  - destruct Hd.
  - simpl in Hd. destruct Hd as [Hed | Hdin].
    + exists (zfc_zprod r). simpl. rewrite Hed. reflexivity.
    + assert (Hr0 : forall e0, In e0 r -> e0 <> 0)
        by (intros e0 H0; apply Hne; simpl; right; exact H0).
      destruct (IH Hr0 Hdin) as [k Hk].
      exists (e * k). simpl zfc_zprod. rewrite Hk. ring.
Qed.

Lemma zfc_pos_gt0 : forall p : positive, (0 < Z.pos p)%Z.
Proof.
  intros p. destruct (Z_lt_le_dec 0 (Z.pos p)) as [H | H]; [exact H |].
  exfalso. pose proof (Zle_0_pos p) as Hp. lia.
Qed.

Lemma zfc_zprod_pos : forall l : list Z,
  Forall (fun d : Z => (0 < d)%Z) l -> (0 < zfc_zprod l)%Z.
Proof.
  induction l as [| d r IH]; intros H.
  - simpl. lia.
  - inversion H as [| ? ? Hd Hr]; subst.
    simpl. assert (Hr0 : (0 < zfc_zprod r)%Z) by (apply IH; exact Hr).
    nia.
Qed.

(* ============================================================
   Z 版检查器（Set 层，可提取）
   ============================================================ *)

Fixpoint zfc_zdots (P : Z) (nums dens : list Z) : Z :=
  match nums, dens with
  | n :: ns, d :: ds => n * (P / d) + zfc_zdots P ns ds
  | _, _ => 0
  end.

Definition zfc_check (nums dens : list Z) : bool :=
  Z.leb (5 * zfc_zdots (zfc_zprod dens) nums dens) (4 * zfc_zprod dens).

(* Q 分母是 positive——退化容忍构造器（全正前提排除退化支） *)
Definition zfc_qmk (n d : Z) : Q :=
  match d with
  | Zpos p => Qmake n p
  | _ => Qmake n 1
  end.

Fixpoint zfc_qsum (nums dens : list Z) : Q :=
  match nums, dens with
  | n :: ns, d :: ds => Qplus (zfc_qmk n d) (zfc_qsum ns ds)
  | _, _ => Qmake 0 1
  end.

(* ============================================================
   Z1 ★ 精确分摊（正分母）+ 同分母合并
   ============================================================ *)

Lemma zfc_qsplit_pos : forall (n kd : Z) (pd pP : positive),
  (Z.pos pd * kd = Z.pos pP)%Z ->
  Qeq (Qmake n pd) (Qmake (n * (Z.pos pP / Z.pos pd)) pP).
Proof.
  intros n kd pd pP Hmul.
  unfold Qeq. cbn [Qnum Qden].
  rewrite <- Hmul.
  rewrite (Z.mul_comm (Z.pos pd) kd).
  rewrite Z.div_mul by (intro Hz; discriminate Hz).
  ring.
Qed.

Lemma zfc_qplus_same : forall (n a : Z) (pP : positive),
  Qeq (Qplus (Qmake n pP) (Qmake a pP)) (Qmake (n + a) pP).
Proof.
  intros n a pP. unfold Qeq, Qplus. cbn [Qnum Qden].
  replace (Z.pos (pP * pP)) with (Z.pos pP * Z.pos pP) by reflexivity.
  ring.
Qed.

(* ============================================================
   Z2 ★ 表示定理：qsum ≡ qmk acc P
   （填充 1：nil/退化分支 + cons 主线）
   ============================================================ *)

Theorem zfc_qsum_spec : forall (nums dens : list Z) (P : Z),
  Forall (fun d : Z => (0 < d)%Z) dens ->
  (forall e, In e dens -> exists k, P = e * k) ->
  (0 < P)%Z ->
  Qeq (zfc_qsum nums dens) (zfc_qmk (zfc_zdots P nums dens) P).
Proof.
  intros nums dens. revert nums.
  induction dens as [| d r IH]; intros nums P Hne Hdiv Hpos.
  - (* dens = []：qsum = 0/1，zdots = 0（P 分支全平） *)
    destruct nums as [| n ns]; simpl;
      destruct P as [| pP | pP];
      unfold Qeq, zfc_qmk; simpl; try (split; ring).
  - destruct nums as [| n ns].
    + (* nums = []：zdots = 0 *)
      simpl. destruct P as [| pP | pP];
        unfold Qeq, zfc_qmk; simpl; try (split; ring).
    + (* 主线：cons/cons——全正假设排除非正分支 *)
      inversion Hne as [| ? ? Hd Hr]; subst.
      assert (Hdd : exists k, P = d * k) by (apply Hdiv; simpl; left; reflexivity).
      assert (Hrd : forall e, In e r -> exists k, P = e * k)
        by (intros e0 H0; apply Hdiv; simpl; right; exact H0).
      destruct P as [| pP | pP] eqn:HP; try (exfalso; lia).
      destruct d as [| pd | pd] eqn:HdE; try (exfalso; lia).
      destruct Hdd as [kd Hkd].
      cbn [zfc_qsum zfc_zdots zfc_zprod].
      setoid_rewrite (IH ns (Z.pos pP) Hr Hrd Hpos).
      cbn [zfc_qmk].
      setoid_rewrite (zfc_qsplit_pos n kd pd pP (eq_sym Hkd)).
      cbn [zfc_qmk].
      apply zfc_qplus_same.
Qed.

(* ============================================================
   Z3 ★★ 检查器定理（iff）
   （填充 2：分子方程桥接 + 双向 Z 代数）
   ============================================================ *)

Theorem zfc_check_spec : forall (nums dens : list Z),
  Forall (fun d : Z => (0 < d)%Z) dens ->
  (forall e, In e dens -> exists k, zfc_zprod dens = e * k) ->
  (0 < zfc_zprod dens)%Z ->
  (Qle (zfc_qsum nums dens) (Qmake 4 5) <->
   Z.leb (5 * zfc_zdots (zfc_zprod dens) nums dens) (4 * zfc_zprod dens) = true).
Proof.
  intros nums dens Hne Hdiv Hpos.
  assert (Hne0 : forall e, In e dens -> e <> 0).
  { assert (Hne' : forall e, In e dens -> (0 < e)%Z) by (apply Forall_forall; exact Hne).
    intros e He. specialize (Hne' e He). lia. }
  pose proof (zfc_qsum_spec nums dens (zfc_zprod dens) Hne Hdiv Hpos) as Hspec.
  unfold Qle. cbn [Qnum Qden].
  destruct (zfc_zprod dens) as [| pP | pP] eqn:HP.
  - exfalso. lia.
  - unfold Qeq, zfc_qmk in Hspec. cbn [Qnum Qden] in Hspec.
    assert (Hpp0 : (0 < Z.pos pP)%Z) by apply zfc_pos_gt0.
    assert (Hdenq0 : (0 < Z.pos (Qden (zfc_qsum nums dens)))%Z) by apply zfc_pos_gt0.
    split.
    + (* 完备：Qle -> check = true *)
      intros Hle. apply Z.leb_le.
      assert (H0 : (Qnum (zfc_qsum nums dens) * 5) * Z.pos pP <= (4 * Z.pos (Qden (zfc_qsum nums dens))) * Z.pos pP).
      { apply (proj1 (Z.mul_le_mono_pos_r (Qnum (zfc_qsum nums dens) * 5) (4 * Z.pos (Qden (zfc_qsum nums dens))) (Z.pos pP) Hpp0)).
        exact Hle. }
      assert (Hr2 : 5 * (Qnum (zfc_qsum nums dens) * Z.pos pP) = (Qnum (zfc_qsum nums dens) * 5) * Z.pos pP) by ring.
      rewrite <- Hr2 in H0.
      rewrite Hspec in H0.
      assert (Hr4 : (4 * Z.pos (Qden (zfc_qsum nums dens))) * Z.pos pP = (4 * Z.pos pP) * Z.pos (Qden (zfc_qsum nums dens))) by ring.
      rewrite Hr4 in H0.
      assert (Hr5 : 5 * (zfc_zdots (Z.pos pP) nums dens * Z.pos (Qden (zfc_qsum nums dens))) = (5 * zfc_zdots (Z.pos pP) nums dens) * Z.pos (Qden (zfc_qsum nums dens))) by ring.
      rewrite Hr5 in H0.
      apply (proj2 (Z.mul_le_mono_pos_r (5 * zfc_zdots (Z.pos pP) nums dens) (4 * Z.pos pP) (Z.pos (Qden (zfc_qsum nums dens))) Hdenq0)).
      exact H0.
    + (* 健全：check = true -> Qle *)
      intros Hchk. apply Z.leb_le in Hchk.
      assert (H0 : (5 * zfc_zdots (Z.pos pP) nums dens) * Z.pos (Qden (zfc_qsum nums dens)) <= (4 * Z.pos pP) * Z.pos (Qden (zfc_qsum nums dens))).
      { apply (proj1 (Z.mul_le_mono_pos_r (5 * zfc_zdots (Z.pos pP) nums dens) (4 * Z.pos pP) (Z.pos (Qden (zfc_qsum nums dens))) Hdenq0)).
         exact Hchk. }
      assert (Hr1 : 5 * (zfc_zdots (Z.pos pP) nums dens * Z.pos (Qden (zfc_qsum nums dens))) = (5 * zfc_zdots (Z.pos pP) nums dens) * Z.pos (Qden (zfc_qsum nums dens))) by ring.
      rewrite <- Hr1 in H0. rewrite <- Hspec in H0.
      assert (Hr2 : 5 * (Qnum (zfc_qsum nums dens) * Z.pos pP) = (Qnum (zfc_qsum nums dens) * 5) * Z.pos pP) by ring.
      rewrite Hr2 in H0.
      assert (Hr3 : (4 * Z.pos pP) * Z.pos (Qden (zfc_qsum nums dens)) = (4 * Z.pos (Qden (zfc_qsum nums dens))) * Z.pos pP) by ring.
      rewrite Hr3 in H0.
      unfold Qle. cbn [Qnum Qden].
      apply (proj2 (Z.mul_le_mono_pos_r (Qnum (zfc_qsum nums dens) * 5) (4 * Z.pos (Qden (zfc_qsum nums dens))) (Z.pos pP) Hpp0)).
      exact H0.
  - (* Zneg：P < 0 与 Hpos : 0 < P 矛盾 *)
    exfalso. assert (Hpp0 : (0 < Z.pos pP)%Z) by apply zfc_pos_gt0.
    lia.
Qed.

(* ============================================================
   Z4 实例 + 双推论
   ============================================================ *)

Corollary zfc_check_sound : forall (nums dens : list Z),
  Forall (fun d : Z => (0 < d)%Z) dens ->
  (forall e, In e dens -> exists k, zfc_zprod dens = e * k) ->
  (0 < zfc_zprod dens)%Z ->
  zfc_check nums dens = true ->
  Qle (zfc_qsum nums dens) (Qmake 4 5).
Proof.
  intros nums dens Hne Hdiv Hpos Hchk.
  apply (proj2 (zfc_check_spec nums dens Hne Hdiv Hpos)).
  exact Hchk.
Qed.

Corollary zfc_check_complete : forall (nums dens : list Z),
  Forall (fun d : Z => (0 < d)%Z) dens ->
  (forall e, In e dens -> exists k, zfc_zprod dens = e * k) ->
  (0 < zfc_zprod dens)%Z ->
  Qle (zfc_qsum nums dens) (Qmake 4 5) ->
  zfc_check nums dens = true.
Proof.
  intros nums dens Hne Hdiv Hpos Hle.
  apply (proj1 (zfc_check_spec nums dens Hne Hdiv Hpos)).
  exact Hle.
Qed.

(* 可运行实例：C=4 行和（unique2sparse D 层同数值） *)
Lemma zfc_c4_row3_check : zfc_check [39; 159; 639] [120; 1200; 10500] = true.
Proof. vm_compute. reflexivity. Qed.

(* ---------- 审计（终态前 Admitted 必须清零） ---------- *)
Print Assumptions zfc_qsum_spec.
Print Assumptions zfc_check_spec.
Print Assumptions zfc_check_sound.
Print Assumptions zfc_check_complete.
Print Assumptions zfc_c4_row3_check.

(* ---------- 提取（Zarith 路线：big-int 无溢出） ---------- *)
From Stdlib Require Import Extraction.

Extraction "z_frame_check.ml" zfc_zprod zfc_zdots zfc_check.
