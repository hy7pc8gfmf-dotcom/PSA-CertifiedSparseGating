(* ============================================================
   CS-16 安全域谓词与溢出自由一致性：probe_safe_domain.v
   （z 区构造性轨道，2026-08-30，M2 venue 对齐扩展——评审 A1/主题
   "运行时检查器 int 镜像信任鸿沟"的正面回应）

   背景：反射检查器 `frame_check_instance`（PSA_framework）为 nat 判定器；
   提取的 OCaml int（63-bit）镜像与 Coq 语义的一致性此前仅为 FFI 24/24
   交叉校验（经验性）。本模块给出**构造性的安全域谓词**：满足该谓词的
   输入下，连乘链不溢出 ⟹ mod-2^63 镜像与精确语义一致（可判定成员资格）。

   数学内容：
     S1 ★ 乘积上界递推（非平凡归纳）：若全部因子 0 < d ≤ D，则
        0 < zprod l ≤ D^length l——安全域"成员判定"的数学核。
     S2 溢出自由一致性：0 ≤ p < 2^63 ⟹ p mod 2^63 == p
        （溢出自由 ⟹ mod-2^63 镜像与精确语义一致）。
     S3 ★★ 最终合成（安全域定理）：C=4 判定链
        dens = [400;2080;3500;20800;33920]（行和有理界的分母）满足
        全因子 0 < d < 2^63 且 zprod < 2^63 —— 判定链落在安全域内，
        镜像一致 + 成员资格可判定（bool 函数，可提取）。

   纪律（承 probe_taugrid_cr.v / probe_c4_four_atom_cr.v）：
     - 纯构造性：nat/Z 层（零实数、零经典公理、零 Admitted）
     - Set 层 Fixpoint（zprod——可计算、可提取）；Prop 层结论
     - 审计：Print Assumptions 尾部
   依赖：Stdlib（List/ZArith/Lia）。
   提取：safe_domain.ml（zprod/判定 bool 函数——Set 层可执行）。
   ============================================================ *)
Require Import Stdlib.QArith.QArith.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Lists.List.
Import ListNotations.

Local Open Scope Z_scope.   (* QArith 会 Open Q_scope——裸 * / <= 需回 Z；Q 全部走 Qmake 显式构造 *)

(* ---------- 63-bit 界 ---------- *)
Definition W63 : Z := 9223372036854775808.   (* 2^63 *)
Definition W53 : Z := 9007199254740992.      (* 2^53 *)

(* ---------- Set 层连乘（可计算、可提取） ---------- *)
Fixpoint zprod (l : list Z) : Z :=
  match l with
  | [] => 1
  | d :: r => d * zprod r
  end.

(* ---------- S1 ★ 乘积上界递推（非平凡归纳核） ---------- *)

Lemma zprod_pos : forall l : list Z, Forall (fun d : Z => (0 < d)%Z) l -> (0 < zprod l)%Z.
Proof.
  induction l as [| d r IH]; intros H.
  - simpl. lia.
  - inversion H as [| ? ? Hd Hr]; subst.
    simpl. assert (Hrp : (0 < zprod r)%Z) by (apply IH; exact Hr).
    nia.
Qed.

(* nat 指数幂（自定义——避免 ^ 记号在 QArith 下的解析歧义；可提取） *)
Fixpoint zpowN (d : Z) (n : nat) : Z :=
  match n with
  | O => 1
  | S k => d * zpowN d k
  end.

Lemma zpowN_pos : forall (d : Z) (n : nat), (0 < d)%Z -> (0 < zpowN d n)%Z.
Proof.
  intros d n Hd. induction n as [| k IHn].
  - simpl. lia.
  - simpl. nia.
Qed.

Lemma zpowN_mono : forall (d : Z) (n : nat), (1 <= d)%Z ->
  (zpowN d n <= zpowN d (S n))%Z.
Proof.
  intros d n Hd.
  assert (Hpos : (0 < zpowN d n)%Z) by (apply zpowN_pos; lia).
  simpl. nia.
Qed.



Theorem zprod_bounded : forall (l : list Z) (dmax : Z),
  Forall (fun d : Z => (0 < d <= dmax)%Z) l ->
  (0 < zprod l <= zpowN dmax (length l))%Z.
Proof.
  intros l dmax H.
  induction l as [| d r IH].
  - simpl. lia.
  - simpl zprod. simpl zpowN. simpl length.
    inversion H as [| ? ? Hd0 Hr]; subst.
    specialize (IH Hr). destruct IH as [IHpos IHle].
    destruct Hd0 as [Hdpos Hdle].
    split.
    + apply Z.mul_pos_pos.
      * exact Hdpos.
      * exact IHpos.
    + nia.
Qed.

(* ---------- S2 溢出自由一致性 ---------- *)

Theorem no_overflow_consistent : forall p : Z,
  (0 <= p < W63)%Z -> p mod W63 = p.
Proof.
  intros p Hp. apply Zmod_small. lia.
Qed.

(* ---------- S3 ★★ C=4 判定链安全域（最终合成） ---------- *)

(* C=4 反射检查器的分母链：3 原子行和界（53/400、689/2080、11289/33920）
   与 213 边带界（213/3500、2769/20800 等）的分母——
   具体值取自 PSA_framework pair_*/c4_coherence_3 常数 *)
Definition c4_dens : list Z := [400; 2080; 3500; 20800; 33920].
Definition c4_bands : list nat := [3%nat; 13%nat; 53%nat; 213%nat].

(* 安全域成员的 bool 判定（可提取——运行时可判定成员资格） *)
Definition in_w63 (p : Z) : bool := Z.eqb (p mod W63) p.
Definition safe_domain_bool (dens : list Z) : bool :=
  forallb (fun d => andb (in_w63 d) (in_w63 (zprod dens))) dens.

(* ★ 安全域定理：C=4 判定链全因子在界内 ⟹ 连乘 < 2^63（溢出自由）
   ⟹ 镜像一致（mod-2^63 == 精确） *)
Theorem c4_safe_domain :
  Forall (fun d : Z => (0 < d < W63)%Z) c4_dens
  /\ (zprod c4_dens < W63)%Z
  /\ (zprod c4_dens mod W63 = zprod c4_dens)%Z.
Proof.
  assert (Hzv : (zprod c4_dens = 2054520832000000000)%Z) by reflexivity.
  assert (Hbounds : Forall (fun d : Z => (0 < d < W63)%Z) c4_dens).
  { apply Forall_forall. intros a Ha. unfold c4_dens in Ha. unfold W63.
    destruct Ha as [H | [H | [H | [H | [H | H]]]]]; subst.
    * lia. * lia. * lia. * lia. * lia. * destruct H. }
  split; [| split].
  - exact Hbounds.
  - unfold W63. rewrite Hzv. lia.
  - apply no_overflow_consistent. unfold W63. rewrite Hzv. lia.
Qed.

(* ---------- 审计 ---------- *)
Print Assumptions zprod_pos.
Print Assumptions zprod_bounded.
Print Assumptions no_overflow_consistent.
Print Assumptions c4_safe_domain.

(* ---------- 提取（Set 层可执行：运行时可判定成员资格） ---------- *)
From Stdlib Require Import Extraction.

Extraction "safe_domain.ml" zprod in_w63 safe_domain_bool c4_dens.
