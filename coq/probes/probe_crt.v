(* ============================================================
   T3a CRT 单射定理 + 素数链见证（z 工作区，E039；2026-08-22 第二批 ④）
   Z 域路线（避开 nat 减法的整除麻烦）：
   crt_inj : 1<N1、1<N2、gcd(N1,N2)=1、k1≡k2 (mod N1)、k1≡k2 (mod N2)、
             0≤k1,k2<N1*N2 ⟹ k1=k2。
   证明：d:=k1−k2；模相等 ⟹ N1∣d、N2∣d；
         gauss（coprime 消解）⟹ N1*N2 ∣ d；
         |d| < N1*N2 ⟹ d=0。
   素数链见证：[3;7;13;29;59;127;251;503] 两两 gcd=1（vm_compute）
   + 乘积 7489590692493 > 4096（8× 视界覆盖）。
   意义：CRT 分辨率定理（素数阶梯 lcm=乘积 ≫ 8× 视界）+ 项目素数身份。
   （注：同事 src/CRTResolve.v 已落 mathcomp 版；本探针为 Stdlib Z 域
    独立复现，零 mathcomp 依赖，供自包含合并选项。）
   ============================================================ *)
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Lists.List.
Import ListNotations.
Open Scope Z_scope.

(* ---------- 基础：模相等 ⟹ 整除 ---------- *)

Lemma mod_eq_dvd_Z (a b n : Z) :
  ((a mod n)%Z = (b mod n)%Z) -> (n <> 0)%Z -> (n | (a - b)%Z).
Proof.
  intros He Hn.
  assert (Ha : a = n * (a / n) + a mod n) by (apply Z.div_mod; exact Hn).
  assert (Hb : b = n * (b / n) + b mod n) by (apply Z.div_mod; exact Hn).
  exists (a / n - b / n)%Z.
  transitivity ((n * (a / n) + a mod n) - (n * (b / n) + b mod n)).
  - congruence.
  - rewrite He. ring.
Qed.

(* ---------- CRT 单射主定理 ---------- *)

Theorem crt_inj (N1 N2 k1 k2 : Z) :
  (1 < N1)%Z -> (1 < N2)%Z ->
  (Z.gcd N1 N2 = 1)%Z ->
  ((k1 mod N1)%Z = (k2 mod N1)%Z) ->
  ((k1 mod N2)%Z = (k2 mod N2)%Z) ->
  (0 <= k1 < N1 * N2)%Z ->
  (0 <= k2 < N1 * N2)%Z ->
  k1 = k2.
Proof.
  intros H1 H2 Hg M1 M2 [L1 U1] [L2 U2].
  assert (Hn1 : (N1 <> 0)%Z) by lia.
  assert (Hn2 : (N2 <> 0)%Z) by lia.
  pose proof (mod_eq_dvd_Z k1 k2 N1 M1 Hn1) as D1.
  pose proof (mod_eq_dvd_Z k1 k2 N2 M2 Hn2) as D2.
  destruct D1 as [q1 Hq1].   (* k1 - k2 = q1 * N1 *)
  destruct D2 as [q2 Hq2].   (* k1 - k2 = q2 * N2 *)
  (* coprime 消解：N2 ∣ q1（因 q1*N1 = q2*N2，gcd(N1,N2)=1） *)
  assert (Hgc : (Z.gcd N2 N1 = 1)%Z) by (rewrite Z.gcd_comm; exact Hg).
  assert (HQ : (N2 | q1)%Z).
  { apply (Z.gauss N2 N1 q1).
    - exists q2%Z. nia.
    - exact Hgc. }
  destruct HQ as [t Ht].    (* q1 = t * N2 *)
  assert (Hd : (k1 - k2 = t * (N1 * N2))%Z).
  { rewrite Hq1, Ht. ring. }
  (* range ⟹ t = 0 *)
  assert (Ht0 : (t = 0)%Z).
  { destruct (Z.eq_dec t 0%Z) as [T0 | TN]; [exact T0 | exfalso].
    assert (Hlow : (Z.abs t >= 1)%Z).
    { destruct (Z.abs_spec t) as [[A B] | [A B]]; lia. }
    assert (HNN : (N1 * N2 >= 1 * 1)%Z) by nia.
    assert (Hbig : (Z.abs (k1 - k2) >= N1 * N2)%Z).
    { rewrite Hd, Z.abs_mul.
      assert (Hann : (Z.abs (N1 * N2) = N1 * N2)%Z) by (apply Z.abs_eq; nia).
      rewrite Hann. nia. }
    assert (Hsmall : (Z.abs (k1 - k2) < N1 * N2)%Z).
    { rewrite Z.abs_lt. split; lia. }
    lia. }
  rewrite Ht0, Z.mul_0_l in Hd. lia.
Qed.

(* ---------- 素数链见证 ---------- *)

Definition prime_ladder : list Z :=
  [3; 7; 13; 29; 59; 127; 251; 503].

Lemma prime_ladder_unfold :
  forall z, In z prime_ladder ->
    z = 3 \/ z = 7 \/ z = 13 \/ z = 29 \/ z = 59 \/ z = 127 \/ z = 251 \/ z = 503.
Proof.
  intros z Hz. simpl in Hz. firstorder congruence.
Qed.

Lemma prime_ladder_pairwise_gcd1 :
  forall a b, In a prime_ladder -> In b prime_ladder -> a <> b -> (Z.gcd a b = 1)%Z.
Proof.
  intros a b Ha Hb Hab.
  destruct (prime_ladder_unfold a Ha) as [A1 | [A2 | [A3 | [A4 | [A5 | [A6 | [A7 | A8]]]]]]];
  destruct (prime_ladder_unfold b Hb) as [B1 | [B2 | [B3 | [B4 | [B5 | [B6 | [B7 | B8]]]]]]];
  subst; vm_compute; congruence || reflexivity.
Qed.

Lemma prime_ladder_product :
  (fold_right Z.mul 1 prime_ladder = 7489590692493)%Z.
Proof. vm_compute. reflexivity. Qed.

(* 乘积 ≫ 8× 评估视界（512 训练窗的 8× = 4096） *)
Theorem prime_ladder_resolves :
  (4096 < fold_right Z.mul 1 prime_ladder)%Z.
Proof.
  rewrite prime_ladder_product. lia.
Qed.

Print Assumptions crt_inj.
Print Assumptions prime_ladder_pairwise_gcd1.
Print Assumptions prime_ladder_resolves.
