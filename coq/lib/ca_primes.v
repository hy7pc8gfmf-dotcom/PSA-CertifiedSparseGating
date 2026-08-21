(* 拆分自 Riemann_Hypothesis_Proof_Framework.v（复分析证明库 v6.0）*)
(* 库: ca_primes  原文行区间: 477-572  机械拆分，未改动内容 *)

Require Import Stdlib.Reals.Reals.          (* 实数公理系统及全套定理 *)
Require Import Stdlib.Reals.Rdefinitions.  (* 实数的原始定义（0,1,加法,乘法等）*)
Require Import Stdlib.Reals.RIneq.         (* 实数不等式基本引理 *)
Require Import Stdlib.Reals.Rtrigo_def.    (* 三角函数定义（sin, cos, PI）*)
Require Import Stdlib.Reals.Rtrigo1.       (* 三角函数基本性质（恒等式、单调性）*)
Require Import Stdlib.Reals.Rsqrt_def.     (* 平方根函数 sqrt 的定义 *)
Require Import Stdlib.Reals.Ranalysis1.    (* 一元实分析基础（导数、可导性、连续性）*)
Require Import Stdlib.Reals.Ranalysis.     (* 实分析汇总模块（包含 Ranalysis1-5）*)
Require Import Stdlib.Reals.Ranalysis3.    (* 高级导数定理（链式法则、反函数定理等）*)
Require Import Stdlib.Reals.Rpower.        (* 实数幂函数 Rpower 及其性质 *)
Require Import Stdlib.Lists.List.          (* 标准列表库，提供列表类型及常用操作 *)
Require Import Stdlib.Arith.Arith.         (* 自然数算术基础库 *)
Require Import Stdlib.Init.Nat.            (* 自然数初始化模块，定义 nat 类型及基本运算 *)
Require Import Stdlib.Classes.RelationClasses.  (* 关系类，定义 Reflexive, Symmetric, Transitive 等 *)
Require Import Stdlib.Program.Basics.      (* 编程基础，提供 id, compose 等函数 *)
Require Import Stdlib.Reals.R_sqrt.        (* 平方根函数及其性质（与 Rsqrt_def 类似）*)
Require Import Stdlib.Logic.ProofIrrelevance.   (* 证明无关性公理 *)
Require Import Stdlib.Logic.Classical.     (* 经典逻辑（排中律）*)
Require Import Stdlib.Logic.FunctionalExtensionality. (* 函数外延性公理 *)
Require Import Stdlib.Logic.IndefiniteDescription. (* 不定描述原理 *)
Require Import Stdlib.Classes.Morphisms.   (* 态射类，用于 Proper 等 *)
Require Import Stdlib.Classes.RelationPairs. (* 关系对组合 *)
Require Import Stdlib.Arith.PeanoNat.      (* 皮亚诺自然数算术，包含加法、乘法、比较等 *)
Require Import Stdlib.ZArith.ZArith.       (* 整数算术总集 *)
Require Import Stdlib.ZArith.Zdiv.         (* 整数除法 *)
Require Import Stdlib.micromega.Lia.       (* 线性整数算术自动化策略（用于 lia）*)
Require Import Stdlib.Strings.String.      (* 字符串类型及操作（用于调试/注释）*)
Require Import Stdlib.micromega.Lra.       (* 线性实数算术自动化策略（用于 lra）*)
From Stdlib Require Import Lia.            (* 再次导入 Lia，确保可用（冗余）*)
  
Local Open Scope R_scope.               (* 开启实数作用域，使实数运算符自动生效 *)
  
(* 导入 Rolle 定理所需的库 *)
From Stdlib Require Ranalysis5.              (* 包含 Rolle 定理的高级分析模块 *)
Open Scope R_scope.

Require Import ca_base ca_algebra.

Require Import Stdlib.Logic.IndefiniteDescription.

(* ====================================================
   第3章：质数理论 (Level 4)
   基于 MathComp 可靠质数库，Prime 类型携带正确性证明
   ==================================================== *)

(* 3.1 构造性质数 *)
Module ConstructivePrimes.
  
Require Import Stdlib.Reals.Reals.         (* 实数公理系统及全套定理 *)
Require Import Stdlib.Reals.Rdefinitions.  (* 实数的原始定义（0,1,加法,乘法等）*)
Require Import Stdlib.Reals.RIneq.         (* 实数不等式基本引理 *)
Require Import Stdlib.Reals.Rtrigo_def.    (* 三角函数定义（sin, cos, PI）*)
Require Import Stdlib.Reals.Rtrigo1.       (* 三角函数基本性质（恒等式、单调性）*)
Require Import Stdlib.Reals.Rsqrt_def.     (* 平方根函数 sqrt 的定义 *)
Require Import Stdlib.Reals.Ranalysis1.    (* 一元实分析基础（导数、可导性、连续性）*)
Require Import Stdlib.Reals.Ranalysis.     (* 实分析汇总模块（包含 Ranalysis1-5）*)
Require Import Stdlib.Reals.Ranalysis3.    (* 高级导数定理（链式法则、反函数定理等）*)
Require Import Stdlib.Reals.Rpower.        (* 实数幂函数 Rpower 及其性质 *)
  
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq prime.   (* SSReflect 核心语言、布尔反射、自然数、可判等类型、序列、素数理论 *)
From mathcomp Require Import ssrnat.                                (* 自然数理论（重载）*)
From mathcomp Require Import boot.prime.                            (* 素数理论（mathcomp≥2.6 位于 boot/；旧版 ssreflect/prime 由 CI -Q boot 双映射兼容）*)
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq prime div. (* SSReflect 完整基础库（含整除理论）*)
From mathcomp Require Import div.                                   (* 整除性理论 *)
From mathcomp Require Import prime.                                 (* 素数理论 *)
Import prime.                                                       (* 导入素数命名空间 *)
Require Import mathcomp.boot.ssrnat.                                (* 自然数理论（mathcomp≥2.6 重构后 boot 路径）*)
Require Import Stdlib.Strings.String.                                  (* 字符串类型及基本操作 *)
Import ComplexNumbers.
Open Scope string_scope.
Local Open Scope nat_scope.

(* 1. 导入 MathComp 核心数论库 —— 提供经过验证的质数定义和算法 *)
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq prime div.

(* 质数判定函数 *)
Definition prime := prime.

(* 质数类型 - 包含数值与质数证明 *)
Record Prime : Type := {
  prime_val : nat;
  prime_prf : prime prime_val
}.

(* 基本质数实例 prime_2 *)
Definition prime_2 : Prime.
Proof.
  refine {| prime_val := 2; prime_prf := _ |}.
  apply/primeP; split.
  - by rewrite ltnSn.
  - move=> d Hd.
    case: d Hd => [|[|[|d']]] Hd.
    + move: Hd; rewrite /div.dvdn /=; move/eqP; discriminate.
    + rewrite eqxx; reflexivity.
    + rewrite eqxx; reflexivity.
    + exfalso.
      move: Hd; rewrite /div.dvdn /= => /eqP Hmod.
      have Hle : d'.+3 <= 2.
        apply dvdn_leq.
        - by rewrite ltn0Sn.
        - by rewrite /dvdn Hmod.
      have Hlt : 2 < d'.+3.
        by rewrite !ltnS; apply: ltn0Sn.
      move: (leq_ltn_trans Hle Hlt).
      by rewrite ltnn; discriminate.
Qed.

(* 质数序列生成函数 *)
Definition prime_sequence (n : nat) : Prime.
Proof.
  induction n as [|n IH].
  - exact prime_2.
  - destruct IH as [p Hp].
    case: (prime_above p) => q Hlt_q Hprime_q.
    exact {| prime_val := q; prime_prf := Hprime_q |}.
Defined.

(* 质数值提取函数 *)
Definition prime_value (p : Prime) : nat := prime_val p.

(* 辅助函数：统计不超过 n 的素数个数 *)
Fixpoint count_primes_upto_nat (n : nat) : nat :=
  match n with
  | 0 => 0
  | 1 => 0
  | S n' => count_primes_upto_nat n' + (if prime (S n') then 1 else 0)
  end.

(* 实数向下取整为自然数 *)
Require Import Stdlib.Reals.Reals.
Definition floor_to_nat (x : R) : nat := Z.to_nat (Int_part x).

(* 素数计数函数 π(x) *)
Definition prime_pi (x : R) : nat := count_primes_upto_nat (floor_to_nat x).

(* --- 主定理补齐 [2026-08-15] --- *)

(* 素数无限性：任意 N 之后都存在更大的素数（欧几里得定理） *)
Lemma primes_infinite : forall N : nat, exists p : nat, prime p /\ (N < p)%nat.
Proof.
  intro N.
  case: (prime_above N) => p Hlt Hp.
  exists p; split; assumption.
Qed.

(* 素数必为正数 *)
Lemma prime_value_positive : forall p : nat, prime p -> (0 < p)%nat.
Proof.
  intros p Hp.
  apply prime_gt0; exact Hp.
Qed.

End ConstructivePrimes.
