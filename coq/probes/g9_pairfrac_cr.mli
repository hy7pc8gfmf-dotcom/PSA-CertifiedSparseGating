
type __ = Obj.t

type nat =
| O
| S of nat

type ('a, 'p) sigT =
| ExistT of 'a * 'p

module Nat :
 sig
  val add : nat -> nat -> nat

  val mul : nat -> nat -> nat

  val sub : nat -> nat -> nat

  val sqrt_iter : nat -> nat -> nat -> nat -> nat

  val sqrt : nat -> nat
 end

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos :
 sig
  val succ : positive -> positive

  val of_succ_nat : nat -> positive
 end

module Coq_Pos :
 sig
  val succ : positive -> positive

  val of_succ_nat : nat -> positive
 end

module Z :
 sig
  val of_nat : nat -> z
 end

type q = { qnum : z; qden : positive }

val g9_pf : nat -> nat -> q

val g9_closed : nat -> q

val g9_pf_C4_13 : __

val g9_closed_form_cert : nat -> nat -> (q, __) sigT
