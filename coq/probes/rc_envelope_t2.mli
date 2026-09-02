
type __ = Obj.t

type bool =
| True
| False

type nat =
| O
| S of nat

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

type ('a, 'p) sigT =
| ExistT of 'a * 'p

val projT1 : ('a1, 'a2) sigT -> 'a1

val projT2 : ('a1, 'a2) sigT -> 'a2

val add : nat -> nat -> nat

val max : nat -> nat -> nat

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

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  val mul : positive -> positive -> positive

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val of_succ_nat : nat -> positive
 end

module Coq_Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val mul : positive -> positive -> positive
 end

module Z :
 sig
  val double : z -> z

  val succ_double : z -> z

  val pred_double : z -> z

  val pos_sub : positive -> positive -> z

  val add : z -> z -> z

  val opp : z -> z

  val mul : z -> z -> z

  val compare : z -> z -> comparison

  val of_nat : nat -> z
 end

type q = { qnum : z; qden : positive }

val qcompare : q -> q -> comparison

val qplus : q -> q -> q

val qmult : q -> q -> q

val qopp : q -> q

val qminus : q -> q -> q

val qinv : q -> q

val qdiv : q -> q -> q

type 'a id =
| Id_refl

val qlt_bool : q -> q -> bool

type qltT = bool id

val qlt_to_QltT : q -> q -> qltT

type qseq = nat -> q

type cauchy = q -> qltT -> (nat, nat -> nat -> __ -> __ -> qltT) sigT

type real = (qseq, cauchy) sigT

val reg_index : (nat -> nat) -> nat -> nat

val reg_mod : qseq -> cauchy -> nat -> nat

val regularize : qseq -> cauchy -> qseq

val env_w : nat -> q

val reg_of : real -> qseq

val env_lo : real -> nat -> q

val env_hi : real -> nat -> q

val env_lt_check : real -> real -> nat -> bool
