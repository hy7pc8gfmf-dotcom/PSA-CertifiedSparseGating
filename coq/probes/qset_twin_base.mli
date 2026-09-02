
type __ = Obj.t

type bool =
| True
| False

type nat =
| O
| S of nat

type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b

type ('a, 'b) prod =
| Pair of 'a * 'b

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

type ('a, 'p) sigT =
| ExistT of 'a * 'p

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Nat :
 sig
  val leb : nat -> nat -> bool
 end

module Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  val mul : positive -> positive -> positive

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val eqb : positive -> positive -> bool
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

  val eqb : z -> z -> bool
 end

type q = { qnum : z; qden : positive }

val qcompare : q -> q -> comparison

val qeq_bool : q -> q -> bool

val qplus : q -> q -> q

val qmult : q -> q -> q

val qopp : q -> q

val qminus : q -> q -> q

type 'a id =
| Id_refl

type ('a, 'b) and0 = ('a, 'b) prod

type ('a, 'b) or0 = ('a, 'b) sum

val idT_of_eq : 'a1 -> 'a1 -> 'a1 id

val qtw_lt_bool : q -> q -> bool

type qltT = bool id

type qeqT = bool id

type qleT = (qltT, qeqT) or0

type natLe = bool id

val qlt_to_QltT : q -> q -> qltT

val qeqT_of_Qeq : q -> q -> qeqT

val qle_to_QleT : q -> q -> qleT

val qtw_ltT_of_eq_true : q -> q -> qltT

val qtw_eqT_of_eq_true : q -> q -> qeqT

val qtw_NatLe_of_le : nat -> nat -> natLe

val qtw_le_of_NatLe : __

val qtw_tri : q -> q -> (qltT, (qeqT, qltT) sum) sum

val qtw_le_dec : q -> q -> (qleT, qltT) sum

val qtw_margin_witness : q -> q -> qltT -> (q, (qltT, qleT) and0) sigT

val qtw_half : q -> qltT -> (q, qltT) sigT

val qtw_qsum : (nat -> q) -> nat -> q
