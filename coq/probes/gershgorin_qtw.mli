
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

val fst : ('a1, 'a2) prod -> 'a1

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

type ('a, 'p) sigT =
| ExistT of 'a * 'p

type sumbool =
| Left
| Right

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
  val pred : nat -> nat

  val eq_dec : nat -> nat -> sumbool
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

  val eqb : z -> z -> bool

  val of_nat : nat -> z

  val abs : z -> z
 end

type q = { qnum : z; qden : positive }

val qcompare : q -> q -> comparison

val qeq_bool : q -> q -> bool

val qplus : q -> q -> q

val qmult : q -> q -> q

val qopp : q -> q

val qminus : q -> q -> q

val qabs : q -> q

type 'a id =
| Id_refl

type ('a, 'b) and0 = ('a, 'b) prod

type ('a, 'b) or0 = ('a, 'b) sum

val idT_of_eq : 'a1 -> 'a1 -> 'a1 id

type qltT = bool id

type qeqT = bool id

type qleT = (qltT, qeqT) or0

val qlt_to_QltT : q -> q -> qltT

val qeqT_of_Qeq : q -> q -> qeqT

val qle_to_QleT : q -> q -> qleT

val qtw_qsum : (nat -> q) -> nat -> q

val gtw_ip : (nat -> nat -> q) -> nat -> nat -> nat -> q

val gtw_S : (nat -> q) -> nat -> q

val gtw_Fsq : (nat -> nat -> q) -> (nat -> q) -> nat -> nat -> q

val gtw_offdiag : (nat -> nat -> q) -> (nat -> q) -> nat -> nat -> q

val gtw_W : (nat -> nat -> q) -> (nat -> q) -> nat -> nat -> q

val gershgorin_frame_mu_qtw :
  nat -> nat -> (nat -> nat -> q) -> q -> (nat -> __ -> qeqT) -> (nat -> __
  -> qleT) -> (nat -> q) -> (qleT, qleT) and0

val gtw_gap_witness :
  nat -> nat -> (nat -> nat -> q) -> q -> (nat -> __ -> qeqT) -> (nat -> __
  -> qleT) -> qltT -> (nat -> q) -> (q, (qltT, qleT) and0) sigT

val gtw_smoke_v : nat -> nat -> q

val gtw_smoke_c : nat -> q

val gtw_smoke_data : bool

val gtw_smoke_eval : bool
