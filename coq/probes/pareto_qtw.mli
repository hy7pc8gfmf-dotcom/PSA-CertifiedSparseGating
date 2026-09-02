
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
  val add : nat -> nat -> nat

  val sub : nat -> nat -> nat

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
 end

type q = { qnum : z; qden : positive }

val qcompare : q -> q -> comparison

val qeq_bool : q -> q -> bool

val qplus : q -> q -> q

val qmult : q -> q -> q

val qopp : q -> q

val qminus : q -> q -> q

val qinv : q -> q

val qdiv : q -> q -> q

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

val qltT_trans : q -> q -> q -> qltT -> qltT -> qltT

val qleT_refl : q -> qleT

val qleT_trans : q -> q -> q -> qleT -> qleT -> qleT

val qtw_leT_congr_r : q -> q -> q -> qleT -> qeqT -> qleT

val qtw_leT_congr_l : q -> q -> q -> qleT -> qeqT -> qleT

val qmult_ltT_compat_r : q -> q -> q -> qltT -> qltT -> qltT

val qmult_leT_compat_r : q -> q -> q -> qleT -> qleT -> qleT

val qmult_leT_0_compat : q -> q -> qleT -> qleT -> qleT

val s281_lo : q

val c_q : q -> q

val par_c_ratio_lt : q -> qleT -> qltT

val par_c_sandwich : q -> qleT -> qleT -> (qltT, qleT) and0

val par_ratio_gap : q -> qleT -> (q, (qltT, qleT) and0) sigT

val par_c_lt_triggers :
  q -> q -> q -> qeqT -> qleT -> qltT -> qltT -> qltT -> qltT

val par_same_bin_quad :
  q -> q -> q -> qeqT -> qleT -> qltT -> qltT -> qltT -> qltT

val qnat : nat -> q

val fall9q : nat -> q

val pow9q : nat -> q

val no_collision_q : nat -> q

val par_qnat_le9 : nat -> qleT

val par_qnat_nonnegT : nat -> qleT

val par_pow9_posT : nat -> qltT

val par_fall9q_nonnegT : nat -> qleT

val par_div_leT : q -> q -> q -> q -> qleT -> qltT -> qltT -> qleT -> qleT

val par_nc_decreasing : nat -> qleT

val par_nc_le : nat -> nat -> qleT

val par_fall10_zero : nat -> qeqT

val par_nc7_val : qeqT

val par_prob7 : qleT

val par_prob8 : qleT

val par_prob_mono : qleT

val par_smoke_gap : q

val par_smoke_gap_ok : bool

val par_smoke_nc : bool

val prt_qleb : q -> q -> bool

val par_smoke_prob : bool

val par_smoke_dec_cert : qleT

val par_smoke_gap_cert : (q, (qltT, qleT) and0) sigT
