
type __ = Obj.t

type bool =
| True
| False

type 'a list =
| Nil
| Cons of 'a * 'a list

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

module Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val mul : positive -> positive -> positive

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison
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
  val mul : z -> z -> z

  val compare : z -> z -> comparison

  val leb : z -> z -> bool
 end

type q = { qnum : z; qden : positive }

val qle_bool : q -> q -> bool

val qmult : q -> q -> q

type ct_cert = { ct_m : q; ct_sb : q; ct_sq : q }

val ct_pos : ct_cert -> bool

val ct_ref : ct_cert -> ct_cert -> bool

val ct_check : ct_cert -> bool

val ct_tighten : ct_cert -> ct_cert list -> ct_cert

val ct_opt_cert : ct_cert -> ct_cert list -> (ct_cert, __) sigT
