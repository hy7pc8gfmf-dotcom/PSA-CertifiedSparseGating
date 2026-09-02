
type bool =
| True
| False

type ('a, 'b) prod =
| Pair of 'a * 'b

type 'a list =
| Nil
| Cons of 'a * 'a list

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

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

  val eqb : positive -> positive -> bool
 end

module Z :
 sig
  val double : z -> z

  val succ_double : z -> z

  val pred_double : z -> z

  val pos_sub : positive -> positive -> z

  val add : z -> z -> z

  val opp : z -> z

  val sub : z -> z -> z

  val mul : z -> z -> z

  val compare : z -> z -> comparison

  val leb : z -> z -> bool

  val ltb : z -> z -> bool

  val eqb : z -> z -> bool

  val pos_div_eucl : positive -> z -> (z, z) prod

  val div_eucl : z -> z -> (z, z) prod

  val div : z -> z -> z

  val modulo : z -> z -> z
 end

val forallb : ('a1 -> bool) -> 'a1 list -> bool

val w63 : z

val zprod : z list -> z

val in_w63 : z -> bool

val zfc_zprod : z list -> z

val zfc_zdots : z -> z list -> z list -> z

val zfc_check : z list -> z list -> bool

val z2b_wrap : z -> z

val z2b_dots63 : z -> z list -> z list -> z

val z2b_check63 : z list -> z list -> bool

val z2b_safe_bool : z list -> z list -> bool

val z2b_overflow_demo : (bool, bool) prod

val z2b_c4_runtime : (bool, bool) prod
