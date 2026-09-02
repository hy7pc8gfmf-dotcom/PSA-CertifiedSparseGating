
type bool =
| True
| False

type nat =
| O
| S of nat

type ('a, 'b) prod =
| Pair of 'a * 'b

val fst : ('a1, 'a2) prod -> 'a1

val snd : ('a1, 'a2) prod -> 'a2

type 'a list =
| Nil
| Cons of 'a * 'a list

val add : nat -> nat -> nat

val mul : nat -> nat -> nat

val sub : nat -> nat -> nat

module Nat :
 sig
  val eqb : nat -> nat -> bool

  val leb : nat -> nat -> bool

  val ltb : nat -> nat -> bool

  val max : nat -> nat -> nat

  val min : nat -> nat -> nat

  val sqrt_iter : nat -> nat -> nat -> nat -> nat

  val sqrt : nat -> nat
 end

val nth : nat -> 'a1 list -> 'a1 -> 'a1

val forallb : ('a1 -> bool) -> 'a1 list -> bool

module FrameCheckInstance :
 sig
  val pair_num : nat -> nat -> nat

  val pair_den : nat -> nat -> nat

  val pair_ok : nat -> nat -> bool

  val frac_add : nat -> nat -> nat -> nat -> (nat, nat) prod

  val row_sum_frac_aux :
    nat list -> nat list -> nat -> (nat, nat) prod -> nat -> (nat, nat) prod

  val row_sum_frac : nat list -> nat -> (nat, nat) prod

  val row_le_4_5 : (nat, nat) prod -> bool

  val sorted_aux : nat -> nat list -> bool

  val sorted_strict_aux : nat list -> bool

  val all_ge_2 : nat list -> bool

  val all_pairs_ok : nat list -> bool

  val all_rows_le : nat list -> nat list -> nat -> bool

  val frame_check_instance : nat list -> bool
 end

type cert_level =
| L1_tight
| L2_composite
| L3_energy_only
| L4_rejected

val pair_le_1 : nat -> nat -> bool

val all_pairs_le_1 : nat list -> bool

val frame_check_graduated : nat list -> cert_level
