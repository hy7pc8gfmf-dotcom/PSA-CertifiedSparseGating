
type bool =
| True
| False

type nat =
| O
| S of nat

type ('a, 'b) prod =
| Pair of 'a * 'b

(** val fst : ('a1, 'a2) prod -> 'a1 **)

let fst = function
| Pair (x, _) -> x

(** val snd : ('a1, 'a2) prod -> 'a2 **)

let snd = function
| Pair (_, y) -> y

type 'a list =
| Nil
| Cons of 'a * 'a list

(** val add : nat -> nat -> nat **)

let rec add n m =
  match n with
  | O -> m
  | S p -> S (add p m)

(** val mul : nat -> nat -> nat **)

let rec mul n m =
  match n with
  | O -> O
  | S p -> add m (mul p m)

(** val sub : nat -> nat -> nat **)

let rec sub n m =
  match n with
  | O -> n
  | S k -> (match m with
            | O -> n
            | S l -> sub k l)

module Nat =
 struct
  (** val add : nat -> nat -> nat **)

  let rec add n m =
    match n with
    | O -> m
    | S p -> S (add p m)

  (** val mul : nat -> nat -> nat **)

  let rec mul n m =
    match n with
    | O -> O
    | S p -> add m (mul p m)

  (** val eqb : nat -> nat -> bool **)

  let rec eqb n m =
    match n with
    | O -> (match m with
            | O -> True
            | S _ -> False)
    | S n' -> (match m with
               | O -> False
               | S m' -> eqb n' m')

  (** val leb : nat -> nat -> bool **)

  let rec leb n m =
    match n with
    | O -> True
    | S n' -> (match m with
               | O -> False
               | S m' -> leb n' m')

  (** val ltb : nat -> nat -> bool **)

  let ltb n m =
    leb (S n) m

  (** val pow : nat -> nat -> nat **)

  let rec pow n = function
  | O -> S O
  | S m0 -> mul n (pow n m0)

  (** val sqrt_iter : nat -> nat -> nat -> nat -> nat **)

  let rec sqrt_iter k p q r =
    match k with
    | O -> p
    | S k' ->
      (match r with
       | O -> sqrt_iter k' (S p) (S (S q)) (S (S q))
       | S r' -> sqrt_iter k' p q r')

  (** val sqrt : nat -> nat **)

  let sqrt n =
    sqrt_iter n O O O
 end

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| Nil -> Nil
| Cons (a, l0) -> Cons ((f a), (map f l0))

(** val seq : nat -> nat -> nat list **)

let rec seq start = function
| O -> Nil
| S len0 -> Cons (start, (seq (S start) len0))

(** val nth : nat -> 'a1 list -> 'a1 -> 'a1 **)

let rec nth n l default =
  match n with
  | O -> (match l with
          | Nil -> default
          | Cons (x, _) -> x)
  | S m -> (match l with
            | Nil -> default
            | Cons (_, l') -> nth m l' default)

(** val forallb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec forallb f = function
| Nil -> True
| Cons (a, l0) -> (match f a with
                   | True -> forallb f l0
                   | False -> False)

module FrameCheckInstance =
 struct
  (** val pair_num : nat -> nat -> nat **)

  let pair_num =
    mul

  (** val pair_den : nat -> nat -> nat **)

  let pair_den n1 n2 =
    mul (mul (S (S O)) (sub n2 n1)) (Nat.sqrt (mul n1 n2))

  (** val pair_ok : nat -> nat -> bool **)

  let pair_ok n1 n2 =
    match Nat.leb (mul (Nat.sqrt (mul n1 n2)) (Nat.sqrt (mul n1 n2)))
            (mul n1 n2) with
    | True -> Nat.ltb O (Nat.sqrt (mul n1 n2))
    | False -> False

  (** val frac_add : nat -> nat -> nat -> nat -> (nat, nat) prod **)

  let frac_add a b c d =
    Pair ((add (mul a d) (mul c b)), (mul b d))

  (** val row_sum_frac_aux :
      nat list -> nat list -> nat -> (nat, nat) prod -> nat -> (nat, nat) prod **)

  let rec row_sum_frac_aux i orig i0 acc j =
    match i with
    | Nil -> acc
    | Cons (h, tl) ->
      let n_i = nth i0 orig O in
      let Pair (num, den) = acc in
      (match Nat.eqb j i0 with
       | True -> row_sum_frac_aux tl orig i0 acc (S j)
       | False ->
         (match Nat.ltb h n_i with
          | True ->
            row_sum_frac_aux tl orig i0
              (frac_add num den (pair_num h n_i) (pair_den h n_i)) (S j)
          | False ->
            row_sum_frac_aux tl orig i0
              (frac_add num den (pair_num n_i h) (pair_den n_i h)) (S j)))

  (** val row_sum_frac : nat list -> nat -> (nat, nat) prod **)

  let row_sum_frac i i0 =
    row_sum_frac_aux i i i0 (Pair (O, (S O))) O

  (** val row_le_4_5 : (nat, nat) prod -> bool **)

  let row_le_4_5 f =
    Nat.leb (mul (S (S (S (S (S O))))) (fst f))
      (mul (S (S (S (S O)))) (snd f))

  (** val sorted_aux : nat -> nat list -> bool **)

  let rec sorted_aux prev = function
  | Nil -> True
  | Cons (h, tl) ->
    (match Nat.ltb prev h with
     | True -> sorted_aux h tl
     | False -> False)

  (** val sorted_strict_aux : nat list -> bool **)

  let sorted_strict_aux = function
  | Nil -> True
  | Cons (h, tl) -> sorted_aux h tl

  (** val all_ge_2 : nat list -> bool **)

  let rec all_ge_2 = function
  | Nil -> True
  | Cons (h, tl) ->
    (match Nat.leb (S (S O)) h with
     | True -> all_ge_2 tl
     | False -> False)

  (** val all_pairs_ok : nat list -> bool **)

  let rec all_pairs_ok = function
  | Nil -> True
  | Cons (h, tl) ->
    (match forallb (fun n -> pair_ok h n) tl with
     | True -> all_pairs_ok tl
     | False -> False)

  (** val all_rows_le : nat list -> nat list -> nat -> bool **)

  let rec all_rows_le i orig i0 =
    match i with
    | Nil -> True
    | Cons (_, tl) ->
      (match row_le_4_5 (row_sum_frac orig i0) with
       | True -> all_rows_le tl orig (S i0)
       | False -> False)

  (** val frame_check_instance : nat list -> bool **)

  let frame_check_instance i =
    match sorted_strict_aux i with
    | True ->
      (match all_ge_2 i with
       | True ->
         (match all_pairs_ok i with
          | True -> all_rows_le i i O
          | False -> False)
       | False -> False)
    | False -> False
 end

(** val z3b_bands : nat -> nat -> nat list **)

let z3b_bands n0 m =
  map (fun k -> mul n0 (Nat.pow (S (S (S (S (S (S (S (S O)))))))) k))
    (seq O m)
