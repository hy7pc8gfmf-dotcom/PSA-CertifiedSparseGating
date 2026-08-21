
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

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | Nil -> m
  | Cons (a, l1) -> Cons (a, (app l1 m))

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

(** val max : nat -> nat -> nat **)

let rec max n m =
  match n with
  | O -> m
  | S n' -> (match m with
             | O -> n
             | S m' -> S (max n' m'))

module Nat =
 struct
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

(** val nth : nat -> 'a1 list -> 'a1 -> 'a1 **)

let rec nth n l default =
  match n with
  | O -> (match l with
          | Nil -> default
          | Cons (x, _) -> x)
  | S m -> (match l with
            | Nil -> default
            | Cons (_, l') -> nth m l' default)

(** val tl : 'a1 list -> 'a1 list **)

let tl = function
| Nil -> Nil
| Cons (_, l') -> l'

(** val rev : 'a1 list -> 'a1 list **)

let rec rev = function
| Nil -> Nil
| Cons (x, l') -> app (rev l') (Cons (x, Nil))

(** val forallb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec forallb f = function
| Nil -> True
| Cons (a, l0) -> (match f a with
                   | True -> forallb f l0
                   | False -> False)

(** val combine : 'a1 list -> 'a2 list -> ('a1, 'a2) prod list **)

let rec combine l l' =
  match l with
  | Nil -> Nil
  | Cons (x, tl0) ->
    (match l' with
     | Nil -> Nil
     | Cons (y, tl') -> Cons ((Pair (x, y)), (combine tl0 tl')))

module RuntimeGuards =
 struct
  (** val all_ge_2 : nat list -> bool **)

  let all_ge_2 vals =
    forallb (fun v -> Nat.leb (S (S O)) v) vals

  (** val forallb_adjacent : nat list -> (nat -> nat -> bool) -> bool **)

  let forallb_adjacent l f =
    forallb (fun ab -> f (fst ab) (snd ab)) (combine l (tl l))

  (** val check_sparse_growth : nat list -> nat -> bool **)

  let check_sparse_growth indices c =
    forallb_adjacent indices (fun a b -> Nat.ltb (mul c a) b)

  (** val check_c_sparse_on_vals : nat list -> nat -> bool **)

  let check_c_sparse_on_vals vals c =
    match forallb_adjacent vals (fun a b -> Nat.leb (mul (mul c c) a) b) with
    | True -> all_ge_2 vals
    | False -> False
 end

module SeqProps =
 struct
  (** val gen_aux : nat -> nat -> nat -> nat list -> nat list **)

  let rec gen_aux c start len acc =
    match len with
    | O -> rev acc
    | S len' ->
      let last = match acc with
                 | Nil -> start
                 | Cons (h, _) -> h in
      let next = max (add (mul last c) (S O)) (add last (S (S O))) in
      gen_aux c start len' (Cons (next, acc))

  (** val next_idx : nat -> nat -> nat **)

  let next_idx last c =
    max (add (mul last c) (S O)) (add last (S (S O)))

  (** val generate_base_indices : nat -> nat -> nat -> nat list **)

  let generate_base_indices len c start =
    gen_aux c start len (Cons (start, Nil))

  (** val base_seq : nat -> nat -> nat -> nat **)

  let rec base_seq c start = function
  | O -> start
  | S i' -> next_idx (base_seq c start i') c
 end

module GreedyGate =
 struct
  (** val greedy_aux : nat -> nat -> nat list -> nat list **)

  let rec greedy_aux m last = function
  | Nil -> Nil
  | Cons (v, vs) ->
    (match Nat.leb (mul m last) v with
     | True -> Cons (v, (greedy_aux m v vs))
     | False -> greedy_aux m last vs)

  (** val greedy_selected : nat -> nat list -> nat list **)

  let greedy_selected m = function
  | Nil -> Nil
  | Cons (v, vs) -> Cons (v, (greedy_aux m v vs))

  (** val mask_aux : nat -> nat -> nat list -> bool list **)

  let rec mask_aux m last = function
  | Nil -> Nil
  | Cons (v, vs) ->
    (match Nat.leb (mul m last) v with
     | True -> Cons (True, (mask_aux m v vs))
     | False -> Cons (False, (mask_aux m last vs)))

  (** val fallback_mask : nat -> nat list -> bool list **)

  let fallback_mask m = function
  | Nil -> Nil
  | Cons (v, vs) -> Cons (True, (mask_aux m v vs))

  (** val selected_by_mask : nat list -> bool list -> nat list **)

  let rec selected_by_mask vals g =
    match vals with
    | Nil -> Nil
    | Cons (v, vs) ->
      (match g with
       | Nil -> Nil
       | Cons (b, gs) ->
         (match b with
          | True -> Cons (v, (selected_by_mask vs gs))
          | False -> selected_by_mask vs gs))

  (** val greedy_idx_aux :
      (nat -> nat) -> nat -> nat -> nat list -> nat list **)

  let rec greedy_idx_aux seq m last = function
  | Nil -> Nil
  | Cons (i0, is) ->
    (match Nat.leb (mul m last) (seq i0) with
     | True -> Cons (i0, (greedy_idx_aux seq m (seq i0) is))
     | False -> greedy_idx_aux seq m last is)

  (** val greedy_indices : (nat -> nat) -> nat -> nat list -> nat list **)

  let greedy_indices seq m = function
  | Nil -> Nil
  | Cons (i0, is) -> Cons (i0, (greedy_idx_aux seq m (seq i0) is))
 end

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
    | Cons (h, tl0) ->
      let n_i = nth i0 orig O in
      let Pair (num, den) = acc in
      (match Nat.eqb j i0 with
       | True -> row_sum_frac_aux tl0 orig i0 acc (S j)
       | False ->
         (match Nat.ltb h n_i with
          | True ->
            row_sum_frac_aux tl0 orig i0
              (frac_add num den (pair_num h n_i) (pair_den h n_i)) (S j)
          | False ->
            row_sum_frac_aux tl0 orig i0
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
  | Cons (h, tl0) ->
    (match Nat.ltb prev h with
     | True -> sorted_aux h tl0
     | False -> False)

  (** val sorted_strict_aux : nat list -> bool **)

  let sorted_strict_aux = function
  | Nil -> True
  | Cons (h, tl0) -> sorted_aux h tl0

  (** val all_ge_2 : nat list -> bool **)

  let rec all_ge_2 = function
  | Nil -> True
  | Cons (h, tl0) ->
    (match Nat.leb (S (S O)) h with
     | True -> all_ge_2 tl0
     | False -> False)

  (** val all_pairs_ok : nat list -> bool **)

  let rec all_pairs_ok = function
  | Nil -> True
  | Cons (h, tl0) ->
    (match forallb (fun n -> pair_ok h n) tl0 with
     | True -> all_pairs_ok tl0
     | False -> False)

  (** val all_rows_le : nat list -> nat list -> nat -> bool **)

  let rec all_rows_le i orig i0 =
    match i with
    | Nil -> True
    | Cons (_, tl0) ->
      (match row_le_4_5 (row_sum_frac orig i0) with
       | True -> all_rows_le tl0 orig (S i0)
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
