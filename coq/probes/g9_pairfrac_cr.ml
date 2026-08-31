
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type nat =
| O
| S of nat

type ('a, 'p) sigT =
| ExistT of 'a * 'p

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

  (** val sub : nat -> nat -> nat **)

  let rec sub n m =
    match n with
    | O -> n
    | S k -> (match m with
              | O -> n
              | S l -> sub k l)

  (** val sqrt_iter : nat -> nat -> nat -> nat -> nat **)

  let rec sqrt_iter k p q0 r =
    match k with
    | O -> p
    | S k' ->
      (match r with
       | O -> sqrt_iter k' (S p) (S (S q0)) (S (S q0))
       | S r' -> sqrt_iter k' p q0 r')

  (** val sqrt : nat -> nat **)

  let sqrt n =
    sqrt_iter n O O O
 end

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val of_succ_nat : nat -> positive **)

  let rec of_succ_nat = function
  | O -> XH
  | S x -> succ (of_succ_nat x)
 end

module Coq_Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val of_succ_nat : nat -> positive **)

  let rec of_succ_nat = function
  | O -> XH
  | S x -> succ (of_succ_nat x)
 end

module Z =
 struct
  (** val of_nat : nat -> z **)

  let of_nat = function
  | O -> Z0
  | S n0 -> Zpos (Pos.of_succ_nat n0)
 end

type q = { qnum : z; qden : positive }

(** val g9_pf : nat -> nat -> q **)

let g9_pf a b =
  { qnum = (Z.of_nat (Nat.mul a b)); qden =
    (Coq_Pos.of_succ_nat
      (Nat.sub
        (Nat.mul (Nat.mul (S (S O)) (Nat.sub b a)) (Nat.sqrt (Nat.mul a b)))
        (S O))) }

(** val g9_closed : nat -> q **)

let g9_closed c =
  { qnum = (Z.of_nat c); qden =
    (Coq_Pos.of_succ_nat
      (Nat.sub (Nat.mul (S (S O)) (Nat.sub (Nat.mul c c) (S O))) (S O))) }

(** val g9_pf_C4_13 : __ **)

let g9_pf_C4_13 =
  __

(** val g9_closed_form_cert : nat -> nat -> (q, __) sigT **)

let g9_closed_form_cert a c =
  ExistT ((g9_pf a (Nat.mul (Nat.mul c c) a)), __)
