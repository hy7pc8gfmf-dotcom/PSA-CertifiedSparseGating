
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

(** val fst : ('a1, 'a2) prod -> 'a1 **)

let fst = function
| Pair (x, _) -> x

type comparison =
| Eq
| Lt
| Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

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

module Nat =
 struct
  (** val pred : nat -> nat **)

  let pred n = match n with
  | O -> n
  | S u -> u

  (** val eq_dec : nat -> nat -> sumbool **)

  let rec eq_dec n m =
    match n with
    | O -> (match m with
            | O -> Left
            | S _ -> Right)
    | S n0 -> (match m with
               | O -> Right
               | S n1 -> eq_dec n0 n1)
 end

module Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> XO (add_carry p q0)
       | XO q0 -> XI (add p q0)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q0 -> XI (add p q0)
       | XO q0 -> XO (add p q0)
       | XH -> XI p)
    | XH -> (match y with
             | XI q0 -> XO (succ q0)
             | XO q0 -> XI q0
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> XI (add_carry p q0)
       | XO q0 -> XO (add_carry p q0)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q0 -> XO (add_carry p q0)
       | XO q0 -> XI (add p q0)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q0 -> XI (succ q0)
       | XO q0 -> XO (succ q0)
       | XH -> XI XH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> compare_cont r p q0
       | XO q0 -> compare_cont Gt p q0
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q0 -> compare_cont Lt p q0
       | XO q0 -> compare_cont r p q0
       | XH -> Gt)
    | XH -> (match y with
             | XH -> r
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq

  (** val eqb : positive -> positive -> bool **)

  let rec eqb p q0 =
    match p with
    | XI p0 -> (match q0 with
                | XI q1 -> eqb p0 q1
                | _ -> False)
    | XO p0 -> (match q0 with
                | XO q1 -> eqb p0 q1
                | _ -> False)
    | XH -> (match q0 with
             | XH -> True
             | _ -> False)

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

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> XO (add_carry p q0)
       | XO q0 -> XI (add p q0)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q0 -> XI (add p q0)
       | XO q0 -> XO (add p q0)
       | XH -> XI p)
    | XH -> (match y with
             | XI q0 -> XO (succ q0)
             | XO q0 -> XI q0
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> XI (add_carry p q0)
       | XO q0 -> XO (add_carry p q0)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q0 -> XO (add_carry p q0)
       | XO q0 -> XI (add p q0)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q0 -> XI (succ q0)
       | XO q0 -> XO (succ q0)
       | XH -> XI XH)

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y
 end

module Z =
 struct
  (** val double : z -> z **)

  let double = function
  | Z0 -> Z0
  | Zpos p -> Zpos (XO p)
  | Zneg p -> Zneg (XO p)

  (** val succ_double : z -> z **)

  let succ_double = function
  | Z0 -> Zpos XH
  | Zpos p -> Zpos (XI p)
  | Zneg p -> Zneg (Pos.pred_double p)

  (** val pred_double : z -> z **)

  let pred_double = function
  | Z0 -> Zneg XH
  | Zpos p -> Zpos (Pos.pred_double p)
  | Zneg p -> Zneg (XI p)

  (** val pos_sub : positive -> positive -> z **)

  let rec pos_sub x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> double (pos_sub p q0)
       | XO q0 -> succ_double (pos_sub p q0)
       | XH -> Zpos (XO p))
    | XO p ->
      (match y with
       | XI q0 -> pred_double (pos_sub p q0)
       | XO q0 -> double (pos_sub p q0)
       | XH -> Zpos (Pos.pred_double p))
    | XH ->
      (match y with
       | XI q0 -> Zneg (XO q0)
       | XO q0 -> Zneg (Pos.pred_double q0)
       | XH -> Z0)

  (** val add : z -> z -> z **)

  let add x y =
    match x with
    | Z0 -> y
    | Zpos x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> Zpos (Pos.add x' y')
       | Zneg y' -> pos_sub x' y')
    | Zneg x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> pos_sub y' x'
       | Zneg y' -> Zneg (Pos.add x' y'))

  (** val opp : z -> z **)

  let opp = function
  | Z0 -> Z0
  | Zpos x0 -> Zneg x0
  | Zneg x0 -> Zpos x0

  (** val mul : z -> z -> z **)

  let mul x y =
    match x with
    | Z0 -> Z0
    | Zpos x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zpos (Pos.mul x' y')
       | Zneg y' -> Zneg (Pos.mul x' y'))
    | Zneg x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zneg (Pos.mul x' y')
       | Zneg y' -> Zpos (Pos.mul x' y'))

  (** val compare : z -> z -> comparison **)

  let compare x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> Eq
             | Zpos _ -> Lt
             | Zneg _ -> Gt)
    | Zpos x' -> (match y with
                  | Zpos y' -> Pos.compare x' y'
                  | _ -> Gt)
    | Zneg x' ->
      (match y with
       | Zneg y' -> compOpp (Pos.compare x' y')
       | _ -> Lt)

  (** val eqb : z -> z -> bool **)

  let eqb x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> True
             | _ -> False)
    | Zpos p -> (match y with
                 | Zpos q0 -> Pos.eqb p q0
                 | _ -> False)
    | Zneg p -> (match y with
                 | Zneg q0 -> Pos.eqb p q0
                 | _ -> False)

  (** val of_nat : nat -> z **)

  let of_nat = function
  | O -> Z0
  | S n0 -> Zpos (Pos.of_succ_nat n0)

  (** val abs : z -> z **)

  let abs = function
  | Zneg p -> Zpos p
  | x -> x
 end

type q = { qnum : z; qden : positive }

(** val qcompare : q -> q -> comparison **)

let qcompare p q0 =
  Z.compare (Z.mul p.qnum (Zpos q0.qden)) (Z.mul q0.qnum (Zpos p.qden))

(** val qeq_bool : q -> q -> bool **)

let qeq_bool x y =
  Z.eqb (Z.mul x.qnum (Zpos y.qden)) (Z.mul y.qnum (Zpos x.qden))

(** val qplus : q -> q -> q **)

let qplus x y =
  { qnum = (Z.add (Z.mul x.qnum (Zpos y.qden)) (Z.mul y.qnum (Zpos x.qden)));
    qden = (Coq_Pos.mul x.qden y.qden) }

(** val qmult : q -> q -> q **)

let qmult x y =
  { qnum = (Z.mul x.qnum y.qnum); qden = (Coq_Pos.mul x.qden y.qden) }

(** val qopp : q -> q **)

let qopp x =
  { qnum = (Z.opp x.qnum); qden = x.qden }

(** val qminus : q -> q -> q **)

let qminus x y =
  qplus x (qopp y)

(** val qabs : q -> q **)

let qabs x =
  let { qnum = n; qden = d } = x in { qnum = (Z.abs n); qden = d }

type 'a id =
| Id_refl

type ('a, 'b) and0 = ('a, 'b) prod

type ('a, 'b) or0 = ('a, 'b) sum

(** val idT_of_eq : 'a1 -> 'a1 -> 'a1 id **)

let idT_of_eq _ _ =
  Id_refl

type qltT = bool id

type qeqT = bool id

type qleT = (qltT, qeqT) or0

(** val qlt_to_QltT : q -> q -> qltT **)

let qlt_to_QltT x y =
  let c = qcompare x y in
  (match c with
   | Lt -> Id_refl
   | _ -> assert false (* absurd case *))

(** val qeqT_of_Qeq : q -> q -> qeqT **)

let qeqT_of_Qeq x y =
  idT_of_eq (qeq_bool x y) True

(** val qle_to_QleT : q -> q -> qleT **)

let qle_to_QleT x y =
  let c = qcompare x y in
  (match c with
   | Eq -> Inr (qeqT_of_Qeq x y)
   | Lt -> Inl (qlt_to_QltT x y)
   | Gt -> assert false (* absurd case *))

(** val qtw_qsum : (nat -> q) -> nat -> q **)

let rec qtw_qsum f = function
| O -> f O
| S n' -> qplus (qtw_qsum f n') (f (S n'))

(** val gtw_ip : (nat -> nat -> q) -> nat -> nat -> nat -> q **)

let gtw_ip v i j m =
  qtw_qsum (fun k -> qmult (v i k) (v j k)) (Nat.pred m)

(** val gtw_S : (nat -> q) -> nat -> q **)

let gtw_S c n =
  qtw_qsum (fun i -> qmult (c i) (c i)) (Nat.pred n)

(** val gtw_Fsq : (nat -> nat -> q) -> (nat -> q) -> nat -> nat -> q **)

let gtw_Fsq v c n m =
  qtw_qsum (fun k ->
    qmult (qtw_qsum (fun i -> qmult (c i) (v i k)) (Nat.pred n))
      (qtw_qsum (fun i -> qmult (c i) (v i k)) (Nat.pred n)))
    (Nat.pred m)

(** val gtw_offdiag : (nat -> nat -> q) -> (nat -> q) -> nat -> nat -> q **)

let gtw_offdiag v c n m =
  qtw_qsum (fun i ->
    qtw_qsum (fun j ->
      match Nat.eq_dec i j with
      | Left -> { qnum = Z0; qden = XH }
      | Right -> qmult (qmult (c i) (c j)) (gtw_ip v i j m)) (Nat.pred n))
    (Nat.pred n)

(** val gtw_W : (nat -> nat -> q) -> (nat -> q) -> nat -> nat -> q **)

let gtw_W v c n m =
  qtw_qsum (fun i ->
    qtw_qsum (fun j ->
      match Nat.eq_dec i j with
      | Left -> { qnum = Z0; qden = XH }
      | Right ->
        qmult (qmult (qabs (c i)) (qabs (c j))) (qabs (gtw_ip v i j m)))
      (Nat.pred n))
    (Nat.pred n)

(** val gershgorin_frame_mu_qtw :
    nat -> nat -> (nat -> nat -> q) -> q -> (nat -> __ -> qeqT) -> (nat -> __
    -> qleT) -> (nat -> q) -> (qleT, qleT) and0 **)

let gershgorin_frame_mu_qtw n m v mu _ _ c =
  Pair
    ((qle_to_QleT
       (qmult (qminus { qnum = (Zpos XH); qden = XH } mu) (gtw_S c n))
       (gtw_Fsq v c n m)),
    (qle_to_QleT (gtw_Fsq v c n m)
      (qmult (qplus { qnum = (Zpos XH); qden = XH } mu) (gtw_S c n))))

(** val gtw_gap_witness :
    nat -> nat -> (nat -> nat -> q) -> q -> (nat -> __ -> qeqT) -> (nat -> __
    -> qleT) -> qltT -> (nat -> q) -> (q, (qltT, qleT) and0) sigT **)

let gtw_gap_witness n m v mu hunit hrow _ c =
  ExistT ((qminus { qnum = (Zpos XH); qden = XH } mu), (Pair
    ((qlt_to_QltT { qnum = Z0; qden = XH }
       (qminus { qnum = (Zpos XH); qden = XH } mu)),
    (fst (gershgorin_frame_mu_qtw n m v mu hunit hrow c)))))

(** val gtw_smoke_v : nat -> nat -> q **)

let gtw_smoke_v i k =
  match Nat.eq_dec i k with
  | Left -> { qnum = (Zpos XH); qden = XH }
  | Right -> { qnum = Z0; qden = XH }

(** val gtw_smoke_c : nat -> q **)

let gtw_smoke_c i =
  { qnum = (Z.add (Z.of_nat i) (Zpos XH)); qden = XH }

(** val gtw_smoke_data : bool **)

let gtw_smoke_data =
  match qeq_bool (gtw_Fsq gtw_smoke_v gtw_smoke_c (S (S O)) (S (S (S O))))
          (gtw_S gtw_smoke_c (S (S O))) with
  | True ->
    qeq_bool (gtw_W gtw_smoke_v gtw_smoke_c (S (S O)) (S (S (S O)))) { qnum =
      Z0; qden = XH }
  | False -> False

(** val gtw_smoke_eval : bool **)

let gtw_smoke_eval =
  qeq_bool
    (qmult (qminus { qnum = (Zpos XH); qden = XH } { qnum = Z0; qden = XH })
      (gtw_S gtw_smoke_c (S (S O))))
    (gtw_Fsq gtw_smoke_v gtw_smoke_c (S (S O)) (S (S (S O))))
