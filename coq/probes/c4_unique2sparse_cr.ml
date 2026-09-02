
type bool =
| True
| False

(** val negb : bool -> bool **)

let negb = function
| True -> False
| False -> True

type nat =
| O
| S of nat

type ('a, 'b) prod =
| Pair of 'a * 'b

type comparison =
| Eq
| Lt
| Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

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

  (** val leb : z -> z -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> False
    | _ -> True
 end

type q = { qnum : z; qden : positive }

(** val qle_bool : q -> q -> bool **)

let qle_bool x y =
  Z.leb (Z.mul x.qnum (Zpos y.qden)) (Z.mul y.qnum (Zpos x.qden))

(** val qplus : q -> q -> q **)

let qplus x y =
  { qnum = (Z.add (Z.mul x.qnum (Zpos y.qden)) (Z.mul y.qnum (Zpos x.qden)));
    qden = (Coq_Pos.mul x.qden y.qden) }

(** val pfb4 : nat -> nat -> q **)

let pfb4 i j =
  match i with
  | O ->
    (match j with
     | O -> { qnum = Z0; qden = XH }
     | S n ->
       (match n with
        | O ->
          { qnum = (Zpos (XI (XI (XI (XO (XO XH)))))); qden = (XO (XO (XO (XI
            (XI (XI XH)))))) }
        | S n0 ->
          (match n0 with
           | O ->
             { qnum = (Zpos (XI (XI (XI (XI (XI (XO (XO XH)))))))); qden =
               (XO (XO (XO (XO (XI (XI (XO (XI (XO (XO XH)))))))))) }
           | S n1 ->
             (match n1 with
              | O ->
                { qnum = (Zpos (XI (XI (XI (XI (XI (XI (XI (XO (XO
                  XH)))))))))); qden = (XO (XO (XI (XO (XO (XO (XO (XO (XI
                  (XO (XO (XI (XO XH))))))))))))) }
              | S _ -> { qnum = Z0; qden = XH }))))
  | S n ->
    (match n with
     | O ->
       (match j with
        | O ->
          { qnum = (Zpos (XI (XI (XI (XO (XO XH)))))); qden = (XO (XO (XO (XI
            (XI (XI XH)))))) }
        | S n0 ->
          (match n0 with
           | O -> { qnum = Z0; qden = XH }
           | S n1 ->
             (match n1 with
              | O ->
                { qnum = (Zpos (XI (XO (XO (XO (XI (XI (XO (XI (XO
                  XH)))))))))); qden = (XO (XO (XO (XO (XO (XI (XO (XO (XO
                  (XO (XO XH))))))))))) }
              | S n2 ->
                (match n2 with
                 | O ->
                   { qnum = (Zpos (XI (XO (XO (XO (XI (XO (XI (XI (XO (XI (XO
                     XH)))))))))))); qden = (XO (XO (XO (XO (XO (XO (XI (XO
                     (XI (XO (XO (XO (XI (XO XH)))))))))))))) }
                 | S _ -> { qnum = Z0; qden = XH }))))
     | S n0 ->
       (match n0 with
        | O ->
          (match j with
           | O ->
             { qnum = (Zpos (XI (XI (XI (XI (XI (XO (XO XH)))))))); qden =
               (XO (XO (XO (XO (XI (XI (XO (XI (XO (XO XH)))))))))) }
           | S n1 ->
             (match n1 with
              | O ->
                { qnum = (Zpos (XI (XO (XO (XO (XI (XI (XO (XI (XO
                  XH)))))))))); qden = (XO (XO (XO (XO (XO (XI (XO (XO (XO
                  (XO (XO XH))))))))))) }
              | S n2 ->
                (match n2 with
                 | O -> { qnum = Z0; qden = XH }
                 | S n3 ->
                   (match n3 with
                    | O ->
                      { qnum = (Zpos (XI (XO (XO (XI (XI (XO (XO (XO (XO (XO
                        (XI (XI (XO XH)))))))))))))); qden = (XO (XO (XO (XO
                        (XO (XO (XO (XI (XO (XO (XI (XO (XO (XO (XO
                        XH))))))))))))))) }
                    | S _ -> { qnum = Z0; qden = XH }))))
        | S _ ->
          (match j with
           | O ->
             { qnum = (Zpos (XI (XI (XI (XI (XI (XI (XI (XO (XO XH))))))))));
               qden = (XO (XO (XI (XO (XO (XO (XO (XO (XI (XO (XO (XI (XO
               XH))))))))))))) }
           | S n1 ->
             (match n1 with
              | O ->
                { qnum = (Zpos (XI (XO (XO (XO (XI (XO (XI (XI (XO (XI (XO
                  XH)))))))))))); qden = (XO (XO (XO (XO (XO (XO (XI (XO (XI
                  (XO (XO (XO (XI (XO XH)))))))))))))) }
              | S n2 ->
                (match n2 with
                 | O ->
                   { qnum = (Zpos (XI (XO (XO (XI (XI (XO (XO (XO (XO (XO (XI
                     (XI (XO XH)))))))))))))); qden = (XO (XO (XO (XO (XO (XO
                     (XO (XI (XO (XO (XI (XO (XO (XO (XO XH))))))))))))))) }
                 | S _ -> { qnum = Z0; qden = XH })))))

(** val col4 : nat -> q **)

let col4 j =
  qplus (qplus (qplus (pfb4 O j) (pfb4 (S O) j)) (pfb4 (S (S O)) j))
    (pfb4 (S (S (S O))) j)

(** val rho4 : q **)

let rho4 =
  col4 (S (S O))

(** val c4u_rho4_window : (z, positive) prod **)

let c4u_rho4_window =
  Pair (rho4.qnum, rho4.qden)

(** val c4u_pfb4_table : nat -> nat -> q **)

let c4u_pfb4_table =
  pfb4

(** val c4u_col_window : nat -> (z, positive) prod **)

let c4u_col_window j =
  Pair ((col4 j).qnum, (col4 j).qden)

(** val c4u_col_ok : nat -> bool **)

let c4u_col_ok j =
  qle_bool (col4 j) rho4

(** val c4u_rho4_ok : bool **)

let c4u_rho4_ok =
  negb (qle_bool { qnum = (Zpos XH); qden = XH } rho4)
