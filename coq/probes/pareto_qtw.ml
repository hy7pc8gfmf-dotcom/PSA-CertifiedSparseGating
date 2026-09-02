
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
  (** val add : nat -> nat -> nat **)

  let rec add n m =
    match n with
    | O -> m
    | S p -> S (add p m)

  (** val sub : nat -> nat -> nat **)

  let rec sub n m =
    match n with
    | O -> n
    | S k -> (match m with
              | O -> n
              | S l -> sub k l)

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

(** val qinv : q -> q **)

let qinv x =
  match x.qnum with
  | Z0 -> { qnum = Z0; qden = XH }
  | Zpos p -> { qnum = (Zpos x.qden); qden = p }
  | Zneg p -> { qnum = (Zneg x.qden); qden = p }

(** val qdiv : q -> q -> q **)

let qdiv x y =
  qmult x (qinv y)

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

(** val qltT_trans : q -> q -> q -> qltT -> qltT -> qltT **)

let qltT_trans x _ z0 _ _ =
  qlt_to_QltT x z0

(** val qleT_refl : q -> qleT **)

let qleT_refl x =
  Inr (qeqT_of_Qeq x x)

(** val qleT_trans : q -> q -> q -> qleT -> qleT -> qleT **)

let qleT_trans x _ z0 _ _ =
  qle_to_QleT x z0

(** val qtw_leT_congr_r : q -> q -> q -> qleT -> qeqT -> qleT **)

let qtw_leT_congr_r x _ z0 h _ =
  match h with
  | Inl _ -> Inl (qlt_to_QltT x z0)
  | Inr _ -> Inr (qeqT_of_Qeq x z0)

(** val qtw_leT_congr_l : q -> q -> q -> qleT -> qeqT -> qleT **)

let qtw_leT_congr_l _ y z0 h _ =
  match h with
  | Inl _ -> Inl (qlt_to_QltT z0 y)
  | Inr _ -> Inr (qeqT_of_Qeq z0 y)

(** val qmult_ltT_compat_r : q -> q -> q -> qltT -> qltT -> qltT **)

let qmult_ltT_compat_r x y a _ _ =
  qlt_to_QltT (qmult x a) (qmult y a)

(** val qmult_leT_compat_r : q -> q -> q -> qleT -> qleT -> qleT **)

let qmult_leT_compat_r x y a _ _ =
  qle_to_QleT (qmult x a) (qmult y a)

(** val qmult_leT_0_compat : q -> q -> qleT -> qleT -> qleT **)

let qmult_leT_0_compat x y _ _ =
  qle_to_QleT { qnum = Z0; qden = XH } (qmult x y)

(** val s281_lo : q **)

let s281_lo =
  { qnum = (Zpos (XI (XI (XI (XO (XO (XI (XO XH)))))))); qden = (XO (XI (XO
    XH))) }

(** val c_q : q -> q **)

let c_q s =
  qmult
    (qplus { qnum = (Zpos (XI (XO (XO (XI (XI (XO (XO XH)))))))); qden = XH }
      (qmult { qnum = (Zpos (XI (XO XH))); qden = XH } s))
    { qnum = (Zpos XH); qden = (XO (XO (XO (XO (XO (XO (XO XH))))))) }

(** val par_c_ratio_lt : q -> qleT -> qltT **)

let par_c_ratio_lt s _ =
  qlt_to_QltT { qnum = (Zpos (XI (XO (XO XH)))); qden = (XI (XO XH)) } (c_q s)

(** val par_c_sandwich : q -> qleT -> qleT -> (qltT, qleT) and0 **)

let par_c_sandwich s hlo _ =
  Pair ((par_c_ratio_lt s hlo),
    (qle_to_QleT (c_q s) { qnum = (Zpos (XI (XO (XI (XI (XO (XI (XI
      XH)))))))); qden = (XO (XO (XO (XO (XO (XO (XO XH))))))) }))

(** val par_ratio_gap : q -> qleT -> (q, (qltT, qleT) and0) sigT **)

let par_ratio_gap s _ =
  ExistT
    ((qminus (c_q s) { qnum = (Zpos (XI (XO (XO XH)))); qden = (XI (XO XH)) }),
    (Pair
    ((qlt_to_QltT { qnum = Z0; qden = XH }
       (qminus (c_q s) { qnum = (Zpos (XI (XO (XO XH)))); qden = (XI (XO
         XH)) })),
    (Inr
    (qeqT_of_Qeq
      (qplus { qnum = (Zpos (XI (XO (XO XH)))); qden = (XI (XO XH)) }
        (qminus (c_q s) { qnum = (Zpos (XI (XO (XO XH)))); qden = (XI (XO
          XH)) }))
      (c_q s))))))

(** val par_c_lt_triggers :
    q -> q -> q -> qeqT -> qleT -> qltT -> qltT -> qltT -> qltT **)

let par_c_lt_triggers _ n n1 _ _ _ _ _ =
  qlt_to_QltT
    (qmult
      (qmult { qnum = (Zpos (XO (XO (XO (XO (XO (XO XH))))))); qden = XH }
        (qminus n1 n))
      (qminus n1 n))
    (qmult { qnum = (Zpos (XI (XO (XO (XI XH))))); qden = XH } (qmult n n1))

(** val par_same_bin_quad :
    q -> q -> q -> qeqT -> qleT -> qltT -> qltT -> qltT -> qltT **)

let par_same_bin_quad s n n1 hss hlo hn hnn hratio =
  par_c_lt_triggers s n n1 hss hlo hn hnn
    (qltT_trans n1
      (qmult { qnum = (Zpos (XI (XO (XO XH)))); qden = (XI (XO XH)) } n)
      (qmult (c_q s) n) hratio
      (qmult_ltT_compat_r { qnum = (Zpos (XI (XO (XO XH)))); qden = (XI (XO
        XH)) } (c_q s) n hn (par_c_ratio_lt s hlo)))

(** val qnat : nat -> q **)

let qnat i =
  { qnum = (Z.of_nat i); qden = XH }

(** val fall9q : nat -> q **)

let rec fall9q = function
| O -> { qnum = (Zpos XH); qden = XH }
| S m1 ->
  qmult (qnat (Nat.sub (S (S (S (S (S (S (S (S (S O))))))))) m1)) (fall9q m1)

(** val pow9q : nat -> q **)

let rec pow9q = function
| O -> { qnum = (Zpos XH); qden = XH }
| S m1 -> qmult { qnum = (Zpos (XI (XO (XO XH)))); qden = XH } (pow9q m1)

(** val no_collision_q : nat -> q **)

let no_collision_q m =
  qdiv (fall9q m) (pow9q m)

(** val par_qnat_le9 : nat -> qleT **)

let par_qnat_le9 m =
  qle_to_QleT (qnat (Nat.sub (S (S (S (S (S (S (S (S (S O))))))))) m))
    { qnum = (Zpos (XI (XO (XO XH)))); qden = XH }

(** val par_qnat_nonnegT : nat -> qleT **)

let par_qnat_nonnegT i =
  qle_to_QleT { qnum = Z0; qden = XH } (qnat i)

(** val par_pow9_posT : nat -> qltT **)

let par_pow9_posT m =
  qlt_to_QltT { qnum = Z0; qden = XH } (pow9q m)

(** val par_fall9q_nonnegT : nat -> qleT **)

let rec par_fall9q_nonnegT = function
| O -> Inl (qlt_to_QltT { qnum = Z0; qden = XH } (fall9q O))
| S n0 ->
  qmult_leT_0_compat
    (qnat (Nat.sub (S (S (S (S (S (S (S (S (S O))))))))) n0))
    (let rec fall9q0 = function
     | O -> { qnum = (Zpos XH); qden = XH }
     | S m1 ->
       qmult (qnat (Nat.sub (S (S (S (S (S (S (S (S (S O))))))))) m1))
         (fall9q0 m1)
     in fall9q0 n0)
    (par_qnat_nonnegT (Nat.sub (S (S (S (S (S (S (S (S (S O))))))))) n0))
    (par_fall9q_nonnegT n0)

(** val par_div_leT :
    q -> q -> q -> q -> qleT -> qltT -> qltT -> qleT -> qleT **)

let par_div_leT a b c d _ _ _ _ =
  qle_to_QleT (qdiv a b) (qdiv c d)

(** val par_nc_decreasing : nat -> qleT **)

let par_nc_decreasing m =
  par_div_leT
    (qmult (qnat (Nat.sub (S (S (S (S (S (S (S (S (S O))))))))) m))
      (fall9q m))
    (qmult { qnum = (Zpos (XI (XO (XO XH)))); qden = XH } (pow9q m))
    (fall9q m) (pow9q m)
    (qmult_leT_0_compat
      (qnat (Nat.sub (S (S (S (S (S (S (S (S (S O))))))))) m)) (fall9q m)
      (par_qnat_nonnegT (Nat.sub (S (S (S (S (S (S (S (S (S O))))))))) m))
      (par_fall9q_nonnegT m))
    (qlt_to_QltT { qnum = Z0; qden = XH }
      (qmult { qnum = (Zpos (XI (XO (XO XH)))); qden = XH } (pow9q m)))
    (qlt_to_QltT { qnum = Z0; qden = XH } (pow9q m))
    (qtw_leT_congr_l
      (qmult (qnat (Nat.sub (S (S (S (S (S (S (S (S (S O))))))))) m))
        (qmult (fall9q m) (pow9q m)))
      (qmult (fall9q m)
        (qmult { qnum = (Zpos (XI (XO (XO XH)))); qden = XH } (pow9q m)))
      (qmult
        (qmult (qnat (Nat.sub (S (S (S (S (S (S (S (S (S O))))))))) m))
          (fall9q m))
        (pow9q m))
      (qtw_leT_congr_r
        (qmult (qnat (Nat.sub (S (S (S (S (S (S (S (S (S O))))))))) m))
          (qmult (fall9q m) (pow9q m)))
        (qmult { qnum = (Zpos (XI (XO (XO XH)))); qden = XH }
          (qmult (fall9q m) (pow9q m)))
        (qmult (fall9q m)
          (qmult { qnum = (Zpos (XI (XO (XO XH)))); qden = XH } (pow9q m)))
        (qmult_leT_compat_r
          (qnat (Nat.sub (S (S (S (S (S (S (S (S (S O))))))))) m)) { qnum =
          (Zpos (XI (XO (XO XH)))); qden = XH } (qmult (fall9q m) (pow9q m))
          (qmult_leT_0_compat (fall9q m) (pow9q m) (par_fall9q_nonnegT m)
            (Inl (par_pow9_posT m)))
          (par_qnat_le9 m))
        (qeqT_of_Qeq
          (qmult { qnum = (Zpos (XI (XO (XO XH)))); qden = XH }
            (qmult (fall9q m) (pow9q m)))
          (qmult (fall9q m)
            (qmult { qnum = (Zpos (XI (XO (XO XH)))); qden = XH } (pow9q m)))))
      (qeqT_of_Qeq
        (qmult
          (qmult (qnat (Nat.sub (S (S (S (S (S (S (S (S (S O))))))))) m))
            (fall9q m))
          (pow9q m))
        (qmult (qnat (Nat.sub (S (S (S (S (S (S (S (S (S O))))))))) m))
          (qmult (fall9q m) (pow9q m)))))

(** val par_nc_le : nat -> nat -> qleT **)

let rec par_nc_le m = function
| O -> qleT_refl (no_collision_q O)
| S n0 ->
  let s = Nat.eq_dec m (S n0) in
  (match s with
   | Left -> qleT_refl (no_collision_q (S n0))
   | Right ->
     qleT_trans (no_collision_q (S n0)) (no_collision_q n0)
       (no_collision_q m) (par_nc_decreasing n0) (par_nc_le m n0))

(** val par_fall10_zero : nat -> qeqT **)

let par_fall10_zero = function
| O ->
  qeqT_of_Qeq (fall9q (Nat.add (S (S (S (S (S (S (S (S (S (S O)))))))))) O))
    { qnum = Z0; qden = XH }
| S n ->
  qeqT_of_Qeq
    (fall9q (Nat.add (S (S (S (S (S (S (S (S (S (S O)))))))))) (S n)))
    { qnum = Z0; qden = XH }

(** val par_nc7_val : qeqT **)

let par_nc7_val =
  qeqT_of_Qeq (no_collision_q (S (S (S (S (S (S (S O)))))))) { qnum = (Zpos
    (XO (XO (XO (XO (XO (XO (XI (XI (XO (XO (XI (XO (XO (XO (XI (XI (XO
    XH)))))))))))))))))); qden = (XI (XO (XO (XI (XI (XI (XI (XO (XI (XI (XO
    (XI (XI (XI (XI (XI (XO (XO (XO (XI (XO (XO XH)))))))))))))))))))))) }

(** val par_prob7 : qleT **)

let par_prob7 =
  Inl
    (qlt_to_QltT { qnum = (Zpos (XO (XO (XO (XO (XO (XI XH))))))); qden = (XO
      (XO (XI (XO (XO (XI XH)))))) }
      (qminus { qnum = (Zpos XH); qden = XH }
        (no_collision_q (S (S (S (S (S (S (S O))))))))))

(** val par_prob8 : qleT **)

let par_prob8 =
  Inl
    (qlt_to_QltT { qnum = (Zpos (XI (XI (XO (XO (XO (XI XH))))))); qden = (XO
      (XO (XI (XO (XO (XI XH)))))) }
      (qminus { qnum = (Zpos XH); qden = XH }
        (no_collision_q (S (S (S (S (S (S (S (S O)))))))))))

(** val par_prob_mono : qleT **)

let par_prob_mono =
  Inl
    (qlt_to_QltT
      (qminus { qnum = (Zpos XH); qden = XH }
        (no_collision_q (S (S (S (S (S (S (S O)))))))))
      (qminus { qnum = (Zpos XH); qden = XH }
        (no_collision_q (S (S (S (S (S (S (S (S O)))))))))))

(** val par_smoke_gap : q **)

let par_smoke_gap =
  qminus (c_q s281_lo) { qnum = (Zpos (XI (XO (XO XH)))); qden = (XI (XO
    XH)) }

(** val par_smoke_gap_ok : bool **)

let par_smoke_gap_ok =
  qeq_bool par_smoke_gap { qnum = (Zpos (XI (XO (XI (XI (XI XH)))))); qden =
    (XO (XO (XO (XO (XO (XO (XO (XO (XI (XO XH)))))))))) }

(** val par_smoke_nc : bool **)

let par_smoke_nc =
  match qeq_bool (no_collision_q (S (S (S (S (S (S (S O)))))))) { qnum =
          (Zpos (XO (XO (XO (XO (XO (XO (XI (XI (XO (XO (XI (XO (XO (XO (XI
          (XI (XO XH)))))))))))))))))); qden = (XI (XO (XO (XI (XI (XI (XI
          (XO (XI (XI (XO (XI (XI (XI (XI (XI (XO (XO (XO (XI (XO (XO
          XH)))))))))))))))))))))) } with
  | True ->
    qeq_bool (no_collision_q (S (S (S (S (S (S (S (S O))))))))) { qnum =
      (Zpos (XO (XO (XO (XO (XO (XO (XO (XI (XI (XO (XO (XI (XO (XO (XO (XI
      (XI (XO XH))))))))))))))))))); qden = (XI (XO (XO (XO (XO (XO (XI (XO
      (XI (XI (XI (XO (XI (XO (XI (XI (XO (XO (XO (XO (XI (XO (XO (XI (XO
      XH))))))))))))))))))))))))) }
  | False -> False

(** val prt_qleb : q -> q -> bool **)

let prt_qleb x y =
  match qcompare x y with
  | Gt -> False
  | _ -> True

(** val par_smoke_prob : bool **)

let par_smoke_prob =
  match prt_qleb { qnum = (Zpos (XO (XO (XO (XO (XO (XI XH))))))); qden = (XO
          (XO (XI (XO (XO (XI XH)))))) }
          (qminus { qnum = (Zpos XH); qden = XH }
            (no_collision_q (S (S (S (S (S (S (S O))))))))) with
  | True ->
    prt_qleb { qnum = (Zpos (XI (XI (XO (XO (XO (XI XH))))))); qden = (XO (XO
      (XI (XO (XO (XI XH)))))) }
      (qminus { qnum = (Zpos XH); qden = XH }
        (no_collision_q (S (S (S (S (S (S (S (S O))))))))))
  | False -> False

(** val par_smoke_dec_cert : qleT **)

let par_smoke_dec_cert =
  par_nc_decreasing (S (S (S (S (S (S (S O)))))))

(** val par_smoke_gap_cert : (q, (qltT, qleT) and0) sigT **)

let par_smoke_gap_cert =
  par_ratio_gap s281_lo (qleT_refl s281_lo)
