
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type unit0 =
| Tt

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

type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b

type ('a, 'b) prod =
| Pair of 'a * 'b

(** val snd : ('a1, 'a2) prod -> 'a2 **)

let snd = function
| Pair (_, y) -> y

type comparison =
| Eq
| Lt
| Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

type ('a, 'p) sigT =
| ExistT of 'a * 'p

type sumbool =
| Left
| Right

module Coq__1 = struct
 (** val add : nat -> nat -> nat **)

 let rec add n m =
   match n with
   | O -> m
   | S p -> S (add p m)
end
include Coq__1

(** val max : nat -> nat -> nat **)

let rec max n m =
  match n with
  | O -> m
  | S n' -> (match m with
             | O -> n
             | S m' -> S (max n' m'))

type 'a unconvertible = unit0

type 'a crelation = __

type ('a, 'b) arrow = 'a -> 'b

type ('a, 'b) iffT = ('a -> 'b, 'b -> 'a) prod

type ('a, 'r, 'x) subrelation = 'a -> 'a -> 'r -> 'x

type ('a, 'r) proper = 'r

type ('a, 'r) properProxy = 'r

type ('a, 'b, 'r, 'x) respectful = 'a -> 'a -> 'r -> 'x

(** val subrelation_respectful :
    ('a1, 'a2, 'a3) subrelation -> ('a4, 'a5, 'a6) subrelation -> ('a1 ->
    'a4, ('a1, 'a4, 'a3, 'a5) respectful, ('a1, 'a4, 'a2, 'a6) respectful)
    subrelation **)

let subrelation_respectful subl subr x y x0 x1 y0 x2 =
  subr (x x1) (y y0) (x0 x1 y0 (subl x1 y0 x2))

(** val subrelation_proper :
    'a1 -> ('a1, 'a2) proper -> 'a1 crelation unconvertible -> ('a1, 'a2,
    'a3) subrelation -> ('a1, 'a3) proper **)

let subrelation_proper m mor _ sub0 =
  sub0 m m mor

(** val iffT_arrow_subrelation : (__, __) iffT -> (__, __) arrow **)

let iffT_arrow_subrelation x x0 =
  let Pair (a, _) = x in a x0

(** val iffT_flip_arrow_subrelation : (__, __) iffT -> (__, __) arrow **)

let iffT_flip_arrow_subrelation x x0 =
  let Pair (_, b) = x in b x0

(** val reflexive_partial_app_morphism :
    ('a1 -> 'a2) -> ('a1 -> 'a2, ('a1, 'a2, 'a3, 'a4) respectful) proper ->
    'a1 -> ('a1, 'a3) properProxy -> ('a2, 'a4) proper **)

let reflexive_partial_app_morphism _ h x h0 =
  h x x h0

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

  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg

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

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  (** val succ_double_mask : mask -> mask **)

  let succ_double_mask = function
  | IsNul -> IsPos XH
  | IsPos p -> IsPos (XI p)
  | IsNeg -> IsNeg

  (** val double_mask : mask -> mask **)

  let double_mask = function
  | IsPos p -> IsPos (XO p)
  | x0 -> x0

  (** val double_pred_mask : positive -> mask **)

  let double_pred_mask = function
  | XI p -> IsPos (XO (XO p))
  | XO p -> IsPos (XO (pred_double p))
  | XH -> IsNul

  (** val sub_mask : positive -> positive -> mask **)

  let rec sub_mask x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> double_mask (sub_mask p q0)
       | XO q0 -> succ_double_mask (sub_mask p q0)
       | XH -> IsPos (XO p))
    | XO p ->
      (match y with
       | XI q0 -> succ_double_mask (sub_mask_carry p q0)
       | XO q0 -> double_mask (sub_mask p q0)
       | XH -> IsPos (pred_double p))
    | XH -> (match y with
             | XH -> IsNul
             | _ -> IsNeg)

  (** val sub_mask_carry : positive -> positive -> mask **)

  and sub_mask_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> succ_double_mask (sub_mask_carry p q0)
       | XO q0 -> double_mask (sub_mask p q0)
       | XH -> IsPos (pred_double p))
    | XO p ->
      (match y with
       | XI q0 -> double_mask (sub_mask_carry p q0)
       | XO q0 -> succ_double_mask (sub_mask_carry p q0)
       | XH -> double_pred_mask p)
    | XH -> IsNeg

  (** val sub : positive -> positive -> positive **)

  let sub x y =
    match sub_mask x y with
    | IsPos z0 -> z0
    | _ -> XH

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1 **)

  let rec iter f x = function
  | XI n' -> f (iter f (iter f x n') n')
  | XO n' -> iter f (iter f x n') n'
  | XH -> f x

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

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    match p with
    | XI p0 -> op a (iter_op op p0 (op a a))
    | XO p0 -> iter_op op p0 (op a a)
    | XH -> a

  (** val to_nat : positive -> nat **)

  let to_nat x =
    iter_op Coq__1.add x (S O)

  (** val pow : positive -> positive -> positive **)

  let pow x =
    iter (mul x) XH

  (** val size_nat : positive -> nat **)

  let rec size_nat = function
  | XI p0 -> S (size_nat p0)
  | XO p0 -> S (size_nat p0)
  | XH -> S O

  (** val ggcdn :
      nat -> positive -> positive -> (positive, (positive, positive) prod)
      prod **)

  let rec ggcdn n a b =
    match n with
    | O -> Pair (XH, (Pair (a, b)))
    | S n0 ->
      (match a with
       | XI a' ->
         (match b with
          | XI b' ->
            (match compare a' b' with
             | Eq -> Pair (a, (Pair (XH, XH)))
             | Lt ->
               let Pair (g, p) = ggcdn n0 (sub b' a') a in
               let Pair (ba, aa) = p in
               Pair (g, (Pair (aa, (add aa (XO ba)))))
             | Gt ->
               let Pair (g, p) = ggcdn n0 (sub a' b') b in
               let Pair (ab, bb) = p in
               Pair (g, (Pair ((add bb (XO ab)), bb))))
          | XO b0 ->
            let Pair (g, p) = ggcdn n0 a b0 in
            let Pair (aa, bb) = p in Pair (g, (Pair (aa, (XO bb))))
          | XH -> Pair (XH, (Pair (a, XH))))
       | XO a0 ->
         (match b with
          | XI _ ->
            let Pair (g, p) = ggcdn n0 a0 b in
            let Pair (aa, bb) = p in Pair (g, (Pair ((XO aa), bb)))
          | XO b0 -> let Pair (g, p) = ggcdn n0 a0 b0 in Pair ((XO g), p)
          | XH -> Pair (XH, (Pair (a, XH))))
       | XH -> Pair (XH, (Pair (XH, b))))

  (** val ggcd :
      positive -> positive -> (positive, (positive, positive) prod) prod **)

  let ggcd a b =
    ggcdn (Coq__1.add (size_nat a) (size_nat b)) a b

  (** val of_nat : nat -> positive **)

  let rec of_nat = function
  | O -> XH
  | S x -> (match x with
            | O -> XH
            | S _ -> succ (of_nat x))
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

  (** val sub : z -> z -> z **)

  let sub m n =
    add m (opp n)

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

  (** val ltb : z -> z -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> True
    | _ -> False

  (** val max : z -> z -> z **)

  let max n m =
    match compare n m with
    | Lt -> m
    | _ -> n

  (** val min : z -> z -> z **)

  let min n m =
    match compare n m with
    | Gt -> m
    | _ -> n

  (** val to_pos : z -> positive **)

  let to_pos = function
  | Zpos p -> p
  | _ -> XH

  (** val pos_div_eucl : positive -> z -> (z, z) prod **)

  let rec pos_div_eucl a b =
    match a with
    | XI a' ->
      let Pair (q0, r) = pos_div_eucl a' b in
      let r' = add (mul (Zpos (XO XH)) r) (Zpos XH) in
      (match ltb r' b with
       | True -> Pair ((mul (Zpos (XO XH)) q0), r')
       | False -> Pair ((add (mul (Zpos (XO XH)) q0) (Zpos XH)), (sub r' b)))
    | XO a' ->
      let Pair (q0, r) = pos_div_eucl a' b in
      let r' = mul (Zpos (XO XH)) r in
      (match ltb r' b with
       | True -> Pair ((mul (Zpos (XO XH)) q0), r')
       | False -> Pair ((add (mul (Zpos (XO XH)) q0) (Zpos XH)), (sub r' b)))
    | XH ->
      (match leb (Zpos (XO XH)) b with
       | True -> Pair (Z0, (Zpos XH))
       | False -> Pair ((Zpos XH), Z0))

  (** val div_eucl : z -> z -> (z, z) prod **)

  let div_eucl a b =
    match a with
    | Z0 -> Pair (Z0, Z0)
    | Zpos a' ->
      (match b with
       | Z0 -> Pair (Z0, a)
       | Zpos _ -> pos_div_eucl a' b
       | Zneg b' ->
         let Pair (q0, r) = pos_div_eucl a' (Zpos b') in
         (match r with
          | Z0 -> Pair ((opp q0), Z0)
          | _ -> Pair ((opp (add q0 (Zpos XH))), (add b r))))
    | Zneg a' ->
      (match b with
       | Z0 -> Pair (Z0, a)
       | Zpos _ ->
         let Pair (q0, r) = pos_div_eucl a' b in
         (match r with
          | Z0 -> Pair ((opp q0), Z0)
          | _ -> Pair ((opp (add q0 (Zpos XH))), (sub b r)))
       | Zneg b' ->
         let Pair (q0, r) = pos_div_eucl a' (Zpos b') in Pair (q0, (opp r)))

  (** val div : z -> z -> z **)

  let div a b =
    let Pair (q0, _) = div_eucl a b in q0

  (** val sgn : z -> z **)

  let sgn = function
  | Z0 -> Z0
  | Zpos _ -> Zpos XH
  | Zneg _ -> Zneg XH

  (** val abs : z -> z **)

  let abs = function
  | Zneg p -> Zpos p
  | x -> x

  (** val ggcd : z -> z -> (z, (z, z) prod) prod **)

  let ggcd a b =
    match a with
    | Z0 -> Pair ((abs b), (Pair (Z0, (sgn b))))
    | Zpos a0 ->
      (match b with
       | Z0 -> Pair ((abs a), (Pair ((sgn a), Z0)))
       | Zpos b0 ->
         let Pair (g, p) = Coq_Pos.ggcd a0 b0 in
         let Pair (aa, bb) = p in
         Pair ((Zpos g), (Pair ((Zpos aa), (Zpos bb))))
       | Zneg b0 ->
         let Pair (g, p) = Coq_Pos.ggcd a0 b0 in
         let Pair (aa, bb) = p in
         Pair ((Zpos g), (Pair ((Zpos aa), (Zneg bb)))))
    | Zneg a0 ->
      (match b with
       | Z0 -> Pair ((abs a), (Pair ((sgn a), Z0)))
       | Zpos b0 ->
         let Pair (g, p) = Coq_Pos.ggcd a0 b0 in
         let Pair (aa, bb) = p in
         Pair ((Zpos g), (Pair ((Zneg aa), (Zpos bb))))
       | Zneg b0 ->
         let Pair (g, p) = Coq_Pos.ggcd a0 b0 in
         let Pair (aa, bb) = p in
         Pair ((Zpos g), (Pair ((Zneg aa), (Zneg bb)))))
 end

(** val pow_pos : ('a1 -> 'a1 -> 'a1) -> 'a1 -> positive -> 'a1 **)

let rec pow_pos rmul x = function
| XI i0 -> let p = pow_pos rmul x i0 in rmul x (rmul p p)
| XO i0 -> let p = pow_pos rmul x i0 in rmul p p
| XH -> x

(** val z_lt_dec : z -> z -> sumbool **)

let z_lt_dec x y =
  match Z.compare x y with
  | Lt -> Left
  | _ -> Right

(** val z_lt_ge_dec : z -> z -> sumbool **)

let z_lt_ge_dec =
  z_lt_dec

(** val z_lt_le_dec : z -> z -> sumbool **)

let z_lt_le_dec =
  z_lt_ge_dec

type q = { qnum : z; qden : positive }

(** val qle_bool : q -> q -> bool **)

let qle_bool x y =
  Z.leb (Z.mul x.qnum (Zpos y.qden)) (Z.mul y.qnum (Zpos x.qden))

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

(** val qlt_le_dec : q -> q -> sumbool **)

let qlt_le_dec x y =
  z_lt_le_dec (Z.mul x.qnum (Zpos y.qden)) (Z.mul y.qnum (Zpos x.qden))

(** val qpower_positive : q -> positive -> q **)

let qpower_positive =
  pow_pos qmult

(** val qpower : q -> z -> q **)

let qpower q0 = function
| Z0 -> { qnum = (Zpos XH); qden = XH }
| Zpos p -> qpower_positive q0 p
| Zneg p -> qinv (qpower_positive q0 p)

(** val qred : q -> q **)

let qred q0 =
  let { qnum = q1; qden = q2 } = q0 in
  let Pair (r1, r2) = snd (Z.ggcd q1 (Zpos q2)) in
  { qnum = r1; qden = (Z.to_pos r2) }

(** val qabs : q -> q **)

let qabs x =
  let { qnum = n; qden = d } = x in { qnum = (Z.abs n); qden = d }

(** val qfloor : q -> z **)

let qfloor x =
  let { qnum = n; qden = d } = x in Z.div n (Zpos d)

(** val linear_search_conform : (nat -> sumbool) -> nat -> nat **)

let rec linear_search_conform p_dec start =
  match p_dec start with
  | Left -> start
  | Right -> linear_search_conform p_dec (S start)

(** val linear_search_from_0_conform : (nat -> sumbool) -> nat **)

let linear_search_from_0_conform p_dec =
  linear_search_conform p_dec O

(** val constructive_indefinite_ground_description_nat :
    (nat -> sumbool) -> nat **)

let constructive_indefinite_ground_description_nat =
  linear_search_from_0_conform

(** val p'_decidable : (nat -> 'a1) -> ('a1 -> sumbool) -> nat -> sumbool **)

let p'_decidable g p_decidable n =
  p_decidable (g n)

(** val constructive_indefinite_ground_description :
    ('a1 -> nat) -> (nat -> 'a1) -> ('a1 -> sumbool) -> 'a1 **)

let constructive_indefinite_ground_description _ g p_decidable =
  let h1 =
    constructive_indefinite_ground_description_nat
      (p'_decidable g p_decidable)
  in
  g h1

(** val pos_log2floor_plus1 : positive -> positive **)

let rec pos_log2floor_plus1 = function
| XI p' -> Coq_Pos.succ (pos_log2floor_plus1 p')
| XO p' -> Coq_Pos.succ (pos_log2floor_plus1 p')
| XH -> XH

(** val qbound_lt_ZExp2 : q -> z **)

let qbound_lt_ZExp2 q0 =
  match q0.qnum with
  | Z0 -> Zneg (XO (XO (XO (XI (XO (XI (XI (XI (XI XH)))))))))
  | Zpos p ->
    Z.pos_sub (Coq_Pos.succ (pos_log2floor_plus1 p))
      (pos_log2floor_plus1 q0.qden)
  | Zneg _ -> Z0

(** val qbound_ltabs_ZExp2 : q -> z **)

let qbound_ltabs_ZExp2 q0 =
  qbound_lt_ZExp2 (qabs q0)

(** val qarchimedeanExp2_Z : q -> z **)

let qarchimedeanExp2_Z =
  qbound_lt_ZExp2

(** val z_inj_nat : z -> nat **)

let z_inj_nat = function
| Z0 -> O
| Zpos p -> Coq_Pos.to_nat (XO p)
| Zneg p -> Coq_Pos.to_nat (Coq_Pos.pred_double p)

(** val z_inj_nat_rev : nat -> z **)

let z_inj_nat_rev n = match n with
| O -> Z0
| S _ ->
  (match Coq_Pos.of_nat n with
   | XI p -> Zneg (Coq_Pos.succ p)
   | XO p -> Zpos p
   | XH -> Zneg XH)

(** val constructive_indefinite_ground_description_Z : (z -> sumbool) -> z **)

let constructive_indefinite_ground_description_Z x =
  constructive_indefinite_ground_description z_inj_nat z_inj_nat_rev x

type cReal = { seq : (z -> q); scale : z }

type cRealLt = z

type cReal_appart = (cRealLt, cRealLt) sum

(** val cRealLtEpsilon : cReal -> cReal -> cRealLt **)

let cRealLtEpsilon x y =
  constructive_indefinite_ground_description_Z (fun n ->
    qlt_le_dec
      (qmult { qnum = (Zpos (XO XH)); qden = XH }
        (qpower { qnum = (Zpos (XO XH)); qden = XH } n))
      (qminus (y.seq n) (x.seq n)))

(** val cRealLt_above : cReal -> cReal -> cRealLt -> z **)

let cRealLt_above x y h =
  let s =
    qarchimedeanExp2_Z
      (qinv
        (qminus (qminus (y.seq h) (x.seq h))
          (qmult { qnum = (Zpos (XO XH)); qden = XH }
            (qpower { qnum = (Zpos (XO XH)); qden = XH } h))))
  in
  Z.min (Z.sub (Z.opp s) (Zpos XH)) h

(** val cRealLt_dec :
    cReal -> cReal -> cReal -> cRealLt -> (cRealLt, cRealLt) sum **)

let cRealLt_dec x y z0 h =
  let s =
    qarchimedeanExp2_Z
      (qinv
        (qminus (qminus (y.seq h) (x.seq h))
          (qmult { qnum = (Zpos (XO XH)); qden = XH }
            (qpower { qnum = (Zpos (XO XH)); qden = XH } h))))
  in
  let s0 =
    qlt_le_dec
      (qmult { qnum = (Zpos XH); qden = (XO XH) } (qplus (y.seq h) (x.seq h)))
      (z0.seq (Z.min h (Z.sub (Z.opp s) (Zpos (XO XH)))))
  in
  (match s0 with
   | Left -> Inl (Z.min h (Z.sub (Z.opp s) (Zpos (XO XH))))
   | Right -> Inr (Z.min h (Z.sub (Z.opp s) (Zpos (XO XH)))))

(** val linear_order_T :
    cReal -> cReal -> cReal -> cRealLt -> (cRealLt, cRealLt) sum **)

let linear_order_T x y z0 =
  cRealLt_dec x z0 y

(** val cReal_le_lt_trans : cReal -> cReal -> cReal -> cRealLt -> cRealLt **)

let cReal_le_lt_trans x y z0 hlt =
  let s = linear_order_T y x z0 hlt in
  (match s with
   | Inl _ -> assert false (* absurd case *)
   | Inr c -> c)

(** val cReal_lt_le_trans : cReal -> cReal -> cReal -> cRealLt -> cRealLt **)

let cReal_lt_le_trans x y z0 hlt =
  let s = linear_order_T x z0 y hlt in
  (match s with
   | Inl c -> c
   | Inr _ -> assert false (* absurd case *))

(** val cReal_lt_trans :
    cReal -> cReal -> cReal -> cRealLt -> cRealLt -> cRealLt **)

let cReal_lt_trans x y z0 hxlty _ =
  cReal_lt_le_trans x y z0 hxlty

(** val cRealLt_morph : cReal -> cReal -> cReal -> cReal -> (__, __) iffT **)

let cRealLt_morph x y x0 y0 =
  Pair ((fun hxltx0 ->
    let s = cRealLt_dec x x0 y (Obj.magic hxltx0) in
    (match s with
     | Inl _ -> assert false (* absurd case *)
     | Inr c ->
       let s0 = cRealLt_dec y x0 y0 c in
       (match s0 with
        | Inl c0 -> Obj.magic c0
        | Inr _ -> assert false (* absurd case *)))),
    (fun hylty0 ->
    let s = cRealLt_dec y y0 x (Obj.magic hylty0) in
    (match s with
     | Inl _ -> assert false (* absurd case *)
     | Inr c ->
       let s0 = cRealLt_dec x y0 x0 c in
       (match s0 with
        | Inl c0 -> Obj.magic c0
        | Inr _ -> assert false (* absurd case *)))))

(** val inject_Q : q -> cReal **)

let inject_Q q0 =
  { seq = (fun _ -> q0); scale = (qbound_ltabs_ZExp2 q0) }

(** val cRealLt_0_1 : cRealLt **)

let cRealLt_0_1 =
  Zneg (XO XH)

(** val cReal_plus_seq : cReal -> cReal -> z -> q **)

let cReal_plus_seq x y n =
  qred (qplus (x.seq (Z.sub n (Zpos XH))) (y.seq (Z.sub n (Zpos XH))))

(** val cReal_plus_scale : cReal -> cReal -> z **)

let cReal_plus_scale x y =
  Z.add (Z.max x.scale y.scale) (Zpos XH)

(** val cReal_plus : cReal -> cReal -> cReal **)

let cReal_plus x y =
  { seq = (cReal_plus_seq x y); scale = (cReal_plus_scale x y) }

(** val cReal_opp_seq : cReal -> z -> q **)

let cReal_opp_seq x n =
  qopp (x.seq n)

(** val cReal_opp_scale : cReal -> z **)

let cReal_opp_scale x =
  x.scale

(** val cReal_opp : cReal -> cReal **)

let cReal_opp x =
  { seq = (cReal_opp_seq x); scale = (cReal_opp_scale x) }

(** val cReal_plus_lt_compat_l :
    cReal -> cReal -> cReal -> cRealLt -> cRealLt **)

let cReal_plus_lt_compat_l _ =
  cRealLt_above

(** val cReal_plus_lt_reg_l :
    cReal -> cReal -> cReal -> cRealLt -> cRealLt **)

let cReal_plus_lt_reg_l _ _ _ hlt =
  Z.sub hlt (Zpos XH)

(** val cReal_plus_lt_reg_r :
    cReal -> cReal -> cReal -> cRealLt -> cRealLt **)

let cReal_plus_lt_reg_r x y z0 hlt =
  let hlt0 =
    subrelation_proper (Obj.magic __) (fun x0 x1 _ x2 x3 _ ->
      cRealLt_morph x0 x1 x2 x3) Tt
      (subrelation_respectful (Obj.magic __)
        (subrelation_respectful (Obj.magic __)
          (Obj.magic (fun _ _ -> iffT_arrow_subrelation))))
      (cReal_plus y x) (cReal_plus x y) __ (cReal_plus z0 x)
      (cReal_plus z0 x) __ hlt
  in
  let hlt1 =
    reflexive_partial_app_morphism (Obj.magic __)
      (subrelation_proper (Obj.magic __) (fun x0 x1 _ x2 x3 _ ->
        cRealLt_morph x0 x1 x2 x3) Tt
        (subrelation_respectful (Obj.magic __)
          (subrelation_respectful (Obj.magic __) (fun _ _ ->
            iffT_arrow_subrelation))))
      (cReal_plus x y) __ (cReal_plus z0 x) (cReal_plus x z0) __ hlt0
  in
  cReal_plus_lt_reg_l x y z0 (Obj.magic hlt1)

(** val inject_Q_lt : q -> q -> cRealLt **)

let inject_Q_lt q0 r =
  let s = qarchimedeanExp2_Z (qinv (qminus r q0)) in Z.sub (Z.opp s) (Zpos XH)

(** val cReal_mult_seq : cReal -> cReal -> z -> q **)

let cReal_mult_seq x y n =
  qmult (x.seq (Z.sub (Z.sub n y.scale) (Zpos XH)))
    (y.seq (Z.sub (Z.sub n x.scale) (Zpos XH)))

(** val cReal_mult_scale : cReal -> cReal -> z **)

let cReal_mult_scale x y =
  Z.add x.scale y.scale

(** val cReal_mult : cReal -> cReal -> cReal **)

let cReal_mult x y =
  { seq = (cReal_mult_seq x y); scale = (cReal_mult_scale x y) }

(** val cReal_mult_lt_0_compat :
    cReal -> cReal -> cRealLt -> cRealLt -> cRealLt **)

let cReal_mult_lt_0_compat _ _ hx hy =
  Z.sub (Z.add hx hy) (Zpos XH)

(** val cRealArchimedean : cReal -> (z, (cRealLt, cRealLt) prod) sigT **)

let cRealArchimedean x =
  let q0 =
    qplus (x.seq (Zneg (XI XH))) { qnum = (Zpos (XI XH)); qden = (XO XH) }
  in
  ExistT ((qfloor q0), (Pair ((Zneg (XI XH)), (Zneg (XI XH)))))

(** val cRealLowerBound : cReal -> cRealLt -> z **)

let cRealLowerBound _ xPos =
  xPos

(** val cReal_inv_pos_cm : cReal -> cRealLt -> z -> z **)

let cReal_inv_pos_cm x xPos n =
  Z.min (cRealLowerBound x xPos)
    (Z.add n (Z.mul (Zpos (XO XH)) (cRealLowerBound x xPos)))

(** val cReal_inv_pos_seq : cReal -> cRealLt -> z -> q **)

let cReal_inv_pos_seq x xPos n =
  qinv (x.seq (cReal_inv_pos_cm x xPos n))

(** val cReal_inv_pos_scale : cReal -> cRealLt -> z **)

let cReal_inv_pos_scale x xPos =
  Z.opp (cRealLowerBound x xPos)

(** val cReal_inv_pos : cReal -> cRealLt -> cReal **)

let cReal_inv_pos x hxpos =
  { seq = (cReal_inv_pos_seq x hxpos); scale = (cReal_inv_pos_scale x hxpos) }

(** val cReal_neg_lt_pos : cReal -> cRealLt -> cRealLt **)

let cReal_neg_lt_pos _ h =
  h

(** val cReal_inv : cReal -> cReal_appart -> cReal **)

let cReal_inv x = function
| Inl xNeg ->
  cReal_opp (cReal_inv_pos (cReal_opp x) (cReal_neg_lt_pos x xNeg))
| Inr xPos -> cReal_inv_pos x xPos

(** val cReal_inv_0_lt_compat :
    cReal -> cReal_appart -> cRealLt -> cRealLt **)

let cReal_inv_0_lt_compat r hrnz _ =
  match hrnz with
  | Inl _ -> assert false (* absurd case *)
  | Inr _ -> Z.sub (Z.opp r.scale) (Zpos XH)

(** val cRealQ_dense :
    cReal -> cReal -> cRealLt -> (q, (cRealLt, cRealLt) prod) sigT **)

let cRealQ_dense a b h =
  ExistT
    ((qmult (qplus (a.seq h) (b.seq h)) { qnum = (Zpos XH); qden = (XO XH) }),
    (Pair
    ((cReal_le_lt_trans a
       (inject_Q
         (qplus (a.seq h) (qpower { qnum = (Zpos (XO XH)); qden = XH } h)))
       (inject_Q
         (qmult (qplus (a.seq h) (b.seq h)) { qnum = (Zpos XH); qden = (XO
           XH) }))
       (inject_Q_lt
         (qplus (a.seq h) (qpower { qnum = (Zpos (XO XH)); qden = XH } h))
         (qmult (qplus (a.seq h) (b.seq h)) { qnum = (Zpos XH); qden = (XO
           XH) }))),
    (cReal_plus_lt_reg_l (cReal_opp b)
      (inject_Q
        (qmult (qplus (a.seq h) (b.seq h)) { qnum = (Zpos XH); qden = (XO
          XH) }))
      b
      (reflexive_partial_app_morphism (Obj.magic __)
        (subrelation_proper (Obj.magic __) (fun x x0 _ x1 x2 _ ->
          cRealLt_morph x x0 x1 x2) Tt
          (subrelation_respectful (Obj.magic __)
            (subrelation_respectful (Obj.magic __)
              (Obj.magic (fun _ _ -> iffT_flip_arrow_subrelation)))))
        (cReal_plus (cReal_opp b)
          (inject_Q
            (qmult (qplus (a.seq h) (b.seq h)) { qnum = (Zpos XH); qden = (XO
              XH) })))
        __ (cReal_plus (cReal_opp b) b) (inject_Q { qnum = Z0; qden = XH })
        __
        (cReal_plus_lt_reg_r
          (cReal_opp
            (inject_Q
              (qmult (qplus (a.seq h) (b.seq h)) { qnum = (Zpos XH); qden =
                (XO XH) })))
          (cReal_plus (cReal_opp b)
            (inject_Q
              (qmult (qplus (a.seq h) (b.seq h)) { qnum = (Zpos XH); qden =
                (XO XH) })))
          (inject_Q { qnum = Z0; qden = XH })
          (subrelation_proper (Obj.magic __) (fun x x0 _ x1 x2 _ ->
            cRealLt_morph x x0 x1 x2) Tt
            (subrelation_respectful (Obj.magic __)
              (subrelation_respectful (Obj.magic __)
                (Obj.magic (fun _ _ -> iffT_flip_arrow_subrelation))))
            (cReal_plus
              (cReal_plus (cReal_opp b)
                (inject_Q
                  (qmult (qplus (a.seq h) (b.seq h)) { qnum = (Zpos XH);
                    qden = (XO XH) })))
              (cReal_opp
                (inject_Q
                  (qmult (qplus (a.seq h) (b.seq h)) { qnum = (Zpos XH);
                    qden = (XO XH) }))))
            (cReal_plus (cReal_opp b)
              (cReal_plus
                (inject_Q
                  (qmult (qplus (a.seq h) (b.seq h)) { qnum = (Zpos XH);
                    qden = (XO XH) }))
                (cReal_opp
                  (inject_Q
                    (qmult (qplus (a.seq h) (b.seq h)) { qnum = (Zpos XH);
                      qden = (XO XH) })))))
            __
            (cReal_plus (inject_Q { qnum = Z0; qden = XH })
              (cReal_opp
                (inject_Q
                  (qmult (qplus (a.seq h) (b.seq h)) { qnum = (Zpos XH);
                    qden = (XO XH) }))))
            (cReal_plus (inject_Q { qnum = Z0; qden = XH })
              (cReal_opp
                (inject_Q
                  (qmult (qplus (a.seq h) (b.seq h)) { qnum = (Zpos XH);
                    qden = (XO XH) }))))
            __
            (subrelation_proper (Obj.magic __) (fun x x0 _ x1 x2 _ ->
              cRealLt_morph x x0 x1 x2) Tt
              (subrelation_respectful (Obj.magic __)
                (subrelation_respectful (Obj.magic __) (fun _ _ ->
                  iffT_flip_arrow_subrelation)))
              (cReal_plus (cReal_opp b)
                (cReal_plus
                  (inject_Q
                    (qmult (qplus (a.seq h) (b.seq h)) { qnum = (Zpos XH);
                      qden = (XO XH) }))
                  (cReal_opp
                    (inject_Q
                      (qmult (qplus (a.seq h) (b.seq h)) { qnum = (Zpos XH);
                        qden = (XO XH) })))))
              (cReal_plus (cReal_opp b) (inject_Q { qnum = Z0; qden = XH }))
              __
              (cReal_plus (inject_Q { qnum = Z0; qden = XH })
                (cReal_opp
                  (inject_Q
                    (qmult (qplus (a.seq h) (b.seq h)) { qnum = (Zpos XH);
                      qden = (XO XH) }))))
              (cReal_plus (inject_Q { qnum = Z0; qden = XH })
                (cReal_opp
                  (inject_Q
                    (qmult (qplus (a.seq h) (b.seq h)) { qnum = (Zpos XH);
                      qden = (XO XH) }))))
              __
              (subrelation_proper (Obj.magic __) (fun x x0 _ x1 x2 _ ->
                cRealLt_morph x x0 x1 x2) Tt
                (subrelation_respectful (Obj.magic __)
                  (subrelation_respectful (Obj.magic __) (fun _ _ ->
                    iffT_flip_arrow_subrelation)))
                (cReal_plus (cReal_opp b) (inject_Q { qnum = Z0; qden = XH }))
                (cReal_opp b) __
                (cReal_plus (inject_Q { qnum = Z0; qden = XH })
                  (cReal_opp
                    (inject_Q
                      (qmult (qplus (a.seq h) (b.seq h)) { qnum = (Zpos XH);
                        qden = (XO XH) }))))
                (cReal_plus (inject_Q { qnum = Z0; qden = XH })
                  (cReal_opp
                    (inject_Q
                      (qmult (qplus (a.seq h) (b.seq h)) { qnum = (Zpos XH);
                        qden = (XO XH) }))))
                __
                (reflexive_partial_app_morphism (Obj.magic __)
                  (subrelation_proper (Obj.magic __) (fun x x0 _ x1 x2 _ ->
                    cRealLt_morph x x0 x1 x2) Tt
                    (subrelation_respectful (Obj.magic __)
                      (subrelation_respectful (Obj.magic __) (fun _ _ ->
                        iffT_flip_arrow_subrelation))))
                  (cReal_opp b) __
                  (cReal_plus (inject_Q { qnum = Z0; qden = XH })
                    (cReal_opp
                      (inject_Q
                        (qmult (qplus (a.seq h) (b.seq h)) { qnum = (Zpos
                          XH); qden = (XO XH) }))))
                  (cReal_opp
                    (inject_Q
                      (qmult (qplus (a.seq h) (b.seq h)) { qnum = (Zpos XH);
                        qden = (XO XH) })))
                  __
                  (reflexive_partial_app_morphism (Obj.magic __)
                    (subrelation_proper (Obj.magic __) (fun x x0 _ x1 x2 _ ->
                      cRealLt_morph x x0 x1 x2) Tt
                      (subrelation_respectful (Obj.magic __)
                        (subrelation_respectful (Obj.magic __)
                          (Obj.magic (fun _ _ -> iffT_flip_arrow_subrelation)))))
                    (cReal_opp b) __
                    (cReal_opp
                      (inject_Q
                        (qmult (qplus (a.seq h) (b.seq h)) { qnum = (Zpos
                          XH); qden = (XO XH) })))
                    (inject_Q
                      (qopp
                        (qmult (qplus (a.seq h) (b.seq h)) { qnum = (Zpos
                          XH); qden = (XO XH) })))
                    __
                    (cReal_le_lt_trans (cReal_opp b)
                      (inject_Q
                        (qplus ((cReal_opp b).seq h)
                          (qpower { qnum = (Zpos (XO XH)); qden = XH } h)))
                      (inject_Q
                        (qopp
                          (qmult (qplus (a.seq h) (b.seq h)) { qnum = (Zpos
                            XH); qden = (XO XH) })))
                      (inject_Q_lt
                        (qplus ((cReal_opp b).seq h)
                          (qpower { qnum = (Zpos (XO XH)); qden = XH } h))
                        (qopp
                          (qmult (qplus (a.seq h) (b.seq h)) { qnum = (Zpos
                            XH); qden = (XO XH) })))))))))))))))

type ('x, 'xlt) isLinearOrder =
  ((__, 'x -> 'x -> 'x -> 'xlt -> 'xlt -> 'xlt) prod, 'x -> 'x -> 'x -> 'xlt
  -> ('xlt, 'xlt) sum) prod

type constructiveReals = { cRltLinear : (__, __) isLinearOrder;
                           cRltEpsilon : (__ -> __ -> __ -> __);
                           cRltDisjunctEpsilon : (__ -> __ -> __ -> __ -> __
                                                 -> (__, __) sum);
                           cR_of_Q : (q -> __);
                           cR_of_Q_lt : (q -> q -> __ -> __);
                           cRplus : (__ -> __ -> __); cRopp : (__ -> __);
                           cRmult : (__ -> __ -> __); cRzero_lt_one : 
                           __;
                           cRplus_lt_compat_l : (__ -> __ -> __ -> __ -> __);
                           cRplus_lt_reg_l : (__ -> __ -> __ -> __ -> __);
                           cRmult_lt_0_compat : (__ -> __ -> __ -> __ -> __);
                           cRinv : (__ -> (__, __) sum -> __);
                           cRinv_0_lt_compat : (__ -> (__, __) sum -> __ ->
                                               __);
                           cR_Q_dense : (__ -> __ -> __ -> (q, (__, __) prod)
                                        sigT);
                           cR_archimedean : (__ -> (positive, __) sigT);
                           cRabs : (__ -> __);
                           cR_complete : ((nat -> __) -> (positive -> nat) ->
                                         (__, positive -> nat) sigT) }

type cRcarrier = __

(** val cReal_abs_seq : cReal -> z -> q **)

let cReal_abs_seq x n =
  qabs (x.seq n)

(** val cReal_abs_scale : cReal -> z **)

let cReal_abs_scale x =
  x.scale

(** val cReal_abs : cReal -> cReal **)

let cReal_abs x =
  { seq = (cReal_abs_seq x); scale = (cReal_abs_scale x) }

type seq_cv = positive -> nat

type un_cauchy_mod = positive -> nat

(** val cReal_from_cauchy_cm : z -> positive **)

let cReal_from_cauchy_cm = function
| Zneg p -> p
| _ -> XH

(** val cReal_from_cauchy_seq : (nat -> cReal) -> un_cauchy_mod -> z -> q **)

let cReal_from_cauchy_seq xn xcau n =
  let p = cReal_from_cauchy_cm n in
  (xn (xcau (Coq_Pos.mul (XO (XO XH)) (Coq_Pos.pow (XO XH) p)))).seq
    (Z.sub (Zneg p) (Zpos (XO XH)))

(** val rup_pos : cReal -> (positive, cRealLt) sigT **)

let rup_pos x =
  let s = cRealArchimedean x in
  let ExistT (x0, p) = s in
  let Pair (c, _) = p in
  (match x0 with
   | Z0 ->
     ExistT (XH,
       (cReal_lt_trans x (inject_Q { qnum = Z0; qden = XH })
         (inject_Q { qnum = (Zpos XH); qden = XH }) c cRealLt_0_1))
   | Zpos p0 -> ExistT (p0, c)
   | Zneg p0 ->
     ExistT (XH,
       (cReal_lt_trans x (inject_Q { qnum = (Zneg p0); qden = XH })
         (inject_Q { qnum = (Zpos XH); qden = XH }) c
         (cReal_lt_trans (inject_Q { qnum = (Zneg p0); qden = XH })
           (inject_Q { qnum = Z0; qden = XH })
           (inject_Q { qnum = (Zpos XH); qden = XH })
           (inject_Q_lt { qnum = (Zneg p0); qden = XH } { qnum = Z0; qden =
             XH })
           cRealLt_0_1))))

(** val cReal_from_cauchy_scale : (nat -> cReal) -> un_cauchy_mod -> z **)

let cReal_from_cauchy_scale xn xcau =
  qbound_lt_ZExp2
    (qplus (qabs (cReal_from_cauchy_seq xn xcau (Zneg XH))) { qnum = (Zpos
      (XO XH)); qden = XH })

(** val cReal_from_cauchy : (nat -> cReal) -> un_cauchy_mod -> cReal **)

let cReal_from_cauchy xn xcau =
  { seq = (cReal_from_cauchy_seq xn xcau); scale =
    (cReal_from_cauchy_scale xn xcau) }

(** val rcauchy_complete :
    (nat -> cReal) -> un_cauchy_mod -> (cReal, seq_cv) sigT **)

let rcauchy_complete xn cau =
  ExistT ((cReal_from_cauchy xn cau), (fun p ->
    let h0 = cau (Coq_Pos.mul (XO XH) p) in
    let i' = cReal_from_cauchy_cm (Z.sub (Zneg p) (Zpos XH)) in
    let s = cau (Coq_Pos.mul (XO (XO XH)) (Coq_Pos.pow (XO XH) i')) in
    max h0 s))

(** val cRealLtIsLinear : (cReal, cRealLt) isLinearOrder **)

let cRealLtIsLinear =
  Pair ((Pair (__, cReal_lt_trans)), (fun x y z0 x0 -> cRealLt_dec x z0 y x0))

(** val cRealComplete :
    (nat -> cReal) -> (positive -> nat) -> (cReal, positive -> nat) sigT **)

let cRealComplete =
  rcauchy_complete

(** val cRealLtDisjunctEpsilon :
    cReal -> cReal -> cReal -> cReal -> (cRealLt, cRealLt) sum **)

let cRealLtDisjunctEpsilon a b c d =
  let h0 =
    constructive_indefinite_ground_description_Z (fun n ->
      let s =
        qlt_le_dec
          (qmult { qnum = (Zpos (XO XH)); qden = XH }
            (qpower { qnum = (Zpos (XO XH)); qden = XH } n))
          (qminus (b.seq n) (a.seq n))
      in
      (match s with
       | Left -> Left
       | Right ->
         qlt_le_dec
           (qmult { qnum = (Zpos (XO XH)); qden = XH }
             (qpower { qnum = (Zpos (XO XH)); qden = XH } n))
           (qminus (d.seq n) (c.seq n))))
  in
  let s =
    qlt_le_dec
      (qmult { qnum = (Zpos (XO XH)); qden = XH }
        (qpower { qnum = (Zpos (XO XH)); qden = XH } h0))
      (qminus (b.seq h0) (a.seq h0))
  in
  (match s with
   | Left -> Inl h0
   | Right -> Inr h0)

(** val cRealConstructive : constructiveReals **)

let cRealConstructive =
  { cRltLinear = (Obj.magic cRealLtIsLinear); cRltEpsilon =
    (Obj.magic (fun x x0 _ -> cRealLtEpsilon x x0)); cRltDisjunctEpsilon =
    (Obj.magic (fun x x0 x1 x2 _ -> cRealLtDisjunctEpsilon x x0 x1 x2));
    cR_of_Q = (Obj.magic inject_Q); cR_of_Q_lt =
    (Obj.magic (fun x x0 _ -> inject_Q_lt x x0)); cRplus =
    (Obj.magic cReal_plus); cRopp = (Obj.magic cReal_opp); cRmult =
    (Obj.magic cReal_mult); cRzero_lt_one = (Obj.magic cRealLt_0_1);
    cRplus_lt_compat_l = (Obj.magic cReal_plus_lt_compat_l);
    cRplus_lt_reg_l = (Obj.magic cReal_plus_lt_reg_l); cRmult_lt_0_compat =
    (Obj.magic cReal_mult_lt_0_compat); cRinv = (Obj.magic cReal_inv);
    cRinv_0_lt_compat = (Obj.magic cReal_inv_0_lt_compat); cR_Q_dense =
    (Obj.magic cRealQ_dense); cR_archimedean = (Obj.magic rup_pos); cRabs =
    (Obj.magic cReal_abs); cR_complete = (Obj.magic cRealComplete) }

type cRComplex = { cre : cRcarrier; cim : cRcarrier }

(** val cRnorm_sq : constructiveReals -> cRComplex -> cRcarrier **)

let cRnorm_sq r z0 =
  r.cRplus (r.cRmult z0.cre z0.cre) (r.cRmult z0.cim z0.cim)

(** val cRzero : constructiveReals -> cRComplex **)

let cRzero r =
  { cre = (r.cR_of_Q { qnum = Z0; qden = XH }); cim =
    (r.cR_of_Q { qnum = Z0; qden = XH }) }

(** val cRcombo :
    constructiveReals -> nat -> (nat -> cRcarrier) -> (nat -> cRComplex) ->
    cRComplex **)

let rec cRcombo r m c u =
  match m with
  | O ->
    { cre = (r.cRmult (c O) (u O).cre); cim = (r.cRmult (c O) (u O).cim) }
  | S m' ->
    { cre =
      (r.cRplus (cRcombo r m' c u).cre (r.cRmult (c (S m')) (u (S m')).cre));
      cim =
      (r.cRplus (cRcombo r m' c u).cim (r.cRmult (c (S m')) (u (S m')).cim)) }

(** val c4g_pfb4 : nat -> nat -> q **)

let c4g_pfb4 i j =
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

(** val c4g_col4 : nat -> q **)

let c4g_col4 j =
  qplus
    (qplus (qplus (c4g_pfb4 O j) (c4g_pfb4 (S O) j)) (c4g_pfb4 (S (S O)) j))
    (c4g_pfb4 (S (S (S O))) j)

(** val c4g_rho4 : q **)

let c4g_rho4 =
  c4g_col4 (S (S O))

(** val lam4 : q **)

let lam4 =
  qminus { qnum = (Zpos XH); qden = XH } c4g_rho4

(** val c4g_rho4_window : (z, positive) prod **)

let c4g_rho4_window =
  Pair (c4g_rho4.qnum, c4g_rho4.qden)

(** val c4g_lam4_window : (z, positive) prod **)

let c4g_lam4_window =
  Pair (lam4.qnum, lam4.qden)

(** val c4g_pfb4_table : nat -> nat -> q **)

let c4g_pfb4_table =
  c4g_pfb4

(** val c4g_col_window : nat -> (z, positive) prod **)

let c4g_col_window j =
  Pair ((c4g_col4 j).qnum, (c4g_col4 j).qden)

(** val c4g_col_ok : nat -> bool **)

let c4g_col_ok j =
  qle_bool (c4g_col4 j) c4g_rho4

(** val c4g_rho_ok : bool **)

let c4g_rho_ok =
  negb (qle_bool { qnum = (Zpos XH); qden = XH } c4g_rho4)

(** val c4g_lam_ok : bool **)

let c4g_lam_ok =
  negb (qle_bool lam4 { qnum = Z0; qden = XH })

(** val c4g_window_ok : bool **)

let c4g_window_ok =
  match c4g_rho_ok with
  | True ->
    (match c4g_lam_ok with
     | True ->
       (match c4g_col_ok O with
        | True ->
          (match c4g_col_ok (S O) with
           | True ->
             (match c4g_col_ok (S (S O)) with
              | True -> c4g_col_ok (S (S (S O)))
              | False -> False)
           | False -> False)
        | False -> False)
     | False -> False)
  | False -> False

(** val c4g_ladder_zero : nat -> cRComplex **)

let c4g_ladder_zero _ =
  cRzero cRealConstructive

(** val c4g_lam_cauchy : cRcarrier **)

let c4g_lam_cauchy =
  cRealConstructive.cR_of_Q lam4

(** val c4g_combo_cauchy : (nat -> cRcarrier) -> cRComplex **)

let c4g_combo_cauchy c =
  cRcombo cRealConstructive (S (S (S O))) c c4g_ladder_zero

(** val c4g_norm_sq_cauchy : (nat -> cRcarrier) -> cRcarrier **)

let c4g_norm_sq_cauchy c =
  cRnorm_sq cRealConstructive (c4g_combo_cauchy c)
