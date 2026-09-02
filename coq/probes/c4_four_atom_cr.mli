
type __ = Obj.t

type unit0 =
| Tt

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

val snd : ('a1, 'a2) prod -> 'a2

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

type ('a, 'p) sigT =
| ExistT of 'a * 'p

type sumbool =
| Left
| Right

type uint =
| Nil
| D0 of uint
| D1 of uint
| D2 of uint
| D3 of uint
| D4 of uint
| D5 of uint
| D6 of uint
| D7 of uint
| D8 of uint
| D9 of uint

type uint0 =
| Nil0
| D10 of uint0
| D11 of uint0
| D12 of uint0
| D13 of uint0
| D14 of uint0
| D15 of uint0
| D16 of uint0
| D17 of uint0
| D18 of uint0
| D19 of uint0
| Da of uint0
| Db of uint0
| Dc of uint0
| Dd of uint0
| De of uint0
| Df of uint0

type uint1 =
| UIntDecimal of uint
| UIntHexadecimal of uint0

val add : nat -> nat -> nat

val max : nat -> nat -> nat

val tail_add : nat -> nat -> nat

val tail_addmul : nat -> nat -> nat -> nat

val tail_mul : nat -> nat -> nat

val of_uint_acc : uint -> nat -> nat

val of_uint : uint -> nat

val of_hex_uint_acc : uint0 -> nat -> nat

val of_hex_uint : uint0 -> nat

val of_num_uint : uint1 -> nat

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

type 'a unconvertible = unit0

type 'a crelation = __

type ('a, 'b) arrow = 'a -> 'b

type ('a, 'b) iffT = ('a -> 'b, 'b -> 'a) prod

type ('a, 'r, 'x) subrelation = 'a -> 'a -> 'r -> 'x

type ('a, 'r) proper = 'r

type ('a, 'r) properProxy = 'r

type ('a, 'b, 'r, 'x) respectful = 'a -> 'a -> 'r -> 'x

val subrelation_respectful :
  ('a1, 'a2, 'a3) subrelation -> ('a4, 'a5, 'a6) subrelation -> ('a1 -> 'a4,
  ('a1, 'a4, 'a3, 'a5) respectful, ('a1, 'a4, 'a2, 'a6) respectful)
  subrelation

val subrelation_proper :
  'a1 -> ('a1, 'a2) proper -> 'a1 crelation unconvertible -> ('a1, 'a2, 'a3)
  subrelation -> ('a1, 'a3) proper

val iffT_arrow_subrelation : (__, __) iffT -> (__, __) arrow

val iffT_flip_arrow_subrelation : (__, __) iffT -> (__, __) arrow

val reflexive_partial_app_morphism :
  ('a1 -> 'a2) -> ('a1 -> 'a2, ('a1, 'a2, 'a3, 'a4) respectful) proper -> 'a1
  -> ('a1, 'a3) properProxy -> ('a2, 'a4) proper

module Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  val mul : positive -> positive -> positive

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison
 end

module Coq_Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  val succ_double_mask : mask -> mask

  val double_mask : mask -> mask

  val double_pred_mask : positive -> mask

  val sub_mask : positive -> positive -> mask

  val sub_mask_carry : positive -> positive -> mask

  val sub : positive -> positive -> positive

  val mul : positive -> positive -> positive

  val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1

  val to_nat : positive -> nat

  val of_succ_nat : nat -> positive

  val pow : positive -> positive -> positive

  val size_nat : positive -> nat

  val ggcdn :
    nat -> positive -> positive -> (positive, (positive, positive) prod) prod

  val ggcd :
    positive -> positive -> (positive, (positive, positive) prod) prod

  val of_nat : nat -> positive
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

  val max : z -> z -> z

  val min : z -> z -> z

  val to_pos : z -> positive

  val pos_div_eucl : positive -> z -> (z, z) prod

  val div_eucl : z -> z -> (z, z) prod

  val div : z -> z -> z

  val sgn : z -> z

  val abs : z -> z

  val ggcd : z -> z -> (z, (z, z) prod) prod
 end

val pow_pos : ('a1 -> 'a1 -> 'a1) -> 'a1 -> positive -> 'a1

val z_lt_dec : z -> z -> sumbool

val z_lt_ge_dec : z -> z -> sumbool

val z_lt_le_dec : z -> z -> sumbool

type q = { qnum : z; qden : positive }

val qplus : q -> q -> q

val qmult : q -> q -> q

val qopp : q -> q

val qminus : q -> q -> q

val qinv : q -> q

val qlt_le_dec : q -> q -> sumbool

val qpower_positive : q -> positive -> q

val qpower : q -> z -> q

val qred : q -> q

val qabs : q -> q

val qfloor : q -> z

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

type cRComplex = { cre : cRcarrier; cim : cRcarrier }

val cRnorm_sq : constructiveReals -> cRComplex -> cRcarrier

val cRzero : constructiveReals -> cRComplex

val cRcombo :
  constructiveReals -> nat -> (nat -> cRcarrier) -> (nat -> cRComplex) ->
  cRComplex

val linear_search_conform : (nat -> sumbool) -> nat -> nat

val linear_search_from_0_conform : (nat -> sumbool) -> nat

val constructive_indefinite_ground_description_nat : (nat -> sumbool) -> nat

val p'_decidable : (nat -> 'a1) -> ('a1 -> sumbool) -> nat -> sumbool

val constructive_indefinite_ground_description :
  ('a1 -> nat) -> (nat -> 'a1) -> ('a1 -> sumbool) -> 'a1

val pos_log2floor_plus1 : positive -> positive

val qbound_lt_ZExp2 : q -> z

val qbound_ltabs_ZExp2 : q -> z

val qarchimedeanExp2_Z : q -> z

val z_inj_nat : z -> nat

val z_inj_nat_rev : nat -> z

val constructive_indefinite_ground_description_Z : (z -> sumbool) -> z

type cReal = { seq : (z -> q); scale : z }

type cRealLt = z

type cReal_appart = (cRealLt, cRealLt) sum

val cRealLtEpsilon : cReal -> cReal -> cRealLt

val cRealLt_above : cReal -> cReal -> cRealLt -> z

val cRealLt_dec : cReal -> cReal -> cReal -> cRealLt -> (cRealLt, cRealLt) sum

val linear_order_T :
  cReal -> cReal -> cReal -> cRealLt -> (cRealLt, cRealLt) sum

val cReal_le_lt_trans : cReal -> cReal -> cReal -> cRealLt -> cRealLt

val cReal_lt_le_trans : cReal -> cReal -> cReal -> cRealLt -> cRealLt

val cReal_lt_trans : cReal -> cReal -> cReal -> cRealLt -> cRealLt -> cRealLt

val cRealLt_morph : cReal -> cReal -> cReal -> cReal -> (__, __) iffT

val inject_Q : q -> cReal

val cRealLt_0_1 : cRealLt

val cReal_plus_seq : cReal -> cReal -> z -> q

val cReal_plus_scale : cReal -> cReal -> z

val cReal_plus : cReal -> cReal -> cReal

val cReal_opp_seq : cReal -> z -> q

val cReal_opp_scale : cReal -> z

val cReal_opp : cReal -> cReal

val cReal_plus_lt_compat_l : cReal -> cReal -> cReal -> cRealLt -> cRealLt

val cReal_plus_lt_reg_l : cReal -> cReal -> cReal -> cRealLt -> cRealLt

val cReal_plus_lt_reg_r : cReal -> cReal -> cReal -> cRealLt -> cRealLt

val inject_Q_lt : q -> q -> cRealLt

val cReal_mult_seq : cReal -> cReal -> z -> q

val cReal_mult_scale : cReal -> cReal -> z

val cReal_mult : cReal -> cReal -> cReal

val cReal_mult_lt_0_compat : cReal -> cReal -> cRealLt -> cRealLt -> cRealLt

val cRealArchimedean : cReal -> (z, (cRealLt, cRealLt) prod) sigT

val cRealLowerBound : cReal -> cRealLt -> z

val cReal_inv_pos_cm : cReal -> cRealLt -> z -> z

val cReal_inv_pos_seq : cReal -> cRealLt -> z -> q

val cReal_inv_pos_scale : cReal -> cRealLt -> z

val cReal_inv_pos : cReal -> cRealLt -> cReal

val cReal_neg_lt_pos : cReal -> cRealLt -> cRealLt

val cReal_inv : cReal -> cReal_appart -> cReal

val cReal_inv_0_lt_compat : cReal -> cReal_appart -> cRealLt -> cRealLt

val cRealQ_dense :
  cReal -> cReal -> cRealLt -> (q, (cRealLt, cRealLt) prod) sigT

val cReal_abs_seq : cReal -> z -> q

val cReal_abs_scale : cReal -> z

val cReal_abs : cReal -> cReal

type seq_cv = positive -> nat

type un_cauchy_mod = positive -> nat

val cReal_from_cauchy_cm : z -> positive

val cReal_from_cauchy_seq : (nat -> cReal) -> un_cauchy_mod -> z -> q

val rup_pos : cReal -> (positive, cRealLt) sigT

val cReal_from_cauchy_scale : (nat -> cReal) -> un_cauchy_mod -> z

val cReal_from_cauchy : (nat -> cReal) -> un_cauchy_mod -> cReal

val rcauchy_complete : (nat -> cReal) -> un_cauchy_mod -> (cReal, seq_cv) sigT

val cRealLtIsLinear : (cReal, cRealLt) isLinearOrder

val cRealComplete :
  (nat -> cReal) -> (positive -> nat) -> (cReal, positive -> nat) sigT

val cRealLtDisjunctEpsilon :
  cReal -> cReal -> cReal -> cReal -> (cRealLt, cRealLt) sum

val cRealConstructive : constructiveReals

val mu_c4 : q

val c4_ladder_zero : nat -> cRComplex

val c4_mu_cauchy : q -> cRcarrier

val c4_combo_cauchy : (nat -> cRcarrier) -> cRComplex

val c4_norm_sq_cauchy : (nat -> cRcarrier) -> cRcarrier

val c4_mu4_window : (z, positive) prod
