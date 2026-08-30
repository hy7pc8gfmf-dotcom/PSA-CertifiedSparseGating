
type __ = Obj.t

type nat =
| O
| S of nat

type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b

type ('a, 'b) prod =
| Pair of 'a * 'b

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

type ('a, 'p) sigT =
| ExistT of 'a * 'p

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

type q = { qnum : z; qden : positive }

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

val cRsum : constructiveReals -> (nat -> cRcarrier) -> nat -> cRcarrier

val g7S :
  constructiveReals -> nat -> (nat -> nat -> cRcarrier) -> nat -> nat ->
  cRcarrier

val g7G :
  constructiveReals -> nat -> (nat -> nat -> cRcarrier) -> nat -> nat ->
  cRcarrier

val g7_welch_lower : __
