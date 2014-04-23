Require Import Orders OrdersTac.
Set Implicit Arguments.

Module Type Coherence.
  Parameter t : Type.
  Parameter eq : t -> t -> Prop.
  Parameter eq_equiv : Equivalence eq.
  Parameter lt : t -> t -> Prop.
  Parameter lt_strorder : StrictOrder lt.
  Parameter lt_compat : Proper (eq ==> eq ==> iff) lt.
  Parameter le : t -> t -> Prop.
  Parameter le_lteq : forall x y : t, le x y <-> lt x y \/ eq x y.
  Parameter lt_total : forall x y : t, lt x y \/ eq x y \/ lt y x.

  Parameter Mo Sh In: t.
  Parameter ub_Mo: forall x, lt Mo x -> False.
  Parameter lb_In: forall x, lt x In -> False.

  Parameter compatible: t -> t -> Prop.

  Parameter compatible_prop: forall x1 x2 y1 y2, compatible x1 y1 ->
                                                 le x2 x1 -> le y2 y1 ->
                                                 compatible x2 y2.

  Parameter ne_In_Sh: ~ eq In Sh.
  Parameter ne_In_Mo: ~ eq In Mo.
  Parameter ne_Sh_Mo: ~ eq Sh Mo.

  Hint Resolve ub_Mo lb_In compatible_prop ne_In_Sh ne_In_Mo ne_Sh_Mo.
End Coherence.

Module CoherenceSolve (cb: Coherence).
  Include !MakeOrderTac cb cb.
End CoherenceSolve.
