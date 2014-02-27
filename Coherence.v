Require Import Coq.Structures.Orders Coq.Structures.OrdersTac.

Module Type Coherence.
  Parameter t: Set.
  Parameter Mo Sh In: t.

  Definition eq (x y: t) := x = y.
  Parameter lt: t -> t -> Prop.
  Definition le (x y: t) := lt x y \/ x = y.

  Axiom eq_equiv: Equivalence eq.
  Axiom lt_strorder: StrictOrder lt.
  Axiom lt_compat: Proper (eq ==> eq ==> iff) lt.
  Axiom le_lteq: forall x y, le x y <-> lt x y \/ eq x y.
  Axiom lt_total: forall x y, lt x y \/ eq x y \/ lt y x.
  Axiom maxMo: forall x, le x Mo.
  Axiom maxMo': forall x, lt Mo x -> False.
  Axiom minIn: forall x, le In x.
  Axiom minIn': forall x, lt x In -> False.

  Parameter compatible: t -> t -> Prop.
End Coherence.

Ltac coherence := repeat match goal with
                           | [|- context [?fn]] => unfold fn
                           | [H: context [?fn] |- _] => unfold fn in H
                           | [|- forall x, _] => intro
                           | [H: ?x = ?y |- _] => rewrite H in *
                           | [x: ?P |- _] => destruct x
                         end; auto; try discriminate.


Module Msi <: Coherence.
  Inductive State := Mod | Sha | Inv.

  Definition t := State.

  Definition Mo := Mod.
  Definition Sh := Sha.
  Definition In := Inv.

  Definition eq (x y : t) := x = y.
  Definition lt (x y : t) := match x, y with
                               | In, In => False
                               | In, _ => True
                               | Sh, Mo => True
                               | Sh, _ => False
                               | Mo, _ => False
                             end.
  Definition le (x y : t) := lt x y \/ x = y.

  Theorem eq_equiv: Equivalence eq.
  Proof.
    constructor; coherence.
  Qed.

  Theorem lt_strorder: StrictOrder lt.
  Proof.
    constructor; coherence.
  Qed.

  Theorem lt_compat: Proper (eq ==> eq ==> iff) lt.
  Proof.
    constructor; coherence.
  Qed.

  Theorem le_lteq: forall x y, le x y <-> lt x y \/ eq x y.
  Proof.
    constructor; coherence.
  Qed.

  Theorem lt_total: forall x y, lt x y \/ eq x y \/ lt y x.
  Proof.
    coherence.
  Qed.

  Theorem maxMo: forall x, le x Mo.
  Proof.
    coherence.
  Qed.

  Theorem maxMo': forall x, lt Mo x -> False.
  Proof.
    coherence.
  Qed.

  Theorem minIn: forall x, le In x.
  Proof.
    coherence.
  Qed.

  Theorem minIn': forall x, lt x In -> False.
  Proof.
    coherence.
  Qed.

  Definition compatible x y :=
    match x, y with
      | In, _ => True
      | Sh, Mo => False
      | Sh, _ => True
      | Mo, In => True
      | Mo, _ => False
    end.

  Hint Resolve maxMo maxMo' minIn minIn'.
  Hint Unfold compatible.
End Msi.

Module Mosi <: Coherence.
  Inductive State := Mod | Ow | Sha | Inv.

  Definition t := State.

  Definition Mo := Mod.
  Definition Sh := Sha.
  Definition In := Inv.

  Definition eq (x y : t) := x = y.
  Definition lt (x y : t) := match x, y with
                               | In, In => False
                               | In, _ => True
                               | Sh, Mo => True
                               | Sh, Ow => True
                               | Sh, _ => False
                               | Ow, Mo => True
                               | Ow, _ => False
                               | Mo, _ => False
                             end.
  Definition le (x y : t) := lt x y \/ x = y.

  Theorem eq_equiv: Equivalence eq.
  Proof.
    constructor; coherence.
  Qed.

  Theorem lt_strorder: StrictOrder lt.
  Proof.
    constructor; coherence.
  Qed.

  Theorem lt_compat: Proper (eq ==> eq ==> iff) lt.
  Proof.
    constructor; coherence.
  Qed.

  Theorem le_lteq: forall x y, le x y <-> lt x y \/ eq x y.
  Proof.
    constructor; coherence.
  Qed.

  Theorem lt_total: forall x y, lt x y \/ eq x y \/ lt y x.
  Proof.
    coherence.
  Qed.

  Theorem maxMo: forall x, le x Mo.
  Proof.
    coherence.
  Qed.

  Theorem maxMo': forall x, lt Mo x -> False.
  Proof.
    coherence.
  Qed.

  Theorem minIn: forall x, le In x.
  Proof.
    coherence.
  Qed.

  Theorem minIn': forall x, lt x In -> False.
  Proof.
    coherence.
  Qed.

  Definition compatible x y :=
    match x, y with
      | In, _ => True
      | Sh, Mo => False
      | Sh, _ => True
      | Ow, Mo => False
      | Ow, Ow => False
      | Ow, _ => True
      | Mo, In => True
      | Mo, _ => False
    end.

  Hint Resolve maxMo maxMo' minIn minIn'.
  Hint Unfold compatible.
End Mosi.
