Set Implicit Arguments.

Record Coherence t :=
  { slt: t -> t -> Prop;

    slt_irrefl: forall x, ~ slt x x;
    slt_trans: forall x y z, slt x y -> slt y z -> slt x z;

    slt_total: forall x y, slt x y \/ x = y \/ slt y x;

    Mo: t;
    Sh: t;
    In: t;

    ub_Mo: forall x, slt Mo x -> False;
    lb_In: forall x, slt x In -> False;

    compatible: t -> t -> Prop;

    compatible_prop: forall x1 x2 y1 y2, compatible x1 y1 ->
                                         (slt x1 x2 \/ x1 = x2) -> (slt y1 y2 \/ y1 = y2) ->
                                         compatible x2 y2;

    ne_In_Sh: In <> Sh;
    ne_In_Mo: In <> Mo;
    ne_Sh_Mo: Sh <> Mo
  }.

Section CoherenceFacts.
  Variable t: Type.
  Variable ord: Coherence t.

  Definition sle x y := slt ord x y \/ x = y.

  Theorem sle_refl x: sle x x.
  Proof.
    unfold sle; intuition.
  Qed.

  Theorem slt_asym x y: slt ord x y -> slt ord y x -> False.
  Proof.
    pose proof (slt_trans ord x y x).
    pose proof (slt_irrefl ord x).
    intuition.
  Qed.

  Theorem sle_antisym x y: sle x y -> sle y x -> x = y.
  Proof.
    pose proof (slt_asym x y).
    unfold sle; intuition.
  Qed.

  Theorem neq_sym (x y: t): x <> y -> y <> x.
  Proof.
    intuition.
  Qed.

  Theorem sle_trans x y z: sle x y -> sle y z -> sle x z.
  Proof.
    pose proof (slt_trans ord x y z).
    unfold sle; intuition; match goal with
                             | H: ?x = ?y |- _ => rewrite H in *; clear H
                             | _ => idtac
                           end; intuition.
  Qed.

  Theorem sle_slt_trans x y z: sle x y -> slt ord y z -> slt ord x z.
  Proof.
    pose proof (slt_trans ord x y z).
    unfold sle; intuition; match goal with
                             | H: ?x = ?y |- _ => rewrite H in *; clear H
                             | _ => idtac
                           end; intuition.
  Qed.

  Theorem slt_sle_trans x y z: slt ord x y -> sle y z -> slt ord x z.
  Proof.
    pose proof (slt_trans ord x y z).
    unfold sle; intuition; match goal with
                             | H: ?x = ?y |- _ => rewrite H in *; clear H
                             | _ => idtac
                           end; intuition.
  Qed.

  Lemma slt_neq x y: slt ord x y -> x <> y.
  Proof.
    intros f s; rewrite <- s in *.
    pose proof (slt_irrefl ord x); intuition.
  Qed.

  Theorem not_neq_eq (x y: t): ~ x <> y -> x = y.
  Proof.
    intros.
    pose proof (@slt_neq x y).
    pose proof (@slt_neq y x).
    destruct (slt_total ord x y); intuition.
  Qed.

  Theorem not_sge_slt x y: ~ sle y x -> slt ord x y.
  Proof.
    unfold sle in *.
    pose proof (slt_irrefl ord x).
    pose proof (slt_irrefl ord y).
    pose proof (slt_total ord x y).
    pose proof (slt_total ord y x).
    try match goal with
          | H: ?x = ?y |- _ => rewrite H; clear H
        end; intuition.
  Qed.

  Theorem not_sgt_sle x y: ~ slt ord y x -> sle x y.
  Proof.
    unfold sle in *.
    pose proof (slt_irrefl ord x).
    pose proof (slt_irrefl ord y).
    pose proof (slt_total ord x y).
    pose proof (slt_total ord y x).
    try match goal with
          | H: ?x = ?y |- _ => rewrite H; clear H
        end; intuition.
  Qed.

  Theorem sle_neq_slt x y: sle x y -> x <> y -> slt ord x y.
  Proof.
    unfold sle in *.
    intuition.
  Qed.

  Lemma ne_Sh_In: Sh ord <> In ord.
  Proof.
    pose proof (ne_In_Sh ord).
    unfold not; let X := fresh in intros X; rewrite X in *; intuition.
  Qed.

  Lemma ne_Mo_In: Mo ord <> In ord.
  Proof.
    pose proof (ne_In_Mo ord).
    unfold not; let X := fresh in intros X; rewrite X in *; intuition.
  Qed.

  Lemma ne_Mo_Sh: Mo ord <> Sh ord.
  Proof.
    pose proof (ne_Sh_Mo ord).
    unfold not; let X := fresh in intros X; rewrite X in *; intuition.
  Qed.

  Definition sgt x y := slt ord y x.
  Definition sge x y := sle y x.
End CoherenceFacts.

Ltac order_prepare ord :=
  unfold not in *;
  match goal with
    | H: context [slt _ ?x ?y \/ ?x = ?y] |- _ => fold (sle ord x y) in H; order_prepare
    | |- context [slt _ ?x ?y \/ ?x = ?y] => fold (sle ord x y); order_prepare
    | H: slt _ ?x ?y -> False |- _ => apply (not_sgt_sle ord y x) in H; order_prepare
    | H: sle _ ?x ?y -> False |- _ => apply (not_sge_slt ord y x) in H; order_prepare
    | |- ?x = ?x => reflexivity
    | |- sle _ ?x ?x => apply (sle_refl ord x)
    | _ => (apply not_neq_eq; intro) ||
           (apply not_sge_slt; intro) ||
           (apply not_sgt_sle; intro) || exfalso
  end.

Ltac order_loop ord :=
  match goal with
    | H: slt _ ?x ?x |- _ => apply (slt_irrefl ord x H)
    | H: ?x <> ?x |- _ => exact (H (eq_refl x))
    | H: sle _ ?x ?x |- _ => clear H; order_loop ord
    | H: ?x = ?y |- _ => rewrite H in *; order_loop ord

    | H1: sle _ ?x ?y, H2: sle _ ?y ?x |- _ =>
        generalize (sle_antisym H1 H2); clear H1 H2; intro; order_loop ord

    | H1: sle _ ?x ?y, H2: ?x <> ?y |- _ =>
        generalize (sle_neq_slt H1 H2); clear H1 H2; intro; order_loop ord
    | H1: sle _ ?x ?y, H2: ?y <> ?x |- _ =>
        generalize (sle_neq_slt H1 (neq_sym H2)); clear H1 H2; intro; order_loop ord
    | H1 : slt _ ?x ?y, H2 : slt _ ?y ?z |- _ =>
        match goal with
          | H : slt _ x z |- _ => fail 1
          | _ => generalize (slt_trans ord x y z H1 H2); intro; order_loop ord
        end
    | H1 : sle _ ?x ?y, H2 : slt _ ?y ?z |- _ =>
       match goal with
         | H : slt _ x z |- _ => fail 1
         | _ => generalize (sle_slt_trans z H1 H2); intro; order_loop ord
       end
    | H1 : slt _ ?x ?y, H2 : sle _ ?y ?z |- _ =>
       match goal with
         | H : slt _ x z |- _ => fail 1
         | _ => generalize (slt_sle_trans H1 H2); intro; order_loop ord
       end
    | H1: sle _ ?x ?y, H2 : sle _ ?y ?z |- _ =>
       match goal with
         | H : sle _ x z |- _ => fail 1
         | _ => generalize (sle_trans H1 H2); intro; order_loop ord
       end
    | _ => idtac
   end.

Hint Resolve ub_Mo lb_In.

Ltac order ord :=
  pose proof (ne_In_Sh ord);
  pose proof (ne_In_Mo ord);
  pose proof (ne_Sh_Mo ord);
  pose proof (ne_Sh_In ord);
  pose proof (ne_Mo_In ord);
  pose proof (ne_Mo_Sh ord);
  unfold sgt, sge in *; unfold not; intros; order_prepare ord; order_loop ord; auto; fail "Order tactic failed".

Section Test.
  Variable t: Type.
  Variable ord: Coherence t.
  Theorem test1 x y: slt ord x y -> ~ slt ord y x.
  Proof.
    order ord.
  Qed.

  Theorem test2 x: ~ slt ord (Mo ord) x.
  Proof.
    eauto.
  Qed.

  Theorem test3 x: ~ slt ord x (In ord).
  Proof.
    eauto.
  Qed.
End Test.