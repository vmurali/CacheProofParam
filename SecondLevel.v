Require Import StoreAtomicity FirstLevel Coherence CacheLocal Tree DataTypes Case Useful.

Set Implicit Arguments.

Section SecondLevel.
  Variable State: Set.
  Variable coh: Coherence State.

  Variable cl: CacheLocal coh.

  Record SecondLevel :=
    {
      nonAncestorCompatible:
        forall t a p1 p2,
          let c1 := node p1 in
          let c2 := node p2 in
          ~ descendent c1 c2 ->
          ~ descendent c2 c1 ->
          compatible coh (state (s cl t) c1 a) (state (s cl t) c2 a);

      dataFromClean:
        forall t a p,
          let c := node p in
          ~ clean cl a t c ->
          clean cl a (S t) c ->
          exists c' t', t' <= t /\ data (s cl t') c' a = data (s cl (S t)) c a /\
                        clean cl a t' c' /\
                        forall ti, t' <= ti <= t ->
                                   match respFn cl ti with
                                     | Some (Build_Resp ci ii _) =>
                                         ~ (loc (reqFn ci ii) = a /\ desc (reqFn ci ii) = St)
                                     | None => True
                                   end
    }.

  Definition classicalProp P := P \/ ~ P.

  Ltac expandSl sl :=
    destruct sl as [nonAncestorCompatible dataFromClean]; simpl in *.

  Section DecChildProp.
    Variable P: Tree -> Tree -> Prop.
    Hypothesis decP: forall p c, classicalProp (P p c).
    Variable p: Tree.

    Lemma decChildProp':
      forall x, classicalProp (forall c, parent c p -> P x c).
    Proof.
      intros x.
      unfold classicalProp in *.
      unfold parent.
      destruct p as [r cs].
      induction cs.

      left; simpl; intuition.

      assert (aDec: classicalProp (P x a)) by apply decP.
      unfold classicalProp in *; simpl.
      destruct IHcs, aDec;
        match goal with
          | [H : P x a |- _ ] =>
              match goal with
                | [H1 : forall c, List.In c cs -> P x c |- _] =>
                    left; simpl; intros c opts;
                  destruct opts as [one|two]; [rewrite one in *| ]; intuition
              end
          | _ => intuition
        end.
    Qed.

    Lemma decChildProp:
      classicalProp (forall c, parent c p -> P p c).
    Proof.
      apply decChildProp'.
    Qed.
  End DecChildProp.

  Lemma decClean:
    forall a t p, clean cl a t p \/ ~ clean cl a t p.
  Proof.
    intros a t p.
    unfold clean.
    assert (sleOpts: forall x y, classicalProp (sle coh x y)) by
           (unfold classicalProp; intros; unfold sle;
            destruct (slt_total coh x y) as [c1 | [c2 | c3]];
            intuition; right; intros;
            match goal with
              | H: slt _ ?x ?y \/ ?x = ?y |- _ => destruct H; order coh
            end).
    assert (first: classicalProp (sle coh (Sh coh) (state (s cl t) p a))) by (apply sleOpts).
    assert (second: classicalProp (forall c, parent c p -> sle coh (dir (s cl t) p c a) (Sh coh))).
    apply (decChildProp (fun p c => sle coh (dir (s cl t) p c a) (Sh coh)) 
                        (fun p c => sleOpts (dir (s cl t) p c a) (Sh coh)) p).
    unfold classicalProp in *.
    destruct first, second; intuition.
  Qed.

  Variable sl: SecondLevel.

  Theorem latestValue:
    forall t a pCache,
      let p := node pCache in
      clean cl a t p ->
      (data (s cl t) p a = initData a /\
       forall t', t' < t -> noStore (respFn cl) t' a ) \/
      (exists tm,
         tm < t /\
         match respFn cl tm with
           | Some (Build_Resp cm im dm) =>
             let (am, descQm, dtQm) := reqFn cm im in
             data (s cl t) p a = dtQm /\ am = a /\ descQm = St /\
             forall t', tm < t' < t -> noStore (respFn cl) t' a
           | None => False
         end).
  Proof.
    intros.
    unfold p in *; clear p.
    expandSl sl.
    pose proof (fun t => decClean a t (node pCache)) as decClean.
    unfold clean in *.
    expandCl cl.
    clear respFnIdx respFnLdData.
    induction t.

    left.
    rewrite stateZero in *.
    destruct (decTree (node pCache) hier);
      [rewrite dataZero; constructor; intuition; omega |
       match goal with
         | H: sle _ _ _ /\ _ |- _ =>
             let x := fresh in
               destruct H as [[x | x] _]; generalize x; clear; intros ;
           pose proof (lb_In coh (Sh coh)); intuition; order coh
       end].

    specialize (decClean t).
    specialize (dataFromClean t a pCache).

  Qed.
End SecondLevel.
