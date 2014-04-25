Require Import StoreAtomicity FirstLevel Coherence CacheLocal Tree DataTypes Case Useful.

Set Implicit Arguments.

Module Type SecondLevel (Import coh: Coherence) (Import cl: CacheLocal coh).
  Definition clean a t p :=
    le Sh (state t p a) /\ forall c, parent c p -> le (dir t p c a) Sh.

  Definition noStoreData d a t :=
    d = initData a /\ forall t', t' < t -> noStore respFn t' a.

  Definition isStoreData d a t :=
    exists tm, tm < t /\ match respFn tm with
                           | Some (Build_Resp cm im dm) =>
                               let (am, descQm, dtQm) := reqFn cm im in
                                 d = dtQm /\ am = a /\ descQm = St /\
                                 forall t', tm < t' < t -> noStore respFn t' a
                           | None => False
                         end.

  Parameter cleanSameData:
    forall t a p,
      clean a t (node p) ->
      noStore respFn t a ->
      data t (node p) a = data (S t) (node p) a.

  Parameter cleanM:
    forall t a p1 p2,
      clean a t (node p1) ->
      clean a t (node p2) ->
      state t (node p1) a = Mo ->
      node p1 = node p2.

(*
  Parameter nonAncestorCompatible:
    forall t a p1 p2,
      let c1 := node p1 in
      let c2 := node p2 in
      ~ descendent c1 c2 ->
      ~ descendent c2 c1 ->
      compatible (state t c1 a) (state t c2 a).
*)
 
  Parameter dataFromClean:
    forall t a p,
      let c := node p in
      ~ clean a t c ->
      clean a (S t) c ->
      exists c' t', t' <= t /\ data t' c' a = data (S t) c a /\
                    clean a t' c' /\ forall ti, t' <= ti <= t -> noStore respFn ti a.

  Parameter processReq:
    forall t, 
      match respFn t with
        | Some (Build_Resp cProc _ _) =>
          let c := p_node cProc in
          let (a, op, d) := reqFn cProc (next t c) in
          match op with
            | Ld => le Sh (state t c a)
            | St => state t c a = Mo
          end
        | None => True
      end.
End SecondLevel.

Module mkFirstLevel (Import coh: Coherence) (Import cl: CacheLocal coh)
                    (Import sl: SecondLevel coh cl): FirstLevel coh cl.
  Module ord := CoherenceSolve coh.

  Definition clean := sl.clean.

  Definition noStoreData := sl.noStoreData.

  Definition isStoreData := sl.isStoreData.

  Definition processReq := sl.processReq.

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
    forall a t p, clean a t p \/ ~ clean a t p.
  Proof.
    intros a t p.
    unfold clean, sl.clean.
    assert (sleOpts: forall x y, classicalProp (le x y)) by
           (unfold classicalProp; intros x y;
            destruct (lt_total x y);
              repeat match goal with
                       | H: lt y x |- _ => right
                       | H: _ \/ _ |- _ => destruct H
                       | |- _ => left
                     end; ord.order).
    assert (first: classicalProp (le Sh (state t p a))) by (apply sleOpts).
    assert (second: classicalProp (forall c, parent c p -> le (dir t p c a) Sh)).
    apply (decChildProp (fun p c => le (dir t p c a) Sh) 
                        (fun p c => sleOpts (dir t p c a) Sh) p).
    unfold classicalProp in *.
    destruct first, second; intuition.
  Qed.

  Lemma noStoreLatest t a p:
    let c := node p in
      clean a t c ->
      (noStoreData (data t c a) a t \/ isStoreData (data t c a) a t) ->
      noStore respFn t a ->
      noStoreData (data (S t) c a) a (S t) \/ isStoreData (data (S t) c a) a (S t).
  Proof.

    Ltac finishOpts :=
      match goal with
        | H: ?t' < S ?t |- _ =>
            let x := fresh in assert (x: t' < t \/ t' = t) by omega;
            destruct x;
            match goal with
              | H': ?t' = ?t |- _ => rewrite H' in *
              | _ => idtac
            end; intuition
      end.

    intros c cleanT prev noCurr.
    pose proof (cleanSameData p cleanT noCurr) as sameData.
    unfold noStoreData, sl.noStoreData, isStoreData, sl.isStoreData in *.
    unfold c in *.
    rewrite <- sameData in *.
    destruct prev;

      [left; intuition; finishOpts |
       right; repeat (try applyExists; destructAll; intuition); finishOpts].
  Qed.

  Theorem latestValue t:
    forall a pCache,
      let p := node pCache in
        clean a t p ->
        noStoreData (data t p a) a t \/ isStoreData (data t p a) a t.
  Proof.
    induction t as [| t IHt].

    intros.

    left; unfold clean, sl.clean in *.
    rewrite state0 in *.
    destruct (decTree p hier);
    [ rewrite data0; constructor; intuition; omega |
      match goal with
        | H : le _ _ /\ _ |- _ => destruct H
      end; pose proof (@lb_In Sh);
      pose proof (ne_In_Sh);
      ord.order].

    intros.
    pose proof (fun t p => decClean a t p) as decClean.

    destruct decClean.
    admit.

    pose proof (dataFromClean _ H0 H).
    match goal with
      | H: clean ?a ?t ?p, H1: clean ?a ?t ?p -> _ |- _ =>
          let x := fresh in
            destruct (H1 H) as [x|x];
          apply (noStoreLatest H (H1 H) x)
    end.

    apply (noStoreLatest H0 H1

    destrutc
    specialize (IHt cleanT).

    destruct decClean.
    decClean).

    pose proof (@dataFromClean t a pCache).

    destruct decClean.
    unfold sl.clean in *.

    unfold noStoreData, isStoreData, sl.noStoreData, sl.isStoreData.
    intros.
    admit.
  Qed.

  Definition nextChange := sl.nextChange.
  Definition noReqAgain := sl.noReqAgain.
End mkFirstLevel.
