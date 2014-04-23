Require Import StoreAtomicity Coherence CacheLocal Tree DataTypes Case Useful.

Set Implicit Arguments.

Module Type FirstLevel (Import coh: Coherence) (Import cl: CacheLocal coh).
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

  Parameter latestValue:
    forall t a pCache,
      let p := node pCache in
      clean a t p ->
      noStoreData (data t p a) a t \/ isStoreData (data t p a) a t.

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
   
  Parameter nextChange:
    forall t p,
      let c := p_node p in
      next (S t) c <> next t c ->
      match respFn t with
        | Some (Build_Resp cProc' _ _) => p_node cProc' = c
        | None => False
      end.
   
  Parameter noReqAgain:
    forall t,
    match respFn t with
      | Some (Build_Resp cProc _ _) =>
        let c := p_node cProc in
        next (S t) c = S (next t c)
      | None => True
    end.
End FirstLevel.

Module mkStoreAtomic (Import coh: Coherence) (Import cl: CacheLocal coh) (Import fl: FirstLevel coh cl).
  Section ForAddr.
    Variable a: Addr.
    Lemma nextIncOrSame:
      forall t p,
        let c := p_node p in
        next t c = next (S t) c \/
        next (S t) c = S (next t c).
    Proof.
      intros t p c.
      assert (opts: next t c = next (S t) c \/
                    next (S t) c <> next t c) by omega.
      pose proof (@nextChange t p) as nextChange.
      pose proof (noReqAgain t) as noReqAgain.
      destruct opts; repeat destructAll;
      try match goal with
            | [H: (next (S t) c <> next t c) |- _ ] =>
                specialize (nextChange H); try rewrite nextChange in *
          end;
      intuition.
    Qed.

    Lemma increasingIdx: forall t1 t2, t1 <= t2 -> forall p,
                                                     let c := p_node p in
                                                     next t1 c <=
                                                     next t2 c.
    Proof.
      intros t1 t2 cond p c.
      diff t1 t2 cond.
      induction td; simplArith.
      omega.
      destruct (nextIncOrSame (t1 + td) p) as [eq|neq]; unfold c in *; omega.
    Qed.

    Lemma incrOnResp: forall t1 t2, t1 < t2 -> match respFn t1 with
                                                 | Some (Build_Resp c1 i1 _) =>
                                                   next t2 (p_node c1) > i1
                                                 | _ => True
                                               end.
    Proof.
      intros t1 t2 t1_lt_t2.
      assert (St1_le_t2: S t1 <= t2) by omega.
      pose proof (increasingIdx St1_le_t2) as u1.
      pose proof (noReqAgain t1).
      pose proof (respFnIdx t1).
      repeat destructAll;
        repeat match goal with
          | c: Proc |- _ => specialize (u1 c); omega
          | _ => intuition
        end.
    Qed.

    Theorem uniqRespLabels':
      forall t1 t2, match respFn t1, respFn t2 with
                      | Some (Build_Resp c1 i1 _), Some (Build_Resp c2 i2 _) =>
                        p_node c1 = p_node c2 -> i1 = i2 -> t1 = t2
                      | _, _ => True
                    end.
    Proof.
      Ltac finish incrOnResp respFnIdx t2 slt :=
        specialize (incrOnResp _ _ slt);
        specialize (respFnIdx t2);
        repeat destructAll;
        match goal with
          | _ => intros pEq idEq; rewrite pEq, idEq in *; omega
          | _ => intuition
        end.

      intros t1 t2.
      pose proof @incrOnResp as incr;
      assert (opts: t1 = t2 \/ t1 < t2 \/ t2 < t1) by (unfold Time in *; omega).
      destruct opts as [eq| [slt|sgt]].
      repeat destructAll; intuition.
      finish incr respFnIdx t2 slt.
      finish incr respFnIdx t1 sgt.
    Qed.

    Theorem localOrdering':
      forall t1 t2, match respFn t1, respFn t2 with
                      | Some (Build_Resp c1 i1 _), Some (Build_Resp c2 i2 _) =>
                        p_node c1 = p_node c2 -> i1 > i2 -> t1 > t2
                      | _, _ => True
                    end.
    Proof.
      intros t1 t2.
      assert (opts: t1 > t2 \/ t1 <= t2) by (unfold Time in *; omega).
      destruct opts as [lt|le].
      repeat destructAll; intuition.
      pose proof (increasingIdx le) as incr.
      pose proof (respFnIdx t1) as r1.
      pose proof (respFnIdx t2) as r2.
      repeat destructAll; intros;
        repeat match goal with
                 | [H: p_node ?p1 = p_node ?p2 |- _] =>
                     rewrite H in *;
                             specialize (incr p2); omega
                 | _ => intuition
               end.
    Qed.

    Lemma allPrevIdx:
      forall t2 p2 i1,
        let c2 := p_node p2 in
        i1 < next t2 c2 ->
        exists t1, t1 < t2 /\
                   match respFn t1 with
                     | Some (Build_Resp c1 i _) =>
                         p_node c1 = c2 /\ i = i1
                     | None => False
                   end.
    Proof.
      Ltac finishPrev iht t2 cond :=
        destruct (iht cond);
        match goal with
          | [H: context [?x < t2] |- _] => exists x; try omega; intuition
        end.

      intros t2 p2 i1 c2 i1LtNext.
      induction t2.
      rewrite next0 in *; omega.
      unfold c2 in *.
      pose proof (nextIncOrSame t2 p2) as opts.
      destruct opts as [same | inc].
      rewrite same in *.
      finishPrev IHt2 t2 i1LtNext.

      assert (opts: i1 < next t2 (p_node p2) \/ i1 = next t2 (p_node p2))
             by omega;
      destruct opts as [lt | same].
      finishPrev IHt2 t2 lt.

      rewrite same in *.
      assert (ne: next (S t2) (p_node p2) <> next t2 (p_node p2)) by omega.
      pose proof (nextChange p2 ne).
      pose proof (respFnIdx t2).
      exists t2.
      repeat destructAll; try omega; match goal with
                                       | [H: p_node ?p = p_node p2 |- _ ] => rewrite <- H in *; intuition
                                     end.
    Qed.

    Theorem allPrevious':
      forall t2, match respFn t2 with
                   | Some (Build_Resp c2 i2 _) =>
                       forall i1, i1 < i2 -> exists t1, t1 < t2 /\
                                                           match respFn t1 with
                                                             | Some (Build_Resp c1 i _) =>
                                                                 p_node c1 = p_node c2 /\ i = i1
                                                             | None => False
                                                           end
                   | _ => True
                 end.
    Proof.
      intros t2.
      pose proof (@allPrevIdx t2) as u1.
      pose proof (respFnIdx t2).
      repeat destructAll;
      try match goal with
            | [p: Proc |- _] => specialize (u1 (p_node p))
          end; intuition.
    Qed.
  End ForAddr.

  Section Sa.
    Lemma leafProp: forall p c, ~ parent c (node (proc p)).
    Proof.
      unfold not; intros p c c_p.
      destruct p.
      unfold parent, leaf in *.
      simpl in *.
      repeat destructAll; simpl in *; intuition.
    Qed.

    Lemma cleanProp:
      forall t p loc,
        le Sh (state t (node (proc p)) loc) ->
        le Sh (state t (node (proc p)) loc) /\
        (forall c, parent c (node (proc p)) ->
                   le (dir t (node (proc p)) c loc) Sh).
    Proof.
      intros.
      pose proof (leafProp p) as leafProp.
      constructor;
      intros;
        (try match goal with
               | [c: Tree |- _] => specialize (leafProp c)
             end); intuition.
    Qed.

    Theorem storeAtomicity':
      forall t,
        match respFn t with
          | Some (Build_Resp c i d) =>
            let (a, descQ, dtQ) := reqFn c i in
            match descQ with
              | Ld =>
                  noStoreData d a t \/ isStoreData d a t
              | St => d = initData zero
            end
          | _ => True
        end.
    Proof.
      intros t.
      unfold noStoreData, isStoreData.
      pose proof (@cleanProp t) as cleanProp.
      pose proof (respFnIdx t) as respFnIdx.
      pose proof (respFnLdData t) as respFnLdData.
      pose proof (@latestValue t).
      pose proof (processReq t) as processReq.
      unfold p_node in *.
      destructAll.
      destructAll.
      rewrite <- respFnIdx in *.
      destructAll.
      destructAll.

      specialize (latestValue (proc procR) (cleanProp _ _ processReq));
      simpl in *; rewrite <- respFnLdData in *;
      intuition.

      intuition.

      intuition.
    Qed.

    Theorem fullStoreAtomicity: StoreAtomicity respFn.
    Proof.
      apply (Build_StoreAtomicity respFn uniqRespLabels' localOrdering'
                                  allPrevious' storeAtomicity').
    Qed.
  End Sa.
End mkStoreAtomic.
