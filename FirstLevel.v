Require Import StoreAtomicity Coherence CacheLocal Tree DataTypes Case Useful.

Set Implicit Arguments.

Ltac expandCl cl :=
  destruct cl as [getCacheState respFn stateZero dirZero dataZero
                  waitZero dwaitZero nextZero respFnIdx respFnLdData];
  simpl in *.

Section FirstLevel.
  Variable State: Set.
  Variable coh: Coherence State.

  Variable cl: CacheLocal coh.

  Definition s t := getCacheState cl t.
  Definition nextS t := getCacheState cl (S t).

  Definition clean a t p :=
    sle coh (Sh coh) (state (s t) p a) /\ forall c, parent c p -> sle coh (dir (s t) p c a) (Sh coh).

  Ltac expandFl fl :=
    destruct fl as [latestValue processReq nextChange noReqAgain];
    unfold clean, s, nextS in *.

  Ltac expandClFl cl fl :=
    expandFl fl;
    expandCl cl.

  Record FirstLevel :=
    {
      latestValue:
        forall t a pCache,
          let p := node pCache in
          clean a t p ->
          (data (s t) p a = initData a /\
           forall t', t' < t -> noStore (respFn cl) t' a ) \/
          (exists tm,
             tm < t /\
             match respFn cl tm with
               | Some (Build_Resp cm im dm) =>
                 let (am, descQm, dtQm) := reqFn cm im in
                 data (s t) p a = dtQm /\ am = a /\ descQm = St /\
                 forall t', tm < t' < t -> noStore (respFn cl) t' a
               | None => False
             end);

      processReq:
        forall t, 
        match respFn cl t with
          | Some (Build_Resp cProc _ _) =>
            let c := p_node cProc in
            let (a, op, d) := reqFn cProc (next (s t) c) in
            match op with
              | Ld => sle coh (Sh coh) (state (s t) c a)
              | St => state (s t) c a = Mo coh
            end
          | None => True
        end;

      nextChange:
        forall t p,
          let c := p_node p in
          next (nextS t) c <> next (s t) c ->
          match respFn cl t with
            | Some (Build_Resp cProc' _ _) => p_node cProc' = c
            | None => False
          end;

      noReqAgain:
        forall t,
        match respFn cl t with
          | Some (Build_Resp cProc _ _) =>
            let c := p_node cProc in
            next (nextS t) c = S (next (s t) c)
          | None => True
        end
    }.

  Section Addr.
    Variable a: Addr.

    Variable fl: FirstLevel.

    Lemma nextIncOrSame:
      forall t p,
        let c := p_node p in
        next (getCacheState cl t) c = next (getCacheState cl (S t)) c \/
        next (getCacheState cl (S t)) c = S (next (getCacheState cl t) c).
    Proof.
      intros t p c.
      expandClFl cl fl.
      assert (opts: next (getCacheState t) c = next (getCacheState (S t)) c \/
                    next (getCacheState (S t)) c <> next (getCacheState t) c) by omega.
      specialize (nextChange t p).
      specialize (noReqAgain t).
      destruct opts; repeat destructAll;
      try match goal with
            | [H: (next (getCacheState (S t)) c <> next (getCacheState t) c) |- _ ] =>
                specialize (nextChange H); rewrite nextChange in *
          end;
      intuition.
    Qed.

    Lemma increasingIdx: forall t1 t2, t1 <= t2 -> forall p,
                                                     let c := p_node p in
                                                     next (s t1) c <=
                                                     next (s t2) c.
    Proof.
      intros t1 t2 cond p c.
      diff t1 t2 cond.
      unfold s in *.
      induction td; simplArith.
      omega.
      destruct (nextIncOrSame (t1 + td) p) as [eq|neq]; unfold c in *; omega.
    Qed.

    Lemma incrOnResp: forall t1 t2, t1 < t2 -> match respFn cl t1 with
                                                 | Some (Build_Resp c1 i1 _) =>
                                                   next (s t2) (p_node c1) > i1
                                                 | _ => True
                                               end.
    Proof.
      intros t1 t2 t1_lt_t2.
      assert (St1_le_t2: S t1 <= t2) by omega.
      pose proof (increasingIdx St1_le_t2) as u1.
      unfold s in *.
      expandClFl cl fl.
      specialize (noReqAgain t1).
      specialize (respFnIdx t1).
      repeat destructAll;
        match goal with
          | [c: Proc |- _] => specialize (u1 c); omega
          | _ => intuition
        end.
    Qed.

    Theorem uniqRespLabels':
      forall t1 t2, match respFn cl t1, respFn cl t2 with
                      | Some (Build_Resp c1 i1 _), Some (Build_Resp c2 i2 _) =>
                        p_node c1 = p_node c2 -> i1 = i2 -> t1 = t2
                      | _, _ => True
                    end.
    Proof.
      Ltac finish incrOnResp respFnIdx t2 lt :=
        specialize (incrOnResp _ _ lt);
        specialize (respFnIdx t2);
        repeat destructAll;
        match goal with
          | [|- True] => intuition
          | _ => try (intros pEq idEq; rewrite pEq, idEq in *; omega)
        end.

      intros t1 t2.
      pose proof @incrOnResp as incr;
      assert (opts: t1 = t2 \/ t1 < t2 \/ t2 < t1) by (unfold Time in *; omega).
      expandClFl cl fl.
      destruct opts as [eq| [lt|gt]].
      repeat destructAll; intuition.
      finish incr respFnIdx t2 lt.
      finish incr respFnIdx t1 gt.
    Qed.

    Theorem localOrdering':
      forall t1 t2, match respFn cl t1, respFn cl t2 with
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
      unfold s, nextS in *.
      expandCl cl.
      pose proof (respFnIdx t1) as r1.
      pose proof (respFnIdx t2) as r2.
      repeat destructAll; intros;
      match goal with
        | [H: p_node ?p1 = p_node ?p2 |- _] => rewrite H in *;
                                               specialize (incr p2); omega
        | _ => intuition
      end.
    Qed.

    Lemma allPrevIdx:
      forall t2 p2 i1,
        let c2 := p_node p2 in
        i1 < next (getCacheState cl t2) c2 ->
        exists t1, t1 < t2 /\
                   match respFn cl t1 with
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
      rewrite nextZero in *; omega.
      unfold c2 in *.
      pose proof (nextIncOrSame t2 p2) as opts.
      expandClFl cl fl.
      destruct opts as [same | inc].
      rewrite same in *.
      finishPrev IHt2 t2 i1LtNext.

      assert (opts: i1 < next (getCacheState t2) (p_node p2) \/ i1 = next (getCacheState t2) (p_node p2))
             by omega;
      destruct opts as [lt | same].
      finishPrev IHt2 t2 lt.

      rewrite same in *.
      assert (ne: next (getCacheState (S t2)) (p_node p2) <> next (getCacheState t2) (p_node p2)) by omega.
      specialize (nextChange t2 p2 ne).
      specialize (respFnIdx t2).
      exists t2.
      repeat destructAll; try omega; match goal with
                                       | [H: p_node ?p = p_node p2 |- _ ] => rewrite <- H in *; intuition
                                     end.
    Qed.

    Theorem allPrevious':
      forall t2, match respFn cl t2 with
                   | Some (Build_Resp c2 i2 _) =>
                       forall i1, i1 < i2 -> exists t1, t1 < t2 /\
                                                           match respFn cl t1 with
                                                             | Some (Build_Resp c1 i _) =>
                                                                 p_node c1 = p_node c2 /\ i = i1
                                                             | None => False
                                                           end
                   | _ => True
                 end.
    Proof.
      intros t2.
      pose proof (allPrevIdx t2) as u1.
      expandClFl cl fl.
      specialize (respFnIdx t2).
      repeat destructAll;
      try match goal with
            | [p: Proc |- _] => specialize (u1 (p_node p))
          end; intuition.
    Qed.
  End Addr.

  Section Sa.
    Variable fl: FirstLevel.

    Lemma leafProp: forall p c, ~ parent c (node (proc p)).
    Proof.
      unfold not; intros p c c_p.
      destruct p.
      unfold parent, leaf in *.
      simpl in *.
      repeat destructAll; simpl in *; intuition.
    Qed.

    Lemma cleanProp:
      forall t p coh loc,
        sle coh (Sh coh) (state (getCacheState cl t) (node (proc p)) loc) ->
        sle coh (Sh coh) (state (getCacheState cl t) (node (proc p)) loc) /\
        (forall c, parent c (node (proc p)) ->
                   sle coh (dir (getCacheState cl t) (node (proc p)) c loc) (Sh coh)).
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
        match respFn cl t with
          | Some (Build_Resp c i d) =>
            let (a, descQ, dtQ) := reqFn c i in
            match descQ with
              | Ld =>
                (d = initData a /\ forall t', t' < t -> noStore (respFn cl) t' a) \/
                (exists tm,
                   tm < t /\
                   match respFn cl tm with
                     | Some (Build_Resp cm im dm) =>
                       let (am, descQm, dtQm) := reqFn cm im in
                       d = dtQm /\ am = a /\ descQm = St /\
                       forall t', tm < t' < t -> noStore (respFn cl) t' a
                     | _ => False
                   end)
              | St => d = initData zero 
            end
          | _ => True
        end.
    Proof.
      intros t.
      pose proof (cleanProp t) as cleanProp.
      expandClFl cl fl.
      specialize (respFnIdx t).
      specialize (respFnLdData t).
      specialize (latestValue t).
      specialize (processReq t).
      unfold p_node in respFnLdData.
      destructAll.
      destructAll.
      rewrite <- respFnIdx in processReq.
      destructAll.
      destructAll.

      specialize (latestValue loc (proc procR) (cleanProp _ _ _ processReq));
      simpl in *; rewrite <- respFnLdData in *;
      intuition.

      intuition.

      intuition.
    Qed.

    Theorem fullStoreAtomicity: StoreAtomicity (respFn cl).
    Proof.
      apply (Build_StoreAtomicity (respFn cl) (uniqRespLabels' fl) (localOrdering' fl)
                                  (allPrevious' fl) storeAtomicity').
    Qed.
  End Sa.
End FirstLevel.
