Require Import StoreAtomicity Coherence CacheLocal Tree DataTypes Case Useful.

Set Implicit Arguments.

Section FirstLevel.
  Variable State: Set.
  Variable coh: Coherence State.

  Variable cl: CacheLocal State.


  Section Addr.
    Variable a: Addr.

    Section Time.
      Variable t: Time.
      Definition s := getCacheState cl t.
      Definition nextS := getCacheState cl (S t).

      Definition clean p :=
        sle coh (Sh coh) (state s p a) /\ forall c, parent c p -> sle coh (dir s p c a) (Sh coh).

      Record FirstLevel :=
        {
          latestValue:
            forall pCache,
              let p := node pCache in
              clean p ->
              (data s p a = initData a /\
               forall t', t' < t -> noStore (respFn cl) t' a ) \/
              (exists tm,
                 tm < t /\
                 match respFn cl tm with
                   | Some (Build_Resp cm im dm) =>
                     let (am, descQm, dtQm) := reqFn cm im in
                     data s p a = dtQm /\ am = a /\ descQm = St /\
                     forall t', tm < t' < t -> noStore (respFn cl) t' a
                   | None => False
                 end);

          nonAncestorCompatible:
            forall cCache1 cCache2: Cache,
              let c1 := node cCache1 in
              let c2 := node cCache2 in
              ~ descendent c1 c2 ->
              ~ descendent c2 c1 ->
              compatible coh (state s c1 a) (state s c2 a);

          processReq:
            match respFn cl t with
              | Some (Build_Resp cProc _ _) =>
                let c := p_node cProc in
                let (a, op, d) := reqFn cProc (next s c) in
                match op with
                  | Ld => sle coh (Sh coh) (state s c a)
                  | St => state s c a = Mo coh
                end
              | None => True
            end;

          nextChange:
            forall c,
              next nextS c <> next s c ->
              match respFn cl t with
                | Some (Build_Resp cProc' _ _) => p_node cProc' = c
                | None => False
              end;

          noReqAgain:
            match respFn cl t with
              | Some (Build_Resp cProc _ _) =>
                let c := p_node cProc in
                next nextS c = S (next s c)
              | None => True
            end
        }.
    End Time.

    Variable fl: forall t, FirstLevel t.

    Lemma increasingIdx: forall t1 t2 c, t1 <= t2 -> next (s t1) c <=
                                                     next (s t2) c.
    Proof.
      intros t1 t2 c cond.
      remember (t2-t1) as td.
      assert (t2eq: t2 = t1 + td) by omega.
      rewrite t2eq in *; clear t2eq Heqtd t2 cond.
      unfold Time in *.
      induction td.
      assert (eq: t1 + 0 = t1) by omega; rewrite eq; omega.
      assert (eq: t1 + S td = S (t1 + td)) by omega; rewrite eq; clear eq.
      assert (step: next (s (t1 + td)) c <=
                    next (nextS (t1 + td)) c).
      pose proof (fl (t1 + td)) as [_ _ _ nextChange noReqAgain].
      repeat destructAll.
      destruct procR.
      unfold p_node in *.
      destruct proc.
      simpl in *.
      destruct (decTree node c).
      rewrite <- e in *.
      omega.
      assert (opts: {next (nextS (t1 + td)) c = next (s (t1 + td)) c} +
                    {next (nextS (t1 + td)) c <> next (s (t1 + td)) c}) by decide equality.
      destruct opts.
      omega.
      specialize (nextChange _ n0); intuition.
      specialize (nextChange c).
      omega.
      unfold nextS, s in *.
      omega.
    Qed.

    Lemma incrOnResp: forall t1 t2, t1 < t2 -> match respFn cl t1 with
                                                 | Some (Build_Resp c1 i1 _) =>
                                                   next (s t2) (p_node c1) > i1
                                                 | _ => True
                                               end.
    Proof.
      intros t1 t2 t1_lt_t2.
      assert (St1_le_t2: S t1 <= t2) by omega.
      unfold s.
      case_eq cl.
      intros getSt respFn respFnIdx respFnData clEq; simpl.
      pose proof (respFnIdx t1) as respIdx.
      case_eq (respFn t1).
      intros r respEq.
      rewrite respEq in *.
      case_eq r.
      intros procR idx datum rEq.
      rewrite rEq in *.
      pose proof (increasingIdx (p_node procR) St1_le_t2) as sth.
      pose proof (noReqAgain (fl t1)) as sth2.
      unfold s, nextS in *.
      rewrite clEq in *; simpl in *; rewrite respEq in *.
      omega.
      intuition.
    Qed.

    Theorem uniqRespLabels':
      forall t1 t2, match respFn cl t1, respFn cl t2 with
                      | Some (Build_Resp c1 i1 _), Some (Build_Resp c2 i2 _) =>
                        p_node c1 = p_node c2 -> i1 = i2 -> t1 = t2
                      | _, _ => True
                    end.
    Proof.
      intros t1 t2.
      assert (opts: t1 = t2 \/ t1 < t2 \/ t2 < t1) by (unfold Time in *; omega).
      destruct opts as [eq| [lt|gt]].

      repeat destructAll; intuition.

      Ltac finish t1 t2 lt :=
        pose proof (incrOnResp lt) as sth;
        case_eq cl; intros getSt respFn respFnIdx respFnData clEq; simpl;
        pose proof (respFnIdx t2) as respIdx;
        unfold s in *; rewrite clEq in *; simpl in *;
        repeat destructAll;
        [ intros pEq idEq;
          rewrite pEq, idEq in *;
          omega |
          intuition |
          intuition |
          intuition ].

      finish t1 t2 lt.
      finish t2 t1 gt.
    Qed.

    Theorem localOrdering:
      forall t1 t2, match respFn cl t1, respFn cl t2 with
                      | Some (Build_Resp c1 i1 _), Some (Build_Resp c2 i2 _) =>
                        p_node c1 = p_node c2 -> i1 > i2 -> t1 > t2
                      | _, _ => True
                    end.
    Proof.
      intros t1 t2.
      assert (opts: t1 > t2 \/ t1 <= t2) by (unfold Time in *; omega).
      destruct opts as [ez | t1_le_t2].
      repeat destructAll; intuition.
      assert (contra: match respFn cl t1, respFn cl t2 with
                        | Some (Build_Resp c1 i1 _), Some (Build_Resp c2 i2 _) =>
                          p_node c1 = p_node c2 -> i1 <= i2
                        | _, _ => True
                      end).
      case_eq cl; simpl.
      intros getSt respFn respFnIdx respDt clEq.
      case_eq (respFn t1).
      intros r respEq.
      case_eq r.
      intros procR idx datum rEq.
      case_eq (respFn t2).
      intros r0 resp0Eq.
      case_eq r0.
      intros procR0 idx0 datum0 r0Eq.
      pose proof (increasingIdx (p_node procR) t1_le_t2) as idxLe.
      unfold s in idxLe.
      rewrite clEq in idxLe; simpl in *.
      pose proof (respFnIdx t1) as sth1.
      pose proof (respFnIdx t2) as sth2.
      rewrite respEq, resp0Eq, rEq, r0Eq in *.
      intros pEq.
      rewrite <- pEq in sth2.
      omega.
      intuition.
      intuition.
      
      repeat destructAll; intuition.
    Qed.
  End Addr.

  Section Sa.
    Variable fl: forall a t, FirstLevel a t.
    Theorem storeAtomicity:
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
      unfold s, nextS in *; 
        destruct cl; simpl in *.
      specialize (respFnLdData t).
      clear respFnIdx.
      destructAll.
      destructAll.
      simpl in *.
      destruct (reqFn procR idx).
      simpl in *.
      specialize (fl loc t).
      destruct fl as [lv _ pr _ _].
      destruct desc.
      simpl in *.
    case_eq cl; intros; simpl.

End FirstLevel.
