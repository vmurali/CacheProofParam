Require Import DataTypes StoreAtomicity Case NamedTrans Useful.

Set Implicit Arguments.

Record State := { mem: Addr -> Data;
                  next: Proc -> nat
                }.

Inductive AtomicTrans s: State -> Set :=
| Req: forall c, AtomicTrans s (Build_State
                                  (match desc (reqFn c (next s c)) with
                                     | Ld => mem s
                                     | St =>
                                       fun t
                                       =>
                                         match decAddr t (loc (reqFn c (next s c))) with
                                           | left _ => dataQ (reqFn c (next s c))
                                           | _ => mem s t
                                         end
                                   end)
                                  (fun t => match decProc t c with
                                              | left _ => S (next s t)
                                              | _ => next s t
                                            end))
| Idle: AtomicTrans s s.

Section Bisim.
  Variable respFn: nat -> option Resp.
  Variable sa: StoreAtomic respFn.

  Definition AtomicList := TransList AtomicTrans (Build_State initData (fun t => 0)).

  Definition getTransNext n s (al: AtomicList n s) :=
    match respFn n with
      | Some r => Build_NextTrans _ _ _ (Req s (procR r))
      | None => Build_NextTrans _ _ _ (Idle s)
    end.

  Lemma nextLe t c: next (getTransSt getTransNext t) c <=
                    next (getTransSt getTransNext (S t)) c.
  Proof.
    pose (getTrans getTransNext t) as trans;
    unfold getTransSt;
    unfold getTransList;
    fold (getTransList getTransNext t).
    simpl; destruct trans; [simpl; destruct (decProc c c0) | ]; omega.
  Qed.

  Lemma nextStarLe t1 t2 c (cond: t1 <= t2): next (getTransSt getTransNext t1) c <=
                                             next (getTransSt getTransNext t2) c.
  Proof.
    remember (t2-t1) as td; assert (H: t2 = t1 + td) by omega;
    rewrite H in *; clear t2 cond H Heqtd.
    induction td.
    assert (H: t1 + 0 = t1) by omega; rewrite H; omega.
    assert (H: t1 + S td = S (t1 + td)) by omega; rewrite H; clear H;
    pose proof (nextLe (t1 + td) c) as sth.
    omega.
  Qed.

  Lemma reqImpGt t: match getTrans getTransNext t with
                      | Req c => S (next (getTransSt getTransNext t) c) =
                                 next (getTransSt getTransNext (S t)) c /\
                                 forall c', c' <> c ->
                                            next (getTransSt getTransNext t ) c' =
                                            next (getTransSt getTransNext (S t)) c'
                      | Idle => forall c, next (getTransSt getTransNext t ) c =
                                          next (getTransSt getTransNext (S t)) c
                    end.
  Proof.
    unfold getTransSt.
    unfold getTransList; fold (getTransList getTransNext t); simpl.
    destruct (getTrans getTransNext t).
    simpl.
    destruct (decProc c c).
    constructor. omega.
    intros c' c'_neq.
    destruct (decProc c' c); intuition.
    intuition.
    intuition.
  Qed.

  Theorem uniqAtomLabels:
    forall t1 t2,
      match getTrans getTransNext t1, getTrans getTransNext t2 with
        | Req c1, Req c2 =>
          c1 = c2 ->
          next (getTransSt getTransNext t1) c1 =
          next (getTransSt getTransNext t2) c2 ->
          t1 = t2
        | _, _ => True
      end.
  Proof.
    intros t1 t2.
    pose proof (reqImpGt t1) as sth1.
    pose proof (reqImpGt t2) as sth2.
    destruct (getTrans getTransNext t1).
    destruct (getTrans getTransNext t2).
    intros c_eq n_eq.
    rewrite <- c_eq in *.
    assert (opts: t1 = t2 \/ t1 < t2 \/ t2 < t1) by omega.

    destruct sth1 as [u1 _];
      destruct sth2 as [u2 _].
    destruct opts as [eq | [lt | gt]].
    assumption.

    Ltac finish c cond :=
      pose proof (nextStarLe c cond) as use;
      omega.
    finish c lt.
    finish c gt.

    intuition.
    intuition.
  Qed.

  Theorem localAtomOrdering:
    forall t1 t2, match getTrans getTransNext t1, getTrans getTransNext t2 with
                    | Req c1, Req c2 =>
                      c1 = c2 ->
                      next (getTransSt getTransNext t1) c1 <
                      next (getTransSt getTransNext t2) c2 ->
                        t1 < t2
                    | _, _ => True
                  end.
  Proof.
    intros t1 t2.
    pose proof (reqImpGt t1) as sth1.
    pose proof (reqImpGt t2) as sth2.
    destruct (getTrans getTransNext t1).
    destruct (getTrans getTransNext t2).
    intros c_eq n_lt.
    rewrite <- c_eq in *.
    destruct sth1 as [u1 _]; destruct sth2 as [u2 _].
    assert (opts: t1 = t2 \/ t1 < t2 \/ t2 < t1) by omega.
    destruct opts as [eq | [lt | gt]].
    rewrite eq in *; assert False by omega; intuition.
    intuition.
    pose proof (nextStarLe c gt) as use;
      assert False by omega; intuition.

    intuition.
    intuition.
  Qed.

  Theorem allAtomPrev t c i:
    next (getTransSt getTransNext t) c > i ->
    exists t', t' < t /\ match getTrans getTransNext t' with
                           | Req c' => c = c' /\ next (getTransSt getTransNext t') c' = i
                           | Idle => False
                         end.
  Proof.
    intros gt.
    induction t.
    simpl in gt.
    assert False by omega; intuition.
    pose proof (nextLe t c) as sth.
    assert (opts: next (getTransSt getTransNext (S t)) c =
                  next (getTransSt getTransNext t) c \/
                  next (getTransSt getTransNext (S t)) c >
                  next (getTransSt getTransNext t) c) by omega.
    destruct opts as [e|n].
    rewrite e in gt; destruct (IHt gt) as [t' [cond rest]]; exists t'; constructor;
    [ omega | intuition].
    assert (opts: next (getTransSt getTransNext t) c = i \/
                  next (getTransSt getTransNext t) c > i \/
                  next (getTransSt getTransNext t) c < i) by omega.
    destruct opts as [eq | [lt | gtt]].
    exists t; constructor.
    omega. 
    pose proof (reqImpGt t) as sth2.
    destruct (getTrans getTransNext t).
    destruct sth2 as [u1 u2].
    destruct (decProc c c0).
    rewrite e in *; intuition.
    specialize (u2 c n0).
    assert False by omega; intuition.
    specialize (sth2 c);
      assert False by omega; intuition.

    destruct (IHt lt) as [t' cond].
    exists t'; constructor; [omega | intuition].

    pose proof (reqImpGt t) as sth2.
    destruct (getTrans getTransNext t).
    destruct sth2 as [u1 u2].
    specialize (u2 c).
    destruct (decProc c c0).
    rewrite <- e in *.
    assert False by omega; intuition.
    specialize (u2 n0); assert False by omega; intuition.
    specialize (sth2 c); assert False by omega; intuition.
  Qed.

  Definition noCurrAtomStore t a :=
    match getTrans getTransNext t with
      | Req c' =>
        let (a', descQ', dtQ') :=
            reqFn c' (next (getTransSt getTransNext t) c') in
        a' = a -> descQ' = St -> False
      | _ => True
    end.

  Definition noAtomStore tl t a :=
    forall t', tl <= t' < t -> noCurrAtomStore t' a.

  Definition matchAtomStore cm tm t a :=
    let (am, descQm, dtQm) :=
        reqFn cm (next (getTransSt getTransNext tm) cm) in
    mem (getTransSt getTransNext t) a = dtQm /\
    am = a /\ descQm = St.

  Definition lastMatchAtomStore tm t a :=
    match getTrans getTransNext tm with
      | Req cm => matchAtomStore cm tm t a /\
                  noAtomStore (S tm) t a
      | _ => False
    end.

  Definition latestAtomValue t a :=
    (mem (getTransSt getTransNext t) a = initData a /\
     noAtomStore 0 t a) \/
    (exists tm,
       tm < t /\ lastMatchAtomStore tm t a).

  Definition atomNoPrevNonSt t a :=
    noAtomStore 0 t a /\
    mem (getTransSt getTransNext (S t)) a = initData a /\
    noCurrAtomStore t a.

  Definition atomPrevNonSt t a :=
    (exists tm,
       tm < t /\
       match getTrans getTransNext tm with
         | Req cm => matchAtomStore cm tm (S t) a /\
                     noAtomStore (S tm) t a
         | _ => False
       end) /\
    noCurrAtomStore t a.

  Definition atomSt t a :=
    lastMatchAtomStore t (S t) a.

  Lemma latestAtomInd t a (now: atomNoPrevNonSt t a \/ atomPrevNonSt t a \/ atomSt t a):
    latestAtomValue (S t) a.
  Proof.
    unfold latestAtomValue.
    destruct now as [noPrevNonSt | [prevNonSt | st]].

    Case "noPrevNonSt".
    unfold atomNoPrevNonSt in *.
    left.
    constructor.
    intuition.
    unfold noAtomStore in *.
    intros t' cond.
    assert (opts: 0 <= t' < t \/ t' = t) by omega.
    destruct opts as [done | eq]; [| rewrite eq]; intuition.

    Case "prevNonSt".
    right.
    unfold atomPrevNonSt in *.
    destruct prevNonSt as [[tm [cond lm]] noCurr].
    exists tm.
    constructor.
    omega.
    unfold lastMatchAtomStore in *.
    destruct (getTrans getTransNext tm).
    constructor.
    intuition.
    unfold noAtomStore.
    intros t' cond2.
    assert (opts: S tm <= t' < t \/ t' = t) by omega.
    destruct opts as [ez|ez2].
    intuition.
    rewrite ez2 in *; intuition.
    intuition.

    Case "st".
    right.
    unfold atomSt in st.
    exists t.
    constructor.
    omega.
    intuition.
  Qed.

  Lemma latestAtomValueHolds t a: latestAtomValue t a.
  Proof.
    induction t.

    Case "0".
    left; constructor; [| intros t' contra; assert False by omega]; intuition.

    Case "S t".
    apply latestAtomInd.

    unfold latestAtomValue in IHt.
    unfold lastMatchAtomStore in IHt.
    unfold atomNoPrevNonSt.
    unfold noCurrAtomStore.
    unfold atomPrevNonSt.
    unfold matchAtomStore in *.
    unfold noCurrAtomStore.

    unfold atomSt.
    unfold lastMatchAtomStore.
    unfold matchAtomStore.
    unfold noAtomStore.

    unfold getTransSt at 1 3 in IHt.
    unfold getTransSt at 1 2 4 5 6 7.
    unfold getTrans at 1 3 4.
    unfold getTransList; 
      fold (getTransList getTransNext t); simpl.
    destruct (trans (getTransNext (lTrans (getTransList getTransNext t))));
      simpl in *.

    SCase "Req".
    destruct (reqFn c (next (lSt (getTransList getTransNext t)) c)); simpl.
    destruct desc.

    SSCase "Ld".
    destruct IHt.

    SSSCase "NoPrev".
    left.
    intuition.
    discriminate.

    SSSCase "Prev".
    right; left.
    destruct (reqFn c (next (lSt (getTransList getTransNext t)) c)).
    intuition.
    discriminate.

    SSCase "St".
    destruct (decAddr a loc).

    SSSCase "addr match".
    right; right.
    constructor.
    auto.
    intros t' contra.
    assert False by omega; intuition.

    SSSCase "addr no match".
    destruct IHt; intuition.

    SCase "Idle".
    destruct IHt; intuition.
  Qed.


  Theorem storeAtomicityAtom:
    forall t,
      match getTrans getTransNext t with
        | Req c =>
          let (a, descQ, dtQ) := reqFn c (next (getTransSt getTransNext t) c) in
          match descQ with
            | Ld => latestAtomValue t a
            | St => True 
          end
        | _ => True
      end.
  Proof.
    intros t.
    pose proof (latestAtomValueHolds t).
    destruct (getTrans getTransNext t).
    destruct (reqFn c (next (getTransSt getTransNext t) c)) as [a desc _].
    destruct desc.
    apply latestAtomValueHolds.
    intuition.
    intuition.
  Qed.

  Definition atomicResp s s' (t: AtomicTrans s s') :=
    match t with
      | Req c => Some (Build_Resp c (next s c)
                                  match desc (reqFn c (next s c)) with
                                    | Ld => (mem s (loc (reqFn c (next s c))))
                                    | St => initData zero
                                  end)
      | Idle => None
    end.

  Section PrevMatch.
    Variable t: nat.
    Variable prevEq: forall ti : nat,
                       ti < t -> respFn ti = atomicResp (getTrans getTransNext ti).

    Definition nextTransList := getTransList getTransNext.

    Ltac assocResp :=
      unfold getTrans in *;
      unfold getTransSt in *;
      fold nextTransList in *;
      unfold getTransNext in *.

    Lemma bothSomeOrNone:
      match atomicResp (getTrans getTransNext t), respFn t with
        | Some _, Some _ => True
        | None, None => True
        | _, _ => False
      end.
    Proof.
      assocResp.
      destruct (respFn t); simpl; intuition.
    Qed.

    Lemma procSame:
      match atomicResp (getTrans getTransNext t), respFn t with
        | Some (Build_Resp c1 _ _), Some (Build_Resp c2 _ _) => c1 = c2
        | _, _ => True
      end.
    Proof.
      assocResp.
      destruct (respFn t); simpl.
      destruct r; intuition.
      intuition.
    Qed.

    Lemma nextGtFalse:
      match atomicResp (getTrans getTransNext t), respFn t with
        | Some (Build_Resp _ i1 _), Some (Build_Resp _ i2 _) => i1 > i2 -> False
        | _, _ => True
      end.
    Proof.
      assocResp;
      case_eq (respFn t);
      [intros r caseR; destruct r; simpl in *;
       intros nextGt;
       pose proof (allAtomPrev _ _ nextGt) as [t' [t'_lt_t allPrev]];
       specialize (prevEq t'_lt_t);
       assocResp;
       case_eq (respFn t'); [
         intros r caseR'; destruct r; rewrite caseR' in *; simpl in *;
         pose proof (uniqRespLabels sa t t') as uniq;
         rewrite caseR, caseR' in uniq;
         injection prevEq as _ idEq;
         rewrite <- idEq in allPrev;
         assert (tEq: t = t') by (generalize allPrev uniq; clear; intuition);
         assert False by omega; intuition|
         intros caseR'; rewrite caseR' in *; intuition] |
       intros caseR; simpl in *; intuition].
    Qed.

    Lemma nextLtFalse:
      match atomicResp (getTrans getTransNext t), respFn t with
        | Some (Build_Resp _ i1 _), Some (Build_Resp _ i2 _) => i1 < i2 -> False
        | _, _ => True
      end.
    Proof.
      assocResp;
      case_eq (respFn t);
      [intros r caseR; destruct r; simpl in *;
       intros nextLt;
       pose proof (allPrevious sa t) as allPrev;
       rewrite caseR in *;
       specialize (allPrev _ nextLt);
       destruct allPrev as [t' [t'_lt_t allPrev]];
       specialize (prevEq t'_lt_t);
       assocResp;
       case_eq (respFn t');
       [intros r caseR'; destruct r; rewrite caseR' in *; simpl in *;
        pose proof (uniqAtomLabels t t') as uniq;
        assocResp;
        rewrite caseR, caseR' in uniq; simpl in *;
        injection prevEq as _ idEq;
        assert (tEq: t = t') by (generalize allPrev idEq uniq; clear; intuition);
        assert False by omega; intuition |
        intros caseR'; rewrite caseR' in *; intuition] | 
        intros caseR; simpl in *; intuition].
    Qed.

    Lemma nextEq:
      match atomicResp (getTrans getTransNext t), respFn t with
        | Some (Build_Resp _ i1 _), Some (Build_Resp _ i2 _) => i1 = i2
        | _, _ => True
      end.
    Proof.
      pose proof nextLtFalse;
      pose proof nextGtFalse;
      repeat destructAll; try (omega); intuition.
    Qed.

    Lemma loadMatch:
      match atomicResp (getTrans getTransNext t), respFn t with
        | Some (Build_Resp _ _ d1), Some (Build_Resp _ _ d2) =>
          d1 = d2
        | _, _ => True
      end.
    Proof.
      assocResp.
      case_eq (respFn t).
      intros r respEq; destruct r; simpl in *.
      case_eq (desc (reqFn procR (next (lSt (nextTransList t)) procR))).
      intros isLd.
      pose proof nextEq as nextEq.
      pose proof (storeAtomicity sa t) as atom1.
      pose proof (storeAtomicityAtom t) as atom2.
      assocResp.
      rewrite respEq in *.
      simpl in *.
      rewrite nextEq in *.
      destruct (reqFn procR idx).
      simpl in *.
      rewrite isLd in *.
      unfold latestAtomValue in atom2.

      destruct atom1 as [no1|yes1]; destruct atom2 as [no2|yes2].

      Case "noBefore1, noBefore 2".
      destruct no1 as [u1 _]; destruct no2 as [u2 _].
      rewrite <- u1 in u2; assumption.

      Case "noBefore1, before 2".
      destruct yes2 as [tm [tm_lt_t stMatch]].
      unfold lastMatchAtomStore in stMatch.
      specialize (prevEq tm_lt_t).
      assocResp.
      destruct no1 as [_ no1].
      specialize (no1 tm tm_lt_t).
      
      case_eq (respFn tm).
      intros r respmEq; destruct r; rewrite respmEq in *; simpl in *.
      unfold matchAtomStore in stMatch.
      assocResp.
      injection prevEq as _ idEq.
      rewrite <- idEq in *.
      destruct (reqFn procR0 idx0).
      destruct stMatch as [[_ [u1 u2]] _].
      intuition.

      intros respmEq; rewrite respmEq in *; simpl in *; intuition.

      Case "before1, noBefore 2".
      destruct yes1 as [tm [tm_lt_t' stMatch]].
      specialize (prevEq tm_lt_t').
      assert (tm_lt_t: 0 <= tm < t) by omega.
      destruct no2 as [_ no2].
      unfold noAtomStore in no2.
      unfold noCurrAtomStore in no2.
      assocResp.
      specialize (no2 tm tm_lt_t).

      case_eq (respFn tm).
      intros r respmEq; destruct r; rewrite respmEq in *; simpl in *.
      injection prevEq as _ idEq.
      rewrite <- idEq in *.
      destruct (reqFn procR0 idx0).
      destruct stMatch as [_ [u1 [u2 _]]].
      intuition.

      intros respmEq; rewrite respmEq in *; simpl in *; intuition.
      
      Case "before1, before 2".
      destruct yes1 as [tm1 [tm1_lt_t stMatch1]].
      destruct yes2 as [tm2 [tm2_lt_t stMatch2]].
      unfold lastMatchAtomStore in stMatch2.
      assocResp.
      pose proof (prevEq tm1_lt_t) as prev1.
      pose proof (prevEq tm2_lt_t) as prev2.
      clear prevEq.
      unfold matchAtomStore, noAtomStore, noCurrAtomStore in *;
        assocResp.

      case_eq (respFn tm1); case_eq (respFn tm2).

      SCase "some tm1, some tm2".
      intros r r2Eq; destruct r; rewrite r2Eq in *;
      intros r r1Eq; destruct r; rewrite r1Eq in *; simpl in *.

      injection prev1 as d1Eq i1Eq.
      rewrite <- i1Eq in *;
      rewrite d1Eq in *; clear prev1 d1Eq.
      injection prev2 as d2Eq i2Eq.
      rewrite <- i2Eq in *;
      rewrite d2Eq in *; clear prev2 d2Eq.

      simpl in *.

      assert (opts: tm1 = tm2 \/ tm1 < tm2 \/ tm1 > tm2) by omega.
      destruct opts.

      SSCase "tm1 = tm2".
      rewrite H in *.
      rewrite r1Eq in r2Eq.
      injection r2Eq as dEq iEq pEq.
      rewrite dEq in *;
        rewrite iEq in *;
        rewrite pEq in *.
      destruct (reqFn procR0 idx0).
      destruct stMatch1 as [u1 _];
        destruct stMatch2 as [[u2 _] _].
      rewrite <- u1 in u2;
        assumption.

      destruct H.

      SSCase "tm1 < tm2".      
      destruct (reqFn procR1 idx1).
      destruct stMatch1 as [_ [_ [_ noLater]]].
      assert (c1: tm1 < tm2 < t) by omega.
      specialize (noLater _ c1); clear c1.
      rewrite r2Eq in noLater.
      destruct (reqFn procR0 idx0).
      generalize stMatch2 noLater; clear; intuition.

      SSCase "tm2 < tm1".
      destruct (reqFn procR0 idx0).
      destruct stMatch2 as [_ noLater].
      assert (c1: S tm2 <= tm1 < t) by omega.
      specialize (noLater _ c1); clear c1.
      rewrite r1Eq in noLater.
      simpl in *.
      rewrite <- i1Eq in *.
      destruct (reqFn procR1 idx1).
      generalize stMatch1 noLater; clear; intuition.

      SCase "some tm1, none tm2".
      intros r2Eq r r1Eq; destruct r; rewrite r2Eq in *; rewrite r1Eq in *;
      simpl in *; intuition.

      SCase "none tm1, some tm2".
      intros r r2Eq r1Eq; destruct r; rewrite r2Eq, r1Eq in *.
      simpl in *; intuition.

      SCase "none tm1, none tm2".
      intros r2Eq r1Eq; rewrite r2Eq, r1Eq in *.
      simpl in *; intuition.

      intros r.
      simpl in *.
      pose proof nextEq as nextEq.
      assocResp.
      pose proof (storeAtomicity sa t).
      rewrite respEq in *.
      simpl in *.
      rewrite nextEq in r.
      destruct (reqFn procR idx).
      simpl in *.
      rewrite r in *.
      auto.

      intros.
      repeat destructAll; intuition.
    Qed.

    Lemma allMatch:
      match atomicResp (getTrans getTransNext t), respFn t with
        | Some (Build_Resp c1 i1 d1), Some (Build_Resp c2 i2 d2) =>
          i1 = i2 /\ c1 = c2 /\ d1 = d2
        | None, Some _ => False
        | Some _, None => False
        | None, None => True
      end.
    Proof.
      pose proof bothSomeOrNone.
      pose proof procSame.
      pose proof nextEq.
      pose proof loadMatch.

      repeat destructAll; intuition.
    Qed.
  End PrevMatch.

  Theorem obeysP: forall n,
                    respFn n = atomicResp (getTrans getTransNext n).
  Proof.
    apply strong_ind.
    intros t prevEq.
    pose proof (allMatch prevEq) as sth.
    repeat destructAll;
    repeat f_equal; intuition.
  Qed.

  Definition getAtomicResp n := atomicResp (getTrans getTransNext n).

  Theorem respEq n: respFn n = getAtomicResp n.
  Proof.
    apply (obeysP n).
  Qed.
End Bisim.
