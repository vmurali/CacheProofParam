Require Import StoreAtomicity Coherence CacheLocal Tree DataTypes.

Set Implicit Arguments.

Module FirstLevel (coh: Coherence).
  Module mkCl := mkCacheLocal coh.
  Import coh mkCl.
  Section GivenState.
    Variable t: Time.
    Variable a: Addr.

    Variable cl: CacheLocal.

    Definition s := getCacheState cl t.
    Definition nextS := getCacheState cl (S t).

    Definition clean p :=
      le Sh (state s p a) /\ forall c, parent c p -> le (dir s p c a) Sh.

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
            compatible (state s c1 a) (state s c2 a);

        processReq:
          match respFn cl t with
            | Some (Build_Resp cProc _ _) =>
              let c := p_node cProc in
              let (a, op, d) := reqFn cProc (next s c) in
              match op with
                | Ld => le Sh (state s c a)
                | St => state s c a = Mo
              end
            | None => True
          end;
        
        nextChange:
          forall cProc,
            let c := p_node cProc in
            next nextS c <> next s c ->
            match respFn cl t with
              | Some (Build_Resp cProc' _ _) => cProc' = cProc
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
  End GivenState.
End FirstLevel.
