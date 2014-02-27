Require Import DataTypes Coherence Tree.

Module mkCacheLocal (coh: Coherence).
  Record CacheState :=
    {
      state: Tree -> Addr -> coh.t;
      dir: Tree -> Tree -> Addr -> coh.t;
      data: Tree -> Addr -> Data;
      wait: Tree -> Addr -> bool;
      waitS: Tree -> Addr -> coh.t;
      dwait: Tree -> Tree -> Addr -> bool;
      dwaitS: Tree -> Tree -> Addr -> coh.t;
      next: Tree -> nat
    }.

  Record CacheLocal :=
    {
      getCacheState: Time -> CacheState;
      deqR: Proc -> Time -> Prop;
      deqOrNot: forall t, {p| deqR p t} + {forall p, ~ deqR p t}
    }.

  Section CacheLocal.
    Variable cl: CacheLocal.
    Variable t: Time.
    Definition s := getCacheState cl t.

    Definition respFn :=
      match deqOrNot cl t with
        | inleft someDeq =>
          match someDeq with
            | exist pCache _ =>
              let p := p_node pCache in
              let (a, op, _) := reqFn pCache (next s p) in
              Some (Build_Resp pCache (next s p)
                               match op with
                                 | Ld => data s p a
                                 | St => initData zero
                               end)
          end
        | inright _ => None
      end.
  End CacheLocal.
End mkCacheLocal.
