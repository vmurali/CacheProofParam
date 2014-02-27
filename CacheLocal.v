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
      deqR: Proc -> Time -> Prop
    }.

End mkCacheLocal.
