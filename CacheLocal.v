Require Import DataTypes Tree.

Set Implicit Arguments.

Section CacheLocal.
  Variable State: Set.

  Record CacheState :=
    {
      state: Tree -> Addr -> State;
      dir: Tree -> Tree -> Addr -> State;
      data: Tree -> Addr -> Data;
      wait: Tree -> Addr -> bool;
      waitS: Tree -> Addr -> State;
      dwait: Tree -> Tree -> Addr -> bool;
      dwaitS: Tree -> Tree -> Addr -> State;
      next: Tree -> nat
    }.

  Record CacheLocal :=
    {
      getCacheState: Time -> CacheState;
      respFn: Time -> option Resp;
      respFnIdx: forall t,
                   match respFn t with
                     | Some (Build_Resp c i _) => i = next (getCacheState t) (p_node c)
                     | None => True
                   end;
      respFnLdData: forall t,
                      match respFn t with
                        | Some (Build_Resp c _ d) =>
                          match desc (reqFn c t) with
                            | Ld => d = data (getCacheState t) (p_node c) (loc (reqFn c t))
                            | St => d = initData zero
                          end
                        | None => True
                      end
    }.
End CacheLocal.
