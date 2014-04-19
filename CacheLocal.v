Require Import DataTypes Coherence Tree.

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

  Variable coh: Coherence State.

  Record CacheLocal :=
    {
      getCacheState: Time -> CacheState;
      respFn: Time -> option Resp;

      stateZero: state (getCacheState 0) = fun c a =>
                   match decTree c hier with
                     | left _ => Mo coh
                     | right _ => In coh
                   end;
      dirZero: dir (getCacheState 0) = fun p c a => In coh;
      dataZero: data (getCacheState 0) = fun c a => initData a;
      waitZero: wait (getCacheState 0) = fun c a => false;
      dwaitZero: dwait (getCacheState 0) = fun p c a => false;
      nextZero: next (getCacheState 0) = fun c => 0;

      respFnIdx: forall t,
                   match respFn t with
                     | Some (Build_Resp c i _) => i = next (getCacheState t) (p_node c)
                     | None => True
                   end;
      respFnLdData: forall t,
                      match respFn t with
                        | Some (Build_Resp c i d) =>
                          match desc (reqFn c i) with
                            | Ld => d = data (getCacheState t) (p_node c) (loc (reqFn c i))
                            | St => d = initData zero
                          end
                        | None => True
                      end
    }.
End CacheLocal.
