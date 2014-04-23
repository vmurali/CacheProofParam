Require Import DataTypes Coherence Tree.

Set Implicit Arguments.

Module Type CacheLocal (Import coh: Coherence).
  Parameter state: Time -> Tree -> Addr -> t.
  Parameter dir: Time -> Tree -> Tree -> Addr -> t.
  Parameter data: Time -> Tree -> Addr -> Data.
  Parameter wait: Time -> Tree -> Addr -> bool.
  Parameter waitS: Time -> Tree -> Addr -> t.
  Parameter dwait: Time -> Tree -> Tree -> Addr -> bool.
  Parameter dwaitS: Time -> Tree -> Tree -> Addr -> t.
  Parameter next: Time -> Tree -> nat.

  Parameter respFn: Time -> option Resp.

  Parameter respFnIdx: forall t,
                         match respFn t with
                           | Some (Build_Resp c i _) => i = next t (p_node c)
                           | None => True
                         end.
  Parameter respFnLdData: forall t,
                            match respFn t with
                              | Some (Build_Resp c i d) =>
                                  match desc (reqFn c i) with
                                    | Ld => d = data t (p_node c) (loc (reqFn c i))
                                    | St => d = initData zero
                                  end
                              | None => True
                            end.

  Parameter state0: state 0 = fun c a =>
                                match decTree c hier with
                                  | left _ => Mo
                                  | right _ => In
                                end.

  Parameter dir0: dir 0 = fun p c a => In.

  Parameter data0: data 0 = fun c a => initData a.

  Parameter wait0: wait 0 = fun c a => false.

  Parameter dwait0: dwait 0 = fun p c a => false.

  Parameter next0: next 0 = fun c => 0.
End CacheLocal.
(*
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

    }.
End CacheLocal.
*)