Set Implicit Arguments.

Parameter Addr: Set.
Parameter zero: Addr.
Axiom decAddr: forall a1 a2:Addr, {a1 = a2} + {a1 <> a2}.

Inductive Desc := Ld | St.

Parameter Data: Set.
Axiom decData: forall (d1 d2: Data), {d1 = d2} + {d1 <> d2}.

Parameter Proc: Set.
Axiom decProc: forall (c1 c2: Proc), {c1 = c2} + {c1 <> c2}.
Definition Label := (Proc * nat)%type.
Theorem decLabel: forall (l1 l2: Label), {l1 = l2} + {l1 <> l2}.
Proof.
  intros l1 l2.
  decide equality.
  decide equality.
  apply (decProc a p).
Qed.

Record Req := { loc: Addr;
                desc: Desc;
                dataQ: Data
              }.

Record Resp := { procR: Proc;
                 idx: nat;
                 datum: Data
               }.

Parameter reqFn: Proc -> nat -> Req.
Parameter initData: Addr -> Data.
