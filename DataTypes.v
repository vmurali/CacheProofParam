Require Import BaseTree Tree.

Set Implicit Arguments.

Parameter Addr: Set.
Parameter zero: Addr.
Axiom decAddr: forall a1 a2:Addr, {a1 = a2} + {a1 <> a2}.

Inductive Desc := Ld | St.

Parameter Data: Set.
Axiom decData: forall (d1 d2: Data), {d1 = d2} + {d1 <> d2}.

Parameter bHier : BaseTree.

Definition hier := getC nil bHier.
Opaque hier.

Record Cache := { node: Tree;
                  def: descendent node hier }.

Record Proc := { proc: Cache;
                 isLeaf: leaf (node proc) }.

Definition p_node x := node (proc x).

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
