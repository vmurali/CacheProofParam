Set Implicit Arguments.

Record Coherence t := 
  {
    Mo: t;
    Sh: t;
    In: t;
    slt: t -> t -> Prop;
    compatible: t -> t -> Prop
  }.

Definition sle t (coh: Coherence t) x y:= slt coh x y \/ x = y.

Inductive Msi := Mod | Sha | Inv.

Definition slt_Msi x y :=
  match x, y with
    | Inv, Inv => False
    | Inv, _ => True
    | Sha, Mod => True
    | Sha, _ => False
    | Mod, _ => False
  end.

Definition compatible_Msi x y :=
  match x, y with
    | Inv, _ => True
    | Sha, Mod => False
    | Sha, _ => True
    | Mod, Inv => True
    | Mod, _ => False
  end.

Definition Coherence_Msi :=
  Build_Coherence Mod Sha Inv slt_Msi compatible_Msi.

Inductive Mosi := Modi | Ow | Shar | Inva.

Definition slt_Mosi x y :=
  match x, y with
    | Inva, Inva => False
    | Inva, _ => True
    | Shar, Modi => True
    | Shar, Ow => True
    | Shar, _ => False
    | Ow, Modi => True
    | Ow, _ => False
    | Modi, _ => False
  end.

Definition compatible_Mosi x y :=
  match x, y with
    | Inva, _ => True
    | Shar, Modi => False
    | Shar, _ => True
    | Ow, Modi => False
    | Ow, Ow => False
    | Ow, _ => True
    | Modi, Inva => True
    | Modi, _ => False
  end.

Definition Coherence_Mosi :=
  Build_Coherence Modi Shar Inva slt_Mosi compatible_Mosi.

Ltac solveCoh :=
  solve [
      unfold sle, Mo, Sh, In in *;
      intros;
      (repeat match goal with
                | [x : Msi |- _] => destruct x
                | [x : Mosi |- _] => destruct x
              end); simpl in *; auto;
      match goal with
        | [_: context [?x = ?y] |- _] =>
          match type of x with
            | Msi => assert (x = y) by intuition; discriminate
            | Mosi => assert (x = y) by intuition; discriminate
          end
      end].

(*
      match goal with
        | [_: context [Mod = Sha] |- _] => assert (Mod = Sha) by intuition; discriminate
        | [_: context [Mod = Inv] |- _] => assert (Mod = Inv) by intuition; discriminate
        | [_: context [Sha = Mod] |- _] => assert (Sha = Mod) by intuition; discriminate
        | [_: context [Sha = Inv] |- _] => assert (Sha = Inv) by intuition; discriminate
        | [_: context [Inv = Mod] |- _] => assert (Inv = Mod) by intuition; discriminate
        | [_: context [Inv = Sha] |- _] => assert (Inv = Sha) by intuition; discriminate
        | [_: context [Modi = Shar] |- _] => assert (Modi = Shar) by intuition; discriminate
        | [_: context [Modi = Ow] |- _] => assert (Modi = Ow) by intuition; discriminate
        | [_: context [Modi = Inva] |- _] => assert (Modi = Inva) by intuition; discriminate
        | [_: context [Ow = Shar] |- _] => assert (Ow = Shar) by intuition; discriminate
        | [_: context [Ow = Modi] |- _] => assert (Ow = Modi) by intuition; discriminate
        | [_: context [Ow = Inva] |- _] => assert (Ow = Inva) by intuition; discriminate
        | [_: context [Shar = Modi] |- _] => assert (Shar = Modi) by intuition; discriminate
        | [_: context [Shar = Ow] |- _] => assert (Shar = Ow) by intuition; discriminate
        | [_: context [Shar = Inva] |- _] => assert (Shar = Inva) by intuition; discriminate
        | [_: context [Inva = Modi] |- _] => assert (Inva = Modi) by intuition; discriminate
        | [_: context [Inva = Ow] |- _] => assert (Inva = Ow) by intuition; discriminate
        | [_: context [Inva = Shar] |- _] => assert (Inva = Shar) by intuition; discriminate
      end ].
*)