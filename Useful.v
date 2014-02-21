Require Import Arith Omega.

Ltac destructAll :=
  match goal with
    | [|- context [match ?P with _ => _ end] ] => destruct P
    | [_:context [match ?P with _ => _ end] |- _] => destruct P
  end.

Section StrongInd1.
  Context {P: nat -> Type}.
  Hypothesis case_0: P 0.
  Hypothesis case_n: forall {t}, (forall ti, ti <= t -> P ti) -> P (S t).

  Theorem strong_ind' t: P t.
  Proof.
    assert (q0: forall ti, ti <= 0 -> P ti) by 
        (intros ti ti_le_0; assert (rew: ti = 0) by omega; rewrite rew; assumption).
    assert (qIHt: forall t, (forall ti, ti <= t -> P ti) -> (forall ti, ti <= S t -> P ti)).
    intros t0 lt_t0.
    specialize (case_n t0 lt_t0).
    intros ti ti_le_S_t0.
    pose proof (le_lt_eq_dec ti (S t0) ti_le_S_t0) as options.
    destruct options as  [hyp|new].
    firstorder.
    rewrite new.
    assumption.
    assert (Hyp: forall t, (forall ti, ti <= t -> P ti)) by (
                                                            induction t0; firstorder).
    specialize (Hyp t t).
    assert (fct: t <= t) by omega.
    firstorder.
  Qed.
End StrongInd1.

Section StrongInd2.
  Context {P: nat -> Type}.
  Hypothesis case_n: forall {t}, (forall ti, ti < t -> P ti) -> P t.
  Theorem strong_ind t: P t.
  Proof.
    assert (case0: P 0).
    specialize (case_n 0).
    assert (ez: forall ti, ti < 0 -> P ti) by (intros ti cond; assert False by omega;
                                               intuition).
    apply (case_n ez).
    assert (casen: forall {t}, (forall ti, ti <= t -> P ti) -> P (S t)).
    intros t0 cond.
    assert (cond2: forall ti, ti < S t0 -> P ti) by (intros ti cond2;
                                                     assert (ti <= t0) by omega;
                                                     intuition).
    apply (case_n (S t0) cond2).
    apply (strong_ind' case0 casen t).
  Qed.
End StrongInd2.

