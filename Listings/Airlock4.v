Lemma secure_transition
  : forall (before after:  airlock)
           (act:           action),
    secure_airlock before
    -> Transition before act after
    -> secure_airlock after.
Proof.
  intros Hinv Htrans.
  induction act;
    inversion Htrans;
    subst;
    unfold secure_airlock;
    cbn.
  + right; reflexivity.
  + left; reflexivity.
  + left; reflexivity.
  + right; reflexivity.
Qed.