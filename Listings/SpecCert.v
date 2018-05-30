Section SpecCert.
  Variables (S Ls Lh:  Type).

  Inductive label :=
  | Software
    : Ls -> label
  | Hardware
    : Lh -> label.

  Definition model
    : Type :=
    S -> label -> S -> Prop.

  Definition from
             (tr:  S * label * S)
    : S :=
    fst (fst tr).

  Definition to
             (tr:  S * label * S)
    : S :=
   snd tr.

  Definition labelled
             (tr:  S * label * S)
    : label :=
    snd (fst tr).

  Definition transition
             (m:  model)
    : Type :=
    { tr | m (from tr) (labelled tr) (to tr) }.

  Notation "'[' x ']'" :=
    (proj1_sig x).

  Arguments exist [_ _] (_ _).

  Inductive sequence
            (a:  Type)
    : Type :=
  | Ssingleton (x:  a)
    : sequence a
  | Scons (x:    a)
          (rst:  sequence a)
    : sequence a.

  Arguments Ssingleton [a] (x).
  Arguments Scons [a] (x rst).

  Definition init
             {m:  model}
             (seq:  sequence (transition m))
    : S :=
    match seq with
    | Ssingleton tr
      => from [tr]
    | Scons tr _
      => from [tr]
    end.

  Inductive is_trace
            {m:  model}
    : sequence (transition m) -> Prop :=
  | singleton_is_trace (tr:  transition m)
    : is_trace (Ssingleton tr)
  | step_is_trace (tr:   transition m)
                  (rho:  sequence (transition m))
                  (Heq:  to [tr] = init rho)
                  (Hrec:  is_trace rho)
    : is_trace (Scons tr rho).

  Definition trace
             (m:  model)
    : Type :=
    { tr:  sequence (transition m) | is_trace tr }.

  Fixpoint trans
           {m:    model}
           (rho:  sequence (transition m))
    : transition m -> Prop :=
    fun (tr:  transition m)
    => match rho with
       | Ssingleton x
         => tr = x
       | Scons x rst
         => tr = x \/ trans rst tr
       end.

  Definition security_policy
             (m:  model) :=
    (trace m -> Prop) -> Prop.

  Definition security_property
             (m:  model)
             (prop:  trace m -> Prop)
    : security_policy m :=
    fun (traces:  trace m -> Prop)
    => forall (rho:  trace m), traces rho -> prop rho.

  Definition safety_property
             {m:     model}
             (prop:  transition m -> Prop) :=
    fun (traces:  trace m -> Prop)
    => forall (rho:  trace m),
        traces rho
        -> forall (tr: transition m),
          trans [rho] tr
          -> prop tr.

  Definition if_software
             (l:  label)
             (P:  Ls -> Prop)
    : Prop :=
    match l with
    | Software l
      => P l
    | Hardware _
      => True
    end.

  Record HSE
         (m:  model) :=
    { software:   Type
    ; tcb:        software -> Prop
    ; context:    S -> software
    ; inv:        S -> Prop
    ; behaviour:  S -> Ls -> Prop
    ; law_1:      forall (tr:  transition m),
        inv (from [tr])
        -> if_software (labelled [tr])
                       (behaviour (from [tr]))
        -> inv (to [tr])
    ; law_2:      forall (tr:  transition m),
        tcb (context (from [tr]))
        -> if_software (labelled [tr])
                       (behaviour (from [tr]))
    }.

  Arguments software [m] (_).
  Arguments tcb [m] (_).
  Arguments context [m] (_ _).
  Arguments inv [m] (_ _).
  Arguments behaviour [m] (_ _ _).

  Definition compliant_trace
             {m:    model}
             (hse:  HSE m)
             (rho:   trace m)
    : Prop :=
    inv hse (init [rho])
    /\ forall (tr:  transition m),
      trans [rho] tr
      -> if_software (labelled [tr])
                     (behaviour hse (from [tr])).

  Lemma compliant_run_rec
        {m:      model}
        (hse:    HSE m)
        (x:      transition m)
        (rho:    sequence (transition m))
        (Hcons:  is_trace (Scons x rho))
        (Hrho:   is_trace rho)
    : compliant_trace hse (exist (Scons x rho) Hcons)
      -> compliant_trace hse (exist rho Hrho).
  Proof.
    intros Hcomp.
    inversion Hcomp as [Hinv Hbehaviour].
    constructor.
    + inversion Hcons; subst.
      cbn.
      rewrite <- Heq.
      apply law_1.
      ++ apply Hinv.
      ++ apply Hbehaviour.
         left; reflexivity.
    + intros tr Htrans.
      apply Hbehaviour.
      right.
      exact Htrans.
  Qed.

  Lemma hse_inv_enforcement
        {m:    model}
        (hse:  HSE m)
    : forall (rho:  trace m),
      compliant_trace hse rho
      -> forall (tr:  transition m),
        trans [rho] tr
        -> inv hse (from [tr])
           /\ inv hse (to [tr]).
  Proof.
    induction rho as [rho Hrho].
    induction rho.
    + intros Hcomp.
      inversion Hcomp as [Hinv Hbehaviour].
      cbn in Hinv.
      cbn in Hbehaviour.
      intros tr Htrans.
      split.
      ++ cbn in Htrans.
         rewrite Htrans.
         exact Hinv.
      ++ apply law_1.
         +++ cbn in Htrans.
             rewrite Htrans.
             exact Hinv.
         +++ apply Hbehaviour.
             exact Htrans.
    + intros Hcomp.
      inversion Hcomp as [Hinv Hbehaviour].
      cbn in Hinv.
      cbn in Hbehaviour.
      intros tr Htrans.
      cbn in Htrans.
      destruct Htrans as [Htrans|Htrans].
      ++ rewrite Htrans.
         split; [exact Hinv |].
         apply law_1.
         exact Hinv.
         apply Hbehaviour.
         left; reflexivity.
      ++ inversion Hrho; subst.
         apply (IHrho Hrec).
         +++ eapply compliant_run_rec.
             apply Hcomp.
         +++ apply Htrans.
  Qed.

  Definition correct_hse
             {m:    model}
             (hse:  HSE m)
             (p:    security_policy m)
    : Prop :=
    p (compliant_trace hse) .

  Theorem safety_property_correct_hse
          {m:    model}
          (hse:  HSE m)
          (p:    transition m -> Prop)
    : (forall (rho:  trace m)
              (tr:   transition m),
          trans [rho] tr
          -> inv hse (from [tr])
          -> if_software (labelled [tr])
                         (behaviour hse (from [tr]))
          -> p tr)
      -> correct_hse hse (safety_property p).
  Proof.
    intros Hreq.
    unfold correct_hse, safety_property.
    intros rho Hcomp tr Htrans.
    apply (Hreq rho tr Htrans).
    + eapply hse_inv_enforcement.
      ++ exact Hcomp.
      ++ exact Htrans.
    + apply Hcomp.
      exact Htrans.
  Qed.
End SpecCert.
