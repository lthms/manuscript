Section SpecCert.
  Variables (S Ls Lh:  Type).

  Inductive label :=
  | Software
    : Ls -> label
  | Hardware
    : Lh -> label.

  Definition t :=
    S -> label -> S -> Prop.

  Definition _from
             (tr:  S * label * S)
    : S :=
    match tr with (s, _, _) => s end.

  Definition _to
             (tr:  S * label * S)
    : S :=
    match tr with (_, _, s) => s end.

  Definition _labelled
             (tr:  S * label * S)
    : label :=
    match tr with (_, l, _) => l end.

  Definition transition
             (m:  t)
    := { tr | m (_from tr) (_labelled tr) (_to tr) }.

  Definition from
             {m:   t}
             (tr:  transition m)
    : S :=
    match tr with exist _ x _ => _from x end.

  Definition labelled
             {m:   t}
             (tr:  transition m)
    : label :=
    match tr with exist _ x _ => _labelled x end.

  Definition to
             {m:   t}
             (tr:  transition m)
    : S :=
    match tr with exist _ x _ => _to x end.

  Inductive sequence
            (a:  Type)
    : Type :=
  | Ssingleton (x:  a)
    : sequence a
  | Scons (x:    a)
          (rst:  sequence a)
    : sequence a.

  Definition _init
             {m:  t}
             (seq:  sequence (transition m))
    : S :=
    match seq with
    | Ssingleton _ tr
      => from tr
    | Scons _ tr _
      => from tr
    end.

  Fixpoint is_trace
           {m:   t}
           (tr:  sequence (transition m))
    : Prop :=
    match tr with
    | Ssingleton _ _
      => True
    | Scons _ tr rst
      => to tr = _init rst
         /\ is_trace rst
    end.

  Definition trace
             (m:  t) :=
    { tr:  sequence (transition m) | is_trace tr }.

  Definition init
             {m:    t}
             (rho:  trace m)
    : S :=
    _init (proj1_sig rho).

  Fixpoint trans_aux
           {m:    t}
           (rho:  sequence (transition m))
    : transition m -> Prop :=
    fun (tr:  transition m)
    => match rho with
       | Ssingleton _ x
         => tr = x
       | Scons _ x rst
         => tr = x \/ trans_aux rst tr
       end.

  Definition trans
             {m:  t}
             (rho:  trace m)
    : transition m -> Prop :=
    trans_aux (proj1_sig rho).

  Definition security_policy
             (m:  t) :=
    (trace m -> Prop) -> Prop.

  Definition security_property
             (m:  t)
             (prop:  trace m -> Prop)
    : security_policy m :=
    fun (traces:  trace m -> Prop)
    => forall (rho:  trace m), traces rho -> prop rho.

  Definition safety_property
             {m:     t}
             (prop:  transition m -> Prop) :=
    fun (traces:  trace m -> Prop)
    => forall (rho:  trace m),
        traces rho
        -> forall (tr: transition m),
          trans rho tr
          -> prop tr.

  Record HSE
         (m:  t) :=
    { software:  Type
      ; tcb:        software -> Prop
      ; context:    S -> software
      ; inv:        S -> Prop
      ; behaviour:  S -> Ls -> Prop
      ; law_1:      forall (tr:  transition m),
          inv (from tr)
          -> match (labelled tr) with
             | Software l
               => behaviour (from tr) l
             | _
               => True
             end
          -> inv (to tr)
      ; law_2:      forall (tr:  transition m),
          tcb (context (from tr))
          -> match (labelled tr) with
             | Software l
               => behaviour (from tr) l
             | _
               => True
             end
    }.

  Definition compliant_trace
             {m:    t}
             (hse:  HSE m)
             (rho:   trace m)
    : Prop :=
    inv _ hse (init rho)
    /\ forall (tr:  transition m),
      trans rho tr
      -> match (labelled tr) with
         | Software l
           => behaviour _ hse (from tr) l
         | _
           => True
         end.

  Lemma compliant_run_rec
        {m:      t}
        (hse:    HSE m)
        (x:      transition m)
        (rho:    sequence (transition m))
        (Hcons:  is_trace (Scons (transition m) x rho))
        (Hrho:   is_trace rho)
    : compliant_trace hse
                      (exist _ (Scons (transition m) x rho)
                             Hcons)
      -> compliant_trace hse (exist _ rho Hrho).
  Proof.
    intros Hcomp.
    inversion Hcomp as [Hinv Hbehaviour].
    constructor.
    + inversion Hcons as [H0 Hrst].
      unfold init.
      cbn.
      rewrite <- H0.
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
        {m:    t}
        (hse:  HSE m)
    : forall (rho:  trace m),
      compliant_trace hse rho
      -> forall (tr:  transition m),
        trans rho tr
        -> inv _ hse (from tr)
           /\ inv _ hse (to tr).
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
      ++ inversion Hrho as [Hs Hrst].
         apply (IHrho Hrst).
         +++ eapply compliant_run_rec.
             apply Hcomp.
         +++ apply Htrans.
  Qed.

  Definition correct_hse
             {m:    t}
             (hse:  HSE m)
             (p:    security_policy m)
    : Prop :=
    p (compliant_trace hse) .

  Theorem safety_property_correct_hse
          {m:    t}
          (hse:  HSE m)
          (p:    transition m -> Prop)
    : (forall (rho:  trace m)
              (tr:   transition m),
          trans rho tr
          -> inv _ hse (from tr)
          -> (match labelled tr with
              | Software l
                => behaviour _ hse (from tr) l
              | _
                => True
              end)
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
  Section SpecCert.
