Section SpecCert.
  Variables (H Ls Lh:  Type).

  Inductive label :=
  | Software
    : Ls -> label
  | Hardware
    : Lh -> label.

  Definition model
    : Type :=
    H -> label -> H -> Prop.

  Definition from
             (tr:  H * label * H)
    : H :=
    fst (fst tr).

  Definition to
             (tr:  H * label * H)
    : H :=
   snd tr.

  Definition labelled
             (tr:  H * label * H)
    : label :=
    snd (fst tr).

  Definition transition
             (m:  model)
    : Type :=
    { tr | m (from tr) (labelled tr) (to tr) }.

  Notation "'#' x" :=
    (proj1_sig x) (at level 0).

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
    : H :=
    match seq with
    | Ssingleton tr
      => from #tr
    | Scons tr _
      => from #tr
    end.

  Inductive is_trace
            {m:  model}
    : sequence (transition m) -> Prop :=
  | singleton_is_trace (tr:  transition m)
    : is_trace (Ssingleton tr)
  | step_is_trace (tr:   transition m)
                  (rho:  sequence (transition m))
                  (Heq:  to #tr = init rho)
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
             (prop:  transition m -> Prop)
    : security_policy m :=
    fun (traces:  trace m -> Prop)
    => forall (rho:  trace m),
        traces rho
        -> forall (tr: transition m),
          trans #rho tr
          -> prop tr.

  Definition if_software
             (l:  label)
             (P:  Ls -> Prop)
    : Prop :=
    match l with
    | Software l
      => P l
    | _
      => True
    end.

  Record HSE
         (m:  model) :=
    { software:      Type
    ; tcb:           software -> Prop
    ; context:       H -> software
    ; hardware_req:  H -> Prop
    ; software_req:  H -> Ls -> Prop
    ; law_1:         forall (tr:  transition m),
        hardware_req (from #tr)
        -> if_software (labelled #tr)
                       (software_req (from #tr))
        -> hardware_req (to #tr)
    ; law_2:         forall (tr:  transition m),
        ~ tcb (context (from #tr))
        -> if_software (labelled #tr)
                       (software_req (from #tr))
    }.

  Arguments software [m] (_).
  Arguments tcb [m] (_).
  Arguments context [m] (_ _).
  Arguments hardware_req [m] (_ _).
  Arguments software_req [m] (_ _ _).

  Definition compliant_trace
             {m:    model}
             (hse:  HSE m)
             (rho:   trace m)
    : Prop :=
    hardware_req hse (init #rho)
    /\ forall (tr:  transition m),
      trans #rho tr
      -> if_software (labelled #tr)
                     (software_req hse (from #tr)).

  Lemma compliant_trace_rec
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
    inversion Hcomp as [Hhard_req Hsoftware_req].
    constructor.
    + inversion Hcons; subst.
      cbn.
      rewrite <- Heq.
      apply law_1.
      ++ apply Hhard_req.
      ++ apply Hsoftware_req.
         left; reflexivity.
    + intros tr Htrans.
      apply Hsoftware_req.
      right.
      exact Htrans.
  Qed.

  Lemma hse_inv_enforcement
        {m:    model}
        (hse:  HSE m)
    : forall (rho:  trace m),
      compliant_trace hse rho
      -> forall (tr:  transition m),
        trans #rho tr
        -> hardware_req hse (from #tr)
           /\ hardware_req hse (to #tr).
  Proof.
    induction rho as [rho Hrho].
    induction rho.
    + intros Hcomp.
      inversion Hcomp as [Hhard_req Hsoftware_req].
      cbn in Hhard_req.
      cbn in Hsoftware_req.
      intros tr Htrans.
      split.
      ++ cbn in Htrans.
         rewrite Htrans.
         exact Hhard_req.
      ++ apply law_1.
         +++ cbn in Htrans.
             rewrite Htrans.
             exact Hhard_req.
         +++ apply Hsoftware_req.
             exact Htrans.
    + intros Hcomp.
      inversion Hcomp as [Hhard_req Hsoftware_req].
      cbn in Hhard_req.
      cbn in Hsoftware_req.
      intros tr Htrans.
      cbn in Htrans.
      destruct Htrans as [Htrans|Htrans].
      ++ rewrite Htrans.
         split; [exact Hhard_req |].
         apply law_1.
         exact Hhard_req.
         apply Hsoftware_req.
         left; reflexivity.
      ++ inversion Hrho; subst.
         apply (IHrho Hrec).
         +++ eapply compliant_trace_rec.
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
          trans #rho tr
          -> hardware_req hse (from #tr)
          -> if_software (labelled #tr)
                         (software_req hse (from #tr))
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

  Inductive software_stack
  : Type :=
  | BIOS
    : software_stack
  | OS
    : software_stack
  | App (n:  nat)
    : software_stack.

  Variables (ss_context:  H -> software_stack)
            (ss_fetched:  H -> label -> (software_stack -> Prop)).

  Inductive stack_ge
    : software_stack -> software_stack -> Prop :=
  | stack_ge_refl (x:  software_stack)
    : stack_ge x x
  | bios_bottom (x:  software_stack)
    : stack_ge BIOS x
  | os_apps (n:  nat)
    : stack_ge OS (App n).

  Require Import Coq.Arith.PeanoNat.
  Require Import Coq.Logic.Decidable.
  Require Coq.Logic.Classical_Prop.

  Definition stack_ge_decidable
           (x y:  software_stack)
    : stack_ge x y \/ ~ stack_ge x y.
    refine (
        match x, y with
        | BIOS, _
        | OS, OS
        | OS, App _
          => _
        | _, _
          => _
        end
      );
      try (left; constructor).
    + right; intros Hge; inversion Hge.
    + induction y.
      ++ right; intros Hge; inversion Hge.
      ++ right; intros Hge; inversion Hge.
      ++ destruct (Nat.eq_dec n n0); subst.
         +++ left; constructor.
         +++ right; intros Hge; inversion Hge.
             subst.
             apply n1.
             reflexivity.
  Qed.

  Lemma stack_ge_asym
    : forall (x y:  software_stack),
      x <> y -> stack_ge x y -> ~ stack_ge y x.
  Proof.
    induction x;
      intros y Hneq Hge Hnge;
      inversion Hnge;
      subst;
      try (apply Hneq; reflexivity);
      try (inversion Hge).
  Qed.

  Lemma stack_ge_trans
    : forall (x y z:  software_stack),
      stack_ge x y -> stack_ge y z -> stack_ge x z.
  Proof.
    induction x;
      intros y z Hge1 Hge2;
      inversion Hge1;
      inversion Hge2;
      subst;
      try constructor;
      try discriminate.
  Qed.

  Definition code_injection
             {m:    model}
             (tr:   transition m)
             (x y:  software_stack)
    : Prop :=
    ss_fetched (from #tr) (labelled #tr) y
    /\ ss_context (from #tr) = y.

  Definition code_injection_policy
             {m:   model}
             (tr:  transition m)
    : Prop :=
    forall (x y:  software_stack),
      code_injection tr x y
      -> stack_ge x y.

  Corollary code_injection_policy_aux
            {m:   model}
            (tr:  transition m)
    : code_injection_policy tr
      <-> forall (x y:  software_stack),
        ~ stack_ge x y -> ~ code_injection tr x y.
  Proof.
    split.
    + intros Hiso x y Hnge Htamper.
      unfold code_injection_policy in Hiso.
      apply Hiso in Htamper.
      apply Hnge.
      exact Htamper.
    + intros Hc x y.
      apply contrapositive.
      ++ apply stack_ge_decidable.
      ++ intros Hneq.
         apply Hc.
         exact Hneq.
  Qed.

  Definition is_tcb
             (U:  software_stack -> Prop)
             (x:  software_stack)
    : Prop :=
    ~ U x /\ forall (u:  software_stack), U u -> stack_ge x u.

  Definition constrain_to_isolation
             {m:   model}
             (U:   software_stack -> Prop)
             (tr:  transition m)
    : Prop :=
    forall (u y:  software_stack),
      U u
      -> code_injection tr u y
      -> stack_ge u y.

  Inductive os_only
    : software_stack -> Prop :=
  | OS_only
    : os_only OS.

  Inductive apps_only
    : software_stack -> Prop :=
  | Apps_only (n:  nat)
    : apps_only (App n).

  Definition compatible_hse
             {m:  model}
             (hse1 hse2:  HSE m)
    : Prop :=
    software hse1 = software hse2
    /\ forall x H,
      context hse2 x = eq_rect _ id (context hse1 x) _ H.

  Definition HSE_cap
             {m:            model}
             (hse1 hse2:    HSE m)
             (Hcompatible:  compatible_hse hse1 hse2)
    : HSE m.
    refine ({| software := software hse1
             ; context  := context hse1
             ; tcb := fun x
                      => tcb hse1 x \/ tcb hse2 (eq_rect _ id x _ _)
             ; hardware_req := fun x
                               => hardware_req hse1 x
                                  /\ hardware_req hse2 x
             ; software_req := fun x l
                            => software_req hse1 x l /\ software_req hse2 x l
             |}).
    + intros tr [Hi1 Hi2] Hsoft.
      split; apply law_1; [exact Hi1 | idtac | exact Hi2 | idtac];
         induction tr as [tr Htr]; induction tr as [[h l] h'];
         induction l; auto;
         apply Hsoft.
    + intros tr Htcb.
      apply Classical_Prop.not_or_and in Htcb.
      destruct Htcb as [Ht1 Ht2].
      inversion Hcompatible as [Hsoftware Hcontext].
      rewrite <- Hcontext in Ht2.
      apply law_2 in Ht1.
      apply law_2 in Ht2.
      induction tr as [tr Htr];
        induction tr as [[h l] h'];
        induction l; auto.
      unfold proj1_sig.
      split.
      ++ apply Ht1.
      ++ apply Ht2.
      Unshelve.
      apply Hcompatible.
  Defined.

  Lemma compliant_trace_intersec_sketches
        (P P' R Q Q':  Prop)
    : (P /\ P') /\ (R -> Q /\ Q')
      <-> (P /\ (R -> Q)) /\ (P' /\ (R -> Q')).
  Proof.
    split.
    + intros [[Hp Hp'] Hr].
      split.
      ++ split.
         +++ exact Hp.
         +++ intros Hr'.
             apply Hr in Hr'.
             apply Hr'.
      ++ split.
         +++ exact Hp'.
         +++ intros Hr'.
             apply Hr in Hr'.
             apply Hr'.
    + intros [[Hp Hq] [Hp' Hq']].
      split.
      ++ split; assumption.
      ++ intros Hr.
         auto.
  Qed.

  Lemma compliant_trace_intersec_intersec_compliant_trace
        {m:      model}
        (hse_1:  HSE m)
        (hse_2:  HSE m)
        (Hcomp:  compatible_hse hse_1 hse_2)
        (rho:    trace m)
    : compliant_trace (HSE_cap hse_1 hse_2 Hcomp) rho
      -> compliant_trace hse_1 rho /\ compliant_trace hse_2 rho.
  Proof.
    intros Hct.
    unfold compliant_trace in Hct.
    unfold HSE_cap in Hct.
    cbn in Hct.
    split.
    + constructor.
      ++ apply Hct.
      ++ intros tr Htr.
         destruct Hct as [_H Hct].
         assert (Hres:  if_software (labelled #tr)
                                    (fun l : Ls =>
                                       software_req hse_1 (from #tr) l
                                       /\ software_req hse_2 (from #tr) l))
           by (apply Hct; exact Htr).
         induction tr as [tr _H2]; induction tr as [[h l] h'].
         induction l; auto.
         cbn in *.
         apply Hres.
    + constructor.
      ++ apply Hct.
      ++ intros tr Htr.
         destruct Hct as [_H Hct].
         assert (Hres:  if_software (labelled #tr)
                                    (fun l : Ls =>
                                       software_req hse_1 (from #tr) l
                                       /\ software_req hse_2 (from #tr) l))
           by (apply Hct; exact Htr).
         induction tr as [tr _H2]; induction tr as [[h l] h'].
         induction l; auto.
         cbn in *.
         apply Hres.
  Qed.

  Lemma intersec_compliant_trace_compliant_trace_intersec
        {m:      model}
        (hse_1:  HSE m)
        (hse_2:  HSE m)
        (Hcomp:  compatible_hse hse_1 hse_2)
        (rho:    trace m)
    : compliant_trace hse_1 rho /\ compliant_trace hse_2 rho
      -> compliant_trace (HSE_cap hse_1 hse_2 Hcomp) rho.
  Proof.
    intros [H1 H2].
    constructor.
    + unfold HSE_cap.
      cbn.
      split; [apply H1|apply H2].
    + intros tr Htrans.
      assert (Hb1:  if_software (labelled #tr)
                                (software_req hse_1 (from #tr)))
        by (apply H1; exact Htrans).
      assert (Hb2:  if_software (labelled #tr)
                                (software_req hse_2 (from #tr)))
        by (apply H2; exact Htrans).
      induction tr as [tr _H3]; induction tr as [[h l] h'].
      induction l; cbn in *; auto.
  Qed.

  Definition bios_code_injection_policy
             {m:         model}
             (tr:  transition m)
    : Prop :=
    forall (x:  software_stack),
      code_injection tr x BIOS
      -> x = BIOS.

  Definition os_code_injection_policy
             {m:         model}
             (tr:  transition m)
    : Prop :=
    forall (x:  software_stack)
           (n:  nat),
      code_injection tr (App n) x
      -> x = App n.

  Theorem constrain_everyone
          {m:         model}
          (hse_bios:  HSE m)
          (hse_os:    HSE m)
          (Hcomp:     compatible_hse hse_bios hse_os)
    : correct_hse hse_bios
                  (safety_property bios_code_injection_policy)
      -> correct_hse hse_os
                     (safety_property os_code_injection_policy)
      -> correct_hse (HSE_cap hse_bios hse_os Hcomp)
                     (safety_property code_injection_policy).
  Proof.
    intros Hbios Hos rho Hct tr Htrans.
    apply compliant_trace_intersec_intersec_compliant_trace in Hct.
    inversion Hct as [Hrb Hro].
    intros x y Htamper.
    unfold correct_hse, safety_property in *.
    unfold bios_code_injection_policy, os_code_injection_policy in *.
    induction x.
    + constructor.
    + induction y.
      ++ apply (Hbios rho Hrb tr Htrans) in Htamper.
         discriminate.
      ++ constructor.
      ++ constructor.
    + apply (Hos rho Hro tr Htrans) in Htamper.
      rewrite Htamper.
      constructor.
  Qed.
End SpecCert.
