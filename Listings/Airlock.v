Inductive door :=
| Open
| Close.

Inductive airlock :=
  Airlock { first_door:   door
          ; second_door:  door
          }.

Inductive action :=
| OpenFirstDoor
| CloseFirstDoor
| OpenSecondDoor
| CloseSecondDoor.

Inductive Transition
  : airlock -> action -> airlock -> Prop :=
| openFirstDoor
  : Transition (Airlock Close Close)
               OpenFirstDoor
               (Airlock Open Close)
| closeFirstDoor (second:  door)
  : Transition (Airlock Open second)
               CloseFirstDoor
               (Airlock Close second)
| openSecondDoor
  : Transition (Airlock Close Close)
               OpenSecondDoor
               (Airlock Close Open)
| closeSecondDoor (first:  door)
  : Transition (Airlock first Open)
               CloseSecondDoor
               (Airlock first Close).

Definition secure_airlock
           (al:  airlock)
  : Prop :=
  first_door al = Close \/ second_door al = Close.

Lemma secure_transition
  : forall (al al':  airlock)
           (act:     action),
    secure_airlock al
    -> Transition al act al'
    -> secure_airlock al'.
Proof.
  intros al al' act Hinv Htrans.
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