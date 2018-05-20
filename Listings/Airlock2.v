Inductive Transition
  : airlock -> action -> airlock -> Prop :=
| openFirstDoor
  : Transition (Airlock Close Close)
               OpenFirstDoor
               (Airlock Open Close)
| closeFirstDoor (second:  door)
  : Transition (Airlock Open second)
               OpenFirstDoor
               (Airlock Close second)
| openSecondDoor
  : Transition (Airlock Close Close)
               OpenSecondDoor
               (Airlock Close Open)
| closeSecondDoor (first:  door)
  : Transition (Airlock first Open)
               OpenSecondDoor
               (Airlock first Close).