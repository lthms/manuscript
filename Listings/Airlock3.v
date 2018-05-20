Definition secure_airlock
           (al:  airlock)
  : Prop :=
  first_door al = Close \/ second_door al = Close.