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