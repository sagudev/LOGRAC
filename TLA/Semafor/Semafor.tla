------------------------------ MODULE Semafor ------------------------------
(* aka. Traffic Light 🚦*)
EXTENDS TLC

VARIABLE light

---------------------------------------------------------------------------------

States == { "Red", "Yellow", "Green" }

Init == light = "Red"

Next ==
  \/ light = "Red" /\ light' = "Yellow"
  \/ light = "Yellow" /\ light' = "Green"
  \/ light = "Green" /\ light' = "Red"

Spec == Init /\ [][Next]_<< light >> /\ WF_<< light >>(Next)

-----------------------------------------------------------------------------

TypeOK == light \in States

EventuallyGreen == []<>( light = "Green" )

YellowLeadsToGreen == []( light = "Yellow" ~> light = "Green" )

(* will be checked by TLC *)
Invariants == TypeOK
Properties == EventuallyGreen /\ YellowLeadsToGreen

-----------------------------------------------------------------------------

THEOREM Spec => []( TypeOK )
PROOF OMITTED
THEOREM Spec => EventuallyGreen
PROOF OMITTED
THEOREM Spec => YellowLeadsToGreen
PROOF OMITTED

=============================================================================