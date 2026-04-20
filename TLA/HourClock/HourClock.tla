----------------------------- MODULE HourClock -----------------------------
(* Hello world of TLA+ - a simple hour clock that cycles through 1..12 *)
EXTENDS Naturals, TLAPS

VARIABLES hour
-----------------------------------------------------------------------------

(* Inital state *)
Init == hour = 1

(* Next-state relation - actions *)
Next == hour' = IF hour = 12 THEN 1 ELSE hour + 1

(* We put it all together into the system specification *)
(* + Weak Fairness: if it always can happen, then it eventually will happen *)
(*                 meaning no infinity stuttering occur (UNCHANGED)*)
Spec == Init /\ [][Next]_hour /\ WF_hour(Next)

-----------------------------------------------------------------------------

(* Type invariant *)
TypeOK == hour \in 1 .. 12

(* Asserts that infinitely many <<Next>>_hour steps occur. *)
(*            G F Next*)
AlwaysTick == []<><<Next>>_hour
(* Asserts that, for each time n in 1..12, hour infinitely often equals n. *)
(*            G F (hour = n) for each n in 1..12 *)
AllTimes == \A n \in 1 .. 12: []<>( hour = n )

(* will be checked by TLC *)
Invariants == TypeOK
Properties == AlwaysTick /\ AllTimes

-----------------------------------------------------------------------------

THEOREM Spec => []( TypeOK )
PROOF OMITTED
THEOREM Spec => AlwaysTick
PROOF OMITTED
THEOREM Spec => AllTimes
PROOF OMITTED

=============================================================================
