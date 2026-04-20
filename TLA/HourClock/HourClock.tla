----------------------------- MODULE HourClock -----------------------------

(* Hello world of TLA+ - a simple hour clock that cycles through 1..12 *)
EXTENDS Naturals

(* Variables are some kind of state holders *)
VARIABLES hour

-----------------------------------------------------------------------------

(*
indentation is important in TLA+ - it is used to group statements together
/\ TRUE
  \/ TRUE
/\ FALSE == (T \/ T) /\ F

\/ TRUE
\/ TRUE
  /\ FALSE == T \/ (T /\ F)
*)
(* Inital state *)
Init == hour = 1

(* State transitions - actions *)
Next == hour' = IF hour = 12 THEN 1 ELSE hour + 1

(* Weak Fairness: if it always can happen, then it eventually will happen *)
(*                 meaning no infinity stuttering occur (UNCHANGED) *)
Fairness == WF_hour(Next)

(* We put it all together into the system specification *)
Spec == Init /\ [][Next]_hour /\ Fairness

-----------------------------------------------------------------------------

(* Invariants are properties that should hold in all states of the system *)
(* They work only for state predicates (no primes or temporal operators) *)
(* Type invariant *)
TypeOK == hour \in 1 .. 12

(* Asserts that infinitely many <<Next>>_hour steps occur. *)
(*            G (F Next) *)
AlwaysTick == []<><<Next>>_hour
(* Asserts that, for each time n in 1..12, hour infinitely often equals n. *)
(*                             G F (hour = n) for each n in 1..12 *)
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
