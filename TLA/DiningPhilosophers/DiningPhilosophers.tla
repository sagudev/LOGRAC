------------------------------ MODULE DiningPhilosophers ------------------------------

EXTENDS Naturals, Sequences, FiniteSets

(* number of philosophers and forks *)
CONSTANT N
ASSUME N \in Nat /\ N >= 1

Philosophers == 1 .. N
Forks == 1 .. N
States == { "thinking", "hungry", "eating" }

(* state of each philosopher and fork ownership *)
VARIABLES state, forkOwner

-----------------------------------------------------------------------------

Left(i) == i
Right(i) == IF i = N THEN 1 ELSE i + 1

(* Naive *)
(*
FirstFork(i) == Left(i)
SecondFork(i) == Right(i)
*)
(* Resource hierarchy solution (aka. lock-rank) *)
(*
Order of acquiring locks: 1, 2, ..., N
Philosopher i picks up the lower numbered fork first, then the higher numbered one.
*)
FirstFork(i) == IF i # N THEN Left(i) ELSE Right(i)
SecondFork(i) == IF i # N THEN Right(i) ELSE Left(i)

Init ==
  /\ state = [i \in Philosophers |-> "thinking"]
  /\ forkOwner = [f \in Forks |-> 0]

Step(i) ==
  CASE state[i] = "thinking" ->
  state' = [state EXCEPT ![i] = "hungry"] /\ UNCHANGED forkOwner
  [] state[i] = "hungry" /\ forkOwner[FirstFork(i)] = 0 ->
  UNCHANGED state /\ forkOwner' = [forkOwner EXCEPT ![FirstFork(i)] = i]
  [] state[i] = "hungry" /\ forkOwner[FirstFork(i)] = i /\
    forkOwner[SecondFork(i)] = 0 ->
  state' = [state EXCEPT ![i] = "eating"] /\
    forkOwner' = [forkOwner EXCEPT ![SecondFork(i)] = i]
  [] state[i] = "eating" /\ forkOwner[FirstFork(i)] = i /\
    forkOwner[SecondFork(i)] = i ->
  state' = [state EXCEPT ![i] = "thinking"] /\
    forkOwner' =
      [f \in Forks |->
        IF f = FirstFork(i) \/ f = SecondFork(i) THEN 0 ELSE forkOwner[f]
      ]
  [] OTHER-> UNCHANGED << state, forkOwner >>

Next == \E i \in Philosophers: Step(i)

Fairness == \A i \in Philosophers: SF_<< state, forkOwner >>(Step(i))

Spec == Init /\ [][Next]_<< state, forkOwner >> /\ Fairness

-----------------------------------------------------------------------------

TypeOK ==
  /\ state \in [Philosophers -> States]
  /\ forkOwner \in [Forks -> ( Philosophers \cup { 0 } )]

(* If two philosophers share a fork, they cannot eat at the same time. *)
ExclusiveAccess ==
  \A i, j \in Philosophers:
    ( i # j /\
          ( Left(i) = Left(j) \/ Left(i) = Right(j) \/ Right(i) = Left(j) \/
              Right(i) = Right(j)
          )
      ) =>
      ~( ( state[i] = "eating" /\ state[j] = "eating" ) )

(* If a philosopher is hungry, it will eventually eat. *)
Liveness ==
  \A i \in Philosophers: []( state[i] = "hungry" ~> state[i] = "eating" )

(* will be checked by TLC *)
Invariants == TypeOK /\ ExclusiveAccess
Properties == Liveness

-----------------------------------------------------------------------------

THEOREM Spec => []( TypeOK )
PROOF OMITTED
THEOREM Spec => ExclusiveAccess
PROOF OMITTED
THEOREM Spec => Liveness
PROOF OMITTED

=============================================================================