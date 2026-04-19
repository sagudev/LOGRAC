----------------------------- MODULE MutexMany -----------------------------

EXTENDS TLAPS, Naturals, Sequences

CONSTANT N
ASSUME N \in Nat /\ N > 0
VARIABLE p

----------------------------------------------------------------------------

States == { "n", "t", "c" }

Proc == 1 .. N

(* Type invariant *)
TypeOK == p \in [Proc -> States]

Init == TypeOK /\ \A i \in Proc: p[i] = "n"

Step(i) ==
  (* if p_i = n keep all p except p[i], which should become "t"*)
  CASE p[i] = "n" -> p' = [p EXCEPT ![i] = "t"]
  [] p[i] = "c" -> p' = [p EXCEPT ![i] = "n"]
  [] p[i] = "t" /\ ( \A j \in Proc \ { i }: p[j] # "c" ) ->
  p' = [p EXCEPT ![i] = "c"]
  [] OTHER-> p' = p

(* move one processor one step forward *)
Next == \E i \in Proc: Step(i)

(* System specification *)
Spec ==
  /\ Init
  /\ [][Next]_p
  /\ \A i \in Proc: SF_p(Step(i))

---------------------------------------------------------------------------

(* Mutual exclusion invariant (safety property) *)
MutualExclusion == \A i, j \in Proc: i # j => ~( p[i] = "c" /\ p[j] = "c" )

(* Liveness property: if a process is trying, it will eventually enter critical section *)
Liveness == \A i \in Proc: []( p[i] = "t" => <>( p[i] = "c" ) )

(* will be checked by TLC *)
Invariants == MutualExclusion /\ TypeOK
Properties == Liveness

-----------------------------------------------------------------------------

THEOREM Spec => []( MutualExclusion )
PROOF OMITTED
THEOREM Spec => Liveness
PROOF OMITTED
=============================================================================