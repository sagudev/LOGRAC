----------------------------- MODULE Mutex -----------------------------
EXTENDS TLAPS

VARIABLES p1, p2

------------------------------------------------------------------------


(*
/\ TRUE
  \/ TRUE
/\ FALSE == (T \/ T) /\ F

\/ TRUE
\/ TRUE
  /\ FALSE == T \/ (T /\ F)
*)
Init ==
  /\ p1 = "n1"
  /\ p2 = "n2"

ChangeP1 == CASE p1 = "n1" -> p1' = "t1"
            [] p1 = "c1" -> p1' = "n1"
            [] p1 = "t1" /\ p2 # "c2" -> p1' = "c1"
            [] OTHER-> p1' = p1

Next1 == ChangeP1 /\ UNCHANGED p2

ChangeP2 == CASE p2 = "n2" -> p2' = "t2"
            [] p2 = "c2" -> p2' = "n2"
            [] p2 = "t2" /\ p1 # "c1" -> p2' = "c2"
            [] OTHER-> p2' = p2

Next2 == ChangeP2 /\ UNCHANGED p1

Next == Next1 \/ Next2

(* System specification *)
Spec ==
  /\ Init
  /\ [][Next]_<< p1, p2 >>
  (*tuple of p1, p2*)
  /\ SF_<< p1, p2 >>(Next1)
  /\ SF_<< p1, p2 >>(Next2)

------------------------------------------------------------------------

(* Mutual exclusion invariant - holds for all states *)
(* Only works for state predicates (one with no primes or temporal operators) *)
(* or as we called it safety property *)
(*                  G ( ¬(c1 ∧ c2) ) *)
MutualExclusion == ~( p1 = "c1" /\ p2 = "c2" )

(*           G ((t1 => F c1) /\ (t2 => F c2))*)
Liveness ==
  /\ []( p1 = "t1" => <>( p1 = "c1" ) )
  /\ []( p2 = "t2" => <>( p2 = "c2" ) )

(* will be checked by TLC *)
Invariants == MutualExclusion
Properties == Liveness

----------------------------------------------------------------------------

THEOREM Spec => []( MutualExclusion )
PROOF
<1>1. Init => MutualExclusion BY DEF Init , MutualExclusion
<1>2. MutualExclusion /\ [Next]_<< p1, p2 >> => MutualExclusion'
  BY DEF Next , Next1 , Next2 , ChangeP1 , ChangeP2 , MutualExclusion
<1>3. Spec => []( MutualExclusion ) BY <1>1 , <1>2 , PTL DEF Spec
<1> QED BY <1>3

THEOREM Spec => Liveness
PROOF OMITTED

=============================================================================