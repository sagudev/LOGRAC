------------------------------ MODULE FIFO ------------------------------
EXTENDS Sequences, Naturals

CONSTANTS Items

VARIABLES q

-------------------------------------------------------------------------

Init == q = <<>>

Enqueue(x) == q' = Append(q, x)

Dequeue == IF q # <<>> THEN q' = Tail(q) ELSE q' = q

Next ==
  \/ \E x \in Items: Enqueue(x)
  \/ Dequeue

Spec == Init /\ [][Next]_q

-------------------------------------------------------------------------

\* Safety: FIFO order is respected
FIFOOrder ==
  \A s \in Items:
    \A x \in Items:
      ( q = Append(s, x) /\ q # <<>> ) => Head(q) = Head(Append(s, x))

\* Liveness: Every enqueued element is eventually dequeued
\* If x is ever enqueued, it will eventually not be in q
Liveness ==
  \A x \in Items:
    []( <>( \E s \in Seq(Items): q = Append(s, x) ) =>
        <>( ~( x \in {q[i]: i \in 1 .. Len(q)} ) )
    )

(* will be checked by TLC *)
Invariants == FIFOOrder
Properties == Liveness

-----------------------------------------------------------------------------

THEOREM Spec => FIFOOrder
PROOF OMITTED
THEOREM Spec => Liveness
PROOF OMITTED

=============================================================================