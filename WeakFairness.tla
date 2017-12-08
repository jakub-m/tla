---------------------------- MODULE WeakFairness ----------------------------

EXTENDS Naturals
(* Use temporal operators and weak fairness with multiple processes. *)

CONSTANTS Process, InitValue, EndValue
VARIABLE pc         \* State of each process.

Init ==
    /\ pc = [proc \in Process |-> InitValue]

Next ==
    \/ \E proc \in Process:
        IF pc[proc] < EndValue
        THEN pc' = [pc EXCEPT ![proc] = pc[proc] + 1]
        ELSE pc' = pc
    \/ UNCHANGED <<pc>>

Spec ==
    /\ Init
    /\ [][Next]_<<pc>>
    /\ WF_<<pc>>(Next)  \* Weak Fairness.

(* Check that each process should eventually reach all the values. This fails without Weak Fairness - e.g. one process can stutter. *)
CheckEndValue == \A proc \in Process: \A s \in InitValue..EndValue: <>(pc[proc] = s)

=============================================================================
