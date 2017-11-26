------------------------ MODULE DieHardWaterProblem ------------------------

EXTENDS Naturals

(*
http://puzzles.nigelcoldwell.co.uk/twentytwo.htm

You have a 3 and a 5 litre water container, each container has no markings
except for that which gives you it's total volume. You also have a running tap.
You must use the containers and the tap in such away as to exactly measure out
4 litres of water. How is this done?  Can you generalise the form of your
answer?
*)

VARIABLES
    smallJug, largeJug

vars == <<smallJug, largeJug>>

Fill(jug, capacity) == jug' = capacity

Empty(jug) == jug' = 0

Pour(fromJug, toJug, toCapacity) ==
    LET space == toCapacity - toJug IN
    IF space >= fromJug THEN
        /\ fromJug' = 0
        /\ toJug' = toJug + fromJug
    ELSE
        /\ fromJug' = fromJug - space
        /\ toJug' = toCapacity

Init ==
    /\ smallJug = 0
    /\ largeJug = 0

Next ==
    \/  /\ Fill(smallJug, 3)
        /\ UNCHANGED <<largeJug>>
    \/  /\ Fill(largeJug, 5)
        /\ UNCHANGED <<smallJug>>
    \/  /\ Empty(smallJug)
        /\ UNCHANGED <<largeJug>>
    \/  /\ Empty(largeJug)
        /\ UNCHANGED <<smallJug>>
    \/ Pour(smallJug, largeJug, 5)
    \/ Pour(largeJug, smallJug, 3)
    \/ UNCHANGED <<smallJug, largeJug>>

Spec == Init /\ [][Next]_vars

TypeInvariant ==
    /\ smallJug \in 0..3
    /\ largeJug \in 0..5

(* Use this as invariant to terminate when a solution is found. *)
Termination == largeJug /= 4

=============================================================================
