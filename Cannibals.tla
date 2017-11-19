----------------------------- MODULE Cannibals -----------------------------

EXTENDS TLC, Naturals

(*
Illustration of "Missionaries and cannibals" problem.

https://en.wikipedia.org/wiki/Missionaries_and_cannibals_problem

Three missionaries and three cannibals must cross a river using a boat which
can carry at most two people, under the constraint that, for both banks, if
there are missionaries present on the bank, they cannot be outnumbered by
cannibals (if they were, the cannibals would eat the missionaries). The boat
cannot cross the river by itself with no people on board.

The specification has a flaw. It doesn't allow "swapping whole crew" of the boat,
which leads to a suboptimal solution. 
*)

PeopleCount(P) == P.cann + P.miss

(* --algorithm cannibals_and_missionaries

\* Initially all missionaries and cannibals are on the left bank.
variables leftbank = [miss |-> 3, cann |-> 3],
          rightbank = [miss |-> 0, cann |-> 0],
          boat = [miss |-> 0 , cann |-> 0];

begin
while TRUE do

\* End condition: all on the right bank.
assert ~( /\ PeopleCount(leftbank) = 0
          /\ PeopleCount(boat) = 0
          /\ PeopleCount(rightbank) = 6 ); 

    either
        \* If there is space on the boat and someone on the left bank, move to boat.
        if PeopleCount(boat) < 2 then
            either
                if /\ leftbank.miss > 0
                   /\ leftbank.miss > leftbank.cann
                then
                    leftbank.miss := leftbank.miss - 1;
                    boat.miss := boat.miss + 1;
                end if
            or
                if /\ leftbank.cann > 0
                   /\ leftbank.miss >= leftbank.cann
                then
                   leftbank.cann := leftbank.cann - 1;
                   boat.cann := boat.cann + 1;
               end if
            end either;
        end if
    or
        \* Disembark to the right bank.
        if /\ PeopleCount(boat) > 0 \* Disembark if there is anyone on the boat.
           \* Boat cannot be empty, if there is still anyone on any side of the river.             
           /\ (PeopleCount(leftbank) > 0 /\ PeopleCount(rightbank) > 0) => PeopleCount(boat) > 1
        then
            either
                if /\ boat.miss > 0 \* Check if missionaries are safe.
                   /\ rightbank.miss >= rightbank.cann
                then
                    boat.miss := boat.miss - 1;
                    rightbank.miss := rightbank.miss + 1
                end if
            or
                if /\ boat.cann > 0 \* Check if missionaries are safe.
                   /\ rightbank.miss > rightbank.cann
                then
                    boat.cann := boat.cann - 1;
                    rightbank.cann := rightbank.cann + 1;
                end if
            end either;
        end if
    end either;

end while;

end algorithm; *)

\* BEGIN TRANSLATION
\* END TRANSLATION

(* Invariants to be used when running the model. *)

(* If there are more cannibals than missionaries, then, well... *)
CannibalismInvariant == /\ leftbank.miss  > 0 => leftbank.miss  >= leftbank.cann
                        /\ rightbank.miss > 0 => rightbank.miss >= rightbank.cann
                        
(* The boat cannot cross the river with noone onboard. *)                        
BoatInvariant == \/ PeopleCount(boat) = 0 => PeopleCount(leftbank) = 0
                 \/ PeopleCount(rightbank) = 0
=============================================================================
