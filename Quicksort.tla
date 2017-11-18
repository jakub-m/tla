(* Implementation and validation (through assertions) of Quicksort. *)

---- MODULE Quicksort ----
EXTENDS TLC, Sequences, Integers, FiniteSets

CONSTANT N

(* IsOrdered tells if a tuple T is ordered. *)
IsOrdered(T) == \/ Len(T) <= 1
                \/ LET n == 2..Len(T) IN \A k \in n: T[k-1] <= T[k] 
   
(* FilterTuple returns a tuple which values meet predicate Pred. *)
RECURSIVE FilterTuple(_, _)                          
FilterTuple(T, Pred) == IF Len(T) = 0 THEN << >>
                        ELSE LET h == Head(T)
                                 t == Tail(T) IN
                            IF Pred[h] THEN <<h>> \o FilterTuple(t, Pred)
                            ELSE FilterTuple(t, Pred)
                            

(* Implementation of Quicksort. *)
RECURSIVE Sort(_)
Sort(T) == IF Len(T) = 0 THEN << >>
           ELSE IF Len(T) = 1 THEN <<T[1]>>
           ELSE LET pivot == Head(T)
                    left  == FilterTuple(Tail(T), [x \in Nat |-> x <  pivot])
                    right == FilterTuple(Tail(T), [x \in Nat |-> x >= pivot])
                    IN
           Sort(left) \o <<pivot>> \o Sort(right)

(* --algorithm example

variable input \in UNION {[1..N -> 1..N]: m \in {1..N}},
         sorted = 0

begin
sorted := Sort(input);
\*print << input, sorted >>;
assert IsOrdered(sorted);
assert Len(input) = Len(sorted);
 
end algorithm *)


\* ==========================================================

\* BEGIN TRANSLATION
VARIABLES input, sorted, pc

vars == << input, sorted, pc >>

Init == (* Global variables *)
        /\ input \in UNION {[1..N -> 1..N]: m \in {1..N}}
        /\ sorted = 0
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ sorted' = Sort(input)
         /\ Assert(IsOrdered(sorted'), 
                   "Failure of assertion at line 39, column 1.")
         /\ Assert(Len(input) = Len(sorted'), 
                   "Failure of assertion at line 40, column 1.")
         /\ pc' = "Done"
         /\ input' = input

Next == Lbl_1
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION
====
