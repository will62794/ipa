---- MODULE M_uni ----
EXTENDS Naturals

\* Interaction preserving abstraction with unidirectional data flow.

VARIABLE a
VARIABLE b
VARIABLE c

cycle == 4

Init == 
    /\ a = 0
    /\ b = 0
    /\ c = 0

IncrementA == 
    /\ b = 0
    /\ a' = a + b
    /\ UNCHANGED b
    /\ UNCHANGED c

IncrementB == 
    /\ b' = b + 2
    /\ UNCHANGED c

IncrementC == 
    /\ c' = (c + 1) % cycle
    /\ c < cycle
    /\ UNCHANGED b

\* 
\* Consider module split of M1={IncrementA} and M2={IncrementB, IncrementC}
\* where b is the only interaction variable between M1 and M2.
\* 
\* In this case the module boundaries are easy to see, since M1 only reads
\* from b and only M2 writes to b, and 'c' is an internal variable of M2.
\* 

\* But, what about alternative module split where the data flow is not 
\* unidirectional e.g. say M1 writes to a and M2 reads from a, and M2 writes to b and 

Next == 
    \/ IncrementA
    \/ IncrementB
    \/ IncrementC

====