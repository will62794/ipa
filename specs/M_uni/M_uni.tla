---- MODULE M_uni ----
EXTENDS Naturals

\* Interaction preserving abstraction with unidirectional data flow.

VARIABLE a
VARIABLE b
VARIABLE c

vars == <<a, b, c>>

cycle == 4

Init == 
    /\ a = 0
    /\ b = 0
    /\ c = 0

IncrementA == 
    /\ guard::
        /\ b = 0
    /\ a' = a + b
    /\ UNCHANGED <<b,c>>
IncrementApre == IncrementA!guard
IncrementAPostExprs == <<a + b>>

IncrementB == 
    /\ guard::
        /\ TRUE
    /\ b' = (b + c) % cycle
    /\ UNCHANGED <<a,c>>
IncrementBpre == TRUE
IncrementBPostExprs == <<b + 2>>

IncrementC == 
    /\ guard::
        /\ TRUE
    /\ c' = (c + 1) % cycle
    /\ c < cycle
    /\ UNCHANGED <<a,b>>
IncrementCpre == TRUE
IncrementCPostExprs == <<(c + 1) % cycle, c < cycle>>

\* 
\* Consider module split of M1={IncrementA} and M2={IncrementB, IncrementC}
\* where b is the only interaction variable between M1 and M2.
\* 
\* In this case the module boundaries are easy to see, since M1 only reads
\* from b and only M2 writes to b, and 'c' is an internal variable of M2.
\* 

\* But, what about alternative module split where the data flow is not 
\* unidirectional e.g. say M1 writes to a and M2 reads from a, and M2 writes to b and 

IncrementAAction == IncrementA
IncrementBAction == IncrementB
IncrementCAction == IncrementC

Next == 
    \/ IncrementAAction
    \/ IncrementBAction
    \/ IncrementCAction

TypeOK == 
    /\ a \in 0..cycle
    /\ b \in 0..cycle
    /\ c \in 0..cycle


\* Action1 == IncrementA
\* Action1pre == IncrementA!guard
\* Action1PostExprs == IncrementAPostExprs

\* \* Action2 == IncrementB
\* \* Action2pre == IncrementB!guard
\* \* Action2PostExprs == IncrementBPostExprs

\* Action2 == IncrementC
\* Action2pre == IncrementC!guard
\* Action2PostExprs == IncrementCPostExprs

\* IndependenceInit == TypeOK
\* IndependenceNext == Action1 \/ Action2

\* Independence == 
\*     \* Action2 cannot disable Action1.
\*     /\ [][((ENABLED Action1 /\ Action2 ) => (Action1pre)')]_vars
\*     \* Action2 cannot enable Action1.
\*     /\ [][((~ENABLED Action1 /\ Action2 ) => (~Action1pre)')]_vars
\*     \* Action1 cannot disable Action2.
\*     /\ [][((ENABLED Action2 /\ Action1 ) => (Action2pre)')]_vars
\*     \* Action1 cannot enable Action2.
\*     /\ [][((~ENABLED Action2 /\ Action1 ) => (~Action2pre)')]_vars

\* \* TODO.
\* \* Basically this is saying that the writes of each actions are "independent" i.e. the
\* \* writes of one action does not affect the values written by the other action.
\* \* We can test this by checking if, from any state, the update expressions of Action2 
\* \* are modified after taking an Action1 step, and vice versa.
\* Commutativity == 
\*     /\ [][Action1 => Action2PostExprs = Action2PostExprs']_vars
\*     /\ [][Action2 => Action1PostExprs = Action1PostExprs']_vars
\* \* Starting from any state, record all states reachable by Action1.
\* \* Then record all states reachable from these states by Action2.


====