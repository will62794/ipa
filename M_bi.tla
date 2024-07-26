---- MODULE M_bi ----
EXTENDS Naturals

\* Interaction preserving abstraction, with bi-directional data flow between modules.


\* Internal variable.
VARIABLE b 

\* Shared variables.
VARIABLE bout, aout

\* Internal variables to M2.
VARIABLE locking
VARIABLE l1, l2

Init == 
    /\ l1 = 0
    /\ l2 = 0
    /\ locking = <<FALSE, 0>>
    /\ aout = 0
    /\ bout = 0
    /\ b = 0

\* When bout is set to 1, this indicates to M2 that M1 is ready to 
\* acquire the lock, and it begins its internal lock acquisition procedure.
\* As long as aout=0, this indicates that M2 has not complete the lock acquisition.
StartAcquire == 
    /\ guard:: 
        /\ b = 0
        /\ bout = 0
    /\ bout' = 1
    /\ aout' = 0
    \* Set some arbitrary lockId vlaue that will be written
    \* to internal lock variables l1 and l2.
    /\ locking' = <<TRUE, 2>>
    /\ UNCHANGED <<b, l1, l2>>

StartAcquirePostExprs == <<1, 0, <<TRUE, 2>>>>

\* Take one of the internal locks in M2.
TakeLock1 ==
    /\ guard:: 
        /\ locking[1]
        /\ aout # 1
        /\ l1 = 0
    /\ l1' = locking[2]
    /\ UNCHANGED <<b,l2,aout,bout,locking>>

TakeLock1PostExprs == <<locking[2]>>

\* Take one of the internal locks in M2.
TakeLock2 ==
    /\ guard:: 
        /\ locking[1]
        /\ bout = 1
        /\ aout # 1
        /\ l2 = 0
    /\ l2' = locking[2]
    /\ UNCHANGED <<b,l1,aout,bout,locking>>

\* Internal lock acquisition is complete in M2. It completes by signalling
\* this to M1 by setting aout to 1.
AckAcquire == 
    /\ guard:: 
        /\ l1 > 0
        /\ l2 > 0
        /\ aout = 0
    /\ aout' = 1
    /\ locking' = <<FALSE, 0>>
    /\ UNCHANGED <<b, l1, l2, bout>>

\* M1 has been signalled that M2's internal lock acquisition is complete,
\* so it can proceed with its incrementing procedure.
IncrementAfterAcquire == 
    /\ guard:: 
        /\ bout = 1
        /\ b < 3
    /\ post::
        /\ b' = b + 1
        /\ UNCHANGED <<l1, l2, aout, bout,locking>>

\* 
\* Consider module split of:
\* 
\*  M1={StartAcquire, IncrementAfterAcquire} -> bout (R/W), aout (R),  b (R/W), 
\*  M2={TakeLock1, TakeLock2, AckAcquire} ->    bout (R),   aout (R/W) l1 (R/W), l2 (R/W) 
\*  
\* 

Next == 
    \/ StartAcquire
    \/ TakeLock1
    \/ TakeLock2
    \/ AckAcquire
    \/ IncrementAfterAcquire

vars == <<aout, b, bout, l1, l2, locking>>

TypeOK == 
    /\ aout \in {0, 1}
    /\ b \in 0..3
    /\ bout \in {0, 1}
    /\ l1 \in {0, 1}
    /\ l2 \in {0, 1}
    /\ locking \in (BOOLEAN \X (0..2))

\* Are StartAcquire and TakeLock1 independent?


Action1 == StartAcquire
Action1pre == StartAcquire!guard

\* Action1 == TakeLock2
\* Action1pre == TakeLock2!guard

Action2 == TakeLock1
Action2pre == TakeLock1!guard

\* Action2 == AckAcquire
\* Action2pre == AckAcquire!guard

Action1PostExprs == StartAcquirePostExprs
Action2PostExprs == TakeLock1PostExprs

IndependenceInit == TypeOK
IndependenceNext == Action1 \/ Action2

Independence == 
    \* Action2 cannot disable Action1.
    /\ [][((ENABLED Action1 /\ Action2 ) => (Action1pre)')]_vars
    \* Action2 cannot enable Action1.
    /\ [][((~ENABLED Action1 /\ Action2 ) => (~Action1pre)')]_vars
    \* Action1 cannot disable Action2.
    /\ [][((ENABLED Action2 /\ Action1 ) => (Action2pre)')]_vars
    \* Action1 cannot enable Action2.
    /\ [][((~ENABLED Action2 /\ Action1 ) => (~Action2pre)')]_vars

\* TODO.
\* Basically this is saying that the writes of each actions are "independent" i.e. the
\* writes of one action does not affect the values written by the other action.
\* We can test this by checking if, from any state, the update expressions of Action2 
\* are modified after taking an Action1 step, and vice versa.
Commutativity == 
    /\ [][Action1 => Action2PostExprs = Action2PostExprs']_vars
    /\ [][Action2 => Action1PostExprs = Action1PostExprs']_vars
\* Starting from any state, record all states reachable by Action1.
\* Then record all states reachable from these states by Action2.



====