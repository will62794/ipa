---- MODULE M_bi ----
EXTENDS Naturals

\* Interaction preserving abstraction, with bi-directional data flow between modules.

\* Internal variable.
VARIABLE aout

VARIABLE l1, l2

\* Internal variable.
VARIABLE b, bout

Init == 
    /\ l1 = 0
    /\ l2 = 0
    /\ aout = 0
    /\ bout = 0
    /\ b = 0

\* When bout is set to 1, this indicates to M2 that M1 is ready to 
\* acquire the lock, and it begins its internal lock acquisition procedure.
\* As long as aout=0, this indicates that M2 has not complete the lock acquisition.
StartAcquire == 
    /\ b = 0
    /\ bout = 0
    /\ bout' = 1
    /\ aout' = 0
    /\ UNCHANGED <<aout, b, l1, l2>>

\* Take one of the internal locks in M2.
TakeLock1 ==
    /\ bout = 1
    /\ aout # 1
    /\ l1 = 0
    /\ l1' = 1
    /\ UNCHANGED <<b,l2,aout,bout>>

\* Take one of the internal locks in M2.
TakeLock2 ==
    /\ bout = 1
    /\ aout # 1
    /\ l2 = 0
    /\ l2' = 1
    /\ UNCHANGED <<b,l1,aout,bout>>

\* Internal lock acquisition is complete in M2. It completes by signalling
\* this to M1 by setting aout to 1.
AckAcquire == 
    /\ l1 = 1
    /\ l2 = 1
    /\ aout = 0
    /\ aout' = 1
    /\ UNCHANGED <<b, l1, l2, bout>>

\* M1 has been signalled that M2's internal lock acquisition is complete,
\* so it can proceed with its incrementing procedure.
IncrementAfterAcquire == 
    /\ aout = 1
    /\ bout = 1
    /\ b < 30
    /\ b' = b + 10
    /\ UNCHANGED <<l1, l2, aout, bout>>

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

====