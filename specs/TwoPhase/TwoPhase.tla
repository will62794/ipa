------------------------------- MODULE TwoPhase ----------------------------- 
\* benchmark: tla-twophase
EXTENDS TLC, Naturals, FiniteSets

(***************************************************************************)
(* This specification describes the Two-Phase Commit protocol, in which a  *)
(* transaction manager (TM) coordinates the resource managers (RMs) to     *)
(* implement the Transaction Commit specification of module $TCommit$.  In *)
(* this specification, RMs spontaneously issue $Prepared$ messages.  We    *)
(* ignore the $Prepare$ messages that the TM can send to the               *)
(* RMs.\vspace{.4em}                                                       *)
(*                                                                         *)
(* For simplicity, we also eliminate $Abort$ messages sent by an RM when   *)
(* it decides to abort.  Such a message would cause the TM to abort the    *)
(* transaction, an event represented here by the TM spontaneously deciding *)
(* to abort.\vspace{.4em}                                                  *)
(*                                                                         *)
(* This specification describes only the safety properties of the          *)
(* protocol--that is, what is allowed to happen.  What must happen would   *)
(* be described by liveness properties, which we do not specify.           *)
(***************************************************************************)

CONSTANT 
    \* @type: Set(RM);
    RM \* The set of resource managers

\* Message ==
\*   (*************************************************************************)
\*   (* The set of all possible messages.  Messages of type $"Prepared"$ are  *)
\*   (* sent from the RM indicated by the message's $rm$ field to the TM\@.   *)
\*   (* Messages of type $"Commit"$ and $"Abort"$ are broadcast by the TM, to *)
\*   (* be received by all RMs.  The set $msgs$ contains just a single copy   *)
\*   (* of such a message.                                                    *)
\*   (*************************************************************************)
\*   [type : {"Prepared"}, rm : RM]  \cup  [type : {"Commit", "Abort"}]
\*   [type : {"Prepared", "Commit", "Abort"}, rm : RM] 

VARIABLES
  \* @type: RM -> Str;
  rmState,       \* $rmState[rm]$ is the state of resource manager RM.
  \* @type: Str;
 tmState,       \* The state of the transaction manager.
  \* @type: Set(RM);
  tmPrepared,    \* The set of RMs from which the TM has received "Prepared" messages
  \* @type: Set( { type: Str, rm: RM } );
  msgsPrepared,
  \* @type: Set( { type: Str } );
  msgsCommit,
  msgsAbort

vars == <<rmState, tmState, tmPrepared, msgsPrepared, msgsCommit, msgsAbort>>

    (***********************************************************************)
    (* In the protocol, processes communicate with one another by sending  *)
    (* messages.  Since we are specifying only safety, a process is not    *)
    (* required to receive a message, so there is no need to model message *)
    (* loss.  (There's no difference between a process not being able to   *)
    (* receive a message because the message was lost and a process simply *)
    (* ignoring the message.)  We therefore represent message passing with *)
    (* a variable $msgs$ whose value is the set of all messages that have  *)
    (* been sent.  Messages are never removed from $msgs$.  An action      *)
    (* that, in an implementation, would be enabled by the receipt of a    *)
    (* certain message is here enabled by the existence of that message in *)
    (* $msgs$.  (Receipt of the same message twice is therefore allowed;   *)
    (* but in this particular protocol, receiving a message for the second *)
    (* time has no effect.)                                                *)
    (***********************************************************************)

TypeOK ==  
  (*************************************************************************)
  (* The type-correctness invariant                                        *)
  (*************************************************************************)
  /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
  /\ tmState \in {"init", "committed", "aborted"}
  /\ tmPrepared \in SUBSET RM
  /\ msgsPrepared \in SUBSET [type : {"Prepared"}, rm : RM]
  /\ msgsCommit \in SUBSET [type : {"Commit"}]
  /\ msgsAbort \in SUBSET [type : {"Abort"}]

ApaTypeOK ==  
  (*************************************************************************)
  (* The type-correctness invariant                                        *)
  (*************************************************************************)
  /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
  /\ tmState \in {"init", "committed", "aborted"}
  /\ tmPrepared \in SUBSET RM
  /\ msgsPrepared \in SUBSET [type : {"Prepared"}, rm : RM]
  /\ msgsCommit \in SUBSET [type : {"Commit"}]
  /\ msgsAbort \in SUBSET [type : {"Abort"}]


Init ==   
  (*************************************************************************)
  (* The initial predicate.                                                *)
  (*************************************************************************)
  /\ rmState = [rm \in RM |-> "working"]
  /\ tmState = "init"
  /\ tmPrepared   = {}
  /\ msgsPrepared = {}
  /\ msgsCommit = {}
  /\ msgsAbort = {}
-----------------------------------------------------------------------------
(***************************************************************************)
(* We now define the actions that may be performed by the processes, first *)
(* the TM's actions, then the RMs' actions.                                *)
(***************************************************************************)
TMRcvPrepared(rm) ==
  (*************************************************************************)
  (* The TM receives a $"Prepared"$ message from resource manager $rm$.    *)
  (*************************************************************************)
  /\ tmState = "init"
  /\ [type |-> "Prepared", rm |-> rm] \in msgsPrepared
  /\ tmPrepared' = tmPrepared \cup {rm}
  /\ UNCHANGED <<rmState, tmState, msgsPrepared, msgsCommit, msgsAbort>>
TMRcvPreparedRVars == <<tmState, msgsPrepared, tmPrepared>>
TMRcvPreparedWVars == <<tmPrepared>>
TMRcvPreparedpre == \E rm \in RM :tmState = "init" /\ [type |-> "Prepared", rm |-> rm] \in msgsPrepared
TMRcvPreparedPostExprs == tmPrepared\* \cup {rm}

TMCommit ==
  (*************************************************************************)
  (* The TM commits the transaction; enabled iff the TM is in its initial  *)
  (* state and every RM has sent a $"Prepared"$ message.                   *)
  (*************************************************************************)
  /\ tmState = "init"
  /\ tmPrepared = RM
  /\ tmState' = "committed"
  /\ msgsCommit' = msgsCommit \cup {[type |-> "Commit"]}
  /\ UNCHANGED <<rmState, tmPrepared, msgsPrepared, msgsAbort>>
TMCommitRVars == <<tmState, tmPrepared, msgsCommit>>
TMCommitWVars == <<tmState, msgsCommit>>
TMCommitpre == tmState = "init" /\ tmPrepared = RM
TMCommitPostExprs == <<"committed", msgsCommit \cup {[type |-> "Commit"]}>>

TMAbort ==
  (*************************************************************************)
  (* The TM spontaneously aborts the transaction.                          *)
  (*************************************************************************)
  /\ tmState = "init"
  /\ tmState' = "aborted"
  /\ msgsAbort' = msgsAbort \cup {[type |-> "Abort"]}
  /\ UNCHANGED <<rmState, tmPrepared, msgsPrepared, msgsCommit>>
TMAbortRVars == <<tmState, msgsAbort>>
TMAbortWVars == <<tmState, msgsAbort>>
TMAbortpre == tmState = "init"
TMAbortPostExprs == <<"aborted", msgsAbort \cup {[type |-> "Abort"]}>>

RMPrepare(rm) == 
  (*************************************************************************)
  (* Resource manager $rm$ prepares.                                       *)
  (*************************************************************************)
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT ![rm] = "prepared"]
  /\ msgsPrepared' = msgsPrepared \cup {[type |-> "Prepared", rm |-> rm]}
  /\ UNCHANGED <<tmState, tmPrepared, msgsCommit, msgsAbort>>
RMPrepareRVars == <<rmState, msgsPrepared>>
RMPrepareWVars == <<rmState, msgsPrepared>>
RMPreparepre == \E rm \in RM : rmState[rm] = "working"
RMPreparePostExprs == msgsPrepared \*\cup {[type |-> "Prepared", rm |-> rm]}

RMChooseToAbort(rm) ==
  (*************************************************************************)
  (* Resource manager $rm$ spontaneously decides to abort.  As noted       *)
  (* above, $rm$ does not send any message in our simplified spec.         *)
  (*************************************************************************)
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared, msgsPrepared, msgsCommit, msgsAbort>>
RMChooseToAbortRVars == <<rmState>>
RMChooseToAbortWVars == <<rmState>>
RMChooseToAbortpre == \E rm \in RM : rmState[rm] = "working"
RMChooseToAbortPostExprs == "aborted"

RMRcvCommitMsg(rm) ==
  (*************************************************************************)
  (* Resource manager $rm$ is told by the TM to commit.                    *)
  (*************************************************************************)
  /\ [type |-> "Commit"] \in msgsCommit
  /\ rmState' = [rmState EXCEPT ![rm] = "committed"]
  /\ UNCHANGED <<tmState, tmPrepared, msgsPrepared, msgsCommit, msgsAbort>>
RMRcvCommitMsgRVars == <<rmState, msgsCommit>>
RMRcvCommitMsgWVars == <<rmState>>
RMRcvCommitMsgpre == [type |-> "Commit"] \in msgsCommit
RMRcvCommitMsgPostExprs == "committed"

RMRcvAbortMsg(rm) ==
  (*************************************************************************)
  (* Resource manager $rm$ is told by the TM to abort.                     *)
  (*************************************************************************)
  /\ [type |-> "Abort"] \in msgsAbort
  /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared, msgsPrepared, msgsCommit, msgsAbort>>
RMRcvAbortMsgRVars == <<rmState, msgsAbort>>
RMRcvAbortMsgWVars == <<rmState>>
RMRcvAbortMsgpre == [type |-> "Abort"] \in msgsAbort
RMRcvAbortMsgPostExprs == "aborted"

TMRcvPreparedAction == TRUE /\ \E rm \in RM : TMRcvPrepared(rm) 
RMPrepareAction == TRUE /\ \E rm \in RM : RMPrepare(rm) 
RMChooseToAbortAction == TRUE /\ \E rm \in RM : RMChooseToAbort(rm)
RMRcvCommitMsgAction == TRUE /\ \E rm \in RM : RMRcvCommitMsg(rm) 
RMRcvAbortMsgAction == TRUE /\ \E rm \in RM : RMRcvAbortMsg(rm)
TMAbortAction == TRUE /\ TMAbort
TMCommitAction == TRUE /\ TMCommit

RMAtomic(rm) == 
    /\ msgsCommit = {} 
    /\ msgsAbort = {}
    /\ msgsPrepared' = msgsPrepared \cup {[type |-> "Prepared", rm |-> rm]}
    /\ UNCHANGED <<tmState, tmPrepared, rmState, msgsCommit, msgsAbort>>

InitRM ==   
  (*************************************************************************)
  (* The initial predicate.                                                *)
  (*************************************************************************)
  /\ rmState = [rm \in RM |-> "working"]
  /\ tmState = "init"
  /\ tmPrepared   = {}
  /\ msgsPrepared = {}
  /\ msgsCommit \in SUBSET [type : {"Commit"}]
  /\ msgsAbort \in SUBSET [type : {"Abort"}]

NextRM == 
  \/ RMPrepareAction
  \/ RMChooseToAbortAction
  \/ RMRcvCommitMsgAction
  \/ RMRcvAbortMsgAction

\* Checks that all transitions are valid RMAtomic actions.
RMInteractionPreserving == [][
    \E rm \in RM : 
            /\ msgsCommit = {} 
            /\ msgsAbort = {}
            /\ msgsPrepared' = msgsPrepared \cup {[type |-> "Prepared", rm |-> rm]}
    ]_<<msgsCommit, msgsAbort, msgsPrepared>>

Next ==
  \/ TMCommitAction 
  \/ TMAbortAction
  \/ TMRcvPreparedAction
  \/ RMPrepareAction
  \/ RMChooseToAbortAction
  \/ RMRcvCommitMsgAction
  \/ RMRcvAbortMsgAction

NextAtomicRM == 
    \/ \E rm \in RM : RMAtomic(rm)
    \/ TMCommitAction 
    \/ TMAbortAction
    \/ TMRcvPreparedAction

NextAnnotated ==
    \/ TMAbort
    \/ TMCommit
    \/ \E rm \in RM : TMRcvPrepared(rm) 
    \/ \E rm \in RM : RMPrepare(rm)
    \/ \E rm \in RM : RMChooseToAbort(rm)
    \/ \E rm \in RM : RMRcvCommitMsg(rm)
    \/ \E rm \in RM : RMRcvAbortMsg(rm)

-----------------------------------------------------------------------------

NextUnchanged == UNCHANGED vars
Symmetry == Permutations(RM)

H_TCConsistent ==  
  (*************************************************************************)
  (* A state predicate asserting that two RMs have not arrived at          *)
  (* conflicting decisions.                                                *)
  (*************************************************************************)
  \A rm1, rm2 \in RM : ~ (rmState[rm1] = "aborted" /\ rmState[rm2] = "committed")

\* ASSUME A1 == RM = {"rm1", "rm2"}
\* USE A1

\* THEOREM L1 == TypeOK /\ H_TCConsistent /\ \E rm \in RM : RMChooseToAbort(rm) => H_TCConsistent'
\*  <1> QED BY DEF H_TCConsistent, RMChooseToAbort, TypeOK

\* THEOREM L1a == TypeOK /\ H_TCConsistent /\ RMChooseToAbort("rm1") => H_TCConsistent'
\*  <1> QED BY DEF H_TCConsistent, RMChooseToAbort, TypeOK

\* THEOREM L2 == H_TCConsistent /\ TMCommit => H_TCConsistent'
\*  <1> QED BY DEF H_TCConsistent, TMCommit
=============================================================================