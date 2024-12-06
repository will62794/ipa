---- MODULE RaftAbstractDynamic ----
\*
\* High level specification of Raft protocol with dynamic reconfiguration.
\*

EXTENDS Naturals, Integers, FiniteSets, Sequences, TLC


CONSTANTS 
    \* @typeAlias: SERVER = Str;
    \* @type: Set(SERVER);
    Server

CONSTANTS 
    \* @type: Str;
    Secondary, 
    \* @type: Str;
    Primary, 
    \* @type: Str;
    Nil

CONSTANT
    \* @type: Int; 
    InitTerm

VARIABLE 
    \* @type: SERVER -> Int; 
    currentTerm

VARIABLE 
    \* @type: SERVER -> Str;
    state

VARIABLE 
    \* @type: SERVER -> Seq(Int);
    log

VARIABLE
   \* @type: Set( <<Int, Int, Int>> );
    immediatelyCommitted

\* Configuration related variables.
VARIABLE configVersion
VARIABLE configTerm
VARIABLE config


vars == <<currentTerm, state, log, immediatelyCommitted, configVersion, configTerm, config>>

\* The set of all allowed config sets.
AllConfigs == SUBSET Server

\*
\* Helper operators.
\*

\* Is a sequence empty.
Empty(s) == Len(s) = 0

\* Is log entry e = <<index, term>> in the log of node 'i'.
\* @type: (<<Int,Int>>,SERVER) => Bool;
InLog(e, i) == \E x \in DOMAIN log[i] : x = e[1] /\ log[i][x] = e[2]

\* The term of the last entry in a log, or 0 if the log is empty.
LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)]

\* @type: Seq(Int) => <<Int, Int>>;
LastEntry(xlog) == <<Len(xlog),xlog[Len(xlog)]>>

\* @type: (Seq(Int), Int) => Int;
GetTerm(xlog, index) == IF index = 0 THEN 0 ELSE xlog[index]
LogTerm(i, index) == GetTerm(log[i], index)

\* The set of all quorums in a given set.
Quorums(S) == {i \in SUBSET(S) : Cardinality(i) * 2 > Cardinality(S)}

\* Do all quorums of two sets intersect.
QuorumsOverlap(x, y) == \A qx \in Quorums(x), qy \in Quorums(y) : qx \cap qy # {}

\* The min/max of a set of numbers.
\* Min(s) == CHOOSE x \in s : \A y \in s : x <= y
\* Max(s) == CHOOSE x \in s : \A y \in s : x >= y

\* Is it possible for log 'i' to roll back against log 'j'. 
\* If this is true, it implies that log 'i' should remove entries from the end of its log.
CanRollback(i, j) ==
    /\ Len(log[i]) > 0
    /\ \* The log with later term is more up-to-date.
       LastTerm(log[i]) < LastTerm(log[j])
    /\ \/ Len(log[i]) > Len(log[j])
       \* There seems no short-cut of OR clauses, so we specify the negative case.
       \/ /\ Len(log[i]) <= Len(log[j])
          /\ LastTerm(log[i]) /= LogTerm(j, Len(log[i]))

\* Can node 'i' currently cast a vote for node 'j' in term 'term'.
CanVoteForOplog(i, j, term) ==
    LET logOk ==
        \/ LastTerm(log[j]) > LastTerm(log[i])
        \/ /\ LastTerm(log[j]) = LastTerm(log[i])
           /\ Len(log[j]) >= Len(log[i]) IN
    /\ currentTerm[i] < term
    /\ logOk

\* Is a log entry 'e'=<<i, t>> immediately immediatelyCommitted in term 't' with a quorum 'Q'.
\* @type: (<<Int, Int>>, Set(SERVER)) => Bool;
ImmediatelyCommitted(e, Q) == 
    LET eind == e[1] 
        eterm == e[2] IN
    \A s \in Q :
        /\ Len(log[s]) >= eind
        /\ InLog(e, s) \* they have the entry.
        /\ currentTerm[s] = eterm  \* they are in the same term as the log entry. 

\* Helper operator for actions that propagate the term between two nodes.
UpdateTermsExpr(i, j) ==
    /\ currentTerm[i] > currentTerm[j]
    /\ currentTerm' = [currentTerm EXCEPT ![j] = currentTerm[i]]
    /\ state' = [state EXCEPT ![j] = Secondary] 


\* (configVersion, term) pair of node i.
CV(i) == <<configVersion[i], configTerm[i]>>

\* Is the config of node i considered 'newer' than the config of node j. This is the condition for
\* node j to accept the config of node i.
IsNewerConfig(i, j) ==
    \/ configTerm[i] > configTerm[j]
    \/ /\ configTerm[i] = configTerm[j]
       /\ configVersion[i] > configVersion[j]

IsNewerOrEqualConfig(i, j) ==
    \/ /\ configTerm[i] = configTerm[j]
       /\ configVersion[i] = configVersion[j]
    \/ IsNewerConfig(i, j)

\* Compares two configs given as <<configVersion, configTerm>> tuples.
NewerConfig(ci, cj) ==
    \* Compare configTerm first.
    \/ ci[2] > cj[2] 
    \* Compare configVersion if terms are equal.
    \/ /\ ci[2] = cj[2]
       /\ ci[1] > cj[1]  

\* Compares two configs given as <<configVersion, configTerm>> tuples.
NewerOrEqualConfig(ci, cj) == NewerConfig(ci, cj) \/ ci = cj

\* Can node 'i' currently cast a vote for node 'j' in term 'term'.
CanVoteForConfig(i, j, term) ==
    /\ currentTerm[i] < term
    /\ IsNewerOrEqualConfig(j, i)
    
\* A quorum of servers in the config of server i have i's config.
ConfigQuorumCheck(i) ==
    \E Q \in Quorums(config[i]) : \A t \in Q : 
        /\ configVersion[t] = configVersion[i]
        /\ configTerm[t] = configTerm[i]

\* A quorum of servers in the config of server i have the term of i.
TermQuorumCheck(i) ==
    \E Q \in Quorums(config[i]) : \A t \in Q : currentTerm[t] = currentTerm[i]    

\* Check whether the entry at "index" on "primary" is immediatelyCommitted in the primary's current config.
IsCommitted(index, primary) ==
    \* The primary must contain such an entry.
    /\ Len(log[primary]) >= index
    \* The entry was written by this leader.
    /\ LogTerm(primary, index) = currentTerm[primary]
    /\ \E quorum \in Quorums(config[primary]):
        \* all nodes have this log entry and are in the term of the leader.
        \A s \in quorum : \E k \in DOMAIN log[s] :
            /\ k = index
            /\ log[s][k] = log[primary][k]    \* they have the entry.
            /\ currentTerm[s] = currentTerm[primary]  \* they are in the same term.

\*
\* This is the precondition about immediatelyCommitted oplog entries that must be satisfied
\* on a primary server s in order for it to execute a reconfiguration.
\*
\* When a primary is first elected in term T, we can be sure that it contains
\* all immediatelyCommitted entries from terms < T. During its reign as primary in term T
\* though, it needs to make sure that any entries it commits in its own term are
\* correctly transferred to new configurations. That is, before leaving a
\* configuration C, it must make sure that any entry it immediatelyCommitted in T is now
\* immediatelyCommitted by the rules of configuration C i.e. it is "immediately immediatelyCommitted"
\* in C. That is, present on some quorum of servers in C that are in term T. 
OplogCommitment(s) == 
    \* The primary has immediatelyCommitted at least one entry in its term, or, no entries
    \* have been immediatelyCommitted yet.
    /\ (immediatelyCommitted = {}) \/ (\E c \in immediatelyCommitted : (c[2] = currentTerm[s]))
    \* All entries immediatelyCommitted in the primary's term are immediatelyCommitted in its current config.
    /\ \A c \in immediatelyCommitted : (c[2] = currentTerm[s]) => IsCommitted(c[1], s)

--------------------------------------------------------------------------------

\*
\* Next state actions.
\*

\* Node 'i', a primary, handles a new client request and places the entry 
\* in its log.    
ClientRequest(i) ==
    /\ guard::
        state[i] = Primary
    /\ post::
        /\ log' = [log EXCEPT ![i] = Append(log[i], currentTerm[i])]
    /\ UNCHANGED <<currentTerm, state, immediatelyCommitted, config, configVersion, configTerm>>
ClientRequestRVars == <<state, currentTerm, log>>
ClientRequestWVars == <<log>>

\* Node 'i' gets a new log entry from node 'j'.
GetEntries(i, j) ==
    /\ state[i] = Secondary
    \* Node j must have more entries than node i.
    /\ Len(log[j]) > Len(log[i])
       \* Ensure that the entry at the last index of node i's log must match the entry at
       \* the same index in node j's log. If the log of node i is empty, then the check
       \* trivially passes. This is the essential 'log consistency check'.
    /\ LET logOk == IF Empty(log[i])
                        THEN TRUE
                        ELSE log[j][Len(log[i])] = log[i][Len(log[i])] IN
       /\ logOk \* log consistency check
       \* If the log of node i is empty, then take the first entry from node j's log.
       \* Otherwise take the entry following the last index of node i.
       /\ LET newEntryIndex == IF Empty(log[i]) THEN 1 ELSE Len(log[i]) + 1
              newEntry      == log[j][newEntryIndex]
              newLog        == Append(log[i], newEntry) IN
              /\ log' = [log EXCEPT ![i] = newLog]
    /\ UNCHANGED <<immediatelyCommitted, currentTerm, state, config, configVersion, configTerm>>
GetEntriesRVars == <<state, log>>
GetEntriesWVars == <<log>>

\*  Node 'i' rolls back against the log of node 'j'.  
RollbackEntries(i, j) ==
    /\ guard:: 
        /\ state[i] = Secondary
        /\ CanRollback(i, j)
    \* Roll back one log entry.
    /\ post::
        /\ log' = [log EXCEPT ![i] = SubSeq(log[i], 1, Len(log[i])-1)]
    /\ UNCHANGED <<immediatelyCommitted, currentTerm, state, config, configVersion, configTerm>>
RollbackEntriesRVars == <<state, log>>
RollbackEntriesWVars == <<log>>

\* Node 'i' gets elected as a primary.
BecomeLeader(i, voteQuorum) == 
    \* Primaries make decisions based on their current configuration.
    LET newTerm == currentTerm[i] + 1 IN
    /\ i \in config[i]
    /\ i \in voteQuorum \* The new leader should vote for itself.
    /\ \A v \in voteQuorum : CanVoteForConfig(v, i, newTerm)
    /\ \A v \in voteQuorum : CanVoteForOplog(v, i, newTerm)
    \* Update the terms of each voter.
    /\ currentTerm' = [s \in Server |-> IF s \in voteQuorum THEN newTerm ELSE currentTerm[s]]
    /\ state' = [s \in Server |->
                    IF s = i THEN Primary
                    ELSE IF s \in voteQuorum THEN Secondary \* All voters should revert to secondary state.
                    ELSE state[s]]
    \* Update config's term upon becoming primary.
    /\ configTerm' = [configTerm EXCEPT ![i] = newTerm]
    /\ UNCHANGED <<log, immediatelyCommitted, config, configVersion>>   
BecomeLeaderRVars == <<state, currentTerm, log, config, configVersion, configTerm>>
BecomeLeaderWVars == <<currentTerm, state, configTerm>>

\* Primary 'i' commits its latest log entry.
CommitEntry(i, commitQuorum) ==
    LET ind == Len(log[i]) IN
    \* Must have some entries to commit.
    /\ ind > 0
    \* This node is leader.
    /\ state[i] = Primary
    \* The entry was written by this leader.
    /\ log[i][ind] = currentTerm[i]
    \* all nodes have this log entry and are in the term of the leader.
    /\ ImmediatelyCommitted(<<ind,currentTerm[i]>>, commitQuorum)
    \* Don't mark an entry as immediatelyCommitted more than once.
    /\ ~\E c \in immediatelyCommitted : c[1] = ind /\ c[2] = currentTerm[i] 
    /\ immediatelyCommitted' = immediatelyCommitted \cup {<<ind, currentTerm[i]>>}
    /\ UNCHANGED <<currentTerm, state, log, config, configVersion, configTerm>>
CommitEntryRVars == <<state, currentTerm, log, config>>
CommitEntryWVars == <<immediatelyCommitted>>
CommitEntrypre == \E i \in Server : \E Q \in Quorums(config[i]) : Len(log[i]) > 0 /\ state[i] = Primary /\ log[i][Len(log[i])] = currentTerm[i]
CommitEntryPostExprs == \E i \in Server :\E c \in immediatelyCommitted : c[1] = Len(log[i]) /\ c[2] = currentTerm[i]

\* Action that exchanges terms between two nodes and step down the primary if
\* needed. This can be safely specified as a separate action, rather than
\* occurring atomically on other replication actions that involve communication
\* between two nodes. This makes it clearer to see where term propagation is
\* strictly necessary for guaranteeing safety.
UpdateTerms(i, j) == 
    /\ UpdateTermsExpr(i, j)
    /\ UNCHANGED <<log, immediatelyCommitted, config, configVersion, configTerm>>
UpdateTermsRVars == <<currentTerm>>
UpdateTermsWVars == <<currentTerm, state>>

\* A reconfig occurs on node i. The node must currently be a leader.
Reconfig(i, newConfig) ==
    /\ state[i] = Primary
    /\ configVersion = configVersion
    /\ configTerm = configTerm
    /\ ConfigQuorumCheck(i)
    /\ TermQuorumCheck(i)
    /\ QuorumsOverlap(config[i], newConfig)
    /\ OplogCommitment(i)
    /\ i \in newConfig
    /\ configTerm' = [configTerm EXCEPT ![i] = currentTerm[i]]
    /\ configVersion' = [configVersion EXCEPT ![i] = configVersion[i] + 1]
    /\ config' = [config EXCEPT ![i] = newConfig]
    /\ UNCHANGED <<currentTerm, state, log, immediatelyCommitted>>
ReconfigRVars == <<state, currentTerm, log, config, configVersion, configTerm>>
ReconfigWVars == <<config, configVersion, configTerm>>

\* Node i sends its current config to node j.
SendConfig(i, j) ==
    /\ guard::
        /\ state[j] = Secondary
        /\ IsNewerConfig(i, j)
    /\ post::
        /\ configVersion' = [configVersion EXCEPT ![j] = configVersion[i]]
        /\ configTerm' = [configTerm EXCEPT ![j] = configTerm[i]]
        /\ config' = [config EXCEPT ![j] = config[i]]
    /\ UNCHANGED <<currentTerm, state, log, immediatelyCommitted>>
SendConfigRVars == <<state, configVersion, configTerm>>
SendConfigWVars == <<config, configVersion, configTerm>>
SendConfigpre == \E i,j \in Server : state[j] = Secondary /\ IsNewerConfig(i, j)
SendConfigPostExprs == \E i \in Server : <<configVersion[i], configTerm[i], config[i]>>
    
Init == 
    /\ currentTerm = [i \in Server |-> InitTerm]
    /\ state       = [i \in Server |-> Secondary]
    /\ log = [i \in Server |-> <<>>]
    /\ immediatelyCommitted = {}
    /\ configVersion =  [i \in Server |-> 1]
    /\ configTerm    =  [i \in Server |-> InitTerm]
    /\ \E initConfig \in AllConfigs :
        /\ initConfig # {}
        /\ config = [i \in Server |-> initConfig]


\* Add dummy precondition for now so TLC tags actions by name explicitly.
ClientRequestAction == TRUE /\ \E s \in Server : ClientRequest(s)
GetEntriesAction == TRUE /\ \E s, t \in Server : GetEntries(s, t)
RollbackEntriesAction == TRUE /\ \E s, t \in Server : RollbackEntries(s, t)
BecomeLeaderAction == TRUE /\ \E s \in Server : \E Q \in Quorums(config[s]) :  BecomeLeader(s, Q)
CommitEntryAction ==  TRUE /\ \E s \in Server :  \E Q \in Quorums(config[s]) : CommitEntry(s, Q)
UpdateTermsAction == TRUE /\ \E s,t \in Server : UpdateTerms(s, t)
ReconfigAction == TRUE /\ \E s \in Server, newConfig \in AllConfigs : Reconfig(s, newConfig)
SendConfigAction == TRUE /\ \E s,t \in Server : SendConfig(s, t)

Next == 
    \/ ClientRequestAction
    \/ GetEntriesAction
    \/ RollbackEntriesAction
    \/ BecomeLeaderAction
    \/ CommitEntryAction
    \/ UpdateTermsAction
    \/ ReconfigAction
    \/ SendConfigAction

NextUnchanged == UNCHANGED vars


Action_RollbackEntries == [
    action |-> \E s, t \in Server : RollbackEntries(s, t),
    pre |-> \E s, t \in Server : RollbackEntries(s, t)!guard,
    pre_primed |-> \E s, t \in Server : RollbackEntries(s, t)!guard',
    post |-> {RollbackEntries(s, t)!post!1!2 : s,t \in Server},
    post_primed |-> {RollbackEntries(s, t)!post!1!2' : s,t \in Server}
]

Action_ClientRequest == [
    action |-> \E s \in Server : ClientRequest(s),
    pre |-> \E s \in Server : ClientRequest(s)!guard,
    pre_primed |-> \E s \in Server : ClientRequest(s)!guard',
    post |-> {ClientRequest(s)!post!1!2 : s \in Server},
    post_primed |-> {ClientRequest(s)!post!1!2' : s \in Server}
]

Action_SendConfig == [
    action |-> \E s, t \in Server : SendConfig(s, t),
    pre |-> \E s, t \in Server : SendConfig(s, t)!guard,
    pre_primed |-> \E s, t \in Server : SendConfig(s, t)!guard',
    post |-> {SendConfig(s, t)!post!1!2 : s,t \in Server},
    post_primed |-> {SendConfig(s, t)!post!1!2' : s,t \in Server}
]

CONSTANTS 
    \* @type: Int;
    MaxTerm, 
    \* @type: Int;
    MaxLogLen,
    MaxConfigVersion

SeqOf(S, n) == UNION {[1..m -> S] : m \in 0..n}
BoundedSeq(S, n) == SeqOf(S, n)

\* Statement of type correctness.
TypeOK ==
    /\ currentTerm \in [Server -> Nat]
    /\ state \in [Server -> {Secondary, Primary}]
    /\ log \in [Server -> BoundedSeq(Nat, MaxLogLen)]
    /\ config \in [Server -> SUBSET Server]
    /\ configVersion \in [Server -> Nat]
    /\ configTerm \in [Server -> Nat]
    \* /\ immediatelyCommitted \in SUBSET [ entry : Nat \X Nat, term : Nat ]
    /\ immediatelyCommitted = {} \* SUBSET [ entry : Nat \X Nat, term : Nat ]


\* IndependenceInit == TypeOK
\* IndependenceNext == Action1 \/ Action2

\* Is action A1 independent of action A2.
IndependenceCond(A1,A2) == 
    \* A2 cannot disable A1.
    /\ (A1.pre /\ A2.action) => (A1.pre_primed)
    \* A2 cannot enable A1.
    /\ (~A1.pre /\ A2.action) => (~A1.pre_primed)
    \* Writes of A2 cannot influence inputs/writes of A1.
    /\ A1.action => A2.post = A2.post_primed

\* P1 == [][IndependenceCond(Action_RollbackEntries,Action_SendConfig)]_vars
P1 == [][IndependenceCond(Action_ClientRequest,Action_SendConfig)]_vars
\* P1 == [][IndependenceCond(Action_RollbackEntries,Action_ClientRequest)]_vars


\* Basically this is saying that the writes of each actions are "independent" i.e. the
\* writes of one action does not affect the values written by the other action.
\* We can test this by checking if, from any state, the update expressions of Action2 
\* are modified after taking an Action1 step, and vice versa.
\* Commutativity == 
\*     /\ [][Action1 => Action2PostExprs = Action2PostExprs']_vars
\*     /\ [][Action2 => Action1PostExprs = Action1PostExprs']_vars




--------------------------------------------------------------------------------

\*
\* Correctness properties
\*

H_OnePrimaryPerTerm == 
    \A s,t \in Server :
        (/\ state[s] = Primary 
         /\ state[t] = Primary
         /\ currentTerm[s] = currentTerm[t]) => (s = t)

LeaderAppendOnly == 
    [][\A s \in Server : state[s] = Primary => Len(log'[s]) >= Len(log[s])]_vars

\* <<index, term>> pairs uniquely identify log prefixes.
LogMatching == 
    \A s,t \in Server : 
    \A i \in DOMAIN log[s] :
        (\E j \in DOMAIN log[t] : i = j /\ log[s][i] = log[t][j]) => 
        (SubSeq(log[s],1,i) = SubSeq(log[t],1,i)) \* prefixes must be the same.

\* When a node gets elected as primary it contains all entries immediatelyCommitted in previous terms.
LeaderCompleteness == 
    \A s \in Server : (state[s] = Primary) => 
        \A c \in immediatelyCommitted : (c[2] < currentTerm[s] => InLog(<<c[1],c[2]>>, s))

\* \* If two entries are immediatelyCommitted at the same index, they must be the same entry.
StateMachineSafety == 
    \A c1, c2 \in immediatelyCommitted : (c1[1] = c2[1]) => (c1 = c2)

--------------------------------------------------------------------------------


\* State Constraint. Used for model checking only.
StateConstraint == 
    \A s \in Server :
        /\ currentTerm[s] <= MaxTerm
        /\ Len(log[s]) <= MaxLogLen
        /\ configVersion[s] <= MaxConfigVersion

Symmetry == Permutations(Server)

Terms == InitTerm..MaxTerm
LogIndices == 1..MaxLogLen
ConfigVersions == 1..MaxConfigVersion

\* \* Statement of type correctness.
\* ApaTypeOK ==
\*     /\ currentTerm \in [Server -> Terms]
\*     /\ state \in [Server -> {Secondary, Primary}]
\*     /\ log = Gen(3)
\*     /\ \A s \in Server : \A i \in DOMAIN log[s] : log[s][i] \in Terms
\*     /\ \A s \in Server : Len(log[s]) <= MaxLogLen
\*     /\ DOMAIN log = Server
\*     \* I believe this should constraint 'committed' to be a set of size 3,
\*     \* with elements of the appropriate type.
\*     /\ immediatelyCommitted = Gen(3)
\*     /\ \A c \in immediatelyCommitted : c \in (LogIndices \X Terms \X Terms)
    
\* /\ immediatelyCommitted \in SUBSET (LogIndices \X Terms \X Terms)

CInit == 
    /\ Primary = "Primary"
    /\ Secondary = "Secondary"
    /\ Nil = "Nil"
    /\ Server = {"s1", "s2", "s3"}
    /\ MaxLogLen = 3
    /\ MaxTerm = 2
    /\ InitTerm = 0

\* 
\* Helper lemmas.
\* 

\* Dummy lemma that is trivially true.
H_TRUE == Cardinality(DOMAIN state) >= 0

\* If a primary has been elected at term T, then there must exist a quorum at term >= T.
H_QuorumsSafeAtTerms == 
    \A s \in Server : (state[s] = Primary) =>
        (\E Q \in Quorums(Server) : \A n \in Q : currentTerm[n] >= currentTerm[s])

H_TermsGrowMonotonically ==
    \A s \in Server : \A i,j \in DOMAIN log[s] : (i <= j) => (log[s][i] <= log[s][j])

H_PrimaryTermAtLeastAsLargeAsLogTerms == 
    \A s \in Server : (state[s] = Primary) => 
        \A i \in DOMAIN log[s] : currentTerm[s] >= log[s][i]

H_CommittedEntryExistsOnQuorum == 
    \A c \in immediatelyCommitted :
        \E Q \in Quorums(Server) : \A n \in Q : InLog(<<c[1],c[2]>>, n)  

H_EntriesCommittedInOwnOrLaterTerm == 
    \A c \in immediatelyCommitted : c[2] >= c[2] 

H_EntriesCommittedInOwnTerm == 
    \A c \in immediatelyCommitted : c[2] = c[2] 

\* Existence of an entry in term T implies a past election in T, so 
\* there must be some quorum at this term or greater.
H_LogEntryInTermImpliesSafeAtTerm == 
    \A s \in Server : 
    \A i \in DOMAIN log[s] :
        \E Q \in Quorums(Server) : \A n \in Q : currentTerm[n] >= log[s][i]

\* If a server's latest log term exceeds a immediatelyCommitted entry c's term, then it must contain that 
\* immediatelyCommitted entry in its log.
H_LogsLaterThanCommittedMustHaveCommitted ==
    \A s \in Server : 
    \A c \in immediatelyCommitted :
        \* Exists an entry in log[s] with a term greater than the term in which the entry was immediatelyCommitted.
        (\E i \in DOMAIN log[s] : (log[s][i] > c[2]) \/ (log[s][i] > c[2])) =>
            /\ Len(log[s]) >= c[1]
            /\ log[s][c[1]] = c[2] \* entry exists in the server's log.

\* If a server's latest log term exceeds a immediatelyCommitted entry c's term, then it must contain that 
\* immediatelyCommitted entry in its log. Also, primary logs must contain entries immediatelyCommitted in earlier terms.
H_PrimaryOrLogsLaterThanCommittedMustHaveEarlierCommitted ==
    /\ H_LogsLaterThanCommittedMustHaveCommitted
    /\ LeaderCompleteness

H_LogsWithEntryInTermMustHaveEarlierCommittedEntriesFromTerm ==
    \A s \in Server : 
    \A c \in immediatelyCommitted :
        \* Exists an entry with same term as the immediatelyCommitted entry. 
        (\E i \in DOMAIN log[s] : log[s][i] = c[2] /\ i >= c[1]) =>
                    /\ Len(log[s]) >= c[1]
                    /\ log[s][c[1]] = c[2]

\* If a log entry exists in term T and there is a primary in term T, then this
\* log entry should be present in that primary's log.
H_PrimaryHasEntriesItCreated == 
    \A i,j \in Server :
    (state[i] = Primary) => 
    \* Can't be that another node has an entry in this primary's term
    \* but the primary doesn't have it.
        ~(\E k \in DOMAIN log[j] :
            /\ log[j][k] = currentTerm[i]
            /\ ~InLog(<<k,log[j][k]>>, i))

\* A server's current term is always at least as large as the terms in its log.
H_CurrentTermAtLeastAsLargeAsLogTermsForPrimary == 
    \A s \in Server : 
        (state[s] = Primary) => 
            (\A i \in DOMAIN log[s] : currentTerm[s] >= log[s][i])

\* If a log contains an entry in term T at index I such that
\* the entries at J < I are in a different term, then there must be
\* no other logs that contains entries in term T at indices J < I
H_UniformLogEntriesInTerm ==
    \A s,t \in Server :
    \A i \in DOMAIN log[s] : 
        (\A j \in DOMAIN log[s] : (j < i) => log[s][j] # log[s][i]) => 
            (~\E k \in DOMAIN log[t] : log[t][k] = log[s][i] /\ k < i)

\* Reconfig related.

H_PrimaryConfigTermEqualToCurrentTerm == 
    \A s \in Server : (state[s] = Primary) => (configTerm[s] = currentTerm[s])

H_ConfigVersionAndTermUnique ==
    \A i,j \in Server :
        (<<configVersion[i],configTerm[i]>> = <<configVersion[j],configTerm[j]>> )=>
        config[i] = config[j]

H_PrimaryInTermContainsNewestConfigOfTerm == 
    \A p,s \in Server : 
        (state[p] = Primary /\ configTerm[s] = configTerm[p]) =>
            (configVersion[p] >= configVersion[s]) 



\* Is node i disabled due to a quorum of its config having moved to a newer config.
ConfigDisabled(i) == 
    \A Q \in Quorums(config[i]) : \E n \in Q : NewerConfig(CV(n), CV(i))

ActiveConfigSet == {s \in Server : ~ConfigDisabled(s)}

\* The quorums of all active configs overlap with each other. 
H_ActiveConfigsOverlap == 
    \A s,t \in ActiveConfigSet : QuorumsOverlap(config[s], config[t])

\* Every active config overlaps with some node in a term >=T for all elections
\* that occurred in term T (and exist in some config that is still around).
H_ActiveConfigsSafeAtTerms == 
    \A s \in Server : 
    \A t \in ActiveConfigSet :
        \A Q \in Quorums(config[t]) : \E n \in Q : currentTerm[n] >= configTerm[s]


\* If a log entry in term T exists, there must have been an election in 
\* term T to create it, implying the existence of a config in term T or newer.
H_LogEntryInTermImpliesConfigInTerm == 
    \A s \in Server : 
        \A i \in DOMAIN log[s] :
        \E t \in Server : 
            configTerm[t] >= log[s][i]

H_ActiveConfigsOverlapWithCommittedEntry == 
    \A c \in immediatelyCommitted :
    \A s \in ActiveConfigSet :
        \A Q \in Quorums(config[s]) : \E n \in Q : InLog(c, n)  

H_NewerConfigsDisablePrimaryCommitsInOlderTerms ==
    \A s,t \in Server : 
    (state[t] = Primary /\ currentTerm[t] < configTerm[s]) =>
        \A Q \in Quorums(config[t]) : \E n \in Q : currentTerm[n] > currentTerm[t]

H_ConfigsNonempty ==
    \A s \in Server : config[s] # {}

\* \* Invariant developed during inductive proof decomposition experimenting.
\* \* 08/19/2023
\* HumanDecompInd == 
\*     /\ StateMachineSafety
\*     /\ LeaderCompleteness
\*     /\ H_CommittedEntryExistsOnQuorum
\*     /\ H_LogsLaterThanCommittedMustHaveCommitted
\*     /\ H_CurrentTermAtLeastAsLargeAsLogTermsForPrimary
\*     /\ H_EntriesCommittedInOwnOrLaterTerm
\*     /\ H_EntriesCommittedInOwnTerm
\*     /\ H_LogEntryInTermImpliesSafeAtTerm
\*     /\ H_OnePrimaryPerTerm
\*     /\ H_PrimaryHasEntriesItCreated
\*     /\ H_QuorumsSafeAtTerms
\*     /\ H_TermsGrowMonotonically
\*     /\ LogMatching
\*     /\ H_UniformLogEntriesInTerm

\* HumanDecompIndWithTypeOK ==
\*     /\ TypeOK
\*     /\ HumanDecompInd   

\* HumanDecompInd_WithConstraint == StateConstraint => HumanDecompInd

=============================================================================