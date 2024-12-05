---- MODULE consensus_epr_abstract ----
EXTENDS TLC, Naturals, FiniteSets, Sequences

CONSTANT 
    \* @type: Set(Str);
    Node,
    \* @type: Set(Str);
    Value

VARIABLE vote_msg

vars == <<vote_msg>>

Quorum == {i \in SUBSET(Node) : Cardinality(i) * 2 > Cardinality(Node)}

Init == 
    /\ vote_msg = {}

SendRequestVote_SendVote_A(src, dst) ==
    /\ ~\E m \in vote_msg : m[1] = src
    /\ vote_msg' = vote_msg \cup {<<src,dst>>}

\* NextAOrig == 
\*     \/ SendRequestVoteAction
\*     \/ SendVoteAction

Next == 
    \/ \E i,j \in Node : SendRequestVote_SendVote_A(i,j)

Spec == Init /\ [][Next]_vars

\* \* Any two chosen values must be consistent.
\* H_NoConflictingValues == 
\*     \A n1,n2 \in Node, v1,v2 \in Value : 
\*         (v1 \in decided[n1] /\ v2 \in decided[n2]) => (v1 = v2)

\* Next2 == 
\*     \/ \E i,j \in Node : SendRequestVote_SendVote_A(i,j)
\*     \/ RecvVoteAction
\*     \/ BecomeLeaderAction
\*     \/ DecideAction


TypeOK == 
    /\ vote_msg \in SUBSET(Node \X Node)


====