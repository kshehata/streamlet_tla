----------------------------- MODULE HotStuff -----------------------------

EXTENDS Blocks, Sequences, FiniteSets, TLC

CONSTANT Leaders

ASSUME Leaders \in Seq(Replicas)

(* --algorithm hotstuff
variables
    \* DO NOT MODIFY DIRECTLY! Should only be used in ProposeNewBlock
    NextBlockId = 1;

    \* Global cache of all blocks, assumed in paper that all nodes can just get all blocks.
    AllBlocks = {GenesisBlock};

    \* All messages sent by replicas
    Messages = {};

define
\* Shortcut for messages from the leader
FilterMessages(src, dest) == { m \in Messages :
            /\ src = m.vote
            /\ dest \in m.dest
            /\ dest \notin m.received }
end define;

macro ReceiveMessage(msg) begin
    Messages := (Messages \ {msg}) \union 
        {MarkMessageReceivedBy(msg, self)};
end macro

macro SendMessage(msg) begin
    Messages := Messages \union {msg};
end macro

macro ReplyWithVote(msg, type, block, dest) begin
    Messages := (Messages \ {msg}) \union {
        MarkMessageReceivedBy(msg, self),
        CreateMessageTo(type, curView, block, Null, self, dest)
    };
end macro;

macro ProposeNewBlock(justifyQC) begin
    with
        newBlock = CreateBlock(NextBlockId, justifyQC.block),
        proposeMsg = CreateBroadcastMessage(Prepare, curView, newBlock, justifyQC, self)
    do
        NextBlockId := NextBlockId + 1;
        AllBlocks := AllBlocks \union {newBlock};
        SendMessage(proposeMsg);
    end with;
end macro;

macro WaitForVotes(voteType) begin
    while ~CheckVotesForQC(ReceivedVotes(Messages, voteType, curView, self)) do
        with m \in { m \in Messages : self \in m.dest /\ self \notin m.received } do
            ReceiveMessage(m);
        end with;
    end while;
end macro;

macro SendQC(voteType, phase, qc) begin
    with votes = ReceivedVotes(Messages, voteType, curView, self) do
        assert CheckVotesForQC(votes);
        qc := GenerateQC(votes);
        SendMessage(CreateBroadcastMessage(phase, curView, Null, qc, self));
    end with;
end macro;

fair process rep \in Replicas
variables
    curView = 1;
    prepareQC = GenesisQC(Prepare);
    lockedQC = GenesisQC(PreCommit);
    \* Only used as a temporary, but makes life easier
    commitQC = GenesisQC(Commit);
    committedBlocks = {};

begin
LeaderCheck:
    if (self # Leaders[curView]) then
        goto ReplicaPrepare;
    end if;

Propose:
    ProposeNewBlock(prepareQC);

LeaderPreCommit:
    WaitForVotes(Prepare);
    SendQC(Prepare, PreCommit, prepareQC);

LeaderCommit:
    WaitForVotes(PreCommit);
    SendQC(PreCommit, Commit, lockedQC);

LeaderDecide:
    WaitForVotes(Commit);
    SendQC(Commit, Decide, commitQC);
    committedBlocks := committedBlocks \union {commitQC.block};
    goto Done;


ReplicaPrepare:
    with leader = Leaders[curView],
        m \in FilterMessages(leader, self) do
        if m.type # Prepare \/ m.viewNum # curView then
            ReceiveMessage(m);
            goto ReplicaPrepare;
        elsif ~DirectlyExtends(m.block, m.justify.block) then
            ReceiveMessage(m);
            \* TODO: What to do in this case ??
        elsif ~( \/ BlockExtends(m.block, lockedQC.block, AllBlocks)
                 \/ m.justify.viewNum > lockedQC.viewNum ) then
            print <<"Proposed block fails SafeNode:", m>>;
            ReceiveMessage(m);
            \* TODO: What to do in this case ??
        else
            ReplyWithVote(m, Prepare, m.block, leader);
        end if;
    end with;

ReplicaPreCommit:
    with leader = Leaders[curView],
        m \in FilterMessages(leader, self) do
        \* TODO: Should this check the message as well ??
        if m.justify.type # Prepare \/ m.justify.viewNum # curView then
            ReceiveMessage(m);
            goto ReplicaPreCommit;
        else
            prepareQC := m.justify;
            ReplyWithVote(m, PreCommit, m.justify.block, leader);
        end if;
    end with;

ReplicaCommit:
    with leader = Leaders[curView],
        m \in FilterMessages(leader, self) do
        \* TODO: Should this check the message as well ??
        if m.justify.type # PreCommit \/ m.justify.viewNum # curView then
            \* print <<"Got invalid Commit message:", m>>;
            ReceiveMessage(m);
            goto ReplicaCommit;
        else
            lockedQC := m.justify;
            ReplyWithVote(m, Commit, m.justify.block, leader);
        end if;
    end with;

ReplicaDecide:
    with leader = Leaders[curView],
        m \in FilterMessages(leader, self) do
        \* TODO: Should this check the message as well ??
        if m.justify.type # Commit \/ m.justify.viewNum # curView then
            \* print <<"Got invalid Decide message:", m>>;
            ReceiveMessage(m);
            goto ReplicaCommit;
        else
            committedBlocks := committedBlocks \union {m.justify.block};
        end if;
    end with;

end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "58a11584" /\ chksum(tla) = "4aaf5c5a")
VARIABLES NextBlockId, AllBlocks, Messages, pc

(* define statement *)
FilterMessages(src, dest) == { m \in Messages :
            /\ src = m.vote
            /\ dest \in m.dest
            /\ dest \notin m.received }

VARIABLES curView, prepareQC, lockedQC, commitQC, committedBlocks

vars == << NextBlockId, AllBlocks, Messages, pc, curView, prepareQC, lockedQC, 
           commitQC, committedBlocks >>

ProcSet == (Replicas)

Init == (* Global variables *)
        /\ NextBlockId = 1
        /\ AllBlocks = {GenesisBlock}
        /\ Messages = {}
        (* Process rep *)
        /\ curView = [self \in Replicas |-> 1]
        /\ prepareQC = [self \in Replicas |-> GenesisQC(Prepare)]
        /\ lockedQC = [self \in Replicas |-> GenesisQC(PreCommit)]
        /\ commitQC = [self \in Replicas |-> GenesisQC(Commit)]
        /\ committedBlocks = [self \in Replicas |-> {}]
        /\ pc = [self \in ProcSet |-> "LeaderCheck"]

LeaderCheck(self) == /\ pc[self] = "LeaderCheck"
                     /\ IF (self # Leaders[curView[self]])
                           THEN /\ pc' = [pc EXCEPT ![self] = "ReplicaPrepare"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "Propose"]
                     /\ UNCHANGED << NextBlockId, AllBlocks, Messages, curView, 
                                     prepareQC, lockedQC, commitQC, 
                                     committedBlocks >>

Propose(self) == /\ pc[self] = "Propose"
                 /\ LET newBlock == CreateBlock(NextBlockId, prepareQC[self].block) IN
                      LET proposeMsg == CreateBroadcastMessage(Prepare, curView[self], newBlock, prepareQC[self], self) IN
                        /\ NextBlockId' = NextBlockId + 1
                        /\ AllBlocks' = (AllBlocks \union {newBlock})
                        /\ Messages' = (Messages \union {proposeMsg})
                 /\ pc' = [pc EXCEPT ![self] = "LeaderPreCommit"]
                 /\ UNCHANGED << curView, prepareQC, lockedQC, commitQC, 
                                 committedBlocks >>

LeaderPreCommit(self) == /\ pc[self] = "LeaderPreCommit"
                         /\ IF ~CheckVotesForQC(ReceivedVotes(Messages, Prepare, curView[self], self))
                               THEN /\ \E m \in { m \in Messages : self \in m.dest /\ self \notin m.received }:
                                         Messages' = (        (Messages \ {m}) \union
                                                      {MarkMessageReceivedBy(m, self)})
                                    /\ pc' = [pc EXCEPT ![self] = "LeaderPreCommit"]
                                    /\ UNCHANGED prepareQC
                               ELSE /\ LET votes == ReceivedVotes(Messages, Prepare, curView[self], self) IN
                                         /\ Assert(CheckVotesForQC(votes), 
                                                   "Failure of assertion at line 65, column 9 of macro called at line 91, column 5.")
                                         /\ prepareQC' = [prepareQC EXCEPT ![self] = GenerateQC(votes)]
                                         /\ Messages' = (Messages \union {(CreateBroadcastMessage(PreCommit, curView[self], Null, prepareQC'[self], self))})
                                    /\ pc' = [pc EXCEPT ![self] = "LeaderCommit"]
                         /\ UNCHANGED << NextBlockId, AllBlocks, curView, 
                                         lockedQC, commitQC, committedBlocks >>

LeaderCommit(self) == /\ pc[self] = "LeaderCommit"
                      /\ IF ~CheckVotesForQC(ReceivedVotes(Messages, PreCommit, curView[self], self))
                            THEN /\ \E m \in { m \in Messages : self \in m.dest /\ self \notin m.received }:
                                      Messages' = (        (Messages \ {m}) \union
                                                   {MarkMessageReceivedBy(m, self)})
                                 /\ pc' = [pc EXCEPT ![self] = "LeaderCommit"]
                                 /\ UNCHANGED lockedQC
                            ELSE /\ LET votes == ReceivedVotes(Messages, PreCommit, curView[self], self) IN
                                      /\ Assert(CheckVotesForQC(votes), 
                                                "Failure of assertion at line 65, column 9 of macro called at line 95, column 5.")
                                      /\ lockedQC' = [lockedQC EXCEPT ![self] = GenerateQC(votes)]
                                      /\ Messages' = (Messages \union {(CreateBroadcastMessage(Commit, curView[self], Null, lockedQC'[self], self))})
                                 /\ pc' = [pc EXCEPT ![self] = "LeaderDecide"]
                      /\ UNCHANGED << NextBlockId, AllBlocks, curView, 
                                      prepareQC, commitQC, committedBlocks >>

LeaderDecide(self) == /\ pc[self] = "LeaderDecide"
                      /\ IF ~CheckVotesForQC(ReceivedVotes(Messages, Commit, curView[self], self))
                            THEN /\ \E m \in { m \in Messages : self \in m.dest /\ self \notin m.received }:
                                      Messages' = (        (Messages \ {m}) \union
                                                   {MarkMessageReceivedBy(m, self)})
                                 /\ pc' = [pc EXCEPT ![self] = "LeaderDecide"]
                                 /\ UNCHANGED << commitQC, committedBlocks >>
                            ELSE /\ LET votes == ReceivedVotes(Messages, Commit, curView[self], self) IN
                                      /\ Assert(CheckVotesForQC(votes), 
                                                "Failure of assertion at line 65, column 9 of macro called at line 99, column 5.")
                                      /\ commitQC' = [commitQC EXCEPT ![self] = GenerateQC(votes)]
                                      /\ Messages' = (Messages \union {(CreateBroadcastMessage(Decide, curView[self], Null, commitQC'[self], self))})
                                 /\ committedBlocks' = [committedBlocks EXCEPT ![self] = committedBlocks[self] \union {commitQC'[self].block}]
                                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ UNCHANGED << NextBlockId, AllBlocks, curView, 
                                      prepareQC, lockedQC >>

ReplicaPrepare(self) == /\ pc[self] = "ReplicaPrepare"
                        /\ LET leader == Leaders[curView[self]] IN
                             \E m \in FilterMessages(leader, self):
                               IF m.type # Prepare \/ m.viewNum # curView[self]
                                  THEN /\ Messages' = (        (Messages \ {m}) \union
                                                       {MarkMessageReceivedBy(m, self)})
                                       /\ pc' = [pc EXCEPT ![self] = "ReplicaPrepare"]
                                  ELSE /\ IF ~DirectlyExtends(m.block, m.justify.block)
                                             THEN /\ Messages' = (        (Messages \ {m}) \union
                                                                  {MarkMessageReceivedBy(m, self)})
                                             ELSE /\ IF ~( \/ BlockExtends(m.block, lockedQC[self].block, AllBlocks)
                                                           \/ m.justify.viewNum > lockedQC[self].viewNum )
                                                        THEN /\ PrintT(<<"Proposed block fails SafeNode:", m>>)
                                                             /\ Messages' = (        (Messages \ {m}) \union
                                                                             {MarkMessageReceivedBy(m, self)})
                                                        ELSE /\ Messages' = (            (Messages \ {m}) \union {
                                                                                 MarkMessageReceivedBy(m, self),
                                                                                 CreateMessageTo(Prepare, curView[self], (m.block), Null, self, leader)
                                                                             })
                                       /\ pc' = [pc EXCEPT ![self] = "ReplicaPreCommit"]
                        /\ UNCHANGED << NextBlockId, AllBlocks, curView, 
                                        prepareQC, lockedQC, commitQC, 
                                        committedBlocks >>

ReplicaPreCommit(self) == /\ pc[self] = "ReplicaPreCommit"
                          /\ LET leader == Leaders[curView[self]] IN
                               \E m \in FilterMessages(leader, self):
                                 IF m.justify.type # Prepare \/ m.justify.viewNum # curView[self]
                                    THEN /\ Messages' = (        (Messages \ {m}) \union
                                                         {MarkMessageReceivedBy(m, self)})
                                         /\ pc' = [pc EXCEPT ![self] = "ReplicaPreCommit"]
                                         /\ UNCHANGED prepareQC
                                    ELSE /\ prepareQC' = [prepareQC EXCEPT ![self] = m.justify]
                                         /\ Messages' = (            (Messages \ {m}) \union {
                                                             MarkMessageReceivedBy(m, self),
                                                             CreateMessageTo(PreCommit, curView[self], (m.justify.block), Null, self, leader)
                                                         })
                                         /\ pc' = [pc EXCEPT ![self] = "ReplicaCommit"]
                          /\ UNCHANGED << NextBlockId, AllBlocks, curView, 
                                          lockedQC, commitQC, committedBlocks >>

ReplicaCommit(self) == /\ pc[self] = "ReplicaCommit"
                       /\ LET leader == Leaders[curView[self]] IN
                            \E m \in FilterMessages(leader, self):
                              IF m.justify.type # PreCommit \/ m.justify.viewNum # curView[self]
                                 THEN /\ Messages' = (        (Messages \ {m}) \union
                                                      {MarkMessageReceivedBy(m, self)})
                                      /\ pc' = [pc EXCEPT ![self] = "ReplicaCommit"]
                                      /\ UNCHANGED lockedQC
                                 ELSE /\ lockedQC' = [lockedQC EXCEPT ![self] = m.justify]
                                      /\ Messages' = (            (Messages \ {m}) \union {
                                                          MarkMessageReceivedBy(m, self),
                                                          CreateMessageTo(Commit, curView[self], (m.justify.block), Null, self, leader)
                                                      })
                                      /\ pc' = [pc EXCEPT ![self] = "ReplicaDecide"]
                       /\ UNCHANGED << NextBlockId, AllBlocks, curView, 
                                       prepareQC, commitQC, committedBlocks >>

ReplicaDecide(self) == /\ pc[self] = "ReplicaDecide"
                       /\ LET leader == Leaders[curView[self]] IN
                            \E m \in FilterMessages(leader, self):
                              IF m.justify.type # Commit \/ m.justify.viewNum # curView[self]
                                 THEN /\ Messages' = (        (Messages \ {m}) \union
                                                      {MarkMessageReceivedBy(m, self)})
                                      /\ pc' = [pc EXCEPT ![self] = "ReplicaCommit"]
                                      /\ UNCHANGED committedBlocks
                                 ELSE /\ committedBlocks' = [committedBlocks EXCEPT ![self] = committedBlocks[self] \union {m.justify.block}]
                                      /\ pc' = [pc EXCEPT ![self] = "Done"]
                                      /\ UNCHANGED Messages
                       /\ UNCHANGED << NextBlockId, AllBlocks, curView, 
                                       prepareQC, lockedQC, commitQC >>

rep(self) == LeaderCheck(self) \/ Propose(self) \/ LeaderPreCommit(self)
                \/ LeaderCommit(self) \/ LeaderDecide(self)
                \/ ReplicaPrepare(self) \/ ReplicaPreCommit(self)
                \/ ReplicaCommit(self) \/ ReplicaDecide(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Replicas: rep(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Replicas : WF_vars(rep(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

TypeInvariant ==
    /\ NextBlockId \in Nat
    /\ \A b \in AllBlocks : b \in BlockType
    /\ \A m \in Messages : m \in MessageType
    /\ \A self \in DOMAIN curView : curView[self] \in Nat
    /\ \A self \in DOMAIN prepareQC : prepareQC[self] \in QCType

AllMessagesEventuallyReceived == <>(
    \A m \in Messages : MessageReceived(m)
)

AllDone == \A self \in ProcSet: pc[self] = "Done"
MsgsReceived == AllDone => \A m \in Messages : MessageReceived(m)

AllEventuallyCommitABlock == AllDone => \A r \in Replicas : Cardinality(committedBlocks[r]) > 0

=============================================================================
