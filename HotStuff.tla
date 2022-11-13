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

    \* Messages broadcast to all replicas
    Messages = {};

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

macro ReceiveAndSendQC(msg, type, qc) begin
    Messages := (Messages \ {msg}) \union {
        MarkMessageReceivedBy(msg, self),
        CreateBroadcastMessage(type, curView, Null, qc, self)
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

fair process rep \in Replicas
variables
    curView = 1;
    prepareQC = GenesisQC(Prepare);
    lockedQC = GenesisQC(PreCommit);
    committedBlocks = {};

begin
LeaderCheck:
    if (self # Leaders[curView]) then
        goto ReplicaPrepare;
    end if;

Propose:
    ProposeNewBlock(prepareQC);

LeaderPrecommit:
    while TRUE do
        with m \in { m \in Messages : self \in m.dest /\ self \notin m.received } do
            if m.type # Prepare \/ m.viewNum # curView then
                \* print <<"Leader got invalid message:", m>>;
                ReceiveMessage(m);
            \* TODO: check that block is correct ??
            else
                \* Count votes so far
                \* TODO: shouldn't this check that block and justify are consistent ?
                with votes = ReceivedVotes(Messages, Prepare, curView, self) \union {m} do
                    if CheckVotesForQC(votes) then
                        prepareQC := GenerateQC(votes);
                        ReceiveAndSendQC(m, PreCommit, prepareQC);
                        goto LeaderCommit;
                    else
                        ReceiveMessage(m);
                    end if;
                end with;
            end if;
        end with;
    end while;

LeaderCommit:
    while TRUE do
        with m \in { m \in Messages : self \in m.dest /\ self \notin m.received } do
            if m.type # PreCommit \/ m.viewNum # curView then
                \* print <<"Leader got invalid message:", m>>;
                ReceiveMessage(m);
            \* TODO: check that block is correct ??
            else
                \* Count votes so far
                \* TODO: shouldn't this check that block and justify are consistent ?
                \* print <<"Recv vote:",m>>;
                with votes = ReceivedVotes(Messages, PreCommit, curView, self) \union {m} do
                    if CheckVotesForQC(votes) then
                        lockedQC := GenerateQC(votes);
                        ReceiveAndSendQC(m, Commit, lockedQC);
                        goto LeaderDecide;
                    else
                        ReceiveMessage(m);
                    end if;
                end with;
            end if;
        end with;
    end while;

LeaderDecide:
    while TRUE do
        with m \in { m \in Messages : self \in m.dest /\ self \notin m.received } do
            if m.type # Commit \/ m.viewNum # curView then
                print <<"Leader got invalid message:", m>>;
                ReceiveMessage(m);
            \* TODO: check that block is correct ??
            else
                \* Count votes so far
                \* TODO: shouldn't this check that block and justify are consistent ?
                \* print <<"Recv vote:",m>>;
                with votes = ReceivedVotes(Messages, Commit, curView, self) \union {m} do
                    if CheckVotesForQC(votes) then
                        committedBlocks := committedBlocks \union {m.block};
                        ReceiveAndSendQC(m, Decide, GenerateQC(votes));
                        goto Done;
                    else
                        ReceiveMessage(m);
                    end if;
                end with;
            end if;
        end with;
    end while;

ReplicaPrepare:
    with leader = Leaders[curView],
        m \in { m \in Messages :
            /\ leader = m.vote
            /\ self \in m.dest
            /\ self \notin m.received } do
        if m.type # Prepare \/ m.viewNum # curView then
            \* print <<"Got invalid proposal:", m>>;
            ReceiveMessage(m);
            goto ReplicaPrepare;
        elsif ~DirectlyExtends(m.block, m.justify.block) then
            print <<"Got proposal that doesn't extend justify:", m>>;
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
        m \in { m \in Messages :
            /\ leader = m.vote
            /\ self \in m.dest
            /\ self \notin m.received } do
        \* TODO: Should this check the message as well ??
        if m.justify.type # Prepare \/ m.justify.viewNum # curView then
            \* print <<"Got invalid PreCommit message:", m>>;
            ReceiveMessage(m);
            goto ReplicaPreCommit;
        else
            prepareQC := m.justify;
            ReplyWithVote(m, PreCommit, m.justify.block, leader);
        end if;
    end with;

ReplicaCommit:
    with leader = Leaders[curView],
        m \in { m \in Messages :
            /\ leader = m.vote
            /\ self \in m.dest
            /\ self \notin m.received } do
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
        m \in { m \in Messages :
            /\ leader = m.vote
            /\ self \in m.dest
            /\ self \notin m.received } do
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
\* BEGIN TRANSLATION (chksum(pcal) = "da4abf26" /\ chksum(tla) = "e01102c5")
VARIABLES NextBlockId, AllBlocks, Messages, pc, curView, prepareQC, lockedQC, 
          committedBlocks

vars == << NextBlockId, AllBlocks, Messages, pc, curView, prepareQC, lockedQC, 
           committedBlocks >>

ProcSet == (Replicas)

Init == (* Global variables *)
        /\ NextBlockId = 1
        /\ AllBlocks = {GenesisBlock}
        /\ Messages = {}
        (* Process rep *)
        /\ curView = [self \in Replicas |-> 1]
        /\ prepareQC = [self \in Replicas |-> GenesisQC(Prepare)]
        /\ lockedQC = [self \in Replicas |-> GenesisQC(PreCommit)]
        /\ committedBlocks = [self \in Replicas |-> {}]
        /\ pc = [self \in ProcSet |-> "LeaderCheck"]

LeaderCheck(self) == /\ pc[self] = "LeaderCheck"
                     /\ IF (self # Leaders[curView[self]])
                           THEN /\ pc' = [pc EXCEPT ![self] = "ReplicaPrepare"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "Propose"]
                     /\ UNCHANGED << NextBlockId, AllBlocks, Messages, curView, 
                                     prepareQC, lockedQC, committedBlocks >>

Propose(self) == /\ pc[self] = "Propose"
                 /\ LET newBlock == CreateBlock(NextBlockId, prepareQC[self].block) IN
                      LET proposeMsg == CreateBroadcastMessage(Prepare, curView[self], newBlock, prepareQC[self], self) IN
                        /\ NextBlockId' = NextBlockId + 1
                        /\ AllBlocks' = (AllBlocks \union {newBlock})
                        /\ Messages' = (Messages \union {proposeMsg})
                 /\ pc' = [pc EXCEPT ![self] = "LeaderPrecommit"]
                 /\ UNCHANGED << curView, prepareQC, lockedQC, committedBlocks >>

LeaderPrecommit(self) == /\ pc[self] = "LeaderPrecommit"
                         /\ \E m \in { m \in Messages : self \in m.dest /\ self \notin m.received }:
                              IF m.type # Prepare \/ m.viewNum # curView[self]
                                 THEN /\ Messages' = (        (Messages \ {m}) \union
                                                      {MarkMessageReceivedBy(m, self)})
                                      /\ pc' = [pc EXCEPT ![self] = "LeaderPrecommit"]
                                      /\ UNCHANGED prepareQC
                                 ELSE /\ LET votes == ReceivedVotes(Messages, Prepare, curView[self], self) \union {m} IN
                                           IF CheckVotesForQC(votes)
                                              THEN /\ prepareQC' = [prepareQC EXCEPT ![self] = GenerateQC(votes)]
                                                   /\ Messages' = (            (Messages \ {m}) \union {
                                                                       MarkMessageReceivedBy(m, self),
                                                                       CreateBroadcastMessage(PreCommit, curView[self], Null, prepareQC'[self], self)
                                                                   })
                                                   /\ pc' = [pc EXCEPT ![self] = "LeaderCommit"]
                                              ELSE /\ Messages' = (        (Messages \ {m}) \union
                                                                   {MarkMessageReceivedBy(m, self)})
                                                   /\ pc' = [pc EXCEPT ![self] = "LeaderPrecommit"]
                                                   /\ UNCHANGED prepareQC
                         /\ UNCHANGED << NextBlockId, AllBlocks, curView, 
                                         lockedQC, committedBlocks >>

LeaderCommit(self) == /\ pc[self] = "LeaderCommit"
                      /\ \E m \in { m \in Messages : self \in m.dest /\ self \notin m.received }:
                           IF m.type # PreCommit \/ m.viewNum # curView[self]
                              THEN /\ Messages' = (        (Messages \ {m}) \union
                                                   {MarkMessageReceivedBy(m, self)})
                                   /\ pc' = [pc EXCEPT ![self] = "LeaderCommit"]
                                   /\ UNCHANGED lockedQC
                              ELSE /\ LET votes == ReceivedVotes(Messages, PreCommit, curView[self], self) \union {m} IN
                                        IF CheckVotesForQC(votes)
                                           THEN /\ lockedQC' = [lockedQC EXCEPT ![self] = GenerateQC(votes)]
                                                /\ Messages' = (            (Messages \ {m}) \union {
                                                                    MarkMessageReceivedBy(m, self),
                                                                    CreateBroadcastMessage(Commit, curView[self], Null, lockedQC'[self], self)
                                                                })
                                                /\ pc' = [pc EXCEPT ![self] = "LeaderDecide"]
                                           ELSE /\ Messages' = (        (Messages \ {m}) \union
                                                                {MarkMessageReceivedBy(m, self)})
                                                /\ pc' = [pc EXCEPT ![self] = "LeaderCommit"]
                                                /\ UNCHANGED lockedQC
                      /\ UNCHANGED << NextBlockId, AllBlocks, curView, 
                                      prepareQC, committedBlocks >>

LeaderDecide(self) == /\ pc[self] = "LeaderDecide"
                      /\ \E m \in { m \in Messages : self \in m.dest /\ self \notin m.received }:
                           IF m.type # Commit \/ m.viewNum # curView[self]
                              THEN /\ PrintT(<<"Leader got invalid message:", m>>)
                                   /\ Messages' = (        (Messages \ {m}) \union
                                                   {MarkMessageReceivedBy(m, self)})
                                   /\ pc' = [pc EXCEPT ![self] = "LeaderDecide"]
                                   /\ UNCHANGED committedBlocks
                              ELSE /\ LET votes == ReceivedVotes(Messages, Commit, curView[self], self) \union {m} IN
                                        IF CheckVotesForQC(votes)
                                           THEN /\ committedBlocks' = [committedBlocks EXCEPT ![self] = committedBlocks[self] \union {m.block}]
                                                /\ Messages' = (            (Messages \ {m}) \union {
                                                                    MarkMessageReceivedBy(m, self),
                                                                    CreateBroadcastMessage(Decide, curView[self], Null, (GenerateQC(votes)), self)
                                                                })
                                                /\ pc' = [pc EXCEPT ![self] = "Done"]
                                           ELSE /\ Messages' = (        (Messages \ {m}) \union
                                                                {MarkMessageReceivedBy(m, self)})
                                                /\ pc' = [pc EXCEPT ![self] = "LeaderDecide"]
                                                /\ UNCHANGED committedBlocks
                      /\ UNCHANGED << NextBlockId, AllBlocks, curView, 
                                      prepareQC, lockedQC >>

ReplicaPrepare(self) == /\ pc[self] = "ReplicaPrepare"
                        /\ LET leader == Leaders[curView[self]] IN
                             \E m \in   { m \in Messages :
                                      /\ leader = m.vote
                                      /\ self \in m.dest
                                      /\ self \notin m.received }:
                               IF m.type # Prepare \/ m.viewNum # curView[self]
                                  THEN /\ Messages' = (        (Messages \ {m}) \union
                                                       {MarkMessageReceivedBy(m, self)})
                                       /\ pc' = [pc EXCEPT ![self] = "ReplicaPrepare"]
                                  ELSE /\ IF ~DirectlyExtends(m.block, m.justify.block)
                                             THEN /\ PrintT(<<"Got proposal that doesn't extend justify:", m>>)
                                                  /\ Messages' = (        (Messages \ {m}) \union
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
                                        prepareQC, lockedQC, committedBlocks >>

ReplicaPreCommit(self) == /\ pc[self] = "ReplicaPreCommit"
                          /\ LET leader == Leaders[curView[self]] IN
                               \E m \in   { m \in Messages :
                                        /\ leader = m.vote
                                        /\ self \in m.dest
                                        /\ self \notin m.received }:
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
                                          lockedQC, committedBlocks >>

ReplicaCommit(self) == /\ pc[self] = "ReplicaCommit"
                       /\ LET leader == Leaders[curView[self]] IN
                            \E m \in   { m \in Messages :
                                     /\ leader = m.vote
                                     /\ self \in m.dest
                                     /\ self \notin m.received }:
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
                                       prepareQC, committedBlocks >>

ReplicaDecide(self) == /\ pc[self] = "ReplicaDecide"
                       /\ LET leader == Leaders[curView[self]] IN
                            \E m \in   { m \in Messages :
                                     /\ leader = m.vote
                                     /\ self \in m.dest
                                     /\ self \notin m.received }:
                              IF m.justify.type # Commit \/ m.justify.viewNum # curView[self]
                                 THEN /\ Messages' = (        (Messages \ {m}) \union
                                                      {MarkMessageReceivedBy(m, self)})
                                      /\ pc' = [pc EXCEPT ![self] = "ReplicaCommit"]
                                      /\ UNCHANGED committedBlocks
                                 ELSE /\ committedBlocks' = [committedBlocks EXCEPT ![self] = committedBlocks[self] \union {m.justify.block}]
                                      /\ pc' = [pc EXCEPT ![self] = "Done"]
                                      /\ UNCHANGED Messages
                       /\ UNCHANGED << NextBlockId, AllBlocks, curView, 
                                       prepareQC, lockedQC >>

rep(self) == LeaderCheck(self) \/ Propose(self) \/ LeaderPrecommit(self)
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
