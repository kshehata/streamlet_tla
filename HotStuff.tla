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

macro ReceiveMessage(m) begin
    Messages := (Messages \ {m}) \union 
        {MarkMessageReceivedBy(m, self)};
end macro

macro SendMessage(msg) begin
    Messages := Messages \union {msg};
end macro

macro ReplyWithVote(msg, dest) begin
    Messages := (Messages \ {m}) \union {
        MarkMessageReceivedBy(m, self),
        CreateMessageTo(msg.type, msg.viewNum, msg.block, Null, self, dest)
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
begin
LeaderCheck:
    if (self # Leaders[curView]) then
        goto WaitForProposal;
    end if;

Propose:
    ProposeNewBlock(prepareQC);

LeaderPrecommit:
    while TRUE do
        with m \in { m \in Messages : self \in m.dest /\ self \notin m.received } do
            ReceiveMessage(m);
            if m.type # Prepare \/ m.viewNum # curView then
                print <<"Leader got invalid message:", m>>
            \* TODO: check that block is correct ??
            else
                \* Count votes so far
                \* TODO: shouldn't this check that block and justify are consistent ?
                with votes = ReceivedVotes(Messages, Prepare, curView, self) do
                    if CheckVotesForQC(votes) then
                        prepareQC := GenerateQC(votes);
                        goto Done;
                    end if;
                end with;
            end if;
        end with;
    end while;


WaitForProposal:
    with leader = Leaders[curView],
        m \in { m \in Messages :
            /\ leader = m.vote
            /\ self \in m.dest
            /\ self \notin m.received } do
        if m.type # Prepare \/ m.viewNum # curView then
            print <<"Got invalid proposal:", m>>;
            ReceiveMessage(m);
            goto WaitForProposal;
        elsif ~DirectlyExtends(m.block, m.justify.block) then
            print <<"Got proposal that doesn't extend justify:", m>>;
            ReceiveMessage(m);
            \* TODO: What to do in this case ??
        \* TODO: Need to check SafeNode here
        else
            ReplyWithVote(m, leader);
        end if;
    end with;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "292f3bef" /\ chksum(tla) = "b8ec0908")
VARIABLES NextBlockId, AllBlocks, Messages, pc, curView, prepareQC

vars == << NextBlockId, AllBlocks, Messages, pc, curView, prepareQC >>

ProcSet == (Replicas)

Init == (* Global variables *)
        /\ NextBlockId = 1
        /\ AllBlocks = {GenesisBlock}
        /\ Messages = {}
        (* Process rep *)
        /\ curView = [self \in Replicas |-> 1]
        /\ prepareQC = [self \in Replicas |-> GenesisQC(Prepare)]
        /\ pc = [self \in ProcSet |-> "LeaderCheck"]

LeaderCheck(self) == /\ pc[self] = "LeaderCheck"
                     /\ IF (self # Leaders[curView[self]])
                           THEN /\ pc' = [pc EXCEPT ![self] = "WaitForProposal"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "Propose"]
                     /\ UNCHANGED << NextBlockId, AllBlocks, Messages, curView, 
                                     prepareQC >>

Propose(self) == /\ pc[self] = "Propose"
                 /\ LET newBlock == CreateBlock(NextBlockId, prepareQC[self].block) IN
                      LET proposeMsg == CreateBroadcastMessage(Prepare, curView[self], newBlock, prepareQC[self], self) IN
                        /\ NextBlockId' = NextBlockId + 1
                        /\ AllBlocks' = (AllBlocks \union {newBlock})
                        /\ Messages' = (Messages \union {proposeMsg})
                 /\ pc' = [pc EXCEPT ![self] = "LeaderPrecommit"]
                 /\ UNCHANGED << curView, prepareQC >>

LeaderPrecommit(self) == /\ pc[self] = "LeaderPrecommit"
                         /\ \E m \in { m \in Messages : self \in m.dest /\ self \notin m.received }:
                              /\ Messages' = (        (Messages \ {m}) \union
                                              {MarkMessageReceivedBy(m, self)})
                              /\ IF m.type # Prepare \/ m.viewNum # curView[self]
                                    THEN /\ PrintT(<<"Leader got invalid message:", m>>)
                                         /\ pc' = [pc EXCEPT ![self] = "LeaderPrecommit"]
                                         /\ UNCHANGED prepareQC
                                    ELSE /\ LET votes == ReceivedVotes(Messages', Prepare, curView[self], self) IN
                                              IF CheckVotesForQC(votes)
                                                 THEN /\ prepareQC' = [prepareQC EXCEPT ![self] = GenerateQC(votes)]
                                                      /\ pc' = [pc EXCEPT ![self] = "Done"]
                                                 ELSE /\ pc' = [pc EXCEPT ![self] = "LeaderPrecommit"]
                                                      /\ UNCHANGED prepareQC
                         /\ UNCHANGED << NextBlockId, AllBlocks, curView >>

WaitForProposal(self) == /\ pc[self] = "WaitForProposal"
                         /\ LET leader == Leaders[curView[self]] IN
                              \E m \in   { m \in Messages :
                                       /\ leader = m.vote
                                       /\ self \in m.dest
                                       /\ self \notin m.received }:
                                IF m.type # Prepare \/ m.viewNum # curView[self]
                                   THEN /\ PrintT(<<"Got invalid proposal:", m>>)
                                        /\ Messages' = (        (Messages \ {m}) \union
                                                        {MarkMessageReceivedBy(m, self)})
                                        /\ pc' = [pc EXCEPT ![self] = "WaitForProposal"]
                                   ELSE /\ IF ~DirectlyExtends(m.block, m.justify.block)
                                              THEN /\ PrintT(<<"Got proposal that doesn't extend justify:", m>>)
                                                   /\ Messages' = (        (Messages \ {m}) \union
                                                                   {MarkMessageReceivedBy(m, self)})
                                              ELSE /\ Messages' = (            (Messages \ {m}) \union {
                                                                       MarkMessageReceivedBy(m, self),
                                                                       CreateMessageTo(m.type, m.viewNum, m.block, Null, self, leader)
                                                                   })
                                        /\ pc' = [pc EXCEPT ![self] = "Done"]
                         /\ UNCHANGED << NextBlockId, AllBlocks, curView, 
                                         prepareQC >>

rep(self) == LeaderCheck(self) \/ Propose(self) \/ LeaderPrecommit(self)
                \/ WaitForProposal(self)

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

=============================================================================
