------------------- MODULE SimpleStreamlet ----------------------
EXTENDS Sequences, FiniteSets, Integers, TLC
CONSTANTS CorrectNodes, FaultyNodes, Leaders, GST 

Nodes == CorrectNodes \union FaultyNodes
NumEpochs == Len(Leaders)
NotarizedThreshold == Cardinality(Nodes) - Cardinality(FaultyNodes)
INSTANCE Block WITH Nodes <- Nodes, NotarizedThreshold <- NotarizedThreshold

\* type checking for parameters
ASSUME
    /\ Nodes # {}
    /\ Leaders \in Seq(Nodes)
    /\ GST < NumEpochs
    \* /\ Cardinality(CorrectNodes) > 2 * Cardinality(FaultyNodes)

Range(f) == { f[x] : x \in DOMAIN f }

(* --algorithm streamlet
variables
    sent = {}; \* all sent messages
    curEpoch = 1;
    \* each node keep all msgs/votes seen
    localMsgs = [ r \in Nodes |-> { [block |-> GenesisBlock, vote |-> node]: node \in Nodes } ]; 
    localEpochs = [r \in Nodes |-> curEpoch];
    nextBlockId = 1;
    newBlock = GenesisBlock;

define
    ReceivedBlocksBy(node) == LET msgs == localMsgs[node] IN { m.block: m \in msgs }
    UnreceivedMsgsBy(node) == {m \in sent: m \notin localMsgs[node]}
    AlreadyProposed(node) == \E m \in sent: m.block.epoch = curEpoch /\ m.vote = node
    LeaderProposed == AlreadyProposed(Leaders[curEpoch])
    AlreadyVoted(block, node) == \E m \in sent: m.block = block /\ m.vote = node
    BlocksVotedBy(node) == LET msgs == {m \in sent: m.vote = node} IN {m.block: m \in msgs}
    NewProposal(m, node) == /\ m.block.epoch = curEpoch
                            /\ m.vote = Leaders[curEpoch]
                            /\ m.block.parent \in { l.id: l \in LongestNotarizedChainTips(localMsgs[node]) }
    Receivers(m) == {r \in Nodes: m \in localMsgs[r]}
end define;

macro CreateBlock(epoch, parent) begin
    newBlock := [id |-> nextBlockId, epoch |-> epoch, parent |-> parent.id];
    nextBlockId := nextBlockId + 1;
end macro

macro RecvMsg(msg) begin
    localMsgs := [localMsgs EXCEPT ![self] = @ \union {msg}];
end macro

macro SendMsg(block) begin
    with msg = [block |-> block, vote |-> self] do 
        sent := sent \union {msg};
        RecvMsg(msg); \* simulate sending to itself
    end with;
    
end macro

fair process honest \in CorrectNodes
begin
    Start:
        while localEpochs[self] = curEpoch do 
            if Leaders[curEpoch] = self /\ ~LeaderProposed then
                \* propose a block as a leader
                with tip \in LongestNotarizedChainTips(localMsgs[self]) do 
                    CreateBlock(curEpoch, tip);
                    SendMsg(newBlock);
                end with;
            else
                \* receive others' votes
                with 
                    m \in UnreceivedMsgsBy(self) 
                do
                    if NewProposal(m, self) /\ ~(\E b \in BlocksVotedBy(self): b.epoch = curEpoch) then
                        \* vote for the new proposal
                        SendMsg(m.block); 
                    else
                        RecvMsg(m);
                    end if;
                end with;
            end if;
        end while;

        \* If timer advanced and local replica are out-of-sync, then Sync Epoch first.
        if curEpoch <= NumEpochs then
            localEpochs[self] := localEpochs[self] + 1;
            goto Start;
        end if;
end process;

fair process byzantine \in FaultyNodes
variable
    numBlocksProposedAsLeader = 0;
begin
    ByzStart:
        while localEpochs[self] = curEpoch do
            if Leaders[curEpoch] = self /\ numBlocksProposedAsLeader < 2 then
                \* can propose two conflicting blocks, but always extending from notarized blocks
                with parent \in LongestNotarizedChainTips(localMsgs[self]) do
                    CreateBlock(curEpoch, parent);
                    SendMsg(newBlock);
                    numBlocksProposedAsLeader := numBlocksProposedAsLeader + 1;
                end with;
            else
                with m \in UnreceivedMsgsBy(self) do 
                    if ~AlreadyVoted(m.block, self) then
                        \* simplification: always vote on every block, extreme equivocation 
                        SendMsg(m.block);
                    else
                        RecvMsg(m);
                    end if;
                end with;
            end if;
        end while;    

        numBlocksProposedAsLeader := 0;

        \* If timer advanced and local replica are out-of-sync, then Sync Epoch first.
        if curEpoch <= NumEpochs then
            localEpochs[self] := localEpochs[self] + 1;
            goto ByzStart;
        end if;
end process

fair process Timer = "timer"
begin
    NextRound:
        while curEpoch <= NumEpochs do 
            await /\ \A r \in Nodes: localEpochs[r] = curEpoch
                  /\ Leaders[curEpoch] \in CorrectNodes => LeaderProposed;
            
            if curEpoch >= GST then
                await \A m \in sent: (m.block.epoch <= curEpoch) => (CorrectNodes \subseteq Receivers(m));
            end if;

            curEpoch := curEpoch + 1;
        end while;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "ae996713" /\ chksum(tla) = "2489e9a6")
VARIABLES sent, curEpoch, localMsgs, localEpochs, nextBlockId, newBlock, pc

(* define statement *)
ReceivedBlocksBy(node) == LET msgs == localMsgs[node] IN { m.block: m \in msgs }
UnreceivedMsgsBy(node) == {m \in sent: m \notin localMsgs[node]}
AlreadyProposed(node) == \E m \in sent: m.block.epoch = curEpoch /\ m.vote = node
LeaderProposed == AlreadyProposed(Leaders[curEpoch])
AlreadyVoted(block, node) == \E m \in sent: m.block = block /\ m.vote = node
BlocksVotedBy(node) == LET msgs == {m \in sent: m.vote = node} IN {m.block: m \in msgs}
NewProposal(m, node) == /\ m.block.epoch = curEpoch
                        /\ m.vote = Leaders[curEpoch]
                        /\ m.block.parent \in { l.id: l \in LongestNotarizedChainTips(localMsgs[node]) }
Receivers(m) == {r \in Nodes: m \in localMsgs[r]}

VARIABLE numBlocksProposedAsLeader

vars == << sent, curEpoch, localMsgs, localEpochs, nextBlockId, newBlock, pc, 
           numBlocksProposedAsLeader >>

ProcSet == (CorrectNodes) \cup (FaultyNodes) \cup {"timer"}

Init == (* Global variables *)
        /\ sent = {}
        /\ curEpoch = 1
        /\ localMsgs = [ r \in Nodes |-> { [block |-> GenesisBlock, vote |-> node]: node \in Nodes } ]
        /\ localEpochs = [r \in Nodes |-> curEpoch]
        /\ nextBlockId = 1
        /\ newBlock = GenesisBlock
        (* Process byzantine *)
        /\ numBlocksProposedAsLeader = [self \in FaultyNodes |-> 0]
        /\ pc = [self \in ProcSet |-> CASE self \in CorrectNodes -> "Start"
                                        [] self \in FaultyNodes -> "ByzStart"
                                        [] self = "timer" -> "NextRound"]

Start(self) == /\ pc[self] = "Start"
               /\ IF localEpochs[self] = curEpoch
                     THEN /\ IF Leaders[curEpoch] = self /\ ~LeaderProposed
                                THEN /\ \E tip \in LongestNotarizedChainTips(localMsgs[self]):
                                          /\ newBlock' = [id |-> nextBlockId, epoch |-> curEpoch, parent |-> tip.id]
                                          /\ nextBlockId' = nextBlockId + 1
                                          /\ LET msg == [block |-> newBlock', vote |-> self] IN
                                               /\ sent' = (sent \union {msg})
                                               /\ localMsgs' = [localMsgs EXCEPT ![self] = @ \union {msg}]
                                ELSE /\ \E m \in UnreceivedMsgsBy(self):
                                          IF NewProposal(m, self) /\ ~(\E b \in BlocksVotedBy(self): b.epoch = curEpoch)
                                             THEN /\ LET msg == [block |-> (m.block), vote |-> self] IN
                                                       /\ sent' = (sent \union {msg})
                                                       /\ localMsgs' = [localMsgs EXCEPT ![self] = @ \union {msg}]
                                             ELSE /\ localMsgs' = [localMsgs EXCEPT ![self] = @ \union {m}]
                                                  /\ sent' = sent
                                     /\ UNCHANGED << nextBlockId, newBlock >>
                          /\ pc' = [pc EXCEPT ![self] = "Start"]
                          /\ UNCHANGED localEpochs
                     ELSE /\ IF curEpoch <= NumEpochs
                                THEN /\ localEpochs' = [localEpochs EXCEPT ![self] = localEpochs[self] + 1]
                                     /\ pc' = [pc EXCEPT ![self] = "Start"]
                                ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                     /\ UNCHANGED localEpochs
                          /\ UNCHANGED << sent, localMsgs, nextBlockId, 
                                          newBlock >>
               /\ UNCHANGED << curEpoch, numBlocksProposedAsLeader >>

honest(self) == Start(self)

ByzStart(self) == /\ pc[self] = "ByzStart"
                  /\ IF localEpochs[self] = curEpoch
                        THEN /\ IF Leaders[curEpoch] = self /\ numBlocksProposedAsLeader[self] < 2
                                   THEN /\ \E parent \in LongestNotarizedChainTips(localMsgs[self]):
                                             /\ newBlock' = [id |-> nextBlockId, epoch |-> curEpoch, parent |-> parent.id]
                                             /\ nextBlockId' = nextBlockId + 1
                                             /\ LET msg == [block |-> newBlock', vote |-> self] IN
                                                  /\ sent' = (sent \union {msg})
                                                  /\ localMsgs' = [localMsgs EXCEPT ![self] = @ \union {msg}]
                                             /\ numBlocksProposedAsLeader' = [numBlocksProposedAsLeader EXCEPT ![self] = numBlocksProposedAsLeader[self] + 1]
                                   ELSE /\ \E m \in UnreceivedMsgsBy(self):
                                             IF ~AlreadyVoted(m.block, self)
                                                THEN /\ LET msg == [block |-> (m.block), vote |-> self] IN
                                                          /\ sent' = (sent \union {msg})
                                                          /\ localMsgs' = [localMsgs EXCEPT ![self] = @ \union {msg}]
                                                ELSE /\ localMsgs' = [localMsgs EXCEPT ![self] = @ \union {m}]
                                                     /\ sent' = sent
                                        /\ UNCHANGED << nextBlockId, newBlock, 
                                                        numBlocksProposedAsLeader >>
                             /\ pc' = [pc EXCEPT ![self] = "ByzStart"]
                             /\ UNCHANGED localEpochs
                        ELSE /\ numBlocksProposedAsLeader' = [numBlocksProposedAsLeader EXCEPT ![self] = 0]
                             /\ IF curEpoch <= NumEpochs
                                   THEN /\ localEpochs' = [localEpochs EXCEPT ![self] = localEpochs[self] + 1]
                                        /\ pc' = [pc EXCEPT ![self] = "ByzStart"]
                                   ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                        /\ UNCHANGED localEpochs
                             /\ UNCHANGED << sent, localMsgs, nextBlockId, 
                                             newBlock >>
                  /\ UNCHANGED curEpoch

byzantine(self) == ByzStart(self)

NextRound == /\ pc["timer"] = "NextRound"
             /\ IF curEpoch <= NumEpochs
                   THEN /\ /\ \A r \in Nodes: localEpochs[r] = curEpoch
                           /\ Leaders[curEpoch] \in CorrectNodes => LeaderProposed
                        /\ IF curEpoch >= GST
                              THEN /\ \A m \in sent: (m.block.epoch <= curEpoch) => (CorrectNodes \subseteq Receivers(m))
                              ELSE /\ TRUE
                        /\ curEpoch' = curEpoch + 1
                        /\ pc' = [pc EXCEPT !["timer"] = "NextRound"]
                   ELSE /\ pc' = [pc EXCEPT !["timer"] = "Done"]
                        /\ UNCHANGED curEpoch
             /\ UNCHANGED << sent, localMsgs, localEpochs, nextBlockId, 
                             newBlock, numBlocksProposedAsLeader >>

Timer == NextRound

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Timer
           \/ (\E self \in CorrectNodes: honest(self))
           \/ (\E self \in FaultyNodes: byzantine(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in CorrectNodes : WF_vars(honest(self))
        /\ \A self \in FaultyNodes : WF_vars(byzantine(self))
        /\ WF_vars(Timer)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

TypeOK ==
    /\ \A m \in sent: m \in MessageType
    /\ \A r \in Nodes: \A m \in localMsgs[r]: m \in MessageType
    /\ curEpoch \in Nat
    /\ localEpochs \in [Nodes -> Nat]
    /\ nextBlockId \in Nat
    /\ newBlock \in BlockType

\* all received messages should come from sent messages, not out of the blue
OnlyRecvSentMsgs == [](\A r \in Nodes: \A m \in localMsgs[r]: m \in sent \/ m.block = GenesisBlock)

\* each block should have unique id, namely any two blocks with the same id should be identical
UniqueBlockId ==
    \A m1, m2 \in sent: 
        m1.block.id = m2.block.id =>
            /\ m1.block.epoch = m2.block.epoch 
            /\ m1.block.parent = m2.block.parent

\* global curEpoch should only monotonically increment 1 at each step
MonoIncEpoch == [][curEpoch' = curEpoch + 1]_curEpoch
\* local epoch should at most left behind global curEpoch by 1 (then should be dragged along)
LocalEpochCorrectness == [](\A r \in Nodes: localEpochs[r] = curEpoch \/ localEpochs[r] = curEpoch - 1)
\* when timer move to the next round, an honest leader should at least voted for the current round
HonestLeaderShouldPropose == [](
    \A r \in CorrectNodes:
        LET e == localEpochs[r]
        IN 
            Leaders[e] = r /\ curEpoch > e => 
            \E m \in sent:
                /\ m.block.epoch = e
                /\ m.vote = r
)

\* honest nodes should only voted for one block per epoch
NoDoubleVotePerEpoch == [](
    \A r \in CorrectNodes:
        \A e \in 1..curEpoch: Cardinality({b \in BlocksVotedBy(r): b.epoch = e}) <= 1
)

\* before GST, no guarantee on message delivery 
\* after GST, all messages from previous epochs should be delivered to all honest nodes.
PartialSynchrony == [](
    [curEpoch' > curEpoch => 
        \/ curEpoch <= GST
        \/ \A m \in sent: CorrectNodes \subseteq Receivers(m)]_curEpoch
)

\* Theorem 3 of the Streamlet paper:
\* finalized chain of two honest nodes won't conflict with each other (namely a prefix of another)
Consistency == [](
    \A r1, r2 \in CorrectNodes: r1 # r2 => 
        LET 
            chain1 == FinalizedBlocks(localMsgs[r1])
            chain2 == FinalizedBlocks(localMsgs[r2])
        IN
            CheckConflictFree(chain1, chain2)
)
=================================================================
