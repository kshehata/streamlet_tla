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
    LeaderProposed == \E m \in sent: m.block.epoch = curEpoch /\ m.vote = Leaders[curEpoch]
    AlreadyVoted(block, node) == \E m \in sent: m.block = block /\ m.vote = node
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
                    if  /\ m.block.epoch = curEpoch
                        /\ m.vote = Leaders[curEpoch]
                        /\ m.block.parent \in { l.id: l \in LongestNotarizedChainTips(localMsgs[self]) }
                        /\ ~AlreadyVoted(m.block, self) then
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
\* BEGIN TRANSLATION (chksum(pcal) = "b40578ea" /\ chksum(tla) = "f8cdbbf")
VARIABLES sent, curEpoch, localMsgs, localEpochs, nextBlockId, newBlock, pc

(* define statement *)
ReceivedBlocksBy(node) == LET msgs == localMsgs[node] IN { m.block: m \in msgs }
UnreceivedMsgsBy(node) == {m \in sent: m \notin localMsgs[node]}
LeaderProposed == \E m \in sent: m.block.epoch = curEpoch /\ m.vote = Leaders[curEpoch]
AlreadyVoted(block, node) == \E m \in sent: m.block = block /\ m.vote = node
Receivers(m) == {r \in Nodes: m \in localMsgs[r]}


vars == << sent, curEpoch, localMsgs, localEpochs, nextBlockId, newBlock, pc
        >>

ProcSet == (CorrectNodes) \cup {"timer"}

Init == (* Global variables *)
        /\ sent = {}
        /\ curEpoch = 1
        /\ localMsgs = [ r \in Nodes |-> { [block |-> GenesisBlock, vote |-> node]: node \in Nodes } ]
        /\ localEpochs = [r \in Nodes |-> curEpoch]
        /\ nextBlockId = 1
        /\ newBlock = GenesisBlock
        /\ pc = [self \in ProcSet |-> CASE self \in CorrectNodes -> "Start"
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
                                          IF /\ m.block.epoch = curEpoch
                                             /\ m.vote = Leaders[curEpoch]
                                             /\ m.block.parent \in { l.id: l \in LongestNotarizedChainTips(localMsgs[self]) }
                                             /\ ~AlreadyVoted(m.block, self)
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
               /\ UNCHANGED curEpoch

honest(self) == Start(self)

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
                             newBlock >>

Timer == NextRound

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Timer
           \/ (\E self \in CorrectNodes: honest(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in CorrectNodes : WF_vars(honest(self))
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
    \A m \in sent: m.vote \in CorrectNodes =>
        ~(\E m2 \in sent: m2.block.epoch = m.block.epoch /\ m2.block.id # m.block.id)
)

\* before GST, no guarantee on message delivery 
\* after GST, all messages from previous epochs should be delivered to all honest nodes.
PartialSynchrony == [](
    \/ curEpoch <= GST
    \/ \A m \in sent: m.block.epoch < curEpoch => CorrectNodes \subseteq Receivers(m)
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
