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
RecvVarInit == LET votes == {[block |-> GenesisBlock, vote |-> r]: r \in Nodes} IN 
    [v \in votes |-> Nodes]

(* --algorithm streamlet
variables
    sent = {}; \* all sent messages
    recv = RecvVarInit; \* all received messages
    curEpoch = 1;
    localEpochs = [r \in Nodes |-> curEpoch];
    nextBlockId = 1;
    newBlock = GenesisBlock;

define
    \* Get a set of all messages/blocks received by `node` from a global `recv` variable
    ReceivedMsgsBy(node) == {m \in DOMAIN recv: node \in recv[m]}
    ReceivedBlocksBy(node) == LET msgs == ReceivedMsgsBy(node) IN { m.block: m \in msgs }
    UnreceivedMsgsBy(node) == {m \in sent: node \notin recv[m]}
    LeaderProposed == \E m \in sent: m.block.epoch = curEpoch /\ m.vote = Leaders[curEpoch]
    AlreadyVoted(block, node) == \E m \in sent: m.block = block /\ m.vote = node
    NewProposal(m, node) == /\ m.block.epoch = curEpoch
                            /\ m.vote = Leaders[curEpoch]
                            /\ m.block.parent \in { l.id: l \in LongestNotarizedChainTips(ReceivedMsgsBy(node)) }
    NewProposalYetVoted(m, node) == NewProposal(m, node) /\ ~AlreadyVoted(m.block, node)
end define;

macro CreateBlock(epoch, parent) begin
    newBlock := [id |-> nextBlockId, epoch |-> epoch, parent |-> parent.id];
    nextBlockId := nextBlockId + 1;
end macro

macro RecvMsg(msg) begin
    if msg \in DOMAIN recv then
        recv := [recv EXCEPT ![msg] = @ \union {self}];
    else
        recv := recv @@ msg :> {self};
    end if;
end macro

macro RecvMsgs(msgs) begin
    recv := BatchUpdate(recv, msgs, self);
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
                with tip \in LongestNotarizedChainTips(ReceivedMsgsBy(self)) do 
                    CreateBlock(curEpoch, tip);
                    SendMsg(newBlock);
                end with;
            else
                \* receive others' votes
                with 
                    msgs = UnreceivedMsgsBy(self) 
                do
                    if \E m \in msgs: NewProposalYetVoted(m, self) then 
                        with m = CHOOSE m \in msgs: NewProposalYetVoted(m, self) do 
                            SendMsg(m.block);
                        end with;
                    else
                        RecvMsgs(msgs);                        
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
                await \A m \in sent: (m.block.epoch <= curEpoch) => (CorrectNodes \subseteq recv[m]);
            end if;

            curEpoch := curEpoch + 1;
        end while;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "6d21dc65" /\ chksum(tla) = "948b140d")
VARIABLES sent, recv, curEpoch, localEpochs, nextBlockId, newBlock, pc

(* define statement *)
ReceivedMsgsBy(node) == {m \in DOMAIN recv: node \in recv[m]}
ReceivedBlocksBy(node) == LET msgs == ReceivedMsgsBy(node) IN { m.block: m \in msgs }
UnreceivedMsgsBy(node) == {m \in sent: node \notin recv[m]}
LeaderProposed == \E m \in sent: m.block.epoch = curEpoch /\ m.vote = Leaders[curEpoch]
AlreadyVoted(block, node) == \E m \in sent: m.block = block /\ m.vote = node
NewProposal(m, node) == /\ m.block.epoch = curEpoch
                        /\ m.vote = Leaders[curEpoch]
                        /\ m.block.parent \in { l.id: l \in LongestNotarizedChainTips(ReceivedMsgsBy(node)) }
NewProposalYetVoted(m, node) == NewProposal(m, node) /\ ~AlreadyVoted(m.block, node)


vars == << sent, recv, curEpoch, localEpochs, nextBlockId, newBlock, pc >>

ProcSet == (CorrectNodes) \cup {"timer"}

Init == (* Global variables *)
        /\ sent = {}
        /\ recv = RecvVarInit
        /\ curEpoch = 1
        /\ localEpochs = [r \in Nodes |-> curEpoch]
        /\ nextBlockId = 1
        /\ newBlock = GenesisBlock
        /\ pc = [self \in ProcSet |-> CASE self \in CorrectNodes -> "Start"
                                        [] self = "timer" -> "NextRound"]

Start(self) == /\ pc[self] = "Start"
               /\ IF localEpochs[self] = curEpoch
                     THEN /\ IF Leaders[curEpoch] = self /\ ~LeaderProposed
                                THEN /\ \E tip \in LongestNotarizedChainTips(ReceivedMsgsBy(self)):
                                          /\ newBlock' = [id |-> nextBlockId, epoch |-> curEpoch, parent |-> tip.id]
                                          /\ nextBlockId' = nextBlockId + 1
                                          /\ LET msg == [block |-> newBlock', vote |-> self] IN
                                               /\ sent' = (sent \union {msg})
                                               /\ IF msg \in DOMAIN recv
                                                     THEN /\ recv' = [recv EXCEPT ![msg] = @ \union {self}]
                                                     ELSE /\ recv' = (recv @@ msg :> {self})
                                ELSE /\ LET msgs == UnreceivedMsgsBy(self) IN
                                          IF \E m \in msgs: NewProposalYetVoted(m, self)
                                             THEN /\ LET m == CHOOSE m \in msgs: NewProposalYetVoted(m, self) IN
                                                       LET msg == [block |-> (m.block), vote |-> self] IN
                                                         /\ sent' = (sent \union {msg})
                                                         /\ IF msg \in DOMAIN recv
                                                               THEN /\ recv' = [recv EXCEPT ![msg] = @ \union {self}]
                                                               ELSE /\ recv' = (recv @@ msg :> {self})
                                             ELSE /\ recv' = BatchUpdate(recv, msgs, self)
                                                  /\ sent' = sent
                                     /\ UNCHANGED << nextBlockId, newBlock >>
                          /\ pc' = [pc EXCEPT ![self] = "Start"]
                          /\ UNCHANGED localEpochs
                     ELSE /\ IF curEpoch <= NumEpochs
                                THEN /\ localEpochs' = [localEpochs EXCEPT ![self] = localEpochs[self] + 1]
                                     /\ pc' = [pc EXCEPT ![self] = "Start"]
                                ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                     /\ UNCHANGED localEpochs
                          /\ UNCHANGED << sent, recv, nextBlockId, newBlock >>
               /\ UNCHANGED curEpoch

honest(self) == Start(self)

NextRound == /\ pc["timer"] = "NextRound"
             /\ IF curEpoch <= NumEpochs
                   THEN /\ /\ \A r \in Nodes: localEpochs[r] = curEpoch
                           /\ Leaders[curEpoch] \in CorrectNodes => LeaderProposed
                        /\ IF curEpoch >= GST
                              THEN /\ \A m \in sent: (m.block.epoch <= curEpoch) => (CorrectNodes \subseteq recv[m])
                              ELSE /\ TRUE
                        /\ curEpoch' = curEpoch + 1
                        /\ pc' = [pc EXCEPT !["timer"] = "NextRound"]
                   ELSE /\ pc' = [pc EXCEPT !["timer"] = "Done"]
                        /\ UNCHANGED curEpoch
             /\ UNCHANGED << sent, recv, localEpochs, nextBlockId, newBlock >>

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
    /\ \A m \in DOMAIN recv: m \in MessageType 
    /\ \A n \in Range(recv): n \in SUBSET(Nodes)
    /\ curEpoch \in Nat
    /\ localEpochs \in [Nodes -> Nat]
    /\ nextBlockId \in Nat
    /\ newBlock \in BlockType

\* all received messages should come from sent messages, not out of the blue
OnlyRecvSentMsgs == [](\A m \in DOMAIN recv: m \in sent \/ m.block = GenesisBlock)

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
    \/ \A m \in sent: m.block.epoch < curEpoch => CorrectNodes \subseteq recv[m]
)

\* Theorem 3 of the Streamlet paper:
\* finalized chain of two honest nodes won't conflict with each other (namely a prefix of another)
Consistency == [](
    \A r1, r2 \in CorrectNodes: r1 # r2 => 
        LET 
            chain1 == FinalizedBlocks(ReceivedMsgsBy(r1))
            chain2 == FinalizedBlocks(ReceivedMsgsBy(r2))
        IN
            CheckConflictFree(chain1, chain2)
)
=================================================================
