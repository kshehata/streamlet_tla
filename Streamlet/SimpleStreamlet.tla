------------------- MODULE SimpleStreamlet ----------------------
EXTENDS Sequences, FiniteSets, Integers
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

(* --algorithm streamlet
variables
    sent = {}; \* all sent messages
    recv = {}; \* all received messages
    curEpoch = 1;
    localEpochs = [r \in Nodes |-> curEpoch];
    nextBlockId = 1;
    newBlock = GenesisBlock;

define
    \* Get a set of all messages/blocks received by `node` from a global `recv` variable
    ReceivedMsgsBy(node) == {m \in DOMAIN recv: node \in recv[m]}
    ReceivedBlocksBy(node) == LET msgs == ReceivedMsgsBy(node) IN { m.block: m \in msgs }

end define;

macro CreateBlock(epoch, parent) begin
    newBlock := [id |-> nextBlockId, epoch |-> epoch, parent |-> parent.id];
    nextBlockId := nextBlockId + 1;
end macro

fair process honest \in CorrectNodes
begin
    Propose:
        skip;
        \* with
        \*     localEpoch = localEpochs[self],
        \*     parent = Longest
        \* do
        \*     if Leaders[localEpochs[self]] = self then
        \*         \* propose a block
        \*         CreateBlock(localEpochs[self], );
        \*     end if;
        \* end with
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "80e7a054" /\ chksum(tla) = "f865f109")
VARIABLES sent, recv, curEpoch, localEpochs, nextBlockId, newBlock, pc

(* define statement *)
ReceivedMsgsBy(node) == {m \in DOMAIN recv: node \in recv[m]}
ReceivedBlocksBy(node) == LET msgs == ReceivedMsgsBy(node) IN { m.block: m \in msgs }


vars == << sent, recv, curEpoch, localEpochs, nextBlockId, newBlock, pc >>

ProcSet == (CorrectNodes)

Init == (* Global variables *)
        /\ sent = {}
        /\ recv = {}
        /\ curEpoch = 1
        /\ localEpochs = [r \in Nodes |-> curEpoch]
        /\ nextBlockId = 1
        /\ newBlock = GenesisBlock
        /\ pc = [self \in ProcSet |-> "Propose"]

Propose(self) == /\ pc[self] = "Propose"
                 /\ TRUE
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << sent, recv, curEpoch, localEpochs, 
                                 nextBlockId, newBlock >>

honest(self) == Propose(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in CorrectNodes: honest(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in CorrectNodes : WF_vars(honest(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

TypeOK ==
    /\ \A m \in sent: m \in MessageType
    /\ \A m \in recv: m \in [MessageType -> SUBSET(Nodes)]

OnlyRecvSentMsgs == [](\A m \in DOMAIN recv: m \in sent)
=================================================================
