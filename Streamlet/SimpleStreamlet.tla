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
    UnreceivedMsgsBy(node) == {m \in sent: m \notin DOMAIN recv \/ node \notin recv[m]}
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

macro SendMsg(block) begin
    with msg = [block |-> block, vote |-> self] do 
        sent := sent \union {msg};
        RecvMsg(msg); \* simulate sending to itself
    end with;
    
end macro

fair process honest \in CorrectNodes
begin
    Propose:
        with
            localEpoch = localEpochs[self],
            msgs = ReceivedMsgsBy(self),
            tip \in LongestNotarizedChainTips(msgs)
        do
            if Leaders[localEpochs[self]] = self then
                \* propose a block
                CreateBlock(localEpochs[self], tip);
                SendMsg(newBlock);
            end if;
        end with;
    Receive:
        with 
            localEpoch = localEpochs[self],
            m \in UnreceivedMsgsBy(self),
        do
            if  /\ m.block.epoch = localEpoch
                /\ m.vote = Leaders[localEpoch]
                /\ m.block.parent \in { l.id: l \in LongestNotarizedChainTips(ReceivedMsgsBy(self)) }
            then
                SendMsg(m.block); 
            else
                RecvMsg(m);
            end if;
        end with;
        goto Receive;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "d87d27b9" /\ chksum(tla) = "7f5c40f4")
VARIABLES sent, recv, curEpoch, localEpochs, nextBlockId, newBlock, pc

(* define statement *)
ReceivedMsgsBy(node) == {m \in DOMAIN recv: node \in recv[m]}
ReceivedBlocksBy(node) == LET msgs == ReceivedMsgsBy(node) IN { m.block: m \in msgs }
UnreceivedMsgsBy(node) == {m \in sent: m \notin DOMAIN recv \/ node \notin recv[m]}


vars == << sent, recv, curEpoch, localEpochs, nextBlockId, newBlock, pc >>

ProcSet == (CorrectNodes)

Init == (* Global variables *)
        /\ sent = {}
        /\ recv = RecvVarInit
        /\ curEpoch = 1
        /\ localEpochs = [r \in Nodes |-> curEpoch]
        /\ nextBlockId = 1
        /\ newBlock = GenesisBlock
        /\ pc = [self \in ProcSet |-> "Propose"]

Propose(self) == /\ pc[self] = "Propose"
                 /\ LET localEpoch == localEpochs[self] IN
                      LET msgs == ReceivedMsgsBy(self) IN
                        \E tip \in LongestNotarizedChainTips(msgs):
                          IF Leaders[localEpochs[self]] = self
                             THEN /\ newBlock' = [id |-> nextBlockId, epoch |-> (localEpochs[self]), parent |-> tip.id]
                                  /\ nextBlockId' = nextBlockId + 1
                                  /\ LET msg == [block |-> newBlock', vote |-> self] IN
                                       /\ sent' = (sent \union {msg})
                                       /\ IF msg \in DOMAIN recv
                                             THEN /\ recv' = [recv EXCEPT ![msg] = @ \union {self}]
                                             ELSE /\ recv' = (recv @@ msg :> {self})
                             ELSE /\ TRUE
                                  /\ UNCHANGED << sent, recv, nextBlockId, 
                                                  newBlock >>
                 /\ pc' = [pc EXCEPT ![self] = "Receive"]
                 /\ UNCHANGED << curEpoch, localEpochs >>

Receive(self) == /\ pc[self] = "Receive"
                 /\ LET localEpoch == localEpochs[self] IN
                      \E m \in UnreceivedMsgsBy(self):
                        IF /\ m.block.epoch = localEpoch
                           /\ m.vote = Leaders[localEpoch]
                           /\ m.block.parent \in { l.id: l \in LongestNotarizedChainTips(ReceivedMsgsBy(self)) }
                           THEN /\ LET msg == [block |-> (m.block), vote |-> self] IN
                                     /\ sent' = (sent \union {msg})
                                     /\ IF msg \in DOMAIN recv
                                           THEN /\ recv' = [recv EXCEPT ![msg] = @ \union {self}]
                                           ELSE /\ recv' = (recv @@ msg :> {self})
                           ELSE /\ IF m \in DOMAIN recv
                                      THEN /\ recv' = [recv EXCEPT ![m] = @ \union {self}]
                                      ELSE /\ recv' = (recv @@ m :> {self})
                                /\ sent' = sent
                 /\ pc' = [pc EXCEPT ![self] = "Receive"]
                 /\ UNCHANGED << curEpoch, localEpochs, nextBlockId, newBlock >>

honest(self) == Propose(self) \/ Receive(self)

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
    /\ \A m \in DOMAIN recv: m \in MessageType 
    /\ \A n \in Range(recv): n \in SUBSET(Nodes)
    /\ curEpoch \in Nat
    /\ localEpochs \in [Nodes -> Nat]
    /\ nextBlockId \in Nat
    /\ newBlock \in BlockType

OnlyRecvSentMsgs == [](\A m \in DOMAIN recv: m \in sent)

=================================================================
