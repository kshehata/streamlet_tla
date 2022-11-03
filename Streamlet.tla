----------------------------- MODULE Streamlet -----------------------------

EXTENDS Integers, Sequences, FiniteSets

Maximum(S) == IF S = {} THEN -1
                        ELSE CHOOSE n \in S : \A m \in S : n \geq m
                        
CONSTANT CorrectNodes,  \* Nodes assumed to be correct ("honest")
         FaultyNodes,   \* Set of faulty ("corrupt") nodes
         Leaders,       \* Sequence of leaders in each epoch
         GlobalStabTime \* Epoch of GST

Nodes == CorrectNodes \cup FaultyNodes
ASSUME Leaders \in Seq(Nodes) /\ FaultyNodes \subseteq Nodes

NotarizedThreshold == Cardinality(Nodes) - Cardinality(FaultyNodes)

(***************************************************************************)
(* Defines blocks and operations on blocks                                 *)
(***************************************************************************)
Blocks == [ \* Blocks are represented as the epoch number they belong.
            epoch : Nat,
            \* Parents are referenced by epoch number as well.
            parent : Nat,
            \* Length is the length of the chain from genesis that leads to this block.
            length : Nat,
            \* Representation of signatures on the block
            sigs : SUBSET(Nodes)
          ]

CreateBlock(epoch, parent, length, n) == [
        epoch |-> epoch,
        parent |-> parent,
        length |-> length,
        sigs |-> {n}
    ]

GenesisBlock == [
        epoch |-> 0,
        parent |-> 0,
        length |-> 0,
        sigs |-> Nodes
    ]

ExtendBlock(epoch, block, node) ==
    CreateBlock(epoch, block.epoch, block.length + 1, node)

SignBlock(block, node) ==
    [block EXCEPT !.sigs = block.sigs \union {node}]

IsNotarized(block) == Cardinality(block.sigs) >= NotarizedThreshold

NotarizedBlocks(blocks) == { b \in blocks : IsNotarized(b) }

LongestNotarizedBlocks(blocks) ==
    LET notarized == NotarizedBlocks(blocks)
    IN { b \in notarized : \A c \in notarized : b.length >= c.length }

IsParent(parent, child) ==
    /\ child.parent = parent.epoch
    /\ child.length = parent.length + 1
    /\ child.epoch > parent.epoch

RECURSIVE IsFinalized(_,_)
IsFinalized(block, notarized) ==
    \/
        /\ \E parent \in notarized: parent.epoch = block.epoch - 1 /\ IsParent(parent, block)
        /\ \E child \in notarized: child.epoch = block.epoch + 1 /\ IsParent(block, child)
    \/
        /\ \E child \in notarized: child.epoch = block.epoch + 1 /\ IsParent(block, child) /\ IsFinalized(child, notarized)

FinalizedBlocks(blocks) == { b \in blocks: IsFinalized(b, NotarizedBlocks(blocks)) }

(***************************************************************************)

\* Updates a set of blocks with signatures from a given block
UpdateLocalState(localState, m) ==
  LET b == CHOOSE b \in localState : b.epoch = m.epoch
  IN (localState \ {b}) \union { [ b EXCEPT !.sigs = b.sigs \union m.sigs ] }

(***************************************************************************)
(* Messages as just blocks with metadata                                   *)
(***************************************************************************)
Messages == [
    block : Blocks,
    received : SUBSET(Nodes)
]
(***************************************************************************)

(* --algorithm streamlet
variables
    messages = { };
    currentEpoch = 1;

macro SendMessage(b) begin
    messages := messages \union {[
        block |-> b,
        received |-> {self}
    ]};
end macro

macro ReceiveMessage(m) begin
    messages := (messages \ {m}) \union 
        {[m EXCEPT !.received = m.received \union {self}]};
end macro

macro ReceiveAndSend(receivedMsg, blockToSend) begin
    messages := (messages \ {receivedMsg}) \union 
        {[receivedMsg EXCEPT !.received = receivedMsg.received \union {self}]}
        \union {[ block |-> blockToSend, received |-> {self}]};
end macro

fair process replica \in Nodes
variables
    i = 1;
    localBlocks = {GenesisBlock};
begin
  Start:
    if Leaders[currentEpoch] = self then
        \* Propose a new block
        with
            parent \in LongestNotarizedBlocks(localBlocks),
            newBlock = ExtendBlock(currentEpoch, parent, self)
        do
            SendMessage(newBlock);
            localBlocks := localBlocks \union { newBlock };
        end with;
    end if;
    i := i + 1;

  ReplicaReceive:
    while (i > currentEpoch) do
        with m \in messages, b = m.block do
            if b.epoch \in { l.epoch : l \in localBlocks } then
                \* Already seen this block, just update it
                \* TODO: check length and parent correct ?
                \* TODO: need to check that current epoch can be signed ?
                ReceiveMessage(m);
                localBlocks := UpdateLocalState(localBlocks, b);
            else
            if  /\ b.epoch = currentEpoch
                /\ Leaders[currentEpoch] \in b.sigs
                /\ b.parent \in { l.epoch : l \in LongestNotarizedBlocks(localBlocks) } then
                \* TODO: check that length is correct
                \* Correctly extends local longest chain
                with signedBlock = SignBlock(b, self) do
                    ReceiveAndSend(m, signedBlock);
                    localBlocks := localBlocks \union {signedBlock};
                end with;
            else
                \* can't sign block, so just add it to local state
                ReceiveMessage(m);
                localBlocks := localBlocks \union { b }
            end if;
            end if;
        end with;
    end while;
    if (i < Len(Leaders) + 1) then
        goto Start;
    end if
end process;


fair process Timer = "timer"
begin
    NextRound:
        while (currentEpoch < Len(Leaders) + 1) do
            await(\E m \in messages : (m.block.epoch = currentEpoch /\ Leaders[currentEpoch] \in m.block.sigs));
            if (currentEpoch >= GlobalStabTime) then
                await(\A m \in messages : (m.block.epoch <= currentEpoch) => (m.received = Nodes));
            end if;
            currentEpoch := currentEpoch + 1;
        end while;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "b8667e3e" /\ chksum(tla) = "b73250de")
VARIABLES messages, currentEpoch, pc, i, localBlocks

vars == << messages, currentEpoch, pc, i, localBlocks >>

ProcSet == (Nodes) \cup {"timer"}

Init == (* Global variables *)
        /\ messages = { }
        /\ currentEpoch = 1
        (* Process replica *)
        /\ i = [self \in Nodes |-> 1]
        /\ localBlocks = [self \in Nodes |-> {GenesisBlock}]
        /\ pc = [self \in ProcSet |-> CASE self \in Nodes -> "Start"
                                        [] self = "timer" -> "NextRound"]

Start(self) == /\ pc[self] = "Start"
               /\ IF Leaders[currentEpoch] = self
                     THEN /\ \E parent \in LongestNotarizedBlocks(localBlocks[self]):
                               LET newBlock == ExtendBlock(currentEpoch, parent, self) IN
                                 /\ messages' = (            messages \union {[
                                                     block |-> newBlock,
                                                     received |-> {self}
                                                 ]})
                                 /\ localBlocks' = [localBlocks EXCEPT ![self] = localBlocks[self] \union { newBlock }]
                     ELSE /\ TRUE
                          /\ UNCHANGED << messages, localBlocks >>
               /\ i' = [i EXCEPT ![self] = i[self] + 1]
               /\ pc' = [pc EXCEPT ![self] = "ReplicaReceive"]
               /\ UNCHANGED currentEpoch

ReplicaReceive(self) == /\ pc[self] = "ReplicaReceive"
                        /\ IF (i[self] > currentEpoch)
                              THEN /\ \E m \in messages:
                                        LET b == m.block IN
                                          IF b.epoch \in { l.epoch : l \in localBlocks[self] }
                                             THEN /\ messages' = (        (messages \ {m}) \union
                                                                  {[m EXCEPT !.received = m.received \union {self}]})
                                                  /\ localBlocks' = [localBlocks EXCEPT ![self] = UpdateLocalState(localBlocks[self], b)]
                                             ELSE /\ IF /\ b.epoch = currentEpoch
                                                        /\ Leaders[currentEpoch] \in b.sigs
                                                        /\ b.parent \in { l.epoch : l \in LongestNotarizedBlocks(localBlocks[self]) }
                                                        THEN /\ LET signedBlock == SignBlock(b, self) IN
                                                                  /\ messages' = (        (messages \ {m}) \union
                                                                                  {[m EXCEPT !.received = m.received \union {self}]}
                                                                                  \union {[ block |-> signedBlock, received |-> {self}]})
                                                                  /\ localBlocks' = [localBlocks EXCEPT ![self] = localBlocks[self] \union {signedBlock}]
                                                        ELSE /\ messages' = (        (messages \ {m}) \union
                                                                             {[m EXCEPT !.received = m.received \union {self}]})
                                                             /\ localBlocks' = [localBlocks EXCEPT ![self] = localBlocks[self] \union { b }]
                                   /\ pc' = [pc EXCEPT ![self] = "ReplicaReceive"]
                              ELSE /\ IF (i[self] < Len(Leaders) + 1)
                                         THEN /\ pc' = [pc EXCEPT ![self] = "Start"]
                                         ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                   /\ UNCHANGED << messages, localBlocks >>
                        /\ UNCHANGED << currentEpoch, i >>

replica(self) == Start(self) \/ ReplicaReceive(self)

NextRound == /\ pc["timer"] = "NextRound"
             /\ IF (currentEpoch < Len(Leaders) + 1)
                   THEN /\ (\E m \in messages : (m.block.epoch = currentEpoch /\ Leaders[currentEpoch] \in m.block.sigs))
                        /\ IF (currentEpoch >= GlobalStabTime)
                              THEN /\ (\A m \in messages : (m.block.epoch <= currentEpoch) => (m.received = Nodes))
                              ELSE /\ TRUE
                        /\ currentEpoch' = currentEpoch + 1
                        /\ pc' = [pc EXCEPT !["timer"] = "NextRound"]
                   ELSE /\ pc' = [pc EXCEPT !["timer"] = "Done"]
                        /\ UNCHANGED currentEpoch
             /\ UNCHANGED << messages, i, localBlocks >>

Timer == NextRound

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Timer
           \/ (\E self \in Nodes: replica(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Nodes : WF_vars(replica(self))
        /\ WF_vars(Timer)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

TypeInvariant == /\ \A m \in messages : m \in Messages
                 /\ \A n \in Nodes : \A b \in localBlocks[n] : b \in Blocks

\* Not really liveness, just check that all nodes got block 1
\* Only works if network is synchronous
Liveness == <>(
    \A n \in Nodes :
        \E b \in localBlocks[n] :
            /\ b.epoch > 0
            /\ b.length > 0
            /\ b.sigs = Nodes
)
 

=============================================================================
\* Modification History
\* Last modified Fri Oct 07 18:34:03 SGT 2022 by kshehata
\* Created Tue Sep 06 19:56:44 SGT 2022 by kshehata
