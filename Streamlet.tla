----------------------------- MODULE Streamlet -----------------------------

EXTENDS Integers, Sequences, FiniteSets

Maximum(S) == IF S = {} THEN 0
                        ELSE CHOOSE n \in S : \A m \in S : n \geq m
                        
CONSTANT CorrectNodes,  \* Nodes assumed to be correct ("honest")
         FaultyNodes,   \* Set of faulty ("corrupt") nodes
         Leaders,       \* Sequence of leaders in each epoch
         GlobalStabTime \* Epoch of GST

Nodes == CorrectNodes \cup FaultyNodes
NumEpochs == Len(Leaders)
ASSUME 
    /\ Leaders \in Seq(Nodes) 
    /\ FaultyNodes \subseteq Nodes
    /\ GlobalStabTime < NumEpochs

NotarizedThreshold == Cardinality(Nodes) - Cardinality(FaultyNodes)

(***************************************************************************)
(* Defines blocks and operations on blocks                                 *)
(***************************************************************************)
BlockType == [ 
        \* Unique identifier for each block.
        id: Nat,
        \* The epoch number they belong.
        epoch : Nat,
        \* Parents are referenced by their id as well.
        parent : Nat,
        \* Length is the length of the chain from genesis that leads to this block.
        length : Nat,
        \* Representation of signatures on the block
        sigs : SUBSET(Nodes)
    ]

CreateBlock(id, epoch, parent, creator) == [
        id |-> id,
        epoch |-> epoch,
        parent |-> parent.id,
        length |-> parent.length + 1,
        sigs |-> {creator}
    ]

GenesisBlock == [
        id |-> 0,
        epoch |-> 0,
        parent |-> 0,
        length |-> 0,
        sigs |-> Nodes
    ]

SignBlock(block, node) ==
    [block EXCEPT !.sigs = block.sigs \union {node}]

IsNotarized(block) == Cardinality(block.sigs) >= NotarizedThreshold

NotarizedBlocks(blocks) == { b \in blocks : IsNotarized(b) }

LongestNotarizedBlocks(blocks) ==
    LET notarized == NotarizedBlocks(blocks)
    IN { b \in notarized : \A c \in notarized : b.length >= c.length }

IsParent(parent, child) ==
    /\ child.parent = parent.id
    /\ child.length = parent.length + 1
    /\ child.epoch > parent.epoch

RECURSIVE IsFinalized(_,_)
IsFinalized(block, notarized) ==
    \/
        /\ block \in notarized
        /\ \E parent \in notarized: parent.epoch = block.epoch - 1 /\ IsParent(parent, block)
        /\ \E child \in notarized: child.epoch = block.epoch + 1 /\ IsParent(block, child)
    \/
        /\ \E child \in notarized: child.epoch = block.epoch + 1 /\ IsParent(block, child) /\ IsFinalized(child, notarized)
    \/  block = GenesisBlock

FinalizedBlocks(blocks) == { b \in blocks: IsFinalized(b, NotarizedBlocks(blocks)) }

CheckBlockchain(blocks) ==
    LET maxLen == Maximum({ b.length: b \in blocks })
    IN
        /\ \A h \in 0..maxLen: Cardinality({ b \in blocks: b.length = h }) = 1
        /\ Cardinality(blocks) = maxLen + 1
        /\ GenesisBlock \in blocks
        /\ \A b \in (blocks \ {GenesisBlock}): \E parent \in blocks: IsParent(parent, b)

IsPrefixedChain(shortChain, longChain) ==
    LET shortLen == Maximum({ b.length: b \in shortChain })
        longLen == Maximum({ b.length: b \in longChain })
    IN
        /\ CheckBlockchain(shortChain)
        /\ CheckBlockchain(longChain)
        /\ shortLen <= longLen
        /\ \A b \in shortChain: \E b2 \in longChain:
                /\ b.id = b2.id 
                /\ b.epoch = b2.epoch 
                /\ b.length = b2.length
                /\ b.parent = b2.parent
                
(***************************************************************************)

\* Updates a set of blocks with signatures from a given block
UpdateLocalState(localState, m) ==
    LET b == CHOOSE b \in localState : b.epoch = m.epoch
    IN (localState \ {b}) \union { [ b EXCEPT !.sigs = b.sigs \union m.sigs ] }

(***************************************************************************)
(* Messages as just blocks with metadata                                   *)
(***************************************************************************)
MessageType == [
    block : BlockType,
    received : SUBSET(Nodes)
]
(***************************************************************************)

(* --algorithm streamlet
variables
    messages = { };
    currentEpoch = 1;
    localEpochs = [r \in Nodes |-> currentEpoch];
    nextBlockId = 1;

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

fair process honest \in CorrectNodes
variables
    localBlocks = {GenesisBlock}; \* blocks that I have seen
begin
    Propose:
        with
            localEpoch = localEpochs[self],
            parent \in LongestNotarizedBlocks(localBlocks),
            newBlock = CreateBlock(nextBlockId, localEpoch, parent, self)
        do 
            if localEpoch = currentEpoch /\ Leaders[localEpoch] = self then
                \* Propose a new block
                SendMessage(newBlock);
                localBlocks := localBlocks \union { newBlock };
                nextBlockId := nextBlockId + 1;
            end if;
        end with;
    ReceiveOrSyncEpoch:
        while localEpochs[self] = currentEpoch do
            with 
                m \in {m \in messages: self \notin m.received}, 
                b = m.block 
            do
                if b.id \in { l.id : l \in localBlocks } then
                    \* Already seen this block, just update the other new votes on it
                    ReceiveMessage(m); 
                    localBlocks := UpdateLocalState(localBlocks, b);
                elsif  
                    /\ b.epoch = currentEpoch
                    /\ Leaders[currentEpoch] \in b.sigs
                    /\ b.epoch \notin { l.epoch: l \in localBlocks }
                    /\ b.parent \in { l.id : l \in LongestNotarizedBlocks(localBlocks) } then
                    with 
                        parent = CHOOSE l \in LongestNotarizedBlocks(localBlocks): b.parent = l.id,
                        signedBlock = SignBlock(b, self)
                    do
                        if (b.length = parent.length + 1) /\ (b.epoch > parent.epoch) then 
                            \* vote for correct new block and add to localBlocks
                            ReceiveAndSend(m, signedBlock);
                            localBlocks := localBlocks \union {signedBlock};
                        else
                            \* correct leader, correct epoch, correct parent, but incorrect height or epoch field
                            ReceiveMessage(m); 
                            localBlocks := localBlocks \union { b }
                        end if;                        
                    end with;
                else
                    \* case 1: haven't seen, but the block is for past or future epoch
                    \* case 2: haven't seen, block for the current epoch, but from the wrong leader
                    \* case 3: haven't seen, block for the current epoch, from the right leader, but already voted for an eariler block by him
                    \* case 4: haven't seen, current epoch, right leader, haven't voted, but conflicting parent 
                    ReceiveMessage(m); 
                    localBlocks := localBlocks \union { b }
                end if;
            end with;
        end while;

        \* If timer advanced and local replica are out-of-sync, then Sync Epoch first.
        localEpochs[self] := localEpochs[self] + 1;
        if localEpochs[self] <= NumEpochs then
            goto Propose;
        end if;
end process;

fair process Timer = "timer"
begin
    NextRound:
        while currentEpoch <= NumEpochs do
            await \A r \in Nodes: localEpochs[r] = currentEpoch;
            if currentEpoch >= GlobalStabTime then
                await (\A m \in messages : (m.block.epoch <= currentEpoch) => (CorrectNodes \subseteq m.received));
            end if;
            currentEpoch := currentEpoch + 1;
        end while;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "c9105664" /\ chksum(tla) = "ef8284ae")
VARIABLES messages, currentEpoch, localEpochs, nextBlockId, pc, localBlocks

vars == << messages, currentEpoch, localEpochs, nextBlockId, pc, localBlocks
        >>

ProcSet == (CorrectNodes) \cup {"timer"}

Init == (* Global variables *)
        /\ messages = { }
        /\ currentEpoch = 1
        /\ localEpochs = [r \in Nodes |-> currentEpoch]
        /\ nextBlockId = 1
        (* Process honest *)
        /\ localBlocks = [self \in CorrectNodes |-> {GenesisBlock}]
        /\ pc = [self \in ProcSet |-> CASE self \in CorrectNodes -> "Propose"
                                        [] self = "timer" -> "NextRound"]

Propose(self) == /\ pc[self] = "Propose"
                 /\ LET localEpoch == localEpochs[self] IN
                      \E parent \in LongestNotarizedBlocks(localBlocks[self]):
                        LET newBlock == CreateBlock(nextBlockId, localEpoch, parent, self) IN
                          IF localEpoch = currentEpoch /\ Leaders[localEpoch] = self
                             THEN /\ messages' = (            messages \union {[
                                                      block |-> newBlock,
                                                      received |-> {self}
                                                  ]})
                                  /\ localBlocks' = [localBlocks EXCEPT ![self] = localBlocks[self] \union { newBlock }]
                                  /\ nextBlockId' = nextBlockId + 1
                             ELSE /\ TRUE
                                  /\ UNCHANGED << messages, nextBlockId, 
                                                  localBlocks >>
                 /\ pc' = [pc EXCEPT ![self] = "ReceiveOrSyncEpoch"]
                 /\ UNCHANGED << currentEpoch, localEpochs >>

ReceiveOrSyncEpoch(self) == /\ pc[self] = "ReceiveOrSyncEpoch"
                            /\ IF localEpochs[self] = currentEpoch
                                  THEN /\ \E m \in {m \in messages: self \notin m.received}:
                                            LET b == m.block IN
                                              IF b.id \in { l.id : l \in localBlocks[self] }
                                                 THEN /\ messages' = (        (messages \ {m}) \union
                                                                      {[m EXCEPT !.received = m.received \union {self}]})
                                                      /\ localBlocks' = [localBlocks EXCEPT ![self] = UpdateLocalState(localBlocks[self], b)]
                                                 ELSE /\ IF /\ b.epoch = currentEpoch
                                                            /\ Leaders[currentEpoch] \in b.sigs
                                                            /\ b.epoch \notin { l.epoch: l \in localBlocks[self] }
                                                            /\ b.parent \in { l.id : l \in LongestNotarizedBlocks(localBlocks[self]) }
                                                            THEN /\ LET parent == CHOOSE l \in LongestNotarizedBlocks(localBlocks[self]): b.parent = l.id IN
                                                                      LET signedBlock == SignBlock(b, self) IN
                                                                        IF (b.length = parent.length + 1) /\ (b.epoch > parent.epoch)
                                                                           THEN /\ messages' = (        (messages \ {m}) \union
                                                                                                {[m EXCEPT !.received = m.received \union {self}]}
                                                                                                \union {[ block |-> signedBlock, received |-> {self}]})
                                                                                /\ localBlocks' = [localBlocks EXCEPT ![self] = localBlocks[self] \union {signedBlock}]
                                                                           ELSE /\ messages' = (        (messages \ {m}) \union
                                                                                                {[m EXCEPT !.received = m.received \union {self}]})
                                                                                /\ localBlocks' = [localBlocks EXCEPT ![self] = localBlocks[self] \union { b }]
                                                            ELSE /\ messages' = (        (messages \ {m}) \union
                                                                                 {[m EXCEPT !.received = m.received \union {self}]})
                                                                 /\ localBlocks' = [localBlocks EXCEPT ![self] = localBlocks[self] \union { b }]
                                       /\ pc' = [pc EXCEPT ![self] = "ReceiveOrSyncEpoch"]
                                       /\ UNCHANGED localEpochs
                                  ELSE /\ localEpochs' = [localEpochs EXCEPT ![self] = localEpochs[self] + 1]
                                       /\ IF localEpochs'[self] <= NumEpochs
                                             THEN /\ pc' = [pc EXCEPT ![self] = "Propose"]
                                             ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                       /\ UNCHANGED << messages, localBlocks >>
                            /\ UNCHANGED << currentEpoch, nextBlockId >>

honest(self) == Propose(self) \/ ReceiveOrSyncEpoch(self)

NextRound == /\ pc["timer"] = "NextRound"
             /\ IF currentEpoch <= NumEpochs
                   THEN /\ \A r \in Nodes: localEpochs[r] = currentEpoch
                        /\ IF currentEpoch >= GlobalStabTime
                              THEN /\ (\A m \in messages : (m.block.epoch <= currentEpoch) => (CorrectNodes \subseteq m.received))
                              ELSE /\ TRUE
                        /\ currentEpoch' = currentEpoch + 1
                        /\ pc' = [pc EXCEPT !["timer"] = "NextRound"]
                   ELSE /\ pc' = [pc EXCEPT !["timer"] = "Done"]
                        /\ UNCHANGED currentEpoch
             /\ UNCHANGED << messages, localEpochs, nextBlockId, localBlocks >>

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

TypeInvariant == /\ \A m \in messages : m \in MessageType
                 /\ \A n \in Nodes : \A b \in localBlocks[n] : b \in BlockType

MonoIncEpoch == [][currentEpoch' = currentEpoch + 1]_currentEpoch
LocalEpochCorrectness == [](\A r \in Nodes: localEpochs[r] = currentEpoch \/ localEpochs[r] = currentEpoch - 1)
NoDoubleVotePerEpoch ==[](
    \A r \in CorrectNodes:
        \A e \in 0..currentEpoch:
            LET voted == {b \in localBlocks[r]: b.epoch = e /\ r \in b.sigs }
            IN Cardinality(voted) <= 1
)

PartialSynchrony == 
    \/ currentEpoch <= GlobalStabTime
    \/ \A m \in messages: (m.block.epoch = currentEpoch \/ CorrectNodes \subseteq m.received)

Consistency == [](
    \A r1, r2 \in CorrectNodes:
        r1 # r2 => 
            LET chain1 == FinalizedBlocks(localBlocks[r1])
                chain2 == FinalizedBlocks(localBlocks[r2])
            IN
                \/ IsPrefixedChain(chain1, chain2)
                \/ IsPrefixedChain(chain2, chain1)
)

\* Not really liveness, just check that all nodes got block 1
\* Only works if network is synchronous
\* TODO: fix this
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
