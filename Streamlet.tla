----------------------------- MODULE Streamlet -----------------------------

EXTENDS Integers, Sequences, FiniteSets

Maximum(S) == IF S = {} THEN 0
                        ELSE CHOOSE n \in S : \A m \in S : n \geq m
                        
CONSTANT 
    CorrectNodes,   \* Nodes assumed to be correct ("honest")
    FaultyNodes,    \* Set of faulty ("corrupt") nodes
    Leaders,        \* Sequence of leaders in each epoch
    GlobalStabTime, \* Epoch of GST
    TrustedCreator  \* Model value for genesis block creator 

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
        creator : Nodes \union {TrustedCreator}
    ]

GenesisBlock == [
        id |-> 0,
        epoch |-> 0,
        parent |-> 0,
        length |-> 0,
        creator |-> TrustedCreator
    ]

\* Structure of localBlocks each replica keep locally
LocalBlockType == [
    payload: BlockType,
    sigs: SUBSET(Nodes)
]

SignBlock(b, signer) ==
    [block |-> b, vote |-> signer, received |-> {signer}]

IsNotarized(block) == Cardinality(block.sigs) >= NotarizedThreshold

NotarizedBlocks(blocks) == { b \in blocks : IsNotarized(b) }

LongestNotarizedBlocks(blocks) ==
    LET notarized == NotarizedBlocks(blocks)
    IN { b \in notarized : \A c \in notarized : b.payload.length >= c.payload.length }

IsParent(parent, child) ==
    /\ child.parent = parent.id
    /\ child.length = parent.length + 1
    /\ child.epoch > parent.epoch

RECURSIVE IsFinalized(_,_)
IsFinalized(block, notarized) ==
    \/
        /\ block \in notarized
        /\ \E parent \in notarized: parent.payload.epoch = block.payload.epoch - 1 /\ IsParent(parent.payload, block.payload)
        /\ \E child \in notarized: child.payload.epoch = block.payload.epoch + 1 /\ IsParent(block.payload, child.payload)
    \/
        \E child \in notarized: 
            /\ child.payload.epoch = block.payload.epoch + 1 
            /\ IsParent(block.payload, child.payload) 
            /\ IsFinalized(child, notarized)
    \/  block.payload = GenesisBlock

FinalizedBlocks(blocks) == { b \in blocks: IsFinalized(b, NotarizedBlocks(blocks)) }

CheckBlockchain(blocks) ==
    LET 
        maxLen == Maximum({ b.payload.length: b \in blocks })
        genesis == [payload |-> GenesisBlock, sigs |-> Nodes]
    IN
        /\ \A h \in 0..maxLen: Cardinality({ b \in blocks: b.payload.length = h }) = 1
        /\ Cardinality(blocks) = maxLen + 1
        /\ genesis \in blocks
        /\ \A b \in (blocks \ {genesis}): \E parent \in blocks: IsParent(parent.payload, b.payload)

IsPrefixedChain(shortChain, longChain) ==
    LET shortLen == Maximum({ b.payload.length: b \in shortChain })
        longLen == Maximum({ b.payload.length: b \in longChain })
    IN
        /\ CheckBlockchain(shortChain)
        /\ CheckBlockchain(longChain)
        /\ shortLen <= longLen
        /\ \A b \in shortChain: \E b2 \in longChain:
                /\ b.payload.id = b2.payload.id 
                /\ b.payload.epoch = b2.payload.epoch 
                /\ b.payload.length = b2.payload.length
                /\ b.payload.parent = b2.payload.parent
                
(***************************************************************************)

(***************************************************************************)
(* Message is a single vote on a block and receivers' ACK                  *)
(***************************************************************************)
MessageType == [
    block : BlockType,
    vote: Nodes,
    received : SUBSET(Nodes)
]
(***************************************************************************)

(* --algorithm streamlet
variables
    messages = { };
    currentEpoch = 1;
    localEpochs = [r \in Nodes |-> currentEpoch];
    nextBlockId = 1;
    newBlock = GenesisBlock; \* a temp variable storing output of CreateBlock

macro CreateBlock(epoch, parent) begin
    newBlock := 
        [
            id |-> nextBlockId,
            epoch |-> epoch,
            parent |-> parent.id,
            length |-> parent.length + 1,
            creator |-> self
        ];
    nextBlockId := nextBlockId + 1;
end macro

macro SendMessage(m) begin
    messages := messages \union { m };
end macro

macro ReceiveMessage(m) begin
    messages := (messages \ {m}) \union 
        {[m EXCEPT !.received = m.received \union {self}]};
end macro

macro ReceiveAndSend(receivedMsg, msgToSend) begin
    messages := (messages \ {receivedMsg}) \union 
        {[receivedMsg EXCEPT !.received = receivedMsg.received \union {self}]}
        \union { msgToSend };
end macro

macro UpdateLocalBlocks(localBlocks, block, vote) begin
    if \E lb \in localBlocks: lb.payload.id = block.id then
        with lb = CHOOSE lb \in localBlocks: lb.payload.id = block.id do 
            localBlocks := (localBlocks \ {lb}) \union {[lb EXCEPT !.sigs = lb.sigs \union vote]};
        end with
    else 
        localBlocks := localBlocks \union {[payload |-> block, sigs |-> {block.creator} \union vote]}
    end if;
end macro

fair process honest \in CorrectNodes
variables
    localBlocks = {[payload |-> GenesisBlock, sigs |-> Nodes]}; \* blocks that I have seen
begin
    Propose:
        with
            localEpoch = localEpochs[self],
            parent \in LongestNotarizedBlocks(localBlocks),
        do 
            if localEpoch = currentEpoch /\ Leaders[localEpoch] = self then
                \* Propose a new block
                CreateBlock(localEpoch, parent.payload);
                SendMessage(SignBlock(newBlock, self));
                UpdateLocalBlocks(localBlocks, newBlock, {self});
            end if;
        end with;
    ReceiveOrSyncEpoch:
        while localEpochs[self] = currentEpoch do
            with 
                m \in {m \in messages: self \notin m.received}, 
                b = m.block 
            do
                if b.id \in { l.payload.id : l \in localBlocks } then
                    \* Already seen this block, just update the other new votes on it
                    ReceiveMessage(m); 
                    UpdateLocalBlocks(localBlocks, b, {m.vote})
                elsif  
                    /\ b.epoch = currentEpoch
                    /\ Leaders[currentEpoch] = b.creator
                    /\ b.epoch \notin { l.payload.epoch: l \in localBlocks }
                    /\ b.parent \in { l.payload.id : l \in LongestNotarizedBlocks(localBlocks) } then
                    with 
                        parent = CHOOSE l \in LongestNotarizedBlocks(localBlocks): b.parent = l.payload.id,
                        signedBlock = SignBlock(b, self)
                    do
                        if (b.length = parent.payload.length + 1) /\ (b.epoch > parent.payload.epoch) then 
                            \* vote for correct new block and add to localBlocks
                            ReceiveAndSend(m, signedBlock);
                            UpdateLocalBlocks(localBlocks, b, {self});
                        end if;                        
                    end with;
                else
                    \* case 1: haven't seen, but the block is for past or future epoch
                    \* case 2: haven't seen, block for the current epoch, but from the wrong leader
                    \* case 3: haven't seen, block for the current epoch, from the right leader, but already voted for an eariler block by him
                    \* case 4: haven't seen, current epoch, right leader, haven't voted, but conflicting parent 
                    \* case 5: haven't seen, correct leader, correct epoch, correct parent, but incorrect height or epoch field
                    ReceiveMessage(m); 
                    UpdateLocalBlocks(localBlocks, b, {});
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
            with currentLeader = Leaders[currentEpoch] do 
                await 
                    /\ \A r \in Nodes: localEpochs[r] = currentEpoch
                    /\ currentLeader \in CorrectNodes => \E m \in messages:
                        /\ m.block.creator = currentLeader
                        /\ m.block.epoch = currentEpoch
            end with;

            if currentEpoch >= GlobalStabTime then
                await (\A m \in messages : (m.block.epoch <= currentEpoch) => (CorrectNodes \subseteq m.received));
            end if;
            currentEpoch := currentEpoch + 1;
        end while;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "18147317" /\ chksum(tla) = "3222c38b")
VARIABLES messages, currentEpoch, localEpochs, nextBlockId, newBlock, pc, 
          localBlocks

vars == << messages, currentEpoch, localEpochs, nextBlockId, newBlock, pc, 
           localBlocks >>

ProcSet == (CorrectNodes) \cup {"timer"}

Init == (* Global variables *)
        /\ messages = { }
        /\ currentEpoch = 1
        /\ localEpochs = [r \in Nodes |-> currentEpoch]
        /\ nextBlockId = 1
        /\ newBlock = GenesisBlock
        (* Process honest *)
        /\ localBlocks = [self \in CorrectNodes |-> {[payload |-> GenesisBlock, sigs |-> Nodes]}]
        /\ pc = [self \in ProcSet |-> CASE self \in CorrectNodes -> "Propose"
                                        [] self = "timer" -> "NextRound"]

Propose(self) == /\ pc[self] = "Propose"
                 /\ LET localEpoch == localEpochs[self] IN
                      \E parent \in LongestNotarizedBlocks(localBlocks[self]):
                        IF localEpoch = currentEpoch /\ Leaders[localEpoch] = self
                           THEN /\ newBlock' = [
                                                   id |-> nextBlockId,
                                                   epoch |-> localEpoch,
                                                   parent |-> (parent.payload).id,
                                                   length |-> (parent.payload).length + 1,
                                                   creator |-> self
                                               ]
                                /\ nextBlockId' = nextBlockId + 1
                                /\ messages' = (messages \union { (SignBlock(newBlock', self)) })
                                /\ IF \E lb \in localBlocks[self]: lb.payload.id = newBlock'.id
                                      THEN /\ LET lb == CHOOSE lb \in localBlocks[self]: lb.payload.id = newBlock'.id IN
                                                localBlocks' = [localBlocks EXCEPT ![self] = (localBlocks[self] \ {lb}) \union {[lb EXCEPT !.sigs = lb.sigs \union ({self})]}]
                                      ELSE /\ localBlocks' = [localBlocks EXCEPT ![self] = localBlocks[self] \union {[payload |-> newBlock', sigs |-> {newBlock'.creator} \union ({self})]}]
                           ELSE /\ TRUE
                                /\ UNCHANGED << messages, nextBlockId, 
                                                newBlock, localBlocks >>
                 /\ pc' = [pc EXCEPT ![self] = "ReceiveOrSyncEpoch"]
                 /\ UNCHANGED << currentEpoch, localEpochs >>

ReceiveOrSyncEpoch(self) == /\ pc[self] = "ReceiveOrSyncEpoch"
                            /\ IF localEpochs[self] = currentEpoch
                                  THEN /\ \E m \in {m \in messages: self \notin m.received}:
                                            LET b == m.block IN
                                              IF b.id \in { l.payload.id : l \in localBlocks[self] }
                                                 THEN /\ messages' = (        (messages \ {m}) \union
                                                                      {[m EXCEPT !.received = m.received \union {self}]})
                                                      /\ IF \E lb \in localBlocks[self]: lb.payload.id = b.id
                                                            THEN /\ LET lb == CHOOSE lb \in localBlocks[self]: lb.payload.id = b.id IN
                                                                      localBlocks' = [localBlocks EXCEPT ![self] = (localBlocks[self] \ {lb}) \union {[lb EXCEPT !.sigs = lb.sigs \union ({m.vote})]}]
                                                            ELSE /\ localBlocks' = [localBlocks EXCEPT ![self] = localBlocks[self] \union {[payload |-> b, sigs |-> {b.creator} \union ({m.vote})]}]
                                                 ELSE /\ IF /\ b.epoch = currentEpoch
                                                            /\ Leaders[currentEpoch] = b.creator
                                                            /\ b.epoch \notin { l.payload.epoch: l \in localBlocks[self] }
                                                            /\ b.parent \in { l.payload.id : l \in LongestNotarizedBlocks(localBlocks[self]) }
                                                            THEN /\ LET parent == CHOOSE l \in LongestNotarizedBlocks(localBlocks[self]): b.parent = l.payload.id IN
                                                                      LET signedBlock == SignBlock(b, self) IN
                                                                        IF (b.length = parent.payload.length + 1) /\ (b.epoch > parent.payload.epoch)
                                                                           THEN /\ messages' = (        (messages \ {m}) \union
                                                                                                {[m EXCEPT !.received = m.received \union {self}]}
                                                                                                \union { signedBlock })
                                                                                /\ IF \E lb \in localBlocks[self]: lb.payload.id = b.id
                                                                                      THEN /\ LET lb == CHOOSE lb \in localBlocks[self]: lb.payload.id = b.id IN
                                                                                                localBlocks' = [localBlocks EXCEPT ![self] = (localBlocks[self] \ {lb}) \union {[lb EXCEPT !.sigs = lb.sigs \union ({self})]}]
                                                                                      ELSE /\ localBlocks' = [localBlocks EXCEPT ![self] = localBlocks[self] \union {[payload |-> b, sigs |-> {b.creator} \union ({self})]}]
                                                                           ELSE /\ TRUE
                                                                                /\ UNCHANGED << messages, 
                                                                                                localBlocks >>
                                                            ELSE /\ messages' = (        (messages \ {m}) \union
                                                                                 {[m EXCEPT !.received = m.received \union {self}]})
                                                                 /\ IF \E lb \in localBlocks[self]: lb.payload.id = b.id
                                                                       THEN /\ LET lb == CHOOSE lb \in localBlocks[self]: lb.payload.id = b.id IN
                                                                                 localBlocks' = [localBlocks EXCEPT ![self] = (localBlocks[self] \ {lb}) \union {[lb EXCEPT !.sigs = lb.sigs \union ({})]}]
                                                                       ELSE /\ localBlocks' = [localBlocks EXCEPT ![self] = localBlocks[self] \union {[payload |-> b, sigs |-> {b.creator} \union ({})]}]
                                       /\ pc' = [pc EXCEPT ![self] = "ReceiveOrSyncEpoch"]
                                       /\ UNCHANGED localEpochs
                                  ELSE /\ localEpochs' = [localEpochs EXCEPT ![self] = localEpochs[self] + 1]
                                       /\ IF localEpochs'[self] <= NumEpochs
                                             THEN /\ pc' = [pc EXCEPT ![self] = "Propose"]
                                             ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                       /\ UNCHANGED << messages, localBlocks >>
                            /\ UNCHANGED << currentEpoch, nextBlockId, 
                                            newBlock >>

honest(self) == Propose(self) \/ ReceiveOrSyncEpoch(self)

NextRound == /\ pc["timer"] = "NextRound"
             /\ IF currentEpoch <= NumEpochs
                   THEN /\ LET currentLeader == Leaders[currentEpoch] IN
                             /\ \A r \in Nodes: localEpochs[r] = currentEpoch
                             /\ currentLeader \in CorrectNodes => \E m \in messages:
                                 /\ m.block.creator = currentLeader
                                 /\ m.block.epoch = currentEpoch
                        /\ IF currentEpoch >= GlobalStabTime
                              THEN /\ (\A m \in messages : (m.block.epoch <= currentEpoch) => (CorrectNodes \subseteq m.received))
                              ELSE /\ TRUE
                        /\ currentEpoch' = currentEpoch + 1
                        /\ pc' = [pc EXCEPT !["timer"] = "NextRound"]
                   ELSE /\ pc' = [pc EXCEPT !["timer"] = "Done"]
                        /\ UNCHANGED currentEpoch
             /\ UNCHANGED << messages, localEpochs, nextBlockId, newBlock, 
                             localBlocks >>

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

TypeInvariant == 
    /\ \A m \in messages: m \in MessageType
    /\ \A n \in Nodes: \A lb \in localBlocks[n]: lb \in LocalBlockType

\* TODO: add UniqueBlockId check

MonoIncEpoch == [][currentEpoch' = currentEpoch + 1]_currentEpoch
LocalEpochCorrectness == [](\A r \in Nodes: localEpochs[r] = currentEpoch \/ localEpochs[r] = currentEpoch - 1)
HonestLeadersShouldPropose == [](
    \A r \in CorrectNodes: 
        LET e == localEpochs[r] 
        IN 
            (currentEpoch # e /\ Leaders[e] = r) => \E m \in messages:
                /\ r \in m.received
                /\ m.block.epoch = e
)
NoDoubleVotePerEpoch ==[](
    \A r \in CorrectNodes:
        \A e \in 0..currentEpoch:
            LET voted == {lb \in localBlocks[r]: lb.payload.epoch = e /\ r \in lb.sigs }
            IN Cardinality(voted) <= 1
)

PartialSynchrony == [](
    \/ currentEpoch <= GlobalStabTime
    \/ \A m \in messages: (m.block.epoch = currentEpoch \/ CorrectNodes \subseteq m.received)
)

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
