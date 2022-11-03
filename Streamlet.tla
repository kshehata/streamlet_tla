----------------------------- MODULE Streamlet -----------------------------

EXTENDS Integers, Sequences, FiniteSets

Maximum(S) == IF S = {} THEN -1
                        ELSE CHOOSE n \in S : \A m \in S : n \geq m
                        
CONSTANT CorrectNodes,  \* Nodes assumed to be correct ("honest")
         FaultyNodes,   \* Set of faulty ("corrupt") nodes
         Leaders        \* Sequence of leaders in each epoch

Nodes == CorrectNodes \cup FaultyNodes
ASSUME Leaders \in Seq(Nodes) /\ FaultyNodes \subseteq Nodes

NotarizedThreshold == Cardinality(Nodes) - Cardinality(FaultyNodes)

(***************************************************************************)
(* Defines blocks and operations on blocks                                 *)
(***************************************************************************)
Blocks == [ \* Blocks are represented as the epoch number they belong.
            \* Parents are referenced by epoch number as well.
            \* Length is the length of the chain that leads to this block.
            epoch : Nat,
            parent : Nat,
            length : Nat,
            sigs : SUBSET(Nodes)
          ]

CreateBlock(epoch, parent, length, sigs) ==
    [
        epoch |-> epoch,
        parent |-> parent,
        length |-> length,
        sigs |-> sigs
    ]

GenesisBlock == CreateBlock(0, 0, 0, Nodes)

ExtendBlock(epoch, block, node) ==
    CreateBlock(epoch, block.epoch, block.length + 1, {node})

SignBlock(block, node) ==
    [block EXCEPT !.sigs = block.sigs \union {node}]

IsNotarized(block) == Cardinality(block.sigs) >= NotarizedThreshold

NotarizedBlocks(blocks) == { b \in blocks : IsNotarized(b) }

LongestNotarizedBlocks(blocks) ==
    LET notarized == NotarizedBlocks(blocks)
    IN { b \in notarized : \A c \in notarized : b.length >= c.length }
(***************************************************************************)

\* Updates a set of blocks with signatures from a given block
UpdateLocalState(localState, m) ==
  LET b == CHOOSE b \in localState : b.epoch = m.epoch
  IN (localState \ {b}) \union { [ b EXCEPT !.sigs = b.sigs \union m.sigs ] }


(* --algorithm streamlet
variables
    messages = { };
    currentEpoch = 1;

fair process replica \in Nodes
variables
  localBlocks = {GenesisBlock};
begin
  Start:
    if Leaders[currentEpoch] = self then
      \* Propose a new block
      with
        b \in LongestNotarizedBlocks(localBlocks),
        m = ExtendBlock(currentEpoch, b, self)
      do
        messages := messages \union { m };
        localBlocks := localBlocks \union { m };
      end with
    end if;
  ReplicaReceive:
    with m \in messages do
      if m.epoch \in { b.epoch : b \in localBlocks } then
        \* Already seen this block, just update it
        \* TODO: check length and parent correct ?
        \* TODO: need to check that current epoch can be signed ?
        localBlocks := UpdateLocalState(localBlocks, m);
      else
        if /\ m.epoch = currentEpoch
           /\ Leaders[currentEpoch] \in m.sigs
           /\ m.parent \in { b.epoch : b \in LongestNotarizedBlocks(localBlocks) } then
          \* TODO: check that length is correct
          \* Correctly extends local longest chain
          messages := messages \union { SignBlock(m, self) };
          localBlocks := localBlocks \union { SignBlock(m, self) };
        else
          \* can't sign block, so just add it to local state
          localBlocks := localBlocks \union { m }
        end if;
      end if;
    end with;
    \* TODO: loop back to start when epoch changes
    goto ReplicaReceive
end process;



\* Uncomment to make network async
\*process network = 1
\*begin
\*  NextEpoch:
\*    \* Make sure at least leader proposes current epoch
\*    await \E m \in messages : m.epoch = currentEpoch;
\*    currentEpoch := currentEpoch + 1;
\*    goto NextEpoch
\*end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "390b7b0a" /\ chksum(tla) = "8561d6b5")
VARIABLES messages, currentEpoch, pc, localBlocks

vars == << messages, currentEpoch, pc, localBlocks >>

ProcSet == (Nodes)

Init == (* Global variables *)
        /\ messages = { }
        /\ currentEpoch = 1
        (* Process replica *)
        /\ localBlocks = [self \in Nodes |-> {GenesisBlock}]
        /\ pc = [self \in ProcSet |-> "Start"]

Start(self) == /\ pc[self] = "Start"
               /\ IF Leaders[currentEpoch] = self
                     THEN /\ \E b \in LongestNotarizedBlocks(localBlocks[self]):
                               LET m == ExtendBlock(currentEpoch, b, self) IN
                                 /\ messages' = (messages \union { m })
                                 /\ localBlocks' = [localBlocks EXCEPT ![self] = localBlocks[self] \union { m }]
                     ELSE /\ TRUE
                          /\ UNCHANGED << messages, localBlocks >>
               /\ pc' = [pc EXCEPT ![self] = "ReplicaReceive"]
               /\ UNCHANGED currentEpoch

ReplicaReceive(self) == /\ pc[self] = "ReplicaReceive"
                        /\ \E m \in messages:
                             IF m.epoch \in { b.epoch : b \in localBlocks[self] }
                                THEN /\ localBlocks' = [localBlocks EXCEPT ![self] = UpdateLocalState(localBlocks[self], m)]
                                     /\ UNCHANGED messages
                                ELSE /\ IF /\ m.epoch = currentEpoch
                                           /\ Leaders[currentEpoch] \in m.sigs
                                           /\ m.parent \in { b.epoch : b \in LongestNotarizedBlocks(localBlocks[self]) }
                                           THEN /\ messages' = (messages \union { SignBlock(m, self) })
                                                /\ localBlocks' = [localBlocks EXCEPT ![self] = localBlocks[self] \union { SignBlock(m, self) }]
                                           ELSE /\ localBlocks' = [localBlocks EXCEPT ![self] = localBlocks[self] \union { m }]
                                                /\ UNCHANGED messages
                        /\ pc' = [pc EXCEPT ![self] = "ReplicaReceive"]
                        /\ UNCHANGED currentEpoch

replica(self) == Start(self) \/ ReplicaReceive(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Nodes: replica(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Nodes : WF_vars(replica(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

\* Not really liveness, just check that all nodes got block 1
\* Only works if network is synchronous
Liveness == <>(
    \A n \in Nodes :
        \E b \in localBlocks[n] :
            /\ b.epoch = 1
            /\ b.parent = 0
            /\ b.length = 1
            /\ b.sigs = Nodes
)
 

=============================================================================
\* Modification History
\* Last modified Fri Oct 07 18:34:03 SGT 2022 by kshehata
\* Created Tue Sep 06 19:56:44 SGT 2022 by kshehata
