---------------------------- MODULE Block ----------------------------
EXTENDS Naturals, FiniteSets, Integers, TLC
CONSTANT Nodes, NotarizedThreshold
ASSUME Nodes # {} /\ NotarizedThreshold > 0

(* Define data structures and helper operators on them used in Streamlet *)

\* Represents a block in Streamlet blockchain
BlockType == [
    \* Unique identifier for each block
    id: Nat,
    \* Epoch in which this block is being proposed and voted on
    epoch: Nat,
    \* Parent are referenced by their id
    parent: Nat
]

GenesisBlock == [id |-> 0, epoch |-> 0, parent |-> 0]

MessageType == [
    block: BlockType,
    vote: Nodes
]

\* check if `block` is finalized given all received `msgs`
IsNotarized(block, msgs) == 
    LET 
        vote_msgs == { m \in msgs: m.block = block }
        votes == { m.vote: m \in vote_msgs }
    IN Cardinality(votes) >= NotarizedThreshold

\* return a list of notarized blocks given all received `msgs`
NotarizedBlocks(msgs) ==
    LET blocks == {m.block: m \in msgs}
    IN { b \in blocks: IsNotarized(b, msgs) }

\* return TRUE if b2 directly extends b1 (b1<-b2) FALSE otherwise
CheckDirectlyExtends(b2, b1) == b2.parent = b1.id

RECURSIVE CheckExtends(_, _, _)
\* returns TRUE if b2 extends b1: b1<-...<-b2, from all received `blocks`
CheckExtends(b2, b1, blocks) ==
    \/ CheckDirectlyExtends(b2, b1)
    \/ \E b3 \in blocks:
        /\ (b3.epoch > b1.epoch /\ b3.epoch < b2.epoch) \* avoid infinite loop
        /\ CheckDirectlyExtends(b3, b1)
        /\ CheckExtends(b2, b3, blocks)

RECURSIVE CheckNotarizedChainTip(_,_)
\* check if Genesis to `tip` block forms a blockchain with each block notarized
\* precondition: CheckExtends(tip, GenesisBlock, blocks) = TRUE
CheckNotarizedChainTip(tip, msgs) ==
    IF tip = GenesisBlock THEN 
        TRUE
    ELSE 
        LET 
            blocks == {m.block: m \in msgs}
            parent == CHOOSE p \in blocks: p.id = tip.parent
        IN 
            /\ IsNotarized(tip, msgs)
            /\ CheckNotarizedChainTip(parent, msgs)

\* returns all blocks that in a notarized blockchain
NotarizedChainBlocks(msgs) ==
    {b \in NotarizedBlocks(msgs): CheckNotarizedChainTip(b, msgs)}

RECURSIVE Length(_, _)
\* return the block length from genesis block, 
\* precondition: CheckExtends(b, GenesisBlock) = TRUE
Length(b, blocks) ==
    IF b = GenesisBlock THEN 
        0
    ELSE 
        LET parent == CHOOSE p \in blocks: p.id = b.parent
        IN Length(parent, blocks) + 1

\* return a list of notarized blocks with the largest Length given all received `msgs`
LongestNotarizedChainTips(msgs) ==
    LET 
        blocks == {m.block: m \in msgs}
        notarized == NotarizedChainBlocks(msgs)
    IN { b \in notarized: \A c \in notarized: Length(b, blocks) >= Length(c, blocks) }


RECURSIVE IsFinalized(_,_)
\* only three adjacent blocks in a notarlized blockchain with consequtive epoch would
\* finalize the second (of the three blocks) and all of its prefix chain.
IsFinalized(block, msgs) == LET notarized == NotarizedChainBlocks(msgs) IN
    \/ block = GenesisBlock
    \/ 
        /\ \E child \in notarized: CheckDirectlyExtends(child, block) /\ child.epoch = block.epoch + 1
        /\ \E parent \in notarized: CheckDirectlyExtends(block, parent) /\ parent.epoch = block.epoch - 1
    \/ \E child \in notarized: CheckDirectlyExtends(child, block) /\ IsFinalized(child, msgs)

FinalizedBlocks(msgs) == LET blocks == {m.block: m \in msgs} IN 
    { b \in blocks: IsFinalized(b, msgs) }

\* precondition: chain1, chain2 both contain blocks that form a proper chain
\* check if two chains are prefix of the other, namely if they are conflict free
\* return TRUE if they don't conflict, FALSE otherwise
CheckConflictFree(chain1, chain2) == 
    LET 
        l1 == Cardinality(chain1)
        l2 == Cardinality(chain2) 
    IN
        \/ 
            /\ l1 <= l2
            /\ chain1 \subseteq chain2
        \/
            /\ l1 > l2
            /\ chain2 \subseteq chain1

(* More utility functions/operators  *)

\* return f' where f'[key] = newValue, the rest unchanged
UpdateFuncEntry(f, key, newValue) ==
    [k \in (DOMAIN f \ {key}) |-> f[k]] @@ key :> newValue

RECURSIVE BatchUpdate(_,_,_)
\* output an updated recv
BatchUpdate(recv, msgs, node) ==
    IF msgs = {} THEN
        recv
    ELSE 
        LET m == CHOOSE m \in msgs: TRUE
        IN 
            IF m \in DOMAIN recv THEN 
                LET updated == UpdateFuncEntry(recv, m, recv[m] \union {node})     
                IN BatchUpdate(updated, msgs \ {m}, node)
            ELSE 
                LET updated == (recv @@ m :> {node})
                IN BatchUpdate(updated, msgs \ {m}, node)            
=============================================================================