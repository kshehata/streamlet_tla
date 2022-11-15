---------------------------- MODULE TestBlock ----------------------------
EXTENDS Naturals, TLC
CONSTANTS n1, n2, n3
Nodes == {n1, n2, n3}

INSTANCE Block WITH Nodes <- Nodes, NotarizedThreshold <- 2

b1 == [id |-> 1, epoch |-> 1, parent |-> 0]
b2 == [id |-> 2, epoch |-> 2, parent |-> 1]
b2p == [id |-> 3, epoch |-> 2, parent |-> 11]
b4 == [id |-> 4, epoch |-> 4, parent |-> 2]
b5 == [id |-> 5, epoch |-> 5, parent |-> 4]
b6 == [id |-> 6, epoch |-> 6, parent |-> 0]
b7 == [id |-> 7, epoch |-> 7, parent |-> 6]
b8 == [id |-> 8, epoch |-> 8, parent |-> 7]
b9 == [id |-> 9, epoch |-> 9, parent |-> 8]
b10 == [id |-> 10, epoch |-> 10, parent |-> 9]

ASSUME GenesisBlock \in BlockType

\*                   b2p
\* \bot (✔) <- b1 (✔) <- b2 <- b4 (✔) <- b5 (✔) 
\*         |<- b6 (✔) <- b7 (✔) <- b8 (✔) <- b9 <- b10 (✔)
Msgs == {
    [block |-> GenesisBlock, vote |-> n1],
    [block |-> GenesisBlock, vote |-> n2],
    [block |-> GenesisBlock, vote |-> n3],
    [block |-> b1, vote |-> n3],
    [block |-> b1, vote |-> n2],
    [block |-> b2, vote |-> n1],
    [block |-> b2p, vote |-> n2],
    [block |-> b4, vote |-> n2],
    [block |-> b4, vote |-> n1],
    [block |-> b5, vote |-> n1],
    [block |-> b5, vote |-> n3],
    [block |-> b6, vote |-> n1],
    [block |-> b6, vote |-> n3],
    [block |-> b7, vote |-> n1],
    [block |-> b7, vote |-> n3],
    [block |-> b8, vote |-> n1],
    [block |-> b8, vote |-> n2],
    [block |-> b8, vote |-> n3],
    [block |-> b9, vote |-> n3],
    [block |-> b10, vote |-> n3],
    [block |-> b10, vote |-> n1]
}
Blocks == {m.block: m \in Msgs}
ASSUME \A b \in Blocks: b \in BlockType
ExpectedNotarizedBlocks == {GenesisBlock, b1, b4, b5, b6, b7, b8, b10}

ASSUME \A b \in ExpectedNotarizedBlocks: IsNotarized(b, Msgs) = TRUE
ASSUME \A b \in Blocks \ ExpectedNotarizedBlocks: IsNotarized(b, Msgs) = FALSE
ASSUME NotarizedBlocks(Msgs) = ExpectedNotarizedBlocks

ASSUME CheckDirectlyExtends(b1, GenesisBlock) = TRUE
ASSUME CheckDirectlyExtends(b2, b1) = TRUE
ASSUME CheckDirectlyExtends(b5, GenesisBlock) = FALSE
ASSUME CheckDirectlyExtends(b4, b2) = TRUE
ASSUME CheckDirectlyExtends(b7, b6) = TRUE
ASSUME CheckDirectlyExtends(b6, b1) = FALSE
ASSUME CheckExtends(GenesisBlock, b1, Blocks) = FALSE
ASSUME CheckExtends(b6, GenesisBlock, Blocks) = TRUE
ASSUME CheckExtends(b1, GenesisBlock, Blocks) = TRUE
ASSUME CheckExtends(b2, GenesisBlock, Blocks) = TRUE
ASSUME CheckExtends(GenesisBlock, b4, Blocks) = FALSE
ASSUME CheckExtends(b4, b1, Blocks) = TRUE
ASSUME CheckExtends(b10, b6, Blocks) = TRUE
ASSUME CheckExtends(b10, GenesisBlock, Blocks) = TRUE
ASSUME CheckExtends(b6, b1, Blocks) = FALSE
ASSUME CheckExtends(b10, b1, Blocks) = FALSE

ASSUME Length(GenesisBlock, Blocks) = 0
ASSUME Length(b1, Blocks) = 1
ASSUME Length(b2, Blocks) = 2
ASSUME Length(b4, Blocks) = 3
ASSUME Length(b5, Blocks) = 4
ASSUME Length(b6, Blocks) = 1
ASSUME Length(b7, Blocks) = 2
ASSUME Length(b8, Blocks) = 3
ASSUME Length(b9, Blocks) = 4
ASSUME Length(b10, Blocks) = 5

ExpectedNotarizedChainTips == {GenesisBlock, b1, b6, b7, b8}
ASSUME \A b \in ExpectedNotarizedChainTips: CheckNotarizedChainTip(b, Msgs) = TRUE
ASSUME \A b \in (Blocks \ ExpectedNotarizedChainTips): CheckNotarizedChainTip(b, Msgs) = FALSE

ASSUME LongestNotarizedChainTips(Msgs) = {b8}

ExpectedFinalizedBlocks == {GenesisBlock, b6, b7}
ASSUME \A b \in ExpectedFinalizedBlocks: IsFinalized(b, Msgs) = TRUE
ASSUME \A b \in (Blocks \ ExpectedFinalizedBlocks): IsFinalized(b, Msgs) = FALSE 
=============================================================================