---- MODULE TestBlocks ----
EXTENDS Blocks, FiniteSets, TLC

CONSTANT r1, r2, r3, r4

ConstReplicas == {r1, r2, r3, r4}

SampleBlocks == <<
    CreateBlock(1, GenesisBlock),
    CreateBlock(2, GenesisBlock),
    [ id |-> 3, parent |-> 1],
    [ id |-> 4, parent |-> 3],
    [ id |-> 5, parent |-> 2]
>>

\* TODO: Need to define this somewhere common
Range(f) == { f[x] : x \in DOMAIN f }

BlockSet == Range(SampleBlocks) \union {GenesisBlock}

ASSUME Assert(NoLoops(BlockSet), "No loops in sample blocks")

LoopBlocksSet == {
    [ id |-> 1, parent |-> 3],
    [ id |-> 2, parent |-> 1],
    [ id |-> 3, parent |-> 2]
}

ASSUME Assert(~NoLoops(LoopBlocksSet), "Loops in sample blocks")

ASSUME Assert(DirectlyExtends(SampleBlocks[1], GenesisBlock),
    "Block 1 Directly Extends Genesis")

ASSUME Assert(~DirectlyExtends(GenesisBlock, SampleBlocks[1]),
    "Genesis Does NOT Directly Extend Block 1")

ASSUME Assert(DirectlyExtends(SampleBlocks[2], GenesisBlock),
    "Block 2 Directly Extends Genesis")

ASSUME Assert(~DirectlyExtends(GenesisBlock, SampleBlocks[2]),
    "Genesis Does NOT Directly Extend Block 2")

ASSUME Assert(DirectlyExtends(SampleBlocks[3], SampleBlocks[1]),
    "Block 3 Directly Extends Block 1")

ASSUME Assert(~DirectlyExtends(SampleBlocks[3], SampleBlocks[2]),
    "Block 3 Does NOT Directly Extend Block 2")

ASSUME Assert(BlockExtends(SampleBlocks[1], GenesisBlock, BlockSet),
    "Block 1 Extends Genesis")

ASSUME Assert(BlockExtends(SampleBlocks[3], GenesisBlock, BlockSet),
    "Block 3 Extends Genesis")

ASSUME Assert(BlockExtends(SampleBlocks[4], SampleBlocks[1], BlockSet),
    "Block 4 Extends Block 1")

ASSUME Assert(BlockExtends(SampleBlocks[5], GenesisBlock, BlockSet),
    "Block 5 Extends Genesis")

ASSUME Assert(~BlockExtends(SampleBlocks[5], SampleBlocks[1], BlockSet),
    "Block 5 Does NOT Extend Block 1")

ASSUME Assert(~BlockExtends(SampleBlocks[5], SampleBlocks[3], BlockSet),
    "Block 5 Does NOT Extend Block 3")

ASSUME Assert(~BlockExtends(SampleBlocks[3], SampleBlocks[5], BlockSet),
    "Block 3 Does NOT Extend Block 5")

ASSUME Assert(BlocksDoNotConflict(SampleBlocks[1], SampleBlocks[1], BlockSet),
    "Block cannot conflict with itself")

ASSUME Assert(BlocksDoNotConflict(SampleBlocks[1], SampleBlocks[3], BlockSet),
    "Blocks 1 and 3 do not conflict")
ASSUME Assert(BlocksDoNotConflict(SampleBlocks[3], SampleBlocks[1], BlockSet),
    "Blocks 1 and 3 do not conflict")
ASSUME Assert(BlocksDoNotConflict(SampleBlocks[1], SampleBlocks[4], BlockSet),
    "Blocks 1 and 4 do not conflict")
ASSUME Assert(BlocksDoNotConflict(SampleBlocks[4], SampleBlocks[1], BlockSet),
    "Blocks 1 and 4 do not conflict")

ASSUME Assert(~BlocksDoNotConflict(SampleBlocks[1], SampleBlocks[2], BlockSet),
    "Blocks 1 and 2 conflict")
ASSUME Assert(~BlocksDoNotConflict(SampleBlocks[2], SampleBlocks[1], BlockSet),
    "Blocks 1 and 2 conflict")
ASSUME Assert(~BlocksDoNotConflict(SampleBlocks[3], SampleBlocks[5], BlockSet),
    "Blocks 3 and 5 conflict")
ASSUME Assert(~BlocksDoNotConflict(SampleBlocks[5], SampleBlocks[3], BlockSet),
    "Blocks 3 and 5 conflict")

ASSUME Assert(NoConflictsInBlockSets(
    {SampleBlocks[1], SampleBlocks[4]},
    {SampleBlocks[3], SampleBlocks[1]},
        BlockSet), "No conflicts in samples")

ASSUME Assert(~NoConflictsInBlockSets(
    {SampleBlocks[2]}, {SampleBlocks[3], SampleBlocks[4]}, BlockSet),
        "Two sets conflict")

ASSUME Assert(GenesisQC(Prepare) \in QCType, "GenesisQC is QC Type")

msg == CreateMessage(
    PreCommit, 99, CreateBlock(1, GenesisBlock), GenesisQC(Commit), r3)
ASSUME Assert(msg \in MessageType, "CreateMessage is MessageType")

pBlock == CreateBlock(1, GenesisBlock)

NotEnoughVotes == {
    CreateMessage(Prepare, 42, pBlock, GenesisQC(Prepare), r3),
    CreateMessage(Prepare, 42, pBlock, Null, r3),
    CreateMessage(Prepare, 42, pBlock, Null, r4)
}

EnoughVotes == NotEnoughVotes \union {CreateMessage(Prepare, 42, pBlock, Null, r2)}

ASSUME Assert(~CheckVotesForQC(NotEnoughVotes), "Not Enough Votes")
ASSUME Assert(CheckVotesForQC(EnoughVotes), "Enough Votes")
ASSUME Assert(~CheckVotesForQC(EnoughVotes \union {msg}), "Not All Votes Match")

myQC == GenerateQC(EnoughVotes)

ASSUME Assert(myQC \in QCType, "Generated QC is QCType")

ASSUME Assert(
    /\ myQC.type = Prepare
    /\ myQC.viewNum = 42
    /\ myQC.block = pBlock, "QC is correct")

MakeQC(type, vn, block) == [ type |-> type, viewNum |-> vn, block |-> block ]

NewViewMsgs == {
    CreateMessage(NewView, 42, Null, MakeQC(Prepare, 3, pBlock), r3),
    CreateMessage(NewView, 42, Null, MakeQC(Prepare, 7, pBlock), r1),
    CreateMessage(NewView, 42, Null, MakeQC(Prepare, 2, pBlock), r2)
}

ASSUME Assert(MaxJustifyVN(NewViewMsgs).vote = r1, "Max works")

=============================================================================
\* Modification History
\* Last modified Fri Oct 07 18:34:03 SGT 2022 by kshehata
\* Created Tue Sep 06 19:56:44 SGT 2022 by kshehata
