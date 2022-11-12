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

BlockSet == Range(SampleBlocks)

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


ASSUME Assert(GenesisQC(Prepare) \in QCType, "GenesisQC is QC Type")

bcast == CreateBroadcastMessage(
    PreCommit, 99, CreateBlock(1, GenesisBlock), GenesisQC(Commit), r2)

\* ASSUME PrintT(bcast)

\* ASSUME bcast.type \in {NewView, Prepare, PreCommit, Commit, Decide}
\* ASSUME bcast.viewNum \in Nat
\* ASSUME bcast.block \in BlockType
\* ASSUME bcast.justify \in QCType
\* ASSUME bcast.vote \in Replicas
\* ASSUME bcast.dest \in SUBSET(Replicas)
\* ASSUME bcast.received \in SUBSET(Replicas)

ASSUME Assert(bcast \in MessageType, "CreateBroadcastMessage is MessageType")
ASSUME Assert(~MessageReceived(bcast), "Broadcast Message Not Yet Received")

bcastAlmostReceived == [ bcast EXCEPT !.received = {r1, r2, r3} ]
ASSUME Assert(~MessageReceived(bcastAlmostReceived), "Broadcast Message Almost Received")

bcastReceived == [ bcast EXCEPT !.received = Replicas ]
ASSUME Assert(MessageReceived(bcastReceived), "Broadcast Message Received")

msg == CreateMessageTo(
    PreCommit, 99, CreateBlock(1, GenesisBlock), GenesisQC(Commit), r3, r2)
ASSUME Assert(msg \in MessageType, "CreateMessageTo is MessageType")
ASSUME Assert(~MessageReceived(msg), "Single Message Not Yet Received")

receivedMsg == MarkMessageReceivedBy(msg, r2)
ASSUME Assert(MessageReceived(receivedMsg), "Single Message Received")

pBlock == CreateBlock(1, GenesisBlock)

SampleMessages == {
    MarkMessageReceivedBy(bcast, r3),
    CreateBroadcastMessage(Prepare, 42, pBlock, GenesisQC(Prepare), r3),
    MarkMessageReceivedBy(CreateMessageTo(Prepare, 42, pBlock, Null, r4, r3), r3),
    MarkMessageReceivedBy(CreateMessageTo(Prepare, 42, pBlock, Null, r1, r3), r3),
    MarkMessageReceivedBy(CreateMessageTo(Commit, 42, pBlock, Null, r2, r3), r3),
    MarkMessageReceivedBy(CreateMessageTo(Prepare, 41, pBlock, Null, r2, r3), r3),
    CreateMessageTo(Prepare, 42, pBlock, Null, r2, r3)
}

myVotes == ReceivedVotes(SampleMessages, Prepare, 42, r3)

ASSUME Assert(\A v \in myVotes :
    /\ v.type = Prepare
    /\ v.viewNum = 42
    /\ v.block = pBlock
    /\ r3 \in v.received, "Votes are valid")

ASSUME Assert(Cardinality(myVotes) = 3, "Vote cardinality correct")

myQC == GenerateQC(myVotes)

ASSUME Assert(myQC \in QCType, "Generated QC is QCType")

ASSUME Assert(
    /\ myQC.type = Prepare
    /\ myQC.viewNum = 42
    /\ myQC.block = pBlock, "QC is correct")

ASSUME Assert(CheckVotesForQC(myVotes), "Enough votes")

=============================================================================
\* Modification History
\* Last modified Fri Oct 07 18:34:03 SGT 2022 by kshehata
\* Created Tue Sep 06 19:56:44 SGT 2022 by kshehata
