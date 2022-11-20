----------------------------- MODULE HotStuff -----------------------------

EXTENDS Blocks, Sequences, FiniteSets, TLC

CONSTANT Leaders, Correct, Faulty

ASSUME Leaders \in Seq(Replicas)

Block1 == CreateBlock(1, GenesisBlock)
Block1QC(type) == [ type |-> type, viewNum |-> 1, block |-> Block1 ]

(* --algorithm hotstuff
variables
    \* DO NOT MODIFY DIRECTLY! Should only be used in ProposeNewBlock
    NextBlockId = 2;

    \* Global cache of all blocks, assumed in paper that all nodes can just get all blocks.
    AllBlocks = {GenesisBlock, Block1};

    \* All QC in system, used for byzantine replicas
    AllQC = {GenesisQC(phase) : phase \in {Prepare, PreCommit, Commit}}
            \union {Block1QC(phase) : phase \in {Prepare, PreCommit, Commit}};

    \* All messages sent by leader to all replicas
    BroadcastMessages = {};

    \* All messages sent by replicas directly to the leader (for the given view)
    RepliesToLeader = {};

define
\* Shortcut for messages from the leader
FilterMessages(type, vn, leader) == { m \in BroadcastMessages :
            /\ type = m.type
            /\ vn = m.viewNum
            /\ m.vote = leader }
end define;

macro SendBroadcast(phase, block, qc) begin
    BroadcastMessages := BroadcastMessages \union
        {CreateMessage(phase, curView, block, qc, self)};
end macro

macro ReplyWithVote(type, block) begin
    RepliesToLeader := RepliesToLeader \union {
        CreateMessage(type, curView, block, Null, self)
    };
end macro;

macro SendNewView(qc) begin
    RepliesToLeader := RepliesToLeader \union {
        CreateMessage(NewView, curView, Null, qc, self)
    }
end macro;

macro ProposeNewBlockImpl(justifyQC, selfVote) begin
    with newBlock = CreateBlock(NextBlockId, justifyQC.block) do
        NextBlockId := NextBlockId + 1;
        AllBlocks := AllBlocks \union {newBlock};
        SendBroadcast(Prepare, newBlock, justifyQC);
        ReplyWithVote(Prepare, newBlock);
        if selfVote then
            \* Clear out old votes, and vote for your own proposal
            receivedVotes := { CreateMessage(Prepare, curView, newBlock, Null, self) };
        end if;
    end with;
end macro;

macro ProposeNewBlock(justifyQC) begin
    ProposeNewBlockImpl(justifyQC, TRUE);
end macro;

macro FProposeNewBlock(justifyQC) begin
    ProposeNewBlockImpl(justifyQC, FALSE);
end macro;

macro WaitForVotes(voteType) begin
    while ~CheckVotesForQC(receivedVotes) do
        either
            with m \in { m \in RepliesToLeader : m.type = voteType /\ m.viewNum = curView } do
                \* Ignore votes that have the wrong block set
                if \A v \in receivedVotes : m.block = v.block then
                receivedVotes := receivedVotes \union {m};
                end if;
            end with;
        or
            \* At any point timeout and go to NextView
            goto NextView;
        end either;
    end while;
end macro;

macro SendQC(voteType, phase, qc) begin
    assert CheckVotesForQC(receivedVotes);
    qc := GenerateQC(receivedVotes);
    AllQC := AllQC \union {qc};
    SendBroadcast(phase, Null, qc);
    if phase = Decide then
        \* No voting in Decide phase
        receivedVotes := {}
    else
        \* Clear out old votes, and vote for your own proposal
        receivedVotes := { CreateMessage(phase, curView, qc.block, Null, self) };
        ReplyWithVote(phase, qc.block);
    end if;
end macro;

macro FaultyLeader(qcType, phase) begin
    \* either
        \* Assume adversary has ALL messages, can use any resulting QC
        with allQC = GenerateAllQCForType(RepliesToLeader, qcType),
            qc1 \in AllQC, qc2 \in AllQC do
            BroadcastMessages := BroadcastMessages \union
                { CreateMessage(phase, curView, Null, qc1, self),
                  CreateMessage(phase, curView, Null, qc1, self) };
        end with;
    \* or
    \*     goto FNextView;
    \* end either;
end macro;

fair process rep \in Correct
variables
    curView = 1;
    leader = Leaders[1];
    prepareQC = Block1QC(Prepare);
    lockedQC = Block1QC(PreCommit);
    \* Only used as a temporary, but makes life easier
    commitQC = Block1QC(Commit);
    \* Blocks commited in view of this replica
    committedBlocks = {Block1};
    \* Only used by the leader to keep votes received in the current phase
    receivedVotes = {};

begin
NextView:
    curView := curView + 1;
    if curView > Len(Leaders) then 
        goto Done;
    end if;

NextView2:
    leader := Leaders[curView];
    if (self = leader) then
        \* Send yourself a vote just to make logic easier
        receivedVotes := {CreateMessage(NewView, curView, Null, prepareQC, self)};
    else
        SendNewView(prepareQC);
        goto ReplicaPrepare;
    end if;

WaitForNewView:
    while Cardinality({v.vote : v \in receivedVotes}) < QCThresh do
        either
            \* TODO: do we need to check that Justify QC is actually prepare ??
            with m \in { m \in RepliesToLeader : m.type = NewView /\ m.viewNum = curView } do
                receivedVotes := receivedVotes \union {m};
            end with;
        or
            \* At any point timeout and go to NextView
            goto NextView;
        end either;
    end while;
    assert Cardinality(receivedVotes) >= QCThresh;
    prepareQC := MaxJustifyVN(receivedVotes).justify;
    ProposeNewBlock(prepareQC);

LeaderPreCommit:
    WaitForVotes(Prepare);
    SendQC(Prepare, PreCommit, prepareQC);

LeaderCommit:
    WaitForVotes(PreCommit);
    SendQC(PreCommit, Commit, lockedQC);

LeaderDecide:
    WaitForVotes(Commit);
    SendQC(Commit, Decide, commitQC);
    committedBlocks := committedBlocks \union {commitQC.block};
    goto NextView;


ReplicaPrepare:
    either
        with m \in FilterMessages(Prepare, curView, leader) do
            \* TODO: What should we do if this fails? Keep going? Timeout?
            if DirectlyExtends(m.block, m.justify.block)
                /\ ( BlockExtends(m.block, lockedQC.block, AllBlocks)
                    \/ m.justify.viewNum > lockedQC.viewNum ) then
                ReplyWithVote(Prepare, m.block);
            end if;
        end with;
    or
        \* At any point timeout and go to NextView
        goto NextView;
    end either;

ReplicaPreCommit:
    either
        with m \in FilterMessages(PreCommit, curView, leader) do
            \* TODO: The check above isn't actually in the paper ??
            \* TODO: What should we do if the check below fails ?
            if m.justify.type = Prepare /\ m.justify.viewNum = curView then
                prepareQC := m.justify;
                ReplyWithVote(PreCommit, m.justify.block);
            end if;
        end with;
    or
        \* At any point timeout and go to NextView
        goto NextView;
    end either;

ReplicaCommit:
    either
        with m \in FilterMessages(Commit, curView, leader) do
            \* TODO: The check above isn't actually in the paper ??
            \* TODO: What should we do if the check below fails ?
            if m.justify.type = PreCommit /\ m.justify.viewNum = curView then
                lockedQC := m.justify;
                ReplyWithVote(Commit, m.justify.block);
            end if;
        end with;
    or
        \* At any point timeout and go to NextView
        goto NextView;
    end either;

ReplicaDecide:
    either
        with m \in FilterMessages(Decide, curView, leader) do
            \* TODO: The check above isn't actually in the paper ??
            \* TODO: What should we do if the check below fails ?
            if m.justify.type = Commit /\ m.justify.viewNum = curView then
                committedBlocks := committedBlocks \union {m.justify.block};
            end if;
        end with;
        goto NextView;
    or
        \* At any point timeout and go to NextView
        goto NextView;
    end either;

end process;

fair process faulty \in Faulty
variables
    curView = 1;
    leader = Leaders[1];

begin
FNextView:
    curView := curView + 1;
    if curView > Len(Leaders) then 
        goto Done;
    end if;

FNextView2:
    leader := Leaders[curView];
    if (self = leader) then
        goto FPrepare;
    else
        with qc \in GenerateAllQCForType(RepliesToLeader, Prepare) do
            SendNewView(qc);
        end with;
        goto FReplicaPrepare;
    end if;

FPrepare:
    \* Faulty nodes don't have to wait for votes, just pick a QC and a block
    \* Assume adversary has ALL messages, can use any resulting QC
    \* TODO: faulty leader can send two different propose messages.
    with qc \in GenerateAllQCForType(RepliesToLeader, Prepare) do
        FProposeNewBlock(qc);
    end with;

FPrepare2:
    with qc \in GenerateAllQCForType(RepliesToLeader, Prepare) do
        FProposeNewBlock(qc);
    end with;

FPreCommit:
    FaultyLeader(Prepare, PreCommit);

FPreCommit2:
    FaultyLeader(Prepare, PreCommit);

FCommit:
    FaultyLeader(PreCommit, Commit);

FCommit2:
    FaultyLeader(PreCommit, Commit);

FDecide:
    FaultyLeader(Commit, Decide);

FLeaderDone:
    goto FNextView;

FReplicaPrepare:
    either
        \* Don't even bother waiting for the leader,
        \* Just pick a random block to vote on
        with b \in AllBlocks do
            ReplyWithVote(Prepare, b);
        end with;
    or
        \* Make your own block
        with p \in AllBlocks, b = CreateBlock(NextBlockId, p) do
            NextBlockId := NextBlockId + 1;
            AllBlocks := AllBlocks \union {b};
            ReplyWithVote(Prepare, b);
        end with;
    or
        \* At any point timeout and go to NextView
        goto FNextView;
    or
        \* Don't bother sending anything just skip ahead
        goto FReplicaPreCommit;
    end either;

FReplicaPreCommit:
    either
        \* Don't even bother waiting for the leader,
        \* Just pick a random block to vote on
        with b \in AllBlocks do
            ReplyWithVote(PreCommit, b);
        end with;
    or
        \* Make your own block
        with p \in AllBlocks, b = CreateBlock(NextBlockId, p) do
            NextBlockId := NextBlockId + 1;
            AllBlocks := AllBlocks \union {b};
            ReplyWithVote(Prepare, b);
        end with;
    or
        \* At any point timeout and go to NextView
        goto FNextView;
    or
        \* Don't bother sending anything just skip ahead
        goto FReplicaCommit;
    end either;

FReplicaCommit:
    either
        \* Don't even bother waiting for the leader,
        \* Just pick a random block to vote on
        with b \in AllBlocks do
            ReplyWithVote(Commit, b);
        end with;
        goto FNextView;
    or
        \* Make your own block
        with p \in AllBlocks, b = CreateBlock(NextBlockId, p) do
            NextBlockId := NextBlockId + 1;
            AllBlocks := AllBlocks \union {b};
            ReplyWithVote(Prepare, b);
        end with;
        goto FNextView;
    or
        \* At any point timeout and go to NextView
        goto FNextView;
    end either;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "f10bdbb8" /\ chksum(tla) = "a3f6ec6e")
\* Process variable curView of process rep at line 123 col 5 changed to curView_
\* Process variable leader of process rep at line 124 col 5 changed to leader_
VARIABLES NextBlockId, AllBlocks, AllQC, BroadcastMessages, RepliesToLeader, 
          pc

(* define statement *)
FilterMessages(type, vn, leader) == { m \in BroadcastMessages :
            /\ type = m.type
            /\ vn = m.viewNum
            /\ m.vote = leader }

VARIABLES curView_, leader_, prepareQC, lockedQC, commitQC, committedBlocks, 
          receivedVotes, curView, leader

vars == << NextBlockId, AllBlocks, AllQC, BroadcastMessages, RepliesToLeader, 
           pc, curView_, leader_, prepareQC, lockedQC, commitQC, 
           committedBlocks, receivedVotes, curView, leader >>

ProcSet == (Correct) \cup (Faulty)

Init == (* Global variables *)
        /\ NextBlockId = 2
        /\ AllBlocks = {GenesisBlock, Block1}
        /\ AllQC = {GenesisQC(phase) : phase \in {Prepare, PreCommit, Commit}}
                   \union {Block1QC(phase) : phase \in {Prepare, PreCommit, Commit}}
        /\ BroadcastMessages = {}
        /\ RepliesToLeader = {}
        (* Process rep *)
        /\ curView_ = [self \in Correct |-> 1]
        /\ leader_ = [self \in Correct |-> Leaders[1]]
        /\ prepareQC = [self \in Correct |-> Block1QC(Prepare)]
        /\ lockedQC = [self \in Correct |-> Block1QC(PreCommit)]
        /\ commitQC = [self \in Correct |-> Block1QC(Commit)]
        /\ committedBlocks = [self \in Correct |-> {Block1}]
        /\ receivedVotes = [self \in Correct |-> {}]
        (* Process faulty *)
        /\ curView = [self \in Faulty |-> 1]
        /\ leader = [self \in Faulty |-> Leaders[1]]
        /\ pc = [self \in ProcSet |-> CASE self \in Correct -> "NextView"
                                        [] self \in Faulty -> "FNextView"]

NextView(self) == /\ pc[self] = "NextView"
                  /\ curView_' = [curView_ EXCEPT ![self] = curView_[self] + 1]
                  /\ IF curView_'[self] > Len(Leaders)
                        THEN /\ pc' = [pc EXCEPT ![self] = "Done"]
                        ELSE /\ pc' = [pc EXCEPT ![self] = "NextView2"]
                  /\ UNCHANGED << NextBlockId, AllBlocks, AllQC, 
                                  BroadcastMessages, RepliesToLeader, leader_, 
                                  prepareQC, lockedQC, commitQC, 
                                  committedBlocks, receivedVotes, curView, 
                                  leader >>

NextView2(self) == /\ pc[self] = "NextView2"
                   /\ leader_' = [leader_ EXCEPT ![self] = Leaders[curView_[self]]]
                   /\ IF (self = leader_'[self])
                         THEN /\ receivedVotes' = [receivedVotes EXCEPT ![self] = {CreateMessage(NewView, curView_[self], Null, prepareQC[self], self)}]
                              /\ pc' = [pc EXCEPT ![self] = "WaitForNewView"]
                              /\ UNCHANGED RepliesToLeader
                         ELSE /\ RepliesToLeader' = (                   RepliesToLeader \union {
                                                         CreateMessage(NewView, curView_[self], Null, prepareQC[self], self)
                                                     })
                              /\ pc' = [pc EXCEPT ![self] = "ReplicaPrepare"]
                              /\ UNCHANGED receivedVotes
                   /\ UNCHANGED << NextBlockId, AllBlocks, AllQC, 
                                   BroadcastMessages, curView_, prepareQC, 
                                   lockedQC, commitQC, committedBlocks, 
                                   curView, leader >>

WaitForNewView(self) == /\ pc[self] = "WaitForNewView"
                        /\ IF Cardinality({v.vote : v \in receivedVotes[self]}) < QCThresh
                              THEN /\ \/ /\ \E m \in { m \in RepliesToLeader : m.type = NewView /\ m.viewNum = curView_[self] }:
                                              receivedVotes' = [receivedVotes EXCEPT ![self] = receivedVotes[self] \union {m}]
                                         /\ pc' = [pc EXCEPT ![self] = "WaitForNewView"]
                                      \/ /\ pc' = [pc EXCEPT ![self] = "NextView"]
                                         /\ UNCHANGED receivedVotes
                                   /\ UNCHANGED << NextBlockId, AllBlocks, 
                                                   BroadcastMessages, 
                                                   RepliesToLeader, prepareQC >>
                              ELSE /\ Assert(Cardinality(receivedVotes[self]) >= QCThresh, 
                                             "Failure of assertion at line 163, column 5.")
                                   /\ prepareQC' = [prepareQC EXCEPT ![self] = MaxJustifyVN(receivedVotes[self]).justify]
                                   /\ LET newBlock == CreateBlock(NextBlockId, prepareQC'[self].block) IN
                                        /\ NextBlockId' = NextBlockId + 1
                                        /\ AllBlocks' = (AllBlocks \union {newBlock})
                                        /\ BroadcastMessages' = (                 BroadcastMessages \union
                                                                 {CreateMessage(Prepare, curView_[self], newBlock, prepareQC'[self], self)})
                                        /\ RepliesToLeader' = (                   RepliesToLeader \union {
                                                                   CreateMessage(Prepare, curView_[self], newBlock, Null, self)
                                                               })
                                        /\ IF TRUE
                                              THEN /\ receivedVotes' = [receivedVotes EXCEPT ![self] = { CreateMessage(Prepare, curView_[self], newBlock, Null, self) }]
                                              ELSE /\ TRUE
                                                   /\ UNCHANGED receivedVotes
                                   /\ pc' = [pc EXCEPT ![self] = "LeaderPreCommit"]
                        /\ UNCHANGED << AllQC, curView_, leader_, lockedQC, 
                                        commitQC, committedBlocks, curView, 
                                        leader >>

LeaderPreCommit(self) == /\ pc[self] = "LeaderPreCommit"
                         /\ IF ~CheckVotesForQC(receivedVotes[self])
                               THEN /\ \/ /\ \E m \in { m \in RepliesToLeader : m.type = Prepare /\ m.viewNum = curView_[self] }:
                                               IF \A v \in receivedVotes[self] : m.block = v.block
                                                  THEN /\ receivedVotes' = [receivedVotes EXCEPT ![self] = receivedVotes[self] \union {m}]
                                                  ELSE /\ TRUE
                                                       /\ UNCHANGED receivedVotes
                                          /\ pc' = [pc EXCEPT ![self] = "LeaderPreCommit"]
                                       \/ /\ pc' = [pc EXCEPT ![self] = "NextView"]
                                          /\ UNCHANGED receivedVotes
                                    /\ UNCHANGED << AllQC, BroadcastMessages, 
                                                    RepliesToLeader, prepareQC >>
                               ELSE /\ Assert(CheckVotesForQC(receivedVotes[self]), 
                                              "Failure of assertion at line 93, column 5 of macro called at line 169, column 5.")
                                    /\ prepareQC' = [prepareQC EXCEPT ![self] = GenerateQC(receivedVotes[self])]
                                    /\ AllQC' = (AllQC \union {prepareQC'[self]})
                                    /\ BroadcastMessages' = (                 BroadcastMessages \union
                                                             {CreateMessage(PreCommit, curView_[self], Null, prepareQC'[self], self)})
                                    /\ IF PreCommit = Decide
                                          THEN /\ receivedVotes' = [receivedVotes EXCEPT ![self] = {}]
                                               /\ UNCHANGED RepliesToLeader
                                          ELSE /\ receivedVotes' = [receivedVotes EXCEPT ![self] = { CreateMessage(PreCommit, curView_[self], prepareQC'[self].block, Null, self) }]
                                               /\ RepliesToLeader' = (                   RepliesToLeader \union {
                                                                          CreateMessage(PreCommit, curView_[self], (prepareQC'[self].block), Null, self)
                                                                      })
                                    /\ pc' = [pc EXCEPT ![self] = "LeaderCommit"]
                         /\ UNCHANGED << NextBlockId, AllBlocks, curView_, 
                                         leader_, lockedQC, commitQC, 
                                         committedBlocks, curView, leader >>

LeaderCommit(self) == /\ pc[self] = "LeaderCommit"
                      /\ IF ~CheckVotesForQC(receivedVotes[self])
                            THEN /\ \/ /\ \E m \in { m \in RepliesToLeader : m.type = PreCommit /\ m.viewNum = curView_[self] }:
                                            IF \A v \in receivedVotes[self] : m.block = v.block
                                               THEN /\ receivedVotes' = [receivedVotes EXCEPT ![self] = receivedVotes[self] \union {m}]
                                               ELSE /\ TRUE
                                                    /\ UNCHANGED receivedVotes
                                       /\ pc' = [pc EXCEPT ![self] = "LeaderCommit"]
                                    \/ /\ pc' = [pc EXCEPT ![self] = "NextView"]
                                       /\ UNCHANGED receivedVotes
                                 /\ UNCHANGED << AllQC, BroadcastMessages, 
                                                 RepliesToLeader, lockedQC >>
                            ELSE /\ Assert(CheckVotesForQC(receivedVotes[self]), 
                                           "Failure of assertion at line 93, column 5 of macro called at line 173, column 5.")
                                 /\ lockedQC' = [lockedQC EXCEPT ![self] = GenerateQC(receivedVotes[self])]
                                 /\ AllQC' = (AllQC \union {lockedQC'[self]})
                                 /\ BroadcastMessages' = (                 BroadcastMessages \union
                                                          {CreateMessage(Commit, curView_[self], Null, lockedQC'[self], self)})
                                 /\ IF Commit = Decide
                                       THEN /\ receivedVotes' = [receivedVotes EXCEPT ![self] = {}]
                                            /\ UNCHANGED RepliesToLeader
                                       ELSE /\ receivedVotes' = [receivedVotes EXCEPT ![self] = { CreateMessage(Commit, curView_[self], lockedQC'[self].block, Null, self) }]
                                            /\ RepliesToLeader' = (                   RepliesToLeader \union {
                                                                       CreateMessage(Commit, curView_[self], (lockedQC'[self].block), Null, self)
                                                                   })
                                 /\ pc' = [pc EXCEPT ![self] = "LeaderDecide"]
                      /\ UNCHANGED << NextBlockId, AllBlocks, curView_, 
                                      leader_, prepareQC, commitQC, 
                                      committedBlocks, curView, leader >>

LeaderDecide(self) == /\ pc[self] = "LeaderDecide"
                      /\ IF ~CheckVotesForQC(receivedVotes[self])
                            THEN /\ \/ /\ \E m \in { m \in RepliesToLeader : m.type = Commit /\ m.viewNum = curView_[self] }:
                                            IF \A v \in receivedVotes[self] : m.block = v.block
                                               THEN /\ receivedVotes' = [receivedVotes EXCEPT ![self] = receivedVotes[self] \union {m}]
                                               ELSE /\ TRUE
                                                    /\ UNCHANGED receivedVotes
                                       /\ pc' = [pc EXCEPT ![self] = "LeaderDecide"]
                                    \/ /\ pc' = [pc EXCEPT ![self] = "NextView"]
                                       /\ UNCHANGED receivedVotes
                                 /\ UNCHANGED << AllQC, BroadcastMessages, 
                                                 RepliesToLeader, commitQC, 
                                                 committedBlocks >>
                            ELSE /\ Assert(CheckVotesForQC(receivedVotes[self]), 
                                           "Failure of assertion at line 93, column 5 of macro called at line 177, column 5.")
                                 /\ commitQC' = [commitQC EXCEPT ![self] = GenerateQC(receivedVotes[self])]
                                 /\ AllQC' = (AllQC \union {commitQC'[self]})
                                 /\ BroadcastMessages' = (                 BroadcastMessages \union
                                                          {CreateMessage(Decide, curView_[self], Null, commitQC'[self], self)})
                                 /\ IF Decide = Decide
                                       THEN /\ receivedVotes' = [receivedVotes EXCEPT ![self] = {}]
                                            /\ UNCHANGED RepliesToLeader
                                       ELSE /\ receivedVotes' = [receivedVotes EXCEPT ![self] = { CreateMessage(Decide, curView_[self], commitQC'[self].block, Null, self) }]
                                            /\ RepliesToLeader' = (                   RepliesToLeader \union {
                                                                       CreateMessage(Decide, curView_[self], (commitQC'[self].block), Null, self)
                                                                   })
                                 /\ committedBlocks' = [committedBlocks EXCEPT ![self] = committedBlocks[self] \union {commitQC'[self].block}]
                                 /\ pc' = [pc EXCEPT ![self] = "NextView"]
                      /\ UNCHANGED << NextBlockId, AllBlocks, curView_, 
                                      leader_, prepareQC, lockedQC, curView, 
                                      leader >>

ReplicaPrepare(self) == /\ pc[self] = "ReplicaPrepare"
                        /\ \/ /\ \E m \in FilterMessages(Prepare, curView_[self], leader_[self]):
                                   IF DirectlyExtends(m.block, m.justify.block)
                                       /\ ( BlockExtends(m.block, lockedQC[self].block, AllBlocks)
                                           \/ m.justify.viewNum > lockedQC[self].viewNum )
                                      THEN /\ RepliesToLeader' = (                   RepliesToLeader \union {
                                                                      CreateMessage(Prepare, curView_[self], (m.block), Null, self)
                                                                  })
                                      ELSE /\ TRUE
                                           /\ UNCHANGED RepliesToLeader
                              /\ pc' = [pc EXCEPT ![self] = "ReplicaPreCommit"]
                           \/ /\ pc' = [pc EXCEPT ![self] = "NextView"]
                              /\ UNCHANGED RepliesToLeader
                        /\ UNCHANGED << NextBlockId, AllBlocks, AllQC, 
                                        BroadcastMessages, curView_, leader_, 
                                        prepareQC, lockedQC, commitQC, 
                                        committedBlocks, receivedVotes, 
                                        curView, leader >>

ReplicaPreCommit(self) == /\ pc[self] = "ReplicaPreCommit"
                          /\ \/ /\ \E m \in FilterMessages(PreCommit, curView_[self], leader_[self]):
                                     IF m.justify.type = Prepare /\ m.justify.viewNum = curView_[self]
                                        THEN /\ prepareQC' = [prepareQC EXCEPT ![self] = m.justify]
                                             /\ RepliesToLeader' = (                   RepliesToLeader \union {
                                                                        CreateMessage(PreCommit, curView_[self], (m.justify.block), Null, self)
                                                                    })
                                        ELSE /\ TRUE
                                             /\ UNCHANGED << RepliesToLeader, 
                                                             prepareQC >>
                                /\ pc' = [pc EXCEPT ![self] = "ReplicaCommit"]
                             \/ /\ pc' = [pc EXCEPT ![self] = "NextView"]
                                /\ UNCHANGED <<RepliesToLeader, prepareQC>>
                          /\ UNCHANGED << NextBlockId, AllBlocks, AllQC, 
                                          BroadcastMessages, curView_, leader_, 
                                          lockedQC, commitQC, committedBlocks, 
                                          receivedVotes, curView, leader >>

ReplicaCommit(self) == /\ pc[self] = "ReplicaCommit"
                       /\ \/ /\ \E m \in FilterMessages(Commit, curView_[self], leader_[self]):
                                  IF m.justify.type = PreCommit /\ m.justify.viewNum = curView_[self]
                                     THEN /\ lockedQC' = [lockedQC EXCEPT ![self] = m.justify]
                                          /\ RepliesToLeader' = (                   RepliesToLeader \union {
                                                                     CreateMessage(Commit, curView_[self], (m.justify.block), Null, self)
                                                                 })
                                     ELSE /\ TRUE
                                          /\ UNCHANGED << RepliesToLeader, 
                                                          lockedQC >>
                             /\ pc' = [pc EXCEPT ![self] = "ReplicaDecide"]
                          \/ /\ pc' = [pc EXCEPT ![self] = "NextView"]
                             /\ UNCHANGED <<RepliesToLeader, lockedQC>>
                       /\ UNCHANGED << NextBlockId, AllBlocks, AllQC, 
                                       BroadcastMessages, curView_, leader_, 
                                       prepareQC, commitQC, committedBlocks, 
                                       receivedVotes, curView, leader >>

ReplicaDecide(self) == /\ pc[self] = "ReplicaDecide"
                       /\ \/ /\ \E m \in FilterMessages(Decide, curView_[self], leader_[self]):
                                  IF m.justify.type = Commit /\ m.justify.viewNum = curView_[self]
                                     THEN /\ committedBlocks' = [committedBlocks EXCEPT ![self] = committedBlocks[self] \union {m.justify.block}]
                                     ELSE /\ TRUE
                                          /\ UNCHANGED committedBlocks
                             /\ pc' = [pc EXCEPT ![self] = "NextView"]
                          \/ /\ pc' = [pc EXCEPT ![self] = "NextView"]
                             /\ UNCHANGED committedBlocks
                       /\ UNCHANGED << NextBlockId, AllBlocks, AllQC, 
                                       BroadcastMessages, RepliesToLeader, 
                                       curView_, leader_, prepareQC, lockedQC, 
                                       commitQC, receivedVotes, curView, 
                                       leader >>

rep(self) == NextView(self) \/ NextView2(self) \/ WaitForNewView(self)
                \/ LeaderPreCommit(self) \/ LeaderCommit(self)
                \/ LeaderDecide(self) \/ ReplicaPrepare(self)
                \/ ReplicaPreCommit(self) \/ ReplicaCommit(self)
                \/ ReplicaDecide(self)

FNextView(self) == /\ pc[self] = "FNextView"
                   /\ curView' = [curView EXCEPT ![self] = curView[self] + 1]
                   /\ IF curView'[self] > Len(Leaders)
                         THEN /\ pc' = [pc EXCEPT ![self] = "Done"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "FNextView2"]
                   /\ UNCHANGED << NextBlockId, AllBlocks, AllQC, 
                                   BroadcastMessages, RepliesToLeader, 
                                   curView_, leader_, prepareQC, lockedQC, 
                                   commitQC, committedBlocks, receivedVotes, 
                                   leader >>

FNextView2(self) == /\ pc[self] = "FNextView2"
                    /\ leader' = [leader EXCEPT ![self] = Leaders[curView[self]]]
                    /\ IF (self = leader'[self])
                          THEN /\ pc' = [pc EXCEPT ![self] = "FPrepare"]
                               /\ UNCHANGED RepliesToLeader
                          ELSE /\ \E qc \in GenerateAllQCForType(RepliesToLeader, Prepare):
                                    RepliesToLeader' = (                   RepliesToLeader \union {
                                                            CreateMessage(NewView, curView[self], Null, qc, self)
                                                        })
                               /\ pc' = [pc EXCEPT ![self] = "FReplicaPrepare"]
                    /\ UNCHANGED << NextBlockId, AllBlocks, AllQC, 
                                    BroadcastMessages, curView_, leader_, 
                                    prepareQC, lockedQC, commitQC, 
                                    committedBlocks, receivedVotes, curView >>

FPrepare(self) == /\ pc[self] = "FPrepare"
                  /\ \E qc \in GenerateAllQCForType(RepliesToLeader, Prepare):
                       LET newBlock == CreateBlock(NextBlockId, qc.block) IN
                         /\ NextBlockId' = NextBlockId + 1
                         /\ AllBlocks' = (AllBlocks \union {newBlock})
                         /\ BroadcastMessages' = (                 BroadcastMessages \union
                                                  {CreateMessage(Prepare, curView[self], newBlock, qc, self)})
                         /\ RepliesToLeader' = (                   RepliesToLeader \union {
                                                    CreateMessage(Prepare, curView[self], newBlock, Null, self)
                                                })
                         /\ IF FALSE
                               THEN /\ receivedVotes' = [receivedVotes EXCEPT ![self] = { CreateMessage(Prepare, curView[self], newBlock, Null, self) }]
                               ELSE /\ TRUE
                                    /\ UNCHANGED receivedVotes
                  /\ pc' = [pc EXCEPT ![self] = "FPrepare2"]
                  /\ UNCHANGED << AllQC, curView_, leader_, prepareQC, 
                                  lockedQC, commitQC, committedBlocks, curView, 
                                  leader >>

FPrepare2(self) == /\ pc[self] = "FPrepare2"
                   /\ \E qc \in GenerateAllQCForType(RepliesToLeader, Prepare):
                        LET newBlock == CreateBlock(NextBlockId, qc.block) IN
                          /\ NextBlockId' = NextBlockId + 1
                          /\ AllBlocks' = (AllBlocks \union {newBlock})
                          /\ BroadcastMessages' = (                 BroadcastMessages \union
                                                   {CreateMessage(Prepare, curView[self], newBlock, qc, self)})
                          /\ RepliesToLeader' = (                   RepliesToLeader \union {
                                                     CreateMessage(Prepare, curView[self], newBlock, Null, self)
                                                 })
                          /\ IF FALSE
                                THEN /\ receivedVotes' = [receivedVotes EXCEPT ![self] = { CreateMessage(Prepare, curView[self], newBlock, Null, self) }]
                                ELSE /\ TRUE
                                     /\ UNCHANGED receivedVotes
                   /\ pc' = [pc EXCEPT ![self] = "FPreCommit"]
                   /\ UNCHANGED << AllQC, curView_, leader_, prepareQC, 
                                   lockedQC, commitQC, committedBlocks, 
                                   curView, leader >>

FPreCommit(self) == /\ pc[self] = "FPreCommit"
                    /\ LET allQC == GenerateAllQCForType(RepliesToLeader, Prepare) IN
                         \E qc1 \in AllQC:
                           \E qc2 \in AllQC:
                             BroadcastMessages' = (                 BroadcastMessages \union
                                                   { CreateMessage(PreCommit, curView[self], Null, qc1, self),
                                                     CreateMessage(PreCommit, curView[self], Null, qc1, self) })
                    /\ pc' = [pc EXCEPT ![self] = "FPreCommit2"]
                    /\ UNCHANGED << NextBlockId, AllBlocks, AllQC, 
                                    RepliesToLeader, curView_, leader_, 
                                    prepareQC, lockedQC, commitQC, 
                                    committedBlocks, receivedVotes, curView, 
                                    leader >>

FPreCommit2(self) == /\ pc[self] = "FPreCommit2"
                     /\ LET allQC == GenerateAllQCForType(RepliesToLeader, Prepare) IN
                          \E qc1 \in AllQC:
                            \E qc2 \in AllQC:
                              BroadcastMessages' = (                 BroadcastMessages \union
                                                    { CreateMessage(PreCommit, curView[self], Null, qc1, self),
                                                      CreateMessage(PreCommit, curView[self], Null, qc1, self) })
                     /\ pc' = [pc EXCEPT ![self] = "FCommit"]
                     /\ UNCHANGED << NextBlockId, AllBlocks, AllQC, 
                                     RepliesToLeader, curView_, leader_, 
                                     prepareQC, lockedQC, commitQC, 
                                     committedBlocks, receivedVotes, curView, 
                                     leader >>

FCommit(self) == /\ pc[self] = "FCommit"
                 /\ LET allQC == GenerateAllQCForType(RepliesToLeader, PreCommit) IN
                      \E qc1 \in AllQC:
                        \E qc2 \in AllQC:
                          BroadcastMessages' = (                 BroadcastMessages \union
                                                { CreateMessage(Commit, curView[self], Null, qc1, self),
                                                  CreateMessage(Commit, curView[self], Null, qc1, self) })
                 /\ pc' = [pc EXCEPT ![self] = "FCommit2"]
                 /\ UNCHANGED << NextBlockId, AllBlocks, AllQC, 
                                 RepliesToLeader, curView_, leader_, prepareQC, 
                                 lockedQC, commitQC, committedBlocks, 
                                 receivedVotes, curView, leader >>

FCommit2(self) == /\ pc[self] = "FCommit2"
                  /\ LET allQC == GenerateAllQCForType(RepliesToLeader, PreCommit) IN
                       \E qc1 \in AllQC:
                         \E qc2 \in AllQC:
                           BroadcastMessages' = (                 BroadcastMessages \union
                                                 { CreateMessage(Commit, curView[self], Null, qc1, self),
                                                   CreateMessage(Commit, curView[self], Null, qc1, self) })
                  /\ pc' = [pc EXCEPT ![self] = "FDecide"]
                  /\ UNCHANGED << NextBlockId, AllBlocks, AllQC, 
                                  RepliesToLeader, curView_, leader_, 
                                  prepareQC, lockedQC, commitQC, 
                                  committedBlocks, receivedVotes, curView, 
                                  leader >>

FDecide(self) == /\ pc[self] = "FDecide"
                 /\ LET allQC == GenerateAllQCForType(RepliesToLeader, Commit) IN
                      \E qc1 \in AllQC:
                        \E qc2 \in AllQC:
                          BroadcastMessages' = (                 BroadcastMessages \union
                                                { CreateMessage(Decide, curView[self], Null, qc1, self),
                                                  CreateMessage(Decide, curView[self], Null, qc1, self) })
                 /\ pc' = [pc EXCEPT ![self] = "FLeaderDone"]
                 /\ UNCHANGED << NextBlockId, AllBlocks, AllQC, 
                                 RepliesToLeader, curView_, leader_, prepareQC, 
                                 lockedQC, commitQC, committedBlocks, 
                                 receivedVotes, curView, leader >>

FLeaderDone(self) == /\ pc[self] = "FLeaderDone"
                     /\ pc' = [pc EXCEPT ![self] = "FNextView"]
                     /\ UNCHANGED << NextBlockId, AllBlocks, AllQC, 
                                     BroadcastMessages, RepliesToLeader, 
                                     curView_, leader_, prepareQC, lockedQC, 
                                     commitQC, committedBlocks, receivedVotes, 
                                     curView, leader >>

FReplicaPrepare(self) == /\ pc[self] = "FReplicaPrepare"
                         /\ \/ /\ \E b \in AllBlocks:
                                    RepliesToLeader' = (                   RepliesToLeader \union {
                                                            CreateMessage(Prepare, curView[self], b, Null, self)
                                                        })
                               /\ pc' = [pc EXCEPT ![self] = "FReplicaPreCommit"]
                               /\ UNCHANGED <<NextBlockId, AllBlocks>>
                            \/ /\ \E p \in AllBlocks:
                                    LET b == CreateBlock(NextBlockId, p) IN
                                      /\ NextBlockId' = NextBlockId + 1
                                      /\ AllBlocks' = (AllBlocks \union {b})
                                      /\ RepliesToLeader' = (                   RepliesToLeader \union {
                                                                 CreateMessage(Prepare, curView[self], b, Null, self)
                                                             })
                               /\ pc' = [pc EXCEPT ![self] = "FReplicaPreCommit"]
                            \/ /\ pc' = [pc EXCEPT ![self] = "FNextView"]
                               /\ UNCHANGED <<NextBlockId, AllBlocks, RepliesToLeader>>
                            \/ /\ pc' = [pc EXCEPT ![self] = "FReplicaPreCommit"]
                               /\ UNCHANGED <<NextBlockId, AllBlocks, RepliesToLeader>>
                         /\ UNCHANGED << AllQC, BroadcastMessages, curView_, 
                                         leader_, prepareQC, lockedQC, 
                                         commitQC, committedBlocks, 
                                         receivedVotes, curView, leader >>

FReplicaPreCommit(self) == /\ pc[self] = "FReplicaPreCommit"
                           /\ \/ /\ \E b \in AllBlocks:
                                      RepliesToLeader' = (                   RepliesToLeader \union {
                                                              CreateMessage(PreCommit, curView[self], b, Null, self)
                                                          })
                                 /\ pc' = [pc EXCEPT ![self] = "FReplicaCommit"]
                                 /\ UNCHANGED <<NextBlockId, AllBlocks>>
                              \/ /\ \E p \in AllBlocks:
                                      LET b == CreateBlock(NextBlockId, p) IN
                                        /\ NextBlockId' = NextBlockId + 1
                                        /\ AllBlocks' = (AllBlocks \union {b})
                                        /\ RepliesToLeader' = (                   RepliesToLeader \union {
                                                                   CreateMessage(Prepare, curView[self], b, Null, self)
                                                               })
                                 /\ pc' = [pc EXCEPT ![self] = "FReplicaCommit"]
                              \/ /\ pc' = [pc EXCEPT ![self] = "FNextView"]
                                 /\ UNCHANGED <<NextBlockId, AllBlocks, RepliesToLeader>>
                              \/ /\ pc' = [pc EXCEPT ![self] = "FReplicaCommit"]
                                 /\ UNCHANGED <<NextBlockId, AllBlocks, RepliesToLeader>>
                           /\ UNCHANGED << AllQC, BroadcastMessages, curView_, 
                                           leader_, prepareQC, lockedQC, 
                                           commitQC, committedBlocks, 
                                           receivedVotes, curView, leader >>

FReplicaCommit(self) == /\ pc[self] = "FReplicaCommit"
                        /\ \/ /\ \E b \in AllBlocks:
                                   RepliesToLeader' = (                   RepliesToLeader \union {
                                                           CreateMessage(Commit, curView[self], b, Null, self)
                                                       })
                              /\ pc' = [pc EXCEPT ![self] = "FNextView"]
                              /\ UNCHANGED <<NextBlockId, AllBlocks>>
                           \/ /\ \E p \in AllBlocks:
                                   LET b == CreateBlock(NextBlockId, p) IN
                                     /\ NextBlockId' = NextBlockId + 1
                                     /\ AllBlocks' = (AllBlocks \union {b})
                                     /\ RepliesToLeader' = (                   RepliesToLeader \union {
                                                                CreateMessage(Prepare, curView[self], b, Null, self)
                                                            })
                              /\ pc' = [pc EXCEPT ![self] = "FNextView"]
                           \/ /\ pc' = [pc EXCEPT ![self] = "FNextView"]
                              /\ UNCHANGED <<NextBlockId, AllBlocks, RepliesToLeader>>
                        /\ UNCHANGED << AllQC, BroadcastMessages, curView_, 
                                        leader_, prepareQC, lockedQC, commitQC, 
                                        committedBlocks, receivedVotes, 
                                        curView, leader >>

faulty(self) == FNextView(self) \/ FNextView2(self) \/ FPrepare(self)
                   \/ FPrepare2(self) \/ FPreCommit(self)
                   \/ FPreCommit2(self) \/ FCommit(self) \/ FCommit2(self)
                   \/ FDecide(self) \/ FLeaderDone(self)
                   \/ FReplicaPrepare(self) \/ FReplicaPreCommit(self)
                   \/ FReplicaCommit(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Correct: rep(self))
           \/ (\E self \in Faulty: faulty(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Correct : WF_vars(rep(self))
        /\ \A self \in Faulty : WF_vars(faulty(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

TypeInvariant ==
    /\ NextBlockId \in Nat
    /\ \A b \in AllBlocks : b \in BlockType
    /\ \A m \in BroadcastMessages : m \in MessageType
    /\ \A m \in RepliesToLeader : m \in MessageType
    /\ \A self \in DOMAIN curView : curView[self] \in Nat
    /\ \A self \in DOMAIN leader : leader[self] \in Replicas
    /\ \A self \in DOMAIN prepareQC : prepareQC[self] \in QCType
    /\ \A self \in DOMAIN lockedQC : lockedQC[self] \in QCType
    /\ \A self \in DOMAIN commitQC : commitQC[self] \in QCType
    /\ \A self \in DOMAIN committedBlocks : \A b \in committedBlocks[self] : b \in BlockType
    /\ \A self \in DOMAIN receivedVotes : \A m \in receivedVotes[self] : m \in MessageType

AllDone == \A self \in ProcSet: pc[self] = "Done"

NoLoopsInBlocks == NoLoops(AllBlocks)

NoConflictingBlocksCommitted ==
    \A r1, r2 \in Correct : NoConflictsInBlockSets(
        committedBlocks[r1], committedBlocks[r2], AllBlocks)

AllEventuallyCommitABlock == AllDone => \A r \in Replicas : Cardinality(committedBlocks[r]) > 1

=============================================================================