---- MODULE MCHotStuff ----
EXTENDS HotStuff, TLC

CONSTANTS r1, r2, r3, r4

ConstCorrect == {r1, r2, r3}
ConstFaulty == {r4}
ReplicaPerms == Permutations(ConstCorrect)
ConstReplicas == ConstCorrect \union ConstFaulty

ConstLeaders == <<r1, r2>>

=============================================================================