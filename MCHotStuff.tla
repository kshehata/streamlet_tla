---- MODULE MCHotStuff ----
EXTENDS HotStuff, TLC

CONSTANTS r1, r2, r3, r4

ConstReplicas == {r1, r2, r3, r4}
ReplicaPerms == Permutations(ConstReplicas)

ConstLeaders == <<r3>>

=============================================================================