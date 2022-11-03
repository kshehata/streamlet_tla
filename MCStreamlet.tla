---- MODULE MCStreamlet ----
EXTENDS Streamlet, TLC

CONSTANTS n1, n2, n3, n4

ConstCorrectNodes == {n1, n2, n3}
ConstFaultyNodes == {n4}
NodePerms == Permutations(ConstCorrectNodes) \cup Permutations(ConstFaultyNodes)

ConstLeaders == <<n1>>

=============================================================================
