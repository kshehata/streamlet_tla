---- MODULE MCStreamlet ----
EXTENDS Streamlet, TLC

CONSTANTS h1, h2, h3, a1

ConstCorrectNodes == {h1, h2}
ConstFaultyNodes == {a1}
NodePerms == Permutations(ConstCorrectNodes) \cup Permutations(ConstFaultyNodes)

ConstLeaders == <<h2, a1, h1>>

=============================================================================
