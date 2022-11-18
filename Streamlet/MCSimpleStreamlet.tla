---- MODULE MCSimpleStreamlet ----
EXTENDS TLC, SimpleStreamlet

CONSTANTS h1, h2, h3, a1

ConstCorrectNodes == {h1, h2}
ConstFaultyNodes == {a1}

NodePerms == Permutations(ConstCorrectNodes) \cup Permutations(ConstFaultyNodes)
CorrectNdoePerm == Permutations(ConstCorrectNodes)

ConstLeaders == <<h1, a1, a1>>
====