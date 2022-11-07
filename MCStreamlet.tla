---- MODULE MCStreamlet ----
EXTENDS Streamlet, TLC

CONSTANTS h1, h2, h3, a1

ConstCorrectNodes == {h1, h2, h3}
ConstFaultyNodes == {}
NodePerms == Permutations(ConstCorrectNodes) \cup Permutations(ConstFaultyNodes)

ConstLeaders == <<h2, h1, h3, h1>>

\* for debugging purposes: copy from error trace then paste here, and uncomment the ASSUME PrintT statements: 
localBlocksTest == (
    h1 :> {[epoch |-> 0, id |-> 0, length |-> 0, parent |-> 0, sigs |-> {h1, h2, a1}], [epoch |-> 1, id |-> 1, length |-> 1, parent |-> 0, sigs |-> {h1, h2}], [epoch |-> 2, id |-> 2, length |-> 2, parent |-> 1, sigs |-> {h1, a1}]} @@
    h2 :> {[epoch |-> 0, id |-> 0, length |-> 0, parent |-> 0, sigs |-> {h1, h2, a1}], [epoch |-> 1, id |-> 1, length |-> 1, parent |-> 0, sigs |-> {h2, a1}], [epoch |-> 2, id |-> 2, length |-> 2, parent |-> 1, sigs |-> {h2, a1}]} @@ 
    a1 :> {[epoch |-> 0, id |-> 0, length |-> 0, parent |-> 0, sigs |-> {h1, h2, a1}], [epoch |-> 1, id |-> 1, length |-> 1, parent |-> 0, sigs |-> {h2, a1}], [epoch |-> 2, id |-> 2, length |-> 2, parent |-> 1, sigs |-> {a1}]})
\* ASSUME PrintT(FinalizedBlocks(localBlocksTest[h1]))
\* ASSUME PrintT(FinalizedBlocks(localBlocksTest[h2]))
\* ASSUME PrintT(FinalizedBlocks(localBlocksTest[a1]))

chain1 == FinalizedBlocks(localBlocksTest[h1])
chain2 == FinalizedBlocks(localBlocksTest[h2])
\* ASSUME PrintT(IsPrefixedChain(chain1, chain2))
=============================================================================
