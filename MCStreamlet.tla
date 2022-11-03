---- MODULE MCStreamlet ----
EXTENDS Streamlet, TLC

CONSTANTS n1, n2, n3

ConstNodes == {n1, n2, n3}

ConstCorrupt == {n3}

ConstLeaders == <<n1>>

=============================================================================
