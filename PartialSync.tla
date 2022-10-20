---------------------------- MODULE PartialSync ----------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANTS Nodes, NumRounds, GlobalStabTime

ASSUME  /\ Cardinality(Nodes) > 0
        /\ NumRounds \in Nat
        /\ GlobalStabTime < NumRounds

Messages == [
                round : Nat,
                sender : Nodes,
                received : SUBSET(Nodes)
            ]

(*--algorithm SyncSenders
variables
  Msgs = {};
  CurrentRound = 0;

macro SendMessage() begin
    Msgs := Msgs \union { [
        round |-> CurrentRound,
        sender |-> self,
        received |-> {self}
    ] };
end macro

macro ReceiveMessage(m) begin
    Msgs := (Msgs \ {m}) \union
            { [m EXCEPT !.received = m.received \union {self}] };
end macro

fair process n \in Nodes
variables
    i = 0;
begin
    Send:
        SendMessage();
        i := i + 1;
    Receive:
        while (i > CurrentRound) do
            with m \in { m \in Msgs : m.round = CurrentRound } do
                ReceiveMessage(m);
            end with;
        end while;
        if (i < NumRounds) then
            goto Send;
        end if;
end process;

fair process Timer = "timer"
begin
    NextRound:
        while (CurrentRound < NumRounds) do
            \* await(\A n \in Nodes \E m \in Msgs : (m.round = CurrentRound) /\ (m.sender = n));
            \* await(\A m \in Msgs : (m.round = CurrentRound) => (m.received = Nodes));
            CurrentRound := CurrentRound + 1;
        end while;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "41902a4b" /\ chksum(tla) = "7da3ad46")
VARIABLES Msgs, CurrentRound, pc, i

vars == << Msgs, CurrentRound, pc, i >>

ProcSet == (Nodes) \cup {"timer"}

Init == (* Global variables *)
        /\ Msgs = {}
        /\ CurrentRound = 0
        (* Process n *)
        /\ i = [self \in Nodes |-> 0]
        /\ pc = [self \in ProcSet |-> CASE self \in Nodes -> "Send"
                                        [] self = "timer" -> "NextRound"]

Send(self) == /\ pc[self] = "Send"
              /\ Msgs' = (        Msgs \union { [
                              round |-> CurrentRound,
                              sender |-> self,
                              received |-> {self}
                          ] })
              /\ i' = [i EXCEPT ![self] = i[self] + 1]
              /\ pc' = [pc EXCEPT ![self] = "Receive"]
              /\ UNCHANGED CurrentRound

Receive(self) == /\ pc[self] = "Receive"
                 /\ IF (i[self] > CurrentRound)
                       THEN /\ \E m \in { m \in Msgs : m.round = CurrentRound }:
                                 Msgs' = ((Msgs \ {m}) \union
                                          { [m EXCEPT !.received = m.received \union {self}] })
                            /\ pc' = [pc EXCEPT ![self] = "Receive"]
                       ELSE /\ IF (i[self] < NumRounds)
                                  THEN /\ pc' = [pc EXCEPT ![self] = "Send"]
                                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                            /\ Msgs' = Msgs
                 /\ UNCHANGED << CurrentRound, i >>

n(self) == Send(self) \/ Receive(self)

NextRound == /\ pc["timer"] = "NextRound"
             /\ IF (CurrentRound < NumRounds)
                   THEN /\ CurrentRound' = CurrentRound + 1
                        /\ pc' = [pc EXCEPT !["timer"] = "NextRound"]
                   ELSE /\ pc' = [pc EXCEPT !["timer"] = "Done"]
                        /\ UNCHANGED CurrentRound
             /\ UNCHANGED << Msgs, i >>

Timer == NextRound

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Timer
           \/ (\E self \in Nodes: n(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Nodes : WF_vars(n(self))
        /\ WF_vars(Timer)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

TypeInvariant == \A m \in Msgs : m \in Messages

NodePerms == Permutations(Nodes)

AllMessagesReceived == \A m \in Msgs : m.received = Nodes

AllMessagesEventuallyReceived == <>(AllMessagesReceived)

=============================================================================
\* Modification History
\* Last modified Thu Oct 20 15:13:00 SGT 2022 by kshehata
\* Created Thu Oct 20 14:55:45 SGT 2022 by kshehata
