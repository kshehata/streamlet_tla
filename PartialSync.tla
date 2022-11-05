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
    localRound = CurrentRound;
begin
    Send:
        SendMessage();
    Receive:
        while (localRound = CurrentRound) do
            with m \in { m \in Msgs : m.round <= CurrentRound /\ self \notin m.received } do
                ReceiveMessage(m);
            end with;
        end while;
        localRound := localRound + 1;
        if (localRound < NumRounds) then
            goto Send;
        end if;
end process;

fair process Timer = "timer"
begin
    NextRound:
        while (CurrentRound < NumRounds) do
            await (\A s \in Nodes : \E m \in Msgs : (m.round = CurrentRound) /\ (m.sender = s));
            if (CurrentRound >= GlobalStabTime) then
                await (\A m \in {m \in Msgs: m.round <= CurrentRound}: m.received = Nodes);
            end if;
            CurrentRound := CurrentRound + 1;
        end while;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "b10f977" /\ chksum(tla) = "77a5e516")
VARIABLES Msgs, CurrentRound, pc, localRound

vars == << Msgs, CurrentRound, pc, localRound >>

ProcSet == (Nodes) \cup {"timer"}

Init == (* Global variables *)
        /\ Msgs = {}
        /\ CurrentRound = 0
        (* Process n *)
        /\ localRound = [self \in Nodes |-> CurrentRound]
        /\ pc = [self \in ProcSet |-> CASE self \in Nodes -> "Send"
                                        [] self = "timer" -> "NextRound"]

Send(self) == /\ pc[self] = "Send"
              /\ Msgs' = (        Msgs \union { [
                              round |-> CurrentRound,
                              sender |-> self,
                              received |-> {self}
                          ] })
              /\ pc' = [pc EXCEPT ![self] = "Receive"]
              /\ UNCHANGED << CurrentRound, localRound >>

Receive(self) == /\ pc[self] = "Receive"
                 /\ IF (localRound[self] = CurrentRound)
                       THEN /\ \E m \in { m \in Msgs : m.round <= CurrentRound /\ self \notin m.received }:
                                 Msgs' = ((Msgs \ {m}) \union
                                          { [m EXCEPT !.received = m.received \union {self}] })
                            /\ pc' = [pc EXCEPT ![self] = "Receive"]
                            /\ UNCHANGED localRound
                       ELSE /\ localRound' = [localRound EXCEPT ![self] = localRound[self] + 1]
                            /\ IF (localRound'[self] < NumRounds)
                                  THEN /\ pc' = [pc EXCEPT ![self] = "Send"]
                                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                            /\ Msgs' = Msgs
                 /\ UNCHANGED CurrentRound

n(self) == Send(self) \/ Receive(self)

NextRound == /\ pc["timer"] = "NextRound"
             /\ IF (CurrentRound < NumRounds)
                   THEN /\ (\A s \in Nodes : \E m \in Msgs : (m.round = CurrentRound) /\ (m.sender = s))
                        /\ IF (CurrentRound >= GlobalStabTime)
                              THEN /\ (\A m \in {m \in Msgs: m.round <= CurrentRound}: m.received = Nodes)
                              ELSE /\ TRUE
                        /\ CurrentRound' = CurrentRound + 1
                        /\ pc' = [pc EXCEPT !["timer"] = "NextRound"]
                   ELSE /\ pc' = [pc EXCEPT !["timer"] = "Done"]
                        /\ UNCHANGED CurrentRound
             /\ UNCHANGED << Msgs, localRound >>

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

TypeInvariant == \A m \in Msgs : m \in Messages /\ m.round <= CurrentRound

AllSendersInPastRounds == \A r \in 0..(CurrentRound - 1) : \A s \in Nodes :
        \E m \in Msgs : m.round = r /\ m.sender = s

AllPastMessageReceived == (CurrentRound > GlobalStabTime) => \A m \in {m \in Msgs : m.round < CurrentRound} : m.received = Nodes

MonoIncCurRound == [][CurrentRound' = CurrentRound + 1]_CurrentRound
LocalRoundCorrectness == [](\A r \in Nodes: localRound[r] = CurrentRound \/ localRound[r] = CurrentRound - 1)

PartialSynchrony == 
    \/ CurrentRound <= GlobalStabTime
    \/ \A m \in Msgs: m.round = CurrentRound \/ m.received = Nodes
Liveness == <>(CurrentRound = NumRounds) 
=============================================================================
\* Modification History
\* Last modified Thu Oct 20 15:13:00 SGT 2022 by kshehata
\* Created Thu Oct 20 14:55:45 SGT 2022 by kshehata
