------------------------------- MODULE messageDetails -------------------------------

EXTENDS Integers

CONSTANTS Processors, Values, Default, MaxOperationsCount

VARIABLES messages,    \* The set of messages that have been sent.
          processorTimestamps,
          processorValues,
          lastTimestamp,
          lastOperationNumber

vars == << messages, processorTimestamps, processorValues, lastTimestamp, lastOperationNumber >> 

\* https://github.com/tlaplus/DrTLAPlus/blob/master/Paxos/Paxos.tla

MessagesType == 
    [sender: Processors, receiver: Processors, type: {"read"}, u: Nat, goal: {"read", "write"}] \cup 
    [sender: Processors, receiver: Processors, type: {"write"}, v: Values \cup { Default }, t: Nat, u: Nat, goal: {"read", "write"}] \cup 
    [sender: Processors, receiver: Processors, type: {"ackW"}, v: Values \cup { Default }, t: Nat, u: Nat, goal: {"read", "write"}] \cup        
    [sender: Processors, receiver: Processors, type: {"ackR"}, v: Values \cup { Default }, t: Nat, u: Nat, goal: {"read", "write"}]            

TypeOK == 
    /\ messages \in SUBSET MessagesType
    /\ processorTimestamps \in [Processors -> Nat]
    /\ processorValues \in [Processors -> Values \cup {Default}]
    /\ lastTimestamp \in Nat
    /\ lastOperationNumber \in Nat

Init == 
    /\ messages = {}
    /\ processorTimestamps = [p \in Processors |-> 0]
    /\ processorValues = [p \in Processors |-> Default]
    /\ lastTimestamp = 0
    /\ lastOperationNumber = 0

\* TODO: "finish Read" op?
Read(reader) == 
    CHOOSE v \in Values \cup { Default }:
        \/ \A p \in Processors \ { reader }:
            /\ \E m \in messages:
                /\ m.sender = p 
                /\ m.receiver = reader
                /\ m.type = "ackW"
                /\ m.t = lastTimestamp
                /\ m.v = v
        \/ v = Default

SendReadReq(p, goal) ==
    LET newMessages == [sender: { p }, receiver: Processors \ { p }, type: {"read"}, u: { lastOperationNumber + 1 }, goal: { goal }]
    IN 
        /\ messages' = messages \cup newMessages
        /\ lastOperationNumber' = lastOperationNumber + 1
        /\ UNCHANGED << processorTimestamps, processorValues, lastTimestamp >>

SendWriteReq(p, v, t, u, goal) ==
    LET newMessages == 
        [sender: { p }, receiver: Processors \ { p }, type: {"write"}, v: { v }, t: { t }, u: { u }, goal: { goal }] 
    IN 
        /\ lastTimestamp' = IF t > lastTimestamp THEN t ELSE lastTimestamp
        /\ processorTimestamps' = [processorTimestamps EXCEPT ![p] = t]
        /\ processorValues' = [processorValues EXCEPT ![p] = v]
        /\ messages' = messages \cup newMessages
        /\ UNCHANGED << lastOperationNumber >>


SendAckWReq(p, to, v, t, u, g) ==
    /\ messages' = messages \cup [sender: { p }, receiver: { to }, type: { "ackW" }, v: { v }, t: { t }, u: { u }, goal: { g }]
    /\ processorTimestamps' = [processorTimestamps EXCEPT ![p] = t]
    /\ processorValues' = [processorValues EXCEPT ![p] = v]
    /\ UNCHANGED << lastTimestamp, lastOperationNumber >>

SendAckRReq(p, to, v, t, u, g) ==
    /\ messages' = messages \cup [sender: { p }, receiver: { to }, type: { "ackR" }, v: { v }, t: { t }, u: { u }, goal: { g }]
    /\ processorTimestamps' = [processorTimestamps EXCEPT ![p] = t]
    /\ processorValues' = [processorValues EXCEPT ![p] = v]
    /\ UNCHANGED << lastTimestamp, lastOperationNumber >>


AckWriteReq ==
    /\ \E p \in Processors:
        /\ \E m \in messages:
            /\ m.receiver = p
            /\ m.type = "write"
            /\ m.t > processorTimestamps[p]

            /\ SendAckWReq(p, m.sender, m.v, m.t, m.u, m.goal)


AckReadReq ==
    /\ \E p \in Processors:
        /\ \E m \in messages:
            /\ m.receiver = p
            /\ m.type = "read"
            \* Not already sent
            /\ ~(\E d \in messages: 
                d.sender = p /\ d.type = m.type /\ d.u = m.u)

            /\ SendAckRReq(p, m.sender, processorValues[p], processorTimestamps[p], m.u, m.goal)

\* TODO: read message, ackRead, chosen impl

WriteReq1 ==
    /\ lastOperationNumber < MaxOperationsCount
    /\ \E v \in Values, p \in Processors:
        SendReadReq(p, "write")

WriteReq2 ==
    /\ \E initiator \in Processors, u \in 0..lastOperationNumber:
        /\ LET ackMessages == { 
            ackM \in messages: 
                /\ ackM.receiver = initiator
                /\ ackM.type = "ackR"
                /\ ackM.u = u
                /\ ackM.goal = "write"
            } IN
            /\ \A p \in Processors \ { initiator }:
                /\ \E m \in ackMessages:
                    /\ m.sender = p

            \* Not already sent 
            /\ ~\E m \in messages: m.sender = initiator /\ m.u = u /\ m.type = "write"

            /\ LET ts == { x.t: x \in ackMessages } IN 
                LET newT == (CHOOSE t \in ts: \A tt \in ts: t >= tt) + 1 IN 
                    LET v == CHOOSE vv \in Values: TRUE IN 
                        /\ SendWriteReq(initiator, v, newT, u, "write")


ReadReq ==
    /\ lastOperationNumber < MaxOperationsCount
    /\ \E p \in Processors:
        SendReadReq(p, "read")

Next == 
    \/ WriteReq1
    \/ WriteReq2
    \/ AckWriteReq
    \/ ReadReq
    \/ AckReadReq

SendMessage(m) == messages' = messages \cup {m}

Chosen(v) == 
    \/ \A p \in Processors:
        Read(p) = v 
    \/ v = Default

    
    
    \* Chosen(v) == 
\*     \A p \in Processors:
\*         \E m \in messages:


Spec == Init /\ [][Next]_vars 

------------------------------------------------------------------------------

chosenBar == {v \in Values : Chosen(v)}

MessageDetailed == INSTANCE messageAbstract WITH chosen <- chosenBar

THEOREM Refinement == Spec => MessageDetailed!Spec


==============================================================================