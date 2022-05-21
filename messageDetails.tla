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
    [sender: Processors, receiver: Processors, type: {"read"}, u: Nat, goal: {"read", "write"},] \cup 
    [sender: Processors, receiver: Processors, type: {"write"}, v: Values \cup { Default }, t: Nat, u: Nat, goal: {"read", "write"}] \cup 
    [sender: Processors, receiver: Processors, type: {"ackW"}, v: Values \cup { Default }, t: Nat, u: Nat] \cup        
    [sender: Processors, receiver: Processors, type: {"ackR"}, v: Values \cup { Default }, t: Nat, u: Nat]            

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

SendWriteReq(p, v) ==
    LET newMessages == 
        [sender: { p }, receiver: Processors \ { p }, type: {"write"}, v: { v }, t: {lastTimestamp + 1}, u: { lastOperationNumber }] 
    IN 
        /\ lastTimestamp' = lastTimestamp + 1
        /\ lastOperationNumber' = lastOperationNumber + 1
        /\ processorTimestamps' = [processorTimestamps EXCEPT ![p] = lastTimestamp + 1]
        /\ processorValues' = [processorValues EXCEPT ![p] = v]
        /\ messages' = messages \cup newMessages
        /\ UNCHANGED << >>

WriteReq ==
    /\ lastOperationNumber < MaxOperationsCount
    /\ \E v \in Values, p \in Processors:
        SendWriteReq(p, v)

SendAckWReq(p, to, v, t, u) ==
    /\ messages' = messages \cup [sender: { p }, receiver: { to }, type: { "ackW" }, v: { v }, t: { t }, u: { u }]
    /\ processorTimestamps' = [processorTimestamps EXCEPT ![p] = t]
    /\ processorValues' = [processorValues EXCEPT ![p] = v]
    /\ UNCHANGED << lastTimestamp, lastOperationNumber >>

AckWriteReq ==
    /\ \E p \in Processors:
        /\ \E m \in messages:
            /\ m.receiver = p
            /\ m.type = "write"
            /\ m.t > processorTimestamps[p]

            /\ SendAckWReq(p, m.sender, m.v, m.t, m.u)

SendReadReq(p) ==
    LET newMessages == [sender: { p }, receiver: Processors \ { p }, type: {"read"}, u: { lastOperationNumber + 1 }]
    IN 
        /\ messages' = messages \cup newMessages
        /\ lastOperationNumber' = lastOperationNumber + 1
        /\ UNCHANGED << processorTimestamps, processorValues, lastTimestamp >>

ReadReq ==
    /\ lastOperationNumber < MaxOperationsCount
    /\ \E p \in Processors:
        SendReadReq(p)

SendAckRReq(p, to, v, t, u) ==
    /\ messages' = messages \cup [sender: { p }, receiver: { to }, type: { "ackR" }, v: { v }, t: { t }, u: { u }]
    /\ processorTimestamps' = [processorTimestamps EXCEPT ![p] = t]
    /\ processorValues' = [processorValues EXCEPT ![p] = v]
    /\ UNCHANGED << lastTimestamp, lastOperationNumber >>

AckReadReq ==
    /\ \E p \in Processors:
        /\ \E m \in messages:
            /\ m.receiver = p
            /\ m.type = "read"
            \* Not already sent
            /\ ~(\E d \in messages: 
                d.sender = p /\ d.type = m.type /\ d.u = m.u)

            /\ SendAckRReq(p, m.sender, processorValues[p], processorTimestamps[p], m.u)

\* TODO: read message, ackRead, chosen impl

Next == 
    \/ WriteReq
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