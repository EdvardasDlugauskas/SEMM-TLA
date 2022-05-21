------------------------------- MODULE messageDetails -------------------------------

EXTENDS Integers

CONSTANTS Processors, Values, Default, MaxOperationsCount

VARIABLES messages,    \* The set of messages that have been sent.
          processorTimestamps,
          processorValues,
          lastOperationNumber,
          lastNonce

vars == << messages, processorTimestamps, processorValues, lastOperationNumber, lastNonce >> 

\* https://github.com/tlaplus/DrTLAPlus/blob/master/Paxos/Paxos.tla

MessagesType == 
    [sender: Processors, receiver: Processors, type: {"read"}, u: Nat] \cup 
    [sender: Processors, receiver: Processors, type: {"write"}, v: Values \cup { Default }, t: Nat] \cup 
    [sender: Processors, receiver: Processors, type: {"ack"}, v: Values \cup { Default }, t: Nat]            

TypeOK == 
    /\ messages \in SUBSET MessagesType
    /\ processorTimestamps \in [Processors -> Nat]
    /\ lastOperationNumber \in Nat
    /\ lastNonce \in Nat
    /\ processorValues \in [Processors -> Values \cup {Default}]

Init == 
    /\ messages = {}
    /\ processorTimestamps = [p \in Processors |-> 0]
    /\ processorValues = [p \in Processors |-> Default]
    /\ lastOperationNumber = 0
    /\ lastNonce = 0

Read == 
    CHOOSE v \in Values \cup { Default }:
        \A p \in Processors:
            /\ \E m \in messages:
                /\ m.p = p
                /\ m.type = "ack"
                /\ m.t = lastOperationNumber
                /\ m.v = v
        \/ v = Default

Write ==
    /\ lastOperationNumber < MaxOperationsCount
    /\ \E v \in Values, p \in Processors:
    \* TODO: get T from readBeforeWrite
        LET newMessages == [sender: { p }, receiver: Processors \ { p }, type: {"write"}, v: { v }, t: {lastOperationNumber + 1}] 
        IN 
            /\ lastOperationNumber' = lastOperationNumber + 1
            /\ processorTimestamps' = [processorTimestamps EXCEPT ![p] = lastOperationNumber + 1]
            /\ processorValues' = [processorValues EXCEPT ![p] = v]
            /\ messages' = messages \cup newMessages
            /\ UNCHANGED << lastNonce >>

AckWrite ==
    /\ \E p \in Processors:
        /\ \E m \in messages:
            /\ m.receiver = p
            /\ m.t > processorTimestamps[p]
            /\ m.type = "write"

            /\ processorTimestamps' = [processorTimestamps EXCEPT ![p] = m.t]
            /\ processorValues' = [processorValues EXCEPT ![p] = m.v]
            /\ messages' = messages \cup [sender: { p }, receiver: { m.sender }, type: { "ack" }, v: { m.v }, t: { m.t }]

            /\ UNCHANGED << lastOperationNumber, lastNonce >>

\* TODO: read message, ackRead, chosen impl

Next == 
    \/ Write
    \/ AckWrite

SendMessage(m) == messages' = messages \cup {m}

Chosen(v) == v = v 
\* Chosen(v) == 
\*     \A p \in Processors:
\*         \E m \in messages:


Spec == Init /\ [][Next]_vars 

------------------------------------------------------------------------------

chosenBar == {v \in Values : Chosen(v)}

MessageDetailed == INSTANCE messageAbstract WITH chosen <- chosenBar

THEOREM Refinement == Spec => MessageDetailed!Spec


==============================================================================