------------------------------- MODULE messageDetails -------------------------------

EXTENDS Integers, TLC, TLAPS, FiniteSets

CONSTANTS Processors, Values, Default, MaxOperationsCount

VARIABLES messages,    \* The set of messages that have been sent.
          processorTimestamps,
          processorValues,
          lastTimestamp,
          lastOperationNumber

ASSUMPTION ValuesAssumption == Cardinality(Values) > 1
ASSUMPTION ProcessorsAssumption == Cardinality(Processors) > 1

vars == << messages, processorTimestamps, processorValues, lastTimestamp, lastOperationNumber >> 

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
    /\ lastOperationNumber = 1

SendReadReq(p, goal, u) ==
    LET newMessages == [sender: { p }, receiver: Processors \ { p }, type: {"read"}, u: { u }, goal: { goal }]
    IN 
        /\ messages' = messages \cup newMessages

SendWriteReq(p, v, t, u, goal) ==
    LET newMessages == 
        [sender: { p }, receiver: Processors \ { p }, type: {"write"}, v: { v }, t: { t }, u: { u }, goal: { goal }] 
    IN 
        /\ messages' = messages \cup newMessages


SendAckWReq(p, to, v, t, u, g) ==
    /\ messages' = messages \cup [sender: { p }, receiver: { to }, type: { "ackW" }, v: { v }, t: { t }, u: { u }, goal: { g }]
    /\ IF t > processorTimestamps[p] THEN 
        /\ processorTimestamps' = [processorTimestamps EXCEPT ![p] = t]
        /\ processorValues' = [processorValues EXCEPT ![p] = v]
        /\ UNCHANGED << lastTimestamp, lastOperationNumber >>
        ELSE 
        /\ UNCHANGED << processorTimestamps, processorValues, lastTimestamp, lastOperationNumber >>

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
            \* Not already sent
            /\ ~(\E d \in messages: 
                d.sender = p /\ d.type = "ackW" /\ d.u = m.u)
            /\ SendAckWReq(p, m.sender, m.v, m.t, m.u, m.goal)


AckReadReq ==
    /\ \E p \in Processors:
        /\ \E m \in messages:
            /\ m.receiver = p
            /\ m.type = "read"
            \* Not already sent
            /\ ~(\E d \in messages: 
                d.sender = p /\ d.type = "ackR" /\ d.u = m.u)
            /\ SendAckRReq(p, m.sender, processorValues[p], processorTimestamps[p], m.u, m.goal)

WriteReq1 ==
    /\ lastOperationNumber < MaxOperationsCount
    /\ \E p \in Processors:
        /\ SendReadReq(p, "write", lastOperationNumber + 1)
    /\ lastOperationNumber' = lastOperationNumber + 1
    /\ UNCHANGED << processorTimestamps, processorValues, lastTimestamp >>


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

                \* Not already sent for this operation
                /\ ~(\E m \in messages: m.sender = initiator /\ m.u = u /\ m.type = "write")

                /\ LET ts == { x.t: x \in ackMessages } IN 
                    LET newT == (CHOOSE t \in ts: \A tt \in ts: t >= tt) + 1 IN  
                        LET v == CHOOSE vv \in Values: TRUE IN 
                            /\ SendWriteReq(initiator, v, newT, u, "write")
                            /\ lastTimestamp' = IF newT > lastTimestamp THEN newT ELSE lastTimestamp
                            /\ processorTimestamps' = [processorTimestamps EXCEPT ![initiator] = newT]
                            /\ processorValues' = [processorValues EXCEPT ![initiator] = v]
                            /\ UNCHANGED << lastOperationNumber >>

ReadReq1 ==
    /\ lastOperationNumber < MaxOperationsCount
    /\ \E p \in Processors:
        /\ SendReadReq(p, "read", lastOperationNumber + 1)
    /\ lastOperationNumber' = lastOperationNumber + 1
    /\ UNCHANGED << processorTimestamps, processorValues, lastTimestamp >>

ReadReq2 ==
    /\ \E initiator \in Processors, u \in 0..lastOperationNumber:
        /\ LET ackMessages == { 
            ackM \in messages: 
                /\ ackM.receiver = initiator
                /\ ackM.type = "ackR"
                /\ ackM.u = u
                /\ ackM.goal = "read"
            } IN
                /\ \A p \in Processors \ { initiator }:
                    /\ \E m \in ackMessages:
                        /\ m.sender = p

                \* Not already sent for this operation
                /\ ~(\E m \in messages: m.sender = initiator /\ m.u = u /\ m.type = "write")

                /\ LET maxTMessage == CHOOSE x \in ackMessages : \A ackM \in ackMessages: x.t >= ackM.t IN 
                    /\ SendWriteReq(initiator, maxTMessage.v, maxTMessage.t, u, "read")
                    /\ lastTimestamp' = IF maxTMessage.t > lastTimestamp THEN maxTMessage.t ELSE lastTimestamp
                    /\ UNCHANGED << lastOperationNumber, processorTimestamps, processorValues >>

Next == 
    \/ WriteReq1
    \/ WriteReq2
    \/ ReadReq1
    \/ ReadReq2
    \/ AckWriteReq
    \/ AckReadReq

SendMessage(m) == messages' = messages \cup {m}


Spec == Init /\ [][Next]_vars 
             /\ WF_vars(AckWriteReq)
             /\ WF_vars(AckReadReq)

LastTimestampCorrect ==
    \A p \in Processors:
        processorTimestamps[p] <= lastTimestamp

NewerValuePropagates ==
    \A p1, p2 \in Processors:
        (processorTimestamps[p1] > processorTimestamps[p2]) ~> (processorTimestamps[p1] <= processorTimestamps[p2])

Read(reader) == 
    processorValues[reader]

Chosen(v) == 
    \/ \A p \in Processors:
        Read(p) = v 
    \/ v = Default


--------------------------------------------


chosenBar == {v \in Values : Chosen(v)}

MessageDetailed == INSTANCE messageAbstract WITH chosen <- chosenBar

Refinement == Spec => MessageDetailed!Spec

MessageDetailedSpec == MessageDetailed!Spec


--------------------------------------------

THEOREM SpecTypeOK == Spec => []TypeOK
    <1>1. Init => TypeOK 
        BY DEF Init, TypeOK
    <1>2. TypeOK /\ [Next]_vars => TypeOK'
        <2> SUFFICES ASSUME TypeOK, Next PROVE TypeOK' BY DEF TypeOK, vars
        <2>1. CASE WriteReq1 BY <2>1 DEF WriteReq1, TypeOK, MessagesType, SendReadReq
        <2>2. CASE WriteReq2 
            <3> SUFFICES ASSUME TypeOK, WriteReq2 PROVE messages' \in SUBSET MessagesType
                                    /\ processorTimestamps' \in [Processors -> Nat]
                                    /\ processorValues' \in [Processors -> Values \cup {Default}]
                                    /\ lastTimestamp' \in Nat
                                    /\ lastOperationNumber' \in Nat
            BY <2>2 DEF TypeOK, Next, vars
            <3>1. messages' \in SUBSET MessagesType PROOF BY <2>2 DEF TypeOK, Next, WriteReq2, SendWriteReq
            <3>2. processorTimestamps' \in [Processors -> Nat] PROOF BY <2>2 DEF TypeOK, Next, WriteReq2, SendWriteReq
            <3>3. processorValues' \in [Processors -> Values \cup {Default}] PROOF BY <2>2 DEF TypeOK, Next, WriteReq2, SendWriteReq
            <3>4. lastTimestamp' \in Nat PROOF BY <2>2 DEF TypeOK, Next, WriteReq2, SendWriteReq
            <3>5. lastOperationNumber' \in Nat PROOF BY <2>2 DEF TypeOK, Next, WriteReq2, SendWriteReq
            <3>q. QED BY <3>1, <3>2, <3>3, <3>4, <3>5
        <2>3. CASE ReadReq1 BY <2>3 DEF ReadReq1, TypeOK, MessagesType, SendReadReq
        <2>4. CASE ReadReq2 BY <2>4 DEF ReadReq2, TypeOK, MessagesType, SendWriteReq
        <2>5. CASE AckWriteReq BY <2>5 DEF AckWriteReq, TypeOK, MessagesType, SendAckWReq
        <2>6. CASE AckReadReq BY <2>6 DEF AckReadReq, TypeOK, MessagesType, SendAckRReq
        
        <2>q. QED BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF TypeOK, Next, WriteReq1, WriteReq2, ReadReq1, ReadReq2, AckWriteReq, AckReadReq        
        
    <1>q. QED BY <1>1, <1>2, PTL DEF Spec
    
(*
THEOREM SpecTypeOK == Spec => []TypeOK
    <1>1. Init => TypeOK 
        BY DEF Init, TypeOK
    <1>2. TypeOK /\ [Next]_vars => TypeOK'
        <2>a SUFFICES ASSUME TypeOK, Next PROVE TypeOK' BY DEF TypeOK, vars
        <2>1. CASE WriteReq1 BY <2>1 DEF WriteReq1, TypeOK, MessagesType, SendReadReq
        <2>2. CASE WriteReq2 
            <3>a SUFFICES ASSUME TypeOK, WriteReq2 PROVE messages' \in SUBSET MessagesType
                                    /\ processorTimestamps' \in [Processors -> Nat]
                                    /\ processorValues' \in [Processors -> Values \cup {Default}]
                                    /\ lastTimestamp' \in Nat
                                    /\ lastOperationNumber' \in Nat
            BY <2>2 DEF TypeOK, Next, vars
            <3>1. messages' \in SUBSET MessagesType PROOF BY <2>2, <3>a DEF Next, WriteReq2, MessagesType
            <3>2. processorTimestamps' \in [Processors -> Nat] PROOF BY <2>2, <3>a DEF Next, WriteReq2
            <3>3. processorValues' \in [Processors -> Values \cup {Default}] PROOF BY <3>a DEF Next, WriteReq2
            <3>4. lastTimestamp' \in Nat PROOF BY <2>2, <3>a DEF Next, WriteReq2
            <3>5. lastOperationNumber' \in Nat PROOF BY <2>2, <3>a DEF Next, WriteReq2
            <3>q. QED BY <3>1, <3>2, <3>3, <3>4, <3>5
        <2>3. CASE ReadReq1 BY <2>3 DEF ReadReq1, TypeOK, MessagesType, SendReadReq
        <2>4. CASE ReadReq2 BY <2>4 DEF ReadReq2, TypeOK, MessagesType, SendWriteReq
        <2>5. CASE AckWriteReq BY <2>5 DEF AckWriteReq, TypeOK, MessagesType, SendAckWReq
        <2>6. CASE AckReadReq BY <2>6 DEF AckReadReq, TypeOK, MessagesType, SendAckRReq
        
        <2>q. QED BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF TypeOK, Next, WriteReq1, WriteReq2, ReadReq1, ReadReq2, AckWriteReq, AckReadReq        
        
    <1>q. QED BY <1>1, <1>2, PTL DEF Spec


*)

    
(*THEOREM SpecTypeOK == Spec => []TypeOK
    <1>1. Init => TypeOK 
        BY DEF Init, TypeOK
    <1>2. TypeOK /\ [Next]_vars => TypeOK'
        <2> SUFFICES ASSUME TypeOK, Next PROVE TypeOK' BY DEF TypeOK, vars
        <2>1. CASE WriteReq1 BY <2>1 DEF WriteReq1, TypeOK, MessagesType, SendReadReq
        <2>2. CASE WriteReq2 BY <2>2, ValuesAssumption DEF WriteReq2, TypeOK, MessagesType, SendWriteReq
        <2>3. CASE ReadReq1 BY <2>3 DEF ReadReq1, TypeOK, MessagesType, SendReadReq
        <2>4. CASE ReadReq2 BY <2>4 DEF ReadReq2, TypeOK, MessagesType, SendWriteReq
        <2>5. CASE AckWriteReq BY <2>5 DEF AckWriteReq, TypeOK, MessagesType, SendAckWReq
        <2>6. CASE AckReadReq BY <2>6 DEF AckReadReq, TypeOK, MessagesType, SendAckRReq
        
        <2>q. QED BY DEF TypeOK, Next, WriteReq1, WriteReq2, ReadReq1, ReadReq2, AckWriteReq, AckReadReq                
    <1>q. QED *)


==============================================================================