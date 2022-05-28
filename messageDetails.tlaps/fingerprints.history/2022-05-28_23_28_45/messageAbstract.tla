------------------------------- MODULE messageAbstract -------------------------------

CONSTANTS Values, Default

VARIABLE chosen

vars == << chosen >> 

Init == chosen = { Default }

Read == chosen 
Write == 
    \E v \in Values:
        chosen' = { v } 
        
Next == 
    /\ Write 
    /\ Read = chosen 

Spec == Init /\ [][Next]_vars 

==============================================================================