----------------------------- MODULE Monolithos -----------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets


VARIABLES ioQueue, ioQueueSize,  currentTime, wRemaining

CONSTANT maxQueueSize, windowSize

IOECB ==
    [ wcet       : Nat,
      deadline   : Nat,
      priority   : Nat,
      completed  : BOOLEAN,
      submittedAt: Nat ]


Init ==
    /\ ioQueue = <<>>
    /\ wRemaining = windowSize
    /\ ioQueueSize = 0
    /\ currentTime = 0
 
Tick ==
    /\ currentTime' = currentTime + 1
    /\ wRemaining' =
        IF wRemaining = 0
        THEN windowSize
        ELSE wRemaining - 1
    /\ UNCHANGED << ioQueue, ioQueueSize>>
    
DeterministicExecution ==
    \A i \in 1..Len(ioQueue) :
        LET e == ioQueue[i] IN
            (e \in [ wcet       : Nat,
                     deadline   : Nat,
                     priority   : Nat,
                     completed  : BOOLEAN,
                     submittedAt: Nat ]) 
            =>
            (e.completed =>
                /\ e.wcet <= windowSize
                /\ e.deadline >= e.submittedAt)
               
ExecutedOnceInvariant ==
  \A i \in 1..Len(ioQueue) :
    LET e == ioQueue[i] IN
      e.completed =>
        Cardinality({
          j \in 1..Len(ioQueue) :
            LET ej == ioQueue[j] IN
              <<ej.submittedAt, ej.deadline, ej.priority>> = <<e.submittedAt, e.deadline, e.priority>>
        }) = 1
        
WindowInvariant ==
  \A i \in 1..Len(ioQueue) :
    LET e == ioQueue[i] IN
      e.completed => e.wcet <= windowSize

AllInvariants ==
  WindowInvariant /\ ExecutedOnceInvariant /\ DeterministicExecution
         
FilterUncompleted(seq) ==
  SelectSeq(seq, LAMBDA e: ~e.completed)

SubmitIOECB ==
    LET newECB ==
        [ wcet       |-> 2,
          deadline   |-> currentTime + 5,
          priority   |-> 1,
          completed  |-> FALSE,
          submittedAt|-> currentTime ]
    IN
    /\ ioQueueSize < maxQueueSize
    /\ ioQueue' = Append(ioQueue, newECB)
    /\ ioQueueSize' = ioQueueSize + 1
    /\ UNCHANGED <<currentTime, wRemaining>>

(* Retrieves the Best IOECB currently in queue during Service Window *)
RetrieveIOECB ==
    CHOOSE i \in 1..Len(ioQueue):
        LET task == ioQueue[i] IN
            /\ ~task.completed
            /\ task.wcet <= wRemaining
            /\ \A j \in 1..Len(ioQueue) :
                LET oTask == ioQueue[j] IN
                    (~oTask.completed /\ oTask.wcet <= wRemaining) =>
                        (task.priority < oTask.priority \/
                        (task.priority = oTask.priority /\ task.deadline < oTask.deadline) \/
                        (task.priority = oTask.priority /\ task.deadline = oTask.deadline /\ task.submittedAt <= oTask.submittedAt))
            
ExecuteIOECB ==
  IF \E i \in 1..Len(ioQueue) :
       LET e == ioQueue[i] IN
         /\ ~e.completed
         /\ e.wcet <= wRemaining
  THEN
    LET i == RetrieveIOECB IN
    LET task == ioQueue[i] IN
    LET ioQueueTemp == [j \in 1..Len(ioQueue) |->
                          IF j = i THEN [task EXCEPT !.completed = TRUE] ELSE ioQueue[j]] IN
    (
      /\ ioQueue' = FilterUncompleted(ioQueueTemp)
      /\ ioQueueSize' = Len(ioQueue')
      /\ wRemaining' = wRemaining - task.wcet
      /\ UNCHANGED <<currentTime>>
    )
  ELSE
    UNCHANGED << ioQueue, ioQueueSize, wRemaining, currentTime >>
    


Next ==
    \/ Tick
    \/ SubmitIOECB 
    \/ ExecuteIOECB
    

    
Spec == Init /\ [][Next]_<<ioQueue, ioQueueSize, currentTime, wRemaining>>



=============================================================================