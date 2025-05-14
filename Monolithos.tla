----------------------------- MODULE Monolithos -----------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets


VARIABLES ioQueue, ioQueueSize,  currentTime, wRemaining, missedTotal

CONSTANT maxQueueSize, windowSize

(* contains only necessary arguments and not full IOECB info *)
IOECB ==
    [ wcet       : Nat,
      deadline   : Nat,
      priority   : Nat,
      completed  : BOOLEAN,
      submittedAt: Nat,
      missed : BOOLEAN (* added to check for missed deadlines, should have 0 missed *)
      ]


Init ==
    /\ ioQueue = <<>>
    /\ wRemaining = windowSize
    /\ ioQueueSize = 0
    /\ currentTime = 0
    /\ missedTotal = 0 (* if this changes model fails *)
 
(* used to increment time sim as well as update Service Window size *)
Tick ==
    /\ currentTime' = currentTime + 1
    /\ wRemaining' =
        IF wRemaining = 0
        THEN windowSize
        ELSE wRemaining - 1
    /\ UNCHANGED << ioQueue, ioQueueSize>>
    
DeterministicExecution ==
    \A i \in 1..Len(ioQueue) :
        LET task == ioQueue[i] IN
            (task \in [ wcet       : Nat,
                     deadline   : Nat,
                     priority   : Nat,
                     completed  : BOOLEAN,
                     submittedAt: Nat,
                     missed : BOOLEAN]) 
            =>
            (task.completed =>
                /\ task.wcet <= windowSize
                /\ task.deadline >= task.submittedAt
                /\ ~task.missed)
               

        
(* IOECBs can only be serviced during IO Service Window *)
WindowInvariant ==
  \A i \in 1..Len(ioQueue) :
    LET e == ioQueue[i] IN
      e.completed => e.wcet <= windowSize

(* didn't want to make a whole invariant for this but it makes it easier to see when it fails *)
NoDeadlineMisses ==
  missedTotal = 0
  
(* Only used during initial testing 
AllInvariants ==
  WindowInvariant /\ DeterministicExecution /\ NoDeadlineMisses
*)       



(* 
create empty IOECB abstracted down to basic attributes that the scheduler can handle.
While I didn't implement any actions,
it doesn't matter as the scheduler only needs a few of the attributes of the IOECB
This is because this model if to model behavior and not code execution
*)
SubmitIOECB ==
    (* I created a local IOECB and appended it to the queue to simulate  *)
    LET newECB ==
        [ wcet       |-> 2,
          deadline   |-> currentTime + 5,
          priority   |-> 1,
          completed  |-> FALSE,
          submittedAt|-> currentTime,
          missed     |-> FALSE
          ]
    IN
    /\ ioQueueSize < maxQueueSize
    /\ ioQueue' = Append(ioQueue, newECB)
    /\ ioQueueSize' = ioQueueSize + 1
    /\ UNCHANGED <<currentTime, wRemaining>>


(* Retrieves the index of the best task for ExecuteIOECB *)
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
      IF j = i THEN 
        [task EXCEPT 
          !.completed = TRUE,
          !.missed = currentTime + task.wcet > task.deadline] (* hopefully doesn't ever become true *)
      ELSE ioQueue[j]
    ] IN
    (* Had to create a new updatedTask var as task.missed would not be set to it's true value in the main list at this point *)
    (
        /\ ioQueue' = SelectSeq(ioQueueTemp, LAMBDA e: ~e.completed)
        /\ ioQueueSize' = Len(ioQueue')
        /\ wRemaining' = wRemaining - task.wcet
        /\ missedTotal' = missedTotal + IF ioQueueTemp[i].missed THEN 1 ELSE 0
        /\ UNCHANGED <<currentTime>>
    )
  ELSE
    UNCHANGED << ioQueue, ioQueueSize, wRemaining, currentTime, missedTotal >>


Next ==
    \/ Tick
    \/ SubmitIOECB 
    \/ ExecuteIOECB
    

    
Spec == Init /\ [][Next]_<<ioQueue, ioQueueSize, currentTime, wRemaining, missedTotal>>




=============================================================================
