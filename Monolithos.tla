(* Problems for future work: 
    Current model does not check for IOECBs that can stay idle inside the queue and thus expire and miss their deadline
            (I will later add a misses sweeping function to solve this)
            (this will probably require a clean sweeping function as well)
    wcet is consumed at execution which means the model can not model parital-completion
    I will also eventually randomize the the submission process for better load testing
    
*)

----------------------------- MODULE Monolithos -----------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets


VARIABLES ioQueue, ioQueueSize,  currentTime, wRemaining, missedTotal, executedTotal

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
    /\ executedTotal = 0
 
(* used to increment time sim as well as update Service Window size *)
Tick ==
    /\ currentTime' = currentTime + 1
    /\ wRemaining' =
        IF wRemaining = 0
        THEN windowSize
        ELSE wRemaining - 1
    /\ UNCHANGED << ioQueue, ioQueueSize, missedTotal, executedTotal>>
    
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
    (*/\ currentTime % 2 = 0  submission of IOECBs was overpowering execution of them this cuts the submissions in half*)
    /\ UNCHANGED <<currentTime, wRemaining, missedTotal, executedTotal>>

ValidTasks ==
  { i \in 1..Len(ioQueue) :
      LET task == ioQueue[i] IN
        /\ ~task.completed
        /\ task.wcet <= wRemaining
        /\ currentTime + task.wcet <= task.deadline
}
(* I had to add this O(n^2) function here to fix the RetrieveIOECB error when CHOOSE from the indicies list trys to scan an empty list *)
BestTasks ==
  { i \in ValidTasks :
      LET task == ioQueue[i] IN
        \A j \in ValidTasks :
          LET oTask == ioQueue[j] IN
            (task.priority < oTask.priority \/
             (task.priority = oTask.priority /\ task.deadline < oTask.deadline) \/
             (task.priority = oTask.priority /\ task.deadline = oTask.deadline /\ task.submittedAt <= oTask.submittedAt)) }


(* Retrieves the index of the best task for ExecuteIOECB *)
RetrieveIOECB ==
  IF BestTasks # {} THEN
    CHOOSE i \in BestTasks : TRUE
  ELSE 0
  
  
ExecuteIOECB ==
   IF ValidTasks # {} THEN
    LET i == RetrieveIOECB IN
    LET task == ioQueue[i] IN
    LET ioQueueTemp == [j \in 1..Len(ioQueue) |->
      IF j = i THEN 
        [task EXCEPT 
          !.completed = TRUE,
          !.missed = currentTime + task.wcet > task.deadline] (* hopefully doesn't ever become true *)
      ELSE ioQueue[j]
    ] IN
    (
        /\ ioQueue' = SelectSeq(ioQueueTemp, LAMBDA e: ~e.completed)
        /\ ioQueueSize' = Len(ioQueue')
        /\ wRemaining' = wRemaining - task.wcet
        /\ missedTotal' = missedTotal + IF ioQueueTemp[i].missed THEN 1 ELSE 0
        /\ executedTotal' = executedTotal + 1
        /\ UNCHANGED <<currentTime>>
    )
    
  ELSE
    UNCHANGED << ioQueue, ioQueueSize, wRemaining, currentTime, missedTotal, executedTotal >>


Next ==
    \/ Tick
    \/ SubmitIOECB 
    \/ ExecuteIOECB
    

    
Spec == Init /\ [][Next]_<<ioQueue, ioQueueSize, currentTime, wRemaining, missedTotal, executedTotal>>




=============================================================================
