------------------------ MODULE AbortableQueueLockCC ------------------------
(****************************************************************************
A TLA Description of Algorithm 1 in 
"Deterministic Constant-Amortized-RMR Abortable Mutex for CC and DSM"
by Prasad Jayanti and Siddhartha Jayanti (extension of PODC 2019 paper)

Pseudo-code of the algorithm is as follows:

DESCRIPTION:
    Amortized constant RMR abortable lock for CC machines. 
    Code shown for process $p$.
    Process $p$ can non-deterministically jump to the Abort Section if 
        the abort signal is on and $p$ is at Line T4 or T5.

VARIABLES:
    - a NODE is a single shared memory word that can hold a pointer, or "nil", or "token". 
    - TAIL: shared variable that points to a node.
            Initially, it points to a node that is allocated and initialized to "token".
            (We call this node the ANCHOR node.)

    When a process $p$ first participates in the algorithm: 
    - It allocates two local variables $mynode_p$ and $mypred_p$ both of which point to the 
        same freshly allocated node initialized to "nil".
    - It allocates an uninitialized local variable $v_p$ that can hold a pointer, "nil", or "token".    


ALGORITHM:
    Try(p):
       T1:  IF FAS( *mynode_p, "nil" ) != mypred_p THEN
       T2:      mypred_p <- FAS(TAIL, mynode_p)
       T3:  v_p <- FAS( *mypred_p, "nil" )
            IF v_p !in {"nil", "token"} THEN mypred_p <- v_p
            WHILE v_p != "token" DO
       T4:      IF (v_p <- *mypred_p) !in {"nil", "token"} THEN
       T5:          v_p <- FAS( *mypred_p, "nil" )
                    IF v_p !in {"nil", "token"} THEN mypred_p <- v_p

    Exit(p):
        E:  *mynode_p <- "token"
            mynode_p  <- mypred_p   

    Abort(p):
        A:  *mynode_p <- mypred_p  

  
  Note: We only number lines with a shared memory instruction. Local lines
        are executed right AFTER the corresponding shared memory line.  

TRANSLATION NOTES:
    - We notice that T5 is equivalent to T3, so we simply have 6 Lines in 
        our TLA code: {T1, T2, T3, T4, E, A}
    - The variable v_p is always used only on a single numbered line, thus
        it is unnecessary in a TLA state-machine description. We eliminate it
        and thus have VARIABLES: {TAIL, NODE, mynode, mypred, pc}
    - We model aborting as non-deterministic jumps of the program counter,
        i.e., after process p executes either T3 or T4, and its next line
        will be some T \in {T3, T4}, we simply enforce that its next pc value
        satisfied pc'[p] \in {T, A}. This is exactly how Jayanti and Jayanti
        model non-determinism in the proofs in the paper.

- MutualExclusion, TypeOK, and Distinct Nodes were model checked via TLC on
  5 (symmetric) processes. The execution:
        took 6 hours with 21,624,917 Distinct States (over 100M checked)
- AFCFS was checked with TLC on 3 processes. The execution:
        took 19 seconds with 85,320 Distinct States
- StarvationFreedom was checked with TLC on 3 processes. The execution:
        took 24 seconds with 85,320 Distinct States
****************************************************************************)

\* EXTENDS TLAPS

CONSTANTS PROCSET, ANCHOR

VARIABLES TAIL, NODE, mynode, mypred, pc
vars == <<TAIL, NODE, mynode, mypred, pc>>

Lines            == {"T1", "T2", "T3", "T4", "E", "A"}
RemainderSection == {"T1"}
TrySection       == {"T1", "T2", "T3", "T4"}
Doorway          == {"T1", "T2"}
WaitRoom         == {"T3", "T4"}
CriticalSection  == {"E"}
ExitSection      == {"E"}
AbortSection     == {"A"}

Nodeset == PROCSET \union {ANCHOR}
NodeContents == {"nil", "token"} \union Nodeset 

Init == /\ TAIL = ANCHOR
        /\ NODE \in [Nodeset -> {"nil", "token"}]   
        /\ \A p \in PROCSET: NODE[p] = "nil"
        /\ NODE[ANCHOR] = "token"
        /\ mynode = [p \in PROCSET |-> p]
        /\ mypred = [p \in PROCSET |-> p] 
        /\ pc = [p \in PROCSET |-> "T1"]          

ExecT1(p) == /\ pc[p] = "T1"
             /\ \/ /\ NODE[mynode[p]] # mypred[p]
                   /\ pc' = [pc EXCEPT ![p] = "T2"]  
                   /\ UNCHANGED <<TAIL, mynode, mypred>>
                \/ /\ NODE[mynode[p]] = mypred[p]
                   /\ pc' = [pc EXCEPT ![p] = "T3"]  
                   /\ UNCHANGED <<TAIL, mynode, mypred>>
             /\ NODE' = [NODE EXCEPT ![mynode[p]] = "nil"]
             

ExecT2(p) == /\ pc[p] = "T2"
             /\ TAIL' = mynode[p]
             /\ mypred' = [mypred EXCEPT ![p] = TAIL]
             /\ pc' = [pc EXCEPT ![p] = "T3"]
             /\ UNCHANGED <<NODE, mynode>>

ExecT3(p) == /\ pc[p] = "T3"
             /\ \/ /\ NODE[mypred[p]] = "nil"
                   /\ pc' \in [PROCSET -> Lines]
                   /\ \A q \in PROCSET: (q # p => pc'[q] = pc[q])
                   /\ pc'[p] \in {"T4", "A"}
                   /\ UNCHANGED mypred
                \/ /\ NODE[mypred[p]] = "token"
                   /\ pc' = [pc EXCEPT ![p] = "E"]
                   /\ UNCHANGED mypred
                \/ /\ NODE[mypred[p]] \notin {"nil", "token"}
                   /\ pc' \in [PROCSET -> Lines]
                   /\ \A q \in PROCSET: (q # p => pc'[q] = pc[q])
                   /\ pc'[p] \in {"T4", "A"}
                   /\ mypred' = [mypred EXCEPT ![p] = NODE[mypred[p]]]
             /\ NODE' = [NODE EXCEPT ![mypred[p]] = "nil"]
             /\ UNCHANGED <<TAIL, mynode>>
                
ExecT4(p) == /\ pc[p] = "T4"
             /\ \/ /\ NODE[mypred[p]] = "nil"
                   /\ pc' = [pc EXCEPT ![p] = "T4"]
                \/ /\ NODE[mypred[p]] = "token"
                   /\ pc' = [pc EXCEPT ![p] = "E"] 
                \/ /\ NODE[mypred[p]] \notin {"nil", "token"}
                   /\ pc' \in [PROCSET -> Lines]
                   /\ \A q \in PROCSET: (q # p => pc'[q] = pc[q])
                   /\ pc'[p] \in {"T3", "A"}
             /\ UNCHANGED <<TAIL, NODE, mynode, mypred>>

              
ExecE(p)  == /\ pc[p] = "E"
             /\ pc' = [pc EXCEPT ![p] = "T1"]
             /\ NODE' = [NODE EXCEPT ![mynode[p]] = "token"]
             /\ mynode' = [mynode EXCEPT ![p] = mypred[p]]
             /\ UNCHANGED <<TAIL, mypred>>

ExecA(p)  == /\ pc[p] = "A"
             /\ pc' = [pc EXCEPT ![p] = "T1"]
             /\ NODE' = [NODE EXCEPT ![mynode[p]] = mypred[p]]
             /\ UNCHANGED <<TAIL, mynode, mypred>>

ExecStep(p) == \/ ExecT1(p)
               \/ ExecT2(p)
               \/ ExecT3(p)
               \/ ExecT4(p)
               \/ ExecA(p)
               \/ ExecE(p)

Next == \E p \in PROCSET: ExecStep(p)


(* Specification *)
Spec     == Init /\ [][Next]_vars

LiveSpec == Spec /\ \A p \in PROCSET: WF_vars(ExecStep(p))



(* Safety Properties: check with TLC Model using Spec *)

\* INVARIANTS
ValidTAIL    == TAIL   \in Nodeset
ValidNODEs   == NODE   \in [Nodeset -> NodeContents]
ValidMyNodes == mynode \in [PROCSET -> Nodeset]
ValidMyPreds == mypred \in [PROCSET -> Nodeset]
ValidPCs     == pc     \in [PROCSET -> Lines]

TypeOK == /\ ValidTAIL
          /\ ValidNODEs
          /\ ValidMyNodes
          /\ ValidMyPreds
          /\ ValidPCs


Mutex == \A p, q \in PROCSET: ~ /\ p # q
                                /\ pc[p] = "E" 
                                /\ pc[q] = "E"
DistinctNodes == \A p, q \in PROCSET: (p # q) => (mynode[p] # mynode[q])

\* TEMPORAL PROPERTIES
ProcAFCFS(p, q) == [](
                      (
                       /\ [](pc[p] \in WaitRoom) 
                       /\ pc[q] \in RemainderSection 
                       /\ NODE[mynode[q]] \in {"nil", "token"}
                      ) 
                      => [](pc[q] \notin CriticalSection) 
                     ) 

AFCFS          == \A p, q \in PROCSET: ProcAFCFS(p, q)
    
                        
(* Liveness Properties: check with TLC Model using LiveSpec *)
ProcStarvationFreedom(p) == []((pc[p] \in TrySection /\ [] ~(pc[p] \in AbortSection))                                    
                                    ~> (pc[p] \in ExitSection))
StarvationFreedom        == \A p \in PROCSET: ProcStarvationFreedom(p) 


(* Attainable Configurations: TLC can find traces *)

InCS(p)    == pc[p] = "E"
InAbort(p) == pc[p] = "A"

ExistsInCS    == \E p \in PROCSET: InCS(p)
ExistsInAbort == \E p \in PROCSET: InAbort(p)

(*
We want a configuration in which the wait-queue has three nodes, a2, a1, a0:
    The tail node, a2. has nil,
    the middle node, a1, in the queue is aborted,
    the head node, a0, contains the token
*)
Config3queue == \E a0, a1, a2 \in Nodeset:
                    \E q1, q2 \in PROCSET:
                        /\ mynode[q1] = a1
                        /\ mynode[q2] = a2
                        
                        /\ TAIL = a2
                        /\ mypred[q2] = a1
                        /\ mypred[q1] = a0
                        
                        /\ NODE[a2] = "nil"
                        /\ NODE[a1] \notin {"nil", "token"}
                        /\ NODE[a0] = "token"

FalseLivelockFreedom == []<>ExistsInCS \*This is FALSE: because of thrashing due to Aborting

=============================================================================
\* Modification History
\* Last modified Mon Aug 08 14:03:56 BST 2022 by prasadjayanti
\* Created Tue Jan 19 12:56:09 EST 2021 by siddharthajayanti
