------------------------------- MODULE Alloc2 -------------------------------
EXTENDS Naturals, TLC, Sequences, FiniteSets,TLAPS
CONSTANT Null,
        P, \* processes
        M  \* available blocks


(*****************************************************************
--fair algorithm Alloc2 {
    variable mem = [ head |-> M,
                     next |-> [i \in 1..M |-> IF i > 1 THEN i-1 ELSE Null ] ];

    macro DoCAS(result, addr, new, old) {
      if (addr = old) {
        addr := new;
        result := old;
      } else {
        result := new;
      }
    }

    procedure DoAlloc()
      variables keepNext = Null, resDA = Null, daCasRes = Null;
    {
      da1: resDA := mem.head;
      da2: while(resDA /= Null) {
        da3: keepNext := mem.next[resDA];
        da4: DoCAS(daCasRes, mem.head, keepNext, resDA);
             if(daCasRes = resDA) {
        da5:    ptr := resDA;
                return;
             };
        da6: resDA := mem.head;
             daCasRes := Null;
          };
      da7: return ;
    }

    procedure Enqueue(k)
      variables prevHead = Null, casRes = Null;
    {
      e1: while(TRUE) {
        e2: prevHead := mem[k];
            casRes := Null;
        e3: mem.next[ptr] := prevHead;
        e4: DoCAS(casRes, mem[k], ptr, prevHead);
            if (casRes = prevHead) {
                ptr := Null;
        e5:     return ;
             }
        }
    }

    procedure Alloc() {
      a1: call DoAlloc();
      a2: return;
    }

    procedure Free() {
      f1: call Enqueue("head");
      f2: return ;
    }

    process (Proc \in 1..P)
      variables ptr = Null;
    {
      p1: while(TRUE) {
        p2: call Alloc();
        p3: if(ptr /= Null) {
               call Free();
            };
      }
    }

}
*****************************************************************)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES mem, pc, stack, keepNext, resDA, daCasRes, k, prevHead, casRes, ptr

vars == << mem, pc, stack, keepNext, resDA, daCasRes, k, prevHead, casRes,
           ptr >>

ProcSet == (1..P)

Init == (* Global variables *)
        /\ mem = [ head |-> M,
                   next |-> [i \in 1..M |-> IF i > 1 THEN i-1 ELSE Null ] ]
        (* Procedure DoAlloc *)
        /\ keepNext = [ self \in ProcSet |-> Null]
        /\ resDA = [ self \in ProcSet |-> Null]
        /\ daCasRes = [ self \in ProcSet |-> Null]
        (* Procedure Enqueue *)
        /\ k = [ self \in ProcSet |-> defaultInitValue]
        /\ prevHead = [ self \in ProcSet |-> Null]
        /\ casRes = [ self \in ProcSet |-> Null]
        (* Process Proc *)
        /\ ptr = [self \in 1..P |-> Null]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "p1"]

da1(self) == /\ pc[self] = "da1"
             /\ resDA' = [resDA EXCEPT ![self] = mem.head]
             /\ pc' = [pc EXCEPT ![self] = "da2"]
             /\ UNCHANGED << mem, stack, keepNext, daCasRes, k, prevHead,
                             casRes, ptr >>

da2(self) == /\ pc[self] = "da2"
             /\ IF resDA[self] /= Null
                   THEN /\ pc' = [pc EXCEPT ![self] = "da3"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "da7"]
             /\ UNCHANGED << mem, stack, keepNext, resDA, daCasRes, k,
                             prevHead, casRes, ptr >>

da3(self) == /\ pc[self] = "da3"
             /\ keepNext' = [keepNext EXCEPT ![self] = mem.next[resDA[self]]]
             /\ pc' = [pc EXCEPT ![self] = "da4"]
             /\ UNCHANGED << mem, stack, resDA, daCasRes, k, prevHead, casRes,
                             ptr >>

da4(self) == /\ pc[self] = "da4"
             /\ IF (mem.head) = resDA[self]
                   THEN /\ mem' = [mem EXCEPT !.head = keepNext[self]]
                        /\ daCasRes' = [daCasRes EXCEPT ![self] = resDA[self]]
                   ELSE /\ daCasRes' = [daCasRes EXCEPT ![self] = keepNext[self]]
                        /\ mem' = mem
             /\ IF daCasRes'[self] = resDA[self]
                   THEN /\ pc' = [pc EXCEPT ![self] = "da5"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "da6"]
             /\ UNCHANGED << stack, keepNext, resDA, k, prevHead, casRes, ptr >>

da5(self) == /\ pc[self] = "da5"
             /\ ptr' = [ptr EXCEPT ![self] = resDA[self]]
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ keepNext' = [keepNext EXCEPT ![self] = Head(stack[self]).keepNext]
             /\ resDA' = [resDA EXCEPT ![self] = Head(stack[self]).resDA]
             /\ daCasRes' = [daCasRes EXCEPT ![self] = Head(stack[self]).daCasRes]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << mem, k, prevHead, casRes >>

da6(self) == /\ pc[self] = "da6"
             /\ resDA' = [resDA EXCEPT ![self] = mem.head]
             /\ daCasRes' = [daCasRes EXCEPT ![self] = Null]
             /\ pc' = [pc EXCEPT ![self] = "da2"]
             /\ UNCHANGED << mem, stack, keepNext, k, prevHead, casRes, ptr >>

da7(self) == /\ pc[self] = "da7"
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ keepNext' = [keepNext EXCEPT ![self] = Head(stack[self]).keepNext]
             /\ resDA' = [resDA EXCEPT ![self] = Head(stack[self]).resDA]
             /\ daCasRes' = [daCasRes EXCEPT ![self] = Head(stack[self]).daCasRes]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << mem, k, prevHead, casRes, ptr >>

DoAlloc(self) == da1(self) \/ da2(self) \/ da3(self) \/ da4(self)
                    \/ da5(self) \/ da6(self) \/ da7(self)

e1(self) == /\ pc[self] = "e1"
            /\ pc' = [pc EXCEPT ![self] = "e2"]
            /\ UNCHANGED << mem, stack, keepNext, resDA, daCasRes, k, prevHead,
                            casRes, ptr >>

e2(self) == /\ pc[self] = "e2"
            /\ prevHead' = [prevHead EXCEPT ![self] = mem[k[self]]]
            /\ casRes' = [casRes EXCEPT ![self] = Null]
            /\ pc' = [pc EXCEPT ![self] = "e3"]
            /\ UNCHANGED << mem, stack, keepNext, resDA, daCasRes, k, ptr >>

e3(self) == /\ pc[self] = "e3"
            /\ mem' = [mem EXCEPT !.next[ptr[self]] = prevHead[self]]
            /\ pc' = [pc EXCEPT ![self] = "e4"]
            /\ UNCHANGED << stack, keepNext, resDA, daCasRes, k, prevHead,
                            casRes, ptr >>

e4(self) == /\ pc[self] = "e4"
            /\ IF (mem[k[self]]) = prevHead[self]
                  THEN /\ mem' = [mem EXCEPT ![k[self]] = ptr[self]]
                       /\ casRes' = [casRes EXCEPT ![self] = prevHead[self]]
                  ELSE /\ casRes' = [casRes EXCEPT ![self] = ptr[self]]
                       /\ mem' = mem
            /\ IF casRes'[self] = prevHead[self]
                  THEN /\ ptr' = [ptr EXCEPT ![self] = Null]
                       /\ pc' = [pc EXCEPT ![self] = "e5"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "e1"]
                       /\ ptr' = ptr
            /\ UNCHANGED << stack, keepNext, resDA, daCasRes, k, prevHead >>

e5(self) == /\ pc[self] = "e5"
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ prevHead' = [prevHead EXCEPT ![self] = Head(stack[self]).prevHead]
            /\ casRes' = [casRes EXCEPT ![self] = Head(stack[self]).casRes]
            /\ k' = [k EXCEPT ![self] = Head(stack[self]).k]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << mem, keepNext, resDA, daCasRes, ptr >>

Enqueue(self) == e1(self) \/ e2(self) \/ e3(self) \/ e4(self) \/ e5(self)

a1(self) == /\ pc[self] = "a1"
            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "DoAlloc",
                                                     pc        |->  "a2",
                                                     keepNext  |->  keepNext[self],
                                                     resDA     |->  resDA[self],
                                                     daCasRes  |->  daCasRes[self] ] >>
                                                 \o stack[self]]
            /\ keepNext' = [keepNext EXCEPT ![self] = Null]
            /\ resDA' = [resDA EXCEPT ![self] = Null]
            /\ daCasRes' = [daCasRes EXCEPT ![self] = Null]
            /\ pc' = [pc EXCEPT ![self] = "da1"]
            /\ UNCHANGED << mem, k, prevHead, casRes, ptr >>

a2(self) == /\ pc[self] = "a2"
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << mem, keepNext, resDA, daCasRes, k, prevHead,
                            casRes, ptr >>

Alloc(self) == a1(self) \/ a2(self)

f1(self) == /\ pc[self] = "f1"
            /\ /\ k' = [k EXCEPT ![self] = "head"]
               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Enqueue",
                                                        pc        |->  "f2",
                                                        prevHead  |->  prevHead[self],
                                                        casRes    |->  casRes[self],
                                                        k         |->  k[self] ] >>
                                                    \o stack[self]]
            /\ prevHead' = [prevHead EXCEPT ![self] = Null]
            /\ casRes' = [casRes EXCEPT ![self] = Null]
            /\ pc' = [pc EXCEPT ![self] = "e1"]
            /\ UNCHANGED << mem, keepNext, resDA, daCasRes, ptr >>

f2(self) == /\ pc[self] = "f2"
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << mem, keepNext, resDA, daCasRes, k, prevHead,
                            casRes, ptr >>

Free(self) == f1(self) \/ f2(self)

p1(self) == /\ pc[self] = "p1"
            /\ pc' = [pc EXCEPT ![self] = "p2"]
            /\ UNCHANGED << mem, stack, keepNext, resDA, daCasRes, k, prevHead,
                            casRes, ptr >>

p2(self) == /\ pc[self] = "p2"
            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Alloc",
                                                     pc        |->  "p3" ] >>
                                                 \o stack[self]]
            /\ pc' = [pc EXCEPT ![self] = "a1"]
            /\ UNCHANGED << mem, keepNext, resDA, daCasRes, k, prevHead,
                            casRes, ptr >>

p3(self) == /\ pc[self] = "p3"
            /\ IF ptr[self] /= Null
                  THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Free",
                                                                pc        |->  "p1" ] >>
                                                            \o stack[self]]
                       /\ pc' = [pc EXCEPT ![self] = "f1"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "p1"]
                       /\ stack' = stack
            /\ UNCHANGED << mem, keepNext, resDA, daCasRes, k, prevHead,
                            casRes, ptr >>

Proc(self) == p1(self) \/ p2(self) \/ p3(self)

Next == (\E self \in ProcSet:  \/ DoAlloc(self) \/ Enqueue(self)
                               \/ Alloc(self) \/ Free(self))
           \/ (\E self \in 1..P: Proc(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

\* END TRANSLATION

RECURSIVE ListSize(_,_,_)
ListSize(h, t, res) == IF h = Null
                       THEN 0
                       ELSE (IF h \in DOMAIN t /\ t[h] /= Null /\ res <= M
                             THEN ListSize(t[h], t, res+1)
                             ELSE res)

RECURSIVE Closure(_,_,_)
Closure(start, next, res) == IF (start \in res \/ start = Null)
                            THEN res
                            ELSE ( IF next[start] /= Null
                                    THEN Closure(next[start], next, res \union {start})
                                    ELSE  res \union {start}  )

TypeInvariant == mem.head \in 1..M \union { Null } /\
        ptr \in [ 1..P -> 1..M \union { Null }] /\
        casRes \in [ 1..P -> 1..M \union { Null } ] /\
        daCasRes \in [ 1..P -> 1..M \union { Null } ]

AllReachable == 1..M \subseteq UNION { Closure(mem.head, mem.next, {}) ,
                                        {ptr[p] : p \in ProcSet },
                                        {resDA[p] : p \in ProcSet }}

NothingLost == ( \A p \in ProcSet : pc[p] \in {"p4"} ) => (
                ListSize(mem.head, mem.next, 1)  = M
              )

Fairness == [] ( \A p  \in ProcSet : M >= P /\ pc[p]="a1" => <> (ptr[p]/=Null) )

Available(m) == m \in Closure(mem.head, mem.next, {})
Processes(m) == { p \in ProcSet :
        \/ ptr[p] = m
        \/  /\ daCasRes[p] = resDA[p]
            /\ daCasRes[p] = m }
ValidState == \A m \in 1..M : (
        \/  /\ Cardinality(Processes(m)) = 1
            /\ ~Available(m)
        \/  /\ Cardinality(Processes(m)) = 0
            /\ Available(m) )

=============================================================================
\* Modification History
\* Last modified Sat May 13 03:37:56 MSK 2017 by orantius
\* Created Fri Apr 14 22:47:15 MSK 2017 by orantius