------------------------------- MODULE Alloc3 -------------------------------
EXTENDS Naturals, TLC, Sequences, FiniteSets
CONSTANT Null, \* model value
         P, \* processes
         M  \* available blocks

(*****************************************************************
--fair algorithm Alloc3 {
    variable mem = [ head |-> M,
                     pending |-> Null,
                     next |-> [i \in 1..M |-> IF i > 1 THEN i-1 ELSE Null ] ],
             AllocCount = 0 ;

    macro DoCAS(result, addr, new, old) {
      if (addr = old) {
        addr := new;
        result := old;
      } else {
        result := new;
      }
    }

    macro AtomicAdd(a, b) {
      a := a + b;
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

    procedure FreeList(ff)
      variables flTail = Null, prevHead = Null;
    {
    ff1:  if (ff = Null) {
    ff2:     return ;
          };
    ff3:  flTail := ff;
    ff4:  while(mem.next[flTail] /= Null) {
    ff5:       flTail := mem.next[flTail];
          };
    ff6:  while(TRUE) {
    ff7:     prevHead := mem.head;
    ff8:     mem.next[flTail] := prevHead;
    ff9:     DoCAS(casRes, mem.head, ff, prevHead);
             if(casRes = prevHead) {
    ff10:         return ;
             }
          };
    ff11: return ;
    }

    procedure Enqueue(headPtr)
      variables prevHeadE = Null, casRes = Null;
    {
      e1: while(TRUE) {
        e2: prevHeadE := mem[headPtr];
            casRes := Null;
        e3: mem.next[ptr] := prevHeadE;
        e4: DoCAS(casRes, mem[headPtr], ptr, prevHeadE);
             if (casRes = prevHeadE) {
                ptr := Null;
        e5:     return ;
            }
        }
    }


    procedure Alloc()
      variables fl = Null, resA = Null, aCasRes = Null;
    {
      a1: fl := mem.pending;
      a2: AllocCount := AllocCount + 1;
          if(AllocCount = 1) {
      a3:   if(fl /= Null) {
      a4:     DoCAS(aCasRes, mem.pending, Null, fl);
              if(aCasRes = fl) {
      a5:       resA := fl;
      a6:       fl := mem.next[fl];
      a7:       call FreeList(fl);
      a8:       AllocCount := AllocCount - 1;
      a9:       ptr := resA;
                return;
              }
            };
          };
      a10: call DoAlloc();
      a11: AllocCount := AllocCount - 1;
           return;
    }

    procedure Free() {
      f1: if(AllocCount = 0) {
      f2:    call Enqueue("head");
           }  else {
      f3:    call Enqueue("pending");
           };
      f4: return ;
    }

    process (Proc \in 1..P)
      variables ptr = Null, casRes = Null;
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
\* Process variable casRes of process Proc at line 114 col 29 changed to casRes_
CONSTANT defaultInitValue
VARIABLES mem, AllocCount, pc, stack, keepNext, resDA, daCasRes, ff, flTail,
          prevHead, headPtr, prevHeadE, casRes, fl, resA, aCasRes, ptr,
          casRes_

vars == << mem, AllocCount, pc, stack, keepNext, resDA, daCasRes, ff, flTail,
           prevHead, headPtr, prevHeadE, casRes, fl, resA, aCasRes, ptr,
           casRes_ >>

ProcSet == (1..P)

Init == (* Global variables *)
        /\ mem = [ head |-> M,
                   pending |-> Null,
                   next |-> [i \in 1..M |-> IF i > 1 THEN i-1 ELSE Null ] ]
        /\ AllocCount = 0
        (* Procedure DoAlloc *)
        /\ keepNext = [ self \in ProcSet |-> Null]
        /\ resDA = [ self \in ProcSet |-> Null]
        /\ daCasRes = [ self \in ProcSet |-> Null]
        (* Procedure FreeList *)
        /\ ff = [ self \in ProcSet |-> defaultInitValue]
        /\ flTail = [ self \in ProcSet |-> Null]
        /\ prevHead = [ self \in ProcSet |-> Null]
        (* Procedure Enqueue *)
        /\ headPtr = [ self \in ProcSet |-> defaultInitValue]
        /\ prevHeadE = [ self \in ProcSet |-> Null]
        /\ casRes = [ self \in ProcSet |-> Null]
        (* Procedure Alloc *)
        /\ fl = [ self \in ProcSet |-> Null]
        /\ resA = [ self \in ProcSet |-> Null]
        /\ aCasRes = [ self \in ProcSet |-> Null]
        (* Process Proc *)
        /\ ptr = [self \in 1..P |-> Null]
        /\ casRes_ = [self \in 1..P |-> Null]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "p1"]

da1(self) == /\ pc[self] = "da1"
             /\ resDA' = [resDA EXCEPT ![self] = mem.head]
             /\ pc' = [pc EXCEPT ![self] = "da2"]
             /\ UNCHANGED << mem, AllocCount, stack, keepNext, daCasRes, ff,
                             flTail, prevHead, headPtr, prevHeadE, casRes, fl,
                             resA, aCasRes, ptr, casRes_ >>

da2(self) == /\ pc[self] = "da2"
             /\ IF resDA[self] /= Null
                   THEN /\ pc' = [pc EXCEPT ![self] = "da3"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "da7"]
             /\ UNCHANGED << mem, AllocCount, stack, keepNext, resDA, daCasRes,
                             ff, flTail, prevHead, headPtr, prevHeadE, casRes,
                             fl, resA, aCasRes, ptr, casRes_ >>

da3(self) == /\ pc[self] = "da3"
             /\ keepNext' = [keepNext EXCEPT ![self] = mem.next[resDA[self]]]
             /\ pc' = [pc EXCEPT ![self] = "da4"]
             /\ UNCHANGED << mem, AllocCount, stack, resDA, daCasRes, ff,
                             flTail, prevHead, headPtr, prevHeadE, casRes, fl,
                             resA, aCasRes, ptr, casRes_ >>

da4(self) == /\ pc[self] = "da4"
             /\ IF (mem.head) = resDA[self]
                   THEN /\ mem' = [mem EXCEPT !.head = keepNext[self]]
                        /\ daCasRes' = [daCasRes EXCEPT ![self] = resDA[self]]
                   ELSE /\ daCasRes' = [daCasRes EXCEPT ![self] = keepNext[self]]
                        /\ mem' = mem
             /\ IF daCasRes'[self] = resDA[self]
                   THEN /\ pc' = [pc EXCEPT ![self] = "da5"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "da6"]
             /\ UNCHANGED << AllocCount, stack, keepNext, resDA, ff, flTail,
                             prevHead, headPtr, prevHeadE, casRes, fl, resA,
                             aCasRes, ptr, casRes_ >>

da5(self) == /\ pc[self] = "da5"
             /\ ptr' = [ptr EXCEPT ![self] = resDA[self]]
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ keepNext' = [keepNext EXCEPT ![self] = Head(stack[self]).keepNext]
             /\ resDA' = [resDA EXCEPT ![self] = Head(stack[self]).resDA]
             /\ daCasRes' = [daCasRes EXCEPT ![self] = Head(stack[self]).daCasRes]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << mem, AllocCount, ff, flTail, prevHead, headPtr,
                             prevHeadE, casRes, fl, resA, aCasRes, casRes_ >>

da6(self) == /\ pc[self] = "da6"
             /\ resDA' = [resDA EXCEPT ![self] = mem.head]
             /\ daCasRes' = [daCasRes EXCEPT ![self] = Null]
             /\ pc' = [pc EXCEPT ![self] = "da2"]
             /\ UNCHANGED << mem, AllocCount, stack, keepNext, ff, flTail,
                             prevHead, headPtr, prevHeadE, casRes, fl, resA,
                             aCasRes, ptr, casRes_ >>

da7(self) == /\ pc[self] = "da7"
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ keepNext' = [keepNext EXCEPT ![self] = Head(stack[self]).keepNext]
             /\ resDA' = [resDA EXCEPT ![self] = Head(stack[self]).resDA]
             /\ daCasRes' = [daCasRes EXCEPT ![self] = Head(stack[self]).daCasRes]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << mem, AllocCount, ff, flTail, prevHead, headPtr,
                             prevHeadE, casRes, fl, resA, aCasRes, ptr,
                             casRes_ >>

DoAlloc(self) == da1(self) \/ da2(self) \/ da3(self) \/ da4(self)
                    \/ da5(self) \/ da6(self) \/ da7(self)

ff1(self) == /\ pc[self] = "ff1"
             /\ IF ff[self] = Null
                   THEN /\ pc' = [pc EXCEPT ![self] = "ff2"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "ff3"]
             /\ UNCHANGED << mem, AllocCount, stack, keepNext, resDA, daCasRes,
                             ff, flTail, prevHead, headPtr, prevHeadE, casRes,
                             fl, resA, aCasRes, ptr, casRes_ >>

ff2(self) == /\ pc[self] = "ff2"
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ flTail' = [flTail EXCEPT ![self] = Head(stack[self]).flTail]
             /\ prevHead' = [prevHead EXCEPT ![self] = Head(stack[self]).prevHead]
             /\ ff' = [ff EXCEPT ![self] = Head(stack[self]).ff]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << mem, AllocCount, keepNext, resDA, daCasRes,
                             headPtr, prevHeadE, casRes, fl, resA, aCasRes,
                             ptr, casRes_ >>

ff3(self) == /\ pc[self] = "ff3"
             /\ flTail' = [flTail EXCEPT ![self] = ff[self]]
             /\ pc' = [pc EXCEPT ![self] = "ff4"]
             /\ UNCHANGED << mem, AllocCount, stack, keepNext, resDA, daCasRes,
                             ff, prevHead, headPtr, prevHeadE, casRes, fl,
                             resA, aCasRes, ptr, casRes_ >>

ff4(self) == /\ pc[self] = "ff4"
             /\ IF mem.next[flTail[self]] /= Null
                   THEN /\ pc' = [pc EXCEPT ![self] = "ff5"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "ff6"]
             /\ UNCHANGED << mem, AllocCount, stack, keepNext, resDA, daCasRes,
                             ff, flTail, prevHead, headPtr, prevHeadE, casRes,
                             fl, resA, aCasRes, ptr, casRes_ >>

ff5(self) == /\ pc[self] = "ff5"
             /\ flTail' = [flTail EXCEPT ![self] = mem.next[flTail[self]]]
             /\ pc' = [pc EXCEPT ![self] = "ff4"]
             /\ UNCHANGED << mem, AllocCount, stack, keepNext, resDA, daCasRes,
                             ff, prevHead, headPtr, prevHeadE, casRes, fl,
                             resA, aCasRes, ptr, casRes_ >>

ff6(self) == /\ pc[self] = "ff6"
             /\ pc' = [pc EXCEPT ![self] = "ff7"]
             /\ UNCHANGED << mem, AllocCount, stack, keepNext, resDA, daCasRes,
                             ff, flTail, prevHead, headPtr, prevHeadE, casRes,
                             fl, resA, aCasRes, ptr, casRes_ >>

ff7(self) == /\ pc[self] = "ff7"
             /\ prevHead' = [prevHead EXCEPT ![self] = mem.head]
             /\ pc' = [pc EXCEPT ![self] = "ff8"]
             /\ UNCHANGED << mem, AllocCount, stack, keepNext, resDA, daCasRes,
                             ff, flTail, headPtr, prevHeadE, casRes, fl, resA,
                             aCasRes, ptr, casRes_ >>

ff8(self) == /\ pc[self] = "ff8"
             /\ mem' = [mem EXCEPT !.next[flTail[self]] = prevHead[self]]
             /\ pc' = [pc EXCEPT ![self] = "ff9"]
             /\ UNCHANGED << AllocCount, stack, keepNext, resDA, daCasRes, ff,
                             flTail, prevHead, headPtr, prevHeadE, casRes, fl,
                             resA, aCasRes, ptr, casRes_ >>

ff9(self) == /\ pc[self] = "ff9"
             /\ IF (mem.head) = prevHead[self]
                   THEN /\ mem' = [mem EXCEPT !.head = ff[self]]
                        /\ casRes' = [casRes EXCEPT ![self] = prevHead[self]]
                   ELSE /\ casRes' = [casRes EXCEPT ![self] = ff[self]]
                        /\ mem' = mem
             /\ IF casRes'[self] = prevHead[self]
                   THEN /\ pc' = [pc EXCEPT ![self] = "ff10"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "ff6"]
             /\ UNCHANGED << AllocCount, stack, keepNext, resDA, daCasRes, ff,
                             flTail, prevHead, headPtr, prevHeadE, fl, resA,
                             aCasRes, ptr, casRes_ >>

ff10(self) == /\ pc[self] = "ff10"
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ flTail' = [flTail EXCEPT ![self] = Head(stack[self]).flTail]
              /\ prevHead' = [prevHead EXCEPT ![self] = Head(stack[self]).prevHead]
              /\ ff' = [ff EXCEPT ![self] = Head(stack[self]).ff]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << mem, AllocCount, keepNext, resDA, daCasRes,
                              headPtr, prevHeadE, casRes, fl, resA, aCasRes,
                              ptr, casRes_ >>

ff11(self) == /\ pc[self] = "ff11"
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ flTail' = [flTail EXCEPT ![self] = Head(stack[self]).flTail]
              /\ prevHead' = [prevHead EXCEPT ![self] = Head(stack[self]).prevHead]
              /\ ff' = [ff EXCEPT ![self] = Head(stack[self]).ff]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << mem, AllocCount, keepNext, resDA, daCasRes,
                              headPtr, prevHeadE, casRes, fl, resA, aCasRes,
                              ptr, casRes_ >>

FreeList(self) == ff1(self) \/ ff2(self) \/ ff3(self) \/ ff4(self)
                     \/ ff5(self) \/ ff6(self) \/ ff7(self) \/ ff8(self)
                     \/ ff9(self) \/ ff10(self) \/ ff11(self)

e1(self) == /\ pc[self] = "e1"
            /\ pc' = [pc EXCEPT ![self] = "e2"]
            /\ UNCHANGED << mem, AllocCount, stack, keepNext, resDA, daCasRes,
                            ff, flTail, prevHead, headPtr, prevHeadE, casRes,
                            fl, resA, aCasRes, ptr, casRes_ >>

e2(self) == /\ pc[self] = "e2"
            /\ prevHeadE' = [prevHeadE EXCEPT ![self] = mem[headPtr[self]]]
            /\ casRes' = [casRes EXCEPT ![self] = Null]
            /\ pc' = [pc EXCEPT ![self] = "e3"]
            /\ UNCHANGED << mem, AllocCount, stack, keepNext, resDA, daCasRes,
                            ff, flTail, prevHead, headPtr, fl, resA, aCasRes,
                            ptr, casRes_ >>

e3(self) == /\ pc[self] = "e3"
            /\ mem' = [mem EXCEPT !.next[ptr[self]] = prevHeadE[self]]
            /\ pc' = [pc EXCEPT ![self] = "e4"]
            /\ UNCHANGED << AllocCount, stack, keepNext, resDA, daCasRes, ff,
                            flTail, prevHead, headPtr, prevHeadE, casRes, fl,
                            resA, aCasRes, ptr, casRes_ >>

e4(self) == /\ pc[self] = "e4"
            /\ IF (mem[headPtr[self]]) = prevHeadE[self]
                  THEN /\ mem' = [mem EXCEPT ![headPtr[self]] = ptr[self]]
                       /\ casRes' = [casRes EXCEPT ![self] = prevHeadE[self]]
                  ELSE /\ casRes' = [casRes EXCEPT ![self] = ptr[self]]
                       /\ mem' = mem
            /\ IF casRes'[self] = prevHeadE[self]
                  THEN /\ ptr' = [ptr EXCEPT ![self] = Null]
                       /\ pc' = [pc EXCEPT ![self] = "e5"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "e1"]
                       /\ ptr' = ptr
            /\ UNCHANGED << AllocCount, stack, keepNext, resDA, daCasRes, ff,
                            flTail, prevHead, headPtr, prevHeadE, fl, resA,
                            aCasRes, casRes_ >>

e5(self) == /\ pc[self] = "e5"
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ prevHeadE' = [prevHeadE EXCEPT ![self] = Head(stack[self]).prevHeadE]
            /\ casRes' = [casRes EXCEPT ![self] = Head(stack[self]).casRes]
            /\ headPtr' = [headPtr EXCEPT ![self] = Head(stack[self]).headPtr]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << mem, AllocCount, keepNext, resDA, daCasRes, ff,
                            flTail, prevHead, fl, resA, aCasRes, ptr, casRes_ >>

Enqueue(self) == e1(self) \/ e2(self) \/ e3(self) \/ e4(self) \/ e5(self)

a1(self) == /\ pc[self] = "a1"
            /\ fl' = [fl EXCEPT ![self] = mem.pending]
            /\ pc' = [pc EXCEPT ![self] = "a2"]
            /\ UNCHANGED << mem, AllocCount, stack, keepNext, resDA, daCasRes,
                            ff, flTail, prevHead, headPtr, prevHeadE, casRes,
                            resA, aCasRes, ptr, casRes_ >>

a2(self) == /\ pc[self] = "a2"
            /\ AllocCount' = AllocCount + 1
            /\ IF AllocCount' = 1
                  THEN /\ pc' = [pc EXCEPT ![self] = "a3"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "a10"]
            /\ UNCHANGED << mem, stack, keepNext, resDA, daCasRes, ff, flTail,
                            prevHead, headPtr, prevHeadE, casRes, fl, resA,
                            aCasRes, ptr, casRes_ >>

a3(self) == /\ pc[self] = "a3"
            /\ IF fl[self] /= Null
                  THEN /\ pc' = [pc EXCEPT ![self] = "a4"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "a10"]
            /\ UNCHANGED << mem, AllocCount, stack, keepNext, resDA, daCasRes,
                            ff, flTail, prevHead, headPtr, prevHeadE, casRes,
                            fl, resA, aCasRes, ptr, casRes_ >>

a4(self) == /\ pc[self] = "a4"
            /\ IF (mem.pending) = fl[self]
                  THEN /\ mem' = [mem EXCEPT !.pending = Null]
                       /\ aCasRes' = [aCasRes EXCEPT ![self] = fl[self]]
                  ELSE /\ aCasRes' = [aCasRes EXCEPT ![self] = Null]
                       /\ mem' = mem
            /\ IF aCasRes'[self] = fl[self]
                  THEN /\ pc' = [pc EXCEPT ![self] = "a5"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "a10"]
            /\ UNCHANGED << AllocCount, stack, keepNext, resDA, daCasRes, ff,
                            flTail, prevHead, headPtr, prevHeadE, casRes, fl,
                            resA, ptr, casRes_ >>

a5(self) == /\ pc[self] = "a5"
            /\ resA' = [resA EXCEPT ![self] = fl[self]]
            /\ pc' = [pc EXCEPT ![self] = "a6"]
            /\ UNCHANGED << mem, AllocCount, stack, keepNext, resDA, daCasRes,
                            ff, flTail, prevHead, headPtr, prevHeadE, casRes,
                            fl, aCasRes, ptr, casRes_ >>

a6(self) == /\ pc[self] = "a6"
            /\ fl' = [fl EXCEPT ![self] = mem.next[fl[self]]]
            /\ pc' = [pc EXCEPT ![self] = "a7"]
            /\ UNCHANGED << mem, AllocCount, stack, keepNext, resDA, daCasRes,
                            ff, flTail, prevHead, headPtr, prevHeadE, casRes,
                            resA, aCasRes, ptr, casRes_ >>

a7(self) == /\ pc[self] = "a7"
            /\ /\ ff' = [ff EXCEPT ![self] = fl[self]]
               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "FreeList",
                                                        pc        |->  "a8",
                                                        flTail    |->  flTail[self],
                                                        prevHead  |->  prevHead[self],
                                                        ff        |->  ff[self] ] >>
                                                    \o stack[self]]
            /\ flTail' = [flTail EXCEPT ![self] = Null]
            /\ prevHead' = [prevHead EXCEPT ![self] = Null]
            /\ pc' = [pc EXCEPT ![self] = "ff1"]
            /\ UNCHANGED << mem, AllocCount, keepNext, resDA, daCasRes,
                            headPtr, prevHeadE, casRes, fl, resA, aCasRes, ptr,
                            casRes_ >>

a8(self) == /\ pc[self] = "a8"
            /\ AllocCount' = AllocCount - 1
            /\ pc' = [pc EXCEPT ![self] = "a9"]
            /\ UNCHANGED << mem, stack, keepNext, resDA, daCasRes, ff, flTail,
                            prevHead, headPtr, prevHeadE, casRes, fl, resA,
                            aCasRes, ptr, casRes_ >>

a9(self) == /\ pc[self] = "a9"
            /\ ptr' = [ptr EXCEPT ![self] = resA[self]]
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ fl' = [fl EXCEPT ![self] = Head(stack[self]).fl]
            /\ resA' = [resA EXCEPT ![self] = Head(stack[self]).resA]
            /\ aCasRes' = [aCasRes EXCEPT ![self] = Head(stack[self]).aCasRes]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << mem, AllocCount, keepNext, resDA, daCasRes, ff,
                            flTail, prevHead, headPtr, prevHeadE, casRes,
                            casRes_ >>

a10(self) == /\ pc[self] = "a10"
             /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "DoAlloc",
                                                      pc        |->  "a11",
                                                      keepNext  |->  keepNext[self],
                                                      resDA     |->  resDA[self],
                                                      daCasRes  |->  daCasRes[self] ] >>
                                                  \o stack[self]]
             /\ keepNext' = [keepNext EXCEPT ![self] = Null]
             /\ resDA' = [resDA EXCEPT ![self] = Null]
             /\ daCasRes' = [daCasRes EXCEPT ![self] = Null]
             /\ pc' = [pc EXCEPT ![self] = "da1"]
             /\ UNCHANGED << mem, AllocCount, ff, flTail, prevHead, headPtr,
                             prevHeadE, casRes, fl, resA, aCasRes, ptr,
                             casRes_ >>

a11(self) == /\ pc[self] = "a11"
             /\ AllocCount' = AllocCount - 1
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ fl' = [fl EXCEPT ![self] = Head(stack[self]).fl]
             /\ resA' = [resA EXCEPT ![self] = Head(stack[self]).resA]
             /\ aCasRes' = [aCasRes EXCEPT ![self] = Head(stack[self]).aCasRes]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << mem, keepNext, resDA, daCasRes, ff, flTail,
                             prevHead, headPtr, prevHeadE, casRes, ptr,
                             casRes_ >>

Alloc(self) == a1(self) \/ a2(self) \/ a3(self) \/ a4(self) \/ a5(self)
                  \/ a6(self) \/ a7(self) \/ a8(self) \/ a9(self)
                  \/ a10(self) \/ a11(self)

f1(self) == /\ pc[self] = "f1"
            /\ IF AllocCount = 0
                  THEN /\ pc' = [pc EXCEPT ![self] = "f2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "f3"]
            /\ UNCHANGED << mem, AllocCount, stack, keepNext, resDA, daCasRes,
                            ff, flTail, prevHead, headPtr, prevHeadE, casRes,
                            fl, resA, aCasRes, ptr, casRes_ >>

f2(self) == /\ pc[self] = "f2"
            /\ /\ headPtr' = [headPtr EXCEPT ![self] = "head"]
               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Enqueue",
                                                        pc        |->  "f4",
                                                        prevHeadE |->  prevHeadE[self],
                                                        casRes    |->  casRes[self],
                                                        headPtr   |->  headPtr[self] ] >>
                                                    \o stack[self]]
            /\ prevHeadE' = [prevHeadE EXCEPT ![self] = Null]
            /\ casRes' = [casRes EXCEPT ![self] = Null]
            /\ pc' = [pc EXCEPT ![self] = "e1"]
            /\ UNCHANGED << mem, AllocCount, keepNext, resDA, daCasRes, ff,
                            flTail, prevHead, fl, resA, aCasRes, ptr, casRes_ >>

f3(self) == /\ pc[self] = "f3"
            /\ /\ headPtr' = [headPtr EXCEPT ![self] = "pending"]
               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Enqueue",
                                                        pc        |->  "f4",
                                                        prevHeadE |->  prevHeadE[self],
                                                        casRes    |->  casRes[self],
                                                        headPtr   |->  headPtr[self] ] >>
                                                    \o stack[self]]
            /\ prevHeadE' = [prevHeadE EXCEPT ![self] = Null]
            /\ casRes' = [casRes EXCEPT ![self] = Null]
            /\ pc' = [pc EXCEPT ![self] = "e1"]
            /\ UNCHANGED << mem, AllocCount, keepNext, resDA, daCasRes, ff,
                            flTail, prevHead, fl, resA, aCasRes, ptr, casRes_ >>

f4(self) == /\ pc[self] = "f4"
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << mem, AllocCount, keepNext, resDA, daCasRes, ff,
                            flTail, prevHead, headPtr, prevHeadE, casRes, fl,
                            resA, aCasRes, ptr, casRes_ >>

Free(self) == f1(self) \/ f2(self) \/ f3(self) \/ f4(self)

p1(self) == /\ pc[self] = "p1"
            /\ pc' = [pc EXCEPT ![self] = "p2"]
            /\ UNCHANGED << mem, AllocCount, stack, keepNext, resDA, daCasRes,
                            ff, flTail, prevHead, headPtr, prevHeadE, casRes,
                            fl, resA, aCasRes, ptr, casRes_ >>

p2(self) == /\ pc[self] = "p2"
            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Alloc",
                                                     pc        |->  "p3",
                                                     fl        |->  fl[self],
                                                     resA      |->  resA[self],
                                                     aCasRes   |->  aCasRes[self] ] >>
                                                 \o stack[self]]
            /\ fl' = [fl EXCEPT ![self] = Null]
            /\ resA' = [resA EXCEPT ![self] = Null]
            /\ aCasRes' = [aCasRes EXCEPT ![self] = Null]
            /\ pc' = [pc EXCEPT ![self] = "a1"]
            /\ UNCHANGED << mem, AllocCount, keepNext, resDA, daCasRes, ff,
                            flTail, prevHead, headPtr, prevHeadE, casRes, ptr,
                            casRes_ >>

p3(self) == /\ pc[self] = "p3"
            /\ IF ptr[self] /= Null
                  THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Free",
                                                                pc        |->  "p1" ] >>
                                                            \o stack[self]]
                       /\ pc' = [pc EXCEPT ![self] = "f1"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "p1"]
                       /\ stack' = stack
            /\ UNCHANGED << mem, AllocCount, keepNext, resDA, daCasRes, ff,
                            flTail, prevHead, headPtr, prevHeadE, casRes, fl,
                            resA, aCasRes, ptr, casRes_ >>

Proc(self) == p1(self) \/ p2(self) \/ p3(self)

Next == (\E self \in ProcSet:  \/ DoAlloc(self) \/ FreeList(self)
                               \/ Enqueue(self) \/ Alloc(self) \/ Free(self))
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
Closure(start, next, res) == IF (start \in res \/ start \notin 1..M)
                            THEN res
                            ELSE ( IF next[start] /= Null
                                    THEN Closure(next[start], next, res \union {start})
                                    ELSE  res \union {start}  )

TypeInvariant == mem.head \in 1..M \union { Null } /\
        ptr \in [ 1..P -> 1..M \union { Null }] /\
        casRes \in [ 1..P -> 1..M \union { Null } ] /\
        AllocCount \in 0..P

AllReachable == 1..M \subseteq UNION { Closure(mem.head, mem.next, {}) ,
                                       Closure(mem.pending, mem.next, {}),
                                       UNION {Closure(fl[p], mem.next, {}) : p \in ProcSet },
                                        {ptr[p] : p \in ProcSet }}

NothingLost == ( \A p \in ProcSet : pc[p] \in {"p4"} ) => (
                (ListSize(mem.head, mem.next, 1) + ListSize(mem.pending, mem.next, 1) ) = M
                /\ AllocCount = 0
              )

IsAvailable(m) == \/ m \in Closure(mem.head, mem.next, {})
                \/ m \in Closure(mem.pending, mem.next, {})
                \/ m \in UNION { IF fl[p] /= Null /\ pc[p] \in {"a5","a6"} THEN Closure(mem.next[fl[p]], mem.next, {}) ELSE {} : p \in ProcSet }
                \/ m \in UNION { IF fl[p] /= Null /\ pc[p] = "a7" THEN Closure(fl[p], mem.next, {}) ELSE {} : p \in ProcSet }
                \/ m \in UNION { Closure(ff[p], mem.next, {}) : p \in ProcSet }
          \*      \/ m \in UNION { Closure(prevHead[p], mem.next, {}) : p \in ProcSet }

Processes(m) == { p \in ProcSet :
        \/ ptr[p] = m
        \/ resA[p] = m
        \/  /\ daCasRes[p] = resDA[p]
            /\ daCasRes[p] = m
        \/  /\ aCasRes[p] = fl[p]
            /\ aCasRes[p] = m
            }
ValidState == \A m \in 1..M : (
        \/  /\ Cardinality(Processes(m)) = 1
            /\ ~IsAvailable(m)
        \/  /\ Cardinality(Processes(m)) = 0
            /\ IsAvailable(m) )

THEOREM Spec => []NothingLost
PROOF
<1>1. Init => NothingLost
<1>2. NothingLost /\ [Next]_vars => NothingLost'
<1>3. QED
=============================================================================
\* Modification History
\* Last modified Sat May 13 18:22:56 MSK 2017 by orantius
\* Created Fri Apr 14 22:47:15 MSK 2017 by orantius