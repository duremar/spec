------------------------------- MODULE Alloc4 -------------------------------
EXTENDS Naturals, TLC, Sequences, FiniteSets
CONSTANT Null, \* model value
         P, \* processes
         M,  \* available blocks
         LCMOD \* PendingToFreeListCounter max_value
\*ASSUME P < M

RECURSIVE ListSize(_,_,_)
ListSize(h, t, res) == IF h = Null THEN 0 ELSE (IF h \in DOMAIN t /\ t[h] /= Null /\ res <= M THEN ListSize(t[h], t, res+1) ELSE res)

RECURSIVE Closure(_,_,_)
Closure(start, next, res) == IF (start \in res \/ start = Null)
                            THEN res
                            ELSE ( IF next[start] /= Null
                                    THEN Closure(next[start], next, res \union {start})
                                    ELSE  res \union {start}  )

(*****************************************************************
--fair algorithm Alloc4 {
    variable mem = [ head |-> M,
                     pending |-> Null,
                     next |-> [i \in 1..M |-> IF i > 1 THEN i-1 ELSE Null ] ],
             AllocCount = 0,
             PendingToFreeListCounter = 0 ;

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
      variables keepNext = Null, resDA = Null;
    {
      da1: resDA := mem.head;
      da2: while(resDA /= Null) {
        da3: keepNext := mem.next[resDA];
        da4: DoCAS(casRes, mem.head, keepNext, resDA);
        da5: if(casRes = resDA) {
        da6:    ptr := resDA;
                return;
             };
        da7: resDA := mem.head;
          };
      da8: return ;
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
      variables prevHead = Null;
    {
      e1: while(TRUE) {
        e2: prevHead := mem[headPtr];
        e3: mem.next[ptr] := prevHead;
        e4: DoCAS(casRes, mem[headPtr], ptr, prevHead);
        e5: if (casRes = prevHead) {
        \*    if (casRes = prevHead) {
        \*     ptr := Null; \* clear
        e6:    return ;
            }
        }
    }


    procedure Alloc()
      variables fl = Null, resA = Null, keepCounter = 0;
    {
      a0: keepCounter := PendingToFreeListCounter;
      a1: fl := mem.pending;
      a2: AllocCount := AllocCount + 1;
          if(AllocCount = 1) {
      a3:   if(fl /= Null /\ keepCounter = PendingToFreeListCounter) {
      a4:     DoCAS(casRes, mem.pending, Null, fl);
      a5:     if(casRes = fl) {
      a6:       resA := fl;
      a7:       fl := mem.next[fl];
      a8:       call FreeList(fl);
      a9:       AllocCount := AllocCount - 1;
      a95:      \* PendingToFreeListCounter := (PendingToFreeListCounter + 1) % LCMOD;
                PendingToFreeListCounter := PendingToFreeListCounter + 1;
      a10:      ptr := resA;
      a11:      return;
              }
            };
          };
      a12: call DoAlloc();
      a13: AllocCount := AllocCount - 1;
      a14: return;

    }

    procedure Free() {
      f1: if(AllocCount = 0) {
      f2:    call Enqueue("head");
           }  else {
      f3:    call Enqueue("pending");
           }   ;
      f4: ptr := Null;
          return ;
    }

    process (Proc \in 1..P)
      variables ptr = Null, casRes = Null;
    {
      p1: while(TRUE) {
        p2: call Alloc();
        p3: if(ptr /= Null) {
               call Free();
            };
    \* p4: print <<mem.head, mem.pending, mem.next, ListSize(mem.head, mem.next, 1), ListSize(mem.pending, mem.next, 1) >>; \* too slow
        p4: ptr := Null;
      }
    }

}
*****************************************************************)
\* BEGIN TRANSLATION
\* Procedure variable prevHead of procedure FreeList at line 57 col 32 changed to prevHead_
CONSTANT defaultInitValue
VARIABLES mem, AllocCount, PendingToFreeListCounter, pc, stack, keepNext,
          resDA, ff, flTail, prevHead_, headPtr, prevHead, fl, resA,
          keepCounter, ptr, casRes

vars == << mem, AllocCount, PendingToFreeListCounter, pc, stack, keepNext,
           resDA, ff, flTail, prevHead_, headPtr, prevHead, fl, resA,
           keepCounter, ptr, casRes >>

ProcSet == (1..P)

Init == (* Global variables *)
        /\ mem = [ head |-> M,
                   pending |-> Null,
                   next |-> [i \in 1..M |-> IF i > 1 THEN i-1 ELSE Null ] ]
        /\ AllocCount = 0
        /\ PendingToFreeListCounter = 0
        (* Procedure DoAlloc *)
        /\ keepNext = [ self \in ProcSet |-> Null]
        /\ resDA = [ self \in ProcSet |-> Null]
        (* Procedure FreeList *)
        /\ ff = [ self \in ProcSet |-> defaultInitValue]
        /\ flTail = [ self \in ProcSet |-> Null]
        /\ prevHead_ = [ self \in ProcSet |-> Null]
        (* Procedure Enqueue *)
        /\ headPtr = [ self \in ProcSet |-> defaultInitValue]
        /\ prevHead = [ self \in ProcSet |-> Null]
        (* Procedure Alloc *)
        /\ fl = [ self \in ProcSet |-> Null]
        /\ resA = [ self \in ProcSet |-> Null]
        /\ keepCounter = [ self \in ProcSet |-> 0]
        (* Process Proc *)
        /\ ptr = [self \in 1..P |-> Null]
        /\ casRes = [self \in 1..P |-> Null]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "p1"]

da1(self) == /\ pc[self] = "da1"
             /\ resDA' = [resDA EXCEPT ![self] = mem.head]
             /\ pc' = [pc EXCEPT ![self] = "da2"]
             /\ UNCHANGED << mem, AllocCount, PendingToFreeListCounter, stack,
                             keepNext, ff, flTail, prevHead_, headPtr,
                             prevHead, fl, resA, keepCounter, ptr, casRes >>

da2(self) == /\ pc[self] = "da2"
             /\ IF resDA[self] /= Null
                   THEN /\ pc' = [pc EXCEPT ![self] = "da3"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "da8"]
             /\ UNCHANGED << mem, AllocCount, PendingToFreeListCounter, stack,
                             keepNext, resDA, ff, flTail, prevHead_, headPtr,
                             prevHead, fl, resA, keepCounter, ptr, casRes >>

da3(self) == /\ pc[self] = "da3"
             /\ keepNext' = [keepNext EXCEPT ![self] = mem.next[resDA[self]]]
             /\ pc' = [pc EXCEPT ![self] = "da4"]
             /\ UNCHANGED << mem, AllocCount, PendingToFreeListCounter, stack,
                             resDA, ff, flTail, prevHead_, headPtr, prevHead,
                             fl, resA, keepCounter, ptr, casRes >>

da4(self) == /\ pc[self] = "da4"
             /\ IF (mem.head) = resDA[self]
                   THEN /\ mem' = [mem EXCEPT !.head = keepNext[self]]
                        /\ casRes' = [casRes EXCEPT ![self] = resDA[self]]
                   ELSE /\ casRes' = [casRes EXCEPT ![self] = keepNext[self]]
                        /\ mem' = mem
             /\ pc' = [pc EXCEPT ![self] = "da5"]
             /\ UNCHANGED << AllocCount, PendingToFreeListCounter, stack,
                             keepNext, resDA, ff, flTail, prevHead_, headPtr,
                             prevHead, fl, resA, keepCounter, ptr >>

da5(self) == /\ pc[self] = "da5"
             /\ IF casRes[self] = resDA[self]
                   THEN /\ pc' = [pc EXCEPT ![self] = "da6"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "da7"]
             /\ UNCHANGED << mem, AllocCount, PendingToFreeListCounter, stack,
                             keepNext, resDA, ff, flTail, prevHead_, headPtr,
                             prevHead, fl, resA, keepCounter, ptr, casRes >>

da6(self) == /\ pc[self] = "da6"
             /\ ptr' = [ptr EXCEPT ![self] = resDA[self]]
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ keepNext' = [keepNext EXCEPT ![self] = Head(stack[self]).keepNext]
             /\ resDA' = [resDA EXCEPT ![self] = Head(stack[self]).resDA]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << mem, AllocCount, PendingToFreeListCounter, ff,
                             flTail, prevHead_, headPtr, prevHead, fl, resA,
                             keepCounter, casRes >>

da7(self) == /\ pc[self] = "da7"
             /\ resDA' = [resDA EXCEPT ![self] = mem.head]
             /\ pc' = [pc EXCEPT ![self] = "da2"]
             /\ UNCHANGED << mem, AllocCount, PendingToFreeListCounter, stack,
                             keepNext, ff, flTail, prevHead_, headPtr,
                             prevHead, fl, resA, keepCounter, ptr, casRes >>

da8(self) == /\ pc[self] = "da8"
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ keepNext' = [keepNext EXCEPT ![self] = Head(stack[self]).keepNext]
             /\ resDA' = [resDA EXCEPT ![self] = Head(stack[self]).resDA]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << mem, AllocCount, PendingToFreeListCounter, ff,
                             flTail, prevHead_, headPtr, prevHead, fl, resA,
                             keepCounter, ptr, casRes >>

DoAlloc(self) == da1(self) \/ da2(self) \/ da3(self) \/ da4(self)
                    \/ da5(self) \/ da6(self) \/ da7(self) \/ da8(self)

ff1(self) == /\ pc[self] = "ff1"
             /\ IF ff[self] = Null
                   THEN /\ pc' = [pc EXCEPT ![self] = "ff2"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "ff3"]
             /\ UNCHANGED << mem, AllocCount, PendingToFreeListCounter, stack,
                             keepNext, resDA, ff, flTail, prevHead_, headPtr,
                             prevHead, fl, resA, keepCounter, ptr, casRes >>

ff2(self) == /\ pc[self] = "ff2"
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ flTail' = [flTail EXCEPT ![self] = Head(stack[self]).flTail]
             /\ prevHead_' = [prevHead_ EXCEPT ![self] = Head(stack[self]).prevHead_]
             /\ ff' = [ff EXCEPT ![self] = Head(stack[self]).ff]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << mem, AllocCount, PendingToFreeListCounter,
                             keepNext, resDA, headPtr, prevHead, fl, resA,
                             keepCounter, ptr, casRes >>

ff3(self) == /\ pc[self] = "ff3"
             /\ flTail' = [flTail EXCEPT ![self] = ff[self]]
             /\ pc' = [pc EXCEPT ![self] = "ff4"]
             /\ UNCHANGED << mem, AllocCount, PendingToFreeListCounter, stack,
                             keepNext, resDA, ff, prevHead_, headPtr, prevHead,
                             fl, resA, keepCounter, ptr, casRes >>

ff4(self) == /\ pc[self] = "ff4"
             /\ IF mem.next[flTail[self]] /= Null
                   THEN /\ pc' = [pc EXCEPT ![self] = "ff5"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "ff6"]
             /\ UNCHANGED << mem, AllocCount, PendingToFreeListCounter, stack,
                             keepNext, resDA, ff, flTail, prevHead_, headPtr,
                             prevHead, fl, resA, keepCounter, ptr, casRes >>

ff5(self) == /\ pc[self] = "ff5"
             /\ flTail' = [flTail EXCEPT ![self] = mem.next[flTail[self]]]
             /\ pc' = [pc EXCEPT ![self] = "ff4"]
             /\ UNCHANGED << mem, AllocCount, PendingToFreeListCounter, stack,
                             keepNext, resDA, ff, prevHead_, headPtr, prevHead,
                             fl, resA, keepCounter, ptr, casRes >>

ff6(self) == /\ pc[self] = "ff6"
             /\ pc' = [pc EXCEPT ![self] = "ff7"]
             /\ UNCHANGED << mem, AllocCount, PendingToFreeListCounter, stack,
                             keepNext, resDA, ff, flTail, prevHead_, headPtr,
                             prevHead, fl, resA, keepCounter, ptr, casRes >>

ff7(self) == /\ pc[self] = "ff7"
             /\ prevHead_' = [prevHead_ EXCEPT ![self] = mem.head]
             /\ pc' = [pc EXCEPT ![self] = "ff8"]
             /\ UNCHANGED << mem, AllocCount, PendingToFreeListCounter, stack,
                             keepNext, resDA, ff, flTail, headPtr, prevHead,
                             fl, resA, keepCounter, ptr, casRes >>

ff8(self) == /\ pc[self] = "ff8"
             /\ mem' = [mem EXCEPT !.next[flTail[self]] = prevHead_[self]]
             /\ pc' = [pc EXCEPT ![self] = "ff9"]
             /\ UNCHANGED << AllocCount, PendingToFreeListCounter, stack,
                             keepNext, resDA, ff, flTail, prevHead_, headPtr,
                             prevHead, fl, resA, keepCounter, ptr, casRes >>

ff9(self) == /\ pc[self] = "ff9"
             /\ IF (mem.head) = prevHead_[self]
                   THEN /\ mem' = [mem EXCEPT !.head = ff[self]]
                        /\ casRes' = [casRes EXCEPT ![self] = prevHead_[self]]
                   ELSE /\ casRes' = [casRes EXCEPT ![self] = ff[self]]
                        /\ mem' = mem
             /\ IF casRes'[self] = prevHead_[self]
                   THEN /\ pc' = [pc EXCEPT ![self] = "ff10"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "ff6"]
             /\ UNCHANGED << AllocCount, PendingToFreeListCounter, stack,
                             keepNext, resDA, ff, flTail, prevHead_, headPtr,
                             prevHead, fl, resA, keepCounter, ptr >>

ff10(self) == /\ pc[self] = "ff10"
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ flTail' = [flTail EXCEPT ![self] = Head(stack[self]).flTail]
              /\ prevHead_' = [prevHead_ EXCEPT ![self] = Head(stack[self]).prevHead_]
              /\ ff' = [ff EXCEPT ![self] = Head(stack[self]).ff]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << mem, AllocCount, PendingToFreeListCounter,
                              keepNext, resDA, headPtr, prevHead, fl, resA,
                              keepCounter, ptr, casRes >>

ff11(self) == /\ pc[self] = "ff11"
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ flTail' = [flTail EXCEPT ![self] = Head(stack[self]).flTail]
              /\ prevHead_' = [prevHead_ EXCEPT ![self] = Head(stack[self]).prevHead_]
              /\ ff' = [ff EXCEPT ![self] = Head(stack[self]).ff]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << mem, AllocCount, PendingToFreeListCounter,
                              keepNext, resDA, headPtr, prevHead, fl, resA,
                              keepCounter, ptr, casRes >>

FreeList(self) == ff1(self) \/ ff2(self) \/ ff3(self) \/ ff4(self)
                     \/ ff5(self) \/ ff6(self) \/ ff7(self) \/ ff8(self)
                     \/ ff9(self) \/ ff10(self) \/ ff11(self)

e1(self) == /\ pc[self] = "e1"
            /\ pc' = [pc EXCEPT ![self] = "e2"]
            /\ UNCHANGED << mem, AllocCount, PendingToFreeListCounter, stack,
                            keepNext, resDA, ff, flTail, prevHead_, headPtr,
                            prevHead, fl, resA, keepCounter, ptr, casRes >>

e2(self) == /\ pc[self] = "e2"
            /\ prevHead' = [prevHead EXCEPT ![self] = mem[headPtr[self]]]
            /\ pc' = [pc EXCEPT ![self] = "e3"]
            /\ UNCHANGED << mem, AllocCount, PendingToFreeListCounter, stack,
                            keepNext, resDA, ff, flTail, prevHead_, headPtr,
                            fl, resA, keepCounter, ptr, casRes >>

e3(self) == /\ pc[self] = "e3"
            /\ mem' = [mem EXCEPT !.next[ptr[self]] = prevHead[self]]
            /\ pc' = [pc EXCEPT ![self] = "e4"]
            /\ UNCHANGED << AllocCount, PendingToFreeListCounter, stack,
                            keepNext, resDA, ff, flTail, prevHead_, headPtr,
                            prevHead, fl, resA, keepCounter, ptr, casRes >>

e4(self) == /\ pc[self] = "e4"
            /\ IF (mem[headPtr[self]]) = prevHead[self]
                  THEN /\ mem' = [mem EXCEPT ![headPtr[self]] = ptr[self]]
                       /\ casRes' = [casRes EXCEPT ![self] = prevHead[self]]
                  ELSE /\ casRes' = [casRes EXCEPT ![self] = ptr[self]]
                       /\ mem' = mem
            /\ pc' = [pc EXCEPT ![self] = "e5"]
            /\ UNCHANGED << AllocCount, PendingToFreeListCounter, stack,
                            keepNext, resDA, ff, flTail, prevHead_, headPtr,
                            prevHead, fl, resA, keepCounter, ptr >>

e5(self) == /\ pc[self] = "e5"
            /\ IF casRes[self] = prevHead[self]
                  THEN /\ pc' = [pc EXCEPT ![self] = "e6"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "e1"]
            /\ UNCHANGED << mem, AllocCount, PendingToFreeListCounter, stack,
                            keepNext, resDA, ff, flTail, prevHead_, headPtr,
                            prevHead, fl, resA, keepCounter, ptr, casRes >>

e6(self) == /\ pc[self] = "e6"
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ prevHead' = [prevHead EXCEPT ![self] = Head(stack[self]).prevHead]
            /\ headPtr' = [headPtr EXCEPT ![self] = Head(stack[self]).headPtr]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << mem, AllocCount, PendingToFreeListCounter,
                            keepNext, resDA, ff, flTail, prevHead_, fl, resA,
                            keepCounter, ptr, casRes >>

Enqueue(self) == e1(self) \/ e2(self) \/ e3(self) \/ e4(self) \/ e5(self)
                    \/ e6(self)

a0(self) == /\ pc[self] = "a0"
            /\ keepCounter' = [keepCounter EXCEPT ![self] = PendingToFreeListCounter]
            /\ pc' = [pc EXCEPT ![self] = "a1"]
            /\ UNCHANGED << mem, AllocCount, PendingToFreeListCounter, stack,
                            keepNext, resDA, ff, flTail, prevHead_, headPtr,
                            prevHead, fl, resA, ptr, casRes >>

a1(self) == /\ pc[self] = "a1"
            /\ fl' = [fl EXCEPT ![self] = mem.pending]
            /\ pc' = [pc EXCEPT ![self] = "a2"]
            /\ UNCHANGED << mem, AllocCount, PendingToFreeListCounter, stack,
                            keepNext, resDA, ff, flTail, prevHead_, headPtr,
                            prevHead, resA, keepCounter, ptr, casRes >>

a2(self) == /\ pc[self] = "a2"
            /\ AllocCount' = AllocCount + 1
            /\ IF AllocCount' = 1
                  THEN /\ pc' = [pc EXCEPT ![self] = "a3"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "a12"]
            /\ UNCHANGED << mem, PendingToFreeListCounter, stack, keepNext,
                            resDA, ff, flTail, prevHead_, headPtr, prevHead,
                            fl, resA, keepCounter, ptr, casRes >>

a3(self) == /\ pc[self] = "a3"
            /\ IF fl[self] /= Null /\ keepCounter[self] = PendingToFreeListCounter
                  THEN /\ pc' = [pc EXCEPT ![self] = "a4"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "a12"]
            /\ UNCHANGED << mem, AllocCount, PendingToFreeListCounter, stack,
                            keepNext, resDA, ff, flTail, prevHead_, headPtr,
                            prevHead, fl, resA, keepCounter, ptr, casRes >>

a4(self) == /\ pc[self] = "a4"
            /\ IF (mem.pending) = fl[self]
                  THEN /\ mem' = [mem EXCEPT !.pending = Null]
                       /\ casRes' = [casRes EXCEPT ![self] = fl[self]]
                  ELSE /\ casRes' = [casRes EXCEPT ![self] = Null]
                       /\ mem' = mem
            /\ pc' = [pc EXCEPT ![self] = "a5"]
            /\ UNCHANGED << AllocCount, PendingToFreeListCounter, stack,
                            keepNext, resDA, ff, flTail, prevHead_, headPtr,
                            prevHead, fl, resA, keepCounter, ptr >>

a5(self) == /\ pc[self] = "a5"
            /\ IF casRes[self] = fl[self]
                  THEN /\ pc' = [pc EXCEPT ![self] = "a6"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "a12"]
            /\ UNCHANGED << mem, AllocCount, PendingToFreeListCounter, stack,
                            keepNext, resDA, ff, flTail, prevHead_, headPtr,
                            prevHead, fl, resA, keepCounter, ptr, casRes >>

a6(self) == /\ pc[self] = "a6"
            /\ resA' = [resA EXCEPT ![self] = fl[self]]
            /\ pc' = [pc EXCEPT ![self] = "a7"]
            /\ UNCHANGED << mem, AllocCount, PendingToFreeListCounter, stack,
                            keepNext, resDA, ff, flTail, prevHead_, headPtr,
                            prevHead, fl, keepCounter, ptr, casRes >>

a7(self) == /\ pc[self] = "a7"
            /\ fl' = [fl EXCEPT ![self] = mem.next[fl[self]]]
            /\ pc' = [pc EXCEPT ![self] = "a8"]
            /\ UNCHANGED << mem, AllocCount, PendingToFreeListCounter, stack,
                            keepNext, resDA, ff, flTail, prevHead_, headPtr,
                            prevHead, resA, keepCounter, ptr, casRes >>

a8(self) == /\ pc[self] = "a8"
            /\ /\ ff' = [ff EXCEPT ![self] = fl[self]]
               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "FreeList",
                                                        pc        |->  "a9",
                                                        flTail    |->  flTail[self],
                                                        prevHead_ |->  prevHead_[self],
                                                        ff        |->  ff[self] ] >>
                                                    \o stack[self]]
            /\ flTail' = [flTail EXCEPT ![self] = Null]
            /\ prevHead_' = [prevHead_ EXCEPT ![self] = Null]
            /\ pc' = [pc EXCEPT ![self] = "ff1"]
            /\ UNCHANGED << mem, AllocCount, PendingToFreeListCounter,
                            keepNext, resDA, headPtr, prevHead, fl, resA,
                            keepCounter, ptr, casRes >>

a9(self) == /\ pc[self] = "a9"
            /\ AllocCount' = AllocCount - 1
            /\ pc' = [pc EXCEPT ![self] = "a95"]
            /\ UNCHANGED << mem, PendingToFreeListCounter, stack, keepNext,
                            resDA, ff, flTail, prevHead_, headPtr, prevHead,
                            fl, resA, keepCounter, ptr, casRes >>

a95(self) == /\ pc[self] = "a95"
             /\ PendingToFreeListCounter' = PendingToFreeListCounter + 1
             /\ pc' = [pc EXCEPT ![self] = "a10"]
             /\ UNCHANGED << mem, AllocCount, stack, keepNext, resDA, ff,
                             flTail, prevHead_, headPtr, prevHead, fl, resA,
                             keepCounter, ptr, casRes >>

a10(self) == /\ pc[self] = "a10"
             /\ ptr' = [ptr EXCEPT ![self] = resA[self]]
             /\ pc' = [pc EXCEPT ![self] = "a11"]
             /\ UNCHANGED << mem, AllocCount, PendingToFreeListCounter, stack,
                             keepNext, resDA, ff, flTail, prevHead_, headPtr,
                             prevHead, fl, resA, keepCounter, casRes >>

a11(self) == /\ pc[self] = "a11"
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ fl' = [fl EXCEPT ![self] = Head(stack[self]).fl]
             /\ resA' = [resA EXCEPT ![self] = Head(stack[self]).resA]
             /\ keepCounter' = [keepCounter EXCEPT ![self] = Head(stack[self]).keepCounter]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << mem, AllocCount, PendingToFreeListCounter,
                             keepNext, resDA, ff, flTail, prevHead_, headPtr,
                             prevHead, ptr, casRes >>

a12(self) == /\ pc[self] = "a12"
             /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "DoAlloc",
                                                      pc        |->  "a13",
                                                      keepNext  |->  keepNext[self],
                                                      resDA     |->  resDA[self] ] >>
                                                  \o stack[self]]
             /\ keepNext' = [keepNext EXCEPT ![self] = Null]
             /\ resDA' = [resDA EXCEPT ![self] = Null]
             /\ pc' = [pc EXCEPT ![self] = "da1"]
             /\ UNCHANGED << mem, AllocCount, PendingToFreeListCounter, ff,
                             flTail, prevHead_, headPtr, prevHead, fl, resA,
                             keepCounter, ptr, casRes >>

a13(self) == /\ pc[self] = "a13"
             /\ AllocCount' = AllocCount - 1
             /\ pc' = [pc EXCEPT ![self] = "a14"]
             /\ UNCHANGED << mem, PendingToFreeListCounter, stack, keepNext,
                             resDA, ff, flTail, prevHead_, headPtr, prevHead,
                             fl, resA, keepCounter, ptr, casRes >>

a14(self) == /\ pc[self] = "a14"
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ fl' = [fl EXCEPT ![self] = Head(stack[self]).fl]
             /\ resA' = [resA EXCEPT ![self] = Head(stack[self]).resA]
             /\ keepCounter' = [keepCounter EXCEPT ![self] = Head(stack[self]).keepCounter]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << mem, AllocCount, PendingToFreeListCounter,
                             keepNext, resDA, ff, flTail, prevHead_, headPtr,
                             prevHead, ptr, casRes >>

Alloc(self) == a0(self) \/ a1(self) \/ a2(self) \/ a3(self) \/ a4(self)
                  \/ a5(self) \/ a6(self) \/ a7(self) \/ a8(self)
                  \/ a9(self) \/ a95(self) \/ a10(self) \/ a11(self)
                  \/ a12(self) \/ a13(self) \/ a14(self)

f1(self) == /\ pc[self] = "f1"
            /\ IF AllocCount = 0
                  THEN /\ pc' = [pc EXCEPT ![self] = "f2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "f3"]
            /\ UNCHANGED << mem, AllocCount, PendingToFreeListCounter, stack,
                            keepNext, resDA, ff, flTail, prevHead_, headPtr,
                            prevHead, fl, resA, keepCounter, ptr, casRes >>

f2(self) == /\ pc[self] = "f2"
            /\ /\ headPtr' = [headPtr EXCEPT ![self] = "head"]
               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Enqueue",
                                                        pc        |->  "f4",
                                                        prevHead  |->  prevHead[self],
                                                        headPtr   |->  headPtr[self] ] >>
                                                    \o stack[self]]
            /\ prevHead' = [prevHead EXCEPT ![self] = Null]
            /\ pc' = [pc EXCEPT ![self] = "e1"]
            /\ UNCHANGED << mem, AllocCount, PendingToFreeListCounter,
                            keepNext, resDA, ff, flTail, prevHead_, fl, resA,
                            keepCounter, ptr, casRes >>

f3(self) == /\ pc[self] = "f3"
            /\ /\ headPtr' = [headPtr EXCEPT ![self] = "pending"]
               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Enqueue",
                                                        pc        |->  "f4",
                                                        prevHead  |->  prevHead[self],
                                                        headPtr   |->  headPtr[self] ] >>
                                                    \o stack[self]]
            /\ prevHead' = [prevHead EXCEPT ![self] = Null]
            /\ pc' = [pc EXCEPT ![self] = "e1"]
            /\ UNCHANGED << mem, AllocCount, PendingToFreeListCounter,
                            keepNext, resDA, ff, flTail, prevHead_, fl, resA,
                            keepCounter, ptr, casRes >>

f4(self) == /\ pc[self] = "f4"
            /\ ptr' = [ptr EXCEPT ![self] = Null]
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << mem, AllocCount, PendingToFreeListCounter,
                            keepNext, resDA, ff, flTail, prevHead_, headPtr,
                            prevHead, fl, resA, keepCounter, casRes >>

Free(self) == f1(self) \/ f2(self) \/ f3(self) \/ f4(self)

p1(self) == /\ pc[self] = "p1"
            /\ pc' = [pc EXCEPT ![self] = "p2"]
            /\ UNCHANGED << mem, AllocCount, PendingToFreeListCounter, stack,
                            keepNext, resDA, ff, flTail, prevHead_, headPtr,
                            prevHead, fl, resA, keepCounter, ptr, casRes >>

p2(self) == /\ pc[self] = "p2"
            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Alloc",
                                                     pc        |->  "p3",
                                                     fl        |->  fl[self],
                                                     resA      |->  resA[self],
                                                     keepCounter |->  keepCounter[self] ] >>
                                                 \o stack[self]]
            /\ fl' = [fl EXCEPT ![self] = Null]
            /\ resA' = [resA EXCEPT ![self] = Null]
            /\ keepCounter' = [keepCounter EXCEPT ![self] = 0]
            /\ pc' = [pc EXCEPT ![self] = "a0"]
            /\ UNCHANGED << mem, AllocCount, PendingToFreeListCounter,
                            keepNext, resDA, ff, flTail, prevHead_, headPtr,
                            prevHead, ptr, casRes >>

p3(self) == /\ pc[self] = "p3"
            /\ IF ptr[self] /= Null
                  THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Free",
                                                                pc        |->  "p4" ] >>
                                                            \o stack[self]]
                       /\ pc' = [pc EXCEPT ![self] = "f1"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "p4"]
                       /\ stack' = stack
            /\ UNCHANGED << mem, AllocCount, PendingToFreeListCounter,
                            keepNext, resDA, ff, flTail, prevHead_, headPtr,
                            prevHead, fl, resA, keepCounter, ptr, casRes >>

p4(self) == /\ pc[self] = "p4"
            /\ ptr' = [ptr EXCEPT ![self] = Null]
            /\ pc' = [pc EXCEPT ![self] = "p1"]
            /\ UNCHANGED << mem, AllocCount, PendingToFreeListCounter, stack,
                            keepNext, resDA, ff, flTail, prevHead_, headPtr,
                            prevHead, fl, resA, keepCounter, casRes >>

Proc(self) == p1(self) \/ p2(self) \/ p3(self) \/ p4(self)

Next == (\E self \in ProcSet:  \/ DoAlloc(self) \/ FreeList(self)
                               \/ Enqueue(self) \/ Alloc(self) \/ Free(self))
           \/ (\E self \in 1..P: Proc(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

\* END TRANSLATION

TypeInvariant == mem.head \in 1..M \union { Null } /\
        ptr \in [ 1..P -> 1..M \union { Null }] /\
        casRes \in [ 1..P -> 1..M \union { Null } ] /\
        AllocCount \in 0..P

AllReachable == 1..M \subseteq UNION { Closure(mem.head, mem.next, {}) ,
                                       Closure(mem.pending, mem.next, {}),
                                       UNION {Closure(fl[p], mem.next, {}) : p \in ProcSet },
                                        {ptr[p] : p \in ProcSet },
                                        {resA[p] : p \in ProcSet },
                                        {resDA[p] : p \in ProcSet }}

AllocDistinct == \A pp1,pp2 \in ProcSet : ptr[pp1] /= Null /\ ptr[pp2] /= Null /\ pp1 /= pp2 => ptr[pp1] /= ptr[pp2]

NothingLost == ( \A p \in ProcSet : pc[p] \in {"p4"} ) => (
                (ListSize(mem.head, mem.next, 1) + ListSize(mem.pending, mem.next, 1) ) = M
                /\ AllocCount = 0
              )

Fairness == [] ( \A p  \in ProcSet : M>=P /\ pc[p]="da1" => <> (pc[p]="da6") )
=============================================================================
\* Modification History
\* Last modified Mon May 08 13:54:44 MSK 2017 by orantius
\* Created Fri Apr 14 22:47:15 MSK 2017 by orantius
