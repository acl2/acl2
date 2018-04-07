; ACL2 hand-translation of tiny.spec

; See notes.txt for thoughts about automated translation.

(in-package "ACL2")

(include-book "../../translator/l3")

#||
type regT  = bits(7)
type wordT = bits(32)
type immT  = bits(24)
type addrT = bits(10)
type memT  = addrT -> wordT
||#

#||
exception Reserved
||#

#||
construct funcT {fADD, fSUB, fINC, fDEC, fAND, fOR, fXOR, fReserved}
construct shiftT {noShift, RCY1, RCY8, RCY16}
construct conditionT {skipNever, skipNeg, skipZero, skipInRdy}

val _ = Construct[("funcT",
    [("fADD",[]), ("fSUB",[]), ("fINC",[]), ("fDEC",[]), ("fAND",[]),
     ("fOR",[]), ("fXOR",[]), ("fReserved",[])])]
;
||#

(construct funcT (fADD fSUB fINC fDEC fAND fOR fXOR fReserved))
(construct shiftT (noShift RCY1 RCY8 RCY16))
(construct conditionT (skipNever skipNeg skipZero skipInRdy))
(construct exception (NoException Reserved))

#||

---------------------------------------------
-- State
---------------------------------------------

declare
{
   PC :: addrT          -- Program Counter
   R :: regT -> wordT   -- Registers
   IM :: memT           -- Instruction Memory
   DM :: memT           -- Data Memory
   InRdy :: bool        -- Input Ready
   InData :: wordT      -- Input Data
   OutStrobe :: wordT   -- Output Data
}

||#

#||
(val _ = Record
  ("tiny-acl2.txt_state"
    (sqbkt ("DM" (ATy (FTy 10) F32)) ("IM" (ATy (FTy 10) F32))
           ("InData" F32) ("InRdy" bTy) ("OutStrobe" F32) ("PC" (FTy 10))
           ("R" (ATy (FTy 7) F32)) ("exception" CTy"exception"))))
||#

(defstobj+ st$
  (dm :type (array (unsigned-byte 32) (1024)) ; addrT -> wordT
      :initially 0)
  (im :type (array (unsigned-byte 32) (1024)) ; addrT -> wordT
      :initially 0)
  (indata :type (unsigned-byte 32) ; wordT
          :initially 0)
  (inrdy :type (satisfies booleanp))
  (outstrobe :type (unsigned-byte 32) ; wordT
             :initially 0)
  (pctr :type (unsigned-byte 10) ; addrT
        :initially 0)
  (r :type (array (unsigned-byte 32) (128)) ; regT -> wordT
     :initially 0)
  exception
  )

#||

---------------------------------------------
-- Operations
---------------------------------------------

wordT function (func::funcT, a:: wordT, b:: wordT) =
   match func
   {
     case fADD => a + b
     case fSUB => a - b
     case fINC => b + 1
     case fDEC => b - 1
     case fAND => a && b
     case fOR  => a || b
     case fXOR => a ?? b
     case _ => #Reserved
   }

val function_def = Def
  ("function",TP[Var("func",CTy"funcT"), Var("a",F32), Var("b",F32)],
   Close
     (qVar"state",
      CS
        (Var("func",CTy"funcT"),
         [(LC("fADD",CTy"funcT"),
           TP[Bop(Add,Var("a",F32),Var("b",F32)), qVar"state"]),
          (LC("fSUB",CTy"funcT"),
           TP[Bop(Sub,Var("a",F32),Var("b",F32)), qVar"state"]),
          (LC("fINC",CTy"funcT"),
           TP[Bop(Add,Var("b",F32),LW(1,32)), qVar"state"]),
          (LC("fDEC",CTy"funcT"),
           TP[Bop(Sub,Var("b",F32),LW(1,32)), qVar"state"]),
          (LC("fAND",CTy"funcT"),
           TP[Bop(BAnd,Var("a",F32),Var("b",F32)), qVar"state"]),
          (LC("fOR",CTy"funcT"),
           TP[Bop(BOr,Var("a",F32),Var("b",F32)), qVar"state"]),
          (LC("fXOR",CTy"funcT"),
           TP[Bop(BXor,Var("a",F32),Var("b",F32)), qVar"state"]),
          (AVar(CTy"funcT"),
           Apply
             (Call
                ("raise'exception",ATy(qTy,PTy(F32,qTy)),
                 LC("Reserved",CTy"exception")),qVar"state"))])))
;

   [function_def]  Definition

      |-  func a b.
           function (func,a,b) =
           ( state.
              case func of
                fADD => (a + b,state)
              | fSUB => (a   b,state)
              | fINC => (b + 1w,state)
              | fDEC => (b   1w,state)
              | fAND => (a && b,state)
              | fOR => (a   b,state)
              | fXOR => (a   b,state)
              | fReserved => raise'exception Reserved state)
||#

(defun-struct function0 (((func (type-funct func))
                          (a (unsigned-byte-p 32 a))
                          (b (unsigned-byte-p 32 b)))
                         st$)
  (declare (xargs :stobjs st$))
  (case-match+
   func
   ('fadd (mv (n+ 32 a b) st$))
   ('fsub (mv (n- 32 a b) st$))
   ('finc (mv (n+ 32 b 1) st$))
   ('fdec (mv (n- 32 b 1) st$))
   ('fand (mv (logand a b) st$))
   ('for  (mv (logior a b) st$))
   ('fxor (mv (logxor a b) st$))
   (& (raise-exception 'reserved
                       (arb (unsigned-byte 32))
                       st$))))

#||
wordT shifter (shift::shiftT, a::wordT) =
   match shift
   {
      case noShift => a
      case RCY1    => a #>> 1
      case RCY8    => a #>> 8
      case RCY16   => a #>> 16
   }

val shifter_def = Def
  ("shifter",TP[Var("shift",CTy"shiftT"), Var("a",F32)],
   CS
     (Var("shift",CTy"shiftT"),
      [(LC("noShift",CTy"shiftT"),Var("a",F32)),
       (LC("RCY1",CTy"shiftT"),Bop(Ror,Var("a",F32),LN 1)),
       (LC("RCY8",CTy"shiftT"),Bop(Ror,Var("a",F32),LN 8)),
       (LC("RCY16",CTy"shiftT"),Bop(Ror,Var("a",F32),LN 16))]))
;

   [shifter_def]  Definition

      |-  shift a.
           shifter (shift,a) =
           case shift of
             noShift => a
           | RCY1 => a   1
           | RCY8 => a   8
           | RCY16 => a   16

||#

;;; Translation note: when generating case-match+, when the last condition is
;;; not t, we may add a catchall case which ostensibly returns an arbitrary
;;; value of the correct shape/type, but then prove that it is unreachable,
;;; using IMPOSSIBLE (see the ACL2 documentation for IMPOSSIBLE).

(defun-struct shifter (((shift (type-shiftt shift))
                        (a (unsigned-byte-p 32 a))))
  (case-match+
   shift
   ('noshift a)
   ('rcy1 (ash a -1))
   ('rcy8 (ash a -8))
   ('rcy16 (ash a -16))
   (& (impossible (arb (unsigned-byte 32))))))

#||
wordT ALU (func::funcT, shift::shiftT, a::wordT, b::wordT) =
   shifter (shift, function (func, a, b))

val ALU_def = Def
  ("ALU",
   TP[Var("func",CTy"funcT"), Var("shift",CTy"shiftT"), Var("a",F32),
      Var("b",F32)],
   Close
     (qVar"state",
      Let
        (TP[Var("v",F32), qVar"s"],
         Apply
           (Call
              ("function",ATy(qTy,PTy(F32,qTy)),
               TP[Var("func",CTy"funcT"), Var("a",F32), Var("b",F32)]),
            qVar"state"),
         TP[Call("shifter",F32,TP[Var("shift",CTy"shiftT"), Var("v",F32)]),
            qVar"s"])))
;

   [ALU_def]  Definition

      |-  func shift a b.
           ALU (func,shift,a,b) =
           ( state.
              (let (v,s) = function (func,a,b) state
               in
                 (shifter (shift,v),s)))

||#

; Note that since alu takes st$, it returns st$ -- well, at least I think
; that's the scheme, but actually no such thinking is required if I simply go
; by what's in the ML code.

(defun-struct alu (((func (type-funct func))
                    (shift (type-shiftt shift))
                    (a (unsigned-byte-p 32 a))
                    (b (unsigned-byte-p 32 b)))
                   st$)
  (declare (xargs :stobjs st$))
  (mv-let (v st$)
          (function0 (tuple func a b) st$)
          (mv (shifter (tuple shift v)) st$)))

#||
unit incPC (skip::conditionT, alu::wordT) =
   match skip
   {
      case skipNever => PC <- PC + 1
      case skipNeg   => PC <- PC + if alu < 0  then 2 else 1
      case skipZero  => PC <- PC + if alu == 0 then 2 else 1
      case skipInRdy => PC <- PC + if InRdy    then 2 else 1
   }

val incPC_def = Def
  ("incPC",TP[Var("skip",CTy"conditionT"), Var("alu",F32)],
   Close
     (qVar"state",
      CS
        (Var("skip",CTy"conditionT"),
         [(LC("skipNever",CTy"conditionT"),
           TP[LU,
              Rupd
                ("PC",
                 TP[qVar"state",
                    Bop(Add,Dest("PC",FTy 10,qVar"state"),LW(1,10))])]),
          (LC("skipNeg",CTy"conditionT"),
           TP[LU,
              Rupd
                ("PC",
                 TP[qVar"state",
                    Bop
                      (Add,Dest("PC",FTy 10,qVar"state"),
                       ITE
                         (Bop(Lt,Var("alu",F32),LW(0,32)),LW(2,10),
                          LW(1,10)))])]),
          (LC("skipZero",CTy"conditionT"),
           TP[LU,
              Rupd
                ("PC",
                 TP[qVar"state",
                    Bop
                      (Add,Dest("PC",FTy 10,qVar"state"),
                       ITE(EQ(Var("alu",F32),LW(0,32)),LW(2,10),LW(1,10)))])]),
          (LC("skipInRdy",CTy"conditionT"),
           TP[LU,
              Rupd
                ("PC",
                 TP[qVar"state",
                    Bop
                      (Add,Dest("PC",FTy 10,qVar"state"),
                       ITE
                         (Dest("InRdy",bTy,qVar"state"),LW(2,10),LW(1,10)))])])])))
;

   [incPC_def]  Definition

      |-  skip alu.
           incPC (skip,alu) =
           ( state.
              case skip of
                skipNever => ((),state with PC := state.PC + 1w)
              | skipNeg =>
                  ((),
                   state with PC := state.PC + if alu < 0w then 2w else 1w)
              | skipZero =>
                  ((),
                   state with PC := state.PC + if alu = 0w then 2w else 1w)
              | skipInRdy =>
                  ((),
                   state with
                   PC := state.PC + if state.InRdy then 2w else 1w))

||#

(defun-struct incpc (((skip (type-conditiont skip))
                      (alu_var (unsigned-byte-p 32 alu_var)))
                     st$)
  (declare (xargs :stobjs st$))
  (case-match+
   skip
   ('skipnever (let ((st$ (update-pctr (n+ 10 (pctr st$) 1) st$)))
                 (mv (unit-value) st$)))
   ('skipneg (let ((st$ (update-pctr (n+ 10
                                         (pctr st$)
                                         (if (< alu_var 0) 2 1))
                                     st$)))
               (mv (unit-value) st$)))
   ('skipzero (let ((st$ (update-pctr (n+ 10
                                          (pctr st$)
                                          (if (eql alu_var 0) 2 1))
                                      st$)))
                (mv (unit-value) st$)))
   ('skipinrdy (let ((st$ (update-pctr (n+ 10
                                           (pctr st$)
                                           (if (inrdy st$) 2 1))
                                       st$)))
                 (mv (unit-value) st$)))
   (& (impossible (mv (arb uty) st$)))))

#||
-- Common functionality
unit norm (func::funcT, shift::shiftT, skip::conditionT,
           wback::bool, strobe::bool, w::regT, a::regT, b::regT) =
{
   alu = ALU (func, shift, R(a), R(b));
   when wback do R(w) <- alu;
   when strobe do OutStrobe <- alu;
   incPC (skip, alu)
}

val norm_def = Def
  ("norm",
   TP[Var("func",CTy"funcT"), Var("shift",CTy"shiftT"),
      Var("skip",CTy"conditionT"), bVar"wback", bVar"strobe",
      Var("w",FTy 7), Var("a",FTy 7), Var("b",FTy 7)],
   Close
     (qVar"state",
      Let
        (TP[Var("v",F32), qVar"s"],
         Apply
           (Call
              ("ALU",ATy(qTy,PTy(F32,qTy)),
               TP[Var("func",CTy"funcT"), Var("shift",CTy"shiftT"),
                  Apply
                    (Dest("R",ATy(FTy 7,F32),qVar"state"),Var("a",FTy 7)),
                  Apply
                    (Dest("R",ATy(FTy 7,F32),qVar"state"),Var("b",FTy 7))]),
            qVar"state"),
         Let
           (qVar"s",
            ITE
              (bVar"wback",
               Rupd
                 ("R",
                  TP[qVar"s",
                     Fupd
                       (Dest("R",ATy(FTy 7,F32),qVar"s"),Var("w",FTy 7),
                        Var("v",F32))]),qVar"s"),
            Apply
              (Call
                 ("incPC",ATy(qTy,PTy(uTy,qTy)),
                  TP[Var("skip",CTy"conditionT"), Var("v",F32)]),
               ITE
                 (bVar"strobe",
                  Rupd("OutStrobe",TP[qVar"s", Var("v",F32)]),qVar"s"))))))
;

   [norm_def]  Definition

      |-  func shift skip wback strobe w a b.
           norm (func,shift,skip,wback,strobe,w,a,b) =
           ( state.
              (let (v,s) = ALU (func,shift,state.R a,state.R b) state in
               let s = if wback then s with R := (w =+ v) s.R else s
               in
                 incPC (skip,v)
                   (if strobe then s with OutStrobe := v else s)))

||#

(defthm rp-yields-unsigned-byte-p-32
  (implies (and (rp x)
                (natp a)
                (< a (len x)))
           (unsigned-byte-p 32 (nth a x)))
  :rule-classes ((:rewrite
                  :corollary
                  (implies (and (rp x)
                                (natp a)
                                (< a (len x)))
                           (unsigned-byte-p 32 (nth a x))))
                 (:type-prescription
                  :corollary
                  (implies (and (rp x)
                                (natp a)
                                (< a (len x)))
                           (integerp (nth a x))))))

(encapsulate
 ()

 (local (scatter-exponents))

 (defthm unsigned-byte-p-ash-negative
   (implies (and (posp k)
                 (unsigned-byte-p k x)
                 (integerp n)
                 (<= n 0))
            (unsigned-byte-p k (ash x n)))
   :hints (("Goal"
            :in-theory (enable unsigned-byte-p)
            :nonlinearp t))))

(defun-struct norm (((func (type-funct func))
                     (shift (type-shiftt shift))
                     (skip (type-conditiont skip))
                     (wback (booleanp wback))
                     (strobe (booleanp strobe))
                     (w (unsigned-byte-p 7 w))
                     (a (unsigned-byte-p 7 a))
                     (b (unsigned-byte-p 7 b)))
                    st$)
  (declare (xargs :stobjs st$))
  (mv-let (v st$)
          (alu (tuple func shift (ri a st$) (ri b st$)) st$)
          (let* ((st$ (if wback
                          (update-ri w v st$)
                        st$))
                 (st$ (if strobe
                          (update-outstrobe v st$)
                        st$)))
            (incpc (tuple skip v) st$))))

#||
---------------------------------------------
-- Instructions
---------------------------------------------
||#

#||
define Normal (func::funcT, shift::shiftT, skip::conditionT,
               w::regT, a::regT, b::regT) =
   norm (func, shift, skip, true, false, w, a, b)

val dfn'Normal_def = Def
  ("dfn'Normal",
   TP[Var("func",CTy"funcT"), Var("shift",CTy"shiftT"),
      Var("skip",CTy"conditionT"), Var("w",FTy 7), Var("a",FTy 7),
      Var("b",FTy 7)],
   Close
     (qVar"state",
      Apply
        (Call
           ("norm",ATy(qTy,PTy(uTy,qTy)),
            TP[Var("func",CTy"funcT"), Var("shift",CTy"shiftT"),
               Var("skip",CTy"conditionT"), LT, LF, Var("w",FTy 7),
               Var("a",FTy 7), Var("b",FTy 7)]),qVar"state")))
;

   [dfn'Normal_def]  Definition

      |-  func shift skip w a b.
           dfn'Normal (func,shift,skip,w,a,b) =
           ( state. norm (func,shift,skip,T,F,w,a,b) state)

||#

(defun-struct dfn-normal (((func (type-funct func))
                           (shift (type-shiftt shift))
                           (skip (type-conditiont skip))
                           (w (unsigned-byte-p 7 w))
                           (a (unsigned-byte-p 7 a))
                           (b (unsigned-byte-p 7 b)))
                          st$)
  (declare (xargs :stobjs st$))
  (norm (tuple func shift skip (true) (false) w a b)
        st$))

#||

define StoreDM (func::funcT, shift::shiftT, skip::conditionT,
                w::regT, a::regT, b::regT) =
{
   DM([R(b)]) <- R(a);
   norm (func, shift, skip, true, false, w, a, b)
}

val dfn'StoreDM_def = Def
  ("dfn'StoreDM",
   TP[Var("func",CTy"funcT"), Var("shift",CTy"shiftT"),
      Var("skip",CTy"conditionT"), Var("w",FTy 7), Var("a",FTy 7),
      Var("b",FTy 7)],
   Close
     (qVar"state",
      Apply
        (Call
           ("norm",ATy(qTy,PTy(uTy,qTy)),
            TP[Var("func",CTy"funcT"), Var("shift",CTy"shiftT"),
               Var("skip",CTy"conditionT"), LT, LF, Var("w",FTy 7),
               Var("a",FTy 7), Var("b",FTy 7)]),
         Rupd
           ("DM",
            TP[qVar"state",
               Fupd
                 (Dest("DM",ATy(FTy 10,F32),qVar"state"),
                  Mop
                    (Cast(FTy 10),
                     Apply
                       (Dest("R",ATy(FTy 7,F32),qVar"state"),
                        Var("b",FTy 7))),
                  Apply
                    (Dest("R",ATy(FTy 7,F32),qVar"state"),Var("a",FTy 7)))]))))
;

   [dfn'StoreDM_def]  Definition

      |-  func shift skip w a b.
           dfn'StoreDM (func,shift,skip,w,a,b) =
           ( state.
              norm (func,shift,skip,T,F,w,a,b)
                (state with DM := (w2w (state.R b) =+ state.R a) state.DM))

||#

(defun-struct dfn-storedm (((func (type-funct func))
                            (shift (type-shiftt shift))
                            (skip (type-conditiont skip))
                            (w (unsigned-byte-p 7 w))
                            (a (unsigned-byte-p 7 a))
                            (b (unsigned-byte-p 7 b)))
                           st$)
  (declare (xargs :stobjs st$))
  (let ((st$ (update-dmi (cast ((unsigned-byte 32) (unsigned-byte 10))
                               (ri b st$))
                         (ri a st$)
                         st$)))
    (norm (tuple func shift skip (true) (false) w a b) st$)))

#||

define StoreIM (func::funcT, shift::shiftT, skip::conditionT,
                w::regT, a::regT, b::regT) =
{
   IM([R(b)]) <- R(a);
   norm (func, shift, skip, true, false, w, a, b)
}

||#

(defun-struct dfn-storeim (((func (type-funct func))
                            (shift (type-shiftt shift))
                            (skip (type-conditiont skip))
                            (w (unsigned-byte-p 7 w))
                            (a (unsigned-byte-p 7 a))
                            (b (unsigned-byte-p 7 b)))
                           st$)
  (declare (xargs :stobjs st$))
  (let ((st$ (update-imi (cast ((unsigned-byte 32) (unsigned-byte 10))
                               (ri b st$))
                         (ri a st$)
                         st$)))
    (norm (tuple func shift skip (true) (false) w a b)
          st$)))

#||

define Out (func::funcT, shift::shiftT, skip::conditionT,
            w::regT, a::regT, b::regT) =
   norm (func, shift, skip, true, true, w, a, b)
||#

(defun-struct dfn-out (((func (type-funct func))
                        (shift (type-shiftt shift))
                        (skip (type-conditiont skip))
                        (w (unsigned-byte-p 7 w))
                        (a (unsigned-byte-p 7 a))
                        (b (unsigned-byte-p 7 b)))
                       st$)
  (declare (xargs :stobjs st$))
  (norm (tuple func shift skip (true) (true) w a b)
        st$))

#||
define LoadDM (func::funcT, shift::shiftT, skip::conditionT,
               w::regT, a::regT, b::regT) =
{
   R(w) <- DM([R(b)]);
   norm (func, shift, skip, false, false, w, a, b)
}
||#

(defthm dmp-yields-unsigned-byte-p-32
  (implies (and (dmp x)
                (natp a)
                (< a (len x)))
           (unsigned-byte-p 32 (nth a x)))
  :rule-classes ((:rewrite
                  :corollary
                  (implies (and (dmp x)
                                (natp a)
                                (< a (len x)))
                           (unsigned-byte-p 32 (nth a x))))
                 (:type-prescription
                  :corollary
                  (implies (and (dmp x)
                                (natp a)
                                (< a (len x)))
                           (integerp (nth a x))))))

(defun-struct dfn-loaddm (((func (type-funct func))
                           (shift (type-shiftt shift))
                           (skip (type-conditiont skip))
                           (w (unsigned-byte-p 7 w))
                           (a (unsigned-byte-p 7 a))
                           (b (unsigned-byte-p 7 b)))
                          st$)
  (declare (xargs :stobjs st$))
  (let ((st$ (update-ri w
                        (dmi (cast ((unsigned-byte 32) (unsigned-byte 10))
                                   (ri b st$))
                             st$)
                        st$)))
    (norm (tuple func shift skip (false) (false) w a b)
          st$)))

#||
define In (func::funcT, shift::shiftT, skip::conditionT,
           w::regT, a::regT, b::regT) =
{
   R(w) <- InData;
   norm (func, shift, skip, false, false, w, a, b)
}
||#

(defun-struct dfn-in (((func (type-funct func))
                       (shift (type-shiftt shift))
                       (skip (type-conditiont skip))
                       (w (unsigned-byte-p 7 w))
                       (a (unsigned-byte-p 7 a))
                       (b (unsigned-byte-p 7 b)))
                      st$)
  (declare (xargs :stobjs st$))
  (let ((st$ (update-ri w (indata st$) st$)))
    (norm (tuple func shift skip (false) (false) w a b)
          st$)))

#||
define Jump (func::funcT, shift::shiftT, w::regT, a::regT, b::regT) =
{
   R(w) <- ZeroExtend (PC + 1);
   PC <- [ALU (func, shift, R(a), R(b))]
}

val dfn'Jump_def = Def
  ("dfn'Jump",
   TP[Var("func",CTy"funcT"), Var("shift",CTy"shiftT"), Var("w",FTy 7),
      Var("a",FTy 7), Var("b",FTy 7)],
   Close
     (qVar"state",
      Let
        (qVar"s",
         Rupd
           ("R",
            TP[qVar"state",
               Fupd
                 (Dest("R",ATy(FTy 7,F32),qVar"state"),Var("w",FTy 7),
                  Mop
                    (Cast(F32),
                     Bop(Add,Dest("PC",FTy 10,qVar"state"),LW(1,10))))]),
         Let
           (TP[Var("v",FTy 10), qVar"s"],
            Let
              (TP[Var("v",F32), qVar"s"],
               Apply
                 (Call
                    ("ALU",ATy(qTy,PTy(F32,qTy)),
                     TP[Var("func",CTy"funcT"), Var("shift",CTy"shiftT"),
                        Apply
                          (Dest("R",ATy(FTy 7,F32),qVar"s"),
                           Var("a",FTy 7)),
                        Apply
                          (Dest("R",ATy(FTy 7,F32),qVar"s"),
                           Var("b",FTy 7))]),qVar"s"),
               TP[Mop(Cast(FTy 10),Var("v",F32)), qVar"s"]),
            TP[LU, Rupd("PC",TP[qVar"s", Var("v",FTy 10)])]))))
;
||#

(defun-struct dfn-jump (((func (type-funct func))
                         (shift (type-shiftt shift))
                         (w (unsigned-byte-p 7 w))
                         (a (unsigned-byte-p 7 a))
                         (b (unsigned-byte-p 7 b)))
                        st$)
  (declare (xargs :stobjs st$))
  (let ((st$ (update-ri w
                        (cast ((unsigned-byte 10) (unsigned-byte 32))
                              (n+ 10 (pctr st$) 1))
                        st$)))
    (mv-let (v st$)
            (mv-let (v st$)
                    (alu (tuple func shift (ri a st$) (ri b st$))
                         st$)
                    (mv (cast ((unsigned-byte 32) (unsigned-byte 10))
                              v)
                        st$))
            (let ((st$ (update-pctr v st$)))
              (mv (unit-value) st$)))))

#||
define LoadConstant (w::regT, imm::immT) =
{
   R(w) <- ZeroExtend (imm);
   PC <- PC + 1
}
||#

(defun-struct dfn-loadconstant (((w (unsigned-byte-p 7 w))
                                 (imm (unsigned-byte-p 24 imm)))
                                st$)
  (declare (xargs :stobjs st$))
  (let* ((st$ (update-ri w
                         (cast ((unsigned-byte 24) (unsigned-byte 32))
                               imm)
                         st$))
         (st$ (update-pctr (n+ 10 (pctr st$) 1) st$)))
    (mv (unit-value) st$)))

#||
define ReservedInstr = #Reserved

(Def "dfn'ReservedInstr" qVar"state"
  (Apply
    (Call "raise'exception" (ATy qTy (PTy uTy qTy))
      (LC "Reserved" CTy"exception")) qVar"state"))

||#

(defun-struct dfn-reservedinstr (st$)
  (declare (xargs :stobjs st$))
  (raise-exception 'reserved
                   (arb uty)
                   st$))

(construct instruction
           ((in (funct shiftt conditiont
                       (unsigned-byte 7)
                       (unsigned-byte 7)
                       (unsigned-byte 7)))
            (jump (funct shiftt
                         (unsigned-byte 7)
                         (unsigned-byte 7)
                         (unsigned-byte 7)))
            (loadconstant ((unsigned-byte 7)
                           (unsigned-byte 24)))
            (loaddm (funct shiftt conditiont
                           (unsigned-byte 7)
                           (unsigned-byte 7)
                           (unsigned-byte 7)))
            (normal (funct shiftt conditiont
                           (unsigned-byte 7)
                           (unsigned-byte 7)
                           (unsigned-byte 7)))
            (out (funct shiftt conditiont
                        (unsigned-byte 7)
                        (unsigned-byte 7)
                        (unsigned-byte 7)))
            reservedinstr
            (storedm (funct shiftt conditiont
                            (unsigned-byte 7)
                            (unsigned-byte 7)
                            (unsigned-byte 7)))
            (storeim (funct shiftt conditiont
                            (unsigned-byte 7)
                            (unsigned-byte 7)
                            (unsigned-byte 7)))))

#||
define Run

val Run_def = Def
  ("Run",Var("v0",CTy"instruction"),
   Close
     (qVar"state",
      CS
        (Var("v0",CTy"instruction"),
         [(Const("ReservedInstr",CTy"instruction"),
           Apply
             (Const("dfn'ReservedInstr",ATy(qTy,PTy(uTy,qTy))),
              qVar"state")),
          (Call
             ("In",CTy"instruction",
              Var
                ("v1",
                 PTy
                   (CTy"funcT",
                    PTy
                      (CTy"shiftT",
                       PTy(CTy"conditionT",PTy(FTy 7,PTy(FTy 7,FTy 7))))))),
           Apply
             (Call
                ("dfn'In",ATy(qTy,PTy(uTy,qTy)),
                 Var
                   ("v1",
                    PTy
                      (CTy"funcT",
                       PTy
                         (CTy"shiftT",
                          PTy(CTy"conditionT",PTy(FTy 7,PTy(FTy 7,FTy 7))))))),
              qVar"state")),
          (Call
             ("Jump",CTy"instruction",
              Var
                ("v2",
                 PTy
                   (CTy"funcT",
                    PTy(CTy"shiftT",PTy(FTy 7,PTy(FTy 7,FTy 7)))))),
           Apply
             (Call
                ("dfn'Jump",ATy(qTy,PTy(uTy,qTy)),
                 Var
                   ("v2",
                    PTy
                      (CTy"funcT",
                       PTy(CTy"shiftT",PTy(FTy 7,PTy(FTy 7,FTy 7)))))),
              qVar"state")),
          (Call
             ("LoadConstant",CTy"instruction",Var("v3",PTy(FTy 7,FTy 24))),
           Apply
             (Call
                ("dfn'LoadConstant",ATy(qTy,PTy(uTy,qTy)),
                 Var("v3",PTy(FTy 7,FTy 24))),qVar"state")),
          (Call
             ("LoadDM",CTy"instruction",
              Var
                ("v4",
                 PTy
                   (CTy"funcT",
                    PTy
                      (CTy"shiftT",
                       PTy(CTy"conditionT",PTy(FTy 7,PTy(FTy 7,FTy 7))))))),
           Apply
             (Call
                ("dfn'LoadDM",ATy(qTy,PTy(uTy,qTy)),
                 Var
                   ("v4",
                    PTy
                      (CTy"funcT",
                       PTy
                         (CTy"shiftT",
                          PTy(CTy"conditionT",PTy(FTy 7,PTy(FTy 7,FTy 7))))))),
              qVar"state")),
          (Call
             ("Normal",CTy"instruction",
              Var
                ("v5",
                 PTy
                   (CTy"funcT",
                    PTy
                      (CTy"shiftT",
                       PTy(CTy"conditionT",PTy(FTy 7,PTy(FTy 7,FTy 7))))))),
           Apply
             (Call
                ("dfn'Normal",ATy(qTy,PTy(uTy,qTy)),
                 Var
                   ("v5",
                    PTy
                      (CTy"funcT",
                       PTy
                         (CTy"shiftT",
                          PTy(CTy"conditionT",PTy(FTy 7,PTy(FTy 7,FTy 7))))))),
              qVar"state")),
          (Call
             ("Out",CTy"instruction",
              Var
                ("v6",
                 PTy
                   (CTy"funcT",
                    PTy
                      (CTy"shiftT",
                       PTy(CTy"conditionT",PTy(FTy 7,PTy(FTy 7,FTy 7))))))),
           Apply
             (Call
                ("dfn'Out",ATy(qTy,PTy(uTy,qTy)),
                 Var
                   ("v6",
                    PTy
                      (CTy"funcT",
                       PTy
                         (CTy"shiftT",
                          PTy(CTy"conditionT",PTy(FTy 7,PTy(FTy 7,FTy 7))))))),
              qVar"state")),
          (Call
             ("StoreDM",CTy"instruction",
              Var
                ("v7",
                 PTy
                   (CTy"funcT",
                    PTy
                      (CTy"shiftT",
                       PTy(CTy"conditionT",PTy(FTy 7,PTy(FTy 7,FTy 7))))))),
           Apply
             (Call
                ("dfn'StoreDM",ATy(qTy,PTy(uTy,qTy)),
                 Var
                   ("v7",
                    PTy
                      (CTy"funcT",
                       PTy
                         (CTy"shiftT",
                          PTy(CTy"conditionT",PTy(FTy 7,PTy(FTy 7,FTy 7))))))),
              qVar"state")),
          (Call
             ("StoreIM",CTy"instruction",
              Var
                ("v8",
                 PTy
                   (CTy"funcT",
                    PTy
                      (CTy"shiftT",
                       PTy(CTy"conditionT",PTy(FTy 7,PTy(FTy 7,FTy 7))))))),
           Apply
             (Call
                ("dfn'StoreIM",ATy(qTy,PTy(uTy,qTy)),
                 Var
                   ("v8",
                    PTy
                      (CTy"funcT",
                       PTy
                         (CTy"shiftT",
                          PTy(CTy"conditionT",PTy(FTy 7,PTy(FTy 7,FTy 7))))))),
              qVar"state"))])))
;

   [Run_def]  Definition

      |-  v0.
           Run v0 =
           ( state.
              case v0 of
                In v1 => dfn'In v1 state
              | Jump v2 => dfn'Jump v2 state
              | LoadConstant v3 => dfn'LoadConstant v3 state
              | LoadDM v4 => dfn'LoadDM v4 state
              | Normal v5 => dfn'Normal v5 state
              | Out v6 => dfn'Out v6 state
              | ReservedInstr => dfn'ReservedInstr state
              | StoreDM v7 => dfn'StoreDM v7 state
              | StoreIM v8 => dfn'StoreIM v8 state)
||#

(defun-struct run ((v0 (type-instruction v0))
                   st$)
  (declare (xargs :stobjs st$))
  (case-match+
   v0
   ('reservedinstr (dfn-reservedinstr st$))
   (('in v1) (dfn-in v1 st$))
   (('jump v2) (dfn-jump v2 st$))
   (('loadconstant v3) (dfn-loadconstant v3 st$))
   (('loaddm v4) (dfn-loaddm v4 st$))
   (('normal v5) (dfn-normal v5 st$))
   (('out v6) (dfn-out v6 st$))
   (('storedm v7) (dfn-storedm v7 st$))
   (('storeim v8) (dfn-storeim v8 st$))
   (& (impossible (mv (arb uty) st$)))))

#||

---------------------------------------------
-- Decode
---------------------------------------------

instruction Decode (opc::wordT) =
   match opc
   {
      case 'Rw 1 imm`24' => LoadConstant (Rw, imm)
      case 'Rw 0 Ra Rb Function Shift Skip Op' =>
         {
            func  = [Function :: bits(3)] :: funcT;
            shift = [Shift :: bits(2)] :: shiftT;
            skip  = [Skip :: bits(2)] :: conditionT;
            match Op
            {
               case 0 => Normal (func, shift, skip, Rw, Ra, Rb)
               case 1 => StoreDM (func, shift, skip, Rw, Ra, Rb)
               case 2 => StoreIM (func, shift, skip, Rw, Ra, Rb)
               case 3 => Out (func, shift, skip, Rw, Ra, Rb)
               case 4 => LoadDM (func, shift, skip, Rw, Ra, Rb)
               case 5 => In (func, shift, skip, Rw, Ra, Rb)
               case 6 => Jump (func, shift, Rw, Ra, Rb)
               case 7 => ReservedInstr
            }
         }
   }

val Decode_def = Def
  ("Decode",Var("opc",F32),
   Let
     (TP[bVar"b'31", bVar"b'30", bVar"b'29", bVar"b'28", bVar"b'27",
         bVar"b'26", bVar"b'25", bVar"b'24", bVar"b'23", bVar"b'22",
         bVar"b'21", bVar"b'20", bVar"b'19", bVar"b'18", bVar"b'17",
         bVar"b'16", bVar"b'15", bVar"b'14", bVar"b'13", bVar"b'12",
         bVar"b'11", bVar"b'10", bVar"b'9", bVar"b'8", bVar"b'7",
         bVar"b'6", bVar"b'5", bVar"b'4", bVar"b'3", bVar"b'2", bVar"b'1",
         bVar"b'0"],BL(32,Var("opc",F32)),
      ITE
        (bVar"b'24",
         Call
           ("LoadConstant",CTy"instruction",
            TP[EX(Var("opc",F32),LN 31,LN 25,FTy 7),
               EX(Var("opc",F32),LN 23,LN 0,FTy 24)]),
         Let
           (Var("Rw",FTy 7),EX(Var("opc",F32),LN 31,LN 25,FTy 7),
            Let
              (Var("Rb",FTy 7),EX(Var("opc",F32),LN 16,LN 10,FTy 7),
               Let
                 (Var("Ra",FTy 7),EX(Var("opc",F32),LN 23,LN 17,FTy 7),
                  Let
                    (Var("func",CTy"funcT"),
                     Mop
                       (Cast(CTy"funcT"),
                        EX(Var("opc",F32),LN 9,LN 7,FTy 3)),
                     Let
                       (Var("shift",CTy"shiftT"),
                        Mop
                          (Cast(CTy"shiftT"),
                           EX(Var("opc",F32),LN 6,LN 5,FTy 2)),
                        Let
                          (Var("skip",CTy"conditionT"),
                           Mop
                             (Cast(CTy"conditionT"),
                              EX(Var("opc",F32),LN 4,LN 3,FTy 2)),
                           CS
                             (EX(Var("opc",F32),LN 2,LN 0,FTy 3),
                              [(LW(0,3),
                                Call
                                  ("Normal",CTy"instruction",
                                   TP[Var("func",CTy"funcT"),
                                      Var("shift",CTy"shiftT"),
                                      Var("skip",CTy"conditionT"),
                                      Var("Rw",FTy 7), Var("Ra",FTy 7),
                                      Var("Rb",FTy 7)])),
                               (LW(1,3),
                                Call
                                  ("StoreDM",CTy"instruction",
                                   TP[Var("func",CTy"funcT"),
                                      Var("shift",CTy"shiftT"),
                                      Var("skip",CTy"conditionT"),
                                      Var("Rw",FTy 7), Var("Ra",FTy 7),
                                      Var("Rb",FTy 7)])),
                               (LW(2,3),
                                Call
                                  ("StoreIM",CTy"instruction",
                                   TP[Var("func",CTy"funcT"),
                                      Var("shift",CTy"shiftT"),
                                      Var("skip",CTy"conditionT"),
                                      Var("Rw",FTy 7), Var("Ra",FTy 7),
                                      Var("Rb",FTy 7)])),
                               (LW(3,3),
                                Call
                                  ("Out",CTy"instruction",
                                   TP[Var("func",CTy"funcT"),
                                      Var("shift",CTy"shiftT"),
                                      Var("skip",CTy"conditionT"),
                                      Var("Rw",FTy 7), Var("Ra",FTy 7),
                                      Var("Rb",FTy 7)])),
                               (LW(4,3),
                                Call
                                  ("LoadDM",CTy"instruction",
                                   TP[Var("func",CTy"funcT"),
                                      Var("shift",CTy"shiftT"),
                                      Var("skip",CTy"conditionT"),
                                      Var("Rw",FTy 7), Var("Ra",FTy 7),
                                      Var("Rb",FTy 7)])),
                               (LW(5,3),
                                Call
                                  ("In",CTy"instruction",
                                   TP[Var("func",CTy"funcT"),
                                      Var("shift",CTy"shiftT"),
                                      Var("skip",CTy"conditionT"),
                                      Var("Rw",FTy 7), Var("Ra",FTy 7),
                                      Var("Rb",FTy 7)])),
                               (LW(6,3),
                                Call
                                  ("Jump",CTy"instruction",
                                   TP[Var("func",CTy"funcT"),
                                      Var("shift",CTy"shiftT"),
                                      Var("Rw",FTy 7), Var("Ra",FTy 7),
                                      Var("Rb",FTy 7)])),
                               (LW(7,3),
                                Const("ReservedInstr",CTy"instruction"))]))))))))))
;

   [Decode_def]  Definition

      |-  opc.
           Decode opc =
           (let (b'31,b'30,b'29,b'28,b'27,b'26,b'25,b'24,b'23,b'22,b'21,
                 b'20,b'19,b'18,b'17,b'16,b'15,b'14,b'13,b'12,b'11,b'10,
                 b'9,b'8,b'7,b'6,b'5,b'4,b'3,b'2,b'1,b'0) = boolify32 opc
            in
              if b'24 then LoadConstant ((31 >< 25) opc,(23 >< 0) opc)
              else
                (let Rw = (31 >< 25) opc in
                 let Rb = (16 >< 10) opc in
                 let Ra = (23 >< 17) opc in
                 let func = num2funcT (w2n ((9 >< 7) opc)) in
                 let shift = num2shiftT (w2n ((6 >< 5) opc)) in
                 let skip = num2conditionT (w2n ((4 >< 3) opc))
                 in
                   case (2 >< 0) opc of
                     0w => Normal (func,shift,skip,Rw,Ra,Rb)
                   | 1w => StoreDM (func,shift,skip,Rw,Ra,Rb)
                   | 2w => StoreIM (func,shift,skip,Rw,Ra,Rb)
                   | 3w => Out (func,shift,skip,Rw,Ra,Rb)
                   | 4w => LoadDM (func,shift,skip,Rw,Ra,Rb)
                   | 5w => In (func,shift,skip,Rw,Ra,Rb)
                   | 6w => Jump (func,shift,Rw,Ra,Rb)
                   | 7w => ReservedInstr
                   | v => ARB))

||#

; !! Generate the following automatically, based on case-match+ expressions that
; are encountered.
(defthm bits-diff-2-forward
  (implies (and (natp i)
                (natp j)
                (equal (- i j) 2))
           (or (equal (bits x i j) 0)
               (equal (bits x i j) 1)
               (equal (bits x i j) 2)
               (equal (bits x i j) 3)
               (equal (bits x i j) 4)
               (equal (bits x i j) 5)
               (equal (bits x i j) 6)
               (equal (bits x i j) 7)))
  :rule-classes ((:forward-chaining
                  :trigger-terms
                  ((bits x i j))))
  :hints (("Goal" :in-theory (enable bits))))

(defun-struct decode ((opc (unsigned-byte-p 32 opc)))
  (mv-let-ignorable
   (b-31 b-30 b-29 b-28 b-27 b-26
         b-25 b-24 b-23 b-22 b-21 b-20 b-19 b-18
         b-17 b-16 b-15 b-14 b-13 b-12 b-11 b-10
         b-9 b-8 b-7 b-6 b-5 b-4 b-3 b-2 b-1 b-0)
   (bl 32 opc)
   (if b-24
       (call-constructor instruction loadconstant
                         (tuple (bits opc 31 25) (bits opc 23 0)))
     (let* ((rw (bits opc 31 25))
            (rb (bits opc 16 10))
            (ra (bits opc 23 17))
            (func (cast ((unsigned-byte 3) funct)
                        (bits opc 9 7)))
            (shift (cast ((unsigned-byte 2) shiftt)
                         (bits opc 6 5)))
            (skip (cast ((unsigned-byte 2) conditiont)
                        (bits opc 4 3))))
       (case-match+
        (bits opc 2 0)
        (0 (call-constructor instruction normal
                             (tuple func shift skip rw ra rb)))
        (1 (call-constructor instruction storedm
                             (tuple func shift skip rw ra rb)))
        (2 (call-constructor instruction storeim
                             (tuple func shift skip rw ra rb)))
        (3 (call-constructor instruction out
                             (tuple func shift skip rw ra rb)))
        (4 (call-constructor instruction loaddm
                             (tuple func shift skip rw ra rb)))
        (5 (call-constructor instruction in
                             (tuple func shift skip rw ra rb)))
        (6 (call-constructor instruction jump
                             (tuple func shift      rw ra rb)))
        (7 'reservedinstr)
        (& (impossible (arb instruction))))))))

#||

---------------------------------------------
-- Next State
---------------------------------------------

unit Next =
{
  i = Decode (IM (PC));
  when i <> ReservedInstr do Run (i)
}

val Next_def = Def
  ("Next",qVar"state",
   Let
     (Var("v",CTy"instruction"),
      Call
        ("Decode",CTy"instruction",
         Apply
           (Dest("IM",ATy(FTy 10,F32),qVar"state"),
            Dest("PC",FTy 10,qVar"state"))),
      ITE
        (Mop
           (Not,
            EQ
              (Var("v",CTy"instruction"),
               Const("ReservedInstr",CTy"instruction"))),
         Apply
           (Call("Run",ATy(qTy,PTy(uTy,qTy)),Var("v",CTy"instruction")),
            qVar"state"),TP[LU, qVar"state"])))
;

   [Next_def]  Definition

      |-  state.
           Next state =
           (let v = Decode (state.IM state.PC)
            in
              if v   ReservedInstr then Run v state else ((),state))

||#

(defthm type-instruction-in
  (implies (force (and (type-funct func)
                       (type-shiftt shift)
                       (type-conditiont skip)
                       (unsigned-byte-p 7 rw)
                       (unsigned-byte-p 7 ra)
                       (unsigned-byte-p 7 rb)))
           (type-instruction
            (tuple 'in (tuple func shift skip rw ra rb)))))

(defthm type-instruction-jump
  (implies (force (and (type-funct func)
                       (type-shiftt shift)
                       (unsigned-byte-p 7 rw)
                       (unsigned-byte-p 7 ra)
                       (unsigned-byte-p 7 rb)))
           (type-instruction
            (tuple 'jump (tuple func shift rw ra rb)))))

(defthm type-instruction-loadconstant
  (implies (force (and (unsigned-byte-p 7 rw)
                       (unsigned-byte-p 24 imm)))
           (type-instruction (tuple 'loadconstant (tuple rw imm)))))

(defthm type-instruction-loaddm
  (implies (force (and (type-funct func)
                       (type-shiftt shift)
                       (type-conditiont skip)
                       (unsigned-byte-p 7 rw)
                       (unsigned-byte-p 7 ra)
                       (unsigned-byte-p 7 rb)))
           (type-instruction
            (tuple 'loaddm (tuple func shift skip rw ra rb)))))

(defthm type-instruction-normal
  (implies (force (and (type-funct func)
                       (type-shiftt shift)
                       (type-conditiont skip)
                       (unsigned-byte-p 7 rw)
                       (unsigned-byte-p 7 ra)
                       (unsigned-byte-p 7 rb)))
           (type-instruction
            (tuple 'normal (tuple func shift skip rw ra rb)))))

(defthm type-instruction-out
  (implies (force (and (type-funct func)
                       (type-shiftt shift)
                       (type-conditiont skip)
                       (unsigned-byte-p 7 rw)
                       (unsigned-byte-p 7 ra)
                       (unsigned-byte-p 7 rb)))
           (type-instruction
            (tuple 'out (tuple func shift skip rw ra rb)))))

(defthm type-instruction-storedm
  (implies (force (and (type-funct func)
                       (type-shiftt shift)
                       (type-conditiont skip)
                       (unsigned-byte-p 7 rw)
                       (unsigned-byte-p 7 ra)
                       (unsigned-byte-p 7 rb)))
           (type-instruction
            (tuple 'storedm (tuple func shift skip rw ra rb)))))

(defthm type-instruction-storeim
  (implies (force (and (type-funct func)
                       (type-shiftt shift)
                       (type-conditiont skip)
                       (unsigned-byte-p 7 rw)
                       (unsigned-byte-p 7 ra)
                       (unsigned-byte-p 7 rb)))
           (type-instruction
            (tuple 'storeim (tuple func shift skip rw ra rb)))))

(in-theory (disable type-instruction))

(defthm imp-yields-unsigned-byte-p-32
  (implies (and (imp x)
                (natp a)
                (< a (len x)))
           (unsigned-byte-p 32 (nth a x)))
  :rule-classes ((:rewrite
                  :corollary
                  (implies (and (imp x)
                                (natp a)
                                (< a (len x)))
                           (unsigned-byte-p 32 (nth a x))))
                 (:type-prescription
                  :corollary
                  (implies (and (imp x)
                                (natp a)
                                (< a (len x)))
                           (integerp (nth a x))))))

; !! Generate the following automatically, based on case-match+ expressions that
; are encountered.
(defthm bits-diff-1-forward
  (implies (and (natp i)
                (natp j)
                (equal (- i j) 1))
           (or (equal (bits x i j) 0)
               (equal (bits x i j) 1)
               (equal (bits x i j) 2)
               (equal (bits x i j) 3)))
  :rule-classes ((:forward-chaining
                  :trigger-terms
                  ((bits x i j))))
  :hints (("Goal" :in-theory (enable bits))))

; !! Perhaps should only be used with some sort of staged simplification, e.g.,
; after stable-under-simplification.
(defthm nth-bits-diff-1-open
  (implies (and (syntaxp (quotep i))
                (syntaxp (quotep j))
                (natp i)
                (natp j)
                (equal (- i j) 1))
           (equal (nth (bits x i j) (list* a0 a1 a2 a3 tail))
                  (case (bits x i j)
                    (0 a0)
                    (1 a1)
                    (2 a2)
                    (otherwise a3))))
  :hints (("Goal" :use bits-diff-1-forward)))

(defun-struct next (st$)
  (declare (xargs :stobjs st$))
  (let ((v (decode (imi (pctr st$) st$))))
    (if (not (eq v 'reservedinstr))
        (run v st$)
      (mv (unit-value) st$))))

#||
---------------------------------------------
-- Encode
---------------------------------------------

wordT enc
  (args::funcT * shiftT * conditionT * regT * regT * regT, opc::bits(3)) =
{
   func, shift, skip, w, a, b = args;
   return (w : '0' : a : b : [func]`3 : [shift]`2 : [skip]`2 : opc)
}

val enc_def = Def
  ("enc",
   TP[Var
        ("args",
         PTy
           (CTy"funcT",
            PTy
              (CTy"shiftT",
               PTy(CTy"conditionT",PTy(FTy 7,PTy(FTy 7,FTy 7)))))),
      Var("opc",FTy 3)],
   Let
     (TP[Var("func",CTy"funcT"), Var("shift",CTy"shiftT"),
         Var("skip",CTy"conditionT"), Var("w",FTy 7), Var("a",FTy 7),
         Var("b",FTy 7)],
      Var
        ("args",
         PTy
           (CTy"funcT",
            PTy
              (CTy"shiftT",
               PTy(CTy"conditionT",PTy(FTy 7,PTy(FTy 7,FTy 7)))))),
      CC[Var("w",FTy 7), LW(0,1), Var("a",FTy 7), Var("b",FTy 7),
         Mop(Cast(FTy 3),Var("func",CTy"funcT")),
         Mop(Cast(FTy 2),Var("shift",CTy"shiftT")),
         Mop(Cast(FTy 2),Var("skip",CTy"conditionT")), Var("opc",FTy 3)]))
;

   [enc_def]  Definition

      |-  args opc.
           enc (args,opc) =
           (let (func,shift,skip,w,a,b) = args
            in
              w @@ 0w @@ a @@ b @@ n2w (funcT2num func) @@
              n2w (shiftT2num shift) @@ n2w (conditionT2num skip) @@ opc)


||#

(defun-struct enc (((args (slet (x0 x1 x2 x3 x4 x5)
                                args
                                (and (type-funct x0)
                                     (type-shiftt x1)
                                     (type-conditiont x2)
                                     (unsigned-byte-p 7 x3)
                                     (unsigned-byte-p 7 x4)
                                     (unsigned-byte-p 7 x5))
                                nil
                                nil))
                    (opc (unsigned-byte-p 3 opc))))
  (slet (func shift skip w a b)
        args
        (cat w 7
             0 1
             a 7
             b 7
             (cast (funct (unsigned-byte 3)) func) 3
             (cast (shiftt (unsigned-byte 2)) shift) 2
             (cast (conditiont (unsigned-byte 2)) skip) 2
             opc 3)))

#||
wordT Encode (i::instruction) =
   match i
   {
      case LoadConstant (Rw, imm) => Rw : '1' : imm
      case Normal (args)  => enc (args, '000')
      case StoreDM (args) => enc (args, '001')
      case StoreIM (args) => enc (args, '010')
      case Out (args)     => enc (args, '011')
      case LoadDM (args)  => enc (args, '100')
      case In (args)      => enc (args, '101')
      case Jump (func, shift, Rw, Ra, Rb) =>
         enc ((func, shift, skipNever, Rw, Ra, Rb), '110')
      case ReservedInstr => 0b111
   }

val Encode_def = Def
  ("Encode",Var("i",CTy"instruction"),
   CS
     (Var("i",CTy"instruction"),
      [(Call
          ("LoadConstant",CTy"instruction",
           TP[Var("Rw",FTy 7), Var("imm",FTy 24)]),
        CC[Var("Rw",FTy 7), LW(1,1), Var("imm",FTy 24)]),
       (Call
          ("Normal",CTy"instruction",
           Var
             ("args",
              PTy
                (CTy"funcT",
                 PTy
                   (CTy"shiftT",
                    PTy(CTy"conditionT",PTy(FTy 7,PTy(FTy 7,FTy 7))))))),
        Call
          ("enc",F32,
           TP[Var
                ("args",
                 PTy
                   (CTy"funcT",
                    PTy
                      (CTy"shiftT",
                       PTy(CTy"conditionT",PTy(FTy 7,PTy(FTy 7,FTy 7)))))),
              LW(0,3)])),
       (Call
          ("StoreDM",CTy"instruction",
           Var
             ("args",
              PTy
                (CTy"funcT",
                 PTy
                   (CTy"shiftT",
                    PTy(CTy"conditionT",PTy(FTy 7,PTy(FTy 7,FTy 7))))))),
        Call
          ("enc",F32,
           TP[Var
                ("args",
                 PTy
                   (CTy"funcT",
                    PTy
                      (CTy"shiftT",
                       PTy(CTy"conditionT",PTy(FTy 7,PTy(FTy 7,FTy 7)))))),
              LW(1,3)])),
       (Call
          ("StoreIM",CTy"instruction",
           Var
             ("args",
              PTy
                (CTy"funcT",
                 PTy
                   (CTy"shiftT",
                    PTy(CTy"conditionT",PTy(FTy 7,PTy(FTy 7,FTy 7))))))),
        Call
          ("enc",F32,
           TP[Var
                ("args",
                 PTy
                   (CTy"funcT",
                    PTy
                      (CTy"shiftT",
                       PTy(CTy"conditionT",PTy(FTy 7,PTy(FTy 7,FTy 7)))))),
              LW(2,3)])),
       (Call
          ("Out",CTy"instruction",
           Var
             ("args",
              PTy
                (CTy"funcT",
                 PTy
                   (CTy"shiftT",
                    PTy(CTy"conditionT",PTy(FTy 7,PTy(FTy 7,FTy 7))))))),
        Call
          ("enc",F32,
           TP[Var
                ("args",
                 PTy
                   (CTy"funcT",
                    PTy
                      (CTy"shiftT",
                       PTy(CTy"conditionT",PTy(FTy 7,PTy(FTy 7,FTy 7)))))),
              LW(3,3)])),
       (Call
          ("LoadDM",CTy"instruction",
           Var
             ("args",
              PTy
                (CTy"funcT",
                 PTy
                   (CTy"shiftT",
                    PTy(CTy"conditionT",PTy(FTy 7,PTy(FTy 7,FTy 7))))))),
        Call
          ("enc",F32,
           TP[Var
                ("args",
                 PTy
                   (CTy"funcT",
                    PTy
                      (CTy"shiftT",
                       PTy(CTy"conditionT",PTy(FTy 7,PTy(FTy 7,FTy 7)))))),
              LW(4,3)])),
       (Call
          ("In",CTy"instruction",
           Var
             ("args",
              PTy
                (CTy"funcT",
                 PTy
                   (CTy"shiftT",
                    PTy(CTy"conditionT",PTy(FTy 7,PTy(FTy 7,FTy 7))))))),
        Call
          ("enc",F32,
           TP[Var
                ("args",
                 PTy
                   (CTy"funcT",
                    PTy
                      (CTy"shiftT",
                       PTy(CTy"conditionT",PTy(FTy 7,PTy(FTy 7,FTy 7)))))),
              LW(5,3)])),
       (Call
          ("Jump",CTy"instruction",
           TP[Var("func",CTy"funcT"), Var("shift",CTy"shiftT"),
              Var("Rw",FTy 7), Var("Ra",FTy 7), Var("Rb",FTy 7)]),
        Call
          ("enc",F32,
           TP[TP[Var("func",CTy"funcT"), Var("shift",CTy"shiftT"),
                 LC("skipNever",CTy"conditionT"), Var("Rw",FTy 7),
                 Var("Ra",FTy 7), Var("Rb",FTy 7)], LW(6,3)])),
       (Const("ReservedInstr",CTy"instruction"),LW(7,32))]))
;

   [Encode_def]  Definition

      |-  i.
           Encode i =
           case i of
             In args_5 => enc (args_5,5w)
           | Jump (func,shift,Rw_1,Ra,Rb) =>
               enc ((func,shift,skipNever,Rw_1,Ra,Rb),6w)
           | LoadConstant (Rw,imm) => Rw @@ 1w @@ imm
           | LoadDM args_4 => enc (args_4,4w)
           | Normal args => enc (args,0w)
           | Out args_3 => enc (args_3,3w)
           | ReservedInstr => 7w
           | StoreDM args_1 => enc (args_1,1w)
           | StoreIM args_2 => enc (args_2,2w)

||#

; !! Think about eliminating in-theory hint by proving a suitable hierarchy of
; forward-chaining rules for our types.
(defun-struct encode ((i (type-instruction i)))
  (declare (xargs :guard-hints
                  (("Goal" :in-theory (enable type-instruction)))))
  (case-match+
   i
   (('loadconstant (rw imm))
    (cat rw 7 1 1 imm 24))
   (('normal args)  (enc (tuple args 0)))
   (('storedm args) (enc (tuple args 1)))
   (('storeim args) (enc (tuple args 2)))
   (('out args)     (enc (tuple args 3)))
   (('loaddm args)  (enc (tuple args 4)))
   (('in args)      (enc (tuple args 5)))
   (('jump (func shift Rw Ra Rb))
    (enc (tuple (tuple func shift 'skipNever Rw Ra Rb) 6)))
   ('ReservedInstr 7)
   (& (impossible (arb (unsigned-byte 32))))))

#||
---------------------------------------------
-- Load into Instruction Memory
---------------------------------------------

unit LoadIM (a::addrT, i::instruction list) measure Length (i) =
   match i
   {
      case Nil => nothing
      case Cons (h, t) =>
        {
           IM(a) <- Encode (h);
           LoadIM (a + 1, t)
        }
   }

val LoadIM_def = tDef
  ("LoadIM",TP[Var("a",FTy 10), Var("i",LTy(CTy"instruction"))],
   Close
     (qVar"state",
      CS
        (Var("i",LTy(CTy"instruction")),
         [(LNL(CTy"instruction"),TP[LU, qVar"state"]),
          (LLC([Var("h",CTy"instruction")],Var("t",LTy(CTy"instruction"))),
           Apply
             (Call
                ("LoadIM",ATy(qTy,PTy(uTy,qTy)),
                 TP[Bop(Add,Var("a",FTy 10),LW(1,10)),
                    Var("t",LTy(CTy"instruction"))]),
              Rupd
                ("IM",
                 TP[qVar"state",
                    Fupd
                      (Dest("IM",ATy(FTy 10,F32),qVar"state"),
                       Var("a",FTy 10),
                       Call("Encode",F32,Var("h",CTy"instruction")))])))])),
   Close
     (Var("x",PTy(PTy(FTy 10,LTy(CTy"instruction")),qTy)),
      CS
        (Var("x",PTy(PTy(FTy 10,LTy(CTy"instruction")),qTy)),
         [(TP[TP[Var("a",FTy 10), Var("i",LTy(CTy"instruction"))],
              AVar(qTy)],Mop(Length,Var("i",LTy(CTy"instruction"))))])))

   [LoadIM_curried_def]  Definition

      |-  x x1. LoadIM x x1 = LoadIM_tupled (x,x1)

   [LoadIM_tupled_primitive_def]  Definition

      |- LoadIM_tupled =
         WFREC
           (@R.
              WF R
               state a i h t.
                (i = h::t)
                R ((a + 1w,t),state with IM := (a =+ Encode h) state.IM)
                  ((a,i),state))
           ( LoadIM_tupled a'.
              case a' of
                ((a,i),state) =>
                  I
                    (case i of
                       [] => ((),state)
                     | h::t =>
                         LoadIM_tupled
                           ((a + 1w,t),
                            state with IM := (a =+ Encode h) state.IM)))

   [LoadIM_def]  Theorem

      |-  state i a.
           LoadIM (a,i) state =
           case i of
             [] => ((),state)
           | h::t =>
               LoadIM (a + 1w,t)
                 (state with IM := (a =+ Encode h) state.IM)


||#

; !! Think about how to deal with the following, which cuts the time to admit
; loadim from 78 seconds down to less than 1/10 second.  I made an attempt to
; start proving type theorems in tiny.lisp.10, but I stumbled at dfn-jump,
; maybe simply because I hadn't proved all necessary type theorems yet.
; As of tiny.lisp.13.good, at least, this book certifies with the following
; four events (two defthms, two in-theory events) commented out.
(defthm unsigned-byte-p-32-enc
  (unsigned-byte-p 32 (enc x)))
(in-theory (disable enc))
(defthm unsigned-byte-p-32-encode
  (unsigned-byte-p 32 (encode x)))
(in-theory (disable encode))

(defun-struct loadim (((a (unsigned-byte-p 10 a))
                       (i (type-instruction-list i)))
                      st$)
  :measure (len i)
  (declare (xargs :stobjs st$))
  (case-match+
   i
   ('nil (mv (unit-value) st$))
   ((h . t_var) (let ((st$ (update-imi a (encode h) st$)))
                  (loadim (tuple (n+ 10 a 1) t_var)
                          st$)))
   (& (impossible (mv (arb uty) st$)))))

#||
---------------------------------------------
-- Initialization & testing
---------------------------------------------

unit initialize (p::instruction list) =
{
   PC <- 0;
   R <- InitMap (0);
   DM <- InitMap (0);
   InRdy <- false;
   InData <- 0;
   OutStrobe <- 0;
   IM <- InitMap (Encode (ReservedInstr));
   LoadIM (0, p)
}

(Def "initialize" (Var "p" (LTy CTy"instruction"))
  (Close qVar"state"
    (Apply
      (Call "LoadIM" (ATy qTy (PTy uTy qTy))
        (TP (sqbkt (LW 0 10) (Var "p" (LTy CTy"instruction")))))
      (Rupd "IM"
        (TP
          (sqbkt (Rupd "OutStrobe"
                   (TP
                     (sqbkt (Rupd "InData"
                              (TP
                                (sqbkt (Rupd "InRdy"
                                         (TP
                                           (sqbkt (Rupd "DM"
                                                    (TP
                                                      (sqbkt (Rupd "R"
                                                               (TP
                                                                 (sqbkt (Rupd
                                                                          "PC"
                                                                          (TP
                                                                            (sqbkt qVar"state"
                                                                                   (LW
                                                                                     0
                                                                                     10))))
                                                                        (Mop
                                                                          (K1
                                                                            (FTy
                                                                              7))
                                                                          (LW
                                                                            0
                                                                            32)))))
                                                             (Mop
                                                               (K1
                                                                 (FTy 10))
                                                               (LW 0 32)))))
                                                  LF))) (LW 0 32))))
                            (LW 0 32))))
                 (Mop (K1 (FTy 10))
                   (Call "Encode" F32
                     (Const "ReservedInstr" CTy"instruction")))))))))

   [initialize_def]  Definition

      |-  p.
           initialize p =
           ( state.
              LoadIM (0w,p)
                (state with
                 <|IM := K (Encode ReservedInstr); OutStrobe := 0w;
                   InData := 0w; InRdy := F; DM := K 0w; R := K 0w;
                   PC := 0w|>))


||#

; Auto-generated the following (copied from out.lisp):
(DEFUN-STRUCT INITIALIZE
              ((P (TYPE-INSTRUCTION-LIST P)) ST$)
              (DECLARE (XARGS :STOBJS ST$))
              (LET ((ST$ (LET* ((ST$ (UPDATE-PCTR 0 ST$))
                                (ST$ (MAP-UPDATE-RI 0 ST$))
                                (ST$ (MAP-UPDATE-DMI 0 ST$))
                                (ST$ (UPDATE-INRDY (FALSE) ST$))
                                (ST$ (UPDATE-INDATA 0 ST$))
                                (ST$ (UPDATE-OUTSTROBE 0 ST$)))
                               (MAP-UPDATE-IMI (ENCODE 'RESERVEDINSTR)
                                               ST$))))
                   (LOADIM (TUPLE 0 P) ST$)))

#||
instruction list test_prog =
   list {
      LoadConstant (0, 0),
      LoadConstant (1, 1000),
      LoadConstant (2, 1010),
      LoadConstant (3, 4),
      StoreDM (fINC, noShift, skipNever, 1, 1, 1),
      Normal (fXOR, noShift, skipZero, 4, 1, 2),
      Jump (fADD, noShift, 4, 3, 0),
      Out (fADD, noShift, skipNever, 1, 1, 0)
   }

(Def0 "test_prog"
  (LL(sqbkt (Call "LoadConstant" CTy"instruction"
              (TP (sqbkt (LW 0 7) (LW 0 24))))
            (Call "LoadConstant" CTy"instruction"
              (TP (sqbkt (LW 1 7) (LW 1000 24))))
            (Call "LoadConstant" CTy"instruction"
              (TP (sqbkt (LW 2 7) (LW 1010 24))))
            (Call "LoadConstant" CTy"instruction"
              (TP (sqbkt (LW 3 7) (LW 4 24))))
            (Call "StoreDM" CTy"instruction"
              (TP
                (sqbkt (LC "fINC" CTy"funcT") (LC "noShift" CTy"shiftT")
                       (LC "skipNever" CTy"conditionT") (LW 1 7) (LW 1 7)
                       (LW 1 7))))
            (Call "Normal" CTy"instruction"
              (TP
                (sqbkt (LC "fXOR" CTy"funcT") (LC "noShift" CTy"shiftT")
                       (LC "skipZero" CTy"conditionT") (LW 4 7) (LW 1 7)
                       (LW 2 7))))
            (Call "Jump" CTy"instruction"
              (TP
                (sqbkt (LC "fADD" CTy"funcT") (LC "noShift" CTy"shiftT")
                       (LW 4 7) (LW 3 7) (LW 0 7))))
            (Call "Out" CTy"instruction"
              (TP
                (sqbkt (LC "fADD" CTy"funcT") (LC "noShift" CTy"shiftT")
                       (LC "skipNever" CTy"conditionT") (LW 1 7) (LW 1 7)
                       (LW 0 7)))))))

   [test_prog_def]  Definition

      |- test_prog =
         [LoadConstant (0w,0w); LoadConstant (1w,1000w);
          LoadConstant (2w,1010w); LoadConstant (3w,4w);
          StoreDM (fINC,noShift,skipNever,1w,1w,1w);
          Normal (fXOR,noShift,skipZero,4w,1w,2w);
          Jump (fADD,noShift,4w,3w,0w);
          Out (fADD,noShift,skipNever,1w,1w,0w)]

||#

; Auto-generated the following (copied from out.lisp):
(DEFCONST *TEST_PROG*
          (LIST (CALL-CONSTRUCTOR INSTRUCTION LOADCONSTANT (TUPLE 0 0))
                (CALL-CONSTRUCTOR INSTRUCTION LOADCONSTANT (TUPLE 1 1000))
                (CALL-CONSTRUCTOR INSTRUCTION LOADCONSTANT (TUPLE 2 1010))
                (CALL-CONSTRUCTOR INSTRUCTION LOADCONSTANT (TUPLE 3 4))
                (CALL-CONSTRUCTOR INSTRUCTION STOREDM
                                  (TUPLE 'FINC 'NOSHIFT 'SKIPNEVER 1 1 1))
                (CALL-CONSTRUCTOR INSTRUCTION NORMAL
                                  (TUPLE 'FXOR 'NOSHIFT 'SKIPZERO 4 1 2))
                (CALL-CONSTRUCTOR INSTRUCTION
                                  JUMP (TUPLE 'FADD 'NOSHIFT 4 3 0))
                (CALL-CONSTRUCTOR INSTRUCTION OUT
                                  (TUPLE 'FADD
                                         'NOSHIFT
                                         'SKIPNEVER
                                         1 1 0))))
