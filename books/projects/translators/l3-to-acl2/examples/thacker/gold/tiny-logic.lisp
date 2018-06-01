(IN-PACKAGE "ACL2")

(VALUE-TRIPLE
     '(:GENERATED-BY (L3-TO-ACL2 "tiny-acl2.txt" "tiny-logic.lisp"
                                 :LOGIC :LOGIC-ONLY
                                 :STR-TO-SYM '(("PC" . PCTR)
                                               ("alu" . ALU_VAR)
                                               ("function" . FUNCTION0)))))

(INCLUDE-BOOK "projects/translators/l3-to-acl2/translator/l3"
              :DIR :SYSTEM)

(CONSTRUCT FUNCT
           (FADD FSUB FINC FDEC FAND FOR FXOR FRESERVED))

(CONSTRUCT SHIFTT (NOSHIFT RCY1 RCY8 RCY16))

(CONSTRUCT CONDITIONT
           (SKIPNEVER SKIPNEG SKIPZERO SKIPINRDY))

(CONSTRUCT INSTRUCTION
           ((IN (FUNCT SHIFTT CONDITIONT (UNSIGNED-BYTE 7)
                       (UNSIGNED-BYTE 7)
                       (UNSIGNED-BYTE 7)))
            (JUMP (FUNCT SHIFTT (UNSIGNED-BYTE 7)
                         (UNSIGNED-BYTE 7)
                         (UNSIGNED-BYTE 7)))
            (LOADCONSTANT ((UNSIGNED-BYTE 7) (UNSIGNED-BYTE 24)))
            (LOADDM (FUNCT SHIFTT CONDITIONT (UNSIGNED-BYTE 7)
                           (UNSIGNED-BYTE 7)
                           (UNSIGNED-BYTE 7)))
            (NORMAL (FUNCT SHIFTT CONDITIONT (UNSIGNED-BYTE 7)
                           (UNSIGNED-BYTE 7)
                           (UNSIGNED-BYTE 7)))
            (OUT (FUNCT SHIFTT CONDITIONT (UNSIGNED-BYTE 7)
                        (UNSIGNED-BYTE 7)
                        (UNSIGNED-BYTE 7)))
            RESERVEDINSTR
            (STOREDM (FUNCT SHIFTT CONDITIONT (UNSIGNED-BYTE 7)
                            (UNSIGNED-BYTE 7)
                            (UNSIGNED-BYTE 7)))
            (STOREIM (FUNCT SHIFTT CONDITIONT (UNSIGNED-BYTE 7)
                            (UNSIGNED-BYTE 7)
                            (UNSIGNED-BYTE 7)))))

(CONSTRUCT EXCEPTION (NOEXCEPTION RESERVED))

(DEFSTOBJ+ ST$
           (DM :TYPE (ARRAY (UNSIGNED-BYTE 32) (1024))
               :INITIALLY 0)
           (IM :TYPE (ARRAY (UNSIGNED-BYTE 32) (1024))
               :INITIALLY 0)
           (INDATA :TYPE (UNSIGNED-BYTE 32)
                   :INITIALLY 0)
           (INRDY :TYPE (SATISFIES BOOLEANP))
           (OUTSTROBE :TYPE (UNSIGNED-BYTE 32)
                      :INITIALLY 0)
           (PCTR :TYPE (UNSIGNED-BYTE 10)
                 :INITIALLY 0)
           (R :TYPE (ARRAY (UNSIGNED-BYTE 32) (128))
              :INITIALLY 0)
           EXCEPTION)

(VALUE-TRIPLE "See l3.lisp for the definition of raise-exception")

(SET-VERIFY-GUARDS-EAGERNESS 0)

(DEFUN-STRUCT FUNCTION0
              (((FUNC (TYPE-FUNCT FUNC))
                (A (UNSIGNED-BYTE-P 32 A))
                (B (UNSIGNED-BYTE-P 32 B)))
               ST$)
              (DECLARE (XARGS :STOBJS ST$))
              (CASE-MATCH+ FUNC ('FADD (MV (N+ 32 A B) ST$))
                           ('FSUB (MV (N- 32 A B) ST$))
                           ('FINC (MV (N+ 32 B 1) ST$))
                           ('FDEC (MV (N- 32 B 1) ST$))
                           ('FAND (MV (LOGAND A B) ST$))
                           ('FOR (MV (LOGIOR A B) ST$))
                           ('FXOR (MV (LOGXOR A B) ST$))
                           (& (RAISE-EXCEPTION 'RESERVED
                                               (ARB (UNSIGNED-BYTE 32))
                                               ST$))))

(DEFUN-STRUCT SHIFTER
              (((SHIFT (TYPE-SHIFTT SHIFT))
                (A (UNSIGNED-BYTE-P 32 A))))
              (CASE-MATCH+ SHIFT ('NOSHIFT A)
                           ('RCY1 (ASH A -1))
                           ('RCY8 (ASH A -8))
                           ('RCY16 (ASH A -16))
                           (& (IMPOSSIBLE (ARB (UNSIGNED-BYTE 32))))))

(DEFUN-STRUCT ALU
              (((FUNC (TYPE-FUNCT FUNC))
                (SHIFT (TYPE-SHIFTT SHIFT))
                (A (UNSIGNED-BYTE-P 32 A))
                (B (UNSIGNED-BYTE-P 32 B)))
               ST$)
              (DECLARE (XARGS :STOBJS ST$))
              (MV-LET (V ST$)
                      (FUNCTION0 (TUPLE FUNC A B) ST$)
                      (MV (SHIFTER (TUPLE SHIFT V)) ST$)))

(DEFUN-STRUCT
   INCPC
   (((SKIP (TYPE-CONDITIONT SKIP))
     (ALU_VAR (UNSIGNED-BYTE-P 32 ALU_VAR)))
    ST$)
   (DECLARE (XARGS :STOBJS ST$))
   (CASE-MATCH+ SKIP
                ('SKIPNEVER
                 (LET ((ST$ (UPDATE-PCTR (N+ 10 (PCTR ST$) 1) ST$)))
                      (MV (UNIT-VALUE) ST$)))
                ('SKIPNEG
                 (LET ((ST$ (UPDATE-PCTR (N+ 10 (PCTR ST$)
                                             (IF (< ALU_VAR 0) 2 1))
                                         ST$)))
                      (MV (UNIT-VALUE) ST$)))
                ('SKIPZERO
                 (LET ((ST$ (UPDATE-PCTR (N+ 10 (PCTR ST$)
                                             (IF (EQL ALU_VAR 0) 2 1))
                                         ST$)))
                      (MV (UNIT-VALUE) ST$)))
                ('SKIPINRDY
                 (LET ((ST$ (UPDATE-PCTR (N+ 10 (PCTR ST$) (IF (INRDY ST$) 2 1))
                                         ST$)))
                      (MV (UNIT-VALUE) ST$)))
                (& (IMPOSSIBLE (MV (ARB UTY) ST$)))))

(DEFUN-STRUCT NORM
              (((FUNC (TYPE-FUNCT FUNC))
                (SHIFT (TYPE-SHIFTT SHIFT))
                (SKIP (TYPE-CONDITIONT SKIP))
                (WBACK (BOOLEANP WBACK))
                (STROBE (BOOLEANP STROBE))
                (W (UNSIGNED-BYTE-P 7 W))
                (A (UNSIGNED-BYTE-P 7 A))
                (B (UNSIGNED-BYTE-P 7 B)))
               ST$)
              (DECLARE (XARGS :STOBJS ST$))
              (MV-LET (V ST$)
                      (ALU (TUPLE FUNC SHIFT (RI A ST$) (RI B ST$))
                           ST$)
                      (LET* ((ST$ (IF WBACK (UPDATE-RI W V ST$) ST$))
                             (ST$ (IF STROBE (UPDATE-OUTSTROBE V ST$)
                                      ST$)))
                            (INCPC (TUPLE SKIP V) ST$))))

(DEFUN-STRUCT DFN-NORMAL
              (((FUNC (TYPE-FUNCT FUNC))
                (SHIFT (TYPE-SHIFTT SHIFT))
                (SKIP (TYPE-CONDITIONT SKIP))
                (W (UNSIGNED-BYTE-P 7 W))
                (A (UNSIGNED-BYTE-P 7 A))
                (B (UNSIGNED-BYTE-P 7 B)))
               ST$)
              (DECLARE (XARGS :STOBJS ST$))
              (NORM (TUPLE FUNC SHIFT SKIP (TRUE)
                           (FALSE)
                           W A B)
                    ST$))

(DEFUN-STRUCT
     DFN-STOREDM
     (((FUNC (TYPE-FUNCT FUNC))
       (SHIFT (TYPE-SHIFTT SHIFT))
       (SKIP (TYPE-CONDITIONT SKIP))
       (W (UNSIGNED-BYTE-P 7 W))
       (A (UNSIGNED-BYTE-P 7 A))
       (B (UNSIGNED-BYTE-P 7 B)))
      ST$)
     (DECLARE (XARGS :STOBJS ST$))
     (LET ((ST$ (UPDATE-DMI (CAST ((UNSIGNED-BYTE 32) (UNSIGNED-BYTE 10))
                                  (RI B ST$))
                            (RI A ST$)
                            ST$)))
          (NORM (TUPLE FUNC SHIFT SKIP (TRUE)
                       (FALSE)
                       W A B)
                ST$)))

(DEFUN-STRUCT
     DFN-STOREIM
     (((FUNC (TYPE-FUNCT FUNC))
       (SHIFT (TYPE-SHIFTT SHIFT))
       (SKIP (TYPE-CONDITIONT SKIP))
       (W (UNSIGNED-BYTE-P 7 W))
       (A (UNSIGNED-BYTE-P 7 A))
       (B (UNSIGNED-BYTE-P 7 B)))
      ST$)
     (DECLARE (XARGS :STOBJS ST$))
     (LET ((ST$ (UPDATE-IMI (CAST ((UNSIGNED-BYTE 32) (UNSIGNED-BYTE 10))
                                  (RI B ST$))
                            (RI A ST$)
                            ST$)))
          (NORM (TUPLE FUNC SHIFT SKIP (TRUE)
                       (FALSE)
                       W A B)
                ST$)))

(DEFUN-STRUCT DFN-OUT
              (((FUNC (TYPE-FUNCT FUNC))
                (SHIFT (TYPE-SHIFTT SHIFT))
                (SKIP (TYPE-CONDITIONT SKIP))
                (W (UNSIGNED-BYTE-P 7 W))
                (A (UNSIGNED-BYTE-P 7 A))
                (B (UNSIGNED-BYTE-P 7 B)))
               ST$)
              (DECLARE (XARGS :STOBJS ST$))
              (NORM (TUPLE FUNC SHIFT SKIP (TRUE)
                           (TRUE)
                           W A B)
                    ST$))

(DEFUN-STRUCT
     DFN-LOADDM
     (((FUNC (TYPE-FUNCT FUNC))
       (SHIFT (TYPE-SHIFTT SHIFT))
       (SKIP (TYPE-CONDITIONT SKIP))
       (W (UNSIGNED-BYTE-P 7 W))
       (A (UNSIGNED-BYTE-P 7 A))
       (B (UNSIGNED-BYTE-P 7 B)))
      ST$)
     (DECLARE (XARGS :STOBJS ST$))
     (LET ((ST$ (UPDATE-RI W
                           (DMI (CAST ((UNSIGNED-BYTE 32) (UNSIGNED-BYTE 10))
                                      (RI B ST$))
                                ST$)
                           ST$)))
          (NORM (TUPLE FUNC SHIFT SKIP (FALSE)
                       (FALSE)
                       W A B)
                ST$)))

(DEFUN-STRUCT DFN-IN
              (((FUNC (TYPE-FUNCT FUNC))
                (SHIFT (TYPE-SHIFTT SHIFT))
                (SKIP (TYPE-CONDITIONT SKIP))
                (W (UNSIGNED-BYTE-P 7 W))
                (A (UNSIGNED-BYTE-P 7 A))
                (B (UNSIGNED-BYTE-P 7 B)))
               ST$)
              (DECLARE (XARGS :STOBJS ST$))
              (LET ((ST$ (UPDATE-RI W (INDATA ST$) ST$)))
                   (NORM (TUPLE FUNC SHIFT SKIP (FALSE)
                                (FALSE)
                                W A B)
                         ST$)))

(DEFUN-STRUCT
     DFN-JUMP
     (((FUNC (TYPE-FUNCT FUNC))
       (SHIFT (TYPE-SHIFTT SHIFT))
       (W (UNSIGNED-BYTE-P 7 W))
       (A (UNSIGNED-BYTE-P 7 A))
       (B (UNSIGNED-BYTE-P 7 B)))
      ST$)
     (DECLARE (XARGS :STOBJS ST$))
     (LET ((ST$ (UPDATE-RI W
                           (CAST ((UNSIGNED-BYTE 10) (UNSIGNED-BYTE 32))
                                 (N+ 10 (PCTR ST$) 1))
                           ST$)))
          (MV-LET (V ST$)
                  (MV-LET (V ST$)
                          (ALU (TUPLE FUNC SHIFT (RI A ST$) (RI B ST$))
                               ST$)
                          (MV (CAST ((UNSIGNED-BYTE 32) (UNSIGNED-BYTE 10))
                                    V)
                              ST$))
                  (LET ((ST$ (UPDATE-PCTR V ST$)))
                       (MV (UNIT-VALUE) ST$)))))

(DEFUN-STRUCT
     DFN-LOADCONSTANT
     (((W (UNSIGNED-BYTE-P 7 W))
       (IMM (UNSIGNED-BYTE-P 24 IMM)))
      ST$)
     (DECLARE (XARGS :STOBJS ST$))
     (LET* ((ST$ (UPDATE-RI W
                            (CAST ((UNSIGNED-BYTE 24) (UNSIGNED-BYTE 32))
                                  IMM)
                            ST$))
            (ST$ (UPDATE-PCTR (N+ 10 (PCTR ST$) 1) ST$)))
           (MV (UNIT-VALUE) ST$)))

(DEFUN-STRUCT DFN-RESERVEDINSTR (ST$)
              (DECLARE (XARGS :STOBJS ST$))
              (RAISE-EXCEPTION 'RESERVED
                               (ARB UTY)
                               ST$))

(DEFUN-STRUCT RUN ((V0 (TYPE-INSTRUCTION V0)) ST$)
              (DECLARE (XARGS :STOBJS ST$))
              (CASE-MATCH+ V0
                           ('RESERVEDINSTR (DFN-RESERVEDINSTR ST$))
                           (('IN V1) (DFN-IN V1 ST$))
                           (('JUMP V2) (DFN-JUMP V2 ST$))
                           (('LOADCONSTANT V3)
                            (DFN-LOADCONSTANT V3 ST$))
                           (('LOADDM V4) (DFN-LOADDM V4 ST$))
                           (('NORMAL V5) (DFN-NORMAL V5 ST$))
                           (('OUT V6) (DFN-OUT V6 ST$))
                           (('STOREDM V7) (DFN-STOREDM V7 ST$))
                           (('STOREIM V8) (DFN-STOREIM V8 ST$))
                           (& (IMPOSSIBLE (MV (ARB UTY) ST$)))))

(DEFUN-STRUCT
 DECODE ((OPC (UNSIGNED-BYTE-P 32 OPC)))
 (MV-LET-IGNORABLE
  (B-31 B-30 B-29 B-28 B-27 B-26
        B-25 B-24 B-23 B-22 B-21 B-20 B-19 B-18
        B-17 B-16 B-15 B-14 B-13 B-12 B-11 B-10
        B-9 B-8 B-7 B-6 B-5 B-4 B-3 B-2 B-1 B-0)
  (BL 32 OPC)
  (IF
   B-24
   (CALL-CONSTRUCTOR INSTRUCTION LOADCONSTANT
                     (TUPLE (BITS OPC 31 25)
                            (BITS OPC 23 0)))
   (LET*
        ((RW (BITS OPC 31 25))
         (RB (BITS OPC 16 10))
         (RA (BITS OPC 23 17))
         (FUNC (CAST ((UNSIGNED-BYTE 3) FUNCT)
                     (BITS OPC 9 7)))
         (SHIFT (CAST ((UNSIGNED-BYTE 2) SHIFTT)
                      (BITS OPC 6 5)))
         (SKIP (CAST ((UNSIGNED-BYTE 2) CONDITIONT)
                     (BITS OPC 4 3))))
        (CASE-MATCH+ (BITS OPC 2 0)
                     (0 (CALL-CONSTRUCTOR INSTRUCTION NORMAL
                                          (TUPLE FUNC SHIFT SKIP RW RA RB)))
                     (1 (CALL-CONSTRUCTOR INSTRUCTION STOREDM
                                          (TUPLE FUNC SHIFT SKIP RW RA RB)))
                     (2 (CALL-CONSTRUCTOR INSTRUCTION STOREIM
                                          (TUPLE FUNC SHIFT SKIP RW RA RB)))
                     (3 (CALL-CONSTRUCTOR INSTRUCTION
                                          OUT (TUPLE FUNC SHIFT SKIP RW RA RB)))
                     (4 (CALL-CONSTRUCTOR INSTRUCTION LOADDM
                                          (TUPLE FUNC SHIFT SKIP RW RA RB)))
                     (5 (CALL-CONSTRUCTOR INSTRUCTION
                                          IN (TUPLE FUNC SHIFT SKIP RW RA RB)))
                     (6 (CALL-CONSTRUCTOR INSTRUCTION
                                          JUMP (TUPLE FUNC SHIFT RW RA RB)))
                     (7 'RESERVEDINSTR)
                     (& (IMPOSSIBLE (ARB INSTRUCTION))))))))

(DEFUN-STRUCT NEXT (ST$)
              (DECLARE (XARGS :STOBJS ST$))
              (LET ((V (DECODE (IMI (PCTR ST$) ST$))))
                   (IF (NOT (EQ V 'RESERVEDINSTR))
                       (RUN V ST$)
                       (MV (UNIT-VALUE) ST$))))

(DEFUN-STRUCT ENC
              (((ARGS (SLET (X0 X1 X2 X3 X4 X5)
                            ARGS
                            (AND (TYPE-FUNCT X0)
                                 (TYPE-SHIFTT X1)
                                 (TYPE-CONDITIONT X2)
                                 (UNSIGNED-BYTE-P 7 X3)
                                 (UNSIGNED-BYTE-P 7 X4)
                                 (UNSIGNED-BYTE-P 7 X5))
                            NIL NIL))
                (OPC (UNSIGNED-BYTE-P 3 OPC))))
              (SLET (FUNC SHIFT SKIP W A B)
                    ARGS
                    (CAT W 7 0 1 A 7 B
                         7 (CAST (FUNCT (UNSIGNED-BYTE 3)) FUNC)
                         3
                         (CAST (SHIFTT (UNSIGNED-BYTE 2)) SHIFT)
                         2
                         (CAST (CONDITIONT (UNSIGNED-BYTE 2))
                               SKIP)
                         2 OPC 3)))

(DEFUN-STRUCT ENCODE ((I (TYPE-INSTRUCTION I)))
              (CASE-MATCH+ I
                           (('LOADCONSTANT (RW IMM))
                            (CAT RW 7 1 1 IMM 24))
                           (('NORMAL ARGS) (ENC (TUPLE ARGS 0)))
                           (('STOREDM ARGS) (ENC (TUPLE ARGS 1)))
                           (('STOREIM ARGS) (ENC (TUPLE ARGS 2)))
                           (('OUT ARGS) (ENC (TUPLE ARGS 3)))
                           (('LOADDM ARGS) (ENC (TUPLE ARGS 4)))
                           (('IN ARGS) (ENC (TUPLE ARGS 5)))
                           (('JUMP (FUNC SHIFT RW RA RB))
                            (ENC (TUPLE (TUPLE FUNC SHIFT 'SKIPNEVER RW RA RB)
                                        6)))
                           ('RESERVEDINSTR 7)
                           (& (IMPOSSIBLE (ARB (UNSIGNED-BYTE 32))))))

(DEFUN-STRUCT LOADIM
              (((A (UNSIGNED-BYTE-P 10 A))
                (I (TYPE-INSTRUCTION-LIST I)))
               ST$)
              :MEASURE (LEN I)
              (DECLARE (XARGS :STOBJS ST$))
              (CASE-MATCH+ I ('NIL (MV (UNIT-VALUE) ST$))
                           ((H . T_VAR)
                            (LET ((ST$ (UPDATE-IMI A (ENCODE H) ST$)))
                                 (LOADIM (TUPLE (N+ 10 A 1) T_VAR) ST$)))
                           (& (IMPOSSIBLE (MV (ARB UTY) ST$)))))

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

