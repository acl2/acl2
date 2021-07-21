(IN-PACKAGE "RTL")

(INCLUDE-BOOK "rtl/rel11/lib/rac" :DIR :SYSTEM)

(SET-IGNORE-OK T)

(SET-IRRELEVANT-FORMALS-OK T)

(DEFUND
 ANALYZE (OP FMT FZ FLAGS)
 (LET
    ((SIGN 0)
     (EXP 0)
     (MAN 0)
     (MANMSB 0)
     (EXPISMAX 0))
    (MV-LET
         (SIGN EXP EXPISMAX MAN MANMSB)
         (CASE FMT
               (2 (LET ((SIGN (BITN OP 63))
                        (EXP (BITS OP 62 52)))
                       (MV SIGN EXP (LOG= (SI EXP 13) 2047)
                           (BITS OP 51 0)
                           (BITS 2251799813685248 51 0))))
               (1 (LET ((SIGN (BITN OP 31))
                        (EXP (BITS OP 30 23)))
                       (MV SIGN EXP (LOG= (SI EXP 13) 255)
                           (BITS OP 22 0)
                           (BITS 4194304 51 0))))
               (0 (LET ((SIGN (BITN OP 15))
                        (EXP (BITS OP 14 10)))
                       (MV SIGN EXP (LOG= (SI EXP 13) 31)
                           (BITS OP 9 0)
                           (BITS 512 51 0))))
               (T (MV SIGN EXP EXPISMAX MAN MANMSB)))
         (LET ((C 0))
              (MV-LET (FLAGS C)
                      (IF1 EXPISMAX
                           (MV FLAGS
                               (IF1 (LOG= MAN 0)
                                    1 (IF1 (LOGAND MAN MANMSB) 3 2)))
                           (IF1 (LOG= (SI EXP 13) 0)
                                (IF1 (LOG= MAN 0)
                                     (MV FLAGS 0)
                                     (MV-LET (C FLAGS)
                                             (IF1 FZ
                                                  (MV 0
                                                      (IF1 (LOG<> FMT 0)
                                                           (SETBITN FLAGS 8 7 1)
                                                           FLAGS))
                                                  (MV 5 FLAGS))
                                             (MV FLAGS C)))
                                (MV FLAGS 4)))
                      (MV SIGN (BITS (SI EXP 13) 10 0)
                          MAN C FLAGS))))))

(DEFUND CLZ53-LOOP-0 (I N K C Z)
        (DECLARE (XARGS :MEASURE (NFIX (- N I))))
        (IF (AND (INTEGERP I) (INTEGERP N) (< I N))
            (LET* ((C (AS I
                          (BITS (IF1 (AG (+ (* 2 I) 1) Z)
                                     (AG (* 2 I) C)
                                     (AG (+ (* 2 I) 1) C))
                                5 0)
                          C))
                   (C (AS I
                          (SETBITN (AG I C)
                                   6 K (AG (+ (* 2 I) 1) Z))
                          C))
                   (Z (AS I
                          (LOGAND1 (AG (+ (* 2 I) 1) Z)
                                   (AG (* 2 I) Z))
                          Z)))
                  (CLZ53-LOOP-0 (+ I 1) N K C Z))
            (MV C Z)))

(DEFUND CLZ53-LOOP-1 (K N C Z)
        (DECLARE (XARGS :MEASURE (NFIX (- 6 K))))
        (IF (AND (INTEGERP K) (< K 6))
            (LET ((N (FLOOR N 2)))
                 (MV-LET (C Z)
                         (CLZ53-LOOP-0 0 N K C Z)
                         (CLZ53-LOOP-1 (+ K 1) N C Z)))
            (MV N C Z)))

(DEFUND CLZ53-LOOP-2 (I X Z C)
        (DECLARE (XARGS :MEASURE (NFIX (- 64 I))))
        (IF (AND (INTEGERP I) (< I 64))
            (LET ((Z (AS I (LOGNOT1 (BITN X I)) Z))
                  (C (AS I (BITS 0 5 0) C)))
                 (CLZ53-LOOP-2 (+ I 1) X Z C))
            (MV Z C)))

(DEFUND CLZ53 (S)
        (LET* ((X (BITS 0 63 0))
               (X (SETBITS X 64 63 11 S))
               (Z NIL)
               (C NIL))
              (MV-LET (Z C)
                      (CLZ53-LOOP-2 0 X Z C)
                      (LET ((N 64))
                           (MV-LET (N C Z)
                                   (CLZ53-LOOP-1 0 N C Z)
                                   (AG 0 C))))))

(DEFUND COMPUTEQ
        (ROOT ROOTM1 ROOTP ROOTM1P RP RN LSBIS2)
        (LET* ((QTRUNC 0)
               (QINC 0)
               (STK 0)
               (REM (BITS (+ (+ RP (LOGNOT RN)) 1) 58 0))
               (REMSIGN (BITN REM 58))
               (REMZERO (LOG= (LOGXOR RP RN) 0))
               (ROOTLO (BITS (IF1 REMSIGN ROOTM1 ROOT) 54 0))
               (ROOTLOP (BITS (IF1 REMSIGN ROOTM1P ROOTP)
                              54 0)))
              (MV-LET (STK QTRUNC QINC)
                      (IF1 LSBIS2
                           (MV (LOGIOR1 (BITN ROOTLO 0)
                                        (LOGNOT1 REMZERO))
                               (BITS ROOTLO 53 1)
                               (BITS ROOTLOP 53 1))
                           (MV (LOGNOT1 REMZERO)
                               (BITS ROOTLO 52 0)
                               (BITS ROOTLOP 52 0)))
                      (MV QTRUNC QINC STK))))

(DEFUND RSHFT64 (X S)
        (LET ((XS (BITS (ASH X (- S)) 63 0)))
             (MV XS (LOG<> X (ASH XS S)))))

(DEFUND
 ROUNDER
 (QTRUNC QINC STK SIGN EXPQ RMODE FMT)
 (LET*
  ((LSB (BITN QTRUNC 1))
   (GRD (BITN QTRUNC 0))
   (QRND 0)
   (QRND (IF1 (LOGIOR1 (LOGIOR1 (LOGAND1 (LOGAND1 (LOG= RMODE 0) GRD)
                                         (LOGIOR1 LSB STK))
                                (LOGAND1 (LOGAND1 (LOG= RMODE 1) (LOGNOT1 SIGN))
                                         (LOGIOR1 GRD STK)))
                       (LOGAND1 (LOGAND1 (LOG= RMODE 2) SIGN)
                                (LOGIOR1 GRD STK)))
              (BITS QINC 53 1)
              (BITS QTRUNC 53 1)))
   (INX (LOGIOR1 GRD STK))
   (QDEN (BITS 0 63 0))
   (QDEN (CASE FMT
               (2 (LET ((QDEN (SETBITN QDEN 64 53 1)))
                       (SETBITS QDEN 64 52 0 (BITS QTRUNC 52 0))))
               (1 (LET ((QDEN (SETBITN QDEN 64 24 1)))
                       (SETBITS QDEN 64 23 0 (BITS QTRUNC 23 0))))
               (0 (LET ((QDEN (SETBITN QDEN 64 11 1)))
                       (SETBITS QDEN 64 10 0 (BITS QTRUNC 10 0))))
               (T QDEN)))
   (SHFT12 (BITS (- 1 (SI EXPQ 13)) 11 0))
   (SHFT (BITS (IF1 (LOG>= SHFT12 64) 63 SHFT12)
               5 0))
   (LSBDEN 0)
   (GRDDEN 0)
   (STKDEN 0)
   (QSHFT 0))
  (MV-LET
   (QSHFT STKDEN)
   (RSHFT64 QDEN SHFT)
   (LET
    ((LSBDEN (BITN QSHFT 1))
     (GRDDEN (BITN QSHFT 0))
     (STKDEN (LOGIOR1 STKDEN STK))
     (QRNDDEN 0))
    (MV
     QRND INX
     (BITS
         (IF1 (LOGIOR1 (LOGIOR1 (LOGAND1 (LOGAND1 (LOG= RMODE 0) GRDDEN)
                                         (LOGIOR1 LSBDEN STKDEN))
                                (LOGAND1 (LOGAND1 (LOG= RMODE 1) (LOGNOT1 SIGN))
                                         (LOGIOR1 GRDDEN STKDEN)))
                       (LOGAND1 (LOGAND1 (LOG= RMODE 2) SIGN)
                                (LOGIOR1 GRDDEN STKDEN)))
              (BITS (+ (BITS QSHFT 53 1) 1) 53 0)
              (BITS QSHFT 53 1))
         52 0)
     (LOGIOR1 GRDDEN STKDEN))))))

(DEFUND
 FINAL
 (QRND INX QRNDDEN
       INXDEN SIGN EXPQ RMODE FZ FMT FLAGS)
 (LET
  ((SELMAXNORM (LOGIOR1 (LOGIOR1 (LOGAND1 (LOG= RMODE 2) (LOGNOT1 SIGN))
                                 (LOGAND1 (LOG= RMODE 1) SIGN))
                        (LOG= RMODE 3)))
   (D (BITS 0 63 0)))
  (CASE
   FMT
   (2
    (LET
     ((D (SETBITN D 64 63 SIGN)))
     (IF1
         (LOG>= (SI EXPQ 13) 2047)
         (MV (IF1 SELMAXNORM
                  (LET ((D (SETBITS D 64 62 52 2046)))
                       (SETBITS D 64 51 0 4503599627370495))
                  (LET ((D (SETBITS D 64 62 52 2047)))
                       (SETBITS D 64 51 0 0)))
             (SETBITN (SETBITN FLAGS 8 2 1) 8 4 1))
         (IF1 (LOG<= (SI EXPQ 13) 0)
              (IF1 FZ (MV D (SETBITN FLAGS 8 3 1))
                   (LET* ((EXP (BITN QRNDDEN 52))
                          (D (SETBITS D 64 62 52 EXP))
                          (D (SETBITS D 64 51 0 (BITS QRNDDEN 51 0)))
                          (FLAGS (SETBITN FLAGS
                                          8 4 (LOGIOR1 (BITN FLAGS 4) INXDEN))))
                         (MV D
                             (SETBITN FLAGS
                                      8 3 (LOGIOR1 (BITN FLAGS 3) INXDEN)))))
              (MV (SETBITS (SETBITS D 64 62 52 (SI EXPQ 13))
                           64 51 0 (BITS QRND 51 0))
                  (SETBITN FLAGS
                           8 4 (LOGIOR1 (BITN FLAGS 4) INX)))))))
   (1
    (LET
     ((D (SETBITN D 64 31 SIGN)))
     (IF1
         (LOG>= (SI EXPQ 13) 255)
         (MV (IF1 SELMAXNORM
                  (LET ((D (SETBITS D 64 30 23 254)))
                       (SETBITS D 64 22 0 8388607))
                  (LET ((D (SETBITS D 64 30 23 255)))
                       (SETBITS D 64 22 0 0)))
             (SETBITN (SETBITN FLAGS 8 2 1) 8 4 1))
         (IF1 (LOG<= (SI EXPQ 13) 0)
              (IF1 FZ (MV D (SETBITN FLAGS 8 3 1))
                   (LET* ((EXP (BITN QRNDDEN 23))
                          (D (SETBITS D 64 30 23 EXP))
                          (D (SETBITS D 64 22 0 (BITS QRNDDEN 22 0)))
                          (FLAGS (SETBITN FLAGS
                                          8 4 (LOGIOR1 (BITN FLAGS 4) INXDEN))))
                         (MV D
                             (SETBITN FLAGS
                                      8 3 (LOGIOR1 (BITN FLAGS 3) INXDEN)))))
              (MV (SETBITS (SETBITS D 64 30 23 (SI EXPQ 13))
                           64 22 0 (BITS QRND 22 0))
                  (SETBITN FLAGS
                           8 4 (LOGIOR1 (BITN FLAGS 4) INX)))))))
   (0
    (LET
     ((D (SETBITN D 64 15 SIGN)))
     (IF1
         (LOG>= (SI EXPQ 13) 31)
         (MV (IF1 SELMAXNORM
                  (LET ((D (SETBITS D 64 14 10 30)))
                       (SETBITS D 64 9 0 1023))
                  (LET ((D (SETBITS D 64 14 10 31)))
                       (SETBITS D 64 9 0 0)))
             (SETBITN (SETBITN FLAGS 8 2 1) 8 4 1))
         (IF1 (LOG<= (SI EXPQ 13) 0)
              (IF1 FZ (MV D (SETBITN FLAGS 8 3 1))
                   (LET* ((EXP (BITN QRNDDEN 10))
                          (D (SETBITS D 64 14 10 EXP))
                          (D (SETBITS D 64 9 0 (BITS QRNDDEN 9 0)))
                          (FLAGS (SETBITN FLAGS
                                          8 4 (LOGIOR1 (BITN FLAGS 4) INXDEN))))
                         (MV D
                             (SETBITN FLAGS
                                      8 3 (LOGIOR1 (BITN FLAGS 3) INXDEN)))))
              (MV (SETBITS (SETBITS D 64 14 10 (SI EXPQ 13))
                           64 9 0 (BITS QRND 9 0))
                  (SETBITN FLAGS
                           8 4 (LOGIOR1 (BITN FLAGS 4) INX)))))))
   (T (MV D FLAGS)))))

(DEFUND
 SPECIALCASE
 (SIGNA OPA CLASSA FMT DN FLAGS)
 (LET
  ((D (BITS 0 63 0))
   (ATRUNC 0)
   (MANMSB 0)
   (DEFNAN 0)
   (ZERO (BITS 0 63 0)))
  (MV-LET
     (ATRUNC ZERO DEFNAN MANMSB)
     (CASE FMT
           (2 (MV (BITS OPA 63 0)
                  (SETBITN ZERO 64 63 SIGNA)
                  (BITS 9221120237041090560 63 0)
                  (BITS 2251799813685248 63 0)))
           (1 (MV (BITS OPA 31 0)
                  (SETBITN ZERO 64 31 SIGNA)
                  (BITS 2143289344 63 0)
                  (BITS 4194304 63 0)))
           (0 (MV (BITS OPA 15 0)
                  (SETBITN ZERO 64 15 SIGNA)
                  (BITS 32256 63 0)
                  (BITS 512 63 0)))
           (T (MV ATRUNC ZERO DEFNAN MANMSB)))
     (IF1 (LOG= CLASSA 2)
          (MV (BITS (IF1 DN DEFNAN (LOGIOR ATRUNC MANMSB))
                    63 0)
              (SETBITN FLAGS 8 0 1))
          (MV-LET (FLAGS D)
                  (IF1 (LOG= CLASSA 3)
                       (MV FLAGS
                           (BITS (IF1 DN DEFNAN ATRUNC) 63 0))
                       (IF1 (LOG= CLASSA 0)
                            (MV FLAGS ZERO)
                            (MV-LET (D FLAGS)
                                    (IF1 SIGNA (MV DEFNAN (SETBITN FLAGS 8 0 1))
                                         (MV ATRUNC FLAGS))
                                    (MV FLAGS D))))
                  (MV D FLAGS))))))

(DEFUND NORMALIZE (EXPA MANA FMT)
        (LET ((SIGA (BITS 0 52 0)) (BIAS 0))
             (MV-LET (SIGA BIAS)
                     (CASE FMT (2 (MV MANA 1023))
                           (1 (MV (SETBITS SIGA 53 51 29 MANA) 127))
                           (0 (MV (SETBITS SIGA 53 51 42 MANA) 15))
                           (T (MV SIGA BIAS)))
                     (MV-LET (SIGA EXPA)
                             (IF1 (LOG= (SI EXPA 13) 0)
                                  (LET ((CLZ (BITS (CLZ53 SIGA) 5 0)))
                                       (MV (BITS (ASH SIGA CLZ) 52 0)
                                           (BITS (- 1 CLZ) 12 0)))
                                  (MV (SETBITN SIGA 53 52 1) EXPA))
                             (MV SIGA EXPA
                                 (BITS (BITS (+ (SI EXPA 13) BIAS) 11 0)
                                       11 1))))))

(DEFUND
    SQRTPOW2 (EXPQ EXPODD RMODE FMT)
    (LET ((D (BITS 0 63 0))
          (FLAGS (BITS 0 7 0))
          (MANWIDTH 0)
          (MANSQRT2 0))
         (MV-LET (MANWIDTH MANSQRT2)
                 (CASE FMT
                       (2 (MV 52
                              (BITS (IF1 (LOGIOR1 (LOG= RMODE 0) (LOG= RMODE 1))
                                         1865452045155277 1865452045155276)
                                    51 0)))
                       (1 (MV 23
                              (BITS (IF1 (LOG= RMODE 1) 3474676 3474675)
                                    51 0)))
                       (0 (MV 10
                              (BITS (IF1 (LOG= RMODE 1) 1449 1448)
                                    51 0)))
                       (T (MV MANWIDTH MANSQRT2)))
                 (MV-LET (D FLAGS)
                         (IF1 (LOGNOT1 EXPODD)
                              (MV MANSQRT2 (SETBITN FLAGS 8 4 1))
                              (MV D FLAGS))
                         (MV (SETBITS D 64 (+ MANWIDTH 10)
                                      MANWIDTH EXPQ)
                             FLAGS)))))

(DEFUND FIRSTITER (SIGA EXPODD)
        (LET ((RP (BITS 0 58 0))
              (RN (BITS 0 58 0))
              (ROOT (BITS 0 54 0))
              (ROOTM1 (BITS 0 54 0))
              (Q 0)
              (I 0))
             (MV-LET (RP Q ROOT ROOTM1 RN I)
                     (IF1 EXPODD
                          (LET* ((RP (SETBITS RP 59 58 56 6))
                                 (RP (SETBITS RP 59 55 3 SIGA)))
                                (MV-LET (Q ROOT ROOTM1 RN I)
                                        (IF1 (BITN SIGA 51)
                                             (MV -1 (SETBITS ROOT 55 53 52 3)
                                                 (SETBITS ROOTM1 55 53 52 2)
                                                 (SETBITS RN 59 58 53 57)
                                                 4)
                                             (MV -2 (SETBITS ROOT 55 53 52 2)
                                                 (SETBITS ROOTM1 55 53 52 1)
                                                 (SETBITS RN 59 58 55 13)
                                                 0))
                                        (MV RP Q ROOT ROOTM1 RN I)))
                          (LET* ((RP (SETBITS RP 59 58 57 3))
                                 (RP (SETBITS RP 59 56 4 SIGA)))
                                (MV-LET (RN Q ROOT ROOTM1 I)
                                        (IF1 (BITN SIGA 51)
                                             (MV RN 0 (SETBITN ROOT 55 54 1)
                                                 (SETBITS ROOTM1 55 53 52 3)
                                                 8)
                                             (MV (SETBITS RN 59 58 53 57)
                                                 -1 (SETBITS ROOT 55 53 52 3)
                                                 (SETBITS ROOTM1 55 53 52 2)
                                                 4))
                                        (MV RP Q ROOT ROOTM1 RN I))))
                     (MV RP RN ROOT ROOTM1 Q I))))

(DEFUND NEXTDIGIT (RP RN I J)
        (LET* ((RP4 (BITS (ASH RP 2) 58 0))
               (RN4 (BITS (ASH RN 2) 58 0))
               (RS8 (BITS (+ (+ (BITS RP4 58 51)
                                (LOGNOT (BITS RN4 58 51)))
                             (LOGIOR1 (BITN RP4 50)
                                      (LOGNOT1 (BITN RN4 50))))
                          7 0))
               (RS7 (BITS RS8 7 1))
               (MP2 0)
               (MP1 0)
               (MZ0 0)
               (MN1 0))
              (MV-LET (MP2 MP1 MZ0 MN1)
                      (CASE I
                            (0 (MV (BITS 12 6 0)
                                   (BITS 4 6 0)
                                   (BITS -4 6 0)
                                   (BITS (IF1 (LOG= J 1) -11 -12) 6 0)))
                            (1 (MV (BITS (IF1 (LOG= J 2) 15 13) 6 0)
                                   (BITS 4 6 0)
                                   (BITS -4 6 0)
                                   (BITS -13 6 0)))
                            (2 (MV (BITS 15 6 0)
                                   (BITS 4 6 0)
                                   (BITS -4 6 0)
                                   (BITS -15 6 0)))
                            (3 (MV (BITS 16 6 0)
                                   (BITS 6 6 0)
                                   (BITS -6 6 0)
                                   (BITS -16 6 0)))
                            (4 (MV (BITS 18 6 0)
                                   (BITS 6 6 0)
                                   (BITS -6 6 0)
                                   (BITS -18 6 0)))
                            (5 (MV (BITS 20 6 0)
                                   (BITS 8 6 0)
                                   (BITS -6 6 0)
                                   (BITS -20 6 0)))
                            (6 (MV (BITS 20 6 0)
                                   (BITS 8 6 0)
                                   (BITS -8 6 0)
                                   (BITS -20 6 0)))
                            (7 (MV (BITS 22 6 0)
                                   (BITS 8 6 0)
                                   (BITS -8 6 0)
                                   (BITS -22 6 0)))
                            (8 (MV (BITS 24 6 0)
                                   (BITS 8 6 0)
                                   (BITS -8 6 0)
                                   (BITS -24 6 0)))
                            (T (MV MP2 MP1 MZ0 MN1)))
                      (LET ((Q 0))
                           (IF1 (LOG>= (SI RS7 7) (SI MP2 7))
                                2
                                (IF1 (LOG>= (SI RS7 7) (SI MP1 7))
                                     1
                                     (IF1 (LOG>= (SI RS7 7) (SI MZ0 7))
                                          0
                                          (IF1 (LOG>= (SI RS7 7) (SI MN1 7))
                                               -1 -2))))))))

(DEFUND
 NEXTREM (RP RN ROOT ROOTM1 Q J FMT)
 (LET
   ((RP4 (BITS (ASH RP 2) 58 0))
    (RN4 (BITS (ASH RN 2) 58 0))
    (D (BITS 0 58 0))
    (DCOMP (BITS 0 58 0)))
   (MV-LET
        (DCOMP D)
        (CASE Q
              (1 (LET* ((DCOMP (SETBITS DCOMP 59 56 2 ROOT))
                        (DCOMP (SETBITS DCOMP 59 (+ (- 53 (* 2 J)) 2)
                                        (- 53 (* 2 J))
                                        1)))
                       (MV DCOMP (BITS (LOGNOT DCOMP) 58 0))))
              (2 (LET* ((DCOMP (SETBITS DCOMP 59 57 3 ROOT))
                        (DCOMP (SETBITS DCOMP 59 (+ (- 54 (* 2 J)) 2)
                                        (- 54 (* 2 J))
                                        2)))
                       (MV DCOMP (BITS (LOGNOT DCOMP) 58 0))))
              (-1 (MV DCOMP
                      (SETBITS (SETBITS D 59 56 2 ROOTM1)
                               59 (+ (- 53 (* 2 J)) 2)
                               (- 53 (* 2 J))
                               7)))
              (-2 (MV DCOMP
                      (SETBITS (SETBITS D 59 57 3 ROOTM1)
                               59 (+ (- 54 (* 2 J)) 2)
                               (- 54 (* 2 J))
                               6)))
              (T (MV DCOMP D)))
        (LET ((SUM (LOGXOR (LOGXOR RP4 RN4) D))
              (CAR (LOGIOR (LOGAND RP4 (BITS (LOGNOT RN4) 58 0))
                           (LOGAND (LOGIOR RP4 (BITS (LOGNOT RN4) 58 0))
                                   D))))
             (IF1 (LOG= Q 0)
                  (MV RP4 RN4)
                  (LET ((NEXTRP (BITS 0 58 0))
                        (NEXTRN (BITS 0 58 0)))
                       (CASE FMT
                             (2 (MV (SETBITS (SETBITN NEXTRP 59 0 (LOG> Q 0))
                                             59 58 1 (BITS CAR 57 0))
                                    SUM))
                             (1 (MV (SETBITS (SETBITN NEXTRP 59 29 (LOG> Q 0))
                                             59 58 30 (BITS CAR 57 29))
                                    (SETBITS NEXTRN 59 58 29 (BITS SUM 58 29))))
                             (0 (MV (SETBITS (SETBITN NEXTRP 59 42 (LOG> Q 0))
                                             59 58 43 (BITS CAR 57 42))
                                    (SETBITS NEXTRN 59 58 42 (BITS SUM 58 42))))
                             (T (MV NEXTRP NEXTRN)))))))))

(DEFUND NEXTROOT (ROOT ROOTM1 Q J)
        (LET ((ROOTNEW 0) (ROOTM1NEW 0))
             (MV (SETBITS (BITS (IF1 (LOG>= Q 0) ROOT ROOTM1)
                                54 0)
                          55 (+ (- 52 (* 2 J)) 1)
                          (- 52 (* 2 J))
                          Q)
                 (SETBITS (BITS (IF1 (LOG> Q 0) ROOT ROOTM1) 54 0)
                          55 (+ (- 52 (* 2 J)) 1)
                          (- 52 (* 2 J))
                          (- Q 1)))))

(DEFUND
     INCROOT
     (Q ROOT ROOTM1
        QLAST ROOTLAST ROOTM1LAST LSBIS2 N)
     (LET ((ROOTP 0)
           (ROOTM1P 0)
           (BASE (- 54 (* 2 N))))
          (IF1 LSBIS2
               (MV (SETBITS (IF1 (LOG>= Q 0)
                                 (LET ((ROOTP (BITS (IF1 (LOG>= QLAST -1)
                                                         ROOTLAST ROOTM1LAST)
                                                    54 0)))
                                      (SETBITS ROOTP 55 (+ (+ BASE 2) 1)
                                               (+ BASE 2)
                                               (+ QLAST 1)))
                                 ROOT)
                            55 (+ BASE 1)
                            BASE Q)
                   (SETBITS (IF1 (LOG>= Q 1)
                                 (LET ((ROOTM1P (BITS (IF1 (LOG>= QLAST -1)
                                                           ROOTLAST ROOTM1LAST)
                                                      54 0)))
                                      (SETBITS ROOTM1P 55 (+ (+ BASE 2) 1)
                                               (+ BASE 2)
                                               (+ QLAST 1)))
                                 ROOT)
                            55 (+ BASE 1)
                            BASE (- Q 1)))
               (IF1 (LOG= Q 2)
                    (MV (SETBITS (SETBITS (BITS (IF1 (LOG>= QLAST -1)
                                                     ROOTLAST ROOTM1LAST)
                                                54 0)
                                          55 (+ (+ BASE 2) 1)
                                          (+ BASE 2)
                                          (+ QLAST 1))
                                 55 (+ BASE 1)
                                 BASE 0)
                        (SETBITS ROOT 55 (+ BASE 1) BASE 3))
                    (MV (SETBITS ROOT 55 (+ BASE 1)
                                 BASE (+ Q 2))
                        (SETBITS (BITS (IF1 (LOG>= Q -1) ROOT ROOTM1)
                                       54 0)
                                 55 (+ BASE 1)
                                 BASE (+ Q 1)))))))

(DEFUND
 FSQRT4-LOOP-0
 (J LSBIS2
    N FMT Q QLAST ROOTLAST ROOTM1LAST I
    RP RN ROOTP ROOTM1P ROOT ROOTM1 EXPINC)
 (DECLARE (XARGS :MEASURE (NFIX (- N J))))
 (IF
  (AND (INTEGERP J) (INTEGERP N) (< J N))
  (LET
   ((Q (NEXTDIGIT RP RN I J)))
   (MV-LET
    (QLAST ROOTLAST ROOTM1LAST)
    (IF1 (LOG= J (- N 2))
         (MV Q ROOT ROOTM1)
         (MV QLAST ROOTLAST ROOTM1LAST))
    (LET
     ((I (IF1 (LOG= J 1) (+ I Q) I)))
     (MV-LET
       (RP RN)
       (NEXTREM RP RN ROOT ROOTM1 Q J FMT)
       (MV-LET
            (ROOTP ROOTM1P)
            (IF1 (LOG= J (- N 1))
                 (INCROOT Q ROOT ROOTM1
                          QLAST ROOTLAST ROOTM1LAST LSBIS2 N)
                 (MV ROOTP ROOTM1P))
            (MV-LET (ROOT ROOTM1)
                    (NEXTROOT ROOT ROOTM1 Q J)
                    (LET ((EXPINC (LOGAND EXPINC
                                          (IF1 (LOG< J (- N 1))
                                               (LOG= Q 0)
                                               (IF1 (LOG= FMT 1)
                                                    (LOG= Q -2)
                                                    (LOG= Q -1))))))
                         (FSQRT4-LOOP-0 (+ J 1)
                                        LSBIS2 N
                                        FMT Q QLAST ROOTLAST ROOTM1LAST I RP RN
                                        ROOTP ROOTM1P ROOT ROOTM1 EXPINC))))))))
  (MV Q QLAST ROOTLAST ROOTM1LAST I RP
      RN ROOTP ROOTM1P ROOT ROOTM1 EXPINC)))

(DEFUND
 FSQRT4 (OPA FMT FZ DN RMODE)
 (LET
  ((SIGNA 0)
   (EXPA 0)
   (MANA 0)
   (CLASSA 0)
   (FLAGS (BITS 0 7 0)))
  (MV-LET
   (SIGNA EXPA MANA CLASSA FLAGS)
   (ANALYZE OPA FMT FZ FLAGS)
   (IF1
    (LOGIOR1 (LOGIOR1 (LOGIOR1 (LOGIOR1 (LOG= CLASSA 0)
                                        (LOG= CLASSA 1))
                               (LOG= CLASSA 2))
                      (LOG= CLASSA 3))
             SIGNA)
    (SPECIALCASE SIGNA OPA CLASSA FMT DN FLAGS)
    (LET
     ((EXPINC (LOGAND1 (LOG= CLASSA 4)
                       (LOG= RMODE 1)))
      (SIGA 0)
      (EXPSHFT 0)
      (EXPQ 0))
     (MV-LET
      (SIGA EXPSHFT EXPQ)
      (NORMALIZE EXPA MANA FMT)
      (LET
       ((EXPODD (BITN EXPSHFT 0)))
       (IF1
        (LOGAND1 (LOG= CLASSA 4) (LOG= MANA 0))
        (SQRTPOW2 EXPQ EXPODD RMODE FMT)
        (LET
         ((RP 0)
          (RN 0)
          (Q 0)
          (QLAST 0)
          (ROOT 0)
          (ROOTM1 0)
          (ROOTLAST 0)
          (ROOTM1LAST 0)
          (ROOTP 0)
          (ROOTM1P 0)
          (I 0))
         (MV-LET
          (RP RN ROOT ROOTM1 Q I)
          (FIRSTITER SIGA EXPODD)
          (LET*
           ((EXPINC (LOGAND EXPINC (LOG= Q 0)))
            (N 0)
            (N (CASE FMT (2 (BITS 27 4 0))
                     (1 (BITS 13 4 0))
                     (0 (BITS 6 4 0))
                     (T N)))
            (LSBIS2 (LOG= FMT 1)))
           (MV-LET
            (Q QLAST ROOTLAST ROOTM1LAST I
               RP RN ROOTP ROOTM1P ROOT ROOTM1 EXPINC)
            (FSQRT4-LOOP-0 1 LSBIS2
                           N FMT Q QLAST ROOTLAST ROOTM1LAST I
                           RP RN ROOTP ROOTM1P ROOT ROOTM1 EXPINC)
            (LET
             ((EXPRND (BITS (IF1 EXPINC (+ EXPQ 1) EXPQ)
                            10 0))
              (ROOTSHFT 0)
              (ROOTM1SHFT 0)
              (ROOTPSHFT 0)
              (ROOTM1PSHFT 0))
             (MV-LET
              (ROOTSHFT ROOTM1SHFT ROOTPSHFT ROOTM1PSHFT)
              (CASE FMT
                    (0 (MV (BITS ROOT 54 42)
                           (BITS ROOTM1 54 42)
                           (BITS ROOTP 54 42)
                           (BITS ROOTM1P 54 42)))
                    (1 (MV (BITS ROOT 54 28)
                           (BITS ROOTM1 54 28)
                           (BITS ROOTP 54 28)
                           (BITS ROOTM1P 54 28)))
                    (2 (MV ROOT ROOTM1 ROOTP ROOTM1P))
                    (T (MV ROOTSHFT
                           ROOTM1SHFT ROOTPSHFT ROOTM1PSHFT)))
              (LET
               ((QTRUNC 0) (QINC 0) (STK 0))
               (MV-LET (QTRUNC QINC STK)
                       (COMPUTEQ ROOTSHFT ROOTM1SHFT
                                 ROOTPSHFT ROOTM1PSHFT RP RN LSBIS2)
                       (LET ((QRND 0)
                             (QRNDDEN 0)
                             (INX 0)
                             (INXDEN 0))
                            (MV-LET (QRND INX QRNDDEN INXDEN)
                                    (ROUNDER QTRUNC QINC STK 0 EXPRND RMODE FMT)
                                    (FINAL QRND INX QRNDDEN INXDEN 0 EXPRND
                                           RMODE FZ FMT FLAGS)))))))))))))))))))

