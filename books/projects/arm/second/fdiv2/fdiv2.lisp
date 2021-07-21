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
               (3 (LET ((SIGN (BITN OP 63))
                        (EXP (BITS OP 62 52)))
                       (MV SIGN EXP (LOG= (SI EXP 13) 2047)
                           (BITS OP 51 0)
                           (BITS 2251799813685248 51 0))))
               (2 (LET ((SIGN (BITN OP 31))
                        (EXP (BITS OP 30 23)))
                       (MV SIGN EXP (LOG= (SI EXP 13) 255)
                           (BITS OP 22 0)
                           (BITS 4194304 51 0))))
               (1 (LET ((SIGN (BITN OP 15))
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
                                                      (IF1 (LOG<> FMT 1)
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

(DEFUND
 SPECIALCASE
 (SIGN OPA OPB CLASSA CLASSB FMT DN FLAGS)
 (LET
  ((ISSPECIAL (FALSE$))
   (D (BITS 0 63 0))
   (ANAN 0)
   (BNAN 0)
   (MANMSB 0)
   (INFINITY 0)
   (DEFNAN 0)
   (ZERO (BITS 0 63 0)))
  (MV-LET
   (ANAN BNAN ZERO INFINITY MANMSB)
   (CASE FMT
         (3 (MV (BITS OPA 63 0)
                (BITS OPB 63 0)
                (SETBITN ZERO 64 63 SIGN)
                (BITS 9218868437227405312 63 0)
                (BITS 2251799813685248 63 0)))
         (2 (MV (BITS OPA 31 0)
                (BITS OPB 31 0)
                (SETBITN ZERO 64 31 SIGN)
                (BITS 2139095040 63 0)
                (BITS 4194304 63 0)))
         (1 (MV (BITS OPA 15 0)
                (BITS OPB 15 0)
                (SETBITN ZERO 64 15 SIGN)
                (BITS 31744 63 0)
                (BITS 512 63 0)))
         (T (MV ANAN BNAN ZERO INFINITY MANMSB)))
   (LET
    ((DEFNAN (LOGIOR INFINITY MANMSB)))
    (IF1
     (LOG= CLASSA 2)
     (MV (BITS (IF1 DN DEFNAN (LOGIOR ANAN MANMSB))
               63 0)
         (SETBITN FLAGS 8 0 1))
     (IF1
      (LOG= CLASSB 2)
      (MV (BITS (IF1 DN DEFNAN (LOGIOR BNAN MANMSB))
                63 0)
          (SETBITN FLAGS 8 0 1))
      (MV-LET
       (FLAGS D)
       (IF1
        (LOG= CLASSA 3)
        (MV FLAGS (BITS (IF1 DN DEFNAN ANAN) 63 0))
        (IF1
         (LOG= CLASSB 3)
         (MV FLAGS (BITS (IF1 DN DEFNAN BNAN) 63 0))
         (MV-LET
           (D FLAGS)
           (IF1 (LOG= CLASSA 1)
                (IF1 (LOG= CLASSB 1)
                     (MV DEFNAN (SETBITN FLAGS 8 0 1))
                     (MV (LOGIOR INFINITY ZERO) FLAGS))
                (MV-LET (FLAGS D)
                        (IF1 (LOG= CLASSB 1)
                             (MV FLAGS ZERO)
                             (MV-LET (D FLAGS)
                                     (IF1 (LOG= CLASSA 0)
                                          (IF1 (LOG= CLASSB 0)
                                               (MV DEFNAN (SETBITN FLAGS 8 0 1))
                                               (MV ZERO FLAGS))
                                          (IF1 (LOG= CLASSB 0)
                                               (MV (LOGIOR INFINITY ZERO)
                                                   (SETBITN FLAGS 8 1 1))
                                               (MV D FLAGS)))
                                     (MV FLAGS D)))
                        (MV D FLAGS)))
           (MV FLAGS D))))
       (MV D FLAGS))))))))

(DEFUND
 NORMALIZE (EXPA EXPB MANA MANB FMT)
 (LET
    ((SIGA (BITS 0 52 0))
     (SIGB (BITS 0 52 0))
     (BIAS 0))
    (MV-LET
         (SIGA SIGB BIAS)
         (CASE FMT (3 (MV MANA MANB 1023))
               (2 (MV (SETBITS SIGA 53 51 29 MANA)
                      (SETBITS SIGB 53 51 29 MANB)
                      127))
               (1 (MV (SETBITS SIGA 53 51 42 MANA)
                      (SETBITS SIGB 53 51 42 MANB)
                      15))
               (T (MV SIGA SIGB BIAS)))
         (LET ((EXPASHFT 0) (EXPBSHFT 0))
              (MV-LET (SIGA EXPASHFT)
                      (IF1 (LOG= EXPA 0)
                           (LET ((CLZ (BITS (CLZ53 SIGA) 5 0)))
                                (MV (BITS (ASH SIGA CLZ) 52 0)
                                    (BITS (- 1 CLZ) 12 0)))
                           (MV (SETBITN SIGA 53 52 1) EXPA))
                      (MV-LET (SIGB EXPBSHFT)
                              (IF1 (LOG= EXPB 0)
                                   (LET ((CLZ (BITS (CLZ53 SIGB) 5 0)))
                                        (MV (BITS (ASH SIGB CLZ) 52 0)
                                            (BITS (- 1 CLZ) 12 0)))
                                   (MV (SETBITN SIGB 53 52 1) EXPB))
                              (MV SIGA SIGB
                                  (BITS (+ (- (SI EXPASHFT 13) (SI EXPBSHFT 13))
                                           BIAS)
                                        12 0))))))))

(DEFUND NEXTDIGIT (RS3 RC3)
        (LET ((R4 (BITS (+ (SI RS3 3) (SI RC3 3)) 3 0)))
             (IF1 (LOG< (SI R4 4) -1)
                  -1 (IF1 (LOG= (SI R4 4) -1) 0 1))))

(DEFUND
 NEXTREM (SUM0 CAR0 D57 Q FMT)
 (LET
    ((SUMIN (BITS (ASH SUM0 1) 56 0))
     (CARIN (BITS (ASH CAR0 1) 56 0))
     (DIN (BITS 0 56 0))
     (SUMOUT (BITS 0 56 0))
     (CAROUT (BITS 0 56 0)))
    (MV-LET
         (DIN SUMOUT CAROUT)
         (IF1 (LOG= Q 0)
              (MV DIN (LOGXOR SUMIN CARIN)
                  (SETBITS CAROUT 57 56 1
                           (LOGAND (BITS SUMIN 55 0)
                                   (BITS CARIN 55 0))))
              (LET* ((DIN (IF1 (LOG= Q 1)
                               (LET ((DIN (BITS (LOGNOT D57) 56 0)))
                                    (CASE FMT (2 (SETBITS DIN 57 29 0 0))
                                          (1 (SETBITS DIN 57 42 0 0))
                                          (T DIN)))
                               D57))
                     (SUMOUT (LOGXOR (LOGXOR SUMIN CARIN) DIN))
                     (CAROUT (SETBITS CAROUT 57 56 1
                                      (LOGIOR (LOGIOR (LOGAND (BITS SUMIN 55 0)
                                                              (BITS CARIN 55 0))
                                                      (LOGAND (BITS SUMIN 55 0)
                                                              (BITS DIN 55 0)))
                                              (LOGAND (BITS CARIN 55 0)
                                                      (BITS DIN 55 0))))))
                    (MV DIN SUMOUT
                        (IF1 (LOG= Q 1)
                             (CASE FMT (3 (SETBITN CAROUT 57 0 1))
                                   (2 (SETBITN CAROUT 57 30 1))
                                   (1 (SETBITN CAROUT 57 43 1))
                                   (T CAROUT))
                             CAROUT))))
         (IF1 (LOG<> (BITN SUMOUT 56)
                     (BITN CAROUT 56))
              (MV (SETBITN SUMOUT 57 56 0)
                  (SETBITN CAROUT 57 56 1))
              (IF1 (LOG= Q 1)
                   (MV (SETBITN SUMOUT 57 56 0)
                       (SETBITN CAROUT 57 56 0))
                   (IF1 (LOG= Q -1)
                        (MV (SETBITN SUMOUT 57 56 1)
                            (SETBITN CAROUT 57 56 1))
                        (MV SUMOUT CAROUT)))))))

(DEFUND NEXTQUOT (QUOT QUOTM1 Q I)
        (MV (SETBITN (BITS (IF1 (LOG= Q -1) QUOTM1 QUOT)
                           54 0)
                     55 (- 55 I)
                     (LOG<> Q 0))
            (SETBITN (BITS (IF1 (LOG= Q 1) QUOT QUOTM1) 54 0)
                     55 (- 55 I)
                     (LOG= Q 0))))

(DEFUND
 FINAL
 (QRND INX SIGN EXPQ RMODE FZ FMT FLAGS)
 (LET
  ((SELMAXNORM (LOGIOR1 (LOGIOR1 (LOGAND1 (LOG= RMODE 2) (LOGNOT1 SIGN))
                                 (LOGAND1 (LOG= RMODE 1) SIGN))
                        (LOG= RMODE 3)))
   (D (BITS 0 63 0)))
  (CASE
   FMT
   (3
    (LET
       ((D (SETBITN D 64 63 SIGN)))
       (IF1 (LOG>= (SI EXPQ 13) 2047)
            (MV (IF1 SELMAXNORM
                     (LET ((D (SETBITS D 64 62 52 2046)))
                          (SETBITS D 64 51 0 4503599627370495))
                     (LET ((D (SETBITS D 64 62 52 2047)))
                          (SETBITS D 64 51 0 0)))
                (SETBITN (SETBITN FLAGS 8 2 1) 8 4 1))
            (IF1 (LOG<= (SI EXPQ 13) 0)
                 (IF1 FZ (MV D (SETBITN FLAGS 8 3 1))
                      (LET* ((EXP (BITN QRND 52))
                             (D (SETBITS D 64 62 52 EXP))
                             (D (SETBITS D 64 51 0 (BITS QRND 51 0)))
                             (FLAGS (SETBITN FLAGS
                                             8 4 (LOGIOR1 (BITN FLAGS 4) INX))))
                            (MV D
                                (SETBITN FLAGS
                                         8 3 (LOGIOR1 (BITN FLAGS 3) INX)))))
                 (MV (SETBITS (SETBITS D 64 62 52 (SI EXPQ 13))
                              64 51 0 (BITS QRND 51 0))
                     (SETBITN FLAGS
                              8 4 (LOGIOR1 (BITN FLAGS 4) INX)))))))
   (2
    (LET
       ((D (SETBITN D 64 31 SIGN)))
       (IF1 (LOG>= (SI EXPQ 13) 255)
            (MV (IF1 SELMAXNORM
                     (LET ((D (SETBITS D 64 30 23 254)))
                          (SETBITS D 64 22 0 8388607))
                     (LET ((D (SETBITS D 64 30 23 255)))
                          (SETBITS D 64 22 0 0)))
                (SETBITN (SETBITN FLAGS 8 2 1) 8 4 1))
            (IF1 (LOG<= (SI EXPQ 13) 0)
                 (IF1 FZ (MV D (SETBITN FLAGS 8 3 1))
                      (LET* ((EXP (BITN QRND 23))
                             (D (SETBITS D 64 30 23 EXP))
                             (D (SETBITS D 64 22 0 (BITS QRND 22 0)))
                             (FLAGS (SETBITN FLAGS
                                             8 4 (LOGIOR1 (BITN FLAGS 4) INX))))
                            (MV D
                                (SETBITN FLAGS
                                         8 3 (LOGIOR1 (BITN FLAGS 3) INX)))))
                 (MV (SETBITS (SETBITS D 64 30 23 (SI EXPQ 13))
                              64 22 0 (BITS QRND 22 0))
                     (SETBITN FLAGS
                              8 4 (LOGIOR1 (BITN FLAGS 4) INX)))))))
   (1
    (LET
       ((D (SETBITN D 64 15 SIGN)))
       (IF1 (LOG>= (SI EXPQ 13) 31)
            (MV (IF1 SELMAXNORM
                     (LET ((D (SETBITS D 64 14 10 30)))
                          (SETBITS D 64 9 0 1023))
                     (LET ((D (SETBITS D 64 14 10 31)))
                          (SETBITS D 64 9 0 0)))
                (SETBITN (SETBITN FLAGS 8 2 1) 8 4 1))
            (IF1 (LOG<= (SI EXPQ 13) 0)
                 (IF1 FZ (MV D (SETBITN FLAGS 8 3 1))
                      (LET* ((EXP (BITN QRND 10))
                             (D (SETBITS D 64 14 10 EXP))
                             (D (SETBITS D 64 9 0 (BITS QRND 9 0)))
                             (FLAGS (SETBITN FLAGS
                                             8 4 (LOGIOR1 (BITN FLAGS 4) INX))))
                            (MV D
                                (SETBITN FLAGS
                                         8 3 (LOGIOR1 (BITN FLAGS 3) INX)))))
                 (MV (SETBITS (SETBITS D 64 14 10 (SI EXPQ 13))
                              64 9 0 (BITS QRND 9 0))
                     (SETBITN FLAGS
                              8 4 (LOGIOR1 (BITN FLAGS 4) INX)))))))
   (T (MV D FLAGS)))))

(DEFUND
  FDIVLANE-LOOP-0
  (I N D57 FMTREM Q RS RC QUOT QUOTM1)
  (DECLARE (XARGS :MEASURE (NFIX (- (1+ N) I))))
  (IF (AND (INTEGERP I)
           (INTEGERP N)
           (AND (<= I N) (<= I 55)))
      (LET ((Q (NEXTDIGIT (BITS RS 56 54)
                          (BITS RC 56 54))))
           (MV-LET (RS RC)
                   (NEXTREM RS RC D57 Q FMTREM)
                   (MV-LET (QUOT QUOTM1)
                           (NEXTQUOT QUOT QUOTM1 Q I)
                           (FDIVLANE-LOOP-0 (+ I 1)
                                            N D57 FMTREM Q RS RC QUOT QUOTM1))))
      (MV Q RS RC QUOT QUOTM1)))

(DEFUND
 FDIVLANE (OPA OPB FMT VEC FZ DN RMODE)
 (LET
  ((SIGNA 0)
   (SIGNB 0)
   (EXPA 0)
   (EXPB 0)
   (MANA 0)
   (MANB 0)
   (CLASSA 0)
   (CLASSB 0)
   (FLAGS (BITS 0 7 0)))
  (MV-LET
   (SIGNA EXPA MANA CLASSA FLAGS)
   (ANALYZE OPA FMT FZ FLAGS)
   (MV-LET
    (SIGNB EXPB MANB CLASSB FLAGS)
    (ANALYZE OPB FMT FZ FLAGS)
    (LET
     ((SIGN (LOGXOR SIGNA SIGNB)))
     (IF1
      (LOGIOR1
          (LOGIOR1 (LOGIOR1 (LOGIOR1 (LOGIOR1 (LOGIOR1 (LOGIOR1 (LOG= CLASSA 0)
                                                                (LOG= CLASSA 1))
                                                       (LOG= CLASSA 2))
                                              (LOG= CLASSA 3))
                                     (LOG= CLASSB 0))
                            (LOG= CLASSB 1))
                   (LOG= CLASSB 2))
          (LOG= CLASSB 3))
      (SPECIALCASE SIGN OPA OPB CLASSA CLASSB FMT DN FLAGS)
      (LET
       ((X 0) (D 0) (EXPQ 0))
       (MV-LET
        (X D EXPQ)
        (NORMALIZE EXPA EXPB MANA MANB FMT)
        (LET*
         ((X57 (BITS 0 56 0))
          (D57 (BITS 0 56 0))
          (X57 (SETBITS X57 57 55 3 X))
          (D57 (SETBITS D57 57 55 3 D))
          (QTRUNC 0)
          (STK 0))
         (MV-LET
          (QTRUNC STK)
          (IF1
           (LOG= MANB 0)
           (MV (BITS (ASH X 2) 54 0) 0)
           (LET*
            ((RS (BITS 0 56 0))
             (RC (BITS 0 56 0))
             (FMTREM (BITS (IF1 VEC FMT 3) 1 0))
             (RS X57)
             (RC D57)
             (RC (BITS (LOGNOT RC) 56 0)))
            (MV-LET
             (RC RS)
             (CASE FMTREM
                   (3 (MV (SETBITS RC 57 1 0 0)
                          (SETBITN RS 57 2 1)))
                   (2 (MV (SETBITS RC 57 30 0 0)
                          (SETBITN RS 57 31 1)))
                   (1 (MV (SETBITS RC 57 43 0 0)
                          (SETBITN RS 57 44 1)))
                   (T (MV RC RS)))
             (LET*
              ((QUOT (BITS 0 54 0))
               (QUOTM1 (BITS 0 54 0))
               (QUOT (SETBITN QUOT 55 54 1))
               (Q 0)
               (C 0)
               (C (CASE FMT (3 18) (2 9) (1 4) (T C)))
               (N (+ (* 3 C) 1)))
              (MV-LET
               (Q RS RC QUOT QUOTM1)
               (FDIVLANE-LOOP-0 2 N D57 FMTREM Q RS RC QUOT QUOTM1)
               (LET*
                ((RFINAL (BITS (+ RS RC) 56 0))
                 (RSIGN (LOG< (SI RFINAL 57) 0))
                 (RNONZERO (LOG<> (SI RFINAL 57) 0))
                 (QTRUNC (BITS (IF1 RSIGN QUOTM1 QUOT) 54 0))
                 (RPLUSDS (LOGXOR (LOGXOR RS RC) D57))
                 (RPLUSDC
                      (BITS (ASH (LOGIOR (LOGIOR (LOGAND RS RC) (LOGAND RS D57))
                                         (LOGAND RC D57))
                                 1)
                            56 0))
                 (RPLUSDXOR (LOGXOR RPLUSDS RPLUSDC))
                 (RPLUSDOR (BITS (ASH (LOGIOR RPLUSDS RPLUSDC) 1)
                                 56 0))
                 (RPLUSDIS0 (LOG= RPLUSDXOR RPLUSDOR))
                 (ASSERT (IN-FUNCTION FDIVLANE
                                      (LOG= RPLUSDIS0
                                            (LOG= (+ (SI RFINAL 57) D57) 0)))))
                (MV QTRUNC
                    (LOGAND1 RNONZERO (LOGNOT1 RPLUSDIS0)))))))))
          (MV-LET
           (EXPQ STK QTRUNC)
           (IF1
             (LOG<= (SI EXPQ 13) 0)
             (LET ((SHFT (BITS (- 1 (SI EXPQ 13)) 12 0)))
                  (MV EXPQ
                      (LOGIOR STK
                              (LOGIOR1 (LOG>= SHFT 55)
                                       (LOG<> (LOGAND QTRUNC (- (ASH 1 SHFT) 1))
                                              0)))
                      (BITS (ASH QTRUNC (- SHFT)) 54 0)))
             (MV-LET (EXPQ QTRUNC)
                     (IF1 (LOGNOT1 (BITN QTRUNC 54))
                          (LET ((EXPQ (BITS (- (SI EXPQ 13) 1) 12 0)))
                               (MV EXPQ
                                   (IF1 (LOG> (SI EXPQ 13) 0)
                                        (BITS (ASH QTRUNC 1) 54 0)
                                        QTRUNC)))
                          (MV EXPQ QTRUNC))
                     (MV EXPQ STK QTRUNC)))
           (MV-LET
            (STK QTRUNC)
            (CASE FMT
                  (2 (MV (LOGIOR STK (LOG<> (BITS QTRUNC 28 0) 0))
                         (BITS (ASH QTRUNC (- 29)) 54 0)))
                  (1 (MV (LOGIOR STK (LOG<> (BITS QTRUNC 41 0) 0))
                         (BITS (ASH QTRUNC (- 42)) 54 0)))
                  (T (MV STK QTRUNC)))
            (LET*
             ((LSB (BITN QTRUNC 2))
              (GRD (BITN QTRUNC 1))
              (STK (LOGIOR STK (BITN QTRUNC 0)))
              (INX (LOGIOR1 GRD STK))
              (QRND 0)
              (QRND
               (IF1
                  (LOGIOR1
                       (LOGIOR1 (LOGAND1 (LOGAND1 (LOG= RMODE 0) GRD)
                                         (LOGIOR1 LSB STK))
                                (LOGAND1 (LOGAND1 (LOG= RMODE 1) (LOGNOT1 SIGN))
                                         (LOGIOR1 GRD STK)))
                       (LOGAND1 (LOGAND1 (LOG= RMODE 2) SIGN)
                                (LOGIOR1 GRD STK)))
                  (BITS (+ (BITS QTRUNC 54 2) 1) 52 0)
                  (BITS QTRUNC 54 2))))
             (FINAL QRND INX SIGN
                    EXPQ RMODE FZ FMT FLAGS))))))))))))))

(DEFUND FDIV2-LOOP-0
        (K NUMLANES FMT VEC FZ DN RMODE
           WIDTH DLANE FLAGSLANE D FLAGS OPA OPB)
        (DECLARE (XARGS :MEASURE (NFIX (- NUMLANES K))))
        (IF (AND (INTEGERP K)
                 (INTEGERP NUMLANES)
                 (AND (< K NUMLANES) (< K 4)))
            (MV-LET (DLANE FLAGSLANE)
                    (FDIVLANE OPA OPB FMT VEC FZ DN RMODE)
                    (LET ((D (BITS (LOGIOR D (ASH DLANE (* K WIDTH)))
                                   63 0))
                          (FLAGS (LOGIOR FLAGS FLAGSLANE))
                          (OPA (BITS (ASH OPA (- WIDTH)) 63 0))
                          (OPB (BITS (ASH OPB (- WIDTH)) 63 0)))
                         (FDIV2-LOOP-0 (+ K 1)
                                       NUMLANES FMT VEC FZ DN RMODE
                                       WIDTH DLANE FLAGSLANE D FLAGS OPA OPB)))
            (MV DLANE FLAGSLANE D FLAGS OPA OPB)))

(DEFUND FDIV2 (OPA OPB FMT VEC FZ DN RMODE)
        (LET ((D (BITS 0 63 0))
              (DLANE 0)
              (FLAGS (BITS 0 7 0))
              (FLAGSLANE 0)
              (NUMLANES (IF1 (LOGIOR1 (LOG= FMT 3) (LOGNOT1 VEC))
                             1 (IF1 (LOG= FMT 2) 2 4)))
              (WIDTH (IF1 (LOG= FMT 2) 32 16)))
             (MV-LET (DLANE FLAGSLANE D FLAGS OPA OPB)
                     (FDIV2-LOOP-0 0 NUMLANES FMT VEC FZ DN RMODE
                                   WIDTH DLANE FLAGSLANE D FLAGS OPA OPB)
                     (MV D FLAGS))))

