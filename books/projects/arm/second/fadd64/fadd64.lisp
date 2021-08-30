(IN-PACKAGE "RTL")

(INCLUDE-BOOK "rtl/rel11/lib/rac" :DIR :SYSTEM)

(SET-IGNORE-OK T)

(SET-IRRELEVANT-FORMALS-OK T)

(DEFUND DEFNAN
        NIL (BITS 9221120237041090560 63 0))

(DEFUND COMPUTERNDDIR (RMODE SIGN)
        (IF1 (LOG= RMODE 0)
             0
             (IF1 (LOGIOR1 (LOGIOR1 (LOG= RMODE 3)
                                    (LOGAND1 (LOG= RMODE 1) SIGN))
                           (LOGAND1 (LOG= RMODE 2) (LOGNOT1 SIGN)))
                  1 2)))

(DEFUND GAG (X)
        (BITS (LOGIOR X 2251799813685248) 63 0))

(DEFUND SIGN (OP) (BITN OP 116))

(DEFUND EXPNT (OP) (BITS OP 115 105))

(DEFUND FRAC (OP) (BITS OP 104 0))

(DEFUND CHECKDENORM (OP FLAGS FZ)
        (IF1 (LOGAND1 (LOGAND1 FZ (LOG= (EXPNT OP) 0))
                      (LOG<> (FRAC OP) 0))
             (MV (SETBITS OP 117 104 0 0)
                 (SETBITN FLAGS 8 7 1))
             (MV OP FLAGS)))

(DEFUND
 CHECKSPECIAL
 (OPA OPB FZ DN
      RMODE OPBLONG MULOVFL PIZ MULSTK FLAGS)
 (LET*
  ((SIGNA (SIGN OPA))
   (SIGNB (SIGN OPB))
   (EXPA (EXPNT OPA))
   (EXPB (EXPNT OPB))
   (FRACA (FRAC OPA))
   (FRACB (FRAC OPB))
   (OPAZERO (LOGAND1 (LOG= EXPA 0) (LOG= FRACA 0)))
   (OPAINF (LOGAND1 (LOG= EXPA 2047)
                    (LOG= FRACA 0)))
   (OPANAN (LOGAND1 (LOG= EXPA 2047)
                    (LOG<> FRACA 0)))
   (OPAQNAN (LOGAND1 OPANAN (BITN FRACA 104)))
   (OPASNAN (LOGAND1 OPANAN (LOGNOT1 (BITN FRACA 104))))
   (OPBZERO (LOGAND1 (LOGAND1 (LOGAND1 (LOG= EXPB 0) (LOG= FRACB 0))
                              (LOGNOT1 MULOVFL))
                     (LOGNOT1 MULSTK)))
   (OPBINF (LOGAND1 (LOGAND1 (LOG= EXPB 2047)
                             (LOG= FRACB 0))
                    (LOGNOT1 OPBLONG)))
   (OPBNAN (LOGAND1 (LOGAND1 (LOG= EXPB 2047)
                             (LOG<> FRACB 0))
                    (LOGNOT1 OPBLONG)))
   (OPBQNAN (LOGAND1 OPBNAN (BITN FRACB 104)))
   (OPBSNAN (LOGAND1 OPBNAN (LOGNOT1 (BITN FRACB 104))))
   (ISSPECIAL (FALSE$))
   (IOC (FALSE$))
   (D (BITS 0 63 0)))
  (IF1
   OPASNAN
   (MV (TRUE$)
       (BITS (IF1 DN (DEFNAN)
                  (GAG (BITS OPA 116 53)))
             63 0)
       (SETBITN FLAGS 8 0 1))
   (MV-LET
    (FLAGS ISSPECIAL D)
    (IF1
     PIZ (MV FLAGS (TRUE$) (DEFNAN))
     (MV-LET
      (ISSPECIAL D FLAGS)
      (IF1
       OPBSNAN
       (MV (TRUE$)
           (BITS (IF1 DN (DEFNAN)
                      (GAG (BITS OPB 116 53)))
                 63 0)
           (SETBITN FLAGS 8 0 1))
       (MV-LET
        (FLAGS ISSPECIAL D)
        (IF1
         OPAQNAN
         (MV FLAGS (TRUE$)
             (BITS (IF1 DN (DEFNAN) (BITS OPA 116 53))
                   63 0))
         (IF1
          OPBQNAN
          (MV FLAGS (TRUE$)
              (BITS (IF1 DN (DEFNAN) (BITS OPB 116 53))
                    63 0))
          (MV-LET
           (ISSPECIAL D FLAGS)
           (IF1
            OPAINF
            (LET ((ISSPECIAL (TRUE$)))
                 (MV-LET (D FLAGS)
                         (IF1 (LOGAND1 OPBINF (LOG<> SIGNA SIGNB))
                              (MV (DEFNAN) (SETBITN FLAGS 8 0 1))
                              (MV (BITS OPA 116 53) FLAGS))
                         (MV ISSPECIAL D FLAGS)))
            (MV-LET
             (ISSPECIAL D)
             (IF1
               OPBINF (MV (TRUE$) (BITS OPB 116 53))
               (IF1 (LOGAND1 (LOGAND1 OPAZERO OPBZERO)
                             (LOG= SIGNA SIGNB))
                    (MV (TRUE$) (SETBITN D 64 63 SIGNA))
                    (IF1 (LOGAND1 (LOGAND1 (LOGAND1 (LOGAND1 (LOG= EXPA EXPB)
                                                             (LOG= FRACA FRACB))
                                                    (LOGNOT1 MULOVFL))
                                           (LOGNOT1 MULSTK))
                                  (LOG<> SIGNA SIGNB))
                         (MV (TRUE$)
                             (IF1 (LOG= RMODE 2)
                                  (SETBITN D 64 63 1)
                                  D))
                         (MV ISSPECIAL D))))
             (MV ISSPECIAL D FLAGS)))
           (MV FLAGS ISSPECIAL D))))
        (MV ISSPECIAL D FLAGS)))
      (MV FLAGS ISSPECIAL D)))
    (MV ISSPECIAL D FLAGS)))))

(DEFUND ISFAR (EXPA EXPB USA)
        (LET* ((EXPAP1 (BITS (+ EXPA 1) 11 0))
               (EXPBP1 (BITS (+ EXPB 1) 11 0))
               (ISNEAR (LOGAND1 USA
                                (LOGIOR1 (LOGIOR1 (LOG= EXPA EXPB)
                                                  (LOG= EXPA EXPBP1))
                                         (LOG= EXPB EXPAP1)))))
              (LOGNOT1 ISNEAR)))

(DEFUND
 ADD (OPA OPB FAR USA MULSTK)
 (LET*
  ((SIGNA (SIGN OPA))
   (SIGNB (SIGN OPB))
   (EXPA (EXPNT OPA))
   (EXPB (EXPNT OPB))
   (FRACA (FRAC OPA))
   (FRACB (FRAC OPB))
   (FRACL 0)
   (FRACS 0)
   (OPBGEOPA (LOGIOR1 (LOG> EXPB EXPA)
                      (LOGAND1 (LOG= EXPB EXPA)
                               (LOG>= FRACB FRACA))))
   (SIGA (BITS 0 107 0))
   (SIGA (SETBITN SIGA 108 106 (LOG<> EXPA 0)))
   (SIGA (SETBITS SIGA 108 105 1 FRACA))
   (SIGB (BITS 0 107 0))
   (SIGB (SETBITN SIGB 108 106 (LOG<> EXPB 0)))
   (SIGB (SETBITS SIGB 108 105 1 FRACB))
   (SIGAPRIME SIGA)
   (SIGBPRIME SIGB))
  (MV-LET
   (SIGAPRIME SIGBPRIME)
   (IF1 (LOGAND1 FAR USA)
        (MV (BITS (ASH SIGAPRIME 1) 107 0)
            (BITS (ASH SIGBPRIME 1) 107 0))
        (MV SIGAPRIME SIGBPRIME))
   (LET
    ((SIGNL 0)
     (SIGL 0)
     (SIGS 0)
     (EXPDIFF 0))
    (MV-LET
     (SIGNL SIGL SIGS EXPDIFF)
     (IF1 OPBGEOPA
          (MV SIGNB SIGBPRIME SIGAPRIME
              (IF1 (LOGAND1 (LOG= EXPA 0) (LOG<> EXPB 0))
                   (BITS (- (- EXPB EXPA) 1) 11 0)
                   (BITS (- EXPB EXPA) 11 0)))
          (MV SIGNA SIGAPRIME SIGBPRIME
              (IF1 (LOGAND1 (LOG= EXPB 0) (LOG<> EXPA 0))
                   (BITS (- (- EXPA EXPB) 1) 11 0)
                   (BITS (- EXPA EXPB) 11 0))))
     (LET*
      ((RSHIFT (BITS EXPDIFF 6 0))
       (RSHIFT (IF1 (LOG<> (BITS EXPDIFF 11 7) 0)
                    (BITS (LOGIOR RSHIFT 112) 6 0)
                    RSHIFT))
       (SIGSHFT (BITS (ASH SIGS (- RSHIFT)) 107 0))
       (SHIFTOUT (LOG<> (ASH SIGSHFT RSHIFT) SIGS)))
      (MV
         (BITS (+ (+ SIGL
                     (BITS (IF1 USA (LOGNOT SIGSHFT) SIGSHFT)
                           107 0))
                  (LOGAND1 USA
                           (LOGNOT1 (LOGIOR1 (LOGAND1 MULSTK (LOGNOT1 OPBGEOPA))
                                             (LOGAND1 FAR SHIFTOUT)))))
               107 0)
         (LOGIOR1 MULSTK (LOGAND1 FAR SHIFTOUT))
         SIGNL)))))))

(DEFUND CLZ128-LOOP-0 (I N K C Z)
        (DECLARE (XARGS :MEASURE (NFIX (- N I))))
        (IF (AND (INTEGERP I) (INTEGERP N) (< I N))
            (LET* ((C (AS I
                          (BITS (IF1 (AG (+ (* 2 I) 1) Z)
                                     (AG (* 2 I) C)
                                     (AG (+ (* 2 I) 1) C))
                                6 0)
                          C))
                   (C (AS I
                          (SETBITN (AG I C)
                                   7 K (AG (+ (* 2 I) 1) Z))
                          C))
                   (Z (AS I
                          (LOGAND1 (AG (+ (* 2 I) 1) Z)
                                   (AG (* 2 I) Z))
                          Z)))
                  (CLZ128-LOOP-0 (+ I 1) N K C Z))
            (MV C Z)))

(DEFUND CLZ128-LOOP-1 (K N C Z)
        (DECLARE (XARGS :MEASURE (NFIX (- 7 K))))
        (IF (AND (INTEGERP K) (< K 7))
            (LET ((N (FLOOR N 2)))
                 (MV-LET (C Z)
                         (CLZ128-LOOP-0 0 N K C Z)
                         (CLZ128-LOOP-1 (+ K 1) N C Z)))
            (MV N C Z)))

(DEFUND CLZ128-LOOP-2 (I X Z C)
        (DECLARE (XARGS :MEASURE (NFIX (- 128 I))))
        (IF (AND (INTEGERP I) (< I 128))
            (LET ((Z (AS I (LOGNOT1 (BITN X I)) Z))
                  (C (AS I (BITS 0 6 0) C)))
                 (CLZ128-LOOP-2 (+ I 1) X Z C))
            (MV Z C)))

(DEFUND CLZ128 (X)
        (LET ((Z NIL) (C NIL))
             (MV-LET (Z C)
                     (CLZ128-LOOP-2 0 X Z C)
                     (LET ((N 128))
                          (MV-LET (N C Z)
                                  (CLZ128-LOOP-1 0 N C Z)
                                  (AG 0 C))))))

(DEFUND LZA128 (A B)
        (LET* ((P (LOGXOR A B))
               (K (LOGAND (BITS (LOGNOT A) 127 0)
                          (BITS (LOGNOT B) 127 0)))
               (W (BITS (LOGNOT (LOGXOR P (ASH K 1)))
                        127 0)))
              (CLZ128 (BITS (ASH W (- 1)) 127 0))))

(DEFUND
 COMPUTELZA (OPA OPB)
 (LET*
  ((IN1LZA (BITS 0 127 0))
   (IN2LZA (BITS 0 127 0))
   (EXPA (EXPNT OPA))
   (EXPB (EXPNT OPB))
   (FRACA (FRAC OPA))
   (FRACB (FRAC OPB))
   (FRACL 0)
   (FRACS 0)
   (OPBGEOPA (LOGIOR1 (LOG> EXPB EXPA)
                      (LOGAND1 (LOG= EXPB EXPA)
                               (LOG>= FRACB FRACA)))))
  (MV-LET
   (FRACL FRACS)
   (IF1 OPBGEOPA (MV FRACB FRACA)
        (MV FRACA FRACB))
   (LET*
       ((IN1LZA (SETBITN IN1LZA 128 127 1))
        (IN1LZA (SETBITS IN1LZA 128 126 22 FRACL))
        (IN2LZA (IF1 (LOG= (BITN EXPB 0) (BITN EXPA 0))
                     (LET ((IN2LZA (BITS (- (ASH 1 22) 1) 127 0)))
                          (SETBITS IN2LZA 128 126 22 (LOGNOT FRACS)))
                     (LET* ((IN2LZA (BITS (- (ASH 1 21) 1) 127 0))
                            (IN2LZA (SETBITS IN2LZA 128 125 21 (LOGNOT FRACS))))
                           (SETBITN IN2LZA 128 127 1)))))
       (LZA128 IN1LZA IN2LZA)))))

(DEFUND COMPUTELSHIFT (OPA OPB FAR USA)
        (LET* ((EXPA (EXPNT OPA))
               (EXPB (EXPNT OPB))
               (EXPL (BITS (IF1 (LOG>= EXPA EXPB) EXPA EXPB)
                           11 0))
               (LSHIFT 0)
               (EXPSHFT 0)
               (LZA (COMPUTELZA OPA OPB)))
              (IF1 FAR
                   (MV (BITS 0 6 0)
                       (BITS (IF1 USA (- EXPL 1) EXPL) 11 0))
                   (IF1 (LOG< LZA EXPL)
                        (MV LZA (BITS (- EXPL LZA) 11 0))
                        (MV (BITS (IF1 (LOG= EXPL 0) 0 (- EXPL 1))
                                  6 0)
                            (BITS 0 11 0))))))

(DEFUND RNDINFO (SUM STK LSHIFT RNDDIR)
        (LET* ((LOVFLMASK (BITS (ASH 36028797018963968 (- LSHIFT))
                                55 0))
               (GOVFLMASK (BITS (ASH LOVFLMASK (- 1)) 54 0))
               (SOVFLMASK (BITS (ASH 18014398509481983 (- LSHIFT))
                                53 0))
               (LNORMMASK (BITS (ASH LOVFLMASK (- 1)) 54 0))
               (GNORMMASK (BITS (ASH LOVFLMASK (- 2)) 53 0))
               (SNORMMASK (BITS (ASH SOVFLMASK (- 1)) 52 0))
               (LOVFL (LOG<> (LOGAND SUM LOVFLMASK) 0))
               (GOVFL (LOG<> (LOGAND SUM GOVFLMASK) 0))
               (SOVFL (LOGIOR1 (LOG<> (LOGAND SUM SOVFLMASK) 0)
                               STK))
               (LNORM (LOG<> (LOGAND SUM LNORMMASK) 0))
               (GNORM (LOG<> (LOGAND SUM GNORMMASK) 0))
               (SNORM (LOGIOR1 (LOG<> (LOGAND SUM SNORMMASK) 0)
                               STK)))
              (MV (LOGIOR1 (LOGAND1 (LOGAND1 (LOG= RNDDIR 0) GOVFL)
                                    (LOGIOR1 LOVFL SOVFL))
                           (LOGAND1 (LOG= RNDDIR 2)
                                    (LOGIOR1 GOVFL SOVFL)))
                  (LOGIOR1 (LOGAND1 (LOGAND1 (LOG= RNDDIR 0) GNORM)
                                    (LOGIOR1 LNORM SNORM))
                           (LOGAND1 (LOG= RNDDIR 2)
                                    (LOGIOR1 GNORM SNORM)))
                  (LOGIOR1 GOVFL SOVFL)
                  (LOGIOR1 GNORM SNORM))))

(DEFUND
 FADD64
 (OPA OPB FZ
      DN RMODE FMA INZ PIZ EXPOVFL MULEXCPS)
 (LET*
  ((D 0)
   (FLAGS (BITS 0 7 0))
   (OPBLONG (LOGAND1 FMA (LOGNOT1 INZ)))
   (MULOVFL (LOGAND1 OPBLONG EXPOVFL))
   (PIZ (LOGAND1 FMA PIZ))
   (MULSTK (LOGAND1 (BITN MULEXCPS 4) OPBLONG))
   (FLAGS (IF1 FMA
               (LET ((FLAGS MULEXCPS))
                    (SETBITN FLAGS 8 4
                             (LOGAND1 (BITN FLAGS 4)
                                      (LOGNOT1 OPBLONG))))
               FLAGS))
   (OPAX (BITS 0 116 0))
   (OPAX (SETBITS OPAX 117 116 53 OPA))
   (OPAZ 0)
   (OPBZ 0))
  (MV-LET
   (OPAZ FLAGS)
   (CHECKDENORM OPAX FLAGS FZ)
   (MV-LET
    (OPBZ FLAGS)
    (IF1 (LOGNOT1 FMA)
         (CHECKDENORM OPB FLAGS FZ)
         (MV OPB FLAGS))
    (LET
     ((ISSPECIAL 0))
     (MV-LET
      (ISSPECIAL D FLAGS)
      (CHECKSPECIAL OPAZ OPBZ FZ DN
                    RMODE OPBLONG MULOVFL PIZ MULSTK FLAGS)
      (IF1
       ISSPECIAL (MV D FLAGS)
       (LET*
        ((USA (LOG<> (SIGN OPAZ) (SIGN OPBZ)))
         (FAR (ISFAR (EXPNT OPAZ) (EXPNT OPBZ) USA))
         (SUM 0)
         (STK 0)
         (SIGNL 0))
        (MV-LET
         (SUM STK SIGNL)
         (ADD OPAZ OPBZ FAR USA MULSTK)
         (LET
          ((LSHIFT 0) (EXPSHFT 0))
          (MV-LET
           (LSHIFT EXPSHFT)
           (COMPUTELSHIFT OPAZ OPBZ FAR USA)
           (LET*
            ((SUMSHFT (BITS (ASH SUM LSHIFT) 107 0))
             (SIGNOUT (IF1 MULOVFL (SIGN OPB) SIGNL))
             (RNDDIR (COMPUTERNDDIR RMODE SIGNOUT))
             (INCOVFL 0)
             (INCNORM 0)
             (INXOVFL 0)
             (INXNORM 0))
            (MV-LET
             (INCOVFL INCNORM INXOVFL INXNORM)
             (RNDINFO SUM STK LSHIFT RNDDIR)
             (LET*
              ((SUMUNRND (BITS SUMSHFT 107 54))
               (SUMNORM (BITS (+ SUMUNRND INCNORM) 53 0))
               (SUMOVFL (BITS (+ (BITS SUMUNRND 53 1) INCOVFL)
                              53 0))
               (TINY (LOGAND1 (LOGNOT1 (BITN SUMUNRND 53))
                              (LOGNOT1 (BITN SUMUNRND 52))))
               (OVFL (BITN SUMNORM 53))
               (OVFL2 (LOGAND1 (LOG= (BITS SUMUNRND 53 1)
                                     (- (ASH 1 53) 1))
                               INCOVFL))
               (INFORMAX
                 (LOGIOR1 (LOGIOR1 (LOGIOR1 (LOGAND1 (LOG= EXPSHFT 2046)
                                                     (LOGIOR1 OVFL OVFL2))
                                            (LOGAND1 (LOG= EXPSHFT 2045) OVFL2))
                                   (LOGAND1 (LOG= EXPSHFT 2047) OPBLONG))
                          MULOVFL))
               (EXPOUT 0)
               (FRACOUT 0))
              (MV-LET
               (EXPOUT FRACOUT FLAGS)
               (IF1
                INFORMAX
                (MV-LET (EXPOUT FRACOUT)
                        (IF1 (LOG= RNDDIR 1)
                             (MV (BITS 2046 10 0)
                                 (BITS 4503599627370495 51 0))
                             (MV (BITS 2047 10 0) (BITS 0 51 0)))
                        (MV EXPOUT FRACOUT
                            (SETBITN (SETBITN FLAGS 8 2 1) 8 4 1)))
                (IF1
                 TINY
                 (IF1 FZ
                      (MV (BITS 0 10 0)
                          (BITS 0 51 0)
                          (SETBITN FLAGS 8 3 1))
                      (IF1 (BITN SUMNORM 52)
                           (MV (BITS 1 10 0)
                               (BITS 0 51 0)
                               (SETBITN (SETBITN FLAGS 8 3 1) 8 4 1))
                           (MV (BITS EXPSHFT 10 0)
                               (BITS SUMNORM 51 0)
                               (IF1 INXNORM
                                    (LET ((FLAGS (SETBITN FLAGS 8 3 1)))
                                         (SETBITN FLAGS 8 4 1))
                                    FLAGS))))
                 (IF1 OVFL2
                      (MV (BITS (+ EXPSHFT 2) 10 0)
                          (BITS 0 51 0)
                          (SETBITN FLAGS
                                   8 4 (LOGIOR1 (BITN FLAGS 4) INXOVFL)))
                      (IF1 OVFL
                           (MV (BITS (IF1 (LOG= EXPSHFT 0) 2 (+ EXPSHFT 1))
                                     10 0)
                               (BITS SUMOVFL 51 0)
                               (SETBITN FLAGS
                                        8 4 (LOGIOR1 (BITN FLAGS 4) INXOVFL)))
                           (MV (BITS (IF1 (LOGAND1 (LOG= EXPSHFT 0)
                                                   (BITN SUMNORM 52))
                                          1 EXPSHFT)
                                     10 0)
                               (BITS SUMNORM 51 0)
                               (SETBITN FLAGS 8
                                        4 (LOGIOR1 (BITN FLAGS 4) INXNORM)))))))
               (MV (SETBITS (SETBITS (SETBITN D 64 63 SIGNOUT)
                                     64 62 52 EXPOUT)
                            64 51 0 FRACOUT)
                   FLAGS))))))))))))))))

