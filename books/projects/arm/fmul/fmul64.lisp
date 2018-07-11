(IN-PACKAGE "RTL")

(INCLUDE-BOOK "rtl/rel11/lib/rac" :DIR :SYSTEM)

(SET-IGNORE-OK T)

(SET-IRRELEVANT-FORMALS-OK T)

(DEFUN RMODENEAR NIL (BITS 0 1 0))

(DEFUN RMODEUP NIL (BITS 1 1 0))

(DEFUN RMODEDN NIL (BITS 2 1 0))

(DEFUN RMODEZERO NIL (BITS 3 1 0))

(DEFUN IDC NIL 7)

(DEFUN IXC NIL 4)

(DEFUN UFC NIL 3)

(DEFUN OFC NIL 2)

(DEFUN DZC NIL 1)

(DEFUN IOC NIL 0)

(DEFUN
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
                   (MV SIGN EXP (LOG= EXP 2047)
                       (BITS OP 51 0)
                       (BITS 2251799813685248 51 0))))
           (1 (LET ((SIGN (BITN OP 31))
                    (EXP (BITS OP 30 23)))
                   (MV SIGN EXP (LOG= EXP 255)
                       (BITS OP 22 0)
                       (BITS 4194304 51 0))))
           (0 (LET ((SIGN (BITN OP 15))
                    (EXP (BITS OP 14 10)))
                   (MV SIGN EXP (LOG= EXP 31)
                       (BITS OP 9 0)
                       (BITS 512 51 0))))
           (T (MV SIGN EXP EXPISMAX MAN MANMSB)))
     (LET ((C 0))
          (MV-LET (FLAGS C)
                  (IF1 EXPISMAX
                       (MV FLAGS
                           (IF1 (LOG= MAN 0)
                                1 (IF1 (LOGAND MAN MANMSB) 3 2)))
                       (IF1 (LOG= EXP 0)
                            (IF1 (LOG= MAN 0)
                                 (MV FLAGS 0)
                                 (MV-LET (C FLAGS)
                                         (IF1 FZ
                                              (MV 0
                                                  (IF1 (LOG<> FMT 0)
                                                       (SETBITN FLAGS 8 (IDC) 1)
                                                       FLAGS))
                                              (MV 5 FLAGS))
                                         (MV FLAGS C)))
                            (MV FLAGS 4)))
                  (MV SIGN EXP MAN C FLAGS))))))

(DEFUN CLZ53-LOOP-0 (I N K C Z)
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

(DEFUN CLZ53-LOOP-1 (K N C Z)
       (DECLARE (XARGS :MEASURE (NFIX (- 6 K))))
       (IF (AND (INTEGERP K) (< K 6))
           (LET ((N (FLOOR N 2)))
                (MV-LET (C Z)
                        (CLZ53-LOOP-0 0 N K C Z)
                        (CLZ53-LOOP-1 (+ K 1) N C Z)))
           (MV N C Z)))

(DEFUN CLZ53-LOOP-2 (I X Z C)
       (DECLARE (XARGS :MEASURE (NFIX (- 64 I))))
       (IF (AND (INTEGERP I) (< I 64))
           (LET ((Z (AS I (LOGNOT1 (BITN X I)) Z))
                 (C (AS I (BITS 0 5 0) C)))
                (CLZ53-LOOP-2 (+ I 1) X Z C))
           (MV Z C)))

(DEFUN CLZ53 (M)
       (LET* ((X (BITS 0 63 0))
              (X (SETBITS X 64 63 11 M))
              (Z NIL)
              (C NIL))
             (MV-LET (Z C)
                     (CLZ53-LOOP-2 0 X Z C)
                     (LET ((N 64))
                          (MV-LET (N C Z)
                                  (CLZ53-LOOP-1 0 N C Z)
                                  (AG 0 C))))))

(DEFUN
 SPECIALCASE
 (OPA OPB CLASSA CLASSB DN FUSED FLAGS)
 (LET*
  ((D (BITS 0 116 0))
   (ZERO (BITS 0 63 0))
   (ZERO (SETBITN ZERO 64 63
                  (LOGXOR (BITN OPA 63) (BITN OPB 63))))
   (INFINITY (BITS (LOGIOR 9218868437227405312 ZERO)
                   63 0))
   (MANMSB (BITS 2251799813685248 63 0))
   (DEFNAN (BITS 9221120237041090560 63 0))
   (PRODINFZERO (FALSE$)))
  (MV-LET
   (PRODINFZERO D FLAGS)
   (IF1
     (LOG= CLASSA 2)
     (MV PRODINFZERO
         (BITS (IF1 DN DEFNAN
                    (IF1 FUSED OPA (LOGIOR OPA MANMSB)))
               116 0)
         (SETBITN FLAGS 8 (IOC) 1))
     (IF1 (LOG= CLASSB 2)
          (MV PRODINFZERO
              (BITS (IF1 DN DEFNAN
                         (IF1 FUSED OPB (LOGIOR OPB MANMSB)))
                    116 0)
              (SETBITN FLAGS 8 (IOC) 1))
          (MV-LET (PRODINFZERO FLAGS D)
                  (IF1 (LOG= CLASSA 3)
                       (MV PRODINFZERO
                           FLAGS (BITS (IF1 DN DEFNAN OPA) 116 0))
                       (IF1 (LOG= CLASSB 3)
                            (MV PRODINFZERO
                                FLAGS (BITS (IF1 DN DEFNAN OPB) 116 0))
                            (MV-LET (D PRODINFZERO FLAGS)
                                    (IF1 (LOGIOR1 (LOGAND1 (LOG= CLASSA 1)
                                                           (LOG= CLASSB 0))
                                                  (LOGAND1 (LOG= CLASSB 1)
                                                           (LOG= CLASSA 0)))
                                         (MV DEFNAN (TRUE$)
                                             (SETBITN FLAGS 8 (IOC) 1))
                                         (MV (IF1 (LOGIOR1 (LOG= CLASSA 1)
                                                           (LOG= CLASSB 1))
                                                  INFINITY
                                                  (IF1 (LOGIOR1 (LOG= CLASSA 0)
                                                                (LOG= CLASSB 0))
                                                       ZERO D))
                                             PRODINFZERO FLAGS))
                                    (MV PRODINFZERO FLAGS D))))
                  (MV PRODINFZERO D FLAGS))))
   (MV (IF1 FUSED (BITS (ASH D 53) 116 0) D)
       FLAGS PRODINFZERO (TRUE$)
       (FALSE$)))))

(DEFUN COMPRESS3TO2 (X Y Z)
       (MV (LOGXOR (LOGXOR X Y) Z)
           (LOGIOR (LOGIOR (LOGAND X Y) (LOGAND X Z))
                   (LOGAND Y Z))))

(DEFUN
 COMPRESS (PP IA IB)
 (LET
  ((T0FA0A (AG 0 PP))
   (T0FA0B (AG 1 PP))
   (T0FA0C (BITS (ASH (AG 2 PP) 2) 58 0))
   (T2PP0S 0)
   (T1PP0C 0))
  (MV-LET
   (T2PP0S T1PP0C)
   (COMPRESS3TO2 T0FA0A T0FA0B T0FA0C)
   (LET
    ((T0FA1A (AG 3 PP))
     (T0FA1B (BITS (ASH (AG 4 PP) 2) 60 0))
     (T0FA1C (BITS (ASH (AG 5 PP) 4) 60 0))
     (T2PP1S 0)
     (T1PP1C 0))
    (MV-LET
     (T2PP1S T1PP1C)
     (COMPRESS3TO2 T0FA1A T0FA1B T0FA1C)
     (LET
      ((T0FA2A (AG 6 PP))
       (T0FA2B (BITS (ASH (AG 7 PP) 2) 60 0))
       (T0FA2C (BITS (ASH (AG 8 PP) 4) 60 0))
       (T2PP2S 0)
       (T1PP2C 0))
      (MV-LET
       (T2PP2S T1PP2C)
       (COMPRESS3TO2 T0FA2A T0FA2B T0FA2C)
       (LET
        ((T0FA3A (AG 9 PP))
         (T0FA3B (BITS (ASH (AG 10 PP) 2) 60 0))
         (T0FA3C (BITS (ASH (AG 11 PP) 4) 60 0))
         (T2PP3S 0)
         (T1PP3C 0))
        (MV-LET
         (T2PP3S T1PP3C)
         (COMPRESS3TO2 T0FA3A T0FA3B T0FA3C)
         (LET
          ((T0FA4A (AG 12 PP))
           (T0FA4B (BITS (ASH (AG 13 PP) 2) 60 0))
           (T0FA4C (BITS (ASH (AG 14 PP) 4) 60 0))
           (T2PP4S 0)
           (T1PP4C 0))
          (MV-LET
           (T2PP4S T1PP4C)
           (COMPRESS3TO2 T0FA4A T0FA4B T0FA4C)
           (LET
            ((T0FA5A (AG 15 PP))
             (T0FA5B (BITS (ASH (AG 16 PP) 2) 60 0))
             (T0FA5C (BITS (ASH (AG 17 PP) 4) 60 0))
             (T2PP5S 0)
             (T1PP5C 0))
            (MV-LET
             (T2PP5S T1PP5C)
             (COMPRESS3TO2 T0FA5A T0FA5B T0FA5C)
             (LET
              ((T0FA6A (AG 18 PP))
               (T0FA6B (BITS (ASH (AG 19 PP) 2) 60 0))
               (T0FA6C (BITS (ASH (AG 20 PP) 4) 60 0))
               (T2PP6S 0)
               (T1PP6C 0))
              (MV-LET
               (T2PP6S T1PP6C)
               (COMPRESS3TO2 T0FA6A T0FA6B T0FA6C)
               (LET
                ((T0FA7A (AG 21 PP))
                 (T0FA7B (BITS (ASH (AG 22 PP) 2) 60 0))
                 (T0FA7C (BITS (ASH (AG 23 PP) 4) 60 0))
                 (T2PP7S 0)
                 (T1PP7C 0))
                (MV-LET
                 (T2PP7S T1PP7C)
                 (COMPRESS3TO2 T0FA7A T0FA7B T0FA7C)
                 (LET
                  ((T0FA8A (AG 24 PP))
                   (T0FA8B (BITS (ASH (AG 25 PP) 2) 60 0))
                   (T0FA8C (BITS (ASH (AG 26 PP) 4) 60 0))
                   (T2PP8S 0)
                   (T1PP8C 0))
                  (MV-LET
                   (T2PP8S T1PP8C)
                   (COMPRESS3TO2 T0FA8A T0FA8B T0FA8C)
                   (LET
                    ((T1FA0A T1PP0C)
                     (T1FA0B (BITS (ASH T1PP1C 4) 70 0))
                     (T1FA0C (BITS (ASH T1PP2C 10) 70 0))
                     (T3PP0S 0)
                     (T2PP0C 0))
                    (MV-LET
                     (T3PP0S T2PP0C)
                     (COMPRESS3TO2 T1FA0A T1FA0B T1FA0C)
                     (LET
                      ((T1FA1A T1PP3C)
                       (T1FA1B (BITS (ASH T1PP4C 6) 72 0))
                       (T1FA1C (BITS (ASH T1PP5C 12) 72 0))
                       (T3PP1S 0)
                       (T2PP1C 0))
                      (MV-LET
                       (T3PP1S T2PP1C)
                       (COMPRESS3TO2 T1FA1A T1FA1B T1FA1C)
                       (LET
                        ((T1FA2A T1PP6C)
                         (T1FA2B (BITS (ASH T1PP7C 6) 72 0))
                         (T1FA2C (BITS (ASH T1PP8C 12) 72 0))
                         (T3PP2S 0)
                         (T2PP2C 0))
                        (MV-LET
                         (T3PP2S T2PP2C)
                         (COMPRESS3TO2 T1FA2A T1FA2B T1FA2C)
                         (LET
                          ((T2FA0A T2PP0S)
                           (T2FA0B (BITS (ASH T2PP1S 4) 70 0))
                           (T2FA0C (BITS (ASH T2PP2S 10) 70 0))
                           (T4PP0S 0)
                           (T3PP0C 0))
                          (MV-LET
                           (T4PP0S T3PP0C)
                           (COMPRESS3TO2 T2FA0A T2FA0B T2FA0C)
                           (LET
                            ((T2FA1A T2PP3S)
                             (T2FA1B (BITS (ASH T2PP4S 6) 72 0))
                             (T2FA1C (BITS (ASH T2PP5S 12) 72 0))
                             (T4PP1S 0)
                             (T3PP1C 0))
                            (MV-LET
                             (T4PP1S T3PP1C)
                             (COMPRESS3TO2 T2FA1A T2FA1B T2FA1C)
                             (LET
                              ((T2FA2A T2PP6S)
                               (T2FA2B (BITS (ASH T2PP7S 6) 72 0))
                               (T2FA2C (BITS (ASH T2PP8S 12) 72 0))
                               (T4PP2S 0)
                               (T3PP2C 0))
                              (MV-LET
                               (T4PP2S T3PP2C)
                               (COMPRESS3TO2 T2FA2A T2FA2B T2FA2C)
                               (LET
                                ((T2FA3A T2PP0C)
                                 (T2FA3B (BITS (ASH T2PP1C 16) 106 0))
                                 (T2FA3C (BITS (ASH T2PP2C 34) 106 0))
                                 (T4PP3S 0)
                                 (T3PP3C 0))
                                (MV-LET
                                 (T4PP3S T3PP3C)
                                 (COMPRESS3TO2 T2FA3A T2FA3B T2FA3C)
                                 (LET
                                  ((T3FA0A T3PP0S)
                                   (T3FA0B (BITS (ASH T3PP1S 16) 106 0))
                                   (T3FA0C (BITS (ASH T3PP2S 34) 106 0))
                                   (T5PP0S 0)
                                   (T4PP0C 0))
                                  (MV-LET
                                   (T5PP0S T4PP0C)
                                   (COMPRESS3TO2 T3FA0A T3FA0B T3FA0C)
                                   (LET
                                    ((T3FA1A T3PP0C)
                                     (T3FA1B (BITS (ASH T3PP1C 16) 106 0))
                                     (T3FA1C (BITS (ASH T3PP2C 34) 106 0))
                                     (T5PP1S 0)
                                     (T4PP1C 0))
                                    (MV-LET
                                     (T5PP1S T4PP1C)
                                     (COMPRESS3TO2 T3FA1A T3FA1B T3FA1C)
                                     (LET
                                      ((T3FA2A (BITS (ASH IA 49) 106 0))
                                       (T3FA2B (BITS (ASH IB 49) 106 0))
                                       (T3FA2C T3PP3C)
                                       (T4PP4S 0)
                                       (T4PP2C 0))
                                      (MV-LET
                                       (T4PP4S T4PP2C)
                                       (COMPRESS3TO2 T3FA2A T3FA2B T3FA2C)
                                       (LET
                                        ((T4FA0A (BITS (ASH T4PP2C 2) 108 0))
                                         (T4FA0B T4PP1C)
                                         (T4FA0C T4PP0C)
                                         (T6PP0S 0)
                                         (T5PP0C 0))
                                        (MV-LET
                                         (T6PP0S T5PP0C)
                                         (COMPRESS3TO2 T4FA0A T4FA0B T4FA0C)
                                         (LET
                                          ((T4FA1A (BITS (ASH T4PP4S 3) 109 0))
                                           (T4FA1B T4PP0S)
                                           (T4FA1C (BITS (ASH T4PP1S 16) 109 0))
                                           (T6PP1S 0)
                                           (T5PP1C 0))
                                          (MV-LET
                                           (T6PP1S T5PP1C)
                                           (COMPRESS3TO2 T4FA1A T4FA1B T4FA1C)
                                           (LET
                                            ((T5FA0A T5PP0S)
                                             (T5FA0B T5PP1S)
                                             (T5FA0C
                                                  (BITS (ASH T5PP0C 2) 110 0))
                                             (T7PP0S 0)
                                             (T6PP0C 0))
                                            (MV-LET
                                             (T7PP0S T6PP0C)
                                             (COMPRESS3TO2 T5FA0A T5FA0B T5FA0C)
                                             (LET
                                              ((T5FA1A
                                                   (BITS (ASH T4PP2S 33) 109 0))
                                               (T5FA1B
                                                    (BITS (ASH T4PP3S 1) 109 0))
                                               (T5FA1C T5PP1C)
                                               (T6PP2S 0)
                                               (T6PP1C 0))
                                              (MV-LET
                                               (T6PP2S T6PP1C)
                                               (COMPRESS3TO2
                                                    T5FA1A T5FA1B T5FA1C)
                                               (LET
                                                ((T6FA0A
                                                    (BITS (ASH T6PP0S 2) 110 0))
                                                 (T6FA0B T6PP1S)
                                                 (T6FA0C
                                                    (BITS (ASH T6PP2S 1) 110 0))
                                                 (T8PP0S 0)
                                                 (T7PP0C 0))
                                                (MV-LET
                                                 (T8PP0S T7PP0C)
                                                 (COMPRESS3TO2
                                                      T6FA0A T6FA0B T6FA0C)
                                                 (LET
                                                  ((T7FA0A T7PP0S)
                                                   (T7FA0B T7PP0C)
                                                   (T7FA0C
                                                    (BITS (ASH T6PP0C 1) 111 0))
                                                   (T9PP0S 0)
                                                   (T7PP1C 0))
                                                  (MV-LET
                                                   (T9PP0S T7PP1C)
                                                   (COMPRESS3TO2
                                                        T7FA0A T7FA0B T7FA0C)
                                                   (LET
                                                    ((T8FA1A
                                                          (BITS (ASH T7PP1C 2)
                                                                113 0))
                                                     (T8FA1B
                                                          (BITS (ASH T6PP1C 2)
                                                                113 0))
                                                     (T8FA1C T8PP0S)
                                                     (T9PP1S 0)
                                                     (T9PP0C 0))
                                                    (MV-LET
                                                     (T9PP1S T9PP0C)
                                                     (COMPRESS3TO2
                                                          T8FA1A T8FA1B T8FA1C)
                                                     (LET
                                                      ((T9FA1A
                                                            (BITS (ASH T9PP0S 1)
                                                                  114 0))
                                                       (T9FA1B T9PP1S)
                                                       (T9FA1C
                                                            (BITS (ASH T9PP0C 1)
                                                                  114 0))
                                                       (T11PP0S 0)
                                                       (T10PP0C 0))
                                                      (MV-LET
                                                       (T11PP0S T10PP0C)
                                                       (COMPRESS3TO2
                                                           T9FA1A T9FA1B T9FA1C)
                                                       (MV
                                                        (BITS T11PP0S 105 0)
                                                        (BITS
                                                         (BITS (ASH T10PP0C 1)
                                                               115 0)
                                                         105
                                                         0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(DEFUN
     COMPUTEPRODUCT-LOOP-0
     (I MULTIPLIER MANA PP)
     (DECLARE (XARGS :MEASURE (NFIX (- 27 I))))
     (IF (AND (INTEGERP I) (< I 27))
         (LET* ((SLICE (BITS MULTIPLIER (+ (* 2 I) 2) (* 2 I)))
                (SIGN (BITN SLICE 2))
                (SIGNLAST (BITN SLICE 0))
                (ENC (- (+ (BITN SLICE 0) (BITN SLICE 1))
                        (* 2 (BITN SLICE 2))))
                (MUX 0)
                (MUX (CASE ENC (0 (BITS 0 52 0))
                           ((1 -1) MANA)
                           ((2 -2) (BITS (ASH MANA 1) 52 0))
                           (T MUX)))
                (MUX (IF1 SIGN (BITS (LOGNOT MUX) 52 0) MUX))
                (PP (IF1 (LOG= I 0)
                         (LET* ((PP (AS I (SETBITS (AG I PP) 57 52 0 MUX)
                                        PP))
                                (PP (AS I (SETBITN (AG I PP) 57 53 SIGN)
                                        PP))
                                (PP (AS I (SETBITN (AG I PP) 57 54 SIGN)
                                        PP))
                                (PP (AS I
                                        (SETBITN (AG I PP) 57 55 (LOGNOT1 SIGN))
                                        PP)))
                               (AS I (SETBITN (AG I PP) 57 56 0) PP))
                         (LET* ((PP (AS I (SETBITN (AG I PP) 57 0 SIGNLAST)
                                        PP))
                                (PP (AS I (SETBITN (AG I PP) 57 1 0) PP))
                                (PP (AS I (SETBITS (AG I PP) 57 54 2 MUX)
                                        PP))
                                (PP (AS I
                                        (SETBITN (AG I PP) 57 55 (LOGNOT1 SIGN))
                                        PP)))
                               (AS I (SETBITN (AG I PP) 57 56 (LOG< I 26))
                                   PP)))))
               (COMPUTEPRODUCT-LOOP-0 (+ I 1)
                                      MULTIPLIER MANA PP))
         PP))

(DEFUN COMPUTEPRODUCT
       (MANA MANB EXPAZERO EXPBZERO)
       (LET* ((PP NIL)
              (MULTIPLIER MANB)
              (MULTIPLIER (BITS (ASH MULTIPLIER 1) 54 0))
              (PP (COMPUTEPRODUCT-LOOP-0 0 MULTIPLIER MANA PP))
              (IA (BITS (IF1 EXPAZERO 0 MANB) 51 0))
              (IB (BITS (IF1 EXPBZERO 0 MANA) 52 0))
              (IB (SETBITN IB 53 52
                           (LOGAND1 (LOGNOT1 EXPAZERO)
                                    (LOGNOT1 EXPBZERO))))
              (PPA 0)
              (PPB 0))
             (MV-LET (PPA PPB)
                     (COMPRESS PP IA IB)
                     (BITS (+ PPA PPB) 105 0))))

(DEFUN EXPINT (EXPBIASED)
       (LET* ((EXPINT 0)
              (EXPINT (SETBITN EXPINT
                               12 11 (LOGNOT1 (BITN EXPBIASED 10))))
              (EXPINT (SETBITN EXPINT
                               12 10 (LOGNOT1 (BITN EXPBIASED 10))))
              (EXPINT (SETBITS EXPINT 12 9 1 (BITS EXPBIASED 9 1))))
             (SETBITN EXPINT 12 0
                      (LOGIOR1 (BITN EXPBIASED 0)
                               (LOG= EXPBIASED 0)))))

(DEFUN RIGHTSHFT-LOOP-0 (I SHIFT STKMASKFMA)
       (DECLARE (XARGS :MEASURE (NFIX (- SHIFT I))))
       (IF (AND (INTEGERP I)
                (INTEGERP SHIFT)
                (< I SHIFT))
           (LET ((STKMASKFMA (SETBITN STKMASKFMA 63 I 1)))
                (RIGHTSHFT-LOOP-0 (+ I 1)
                                  SHIFT STKMASKFMA))
           STKMASKFMA))

(DEFUN RIGHTSHFT (EXPA EXPB PROD)
       (LET* ((EXPDEFICIT (BITS (+ (+ (+ (LOGNOT EXPA) (LOGNOT EXPB)) 1)
                                   (LOGAND1 (LOG<> EXPA 0) (LOG<> EXPB 0)))
                                9 0))
              (SHIFT (BITS EXPDEFICIT 5 0))
              (SHIFT (IF1 (LOG<> (BITS EXPDEFICIT 9 6) 0)
                          (SETBITS SHIFT 6 5 1 31)
                          SHIFT))
              (PROD0 (BITS 0 106 0))
              (PROD0 (SETBITS PROD0 107 106 1 PROD))
              (PRODSHFT (BITS (ASH PROD0 (- SHIFT)) 105 0))
              (FRAC105 (BITS PRODSHFT 104 0))
              (EXPSHFTINT (BITS 3072 11 0))
              (EXPINC (LOGAND1 (BITN PROD 105)
                               (LOG= SHIFT 1)))
              (STKMASKFMA (BITS 0 62 0))
              (STKMASKFMA (RIGHTSHFT-LOOP-0 0 SHIFT STKMASKFMA))
              (STKFMA (LOG<> (LOGAND PROD (ASH STKMASKFMA (- 1)))
                             0))
              (STKMASK (BITS 4503599627370495 106 0))
              (STKMASK (SETBITS STKMASK
                                107 106 52 (BITS STKMASKFMA 54 0)))
              (STK (LOG<> (LOGAND PROD (BITS STKMASK 106 1))
                          0))
              (GRDMASK (BITS (LOGAND (LOGNOT (BITS STKMASK 106 52))
                                     (BITS STKMASK 105 51))
                             54 0)))
             (MV EXPSHFTINT EXPINC FRAC105 STKFMA
                 (LOG<> (LOGAND (BITS GRDMASK 53 0)
                                (BITS PROD 105 52))
                        0)
                 (LOG<> (LOGAND GRDMASK (BITS PROD 105 51))
                        0)
                 STK)))

(DEFUN LEFTSHFT (EXPA EXPB PROD CLZ)
       (LET* ((EXPAINT (EXPINT EXPA))
              (EXPBINT (EXPINT EXPB))
              (EXPDIFFINT (BITS (+ (- (+ EXPAINT EXPBINT) CLZ) 1)
                                11 0))
              (EXPPRODM1INT (BITS (+ EXPAINT EXPBINT) 11 0))
              (EXPDIFFBIASEDZERO (LOG= EXPDIFFINT 3072))
              (EXPDIFFBIASEDNEG (LOG= (BITS EXPDIFFINT 11 10) 2))
              (EXPDIFFBIASEDPOS (LOGAND1 (LOGNOT1 EXPDIFFBIASEDZERO)
                                         (LOGNOT1 EXPDIFFBIASEDNEG)))
              (SHIFT (BITS (IF1 EXPDIFFBIASEDZERO (- CLZ 1)
                                (IF1 EXPDIFFBIASEDPOS CLZ EXPPRODM1INT))
                           5 0))
              (PRODSHFT (BITS (ASH PROD SHIFT) 105 0))
              (EXPSHFTINT (BITS (IF1 EXPDIFFBIASEDPOS EXPDIFFINT 3072)
                                11 0))
              (OVFMASK (BITS (ASH 9223372036854775808 (- SHIFT))
                             63 0))
              (MULOVF (LOG<> (LOGAND OVFMASK (BITS PROD 105 42))
                             0))
              (SUB2NORM (LOG<> (LOGAND (ASH OVFMASK (- 1))
                                       (BITS PROD 104 42))
                               0))
              (FRAC105 (BITS PRODSHFT 104 0))
              (FRAC105 (IF1 (LOGNOT1 MULOVF)
                            (BITS (ASH FRAC105 1) 104 0)
                            FRAC105))
              (EXPINC (LOGIOR1 MULOVF
                               (LOGAND1 EXPDIFFBIASEDZERO SUB2NORM)))
              (STKMASK (BITS (ASH 4503599627370495 (- SHIFT))
                             51 0))
              (STK (IF1 MULOVF (LOG<> (LOGAND STKMASK PROD) 0)
                        (LOG<> (LOGAND (ASH STKMASK (- 1)) PROD)
                               0)))
              (GRDMASK (BITS OVFMASK 63 11))
              (GRD (IF1 MULOVF (LOG<> (LOGAND GRDMASK PROD) 0)
                        (LOG<> (LOGAND (ASH GRDMASK (- 1)) PROD)
                               0)))
              (LSBMASK (BITS OVFMASK 63 10)))
             (MV EXPSHFTINT EXPINC FRAC105 0
                 (IF1 MULOVF (LOG<> (LOGAND LSBMASK PROD) 0)
                      (LOG<> (LOGAND (ASH LSBMASK (- 1)) PROD)
                             0))
                 GRD STK)))

(DEFUN
 FMUL64 (OPA OPB FZ DN RMODE FUSED)
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
   (ANALYZE OPA 2 FZ FLAGS)
   (MV-LET
    (SIGNB EXPB MANB CLASSB FLAGS)
    (ANALYZE OPB 2 FZ FLAGS)
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
     (SPECIALCASE OPA OPB CLASSA CLASSB DN FUSED FLAGS)
     (LET*
      ((CLZ (BITS 0 5 0))
       (CLZ (IF1 (LOG= EXPA 0)
                 (LOGIOR CLZ (CLZ53 MANA))
                 CLZ))
       (CLZ (IF1 (LOG= EXPB 0)
                 (LOGIOR CLZ (CLZ53 MANB))
                 CLZ))
       (PROD (COMPUTEPRODUCT MANA MANB (LOG= EXPA 0)
                             (LOG= EXPB 0)))
       (EXPPRODINT (BITS (+ (+ (EXPINT EXPA) (EXPINT EXPB)) 1)
                         11 0))
       (EXPBIASEDZERO (LOG= EXPPRODINT 3072))
       (EXPBIASEDNEG (LOG= (BITS EXPPRODINT 11 10) 2))
       (EXPSHFTINT 0)
       (EXPINC 0)
       (FRAC105 0)
       (STKFMA 0)
       (LSB 0)
       (GRD 0)
       (STK 0))
      (MV-LET
       (EXPSHFTINT EXPINC FRAC105 STKFMA LSB GRD STK)
       (IF1 (LOGIOR1 EXPBIASEDZERO EXPBIASEDNEG)
            (RIGHTSHFT EXPA EXPB PROD)
            (LEFTSHFT EXPA EXPB PROD CLZ))
       (LET*
        ((EXPZERO (LOG= (BITS EXPSHFTINT 11 0) 3072))
         (EXPMAX (LOG= (BITS EXPSHFTINT 11 0) 1022))
         (EXPINF (LOG= (BITS EXPSHFTINT 11 0) 1023))
         (EXPGTINF (LOG= (BITS EXPSHFTINT 11 10) 1))
         (EXP11 (BITS EXPSHFTINT 10 0))
         (EXP11 (SETBITN EXP11 11 10 (LOGNOT1 (BITN EXP11 10))))
         (SIGN (LOGXOR SIGNA SIGNB)))
        (IF1
         FUSED
         (LET* ((D 0) (D (SETBITN D 117 116 SIGN)))
               (MV (SETBITS (IF1 (LOGAND1 EXPINC (LOGNOT1 EXPINF))
                                 (SETBITS D 117 115 105 (+ EXP11 1))
                                 (SETBITS D 117 115 105 EXP11))
                            117 104 0 FRAC105)
                   (SETBITN FLAGS 8 (IXC) STKFMA)
                   (FALSE$)
                   (FALSE$)
                   (LOGIOR1 EXPGTINF (LOGAND1 EXPINF EXPINC))))
         (LET*
          ((D (BITS 0 63 0))
           (D (SETBITN D 64 63 SIGN))
           (RNDUP
               (LOGIOR1 (LOGIOR1 (LOGAND1 (LOGAND1 (LOG= RMODE (RMODENEAR)) GRD)
                                          (LOGIOR1 LSB STK))
                                 (LOGAND1 (LOGAND1 (LOG= RMODE (RMODEUP))
                                                   (LOGNOT1 SIGN))
                                          (LOGIOR1 GRD STK)))
                        (LOGAND1 (LOGAND1 (LOG= RMODE (RMODEDN)) SIGN)
                                 (LOGIOR1 GRD STK))))
           (FRACUNRND (BITS FRAC105 104 53))
           (FRACP1 (BITS (+ FRACUNRND 1) 52 0))
           (FRACRND (BITS (IF1 RNDUP (BITS FRACP1 51 0) FRACUNRND)
                          51 0))
           (EXPRNDINC (LOGAND1 RNDUP (BITN FRACP1 52)))
           (EXPRND (BITS (IF1 (LOGIOR1 EXPINC EXPRNDINC)
                              (+ EXP11 1)
                              EXP11)
                         10 0))
           (UNDERFLOW (LOGAND1 EXPZERO (LOGNOT1 EXPINC)))
           (OVERFLOW (LOGIOR1 (LOGIOR1 EXPGTINF EXPINF)
                              (LOGAND1 EXPMAX (LOGIOR1 EXPINC EXPRNDINC)))))
          (MV-LET
           (FLAGS D)
           (IF1
             OVERFLOW
             (MV (SETBITN (SETBITN FLAGS 8 (IXC) 1)
                          8 (OFC)
                          1)
                 (IF1 (LOGIOR1 (LOGIOR1 (LOGAND1 (LOG= RMODE (RMODEUP)) SIGN)
                                        (LOGAND1 (LOG= RMODE (RMODEDN))
                                                 (LOGNOT1 SIGN)))
                               (LOG= RMODE (RMODEZERO)))
                      (SETBITS D 64 62 0 9218868437227405311)
                      (SETBITS D 64 62 0 9218868437227405312)))
             (MV-LET (D FLAGS)
                     (IF1 UNDERFLOW
                          (IF1 FZ (MV D (SETBITN FLAGS 8 (UFC) 1))
                               (MV (SETBITS (SETBITS D 64 51 0 FRACRND)
                                            64 62 52 EXPRND)
                                   (IF1 (LOGIOR1 GRD STK)
                                        (LET ((FLAGS (SETBITN FLAGS 8 (UFC) 1)))
                                             (SETBITN FLAGS 8 (IXC) 1))
                                        FLAGS)))
                          (MV (SETBITS (SETBITS D 64 51 0 FRACRND)
                                       64 62 52 EXPRND)
                              (IF1 (LOGIOR1 GRD STK)
                                   (SETBITN FLAGS 8 (IXC) 1)
                                   FLAGS)))
                     (MV FLAGS D)))
           (MV D FLAGS (FALSE$)
               (FALSE$)
               (FALSE$)))))))))))))

