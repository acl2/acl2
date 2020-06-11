(NUMERATOR-OF-X-MINUS-1 (11 5 (:REWRITE NUMERATOR-WHEN-INTEGERP))
                        (8 8 (:REWRITE DEFAULT-+-2))
                        (8 8 (:REWRITE DEFAULT-+-1))
                        (7 5 (:REWRITE DEFAULT-*-2))
                        (6 4 (:REWRITE DEFAULT-NUMERATOR))
                        (5 5 (:REWRITE DEFAULT-*-1))
                        (4 2 (:REWRITE /R-WHEN-ABS-NUMERATOR=1))
                        (2 2 (:REWRITE INTEGERP==>DENOMINATOR=1))
                        (2 2 (:REWRITE EQUAL-CONSTANT-+))
                        (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
                        (2 2 (:REWRITE DEFAULT-DENOMINATOR))
                        (1 1 (:REWRITE EQUAL-DENOMINATOR-1))
                        (1 1 (:REWRITE DEFAULT-UNARY-/)))
(NUMERATOR-OF-X-PLUS-1 (8 8 (:REWRITE DEFAULT-+-2))
                       (8 8 (:REWRITE DEFAULT-+-1))
                       (5 5 (:REWRITE NUMERATOR-WHEN-INTEGERP))
                       (5 5 (:REWRITE DEFAULT-*-2))
                       (5 5 (:REWRITE DEFAULT-*-1))
                       (4 4 (:REWRITE DEFAULT-NUMERATOR))
                       (4 2 (:REWRITE /R-WHEN-ABS-NUMERATOR=1))
                       (2 2 (:REWRITE INTEGERP==>DENOMINATOR=1))
                       (2 2 (:REWRITE EQUAL-CONSTANT-+))
                       (2 2 (:REWRITE DEFAULT-DENOMINATOR))
                       (1 1 (:REWRITE EQUAL-DENOMINATOR-1))
                       (1 1 (:REWRITE DEFAULT-UNARY-/)))
(NUMERATOR-<-DENOMINATOR (132 12 (:LINEAR X*Y>1-POSITIVE))
                         (120 12 (:REWRITE <-UNARY-/-POSITIVE-RIGHT))
                         (100 50 (:REWRITE /R-WHEN-ABS-NUMERATOR=1))
                         (53 53 (:REWRITE DEFAULT-*-2))
                         (53 53 (:REWRITE DEFAULT-*-1))
                         (43 43 (:REWRITE DEFAULT-<-2))
                         (43 43 (:REWRITE DEFAULT-<-1))
                         (39 39 (:REWRITE DEFAULT-NUMERATOR))
                         (37 37 (:REWRITE INTEGERP==>DENOMINATOR=1))
                         (37 37 (:REWRITE DEFAULT-DENOMINATOR))
                         (31 19 (:REWRITE EQUAL-DENOMINATOR-1))
                         (25 25 (:REWRITE DEFAULT-UNARY-/))
                         (14 6
                             (:LINEAR NUMERATOR-GOES-DOWN-BY-INTEGER-DIVISION
                                      . 2)))
(NUMERATOR-<-0 (3 3 (:REWRITE DEFAULT-<-2))
               (3 3 (:REWRITE DEFAULT-<-1))
               (1 1 (:REWRITE NUMERATOR-WHEN-INTEGERP))
               (1 1 (:REWRITE DEFAULT-NUMERATOR)))
(INTEGERP-OF-DIVIDE-WHEN-LESS (16 8 (:REWRITE /R-WHEN-ABS-NUMERATOR=1))
                              (9 9 (:REWRITE DEFAULT-<-2))
                              (9 9 (:REWRITE DEFAULT-<-1))
                              (4 4 (:REWRITE NUMERATOR-WHEN-INTEGERP))
                              (4 4 (:REWRITE DEFAULT-UNARY-/))
                              (4 4 (:REWRITE DEFAULT-NUMERATOR))
                              (4 4 (:REWRITE DEFAULT-*-2))
                              (4 4 (:REWRITE DEFAULT-*-1)))
(FLOOR-OF-NONNEG-OPERANDS-BASE-CASE
     (19 19
         (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
     (6 2 (:REWRITE /R-WHEN-ABS-NUMERATOR=1))
     (5 5 (:REWRITE DEFAULT-<-2))
     (5 5 (:REWRITE DEFAULT-<-1))
     (4 3 (:REWRITE NUMERATOR-WHEN-INTEGERP))
     (3 3 (:REWRITE DEFAULT-NUMERATOR))
     (2 2 (:REWRITE DEFAULT-*-2))
     (2 2 (:REWRITE DEFAULT-*-1))
     (2 1 (:REWRITE INTEGERP==>DENOMINATOR=1))
     (1 1 (:REWRITE DEFAULT-UNARY-/))
     (1 1 (:REWRITE DEFAULT-DENOMINATOR)))
(MOD-OF-NONNEG-OPERANDS-BASE-CASE (2 2 (:REWRITE DEFAULT-<-2))
                                  (2 2 (:REWRITE DEFAULT-<-1))
                                  (2 2 (:REWRITE DEFAULT-+-2))
                                  (2 2 (:REWRITE DEFAULT-+-1)))
(FLOOR-OF-NONNEG-OPERANDS-STEP (41 30 (:REWRITE DEFAULT-+-2))
                               (31 30 (:REWRITE DEFAULT-+-1))
                               (28 22 (:REWRITE /R-WHEN-ABS-NUMERATOR=1))
                               (23 20 (:REWRITE DEFAULT-<-1))
                               (20 20 (:REWRITE DEFAULT-<-2))
                               (20 19 (:REWRITE DEFAULT-*-2))
                               (20 19 (:REWRITE DEFAULT-*-1))
                               (13 12 (:REWRITE DEFAULT-UNARY-MINUS))
                               (11 11 (:REWRITE DEFAULT-UNARY-/))
                               (9 8 (:REWRITE NUMERATOR-WHEN-INTEGERP))
                               (9 8 (:REWRITE INTEGERP==>DENOMINATOR=1))
                               (8 8 (:REWRITE DEFAULT-NUMERATOR))
                               (8 8 (:REWRITE DEFAULT-DENOMINATOR))
                               (7 7
                                  (:REWRITE INTEGERP-OF-DIVIDE-WHEN-LESS))
                               (3 3 (:REWRITE FOLD-CONSTS-IN-+))
                               (3 1 (:LINEAR X*Y>1-POSITIVE))
                               (1 1 (:REWRITE EQUAL-CONSTANT-+)))
(MOD-OF-NONNEG-OPERANDS-STEP
     (27 23
         (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
     (22 9 (:REWRITE DEFAULT-+-2))
     (16 16 (:TYPE-PRESCRIPTION FLOOR))
     (14 2
         (:REWRITE FLOOR-OF-NONNEG-OPERANDS-BASE-CASE))
     (12 7 (:REWRITE DEFAULT-<-1))
     (10 9 (:REWRITE DEFAULT-+-1))
     (10 7 (:REWRITE DEFAULT-*-2))
     (9 7 (:REWRITE DEFAULT-*-1))
     (8 2
        (:REWRITE MOD-OF-NONNEG-OPERANDS-BASE-CASE))
     (7 7 (:REWRITE DEFAULT-<-2))
     (7 5 (:REWRITE DEFAULT-UNARY-MINUS))
     (2 2
        (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
     (2 2 (:REWRITE FOLD-CONSTS-IN-+)))
(FLOOR-REDEF-WHEN-X-NEGATIVE-LEMMA
     (58 58
         (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
     (32 2
         (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
     (13 9 (:REWRITE DEFAULT-+-2))
     (10 9 (:REWRITE DEFAULT-+-1))
     (10 6 (:REWRITE /R-WHEN-ABS-NUMERATOR=1))
     (9 7 (:REWRITE DEFAULT-UNARY-MINUS))
     (8 8 (:REWRITE DEFAULT-<-2))
     (8 8 (:REWRITE DEFAULT-<-1))
     (6 2 (:DEFINITION NFIX))
     (4 4 (:REWRITE NUMERATOR-WHEN-INTEGERP))
     (4 4 (:REWRITE DEFAULT-NUMERATOR))
     (3 3 (:REWRITE DEFAULT-UNARY-/))
     (3 3 (:REWRITE DEFAULT-*-2))
     (3 3 (:REWRITE DEFAULT-*-1))
     (2 2 (:REWRITE INTEGERP==>DENOMINATOR=1))
     (2 2 (:REWRITE DEFAULT-DENOMINATOR))
     (2 2 (:DEFINITION IFIX))
     (1 1
        (:REWRITE INTEGERP-OF-DIVIDE-WHEN-LESS)))
(FLOOR-OF-X-NEGATIVE-STEP (118 60 (:REWRITE /R-WHEN-ABS-NUMERATOR=1))
                          (81 77 (:REWRITE DEFAULT-<-1))
                          (77 77 (:REWRITE DEFAULT-<-2))
                          (56 47 (:REWRITE DEFAULT-+-2))
                          (53 53 (:REWRITE DEFAULT-*-2))
                          (53 53 (:REWRITE DEFAULT-*-1))
                          (47 47 (:REWRITE DEFAULT-+-1))
                          (39 34 (:REWRITE DEFAULT-UNARY-MINUS))
                          (30 30 (:REWRITE DEFAULT-UNARY-/))
                          (29 29 (:REWRITE DEFAULT-NUMERATOR))
                          (16 16
                              (:REWRITE INTEGERP-OF-DIVIDE-WHEN-LESS))
                          (5 5 (:REWRITE EQUAL-CONSTANT-+))
                          (3 3 (:LINEAR X*Y>1-POSITIVE))
                          (3 1 (:REWRITE <-+-NEGATIVE-0-2)))
(MOD-OF-X-NEGATIVE-STEP (20 9 (:REWRITE DEFAULT-+-2))
                        (16 16 (:TYPE-PRESCRIPTION FLOOR))
                        (11 7 (:REWRITE DEFAULT-*-2))
                        (10 10 (:REWRITE DEFAULT-<-2))
                        (10 10 (:REWRITE DEFAULT-<-1))
                        (10 7 (:REWRITE DEFAULT-*-1))
                        (9 9 (:REWRITE DEFAULT-+-1))
                        (6 2
                           (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
                        (6 2
                           (:REWRITE FLOOR-OF-NONNEG-OPERANDS-STEP))
                        (6 2
                           (:REWRITE FLOOR-OF-NONNEG-OPERANDS-BASE-CASE))
                        (5 3 (:REWRITE DEFAULT-UNARY-MINUS))
                        (4 2
                           (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
                        (4 2
                           (:REWRITE MOD-OF-NONNEG-OPERANDS-STEP))
                        (4 2
                           (:REWRITE MOD-OF-NONNEG-OPERANDS-BASE-CASE))
                        (2 2 (:REWRITE FOLD-CONSTS-IN-+)))
(FLOOR-OF-Y-NEGATIVE-INVERT (68 4
                                (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
                            (38 38
                                (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
                            (22 16 (:REWRITE DEFAULT-+-2))
                            (18 16 (:REWRITE DEFAULT-+-1))
                            (12 11 (:REWRITE DEFAULT-<-1))
                            (12 4 (:DEFINITION NFIX))
                            (11 11 (:REWRITE DEFAULT-<-2))
                            (10 8 (:REWRITE DEFAULT-UNARY-MINUS))
                            (8 2 (:REWRITE NUMERATOR-<-DENOMINATOR))
                            (6 4 (:REWRITE /R-WHEN-ABS-NUMERATOR=1))
                            (4 4 (:REWRITE RATIONALP-*))
                            (4 4
                               (:REWRITE INTEGERP-OF-DIVIDE-WHEN-LESS))
                            (4 4 (:REWRITE <-*-/-LEFT))
                            (4 4 (:DEFINITION IFIX))
                            (4 3 (:REWRITE NUMERATOR-WHEN-INTEGERP))
                            (4 3 (:REWRITE DEFAULT-NUMERATOR))
                            (3 2 (:REWRITE INTEGERP==>DENOMINATOR=1))
                            (3 2 (:REWRITE DEFAULT-DENOMINATOR))
                            (3 2 (:REWRITE DEFAULT-*-1))
                            (2 2
                               (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                            (2 2 (:REWRITE DEFAULT-UNARY-/))
                            (2 2 (:REWRITE DEFAULT-*-2))
                            (2 2 (:REWRITE <-*-0)))
(MOD-OF-Y-NEGATIVE-INVERT (15 13 (:REWRITE DEFAULT-<-2))
                          (15 13 (:REWRITE DEFAULT-<-1))
                          (14 4 (:REWRITE <-MINUS-ZERO))
                          (12 7 (:REWRITE DEFAULT-UNARY-MINUS))
                          (10 2 (:REWRITE FLOOR-OF-X-NEGATIVE-STEP))
                          (9 9
                             (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                          (7 2
                             (:REWRITE MOD-OF-NONNEG-OPERANDS-STEP))
                          (6 4 (:REWRITE DEFAULT-*-2))
                          (6 4 (:REWRITE DEFAULT-*-1))
                          (6 3 (:REWRITE DEFAULT-+-2))
                          (6 2
                             (:REWRITE MOD-OF-NONNEG-OPERANDS-BASE-CASE))
                          (6 2
                             (:REWRITE FLOOR-OF-NONNEG-OPERANDS-STEP))
                          (6 2
                             (:REWRITE FLOOR-OF-NONNEG-OPERANDS-BASE-CASE))
                          (4 3 (:REWRITE DEFAULT-+-1))
                          (1 1 (:REWRITE EQUAL-CONSTANT-+)))
(FLOOR-OF-Y-NEGATIVE-STEP (13 2
                              (:REWRITE FLOOR-OF-NONNEG-OPERANDS-BASE-CASE))
                          (12 2
                              (:REWRITE FLOOR-OF-NONNEG-OPERANDS-STEP))
                          (10 10
                              (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
                          (7 5 (:REWRITE DEFAULT-<-1))
                          (7 5 (:REWRITE DEFAULT-+-2))
                          (6 2 (:REWRITE <-+-NEGATIVE-0-2))
                          (5 5 (:REWRITE DEFAULT-UNARY-MINUS))
                          (5 5 (:REWRITE DEFAULT-<-2))
                          (5 5 (:REWRITE DEFAULT-+-1)))
(FLOOR-OF-NEGATIVE-OPERANDS-BASE-CASE
     (4 4 (:REWRITE DEFAULT-<-2))
     (4 4 (:REWRITE DEFAULT-<-1))
     (3 1
        (:REWRITE FLOOR-OF-NONNEG-OPERANDS-STEP))
     (3 1 (:REWRITE <-MINUS-ZERO))
     (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
     (1 1 (:REWRITE FLOOR-OF-X-NEGATIVE-STEP)))
(FLOOR-OF-NEGATIVE-OPERANDS-STEP
     (11 3 (:REWRITE FLOOR-OF-X-NEGATIVE-STEP))
     (10 10
         (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
     (8 6 (:REWRITE DEFAULT-<-1))
     (8 2
        (:REWRITE FLOOR-OF-NONNEG-OPERANDS-BASE-CASE))
     (7 5 (:REWRITE DEFAULT-+-2))
     (6 6 (:REWRITE DEFAULT-<-2))
     (5 5 (:REWRITE DEFAULT-UNARY-MINUS))
     (5 5 (:REWRITE DEFAULT-+-1))
     (3 1 (:REWRITE <-MINUS-ZERO))
     (3 1 (:REWRITE <-+-NEGATIVE-0-1)))
(MOD-OF-Y-NEGATIVE-STEP (37 33
                            (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
                        (35 31
                            (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
                        (33 15 (:REWRITE DEFAULT-+-2))
                        (24 2
                            (:REWRITE FLOOR-OF-NONNEG-OPERANDS-BASE-CASE))
                        (22 2
                            (:REWRITE FLOOR-OF-NONNEG-OPERANDS-STEP))
                        (17 15 (:REWRITE DEFAULT-+-1))
                        (16 10 (:REWRITE DEFAULT-<-1))
                        (15 11 (:REWRITE DEFAULT-UNARY-MINUS))
                        (15 5 (:REWRITE <-+-NEGATIVE-0-2))
                        (13 2
                            (:REWRITE MOD-OF-NONNEG-OPERANDS-BASE-CASE))
                        (12 2
                            (:REWRITE MOD-OF-NONNEG-OPERANDS-STEP))
                        (11 7 (:REWRITE DEFAULT-*-2))
                        (10 10 (:REWRITE DEFAULT-<-2))
                        (10 7 (:REWRITE DEFAULT-*-1))
                        (4 4 (:REWRITE FOLD-CONSTS-IN-+))
                        (3 3
                           (:REWRITE FLOOR-OF-Y-NEGATIVE-INVERT)))
(MOD-OF-NEGATIVE-OPERANDS-BASE-CASE
     (4 4 (:REWRITE DEFAULT-<-2))
     (4 4 (:REWRITE DEFAULT-<-1))
     (3 1
        (:REWRITE MOD-OF-NONNEG-OPERANDS-STEP))
     (3 1 (:REWRITE <-MINUS-ZERO))
     (2 2 (:REWRITE DEFAULT-UNARY-MINUS)))
(MOD-OF-NEGATIVE-OPERANDS-STEP
     (32 32
         (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
     (29 13 (:REWRITE DEFAULT-+-2))
     (16 10 (:REWRITE DEFAULT-<-1))
     (15 13 (:REWRITE DEFAULT-+-1))
     (15 11 (:REWRITE DEFAULT-UNARY-MINUS))
     (14 2
         (:REWRITE FLOOR-OF-NONNEG-OPERANDS-STEP))
     (14 2
         (:REWRITE FLOOR-OF-NONNEG-OPERANDS-BASE-CASE))
     (12 2 (:REWRITE FLOOR-OF-X-NEGATIVE-STEP))
     (10 10 (:REWRITE DEFAULT-<-2))
     (8 2
        (:REWRITE MOD-OF-NONNEG-OPERANDS-BASE-CASE))
     (6 4 (:REWRITE DEFAULT-*-2))
     (6 4 (:REWRITE DEFAULT-*-1))
     (6 2
        (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
     (6 2 (:REWRITE <-+-NEGATIVE-0-1))
     (4 4 (:REWRITE FOLD-CONSTS-IN-+))
     (2 2
        (:REWRITE FLOOR-OF-Y-NEGATIVE-INVERT)))
(FLOOR-WHEN-Y-IS-0)
(MOD-WHEN-Y-IS-0 (5 5
                    (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                 (4 1
                    (:REWRITE MOD-OF-NONNEG-OPERANDS-STEP))
                 (3 2 (:REWRITE DEFAULT-<-1))
                 (3 2 (:REWRITE DEFAULT-+-2))
                 (3 2 (:REWRITE DEFAULT-+-1))
                 (3 1
                    (:REWRITE MOD-OF-NONNEG-OPERANDS-BASE-CASE))
                 (2 2 (:REWRITE DEFAULT-<-2))
                 (1 1 (:REWRITE MOD-OF-Y-NEGATIVE-INVERT)))
(FLOOR-REDEF (59 47 (:REWRITE DEFAULT-<-1))
             (47 47 (:REWRITE DEFAULT-<-2))
             (42 42
                 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
             (38 26 (:REWRITE DEFAULT-+-2))
             (26 26 (:REWRITE DEFAULT-+-1))
             (20 20 (:REWRITE DEFAULT-UNARY-MINUS))
             (18 6 (:REWRITE <-+-NEGATIVE-0-2))
             (6 2 (:REWRITE <-+-NEGATIVE-0-1)))
(MOD-REDEF (286 47
                (:REWRITE FLOOR-OF-NONNEG-OPERANDS-BASE-CASE))
           (273 175 (:REWRITE DEFAULT-+-2))
           (254 37 (:REWRITE COMMUTATIVITY-OF-+))
           (216 148 (:REWRITE DEFAULT-<-1))
           (196 23 (:REWRITE COMMUTATIVITY-2-OF-+))
           (187 175 (:REWRITE DEFAULT-+-1))
           (149 148 (:REWRITE DEFAULT-<-2))
           (88 16
               (:REWRITE FLOOR-OF-NONNEG-OPERANDS-STEP))
           (80 60 (:REWRITE DEFAULT-UNARY-MINUS))
           (73 16 (:REWRITE FLOOR-OF-X-NEGATIVE-STEP))
           (54 30 (:REWRITE DEFAULT-*-2))
           (54 18 (:REWRITE <-+-NEGATIVE-0-2))
           (47 47 (:REWRITE FOLD-CONSTS-IN-+))
           (40 30 (:REWRITE DEFAULT-*-1))
           (32 5
               (:REWRITE MOD-OF-NONNEG-OPERANDS-BASE-CASE))
           (31 5
               (:REWRITE MOD-OF-NONNEG-OPERANDS-STEP))
           (24 8 (:REWRITE <-0-MINUS))
           (21 7 (:REWRITE <-+-NEGATIVE-0-1))
           (10 5 (:REWRITE UNICITY-OF-0))
           (8 4
              (:REWRITE MINUS-CANCELLATION-ON-RIGHT))
           (5 5 (:REWRITE INVERSE-OF-+))
           (3 1 (:REWRITE <-0-+-NEGATIVE-2))
           (1 1 (:REWRITE EQUAL-CONSTANT-+)))
(FLOOR-NEGATIVE (1 1
                   (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|)))
(FLOOR-NEGATIVE-LEMMA (7 7 (:REWRITE DEFAULT-<-2))
                      (7 7 (:REWRITE DEFAULT-<-1))
                      (3 1
                         (:REWRITE FLOOR-OF-NONNEG-OPERANDS-STEP))
                      (3 1
                         (:REWRITE FLOOR-OF-NONNEG-OPERANDS-BASE-CASE))
                      (3 1 (:LINEAR FLOOR-NEGATIVE))
                      (2 2 (:REWRITE FLOOR-OF-Y-NEGATIVE-INVERT))
                      (2 2 (:REWRITE DEFAULT-+-2))
                      (2 2 (:REWRITE DEFAULT-+-1)))
(FLOOR-NONNEGATIVE)
(FLOOR/MOD-NATS-IND (40 40
                        (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
                    (39 28 (:REWRITE DEFAULT-<-1))
                    (30 28 (:REWRITE DEFAULT-<-2))
                    (25 5
                        (:REWRITE FLOOR-OF-NONNEG-OPERANDS-BASE-CASE))
                    (21 6 (:REWRITE FLOOR-OF-X-NEGATIVE-STEP))
                    (6 6 (:REWRITE FLOOR-OF-Y-NEGATIVE-INVERT))
                    (4 3 (:REWRITE DEFAULT-+-2))
                    (3 3 (:REWRITE DEFAULT-+-1))
                    (2 2 (:REWRITE DEFAULT-UNARY-MINUS)))
(FLOOR-MOD-IND (217 217
                    (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
               (179 120 (:REWRITE DEFAULT-<-1))
               (165 29
                    (:REWRITE FLOOR-OF-NONNEG-OPERANDS-BASE-CASE))
               (137 120 (:REWRITE DEFAULT-<-2))
               (38 34 (:REWRITE DEFAULT-+-2))
               (36 35 (:REWRITE DEFAULT-UNARY-MINUS))
               (34 34 (:REWRITE DEFAULT-+-1))
               (32 8 (:DEFINITION O-FIRST-EXPT))
               (24 8 (:REWRITE <-+-NEGATIVE-0-2))
               (22 22 (:REWRITE DEFAULT-CAR))
               (20 5 (:DEFINITION O-FIRST-COEFF))
               (16 6 (:LINEAR FLOOR-NEGATIVE))
               (9 9 (:REWRITE DEFAULT-CDR))
               (8 4 (:DEFINITION O-RST))
               (5 5 (:TYPE-PRESCRIPTION ABS))
               (4 4
                  (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
               (4 2 (:REWRITE NATP-RW))
               (4 1 (:REWRITE NATP-POSP))
               (2 2 (:TYPE-PRESCRIPTION NATP))
               (1 1 (:REWRITE POSP-RW)))
(TRUNCATE-OF-NONNEG-OPERANDS-BASE-CASE
     (6 2 (:REWRITE /R-WHEN-ABS-NUMERATOR=1))
     (5 5 (:REWRITE DEFAULT-<-2))
     (5 5 (:REWRITE DEFAULT-<-1))
     (4 3 (:REWRITE NUMERATOR-WHEN-INTEGERP))
     (3 3 (:REWRITE DEFAULT-NUMERATOR))
     (2 2 (:REWRITE DEFAULT-*-2))
     (2 2 (:REWRITE DEFAULT-*-1))
     (2 1 (:REWRITE INTEGERP==>DENOMINATOR=1))
     (1 1 (:REWRITE DEFAULT-UNARY-/))
     (1 1 (:REWRITE DEFAULT-DENOMINATOR)))
(REM-OF-NONNEG-OPERANDS-BASE-CASE (2 2 (:REWRITE DEFAULT-<-2))
                                  (2 2 (:REWRITE DEFAULT-<-1))
                                  (2 2 (:REWRITE DEFAULT-+-2))
                                  (2 2 (:REWRITE DEFAULT-+-1)))
(TRUNCATE-OF-NONNEG-OPERANDS-STEP
     (38 28 (:REWRITE DEFAULT-+-2))
     (30 30
         (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
     (28 28 (:REWRITE DEFAULT-+-1))
     (28 22 (:REWRITE /R-WHEN-ABS-NUMERATOR=1))
     (23 20 (:REWRITE DEFAULT-<-1))
     (20 20 (:REWRITE DEFAULT-<-2))
     (20 19 (:REWRITE DEFAULT-*-2))
     (20 19 (:REWRITE DEFAULT-*-1))
     (13 12 (:REWRITE DEFAULT-UNARY-MINUS))
     (11 11 (:REWRITE DEFAULT-UNARY-/))
     (9 8 (:REWRITE NUMERATOR-WHEN-INTEGERP))
     (9 8 (:REWRITE INTEGERP==>DENOMINATOR=1))
     (8 8 (:REWRITE DEFAULT-NUMERATOR))
     (8 8 (:REWRITE DEFAULT-DENOMINATOR))
     (7 7
        (:REWRITE INTEGERP-OF-DIVIDE-WHEN-LESS))
     (3 3 (:REWRITE FOLD-CONSTS-IN-+))
     (3 1 (:LINEAR X*Y>1-POSITIVE))
     (1 1 (:REWRITE EQUAL-CONSTANT-+)))
(REM-OF-NONNEG-OPERANDS-STEP
     (27 23
         (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
     (22 9 (:REWRITE DEFAULT-+-2))
     (16 16 (:TYPE-PRESCRIPTION TRUNCATE))
     (14 2
         (:REWRITE TRUNCATE-OF-NONNEG-OPERANDS-BASE-CASE))
     (12 7 (:REWRITE DEFAULT-<-1))
     (10 9 (:REWRITE DEFAULT-+-1))
     (10 7 (:REWRITE DEFAULT-*-2))
     (9 7 (:REWRITE DEFAULT-*-1))
     (8 2
        (:REWRITE REM-OF-NONNEG-OPERANDS-BASE-CASE))
     (7 7 (:REWRITE DEFAULT-<-2))
     (7 5 (:REWRITE DEFAULT-UNARY-MINUS))
     (2 2
        (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
     (2 2 (:REWRITE FOLD-CONSTS-IN-+)))
(TRUNCATE-OF-X-NEGATIVE-INVERT
     (32 2
         (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
     (16 10 (:REWRITE /R-WHEN-ABS-NUMERATOR=1))
     (10 10 (:REWRITE DEFAULT-<-2))
     (10 10 (:REWRITE DEFAULT-<-1))
     (9 7 (:REWRITE DEFAULT-UNARY-MINUS))
     (8 6 (:REWRITE DEFAULT-+-2))
     (7 7
        (:REWRITE INTEGERP-OF-DIVIDE-WHEN-LESS))
     (6 6 (:REWRITE DEFAULT-+-1))
     (6 2 (:REWRITE COMMUTATIVITY-OF-+))
     (6 2 (:DEFINITION NFIX))
     (5 5 (:REWRITE DEFAULT-UNARY-/))
     (5 5 (:REWRITE DEFAULT-NUMERATOR))
     (5 5 (:REWRITE DEFAULT-*-2))
     (5 5 (:REWRITE DEFAULT-*-1))
     (3 2 (:REWRITE INTEGERP==>DENOMINATOR=1))
     (2 2 (:REWRITE DEFAULT-DENOMINATOR))
     (2 2 (:DEFINITION IFIX))
     (1 1 (:LINEAR X*Y>1-POSITIVE)))
(TRUNCATE-OF-Y-NEGATIVE-INVERT
     (68 4
         (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
     (16 12 (:REWRITE DEFAULT-+-2))
     (12 12 (:REWRITE DEFAULT-<-2))
     (12 12 (:REWRITE DEFAULT-<-1))
     (12 12 (:REWRITE DEFAULT-+-1))
     (12 4 (:REWRITE COMMUTATIVITY-OF-+))
     (12 4 (:DEFINITION NFIX))
     (10 8 (:REWRITE DEFAULT-UNARY-MINUS))
     (8 6
        (:REWRITE INTEGERP-OF-DIVIDE-WHEN-LESS))
     (8 2 (:REWRITE NUMERATOR-<-DENOMINATOR))
     (6 4 (:REWRITE /R-WHEN-ABS-NUMERATOR=1))
     (5 2 (:REWRITE INTEGERP==>DENOMINATOR=1))
     (4 4 (:REWRITE DEFAULT-*-2))
     (4 4 (:REWRITE DEFAULT-*-1))
     (4 4 (:REWRITE <-*-/-LEFT))
     (4 4 (:DEFINITION IFIX))
     (4 3 (:REWRITE NUMERATOR-WHEN-INTEGERP))
     (3 3 (:REWRITE DEFAULT-NUMERATOR))
     (2 2 (:REWRITE DEFAULT-UNARY-/))
     (2 2 (:REWRITE DEFAULT-DENOMINATOR))
     (2 2 (:REWRITE <-UNARY-/-POSITIVE-RIGHT)))
(REM-OF-X-NEGATIVE-INVERT
     (8 8 (:REWRITE DEFAULT-<-2))
     (8 8 (:REWRITE DEFAULT-<-1))
     (8 5 (:REWRITE DEFAULT-UNARY-MINUS))
     (6 4 (:REWRITE DEFAULT-*-2))
     (6 4 (:REWRITE DEFAULT-*-1))
     (6 3 (:REWRITE DEFAULT-+-2))
     (6 2
        (:REWRITE TRUNCATE-OF-NONNEG-OPERANDS-STEP))
     (6 2
        (:REWRITE TRUNCATE-OF-NONNEG-OPERANDS-BASE-CASE))
     (4 2
        (:REWRITE REM-OF-NONNEG-OPERANDS-STEP))
     (4 2
        (:REWRITE REM-OF-NONNEG-OPERANDS-BASE-CASE))
     (3 3
        (:REWRITE TRUNCATE-OF-Y-NEGATIVE-INVERT))
     (3 3 (:REWRITE DEFAULT-+-1)))
(REM-OF-Y-NEGATIVE-INVERT
     (13 13 (:REWRITE DEFAULT-<-2))
     (13 13 (:REWRITE DEFAULT-<-1))
     (10 7 (:REWRITE DEFAULT-UNARY-MINUS))
     (9 3 (:REWRITE <-MINUS-ZERO))
     (8 2
        (:REWRITE TRUNCATE-OF-X-NEGATIVE-INVERT))
     (7 2 (:REWRITE REM-OF-X-NEGATIVE-INVERT))
     (6 4 (:REWRITE DEFAULT-*-2))
     (6 4 (:REWRITE DEFAULT-*-1))
     (6 3 (:REWRITE DEFAULT-+-2))
     (6 2
        (:REWRITE TRUNCATE-OF-NONNEG-OPERANDS-STEP))
     (6 2
        (:REWRITE TRUNCATE-OF-NONNEG-OPERANDS-BASE-CASE))
     (6 2
        (:REWRITE REM-OF-NONNEG-OPERANDS-STEP))
     (6 2
        (:REWRITE REM-OF-NONNEG-OPERANDS-BASE-CASE))
     (3 3 (:REWRITE DEFAULT-+-1)))
(TRUNCATE-OF-Y-POSITIVE-BASE-CASE
     (5 5 (:REWRITE DEFAULT-<-2))
     (5 5 (:REWRITE DEFAULT-<-1))
     (3 1
        (:REWRITE TRUNCATE-OF-NONNEG-OPERANDS-STEP))
     (2 2
        (:REWRITE TRUNCATE-OF-Y-NEGATIVE-INVERT))
     (2 2 (:REWRITE DEFAULT-UNARY-MINUS)))
(TRUNCATE-OF-X-NEGATIVE-STEP (14 10 (:REWRITE DEFAULT-<-1))
                             (13 10 (:REWRITE DEFAULT-+-2))
                             (12 10 (:REWRITE DEFAULT-UNARY-MINUS))
                             (10 10 (:REWRITE DEFAULT-<-2))
                             (10 10 (:REWRITE DEFAULT-+-1))
                             (9 9
                                (:REWRITE TRUNCATE-OF-Y-NEGATIVE-INVERT))
                             (6 2 (:REWRITE <-MINUS-ZERO))
                             (3 1 (:REWRITE <-+-NEGATIVE-0-2))
                             (2 2 (:REWRITE EQUAL-CONSTANT-+)))
(REM-OF-Y-POSITIVE-BASE-CASE (5 5 (:REWRITE DEFAULT-<-2))
                             (5 5 (:REWRITE DEFAULT-<-1))
                             (3 1 (:REWRITE REM-OF-X-NEGATIVE-INVERT))
                             (3 1
                                (:REWRITE REM-OF-NONNEG-OPERANDS-BASE-CASE))
                             (2 2 (:REWRITE DEFAULT-+-2))
                             (2 2 (:REWRITE DEFAULT-+-1))
                             (1 1 (:REWRITE REM-OF-Y-NEGATIVE-INVERT))
                             (1 1
                                (:REWRITE REM-OF-NONNEG-OPERANDS-STEP))
                             (1 1 (:REWRITE DEFAULT-UNARY-MINUS)))
(REM-OF-X-NEGATIVE-STEP (20 9 (:REWRITE DEFAULT-+-2))
                        (16 16 (:TYPE-PRESCRIPTION TRUNCATE))
                        (14 14 (:REWRITE DEFAULT-<-2))
                        (14 14 (:REWRITE DEFAULT-<-1))
                        (11 7 (:REWRITE DEFAULT-*-2))
                        (10 7 (:REWRITE DEFAULT-*-1))
                        (9 9 (:REWRITE DEFAULT-+-1))
                        (8 6 (:REWRITE DEFAULT-UNARY-MINUS))
                        (6 2
                           (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
                        (6 2
                           (:REWRITE TRUNCATE-OF-X-NEGATIVE-INVERT))
                        (6 2
                           (:REWRITE TRUNCATE-OF-NONNEG-OPERANDS-STEP))
                        (6 2
                           (:REWRITE TRUNCATE-OF-NONNEG-OPERANDS-BASE-CASE))
                        (6 2
                           (:REWRITE REM-OF-NONNEG-OPERANDS-STEP))
                        (6 2
                           (:REWRITE REM-OF-NONNEG-OPERANDS-BASE-CASE))
                        (4 2
                           (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
                        (2 2
                           (:REWRITE TRUNCATE-OF-Y-NEGATIVE-INVERT))
                        (2 2 (:REWRITE REM-OF-Y-NEGATIVE-INVERT))
                        (2 2 (:REWRITE FOLD-CONSTS-IN-+)))
(TRUNCATE-OF-Y-NEGATIVE-BASE-CASE
     (11 11 (:REWRITE DEFAULT-<-2))
     (11 11 (:REWRITE DEFAULT-<-1))
     (8 8 (:REWRITE DEFAULT-UNARY-MINUS))
     (5 3
        (:REWRITE TRUNCATE-OF-NONNEG-OPERANDS-STEP)))
(TRUNCATE-OF-Y-NEGATIVE-STEP (19 17 (:REWRITE DEFAULT-UNARY-MINUS))
                             (14 11 (:REWRITE DEFAULT-+-2))
                             (11 11 (:REWRITE DEFAULT-+-1))
                             (8 8 (:REWRITE DEFAULT-<-2))
                             (8 8 (:REWRITE DEFAULT-<-1)))
(REM-OF-Y-NEGATIVE-BASE-CASE (5 5 (:REWRITE DEFAULT-<-2))
                             (5 5 (:REWRITE DEFAULT-<-1))
                             (3 1 (:REWRITE REM-OF-X-NEGATIVE-INVERT))
                             (3 1
                                (:REWRITE REM-OF-NONNEG-OPERANDS-BASE-CASE))
                             (2 2 (:REWRITE DEFAULT-+-2))
                             (2 2 (:REWRITE DEFAULT-+-1))
                             (1 1
                                (:REWRITE REM-OF-NONNEG-OPERANDS-STEP))
                             (1 1 (:REWRITE DEFAULT-UNARY-MINUS)))
(REM-OF-Y-NEGATIVE-STEP (34 30
                            (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
                        (32 30
                            (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
                        (24 16 (:REWRITE DEFAULT-<-1))
                        (24 2
                            (:REWRITE TRUNCATE-OF-NONNEG-OPERANDS-BASE-CASE))
                        (22 11 (:REWRITE DEFAULT-+-2))
                        (22 2
                            (:REWRITE TRUNCATE-OF-NONNEG-OPERANDS-STEP))
                        (16 16 (:TYPE-PRESCRIPTION TRUNCATE))
                        (16 16 (:REWRITE DEFAULT-<-2))
                        (16 2
                            (:REWRITE TRUNCATE-OF-X-NEGATIVE-INVERT))
                        (14 12 (:REWRITE DEFAULT-UNARY-MINUS))
                        (12 4 (:REWRITE <-+-NEGATIVE-0-2))
                        (11 11 (:REWRITE DEFAULT-+-1))
                        (11 7 (:REWRITE DEFAULT-*-2))
                        (10 7 (:REWRITE DEFAULT-*-1))
                        (6 2 (:REWRITE REM-OF-X-NEGATIVE-INVERT))
                        (6 2
                           (:REWRITE REM-OF-NONNEG-OPERANDS-BASE-CASE))
                        (2 2
                           (:REWRITE REM-OF-NONNEG-OPERANDS-STEP))
                        (2 2 (:REWRITE FOLD-CONSTS-IN-+)))
(TRUNCATE-OF-NEGATIVE-OPERANDS-STEP
     (11 3
         (:REWRITE TRUNCATE-OF-X-NEGATIVE-INVERT))
     (10 10
         (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
     (8 6 (:REWRITE DEFAULT-<-1))
     (8 2
        (:REWRITE TRUNCATE-OF-NONNEG-OPERANDS-BASE-CASE))
     (7 5 (:REWRITE DEFAULT-+-2))
     (6 6 (:REWRITE DEFAULT-<-2))
     (5 5
        (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
     (5 5 (:REWRITE DEFAULT-UNARY-MINUS))
     (5 5 (:REWRITE DEFAULT-+-1))
     (3 1 (:REWRITE <-MINUS-ZERO))
     (3 1 (:REWRITE <-+-NEGATIVE-0-1)))
(REM-OF-NEGATIVE-OPERANDS-STEP
     (34 34
         (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
     (29 13 (:REWRITE DEFAULT-+-2))
     (18 12 (:REWRITE DEFAULT-<-1))
     (15 13 (:REWRITE DEFAULT-+-1))
     (15 11 (:REWRITE DEFAULT-UNARY-MINUS))
     (14 2
         (:REWRITE TRUNCATE-OF-NONNEG-OPERANDS-STEP))
     (14 2
         (:REWRITE TRUNCATE-OF-NONNEG-OPERANDS-BASE-CASE))
     (12 12 (:REWRITE DEFAULT-<-2))
     (12 2
         (:REWRITE TRUNCATE-OF-X-NEGATIVE-INVERT))
     (11 3 (:REWRITE REM-OF-X-NEGATIVE-INVERT))
     (9 3 (:REWRITE <-+-NEGATIVE-0-1))
     (8 2
        (:REWRITE REM-OF-NONNEG-OPERANDS-BASE-CASE))
     (7 3
        (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
     (6 4 (:REWRITE DEFAULT-*-2))
     (6 4 (:REWRITE DEFAULT-*-1))
     (4 4 (:REWRITE FOLD-CONSTS-IN-+))
     (3 1 (:REWRITE <-MINUS-ZERO))
     (2 2
        (:REWRITE TRUNCATE-OF-Y-NEGATIVE-INVERT)))
(TRUNCATE-WHEN-Y-IS-0)
(REM-WHEN-Y-IS-0 (5 5
                    (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                 (4 3 (:REWRITE DEFAULT-<-1))
                 (4 1 (:REWRITE REM-OF-X-NEGATIVE-INVERT))
                 (3 3 (:REWRITE DEFAULT-<-2))
                 (3 2 (:REWRITE DEFAULT-+-2))
                 (3 2 (:REWRITE DEFAULT-+-1))
                 (3 1
                    (:REWRITE REM-OF-NONNEG-OPERANDS-STEP))
                 (3 1
                    (:REWRITE REM-OF-NONNEG-OPERANDS-BASE-CASE))
                 (1 1 (:REWRITE REM-OF-Y-NEGATIVE-INVERT)))
(TRUNCATE-REDEF (120 120
                     (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
                (88 74 (:REWRITE DEFAULT-<-1))
                (84 74 (:REWRITE DEFAULT-<-2))
                (61 14
                    (:REWRITE TRUNCATE-OF-Y-POSITIVE-BASE-CASE))
                (47 47 (:REWRITE DEFAULT-UNARY-MINUS))
                (47 13
                    (:REWRITE TRUNCATE-OF-NONNEG-OPERANDS-BASE-CASE))
                (36 24 (:REWRITE DEFAULT-+-2))
                (24 24 (:REWRITE DEFAULT-+-1)))
(REM-REDEF (112 112
                (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
           (92 78 (:REWRITE DEFAULT-<-1))
           (88 78 (:REWRITE DEFAULT-<-2))
           (50 50 (:REWRITE DEFAULT-UNARY-MINUS))
           (47 13
               (:REWRITE REM-OF-NONNEG-OPERANDS-BASE-CASE))
           (12 12 (:REWRITE DEFAULT-+-2))
           (12 12 (:REWRITE DEFAULT-+-1)))
(NONNEG-INT-QUOTIENT-EQUAL-0 (38 38
                                 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
                             (37 35 (:REWRITE DEFAULT-<-2))
                             (36 35 (:REWRITE DEFAULT-<-1))
                             (16 11 (:REWRITE DEFAULT-+-2))
                             (12 11 (:REWRITE DEFAULT-+-1))
                             (6 5 (:REWRITE DEFAULT-UNARY-MINUS))
                             (4 4
                                (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP)))
(NATP-NONNEG-INT-QUOTIENT)
(TRUNCATE-NEGATIVE (38 22 (:REWRITE /R-WHEN-ABS-NUMERATOR=1))
                   (37 36 (:REWRITE DEFAULT-<-1))
                   (36 36 (:REWRITE DEFAULT-<-2))
                   (17 12 (:REWRITE NUMERATOR-WHEN-INTEGERP))
                   (16 15 (:REWRITE DEFAULT-UNARY-MINUS))
                   (16 10
                       (:REWRITE INTEGERP-OF-DIVIDE-WHEN-LESS))
                   (12 12 (:REWRITE DEFAULT-NUMERATOR))
                   (11 11 (:REWRITE DEFAULT-UNARY-/))
                   (11 11 (:REWRITE DEFAULT-*-2))
                   (11 11 (:REWRITE DEFAULT-*-1))
                   (11 4 (:REWRITE INTEGERP==>DENOMINATOR=1))
                   (8 6 (:REWRITE DEFAULT-+-2))
                   (6 6 (:REWRITE DEFAULT-+-1))
                   (6 2 (:REWRITE COMMUTATIVITY-OF-+))
                   (6 2 (:LINEAR X*Y>1-POSITIVE))
                   (4 4 (:REWRITE DEFAULT-DENOMINATOR)))
(TRUNCATE-NONNEGATIVE)
(TRUNCATE-NEGATIVE-LEMMA
     (23 15 (:REWRITE DEFAULT-<-1))
     (22 2
         (:REWRITE TRUNCATE-OF-NONNEG-OPERANDS-BASE-CASE))
     (20 20
         (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
     (20 20
         (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
     (16 15 (:REWRITE DEFAULT-<-2))
     (9 8 (:REWRITE DEFAULT-UNARY-MINUS))
     (9 7 (:REWRITE DEFAULT-+-2))
     (7 7 (:REWRITE DEFAULT-+-1))
     (5 5
        (:REWRITE TRUNCATE-OF-Y-NEGATIVE-INVERT))
     (4 1 (:LINEAR TRUNCATE-NEGATIVE))
     (1 1 (:LINEAR TRUNCATE-NONNEGATIVE)))
(TRUNCATE/REM-NATS-IND (40 40
                           (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
                       (39 28 (:REWRITE DEFAULT-<-1))
                       (30 28 (:REWRITE DEFAULT-<-2))
                       (25 5
                           (:REWRITE TRUNCATE-OF-NONNEG-OPERANDS-BASE-CASE))
                       (21 6
                           (:REWRITE TRUNCATE-OF-X-NEGATIVE-INVERT))
                       (6 6
                          (:REWRITE TRUNCATE-OF-Y-NEGATIVE-INVERT))
                       (4 3 (:REWRITE DEFAULT-+-2))
                       (3 3 (:REWRITE DEFAULT-+-1))
                       (2 2 (:REWRITE DEFAULT-UNARY-MINUS)))
(TRUNCATE-REM-IND (1121 182 (:REWRITE COMMUTATIVITY-OF-+))
                  (1045 718 (:REWRITE DEFAULT-<-1))
                  (1034 958
                        (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
                  (885 659 (:REWRITE DEFAULT-+-2))
                  (852 91 (:REWRITE COMMUTATIVITY-2-OF-+))
                  (842 718 (:REWRITE DEFAULT-<-2))
                  (663 659 (:REWRITE DEFAULT-+-1))
                  (290 282 (:REWRITE DEFAULT-UNARY-MINUS))
                  (160 40 (:DEFINITION O-FIRST-EXPT))
                  (151 151 (:REWRITE FOLD-CONSTS-IN-+))
                  (124 31 (:DEFINITION O-FIRST-COEFF))
                  (114 114 (:REWRITE DEFAULT-CAR))
                  (67 13 (:LINEAR TRUNCATE-NEGATIVE))
                  (58 29
                      (:REWRITE MINUS-CANCELLATION-ON-RIGHT))
                  (53 39
                      (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                  (51 51 (:REWRITE DEFAULT-CDR))
                  (42 10 (:REWRITE <-+-NEGATIVE-0-1))
                  (40 20 (:DEFINITION O-RST))
                  (31 31 (:REWRITE INVERSE-OF-+))
                  (17 17 (:REWRITE EQUAL-CONSTANT-+))
                  (12 3 (:REWRITE NATP-POSP))
                  (10 6 (:REWRITE NATP-RW))
                  (6 6 (:TYPE-PRESCRIPTION NATP))
                  (3 3 (:REWRITE POSP-RW)))
