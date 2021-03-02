(FM9001::4VP)
(FM9001::4V-FIX (1 1 (:TYPE-PRESCRIPTION FM9001::4V-FIX)))
(FM9001::4V-LISTP)
(FM9001::3VP)
(FM9001::3V-FIX (1 1 (:TYPE-PRESCRIPTION FM9001::3V-FIX)))
(FM9001::3V-FIX-IDEMPOTENT (34 34 (:TYPE-PRESCRIPTION FM9001::3V-FIX))
                           (1 1 (:TYPE-PRESCRIPTION FM9001::3VP)))
(FM9001::3V-LISTP)
(FM9001::BVP)
(FM9001::BOOLEANP-CAR-OF-BVP (1 1 (:REWRITE DEFAULT-CAR)))
(FM9001::NTH-OF-BVP-IS-BOOLEANP (9 9 (:REWRITE DEFAULT-CAR))
                                (5 5 (:REWRITE ZP-OPEN))
                                (4 4 (:REWRITE DEFAULT-CDR))
                                (2 2 (:REWRITE DEFAULT-+-2))
                                (2 2 (:REWRITE DEFAULT-+-1)))
(FM9001::BVP-TAKE (87 9 (:REWRITE TAKE-OF-LEN-FREE))
                  (78 14 (:DEFINITION LEN))
                  (60 18 (:REWRITE ZP-OPEN))
                  (50 8 (:REWRITE REPEAT-WHEN-ZP))
                  (46 40 (:REWRITE DEFAULT-<-2))
                  (44 28 (:REWRITE DEFAULT-+-2))
                  (44 27 (:REWRITE DEFAULT-CDR))
                  (40 40 (:REWRITE DEFAULT-<-1))
                  (28 28 (:REWRITE DEFAULT-+-1))
                  (24 16 (:REWRITE DEFAULT-CAR))
                  (20 3 (:REWRITE CAR-OF-TAKE))
                  (17 6 (:REWRITE CONSP-OF-TAKE))
                  (13 6 (:REWRITE CONSP-OF-REPEAT))
                  (6 6 (:REWRITE TAKE-WHEN-ATOM)))
(FM9001::BVP-NTHCDR (14 14 (:REWRITE DEFAULT-+-2))
                    (14 14 (:REWRITE DEFAULT-+-1))
                    (14 8 (:REWRITE ZP-OPEN))
                    (13 13 (:REWRITE DEFAULT-CAR))
                    (10 10 (:REWRITE DEFAULT-CDR))
                    (6 2 (:REWRITE FOLD-CONSTS-IN-+))
                    (2 2 (:REWRITE DEFAULT-<-2))
                    (2 2 (:REWRITE DEFAULT-<-1)))
(FM9001::BVP-REPEAT-OF-BOOLEANP (25 5 (:REWRITE REPEAT-WHEN-ZP))
                                (23 10 (:REWRITE ZP-OPEN))
                                (20 9 (:REWRITE CONSP-OF-REPEAT))
                                (14 4 (:REWRITE DEFAULT-CDR))
                                (14 4 (:REWRITE DEFAULT-CAR))
                                (6 6 (:REWRITE DEFAULT-<-2))
                                (6 6 (:REWRITE DEFAULT-<-1))
                                (2 2 (:REWRITE DEFAULT-+-2))
                                (2 2 (:REWRITE DEFAULT-+-1)))
(FM9001::BVP-APPEND (21 18 (:REWRITE DEFAULT-CAR))
                    (18 15 (:REWRITE DEFAULT-CDR))
                    (18 9
                        (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
                    (9 9 (:TYPE-PRESCRIPTION TRUE-LISTP))
                    (9 9 (:TYPE-PRESCRIPTION BINARY-APPEND)))
(FM9001::BVP-REV (39 39 (:TYPE-PRESCRIPTION REV))
                 (33 3 (:DEFINITION BINARY-APPEND))
                 (32 14 (:REWRITE DEFAULT-CAR))
                 (29 11 (:REWRITE DEFAULT-CDR))
                 (18 18 (:REWRITE CONSP-OF-REV))
                 (5 5 (:REWRITE REV-WHEN-NOT-CONSP)))
(FM9001::BVP-IS-TRUE-LISTP (4 4 (:REWRITE DEFAULT-CDR))
                           (4 2 (:DEFINITION TRUE-LISTP))
                           (3 3 (:REWRITE DEFAULT-CAR)))
(FM9001::TRUE-LISTP-MAKE-LIST)
(FM9001::BVP-MAKE-LIST (32 8 (:REWRITE REPEAT-WHEN-ZP))
                       (21 12 (:REWRITE CONSP-OF-REPEAT))
                       (20 6 (:REWRITE DEFAULT-CDR))
                       (20 6 (:REWRITE DEFAULT-CAR))
                       (9 9 (:REWRITE DEFAULT-<-2))
                       (9 9 (:REWRITE DEFAULT-<-1))
                       (4 4 (:REWRITE DEFAULT-+-2))
                       (4 4 (:REWRITE DEFAULT-+-1)))
(FM9001::LEN-MAKE-LIST (4 1 (:REWRITE REPEAT-WHEN-ZP))
                       (2 2 (:TYPE-PRESCRIPTION ZP))
                       (2 2 (:REWRITE DEFAULT-<-2))
                       (2 2 (:REWRITE DEFAULT-<-1))
                       (1 1 (:REWRITE ZP-OPEN)))
(FM9001::BV2P)
(FM9001::BVP-LEN)
(FM9001::BVP-LEN-CDR (12 6 (:REWRITE DEFAULT-+-2))
                     (9 9 (:REWRITE DEFAULT-CDR))
                     (6 6 (:REWRITE DEFAULT-+-1))
                     (6 4 (:REWRITE DEFAULT-<-2))
                     (6 4 (:REWRITE DEFAULT-<-1))
                     (4 4
                        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                     (4 4 (:REWRITE DEFAULT-CAR)))
(FM9001::BOOL-FIX-CAR-X=X (10 5 (:REWRITE DEFAULT-+-2))
                          (8 8 (:REWRITE DEFAULT-CDR))
                          (8 8 (:REWRITE DEFAULT-CAR))
                          (6 3 (:REWRITE DEFAULT-<-1))
                          (5 5 (:REWRITE DEFAULT-+-1))
                          (4 4 (:TYPE-PRESCRIPTION BOOLEANP))
                          (3 3 (:REWRITE DEFAULT-<-2)))
(FM9001::BOOLEANP-CAR-X)
(FM9001::BVP-LEN-NTHCDR
     (112 67 (:REWRITE DEFAULT-+-2))
     (73 67 (:REWRITE DEFAULT-+-1))
     (70 40 (:REWRITE DEFAULT-<-1))
     (58 40 (:REWRITE DEFAULT-<-2))
     (40 20
         (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
     (30 30 (:REWRITE DEFAULT-CDR))
     (20 20 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (18 18
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (14 14 (:REWRITE DEFAULT-CAR))
     (9 9 (:REWRITE DEFAULT-UNARY-MINUS))
     (6 6 (:REWRITE ZP-OPEN)))
(FM9001::B-BUF)
(FM9001::B-NOT)
(FM9001::B-NAND)
(FM9001::B-NAND3)
(FM9001::B-NAND4)
(FM9001::B-NAND5)
(FM9001::B-NAND6)
(FM9001::B-NAND8)
(FM9001::B-OR)
(FM9001::B-OR3)
(FM9001::B-OR4)
(FM9001::B-XOR)
(FM9001::B-XOR3)
(FM9001::B-EQUV)
(FM9001::B-EQUV3)
(FM9001::B-AND)
(FM9001::B-AND3)
(FM9001::B-AND4)
(FM9001::B-NOR)
(FM9001::B-NOR3)
(FM9001::B-NOR4)
(FM9001::B-NOR5)
(FM9001::B-NOR6)
(FM9001::B-NOR8)
(FM9001::B-IF)
(FM9001::BOOLEANP-B-GATES)
(FM9001::AO2)
(FM9001::AO4)
(FM9001::AO6)
(FM9001::AO7)
(FM9001::VSS)
(FM9001::VDD)
(FM9001::V-BUF)
(FM9001::V-NOT)
(FM9001::V-AND)
(FM9001::V-OR)
(FM9001::V-XOR)
(FM9001::V-SHIFT-RIGHT)
(FM9001::V-LSR)
(FM9001::V-ROR)
(FM9001::V-ASR (12 4 (:REWRITE FM9001::BVP-IS-TRUE-LISTP))
               (10 2 (:DEFINITION TRUE-LISTP))
               (7 4 (:REWRITE DEFAULT-+-2))
               (5 5 (:REWRITE DEFAULT-CDR))
               (4 4 (:REWRITE DEFAULT-+-1)))
(FM9001::V-IF)
(FM9001::BVP-V-BUF (8 7 (:REWRITE DEFAULT-CAR))
                   (7 6 (:REWRITE DEFAULT-CDR)))
(FM9001::BVP-V-NOT (8 7 (:REWRITE DEFAULT-CAR))
                   (7 6 (:REWRITE DEFAULT-CDR)))
(FM9001::BVP-V-AND (11 10 (:REWRITE DEFAULT-CAR))
                   (9 8 (:REWRITE DEFAULT-CDR))
                   (9 3 (:REWRITE BOOL-FIX-WHEN-BOOLEANP))
                   (9 3 (:REWRITE FM9001::BOOL-FIX-CAR-X=X))
                   (6 6 (:TYPE-PRESCRIPTION FM9001::BVP-LEN))
                   (6 6 (:TYPE-PRESCRIPTION BOOLEANP)))
(FM9001::BVP-V-OR (18 6 (:REWRITE FM9001::BOOL-FIX-CAR-X=X))
                  (12 12 (:TYPE-PRESCRIPTION FM9001::BVP-LEN))
                  (11 10 (:REWRITE DEFAULT-CAR))
                  (9 8 (:REWRITE DEFAULT-CDR))
                  (9 3 (:REWRITE BOOL-FIX-WHEN-BOOLEANP))
                  (6 6 (:TYPE-PRESCRIPTION BOOLEANP)))
(FM9001::BVP-V-XOR (11 10 (:REWRITE DEFAULT-CAR))
                   (9 8 (:REWRITE DEFAULT-CDR)))
(FM9001::BVP-V-SHIFT-RIGHT (10 2 (:DEFINITION BINARY-APPEND))
                           (8 8 (:REWRITE DEFAULT-CDR))
                           (8 2 (:DEFINITION FM9001::V-BUF))
                           (6 6 (:TYPE-PRESCRIPTION FM9001::V-BUF))
                           (6 6 (:REWRITE DEFAULT-CAR))
                           (6 2 (:REWRITE BOOL-FIX-WHEN-BOOLEANP))
                           (4 4 (:TYPE-PRESCRIPTION BOOLEANP))
                           (4 2
                              (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
                           (2 2 (:TYPE-PRESCRIPTION BINARY-APPEND))
                           (2 2 (:DEFINITION FM9001::B-BUF)))
(FM9001::BVP-V-LSR)
(FM9001::BVP-V-ASR (34 2 (:DEFINITION NTH))
                   (24 2 (:REWRITE BOOL-FIX-WHEN-BOOLEANP))
                   (18 6
                       (:TYPE-PRESCRIPTION FM9001::NTH-OF-BVP-IS-BOOLEANP))
                   (16 2 (:REWRITE ZP-OPEN))
                   (15 8 (:REWRITE DEFAULT-+-2))
                   (14 14 (:REWRITE DEFAULT-CDR))
                   (10 2 (:DEFINITION BINARY-APPEND))
                   (8 8 (:REWRITE DEFAULT-CAR))
                   (8 8 (:REWRITE DEFAULT-+-1))
                   (8 2 (:DEFINITION FM9001::V-BUF))
                   (6 6 (:TYPE-PRESCRIPTION FM9001::V-BUF))
                   (4 4 (:TYPE-PRESCRIPTION BOOLEANP))
                   (4 2
                      (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
                   (4 2 (:REWRITE DEFAULT-<-2))
                   (2 2 (:TYPE-PRESCRIPTION BINARY-APPEND))
                   (2 2 (:REWRITE DEFAULT-<-1))
                   (2 2 (:DEFINITION FM9001::B-BUF)))
(FM9001::BVP-V-ROR)
(FM9001::BVP-V-IF (84 76 (:REWRITE DEFAULT-CDR))
                  (38 30 (:REWRITE DEFAULT-CAR)))
(FM9001::LEN-V-BUF (14 7 (:REWRITE DEFAULT-+-2))
                   (9 8 (:REWRITE DEFAULT-CDR))
                   (7 7 (:REWRITE DEFAULT-+-1))
                   (3 3 (:REWRITE DEFAULT-CAR)))
(FM9001::LEN-V-NOT (14 7 (:REWRITE DEFAULT-+-2))
                   (9 8 (:REWRITE DEFAULT-CDR))
                   (7 7 (:REWRITE DEFAULT-+-1))
                   (3 3 (:REWRITE DEFAULT-CAR)))
(FM9001::LEN-V-AND (14 7 (:REWRITE DEFAULT-+-2))
                   (11 10 (:REWRITE DEFAULT-CDR))
                   (9 3 (:REWRITE BOOL-FIX-WHEN-BOOLEANP))
                   (9 3 (:REWRITE FM9001::BOOL-FIX-CAR-X=X))
                   (7 7 (:REWRITE DEFAULT-+-1))
                   (6 6 (:TYPE-PRESCRIPTION FM9001::BVP-LEN))
                   (6 6 (:TYPE-PRESCRIPTION BOOLEANP))
                   (6 6 (:REWRITE DEFAULT-CAR)))
(FM9001::LEN-V-OR (18 6 (:REWRITE FM9001::BOOL-FIX-CAR-X=X))
                  (14 7 (:REWRITE DEFAULT-+-2))
                  (12 12 (:TYPE-PRESCRIPTION FM9001::BVP-LEN))
                  (11 10 (:REWRITE DEFAULT-CDR))
                  (9 3 (:REWRITE BOOL-FIX-WHEN-BOOLEANP))
                  (7 7 (:REWRITE DEFAULT-+-1))
                  (6 6 (:TYPE-PRESCRIPTION BOOLEANP))
                  (6 6 (:REWRITE DEFAULT-CAR)))
(FM9001::LEN-V-XOR (14 7 (:REWRITE DEFAULT-+-2))
                   (11 10 (:REWRITE DEFAULT-CDR))
                   (7 7 (:REWRITE DEFAULT-+-1))
                   (6 6 (:REWRITE DEFAULT-CAR)))
(FM9001::LEN-V-SHIFT-RIGHT (100 75 (:REWRITE DEFAULT-CDR))
                           (68 34 (:REWRITE DEFAULT-+-2))
                           (34 34 (:REWRITE DEFAULT-+-1))
                           (34 12 (:REWRITE BOOL-FIX-WHEN-BOOLEANP))
                           (26 25 (:REWRITE DEFAULT-CAR))
                           (23 23
                               (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
                           (22 22 (:TYPE-PRESCRIPTION BOOLEANP)))
(FM9001::LEN-V-LSR)
(FM9001::LEN-V-ASR (142 117 (:REWRITE DEFAULT-CDR))
                   (134 72 (:REWRITE DEFAULT-+-2))
                   (133 12 (:REWRITE BOOL-FIX-WHEN-BOOLEANP))
                   (99 33
                       (:TYPE-PRESCRIPTION FM9001::NTH-OF-BVP-IS-BOOLEANP))
                   (96 12 (:REWRITE ZP-OPEN))
                   (72 72 (:REWRITE DEFAULT-+-1))
                   (38 37 (:REWRITE DEFAULT-CAR))
                   (33 33 (:TYPE-PRESCRIPTION FM9001::BVP))
                   (24 12 (:REWRITE DEFAULT-<-2))
                   (23 23
                       (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
                   (22 22 (:TYPE-PRESCRIPTION BOOLEANP))
                   (12 12 (:REWRITE DEFAULT-<-1)))
(FM9001::LEN-V-ROR)
(FM9001::LEN-V-IF (110 102 (:REWRITE DEFAULT-CDR))
                  (70 35 (:REWRITE DEFAULT-+-2))
                  (35 35 (:REWRITE DEFAULT-+-1))
                  (18 18 (:REWRITE DEFAULT-CAR)))
(FM9001::APPEND-V-AND (121 66 (:REWRITE DEFAULT-CAR))
                      (109 54 (:REWRITE DEFAULT-CDR))
                      (108 24 (:REWRITE BOOL-FIX-WHEN-BOOLEANP))
                      (72 24 (:REWRITE FM9001::BOOL-FIX-CAR-X=X))
                      (54 54 (:TYPE-PRESCRIPTION TRUE-LISTP))
                      (48 48 (:TYPE-PRESCRIPTION FM9001::BVP-LEN))
                      (48 48 (:TYPE-PRESCRIPTION BOOLEANP))
                      (20 10 (:REWRITE DEFAULT-+-2))
                      (10 10 (:REWRITE DEFAULT-+-1)))
(FM9001::APPEND-V-OR (132 44 (:REWRITE FM9001::BOOL-FIX-CAR-X=X))
                     (121 66 (:REWRITE DEFAULT-CAR))
                     (109 54 (:REWRITE DEFAULT-CDR))
                     (108 24 (:REWRITE BOOL-FIX-WHEN-BOOLEANP))
                     (88 88 (:TYPE-PRESCRIPTION FM9001::BVP-LEN))
                     (54 54 (:TYPE-PRESCRIPTION TRUE-LISTP))
                     (48 48 (:TYPE-PRESCRIPTION BOOLEANP))
                     (20 10 (:REWRITE DEFAULT-+-2))
                     (10 10 (:REWRITE DEFAULT-+-1)))
(FM9001::APPEND-V-XOR (125 70 (:REWRITE DEFAULT-CAR))
                      (109 54 (:REWRITE DEFAULT-CDR))
                      (62 62 (:TYPE-PRESCRIPTION TRUE-LISTP))
                      (20 10 (:REWRITE DEFAULT-+-2))
                      (10 10 (:REWRITE DEFAULT-+-1)))
(FM9001::APPEND-V-NOT (26 22 (:REWRITE DEFAULT-CAR))
                      (23 19 (:REWRITE DEFAULT-CDR))
                      (11 11 (:TYPE-PRESCRIPTION TRUE-LISTP)))
(FM9001::APPEND-V-BUF (26 22 (:REWRITE DEFAULT-CAR))
                      (23 19 (:REWRITE DEFAULT-CDR))
                      (11 11 (:TYPE-PRESCRIPTION TRUE-LISTP)))
(FM9001::APPEND-V-IF (846 357 (:REWRITE DEFAULT-CDR))
                     (276 276 (:TYPE-PRESCRIPTION TRUE-LISTP))
                     (262 121 (:REWRITE DEFAULT-CAR))
                     (52 26 (:REWRITE DEFAULT-+-2))
                     (26 26 (:REWRITE DEFAULT-+-1)))
(FM9001::V-IF-C-CONGRUENCE (24 24 (:REWRITE DEFAULT-CDR))
                           (8 8 (:REWRITE DEFAULT-CAR)))
(FM9001::V-NOT-TAKE (381 32 (:REWRITE TAKE-OF-LEN-FREE))
                    (162 93 (:REWRITE DEFAULT-+-2))
                    (145 103 (:REWRITE DEFAULT-CDR))
                    (127 93 (:REWRITE DEFAULT-<-2))
                    (100 93 (:REWRITE DEFAULT-<-1))
                    (97 17 (:REWRITE FM9001::LEN-V-NOT))
                    (93 93 (:REWRITE DEFAULT-+-1))
                    (77 29 (:REWRITE TAKE-WHEN-ATOM))
                    (62 36 (:REWRITE DEFAULT-CAR))
                    (62 23 (:REWRITE ZP-OPEN))
                    (36 5 (:REWRITE CAR-OF-TAKE))
                    (33 10 (:REWRITE CONSP-OF-TAKE))
                    (30 10 (:REWRITE FOLD-CONSTS-IN-+))
                    (6 6
                       (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                    (6 1 (:REWRITE APPEND-TO-NIL))
                    (3 1 (:REWRITE FM9001::BVP-IS-TRUE-LISTP))
                    (2 2 (:TYPE-PRESCRIPTION FM9001::BVP))
                    (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP))
                    (1 1 (:DEFINITION TRUE-LISTP)))
(FM9001::TAKE-V-NOT (134 3 (:DEFINITION TAKE))
                    (91 6 (:REWRITE TAKE-OF-TOO-MANY))
                    (64 6 (:REWRITE TAKE-OF-LEN-FREE))
                    (63 11 (:DEFINITION LEN))
                    (25 14 (:REWRITE DEFAULT-+-2))
                    (22 16 (:REWRITE DEFAULT-CDR))
                    (17 11 (:REWRITE DEFAULT-<-2))
                    (15 6 (:REWRITE TAKE-WHEN-ATOM))
                    (15 5 (:DEFINITION NFIX))
                    (14 14 (:REWRITE DEFAULT-+-1))
                    (12 11 (:REWRITE DEFAULT-<-1))
                    (12 2 (:REWRITE FM9001::LEN-V-NOT))
                    (11 5 (:REWRITE DEFAULT-CAR))
                    (8 2 (:DEFINITION FM9001::V-NOT))
                    (5 5 (:TYPE-PRESCRIPTION NFIX))
                    (3 3 (:REWRITE ZP-OPEN))
                    (2 2 (:DEFINITION FM9001::B-NOT))
                    (1 1
                       (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP)))
(FM9001::NTHCDR-NIL (6 2 (:REWRITE COMMUTATIVITY-OF-+))
                    (4 4 (:REWRITE ZP-OPEN))
                    (4 4 (:REWRITE DEFAULT-+-2))
                    (4 4 (:REWRITE DEFAULT-+-1)))
(FM9001::V-NOT-NTHCDR (72 30 (:REWRITE ZP-OPEN))
                      (68 68 (:REWRITE DEFAULT-+-2))
                      (68 68 (:REWRITE DEFAULT-+-1))
                      (42 14 (:REWRITE FOLD-CONSTS-IN-+))
                      (36 36 (:REWRITE DEFAULT-CAR))
                      (14 14 (:REWRITE DEFAULT-<-2))
                      (14 14 (:REWRITE DEFAULT-<-1)))
(FM9001::NTHCDR-V-NOT)
(FM9001::NTH-V-NOT (46 33 (:REWRITE DEFAULT-+-2))
                   (42 38 (:REWRITE DEFAULT-CDR))
                   (36 35 (:REWRITE DEFAULT-CAR))
                   (33 33 (:REWRITE DEFAULT-+-1))
                   (28 15 (:REWRITE DEFAULT-<-2))
                   (23 15 (:REWRITE DEFAULT-<-1))
                   (19 19 (:REWRITE ZP-OPEN))
                   (8 8
                      (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP)))
(FM9001::V-OR-MAKE-LIST (102 9 (:REWRITE ZP-OPEN))
                        (92 6 (:REWRITE REPEAT-WHEN-ZP))
                        (36 18 (:REWRITE DEFAULT-<-2))
                        (29 17 (:REWRITE DEFAULT-CDR))
                        (27 9 (:REWRITE FM9001::BOOL-FIX-CAR-X=X))
                        (26 14 (:REWRITE DEFAULT-CAR))
                        (18 18 (:TYPE-PRESCRIPTION FM9001::BVP-LEN))
                        (18 18 (:REWRITE DEFAULT-<-1))
                        (8 8 (:TYPE-PRESCRIPTION BOOLEANP))
                        (8 4 (:REWRITE DEFAULT-+-2))
                        (5 5 (:TYPE-PRESCRIPTION ZP))
                        (4 4 (:REWRITE DEFAULT-+-1))
                        (4 4 (:REWRITE BOOL-FIX-UNDER-IFF)))
(FM9001::V-TO-NAT)
(FM9001::NATP-V-TO-NAT)
(FM9001::BIT->BOOL)
(FM9001::BOOLEANP-BIT->BOOL)
(FM9001::NAT-TO-V
     (213 213
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (213 213
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (213 213
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (213 213
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (210 42 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (210 42 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (194 42
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (194 42
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (42 42 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (42 42 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (42 42
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (42 42 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (42 42
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (42 42 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (40 4 (:REWRITE DEFAULT-MOD-RATIO))
     (22 1 (:LINEAR MOD-BOUNDS-3))
     (20 5 (:REWRITE |(* y x)|))
     (19 19 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (19 19 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (19 19 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (19 19 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (18 2 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (14 14 (:REWRITE DEFAULT-TIMES-2))
     (14 14 (:REWRITE DEFAULT-TIMES-1))
     (14 2
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (14 2
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (14 2
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (10 2 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
     (10 2 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (10 2 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (10 2
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (10 2
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (10 2
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (10 2
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (10 2
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (10 2
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (10 2
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (10 2 (:LINEAR MOD-BOUNDS-2))
     (9 9
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (6 6 (:REWRITE REDUCE-INTEGERP-+))
     (6 6 (:REWRITE INTEGERP-MINUS-X))
     (6 6 (:META META-INTEGERP-CORRECT))
     (5 1
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (4 4 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (4 4 (:REWRITE DEFAULT-MOD-2))
     (4 4 (:REWRITE DEFAULT-MOD-1))
     (4 4 (:REWRITE |(mod x 2)| . 2))
     (2 2 (:REWRITE THE-FLOOR-BELOW))
     (2 2 (:REWRITE THE-FLOOR-ABOVE))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (2 2 (:REWRITE SIMPLIFY-SUMS-<))
     (2 2
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (2 2 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (2 2 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (2 2
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (2 2
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (2 2 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (2 2 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (2 2 (:REWRITE INTEGERP-<-CONSTANT))
     (2 2 (:REWRITE DEFAULT-LESS-THAN-2))
     (2 2 (:REWRITE DEFAULT-LESS-THAN-1))
     (2 2 (:REWRITE CONSTANT-<-INTEGERP))
     (2 2
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (2 2
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (2 2
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (2 2
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (2 2 (:REWRITE |(< c (- x))|))
     (2 2
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (2 2
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (2 2
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (2 2
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (2 2 (:REWRITE |(< (/ x) 0)|))
     (2 2 (:REWRITE |(< (/ x) (/ y))|))
     (2 2 (:REWRITE |(< (- x) c)|))
     (2 2 (:REWRITE |(< (- x) (- y))|))
     (2 2 (:REWRITE |(< (* x y) 0)|))
     (1 1 (:REWRITE ZP-OPEN)))
(FM9001::LEN-NAT-TO-V
     (1392 9 (:REWRITE DEFAULT-FLOOR-1))
     (1353 6 (:REWRITE DEFAULT-FLOOR-RATIO))
     (332 41 (:REWRITE RATIONALP-X))
     (237 76 (:REWRITE INTEGERP-MINUS-X))
     (231 35
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (212 4 (:REWRITE CANCEL-MOD-+))
     (205 205
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (205 205
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (205 205
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (205 205
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (204 3 (:REWRITE FLOOR-ZERO . 3))
     (192 4 (:REWRITE MOD-X-Y-=-X+Y . 1))
     (173 117 (:REWRITE DEFAULT-TIMES-2))
     (171 171
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (171 171
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (171 171
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (171 171
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (159 3 (:REWRITE CANCEL-FLOOR-+))
     (140 22
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (140 22
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (140 4 (:REWRITE MOD-X-Y-=-X . 4))
     (140 4 (:REWRITE MOD-X-Y-=-X . 3))
     (136 4 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (128 4 (:REWRITE MOD-X-Y-=-X-Y . 1))
     (124 4 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (120 16 (:REWRITE ACL2-NUMBERP-X))
     (119 14 (:REWRITE |(* (- x) y)|))
     (117 117 (:REWRITE DEFAULT-TIMES-1))
     (105 3 (:REWRITE FLOOR-ZERO . 5))
     (105 3 (:REWRITE FLOOR-ZERO . 4))
     (102 3 (:REWRITE FLOOR-X-Y-=--1 . 2))
     (100 20 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (100 20 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (100 20
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (100 20
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (93 3 (:REWRITE FLOOR-X-Y-=-1 . 2))
     (88 4 (:REWRITE MOD-ZERO . 3))
     (72 4 (:REWRITE MOD-ZERO . 4))
     (70 14 (:REWRITE DEFAULT-MINUS))
     (69 69 (:REWRITE REDUCE-INTEGERP-+))
     (69 69 (:META META-INTEGERP-CORRECT))
     (66 3 (:REWRITE FLOOR-=-X/Y . 3))
     (66 3 (:REWRITE FLOOR-=-X/Y . 2))
     (64 58 (:REWRITE DEFAULT-PLUS-2))
     (63 14 (:REWRITE |(- (* c x))|))
     (58 58 (:REWRITE DEFAULT-PLUS-1))
     (55 55
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (52 12 (:REWRITE |(+ c (+ d x))|))
     (47 35
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (47 35 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (44 4 (:REWRITE |(+ y (+ x z))|))
     (41 41 (:REWRITE RATIONALP-MINUS-X))
     (40 8 (:REWRITE |(+ y x)|))
     (39 36
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (39 36
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (37 37 (:REWRITE THE-FLOOR-BELOW))
     (37 37 (:REWRITE THE-FLOOR-ABOVE))
     (37 37 (:REWRITE DEFAULT-LESS-THAN-2))
     (36 36
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (36 36
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (36 36 (:REWRITE INTEGERP-<-CONSTANT))
     (36 36 (:REWRITE CONSTANT-<-INTEGERP))
     (36 36
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (36 36
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (36 36
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (36 36
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (36 36 (:REWRITE |(< c (- x))|))
     (36 36
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (36 36
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (36 36
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (36 36
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (36 36 (:REWRITE |(< (/ x) (/ y))|))
     (36 36 (:REWRITE |(< (- x) c)|))
     (36 36 (:REWRITE |(< (- x) (- y))|))
     (35 35 (:REWRITE SIMPLIFY-SUMS-<))
     (35 35
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (27 27 (:REWRITE REDUCE-RATIONALP-+))
     (27 27 (:META META-RATIONALP-CORRECT))
     (26 26
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (26 26 (:REWRITE NORMALIZE-ADDENDS))
     (26 22 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (22 22
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (22 22 (:REWRITE |(equal c (/ x))|))
     (22 22 (:REWRITE |(equal c (- x))|))
     (22 22 (:REWRITE |(equal (/ x) c)|))
     (22 22 (:REWRITE |(equal (/ x) (/ y))|))
     (22 22 (:REWRITE |(equal (- x) c)|))
     (22 22 (:REWRITE |(equal (- x) (- y))|))
     (22 22 (:REWRITE |(< (/ x) 0)|))
     (22 22 (:REWRITE |(< (* x y) 0)|))
     (21 21
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (21 21
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (20 20 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (20 20 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (20 20
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (20 20 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (20 20
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (20 20 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (20 20 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (20 4 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (20 4 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (20 4 (:REWRITE MOD-X-Y-=-X . 2))
     (20 4
         (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (20 4 (:REWRITE MOD-CANCEL-*-CONST))
     (20 4 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (20 4
         (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (20 4
         (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (16 4 (:REWRITE |(mod x 2)| . 1))
     (15 3 (:REWRITE FLOOR-ZERO . 2))
     (15 3 (:REWRITE FLOOR-X-Y-=-1 . 3))
     (15 3 (:REWRITE FLOOR-X-Y-=--1 . 3))
     (15 3
         (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
     (15 3 (:REWRITE FLOOR-CANCEL-*-CONST))
     (15 3
         (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
     (12 12 (:REWRITE DEFAULT-MOD-2))
     (12 3 (:REWRITE |(floor x 2)| . 1))
     (9 9 (:REWRITE DEFAULT-FLOOR-2))
     (8 8 (:REWRITE |(+ 0 x)|))
     (7 7
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (7 7
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (7 7 (:REWRITE |(< 0 (/ x))|))
     (7 7 (:REWRITE |(< 0 (* x y))|))
     (6 6 (:TYPE-PRESCRIPTION ABS))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (6 5 (:REWRITE DEFAULT-CDR))
     (4 4 (:REWRITE ZP-OPEN))
     (4 4
        (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (4 4 (:REWRITE |(mod x 2)| . 2))
     (4 4 (:REWRITE |(mod x (- y))| . 3))
     (4 4 (:REWRITE |(mod x (- y))| . 2))
     (4 4 (:REWRITE |(mod x (- y))| . 1))
     (4 4
        (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (4 4
        (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (4 4 (:REWRITE |(mod (- x) y)| . 3))
     (4 4 (:REWRITE |(mod (- x) y)| . 2))
     (4 4 (:REWRITE |(mod (- x) y)| . 1))
     (4 4
        (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (4 4
        (:REWRITE |(equal (mod (+ x y) z) x)|))
     (3 3
        (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (3 3 (:REWRITE |(floor x 2)| . 2))
     (3 3 (:REWRITE |(floor x (- y))| . 2))
     (3 3 (:REWRITE |(floor x (- y))| . 1))
     (3 3
        (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
     (3 3
        (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
     (3 3 (:REWRITE |(floor (- x) y)| . 2))
     (3 3 (:REWRITE |(floor (- x) y)| . 1))
     (3 3
        (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
     (3 3
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|)))
(FM9001::TAKE-NAT-TO-V
     (3248 21 (:REWRITE DEFAULT-FLOOR-1))
     (3157 14 (:REWRITE DEFAULT-FLOOR-RATIO))
     (1009 8 (:REWRITE TAKE-OF-TOO-MANY))
     (856 106 (:REWRITE RATIONALP-X))
     (634 95
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (609 195 (:REWRITE INTEGERP-MINUS-X))
     (583 11 (:REWRITE CANCEL-MOD-+))
     (535 535
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (535 535
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (535 535
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (535 535
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (528 11 (:REWRITE MOD-X-Y-=-X+Y . 1))
     (522 16 (:DEFINITION NFIX))
     (476 7 (:REWRITE FLOOR-ZERO . 3))
     (442 298 (:REWRITE DEFAULT-TIMES-2))
     (434 434
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (434 434
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (434 434
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (434 434
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (416 9 (:REWRITE TAKE-OF-LEN-FREE))
     (385 11 (:REWRITE MOD-X-Y-=-X . 4))
     (385 11 (:REWRITE MOD-X-Y-=-X . 3))
     (375 59
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (375 59
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (374 11 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (371 7 (:REWRITE CANCEL-FLOOR-+))
     (352 11 (:REWRITE MOD-X-Y-=-X-Y . 1))
     (341 11 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (321 6 (:REWRITE |(< (if a b c) x)|))
     (313 41 (:REWRITE ACL2-NUMBERP-X))
     (306 36 (:REWRITE |(* (- x) y)|))
     (298 298 (:REWRITE DEFAULT-TIMES-1))
     (275 55 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (275 55 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (275 55
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (275 55
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (267 9 (:REWRITE |(< x (if a b c))|))
     (267 8 (:REWRITE FM9001::LEN-NAT-TO-V))
     (245 121
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (245 7 (:REWRITE FLOOR-ZERO . 5))
     (245 7 (:REWRITE FLOOR-ZERO . 4))
     (242 11 (:REWRITE MOD-ZERO . 3))
     (238 7 (:REWRITE FLOOR-X-Y-=--1 . 2))
     (217 7 (:REWRITE FLOOR-X-Y-=-1 . 2))
     (198 11 (:REWRITE MOD-ZERO . 4))
     (180 166 (:REWRITE DEFAULT-PLUS-2))
     (180 36 (:REWRITE DEFAULT-MINUS))
     (177 177 (:REWRITE REDUCE-INTEGERP-+))
     (177 177 (:META META-INTEGERP-CORRECT))
     (166 166 (:REWRITE DEFAULT-PLUS-1))
     (164 136 (:REWRITE DEFAULT-LESS-THAN-1))
     (163 38 (:REWRITE |(+ c (+ d x))|))
     (162 36 (:REWRITE |(- (* c x))|))
     (154 7 (:REWRITE FLOOR-=-X/Y . 3))
     (154 7 (:REWRITE FLOOR-=-X/Y . 2))
     (146 114
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (146 114
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (140 140
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (137 137 (:REWRITE THE-FLOOR-BELOW))
     (137 137 (:REWRITE THE-FLOOR-ABOVE))
     (128 121
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (128 121
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (126 9 (:DEFINITION LEN))
     (126 3 (:REWRITE |(< (+ (- c) x) y)|))
     (121 11 (:REWRITE |(+ y (+ x z))|))
     (117 117 (:TYPE-PRESCRIPTION LEN))
     (117 114 (:REWRITE SIMPLIFY-SUMS-<))
     (114 114
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (114 114 (:REWRITE INTEGERP-<-CONSTANT))
     (114 114 (:REWRITE CONSTANT-<-INTEGERP))
     (114 114
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (114 114
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (114 114
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (114 114
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (114 114 (:REWRITE |(< c (- x))|))
     (114 114
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (114 114
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (114 114
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (114 114
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (114 114 (:REWRITE |(< (/ x) (/ y))|))
     (114 114 (:REWRITE |(< (- x) c)|))
     (114 114 (:REWRITE |(< (- x) (- y))|))
     (110 22 (:REWRITE |(+ y x)|))
     (106 106 (:REWRITE RATIONALP-MINUS-X))
     (96 96 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (95 95
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (84 6 (:REWRITE |(equal (+ (- c) x) y)|))
     (70 70 (:REWRITE REDUCE-RATIONALP-+))
     (70 70 (:META META-RATIONALP-CORRECT))
     (68 68
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (68 68 (:REWRITE NORMALIZE-ADDENDS))
     (67 59 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (59 59
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (59 59 (:REWRITE |(equal c (/ x))|))
     (59 59 (:REWRITE |(equal c (- x))|))
     (59 59 (:REWRITE |(equal (/ x) c)|))
     (59 59 (:REWRITE |(equal (/ x) (/ y))|))
     (59 59 (:REWRITE |(equal (- x) c)|))
     (59 59 (:REWRITE |(equal (- x) (- y))|))
     (59 59 (:REWRITE |(< (* x y) 0)|))
     (55 55 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (55 55 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (55 55
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (55 55 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (55 55
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (55 55 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (55 55 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (55 55
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (55 55
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (55 55 (:REWRITE |(< (/ x) 0)|))
     (55 11 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (55 11 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (55 11 (:REWRITE MOD-X-Y-=-X . 2))
     (55 11
         (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (55 11 (:REWRITE MOD-CANCEL-*-CONST))
     (55 11 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (55 11
         (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (55 11
         (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (44 11 (:REWRITE |(mod x 2)| . 1))
     (35 7 (:REWRITE FLOOR-ZERO . 2))
     (35 7 (:REWRITE FLOOR-X-Y-=-1 . 3))
     (35 7 (:REWRITE FLOOR-X-Y-=--1 . 3))
     (35 7
         (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
     (35 7 (:REWRITE FLOOR-CANCEL-*-CONST))
     (35 7
         (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
     (33 33 (:REWRITE DEFAULT-MOD-2))
     (32 8 (:REWRITE TAKE-WHEN-ATOM))
     (28 7 (:REWRITE |(floor x 2)| . 1))
     (27 27 (:REWRITE |(+ 0 x)|))
     (26 26
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (26 26
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (26 26 (:REWRITE |(< 0 (/ x))|))
     (26 26 (:REWRITE |(< 0 (* x y))|))
     (22 12 (:REWRITE DEFAULT-CDR))
     (21 21 (:REWRITE DEFAULT-FLOOR-2))
     (14 14 (:TYPE-PRESCRIPTION ABS))
     (14 14 (:REWRITE ZP-OPEN))
     (14 14
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (12 3 (:REWRITE DEFAULT-CAR))
     (11 11
         (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (11 11 (:REWRITE |(mod x 2)| . 2))
     (11 11 (:REWRITE |(mod x (- y))| . 3))
     (11 11 (:REWRITE |(mod x (- y))| . 2))
     (11 11 (:REWRITE |(mod x (- y))| . 1))
     (11 11
         (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (11 11
         (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (11 11 (:REWRITE |(mod (- x) y)| . 3))
     (11 11 (:REWRITE |(mod (- x) y)| . 2))
     (11 11 (:REWRITE |(mod (- x) y)| . 1))
     (11 11
         (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (11 11
         (:REWRITE |(equal (mod (+ x y) z) x)|))
     (8 8 (:TYPE-PRESCRIPTION NFIX))
     (7 7
        (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (7 7 (:REWRITE |(floor x 2)| . 2))
     (7 7 (:REWRITE |(floor x (- y))| . 2))
     (7 7 (:REWRITE |(floor x (- y))| . 1))
     (7 7
        (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
     (7 7
        (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
     (7 7 (:REWRITE |(floor (- x) y)| . 2))
     (7 7 (:REWRITE |(floor (- x) y)| . 1))
     (7 7
        (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
     (7 7 (:REWRITE |(< (+ c/d x) y)|))
     (7 7
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (3 3 (:REWRITE |(< y (+ (- c) x))|))
     (3 3 (:REWRITE |(< x (+ c/d y))|))
     (1 1 (:REWRITE CDR-CONS)))
(FM9001::NTHCDR-OF-LEN-L
     (152 4 (:REWRITE ZP-OPEN))
     (24 17 (:REWRITE DEFAULT-PLUS-2))
     (24 8 (:REWRITE FM9001::BVP-IS-TRUE-LISTP))
     (19 17 (:REWRITE DEFAULT-PLUS-1))
     (16 16 (:TYPE-PRESCRIPTION FM9001::BVP))
     (12 12 (:REWRITE DEFAULT-CDR))
     (9 9
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (9 9 (:REWRITE NORMALIZE-ADDENDS))
     (8 4
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (8 4 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (8 4 (:REWRITE DEFAULT-LESS-THAN-2))
     (4 4 (:REWRITE THE-FLOOR-BELOW))
     (4 4 (:REWRITE THE-FLOOR-ABOVE))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (4 4 (:REWRITE SIMPLIFY-SUMS-<))
     (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (4 4 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (4 4
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (4 4
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (4 4 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (4 4 (:REWRITE INTEGERP-<-CONSTANT))
     (4 4 (:REWRITE DEFAULT-LESS-THAN-1))
     (4 4 (:REWRITE CONSTANT-<-INTEGERP))
     (4 4
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (4 4
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (4 4
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (4 4
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (4 4 (:REWRITE |(< c (- x))|))
     (4 4 (:REWRITE |(< 0 (/ x))|))
     (4 4 (:REWRITE |(< 0 (* x y))|))
     (4 4
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (4 4
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (4 4
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (4 4
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (4 4 (:REWRITE |(< (/ x) (/ y))|))
     (4 4 (:REWRITE |(< (- x) c)|))
     (4 4 (:REWRITE |(< (- x) (- y))|)))
(FM9001::NTHCDR-NAT-TO-V-0-HACK
     (1843 183 (:REWRITE |(equal (+ (- c) x) y)|))
     (1637 330
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (1522 1159 (:REWRITE DEFAULT-PLUS-2))
     (1421 233 (:REWRITE |(< c (- x))|))
     (1181 1159 (:REWRITE DEFAULT-PLUS-1))
     (626 626
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (449 383 (:REWRITE DEFAULT-CDR))
     (388 221 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (361 221
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (361 221
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (330 330
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (265 265 (:REWRITE THE-FLOOR-BELOW))
     (265 265 (:REWRITE THE-FLOOR-ABOVE))
     (265 265
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (265 265
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (265 265 (:REWRITE DEFAULT-LESS-THAN-2))
     (265 265 (:REWRITE DEFAULT-LESS-THAN-1))
     (233 233
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (233 233
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (233 233
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (233 233
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (233 233
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (233 233
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (233 233
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (233 233
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (233 233 (:REWRITE |(< (/ x) (/ y))|))
     (233 233 (:REWRITE |(< (- x) (- y))|))
     (225 75 (:REWRITE FM9001::BVP-IS-TRUE-LISTP))
     (221 221 (:REWRITE INTEGERP-<-CONSTANT))
     (221 221
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (221 221 (:REWRITE CONSTANT-<-INTEGERP))
     (221 221 (:REWRITE |(equal c (/ x))|))
     (221 221 (:REWRITE |(equal c (- x))|))
     (221 221 (:REWRITE |(equal (/ x) c)|))
     (221 221 (:REWRITE |(equal (/ x) (/ y))|))
     (221 221 (:REWRITE |(equal (- x) c)|))
     (221 221 (:REWRITE |(equal (- x) (- y))|))
     (221 221 (:REWRITE |(< (- x) c)|))
     (150 150 (:TYPE-PRESCRIPTION FM9001::BVP))
     (88 88 (:REWRITE |(< (* x y) 0)|))
     (73 73 (:REWRITE |(< 0 (* x y))|))
     (71 71 (:REWRITE |(< y (+ (- c) x))|))
     (71 71 (:REWRITE |(< x (+ c/d y))|))
     (71 71 (:REWRITE |(< 0 (/ x))|))
     (66 66 (:REWRITE DEFAULT-MINUS))
     (60 12 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
     (59 59 (:REWRITE |(< (/ x) 0)|))
     (54 54
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (54 54
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (54 54 (:REWRITE |(< (+ c/d x) y)|))
     (50 50 (:REWRITE FOLD-CONSTS-IN-+))
     (38 38
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (38 38
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (35 35 (:REWRITE REDUCE-INTEGERP-+))
     (35 35 (:REWRITE INTEGERP-MINUS-X))
     (35 35 (:REWRITE DEFAULT-CAR))
     (35 35 (:META META-INTEGERP-CORRECT))
     (22 22 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (12 12 (:REWRITE |(- (- x))|))
     (8 8 (:REWRITE DEFAULT-TIMES-2))
     (8 8 (:REWRITE DEFAULT-TIMES-1))
     (4 4 (:REWRITE |(equal x (if a b c))|))
     (2 2
        (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (2 2
        (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (2 2 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(FM9001::BVP-NAT-TO-V
     (928 6 (:REWRITE DEFAULT-FLOOR-1))
     (902 4 (:REWRITE DEFAULT-FLOOR-RATIO))
     (232 28 (:REWRITE RATIONALP-X))
     (168 21
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (165 50 (:REWRITE INTEGERP-MINUS-X))
     (159 3 (:REWRITE CANCEL-MOD-+))
     (158 158
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (158 158
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (158 158
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (158 158
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (144 3 (:REWRITE MOD-X-Y-=-X+Y . 1))
     (136 2 (:REWRITE FLOOR-ZERO . 3))
     (123 83 (:REWRITE DEFAULT-TIMES-2))
     (121 121
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (121 121
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (121 121
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (121 121
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (106 2 (:REWRITE CANCEL-FLOOR-+))
     (105 3 (:REWRITE MOD-X-Y-=-X . 4))
     (105 3 (:REWRITE MOD-X-Y-=-X . 3))
     (102 3 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (96 12
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (96 12
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (96 3 (:REWRITE MOD-X-Y-=-X-Y . 1))
     (93 3 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (85 10 (:REWRITE |(* (- x) y)|))
     (83 83 (:REWRITE DEFAULT-TIMES-1))
     (80 16 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (80 16 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (80 16
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (80 16
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (74 10 (:REWRITE ACL2-NUMBERP-X))
     (70 2 (:REWRITE FLOOR-ZERO . 5))
     (70 2 (:REWRITE FLOOR-ZERO . 4))
     (68 2 (:REWRITE FLOOR-X-Y-=--1 . 2))
     (66 3 (:REWRITE MOD-ZERO . 3))
     (62 2 (:REWRITE FLOOR-X-Y-=-1 . 2))
     (54 3 (:REWRITE MOD-ZERO . 4))
     (50 10 (:REWRITE DEFAULT-MINUS))
     (45 45 (:REWRITE REDUCE-INTEGERP-+))
     (45 45 (:META META-INTEGERP-CORRECT))
     (45 10 (:REWRITE |(- (* c x))|))
     (44 2 (:REWRITE FLOOR-=-X/Y . 3))
     (44 2 (:REWRITE FLOOR-=-X/Y . 2))
     (39 39
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (39 9 (:REWRITE |(+ c (+ d x))|))
     (38 38 (:REWRITE DEFAULT-PLUS-2))
     (38 38 (:REWRITE DEFAULT-PLUS-1))
     (33 3 (:REWRITE |(+ y (+ x z))|))
     (30 22
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (30 22 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (30 22 (:REWRITE DEFAULT-LESS-THAN-1))
     (30 6 (:REWRITE |(+ y x)|))
     (28 28 (:REWRITE RATIONALP-MINUS-X))
     (24 22
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (24 22
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (22 22 (:REWRITE THE-FLOOR-BELOW))
     (22 22 (:REWRITE THE-FLOOR-ABOVE))
     (22 22 (:REWRITE SIMPLIFY-SUMS-<))
     (22 22
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (22 22
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (22 22 (:REWRITE INTEGERP-<-CONSTANT))
     (22 22 (:REWRITE DEFAULT-LESS-THAN-2))
     (22 22 (:REWRITE CONSTANT-<-INTEGERP))
     (22 22
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (22 22
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (22 22
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (22 22
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (22 22 (:REWRITE |(< c (- x))|))
     (22 22
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (22 22
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (22 22
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (22 22
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (22 22 (:REWRITE |(< (/ x) (/ y))|))
     (22 22 (:REWRITE |(< (- x) c)|))
     (22 22 (:REWRITE |(< (- x) (- y))|))
     (21 21
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (18 18 (:REWRITE REDUCE-RATIONALP-+))
     (18 18 (:META META-RATIONALP-CORRECT))
     (17 17 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (16 16 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (16 16 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (16 16
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (16 16 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (16 16
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (16 16 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (16 16 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (15 3 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (15 3 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (15 3 (:REWRITE MOD-X-Y-=-X . 2))
     (15 3
         (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (15 3 (:REWRITE MOD-CANCEL-*-CONST))
     (15 3 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (15 3
         (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (15 3
         (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (14 14
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (14 14 (:REWRITE NORMALIZE-ADDENDS))
     (12 12
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (12 12
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (12 12 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (12 12
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (12 12 (:REWRITE |(equal c (/ x))|))
     (12 12 (:REWRITE |(equal c (- x))|))
     (12 12 (:REWRITE |(equal (/ x) c)|))
     (12 12 (:REWRITE |(equal (/ x) (/ y))|))
     (12 12 (:REWRITE |(equal (- x) c)|))
     (12 12 (:REWRITE |(equal (- x) (- y))|))
     (12 12 (:REWRITE |(< (/ x) 0)|))
     (12 12 (:REWRITE |(< (* x y) 0)|))
     (12 3 (:REWRITE |(mod x 2)| . 1))
     (10 2 (:REWRITE FLOOR-ZERO . 2))
     (10 2 (:REWRITE FLOOR-X-Y-=-1 . 3))
     (10 2 (:REWRITE FLOOR-X-Y-=--1 . 3))
     (10 2
         (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
     (10 2 (:REWRITE FLOOR-CANCEL-*-CONST))
     (10 2
         (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
     (9 9 (:REWRITE DEFAULT-MOD-2))
     (8 2 (:REWRITE |(floor x 2)| . 1))
     (6 6 (:REWRITE DEFAULT-FLOOR-2))
     (6 6 (:REWRITE |(+ 0 x)|))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (5 5 (:REWRITE |(< 0 (/ x))|))
     (5 5 (:REWRITE |(< 0 (* x y))|))
     (5 4 (:REWRITE DEFAULT-CDR))
     (5 4 (:REWRITE DEFAULT-CAR))
     (4 4 (:TYPE-PRESCRIPTION ABS))
     (4 4 (:REWRITE ZP-OPEN))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (3 3
        (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (3 3 (:REWRITE |(mod x 2)| . 2))
     (3 3 (:REWRITE |(mod x (- y))| . 3))
     (3 3 (:REWRITE |(mod x (- y))| . 2))
     (3 3 (:REWRITE |(mod x (- y))| . 1))
     (3 3
        (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (3 3
        (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (3 3 (:REWRITE |(mod (- x) y)| . 3))
     (3 3 (:REWRITE |(mod (- x) y)| . 2))
     (3 3 (:REWRITE |(mod (- x) y)| . 1))
     (3 3
        (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (3 3
        (:REWRITE |(equal (mod (+ x y) z) x)|))
     (2 2
        (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (2 2 (:REWRITE |(floor x 2)| . 2))
     (2 2 (:REWRITE |(floor x (- y))| . 2))
     (2 2 (:REWRITE |(floor x (- y))| . 1))
     (2 2
        (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
     (2 2
        (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
     (2 2 (:REWRITE |(floor (- x) y)| . 2))
     (2 2 (:REWRITE |(floor (- x) y)| . 1))
     (2 2
        (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
     (2 2
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|)))
(FM9001::CAR-NAT-TO-V-0-IS-NIL
     (14 4 (:REWRITE DEFAULT-CAR))
     (4 4 (:REWRITE ZP-OPEN))
     (3 3
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (3 3 (:REWRITE NORMALIZE-ADDENDS))
     (3 3 (:REWRITE DEFAULT-PLUS-2))
     (3 3 (:REWRITE DEFAULT-PLUS-1)))
(FM9001::ANY-OF-NAT-TO-V-0-IS-NIL-INDUCT)
(FM9001::ANY-OF-NAT-TO-V-0-IS-NIL
     (147 7 (:REWRITE ZP-OPEN))
     (33 1 (:REWRITE |(< x (if a b c))|))
     (20 4 (:REWRITE |(+ c (+ d x))|))
     (18 2 (:REWRITE ACL2-NUMBERP-X))
     (16 16 (:REWRITE DEFAULT-PLUS-1))
     (11 11
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (11 11 (:REWRITE NORMALIZE-ADDENDS))
     (8 2 (:REWRITE RATIONALP-X))
     (8 1 (:REWRITE |(+ x (if a b c))|))
     (5 5 (:REWRITE THE-FLOOR-BELOW))
     (5 5 (:REWRITE THE-FLOOR-ABOVE))
     (5 5 (:REWRITE DEFAULT-LESS-THAN-2))
     (5 5 (:REWRITE DEFAULT-LESS-THAN-1))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (4 4 (:REWRITE SIMPLIFY-SUMS-<))
     (4 4
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (4 4 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (4 4
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (4 4
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (4 4 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (4 4 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (4 4 (:REWRITE INTEGERP-<-CONSTANT))
     (4 4 (:REWRITE CONSTANT-<-INTEGERP))
     (4 4 (:REWRITE |(< y (+ (- c) x))|))
     (4 4 (:REWRITE |(< x (+ c/d y))|))
     (4 4
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (4 4
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (4 4
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (4 4
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (4 4 (:REWRITE |(< c (- x))|))
     (4 4 (:REWRITE |(< 0 (/ x))|))
     (4 4 (:REWRITE |(< 0 (* x y))|))
     (4 4
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (4 4
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (4 4
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (4 4
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (4 4 (:REWRITE |(< (/ x) (/ y))|))
     (4 4 (:REWRITE |(< (- x) c)|))
     (4 4 (:REWRITE |(< (- x) (- y))|))
     (4 2 (:REWRITE DEFAULT-CAR))
     (3 3
        (:TYPE-PRESCRIPTION FM9001::ANY-OF-NAT-TO-V-0-IS-NIL-INDUCT))
     (3 3 (:REWRITE REDUCE-INTEGERP-+))
     (3 3 (:REWRITE INTEGERP-MINUS-X))
     (3 3 (:META META-INTEGERP-CORRECT))
     (3 2 (:REWRITE DEFAULT-CDR))
     (2 2 (:REWRITE REDUCE-RATIONALP-+))
     (2 2 (:REWRITE REDUCE-RATIONALP-*))
     (2 2 (:REWRITE RATIONALP-MINUS-X))
     (2 2 (:META META-RATIONALP-CORRECT))
     (1 1
        (:REWRITE FM9001::CAR-NAT-TO-V-0-IS-NIL)))
(FM9001::V-NTH)
(FM9001::UPDATE-V-NTH)
(FM9001::V-NZP)
(FM9001::V-ZP)
(FM9001::BOOLEANP-V-NZP (16 16 (:REWRITE DEFAULT-CAR))
                        (4 4 (:REWRITE DEFAULT-CDR)))
(FM9001::V-NZP-AS-OR-CROCK
     (1098 16 (:REWRITE |(< (if a b c) x)|))
     (1013 51 (:REWRITE ZP-OPEN))
     (1000 106
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (540 14 (:REWRITE TAKE-OF-LEN-FREE))
     (436 28 (:REWRITE FM9001::NTHCDR-OF-LEN-L))
     (341 9 (:REWRITE REPEAT-WHEN-ZP))
     (280 4 (:REWRITE CAR-OF-TAKE))
     (264 264 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (257 31 (:DEFINITION TRUE-LISTP))
     (252 6 (:REWRITE |(< (+ (- c) x) y)|))
     (250 125
          (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
     (228 10 (:REWRITE |(< x (if a b c))|))
     (212 36 (:REWRITE ACL2-NUMBERP-X))
     (202 101
          (:TYPE-PRESCRIPTION FM9001::BVP-NTHCDR))
     (188 188 (:REWRITE DEFAULT-PLUS-1))
     (186 132 (:REWRITE DEFAULT-LESS-THAN-2))
     (183 61 (:REWRITE FM9001::BVP-IS-TRUE-LISTP))
     (183 32 (:REWRITE |(+ c (+ d x))|))
     (171 15 (:REWRITE |(equal (+ (- c) x) y)|))
     (159 53 (:REWRITE DEFAULT-CAR))
     (132 132 (:REWRITE THE-FLOOR-BELOW))
     (132 132 (:REWRITE THE-FLOOR-ABOVE))
     (132 132 (:REWRITE DEFAULT-LESS-THAN-1))
     (131 15 (:REWRITE CONSP-OF-REPEAT))
     (106 106
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (106 106
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (105 7 (:REWRITE |(+ y (+ x z))|))
     (103 76 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (101 76
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (95 4 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (94 94
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (94 94 (:REWRITE NORMALIZE-ADDENDS))
     (90 6 (:REWRITE |(+ (+ x y) z)|))
     (88 76 (:REWRITE SIMPLIFY-SUMS-<))
     (88 22 (:REWRITE RATIONALP-X))
     (77 77
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (77 77 (:REWRITE INTEGERP-<-CONSTANT))
     (77 77 (:REWRITE CONSTANT-<-INTEGERP))
     (77 77
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (77 77
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (77 77
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (77 77
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (77 77 (:REWRITE |(< c (- x))|))
     (77 77
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (77 77
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (77 77
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (77 77
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (77 77 (:REWRITE |(< (/ x) (/ y))|))
     (77 77 (:REWRITE |(< (- x) c)|))
     (77 77 (:REWRITE |(< (- x) (- y))|))
     (75 14
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (38 21
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (37 37 (:REWRITE |(< 0 (* x y))|))
     (36 36 (:REWRITE REDUCE-INTEGERP-+))
     (36 36 (:REWRITE INTEGERP-MINUS-X))
     (36 36 (:META META-INTEGERP-CORRECT))
     (35 35 (:REWRITE |(< x (+ c/d y))|))
     (27 14
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (26 14 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (24 24
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (24 24
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (24 24 (:REWRITE |(< 0 (/ x))|))
     (22 22 (:REWRITE REDUCE-RATIONALP-+))
     (22 22 (:REWRITE REDUCE-RATIONALP-*))
     (22 22 (:REWRITE RATIONALP-MINUS-X))
     (22 22 (:REWRITE |(< y (+ (- c) x))|))
     (22 22 (:REWRITE |(< (* x y) 0)|))
     (22 22 (:META META-RATIONALP-CORRECT))
     (21 21
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (16 16 (:REWRITE |(< (+ c/d x) y)|))
     (14 14
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (14 14 (:REWRITE |(equal c (/ x))|))
     (14 14 (:REWRITE |(equal c (- x))|))
     (14 14 (:REWRITE |(equal (/ x) c)|))
     (14 14 (:REWRITE |(equal (/ x) (/ y))|))
     (14 14 (:REWRITE |(equal (- x) c)|))
     (14 14 (:REWRITE |(equal (- x) (- y))|))
     (14 14 (:REWRITE |(< (/ x) 0)|))
     (13 13 (:REWRITE TAKE-WHEN-ATOM))
     (13 13
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (13 13
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (8 2 (:REWRITE |(+ x (if a b c))|))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(FM9001::NOT-V-NZP-TAKE-NTHCDR
     (1187 17 (:REWRITE |(< (if a b c) x)|))
     (926 94
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (628 16 (:REWRITE TAKE-OF-LEN-FREE))
     (569 27 (:REWRITE ZP-OPEN))
     (439 27 (:REWRITE FM9001::NTHCDR-OF-LEN-L))
     (424 212
          (:TYPE-PRESCRIPTION FM9001::BVP-NTHCDR))
     (336 8 (:REWRITE |(< (+ (- c) x) y)|))
     (308 10 (:REWRITE CONSP-OF-TAKE))
     (280 4 (:REWRITE CAR-OF-TAKE))
     (271 33 (:DEFINITION TRUE-LISTP))
     (227 19 (:REWRITE |(equal (+ (- c) x) y)|))
     (189 63 (:REWRITE FM9001::BVP-IS-TRUE-LISTP))
     (185 33 (:REWRITE ACL2-NUMBERP-X))
     (178 118 (:REWRITE DEFAULT-LESS-THAN-2))
     (169 169 (:REWRITE DEFAULT-PLUS-1))
     (165 28 (:REWRITE |(+ c (+ d x))|))
     (159 7 (:REWRITE |(< x (if a b c))|))
     (144 50 (:REWRITE DEFAULT-CAR))
     (118 118 (:REWRITE THE-FLOOR-BELOW))
     (118 118 (:REWRITE THE-FLOOR-ABOVE))
     (118 118 (:REWRITE DEFAULT-LESS-THAN-1))
     (114 114
          (:REWRITE FM9001::V-NZP-AS-OR-CROCK))
     (105 7 (:REWRITE |(+ y (+ x z))|))
     (95 65 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (95 4 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (94 94
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (94 94
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (92 65
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (90 90
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (90 90 (:REWRITE NORMALIZE-ADDENDS))
     (79 65 (:REWRITE SIMPLIFY-SUMS-<))
     (79 16
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (76 19 (:REWRITE RATIONALP-X))
     (65 65 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (65 65
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (65 65 (:REWRITE INTEGERP-<-CONSTANT))
     (65 65 (:REWRITE CONSTANT-<-INTEGERP))
     (65 65
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (65 65
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (65 65
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (65 65
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (65 65 (:REWRITE |(< c (- x))|))
     (65 65
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (65 65
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (65 65
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (65 65
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (65 65 (:REWRITE |(< (/ x) (/ y))|))
     (65 65 (:REWRITE |(< (- x) c)|))
     (65 65 (:REWRITE |(< (- x) (- y))|))
     (46 3 (:REWRITE CONSP-OF-REPEAT))
     (45 3 (:REWRITE |(+ (+ x y) z)|))
     (44 1 (:REWRITE REPEAT-WHEN-ZP))
     (42 25
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (31 16
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (30 16 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (29 29 (:REWRITE REDUCE-INTEGERP-+))
     (29 29 (:REWRITE INTEGERP-MINUS-X))
     (29 29 (:REWRITE |(< x (+ c/d y))|))
     (29 29 (:REWRITE |(< 0 (* x y))|))
     (29 29 (:META META-INTEGERP-CORRECT))
     (25 25
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (20 20
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (20 20
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (20 20 (:REWRITE |(< y (+ (- c) x))|))
     (20 20 (:REWRITE |(< 0 (/ x))|))
     (20 20 (:REWRITE |(< (+ c/d x) y)|))
     (20 20 (:REWRITE |(< (* x y) 0)|))
     (19 19 (:REWRITE REDUCE-RATIONALP-+))
     (19 19 (:REWRITE REDUCE-RATIONALP-*))
     (19 19 (:REWRITE RATIONALP-MINUS-X))
     (19 19 (:META META-RATIONALP-CORRECT))
     (16 16
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (16 16 (:REWRITE |(equal c (/ x))|))
     (16 16 (:REWRITE |(equal c (- x))|))
     (16 16 (:REWRITE |(equal (/ x) c)|))
     (16 16 (:REWRITE |(equal (/ x) (/ y))|))
     (16 16 (:REWRITE |(equal (- x) c)|))
     (16 16 (:REWRITE |(equal (- x) (- y))|))
     (15 15 (:REWRITE TAKE-WHEN-ATOM))
     (10 10
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (10 10
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (10 10 (:REWRITE |(< (/ x) 0)|))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(FM9001::V-ZP-AS-AND-CROCK
     (270 2 (:REWRITE TAKE-OF-TOO-MANY))
     (157 1 (:DEFINITION TAKE))
     (114 2 (:REWRITE |(< (if a b c) x)|))
     (107 3 (:DEFINITION NFIX))
     (80 2 (:REWRITE TAKE-OF-LEN-FREE))
     (64 64 (:TYPE-PRESCRIPTION LEN))
     (56 2 (:DEFINITION FM9001::V-NZP))
     (42 1 (:REWRITE |(< (+ (- c) x) y)|))
     (40 9 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (34 17
         (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
     (34 1 (:REWRITE CAR-OF-TAKE))
     (30 15
         (:TYPE-PRESCRIPTION FM9001::BVP-TAKE))
     (30 15
         (:TYPE-PRESCRIPTION FM9001::BVP-NTHCDR))
     (28 4 (:DEFINITION LEN))
     (28 2 (:REWRITE FM9001::NTHCDR-OF-LEN-L))
     (28 2 (:REWRITE |(equal (+ (- c) x) y)|))
     (27 27 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (24 1 (:DEFINITION NTHCDR))
     (18 11 (:REWRITE DEFAULT-LESS-THAN-2))
     (17 11 (:REWRITE DEFAULT-PLUS-2))
     (16 2 (:DEFINITION TRUE-LISTP))
     (13 10 (:REWRITE DEFAULT-CDR))
     (12 4 (:REWRITE FM9001::BVP-IS-TRUE-LISTP))
     (12 2
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (11 11 (:REWRITE THE-FLOOR-BELOW))
     (11 11 (:REWRITE THE-FLOOR-ABOVE))
     (11 11 (:REWRITE DEFAULT-PLUS-1))
     (11 11 (:REWRITE DEFAULT-LESS-THAN-1))
     (11 7
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (11 7 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (11 3 (:REWRITE ACL2-NUMBERP-X))
     (9 9
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (9 9
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (9 7 (:REWRITE SIMPLIFY-SUMS-<))
     (8 8 (:REWRITE FM9001::V-NZP-AS-OR-CROCK))
     (8 8
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (8 8 (:REWRITE NORMALIZE-ADDENDS))
     (7 7 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (7 7 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (7 7 (:REWRITE INTEGERP-<-CONSTANT))
     (7 7 (:REWRITE CONSTANT-<-INTEGERP))
     (7 7
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (7 7
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (7 7
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (7 7
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (7 7 (:REWRITE |(< c (- x))|))
     (7 7
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (7 7
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (7 7
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (7 7
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (7 7 (:REWRITE |(< (/ x) (/ y))|))
     (7 7 (:REWRITE |(< (- x) c)|))
     (7 7 (:REWRITE |(< (- x) (- y))|))
     (5 1 (:REWRITE |(+ y x)|))
     (4 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (4 2
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (4 2 (:REWRITE CONSP-OF-TAKE))
     (4 1 (:REWRITE RATIONALP-X))
     (4 1 (:REWRITE |(+ c (+ d x))|))
     (3 3 (:TYPE-PRESCRIPTION NFIX))
     (3 3 (:REWRITE ZP-OPEN))
     (3 3
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (3 3
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (3 3 (:REWRITE DEFAULT-CAR))
     (3 3 (:REWRITE |(< (* x y) 0)|))
     (2 2 (:REWRITE TAKE-WHEN-ATOM))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (2 2 (:REWRITE REDUCE-INTEGERP-+))
     (2 2 (:REWRITE INTEGERP-MINUS-X))
     (2 2
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (2 2 (:REWRITE |(equal c (/ x))|))
     (2 2 (:REWRITE |(equal c (- x))|))
     (2 2 (:REWRITE |(equal (/ x) c)|))
     (2 2 (:REWRITE |(equal (/ x) (/ y))|))
     (2 2 (:REWRITE |(equal (- x) c)|))
     (2 2 (:REWRITE |(equal (- x) (- y))|))
     (2 2 (:REWRITE |(< 0 (/ x))|))
     (2 2 (:REWRITE |(< 0 (* x y))|))
     (2 2 (:REWRITE |(< (/ x) 0)|))
     (2 2 (:REWRITE |(< (+ c/d x) y)|))
     (2 2 (:META META-INTEGERP-CORRECT))
     (1 1 (:REWRITE REDUCE-RATIONALP-+))
     (1 1 (:REWRITE REDUCE-RATIONALP-*))
     (1 1 (:REWRITE RATIONALP-MINUS-X))
     (1 1 (:REWRITE |(< y (+ (- c) x))|))
     (1 1 (:REWRITE |(< x (+ c/d y))|))
     (1 1 (:REWRITE |(+ 0 x)|))
     (1 1 (:META META-RATIONALP-CORRECT)))
(FM9001::V-ZP-V-XOR-X-X (16 16 (:REWRITE FM9001::V-NZP-AS-OR-CROCK))
                        (11 10 (:REWRITE DEFAULT-CAR))
                        (9 8 (:REWRITE DEFAULT-CDR))
                        (8 8
                           (:REWRITE FM9001::NOT-V-NZP-TAKE-NTHCDR)))
(FM9001::V-NZP-V-XOR=NOT-EQUAL
     (146 21
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (134 131 (:REWRITE DEFAULT-CDR))
     (113 107 (:REWRITE DEFAULT-CAR))
     (110 22 (:REWRITE ACL2-NUMBERP-X))
     (73 38 (:REWRITE DEFAULT-PLUS-2))
     (58 21
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (44 8 (:REWRITE RATIONALP-X))
     (39 21 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (38 38
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (38 38 (:REWRITE NORMALIZE-ADDENDS))
     (38 38 (:REWRITE DEFAULT-PLUS-1))
     (36 36 (:REWRITE FM9001::V-NZP-AS-OR-CROCK))
     (30 30
         (:REWRITE FM9001::NOT-V-NZP-TAKE-NTHCDR))
     (21 21
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (21 21
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (21 21
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (21 21 (:REWRITE |(equal c (/ x))|))
     (21 21 (:REWRITE |(equal c (- x))|))
     (21 21 (:REWRITE |(equal (/ x) c)|))
     (21 21 (:REWRITE |(equal (/ x) (/ y))|))
     (21 21 (:REWRITE |(equal (- x) c)|))
     (21 21 (:REWRITE |(equal (- x) (- y))|))
     (8 8 (:REWRITE REDUCE-RATIONALP-+))
     (8 8 (:REWRITE REDUCE-RATIONALP-*))
     (8 8 (:REWRITE REDUCE-INTEGERP-+))
     (8 8 (:REWRITE RATIONALP-MINUS-X))
     (8 8 (:REWRITE INTEGERP-MINUS-X))
     (8 8 (:META META-RATIONALP-CORRECT))
     (8 8 (:META META-INTEGERP-CORRECT))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (2 2 (:REWRITE |(equal (+ (- c) x) y)|)))
(FM9001::V-ZP-MAKE-LIST
     (252 15 (:REWRITE ZP-OPEN))
     (104 11
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (85 12 (:REWRITE CONSP-OF-REPEAT))
     (20 20 (:REWRITE FM9001::V-NZP-AS-OR-CROCK))
     (18 5 (:REWRITE DEFAULT-CDR))
     (18 5 (:REWRITE DEFAULT-CAR))
     (12 3 (:REWRITE |(+ c (+ d x))|))
     (11 11 (:REWRITE THE-FLOOR-BELOW))
     (11 11 (:REWRITE THE-FLOOR-ABOVE))
     (11 11
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (11 11
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (11 11 (:REWRITE DEFAULT-LESS-THAN-2))
     (11 11 (:REWRITE DEFAULT-LESS-THAN-1))
     (10 10
         (:REWRITE FM9001::NOT-V-NZP-TAKE-NTHCDR))
     (9 9 (:REWRITE DEFAULT-PLUS-2))
     (9 9 (:REWRITE DEFAULT-PLUS-1))
     (8 8 (:REWRITE SIMPLIFY-SUMS-<))
     (8 8
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (8 8 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (8 8 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (8 8 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (8 8 (:REWRITE INTEGERP-<-CONSTANT))
     (8 8 (:REWRITE CONSTANT-<-INTEGERP))
     (8 8
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (8 8
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (8 8
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (8 8
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (8 8 (:REWRITE |(< c (- x))|))
     (8 8
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (8 8
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (8 8
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (8 8
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (8 8 (:REWRITE |(< (/ x) (/ y))|))
     (8 8 (:REWRITE |(< (- x) c)|))
     (8 8 (:REWRITE |(< (- x) (- y))|))
     (5 5 (:REWRITE |(< x (+ c/d y))|))
     (5 5 (:REWRITE |(< 0 (* x y))|))
     (3 3
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (3 3 (:REWRITE NORMALIZE-ADDENDS))
     (3 3 (:REWRITE |(+ 0 x)|))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (2 2 (:REWRITE |(< y (+ (- c) x))|))
     (2 2 (:REWRITE |(< 0 (/ x))|)))
(FM9001::V-NEGP)
(FM9001::BOOLEANP-V-NEGP (11 11 (:REWRITE DEFAULT-CDR))
                         (8 8 (:REWRITE DEFAULT-CAR)))
(FM9001::V-NEGP-AS-NTH
     (380 27
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (308 48 (:REWRITE ACL2-NUMBERP-X))
     (130 16 (:REWRITE RATIONALP-X))
     (120 27
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (109 27 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (71 71 (:REWRITE DEFAULT-CDR))
     (70 40 (:REWRITE DEFAULT-PLUS-2))
     (40 40 (:REWRITE DEFAULT-PLUS-1))
     (31 31
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (31 31 (:REWRITE NORMALIZE-ADDENDS))
     (29 29 (:REWRITE DEFAULT-CAR))
     (27 27
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (27 27
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (27 27
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (27 27 (:REWRITE |(equal c (/ x))|))
     (27 27 (:REWRITE |(equal c (- x))|))
     (27 27 (:REWRITE |(equal (/ x) c)|))
     (27 27 (:REWRITE |(equal (/ x) (/ y))|))
     (27 27 (:REWRITE |(equal (- x) c)|))
     (27 27 (:REWRITE |(equal (- x) (- y))|))
     (16 16 (:REWRITE REDUCE-RATIONALP-+))
     (16 16 (:REWRITE REDUCE-RATIONALP-*))
     (16 16 (:REWRITE REDUCE-INTEGERP-+))
     (16 16 (:REWRITE RATIONALP-MINUS-X))
     (16 16 (:REWRITE INTEGERP-MINUS-X))
     (16 16 (:META META-RATIONALP-CORRECT))
     (16 16 (:META META-INTEGERP-CORRECT))
     (11 11
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (8 5
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (8 5 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (8 5 (:REWRITE DEFAULT-LESS-THAN-2))
     (5 5 (:REWRITE THE-FLOOR-BELOW))
     (5 5 (:REWRITE THE-FLOOR-ABOVE))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (5 5 (:REWRITE SIMPLIFY-SUMS-<))
     (5 5 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (5 5 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (5 5
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (5 5
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (5 5 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (5 5 (:REWRITE INTEGERP-<-CONSTANT))
     (5 5 (:REWRITE DEFAULT-LESS-THAN-1))
     (5 5 (:REWRITE CONSTANT-<-INTEGERP))
     (5 5
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (5 5
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (5 5
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (5 5
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (5 5 (:REWRITE |(< c (- x))|))
     (5 5 (:REWRITE |(< 0 (/ x))|))
     (5 5 (:REWRITE |(< 0 (* x y))|))
     (5 5
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (5 5
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (5 5
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (5 5
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (5 5 (:REWRITE |(< (/ x) (/ y))|))
     (5 5 (:REWRITE |(< (- x) c)|))
     (5 5 (:REWRITE |(< (- x) (- y))|))
     (3 3 (:REWRITE |(< y (+ (- c) x))|))
     (3 3 (:REWRITE |(< x (+ c/d y))|)))
(FM9001::SIGN-EXTEND)
(FM9001::LEN-SIGN-EXTEND
     (288 8 (:REWRITE REPEAT-WHEN-ZP))
     (282 10 (:REWRITE ZP-OPEN))
     (145 21
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (30 24 (:REWRITE DEFAULT-PLUS-2))
     (28 12 (:REWRITE BOOL-FIX-WHEN-BOOLEANP))
     (28 12 (:REWRITE FM9001::BOOL-FIX-CAR-X=X))
     (24 24 (:REWRITE DEFAULT-PLUS-1))
     (22 22 (:REWRITE THE-FLOOR-BELOW))
     (22 22 (:REWRITE THE-FLOOR-ABOVE))
     (22 22 (:REWRITE DEFAULT-LESS-THAN-2))
     (21 21
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (21 21
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (18 16 (:REWRITE DEFAULT-CDR))
     (18 2 (:REWRITE ACL2-NUMBERP-X))
     (17 17
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (17 17 (:REWRITE INTEGERP-<-CONSTANT))
     (17 17 (:REWRITE CONSTANT-<-INTEGERP))
     (17 17
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (17 17
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (17 17
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (17 17
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (17 17 (:REWRITE |(< c (- x))|))
     (17 17
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (17 17
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (17 17
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (17 17
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (17 17 (:REWRITE |(< (/ x) (/ y))|))
     (17 17 (:REWRITE |(< (- x) c)|))
     (17 17 (:REWRITE |(< (- x) (- y))|))
     (16 16 (:TYPE-PRESCRIPTION FM9001::BVP-LEN))
     (16 16 (:TYPE-PRESCRIPTION BOOLEANP))
     (14 14
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (14 14 (:REWRITE NORMALIZE-ADDENDS))
     (13 13 (:REWRITE SIMPLIFY-SUMS-<))
     (13 13
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (13 13 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (12 12 (:REWRITE DEFAULT-CAR))
     (12 6
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (12 6
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (10 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (9 9 (:REWRITE |(< (/ x) 0)|))
     (9 9 (:REWRITE |(< (* x y) 0)|))
     (8 2 (:REWRITE RATIONALP-X))
     (7 7
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (7 7
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (6 6 (:REWRITE REDUCE-INTEGERP-+))
     (6 6 (:REWRITE INTEGERP-MINUS-X))
     (6 6
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (6 6 (:REWRITE |(equal c (/ x))|))
     (6 6 (:REWRITE |(equal c (- x))|))
     (6 6 (:REWRITE |(equal (/ x) c)|))
     (6 6 (:REWRITE |(equal (/ x) (/ y))|))
     (6 6 (:REWRITE |(equal (- x) c)|))
     (6 6 (:REWRITE |(equal (- x) (- y))|))
     (6 6 (:META META-INTEGERP-CORRECT))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (4 4 (:REWRITE |(< x (+ c/d y))|))
     (4 4 (:REWRITE |(< 0 (* x y))|))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (2 2 (:REWRITE REDUCE-RATIONALP-+))
     (2 2 (:REWRITE REDUCE-RATIONALP-*))
     (2 2 (:REWRITE RATIONALP-MINUS-X))
     (2 2 (:META META-RATIONALP-CORRECT))
     (1 1 (:REWRITE |(< (+ c/d x) y)|))
     (1 1 (:REWRITE |(< (+ (- c) x) y)|)))
(FM9001::BVP-REPEAT-BOOL (2 2 (:TYPE-PRESCRIPTION BOOLEANP)))
(FM9001::BVP-SIGN-EXTEND
     (729 18 (:REWRITE ZP-OPEN))
     (642 12 (:REWRITE REPEAT-WHEN-ZP))
     (567 6 (:DEFINITION REPEAT))
     (309 30
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (51 12 (:REWRITE |(+ c (+ d x))|))
     (32 32 (:REWRITE DEFAULT-PLUS-2))
     (32 32 (:REWRITE DEFAULT-PLUS-1))
     (30 30 (:REWRITE THE-FLOOR-BELOW))
     (30 30 (:REWRITE THE-FLOOR-ABOVE))
     (30 30
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (30 30
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (30 30 (:REWRITE DEFAULT-LESS-THAN-2))
     (30 30 (:REWRITE DEFAULT-LESS-THAN-1))
     (21 21 (:REWRITE SIMPLIFY-SUMS-<))
     (21 21
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (21 21 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (21 21
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (21 21 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (21 21 (:REWRITE INTEGERP-<-CONSTANT))
     (21 21 (:REWRITE CONSTANT-<-INTEGERP))
     (21 21
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (21 21
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (21 21
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (21 21
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (21 21 (:REWRITE |(< c (- x))|))
     (21 21
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (21 21
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (21 21
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (21 21
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (21 21 (:REWRITE |(< (/ x) (/ y))|))
     (21 21 (:REWRITE |(< (- x) c)|))
     (21 21 (:REWRITE |(< (- x) (- y))|))
     (21 9 (:REWRITE BOOL-FIX-WHEN-BOOLEANP))
     (21 9 (:REWRITE FM9001::BOOL-FIX-CAR-X=X))
     (16 14 (:REWRITE DEFAULT-CAR))
     (15 13 (:REWRITE DEFAULT-CDR))
     (12 12 (:TYPE-PRESCRIPTION FM9001::BVP-LEN))
     (12 12 (:TYPE-PRESCRIPTION BOOLEANP))
     (12 12 (:REWRITE |(< x (+ c/d y))|))
     (12 12 (:REWRITE |(< 0 (* x y))|))
     (11 11
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (11 11 (:REWRITE NORMALIZE-ADDENDS))
     (9 9 (:REWRITE |(+ 0 x)|))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (3 3 (:REWRITE |(< y (+ (- c) x))|))
     (3 3 (:REWRITE |(< 0 (/ x))|)))
(FM9001::SIGN-EXTEND-AS-APPEND
     (10094 154 (:REWRITE REPEAT-WHEN-ZP))
     (9461 77 (:DEFINITION REPEAT))
     (1608 416
           (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (900 802 (:REWRITE DEFAULT-PLUS-2))
     (860 420 (:REWRITE |(< c (- x))|))
     (839 802 (:REWRITE DEFAULT-PLUS-1))
     (570 552 (:REWRITE DEFAULT-LESS-THAN-2))
     (564 552 (:REWRITE DEFAULT-LESS-THAN-1))
     (552 552 (:REWRITE THE-FLOOR-BELOW))
     (552 552 (:REWRITE THE-FLOOR-ABOVE))
     (552 552
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (552 552
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (456 300 (:REWRITE NORMALIZE-ADDENDS))
     (439 416
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (420 420
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (420 420
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (420 420
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (420 420
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (420 420
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (420 420
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (420 420
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (420 420
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (420 420 (:REWRITE |(< (/ x) (/ y))|))
     (420 420 (:REWRITE |(< (- x) (- y))|))
     (418 416
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (416 416 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (416 416 (:REWRITE INTEGERP-<-CONSTANT))
     (416 416 (:REWRITE CONSTANT-<-INTEGERP))
     (416 416 (:REWRITE |(< (- x) c)|))
     (408 395 (:REWRITE SIMPLIFY-SUMS-<))
     (279 279
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (241 241 (:REWRITE |(< x (+ c/d y))|))
     (240 232 (:REWRITE DEFAULT-CDR))
     (229 229 (:REWRITE |(< 0 (* x y))|))
     (213 205 (:REWRITE DEFAULT-CAR))
     (161 69 (:REWRITE FM9001::BOOL-FIX-CAR-X=X))
     (135 135 (:TYPE-PRESCRIPTION ZP))
     (110 110 (:REWRITE |(< y (+ (- c) x))|))
     (100 49
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (100 49
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (98 98 (:REWRITE |(< 0 (/ x))|))
     (88 88
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (88 88
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (84 49 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (50 42 (:DEFINITION FIX))
     (49 49
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (49 49
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (49 49
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (49 49 (:REWRITE |(equal c (/ x))|))
     (49 49 (:REWRITE |(equal c (- x))|))
     (49 49 (:REWRITE |(equal (/ x) c)|))
     (49 49 (:REWRITE |(equal (/ x) (/ y))|))
     (49 49 (:REWRITE |(equal (- x) c)|))
     (49 49 (:REWRITE |(equal (- x) (- y))|))
     (36 36 (:REWRITE REDUCE-INTEGERP-+))
     (36 36 (:REWRITE INTEGERP-MINUS-X))
     (36 36 (:META META-INTEGERP-CORRECT))
     (34 17 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
     (33 24 (:REWRITE DEFAULT-MINUS))
     (31 31 (:REWRITE |(< (+ c/d x) y)|))
     (25 21 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (24 4 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
     (21 21 (:REWRITE |(+ x (- x))|))
     (16 16
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (15 15 (:REWRITE FOLD-CONSTS-IN-+))
     (10 10 (:REWRITE |(< (/ x) 0)|))
     (10 10 (:REWRITE |(< (* x y) 0)|))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (6 4 (:REWRITE |(- (- x))|))
     (2 2 (:REWRITE |(equal x (if a b c))|)))
(FM9001::V-ADDER)
(FM9001::LEN-OF-V-ADDER
     (31 11 (:REWRITE BOOL-FIX-WHEN-BOOLEANP))
     (30 6 (:DEFINITION FM9001::B-AND))
     (26 13 (:REWRITE DEFAULT-PLUS-2))
     (18 18 (:TYPE-PRESCRIPTION BOOLEANP))
     (15 11 (:REWRITE DEFAULT-CDR))
     (14 14 (:REWRITE DEFAULT-CAR))
     (14 2 (:DEFINITION FM9001::B-OR3))
     (13 13 (:REWRITE DEFAULT-PLUS-1))
     (11 11
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (11 11 (:REWRITE NORMALIZE-ADDENDS))
     (9 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (9 3
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (9 3
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (6 6
        (:TYPE-PRESCRIPTION BOOLEANP-OF-BOOL-FIX))
     (6 2 (:REWRITE FM9001::BOOL-FIX-CAR-X=X))
     (4 4 (:REWRITE BOOL-FIX-UNDER-IFF))
     (3 3
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (3 3
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (3 3
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (3 3 (:REWRITE |(equal c (/ x))|))
     (3 3 (:REWRITE |(equal c (- x))|))
     (3 3 (:REWRITE |(equal (/ x) c)|))
     (3 3 (:REWRITE |(equal (/ x) (/ y))|))
     (3 3 (:REWRITE |(equal (- x) c)|))
     (3 3 (:REWRITE |(equal (- x) (- y))|))
     (3 3 (:REWRITE |(equal (+ (- c) x) y)|)))
(FM9001::BVP-V-ADDER (31 11 (:REWRITE BOOL-FIX-WHEN-BOOLEANP))
                     (30 6 (:DEFINITION FM9001::B-AND))
                     (23 19 (:REWRITE DEFAULT-CAR))
                     (18 18 (:TYPE-PRESCRIPTION BOOLEANP))
                     (14 2 (:DEFINITION FM9001::B-OR3))
                     (13 9 (:REWRITE DEFAULT-CDR))
                     (6 2 (:REWRITE FM9001::BOOL-FIX-CAR-X=X))
                     (4 4 (:REWRITE BOOL-FIX-UNDER-IFF)))
(FM9001::V-ADDER-OUTPUT)
(FM9001::LEN-V-ADDER-OUTPUT
     (243 2 (:REWRITE TAKE-OF-TOO-MANY))
     (208 1 (:DEFINITION TAKE))
     (130 2 (:REWRITE TAKE-OF-LEN-FREE))
     (60 4 (:REWRITE |(+ y x)|))
     (54 6 (:REWRITE SIMPLIFY-SUMS-<))
     (51 27 (:REWRITE DEFAULT-PLUS-2))
     (51 15 (:REWRITE NORMALIZE-ADDENDS))
     (50 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (46 6 (:DEFINITION LEN))
     (45 27 (:REWRITE DEFAULT-PLUS-1))
     (43 1 (:REWRITE |(< (+ (- c) x) y)|))
     (40 2 (:REWRITE |(+ y (+ x z))|))
     (39 8 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (38 1 (:REWRITE ZP-OPEN))
     (30 3 (:REWRITE |(equal (+ (- c) x) y)|))
     (26 2 (:REWRITE FM9001::LEN-OF-V-ADDER))
     (12 8 (:REWRITE DEFAULT-LESS-THAN-2))
     (12 6
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (12 6 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (12 6 (:DEFINITION FIX))
     (11 11
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (11 8 (:REWRITE DEFAULT-LESS-THAN-1))
     (10 10 (:TYPE-PRESCRIPTION FM9001::V-ADDER))
     (8 8 (:REWRITE THE-FLOOR-BELOW))
     (8 8 (:REWRITE THE-FLOOR-ABOVE))
     (8 8
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (8 8
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (8 7 (:REWRITE DEFAULT-CDR))
     (8 4 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (8 4 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
     (6 6 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (6 6 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (6 6 (:REWRITE INTEGERP-<-CONSTANT))
     (6 6 (:REWRITE CONSTANT-<-INTEGERP))
     (6 6
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (6 6
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (6 6
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (6 6
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (6 6 (:REWRITE |(< c (- x))|))
     (6 6
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (6 6
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (6 6
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (6 6
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (6 6 (:REWRITE |(< (/ x) (/ y))|))
     (6 6 (:REWRITE |(< (- x) c)|))
     (6 6 (:REWRITE |(< (- x) (- y))|))
     (6 2 (:REWRITE TAKE-WHEN-ATOM))
     (5 2
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (5 2
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (4 4 (:REWRITE |(+ x (- x))|))
     (4 1 (:REWRITE |(+ c (+ d x))|))
     (3 3
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (3 3
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (3 3 (:REWRITE |(< (* x y) 0)|))
     (3 1 (:DEFINITION NOT))
     (2 2 (:TYPE-PRESCRIPTION NFIX))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (2 2
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (2 2 (:REWRITE |(equal c (/ x))|))
     (2 2 (:REWRITE |(equal c (- x))|))
     (2 2 (:REWRITE |(equal (/ x) c)|))
     (2 2 (:REWRITE |(equal (/ x) (/ y))|))
     (2 2 (:REWRITE |(equal (- x) c)|))
     (2 2 (:REWRITE |(equal (- x) (- y))|))
     (2 2 (:REWRITE |(< y (+ (- c) x))|))
     (2 2 (:REWRITE |(< x (+ c/d y))|))
     (2 2 (:REWRITE |(< (/ x) 0)|))
     (2 2 (:REWRITE |(< (+ c/d x) y)|))
     (2 1 (:REWRITE DEFAULT-CAR))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (1 1 (:REWRITE |(< 0 (/ x))|))
     (1 1 (:REWRITE |(< 0 (* x y))|))
     (1 1 (:REWRITE |(+ 0 x)|)))
(FM9001::V-ADDER-CARRY-OUT)
(FM9001::V-ADDER-OVERFLOWP
     (48 16 (:REWRITE FM9001::BVP-IS-TRUE-LISTP))
     (40 8 (:DEFINITION TRUE-LISTP))
     (13 13 (:REWRITE DEFAULT-CDR))
     (11 6 (:REWRITE DEFAULT-PLUS-2))
     (10 5
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (10 5
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (6 6
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (6 6 (:REWRITE NORMALIZE-ADDENDS))
     (6 6 (:REWRITE DEFAULT-PLUS-1))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (5 5 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (5 5
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (5 5
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (5 5
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (5 5 (:REWRITE |(equal c (/ x))|))
     (5 5 (:REWRITE |(equal c (- x))|))
     (5 5 (:REWRITE |(equal (/ x) c)|))
     (5 5 (:REWRITE |(equal (/ x) (/ y))|))
     (5 5 (:REWRITE |(equal (- x) c)|))
     (5 5 (:REWRITE |(equal (- x) (- y))|)))
(FM9001::V-SUBTRACTER-OUTPUT)
(FM9001::LEN-V-SUBTRACTER-OUTPUT)
(FM9001::V-SUBTRACTER-CARRY-OUT)
(FM9001::V-SUBTRACTER-OVERFLOWP (42 14 (:REWRITE FM9001::BVP-IS-TRUE-LISTP))
                                (28 28 (:TYPE-PRESCRIPTION FM9001::BVP))
                                (9 9 (:REWRITE DEFAULT-CDR))
                                (4 4 (:REWRITE DEFAULT-CAR)))
(FM9001::V-INC)
(FM9001::V-DEC)
(FM9001::BVP-LEN-V-INC-V-DEC
     (1034 8 (:REWRITE TAKE-OF-TOO-MANY))
     (832 4 (:DEFINITION TAKE))
     (582 8 (:REWRITE TAKE-OF-LEN-FREE))
     (240 16 (:REWRITE |(+ y x)|))
     (228 8 (:REWRITE FM9001::LEN-OF-V-ADDER))
     (220 28 (:REWRITE SIMPLIFY-SUMS-<))
     (200 56 (:REWRITE NORMALIZE-ADDENDS))
     (200 8 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (196 104 (:REWRITE DEFAULT-PLUS-2))
     (176 104 (:REWRITE DEFAULT-PLUS-1))
     (172 4 (:REWRITE |(< (+ (- c) x) y)|))
     (160 36
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (160 8 (:REWRITE |(+ y (+ x z))|))
     (156 20 (:DEFINITION LEN))
     (152 4 (:REWRITE ZP-OPEN))
     (120 12 (:REWRITE |(equal (+ (- c) x) y)|))
     (56 28
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (56 28 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (52 36 (:REWRITE DEFAULT-LESS-THAN-2))
     (52 36 (:REWRITE DEFAULT-LESS-THAN-1))
     (48 24 (:DEFINITION FIX))
     (40 40 (:TYPE-PRESCRIPTION FM9001::V-ADDER))
     (40 40
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (36 36 (:REWRITE THE-FLOOR-BELOW))
     (36 36 (:REWRITE THE-FLOOR-ABOVE))
     (36 36
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (36 36
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (32 16 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (32 16 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
     (28 28 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (28 28
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (28 28 (:REWRITE INTEGERP-<-CONSTANT))
     (28 28 (:REWRITE CONSTANT-<-INTEGERP))
     (28 28
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (28 28
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (28 28
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (28 28
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (28 28 (:REWRITE |(< c (- x))|))
     (28 28
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (28 28
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (28 28
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (28 28
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (28 28 (:REWRITE |(< (/ x) (/ y))|))
     (28 28 (:REWRITE |(< (- x) c)|))
     (28 28 (:REWRITE |(< (- x) (- y))|))
     (28 24 (:REWRITE DEFAULT-CDR))
     (24 8 (:REWRITE TAKE-WHEN-ATOM))
     (20 8
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (20 8
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (16 16 (:REWRITE |(< (* x y) 0)|))
     (16 16 (:REWRITE |(+ x (- x))|))
     (16 4 (:REWRITE |(+ c (+ d x))|))
     (12 12
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (12 12
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (12 12
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (12 12
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (12 12 (:REWRITE |(< (/ x) 0)|))
     (12 4 (:DEFINITION NOT))
     (8 8 (:TYPE-PRESCRIPTION NFIX))
     (8 8
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (8 8 (:REWRITE |(equal c (/ x))|))
     (8 8 (:REWRITE |(equal c (- x))|))
     (8 8 (:REWRITE |(equal (/ x) c)|))
     (8 8 (:REWRITE |(equal (/ x) (/ y))|))
     (8 8 (:REWRITE |(equal (- x) c)|))
     (8 8 (:REWRITE |(equal (- x) (- y))|))
     (8 8 (:REWRITE |(< y (+ (- c) x))|))
     (8 8 (:REWRITE |(< x (+ c/d y))|))
     (8 8 (:REWRITE |(< (+ c/d x) y)|))
     (8 4 (:REWRITE DEFAULT-CAR))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (4 4 (:REWRITE |(< 0 (/ x))|))
     (4 4 (:REWRITE |(< 0 (* x y))|))
     (4 4 (:REWRITE |(+ 0 x)|)))
(FM9001::V-BUF-WORKS (10 10 (:REWRITE DEFAULT-CAR))
                     (6 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                     (6 3
                        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                     (6 3
                        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                     (5 5 (:REWRITE DEFAULT-CDR))
                     (3 3
                        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                     (3 3
                        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
                     (3 3
                        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
                     (3 3 (:REWRITE |(equal c (/ x))|))
                     (3 3 (:REWRITE |(equal c (- x))|))
                     (3 3 (:REWRITE |(equal (/ x) c)|))
                     (3 3 (:REWRITE |(equal (/ x) (/ y))|))
                     (3 3 (:REWRITE |(equal (- x) c)|))
                     (3 3 (:REWRITE |(equal (- x) (- y))|)))
(FM9001::V-IF-WORKS (221 209 (:REWRITE DEFAULT-CDR))
                    (190 36
                         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                    (187 95 (:REWRITE DEFAULT-PLUS-2))
                    (143 39 (:REWRITE ACL2-NUMBERP-X))
                    (113 101 (:REWRITE DEFAULT-CAR))
                    (95 95 (:REWRITE DEFAULT-PLUS-1))
                    (86 36
                        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                    (81 36 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                    (71 71
                        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                    (71 71 (:REWRITE NORMALIZE-ADDENDS))
                    (52 13 (:REWRITE RATIONALP-X))
                    (40 40
                        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                    (36 36
                        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
                    (36 36 (:REWRITE |(equal c (/ x))|))
                    (36 36 (:REWRITE |(equal c (- x))|))
                    (36 36 (:REWRITE |(equal (/ x) c)|))
                    (36 36 (:REWRITE |(equal (/ x) (/ y))|))
                    (36 36 (:REWRITE |(equal (- x) c)|))
                    (36 36 (:REWRITE |(equal (- x) (- y))|))
                    (13 13 (:REWRITE REDUCE-RATIONALP-+))
                    (13 13 (:REWRITE REDUCE-RATIONALP-*))
                    (13 13 (:REWRITE REDUCE-INTEGERP-+))
                    (13 13 (:REWRITE RATIONALP-MINUS-X))
                    (13 13 (:REWRITE INTEGERP-MINUS-X))
                    (13 13 (:META META-RATIONALP-CORRECT))
                    (13 13 (:META META-INTEGERP-CORRECT))
                    (5 5
                       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
                    (3 3 (:REWRITE |(equal (+ (- c) x) y)|)))
(FM9001::V-ADDER-WORKS
     (644 279 (:REWRITE DEFAULT-PLUS-2))
     (341 279 (:REWRITE DEFAULT-PLUS-1))
     (283 249 (:REWRITE DEFAULT-CDR))
     (256 122 (:REWRITE DEFAULT-TIMES-2))
     (221 204 (:REWRITE DEFAULT-CAR))
     (183 37
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (183 37
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (182 37 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (181 181
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (181 181 (:REWRITE NORMALIZE-ADDENDS))
     (122 122
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (122 122 (:REWRITE DEFAULT-TIMES-1))
     (56 21 (:REWRITE BOOL-FIX-WHEN-BOOLEANP))
     (37 37
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (37 37
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (37 37
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (37 37 (:REWRITE |(equal c (/ x))|))
     (37 37 (:REWRITE |(equal c (- x))|))
     (37 37 (:REWRITE |(equal (/ x) c)|))
     (37 37 (:REWRITE |(equal (/ x) (/ y))|))
     (37 37 (:REWRITE |(equal (- x) c)|))
     (37 37 (:REWRITE |(equal (- x) (- y))|))
     (32 32 (:TYPE-PRESCRIPTION BOOLEANP))
     (28 28 (:REWRITE |(equal (+ (- c) x) y)|))
     (26 26 (:REWRITE FOLD-CONSTS-IN-+))
     (21 7 (:REWRITE FM9001::BOOL-FIX-CAR-X=X))
     (13 13 (:REWRITE |(+ x (if a b c))|))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(FM9001::V-THREEFIX (1 1 (:TYPE-PRESCRIPTION FM9001::3V-FIX)))
(FM9001::OPEN-V-THREEFIX (6 6 (:REWRITE DEFAULT-CAR))
                         (5 5 (:REWRITE DEFAULT-CDR)))
(FM9001::V-THREEFIX-BVP
     (18 3 (:DEFINITION FM9001::V-THREEFIX))
     (16 16 (:REWRITE DEFAULT-CAR))
     (13 13 (:REWRITE DEFAULT-CDR))
     (9 5 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (9 5
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (9 5
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (5 5
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (5 5
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (5 5
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (5 5 (:REWRITE |(equal c (/ x))|))
     (5 5 (:REWRITE |(equal c (- x))|))
     (5 5 (:REWRITE |(equal (/ x) c)|))
     (5 5 (:REWRITE |(equal (/ x) (/ y))|))
     (5 5 (:REWRITE |(equal (- x) c)|))
     (5 5 (:REWRITE |(equal (- x) (- y))|)))
(FM9001::LEN-V-THREEFIX
     (18 6 (:REWRITE FM9001::V-THREEFIX-BVP))
     (18 2 (:DEFINITION FM9001::V-THREEFIX))
     (14 7 (:REWRITE DEFAULT-PLUS-2))
     (12 12 (:TYPE-PRESCRIPTION FM9001::BVP))
     (9 8 (:REWRITE DEFAULT-CDR))
     (9 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (9 3
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (9 3
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (7 7
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (7 7 (:REWRITE NORMALIZE-ADDENDS))
     (7 7 (:REWRITE DEFAULT-PLUS-1))
     (3 3
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (3 3
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (3 3
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (3 3 (:REWRITE DEFAULT-CAR))
     (3 3 (:REWRITE |(equal c (/ x))|))
     (3 3 (:REWRITE |(equal c (- x))|))
     (3 3 (:REWRITE |(equal (/ x) c)|))
     (3 3 (:REWRITE |(equal (/ x) (/ y))|))
     (3 3 (:REWRITE |(equal (- x) c)|))
     (3 3 (:REWRITE |(equal (- x) (- y))|)))
(FM9001::APPEND-V-THREEFIX
     (132 12 (:DEFINITION FM9001::V-THREEFIX))
     (91 27 (:REWRITE FM9001::V-THREEFIX-BVP))
     (60 60 (:TYPE-PRESCRIPTION FM9001::BVP))
     (35 35 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (25 21 (:REWRITE DEFAULT-CAR))
     (23 19 (:REWRITE DEFAULT-CDR))
     (15 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (15 3
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (15 3
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (12 4 (:REWRITE FM9001::BVP-APPEND))
     (3 3
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (3 3
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (3 3
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (3 3 (:REWRITE |(equal c (/ x))|))
     (3 3 (:REWRITE |(equal c (- x))|))
     (3 3 (:REWRITE |(equal (/ x) c)|))
     (3 3 (:REWRITE |(equal (/ x) (/ y))|))
     (3 3 (:REWRITE |(equal (- x) c)|))
     (3 3 (:REWRITE |(equal (- x) (- y))|)))
(FM9001::V-THREEFIX-APPEND)
(FM9001::V-THREEFIX-IDEMPOTENCE
     (71 27 (:REWRITE FM9001::V-THREEFIX-BVP))
     (52 33 (:TYPE-PRESCRIPTION FM9001::3V-FIX))
     (44 44 (:TYPE-PRESCRIPTION FM9001::BVP))
     (39 7
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (23 3 (:REWRITE ACL2-NUMBERP-X))
     (22 19 (:REWRITE DEFAULT-CAR))
     (19 16 (:REWRITE DEFAULT-CDR))
     (19 7 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (19 7
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (10 1 (:REWRITE RATIONALP-X))
     (7 7
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (7 7
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (7 7
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (7 7 (:REWRITE |(equal c (/ x))|))
     (7 7 (:REWRITE |(equal c (- x))|))
     (7 7 (:REWRITE |(equal (/ x) c)|))
     (7 7 (:REWRITE |(equal (/ x) (/ y))|))
     (7 7 (:REWRITE |(equal (- x) c)|))
     (7 7 (:REWRITE |(equal (- x) (- y))|))
     (2 2 (:REWRITE |(equal x (if a b c))|))
     (2 2 (:REWRITE |(equal (if a b c) x)|))
     (1 1 (:REWRITE REDUCE-RATIONALP-+))
     (1 1 (:REWRITE REDUCE-RATIONALP-*))
     (1 1 (:REWRITE REDUCE-INTEGERP-+))
     (1 1 (:REWRITE RATIONALP-MINUS-X))
     (1 1 (:REWRITE INTEGERP-MINUS-X))
     (1 1 (:META META-RATIONALP-CORRECT))
     (1 1 (:META META-INTEGERP-CORRECT)))
(FM9001::BVP-V-THREEFIX
     (52 7 (:REWRITE FM9001::BVP-IS-TRUE-LISTP))
     (49 6 (:REWRITE FM9001::V-THREEFIX-BVP))
     (32 2 (:DEFINITION FM9001::V-THREEFIX))
     (29 27 (:REWRITE DEFAULT-CAR))
     (19 18 (:REWRITE DEFAULT-CDR))
     (9 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (9 4
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (9 4
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (4 4
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (4 4
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (4 4
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (4 4 (:REWRITE |(equal c (/ x))|))
     (4 4 (:REWRITE |(equal c (- x))|))
     (4 4 (:REWRITE |(equal (/ x) c)|))
     (4 4 (:REWRITE |(equal (/ x) (/ y))|))
     (4 4 (:REWRITE |(equal (- x) c)|))
     (4 4 (:REWRITE |(equal (- x) (- y))|))
     (1 1 (:REWRITE |(equal x (if a b c))|))
     (1 1 (:REWRITE |(equal (if a b c) x)|)))
(FM9001::V-THREEFIX-MAKE-LIST-4X
     (344 34
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (63 11 (:REWRITE FM9001::V-THREEFIX-BVP))
     (40 10 (:REWRITE |(+ c (+ d x))|))
     (34 34 (:REWRITE THE-FLOOR-BELOW))
     (34 34 (:REWRITE THE-FLOOR-ABOVE))
     (34 34
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (34 34
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (34 34 (:REWRITE DEFAULT-LESS-THAN-2))
     (34 34 (:REWRITE DEFAULT-LESS-THAN-1))
     (26 26 (:REWRITE DEFAULT-PLUS-2))
     (26 26 (:REWRITE DEFAULT-PLUS-1))
     (24 24 (:REWRITE SIMPLIFY-SUMS-<))
     (24 24
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (24 24
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (24 24 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (24 24 (:REWRITE INTEGERP-<-CONSTANT))
     (24 24 (:REWRITE CONSTANT-<-INTEGERP))
     (24 24
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (24 24
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (24 24
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (24 24
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (24 24 (:REWRITE |(< c (- x))|))
     (24 24
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (24 24
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (24 24
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (24 24
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (24 24 (:REWRITE |(< (/ x) (/ y))|))
     (24 24 (:REWRITE |(< (- x) c)|))
     (24 24 (:REWRITE |(< (- x) (- y))|))
     (22 22 (:TYPE-PRESCRIPTION FM9001::BVP))
     (22 22 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (22 6 (:REWRITE DEFAULT-CDR))
     (22 6 (:REWRITE DEFAULT-CAR))
     (14 14 (:REWRITE |(< x (+ c/d y))|))
     (14 14 (:REWRITE |(< 0 (* x y))|))
     (10 10
         (:TYPE-PRESCRIPTION FM9001::BVP-REPEAT-OF-BOOLEANP))
     (10 10
         (:TYPE-PRESCRIPTION FM9001::BVP-REPEAT-BOOL))
     (10 10 (:REWRITE |(+ 0 x)|))
     (8 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (8 4
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (8 4
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (6 6
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (6 6 (:REWRITE NORMALIZE-ADDENDS))
     (5 5
        (:REWRITE FM9001::BVP-REPEAT-OF-BOOLEANP))
     (5 5 (:REWRITE FM9001::BVP-REPEAT-BOOL))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (4 4
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (4 4
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (4 4
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (4 4 (:REWRITE |(equal c (/ x))|))
     (4 4 (:REWRITE |(equal c (- x))|))
     (4 4 (:REWRITE |(equal (/ x) c)|))
     (4 4 (:REWRITE |(equal (/ x) (/ y))|))
     (4 4 (:REWRITE |(equal (- x) c)|))
     (4 4 (:REWRITE |(equal (- x) (- y))|))
     (4 4 (:REWRITE |(< y (+ (- c) x))|))
     (4 4 (:REWRITE |(< 0 (/ x))|)))
(FM9001::V-FOURFIX (1 1 (:TYPE-PRESCRIPTION FM9001::4V-FIX)))
(FM9001::4V-LISTP-V-FOURFIX (8 7 (:REWRITE DEFAULT-CAR))
                            (7 6 (:REWRITE DEFAULT-CDR)))
(FM9001::LEN-V-FOURFIX
     (14 7 (:REWRITE DEFAULT-PLUS-2))
     (9 8 (:REWRITE DEFAULT-CDR))
     (9 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (9 3
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (9 3
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (7 7
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (7 7 (:REWRITE NORMALIZE-ADDENDS))
     (7 7 (:REWRITE DEFAULT-PLUS-1))
     (3 3
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (3 3
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (3 3
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (3 3 (:REWRITE DEFAULT-CAR))
     (3 3 (:REWRITE |(equal c (/ x))|))
     (3 3 (:REWRITE |(equal c (- x))|))
     (3 3 (:REWRITE |(equal (/ x) c)|))
     (3 3 (:REWRITE |(equal (/ x) (/ y))|))
     (3 3 (:REWRITE |(equal (- x) c)|))
     (3 3 (:REWRITE |(equal (- x) (- y))|)))
(FM9001::BVP-V-FOURFIX
     (16 16 (:REWRITE DEFAULT-CAR))
     (13 13 (:REWRITE DEFAULT-CDR))
     (9 5 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (9 5
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (9 5
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (5 5
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (5 5
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (5 5
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (5 5 (:REWRITE |(equal c (/ x))|))
     (5 5 (:REWRITE |(equal c (- x))|))
     (5 5 (:REWRITE |(equal (/ x) c)|))
     (5 5 (:REWRITE |(equal (/ x) (/ y))|))
     (5 5 (:REWRITE |(equal (- x) c)|))
     (5 5 (:REWRITE |(equal (- x) (- y))|)))
(FM9001::V-FOURFIX-MAKE-LIST
     (462 21 (:REWRITE ZP-OPEN))
     (206 20
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (100 10 (:REWRITE FM9001::BVP-V-FOURFIX))
     (85 12 (:REWRITE CONSP-OF-REPEAT))
     (40 40 (:TYPE-PRESCRIPTION BOOLEANP))
     (24 6 (:REWRITE |(+ c (+ d x))|))
     (20 20 (:TYPE-PRESCRIPTION FM9001::BVP))
     (20 20 (:REWRITE THE-FLOOR-BELOW))
     (20 20 (:REWRITE THE-FLOOR-ABOVE))
     (20 20
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (20 20
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (20 20 (:REWRITE DEFAULT-LESS-THAN-2))
     (20 20 (:REWRITE DEFAULT-LESS-THAN-1))
     (20 10
         (:TYPE-PRESCRIPTION FM9001::BVP-REPEAT-OF-BOOLEANP))
     (20 10
         (:TYPE-PRESCRIPTION FM9001::BVP-REPEAT-BOOL))
     (18 18 (:REWRITE DEFAULT-PLUS-2))
     (18 18 (:REWRITE DEFAULT-PLUS-1))
     (18 5 (:REWRITE DEFAULT-CDR))
     (18 5 (:REWRITE DEFAULT-CAR))
     (15 5
         (:REWRITE FM9001::BVP-REPEAT-OF-BOOLEANP))
     (15 5 (:REWRITE FM9001::BVP-REPEAT-BOOL))
     (14 14 (:REWRITE SIMPLIFY-SUMS-<))
     (14 14
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (14 14 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (14 14
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (14 14 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (14 14 (:REWRITE INTEGERP-<-CONSTANT))
     (14 14 (:REWRITE CONSTANT-<-INTEGERP))
     (14 14
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (14 14
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (14 14
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (14 14
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (14 14 (:REWRITE |(< c (- x))|))
     (14 14
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (14 14
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (14 14
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (14 14
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (14 14 (:REWRITE |(< (/ x) (/ y))|))
     (14 14 (:REWRITE |(< (- x) c)|))
     (14 14 (:REWRITE |(< (- x) (- y))|))
     (8 8 (:REWRITE |(< x (+ c/d y))|))
     (8 8 (:REWRITE |(< 0 (* x y))|))
     (8 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (8 4
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (8 4
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (6 6
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (6 6 (:REWRITE NORMALIZE-ADDENDS))
     (6 6 (:REWRITE |(+ 0 x)|))
     (4 4
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (4 4
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (4 4
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (4 4 (:REWRITE |(equal c (/ x))|))
     (4 4 (:REWRITE |(equal c (- x))|))
     (4 4 (:REWRITE |(equal (/ x) c)|))
     (4 4 (:REWRITE |(equal (/ x) (/ y))|))
     (4 4 (:REWRITE |(equal (- x) c)|))
     (4 4 (:REWRITE |(equal (- x) (- y))|))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (2 2 (:REWRITE |(< y (+ (- c) x))|))
     (2 2 (:REWRITE |(< 0 (/ x))|)))
(FM9001::V-THREEFIX-V-FOURFIX
     (350 39
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (337 67 (:REWRITE ACL2-NUMBERP-X))
     (135 33 (:REWRITE RATIONALP-X))
     (80 39
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (57 19 (:REWRITE FM9001::V-THREEFIX-BVP))
     (54 54 (:TYPE-PRESCRIPTION FM9001::BVP))
     (48 39 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (39 39
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (39 39
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (39 39
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (39 39 (:REWRITE |(equal c (/ x))|))
     (39 39 (:REWRITE |(equal c (- x))|))
     (39 39 (:REWRITE |(equal (/ x) c)|))
     (39 39 (:REWRITE |(equal (/ x) (/ y))|))
     (39 39 (:REWRITE |(equal (- x) c)|))
     (39 39 (:REWRITE |(equal (- x) (- y))|))
     (33 33 (:REWRITE REDUCE-RATIONALP-+))
     (33 33 (:REWRITE REDUCE-RATIONALP-*))
     (33 33 (:REWRITE REDUCE-INTEGERP-+))
     (33 33 (:REWRITE RATIONALP-MINUS-X))
     (33 33 (:REWRITE INTEGERP-MINUS-X))
     (33 33 (:META META-RATIONALP-CORRECT))
     (33 33 (:META META-INTEGERP-CORRECT))
     (24 8 (:REWRITE FM9001::BVP-V-FOURFIX))
     (22 19 (:REWRITE DEFAULT-CAR))
     (19 16 (:REWRITE DEFAULT-CDR))
     (4 4 (:REWRITE |(equal x (if a b c))|))
     (4 4 (:REWRITE |(equal (if a b c) x)|))
     (1 1 (:TYPE-PRESCRIPTION FM9001::3VP)))
(FM9001::V-IFF
     (525 10 (:DEFINITION INTEGER-ABS))
     (217 80 (:REWRITE DEFAULT-PLUS-1))
     (198 80 (:REWRITE DEFAULT-PLUS-2))
     (175 5 (:REWRITE |(+ (if a b c) x)|))
     (155 5 (:REWRITE NUMERATOR-NEGATIVE))
     (50 5 (:DEFINITION LENGTH))
     (45 45 (:TYPE-PRESCRIPTION NUMERATOR-ZERO))
     (45 45
         (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 2))
     (45 45
         (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 1))
     (45 45
         (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 2))
     (45 45
         (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 1))
     (45 18 (:REWRITE DEFAULT-LESS-THAN-1))
     (42 42
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (35 10 (:REWRITE DEFAULT-MINUS))
     (35 5 (:DEFINITION LEN))
     (22 18 (:REWRITE DEFAULT-LESS-THAN-2))
     (20 5 (:REWRITE RATIONALP-X))
     (19 13
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (19 13 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (18 18 (:REWRITE THE-FLOOR-BELOW))
     (18 18 (:REWRITE THE-FLOOR-ABOVE))
     (18 18 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (18 18
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (18 18
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (18 18
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (18 18
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (18 18 (:REWRITE INTEGERP-<-CONSTANT))
     (18 18 (:REWRITE CONSTANT-<-INTEGERP))
     (18 18
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (18 18
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (18 18
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (18 18
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (18 18 (:REWRITE |(< c (- x))|))
     (18 18
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (18 18
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (18 18
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (18 18
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (18 18 (:REWRITE |(< (/ x) (/ y))|))
     (18 18 (:REWRITE |(< (- x) c)|))
     (18 18 (:REWRITE |(< (- x) (- y))|))
     (16 16 (:REWRITE DEFAULT-CDR))
     (15 15 (:REWRITE |(< (/ x) 0)|))
     (15 15 (:REWRITE |(< (* x y) 0)|))
     (12 12 (:REWRITE FOLD-CONSTS-IN-+))
     (12 12 (:REWRITE |(+ c (+ d x))|))
     (11 11 (:REWRITE DEFAULT-CAR))
     (10 10
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (10 10
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (10 10 (:REWRITE REDUCE-INTEGERP-+))
     (10 10 (:REWRITE INTEGERP-MINUS-X))
     (10 10 (:META META-INTEGERP-CORRECT))
     (8 4 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (5 5 (:TYPE-PRESCRIPTION LEN))
     (5 5 (:REWRITE REDUCE-RATIONALP-+))
     (5 5 (:REWRITE REDUCE-RATIONALP-*))
     (5 5 (:REWRITE RATIONALP-MINUS-X))
     (5 5 (:REWRITE INTEGERP==>NUMERATOR-=-X))
     (5 5 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
     (5 5 (:REWRITE DEFAULT-REALPART))
     (5 5 (:REWRITE DEFAULT-RATIONAL-NUMERATOR))
     (5 5
        (:REWRITE DEFAULT-RATIONAL-DENOMINATOR))
     (5 5 (:REWRITE DEFAULT-IMAGPART))
     (5 5 (:REWRITE DEFAULT-COERCE-2))
     (5 5 (:REWRITE DEFAULT-COERCE-1))
     (5 5 (:META META-RATIONALP-CORRECT))
     (3 3 (:REWRITE |(< y (+ (- c) x))|))
     (3 3 (:REWRITE |(< x (+ c/d y))|))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (1 1 (:REWRITE |(< 0 (/ x))|))
     (1 1 (:REWRITE |(< 0 (* x y))|)))
(FM9001::V-IFF-X-X (8 8 (:REWRITE DEFAULT-CAR))
                   (4 4 (:REWRITE DEFAULT-CDR)))
(FM9001::APPEND-ASSOCIATIVITY
     (1751 703
           (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
     (905 703 (:TYPE-PRESCRIPTION BINARY-APPEND))
     (703 703 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (192 3
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (141 9 (:REWRITE ACL2-NUMBERP-X))
     (66 3 (:REWRITE RATIONALP-X))
     (60 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (60 3
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (23 20 (:REWRITE DEFAULT-CAR))
     (19 16 (:REWRITE DEFAULT-CDR))
     (6 6
        (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
     (3 3 (:REWRITE REDUCE-RATIONALP-+))
     (3 3 (:REWRITE REDUCE-RATIONALP-*))
     (3 3
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (3 3 (:REWRITE REDUCE-INTEGERP-+))
     (3 3
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (3 3 (:REWRITE RATIONALP-MINUS-X))
     (3 3 (:REWRITE INTEGERP-MINUS-X))
     (3 3
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (3 3 (:REWRITE |(equal c (/ x))|))
     (3 3 (:REWRITE |(equal c (- x))|))
     (3 3 (:REWRITE |(equal (/ x) c)|))
     (3 3 (:REWRITE |(equal (/ x) (/ y))|))
     (3 3 (:REWRITE |(equal (- x) c)|))
     (3 3 (:REWRITE |(equal (- x) (- y))|))
     (3 3 (:META META-RATIONALP-CORRECT))
     (3 3 (:META META-INTEGERP-CORRECT)))
(FM9001::V-IFF-REVAPPEND
     (1358 592 (:REWRITE DEFAULT-CDR))
     (1259 493 (:REWRITE DEFAULT-CAR))
     (438 438 (:REWRITE CONSP-OF-REV))
     (272 136 (:REWRITE DEFAULT-PLUS-2))
     (189 73
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (189 73
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (188 73 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (136 136 (:REWRITE DEFAULT-PLUS-1))
     (106 106
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (106 106 (:REWRITE NORMALIZE-ADDENDS))
     (78 78
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (73 73
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (73 73 (:REWRITE |(equal c (/ x))|))
     (73 73 (:REWRITE |(equal c (- x))|))
     (73 73 (:REWRITE |(equal (/ x) c)|))
     (73 73 (:REWRITE |(equal (/ x) (/ y))|))
     (73 73 (:REWRITE |(equal (- x) c)|))
     (73 73 (:REWRITE |(equal (- x) (- y))|))
     (10 10 (:REWRITE |(equal x (if a b c))|))
     (10 10 (:REWRITE |(equal (if a b c) x)|))
     (6 6 (:REWRITE |(equal (+ (- c) x) y)|))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(FM9001::V-IFF-APPEND
     (100 82 (:REWRITE DEFAULT-CAR))
     (100 50
          (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
     (94 76 (:REWRITE DEFAULT-CDR))
     (50 50 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (50 50 (:TYPE-PRESCRIPTION BINARY-APPEND))
     (42 16
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (42 16
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (41 16 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (40 20 (:REWRITE DEFAULT-PLUS-2))
     (20 20
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (20 20 (:REWRITE NORMALIZE-ADDENDS))
     (20 20 (:REWRITE DEFAULT-PLUS-1))
     (16 16
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (16 16
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (16 16
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (16 16 (:REWRITE |(equal c (/ x))|))
     (16 16 (:REWRITE |(equal c (- x))|))
     (16 16 (:REWRITE |(equal (/ x) c)|))
     (16 16 (:REWRITE |(equal (/ x) (/ y))|))
     (16 16 (:REWRITE |(equal (- x) c)|))
     (16 16 (:REWRITE |(equal (- x) (- y))|))
     (7 7 (:REWRITE |(equal x (if a b c))|))
     (7 7 (:REWRITE |(equal (if a b c) x)|))
     (3 3 (:REWRITE |(equal (+ (- c) x) y)|))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(FM9001::V-IFF-REV (744 378 (:REWRITE DEFAULT-CDR))
                   (608 242 (:REWRITE DEFAULT-CAR))
                   (212 106 (:REWRITE DEFAULT-PLUS-2))
                   (192 96
                        (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
                   (176 16 (:DEFINITION BINARY-APPEND))
                   (167 69
                        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                   (167 69
                        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                   (166 69 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                   (106 106 (:REWRITE DEFAULT-PLUS-1))
                   (96 96 (:TYPE-PRESCRIPTION BINARY-APPEND))
                   (82 82
                       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                   (82 82 (:REWRITE NORMALIZE-ADDENDS))
                   (73 73
                       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                   (69 69
                       (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
                   (69 69 (:REWRITE |(equal c (/ x))|))
                   (69 69 (:REWRITE |(equal c (- x))|))
                   (69 69 (:REWRITE |(equal (/ x) c)|))
                   (69 69 (:REWRITE |(equal (/ x) (/ y))|))
                   (69 69 (:REWRITE |(equal (- x) c)|))
                   (69 69 (:REWRITE |(equal (- x) (- y))|))
                   (5 5 (:REWRITE |(equal x (if a b c))|))
                   (5 5 (:REWRITE |(equal (if a b c) x)|))
                   (2 2 (:REWRITE |(equal (+ (- c) x) y)|))
                   (1 1
                      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(FM9001::V-IFF=EQUAL (84 16
                         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                     (66 18 (:REWRITE ACL2-NUMBERP-X))
                     (56 56 (:REWRITE DEFAULT-CAR))
                     (51 51 (:REWRITE DEFAULT-CDR))
                     (49 25 (:REWRITE DEFAULT-PLUS-2))
                     (36 16 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                     (36 16
                         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                     (25 25
                         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                     (25 25 (:REWRITE NORMALIZE-ADDENDS))
                     (25 25 (:REWRITE DEFAULT-PLUS-1))
                     (24 6 (:REWRITE RATIONALP-X))
                     (16 16
                         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                     (16 16
                         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
                     (16 16
                         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
                     (16 16 (:REWRITE |(equal c (/ x))|))
                     (16 16 (:REWRITE |(equal c (- x))|))
                     (16 16 (:REWRITE |(equal (/ x) c)|))
                     (16 16 (:REWRITE |(equal (/ x) (/ y))|))
                     (16 16 (:REWRITE |(equal (- x) c)|))
                     (16 16 (:REWRITE |(equal (- x) (- y))|))
                     (6 6 (:REWRITE REDUCE-RATIONALP-+))
                     (6 6 (:REWRITE REDUCE-RATIONALP-*))
                     (6 6 (:REWRITE REDUCE-INTEGERP-+))
                     (6 6 (:REWRITE RATIONALP-MINUS-X))
                     (6 6 (:REWRITE INTEGERP-MINUS-X))
                     (6 6 (:META META-RATIONALP-CORRECT))
                     (6 6 (:META META-INTEGERP-CORRECT))
                     (3 3 (:REWRITE |(equal (+ (- c) x) y)|)))
(FM9001::BVP-SUBSEQ
     (4075 6 (:DEFINITION TAKE))
     (3356 12 (:REWRITE TAKE-OF-TOO-MANY))
     (2624 24 (:REWRITE |(< (if a b c) x)|))
     (1396 12 (:DEFINITION NFIX))
     (1388 12 (:REWRITE TAKE-OF-LEN-FREE))
     (1293 83 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (974 10 (:REWRITE |(equal (if a b c) x)|))
     (951 15 (:REWRITE ZP-OPEN))
     (908 22 (:REWRITE |(< (+ (- c) x) y)|))
     (837 9 (:REWRITE |(< x (if a b c))|))
     (810 112
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (754 40 (:REWRITE |(equal (+ (- c) x) y)|))
     (630 41
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (471 301 (:REWRITE DEFAULT-PLUS-2))
     (442 145 (:REWRITE NORMALIZE-ADDENDS))
     (411 12 (:REWRITE FM9001::NTHCDR-OF-LEN-L))
     (339 3 (:REWRITE DEFAULT-COERCE-3))
     (330 3 (:REWRITE CONSP-OF-TAKE))
     (324 36 (:DEFINITION LEN))
     (273 6 (:DEFINITION NTHCDR))
     (224 16 (:REWRITE |(+ y (+ x z))|))
     (203 145 (:REWRITE DEFAULT-LESS-THAN-1))
     (203 87 (:REWRITE |(< (- x) c)|))
     (190 125
          (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
     (183 90 (:REWRITE |(< c (- x))|))
     (156 26 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
     (150 83
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (146 146 (:REWRITE THE-FLOOR-BELOW))
     (146 146 (:REWRITE THE-FLOOR-ABOVE))
     (144 32 (:REWRITE ACL2-NUMBERP-X))
     (136 56
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (118 60 (:REWRITE |(+ c (+ d x))|))
     (115 115
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (112 112
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (112 112
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (100 41
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (95 63 (:REWRITE SIMPLIFY-SUMS-<))
     (90 90
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (90 90
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (90 90
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (90 90
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (90 90
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (90 90
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (90 90
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (90 90
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (90 90 (:REWRITE |(< (/ x) (/ y))|))
     (90 90 (:REWRITE |(< (- x) (- y))|))
     (87 60 (:REWRITE DEFAULT-CDR))
     (85 83 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (83 83 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (83 83
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (83 83 (:REWRITE INTEGERP-<-CONSTANT))
     (83 83 (:REWRITE CONSTANT-<-INTEGERP))
     (72 31 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (66 12 (:REWRITE TAKE-WHEN-ATOM))
     (63 9 (:REWRITE FM9001::BVP-IS-TRUE-LISTP))
     (60 60 (:DEFINITION FIX))
     (56 56
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (56 14 (:REWRITE RATIONALP-X))
     (54 54 (:TYPE-PRESCRIPTION NFIX))
     (45 3 (:DEFINITION TRUE-LISTP))
     (42 15 (:REWRITE DEFAULT-CAR))
     (41 41
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (41 41 (:REWRITE |(equal c (/ x))|))
     (41 41 (:REWRITE |(equal c (- x))|))
     (41 41 (:REWRITE |(equal (/ x) c)|))
     (41 41 (:REWRITE |(equal (/ x) (/ y))|))
     (41 41 (:REWRITE |(equal (- x) c)|))
     (41 41 (:REWRITE |(equal (- x) (- y))|))
     (35 35 (:REWRITE REDUCE-INTEGERP-+))
     (35 35 (:REWRITE INTEGERP-MINUS-X))
     (35 35 (:META META-INTEGERP-CORRECT))
     (32 32 (:REWRITE |(< (+ c/d x) y)|))
     (30 30 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (30 30 (:REWRITE |(+ x (- x))|))
     (29 29 (:REWRITE |(< 0 (* x y))|))
     (28 28 (:REWRITE |(< x (+ c/d y))|))
     (27 27 (:REWRITE |(< 0 (/ x))|))
     (26 26 (:REWRITE |(< y (+ (- c) x))|))
     (24 24 (:REWRITE |(< (* x y) 0)|))
     (20 20 (:REWRITE FOLD-CONSTS-IN-+))
     (18 18 (:TYPE-PRESCRIPTION TRUE-LISTP-TAKE))
     (18 18
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (18 18
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (16 2 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (14 14 (:REWRITE REDUCE-RATIONALP-+))
     (14 14 (:REWRITE REDUCE-RATIONALP-*))
     (14 14 (:REWRITE RATIONALP-MINUS-X))
     (14 14 (:REWRITE |(< (/ x) 0)|))
     (14 14 (:META META-RATIONALP-CORRECT))
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (8 4 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
     (8 2 (:REWRITE |(integerp (- x))|))
     (7 7 (:REWRITE DEFAULT-COERCE-2))
     (7 7 (:REWRITE |(- (- x))|))
     (6 6 (:TYPE-PRESCRIPTION BOOLEANP))
     (4 4 (:REWRITE DEFAULT-COERCE-1))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(FM9001::LEN-SUBSEQ-LIST
     (1158 17 (:REWRITE |(< (if a b c) x)|))
     (1144 1 (:DEFINITION TAKE))
     (910 2 (:REWRITE TAKE-OF-TOO-MANY))
     (744 4 (:DEFINITION NFIX))
     (421 29 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (383 2 (:REWRITE TAKE-OF-LEN-FREE))
     (353 6 (:REWRITE |(equal (if a b c) x)|))
     (284 8 (:REWRITE |(< (+ (- c) x) y)|))
     (257 41
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (204 10 (:REWRITE |(equal (+ (- c) x) y)|))
     (178 10
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (178 2 (:REWRITE ZP-OPEN))
     (168 3 (:REWRITE |(< x (if a b c))|))
     (153 33 (:REWRITE |(< (- x) c)|))
     (126 95 (:REWRITE DEFAULT-PLUS-2))
     (122 38 (:REWRITE NORMALIZE-ADDENDS))
     (86 6 (:REWRITE |(+ y (+ x z))|))
     (79 61 (:REWRITE DEFAULT-LESS-THAN-2))
     (72 8 (:REWRITE ACL2-NUMBERP-X))
     (65 34 (:REWRITE |(< c (- x))|))
     (62 61 (:REWRITE DEFAULT-LESS-THAN-1))
     (61 61 (:REWRITE THE-FLOOR-BELOW))
     (61 61 (:REWRITE THE-FLOOR-ABOVE))
     (54 14
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (44 4 (:DEFINITION LEN))
     (41 41
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (41 41
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (40 20
         (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
     (40 8 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
     (39 29
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (39 20 (:REWRITE |(+ c (+ d x))|))
     (34 34
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (34 34
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (34 34
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (34 34
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (34 34
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (34 34
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (34 34
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (34 34
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (34 34 (:REWRITE |(< (/ x) (/ y))|))
     (34 34 (:REWRITE |(< (- x) (- y))|))
     (32 8 (:REWRITE RATIONALP-X))
     (30 30 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (29 29 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (29 29
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (29 29 (:REWRITE INTEGERP-<-CONSTANT))
     (29 29 (:REWRITE CONSTANT-<-INTEGERP))
     (28 28
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (28 2 (:REWRITE FM9001::NTHCDR-OF-LEN-L))
     (26 22 (:REWRITE SIMPLIFY-SUMS-<))
     (24 1 (:DEFINITION NTHCDR))
     (20 20 (:DEFINITION FIX))
     (20 10
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (16 2 (:DEFINITION TRUE-LISTP))
     (14 14
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (14 8 (:REWRITE DEFAULT-CDR))
     (14 2 (:REWRITE TAKE-WHEN-ATOM))
     (13 13 (:REWRITE REDUCE-INTEGERP-+))
     (13 13 (:REWRITE INTEGERP-MINUS-X))
     (13 13 (:REWRITE |(< (* x y) 0)|))
     (13 13 (:META META-INTEGERP-CORRECT))
     (12 7 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (12 4 (:REWRITE FM9001::BVP-IS-TRUE-LISTP))
     (11 11 (:REWRITE |(< (+ c/d x) y)|))
     (10 10 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (10 10
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (10 10 (:REWRITE |(equal c (/ x))|))
     (10 10 (:REWRITE |(equal c (- x))|))
     (10 10 (:REWRITE |(equal (/ x) c)|))
     (10 10 (:REWRITE |(equal (/ x) (/ y))|))
     (10 10 (:REWRITE |(equal (- x) c)|))
     (10 10 (:REWRITE |(equal (- x) (- y))|))
     (10 10 (:REWRITE |(< (/ x) 0)|))
     (10 10 (:REWRITE |(+ x (- x))|))
     (9 9 (:REWRITE |(< 0 (* x y))|))
     (8 8 (:TYPE-PRESCRIPTION FM9001::BVP))
     (8 8 (:REWRITE REDUCE-RATIONALP-+))
     (8 8 (:REWRITE REDUCE-RATIONALP-*))
     (8 8 (:REWRITE RATIONALP-MINUS-X))
     (8 8 (:REWRITE |(< x (+ c/d y))|))
     (8 8 (:REWRITE |(< 0 (/ x))|))
     (8 8 (:META META-RATIONALP-CORRECT))
     (7 7 (:REWRITE FOLD-CONSTS-IN-+))
     (7 7 (:REWRITE |(< y (+ (- c) x))|))
     (7 1 (:REWRITE DEFAULT-CAR))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (5 5 (:REWRITE |(- (- x))|))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (4 2 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (1 1 (:DEFINITION NOT)))
(FM9001::BOOLEANP-IF*)
(FM9001::TRUE-LISTP-IF* (6 3
                           (:TYPE-PRESCRIPTION FM9001::BOOLEANP-IF*))
                        (3 3 (:TYPE-PRESCRIPTION BOOLEANP)))
(FM9001::BVP-IF*)
(FM9001::LEN-IF* (28 4 (:DEFINITION LEN))
                 (8 4 (:REWRITE DEFAULT-PLUS-2))
                 (6 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                 (6 2
                    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                 (6 2
                    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                 (4 4
                    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                 (4 4 (:REWRITE NORMALIZE-ADDENDS))
                 (4 4 (:REWRITE DEFAULT-PLUS-1))
                 (4 4 (:REWRITE DEFAULT-CDR))
                 (2 2
                    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                 (2 2
                    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
                 (2 2
                    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
                 (2 2 (:REWRITE |(equal c (/ x))|))
                 (2 2 (:REWRITE |(equal c (- x))|))
                 (2 2 (:REWRITE |(equal (/ x) c)|))
                 (2 2 (:REWRITE |(equal (/ x) (/ y))|))
                 (2 2 (:REWRITE |(equal (- x) c)|))
                 (2 2 (:REWRITE |(equal (- x) (- y))|)))
(FM9001::IF*-REWRITE (60 30
                         (:TYPE-PRESCRIPTION FM9001::TRUE-LISTP-IF*))
                     (60 30
                         (:TYPE-PRESCRIPTION FM9001::BOOLEANP-IF*))
                     (30 30 (:TYPE-PRESCRIPTION TRUE-LISTP))
                     (30 30 (:TYPE-PRESCRIPTION IF*))
                     (30 30 (:TYPE-PRESCRIPTION BOOLEANP)))
