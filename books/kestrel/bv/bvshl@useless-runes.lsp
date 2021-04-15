(BVSHL)
(BVSHL-OF-0-ARG1 (3 1 (:REWRITE BVCHOP-IDENTITY))
                 (2 2 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
                 (2 1
                    (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
                 (1 1 (:TYPE-PRESCRIPTION POSP))
                 (1 1 (:REWRITE DEFAULT-UNARY-MINUS))
                 (1 1 (:REWRITE DEFAULT-<-2))
                 (1 1 (:REWRITE DEFAULT-<-1))
                 (1 1 (:REWRITE DEFAULT-+-2))
                 (1 1 (:REWRITE DEFAULT-+-1))
                 (1 1
                    (:REWRITE BVCHOP-WHEN-TOP-BIT-NOT-1-FAKE-FREE))
                 (1 1
                    (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
                 (1 1
                    (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
                 (1 1 (:REWRITE BVCHOP-SUBST-CONSTANT))
                 (1 1
                    (:REWRITE BVCAT-WHEN-ARG2-IS-NOT-AN-INTEGER))
                 (1 1 (:REWRITE BVCAT-FIX-CONSTANT-ARG4))
                 (1 1 (:REWRITE BVCAT-FIX-CONSTANT-ARG2)))
(BVSHL-OF-0-ARG2 (6 2 (:DEFINITION POSP))
                 (5 1
                    (:REWRITE BVCAT-WHEN-LOWSIZE-IS-NOT-POSP))
                 (5 1
                    (:REWRITE BVCAT-WHEN-HIGHSIZE-IS-NOT-POSP))
                 (3 3
                    (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                 (3 2 (:REWRITE DEFAULT-+-2))
                 (3 2 (:REWRITE DEFAULT-+-1))
                 (2 2 (:TYPE-PRESCRIPTION POSP))
                 (2 2 (:REWRITE DEFAULT-<-2))
                 (2 2 (:REWRITE DEFAULT-<-1))
                 (2 1 (:REWRITE DEFAULT-UNARY-MINUS))
                 (1 1
                    (:REWRITE BVCAT-WHEN-ARG2-IS-NOT-AN-INTEGER))
                 (1 1 (:REWRITE BVCAT-FIX-CONSTANT-ARG4))
                 (1 1 (:REWRITE BVCAT-FIX-CONSTANT-ARG2)))
(BVSHL-OF-0-ARG3
     (22 1 (:DEFINITION EXPT))
     (11 11 (:TYPE-PRESCRIPTION NATP))
     (11 3 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
     (10 8 (:REWRITE DEFAULT-<-2))
     (10 3 (:DEFINITION NATP))
     (9 3 (:REWRITE BVCHOP-IDENTITY))
     (8 8 (:REWRITE DEFAULT-<-1))
     (7 7 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
     (7 6 (:REWRITE DEFAULT-+-2))
     (7 6 (:REWRITE DEFAULT-+-1))
     (7 1
        (:REWRITE EQUAL-OF-BVCHOP-AND-BVCHOP-SAME))
     (7 1
        (:REWRITE BVCAT-WHEN-HIGHSIZE-IS-NOT-POSP))
     (6 6 (:TYPE-PRESCRIPTION POSP))
     (6 3
        (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
     (6 3
        (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
     (6 3
        (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
     (6 2 (:REWRITE DEFAULT-*-2))
     (5 5
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (5 1
        (:LINEAR BVCHOP-UPPER-BOUND-LINEAR-STRONG))
     (5 1 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR))
     (4 1 (:DEFINITION POSP))
     (3 3
        (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
     (3 3
        (:REWRITE BVCHOP-WHEN-TOP-BIT-NOT-1-FAKE-FREE))
     (3 3
        (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
     (3 3
        (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
     (3 3 (:REWRITE BVCHOP-SUBST-CONSTANT))
     (2 2 (:REWRITE DEFAULT-*-1))
     (2 2 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR-2))
     (2 1 (:REWRITE BVCAT-FIX-CONSTANT-ARG4))
     (1 1 (:REWRITE ZIP-OPEN))
     (1 1
        (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
     (1 1 (:REWRITE BVCHOP-IMPOSSIBLE-VALUE))
     (1 1
        (:REWRITE BVCAT-WHEN-ARG2-IS-NOT-AN-INTEGER))
     (1 1 (:REWRITE BVCAT-FIX-CONSTANT-ARG2)))
(BVSHL-OF-BVCHOP (12 4 (:DEFINITION POSP))
                 (11 3
                     (:REWRITE BVCAT-WHEN-LOWSIZE-IS-NOT-POSP))
                 (11 3
                     (:REWRITE BVCAT-WHEN-HIGHSIZE-IS-NOT-POSP))
                 (9 9 (:REWRITE DEFAULT-<-2))
                 (9 9 (:REWRITE DEFAULT-<-1))
                 (4 4 (:TYPE-PRESCRIPTION POSP))
                 (4 4 (:REWRITE DEFAULT-+-2))
                 (4 4 (:REWRITE DEFAULT-+-1))
                 (4 3
                    (:REWRITE BVCAT-WHEN-HIGHVAL-IS-NOT-AN-INTEGER))
                 (3 3
                    (:REWRITE BVCAT-WHEN-LOWVAL-IS-NOT-AN-INTEGER))
                 (3 3
                    (:REWRITE BVCAT-WHEN-ARG2-IS-NOT-AN-INTEGER))
                 (3 3 (:REWRITE BVCAT-FIX-CONSTANT-ARG4))
                 (3 3 (:REWRITE BVCAT-FIX-CONSTANT-ARG2))
                 (3 1 (:REWRITE BVCHOP-IDENTITY))
                 (3 1 (:REWRITE BVCAT-OF-BVCHOP-TIGHTEN))
                 (3 1
                    (:REWRITE BVCAT-OF-BVCHOP-HIGH-TIGHTEN))
                 (2 2 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
                 (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
                 (1 1 (:TYPE-PRESCRIPTION NATP-OF-BVCHOP))
                 (1 1
                    (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
                 (1 1 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
                 (1 1
                    (:REWRITE BVCHOP-WHEN-TOP-BIT-NOT-1-FAKE-FREE))
                 (1 1
                    (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
                 (1 1
                    (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
                 (1 1
                    (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
                 (1 1
                    (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
                 (1 1
                    (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
                 (1 1 (:REWRITE BVCHOP-SUBST-CONSTANT)))
(INTEGERP-OF-BVSHL)
(NATP-OF-BVSHL)
(UNSIGNED-BYTE-P-OF-BVSHL (6 2 (:DEFINITION POSP))
                          (5 1
                             (:REWRITE BVCAT-WHEN-LOWSIZE-IS-NOT-POSP))
                          (5 1
                             (:REWRITE BVCAT-WHEN-HIGHSIZE-IS-NOT-POSP))
                          (4 4 (:REWRITE DEFAULT-<-2))
                          (4 4 (:REWRITE DEFAULT-<-1))
                          (3 3 (:REWRITE DEFAULT-+-2))
                          (3 3 (:REWRITE DEFAULT-+-1))
                          (2 2 (:TYPE-PRESCRIPTION POSP))
                          (1 1 (:REWRITE FOLD-CONSTS-IN-+))
                          (1 1 (:REWRITE DEFAULT-UNARY-MINUS))
                          (1 1
                             (:REWRITE BVCAT-WHEN-LOWVAL-IS-NOT-AN-INTEGER))
                          (1 1
                             (:REWRITE BVCAT-WHEN-HIGHVAL-IS-NOT-AN-INTEGER))
                          (1 1
                             (:REWRITE BVCAT-WHEN-ARG2-IS-NOT-AN-INTEGER))
                          (1 1 (:REWRITE BVCAT-FIX-CONSTANT-ARG4))
                          (1 1 (:REWRITE BVCAT-FIX-CONSTANT-ARG2)))
