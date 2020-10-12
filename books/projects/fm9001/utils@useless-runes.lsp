(FM9001::TRUE-LIST-ALISTP)
(FM9001::DELETE-TO-EQ (2 2 (:REWRITE DEFAULT-CAR))
                      (1 1 (:REWRITE DEFAULT-CDR)))
(FM9001::UPDATE-ALIST (2 2 (:REWRITE DEFAULT-CAR))
                      (1 1 (:REWRITE DEFAULT-CDR)))
(FM9001::SYMBOL-ALISTP-UPDATE-ALIST (52 50 (:REWRITE DEFAULT-CAR))
                                    (13 12 (:REWRITE DEFAULT-CDR)))
(FM9001::CONSP-OF-ASSOC-UPDATE-ALIST-LEMMA (137 124 (:REWRITE DEFAULT-CAR))
                                           (49 46 (:REWRITE DEFAULT-CDR)))
(FM9001::STRIP-CARS-UPDATE-ALIST (36 35 (:REWRITE DEFAULT-CAR))
                                 (13 12 (:REWRITE DEFAULT-CDR)))
(FM9001::UPDATE-ALIST-DIFF-KEYS (149 139 (:REWRITE DEFAULT-CAR))
                                (78 72 (:REWRITE DEFAULT-CDR)))
(FM9001::OPEN-LEN (10 5 (:REWRITE DEFAULT-+-2))
                  (8 8 (:LINEAR LEN-WHEN-PREFIXP))
                  (5 5 (:REWRITE DEFAULT-CDR))
                  (5 5 (:REWRITE DEFAULT-+-1)))
(FM9001::OPEN-NTH (10 4 (:REWRITE ZP-OPEN))
                  (6 2 (:REWRITE FOLD-CONSTS-IN-+))
                  (5 5 (:REWRITE NTH-WHEN-PREFIXP))
                  (5 5 (:REWRITE DEFAULT-CDR))
                  (5 5 (:REWRITE DEFAULT-+-2))
                  (5 5 (:REWRITE DEFAULT-+-1))
                  (4 4 (:REWRITE DEFAULT-CAR))
                  (2 2 (:REWRITE DEFAULT-<-2))
                  (2 2 (:REWRITE DEFAULT-<-1)))
(FM9001::SYMBOL-LISTP-APPEND (30 13 (:REWRITE DEFAULT-CDR))
                             (21 19 (:REWRITE DEFAULT-CAR))
                             (9 3 (:REWRITE CAR-OF-APPEND))
                             (6 6 (:REWRITE CONSP-OF-APPEND))
                             (5 5 (:TYPE-PRESCRIPTION TRUE-LISTP))
                             (3 3 (:REWRITE CDR-OF-APPEND-WHEN-CONSP)))
(FM9001::SYMBOL-LISTP-REMOVE-DUPLICATES-EQ (32 31 (:REWRITE DEFAULT-CAR))
                                           (29 28 (:REWRITE DEFAULT-CDR)))
(FM9001::TRUE-LISTP-UNION-LEMMA (21 21 (:REWRITE DEFAULT-CDR))
                                (15 15 (:REWRITE DEFAULT-CAR)))
(FM9001::NOT-MEMBER-APPEND (37 13 (:REWRITE DEFAULT-CDR))
                           (30 15
                               (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
                           (22 19 (:REWRITE DEFAULT-CAR))
                           (15 15 (:TYPE-PRESCRIPTION TRUE-LISTP))
                           (15 15 (:TYPE-PRESCRIPTION BINARY-APPEND))
                           (9 3 (:REWRITE CAR-OF-APPEND))
                           (6 6 (:REWRITE CONSP-OF-APPEND))
                           (5 5
                              (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
                           (3 3 (:REWRITE CDR-OF-APPEND-WHEN-CONSP)))
(FM9001::NOT-MEMBER=>NOT-EQUAL-NTH
     (29 17 (:REWRITE DEFAULT-<-1))
     (25 17 (:REWRITE DEFAULT-<-2))
     (22 22 (:REWRITE DEFAULT-CAR))
     (22 13 (:REWRITE DEFAULT-+-2))
     (18 18 (:LINEAR LEN-WHEN-PREFIXP))
     (13 13 (:REWRITE DEFAULT-+-1))
     (12 12
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (10 10 (:REWRITE ZP-OPEN))
     (10 10 (:REWRITE NTH-WHEN-PREFIXP))
     (9 9 (:REWRITE DEFAULT-CDR)))
(FM9001::SUBSETP=>MEMBER-NTH
     (28 4
         (:REWRITE FM9001::NOT-MEMBER=>NOT-EQUAL-NTH))
     (23 15 (:REWRITE DEFAULT-<-2))
     (23 15 (:REWRITE DEFAULT-<-1))
     (22 22 (:REWRITE DEFAULT-CAR))
     (20 20 (:LINEAR LEN-WHEN-PREFIXP))
     (18 18 (:REWRITE DEFAULT-CDR))
     (15 9 (:REWRITE DEFAULT-+-2))
     (9 9 (:REWRITE DEFAULT-+-1))
     (8 8
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (6 6 (:REWRITE ZP-OPEN))
     (4 4 (:REWRITE NTH-WHEN-PREFIXP)))
(FM9001::PAIR-WITH-NIL)
(FM9001::PAIRS)
(FM9001::PAIRS-IS-PAIRLIS$)
(FM9001::ALISTP-PAIRLIS$ (11 10 (:REWRITE DEFAULT-CAR))
                         (9 8 (:REWRITE DEFAULT-CDR)))
(FM9001::LEN-PAIRLIS$ (28 28 (:LINEAR LEN-WHEN-PREFIXP))
                      (14 7 (:REWRITE DEFAULT-+-2))
                      (11 10 (:REWRITE DEFAULT-CDR))
                      (7 7 (:REWRITE DEFAULT-+-1))
                      (6 6 (:REWRITE DEFAULT-CAR)))
(FM9001::ALISTP-DELETE-TO-EQ (25 25 (:REWRITE DEFAULT-CAR))
                             (12 12 (:REWRITE DEFAULT-CDR)))
(FM9001::SYMBOL-ALISTP-PAIRLIS$ (24 22 (:REWRITE DEFAULT-CAR))
                                (11 10 (:REWRITE DEFAULT-CDR)))
(FM9001::PAIRLIS$-APPEND (121 48 (:REWRITE DEFAULT-CDR))
                         (81 64 (:REWRITE DEFAULT-CAR))
                         (30 30 (:TYPE-PRESCRIPTION TRUE-LISTP))
                         (26 26 (:LINEAR LEN-WHEN-PREFIXP))
                         (24 8 (:REWRITE CAR-OF-APPEND))
                         (20 10 (:REWRITE DEFAULT-+-2))
                         (12 12 (:REWRITE CONSP-OF-APPEND))
                         (10 10 (:REWRITE DEFAULT-+-1))
                         (8 8 (:REWRITE CDR-OF-APPEND-WHEN-CONSP)))
(FM9001::ALISTP-APPEND (30 13 (:REWRITE DEFAULT-CDR))
                       (21 19 (:REWRITE DEFAULT-CAR))
                       (9 3 (:REWRITE CAR-OF-APPEND))
                       (6 6 (:REWRITE CONSP-OF-APPEND))
                       (5 5 (:TYPE-PRESCRIPTION TRUE-LISTP))
                       (3 3 (:REWRITE CDR-OF-APPEND-WHEN-CONSP)))
(FM9001::ALISTP-APPEND-TWO-PAIRLIS$)
(FM9001::SYMBOL-ALISTP-APPEND (52 48 (:REWRITE DEFAULT-CAR))
                              (30 13 (:REWRITE DEFAULT-CDR))
                              (18 6 (:REWRITE CAR-OF-APPEND))
                              (6 6 (:REWRITE CONSP-OF-APPEND))
                              (5 5 (:TYPE-PRESCRIPTION TRUE-LISTP))
                              (3 3 (:REWRITE CDR-OF-APPEND-WHEN-CONSP)))
(FM9001::SYMBOL-ALISTP-APPEND-TWO-PAIRLIS$)
(FM9001::STRIP-CARS-OF-SYMBOL-ALIST-IS-SYMBOL-LISTP
     (25 23 (:REWRITE DEFAULT-CAR))
     (12 10 (:REWRITE DEFAULT-CDR)))
(FM9001::STRIP-CARS-PAIRLIS$ (15 14 (:REWRITE DEFAULT-CAR))
                             (12 11 (:REWRITE DEFAULT-CDR)))
(FM9001::STRIP-CDRS-PAIRLIS$ (28 25 (:REWRITE DEFAULT-CDR))
                             (26 26 (:LINEAR LEN-WHEN-PREFIXP))
                             (20 17 (:REWRITE DEFAULT-CAR))
                             (20 10 (:REWRITE DEFAULT-+-2))
                             (10 10 (:REWRITE DEFAULT-+-1)))
(FM9001::LEN-STRIP-CARS (28 28 (:LINEAR LEN-WHEN-PREFIXP))
                        (14 7 (:REWRITE DEFAULT-+-2))
                        (9 8 (:REWRITE DEFAULT-CDR))
                        (7 7 (:REWRITE DEFAULT-+-1))
                        (6 6 (:REWRITE DEFAULT-CAR)))
(FM9001::NTHCDR-APPEND-INDUCT (10 5
                                  (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
                              (5 5 (:TYPE-PRESCRIPTION TRUE-LISTP)))
(FM9001::NTHCDR-APPEND (297 297 (:TYPE-PRESCRIPTION BINARY-APPEND))
                       (81 60 (:REWRITE DEFAULT-+-2))
                       (73 46 (:REWRITE DEFAULT-CDR))
                       (60 60 (:REWRITE DEFAULT-+-1))
                       (18 18 (:LINEAR LEN-WHEN-PREFIXP))
                       (13 9 (:REWRITE DEFAULT-<-2))
                       (12 12 (:REWRITE DEFAULT-CAR))
                       (9 9 (:REWRITE DEFAULT-<-1))
                       (5 3 (:REWRITE DEFAULT-UNARY-MINUS))
                       (3 3
                          (:TYPE-PRESCRIPTION FM9001::NTHCDR-APPEND-INDUCT))
                       (3 3 (:REWRITE CONSP-OF-APPEND))
                       (3 3 (:REWRITE CDR-OF-APPEND-WHEN-CONSP)))
(FM9001::BINARY-AND*)
(FM9001::BOOLEANP-BINARY-AND*)
(FM9001::AND*-MACRO)
(FM9001::BINARY-OR*)
(FM9001::BOOLEANP-BINARY-OR*)
(FM9001::OR*-MACRO)
(FM9001::NOT*)
(FM9001::BOOLEANP-NOT*)
(FM9001::DISJOINT)
(FM9001::DISJOINT-ATOM (6 6 (:REWRITE DEFAULT-CAR))
                       (3 3 (:REWRITE DEFAULT-CDR)))
(FM9001::DISJOINT-CONS (95 95 (:REWRITE DEFAULT-CAR))
                       (64 64 (:REWRITE DEFAULT-CDR))
                       (20 20 (:TYPE-PRESCRIPTION ATOM)))
(FM9001::DISJOINT-APPEND (942 471
                              (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
                         (690 389 (:REWRITE DEFAULT-CDR))
                         (471 471 (:TYPE-PRESCRIPTION TRUE-LISTP))
                         (471 471 (:TYPE-PRESCRIPTION BINARY-APPEND))
                         (422 422 (:REWRITE DEFAULT-CAR))
                         (227 227 (:TYPE-PRESCRIPTION ATOM))
                         (225 25 (:REWRITE FM9001::NOT-MEMBER-APPEND))
                         (43 43 (:REWRITE CDR-OF-APPEND-WHEN-CONSP)))
(FM9001::DISJOINT=>NOT-MEMBER-NTH
     (116 8
          (:REWRITE FM9001::SUBSETP=>MEMBER-NTH))
     (92 8 (:DEFINITION SUBSETP-EQUAL))
     (40 40 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (34 34 (:REWRITE DEFAULT-CAR))
     (30 30 (:REWRITE DEFAULT-CDR))
     (28 4
         (:REWRITE FM9001::NOT-MEMBER=>NOT-EQUAL-NTH))
     (23 15 (:REWRITE DEFAULT-<-2))
     (23 15 (:REWRITE DEFAULT-<-1))
     (20 20 (:LINEAR LEN-WHEN-PREFIXP))
     (15 9 (:REWRITE DEFAULT-+-2))
     (12 12 (:DEFINITION ATOM))
     (9 9 (:REWRITE DEFAULT-+-1))
     (8 8 (:TYPE-PRESCRIPTION ATOM))
     (8 8
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (6 6 (:REWRITE ZP-OPEN))
     (4 4 (:REWRITE NTH-WHEN-PREFIXP)))
(FM9001::OPEN-TAKE (117 7 (:REWRITE TAKE-OF-LEN-FREE))
                   (51 51 (:TYPE-PRESCRIPTION LEN))
                   (44 8 (:DEFINITION LEN))
                   (24 24 (:LINEAR LEN-WHEN-PREFIXP))
                   (23 14 (:REWRITE DEFAULT-+-2))
                   (14 14 (:REWRITE DEFAULT-CDR))
                   (14 14 (:REWRITE DEFAULT-+-1))
                   (10 4 (:REWRITE ZP-OPEN))
                   (6 2 (:REWRITE FOLD-CONSTS-IN-+))
                   (5 5 (:REWRITE DEFAULT-CAR))
                   (2 2 (:REWRITE DEFAULT-<-2))
                   (2 2 (:REWRITE DEFAULT-<-1)))
(FM9001::OPEN-NTHCDR (10 4 (:REWRITE ZP-OPEN))
                     (8 8 (:REWRITE DEFAULT-+-2))
                     (8 8 (:REWRITE DEFAULT-+-1))
                     (6 2 (:REWRITE FOLD-CONSTS-IN-+))
                     (5 5 (:REWRITE DEFAULT-CDR))
                     (2 2 (:REWRITE DEFAULT-<-2))
                     (2 2 (:REWRITE DEFAULT-<-1)))
(FM9001::LEN-NTHCDR
     (100 57 (:REWRITE DEFAULT-+-2))
     (66 66 (:LINEAR LEN-WHEN-PREFIXP))
     (61 57 (:REWRITE DEFAULT-+-1))
     (28 17 (:REWRITE DEFAULT-<-1))
     (28 14
         (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
     (25 25 (:REWRITE DEFAULT-CDR))
     (19 17 (:REWRITE DEFAULT-<-2))
     (14 14 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (7 7 (:REWRITE DEFAULT-UNARY-MINUS))
     (6 6 (:REWRITE ZP-OPEN))
     (6 6 (:REWRITE FOLD-CONSTS-IN-+))
     (3 3
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP)))
(FM9001::CAR-NTHCDR (75 6
                        (:REWRITE FM9001::NOT-MEMBER=>NOT-EQUAL-NTH))
                    (47 14 (:REWRITE DEFAULT-CAR))
                    (38 32 (:REWRITE DEFAULT-+-2))
                    (32 32 (:REWRITE DEFAULT-+-1))
                    (32 14 (:REWRITE ZP-OPEN))
                    (29 5 (:DEFINITION LEN))
                    (26 26 (:TYPE-PRESCRIPTION LEN))
                    (18 6 (:REWRITE FOLD-CONSTS-IN-+))
                    (16 12 (:REWRITE DEFAULT-<-2))
                    (14 12 (:REWRITE DEFAULT-<-1))
                    (11 11 (:REWRITE NTH-WHEN-PREFIXP))
                    (6 6 (:LINEAR LEN-WHEN-PREFIXP))
                    (2 2
                       (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP)))
(FM9001::CDR-NTHCDR (33 33 (:REWRITE DEFAULT-+-2))
                    (33 33 (:REWRITE DEFAULT-+-1))
                    (19 16 (:REWRITE ZP-OPEN))
                    (10 10 (:REWRITE DEFAULT-<-2))
                    (10 10 (:REWRITE DEFAULT-<-1)))
(FM9001::APPEND-TAKE-NTHCDR (342 114 (:TYPE-PRESCRIPTION BINARY-APPEND))
                            (83 7 (:REWRITE TAKE-OF-LEN-FREE))
                            (41 28 (:REWRITE DEFAULT-+-2))
                            (32 20 (:REWRITE DEFAULT-CDR))
                            (28 28 (:REWRITE DEFAULT-+-1))
                            (28 22 (:REWRITE DEFAULT-<-1))
                            (25 22 (:REWRITE DEFAULT-<-2))
                            (24 24 (:LINEAR LEN-WHEN-PREFIXP))
                            (7 7 (:REWRITE DEFAULT-CAR))
                            (6 2 (:REWRITE FOLD-CONSTS-IN-+))
                            (3 3
                               (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP)))
(FM9001::NOT-MEMBER-TAKE-LEMMA (86 8 (:REWRITE TAKE-OF-LEN-FREE))
                               (29 16 (:REWRITE DEFAULT-+-2))
                               (26 26 (:LINEAR LEN-WHEN-PREFIXP))
                               (24 14 (:REWRITE DEFAULT-CDR))
                               (22 16 (:REWRITE DEFAULT-<-1))
                               (20 16 (:REWRITE DEFAULT-<-2))
                               (20 3 (:REWRITE CAR-OF-TAKE))
                               (17 6 (:REWRITE CONSP-OF-TAKE))
                               (16 16 (:REWRITE DEFAULT-+-1))
                               (15 14 (:REWRITE DEFAULT-CAR))
                               (12 9 (:REWRITE ZP-OPEN))
                               (9 3 (:DEFINITION NFIX))
                               (4 4
                                  (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                               (3 3 (:TYPE-PRESCRIPTION NFIX)))
(FM9001::NOT-MEMBER-NTHCDR-LEMMA (13 13 (:REWRITE DEFAULT-CAR))
                                 (6 6 (:REWRITE ZP-OPEN))
                                 (6 2 (:REWRITE COMMUTATIVITY-OF-+))
                                 (4 4 (:REWRITE DEFAULT-+-2))
                                 (4 4 (:REWRITE DEFAULT-+-1)))
(FM9001::SUBSETP-CONS (43 43 (:REWRITE DEFAULT-CAR))
                      (22 22 (:REWRITE DEFAULT-CDR)))
(FM9001::SUBSETP-IDENTITY (22 22 (:REWRITE DEFAULT-CAR))
                          (19 19 (:REWRITE DEFAULT-CDR)))
(FM9001::SUBSETP-TAKE (27 2 (:REWRITE TAKE-OF-LEN-FREE))
                      (25 5 (:DEFINITION LEN))
                      (22 1 (:DEFINITION TAKE))
                      (11 6 (:REWRITE DEFAULT-+-2))
                      (8 5 (:REWRITE DEFAULT-<-1))
                      (7 7 (:REWRITE DEFAULT-CDR))
                      (6 6 (:REWRITE DEFAULT-+-1))
                      (6 6 (:LINEAR LEN-WHEN-PREFIXP))
                      (6 5 (:REWRITE DEFAULT-<-2))
                      (3 1 (:DEFINITION MEMBER-EQUAL))
                      (2 2 (:REWRITE DEFAULT-CAR))
                      (1 1 (:REWRITE ZP-OPEN))
                      (1 1
                         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP)))
(FM9001::SUBSETP-NTHCDR (36 36 (:REWRITE DEFAULT-+-2))
                        (36 36 (:REWRITE DEFAULT-+-1))
                        (25 25 (:TYPE-PRESCRIPTION TRUE-LISTP))
                        (23 23 (:REWRITE DEFAULT-CAR))
                        (11 11 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
                        (10 10 (:REWRITE DEFAULT-<-2))
                        (10 10 (:REWRITE DEFAULT-<-1)))
(FM9001::SUBSETP-TRANSITIVITY (116 116 (:REWRITE DEFAULT-CAR))
                              (89 89 (:REWRITE DEFAULT-CDR)))
(FM9001::SUBSETP-TRANSITIVITY-TAKE-NTHCDR
     (1081 46 (:REWRITE TAKE-OF-LEN-FREE))
     (775 23 (:DEFINITION TAKE))
     (585 304
          (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
     (387 156 (:REWRITE DEFAULT-CAR))
     (378 213 (:REWRITE DEFAULT-CDR))
     (291 194 (:REWRITE DEFAULT-+-2))
     (230 19 (:REWRITE FM9001::LEN-NTHCDR))
     (222 222 (:LINEAR LEN-WHEN-PREFIXP))
     (212 194 (:REWRITE DEFAULT-+-1))
     (144 101 (:REWRITE DEFAULT-<-1))
     (124 82 (:REWRITE ZP-OPEN))
     (105 101 (:REWRITE DEFAULT-<-2))
     (44 16 (:REWRITE FOLD-CONSTS-IN-+))
     (28 28
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (25 2 (:REWRITE FM9001::SUBSETP-TAKE)))
(FM9001::DISJOINT-TAKE (206 16 (:REWRITE TAKE-OF-LEN-FREE))
                       (148 53 (:DEFINITION ATOM))
                       (81 46 (:REWRITE DEFAULT-+-2))
                       (73 16 (:REWRITE CONSP-OF-TAKE))
                       (62 29 (:REWRITE ZP-OPEN))
                       (58 58 (:LINEAR LEN-WHEN-PREFIXP))
                       (47 47 (:REWRITE DEFAULT-CDR))
                       (46 46 (:REWRITE DEFAULT-+-1))
                       (44 31 (:REWRITE DEFAULT-<-1))
                       (41 41 (:TYPE-PRESCRIPTION TRUE-LISTP-TAKE))
                       (34 31 (:REWRITE DEFAULT-<-2))
                       (26 26 (:TYPE-PRESCRIPTION ATOM))
                       (19 19 (:REWRITE DEFAULT-CAR))
                       (18 6 (:DEFINITION MEMBER-EQUAL))
                       (12 4 (:REWRITE FOLD-CONSTS-IN-+))
                       (3 3
                          (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP)))
(FM9001::DISJOINT-NTHCDR
     (96 48
         (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
     (90 42 (:DEFINITION ATOM))
     (48 48 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (21 21 (:TYPE-PRESCRIPTION ATOM))
     (21 12 (:REWRITE ZP-OPEN))
     (14 14 (:REWRITE DEFAULT-+-2))
     (14 14 (:REWRITE DEFAULT-+-1))
     (9 3 (:REWRITE FOLD-CONSTS-IN-+))
     (3 3 (:REWRITE DEFAULT-<-2))
     (3 3 (:REWRITE DEFAULT-<-1)))
(FM9001::NO-DUPLICATESP-TAKE-LEMMA
     (123 9 (:REWRITE TAKE-OF-LEN-FREE))
     (79 11 (:DEFINITION MEMBER-EQUAL))
     (66 52 (:REWRITE DEFAULT-CDR))
     (45 35 (:REWRITE DEFAULT-<-1))
     (45 26 (:REWRITE DEFAULT-+-2))
     (38 38 (:LINEAR LEN-WHEN-PREFIXP))
     (37 35 (:REWRITE DEFAULT-<-2))
     (29 28 (:REWRITE DEFAULT-CAR))
     (28 4 (:REWRITE CAR-OF-TAKE))
     (26 26 (:REWRITE DEFAULT-+-1))
     (26 8 (:REWRITE CONSP-OF-TAKE))
     (24 12 (:REWRITE ZP-OPEN))
     (21 3 (:REWRITE SECOND-OF-TAKE))
     (6 2 (:REWRITE FOLD-CONSTS-IN-+))
     (2 2
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP)))
(FM9001::NO-DUPLICATESP-NTHCDR-LEMMA (36 36 (:REWRITE DEFAULT-CDR))
                                     (26 26 (:REWRITE DEFAULT-CAR))
                                     (6 2 (:REWRITE COMMUTATIVITY-OF-+))
                                     (5 5 (:REWRITE ZP-OPEN))
                                     (4 4 (:REWRITE DEFAULT-+-2))
                                     (4 4 (:REWRITE DEFAULT-+-1)))
(FM9001::DISJOINT-TAKE-NTHCDR-SAME-LIST
     (217 36 (:DEFINITION ATOM))
     (126 17 (:REWRITE TAKE-OF-LEN-FREE))
     (125 70
          (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
     (106 10 (:REWRITE FM9001::DISJOINT-TAKE))
     (83 32 (:REWRITE ZP-OPEN))
     (82 18 (:REWRITE CONSP-OF-TAKE))
     (55 55 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (55 47 (:REWRITE DEFAULT-+-2))
     (47 47 (:REWRITE DEFAULT-+-1))
     (46 46 (:TYPE-PRESCRIPTION TRUE-LISTP-TAKE))
     (44 12 (:DEFINITION LEN))
     (31 31 (:REWRITE DEFAULT-<-2))
     (31 31 (:REWRITE DEFAULT-<-1))
     (27 9 (:REWRITE FOLD-CONSTS-IN-+))
     (20 20 (:LINEAR LEN-WHEN-PREFIXP))
     (14 14 (:TYPE-PRESCRIPTION ATOM)))
(FM9001::DISJOINT-NTHCDR-TAKE-OF-DISJOINT-LISTS
     (332 74 (:DEFINITION ATOM))
     (233 18 (:REWRITE TAKE-OF-LEN-FREE))
     (164 22 (:REWRITE CONSP-OF-TAKE))
     (144 72
          (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
     (136 17 (:DEFINITION NTHCDR))
     (134 65 (:REWRITE ZP-OPEN))
     (125 86 (:REWRITE DEFAULT-+-2))
     (99 17 (:DEFINITION MEMBER-EQUAL))
     (86 86 (:REWRITE DEFAULT-+-1))
     (79 79 (:REWRITE DEFAULT-CDR))
     (72 72 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (69 55 (:REWRITE DEFAULT-<-1))
     (66 66 (:TYPE-PRESCRIPTION TRUE-LISTP-TAKE))
     (64 64 (:LINEAR LEN-WHEN-PREFIXP))
     (58 55 (:REWRITE DEFAULT-<-2))
     (51 17 (:REWRITE COMMUTATIVITY-OF-+))
     (34 34 (:TYPE-PRESCRIPTION ATOM))
     (31 31 (:REWRITE DEFAULT-CAR))
     (15 5 (:REWRITE FOLD-CONSTS-IN-+))
     (3 3
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP)))
(FM9001::POSITION1)
(FM9001::MEMBER==>POSITION1 (13 13 (:REWRITE DEFAULT-CAR))
                            (6 6 (:REWRITE DEFAULT-CDR))
                            (3 3 (:REWRITE DEFAULT-+-2))
                            (3 3 (:REWRITE DEFAULT-+-1)))
(FM9001::TREE-SIZE)
(FM9001::TREE-SIZE-ATOM)
(FM9001::NOT-EQUAL-TREE-SIZE-TREE-0)
(FM9001::TREE-SIZE-1-CROCK (9 9 (:REWRITE FM9001::TREE-SIZE-ATOM))
                           (8 4 (:REWRITE DEFAULT-+-2))
                           (8 4 (:REWRITE DEFAULT-+-1))
                           (3 3 (:REWRITE DEFAULT-CDR))
                           (3 3 (:REWRITE DEFAULT-CAR)))
(FM9001::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS (35 7 (:DEFINITION LEN))
                                             (32 16 (:REWRITE DEFAULT-+-2))
                                             (25 16 (:REWRITE DEFAULT-+-1))
                                             (15 15 (:REWRITE DEFAULT-CDR))
                                             (8 8 (:LINEAR LEN-WHEN-PREFIXP))
                                             (6 3 (:REWRITE DEFAULT-<-2))
                                             (3 3 (:REWRITE DEFAULT-<-1)))
(FM9001::TREE-SIZE-LEMMAS
     (41 20 (:REWRITE DEFAULT-+-1))
     (40 20 (:REWRITE DEFAULT-+-2))
     (30 30 (:REWRITE FM9001::TREE-SIZE-ATOM))
     (14 14 (:REWRITE DEFAULT-CDR))
     (14 14 (:REWRITE DEFAULT-CAR))
     (4 2 (:REWRITE DEFAULT-UNARY-MINUS))
     (3 3 (:REWRITE FOLD-CONSTS-IN-+))
     (2 2
        (:LINEAR FM9001::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS)))
(FM9001::MAKE-LIST-APPEND-TREE-CROCK
     (22 22
         (:TYPE-PRESCRIPTION FM9001::TREE-SIZE))
     (20 9 (:REWRITE DEFAULT-+-2))
     (16 9 (:REWRITE DEFAULT-+-1))
     (16 2 (:DEFINITION MAKE-LIST-AC))
     (15 15 (:REWRITE FM9001::TREE-SIZE-ATOM))
     (7 7 (:REWRITE DEFAULT-CDR))
     (7 7 (:REWRITE DEFAULT-CAR))
     (2 2 (:REWRITE FOLD-CONSTS-IN-+)))
(FM9001::TFIRSTN)
(FM9001::TRESTN)
(FM9001::TREE-HEIGHT)
(FM9001::MAKE-TREE
     (812 812
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (812 812
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (812 812
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (812 812
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (400 32 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (280 32
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (280 32
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (280 32
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (211 68 (:REWRITE DEFAULT-PLUS-2))
     (160 32 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
     (160 32 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (160 32 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (160 32
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (160 32
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (160 32
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (160 32
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (160 32
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (160 32
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (160 32
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (152 152
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (152 152
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (152 152
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (124 68 (:REWRITE DEFAULT-PLUS-1))
     (123 47 (:REWRITE DEFAULT-LESS-THAN-1))
     (106 106 (:TYPE-PRESCRIPTION NUMERATOR-ZERO))
     (60 60 (:REWRITE DEFAULT-TIMES-2))
     (60 60 (:REWRITE DEFAULT-TIMES-1))
     (52 47 (:REWRITE DEFAULT-LESS-THAN-2))
     (47 47 (:REWRITE THE-FLOOR-BELOW))
     (47 47 (:REWRITE THE-FLOOR-ABOVE))
     (43 36
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (43 36
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (40 40
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (37 32 (:REWRITE |(< (- x) (- y))|))
     (36 36
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (35 14 (:REWRITE DEFAULT-MINUS))
     (33 3 (:REWRITE DEFAULT-FLOOR-RATIO))
     (32 32
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (32 32
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (32 32
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (32 32
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (32 32 (:REWRITE |(< c (- x))|))
     (32 32
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (32 32
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (32 32
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (32 32
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (32 32 (:REWRITE |(< (/ x) (/ y))|))
     (31 31 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (31 31
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (31 31 (:REWRITE INTEGERP-<-CONSTANT))
     (31 31 (:REWRITE CONSTANT-<-INTEGERP))
     (23 23
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (21 21 (:REWRITE |(< (/ x) 0)|))
     (21 21 (:REWRITE |(< (* x y) 0)|))
     (17 12 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (16 16 (:REWRITE |(< (+ c/d x) y)|))
     (16 16 (:REWRITE |(< (+ (- c) x) y)|))
     (14 14 (:TYPE-PRESCRIPTION ABS))
     (14 14
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (10 10 (:REWRITE REDUCE-INTEGERP-+))
     (10 10 (:REWRITE INTEGERP-MINUS-X))
     (10 10 (:META META-INTEGERP-CORRECT))
     (10 2
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (7 7 (:REWRITE |(* (- x) y)|))
     (6 6 (:REWRITE ZP-OPEN))
     (6 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (6 6
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (6 6
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (6 6
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (6 6
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (6 6
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (6 6 (:REWRITE |(equal c (/ x))|))
     (6 6 (:REWRITE |(equal c (- x))|))
     (6 6 (:REWRITE |(equal (/ x) c)|))
     (6 6 (:REWRITE |(equal (/ x) (/ y))|))
     (6 6 (:REWRITE |(equal (- x) c)|))
     (6 6 (:REWRITE |(equal (- x) (- y))|))
     (5 5
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (4 4 (:REWRITE |(< 0 (* x y))|))
     (3 3 (:REWRITE DEFAULT-FLOOR-2))
     (3 3 (:REWRITE DEFAULT-FLOOR-1))
     (3 3 (:REWRITE |(floor x 2)| . 2))
     (3 3 (:REWRITE |(< y (+ (- c) x))|))
     (3 3 (:REWRITE |(< x (+ c/d y))|))
     (2 2 (:REWRITE INTEGERP==>NUMERATOR-=-X))
     (2 2 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
     (2 2 (:REWRITE DEFAULT-RATIONAL-NUMERATOR))
     (2 2
        (:REWRITE DEFAULT-RATIONAL-DENOMINATOR))
     (2 2
        (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (2 2
        (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (2 2 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (2 2 (:REWRITE |(< 0 (/ x))|))
     (2 2 (:REWRITE |(< (/ x) y) with (< x 0)|))
     (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-4D))
     (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-3D))
     (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-2D))
     (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-1D))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER)))
(FM9001::TREE-SIZE-MAKE-TREE
     (932 932
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (932 932
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (932 932
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (932 932
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (488 40 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (344 40
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (344 40
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (317 37
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (200 40 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
     (200 40 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (200 40 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (200 40
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (200 40
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (200 40
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (200 40
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (200 40
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (197 63 (:REWRITE DEFAULT-PLUS-2))
     (185 37
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (138 14 (:REWRITE DEFAULT-FLOOR-RATIO))
     (128 2 (:REWRITE |(+ x (if a b c))|))
     (114 114
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (114 114
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (114 114
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (114 114
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (100 100 (:REWRITE DEFAULT-TIMES-2))
     (100 100 (:REWRITE DEFAULT-TIMES-1))
     (87 63 (:REWRITE DEFAULT-PLUS-1))
     (76 76
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (56 24 (:REWRITE FM9001::TREE-SIZE-ATOM))
     (54 2 (:REWRITE |(- (if a b c))|))
     (52 2 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
     (44 2 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (30 30
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (22 14 (:REWRITE DEFAULT-MINUS))
     (20 12 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (20 12
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (20 12
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (20 4
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (14 14 (:REWRITE REDUCE-INTEGERP-+))
     (14 14 (:REWRITE INTEGERP-MINUS-X))
     (14 14 (:REWRITE DEFAULT-FLOOR-2))
     (14 14 (:REWRITE DEFAULT-FLOOR-1))
     (14 14 (:REWRITE |(floor x 2)| . 2))
     (14 14 (:META META-INTEGERP-CORRECT))
     (12 12
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (12 12
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (12 12
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (12 12 (:REWRITE |(equal c (/ x))|))
     (12 12 (:REWRITE |(equal c (- x))|))
     (12 12 (:REWRITE |(equal (/ x) c)|))
     (12 12 (:REWRITE |(equal (/ x) (/ y))|))
     (12 12 (:REWRITE |(equal (- x) c)|))
     (12 12 (:REWRITE |(equal (- x) (- y))|))
     (10 10 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (10 8 (:REWRITE DEFAULT-CDR))
     (10 8 (:REWRITE DEFAULT-CAR))
     (8 8 (:REWRITE |(* (- x) y)|))
     (4 4 (:REWRITE ZP-OPEN))
     (3 3 (:REWRITE |(equal (+ (- c) x) y)|)))
(FM9001::CONSP-MAKE-TREE
     (1662 1662
           (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (1662 1662
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (1662 1662
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (1662 1662
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (953 77 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (669 77
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (669 77
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (660 76
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (452 108 (:REWRITE DEFAULT-PLUS-2))
     (385 77 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
     (385 77 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (385 77 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (385 77
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (385 77
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (385 77
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (385 77
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (385 77
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (380 76
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (256 4 (:REWRITE |(+ x (if a b c))|))
     (231 25 (:REWRITE DEFAULT-FLOOR-RATIO))
     (210 210
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (210 210
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (210 210
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (158 158 (:REWRITE DEFAULT-TIMES-2))
     (158 158 (:REWRITE DEFAULT-TIMES-1))
     (131 131
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (129 108 (:REWRITE DEFAULT-PLUS-1))
     (108 4 (:REWRITE |(- (if a b c))|))
     (100 25 (:REWRITE |(* y x)|))
     (70 38 (:REWRITE DEFAULT-MINUS))
     (54 6 (:REWRITE ACL2-NUMBERP-X))
     (49 49
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (37 31
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (36 36 (:REWRITE THE-FLOOR-BELOW))
     (36 36 (:REWRITE THE-FLOOR-ABOVE))
     (36 36 (:REWRITE DEFAULT-LESS-THAN-2))
     (35 31
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (35 31
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (31 31
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (31 31
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (31 31 (:REWRITE INTEGERP-<-CONSTANT))
     (31 31 (:REWRITE CONSTANT-<-INTEGERP))
     (31 31
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (31 31
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (31 31
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (31 31
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (31 31 (:REWRITE |(< c (- x))|))
     (31 31
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (31 31
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (31 31
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (31 31 (:REWRITE |(< (/ x) (/ y))|))
     (31 31 (:REWRITE |(< (- x) c)|))
     (31 31 (:REWRITE |(< (- x) (- y))|))
     (30 30 (:REWRITE SIMPLIFY-SUMS-<))
     (30 30
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (30 30 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (30 6
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (25 25 (:REWRITE REDUCE-INTEGERP-+))
     (25 25 (:REWRITE INTEGERP-MINUS-X))
     (25 25 (:REWRITE DEFAULT-FLOOR-2))
     (25 25 (:REWRITE DEFAULT-FLOOR-1))
     (25 25 (:REWRITE |(floor x 2)| . 2))
     (25 25 (:META META-INTEGERP-CORRECT))
     (24 6 (:REWRITE RATIONALP-X))
     (21 21 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (21 21 (:REWRITE |(* (- x) y)|))
     (10 10 (:REWRITE |(< (/ x) 0)|))
     (10 10 (:REWRITE |(< (* x y) 0)|))
     (9 9 (:REWRITE |(< (+ c/d x) y)|))
     (9 9 (:REWRITE |(< (+ (- c) x) y)|))
     (8 8 (:TYPE-PRESCRIPTION ABS))
     (7 7
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (6 6 (:REWRITE REDUCE-RATIONALP-+))
     (6 6 (:REWRITE REDUCE-RATIONALP-*))
     (6 6 (:REWRITE RATIONALP-MINUS-X))
     (6 6 (:META META-RATIONALP-CORRECT))
     (5 5 (:REWRITE ZP-OPEN))
     (4 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (4 4
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (4 4
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (4 4
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (4 4
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (4 4
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (4 4 (:REWRITE |(equal c (/ x))|))
     (4 4 (:REWRITE |(equal c (- x))|))
     (4 4 (:REWRITE |(equal (/ x) c)|))
     (4 4 (:REWRITE |(equal (/ x) (/ y))|))
     (4 4 (:REWRITE |(equal (- x) c)|))
     (4 4 (:REWRITE |(equal (- x) (- y))|))
     (1 1
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|)))
(FM9001::TV-GUARD)
(FM9001::LEN-1-LISTP)
(FM9001::LEN-1-TRUE-LISTP)
(FM9001::PAIRLIS$-STRIP-CARS
     (122 121 (:REWRITE DEFAULT-CDR))
     (88 87 (:REWRITE DEFAULT-CAR))
     (73 39
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (73 39
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (65 33 (:REWRITE DEFAULT-PLUS-2))
     (48 39 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (40 40
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (39 39
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (39 39 (:REWRITE |(equal c (/ x))|))
     (39 39 (:REWRITE |(equal c (- x))|))
     (39 39 (:REWRITE |(equal (/ x) c)|))
     (39 39 (:REWRITE |(equal (/ x) (/ y))|))
     (39 39 (:REWRITE |(equal (- x) c)|))
     (39 39 (:REWRITE |(equal (- x) (- y))|))
     (33 33 (:REWRITE DEFAULT-PLUS-1))
     (30 30
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (30 30 (:REWRITE NORMALIZE-ADDENDS))
     (28 28 (:LINEAR LEN-WHEN-PREFIXP))
     (14 14
         (:LINEAR FM9001::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (1 1 (:REWRITE |(equal (+ (- c) x) y)|)))
(FM9001::LEN-1-TRUE-LISTP-PAIRLIS$-WITH-NIL
     (31 29 (:REWRITE DEFAULT-CDR))
     (20 20 (:TYPE-PRESCRIPTION LEN))
     (18 16 (:REWRITE DEFAULT-CAR))
     (8 4
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (8 4
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (8 4 (:REWRITE DEFAULT-PLUS-2))
     (4 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (4 4
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (4 4
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (4 4
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (4 4 (:REWRITE NORMALIZE-ADDENDS))
     (4 4
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (4 4 (:REWRITE DEFAULT-PLUS-1))
     (4 4 (:REWRITE |(equal c (/ x))|))
     (4 4 (:REWRITE |(equal c (- x))|))
     (4 4 (:REWRITE |(equal (/ x) c)|))
     (4 4 (:REWRITE |(equal (/ x) (/ y))|))
     (4 4 (:REWRITE |(equal (- x) c)|))
     (4 4 (:REWRITE |(equal (- x) (- y))|)))
(FM9001::STR-APPEND-SYMBOL-UNDERSCORE)
(FM9001::APPEND-SYMBOL-STRING)
(FM9001::SI)
(FM9001::SIS)
(FM9001::CONSP-SIS
     (255 9 (:DEFINITION BINARY-APPEND))
     (222 30 (:REWRITE STR::CONSP-OF-EXPLODE))
     (36 9 (:REWRITE DEFAULT-CDR))
     (36 9 (:REWRITE DEFAULT-CAR))
     (36 4 (:REWRITE ACL2-NUMBERP-X))
     (34 1 (:REWRITE ZP-OPEN))
     (33 1 (:REWRITE |(< (if a b c) x)|))
     (16 4 (:REWRITE RATIONALP-X))
     (15 15 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (15 15
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (15 15
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (15 15
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (15 15
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (15 15
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (15 15 (:REWRITE |(equal c (/ x))|))
     (15 15 (:REWRITE |(equal c (- x))|))
     (15 15 (:REWRITE |(equal (/ x) c)|))
     (15 15 (:REWRITE |(equal (/ x) (/ y))|))
     (15 15 (:REWRITE |(equal (- x) c)|))
     (15 15 (:REWRITE |(equal (- x) (- y))|))
     (15 3
         (:REWRITE STR::CHARACTER-LISTP-WHEN-DIGIT-LISTP))
     (12 3
         (:REWRITE INTERN-IN-PACKAGE-OF-SYMBOL-IS-IDENTITY))
     (10 2 (:REWRITE |(+ c (+ d x))|))
     (9 9 (:REWRITE DEFAULT-PLUS-1))
     (9 6
        (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
     (8 8 (:REWRITE REDUCE-INTEGERP-+))
     (8 8 (:REWRITE INTEGERP-MINUS-X))
     (8 8 (:META META-INTEGERP-CORRECT))
     (8 1 (:REWRITE |(+ x (if a b c))|))
     (6 6
        (:TYPE-PRESCRIPTION STRINGP-OF-IMPLODE))
     (6 6
        (:TYPE-PRESCRIPTION MEMBER-SYMBOL-NAME))
     (6 6 (:TYPE-PRESCRIPTION STR::DIGIT-LISTP))
     (6 6 (:REWRITE THE-FLOOR-BELOW))
     (6 6 (:REWRITE THE-FLOOR-ABOVE))
     (6 6
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (6 6 (:REWRITE NORMALIZE-ADDENDS))
     (6 6 (:REWRITE DEFAULT-LESS-THAN-2))
     (6 6 (:REWRITE DEFAULT-LESS-THAN-1))
     (6 6
        (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
     (6 3
        (:REWRITE STR::DIGIT-LISTP-WHEN-NOT-CONSP))
     (6 3
        (:REWRITE DEFAULT-INTERN-IN-PACKAGE-OF-SYMBOL))
     (5 5 (:REWRITE SIMPLIFY-SUMS-<))
     (5 5
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (5 5 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (5 5 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (5 5
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (5 5
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (5 5 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (5 5 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (5 5 (:REWRITE INTEGERP-<-CONSTANT))
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
     (4 4 (:REWRITE REDUCE-RATIONALP-+))
     (4 4 (:REWRITE REDUCE-RATIONALP-*))
     (4 4 (:REWRITE RATIONALP-MINUS-X))
     (4 4 (:META META-RATIONALP-CORRECT))
     (3 3
        (:TYPE-PRESCRIPTION STR::STRINGP-OF-NATSTR))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (3 3 (:REWRITE DEFAULT-SYMBOL-NAME))
     (3 3 (:REWRITE |(< (/ x) 0)|))
     (3 3 (:REWRITE |(< (* x y) 0)|))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (2 2 (:REWRITE |(< 0 (/ x))|))
     (2 2 (:REWRITE |(< 0 (* x y))|))
     (1 1 (:REWRITE |(< y (+ (- c) x))|))
     (1 1 (:REWRITE |(< x (+ c/d y))|))
     (1 1 (:REWRITE |(< (+ c/d x) y)|))
     (1 1 (:REWRITE |(< (+ (- c) x) y)|)))
(FM9001::SYMBOL-INEQUALITY)
(FM9001::INTERN$-DIFF-STRINGS
     (8 2
        (:REWRITE INTERN-IN-PACKAGE-OF-SYMBOL-IS-IDENTITY))
     (4 4
        (:TYPE-PRESCRIPTION MEMBER-SYMBOL-NAME))
     (4 2 (:REWRITE DEFAULT-SYMBOL-NAME))
     (2 2 (:REWRITE FM9001-PACKAGE))
     (2 2
        (:REWRITE DEFAULT-INTERN-IN-PACKAGE-OF-SYMBOL))
     (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (1 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (1 1
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (1 1
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (1 1
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (1 1
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (1 1 (:REWRITE |(equal c (/ x))|))
     (1 1 (:REWRITE |(equal c (- x))|))
     (1 1 (:REWRITE |(equal (/ x) c)|))
     (1 1 (:REWRITE |(equal (/ x) (/ y))|))
     (1 1 (:REWRITE |(equal (- x) c)|))
     (1 1 (:REWRITE |(equal (- x) (- y))|)))
(FM9001::NOT-PREFIXP-NOT-EQUAL (1 1 (:REWRITE PREFIXP-TRANSITIVE . 2))
                               (1 1 (:REWRITE PREFIXP-TRANSITIVE . 1))
                               (1 1
                                  (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
                               (1 1
                                  (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
                               (1 1 (:REWRITE LIST-EQUIV-WHEN-ATOM-RIGHT))
                               (1 1 (:REWRITE LIST-EQUIV-WHEN-ATOM-LEFT)))
(FM9001::PREFIXP-APPEND-RELATION-1
     (9068 91
           (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
     (3806 422 (:DEFINITION LEN))
     (3417 3417 (:TYPE-PRESCRIPTION LEN))
     (2272 149
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (1887 31
           (:REWRITE FM9001::NOT-PREFIXP-NOT-EQUAL))
     (1787 728 (:LINEAR LEN-WHEN-PREFIXP))
     (1528 704 (:REWRITE DEFAULT-PLUS-2))
     (1404 54 (:REWRITE LEN-OF-APPEND))
     (812 704 (:REWRITE DEFAULT-PLUS-1))
     (790 10
          (:REWRITE PREFIXP-OF-APPEND-WHEN-SAME-LENGTH))
     (712 494 (:REWRITE DEFAULT-CDR))
     (654 34 (:REWRITE |(+ y (+ x z))|))
     (647 132
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (548 548
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (548 548 (:REWRITE NORMALIZE-ADDENDS))
     (548 274
          (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
     (415 132
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (413 132 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (378 54 (:REWRITE |(+ y x)|))
     (367 367
          (:LINEAR FM9001::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
     (319 87 (:REWRITE ACL2-NUMBERP-X))
     (300 82 (:REWRITE |(+ c (+ d x))|))
     (274 274 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (274 274 (:TYPE-PRESCRIPTION BINARY-APPEND))
     (164 128 (:REWRITE DEFAULT-CAR))
     (149 149
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (132 132
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (132 132 (:REWRITE |(equal c (/ x))|))
     (132 132 (:REWRITE |(equal c (- x))|))
     (132 132 (:REWRITE |(equal (/ x) c)|))
     (132 132 (:REWRITE |(equal (/ x) (/ y))|))
     (132 132 (:REWRITE |(equal (- x) c)|))
     (132 132 (:REWRITE |(equal (- x) (- y))|))
     (116 29 (:REWRITE RATIONALP-X))
     (92 34 (:REWRITE |(+ 0 x)|))
     (91 91 (:REWRITE PREFIXP-TRANSITIVE . 2))
     (91 91 (:REWRITE PREFIXP-TRANSITIVE . 1))
     (91 91
         (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
     (91 91
         (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
     (48 48 (:REWRITE FOLD-CONSTS-IN-+))
     (48 48 (:REWRITE APPEND-WHEN-NOT-CONSP))
     (48 48
         (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
     (35 35 (:REWRITE |(equal (+ (- c) x) y)|))
     (31 31 (:REWRITE FM9001::SYMBOL-INEQUALITY))
     (29 29 (:REWRITE REDUCE-RATIONALP-+))
     (29 29 (:REWRITE REDUCE-RATIONALP-*))
     (29 29 (:REWRITE REDUCE-INTEGERP-+))
     (29 29 (:REWRITE RATIONALP-MINUS-X))
     (29 29 (:REWRITE INTEGERP-MINUS-X))
     (29 29 (:META META-RATIONALP-CORRECT))
     (29 29 (:META META-INTEGERP-CORRECT))
     (20 20 (:REWRITE CDR-OF-APPEND-WHEN-CONSP))
     (13 13 (:REWRITE |(equal x (if a b c))|))
     (13 13 (:REWRITE |(equal (if a b c) x)|))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(FM9001::PREFIXP-APPEND-RELATION-2
     (229 5
          (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
     (114 114 (:TYPE-PRESCRIPTION LEN))
     (91 13 (:DEFINITION LEN))
     (90 16 (:LINEAR LEN-WHEN-PREFIXP))
     (90 5 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (90 1 (:DEFINITION PREFIXP))
     (78 3 (:REWRITE LEN-OF-APPEND))
     (57 6 (:REWRITE |(+ y x)|))
     (56 28 (:REWRITE DEFAULT-PLUS-2))
     (44 28 (:REWRITE DEFAULT-PLUS-1))
     (36 18 (:REWRITE NORMALIZE-ADDENDS))
     (29 1 (:REWRITE |(+ y (+ x z))|))
     (22 5
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (16 16
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (15 15 (:REWRITE DEFAULT-CDR))
     (14 5
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (11 3 (:REWRITE ACL2-NUMBERP-X))
     (8 8
        (:LINEAR FM9001::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
     (6 3 (:DEFINITION FIX))
     (5 5
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (5 5
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (5 5
        (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
     (5 5
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (5 5 (:REWRITE |(equal c (/ x))|))
     (5 5 (:REWRITE |(equal c (- x))|))
     (5 5 (:REWRITE |(equal (/ x) c)|))
     (5 5 (:REWRITE |(equal (/ x) (/ y))|))
     (5 5 (:REWRITE |(equal (- x) c)|))
     (5 5 (:REWRITE |(equal (- x) (- y))|))
     (4 4 (:REWRITE PREFIXP-TRANSITIVE . 1))
     (4 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (4 2 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
     (4 1 (:REWRITE RATIONALP-X))
     (2 2
        (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
     (2 2
        (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
     (2 2 (:REWRITE DEFAULT-CAR))
     (2 2 (:REWRITE |(+ x (- x))|))
     (2 1 (:REWRITE |(+ 0 x)|))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (1 1 (:REWRITE REDUCE-RATIONALP-+))
     (1 1 (:REWRITE REDUCE-RATIONALP-*))
     (1 1 (:REWRITE REDUCE-INTEGERP-+))
     (1 1 (:REWRITE RATIONALP-MINUS-X))
     (1 1 (:REWRITE LIST-EQUIV-WHEN-ATOM-RIGHT))
     (1 1 (:REWRITE LIST-EQUIV-WHEN-ATOM-LEFT))
     (1 1 (:REWRITE INTEGERP-MINUS-X))
     (1 1 (:REWRITE |(equal (+ (- c) x) y)|))
     (1 1 (:META META-RATIONALP-CORRECT))
     (1 1 (:META META-INTEGERP-CORRECT)))
(FM9001::ISTRPREFIXP-PREFIXP-EXPLODE-RELATION
     (2 2
        (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP)))
(FM9001::ISTRPREFIXP-STRING-APPEND-RELATION-1
     (1839 65 (:REWRITE STR::CONSP-OF-EXPLODE))
     (1670 1
           (:REWRITE FM9001::PREFIXP-APPEND-RELATION-2))
     (1416 53
           (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
     (1273 1 (:REWRITE PREFIXP-OF-APPEND-ARG2))
     (1056 48 (:DEFINITION LEN))
     (494 4 (:REWRITE STR::IPREFIXP-WHEN-PREFIXP))
     (427 427 (:TYPE-PRESCRIPTION LEN))
     (192 1 (:DEFINITION TAKE))
     (183 23
          (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
     (164 4
          (:REWRITE STR::IPREFIXP-WHEN-NOT-CONSP-RIGHT))
     (164 4
          (:REWRITE STR::IPREFIXP-WHEN-NOT-CONSP-LEFT))
     (164 4
          (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
     (162 2 (:REWRITE TAKE-OF-LEN-FREE))
     (162 2 (:DEFINITION BINARY-APPEND))
     (160 23 (:REWRITE DEFAULT-CDR))
     (157 1
          (:REWRITE PREFIXP-OF-APPEND-WHEN-SAME-LENGTH))
     (135 6
          (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
     (131 96
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (129 96
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (125 1 (:REWRITE LEN-OF-APPEND))
     (114 96 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (114 29
          (:REWRITE LIST-EQUIV-WHEN-ATOM-RIGHT))
     (112 3 (:REWRITE ZP-OPEN))
     (105 1 (:REWRITE FM9001::LEN-NTHCDR))
     (97 97
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (97 97
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (96 96
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (96 96 (:REWRITE |(equal c (/ x))|))
     (96 96 (:REWRITE |(equal c (- x))|))
     (96 96 (:REWRITE |(equal (/ x) c)|))
     (96 96 (:REWRITE |(equal (/ x) (/ y))|))
     (96 96 (:REWRITE |(equal (- x) c)|))
     (96 96 (:REWRITE |(equal (- x) (- y))|))
     (94 94 (:LINEAR LEN-WHEN-PREFIXP))
     (90 4 (:REWRITE APPEND-WHEN-NOT-CONSP))
     (88 1 (:DEFINITION NTHCDR))
     (81 1 (:REWRITE CONSP-OF-TAKE))
     (53 53 (:REWRITE PREFIXP-TRANSITIVE . 2))
     (53 53 (:REWRITE PREFIXP-TRANSITIVE . 1))
     (53 53
         (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
     (53 53
         (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
     (50 46 (:REWRITE FM9001::SYMBOL-INEQUALITY))
     (49 3 (:REWRITE DEFAULT-CAR))
     (47 47
         (:LINEAR FM9001::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
     (45 24 (:REWRITE DEFAULT-PLUS-2))
     (41 1 (:REWRITE LIST-EQUIV-WHEN-ATOM-LEFT))
     (40 6
         (:REWRITE STR::CHARACTER-LISTP-WHEN-DIGIT-LISTP))
     (39 3 (:REWRITE |(equal (+ (- c) x) y)|))
     (37 1 (:REWRITE LEN-OF-TAKE))
     (36 1 (:DEFINITION NFIX))
     (25 24 (:REWRITE DEFAULT-PLUS-1))
     (23 23
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (23 23 (:REWRITE NORMALIZE-ADDENDS))
     (17 17
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (16 16
         (:TYPE-PRESCRIPTION STR::DIGIT-LISTP))
     (16 16
         (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
     (16 8
         (:REWRITE STR::DIGIT-LISTP-WHEN-NOT-CONSP))
     (16 2 (:REWRITE STR::DIGIT-LISTP-OF-APPEND))
     (15 5
         (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
     (11 6
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (11 6 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (11 6 (:REWRITE DEFAULT-LESS-THAN-2))
     (8 6 (:REWRITE SIMPLIFY-SUMS-<))
     (8 6 (:REWRITE DEFAULT-LESS-THAN-1))
     (7 7 (:TYPE-PRESCRIPTION TRUE-LISTP-TAKE))
     (6 6 (:REWRITE THE-FLOOR-BELOW))
     (6 6 (:REWRITE THE-FLOOR-ABOVE))
     (6 6 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (6 6 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (6 6
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (6 6
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (6 6 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
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
     (5 1 (:REWRITE |(+ y x)|))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (4 4 (:REWRITE |(< 0 (/ x))|))
     (4 4 (:REWRITE |(< 0 (* x y))|))
     (2 1 (:REWRITE LIST-FIX-WHEN-TRUE-LISTP))
     (1 1 (:TYPE-PRESCRIPTION LIST-EQUIV))
     (1 1 (:REWRITE TAKE-WHEN-PREFIXP))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (1 1 (:REWRITE LEN-WHEN-PREFIXP))
     (1 1 (:REWRITE |(< (/ x) 0)|))
     (1 1 (:REWRITE |(< (* x y) 0)|)))
(FM9001::APPEND-DIFF-SYMBOLS-STRING-1 (6 6 (:REWRITE DEFAULT-SYMBOL-NAME)))
(FM9001::ISTRPREFIXP-STRING-APPEND-RELATION-2
     (365 14 (:REWRITE STR::CONSP-OF-EXPLODE))
     (183 9 (:DEFINITION LEN))
     (165 9
          (:REWRITE FM9001::NOT-PREFIXP-NOT-EQUAL))
     (125 1 (:REWRITE LEN-OF-APPEND))
     (99 19 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (92 92 (:TYPE-PRESCRIPTION LEN))
     (82 2
         (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
     (81 1 (:DEFINITION BINARY-APPEND))
     (46 7 (:REWRITE LIST-EQUIV-WHEN-ATOM-RIGHT))
     (45 2 (:REWRITE APPEND-WHEN-NOT-CONSP))
     (41 1 (:REWRITE LIST-EQUIV-WHEN-ATOM-LEFT))
     (31 7 (:REWRITE NORMALIZE-ADDENDS))
     (29 1 (:REWRITE |(+ y (+ x z))|))
     (27 12 (:REWRITE DEFAULT-PLUS-2))
     (26 19
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (26 19
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (22 12 (:REWRITE DEFAULT-PLUS-1))
     (19 19
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (19 19
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (19 19
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (19 19 (:REWRITE |(equal c (/ x))|))
     (19 19 (:REWRITE |(equal c (- x))|))
     (19 19 (:REWRITE |(equal (/ x) c)|))
     (19 19 (:REWRITE |(equal (/ x) (/ y))|))
     (19 19 (:REWRITE |(equal (- x) c)|))
     (19 19 (:REWRITE |(equal (- x) (- y))|))
     (16 4 (:REWRITE DEFAULT-CDR))
     (15 1 (:REWRITE |(+ y x)|))
     (11 11 (:REWRITE PREFIXP-TRANSITIVE . 2))
     (11 11 (:REWRITE PREFIXP-TRANSITIVE . 1))
     (11 11
         (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
     (11 11
         (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
     (10 10 (:LINEAR LEN-WHEN-PREFIXP))
     (9 9 (:REWRITE FM9001::SYMBOL-INEQUALITY))
     (7 1 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
     (6 3 (:DEFINITION FIX))
     (5 5
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (5 5
        (:LINEAR FM9001::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (4 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (4 1 (:REWRITE DEFAULT-CAR))
     (3 3
        (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
     (3 3
        (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
     (2 2 (:REWRITE |(+ x (- x))|))
     (2 1 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
     (2 1 (:REWRITE |(+ 0 x)|))
     (1 1 (:REWRITE |(equal (+ (- c) x) y)|))
     (1 1 (:REWRITE |(+ c (+ d x))|)))
(FM9001::APPEND-DIFF-SYMBOLS-STRING-2 (4 4 (:REWRITE DEFAULT-SYMBOL-NAME)))
(FM9001::SI-OF-DIFF-SYMBOLS-1
     (998 4 (:REWRITE STR::IPREFIXP-WHEN-PREFIXP))
     (966 32 (:REWRITE STR::CONSP-OF-EXPLODE))
     (666 17
          (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
     (472 16 (:DEFINITION LEN))
     (314 25
          (:REWRITE FM9001::NOT-PREFIXP-NOT-EQUAL))
     (192 10
          (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
     (180 4
          (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
     (146 146
          (:TYPE-PRESCRIPTION FM9001::STR-APPEND-SYMBOL-UNDERSCORE))
     (144 144 (:TYPE-PRESCRIPTION LEN))
     (144 4
          (:REWRITE STR::IPREFIXP-WHEN-NOT-CONSP-RIGHT))
     (144 4
          (:REWRITE STR::IPREFIXP-WHEN-NOT-CONSP-LEFT))
     (64 50
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (64 50
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (58 50 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (56 56
         (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
     (50 50
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (50 50
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (50 50
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (50 50 (:REWRITE |(equal c (/ x))|))
     (50 50 (:REWRITE |(equal c (- x))|))
     (50 50 (:REWRITE |(equal (/ x) c)|))
     (50 50 (:REWRITE |(equal (/ x) (/ y))|))
     (50 50 (:REWRITE |(equal (- x) c)|))
     (50 50 (:REWRITE |(equal (- x) (- y))|))
     (40 8 (:REWRITE DEFAULT-CDR))
     (36 36 (:LINEAR LEN-WHEN-PREFIXP))
     (21 21 (:TYPE-PRESCRIPTION PREFIXP))
     (18 18
         (:LINEAR FM9001::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
     (17 17 (:REWRITE PREFIXP-TRANSITIVE . 2))
     (17 17 (:REWRITE PREFIXP-TRANSITIVE . 1))
     (17 17
         (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
     (17 17
         (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
     (17 7 (:REWRITE LIST-EQUIV-WHEN-ATOM-RIGHT))
     (16 8
         (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
     (16 8 (:REWRITE DEFAULT-PLUS-2))
     (8 8
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (8 8 (:REWRITE NORMALIZE-ADDENDS))
     (8 8 (:REWRITE DEFAULT-PLUS-1))
     (8 2
        (:REWRITE INTERN-IN-PACKAGE-OF-SYMBOL-IS-IDENTITY))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (6 2 (:REWRITE DEFAULT-SYMBOL-NAME))
     (4 4
        (:TYPE-PRESCRIPTION MEMBER-SYMBOL-NAME))
     (4 2
        (:REWRITE DEFAULT-INTERN-IN-PACKAGE-OF-SYMBOL))
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
     (2 2 (:REWRITE REDUCE-INTEGERP-+))
     (2 2 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (2 2 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (2 2 (:REWRITE INTEGERP-MINUS-X))
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
     (2 2 (:META META-INTEGERP-CORRECT)))
(FM9001::SI-OF-DIFF-SYMBOLS-2
     (242 13 (:REWRITE STR::CONSP-OF-EXPLODE))
     (114 5 (:DEFINITION LEN))
     (94 14 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (85 1 (:REWRITE LEN-OF-APPEND))
     (57 57 (:TYPE-PRESCRIPTION LEN))
     (52 2 (:REWRITE APPEND-WHEN-NOT-CONSP))
     (40 3 (:REWRITE LIST-EQUIV-WHEN-ATOM-RIGHT))
     (37 1 (:DEFINITION BINARY-APPEND))
     (36 4 (:REWRITE DEFAULT-CDR))
     (36 1 (:REWRITE LIST-EQUIV-WHEN-ATOM-LEFT))
     (35 35
         (:TYPE-PRESCRIPTION FM9001::STR-APPEND-SYMBOL-UNDERSCORE))
     (34 2
         (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
     (33 9
         (:REWRITE FM9001::NOT-PREFIXP-NOT-EQUAL))
     (31 7 (:REWRITE NORMALIZE-ADDENDS))
     (29 1 (:REWRITE |(+ y (+ x z))|))
     (27 12 (:REWRITE DEFAULT-PLUS-2))
     (22 12 (:REWRITE DEFAULT-PLUS-1))
     (18 14
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (18 14
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (15 1 (:REWRITE |(+ y x)|))
     (14 14
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (14 14
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (14 14
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (14 14 (:REWRITE |(equal c (/ x))|))
     (14 14 (:REWRITE |(equal c (- x))|))
     (14 14 (:REWRITE |(equal (/ x) c)|))
     (14 14 (:REWRITE |(equal (/ x) (/ y))|))
     (14 14 (:REWRITE |(equal (- x) c)|))
     (14 14 (:REWRITE |(equal (- x) (- y))|))
     (9 9
        (:TYPE-PRESCRIPTION STR::STRINGP-OF-NATSTR))
     (9 9 (:REWRITE FM9001::SYMBOL-INEQUALITY))
     (7 1 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
     (6 3
        (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
     (6 3 (:DEFINITION FIX))
     (5 5
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (5 1 (:REWRITE DEFAULT-CAR))
     (4 4 (:REWRITE PREFIXP-TRANSITIVE . 2))
     (4 4 (:REWRITE PREFIXP-TRANSITIVE . 1))
     (4 4
        (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
     (4 4
        (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
     (4 4 (:LINEAR LEN-WHEN-PREFIXP))
     (4 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (4 1
        (:REWRITE INTERN-IN-PACKAGE-OF-SYMBOL-IS-IDENTITY))
     (3 3 (:REWRITE STR::NATSTR-NONEMPTY))
     (3 1 (:REWRITE DEFAULT-SYMBOL-NAME))
     (2 2
        (:TYPE-PRESCRIPTION MEMBER-SYMBOL-NAME))
     (2 2 (:REWRITE |(+ x (- x))|))
     (2 2
        (:LINEAR FM9001::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
     (2 1
        (:REWRITE DEFAULT-INTERN-IN-PACKAGE-OF-SYMBOL))
     (2 1 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
     (2 1 (:REWRITE |(+ 0 x)|))
     (1 1 (:REWRITE THE-FLOOR-BELOW))
     (1 1 (:REWRITE THE-FLOOR-ABOVE))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (1 1 (:REWRITE SIMPLIFY-SUMS-<))
     (1 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (1 1 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (1 1 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (1 1
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (1 1
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (1 1 (:REWRITE REDUCE-INTEGERP-+))
     (1 1 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (1 1 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (1 1 (:REWRITE INTEGERP-MINUS-X))
     (1 1 (:REWRITE INTEGERP-<-CONSTANT))
     (1 1 (:REWRITE DEFAULT-LESS-THAN-2))
     (1 1 (:REWRITE DEFAULT-LESS-THAN-1))
     (1 1 (:REWRITE CONSTANT-<-INTEGERP))
     (1 1 (:REWRITE |(equal (+ (- c) x) y)|))
     (1 1
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (1 1
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (1 1
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (1 1
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (1 1 (:REWRITE |(< c (- x))|))
     (1 1
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (1 1
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (1 1
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (1 1
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (1 1 (:REWRITE |(< (/ x) 0)|))
     (1 1 (:REWRITE |(< (/ x) (/ y))|))
     (1 1 (:REWRITE |(< (- x) c)|))
     (1 1 (:REWRITE |(< (- x) (- y))|))
     (1 1 (:REWRITE |(< (* x y) 0)|))
     (1 1 (:REWRITE |(+ c (+ d x))|))
     (1 1 (:META META-INTEGERP-CORRECT)))
(FM9001::APPEND-SYMBOL-DIFF-STRINGS
     (1618 39
           (:REWRITE FM9001::NOT-PREFIXP-NOT-EQUAL))
     (1197 1 (:REWRITE PREFIXP-OF-APPEND-ARG1))
     (869 57 (:REWRITE STR::CONSP-OF-EXPLODE))
     (811 16
          (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
     (546 25 (:DEFINITION LEN))
     (319 1
          (:REWRITE FM9001::PREFIXP-APPEND-RELATION-2))
     (318 5
          (:REWRITE FM9001::ISTRPREFIXP-PREFIXP-EXPLODE-RELATION))
     (311 2 (:DEFINITION STR::ISTRPREFIXP$INLINE))
     (302 1 (:REWRITE TAKE-WHEN-PREFIXP))
     (274 3 (:REWRITE SIMPLIFY-SUMS-<))
     (253 253 (:TYPE-PRESCRIPTION LEN))
     (240 2 (:REWRITE STR::IPREFIXP-WHEN-PREFIXP))
     (228 60 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (213 3 (:REWRITE LEN-OF-APPEND))
     (175 2
          (:REWRITE PREFIXP-OF-APPEND-WHEN-SAME-LENGTH))
     (162 1 (:REWRITE LEN-WHEN-PREFIXP))
     (144 4
          (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
     (142 14 (:REWRITE |(+ y x)|))
     (134 2 (:DEFINITION BINARY-APPEND))
     (116 58 (:REWRITE DEFAULT-PLUS-2))
     (116 4 (:REWRITE |(+ y (+ x z))|))
     (101 58 (:REWRITE DEFAULT-PLUS-1))
     (93 93
         (:TYPE-PRESCRIPTION FM9001::STR-APPEND-SYMBOL-UNDERSCORE))
     (92 29 (:REWRITE NORMALIZE-ADDENDS))
     (92 20 (:REWRITE DEFAULT-CDR))
     (87 1 (:REWRITE FM9001::NTHCDR-APPEND))
     (83 10
         (:REWRITE LIST-EQUIV-WHEN-ATOM-RIGHT))
     (77 60
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (75 60
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (75 5 (:REWRITE LIST-EQUIV-WHEN-ATOM-LEFT))
     (64 4
         (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
     (64 4
         (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
     (60 60
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (60 60
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (60 60
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (60 60 (:REWRITE |(equal c (/ x))|))
     (60 60 (:REWRITE |(equal c (- x))|))
     (60 60 (:REWRITE |(equal (/ x) c)|))
     (60 60 (:REWRITE |(equal (/ x) (/ y))|))
     (60 60 (:REWRITE |(equal (- x) c)|))
     (60 60 (:REWRITE |(equal (- x) (- y))|))
     (57 4 (:REWRITE APPEND-WHEN-NOT-CONSP))
     (55 39 (:REWRITE FM9001::SYMBOL-INEQUALITY))
     (36 6
         (:REWRITE STR::CHARACTER-LISTP-WHEN-DIGIT-LISTP))
     (31 1
         (:REWRITE STR::IPREFIXP-WHEN-NOT-CONSP-RIGHT))
     (31 1
         (:REWRITE STR::IPREFIXP-WHEN-NOT-CONSP-LEFT))
     (22 22
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (22 22 (:LINEAR LEN-WHEN-PREFIXP))
     (22 2
         (:REWRITE FM9001::PREFIXP-APPEND-RELATION-1))
     (20 10 (:DEFINITION FIX))
     (18 18 (:TYPE-PRESCRIPTION PREFIXP))
     (16 16 (:REWRITE PREFIXP-TRANSITIVE . 2))
     (16 16 (:REWRITE PREFIXP-TRANSITIVE . 1))
     (16 16
         (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
     (16 16
         (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
     (16 2 (:REWRITE STR::DIGIT-LISTP-OF-APPEND))
     (14 14
         (:TYPE-PRESCRIPTION STR::DIGIT-LISTP))
     (14 7 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (14 7
         (:REWRITE STR::DIGIT-LISTP-WHEN-NOT-CONSP))
     (14 7 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
     (12 8
         (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
     (11 11
         (:LINEAR FM9001::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
     (11 3
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (10 2 (:REWRITE DEFAULT-CAR))
     (9 3 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (8 4 (:REWRITE |(+ 0 x)|))
     (7 7 (:REWRITE |(+ x (- x))|))
     (7 3 (:REWRITE DEFAULT-LESS-THAN-2))
     (7 3 (:REWRITE DEFAULT-LESS-THAN-1))
     (5 5 (:TYPE-PRESCRIPTION LIST-EQUIV))
     (4 2 (:REWRITE LIST-FIX-WHEN-TRUE-LISTP))
     (3 3 (:REWRITE THE-FLOOR-BELOW))
     (3 3 (:REWRITE THE-FLOOR-ABOVE))
     (3 3 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (3 3
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (3 3
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (3 3 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (3 3 (:REWRITE INTEGERP-<-CONSTANT))
     (3 3 (:REWRITE CONSTANT-<-INTEGERP))
     (3 3
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (3 3
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (3 3
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (3 3
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (3 3 (:REWRITE |(< c (- x))|))
     (3 3
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (3 3
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (3 3
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (3 3
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (3 3 (:REWRITE |(< (/ x) (/ y))|))
     (3 3 (:REWRITE |(< (- x) c)|))
     (3 3 (:REWRITE |(< (- x) (- y))|))
     (2 2
        (:TYPE-PRESCRIPTION STR::ISTRPREFIXP$INLINE))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (2 2 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (2 2 (:REWRITE |(equal (+ (- c) x) y)|))
     (2 1 (:REWRITE DEFAULT-MINUS))
     (1 1 (:TYPE-PRESCRIPTION STR::IPREFIXP))
     (1 1 (:REWRITE |(< y (+ (- c) x))|))
     (1 1 (:REWRITE |(< x (+ c/d y))|))
     (1 1 (:REWRITE |(< (+ c/d x) y)|))
     (1 1 (:REWRITE |(< (+ (- c) x) y)|))
     (1 1 (:DEFINITION NTHCDR)))
(FM9001::SI-OF-DIFF-IDXES
     (44 3
         (:REWRITE FM9001::NOT-PREFIXP-NOT-EQUAL))
     (23 3 (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
     (8 4 (:DEFINITION LEN))
     (8 2
        (:REWRITE INTERN-IN-PACKAGE-OF-SYMBOL-IS-IDENTITY))
     (6 6 (:TYPE-PRESCRIPTION LEN))
     (6 6 (:REWRITE THE-FLOOR-BELOW))
     (6 6 (:REWRITE THE-FLOOR-ABOVE))
     (6 6 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (6 6
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (6 6
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (6 6 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (6 6 (:REWRITE INTEGERP-<-CONSTANT))
     (6 6 (:REWRITE DEFAULT-LESS-THAN-2))
     (6 6 (:REWRITE DEFAULT-LESS-THAN-1))
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
     (6 6 (:REWRITE |(< (/ x) 0)|))
     (6 6 (:REWRITE |(< (/ x) (/ y))|))
     (6 6 (:REWRITE |(< (- x) c)|))
     (6 6 (:REWRITE |(< (- x) (- y))|))
     (6 6 (:REWRITE |(< (* x y) 0)|))
     (6 2 (:REWRITE LIST-EQUIV-WHEN-ATOM-RIGHT))
     (6 2 (:REWRITE DEFAULT-SYMBOL-NAME))
     (4 4
        (:TYPE-PRESCRIPTION MEMBER-SYMBOL-NAME))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (4 4 (:REWRITE SIMPLIFY-SUMS-<))
     (4 4
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (4 4 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (4 2
        (:REWRITE DEFAULT-INTERN-IN-PACKAGE-OF-SYMBOL))
     (3 3 (:TYPE-PRESCRIPTION PREFIXP))
     (3 3 (:REWRITE PREFIXP-TRANSITIVE . 2))
     (3 3 (:REWRITE PREFIXP-TRANSITIVE . 1))
     (3 3
        (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
     (3 3
        (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
     (3 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (3 2
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (3 2
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (3 1
        (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
     (2 2
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (2 2 (:REWRITE REDUCE-INTEGERP-+))
     (2 2
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (2 2 (:REWRITE INTEGERP-MINUS-X))
     (2 2
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (2 2 (:REWRITE |(equal c (/ x))|))
     (2 2 (:REWRITE |(equal c (- x))|))
     (2 2 (:REWRITE |(equal (/ x) c)|))
     (2 2 (:REWRITE |(equal (/ x) (/ y))|))
     (2 2 (:REWRITE |(equal (- x) c)|))
     (2 2 (:REWRITE |(equal (- x) (- y))|))
     (2 2 (:META META-INTEGERP-CORRECT)))
(FM9001::SI-SIS-DIFF-SYMBOLS-1
     (3586 14
           (:REWRITE STR::IPREFIXP-WHEN-PREFIXP))
     (3427 110 (:REWRITE STR::CONSP-OF-EXPLODE))
     (2515 67
           (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
     (1770 59 (:DEFINITION LEN))
     (1337 4
           (:REWRITE FM9001::SI-OF-DIFF-SYMBOLS-2))
     (1327 85
           (:REWRITE FM9001::NOT-PREFIXP-NOT-EQUAL))
     (669 42
          (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
     (631 17
          (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
     (571 571 (:TYPE-PRESCRIPTION LEN))
     (484 14
          (:REWRITE STR::IPREFIXP-WHEN-NOT-CONSP-RIGHT))
     (469 14
          (:REWRITE STR::IPREFIXP-WHEN-NOT-CONSP-LEFT))
     (437 437
          (:TYPE-PRESCRIPTION FM9001::STR-APPEND-SYMBOL-UNDERSCORE))
     (240 181
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (240 181
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (212 181 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (192 192
          (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
     (181 181
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (181 181
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (181 181
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (181 181 (:REWRITE |(equal c (/ x))|))
     (181 181 (:REWRITE |(equal c (- x))|))
     (181 181 (:REWRITE |(equal (/ x) c)|))
     (181 181 (:REWRITE |(equal (/ x) (/ y))|))
     (181 181 (:REWRITE |(equal (- x) c)|))
     (181 181 (:REWRITE |(equal (- x) (- y))|))
     (146 35 (:REWRITE DEFAULT-CDR))
     (140 140 (:LINEAR LEN-WHEN-PREFIXP))
     (110 37 (:REWRITE DEFAULT-PLUS-2))
     (88 85 (:REWRITE FM9001::SYMBOL-INEQUALITY))
     (81 81 (:TYPE-PRESCRIPTION PREFIXP))
     (70 70
         (:LINEAR FM9001::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
     (67 67 (:REWRITE PREFIXP-TRANSITIVE . 2))
     (67 67 (:REWRITE PREFIXP-TRANSITIVE . 1))
     (67 67
         (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
     (67 67
         (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
     (52 28
         (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
     (46 25
         (:REWRITE LIST-EQUIV-WHEN-ATOM-RIGHT))
     (36 4 (:REWRITE ACL2-NUMBERP-X))
     (35 35
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (35 35 (:REWRITE NORMALIZE-ADDENDS))
     (35 35 (:REWRITE DEFAULT-PLUS-1))
     (28 28
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (16 4 (:REWRITE RATIONALP-X))
     (7 4 (:REWRITE DEFAULT-CAR))
     (5 4 (:REWRITE DEFAULT-SYMBOL-NAME))
     (4 4 (:REWRITE ZP-OPEN))
     (4 4 (:REWRITE REDUCE-RATIONALP-+))
     (4 4 (:REWRITE REDUCE-RATIONALP-*))
     (4 4 (:REWRITE REDUCE-INTEGERP-+))
     (4 4 (:REWRITE RATIONALP-MINUS-X))
     (4 4 (:REWRITE INTEGERP-MINUS-X))
     (4 4 (:META META-RATIONALP-CORRECT))
     (4 4 (:META META-INTEGERP-CORRECT)))
(FM9001::SI-SIS-DIFF-SYMBOLS-2
     (1295 5 (:REWRITE STR::IPREFIXP-WHEN-PREFIXP))
     (1235 40 (:REWRITE STR::CONSP-OF-EXPLODE))
     (1034 28
           (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
     (677 26 (:DEFINITION LEN))
     (651 33
          (:REWRITE FM9001::NOT-PREFIXP-NOT-EQUAL))
     (262 262 (:TYPE-PRESCRIPTION LEN))
     (243 8
          (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
     (223 18
          (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
     (180 5
          (:REWRITE STR::IPREFIXP-WHEN-NOT-CONSP-LEFT))
     (155 5
          (:REWRITE STR::IPREFIXP-WHEN-NOT-CONSP-RIGHT))
     (124 71
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (100 71
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (95 95
         (:TYPE-PRESCRIPTION FM9001::STR-APPEND-SYMBOL-UNDERSCORE))
     (90 71 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (80 22 (:REWRITE DEFAULT-PLUS-2))
     (71 71
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (71 71
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (71 71
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (71 71 (:REWRITE |(equal c (/ x))|))
     (71 71 (:REWRITE |(equal c (- x))|))
     (71 71 (:REWRITE |(equal (/ x) c)|))
     (71 71 (:REWRITE |(equal (/ x) (/ y))|))
     (71 71 (:REWRITE |(equal (- x) c)|))
     (71 71 (:REWRITE |(equal (- x) (- y))|))
     (70 70
         (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
     (69 13 (:REWRITE ACL2-NUMBERP-X))
     (68 68 (:LINEAR LEN-WHEN-PREFIXP))
     (58 20 (:REWRITE DEFAULT-CDR))
     (36 36 (:TYPE-PRESCRIPTION PREFIXP))
     (34 34
         (:LINEAR FM9001::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
     (33 33 (:REWRITE FM9001::SYMBOL-INEQUALITY))
     (28 28 (:REWRITE PREFIXP-TRANSITIVE . 2))
     (28 28 (:REWRITE PREFIXP-TRANSITIVE . 1))
     (28 28
         (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
     (28 28
         (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
     (28 7 (:REWRITE RATIONALP-X))
     (20 20
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (20 20 (:REWRITE NORMALIZE-ADDENDS))
     (20 20 (:REWRITE DEFAULT-PLUS-1))
     (15 10
         (:REWRITE LIST-EQUIV-WHEN-ATOM-RIGHT))
     (15 10
         (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
     (10 10
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (7 7 (:REWRITE REDUCE-RATIONALP-+))
     (7 7 (:REWRITE REDUCE-RATIONALP-*))
     (7 7 (:REWRITE REDUCE-INTEGERP-+))
     (7 7 (:REWRITE RATIONALP-MINUS-X))
     (7 7 (:REWRITE INTEGERP-MINUS-X))
     (7 7 (:META META-RATIONALP-CORRECT))
     (7 7 (:META META-INTEGERP-CORRECT))
     (7 4 (:REWRITE DEFAULT-CAR))
     (5 5 (:REWRITE DEFAULT-SYMBOL-NAME))
     (4 4 (:REWRITE ZP-OPEN)))
(FM9001::SI-SIS-DIFF-IDXES
     (2522 11
           (:DEFINITION STR::ISTRPREFIXP$INLINE))
     (1998 11
           (:REWRITE STR::IPREFIXP-WHEN-PREFIXP))
     (1858 64 (:REWRITE STR::CONSP-OF-EXPLODE))
     (1506 36
           (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
     (1340 4
           (:REWRITE FM9001::SI-SIS-DIFF-SYMBOLS-2))
     (867 3
          (:REWRITE FM9001::SI-OF-DIFF-SYMBOLS-2))
     (811 31 (:DEFINITION LEN))
     (656 53
          (:REWRITE FM9001::NOT-PREFIXP-NOT-EQUAL))
     (348 4
          (:REWRITE FM9001::SI-SIS-DIFF-SYMBOLS-1))
     (306 10
          (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
     (305 21
          (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
     (284 284 (:TYPE-PRESCRIPTION LEN))
     (252 7
          (:REWRITE STR::IPREFIXP-WHEN-NOT-CONSP-LEFT))
     (217 7
          (:REWRITE STR::IPREFIXP-WHEN-NOT-CONSP-RIGHT))
     (172 172
          (:TYPE-PRESCRIPTION FM9001::STR-APPEND-SYMBOL-UNDERSCORE))
     (159 15
          (:REWRITE LIST-EQUIV-WHEN-ATOM-RIGHT))
     (144 4 (:REWRITE LIST-EQUIV-WHEN-ATOM-LEFT))
     (141 110
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (141 110
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (127 110 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (114 114
          (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
     (110 110
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (110 110
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (110 110
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (110 110 (:REWRITE |(equal c (/ x))|))
     (110 110 (:REWRITE |(equal c (- x))|))
     (110 110 (:REWRITE |(equal (/ x) c)|))
     (110 110 (:REWRITE |(equal (/ x) (/ y))|))
     (110 110 (:REWRITE |(equal (- x) c)|))
     (110 110 (:REWRITE |(equal (- x) (- y))|))
     (73 21 (:REWRITE DEFAULT-CDR))
     (70 70 (:LINEAR LEN-WHEN-PREFIXP))
     (56 53 (:REWRITE FM9001::SYMBOL-INEQUALITY))
     (43 43 (:TYPE-PRESCRIPTION PREFIXP))
     (38 21 (:REWRITE DEFAULT-PLUS-2))
     (37 22
         (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
     (36 36 (:REWRITE PREFIXP-TRANSITIVE . 2))
     (36 36 (:REWRITE PREFIXP-TRANSITIVE . 1))
     (36 36
         (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
     (36 36
         (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
     (35 35
         (:LINEAR FM9001::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
     (21 21
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (21 21 (:REWRITE NORMALIZE-ADDENDS))
     (21 21 (:REWRITE DEFAULT-PLUS-1))
     (14 14
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (12 12 (:REWRITE THE-FLOOR-BELOW))
     (12 12 (:REWRITE THE-FLOOR-ABOVE))
     (12 12 (:REWRITE SIMPLIFY-SUMS-<))
     (12 12
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (12 12 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (12 12
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (12 12
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (12 12
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (12 12
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (12 12 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (12 12 (:REWRITE INTEGERP-<-CONSTANT))
     (12 12 (:REWRITE DEFAULT-LESS-THAN-2))
     (12 12 (:REWRITE DEFAULT-LESS-THAN-1))
     (12 12 (:REWRITE CONSTANT-<-INTEGERP))
     (12 12
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (12 12
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (12 12
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (12 12
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (12 12 (:REWRITE |(< c (- x))|))
     (12 12
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (12 12
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (12 12
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (12 12
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (12 12 (:REWRITE |(< (/ x) (/ y))|))
     (12 12 (:REWRITE |(< (- x) c)|))
     (12 12 (:REWRITE |(< (- x) (- y))|))
     (11 11
         (:TYPE-PRESCRIPTION STR::ISTRPREFIXP$INLINE))
     (11 7 (:REWRITE DEFAULT-SYMBOL-NAME))
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (8 8 (:REWRITE REDUCE-INTEGERP-+))
     (8 8 (:REWRITE INTEGERP-MINUS-X))
     (8 8 (:REWRITE |(< (/ x) 0)|))
     (8 8 (:REWRITE |(< (* x y) 0)|))
     (8 8 (:META META-INTEGERP-CORRECT))
     (7 7 (:TYPE-PRESCRIPTION STR::IPREFIXP))
     (7 4 (:REWRITE DEFAULT-CAR))
     (4 4 (:TYPE-PRESCRIPTION LIST-EQUIV))
     (4 4 (:REWRITE ZP-OPEN)))
(FM9001::LEN-SIS
     (124 9
          (:REWRITE FM9001::NOT-PREFIXP-NOT-EQUAL))
     (85 16 (:REWRITE DEFAULT-PLUS-2))
     (72 8 (:REWRITE ACL2-NUMBERP-X))
     (70 9 (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
     (32 8 (:REWRITE RATIONALP-X))
     (26 26 (:LINEAR LEN-WHEN-PREFIXP))
     (18 9 (:REWRITE LIST-EQUIV-WHEN-ATOM-RIGHT))
     (13 13
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (13 13 (:REWRITE NORMALIZE-ADDENDS))
     (13 13 (:REWRITE DEFAULT-PLUS-1))
     (13 13
         (:LINEAR FM9001::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
     (12 12 (:REWRITE REDUCE-INTEGERP-+))
     (12 12 (:REWRITE INTEGERP-MINUS-X))
     (12 12 (:META META-INTEGERP-CORRECT))
     (12 6
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (12 6
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (10 9 (:REWRITE FM9001::SYMBOL-INEQUALITY))
     (10 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (9 9 (:TYPE-PRESCRIPTION PREFIXP))
     (9 9 (:REWRITE PREFIXP-TRANSITIVE . 2))
     (9 9 (:REWRITE PREFIXP-TRANSITIVE . 1))
     (9 9
        (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
     (9 9
        (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
     (8 8 (:REWRITE REDUCE-RATIONALP-+))
     (8 8 (:REWRITE REDUCE-RATIONALP-*))
     (8 8 (:REWRITE RATIONALP-MINUS-X))
     (8 8 (:META META-RATIONALP-CORRECT))
     (8 5 (:REWRITE DEFAULT-CDR))
     (7 7
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (7 7
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (6 6 (:REWRITE THE-FLOOR-BELOW))
     (6 6 (:REWRITE THE-FLOOR-ABOVE))
     (6 6
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (6 6 (:REWRITE DEFAULT-LESS-THAN-2))
     (6 6 (:REWRITE |(equal c (/ x))|))
     (6 6 (:REWRITE |(equal c (- x))|))
     (6 6 (:REWRITE |(equal (/ x) c)|))
     (6 6 (:REWRITE |(equal (/ x) (/ y))|))
     (6 6 (:REWRITE |(equal (- x) c)|))
     (6 6 (:REWRITE |(equal (- x) (- y))|))
     (5 5 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (5 5
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (5 5
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (5 5 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (5 5 (:REWRITE INTEGERP-<-CONSTANT))
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
     (5 5
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (5 5
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (5 5
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (5 5
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (5 5 (:REWRITE |(< (/ x) 0)|))
     (5 5 (:REWRITE |(< (/ x) (/ y))|))
     (5 5 (:REWRITE |(< (- x) c)|))
     (5 5 (:REWRITE |(< (- x) (- y))|))
     (5 5 (:REWRITE |(< (* x y) 0)|))
     (4 4 (:REWRITE ZP-OPEN))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (4 4 (:REWRITE SIMPLIFY-SUMS-<))
     (4 4
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (4 4 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(FM9001::NO-DUPLICATESP-SIS
     (267 3 (:DEFINITION MEMBER-EQUAL))
     (186 3
          (:REWRITE FM9001::NOT-PREFIXP-NOT-EQUAL))
     (159 3 (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
     (57 57 (:TYPE-PRESCRIPTION LEN))
     (42 6 (:DEFINITION LEN))
     (39 6
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (33 9 (:REWRITE ACL2-NUMBERP-X))
     (23 17 (:REWRITE DEFAULT-CDR))
     (18 18 (:LINEAR LEN-WHEN-PREFIXP))
     (16 10 (:REWRITE DEFAULT-PLUS-2))
     (15 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (15 6
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (12 3 (:REWRITE RATIONALP-X))
     (10 10
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (10 10 (:REWRITE NORMALIZE-ADDENDS))
     (10 10 (:REWRITE DEFAULT-PLUS-1))
     (10 7 (:REWRITE DEFAULT-CAR))
     (9 9
        (:LINEAR FM9001::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
     (7 7 (:REWRITE REDUCE-INTEGERP-+))
     (7 7 (:REWRITE INTEGERP-MINUS-X))
     (7 7 (:META META-INTEGERP-CORRECT))
     (6 6 (:TYPE-PRESCRIPTION PREFIXP))
     (6 6
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (6 6
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (6 6
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (6 6 (:REWRITE |(equal c (/ x))|))
     (6 6 (:REWRITE |(equal c (- x))|))
     (6 6 (:REWRITE |(equal (/ x) c)|))
     (6 6 (:REWRITE |(equal (/ x) (/ y))|))
     (6 6 (:REWRITE |(equal (- x) c)|))
     (6 6 (:REWRITE |(equal (- x) (- y))|))
     (4 4 (:REWRITE ZP-OPEN))
     (4 4 (:REWRITE THE-FLOOR-BELOW))
     (4 4 (:REWRITE THE-FLOOR-ABOVE))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
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
     (4 4 (:REWRITE DEFAULT-LESS-THAN-2))
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
     (4 4
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (4 4
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (4 4
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (4 4
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (4 4 (:REWRITE |(< (/ x) 0)|))
     (4 4 (:REWRITE |(< (/ x) (/ y))|))
     (4 4 (:REWRITE |(< (- x) c)|))
     (4 4 (:REWRITE |(< (- x) (- y))|))
     (4 4 (:REWRITE |(< (* x y) 0)|))
     (3 3 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (3 3 (:REWRITE FM9001::SYMBOL-INEQUALITY))
     (3 3 (:REWRITE REDUCE-RATIONALP-+))
     (3 3 (:REWRITE REDUCE-RATIONALP-*))
     (3 3 (:REWRITE RATIONALP-MINUS-X))
     (3 3
        (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
     (3 3
        (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
     (3 3 (:REWRITE PREFIXP-TRANSITIVE . 2))
     (3 3 (:REWRITE PREFIXP-TRANSITIVE . 1))
     (3 3
        (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
     (3 3
        (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
     (3 3 (:META META-RATIONALP-CORRECT)))
(FM9001::DISJOINT-SIS-DIFF-SYMS
     (2809 11
           (:REWRITE STR::IPREFIXP-WHEN-PREFIXP))
     (2686 86 (:REWRITE STR::CONSP-OF-EXPLODE))
     (1885 49
           (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
     (1362 41 (:DEFINITION LEN))
     (916 64
          (:REWRITE FM9001::NOT-PREFIXP-NOT-EQUAL))
     (534 30
          (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
     (481 11
          (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
     (418 418 (:TYPE-PRESCRIPTION LEN))
     (391 11
          (:REWRITE STR::IPREFIXP-WHEN-NOT-CONSP-RIGHT))
     (380 380
          (:TYPE-PRESCRIPTION FM9001::STR-APPEND-SYMBOL-UNDERSCORE))
     (361 11
          (:REWRITE STR::IPREFIXP-WHEN-NOT-CONSP-LEFT))
     (335 1
          (:REWRITE FM9001::SI-SIS-DIFF-SYMBOLS-2))
     (212 43 (:REWRITE DEFAULT-PLUS-2))
     (177 136
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (177 136
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (158 136 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (150 150
          (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
     (136 136
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (136 136
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (136 136
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (136 136 (:REWRITE |(equal c (/ x))|))
     (136 136 (:REWRITE |(equal c (- x))|))
     (136 136 (:REWRITE |(equal (/ x) c)|))
     (136 136 (:REWRITE |(equal (/ x) (/ y))|))
     (136 136 (:REWRITE |(equal (- x) c)|))
     (136 136 (:REWRITE |(equal (- x) (- y))|))
     (126 14 (:REWRITE ACL2-NUMBERP-X))
     (109 22 (:REWRITE DEFAULT-CDR))
     (104 104 (:LINEAR LEN-WHEN-PREFIXP))
     (88 44
         (:TYPE-PRESCRIPTION FM9001::CONSP-SIS))
     (80 8 (:DEFINITION ATOM))
     (64 64 (:REWRITE FM9001::SYMBOL-INEQUALITY))
     (60 60 (:TYPE-PRESCRIPTION PREFIXP))
     (56 14 (:REWRITE RATIONALP-X))
     (52 52
         (:LINEAR FM9001::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
     (49 49 (:REWRITE PREFIXP-TRANSITIVE . 2))
     (49 49 (:REWRITE PREFIXP-TRANSITIVE . 1))
     (49 49
         (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
     (49 49
         (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
     (44 44 (:TYPE-PRESCRIPTION FM9001::SIS))
     (44 44 (:TYPE-PRESCRIPTION POSP))
     (43 22
         (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
     (37 19
         (:REWRITE LIST-EQUIV-WHEN-ATOM-RIGHT))
     (36 36
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (36 36 (:REWRITE NORMALIZE-ADDENDS))
     (36 36 (:REWRITE DEFAULT-PLUS-1))
     (19 19
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (14 14 (:REWRITE REDUCE-RATIONALP-+))
     (14 14 (:REWRITE REDUCE-RATIONALP-*))
     (14 14 (:REWRITE REDUCE-INTEGERP-+))
     (14 14 (:REWRITE RATIONALP-MINUS-X))
     (14 14 (:REWRITE INTEGERP-MINUS-X))
     (14 14 (:META META-RATIONALP-CORRECT))
     (14 14 (:META META-INTEGERP-CORRECT))
     (9 9 (:REWRITE ZP-OPEN))
     (4 4 (:TYPE-PRESCRIPTION ATOM))
     (2 1 (:REWRITE DEFAULT-SYMBOL-NAME))
     (1 1 (:TYPE-PRESCRIPTION FM9001::SI)))
(FM9001::SI-MEMBER-SIS
     (2709 13
           (:DEFINITION STR::ISTRPREFIXP$INLINE))
     (2178 13
           (:REWRITE STR::IPREFIXP-WHEN-PREFIXP))
     (1952 70 (:REWRITE STR::CONSP-OF-EXPLODE))
     (1712 45
           (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
     (1251 4
           (:REWRITE FM9001::SI-SIS-DIFF-SYMBOLS-2))
     (1074 4
           (:REWRITE FM9001::SI-OF-DIFF-SYMBOLS-2))
     (882 35 (:DEFINITION LEN))
     (760 68
          (:REWRITE FM9001::NOT-PREFIXP-NOT-EQUAL))
     (354 28
          (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
     (348 4
          (:REWRITE FM9001::SI-SIS-DIFF-SYMBOLS-1))
     (315 315 (:TYPE-PRESCRIPTION LEN))
     (272 11
          (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
     (248 8
          (:REWRITE STR::IPREFIXP-WHEN-NOT-CONSP-RIGHT))
     (218 8
          (:REWRITE STR::IPREFIXP-WHEN-NOT-CONSP-LEFT))
     (198 17
          (:REWRITE LIST-EQUIV-WHEN-ATOM-RIGHT))
     (180 180
          (:TYPE-PRESCRIPTION FM9001::STR-APPEND-SYMBOL-UNDERSCORE))
     (180 5 (:REWRITE LIST-EQUIV-WHEN-ATOM-LEFT))
     (160 126
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (158 126
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (146 126 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (128 128
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (128 128
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (128 128 (:REWRITE |(equal c (/ x))|))
     (128 128 (:REWRITE |(equal (/ x) (/ y))|))
     (128 128 (:REWRITE |(equal (- x) (- y))|))
     (126 126
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (126 126 (:REWRITE |(equal c (- x))|))
     (126 126 (:REWRITE |(equal (- x) c)|))
     (124 124
          (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
     (111 68 (:REWRITE FM9001::SYMBOL-INEQUALITY))
     (87 1
         (:REWRITE FM9001::SI-OF-DIFF-SYMBOLS-1))
     (86 67 (:REWRITE DEFAULT-PLUS-2))
     (86 23 (:REWRITE DEFAULT-CDR))
     (76 76 (:LINEAR LEN-WHEN-PREFIXP))
     (73 67 (:REWRITE DEFAULT-PLUS-1))
     (68 2 (:REWRITE ZP-OPEN))
     (60 2
         (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (60 2 (:REWRITE |(< x (/ y)) with (< 0 y)|))
     (58 4 (:REWRITE FM9001::SI-SIS-DIFF-IDXES))
     (53 53 (:TYPE-PRESCRIPTION PREFIXP))
     (45 45 (:REWRITE PREFIXP-TRANSITIVE . 2))
     (45 45 (:REWRITE PREFIXP-TRANSITIVE . 1))
     (45 45
         (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
     (45 45
         (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
     (44 26
         (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
     (42 42 (:REWRITE THE-FLOOR-BELOW))
     (42 42 (:REWRITE THE-FLOOR-ABOVE))
     (42 42 (:REWRITE DEFAULT-LESS-THAN-2))
     (42 42 (:REWRITE DEFAULT-LESS-THAN-1))
     (41 41
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (38 38
         (:LINEAR FM9001::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
     (36 36
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (36 36
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (36 36
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
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
     (34 34 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (30 30 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (29 10 (:REWRITE DEFAULT-SYMBOL-NAME))
     (24 1 (:REWRITE FM9001::SI-OF-DIFF-IDXES))
     (21 8 (:REWRITE DEFAULT-CAR))
     (20 20
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (16 4 (:REWRITE |(+ c (+ d x))|))
     (15 15
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (15 15
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (15 15 (:REWRITE |(< 0 (/ x))|))
     (15 15 (:REWRITE |(< 0 (* x y))|))
     (13 13
         (:TYPE-PRESCRIPTION STR::ISTRPREFIXP$INLINE))
     (13 13 (:REWRITE REDUCE-INTEGERP-+))
     (13 13 (:REWRITE INTEGERP-MINUS-X))
     (13 13 (:META META-INTEGERP-CORRECT))
     (12 12 (:REWRITE DEFAULT-TIMES-2))
     (12 12 (:REWRITE DEFAULT-TIMES-1))
     (10 10 (:REWRITE |(< y (+ (- c) x))|))
     (10 10 (:REWRITE |(< x (+ c/d y))|))
     (8 8 (:TYPE-PRESCRIPTION STR::IPREFIXP))
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (8 8 (:REWRITE |(< (/ x) 0)|))
     (8 8 (:REWRITE |(< (* x y) 0)|))
     (6 6 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (5 5 (:TYPE-PRESCRIPTION LIST-EQUIV))
     (2 2 (:REWRITE DEFAULT-DIVIDE))
     (2 2 (:REWRITE |(not (equal x (/ y)))|))
     (2 2 (:REWRITE |(equal x (/ y))|))
     (2 2
        (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (2 2
        (:REWRITE |(< x (/ y)) with (< y 0)|)))
(FM9001::SI-IS-NTH-OF-SIS
     (1695 6 (:DEFINITION STR::ISTRPREFIXP$INLINE))
     (1628 5
           (:REWRITE FM9001::SI-OF-DIFF-SYMBOLS-2))
     (1330 6 (:REWRITE STR::IPREFIXP-WHEN-PREFIXP))
     (1256 42 (:REWRITE STR::CONSP-OF-EXPLODE))
     (1057 36
           (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
     (662 48
          (:REWRITE FM9001::NOT-PREFIXP-NOT-EQUAL))
     (636 29 (:DEFINITION LEN))
     (244 244 (:TYPE-PRESCRIPTION LEN))
     (234 8
          (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
     (228 24
          (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
     (180 5
          (:REWRITE STR::IPREFIXP-WHEN-NOT-CONSP-LEFT))
     (169 3
          (:REWRITE FM9001::NOT-MEMBER=>NOT-EQUAL-NTH))
     (155 5
          (:REWRITE STR::IPREFIXP-WHEN-NOT-CONSP-RIGHT))
     (146 47 (:REWRITE |(< c (- x))|))
     (133 48
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (129 116 (:REWRITE DEFAULT-PLUS-2))
     (129 116 (:REWRITE DEFAULT-PLUS-1))
     (110 84
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (110 84
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (109 48 (:REWRITE FM9001::SYMBOL-INEQUALITY))
     (104 104
          (:TYPE-PRESCRIPTION FM9001::STR-APPEND-SYMBOL-UNDERSCORE))
     (98 84 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (87 1
         (:REWRITE FM9001::SI-OF-DIFF-SYMBOLS-1))
     (86 86
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (86 86
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (86 86 (:REWRITE |(equal c (/ x))|))
     (86 86 (:REWRITE |(equal (/ x) (/ y))|))
     (86 86 (:REWRITE |(equal (- x) (- y))|))
     (84 84
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (84 84 (:REWRITE |(equal c (- x))|))
     (84 84 (:REWRITE |(equal (- x) c)|))
     (74 74
         (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
     (64 2 (:REWRITE FM9001::LEN-SIS))
     (62 2 (:DEFINITION NFIX))
     (60 2
         (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (60 2 (:REWRITE |(< x (/ y)) with (< 0 y)|))
     (59 17 (:REWRITE DEFAULT-CDR))
     (56 12
         (:REWRITE LIST-EQUIV-WHEN-ATOM-RIGHT))
     (54 54 (:REWRITE THE-FLOOR-BELOW))
     (54 54 (:REWRITE THE-FLOOR-ABOVE))
     (54 54 (:REWRITE DEFAULT-LESS-THAN-2))
     (54 54 (:REWRITE DEFAULT-LESS-THAN-1))
     (54 54 (:LINEAR LEN-WHEN-PREFIXP))
     (49 49
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (48 48
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (48 48
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (47 47
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (47 47
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (47 47
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (47 47
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (47 47
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (47 47
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (47 47
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (47 47
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (47 47 (:REWRITE |(< (/ x) (/ y))|))
     (47 47 (:REWRITE |(< (- x) (- y))|))
     (46 46
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (46 46 (:REWRITE INTEGERP-<-CONSTANT))
     (46 46 (:REWRITE CONSTANT-<-INTEGERP))
     (46 46 (:REWRITE |(< (- x) c)|))
     (42 42 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (41 41 (:TYPE-PRESCRIPTION PREFIXP))
     (36 36 (:REWRITE PREFIXP-TRANSITIVE . 2))
     (36 36 (:REWRITE PREFIXP-TRANSITIVE . 1))
     (36 36
         (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
     (36 36
         (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
     (36 1 (:REWRITE LIST-EQUIV-WHEN-ATOM-LEFT))
     (33 13 (:REWRITE |(+ c (+ d x))|))
     (27 27
         (:LINEAR FM9001::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
     (24 1 (:REWRITE FM9001::SI-OF-DIFF-IDXES))
     (19 19 (:REWRITE |(< 0 (/ x))|))
     (19 19 (:REWRITE |(< 0 (* x y))|))
     (19 12
         (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
     (18 18
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (17 9 (:REWRITE DEFAULT-SYMBOL-NAME))
     (15 15
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (15 15
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (13 13 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (13 13 (:REWRITE REDUCE-INTEGERP-+))
     (13 13 (:REWRITE INTEGERP-MINUS-X))
     (13 13 (:REWRITE |(< y (+ (- c) x))|))
     (13 13 (:REWRITE |(< x (+ c/d y))|))
     (13 13 (:META META-INTEGERP-CORRECT))
     (12 12 (:REWRITE DEFAULT-TIMES-2))
     (12 12 (:REWRITE DEFAULT-TIMES-1))
     (12 12 (:REWRITE |(< (* x y) 0)|))
     (11 11 (:REWRITE |(< (/ x) 0)|))
     (11 4 (:REWRITE DEFAULT-CAR))
     (10 10
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (10 10
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (10 10 (:REWRITE DEFAULT-MINUS))
     (8 8 (:REWRITE NTH-WHEN-PREFIXP))
     (6 6
        (:TYPE-PRESCRIPTION STR::ISTRPREFIXP$INLINE))
     (6 6 (:REWRITE FOLD-CONSTS-IN-+))
     (5 5 (:TYPE-PRESCRIPTION STR::IPREFIXP))
     (4 4 (:REWRITE |(< (+ c/d x) y)|))
     (3 3 (:REWRITE |(< (+ (- c) x) y)|))
     (2 2 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (2 2 (:REWRITE FM9001::SI-MEMBER-SIS))
     (2 2 (:REWRITE DEFAULT-DIVIDE))
     (2 2 (:REWRITE |(not (equal x (/ y)))|))
     (2 2 (:REWRITE |(equal x (/ y))|))
     (2 2
        (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (2 2 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (1 1 (:TYPE-PRESCRIPTION LIST-EQUIV))
     (1 1 (:REWRITE |(- (- x))|)))
