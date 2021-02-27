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
        (:REWRITE-QUOTED-CONSTANT FIX-UNDER-NUMBER-EQUIV))
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
     (1022 1022
           (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (1022 1022
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (1022 1022
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (1022 1022
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
     (1722 1722
           (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (1722 1722
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (1722 1722
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (1722 1722
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
         (:REWRITE STR::CHARACTER-LISTP-WHEN-DEC-DIGIT-CHAR-LISTP))
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
     (6 6
        (:TYPE-PRESCRIPTION STR::DEC-DIGIT-CHAR-LISTP))
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
        (:REWRITE DEFAULT-INTERN-IN-PACKAGE-OF-SYMBOL))
     (6 3
        (:REWRITE STR::DEC-DIGIT-CHAR-LISTP-WHEN-NOT-CONSP))
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
(FM9001::NOT-PREFIXP-NOT-EQUAL (2 2 (:REWRITE LIST-EQUIV-WHEN-ATOM-RIGHT))
                               (2 2 (:REWRITE LIST-EQUIV-WHEN-ATOM-LEFT))
                               (1 1 (:REWRITE PREFIXP-TRANSITIVE . 2))
                               (1 1 (:REWRITE PREFIXP-TRANSITIVE . 1))
                               (1 1
                                  (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
                               (1 1
                                  (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1)))
(FM9001::PREFIXP-APPEND-RELATION-1
     (14234 178
            (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
     (9770 178 (:REWRITE PREFIXP-WHEN-PREFIXP))
     (5696 650 (:DEFINITION LEN))
     (5390 5390 (:TYPE-PRESCRIPTION LEN))
     (3849 31
           (:REWRITE FM9001::NOT-PREFIXP-NOT-EQUAL))
     (2859 249
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (2545 1230 (:LINEAR LEN-WHEN-PREFIXP))
     (2178 1029 (:REWRITE DEFAULT-PLUS-2))
     (2028 78 (:REWRITE LEN-OF-APPEND))
     (1422 18
           (:REWRITE PREFIXP-OF-APPEND-WHEN-SAME-LENGTH))
     (1185 1029 (:REWRITE DEFAULT-PLUS-1))
     (1160 580
           (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
     (1089 753 (:REWRITE DEFAULT-CDR))
     (1035 227
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (819 819
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (819 819 (:REWRITE NORMALIZE-ADDENDS))
     (804 44 (:REWRITE |(+ y (+ x z))|))
     (707 227
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (704 227 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (621 621
          (:LINEAR FM9001::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
     (580 580 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (580 580 (:TYPE-PRESCRIPTION BINARY-APPEND))
     (546 78 (:REWRITE |(+ y x)|))
     (451 123 (:REWRITE ACL2-NUMBERP-X))
     (360 92 (:REWRITE |(+ c (+ d x))|))
     (258 186 (:REWRITE DEFAULT-CAR))
     (249 249
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (227 227
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (227 227 (:REWRITE |(equal c (/ x))|))
     (227 227 (:REWRITE |(equal c (- x))|))
     (227 227 (:REWRITE |(equal (/ x) c)|))
     (227 227 (:REWRITE |(equal (/ x) (/ y))|))
     (227 227 (:REWRITE |(equal (- x) c)|))
     (227 227 (:REWRITE |(equal (- x) (- y))|))
     (178 178 (:REWRITE PREFIXP-TRANSITIVE . 2))
     (178 178 (:REWRITE PREFIXP-TRANSITIVE . 1))
     (178 178
          (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
     (178 178
          (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
     (164 41 (:REWRITE RATIONALP-X))
     (112 44 (:REWRITE |(+ 0 x)|))
     (51 51 (:REWRITE |(equal (+ (- c) x) y)|))
     (48 48 (:REWRITE FOLD-CONSTS-IN-+))
     (48 48 (:REWRITE APPEND-WHEN-NOT-CONSP))
     (48 48
         (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
     (41 41 (:REWRITE REDUCE-RATIONALP-+))
     (41 41 (:REWRITE REDUCE-RATIONALP-*))
     (41 41 (:REWRITE REDUCE-INTEGERP-+))
     (41 41 (:REWRITE RATIONALP-MINUS-X))
     (41 41 (:REWRITE INTEGERP-MINUS-X))
     (41 41 (:META META-RATIONALP-CORRECT))
     (41 41 (:META META-INTEGERP-CORRECT))
     (36 36 (:REWRITE CDR-OF-APPEND-WHEN-CONSP))
     (31 31 (:REWRITE FM9001::SYMBOL-INEQUALITY))
     (21 21 (:REWRITE |(equal x (if a b c))|))
     (21 21 (:REWRITE |(equal (if a b c) x)|))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(FM9001::PREFIXP-APPEND-RELATION-2
     (830 6 (:DEFINITION PREFIXP))
     (394 394 (:TYPE-PRESCRIPTION LEN))
     (307 18
          (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
     (287 41 (:DEFINITION LEN))
     (284 21 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (280 17 (:REWRITE PREFIXP-TRANSITIVE . 1))
     (220 72 (:LINEAR LEN-WHEN-PREFIXP))
     (182 7 (:REWRITE LEN-OF-APPEND))
     (181 18
          (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
     (164 82 (:REWRITE DEFAULT-PLUS-2))
     (157 16 (:REWRITE |(+ y x)|))
     (126 82 (:REWRITE DEFAULT-PLUS-1))
     (108 54 (:REWRITE NORMALIZE-ADDENDS))
     (97 21
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (87 3 (:REWRITE |(+ y (+ x z))|))
     (57 21
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (55 15 (:REWRITE ACL2-NUMBERP-X))
     (54 54 (:REWRITE DEFAULT-CDR))
     (48 48
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (36 36
         (:LINEAR FM9001::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
     (29 15
         (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
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
     (20 5 (:REWRITE RATIONALP-X))
     (18 9 (:DEFINITION FIX))
     (15 15
         (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
     (13 13 (:REWRITE DEFAULT-CAR))
     (12 6 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (12 6 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
     (10 5
         (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
     (9 1 (:REWRITE CDR-OF-APPEND-WHEN-CONSP))
     (6 6 (:REWRITE |(+ x (- x))|))
     (6 3 (:REWRITE |(+ 0 x)|))
     (5 5 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (5 5 (:TYPE-PRESCRIPTION BINARY-APPEND))
     (5 5 (:REWRITE REDUCE-RATIONALP-+))
     (5 5 (:REWRITE REDUCE-RATIONALP-*))
     (5 5 (:REWRITE REDUCE-INTEGERP-+))
     (5 5 (:REWRITE RATIONALP-MINUS-X))
     (5 5 (:REWRITE INTEGERP-MINUS-X))
     (5 5 (:META META-RATIONALP-CORRECT))
     (5 5 (:META META-INTEGERP-CORRECT))
     (5 1 (:DEFINITION BINARY-APPEND))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (3 3 (:REWRITE CONSP-OF-APPEND))
     (3 3 (:REWRITE |(equal (+ (- c) x) y)|))
     (2 2 (:REWRITE LIST-EQUIV-WHEN-ATOM-RIGHT))
     (2 2 (:REWRITE LIST-EQUIV-WHEN-ATOM-LEFT))
     (2 2 (:REWRITE APPEND-WHEN-NOT-CONSP))
     (2 2
        (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
     (2 1 (:REWRITE CAR-OF-APPEND)))
(FM9001::ISTRPREFIXP-PREFIXP-EXPLODE-RELATION
     (2 2
        (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP)))
(FM9001::ISTRPREFIXP-STRING-APPEND-RELATION-1
     (3247 1
           (:REWRITE FM9001::PREFIXP-APPEND-RELATION-2))
     (2997 95 (:REWRITE STR::CONSP-OF-EXPLODE))
     (2900 141 (:REWRITE PREFIXP-WHEN-PREFIXP))
     (2389 76
           (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
     (1888 70 (:DEFINITION LEN))
     (1670 1 (:REWRITE PREFIXP-OF-APPEND-ARG2))
     (1151 1 (:REWRITE PREFIXP-OF-APPEND-ARG1))
     (803 4 (:REWRITE STR::IPREFIXP-WHEN-PREFIXP))
     (736 736 (:TYPE-PRESCRIPTION LEN))
     (404 2 (:DEFINITION TAKE))
     (309 39 (:REWRITE DEFAULT-CDR))
     (288 9
          (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
     (280 37
          (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
     (232 4 (:REWRITE TAKE-OF-LEN-FREE))
     (230 102
          (:REWRITE LIST-EQUIV-WHEN-ATOM-RIGHT))
     (224 6 (:REWRITE ZP-OPEN))
     (221 3 (:REWRITE FM9001::LEN-NTHCDR))
     (193 139
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (191 139
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (188 2 (:DEFINITION NTHCDR))
     (184 4
          (:REWRITE STR::IPREFIXP-WHEN-NOT-CONSP-RIGHT))
     (184 4
          (:REWRITE STR::IPREFIXP-WHEN-NOT-CONSP-LEFT))
     (184 4
          (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
     (182 2 (:DEFINITION BINARY-APPEND))
     (167 1
          (:REWRITE PREFIXP-OF-APPEND-WHEN-SAME-LENGTH))
     (165 139 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (160 2 (:REWRITE CONSP-OF-TAKE))
     (152 152 (:LINEAR LEN-WHEN-PREFIXP))
     (141 141
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (141 141
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (139 139
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (139 139 (:REWRITE |(equal c (/ x))|))
     (139 139 (:REWRITE |(equal c (- x))|))
     (139 139 (:REWRITE |(equal (/ x) c)|))
     (139 139 (:REWRITE |(equal (/ x) (/ y))|))
     (139 139 (:REWRITE |(equal (- x) c)|))
     (139 139 (:REWRITE |(equal (- x) (- y))|))
     (135 1 (:REWRITE LEN-OF-APPEND))
     (130 2 (:REWRITE LIST-EQUIV-WHEN-ATOM-LEFT))
     (100 4 (:REWRITE DEFAULT-CAR))
     (100 4 (:REWRITE APPEND-WHEN-NOT-CONSP))
     (80 43 (:REWRITE DEFAULT-PLUS-2))
     (77 5 (:REWRITE |(equal (+ (- c) x) y)|))
     (76 76 (:REWRITE PREFIXP-TRANSITIVE . 2))
     (76 76 (:REWRITE PREFIXP-TRANSITIVE . 1))
     (76 76
         (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
     (76 76
         (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
     (76 76
         (:LINEAR FM9001::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
     (74 2 (:REWRITE LEN-OF-TAKE))
     (72 2 (:DEFINITION NFIX))
     (69 65 (:REWRITE FM9001::SYMBOL-INEQUALITY))
     (45 43 (:REWRITE DEFAULT-PLUS-1))
     (45 15
         (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
     (41 41
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (41 41 (:REWRITE NORMALIZE-ADDENDS))
     (40 6
         (:REWRITE STR::CHARACTER-LISTP-WHEN-DEC-DIGIT-CHAR-LISTP))
     (30 14
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (30 14 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (28 28
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (28 14 (:REWRITE DEFAULT-LESS-THAN-2))
     (24 14 (:REWRITE SIMPLIFY-SUMS-<))
     (20 14 (:REWRITE DEFAULT-LESS-THAN-1))
     (16 16
         (:TYPE-PRESCRIPTION STR::DEC-DIGIT-CHAR-LISTP))
     (16 16
         (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
     (16 8
         (:REWRITE STR::DEC-DIGIT-CHAR-LISTP-WHEN-NOT-CONSP))
     (16 2
         (:REWRITE STR::DEC-DIGIT-CHAR-LISTP-OF-APPEND))
     (14 14 (:REWRITE THE-FLOOR-BELOW))
     (14 14 (:REWRITE THE-FLOOR-ABOVE))
     (14 14 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (14 14
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (14 14
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (14 14
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (14 14
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
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
     (13 13 (:TYPE-PRESCRIPTION TRUE-LISTP-TAKE))
     (10 2 (:REWRITE |(+ y x)|))
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (8 8 (:REWRITE |(< 0 (/ x))|))
     (8 8 (:REWRITE |(< 0 (* x y))|))
     (4 2 (:REWRITE LIST-FIX-WHEN-TRUE-LISTP))
     (2 2 (:TYPE-PRESCRIPTION LIST-EQUIV))
     (2 2 (:REWRITE TAKE-WHEN-PREFIXP))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (2 2 (:REWRITE LEN-WHEN-PREFIXP))
     (2 2 (:REWRITE |(< y (+ (- c) x))|))
     (2 2 (:REWRITE |(< x (+ c/d y))|))
     (2 2 (:REWRITE |(< (/ x) 0)|))
     (2 2 (:REWRITE |(< (* x y) 0)|)))
(FM9001::APPEND-DIFF-SYMBOLS-STRING-1 (6 6 (:REWRITE DEFAULT-SYMBOL-NAME)))
(FM9001::ISTRPREFIXP-STRING-APPEND-RELATION-2
     (1011 1 (:REWRITE PREFIXP-OF-APPEND-ARG1))
     (928 32 (:REWRITE STR::CONSP-OF-EXPLODE))
     (712 19 (:DEFINITION LEN))
     (546 19
          (:REWRITE FM9001::NOT-PREFIXP-NOT-EQUAL))
     (250 250 (:TYPE-PRESCRIPTION LEN))
     (185 1 (:REWRITE FM9001::LEN-NTHCDR))
     (135 1 (:REWRITE LEN-OF-APPEND))
     (119 39 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (104 1 (:REWRITE TAKE-WHEN-PREFIXP))
     (95 5 (:REWRITE SIMPLIFY-SUMS-<))
     (94 13 (:REWRITE DEFAULT-CDR))
     (94 4 (:REWRITE LIST-EQUIV-WHEN-ATOM-LEFT))
     (94 1 (:DEFINITION NTHCDR))
     (92 2
         (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
     (91 1 (:DEFINITION BINARY-APPEND))
     (83 31
         (:REWRITE LIST-EQUIV-WHEN-ATOM-RIGHT))
     (78 21 (:REWRITE NORMALIZE-ADDENDS))
     (70 33 (:REWRITE DEFAULT-PLUS-2))
     (58 2 (:REWRITE |(+ y (+ x z))|))
     (56 33 (:REWRITE DEFAULT-PLUS-1))
     (54 39
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (54 39
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (50 2 (:REWRITE APPEND-WHEN-NOT-CONSP))
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
     (37 1 (:REWRITE ZP-OPEN))
     (36 1 (:DEFINITION NFIX))
     (35 3 (:REWRITE |(+ y x)|))
     (28 28 (:LINEAR LEN-WHEN-PREFIXP))
     (23 23 (:REWRITE PREFIXP-TRANSITIVE . 2))
     (23 23 (:REWRITE PREFIXP-TRANSITIVE . 1))
     (23 23
         (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
     (23 23
         (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
     (19 19 (:REWRITE FM9001::SYMBOL-INEQUALITY))
     (16 16
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (14 14
         (:LINEAR FM9001::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
     (14 7 (:DEFINITION FIX))
     (14 2 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
     (12 12
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (11 11
         (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
     (11 5 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (10 5 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (10 5
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (10 5 (:REWRITE DEFAULT-LESS-THAN-2))
     (9 3
        (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
     (7 5 (:REWRITE DEFAULT-LESS-THAN-1))
     (6 3 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
     (5 5 (:REWRITE THE-FLOOR-BELOW))
     (5 5 (:REWRITE THE-FLOOR-ABOVE))
     (5 5 (:REWRITE REMOVE-WEAK-INEQUALITIES))
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
     (5 5 (:REWRITE |(< (/ x) (/ y))|))
     (5 5 (:REWRITE |(< (- x) c)|))
     (5 5 (:REWRITE |(< (- x) (- y))|))
     (5 5 (:REWRITE |(+ x (- x))|))
     (4 2 (:REWRITE LIST-FIX-WHEN-TRUE-LISTP))
     (4 2 (:REWRITE |(+ 0 x)|))
     (4 1 (:REWRITE DEFAULT-CAR))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (3 3
        (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
     (3 3 (:REWRITE |(< 0 (/ x))|))
     (3 3 (:REWRITE |(< 0 (* x y))|))
     (2 2 (:REWRITE |(+ c (+ d x))|))
     (2 1 (:REWRITE DEFAULT-MINUS))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (1 1 (:REWRITE |(equal (+ (- c) x) y)|))
     (1 1 (:REWRITE |(< y (+ (- c) x))|))
     (1 1 (:REWRITE |(< x (+ c/d y))|))
     (1 1 (:REWRITE |(< (/ x) 0)|))
     (1 1 (:REWRITE |(< (* x y) 0)|)))
(FM9001::APPEND-DIFF-SYMBOLS-STRING-2 (4 4 (:REWRITE DEFAULT-SYMBOL-NAME)))
(FM9001::SI-OF-DIFF-SYMBOLS-1
     (1461 4 (:REWRITE STR::IPREFIXP-WHEN-PREFIXP))
     (1254 44 (:REWRITE STR::CONSP-OF-EXPLODE))
     (932 34 (:REWRITE PREFIXP-WHEN-PREFIXP))
     (910 21
          (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
     (636 20 (:DEFINITION LEN))
     (403 33
          (:REWRITE FM9001::NOT-PREFIXP-NOT-EQUAL))
     (284 14
          (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
     (272 8
          (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
     (198 198
          (:TYPE-PRESCRIPTION FM9001::STR-APPEND-SYMBOL-UNDERSCORE))
     (182 182 (:TYPE-PRESCRIPTION LEN))
     (144 4
          (:REWRITE STR::IPREFIXP-WHEN-NOT-CONSP-RIGHT))
     (144 4
          (:REWRITE STR::IPREFIXP-WHEN-NOT-CONSP-LEFT))
     (82 64
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (82 64
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (76 76
         (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
     (76 64 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (64 64
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (64 64
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (64 64
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (64 64 (:REWRITE |(equal c (/ x))|))
     (64 64 (:REWRITE |(equal c (- x))|))
     (64 64 (:REWRITE |(equal (/ x) c)|))
     (64 64 (:REWRITE |(equal (/ x) (/ y))|))
     (64 64 (:REWRITE |(equal (- x) c)|))
     (64 64 (:REWRITE |(equal (- x) (- y))|))
     (60 12 (:REWRITE DEFAULT-CDR))
     (58 58 (:TYPE-PRESCRIPTION PREFIXP))
     (48 48 (:LINEAR LEN-WHEN-PREFIXP))
     (46 20
         (:REWRITE LIST-EQUIV-WHEN-ATOM-RIGHT))
     (24 24
         (:LINEAR FM9001::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
     (24 12 (:REWRITE DEFAULT-PLUS-2))
     (21 21 (:REWRITE PREFIXP-TRANSITIVE . 2))
     (21 21 (:REWRITE PREFIXP-TRANSITIVE . 1))
     (21 21
         (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
     (21 21
         (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
     (16 8
         (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
     (12 12
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (12 12 (:REWRITE NORMALIZE-ADDENDS))
     (12 12 (:REWRITE DEFAULT-PLUS-1))
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
     (728 1 (:REWRITE PREFIXP-OF-APPEND-ARG1))
     (503 31 (:REWRITE STR::CONSP-OF-EXPLODE))
     (398 13 (:DEFINITION LEN))
     (144 13 (:REWRITE DEFAULT-CDR))
     (139 139 (:TYPE-PRESCRIPTION LEN))
     (121 1 (:REWRITE FM9001::LEN-NTHCDR))
     (107 27 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (96 6 (:REWRITE SIMPLIFY-SUMS-<))
     (85 1 (:REWRITE LEN-OF-APPEND))
     (84 1 (:REWRITE TAKE-WHEN-PREFIXP))
     (84 1 (:DEFINITION NTHCDR))
     (78 21 (:REWRITE NORMALIZE-ADDENDS))
     (71 71
         (:TYPE-PRESCRIPTION FM9001::STR-APPEND-SYMBOL-UNDERSCORE))
     (70 33 (:REWRITE DEFAULT-PLUS-2))
     (59 4 (:REWRITE LIST-EQUIV-WHEN-ATOM-LEFT))
     (58 2 (:REWRITE APPEND-WHEN-NOT-CONSP))
     (58 2 (:REWRITE |(+ y (+ x z))|))
     (57 21
         (:REWRITE FM9001::NOT-PREFIXP-NOT-EQUAL))
     (56 33 (:REWRITE DEFAULT-PLUS-1))
     (56 8 (:REWRITE LIST-EQUIV-WHEN-ATOM-RIGHT))
     (40 2
         (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
     (37 1 (:REWRITE ZP-OPEN))
     (37 1 (:DEFINITION BINARY-APPEND))
     (35 3 (:REWRITE |(+ y x)|))
     (31 27
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (31 27
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
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
     (21 21 (:REWRITE FM9001::SYMBOL-INEQUALITY))
     (20 20
         (:TYPE-PRESCRIPTION STR::STRINGP-OF-NATSTR))
     (16 16
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (14 7 (:DEFINITION FIX))
     (14 2 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
     (12 6 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (11 6
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (11 6 (:REWRITE DEFAULT-LESS-THAN-2))
     (10 5 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (9 3
        (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
     (8 8 (:REWRITE STR::NATSTR-NONEMPTY))
     (8 6 (:REWRITE DEFAULT-LESS-THAN-1))
     (6 6 (:REWRITE THE-FLOOR-BELOW))
     (6 6 (:REWRITE THE-FLOOR-ABOVE))
     (6 6 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (6 6 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (6 6
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (6 6
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (6 6 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (6 6 (:REWRITE PREFIXP-TRANSITIVE . 2))
     (6 6 (:REWRITE PREFIXP-TRANSITIVE . 1))
     (6 6
        (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
     (6 6
        (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
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
     (6 6 (:LINEAR LEN-WHEN-PREFIXP))
     (6 3
        (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
     (6 3 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
     (5 5 (:REWRITE |(+ x (- x))|))
     (5 1 (:REWRITE DEFAULT-CAR))
     (4 2 (:REWRITE LIST-FIX-WHEN-TRUE-LISTP))
     (4 2 (:REWRITE |(+ 0 x)|))
     (4 1
        (:REWRITE INTERN-IN-PACKAGE-OF-SYMBOL-IS-IDENTITY))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (3 3 (:REWRITE |(< 0 (/ x))|))
     (3 3 (:REWRITE |(< 0 (* x y))|))
     (3 3
        (:LINEAR FM9001::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
     (3 1 (:REWRITE DEFAULT-SYMBOL-NAME))
     (2 2
        (:TYPE-PRESCRIPTION MEMBER-SYMBOL-NAME))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (2 2 (:REWRITE |(< (/ x) 0)|))
     (2 2 (:REWRITE |(< (* x y) 0)|))
     (2 2 (:REWRITE |(+ c (+ d x))|))
     (2 1 (:REWRITE DEFAULT-MINUS))
     (2 1
        (:REWRITE DEFAULT-INTERN-IN-PACKAGE-OF-SYMBOL))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (1 1 (:REWRITE REDUCE-INTEGERP-+))
     (1 1 (:REWRITE INTEGERP-MINUS-X))
     (1 1 (:REWRITE |(equal (+ (- c) x) y)|))
     (1 1 (:REWRITE |(< y (+ (- c) x))|))
     (1 1 (:REWRITE |(< x (+ c/d y))|))
     (1 1 (:META META-INTEGERP-CORRECT)))
(FM9001::APPEND-SYMBOL-DIFF-STRINGS
     (5052 98
           (:REWRITE FM9001::NOT-PREFIXP-NOT-EQUAL))
     (4661 5 (:REWRITE PREFIXP-OF-APPEND-ARG1))
     (3811 43 (:REWRITE PREFIXP-WHEN-PREFIXP))
     (2193 159 (:REWRITE STR::CONSP-OF-EXPLODE))
     (2049 28
           (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
     (1978 5 (:REWRITE TAKE-WHEN-PREFIXP))
     (1837 68 (:DEFINITION LEN))
     (967 1
          (:REWRITE FM9001::PREFIXP-APPEND-RELATION-2))
     (853 21 (:REWRITE SIMPLIFY-SUMS-<))
     (723 723 (:TYPE-PRESCRIPTION LEN))
     (412 5
          (:REWRITE FM9001::ISTRPREFIXP-PREFIXP-EXPLODE-RELATION))
     (405 2 (:DEFINITION STR::ISTRPREFIXP$INLINE))
     (398 66 (:REWRITE DEFAULT-CDR))
     (396 141 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (385 39 (:REWRITE |(+ y x)|))
     (363 3 (:REWRITE FM9001::LEN-NTHCDR))
     (355 5 (:REWRITE LEN-OF-APPEND))
     (348 3 (:REWRITE LEN-WHEN-PREFIXP))
     (344 175 (:REWRITE DEFAULT-PLUS-2))
     (334 2 (:REWRITE STR::IPREFIXP-WHEN-PREFIXP))
     (294 175 (:REWRITE DEFAULT-PLUS-1))
     (290 10 (:REWRITE |(+ y (+ x z))|))
     (284 95 (:REWRITE NORMALIZE-ADDENDS))
     (254 5 (:DEFINITION NTHCDR))
     (249 249
          (:TYPE-PRESCRIPTION FM9001::STR-APPEND-SYMBOL-UNDERSCORE))
     (210 15 (:REWRITE LIST-EQUIV-WHEN-ATOM-LEFT))
     (190 10
          (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
     (190 10
          (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
     (174 2 (:REWRITE FM9001::NTHCDR-APPEND))
     (169 141
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (163 25
          (:REWRITE LIST-EQUIV-WHEN-ATOM-RIGHT))
     (162 141
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (154 4
          (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
     (141 141
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (141 141
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (141 141
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (141 141 (:REWRITE |(equal c (/ x))|))
     (141 141 (:REWRITE |(equal c (- x))|))
     (141 141 (:REWRITE |(equal (/ x) c)|))
     (141 141 (:REWRITE |(equal (/ x) (/ y))|))
     (141 141 (:REWRITE |(equal (- x) c)|))
     (141 141 (:REWRITE |(equal (- x) (- y))|))
     (134 2 (:DEFINITION BINARY-APPEND))
     (114 98 (:REWRITE FM9001::SYMBOL-INEQUALITY))
     (111 3 (:REWRITE ZP-OPEN))
     (108 3 (:DEFINITION NFIX))
     (74 74
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (69 69 (:TYPE-PRESCRIPTION PREFIXP))
     (67 3
         (:REWRITE PREFIXP-OF-APPEND-WHEN-SAME-LENGTH))
     (63 4 (:REWRITE APPEND-WHEN-NOT-CONSP))
     (58 58 (:LINEAR LEN-WHEN-PREFIXP))
     (58 29 (:DEFINITION FIX))
     (50 21
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (50 21 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (44 21 (:REWRITE DEFAULT-LESS-THAN-2))
     (42 21 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (42 21 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
     (36 6
         (:REWRITE STR::CHARACTER-LISTP-WHEN-DEC-DIGIT-CHAR-LISTP))
     (35 21 (:REWRITE DEFAULT-LESS-THAN-1))
     (31 1
         (:REWRITE STR::IPREFIXP-WHEN-NOT-CONSP-RIGHT))
     (31 1
         (:REWRITE STR::IPREFIXP-WHEN-NOT-CONSP-LEFT))
     (29 29
         (:LINEAR FM9001::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
     (28 28 (:REWRITE PREFIXP-TRANSITIVE . 2))
     (28 28 (:REWRITE PREFIXP-TRANSITIVE . 1))
     (28 28
         (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
     (28 28
         (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
     (27 9
         (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
     (21 21 (:REWRITE THE-FLOOR-BELOW))
     (21 21 (:REWRITE THE-FLOOR-ABOVE))
     (21 21
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (21 21
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (21 21
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (21 21
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
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
     (21 21 (:REWRITE |(+ x (- x))|))
     (20 20 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (20 10 (:REWRITE LIST-FIX-WHEN-TRUE-LISTP))
     (20 10 (:REWRITE |(+ 0 x)|))
     (16 2
         (:REWRITE FM9001::PREFIXP-APPEND-RELATION-1))
     (16 2
         (:REWRITE STR::DEC-DIGIT-CHAR-LISTP-OF-APPEND))
     (15 15 (:TYPE-PRESCRIPTION LIST-EQUIV))
     (14 14
         (:TYPE-PRESCRIPTION STR::DEC-DIGIT-CHAR-LISTP))
     (14 7
         (:REWRITE STR::DEC-DIGIT-CHAR-LISTP-WHEN-NOT-CONSP))
     (12 8
         (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
     (10 5 (:REWRITE DEFAULT-MINUS))
     (10 2 (:REWRITE DEFAULT-CAR))
     (9 9
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (9 9
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (9 9 (:REWRITE |(< 0 (/ x))|))
     (9 9 (:REWRITE |(< 0 (* x y))|))
     (5 5 (:REWRITE |(< y (+ (- c) x))|))
     (5 5 (:REWRITE |(< x (+ c/d y))|))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (3 3 (:REWRITE |(equal (+ (- c) x) y)|))
     (3 3 (:REWRITE |(< (/ x) 0)|))
     (3 3 (:REWRITE |(< (* x y) 0)|))
     (2 2
        (:TYPE-PRESCRIPTION STR::ISTRPREFIXP$INLINE))
     (2 2 (:REWRITE |(< (+ c/d x) y)|))
     (2 2 (:REWRITE |(< (+ (- c) x) y)|))
     (1 1 (:TYPE-PRESCRIPTION STR::IPREFIXP)))
(FM9001::SI-OF-DIFF-IDXES
     (69 3
         (:REWRITE FM9001::NOT-PREFIXP-NOT-EQUAL))
     (63 6 (:REWRITE PREFIXP-WHEN-PREFIXP))
     (30 3 (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
     (18 6 (:REWRITE LIST-EQUIV-WHEN-ATOM-RIGHT))
     (12 6 (:DEFINITION LEN))
     (9 9 (:TYPE-PRESCRIPTION PREFIXP))
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
     (6034 14
           (:REWRITE STR::IPREFIXP-WHEN-PREFIXP))
     (4946 181 (:REWRITE STR::CONSP-OF-EXPLODE))
     (3984 84
           (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
     (3871 134 (:REWRITE PREFIXP-WHEN-PREFIXP))
     (2691 89 (:DEFINITION LEN))
     (2121 4
           (:REWRITE FM9001::SI-OF-DIFF-SYMBOLS-2))
     (1804 132
           (:REWRITE FM9001::NOT-PREFIXP-NOT-EQUAL))
     (1175 59
           (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
     (1093 31
           (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
     (829 829 (:TYPE-PRESCRIPTION LEN))
     (674 674
          (:TYPE-PRESCRIPTION FM9001::STR-APPEND-SYMBOL-UNDERSCORE))
     (484 14
          (:REWRITE STR::IPREFIXP-WHEN-NOT-CONSP-RIGHT))
     (469 14
          (:REWRITE STR::IPREFIXP-WHEN-NOT-CONSP-LEFT))
     (352 266
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (352 266
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (321 266 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (310 310
          (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
     (266 266
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (266 266
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (266 266
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (266 266 (:REWRITE |(equal c (/ x))|))
     (266 266 (:REWRITE |(equal c (- x))|))
     (266 266 (:REWRITE |(equal (/ x) c)|))
     (266 266 (:REWRITE |(equal (/ x) (/ y))|))
     (266 266 (:REWRITE |(equal (- x) c)|))
     (266 266 (:REWRITE |(equal (- x) (- y))|))
     (265 62 (:REWRITE DEFAULT-CDR))
     (228 228 (:TYPE-PRESCRIPTION PREFIXP))
     (218 218 (:LINEAR LEN-WHEN-PREFIXP))
     (164 64 (:REWRITE DEFAULT-PLUS-2))
     (138 75
          (:REWRITE LIST-EQUIV-WHEN-ATOM-RIGHT))
     (135 132
          (:REWRITE FM9001::SYMBOL-INEQUALITY))
     (109 109
          (:LINEAR FM9001::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
     (84 84 (:REWRITE PREFIXP-TRANSITIVE . 2))
     (84 84 (:REWRITE PREFIXP-TRANSITIVE . 1))
     (84 84
         (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
     (84 84
         (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
     (62 62
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (62 62 (:REWRITE NORMALIZE-ADDENDS))
     (62 62 (:REWRITE DEFAULT-PLUS-1))
     (52 28
         (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
     (36 4 (:REWRITE ACL2-NUMBERP-X))
     (31 31
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
     (2275 5 (:REWRITE STR::IPREFIXP-WHEN-PREFIXP))
     (1840 70 (:REWRITE STR::CONSP-OF-EXPLODE))
     (1738 36
           (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
     (1607 56 (:REWRITE PREFIXP-WHEN-PREFIXP))
     (1069 42 (:DEFINITION LEN))
     (973 53
          (:REWRITE FM9001::NOT-PREFIXP-NOT-EQUAL))
     (446 26
          (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
     (416 16
          (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
     (414 414 (:TYPE-PRESCRIPTION LEN))
     (180 5
          (:REWRITE STR::IPREFIXP-WHEN-NOT-CONSP-LEFT))
     (178 109
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (155 155
          (:TYPE-PRESCRIPTION FM9001::STR-APPEND-SYMBOL-UNDERSCORE))
     (155 5
          (:REWRITE STR::IPREFIXP-WHEN-NOT-CONSP-RIGHT))
     (154 109
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (144 109 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (120 120
          (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
     (116 116 (:LINEAR LEN-WHEN-PREFIXP))
     (112 38 (:REWRITE DEFAULT-PLUS-2))
     (109 109
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (109 109
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (109 109
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (109 109 (:REWRITE |(equal c (/ x))|))
     (109 109 (:REWRITE |(equal c (- x))|))
     (109 109 (:REWRITE |(equal (/ x) c)|))
     (109 109 (:REWRITE |(equal (/ x) (/ y))|))
     (109 109 (:REWRITE |(equal (- x) c)|))
     (109 109 (:REWRITE |(equal (- x) (- y))|))
     (109 36 (:REWRITE DEFAULT-CDR))
     (100 100 (:TYPE-PRESCRIPTION PREFIXP))
     (69 13 (:REWRITE ACL2-NUMBERP-X))
     (58 58
         (:LINEAR FM9001::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
     (53 53 (:REWRITE FM9001::SYMBOL-INEQUALITY))
     (45 30
         (:REWRITE LIST-EQUIV-WHEN-ATOM-RIGHT))
     (36 36 (:REWRITE PREFIXP-TRANSITIVE . 2))
     (36 36 (:REWRITE PREFIXP-TRANSITIVE . 1))
     (36 36
         (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
     (36 36
         (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
     (36 36
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (36 36 (:REWRITE NORMALIZE-ADDENDS))
     (36 36 (:REWRITE DEFAULT-PLUS-1))
     (28 7 (:REWRITE RATIONALP-X))
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
     (3866 11
           (:DEFINITION STR::ISTRPREFIXP$INLINE))
     (3342 11
           (:REWRITE STR::IPREFIXP-WHEN-PREFIXP))
     (2669 106 (:REWRITE STR::CONSP-OF-EXPLODE))
     (2356 46
           (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
     (2124 4
           (:REWRITE FM9001::SI-SIS-DIFF-SYMBOLS-2))
     (1956 68 (:REWRITE PREFIXP-WHEN-PREFIXP))
     (1419 3
           (:REWRITE FM9001::SI-OF-DIFF-SYMBOLS-2))
     (1310 51 (:DEFINITION LEN))
     (940 81
          (:REWRITE FM9001::NOT-PREFIXP-NOT-EQUAL))
     (580 17
          (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
     (568 31
          (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
     (447 447 (:TYPE-PRESCRIPTION LEN))
     (356 4
          (:REWRITE FM9001::SI-SIS-DIFF-SYMBOLS-1))
     (252 7
          (:REWRITE STR::IPREFIXP-WHEN-NOT-CONSP-LEFT))
     (250 250
          (:TYPE-PRESCRIPTION FM9001::STR-APPEND-SYMBOL-UNDERSCORE))
     (217 7
          (:REWRITE STR::IPREFIXP-WHEN-NOT-CONSP-RIGHT))
     (210 162
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (210 162
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (193 162 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (189 37
          (:REWRITE LIST-EQUIV-WHEN-ATOM-RIGHT))
     (184 184
          (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
     (162 162
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (162 162
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (162 162
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (162 162 (:REWRITE |(equal c (/ x))|))
     (162 162 (:REWRITE |(equal c (- x))|))
     (162 162 (:REWRITE |(equal (/ x) c)|))
     (162 162 (:REWRITE |(equal (/ x) (/ y))|))
     (162 162 (:REWRITE |(equal (- x) c)|))
     (162 162 (:REWRITE |(equal (- x) (- y))|))
     (144 4 (:REWRITE LIST-EQUIV-WHEN-ATOM-LEFT))
     (139 38 (:REWRITE DEFAULT-CDR))
     (118 118 (:TYPE-PRESCRIPTION PREFIXP))
     (118 118 (:LINEAR LEN-WHEN-PREFIXP))
     (84 81 (:REWRITE FM9001::SYMBOL-INEQUALITY))
     (72 38 (:REWRITE DEFAULT-PLUS-2))
     (59 59
         (:LINEAR FM9001::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
     (46 46 (:REWRITE PREFIXP-TRANSITIVE . 2))
     (46 46 (:REWRITE PREFIXP-TRANSITIVE . 1))
     (46 46
         (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
     (46 46
         (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
     (38 38
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (38 38 (:REWRITE NORMALIZE-ADDENDS))
     (38 38 (:REWRITE DEFAULT-PLUS-1))
     (37 22
         (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
     (17 17
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
     (178 9
          (:REWRITE FM9001::NOT-PREFIXP-NOT-EQUAL))
     (160 18 (:REWRITE PREFIXP-WHEN-PREFIXP))
     (85 16 (:REWRITE DEFAULT-PLUS-2))
     (72 8 (:REWRITE ACL2-NUMBERP-X))
     (70 9 (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
     (36 18
         (:REWRITE LIST-EQUIV-WHEN-ATOM-RIGHT))
     (32 8 (:REWRITE RATIONALP-X))
     (27 27 (:TYPE-PRESCRIPTION PREFIXP))
     (26 26 (:LINEAR LEN-WHEN-PREFIXP))
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
     (459 3 (:DEFINITION MEMBER-EQUAL))
     (378 3
          (:REWRITE FM9001::NOT-PREFIXP-NOT-EQUAL))
     (318 6 (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
     (192 6 (:REWRITE PREFIXP-WHEN-PREFIXP))
     (114 114 (:TYPE-PRESCRIPTION LEN))
     (84 12 (:DEFINITION LEN))
     (48 9
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (36 36 (:LINEAR LEN-WHEN-PREFIXP))
     (33 9 (:REWRITE ACL2-NUMBERP-X))
     (29 23 (:REWRITE DEFAULT-CDR))
     (28 16 (:REWRITE DEFAULT-PLUS-2))
     (24 9 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (24 9
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (18 18
         (:LINEAR FM9001::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
     (16 16
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (16 16 (:REWRITE NORMALIZE-ADDENDS))
     (16 16 (:REWRITE DEFAULT-PLUS-1))
     (15 15 (:TYPE-PRESCRIPTION PREFIXP))
     (12 3 (:REWRITE RATIONALP-X))
     (10 7 (:REWRITE DEFAULT-CAR))
     (9 9
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (9 9
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (9 9
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (9 9 (:REWRITE |(equal c (/ x))|))
     (9 9 (:REWRITE |(equal c (- x))|))
     (9 9 (:REWRITE |(equal (/ x) c)|))
     (9 9 (:REWRITE |(equal (/ x) (/ y))|))
     (9 9 (:REWRITE |(equal (- x) c)|))
     (9 9 (:REWRITE |(equal (- x) (- y))|))
     (7 7 (:REWRITE REDUCE-INTEGERP-+))
     (7 7 (:REWRITE INTEGERP-MINUS-X))
     (7 7 (:META META-INTEGERP-CORRECT))
     (6 6
        (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
     (6 6
        (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
     (6 6 (:REWRITE PREFIXP-TRANSITIVE . 2))
     (6 6 (:REWRITE PREFIXP-TRANSITIVE . 1))
     (6 6
        (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
     (6 6
        (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
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
     (3 3 (:META META-RATIONALP-CORRECT)))
(FM9001::DISJOINT-SIS-DIFF-SYMS
     (4669 11
           (:REWRITE STR::IPREFIXP-WHEN-PREFIXP))
     (3842 139 (:REWRITE STR::CONSP-OF-EXPLODE))
     (2922 60
           (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
     (2884 98 (:REWRITE PREFIXP-WHEN-PREFIXP))
     (2046 59 (:DEFINITION LEN))
     (1177 99
           (:REWRITE FM9001::NOT-PREFIXP-NOT-EQUAL))
     (899 41
          (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
     (841 22
          (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
     (589 589 (:TYPE-PRESCRIPTION LEN))
     (581 581
          (:TYPE-PRESCRIPTION FM9001::STR-APPEND-SYMBOL-UNDERSCORE))
     (531 1
          (:REWRITE FM9001::SI-SIS-DIFF-SYMBOLS-2))
     (391 11
          (:REWRITE STR::IPREFIXP-WHEN-NOT-CONSP-RIGHT))
     (361 11
          (:REWRITE STR::IPREFIXP-WHEN-NOT-CONSP-LEFT))
     (256 197
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (256 197
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (248 61 (:REWRITE DEFAULT-PLUS-2))
     (238 238
          (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
     (237 197 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (198 40 (:REWRITE DEFAULT-CDR))
     (197 197
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (197 197
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (197 197
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (197 197 (:REWRITE |(equal c (/ x))|))
     (197 197 (:REWRITE |(equal c (- x))|))
     (197 197 (:REWRITE |(equal (/ x) c)|))
     (197 197 (:REWRITE |(equal (/ x) (/ y))|))
     (197 197 (:REWRITE |(equal (- x) c)|))
     (197 197 (:REWRITE |(equal (- x) (- y))|))
     (168 168 (:TYPE-PRESCRIPTION PREFIXP))
     (158 158 (:LINEAR LEN-WHEN-PREFIXP))
     (126 14 (:REWRITE ACL2-NUMBERP-X))
     (111 57
          (:REWRITE LIST-EQUIV-WHEN-ATOM-RIGHT))
     (99 99 (:REWRITE FM9001::SYMBOL-INEQUALITY))
     (88 44
         (:TYPE-PRESCRIPTION FM9001::CONSP-SIS))
     (80 8 (:DEFINITION ATOM))
     (79 79
         (:LINEAR FM9001::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
     (60 60 (:REWRITE PREFIXP-TRANSITIVE . 2))
     (60 60 (:REWRITE PREFIXP-TRANSITIVE . 1))
     (60 60
         (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
     (60 60
         (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
     (56 14 (:REWRITE RATIONALP-X))
     (54 54
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (54 54 (:REWRITE NORMALIZE-ADDENDS))
     (54 54 (:REWRITE DEFAULT-PLUS-1))
     (44 44 (:TYPE-PRESCRIPTION FM9001::SIS))
     (44 44 (:TYPE-PRESCRIPTION POSP))
     (43 22
         (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
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
     (4157 13
           (:DEFINITION STR::ISTRPREFIXP$INLINE))
     (3626 13
           (:REWRITE STR::IPREFIXP-WHEN-PREFIXP))
     (2796 116 (:REWRITE STR::CONSP-OF-EXPLODE))
     (2672 56
           (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
     (2183 85 (:REWRITE PREFIXP-WHEN-PREFIXP))
     (2011 4
           (:REWRITE FM9001::SI-SIS-DIFF-SYMBOLS-2))
     (1752 4
           (:REWRITE FM9001::SI-OF-DIFF-SYMBOLS-2))
     (1452 61 (:DEFINITION LEN))
     (1107 98
           (:REWRITE FM9001::NOT-PREFIXP-NOT-EQUAL))
     (593 37
          (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
     (577 19
          (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
     (495 495 (:TYPE-PRESCRIPTION LEN))
     (356 4
          (:REWRITE FM9001::SI-SIS-DIFF-SYMBOLS-1))
     (258 258
          (:TYPE-PRESCRIPTION FM9001::STR-APPEND-SYMBOL-UNDERSCORE))
     (248 8
          (:REWRITE STR::IPREFIXP-WHEN-NOT-CONSP-RIGHT))
     (239 48
          (:REWRITE LIST-EQUIV-WHEN-ATOM-RIGHT))
     (234 181
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (230 181
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (218 8
          (:REWRITE STR::IPREFIXP-WHEN-NOT-CONSP-LEFT))
     (217 181 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (200 200
          (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
     (183 183
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (183 183
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (183 183 (:REWRITE |(equal c (/ x))|))
     (183 183 (:REWRITE |(equal (/ x) (/ y))|))
     (183 183 (:REWRITE |(equal (- x) (- y))|))
     (181 181
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (181 181 (:REWRITE |(equal c (- x))|))
     (181 181 (:REWRITE |(equal (- x) c)|))
     (180 5 (:REWRITE LIST-EQUIV-WHEN-ATOM-LEFT))
     (161 42 (:REWRITE DEFAULT-CDR))
     (148 98 (:REWRITE FM9001::SYMBOL-INEQUALITY))
     (146 146 (:TYPE-PRESCRIPTION PREFIXP))
     (130 130 (:LINEAR LEN-WHEN-PREFIXP))
     (124 86 (:REWRITE DEFAULT-PLUS-2))
     (92 86 (:REWRITE DEFAULT-PLUS-1))
     (89 1
         (:REWRITE FM9001::SI-OF-DIFF-SYMBOLS-1))
     (68 2 (:REWRITE ZP-OPEN))
     (65 65
         (:LINEAR FM9001::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
     (60 60
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (60 2
         (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (60 2 (:REWRITE |(< x (/ y)) with (< 0 y)|))
     (58 4 (:REWRITE FM9001::SI-SIS-DIFF-IDXES))
     (56 56 (:REWRITE PREFIXP-TRANSITIVE . 2))
     (56 56 (:REWRITE PREFIXP-TRANSITIVE . 1))
     (56 56
         (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
     (56 56
         (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
     (44 26
         (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
     (42 42 (:REWRITE THE-FLOOR-BELOW))
     (42 42 (:REWRITE THE-FLOOR-ABOVE))
     (42 42 (:REWRITE DEFAULT-LESS-THAN-2))
     (42 42 (:REWRITE DEFAULT-LESS-THAN-1))
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
     (31 1 (:REWRITE FM9001::SI-OF-DIFF-IDXES))
     (30 30 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (29 10 (:REWRITE DEFAULT-SYMBOL-NAME))
     (23 23
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (21 8 (:REWRITE DEFAULT-CAR))
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
     (2665 6 (:DEFINITION STR::ISTRPREFIXP$INLINE))
     (2596 5
           (:REWRITE FM9001::SI-OF-DIFF-SYMBOLS-2))
     (2300 6 (:REWRITE STR::IPREFIXP-WHEN-PREFIXP))
     (1849 72 (:REWRITE STR::CONSP-OF-EXPLODE))
     (1707 44
           (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
     (1638 71 (:REWRITE PREFIXP-WHEN-PREFIXP))
     (1011 49 (:DEFINITION LEN))
     (972 68
          (:REWRITE FM9001::NOT-PREFIXP-NOT-EQUAL))
     (437 30
          (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
     (416 13
          (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
     (369 369 (:TYPE-PRESCRIPTION LEN))
     (180 5
          (:REWRITE STR::IPREFIXP-WHEN-NOT-CONSP-LEFT))
     (169 3
          (:REWRITE FM9001::NOT-MEMBER=>NOT-EQUAL-NTH))
     (162 162
          (:TYPE-PRESCRIPTION FM9001::STR-APPEND-SYMBOL-UNDERSCORE))
     (161 122
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (161 122
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (155 129 (:REWRITE DEFAULT-PLUS-2))
     (155 5
          (:REWRITE STR::IPREFIXP-WHEN-NOT-CONSP-RIGHT))
     (146 122 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (146 47 (:REWRITE |(< c (- x))|))
     (142 129 (:REWRITE DEFAULT-PLUS-1))
     (141 68 (:REWRITE FM9001::SYMBOL-INEQUALITY))
     (133 48
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (124 124
          (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
     (124 124
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (124 124
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (124 124 (:REWRITE |(equal c (/ x))|))
     (124 124 (:REWRITE |(equal (/ x) (/ y))|))
     (124 124 (:REWRITE |(equal (- x) (- y))|))
     (122 122
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (122 122 (:REWRITE |(equal c (- x))|))
     (122 122 (:REWRITE |(equal (- x) c)|))
     (117 117 (:TYPE-PRESCRIPTION PREFIXP))
     (107 30 (:REWRITE DEFAULT-CDR))
     (98 41
         (:REWRITE LIST-EQUIV-WHEN-ATOM-RIGHT))
     (90 90 (:LINEAR LEN-WHEN-PREFIXP))
     (89 1
         (:REWRITE FM9001::SI-OF-DIFF-SYMBOLS-1))
     (64 2 (:REWRITE FM9001::LEN-SIS))
     (62 62
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (62 2 (:DEFINITION NFIX))
     (60 2
         (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (60 2 (:REWRITE |(< x (/ y)) with (< 0 y)|))
     (54 54 (:REWRITE THE-FLOOR-BELOW))
     (54 54 (:REWRITE THE-FLOOR-ABOVE))
     (54 54 (:REWRITE DEFAULT-LESS-THAN-2))
     (54 54 (:REWRITE DEFAULT-LESS-THAN-1))
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
     (45 45
         (:LINEAR FM9001::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
     (44 44 (:REWRITE PREFIXP-TRANSITIVE . 2))
     (44 44 (:REWRITE PREFIXP-TRANSITIVE . 1))
     (44 44
         (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
     (44 44
         (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
     (42 42 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (36 1 (:REWRITE LIST-EQUIV-WHEN-ATOM-LEFT))
     (33 13 (:REWRITE |(+ c (+ d x))|))
     (31 1 (:REWRITE FM9001::SI-OF-DIFF-IDXES))
     (21 21
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (19 19 (:REWRITE |(< 0 (/ x))|))
     (19 19 (:REWRITE |(< 0 (* x y))|))
     (19 12
         (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
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
