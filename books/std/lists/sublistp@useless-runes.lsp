(SUBLISTP)
(SUBLISTP-WHEN-ATOM-LEFT (32 2 (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
                         (26 2 (:REWRITE PREFIXP-WHEN-PREFIXP))
                         (16 16 (:TYPE-PRESCRIPTION LEN))
                         (12 4 (:DEFINITION LEN))
                         (4 4 (:LINEAR LEN-WHEN-PREFIXP))
                         (4 2 (:REWRITE DEFAULT-+-2))
                         (3 2
                            (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
                         (2 2 (:TYPE-PRESCRIPTION PREFIXP))
                         (2 2 (:REWRITE PREFIXP-TRANSITIVE . 2))
                         (2 2 (:REWRITE PREFIXP-TRANSITIVE . 1))
                         (2 2
                            (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
                         (2 2
                            (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
                         (2 2 (:REWRITE DEFAULT-CDR))
                         (2 2 (:REWRITE DEFAULT-+-1))
                         (1 1 (:DEFINITION NOT)))
(SUBLISTP-WHEN-ATOM-RIGHT (16 1 (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
                          (8 8 (:TYPE-PRESCRIPTION LEN))
                          (6 2 (:DEFINITION LEN))
                          (2 2 (:LINEAR LEN-WHEN-PREFIXP))
                          (2 1 (:REWRITE DEFAULT-+-2))
                          (1 1 (:REWRITE SUBLISTP-WHEN-ATOM-LEFT))
                          (1 1
                             (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
                          (1 1 (:REWRITE PREFIXP-TRANSITIVE . 2))
                          (1 1 (:REWRITE PREFIXP-TRANSITIVE . 1))
                          (1 1
                             (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
                          (1 1
                             (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
                          (1 1 (:REWRITE DEFAULT-CDR))
                          (1 1 (:REWRITE DEFAULT-+-1)))
(SUBLISTP-OF-CONS-RIGHT (726 24
                             (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
                        (603 24 (:REWRITE PREFIXP-WHEN-PREFIXP))
                        (324 324 (:TYPE-PRESCRIPTION LEN))
                        (294 54 (:DEFINITION LEN))
                        (231 3 (:REWRITE PREFIXP-OF-CONS-LEFT))
                        (144 144 (:LINEAR LEN-WHEN-PREFIXP))
                        (120 60 (:REWRITE DEFAULT-+-2))
                        (64 64 (:REWRITE DEFAULT-CDR))
                        (60 60 (:REWRITE DEFAULT-+-1))
                        (24 24 (:REWRITE PREFIXP-TRANSITIVE . 2))
                        (24 24 (:REWRITE PREFIXP-TRANSITIVE . 1))
                        (24 24
                            (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
                        (24 24
                            (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
                        (21 21
                            (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
                        (18 18
                            (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
                        (7 7 (:REWRITE DEFAULT-CAR))
                        (6 6 (:REWRITE SUBLISTP-WHEN-ATOM-RIGHT))
                        (6 6 (:REWRITE SUBLISTP-WHEN-ATOM-LEFT)))
(SUBLISTP-WHEN-PREFIXP (60 3 (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
                       (57 8 (:REWRITE PREFIXP-WHEN-PREFIXP))
                       (26 26 (:TYPE-PRESCRIPTION LEN))
                       (20 4 (:DEFINITION LEN))
                       (12 12 (:LINEAR LEN-WHEN-PREFIXP))
                       (8 4 (:REWRITE DEFAULT-+-2))
                       (4 4 (:TYPE-PRESCRIPTION LIST-EQUIV))
                       (4 4
                          (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
                       (4 4 (:REWRITE LIST-EQUIV-WHEN-ATOM-RIGHT))
                       (4 4 (:REWRITE LIST-EQUIV-WHEN-ATOM-LEFT))
                       (4 4 (:REWRITE DEFAULT-CDR))
                       (4 4 (:REWRITE DEFAULT-+-1))
                       (3 3 (:REWRITE PREFIXP-TRANSITIVE . 1))
                       (2 2
                          (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
                       (2 2
                          (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
                       (1 1 (:REWRITE SUBLISTP-WHEN-ATOM-RIGHT))
                       (1 1 (:REWRITE SUBLISTP-WHEN-ATOM-LEFT)))
(SUBLISTP-OF-LIST-FIX-LEFT (1079 59
                                 (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
                           (483 95 (:DEFINITION LEN))
                           (404 8 (:REWRITE PREFIXP-OF-LIST-FIX-RIGHT))
                           (267 194 (:LINEAR LEN-WHEN-PREFIXP))
                           (194 97 (:REWRITE DEFAULT-+-2))
                           (106 106 (:REWRITE DEFAULT-CDR))
                           (97 97 (:REWRITE DEFAULT-+-1))
                           (97 5 (:REWRITE LIST-FIX-WHEN-LEN-ZERO))
                           (90 15 (:REWRITE LEN-OF-LIST-FIX))
                           (71 59 (:REWRITE PREFIXP-TRANSITIVE . 1))
                           (61 60
                               (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
                           (40 5 (:REWRITE LIST-FIX-WHEN-TRUE-LISTP))
                           (39 39
                               (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
                           (25 25 (:TYPE-PRESCRIPTION TRUE-LISTP))
                           (25 10 (:REWRITE SUBLISTP-WHEN-ATOM-LEFT))
                           (25 5 (:DEFINITION TRUE-LISTP))
                           (11 8 (:REWRITE LIST-EQUIV-WHEN-ATOM-LEFT))
                           (8 8 (:TYPE-PRESCRIPTION LIST-EQUIV))
                           (5 5 (:REWRITE LIST-FIX-WHEN-NOT-CONSP)))
(SUBLISTP-OF-LIST-FIX-RIGHT (1461 80
                                  (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
                            (581 10 (:REWRITE PREFIXP-OF-LIST-FIX-LEFT))
                            (329 268 (:LINEAR LEN-WHEN-PREFIXP))
                            (260 130 (:REWRITE DEFAULT-+-2))
                            (156 23 (:REWRITE LEN-OF-LIST-FIX))
                            (148 148 (:REWRITE DEFAULT-CDR))
                            (130 130 (:REWRITE DEFAULT-+-1))
                            (124 80 (:REWRITE PREFIXP-TRANSITIVE . 1))
                            (108 81
                                 (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
                            (80 10 (:REWRITE LIST-FIX-WHEN-TRUE-LISTP))
                            (52 11 (:DEFINITION TRUE-LISTP))
                            (51 51
                                (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
                            (48 48 (:TYPE-PRESCRIPTION TRUE-LISTP))
                            (14 11 (:REWRITE LIST-EQUIV-WHEN-ATOM-LEFT))
                            (13 13 (:REWRITE SUBLISTP-WHEN-ATOM-LEFT))
                            (11 11 (:TYPE-PRESCRIPTION LIST-EQUIV))
                            (9 9 (:REWRITE LIST-FIX-WHEN-NOT-CONSP))
                            (1 1 (:REWRITE LIST-EQUIV-OF-NIL-RIGHT)))
(LIST-EQUIV-IMPLIES-EQUAL-SUBLISTP-1
     (356 4 (:REWRITE SUBLISTP-WHEN-PREFIXP))
     (248 14 (:REWRITE PREFIXP-WHEN-PREFIXP))
     (234 14
          (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
     (150 2 (:REWRITE PREFIXP-OF-LIST-FIX-RIGHT))
     (90 18 (:DEFINITION LEN))
     (52 52 (:LINEAR LEN-WHEN-PREFIXP))
     (40 2 (:REWRITE PREFIXP-OF-LIST-FIX-LEFT))
     (36 18 (:REWRITE DEFAULT-+-2))
     (28 2 (:REWRITE LIST-FIX-WHEN-LEN-ZERO))
     (24 24 (:TYPE-PRESCRIPTION PREFIXP))
     (24 4 (:REWRITE LEN-OF-LIST-FIX))
     (20 20 (:REWRITE DEFAULT-CDR))
     (18 18 (:REWRITE DEFAULT-+-1))
     (16 2 (:REWRITE LIST-FIX-WHEN-TRUE-LISTP))
     (14 14 (:REWRITE PREFIXP-TRANSITIVE . 2))
     (14 14 (:REWRITE PREFIXP-TRANSITIVE . 1))
     (14 14
         (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
     (14 14
         (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
     (10 10 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (10 10
         (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
     (10 10
         (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
     (10 4 (:REWRITE SUBLISTP-WHEN-ATOM-LEFT))
     (10 2 (:DEFINITION TRUE-LISTP))
     (4 4 (:TYPE-PRESCRIPTION TRUE-LIST-FIX))
     (4 4 (:REWRITE SUBLISTP-WHEN-ATOM-RIGHT))
     (2 2 (:REWRITE LIST-FIX-WHEN-NOT-CONSP))
     (2 2 (:REWRITE CONSP-OF-LIST-FIX)))
(LIST-EQUIV-IMPLIES-EQUAL-SUBLISTP-2
     (356 4 (:REWRITE SUBLISTP-WHEN-PREFIXP))
     (248 14 (:REWRITE PREFIXP-WHEN-PREFIXP))
     (234 14
          (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
     (150 2 (:REWRITE PREFIXP-OF-LIST-FIX-LEFT))
     (90 18 (:DEFINITION LEN))
     (52 52 (:LINEAR LEN-WHEN-PREFIXP))
     (40 2 (:REWRITE PREFIXP-OF-LIST-FIX-RIGHT))
     (36 18 (:REWRITE DEFAULT-+-2))
     (28 2 (:REWRITE LIST-FIX-WHEN-LEN-ZERO))
     (24 24 (:TYPE-PRESCRIPTION PREFIXP))
     (24 4 (:REWRITE LEN-OF-LIST-FIX))
     (20 20 (:REWRITE DEFAULT-CDR))
     (18 18 (:REWRITE DEFAULT-+-1))
     (16 2 (:REWRITE LIST-FIX-WHEN-TRUE-LISTP))
     (14 14 (:REWRITE PREFIXP-TRANSITIVE . 2))
     (14 14 (:REWRITE PREFIXP-TRANSITIVE . 1))
     (14 14
         (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
     (14 14
         (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
     (10 10 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (10 10
         (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
     (10 10
         (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
     (10 4 (:REWRITE SUBLISTP-WHEN-ATOM-RIGHT))
     (10 2 (:DEFINITION TRUE-LISTP))
     (4 4 (:TYPE-PRESCRIPTION TRUE-LIST-FIX))
     (4 4 (:REWRITE SUBLISTP-WHEN-ATOM-LEFT))
     (2 2 (:REWRITE LIST-FIX-WHEN-NOT-CONSP))
     (2 2 (:REWRITE CONSP-OF-LIST-FIX)))
(LOWER-BOUND-OF-LEN-WHEN-SUBLISTP
     (369 7 (:REWRITE SUBLISTP-WHEN-PREFIXP))
     (354 24
          (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
     (295 25 (:REWRITE PREFIXP-WHEN-PREFIXP))
     (174 3 (:REWRITE LEN-WHEN-PREFIXP))
     (100 50 (:REWRITE DEFAULT-+-2))
     (50 50 (:REWRITE DEFAULT-+-1))
     (45 45 (:REWRITE DEFAULT-CDR))
     (24 24
         (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
     (24 24
         (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
     (24 24 (:REWRITE PREFIXP-TRANSITIVE . 2))
     (24 24 (:REWRITE PREFIXP-TRANSITIVE . 1))
     (24 24
         (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
     (24 24
         (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
     (12 6 (:REWRITE DEFAULT-<-1))
     (11 6 (:REWRITE DEFAULT-<-2))
     (6 6 (:REWRITE SUBLISTP-WHEN-ATOM-LEFT))
     (2 1
        (:REWRITE LIST-EQUIV-WHEN-ATOM-RIGHT)))
(LISTPOS)
(LISTPOS-WHEN-ATOM-LEFT (36 2 (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
                        (28 2 (:REWRITE PREFIXP-WHEN-PREFIXP))
                        (16 16 (:TYPE-PRESCRIPTION LEN))
                        (12 4 (:DEFINITION LEN))
                        (4 4
                           (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
                        (4 4 (:LINEAR LEN-WHEN-PREFIXP))
                        (4 2 (:REWRITE DEFAULT-+-2))
                        (3 2
                           (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
                        (2 2 (:TYPE-PRESCRIPTION PREFIXP))
                        (2 2 (:REWRITE PREFIXP-TRANSITIVE . 2))
                        (2 2 (:REWRITE PREFIXP-TRANSITIVE . 1))
                        (2 2
                           (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
                        (2 2
                           (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
                        (2 2 (:REWRITE DEFAULT-CDR))
                        (2 2 (:REWRITE DEFAULT-+-1))
                        (1 1 (:DEFINITION NOT)))
(LISTPOS-WHEN-ATOM-RIGHT (18 1 (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
                         (8 8 (:TYPE-PRESCRIPTION LEN))
                         (6 2 (:DEFINITION LEN))
                         (2 2
                            (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
                         (2 2 (:LINEAR LEN-WHEN-PREFIXP))
                         (2 1 (:REWRITE DEFAULT-+-2))
                         (1 1
                            (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
                         (1 1 (:REWRITE PREFIXP-TRANSITIVE . 2))
                         (1 1 (:REWRITE PREFIXP-TRANSITIVE . 1))
                         (1 1
                            (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
                         (1 1
                            (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
                         (1 1 (:REWRITE LISTPOS-WHEN-ATOM-LEFT))
                         (1 1 (:REWRITE DEFAULT-CDR))
                         (1 1 (:REWRITE DEFAULT-+-1)))
(LISTPOS-OF-LIST-FIX-LEFT (1370 43
                                (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
                          (590 106 (:DEFINITION LEN))
                          (302 205 (:LINEAR LEN-WHEN-PREFIXP))
                          (283 5 (:REWRITE PREFIXP-OF-LIST-FIX-RIGHT))
                          (248 127 (:REWRITE DEFAULT-+-2))
                          (208 208
                               (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
                          (131 131 (:REWRITE DEFAULT-CDR))
                          (127 127 (:REWRITE DEFAULT-+-1))
                          (125 6 (:REWRITE LIST-FIX-WHEN-LEN-ZERO))
                          (66 11 (:REWRITE LEN-OF-LIST-FIX))
                          (48 6 (:REWRITE LIST-FIX-WHEN-TRUE-LISTP))
                          (46 46
                              (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
                          (43 43 (:REWRITE PREFIXP-TRANSITIVE . 1))
                          (35 14 (:REWRITE LISTPOS-WHEN-ATOM-LEFT))
                          (30 30 (:TYPE-PRESCRIPTION TRUE-LISTP))
                          (30 6 (:DEFINITION TRUE-LISTP))
                          (29 29
                              (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
                          (17 14 (:REWRITE LIST-EQUIV-WHEN-ATOM-LEFT))
                          (14 14 (:TYPE-PRESCRIPTION LIST-EQUIV))
                          (6 6 (:REWRITE LIST-FIX-WHEN-NOT-CONSP)))
(LISTPOS-OF-LIST-FIX-RIGHT (1667 58
                                 (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
                           (457 7 (:REWRITE PREFIXP-OF-LIST-FIX-LEFT))
                           (319 258 (:LINEAR LEN-WHEN-PREFIXP))
                           (304 156 (:REWRITE DEFAULT-+-2))
                           (260 260
                                (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
                           (175 175 (:REWRITE DEFAULT-CDR))
                           (156 156 (:REWRITE DEFAULT-+-1))
                           (144 18 (:REWRITE LEN-OF-LIST-FIX))
                           (117 14 (:REWRITE LIST-FIX-WHEN-TRUE-LISTP))
                           (88 61
                               (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
                           (81 58 (:REWRITE PREFIXP-TRANSITIVE . 1))
                           (78 16 (:DEFINITION TRUE-LISTP))
                           (70 70 (:TYPE-PRESCRIPTION TRUE-LISTP))
                           (37 37
                               (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
                           (20 20 (:REWRITE LISTPOS-WHEN-ATOM-LEFT))
                           (17 14 (:REWRITE LIST-EQUIV-WHEN-ATOM-LEFT))
                           (14 14 (:TYPE-PRESCRIPTION LIST-EQUIV))
                           (13 13 (:REWRITE LIST-FIX-WHEN-NOT-CONSP)))
(LIST-EQUIV-IMPLIES-EQUAL-LISTPOS-1
     (882 25
          (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
     (334 58 (:DEFINITION LEN))
     (318 318 (:TYPE-PRESCRIPTION LEN))
     (144 75 (:REWRITE DEFAULT-+-2))
     (134 134
          (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
     (134 134 (:LINEAR LEN-WHEN-PREFIXP))
     (75 75 (:REWRITE DEFAULT-+-1))
     (73 73 (:REWRITE DEFAULT-CDR))
     (27 27
         (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
     (25 25 (:REWRITE PREFIXP-TRANSITIVE . 1))
     (23 23
         (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
     (14 14 (:REWRITE LISTPOS-WHEN-ATOM-LEFT))
     (14 14
         (:REWRITE LIST-EQUIV-WHEN-ATOM-LEFT)))
(LIST-EQUIV-IMPLIES-EQUAL-LISTPOS-2
     (416 16
          (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
     (372 16 (:REWRITE PREFIXP-WHEN-PREFIXP))
     (174 2 (:REWRITE PREFIXP-OF-LIST-FIX-LEFT))
     (140 28 (:DEFINITION LEN))
     (80 80
         (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
     (80 80 (:LINEAR LEN-WHEN-PREFIXP))
     (64 4 (:REWRITE LIST-FIX-WHEN-LEN-ZERO))
     (60 32 (:REWRITE DEFAULT-+-2))
     (36 36 (:REWRITE DEFAULT-CDR))
     (32 32 (:REWRITE DEFAULT-+-1))
     (32 4 (:REWRITE LIST-FIX-WHEN-TRUE-LISTP))
     (24 4 (:REWRITE LEN-OF-LIST-FIX))
     (20 20 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (20 8 (:REWRITE LISTPOS-WHEN-ATOM-RIGHT))
     (20 4 (:DEFINITION TRUE-LISTP))
     (16 16 (:REWRITE PREFIXP-TRANSITIVE . 2))
     (16 16 (:REWRITE PREFIXP-TRANSITIVE . 1))
     (16 16
         (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
     (16 16
         (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
     (12 12
         (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
     (12 12
         (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
     (8 8 (:REWRITE LISTPOS-WHEN-ATOM-LEFT))
     (4 4 (:REWRITE LIST-FIX-WHEN-NOT-CONSP)))
(LISTPOS-UNDER-IFF (1956 57
                         (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
                   (800 152 (:DEFINITION LEN))
                   (744 744 (:TYPE-PRESCRIPTION LEN))
                   (502 262
                        (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
                   (330 168 (:REWRITE DEFAULT-+-2))
                   (252 252 (:LINEAR LEN-WHEN-PREFIXP))
                   (173 173 (:REWRITE DEFAULT-CDR))
                   (168 168 (:REWRITE DEFAULT-+-1))
                   (58 58
                       (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
                   (57 57 (:REWRITE PREFIXP-TRANSITIVE . 1))
                   (56 56
                       (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
                   (14 14 (:REWRITE SUBLISTP-WHEN-ATOM-LEFT))
                   (13 13 (:REWRITE LISTPOS-WHEN-ATOM-LEFT))
                   (4 4 (:TYPE-PRESCRIPTION LIST-EQUIV))
                   (4 4 (:REWRITE LIST-EQUIV-WHEN-ATOM-LEFT)))
(NATP-OF-LISTPOS (4937 107
                       (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
                 (2461 421 (:DEFINITION LEN))
                 (1778 1778 (:TYPE-PRESCRIPTION LEN))
                 (1657 558
                       (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
                 (1032 522 (:REWRITE DEFAULT-+-2))
                 (540 540 (:LINEAR LEN-WHEN-PREFIXP))
                 (533 533 (:REWRITE DEFAULT-CDR))
                 (522 522 (:REWRITE DEFAULT-+-1))
                 (115 4 (:REWRITE PREFIXP-OF-CONS-LEFT))
                 (108 108
                      (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
                 (107 107 (:REWRITE PREFIXP-TRANSITIVE . 1))
                 (98 98
                     (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
                 (26 26 (:REWRITE SUBLISTP-WHEN-ATOM-LEFT))
                 (25 25 (:REWRITE LISTPOS-WHEN-ATOM-LEFT))
                 (14 14 (:REWRITE DEFAULT-CAR))
                 (8 8 (:REWRITE CDR-CONS))
                 (4 4 (:TYPE-PRESCRIPTION LIST-EQUIV))
                 (4 4 (:REWRITE LIST-EQUIV-WHEN-ATOM-LEFT))
                 (1 1 (:REWRITE DEFAULT-<-2))
                 (1 1 (:REWRITE DEFAULT-<-1)))
(INTEGERP-OF-LISTPOS (4801 103
                           (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
                     (2421 413 (:DEFINITION LEN))
                     (1726 1726 (:TYPE-PRESCRIPTION LEN))
                     (1633 534
                           (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
                     (1015 513 (:REWRITE DEFAULT-+-2))
                     (524 524 (:REWRITE DEFAULT-CDR))
                     (516 516 (:LINEAR LEN-WHEN-PREFIXP))
                     (513 513 (:REWRITE DEFAULT-+-1))
                     (115 4 (:REWRITE PREFIXP-OF-CONS-LEFT))
                     (104 104
                          (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
                     (103 103 (:REWRITE PREFIXP-TRANSITIVE . 1))
                     (94 94
                         (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
                     (25 25 (:REWRITE SUBLISTP-WHEN-ATOM-LEFT))
                     (23 23 (:REWRITE LISTPOS-WHEN-ATOM-LEFT))
                     (14 14 (:REWRITE DEFAULT-CAR))
                     (8 8 (:REWRITE CDR-CONS))
                     (4 4 (:TYPE-PRESCRIPTION LIST-EQUIV))
                     (4 4 (:REWRITE LIST-EQUIV-WHEN-ATOM-LEFT)))
(RATIONALP-OF-LISTPOS (4801 103
                            (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
                      (2421 413 (:DEFINITION LEN))
                      (1726 1726 (:TYPE-PRESCRIPTION LEN))
                      (1633 534
                            (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
                      (1015 513 (:REWRITE DEFAULT-+-2))
                      (524 524 (:REWRITE DEFAULT-CDR))
                      (516 516 (:LINEAR LEN-WHEN-PREFIXP))
                      (513 513 (:REWRITE DEFAULT-+-1))
                      (115 4 (:REWRITE PREFIXP-OF-CONS-LEFT))
                      (104 104
                           (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
                      (103 103 (:REWRITE PREFIXP-TRANSITIVE . 1))
                      (94 94
                          (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
                      (25 25 (:REWRITE SUBLISTP-WHEN-ATOM-LEFT))
                      (23 23 (:REWRITE LISTPOS-WHEN-ATOM-LEFT))
                      (14 14 (:REWRITE DEFAULT-CAR))
                      (8 8 (:REWRITE CDR-CONS))
                      (4 4 (:TYPE-PRESCRIPTION LIST-EQUIV))
                      (4 4 (:REWRITE LIST-EQUIV-WHEN-ATOM-LEFT)))
(ACL2-NUMBERP-OF-LISTPOS (5189 111
                               (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
                         (2597 445 (:DEFINITION LEN))
                         (1876 1876 (:TYPE-PRESCRIPTION LEN))
                         (1783 580
                               (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
                         (1192 547 (:REWRITE DEFAULT-+-2))
                         (560 560 (:LINEAR LEN-WHEN-PREFIXP))
                         (557 557 (:REWRITE DEFAULT-CDR))
                         (547 547 (:REWRITE DEFAULT-+-1))
                         (115 4 (:REWRITE PREFIXP-OF-CONS-LEFT))
                         (112 112
                              (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
                         (111 111 (:REWRITE PREFIXP-TRANSITIVE . 1))
                         (102 102
                              (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
                         (36 36 (:REWRITE SUBLISTP-WHEN-ATOM-LEFT))
                         (17 17 (:REWRITE LISTPOS-WHEN-ATOM-LEFT))
                         (14 14 (:REWRITE DEFAULT-CAR))
                         (8 8 (:REWRITE CDR-CONS))
                         (4 4 (:TYPE-PRESCRIPTION LIST-EQUIV))
                         (4 4 (:REWRITE LIST-EQUIV-WHEN-ATOM-LEFT)))
(LISTPOS-LOWER-BOUND-WEAK)
(LISTPOS-UPPER-BOUND-WEAK (968 37
                               (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
                          (412 6 (:REWRITE SUBLISTP-WHEN-PREFIXP))
                          (156 82 (:REWRITE DEFAULT-+-2))
                          (118 118 (:LINEAR LEN-WHEN-PREFIXP))
                          (82 82 (:REWRITE DEFAULT-+-1))
                          (60 60 (:REWRITE DEFAULT-CDR))
                          (39 39
                              (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
                          (37 37 (:REWRITE PREFIXP-TRANSITIVE . 1))
                          (35 35
                              (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
                          (14 14 (:REWRITE LISTPOS-WHEN-ATOM-LEFT))
                          (14 7 (:REWRITE DEFAULT-<-1))
                          (8 8 (:TYPE-PRESCRIPTION LIST-EQUIV))
                          (8 8 (:REWRITE LIST-EQUIV-WHEN-ATOM-LEFT))
                          (8 2
                             (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                          (6 6 (:REWRITE SUBLISTP-WHEN-ATOM-RIGHT))
                          (6 6 (:REWRITE SUBLISTP-WHEN-ATOM-LEFT)))
(LISTPOS-UPPER-BOUND-STRONG-1 (614 31 (:REWRITE PREFIXP-WHEN-PREFIXP))
                              (292 6 (:REWRITE DEFAULT-<-1))
                              (177 93 (:REWRITE DEFAULT-+-2))
                              (105 105 (:REWRITE DEFAULT-CDR))
                              (93 93 (:REWRITE DEFAULT-+-1))
                              (92 92 (:LINEAR LEN-WHEN-PREFIXP))
                              (30 30 (:REWRITE PREFIXP-TRANSITIVE . 2))
                              (30 30 (:REWRITE PREFIXP-TRANSITIVE . 1))
                              (30 30
                                  (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
                              (30 30
                                  (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
                              (29 29
                                  (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
                              (17 17 (:REWRITE LISTPOS-WHEN-ATOM-LEFT))
                              (11 6 (:REWRITE DEFAULT-<-2))
                              (8 2
                                 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                              (3 3 (:REWRITE SUBLISTP-WHEN-ATOM-LEFT))
                              (3 2 (:REWRITE LIST-EQUIV-WHEN-ATOM-RIGHT))
                              (1 1 (:REWRITE LIST-EQUIV-WHEN-ATOM-LEFT)))
(LISTPOS-UPPER-BOUND-STRONG-2 (652 337 (:REWRITE DEFAULT-+-2))
                              (347 337 (:REWRITE DEFAULT-+-1))
                              (236 236 (:REWRITE DEFAULT-CDR))
                              (79 79
                                  (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
                              (76 76 (:REWRITE PREFIXP-TRANSITIVE . 1))
                              (72 72
                                  (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
                              (72 72
                                  (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
                              (33 33 (:REWRITE LISTPOS-WHEN-ATOM-LEFT))
                              (23 9 (:REWRITE DEFAULT-<-1))
                              (18 9 (:REWRITE DEFAULT-UNARY-MINUS))
                              (14 14 (:REWRITE SUBLISTP-WHEN-ATOM-RIGHT))
                              (14 14 (:REWRITE SUBLISTP-WHEN-ATOM-LEFT))
                              (12 12 (:TYPE-PRESCRIPTION LIST-EQUIV))
                              (12 12 (:REWRITE LIST-EQUIV-WHEN-ATOM-LEFT))
                              (12 3
                                  (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                              (6 6 (:REWRITE FOLD-CONSTS-IN-+)))
(L0 (7874 563
          (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
    (6566 3443 (:REWRITE DEFAULT-+-2))
    (3997 3443 (:REWRITE DEFAULT-+-1))
    (2623 501
          (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
    (2589 2491 (:REWRITE DEFAULT-CDR))
    (2529 501
          (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
    (1022 511
          (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
    (912 108 (:REWRITE COMMUTATIVITY-2-OF-+))
    (909 685 (:REWRITE DEFAULT-<-1))
    (637 71 (:REWRITE LIST-EQUIV-WHEN-ATOM-LEFT))
    (511 511 (:TYPE-PRESCRIPTION TRUE-LISTP))
    (511 343 (:REWRITE DEFAULT-UNARY-MINUS))
    (452 276 (:REWRITE FOLD-CONSTS-IN-+))
    (108 17 (:REWRITE NTHCDR-WHEN-ZP))
    (92 30 (:REWRITE ZP-OPEN))
    (84 12
        (:REWRITE DISTRIBUTIVITY-OF-MINUS-OVER-+))
    (68 68 (:TYPE-PRESCRIPTION LIST-EQUIV))
    (67 67 (:REWRITE LISTPOS-WHEN-ATOM-LEFT))
    (25 23 (:REWRITE SUBLISTP-WHEN-ATOM-RIGHT))
    (21 21 (:REWRITE SUBLISTP-WHEN-ATOM-LEFT))
    (17 17 (:REWRITE NTHCDR-WHEN-ATOM))
    (16 4
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP)))
(LISTPOS-COMPLETE
     (36724 1688
            (:LINEAR LISTPOS-UPPER-BOUND-STRONG-2))
     (15636 1855 (:REWRITE PREFIXP-TRANSITIVE . 1))
     (14291 8 (:REWRITE PREFIXP-OF-CONS-LEFT))
     (13459 1858
            (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
     (10289 5423 (:REWRITE DEFAULT-+-2))
     (10106 94 (:REWRITE CONSP-OF-NTHCDR))
     (6410 1286 (:LINEAR LEN-WHEN-PREFIXP))
     (6346 5423 (:REWRITE DEFAULT-+-1))
     (5764 1807
           (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
     (4769 1460
           (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
     (4579 1815
           (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
     (3478 155 (:REWRITE LEN-OF-NTHCDR))
     (2393 35 (:REWRITE LIST-EQUIV-WHEN-ATOM-LEFT))
     (2335 530 (:REWRITE DEFAULT-<-2))
     (1729 1 (:REWRITE ACL2-NUMBERP-OF-LISTPOS))
     (1684 842
           (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
     (970 970 (:REWRITE LISTPOS-WHEN-ATOM-RIGHT))
     (970 970 (:REWRITE LISTPOS-WHEN-ATOM-LEFT))
     (889 505 (:REWRITE DEFAULT-UNARY-MINUS))
     (842 842 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (686 530 (:REWRITE DEFAULT-<-1))
     (120 10 (:REWRITE COMMUTATIVITY-2-OF-+))
     (118 118
          (:LINEAR LISTPOS-UPPER-BOUND-STRONG-1))
     (102 34 (:REWRITE UNICITY-OF-0))
     (70 10
         (:REWRITE DISTRIBUTIVITY-OF-MINUS-OVER-+))
     (68 34 (:DEFINITION FIX))
     (35 35 (:TYPE-PRESCRIPTION LIST-EQUIV))
     (19 19 (:REWRITE SUBLISTP-WHEN-ATOM-LEFT))
     (19 19 (:REWRITE OPEN-SMALL-NTHCDR))
     (17 17 (:REWRITE DEFAULT-CAR))
     (8 8 (:REWRITE CDR-CONS))
     (1 1
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP)))
(SUBLISTP-SOUND
     (7806 238 (:REWRITE PREFIXP-WHEN-PREFIXP))
     (5609 7 (:REWRITE ZP-OPEN))
     (5606 6 (:REWRITE NTHCDR-WHEN-ZP))
     (2972 945 (:REWRITE DEFAULT-CDR))
     (2319 1172 (:REWRITE DEFAULT-+-2))
     (2168 2 (:REWRITE CONSP-OF-NTHCDR))
     (1938 346 (:LINEAR LEN-WHEN-PREFIXP))
     (1933 26 (:LINEAR LISTPOS-UPPER-BOUND-WEAK))
     (1752 26 (:LINEAR LISTPOS-LOWER-BOUND-WEAK))
     (1397 1172 (:REWRITE DEFAULT-+-1))
     (1068 380
           (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
     (624 222 (:REWRITE PREFIXP-TRANSITIVE . 1))
     (382 217
          (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
     (382 217
          (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
     (380 380 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (265 225
          (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
     (228 114 (:REWRITE DEFAULT-UNARY-MINUS))
     (221 221 (:REWRITE LISTPOS-WHEN-ATOM-LEFT))
     (80 8 (:REWRITE COMMUTATIVITY-2-OF-+))
     (64 26
         (:LINEAR LISTPOS-UPPER-BOUND-STRONG-1))
     (41 16 (:REWRITE DEFAULT-<-1))
     (34 16 (:REWRITE DEFAULT-<-2))
     (26 26 (:LINEAR LISTPOS-COMPLETE))
     (23 13 (:REWRITE LIST-EQUIV-WHEN-ATOM-LEFT))
     (21 2 (:DEFINITION NFIX))
     (12 12 (:TYPE-PRESCRIPTION LIST-EQUIV))
     (10 7 (:REWRITE INTEGERP-OF-LISTPOS))
     (7 1
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (6 6 (:REWRITE NTHCDR-WHEN-ATOM))
     (5 5 (:TYPE-PRESCRIPTION ZP))
     (5 5 (:REWRITE LISTPOS-COMPLETE))
     (2 2 (:REWRITE SUBLISTP-WHEN-ATOM-LEFT)))
(SUBLISTP-COMPLETE
     (5085 279
           (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
     (4908 68 (:DEFINITION LISTPOS))
     (4259 434
           (:LINEAR LISTPOS-UPPER-BOUND-STRONG-2))
     (2872 279
           (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
     (1769 964 (:REWRITE DEFAULT-+-2))
     (1714 270
           (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
     (1492 371 (:LINEAR LEN-WHEN-PREFIXP))
     (1454 279 (:REWRITE PREFIXP-TRANSITIVE . 2))
     (1365 270
           (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
     (1131 964 (:REWRITE DEFAULT-+-1))
     (973 18 (:LINEAR LISTPOS-UPPER-BOUND-WEAK))
     (890 400
          (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
     (865 18 (:LINEAR LISTPOS-LOWER-BOUND-WEAK))
     (829 743 (:REWRITE DEFAULT-CDR))
     (489 56 (:LINEAR LISTPOS-COMPLETE))
     (424 212
          (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
     (272 224 (:REWRITE DEFAULT-<-1))
     (265 224 (:REWRITE DEFAULT-<-2))
     (248 248 (:TYPE-PRESCRIPTION LISTPOS))
     (212 212 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (172 114 (:REWRITE DEFAULT-UNARY-MINUS))
     (168 168 (:REWRITE LISTPOS-WHEN-ATOM-RIGHT))
     (168 168 (:REWRITE LISTPOS-WHEN-ATOM-LEFT))
     (120 10 (:REWRITE COMMUTATIVITY-2-OF-+))
     (92 92 (:TYPE-PRESCRIPTION NFIX))
     (84 13 (:REWRITE NTHCDR-WHEN-ZP))
     (74 25 (:REWRITE ZP-OPEN))
     (70 10
         (:REWRITE DISTRIBUTIVITY-OF-MINUS-OVER-+))
     (32 25 (:REWRITE FOLD-CONSTS-IN-+))
     (18 18
         (:LINEAR LISTPOS-UPPER-BOUND-STRONG-1))
     (16 2 (:REWRITE ASSOCIATIVITY-OF-+))
     (13 13 (:REWRITE NTHCDR-WHEN-ATOM))
     (8 8 (:REWRITE OPEN-SMALL-NTHCDR))
     (6 6 (:REWRITE SUBLISTP-WHEN-ATOM-RIGHT))
     (6 6 (:REWRITE SUBLISTP-WHEN-ATOM-LEFT))
     (6 3 (:REWRITE LIST-EQUIV-WHEN-ATOM-LEFT))
     (3 3
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP)))
