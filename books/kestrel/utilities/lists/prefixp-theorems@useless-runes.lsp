(SAME-CAR-WHEN-PREFIXP-AND-CONSP
     (109 4 (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
     (49 49 (:TYPE-PRESCRIPTION LEN))
     (45 9 (:DEFINITION LEN))
     (20 20 (:LINEAR LEN-WHEN-PREFIXP))
     (18 9 (:REWRITE DEFAULT-+-2))
     (9 9 (:REWRITE DEFAULT-+-1))
     (8 8 (:REWRITE DEFAULT-CDR))
     (5 5 (:REWRITE DEFAULT-CAR))
     (4 4 (:REWRITE PREFIXP-TRANSITIVE . 2))
     (4 4 (:REWRITE PREFIXP-TRANSITIVE . 1))
     (4 4
        (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
     (4 4
        (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
     (2 2
        (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
     (1 1 (:REWRITE CDR-CONS)))
(SAME-TAKE-WHEN-PREFIXP-AND-LONGER
     (784 28
          (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
     (573 44 (:REWRITE TAKE-OF-LEN-FREE))
     (403 217 (:REWRITE DEFAULT-+-2))
     (217 217 (:REWRITE DEFAULT-+-1))
     (69 33 (:REWRITE ZP-OPEN))
     (50 37 (:REWRITE DEFAULT-<-1))
     (42 38 (:REWRITE DEFAULT-CAR))
     (37 37 (:REWRITE DEFAULT-<-2))
     (36 12 (:REWRITE FOLD-CONSTS-IN-+))
     (28 28 (:REWRITE PREFIXP-TRANSITIVE . 2))
     (28 28 (:REWRITE PREFIXP-TRANSITIVE . 1))
     (28 28
         (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
     (28 28
         (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
     (20 20
         (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT)))
(PREFIXP-OF-CDR-CDR (233 7 (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
                    (129 21 (:DEFINITION LEN))
                    (96 96 (:TYPE-PRESCRIPTION LEN))
                    (54 27 (:REWRITE DEFAULT-+-2))
                    (31 31 (:REWRITE DEFAULT-CDR))
                    (28 28 (:LINEAR LEN-WHEN-PREFIXP))
                    (27 27 (:REWRITE DEFAULT-+-1))
                    (7 7 (:REWRITE PREFIXP-TRANSITIVE . 2))
                    (7 7 (:REWRITE PREFIXP-TRANSITIVE . 1))
                    (7 7
                       (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
                    (7 7
                       (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
                    (5 5
                       (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
                    (1 1 (:REWRITE DEFAULT-CAR))
                    (1 1 (:REWRITE CDR-CONS)))
(PREFIXP-OF-RCONS (267 6 (:REWRITE PREFIXP-OF-CDR-CDR))
                  (206 107 (:REWRITE DEFAULT-+-2))
                  (176 176 (:LINEAR LEN-WHEN-PREFIXP))
                  (128 8 (:REWRITE LEN-OF-APPEND))
                  (115 107 (:REWRITE DEFAULT-+-1))
                  (84 3
                      (:REWRITE PREFIXP-OF-APPEND-WHEN-SAME-LENGTH))
                  (76 72 (:REWRITE DEFAULT-CAR))
                  (39 39
                      (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
                  (39 39
                      (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
                  (38 38 (:REWRITE PREFIXP-TRANSITIVE . 2))
                  (38 38 (:REWRITE PREFIXP-TRANSITIVE . 1))
                  (38 20
                      (:REWRITE LIST-EQUIV-WHEN-ATOM-RIGHT))
                  (34 34
                      (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
                  (32 8 (:REWRITE COMMUTATIVITY-OF-+))
                  (12 3 (:REWRITE CAR-OF-APPEND))
                  (8 2 (:REWRITE FOLD-CONSTS-IN-+))
                  (3 3 (:REWRITE CDR-OF-APPEND-WHEN-CONSP)))
(PREFIXP-OF-BUTLAST-1-RIGHT (5238 309
                                  (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
                            (1853 984 (:REWRITE DEFAULT-+-2))
                            (1368 1218 (:REWRITE DEFAULT-CDR))
                            (1321 307
                                  (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
                            (984 984 (:REWRITE DEFAULT-+-1))
                            (805 9 (:REWRITE TAKE-WHEN-PREFIXP))
                            (572 44 (:REWRITE TAKE-OF-LEN-FREE))
                            (357 87 (:REWRITE LEN-OF-TAKE))
                            (317 282 (:REWRITE DEFAULT-<-2))
                            (286 282 (:REWRITE DEFAULT-<-1))
                            (229 229 (:REWRITE DEFAULT-CAR))
                            (176 176 (:TYPE-PRESCRIPTION BUTLAST))
                            (3 3 (:REWRITE CDR-CONS)))
