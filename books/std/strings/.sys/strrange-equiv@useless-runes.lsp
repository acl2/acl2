(STR::CHARACTER-LISTP-OF-MAKE-CHARACTER-LIST
 (17 15 (:REWRITE DEFAULT-CAR))
 (12 10 (:REWRITE DEFAULT-CDR))
 )
(STR::COERCE-INVERSE-BETTER
 (30 6 (:DEFINITION MAKE-CHARACTER-LIST))
 (16 7 (:REWRITE DEFAULT-COERCE-3))
 (14 14 (:REWRITE DEFAULT-CDR))
 (14 14 (:REWRITE DEFAULT-CAR))
 (12 2 (:DEFINITION CHARACTER-LISTP))
 (10 10 (:REWRITE DEFAULT-COERCE-2))
 (4 3 (:REWRITE DEFAULT-COERCE-1))
 )
(STR::EQUAL-OF-COERCE-STRING
 (54 6 (:REWRITE COERCE-INVERSE-1))
 (36 6 (:DEFINITION CHARACTER-LISTP))
 (34 34 (:REWRITE DEFAULT-CDR))
 (34 34 (:REWRITE DEFAULT-CAR))
 (34 16 (:REWRITE DEFAULT-COERCE-3))
 (22 22 (:REWRITE DEFAULT-COERCE-2))
 (6 6 (:REWRITE DEFAULT-COERCE-1))
 )
(STR::COERCE-OF-STR-FIX
 (5 5 (:REWRITE DEFAULT-COERCE-2))
 (5 5 (:REWRITE DEFAULT-COERCE-1))
 (1 1 (:REWRITE STR-FIX-DEFAULT))
 )
(STR::STRRANGE-EQUIV
 (164 14 (:DEFINITION NTH))
 (110 22 (:DEFINITION LEN))
 (85 69 (:REWRITE DEFAULT-<-1))
 (83 61 (:REWRITE DEFAULT-+-2))
 (75 69 (:REWRITE DEFAULT-<-2))
 (63 21 (:REWRITE ZP-WHEN-GT-0))
 (61 61 (:REWRITE DEFAULT-+-1))
 (57 21 (:REWRITE ZP-WHEN-INTEGERP))
 (40 14 (:REWRITE NATP-WHEN-GTE-0))
 (36 36 (:REWRITE DEFAULT-CDR))
 (28 28 (:REWRITE DEFAULT-COERCE-2))
 (28 28 (:REWRITE DEFAULT-COERCE-1))
 (16 8 (:REWRITE CHAR-FIX-DEFAULT))
 (14 14 (:REWRITE NATP-WHEN-INTEGERP))
 (14 14 (:REWRITE DEFAULT-CAR))
 (9 9 (:REWRITE ZP-OPEN))
 (9 5 (:REWRITE NFIX-WHEN-NOT-NATP))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(STR::MAKE-CHARACTER-LIST-REDEF
 (24 24 (:REWRITE DEFAULT-CAR))
 (23 23 (:REWRITE DEFAULT-CDR))
 )
(STR::STRRANGE-EQUIV-EQUALS-CHARLIST-SUBSEQS-EQUAL
 (3184 96 (:DEFINITION MAKE-CHARACTER-LIST))
 (2440 308 (:REWRITE CHAR-FIX-WHEN-CHARACTERP))
 (2364 444 (:REWRITE CONSP-OF-TAKE))
 (2244 762 (:REWRITE DEFAULT-CDR))
 (2176 280 (:REWRITE CHARACTERP-NTH))
 (1980 252 (:REWRITE CAR-OF-TAKE))
 (1229 1133 (:REWRITE DEFAULT-<-2))
 (1173 1133 (:REWRITE DEFAULT-<-1))
 (1159 831 (:REWRITE DEFAULT-+-2))
 (1052 148 (:DEFINITION LEN))
 (921 301 (:REWRITE ZP-WHEN-GT-0))
 (837 831 (:REWRITE DEFAULT-+-1))
 (760 386 (:REWRITE DEFAULT-CAR))
 (636 36 (:REWRITE CONSP-OF-NTHCDR))
 (616 616 (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
 (568 432 (:REWRITE NFIX-WHEN-NOT-NATP))
 (544 308 (:REWRITE CHAR-FIX-DEFAULT))
 (444 444 (:REWRITE DEFAULT-COERCE-2))
 (444 444 (:REWRITE DEFAULT-COERCE-1))
 (264 44 (:DEFINITION CHARACTER-LISTP))
 (112 112 (:REWRITE OPEN-SMALL-NTHCDR))
 (100 100 (:TYPE-PRESCRIPTION LNFIX$INLINE))
 (96 96 (:TYPE-PRESCRIPTION NATP))
 (96 48 (:REWRITE NATP-WHEN-GTE-0))
 (57 57 (:REWRITE ZP-OPEN))
 (48 48 (:REWRITE NATP-WHEN-INTEGERP))
 (12 12 (:REWRITE INEQUALITY-WITH-NFIX-HYP-1))
 )
(STR::STRRANGE-EQUIV-EQUALS-SUBSEQS-EQUAL
 (324 26 (:REWRITE CONSP-OF-TAKE))
 (264 4 (:DEFINITION MAKE-CHARACTER-LIST))
 (230 58 (:REWRITE ZP-WHEN-GT-0))
 (212 4 (:DEFINITION STR::MAKE-CHARACTER-LIST-REDEF))
 (142 48 (:REWRITE ZP-WHEN-INTEGERP))
 (134 26 (:REWRITE NFIX-POSITIVE-TO-NON-ZP))
 (108 12 (:REWRITE CAR-OF-TAKE))
 (96 12 (:REWRITE DEFAULT-CDR))
 (80 4 (:REWRITE NTHCDR-WHEN-ZP))
 (78 2 (:REWRITE DEFAULT-COERCE-3))
 (50 6 (:REWRITE DEFAULT-CAR))
 (42 18 (:REWRITE NFIX-WHEN-NATP))
 (40 40 (:REWRITE ZP-OPEN))
 (36 18 (:REWRITE NFIX-WHEN-NOT-NATP))
 (35 25 (:REWRITE DEFAULT-<-1))
 (28 14 (:REWRITE DEFAULT-+-2))
 (28 14 (:REWRITE DEFAULT-+-1))
 (26 26 (:TYPE-PRESCRIPTION ZP))
 (26 26 (:REWRITE INEQUALITY-WITH-NFIX-HYP-1))
 (26 6 (:REWRITE CHARACTERP-NTH))
 (25 25 (:REWRITE DEFAULT-<-2))
 (22 4 (:REWRITE CHAR-FIX-WHEN-CHARACTERP))
 (12 12 (:TYPE-PRESCRIPTION NATP))
 (12 6 (:REWRITE NATP-WHEN-GTE-0))
 (12 4 (:REWRITE CHAR-FIX-DEFAULT))
 (6 6 (:REWRITE NATP-WHEN-INTEGERP))
 (6 6 (:REWRITE INEQUALITY-WITH-NFIX-HYP-2))
 (6 6 (:REWRITE DEFAULT-COERCE-2))
 (6 6 (:REWRITE CAR-OF-NTHCDR))
 (4 4 (:TYPE-PRESCRIPTION CHARACTER-LISTP))
 (4 4 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 4 (:REWRITE OPEN-SMALL-NTHCDR))
 (4 4 (:REWRITE NTHCDR-WHEN-ATOM))
 (4 4 (:REWRITE DEFAULT-COERCE-1))
 (4 4 (:REWRITE CHARACTER-LISTP-COERCE))
 (4 2 (:REWRITE DEFAULT-UNARY-MINUS))
 (2 2 (:REWRITE STR-FIX-WHEN-STRINGP))
 (2 2 (:REWRITE STR-FIX-DEFAULT))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 )
