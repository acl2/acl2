(TYPES::LEN-LEN-INDUCTION)
(TYPES::LEN-EQUIV)
(TYPES::LEN-EQUIV-IS-AN-EQUIVALENCE)
(TYPES::LEN-EQUIV-IMPLIES-EQUAL-CONSP-1
 (22 12 (:REWRITE DEFAULT-+-2))
 (12 12 (:REWRITE DEFAULT-+-1))
 (10 10 (:REWRITE DEFAULT-CDR))
 )
(TYPES::LEN-EQUIV-IMPLIES-LEN-EQUIV-CONS-2
 (16 8 (:REWRITE DEFAULT-+-2))
 (8 8 (:REWRITE DEFAULT-+-1))
 (6 6 (:REWRITE DEFAULT-CDR))
 )
(TYPES::LEN-EQUIV-IMPLIES-LEN-EQUIV-CDR-1
 (16 8 (:REWRITE DEFAULT-+-2))
 (8 8 (:REWRITE DEFAULT-+-1))
 )
(TYPES::LEN-EQUIV-IMPLIES-EQUAL-LEN-1)
(TYPES::GET-KEY?)
(TYPES::DEF-TYPE-LIST-FN)
(TYPES::DEF-TYPE-LIST-FN-WRAPPER)
(TMP-DEFTYPES-NATP-OF-NFIX)
(TMP-DEFTYPES-NFIX-WHEN-NATP
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 )
(TYPES::NAT-LIST-P)
(STD::DEFLIST-LOCAL-BOOLEANP-ELEMENT-THM)
(TYPES::NAT-LIST-P-OF-CONS)
(TYPES::NAT-LIST-P-OF-CDR-WHEN-NAT-LIST-P)
(TYPES::NAT-LIST-P-WHEN-NOT-CONSP)
(TYPES::NATP-OF-CAR-WHEN-NAT-LIST-P)
(TYPES::TRUE-LISTP-WHEN-NAT-LIST-P)
(TYPES::NAT-LIST-FIX$INLINE)
(TYPES::NAT-LIST-P-OF-NAT-LIST-FIX
 (14 1 (:REWRITE TMP-DEFTYPES-NFIX-WHEN-NATP))
 (11 2 (:REWRITE TYPES::NATP-OF-CAR-WHEN-NAT-LIST-P))
 (9 5 (:REWRITE TYPES::NAT-LIST-P-WHEN-NOT-CONSP))
 (8 1 (:DEFINITION TYPES::NAT-LIST-P))
 (3 3 (:TYPE-PRESCRIPTION NATP))
 (2 1 (:REWRITE TYPES::NAT-LIST-P-OF-CDR-WHEN-NAT-LIST-P))
 )
(TYPES::NAT-LIST-FIX-WHEN-NAT-LIST-P
 (17 4 (:REWRITE TYPES::NAT-LIST-P-OF-CDR-WHEN-NAT-LIST-P))
 (9 3 (:REWRITE TYPES::NATP-OF-CAR-WHEN-NAT-LIST-P))
 )
(TYPES::NAT-LIST-FIX$INLINE
 (4 4 (:REWRITE TYPES::NAT-LIST-P-WHEN-NOT-CONSP))
 (4 1 (:REWRITE TYPES::NATP-OF-CAR-WHEN-NAT-LIST-P))
 (4 1 (:REWRITE TYPES::NAT-LIST-P-OF-CDR-WHEN-NAT-LIST-P))
 )
(FTY::TMP-DEFFIXTYPE-IDEMPOTENT
 (1 1 (:REWRITE TYPES::NAT-LIST-P-WHEN-NOT-CONSP))
 )
(TYPES::NAT-LIST-EQUIV$INLINE)
(TYPES::NAT-LIST-EQUIV-IS-AN-EQUIVALENCE)
(TYPES::NAT-LIST-EQUIV-IMPLIES-EQUAL-NAT-LIST-FIX-1)
(TYPES::NAT-LIST-FIX-UNDER-NAT-LIST-EQUIV)
(TYPES::EQUAL-OF-NAT-LIST-FIX-1-FORWARD-TO-NAT-LIST-EQUIV)
(TYPES::EQUAL-OF-NAT-LIST-FIX-2-FORWARD-TO-NAT-LIST-EQUIV)
(TYPES::NAT-LIST-EQUIV-OF-NAT-LIST-FIX-1-FORWARD)
(TYPES::NAT-LIST-EQUIV-OF-NAT-LIST-FIX-2-FORWARD)
(TYPES::CAR-OF-NAT-LIST-FIX-X-UNDER-NAT-EQUIV
 (21 3 (:REWRITE TMP-DEFTYPES-NFIX-WHEN-NATP))
 (12 12 (:TYPE-PRESCRIPTION TYPES::NAT-LIST-P))
 (12 3 (:REWRITE TYPES::NATP-OF-CAR-WHEN-NAT-LIST-P))
 (12 2 (:REWRITE TYPES::NAT-LIST-FIX-WHEN-NAT-LIST-P))
 (6 6 (:TYPE-PRESCRIPTION NATP))
 (6 6 (:REWRITE TYPES::NAT-LIST-P-WHEN-NOT-CONSP))
 (4 1 (:REWRITE TYPES::NAT-LIST-P-OF-CDR-WHEN-NAT-LIST-P))
 (3 3 (:TYPE-PRESCRIPTION TYPES::NAT-LIST-FIX$INLINE))
 )
(TYPES::CAR-NAT-LIST-EQUIV-CONGRUENCE-ON-X-UNDER-NAT-EQUIV)
(TYPES::CDR-OF-NAT-LIST-FIX-X-UNDER-NAT-LIST-EQUIV
 (29 3 (:REWRITE TYPES::NAT-LIST-P-OF-CDR-WHEN-NAT-LIST-P))
 (14 2 (:REWRITE TMP-DEFTYPES-NFIX-WHEN-NATP))
 (8 2 (:REWRITE TYPES::NATP-OF-CAR-WHEN-NAT-LIST-P))
 (4 4 (:TYPE-PRESCRIPTION NATP))
 )
(TYPES::CDR-NAT-LIST-EQUIV-CONGRUENCE-ON-X-UNDER-NAT-LIST-EQUIV)
(TYPES::CONS-OF-NFIX-X-UNDER-NAT-LIST-EQUIV
 (19 4 (:REWRITE TYPES::NAT-LIST-FIX-WHEN-NAT-LIST-P))
 (8 2 (:REWRITE TYPES::NAT-LIST-P-OF-CONS))
 (6 6 (:TYPE-PRESCRIPTION TYPES::NAT-LIST-P))
 (5 5 (:REWRITE TYPES::NAT-LIST-P-WHEN-NOT-CONSP))
 (3 3 (:TYPE-PRESCRIPTION NATP))
 )
(TYPES::CONS-NAT-EQUIV-CONGRUENCE-ON-X-UNDER-NAT-LIST-EQUIV)
(TYPES::CONS-OF-NAT-LIST-FIX-Y-UNDER-NAT-LIST-EQUIV
 (10 2 (:REWRITE TYPES::NAT-LIST-P-OF-CONS))
 (6 6 (:TYPE-PRESCRIPTION NATP))
 (5 4 (:REWRITE TYPES::NAT-LIST-P-WHEN-NOT-CONSP))
 (4 2 (:REWRITE TMP-DEFTYPES-NFIX-WHEN-NATP))
 )
(TYPES::CONS-NAT-LIST-EQUIV-CONGRUENCE-ON-Y-UNDER-NAT-LIST-EQUIV)
(TYPES::CONSP-OF-NAT-LIST-FIX
 (12 2 (:REWRITE TYPES::NAT-LIST-FIX-WHEN-NAT-LIST-P))
 (8 8 (:TYPE-PRESCRIPTION TYPES::NAT-LIST-P))
 (7 1 (:REWRITE TMP-DEFTYPES-NFIX-WHEN-NATP))
 (4 4 (:REWRITE TYPES::NAT-LIST-P-WHEN-NOT-CONSP))
 (4 1 (:REWRITE TYPES::NATP-OF-CAR-WHEN-NAT-LIST-P))
 (4 1 (:REWRITE TYPES::NAT-LIST-P-OF-CDR-WHEN-NAT-LIST-P))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 )
(TYPES::NAT-LIST-FIX-UNDER-IFF
 (12 2 (:REWRITE TYPES::NAT-LIST-FIX-WHEN-NAT-LIST-P))
 (8 8 (:TYPE-PRESCRIPTION TYPES::NAT-LIST-P))
 (7 1 (:REWRITE TMP-DEFTYPES-NFIX-WHEN-NATP))
 (4 4 (:REWRITE TYPES::NAT-LIST-P-WHEN-NOT-CONSP))
 (4 1 (:REWRITE TYPES::NATP-OF-CAR-WHEN-NAT-LIST-P))
 (4 1 (:REWRITE TYPES::NAT-LIST-P-OF-CDR-WHEN-NAT-LIST-P))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 )
(TYPES::NAT-LIST-FIX-OF-CONS
 (12 3 (:REWRITE TYPES::NAT-LIST-FIX-WHEN-NAT-LIST-P))
 (4 4 (:TYPE-PRESCRIPTION TYPES::NAT-LIST-P))
 (4 2 (:REWRITE TMP-DEFTYPES-NFIX-WHEN-NATP))
 (4 1 (:REWRITE TYPES::NAT-LIST-P-OF-CONS))
 (3 3 (:TYPE-PRESCRIPTION NATP))
 (3 3 (:REWRITE TYPES::NAT-LIST-P-WHEN-NOT-CONSP))
 )
(TYPES::LEN-OF-NAT-LIST-FIX
 (23 4 (:REWRITE TYPES::NAT-LIST-FIX-WHEN-NAT-LIST-P))
 (13 13 (:TYPE-PRESCRIPTION TYPES::NAT-LIST-P))
 (8 2 (:REWRITE TYPES::NAT-LIST-P-OF-CDR-WHEN-NAT-LIST-P))
 (7 7 (:REWRITE TYPES::NAT-LIST-P-WHEN-NOT-CONSP))
 (7 1 (:REWRITE TMP-DEFTYPES-NFIX-WHEN-NATP))
 (4 1 (:REWRITE TYPES::NATP-OF-CAR-WHEN-NAT-LIST-P))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 (1 1 (:REWRITE FTY::EQUAL-OF-LEN))
 )
(TYPES::NAT-LIST-FIX-OF-APPEND
 (56 10 (:REWRITE TYPES::NAT-LIST-FIX-WHEN-NAT-LIST-P))
 (23 23 (:TYPE-PRESCRIPTION TYPES::NAT-LIST-P))
 (18 12 (:REWRITE TYPES::NAT-LIST-P-WHEN-NOT-CONSP))
 (8 2 (:REWRITE TMP-DEFTYPES-NFIX-WHEN-NATP))
 (8 2 (:REWRITE TYPES::NAT-LIST-P-OF-CDR-WHEN-NAT-LIST-P))
 (4 1 (:REWRITE TYPES::NATP-OF-CAR-WHEN-NAT-LIST-P))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 )
(TYPES::NAT-LIST-FIX-OF-REPEAT
 (20 2 (:REWRITE TYPES::NAT-LIST-FIX-WHEN-NAT-LIST-P))
 (10 4 (:REWRITE TMP-DEFTYPES-NFIX-WHEN-NATP))
 (8 2 (:REWRITE TYPES::NAT-LIST-P-WHEN-NOT-CONSP))
 (6 6 (:TYPE-PRESCRIPTION NATP))
 (4 4 (:TYPE-PRESCRIPTION TYPES::NAT-LIST-P))
 (1 1 (:REWRITE-QUOTED-CONSTANT TYPES::NAT-LIST-FIX-UNDER-NAT-LIST-EQUIV))
 )
(TYPES::LIST-EQUIV-REFINES-NAT-LIST-EQUIV
 (98 14 (:REWRITE TYPES::NAT-LIST-FIX-WHEN-NAT-LIST-P))
 (72 8 (:REWRITE TMP-DEFTYPES-NFIX-WHEN-NATP))
 (70 70 (:TYPE-PRESCRIPTION TYPES::NAT-LIST-P))
 (60 18 (:REWRITE TYPES::NAT-LIST-P-OF-CDR-WHEN-NAT-LIST-P))
 (48 8 (:REWRITE TYPES::NATP-OF-CAR-WHEN-NAT-LIST-P))
 (36 36 (:REWRITE TYPES::NAT-LIST-P-WHEN-NOT-CONSP))
 (16 16 (:TYPE-PRESCRIPTION NATP))
 )
(TYPES::NTH-OF-NAT-LIST-FIX
 (111 16 (:REWRITE TYPES::NAT-LIST-FIX-WHEN-NAT-LIST-P))
 (73 73 (:TYPE-PRESCRIPTION NATP))
 (48 12 (:REWRITE TYPES::NAT-LIST-P-OF-CDR-WHEN-NAT-LIST-P))
 (35 26 (:REWRITE DEFAULT-+-2))
 (33 33 (:REWRITE TYPES::NAT-LIST-P-WHEN-NOT-CONSP))
 (28 22 (:REWRITE DEFAULT-CDR))
 (26 26 (:REWRITE DEFAULT-+-1))
 (21 17 (:REWRITE DEFAULT-<-2))
 (20 5 (:REWRITE TYPES::NATP-OF-CAR-WHEN-NAT-LIST-P))
 (19 7 (:REWRITE ZP-OPEN))
 (17 17 (:REWRITE DEFAULT-<-1))
 (13 13 (:REWRITE TYPES::CONSP-OF-NAT-LIST-FIX))
 (12 4 (:REWRITE FOLD-CONSTS-IN-+))
 (10 4 (:REWRITE DEFAULT-CAR))
 (9 3 (:DEFINITION NATP))
 (2 2 (:REWRITE-QUOTED-CONSTANT FIX-UNDER-NUMBER-EQUIV))
 )
(TYPES::NAT-LIST-EQUIV-IMPLIES-NAT-LIST-EQUIV-APPEND-1
 (181 32 (:REWRITE TYPES::NAT-LIST-FIX-WHEN-NAT-LIST-P))
 (131 17 (:REWRITE TMP-DEFTYPES-NFIX-WHEN-NATP))
 (126 126 (:TYPE-PRESCRIPTION TYPES::NAT-LIST-P))
 (80 17 (:REWRITE TYPES::NATP-OF-CAR-WHEN-NAT-LIST-P))
 (79 22 (:REWRITE TYPES::NAT-LIST-P-OF-CDR-WHEN-NAT-LIST-P))
 (64 64 (:REWRITE TYPES::NAT-LIST-P-WHEN-NOT-CONSP))
 (34 34 (:TYPE-PRESCRIPTION NATP))
 )
(TYPES::NAT-LIST-EQUIV-IMPLIES-NAT-LIST-EQUIV-APPEND-2
 (267 46 (:REWRITE TYPES::NAT-LIST-FIX-WHEN-NAT-LIST-P))
 (206 26 (:REWRITE TMP-DEFTYPES-NFIX-WHEN-NATP))
 (189 189 (:TYPE-PRESCRIPTION TYPES::NAT-LIST-P))
 (138 39 (:REWRITE TYPES::NAT-LIST-P-OF-CDR-WHEN-NAT-LIST-P))
 (128 26 (:REWRITE TYPES::NATP-OF-CAR-WHEN-NAT-LIST-P))
 (95 95 (:REWRITE TYPES::NAT-LIST-P-WHEN-NOT-CONSP))
 (52 52 (:TYPE-PRESCRIPTION NATP))
 (4 4 (:REWRITE TYPES::CONSP-OF-NAT-LIST-FIX))
 )
(TYPES::NAT-LIST-EQUIV-IMPLIES-NAT-LIST-EQUIV-NTHCDR-2
 (249 39 (:REWRITE TYPES::NAT-LIST-FIX-WHEN-NAT-LIST-P))
 (175 175 (:TYPE-PRESCRIPTION TYPES::NAT-LIST-P))
 (174 22 (:REWRITE TMP-DEFTYPES-NFIX-WHEN-NATP))
 (117 33 (:REWRITE TYPES::NAT-LIST-P-OF-CDR-WHEN-NAT-LIST-P))
 (108 22 (:REWRITE TYPES::NATP-OF-CAR-WHEN-NAT-LIST-P))
 (88 88 (:REWRITE TYPES::NAT-LIST-P-WHEN-NOT-CONSP))
 (44 44 (:TYPE-PRESCRIPTION NATP))
 )
(TYPES::NAT-LIST-EQUIV-IMPLIES-NAT-LIST-EQUIV-TAKE-2
 (326 38 (:REWRITE TYPES::NAT-LIST-FIX-WHEN-NAT-LIST-P))
 (220 28 (:REWRITE TMP-DEFTYPES-NFIX-WHEN-NATP))
 (190 190 (:TYPE-PRESCRIPTION TYPES::NAT-LIST-P))
 (149 39 (:REWRITE TYPES::NAT-LIST-P-OF-CDR-WHEN-NAT-LIST-P))
 (140 26 (:REWRITE TYPES::NATP-OF-CAR-WHEN-NAT-LIST-P))
 (119 95 (:REWRITE TYPES::NAT-LIST-P-WHEN-NOT-CONSP))
 (52 52 (:TYPE-PRESCRIPTION NATP))
 (6 6 (:REWRITE-QUOTED-CONSTANT TYPES::NAT-LIST-FIX-UNDER-NAT-LIST-EQUIV))
 )
(TMP-DEFTYPES-INTEGERP-OF-IFIX)
(TMP-DEFTYPES-IFIX-WHEN-INTEGERP)
(TYPES::INT-LISTP)
(STD::DEFLIST-LOCAL-BOOLEANP-ELEMENT-THM)
(TYPES::INT-LISTP-OF-CONS)
(TYPES::INT-LISTP-OF-CDR-WHEN-INT-LISTP)
(TYPES::INT-LISTP-WHEN-NOT-CONSP)
(TYPES::INTEGERP-OF-CAR-WHEN-INT-LISTP)
(TYPES::TRUE-LISTP-WHEN-INT-LISTP)
(TYPES::INT-LIST-FIX$INLINE)
(TYPES::INT-LISTP-OF-INT-LIST-FIX
 (11 1 (:REWRITE TMP-DEFTYPES-IFIX-WHEN-INTEGERP))
 (10 2 (:REWRITE TYPES::INTEGERP-OF-CAR-WHEN-INT-LISTP))
 (9 5 (:REWRITE TYPES::INT-LISTP-WHEN-NOT-CONSP))
 (7 1 (:DEFINITION TYPES::INT-LISTP))
 (2 1 (:REWRITE TYPES::INT-LISTP-OF-CDR-WHEN-INT-LISTP))
 )
(TYPES::INT-LIST-FIX-WHEN-INT-LISTP
 (17 4 (:REWRITE TYPES::INT-LISTP-OF-CDR-WHEN-INT-LISTP))
 (9 3 (:REWRITE TYPES::INTEGERP-OF-CAR-WHEN-INT-LISTP))
 )
(TYPES::INT-LIST-FIX$INLINE
 (4 4 (:REWRITE TYPES::INT-LISTP-WHEN-NOT-CONSP))
 (4 1 (:REWRITE TYPES::INTEGERP-OF-CAR-WHEN-INT-LISTP))
 (4 1 (:REWRITE TYPES::INT-LISTP-OF-CDR-WHEN-INT-LISTP))
 )
(FTY::TMP-DEFFIXTYPE-IDEMPOTENT
 (1 1 (:REWRITE TYPES::INT-LISTP-WHEN-NOT-CONSP))
 )
(TYPES::INT-LIST-EQUIV$INLINE)
(TYPES::INT-LIST-EQUIV-IS-AN-EQUIVALENCE)
(TYPES::INT-LIST-EQUIV-IMPLIES-EQUAL-INT-LIST-FIX-1)
(TYPES::INT-LIST-FIX-UNDER-INT-LIST-EQUIV)
(TYPES::EQUAL-OF-INT-LIST-FIX-1-FORWARD-TO-INT-LIST-EQUIV)
(TYPES::EQUAL-OF-INT-LIST-FIX-2-FORWARD-TO-INT-LIST-EQUIV)
(TYPES::INT-LIST-EQUIV-OF-INT-LIST-FIX-1-FORWARD)
(TYPES::INT-LIST-EQUIV-OF-INT-LIST-FIX-2-FORWARD)
(TYPES::CAR-OF-INT-LIST-FIX-X-UNDER-INT-EQUIV
 (15 3 (:REWRITE TMP-DEFTYPES-IFIX-WHEN-INTEGERP))
 (12 12 (:TYPE-PRESCRIPTION TYPES::INT-LISTP))
 (12 3 (:REWRITE TYPES::INTEGERP-OF-CAR-WHEN-INT-LISTP))
 (12 2 (:REWRITE TYPES::INT-LIST-FIX-WHEN-INT-LISTP))
 (6 6 (:REWRITE TYPES::INT-LISTP-WHEN-NOT-CONSP))
 (4 1 (:REWRITE TYPES::INT-LISTP-OF-CDR-WHEN-INT-LISTP))
 (3 3 (:TYPE-PRESCRIPTION TYPES::INT-LIST-FIX$INLINE))
 )
(TYPES::CAR-INT-LIST-EQUIV-CONGRUENCE-ON-X-UNDER-INT-EQUIV)
(TYPES::CDR-OF-INT-LIST-FIX-X-UNDER-INT-LIST-EQUIV
 (27 3 (:REWRITE TYPES::INT-LISTP-OF-CDR-WHEN-INT-LISTP))
 (10 2 (:REWRITE TMP-DEFTYPES-IFIX-WHEN-INTEGERP))
 (8 2 (:REWRITE TYPES::INTEGERP-OF-CAR-WHEN-INT-LISTP))
 )
(TYPES::CDR-INT-LIST-EQUIV-CONGRUENCE-ON-X-UNDER-INT-LIST-EQUIV)
(TYPES::CONS-OF-IFIX-X-UNDER-INT-LIST-EQUIV
 (18 4 (:REWRITE TYPES::INT-LIST-FIX-WHEN-INT-LISTP))
 (7 2 (:REWRITE TYPES::INT-LISTP-OF-CONS))
 (6 6 (:TYPE-PRESCRIPTION TYPES::INT-LISTP))
 (5 5 (:REWRITE TYPES::INT-LISTP-WHEN-NOT-CONSP))
 )
(TYPES::CONS-INT-EQUIV-CONGRUENCE-ON-X-UNDER-INT-LIST-EQUIV)
(TYPES::CONS-OF-INT-LIST-FIX-Y-UNDER-INT-LIST-EQUIV
 (6 2 (:REWRITE TYPES::INT-LISTP-OF-CONS))
 (5 4 (:REWRITE TYPES::INT-LISTP-WHEN-NOT-CONSP))
 (2 2 (:REWRITE TMP-DEFTYPES-IFIX-WHEN-INTEGERP))
 )
(TYPES::CONS-INT-LIST-EQUIV-CONGRUENCE-ON-Y-UNDER-INT-LIST-EQUIV)
(TYPES::CONSP-OF-INT-LIST-FIX
 (12 2 (:REWRITE TYPES::INT-LIST-FIX-WHEN-INT-LISTP))
 (8 8 (:TYPE-PRESCRIPTION TYPES::INT-LISTP))
 (5 1 (:REWRITE TMP-DEFTYPES-IFIX-WHEN-INTEGERP))
 (4 4 (:REWRITE TYPES::INT-LISTP-WHEN-NOT-CONSP))
 (4 1 (:REWRITE TYPES::INTEGERP-OF-CAR-WHEN-INT-LISTP))
 (4 1 (:REWRITE TYPES::INT-LISTP-OF-CDR-WHEN-INT-LISTP))
 )
(TYPES::INT-LIST-FIX-UNDER-IFF
 (12 2 (:REWRITE TYPES::INT-LIST-FIX-WHEN-INT-LISTP))
 (8 8 (:TYPE-PRESCRIPTION TYPES::INT-LISTP))
 (5 1 (:REWRITE TMP-DEFTYPES-IFIX-WHEN-INTEGERP))
 (4 4 (:REWRITE TYPES::INT-LISTP-WHEN-NOT-CONSP))
 (4 1 (:REWRITE TYPES::INTEGERP-OF-CAR-WHEN-INT-LISTP))
 (4 1 (:REWRITE TYPES::INT-LISTP-OF-CDR-WHEN-INT-LISTP))
 )
(TYPES::INT-LIST-FIX-OF-CONS
 (11 3 (:REWRITE TYPES::INT-LIST-FIX-WHEN-INT-LISTP))
 (4 4 (:TYPE-PRESCRIPTION TYPES::INT-LISTP))
 (3 3 (:REWRITE TYPES::INT-LISTP-WHEN-NOT-CONSP))
 (3 1 (:REWRITE TYPES::INT-LISTP-OF-CONS))
 (2 2 (:REWRITE TMP-DEFTYPES-IFIX-WHEN-INTEGERP))
 )
(TYPES::LEN-OF-INT-LIST-FIX
 (23 4 (:REWRITE TYPES::INT-LIST-FIX-WHEN-INT-LISTP))
 (13 13 (:TYPE-PRESCRIPTION TYPES::INT-LISTP))
 (8 2 (:REWRITE TYPES::INT-LISTP-OF-CDR-WHEN-INT-LISTP))
 (7 7 (:REWRITE TYPES::INT-LISTP-WHEN-NOT-CONSP))
 (5 1 (:REWRITE TMP-DEFTYPES-IFIX-WHEN-INTEGERP))
 (4 1 (:REWRITE TYPES::INTEGERP-OF-CAR-WHEN-INT-LISTP))
 (1 1 (:REWRITE FTY::EQUAL-OF-LEN))
 )
(TYPES::INT-LIST-FIX-OF-APPEND
 (56 10 (:REWRITE TYPES::INT-LIST-FIX-WHEN-INT-LISTP))
 (23 23 (:TYPE-PRESCRIPTION TYPES::INT-LISTP))
 (18 12 (:REWRITE TYPES::INT-LISTP-WHEN-NOT-CONSP))
 (8 2 (:REWRITE TYPES::INT-LISTP-OF-CDR-WHEN-INT-LISTP))
 (6 2 (:REWRITE TMP-DEFTYPES-IFIX-WHEN-INTEGERP))
 (4 1 (:REWRITE TYPES::INTEGERP-OF-CAR-WHEN-INT-LISTP))
 )
(TYPES::INT-LIST-FIX-OF-REPEAT
 (20 2 (:REWRITE TYPES::INT-LIST-FIX-WHEN-INT-LISTP))
 (8 2 (:REWRITE TYPES::INT-LISTP-WHEN-NOT-CONSP))
 (4 4 (:TYPE-PRESCRIPTION TYPES::INT-LISTP))
 (4 4 (:REWRITE TMP-DEFTYPES-IFIX-WHEN-INTEGERP))
 (1 1 (:REWRITE-QUOTED-CONSTANT TYPES::INT-LIST-FIX-UNDER-INT-LIST-EQUIV))
 )
(TYPES::LIST-EQUIV-REFINES-INT-LIST-EQUIV
 (98 14 (:REWRITE TYPES::INT-LIST-FIX-WHEN-INT-LISTP))
 (70 70 (:TYPE-PRESCRIPTION TYPES::INT-LISTP))
 (60 18 (:REWRITE TYPES::INT-LISTP-OF-CDR-WHEN-INT-LISTP))
 (56 8 (:REWRITE TMP-DEFTYPES-IFIX-WHEN-INTEGERP))
 (48 8 (:REWRITE TYPES::INTEGERP-OF-CAR-WHEN-INT-LISTP))
 (36 36 (:REWRITE TYPES::INT-LISTP-WHEN-NOT-CONSP))
 )
(TYPES::NTH-OF-INT-LIST-FIX
 (111 16 (:REWRITE TYPES::INT-LIST-FIX-WHEN-INT-LISTP))
 (48 12 (:REWRITE TYPES::INT-LISTP-OF-CDR-WHEN-INT-LISTP))
 (37 17 (:REWRITE TMP-DEFTYPES-IFIX-WHEN-INTEGERP))
 (33 33 (:REWRITE TYPES::INT-LISTP-WHEN-NOT-CONSP))
 (32 24 (:REWRITE DEFAULT-+-2))
 (26 20 (:REWRITE DEFAULT-CDR))
 (24 24 (:REWRITE DEFAULT-+-1))
 (20 16 (:REWRITE DEFAULT-<-2))
 (20 5 (:REWRITE TYPES::INTEGERP-OF-CAR-WHEN-INT-LISTP))
 (19 7 (:REWRITE ZP-OPEN))
 (16 16 (:REWRITE DEFAULT-<-1))
 (13 13 (:REWRITE TYPES::CONSP-OF-INT-LIST-FIX))
 (12 4 (:REWRITE FOLD-CONSTS-IN-+))
 (10 4 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE-QUOTED-CONSTANT FIX-UNDER-NUMBER-EQUIV))
 )
(TYPES::INT-LIST-EQUIV-IMPLIES-INT-LIST-EQUIV-APPEND-1
 (181 32 (:REWRITE TYPES::INT-LIST-FIX-WHEN-INT-LISTP))
 (126 126 (:TYPE-PRESCRIPTION TYPES::INT-LISTP))
 (97 17 (:REWRITE TMP-DEFTYPES-IFIX-WHEN-INTEGERP))
 (80 17 (:REWRITE TYPES::INTEGERP-OF-CAR-WHEN-INT-LISTP))
 (79 22 (:REWRITE TYPES::INT-LISTP-OF-CDR-WHEN-INT-LISTP))
 (64 64 (:REWRITE TYPES::INT-LISTP-WHEN-NOT-CONSP))
 )
(TYPES::INT-LIST-EQUIV-IMPLIES-INT-LIST-EQUIV-APPEND-2
 (267 46 (:REWRITE TYPES::INT-LIST-FIX-WHEN-INT-LISTP))
 (189 189 (:TYPE-PRESCRIPTION TYPES::INT-LISTP))
 (154 26 (:REWRITE TMP-DEFTYPES-IFIX-WHEN-INTEGERP))
 (138 39 (:REWRITE TYPES::INT-LISTP-OF-CDR-WHEN-INT-LISTP))
 (128 26 (:REWRITE TYPES::INTEGERP-OF-CAR-WHEN-INT-LISTP))
 (95 95 (:REWRITE TYPES::INT-LISTP-WHEN-NOT-CONSP))
 (4 4 (:REWRITE TYPES::CONSP-OF-INT-LIST-FIX))
 )
(TYPES::INT-LIST-EQUIV-IMPLIES-INT-LIST-EQUIV-NTHCDR-2
 (249 39 (:REWRITE TYPES::INT-LIST-FIX-WHEN-INT-LISTP))
 (175 175 (:TYPE-PRESCRIPTION TYPES::INT-LISTP))
 (130 22 (:REWRITE TMP-DEFTYPES-IFIX-WHEN-INTEGERP))
 (117 33 (:REWRITE TYPES::INT-LISTP-OF-CDR-WHEN-INT-LISTP))
 (108 22 (:REWRITE TYPES::INTEGERP-OF-CAR-WHEN-INT-LISTP))
 (88 88 (:REWRITE TYPES::INT-LISTP-WHEN-NOT-CONSP))
 )
(TYPES::INT-LIST-EQUIV-IMPLIES-INT-LIST-EQUIV-TAKE-2
 (326 38 (:REWRITE TYPES::INT-LIST-FIX-WHEN-INT-LISTP))
 (190 190 (:TYPE-PRESCRIPTION TYPES::INT-LISTP))
 (168 28 (:REWRITE TMP-DEFTYPES-IFIX-WHEN-INTEGERP))
 (149 39 (:REWRITE TYPES::INT-LISTP-OF-CDR-WHEN-INT-LISTP))
 (140 26 (:REWRITE TYPES::INTEGERP-OF-CAR-WHEN-INT-LISTP))
 (119 95 (:REWRITE TYPES::INT-LISTP-WHEN-NOT-CONSP))
 (6 6 (:REWRITE-QUOTED-CONSTANT TYPES::INT-LIST-FIX-UNDER-INT-LIST-EQUIV))
 )
(OPEN-INT-LIST-FIX
 (54 6 (:REWRITE TYPES::INT-LIST-FIX-WHEN-INT-LISTP))
 (38 9 (:REWRITE TYPES::INT-LISTP-OF-CDR-WHEN-INT-LISTP))
 (28 5 (:REWRITE TYPES::INTEGERP-OF-CAR-WHEN-INT-LISTP))
 (20 20 (:REWRITE TYPES::INT-LISTP-WHEN-NOT-CONSP))
 (7 7 (:REWRITE DEFAULT-CDR))
 (6 6 (:REWRITE DEFAULT-CAR))
 )
(TYPES::INT-LIST-FIX!)
(TYPES::INT-LIST-FIX!-TO-INT-LIST-FIX
 (28 5 (:REWRITE TYPES::INT-LIST-FIX-WHEN-INT-LISTP))
 (24 6 (:REWRITE TYPES::INTEGERP-OF-CAR-WHEN-INT-LISTP))
 (14 13 (:REWRITE TYPES::INT-LISTP-WHEN-NOT-CONSP))
 (8 2 (:REWRITE TYPES::INT-LISTP-OF-CDR-WHEN-INT-LISTP))
 (6 6 (:REWRITE DEFAULT-CAR))
 (4 4 (:REWRITE DEFAULT-CDR))
 )
(TYPES::OPEN-INT-LIST-EQUIV
 (248 28 (:REWRITE TYPES::INT-LIST-FIX-WHEN-INT-LISTP))
 (196 46 (:REWRITE TYPES::INT-LISTP-OF-CDR-WHEN-INT-LISTP))
 (136 22 (:REWRITE TYPES::INTEGERP-OF-CAR-WHEN-INT-LISTP))
 (92 92 (:REWRITE TYPES::INT-LISTP-WHEN-NOT-CONSP))
 (38 38 (:REWRITE DEFAULT-CDR))
 (28 28 (:REWRITE DEFAULT-CAR))
 (14 14 (:REWRITE OPEN-INT-LIST-FIX))
 )
(TYPES::INT-LIST-EQUIV-INDUCTION)
(TYPES::INT-LIST-EQUIV-IMPLIES-INT-EQUIV-NTH-2
 (96 24 (:REWRITE TYPES::INTEGERP-OF-CAR-WHEN-INT-LISTP))
 (48 48 (:REWRITE DEFAULT-CAR))
 (26 26 (:REWRITE DEFAULT-CDR))
 (24 24 (:REWRITE TYPES::INT-LISTP-WHEN-NOT-CONSP))
 (18 18 (:REWRITE ZP-OPEN))
 (16 16 (:REWRITE DEFAULT-+-2))
 (16 16 (:REWRITE DEFAULT-+-1))
 )
(PICK-A-POINT::INT-LIST-EQUIV-POINT)
(PICK-A-POINT::INT-LIST-EQUIV-DEFINITION
 (200 32 (:REWRITE TYPES::INTEGERP-OF-CAR-WHEN-INT-LISTP))
 (72 18 (:REWRITE TYPES::INT-LISTP-OF-CDR-WHEN-INT-LISTP))
 (56 56 (:REWRITE DEFAULT-CAR))
 (50 50 (:REWRITE TYPES::INT-LISTP-WHEN-NOT-CONSP))
 (46 46 (:REWRITE DEFAULT-CDR))
 )
(PICK-A-POINT::INT-LIST-EQUIV-CANARY
 (552 84 (:REWRITE TYPES::INTEGERP-OF-CAR-WHEN-INT-LISTP))
 (232 10 (:DEFINITION TYPES::OPEN-INT-LIST-EQUIV))
 (216 54 (:REWRITE TYPES::INT-LISTP-OF-CDR-WHEN-INT-LISTP))
 (182 10 (:DEFINITION INT-EQUIV$INLINE))
 (138 138 (:REWRITE TYPES::INT-LISTP-WHEN-NOT-CONSP))
 (132 132 (:REWRITE DEFAULT-CAR))
 (112 112 (:REWRITE DEFAULT-CDR))
 (46 23 (:REWRITE DEFAULT-+-2))
 (23 23 (:REWRITE DEFAULT-+-1))
 )
(PICK-A-POINT::INT-LIST-EQUIV-POINT-UPPER-BOUND)
(TYPES::INT-LIST-EQUIV-PICK-A-POINT)
(TYPES::INT-LIST-EQUIV-PICK-A-POINT-REWRITE)
(TYPES::EQUAL-TYPE-IMPLIES-TYPE)
(TYPES::EQUAL-LEN-INT-LIST-FIX)
(TYPES::LEN-EQUIV-DEFINITION)
(TYPES::INT-LIST-EQUIV-DEFINITION
 (32 2 (:DEFINITION TYPES::INT-LIST-FIX$INLINE))
 (24 4 (:REWRITE TYPES::INT-LIST-FIX-WHEN-INT-LISTP))
 (20 20 (:TYPE-PRESCRIPTION TYPES::INT-LISTP))
 (20 4 (:DEFINITION IFIX))
 (16 4 (:REWRITE TYPES::INTEGERP-OF-CAR-WHEN-INT-LISTP))
 (16 1 (:DEFINITION TYPES::OPEN-INT-LIST-EQUIV))
 (11 1 (:DEFINITION INT-EQUIV$INLINE))
 (10 10 (:REWRITE TYPES::INT-LISTP-WHEN-NOT-CONSP))
 (8 2 (:REWRITE TYPES::INT-LISTP-OF-CDR-WHEN-INT-LISTP))
 (4 4 (:REWRITE DEFAULT-CDR))
 (4 4 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE OPEN-INT-LIST-FIX))
 )
(TYPES::EQUAL-IS-AN-EQUIVALENCE)
(TYPES::CANARY-LEMMA-INSTANCE)
(TYPES::INT-LIST-EQUIV-EQUAL-LEN-CONGRUENCE)
(TYPES::INT-LIST-EQUIV-LEN-EQUIV-REFINEMENT)
(TYPES::EQUAL-TYPE-IMPLIES-TYPE)
(TYPES::EQUAL-NAT-LIST-FIX-INT-LIST-FIX
 (100 5 (:REWRITE TYPES::INT-LIST-FIX-WHEN-INT-LISTP))
 (88 9 (:REWRITE TYPES::NAT-LIST-FIX-WHEN-NAT-LIST-P))
 (72 6 (:DEFINITION TYPES::INT-LISTP))
 (44 8 (:REWRITE TYPES::INT-LISTP-OF-CDR-WHEN-INT-LISTP))
 (33 24 (:REWRITE TYPES::EQUAL-TYPE-IMPLIES-TYPE))
 (22 12 (:REWRITE TYPES::NAT-LIST-P-WHEN-NOT-CONSP))
 (18 18 (:TYPE-PRESCRIPTION TYPES::INT-LIST-FIX$INLINE))
 (18 6 (:REWRITE TYPES::INTEGERP-OF-CAR-WHEN-INT-LISTP))
 (18 1 (:REWRITE TYPES::NAT-LIST-P-OF-CDR-WHEN-NAT-LIST-P))
 (16 15 (:REWRITE TYPES::INT-LISTP-WHEN-NOT-CONSP))
 (9 9 (:REWRITE DEFAULT-CDR))
 (9 9 (:REWRITE DEFAULT-CAR))
 (3 3 (:REWRITE-QUOTED-CONSTANT TYPES::NAT-LIST-FIX-UNDER-NAT-LIST-EQUIV))
 (3 3 (:REWRITE TYPES::CONSP-OF-INT-LIST-FIX))
 )
(TYPES::NAT-LIST-EQUIV-DEFINITION)
(TYPES::INT-LIST-EQUIV-DEFINITION
 (116 10 (:DEFINITION TYPES::INT-LISTP))
 (104 2 (:DEFINITION TYPES::INT-LIST-FIX$INLINE))
 (96 4 (:REWRITE TYPES::INT-LIST-FIX-WHEN-INT-LISTP))
 (78 14 (:REWRITE TYPES::INTEGERP-OF-CAR-WHEN-INT-LISTP))
 (74 74 (:TYPE-PRESCRIPTION TYPES::INT-LISTP))
 (64 4 (:DEFINITION IFIX))
 (52 12 (:REWRITE TYPES::INT-LISTP-OF-CDR-WHEN-INT-LISTP))
 (38 1 (:DEFINITION TYPES::OPEN-INT-LIST-EQUIV))
 (33 1 (:DEFINITION INT-EQUIV$INLINE))
 (22 22 (:REWRITE TYPES::INT-LISTP-WHEN-NOT-CONSP))
 (14 14 (:REWRITE DEFAULT-CDR))
 (14 14 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE OPEN-INT-LIST-FIX))
 )
(TYPES::EQUAL-IS-AN-EQUIVALENCE)
(TYPES::CANARY-LEMMA-INSTANCE)
(TYPES::INT-LIST-EQUIV-EQUAL-NAT-LIST-FIX-CONGRUENCE)
(TYPES::INT-LIST-EQUIV-NAT-LIST-EQUIV-REFINEMENT)