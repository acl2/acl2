(STD::DEFLIST-LOCAL-BOOLEANP-ELEMENT-THM)
(STD::DEFLIST-LOCAL-ELEMENTP-OF-NIL-THM)
(STR::BIN-DIGIT-CHAR-LIST-FIX$INLINE)
(STR::BIN-DIGIT-CHAR-LISTP-OF-BIN-DIGIT-CHAR-LIST-FIX
 (3 1 (:REWRITE STR::BIN-DIGIT-CHAR-FIX-WHEN-BIN-DIGIT-CHAR-P))
 (2 2 (:TYPE-PRESCRIPTION STR::BIN-DIGIT-CHAR-P$INLINE))
 )
(STR::BIN-DIGIT-CHAR-LIST-FIX-WHEN-BIN-DIGIT-CHAR-LISTP)
(STR::BIN-DIGIT-CHAR-LIST-FIX$INLINE)
(FTY::TMP-DEFFIXTYPE-IDEMPOTENT)
(STR::BIN-DIGIT-CHAR-LIST-EQUIV$INLINE)
(STR::BIN-DIGIT-CHAR-LIST-EQUIV-IS-AN-EQUIVALENCE)
(STR::BIN-DIGIT-CHAR-LIST-EQUIV-IMPLIES-EQUAL-BIN-DIGIT-CHAR-LIST-FIX-1)
(STR::BIN-DIGIT-CHAR-LIST-FIX-UNDER-BIN-DIGIT-CHAR-LIST-EQUIV)
(STR::EQUAL-OF-BIN-DIGIT-CHAR-LIST-FIX-1-FORWARD-TO-BIN-DIGIT-CHAR-LIST-EQUIV)
(STR::EQUAL-OF-BIN-DIGIT-CHAR-LIST-FIX-2-FORWARD-TO-BIN-DIGIT-CHAR-LIST-EQUIV)
(STR::BIN-DIGIT-CHAR-LIST-EQUIV-OF-BIN-DIGIT-CHAR-LIST-FIX-1-FORWARD)
(STR::BIN-DIGIT-CHAR-LIST-EQUIV-OF-BIN-DIGIT-CHAR-LIST-FIX-2-FORWARD)
(STR::CAR-OF-BIN-DIGIT-CHAR-LIST-FIX-X-UNDER-BIN-DIGIT-CHAR-EQUIV
 (9 3 (:REWRITE STR::BIN-DIGIT-CHAR-FIX-WHEN-BIN-DIGIT-CHAR-P))
 (6 6 (:TYPE-PRESCRIPTION STR::BIN-DIGIT-CHAR-P$INLINE))
 (6 2 (:REWRITE STR::BIN-DIGIT-CHAR-LIST-FIX-WHEN-BIN-DIGIT-CHAR-LISTP))
 (4 4 (:TYPE-PRESCRIPTION STR::BIN-DIGIT-CHAR-LISTP))
 (3 3 (:TYPE-PRESCRIPTION STR::BIN-DIGIT-CHAR-LIST-FIX$INLINE))
 )
(STR::CAR-BIN-DIGIT-CHAR-LIST-EQUIV-CONGRUENCE-ON-X-UNDER-BIN-DIGIT-CHAR-EQUIV)
(STR::CDR-OF-BIN-DIGIT-CHAR-LIST-FIX-X-UNDER-BIN-DIGIT-CHAR-LIST-EQUIV
 (3 1 (:REWRITE STR::BIN-DIGIT-CHAR-FIX-WHEN-BIN-DIGIT-CHAR-P))
 (2 2 (:TYPE-PRESCRIPTION STR::BIN-DIGIT-CHAR-P$INLINE))
 (2 2 (:REWRITE STR::BIN-DIGIT-CHAR-LISTP-WHEN-SUBSETP-EQUAL))
 )
(STR::CDR-BIN-DIGIT-CHAR-LIST-EQUIV-CONGRUENCE-ON-X-UNDER-BIN-DIGIT-CHAR-LIST-EQUIV)
(STR::CONS-OF-BIN-DIGIT-CHAR-FIX-X-UNDER-BIN-DIGIT-CHAR-LIST-EQUIV
 (10 4 (:REWRITE STR::BIN-DIGIT-CHAR-LIST-FIX-WHEN-BIN-DIGIT-CHAR-LISTP))
 (6 6 (:TYPE-PRESCRIPTION STR::BIN-DIGIT-CHAR-LISTP))
 )
(STR::CONS-BIN-DIGIT-CHAR-EQUIV-CONGRUENCE-ON-X-UNDER-BIN-DIGIT-CHAR-LIST-EQUIV)
(STR::CONS-OF-BIN-DIGIT-CHAR-LIST-FIX-Y-UNDER-BIN-DIGIT-CHAR-LIST-EQUIV
 (4 2 (:REWRITE STR::BIN-DIGIT-CHAR-FIX-WHEN-BIN-DIGIT-CHAR-P))
 (2 2 (:TYPE-PRESCRIPTION STR::BIN-DIGIT-CHAR-P$INLINE))
 )
(STR::CONS-BIN-DIGIT-CHAR-LIST-EQUIV-CONGRUENCE-ON-Y-UNDER-BIN-DIGIT-CHAR-LIST-EQUIV)
(STR::CONSP-OF-BIN-DIGIT-CHAR-LIST-FIX
 (6 2 (:REWRITE STR::BIN-DIGIT-CHAR-LIST-FIX-WHEN-BIN-DIGIT-CHAR-LISTP))
 (4 4 (:TYPE-PRESCRIPTION STR::BIN-DIGIT-CHAR-LISTP))
 (3 1 (:REWRITE STR::BIN-DIGIT-CHAR-FIX-WHEN-BIN-DIGIT-CHAR-P))
 (2 2 (:TYPE-PRESCRIPTION STR::BIN-DIGIT-CHAR-P$INLINE))
 )
(STR::BIN-DIGIT-CHAR-LIST-FIX-UNDER-IFF
 (6 2 (:REWRITE STR::BIN-DIGIT-CHAR-LIST-FIX-WHEN-BIN-DIGIT-CHAR-LISTP))
 (4 4 (:TYPE-PRESCRIPTION STR::BIN-DIGIT-CHAR-LISTP))
 (3 1 (:REWRITE STR::BIN-DIGIT-CHAR-FIX-WHEN-BIN-DIGIT-CHAR-P))
 (2 2 (:TYPE-PRESCRIPTION STR::BIN-DIGIT-CHAR-P$INLINE))
 )
(STR::BIN-DIGIT-CHAR-LIST-FIX-OF-CONS
 (7 3 (:REWRITE STR::BIN-DIGIT-CHAR-LIST-FIX-WHEN-BIN-DIGIT-CHAR-LISTP))
 (4 4 (:TYPE-PRESCRIPTION STR::BIN-DIGIT-CHAR-LISTP))
 (4 2 (:REWRITE STR::BIN-DIGIT-CHAR-FIX-WHEN-BIN-DIGIT-CHAR-P))
 (2 2 (:TYPE-PRESCRIPTION STR::BIN-DIGIT-CHAR-P$INLINE))
 )
(STR::LEN-OF-BIN-DIGIT-CHAR-LIST-FIX
 (12 4 (:REWRITE STR::BIN-DIGIT-CHAR-LIST-FIX-WHEN-BIN-DIGIT-CHAR-LISTP))
 (8 8 (:TYPE-PRESCRIPTION STR::BIN-DIGIT-CHAR-LISTP))
 (3 1 (:REWRITE STR::BIN-DIGIT-CHAR-FIX-WHEN-BIN-DIGIT-CHAR-P))
 (2 2 (:TYPE-PRESCRIPTION STR::BIN-DIGIT-CHAR-P$INLINE))
 (1 1 (:REWRITE FTY::EQUAL-OF-LEN))
 )
(STR::BIN-DIGIT-CHAR-LIST-FIX-OF-APPEND
 (28 10 (:REWRITE STR::BIN-DIGIT-CHAR-LIST-FIX-WHEN-BIN-DIGIT-CHAR-LISTP))
 (18 18 (:TYPE-PRESCRIPTION STR::BIN-DIGIT-CHAR-LISTP))
 (4 2 (:REWRITE STR::BIN-DIGIT-CHAR-FIX-WHEN-BIN-DIGIT-CHAR-P))
 (2 2 (:TYPE-PRESCRIPTION STR::BIN-DIGIT-CHAR-P$INLINE))
 )
(STR::BIN-DIGIT-CHAR-LIST-FIX-OF-REPEAT
 (10 4 (:REWRITE STR::BIN-DIGIT-CHAR-FIX-WHEN-BIN-DIGIT-CHAR-P))
 (6 6 (:TYPE-PRESCRIPTION STR::BIN-DIGIT-CHAR-P$INLINE))
 (6 2 (:REWRITE STR::BIN-DIGIT-CHAR-LIST-FIX-WHEN-BIN-DIGIT-CHAR-LISTP))
 (4 4 (:TYPE-PRESCRIPTION STR::BIN-DIGIT-CHAR-LISTP))
 (1 1 (:REWRITE-QUOTED-CONSTANT STR::BIN-DIGIT-CHAR-LIST-FIX-UNDER-BIN-DIGIT-CHAR-LIST-EQUIV))
 )
(STR::LIST-EQUIV-REFINES-BIN-DIGIT-CHAR-LIST-EQUIV
 (42 14 (:REWRITE STR::BIN-DIGIT-CHAR-LIST-FIX-WHEN-BIN-DIGIT-CHAR-LISTP))
 (28 28 (:TYPE-PRESCRIPTION STR::BIN-DIGIT-CHAR-LISTP))
 (24 8 (:REWRITE STR::BIN-DIGIT-CHAR-FIX-WHEN-BIN-DIGIT-CHAR-P))
 (16 16 (:TYPE-PRESCRIPTION STR::BIN-DIGIT-CHAR-P$INLINE))
 (1 1 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 )
(STR::NTH-OF-BIN-DIGIT-CHAR-LIST-FIX
 (75 25 (:REWRITE STR::BIN-DIGIT-CHAR-FIX-WHEN-BIN-DIGIT-CHAR-P))
 (60 20 (:REWRITE STR::BIN-DIGIT-CHAR-LIST-FIX-WHEN-BIN-DIGIT-CHAR-LISTP))
 (50 50 (:TYPE-PRESCRIPTION STR::BIN-DIGIT-CHAR-P$INLINE))
 (40 40 (:TYPE-PRESCRIPTION STR::BIN-DIGIT-CHAR-LISTP))
 )
(STR::BIN-DIGIT-CHAR-LIST-EQUIV-IMPLIES-BIN-DIGIT-CHAR-LIST-EQUIV-APPEND-1
 (88 32 (:REWRITE STR::BIN-DIGIT-CHAR-LIST-FIX-WHEN-BIN-DIGIT-CHAR-LISTP))
 (56 56 (:TYPE-PRESCRIPTION STR::BIN-DIGIT-CHAR-LISTP))
 (51 17 (:REWRITE STR::BIN-DIGIT-CHAR-FIX-WHEN-BIN-DIGIT-CHAR-P))
 (34 34 (:TYPE-PRESCRIPTION STR::BIN-DIGIT-CHAR-P$INLINE))
 (1 1 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 )
(STR::BIN-DIGIT-CHAR-LIST-EQUIV-IMPLIES-BIN-DIGIT-CHAR-LIST-EQUIV-APPEND-2
 (118 46 (:REWRITE STR::BIN-DIGIT-CHAR-LIST-FIX-WHEN-BIN-DIGIT-CHAR-LISTP))
 (78 26 (:REWRITE STR::BIN-DIGIT-CHAR-FIX-WHEN-BIN-DIGIT-CHAR-P))
 (72 72 (:TYPE-PRESCRIPTION STR::BIN-DIGIT-CHAR-LISTP))
 (52 52 (:TYPE-PRESCRIPTION STR::BIN-DIGIT-CHAR-P$INLINE))
 (4 4 (:REWRITE STR::CONSP-OF-BIN-DIGIT-CHAR-LIST-FIX))
 )
(STR::BIN-DIGIT-CHAR-LIST-EQUIV-IMPLIES-BIN-DIGIT-CHAR-LIST-EQUIV-NTHCDR-2
 (115 39 (:REWRITE STR::BIN-DIGIT-CHAR-LIST-FIX-WHEN-BIN-DIGIT-CHAR-LISTP))
 (76 76 (:TYPE-PRESCRIPTION STR::BIN-DIGIT-CHAR-LISTP))
 (66 22 (:REWRITE STR::BIN-DIGIT-CHAR-FIX-WHEN-BIN-DIGIT-CHAR-P))
 (44 44 (:TYPE-PRESCRIPTION STR::BIN-DIGIT-CHAR-P$INLINE))
 )
(STR::BIN-DIGIT-CHAR-LIST-EQUIV-IMPLIES-BIN-DIGIT-CHAR-LIST-EQUIV-TAKE-2
 (112 38 (:REWRITE STR::BIN-DIGIT-CHAR-LIST-FIX-WHEN-BIN-DIGIT-CHAR-LISTP))
 (82 28 (:REWRITE STR::BIN-DIGIT-CHAR-FIX-WHEN-BIN-DIGIT-CHAR-P))
 (74 74 (:TYPE-PRESCRIPTION STR::BIN-DIGIT-CHAR-LISTP))
 (54 54 (:TYPE-PRESCRIPTION STR::BIN-DIGIT-CHAR-P$INLINE))
 (6 6 (:REWRITE-QUOTED-CONSTANT STR::BIN-DIGIT-CHAR-LIST-FIX-UNDER-BIN-DIGIT-CHAR-LIST-EQUIV))
 (1 1 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 )
