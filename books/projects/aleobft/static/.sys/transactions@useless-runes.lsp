(TMP-DEFTYPES-ANY-P$INLINE-OF-IDENTITY)
(TMP-DEFTYPES-IDENTITY-WHEN-ANY-P$INLINE
 (3 3 (:TYPE-PRESCRIPTION IDENTITY))
 )
(ALEOBFT-STATIC::TRANSACTIONP
 (44 9 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 (14 14 (:REWRITE CAR-WHEN-ALL-EQUALP))
 (10 10 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (10 10 (:REWRITE CONSP-BY-LEN))
 (4 2 (:REWRITE FTY::STRIP-CARS-UNDER-IFF))
 )
(ALEOBFT-STATIC::CONSP-WHEN-TRANSACTIONP)
(ALEOBFT-STATIC::TRANSACTION-FIX$INLINE
 (6 6 (:TYPE-PRESCRIPTION IDENTITY))
 )
(ALEOBFT-STATIC::TRANSACTIONP-OF-TRANSACTION-FIX)
(ALEOBFT-STATIC::TRANSACTION-FIX-WHEN-TRANSACTIONP
 (6 3 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 (1 1 (:DEFINITION STRIP-CARS))
 (1 1 (:DEFINITION ALISTP))
 )
(ALEOBFT-STATIC::TRANSACTION-FIX$INLINE
 (6 6 (:TYPE-PRESCRIPTION IDENTITY))
 (6 3 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 (1 1 (:DEFINITION STRIP-CARS))
 (1 1 (:DEFINITION ALISTP))
 )
(FTY::TMP-DEFFIXTYPE-IDEMPOTENT)
(ALEOBFT-STATIC::TRANSACTION-EQUIV$INLINE)
(ALEOBFT-STATIC::TRANSACTION-EQUIV-IS-AN-EQUIVALENCE)
(ALEOBFT-STATIC::TRANSACTION-EQUIV-IMPLIES-EQUAL-TRANSACTION-FIX-1)
(ALEOBFT-STATIC::TRANSACTION-FIX-UNDER-TRANSACTION-EQUIV)
(ALEOBFT-STATIC::EQUAL-OF-TRANSACTION-FIX-1-FORWARD-TO-TRANSACTION-EQUIV)
(ALEOBFT-STATIC::EQUAL-OF-TRANSACTION-FIX-2-FORWARD-TO-TRANSACTION-EQUIV)
(ALEOBFT-STATIC::TRANSACTION-EQUIV-OF-TRANSACTION-FIX-1-FORWARD)
(ALEOBFT-STATIC::TRANSACTION-EQUIV-OF-TRANSACTION-FIX-2-FORWARD)
(ALEOBFT-STATIC::TRANSACTION->UNWRAP$INLINE
 (7 7 (:TYPE-PRESCRIPTION IDENTITY))
 (5 2 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 (1 1 (:DEFINITION STRIP-CARS))
 )
(ALEOBFT-STATIC::ANY-P-OF-TRANSACTION->UNWRAP)
(ALEOBFT-STATIC::TRANSACTION->UNWRAP$INLINE-OF-TRANSACTION-FIX-X
 (9 3 (:REWRITE ALEOBFT-STATIC::TRANSACTION-FIX-WHEN-TRANSACTIONP))
 (6 6 (:TYPE-PRESCRIPTION ALEOBFT-STATIC::TRANSACTIONP))
 )
(ALEOBFT-STATIC::TRANSACTION->UNWRAP$INLINE-TRANSACTION-EQUIV-CONGRUENCE-ON-X)
(ALEOBFT-STATIC::TRANSACTION)
(ALEOBFT-STATIC::TRANSACTIONP-OF-TRANSACTION)
(ALEOBFT-STATIC::TRANSACTION->UNWRAP-OF-TRANSACTION
 (3 3 (:TYPE-PRESCRIPTION IDENTITY))
 )
(ALEOBFT-STATIC::TRANSACTION-OF-FIELDS
 (3 1 (:REWRITE ALEOBFT-STATIC::TRANSACTION-FIX-WHEN-TRANSACTIONP))
 (2 2 (:TYPE-PRESCRIPTION ALEOBFT-STATIC::TRANSACTIONP))
 )
(ALEOBFT-STATIC::TRANSACTION-FIX-WHEN-TRANSACTION
 (3 1 (:REWRITE ALEOBFT-STATIC::TRANSACTION-FIX-WHEN-TRANSACTIONP))
 (2 2 (:TYPE-PRESCRIPTION ALEOBFT-STATIC::TRANSACTIONP))
 )
(ALEOBFT-STATIC::EQUAL-OF-TRANSACTION)
(ALEOBFT-STATIC::TRANSACTION-OF-IDENTITY-UNWRAP)
(ALEOBFT-STATIC::TRANSACTION-EQUAL-CONGRUENCE-ON-UNWRAP)
(ALEOBFT-STATIC::TRANSACTION-FIX-REDEF)
(ALEOBFT-STATIC::TRANSACTION-LISTP)
(STD::DEFLIST-LOCAL-BOOLEANP-ELEMENT-THM)
(STD::DEFLIST-LOCAL-ELEMENTP-OF-NIL-THM)
(ALEOBFT-STATIC::TRANSACTION-LISTP-OF-CONS)
(ALEOBFT-STATIC::TRANSACTION-LISTP-OF-CDR-WHEN-TRANSACTION-LISTP)
(ALEOBFT-STATIC::TRANSACTION-LISTP-WHEN-NOT-CONSP)
(ALEOBFT-STATIC::TRANSACTIONP-OF-CAR-WHEN-TRANSACTION-LISTP)
(ALEOBFT-STATIC::TRUE-LISTP-WHEN-TRANSACTION-LISTP-COMPOUND-RECOGNIZER)
(ALEOBFT-STATIC::TRANSACTION-LISTP-OF-LIST-FIX)
(ALEOBFT-STATIC::TRANSACTION-LISTP-OF-REV)
(ALEOBFT-STATIC::TRANSACTION-LISTP-OF-APPEND)
(ALEOBFT-STATIC::TRANSACTION-LISTP-OF-LAST)
(ALEOBFT-STATIC::TRANSACTIONP-OF-NTH-WHEN-TRANSACTION-LISTP)
(ALEOBFT-STATIC::TRANSACTION-LISTP-OF-NTHCDR)
(ALEOBFT-STATIC::TRANSACTION-LISTP-OF-REMOVE)
(ALEOBFT-STATIC::TRANSACTION-LISTP-OF-REPEAT)
(ALEOBFT-STATIC::TRANSACTION-LISTP-OF-REVAPPEND)
(ALEOBFT-STATIC::TRANSACTION-LISTP-OF-RCONS)
(ALEOBFT-STATIC::TRANSACTIONP-WHEN-MEMBER-EQUAL-OF-TRANSACTION-LISTP)
(ALEOBFT-STATIC::TRANSACTION-LISTP-WHEN-SUBSETP-EQUAL)
(ALEOBFT-STATIC::TRANSACTION-LISTP-OF-SET-DIFFERENCE-EQUAL)
(ALEOBFT-STATIC::TRANSACTION-LISTP-OF-INTERSECTION-EQUAL-1)
(ALEOBFT-STATIC::TRANSACTION-LISTP-OF-INTERSECTION-EQUAL-2)
(ALEOBFT-STATIC::TRANSACTION-LISTP-OF-UNION-EQUAL)
(ALEOBFT-STATIC::TRANSACTION-LISTP-OF-TAKE)
(ALEOBFT-STATIC::TRANSACTION-LISTP-OF-UPDATE-NTH)
(ALEOBFT-STATIC::TRANSACTION-LIST-FIX$INLINE)
(ALEOBFT-STATIC::TRANSACTION-LISTP-OF-TRANSACTION-LIST-FIX
 (30 1 (:REWRITE ALEOBFT-STATIC::TRANSACTION-FIX-WHEN-TRANSACTIONP))
 (22 2 (:REWRITE ALEOBFT-STATIC::TRANSACTIONP-OF-CAR-WHEN-TRANSACTION-LISTP))
 (18 10 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LISTP-WHEN-SUBSETP-EQUAL))
 (15 1 (:DEFINITION ALEOBFT-STATIC::TRANSACTION-LISTP))
 (12 6 (:REWRITE ALEOBFT-STATIC::TRANSACTIONP-WHEN-MEMBER-EQUAL-OF-TRANSACTION-LISTP))
 (12 5 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LISTP-WHEN-NOT-CONSP))
 (8 8 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (4 4 (:TYPE-PRESCRIPTION ALEOBFT-STATIC::TRANSACTIONP))
 (4 4 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (2 2 (:REWRITE FTY::OPEN-MEMBER-EQUAL-ON-LIST-OF-TAGS))
 (2 1 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LISTP-OF-CDR-WHEN-TRANSACTION-LISTP))
 )
(ALEOBFT-STATIC::TRANSACTION-LIST-FIX-WHEN-TRANSACTION-LISTP
 (32 4 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LISTP-OF-CDR-WHEN-TRANSACTION-LISTP))
 (28 24 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LISTP-WHEN-SUBSETP-EQUAL))
 (13 3 (:REWRITE ALEOBFT-STATIC::TRANSACTIONP-OF-CAR-WHEN-TRANSACTION-LISTP))
 (9 6 (:REWRITE ALEOBFT-STATIC::TRANSACTIONP-WHEN-MEMBER-EQUAL-OF-TRANSACTION-LISTP))
 (4 4 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (2 2 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (1 1 (:REWRITE FTY::OPEN-MEMBER-EQUAL-ON-LIST-OF-TAGS))
 )
(ALEOBFT-STATIC::TRANSACTION-LIST-FIX$INLINE
 (8 8 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LISTP-WHEN-SUBSETP-EQUAL))
 (6 1 (:REWRITE ALEOBFT-STATIC::TRANSACTIONP-OF-CAR-WHEN-TRANSACTION-LISTP))
 (6 1 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LISTP-OF-CDR-WHEN-TRANSACTION-LISTP))
 (4 4 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LISTP-WHEN-NOT-CONSP))
 (2 2 (:REWRITE ALEOBFT-STATIC::TRANSACTIONP-WHEN-MEMBER-EQUAL-OF-TRANSACTION-LISTP))
 )
(FTY::TMP-DEFFIXTYPE-IDEMPOTENT
 (2 2 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LISTP-WHEN-SUBSETP-EQUAL))
 (1 1 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LISTP-WHEN-NOT-CONSP))
 )
(ALEOBFT-STATIC::TRANSACTION-LIST-EQUIV$INLINE)
(ALEOBFT-STATIC::TRANSACTION-LIST-EQUIV-IS-AN-EQUIVALENCE)
(ALEOBFT-STATIC::TRANSACTION-LIST-EQUIV-IMPLIES-EQUAL-TRANSACTION-LIST-FIX-1)
(ALEOBFT-STATIC::TRANSACTION-LIST-FIX-UNDER-TRANSACTION-LIST-EQUIV)
(ALEOBFT-STATIC::EQUAL-OF-TRANSACTION-LIST-FIX-1-FORWARD-TO-TRANSACTION-LIST-EQUIV)
(ALEOBFT-STATIC::EQUAL-OF-TRANSACTION-LIST-FIX-2-FORWARD-TO-TRANSACTION-LIST-EQUIV)
(ALEOBFT-STATIC::TRANSACTION-LIST-EQUIV-OF-TRANSACTION-LIST-FIX-1-FORWARD)
(ALEOBFT-STATIC::TRANSACTION-LIST-EQUIV-OF-TRANSACTION-LIST-FIX-2-FORWARD)
(ALEOBFT-STATIC::CAR-OF-TRANSACTION-LIST-FIX-X-UNDER-TRANSACTION-EQUIV
 (33 3 (:REWRITE ALEOBFT-STATIC::TRANSACTION-FIX-WHEN-TRANSACTIONP))
 (18 3 (:REWRITE ALEOBFT-STATIC::TRANSACTIONP-OF-CAR-WHEN-TRANSACTION-LISTP))
 (18 2 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LIST-FIX-WHEN-TRANSACTION-LISTP))
 (12 12 (:TYPE-PRESCRIPTION ALEOBFT-STATIC::TRANSACTION-LISTP))
 (12 12 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LISTP-WHEN-SUBSETP-EQUAL))
 (6 6 (:TYPE-PRESCRIPTION ALEOBFT-STATIC::TRANSACTIONP))
 (6 6 (:REWRITE ALEOBFT-STATIC::TRANSACTIONP-WHEN-MEMBER-EQUAL-OF-TRANSACTION-LISTP))
 (6 6 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LISTP-WHEN-NOT-CONSP))
 (6 1 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LISTP-OF-CDR-WHEN-TRANSACTION-LISTP))
 (3 3 (:TYPE-PRESCRIPTION ALEOBFT-STATIC::TRANSACTION-LIST-FIX$INLINE))
 )
(ALEOBFT-STATIC::CAR-TRANSACTION-LIST-EQUIV-CONGRUENCE-ON-X-UNDER-TRANSACTION-EQUIV)
(ALEOBFT-STATIC::CDR-OF-TRANSACTION-LIST-FIX-X-UNDER-TRANSACTION-LIST-EQUIV
 (41 3 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LISTP-OF-CDR-WHEN-TRANSACTION-LISTP))
 (22 2 (:REWRITE ALEOBFT-STATIC::TRANSACTION-FIX-WHEN-TRANSACTIONP))
 (20 20 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LISTP-WHEN-SUBSETP-EQUAL))
 (12 2 (:REWRITE ALEOBFT-STATIC::TRANSACTIONP-OF-CAR-WHEN-TRANSACTION-LISTP))
 (4 4 (:TYPE-PRESCRIPTION ALEOBFT-STATIC::TRANSACTIONP))
 (4 4 (:REWRITE ALEOBFT-STATIC::TRANSACTIONP-WHEN-MEMBER-EQUAL-OF-TRANSACTION-LISTP))
 )
(ALEOBFT-STATIC::CDR-TRANSACTION-LIST-EQUIV-CONGRUENCE-ON-X-UNDER-TRANSACTION-LIST-EQUIV)
(ALEOBFT-STATIC::CONS-OF-TRANSACTION-FIX-X-UNDER-TRANSACTION-LIST-EQUIV
 (34 4 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LIST-FIX-WHEN-TRANSACTION-LISTP))
 (17 2 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LISTP-OF-CONS))
 (10 10 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LISTP-WHEN-SUBSETP-EQUAL))
 (8 8 (:REWRITE ALEOBFT-STATIC::TRANSACTIONP-WHEN-MEMBER-EQUAL-OF-TRANSACTION-LISTP))
 (6 6 (:TYPE-PRESCRIPTION ALEOBFT-STATIC::TRANSACTION-LISTP))
 (5 5 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LISTP-WHEN-NOT-CONSP))
 )
(ALEOBFT-STATIC::CONS-TRANSACTION-EQUIV-CONGRUENCE-ON-X-UNDER-TRANSACTION-LIST-EQUIV)
(ALEOBFT-STATIC::CONS-OF-TRANSACTION-LIST-FIX-Y-UNDER-TRANSACTION-LIST-EQUIV
 (20 2 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LISTP-OF-CONS))
 (8 8 (:TYPE-PRESCRIPTION ALEOBFT-STATIC::TRANSACTIONP))
 (8 8 (:REWRITE ALEOBFT-STATIC::TRANSACTIONP-WHEN-MEMBER-EQUAL-OF-TRANSACTION-LISTP))
 (8 8 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LISTP-WHEN-SUBSETP-EQUAL))
 (6 2 (:REWRITE ALEOBFT-STATIC::TRANSACTION-FIX-WHEN-TRANSACTIONP))
 (5 4 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LISTP-WHEN-NOT-CONSP))
 )
(ALEOBFT-STATIC::CONS-TRANSACTION-LIST-EQUIV-CONGRUENCE-ON-Y-UNDER-TRANSACTION-LIST-EQUIV)
(ALEOBFT-STATIC::CONSP-OF-TRANSACTION-LIST-FIX
 (18 2 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LIST-FIX-WHEN-TRANSACTION-LISTP))
 (11 1 (:REWRITE ALEOBFT-STATIC::TRANSACTION-FIX-WHEN-TRANSACTIONP))
 (8 8 (:TYPE-PRESCRIPTION ALEOBFT-STATIC::TRANSACTION-LISTP))
 (8 8 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LISTP-WHEN-SUBSETP-EQUAL))
 (6 1 (:REWRITE ALEOBFT-STATIC::TRANSACTIONP-OF-CAR-WHEN-TRANSACTION-LISTP))
 (6 1 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LISTP-OF-CDR-WHEN-TRANSACTION-LISTP))
 (4 4 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LISTP-WHEN-NOT-CONSP))
 (2 2 (:TYPE-PRESCRIPTION ALEOBFT-STATIC::TRANSACTIONP))
 (2 2 (:REWRITE ALEOBFT-STATIC::TRANSACTIONP-WHEN-MEMBER-EQUAL-OF-TRANSACTION-LISTP))
 )
(ALEOBFT-STATIC::TRANSACTION-LIST-FIX-UNDER-IFF
 (18 2 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LIST-FIX-WHEN-TRANSACTION-LISTP))
 (11 1 (:REWRITE ALEOBFT-STATIC::TRANSACTION-FIX-WHEN-TRANSACTIONP))
 (8 8 (:TYPE-PRESCRIPTION ALEOBFT-STATIC::TRANSACTION-LISTP))
 (8 8 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LISTP-WHEN-SUBSETP-EQUAL))
 (6 1 (:REWRITE ALEOBFT-STATIC::TRANSACTIONP-OF-CAR-WHEN-TRANSACTION-LISTP))
 (6 1 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LISTP-OF-CDR-WHEN-TRANSACTION-LISTP))
 (4 4 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LISTP-WHEN-NOT-CONSP))
 (2 2 (:TYPE-PRESCRIPTION ALEOBFT-STATIC::TRANSACTIONP))
 (2 2 (:REWRITE ALEOBFT-STATIC::TRANSACTIONP-WHEN-MEMBER-EQUAL-OF-TRANSACTION-LISTP))
 )
(ALEOBFT-STATIC::TRANSACTION-LIST-FIX-OF-CONS
 (21 3 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LIST-FIX-WHEN-TRANSACTION-LISTP))
 (9 1 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LISTP-OF-CONS))
 (6 6 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LISTP-WHEN-SUBSETP-EQUAL))
 (6 2 (:REWRITE ALEOBFT-STATIC::TRANSACTION-FIX-WHEN-TRANSACTIONP))
 (4 4 (:TYPE-PRESCRIPTION ALEOBFT-STATIC::TRANSACTIONP))
 (4 4 (:TYPE-PRESCRIPTION ALEOBFT-STATIC::TRANSACTION-LISTP))
 (4 4 (:REWRITE ALEOBFT-STATIC::TRANSACTIONP-WHEN-MEMBER-EQUAL-OF-TRANSACTION-LISTP))
 (3 3 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LISTP-WHEN-NOT-CONSP))
 )
(ALEOBFT-STATIC::LEN-OF-TRANSACTION-LIST-FIX
 (35 4 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LIST-FIX-WHEN-TRANSACTION-LISTP))
 (14 14 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LISTP-WHEN-SUBSETP-EQUAL))
 (13 13 (:TYPE-PRESCRIPTION ALEOBFT-STATIC::TRANSACTION-LISTP))
 (12 2 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LISTP-OF-CDR-WHEN-TRANSACTION-LISTP))
 (11 1 (:REWRITE ALEOBFT-STATIC::TRANSACTION-FIX-WHEN-TRANSACTIONP))
 (7 7 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LISTP-WHEN-NOT-CONSP))
 (6 1 (:REWRITE ALEOBFT-STATIC::TRANSACTIONP-OF-CAR-WHEN-TRANSACTION-LISTP))
 (2 2 (:TYPE-PRESCRIPTION ALEOBFT-STATIC::TRANSACTIONP))
 (2 2 (:REWRITE ALEOBFT-STATIC::TRANSACTIONP-WHEN-MEMBER-EQUAL-OF-TRANSACTION-LISTP))
 (1 1 (:REWRITE FTY::EQUAL-OF-LEN))
 )
(ALEOBFT-STATIC::TRANSACTION-LIST-FIX-OF-APPEND
 (114 10 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LIST-FIX-WHEN-TRANSACTION-LISTP))
 (58 2 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LISTP-OF-APPEND))
 (40 36 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LISTP-WHEN-SUBSETP-EQUAL))
 (29 29 (:TYPE-PRESCRIPTION ALEOBFT-STATIC::TRANSACTION-LISTP))
 (24 2 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LISTP-OF-LIST-FIX))
 (22 16 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LISTP-WHEN-NOT-CONSP))
 (14 4 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LISTP-OF-CDR-WHEN-TRANSACTION-LISTP))
 (12 12 (:TYPE-PRESCRIPTION TRUE-LIST-FIX))
 (12 2 (:REWRITE ALEOBFT-STATIC::TRANSACTION-FIX-WHEN-TRANSACTIONP))
 (6 1 (:REWRITE ALEOBFT-STATIC::TRANSACTIONP-OF-CAR-WHEN-TRANSACTION-LISTP))
 (4 4 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (2 2 (:TYPE-PRESCRIPTION ALEOBFT-STATIC::TRANSACTIONP))
 (2 2 (:REWRITE ALEOBFT-STATIC::TRANSACTIONP-WHEN-MEMBER-EQUAL-OF-TRANSACTION-LISTP))
 )
(ALEOBFT-STATIC::TRANSACTION-LIST-FIX-OF-REPEAT
 (24 2 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LIST-FIX-WHEN-TRANSACTION-LISTP))
 (16 4 (:REWRITE ALEOBFT-STATIC::TRANSACTION-FIX-WHEN-TRANSACTIONP))
 (12 2 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LISTP-OF-REPEAT))
 (10 10 (:TYPE-PRESCRIPTION ALEOBFT-STATIC::TRANSACTIONP))
 (10 10 (:REWRITE ALEOBFT-STATIC::TRANSACTIONP-WHEN-MEMBER-EQUAL-OF-TRANSACTION-LISTP))
 (4 4 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LISTP-WHEN-SUBSETP-EQUAL))
 (2 2 (:TYPE-PRESCRIPTION ALEOBFT-STATIC::TRANSACTION-LISTP))
 (1 1 (:REWRITE-QUOTED-CONSTANT ALEOBFT-STATIC::TRANSACTION-LIST-FIX-UNDER-TRANSACTION-LIST-EQUIV))
 )
(ALEOBFT-STATIC::LIST-EQUIV-REFINES-TRANSACTION-LIST-EQUIV
 (146 14 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LIST-FIX-WHEN-TRANSACTION-LISTP))
 (112 8 (:REWRITE ALEOBFT-STATIC::TRANSACTION-FIX-WHEN-TRANSACTIONP))
 (88 18 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LISTP-OF-CDR-WHEN-TRANSACTION-LISTP))
 (72 72 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LISTP-WHEN-SUBSETP-EQUAL))
 (72 8 (:REWRITE ALEOBFT-STATIC::TRANSACTIONP-OF-CAR-WHEN-TRANSACTION-LISTP))
 (70 70 (:TYPE-PRESCRIPTION ALEOBFT-STATIC::TRANSACTION-LISTP))
 (36 36 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LISTP-WHEN-NOT-CONSP))
 (16 16 (:TYPE-PRESCRIPTION ALEOBFT-STATIC::TRANSACTIONP))
 (16 16 (:REWRITE ALEOBFT-STATIC::TRANSACTIONP-WHEN-MEMBER-EQUAL-OF-TRANSACTION-LISTP))
 (1 1 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 )
(ALEOBFT-STATIC::NTH-OF-TRANSACTION-LIST-FIX
 (253 25 (:REWRITE ALEOBFT-STATIC::TRANSACTION-FIX-WHEN-TRANSACTIONP))
 (166 23 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LIST-FIX-WHEN-TRANSACTION-LISTP))
 (98 98 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LISTP-WHEN-SUBSETP-EQUAL))
 (93 93 (:TYPE-PRESCRIPTION ALEOBFT-STATIC::TRANSACTION-LISTP))
 (80 15 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LISTP-OF-CDR-WHEN-TRANSACTION-LISTP))
 (74 7 (:REWRITE ALEOBFT-STATIC::TRANSACTIONP-OF-NTH-WHEN-TRANSACTION-LISTP))
 (54 9 (:REWRITE ALEOBFT-STATIC::TRANSACTIONP-OF-CAR-WHEN-TRANSACTION-LISTP))
 (50 50 (:TYPE-PRESCRIPTION ALEOBFT-STATIC::TRANSACTIONP))
 (50 50 (:REWRITE ALEOBFT-STATIC::TRANSACTIONP-WHEN-MEMBER-EQUAL-OF-TRANSACTION-LISTP))
 (49 49 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LISTP-WHEN-NOT-CONSP))
 (2 2 (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
 (2 2 (:LINEAR LISTPOS-UPPER-BOUND-STRONG-2))
 (2 2 (:LINEAR LEN-WHEN-PREFIXP))
 (1 1 (:LINEAR INDEX-OF-<-LEN))
 )
(ALEOBFT-STATIC::TRANSACTION-LIST-EQUIV-IMPLIES-TRANSACTION-LIST-EQUIV-APPEND-1
 (269 32 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LIST-FIX-WHEN-TRANSACTION-LISTP))
 (205 17 (:REWRITE ALEOBFT-STATIC::TRANSACTION-FIX-WHEN-TRANSACTIONP))
 (128 128 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LISTP-WHEN-SUBSETP-EQUAL))
 (126 126 (:TYPE-PRESCRIPTION ALEOBFT-STATIC::TRANSACTION-LISTP))
 (120 17 (:REWRITE ALEOBFT-STATIC::TRANSACTIONP-OF-CAR-WHEN-TRANSACTION-LISTP))
 (117 22 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LISTP-OF-CDR-WHEN-TRANSACTION-LISTP))
 (64 64 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LISTP-WHEN-NOT-CONSP))
 (34 34 (:TYPE-PRESCRIPTION ALEOBFT-STATIC::TRANSACTIONP))
 (34 34 (:REWRITE ALEOBFT-STATIC::TRANSACTIONP-WHEN-MEMBER-EQUAL-OF-TRANSACTION-LISTP))
 (1 1 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 )
(ALEOBFT-STATIC::TRANSACTION-LIST-EQUIV-IMPLIES-TRANSACTION-LIST-EQUIV-APPEND-2
 (393 46 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LIST-FIX-WHEN-TRANSACTION-LISTP))
 (322 26 (:REWRITE ALEOBFT-STATIC::TRANSACTION-FIX-WHEN-TRANSACTIONP))
 (204 39 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LISTP-OF-CDR-WHEN-TRANSACTION-LISTP))
 (192 26 (:REWRITE ALEOBFT-STATIC::TRANSACTIONP-OF-CAR-WHEN-TRANSACTION-LISTP))
 (190 190 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LISTP-WHEN-SUBSETP-EQUAL))
 (189 189 (:TYPE-PRESCRIPTION ALEOBFT-STATIC::TRANSACTION-LISTP))
 (95 95 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LISTP-WHEN-NOT-CONSP))
 (52 52 (:TYPE-PRESCRIPTION ALEOBFT-STATIC::TRANSACTIONP))
 (52 52 (:REWRITE ALEOBFT-STATIC::TRANSACTIONP-WHEN-MEMBER-EQUAL-OF-TRANSACTION-LISTP))
 (4 4 (:REWRITE ALEOBFT-STATIC::CONSP-OF-TRANSACTION-LIST-FIX))
 )
(ALEOBFT-STATIC::TRANSACTION-LIST-EQUIV-IMPLIES-TRANSACTION-LIST-EQUIV-NTHCDR-2
 (298 20 (:REWRITE ALEOBFT-STATIC::TRANSACTION-FIX-WHEN-TRANSACTIONP))
 (208 39 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LISTP-OF-CDR-WHEN-TRANSACTION-LISTP))
 (206 206 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LISTP-WHEN-SUBSETP-EQUAL))
 (198 20 (:REWRITE ALEOBFT-STATIC::TRANSACTIONP-OF-CAR-WHEN-TRANSACTION-LISTP))
 (40 40 (:TYPE-PRESCRIPTION ALEOBFT-STATIC::TRANSACTIONP))
 (40 40 (:REWRITE ALEOBFT-STATIC::TRANSACTIONP-WHEN-MEMBER-EQUAL-OF-TRANSACTION-LISTP))
 )
(ALEOBFT-STATIC::TRANSACTION-LIST-EQUIV-IMPLIES-TRANSACTION-LIST-EQUIV-TAKE-2
 (545 38 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LIST-FIX-WHEN-TRANSACTION-LISTP))
 (428 28 (:REWRITE ALEOBFT-STATIC::TRANSACTION-FIX-WHEN-TRANSACTIONP))
 (300 51 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LISTP-OF-CDR-WHEN-TRANSACTION-LISTP))
 (292 26 (:REWRITE ALEOBFT-STATIC::TRANSACTIONP-OF-CAR-WHEN-TRANSACTION-LISTP))
 (236 236 (:TYPE-PRESCRIPTION ALEOBFT-STATIC::TRANSACTION-LISTP))
 (236 236 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LISTP-WHEN-SUBSETP-EQUAL))
 (217 24 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LISTP-OF-TAKE))
 (136 118 (:REWRITE ALEOBFT-STATIC::TRANSACTION-LISTP-WHEN-NOT-CONSP))
 (66 66 (:TYPE-PRESCRIPTION ALEOBFT-STATIC::TRANSACTIONP))
 (66 66 (:REWRITE ALEOBFT-STATIC::TRANSACTIONP-WHEN-MEMBER-EQUAL-OF-TRANSACTION-LISTP))
 (12 12 (:TYPE-PRESCRIPTION LEN))
 (6 6 (:REWRITE-QUOTED-CONSTANT ALEOBFT-STATIC::TRANSACTION-LIST-FIX-UNDER-TRANSACTION-LIST-EQUIV))
 (6 6 (:DEFINITION NFIX))
 (1 1 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 )
