(AIGNET::GATESIMP-LEVEL-P)
(AIGNET::GATESIMP-LEVEL-FIX
 (1 1 (:TYPE-PRESCRIPTION AIGNET::GATESIMP-LEVEL-FIX))
 )
(AIGNET::GATESIMP-LEVEL-P-OF-GATESIMP-LEVEL-FIX
 (33 33 (:TYPE-PRESCRIPTION AIGNET::GATESIMP-LEVEL-FIX))
 (6 2 (:REWRITE NATP-WHEN-GTE-0))
 (5 5 (:REWRITE DEFAULT-<-2))
 (5 5 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE NATP-WHEN-INTEGERP))
 )
(AIGNET::GATESIMP-LEVEL-FIX-WHEN-GATESIMP-LEVEL-P
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 (3 1 (:REWRITE NATP-WHEN-GTE-0))
 (1 1 (:REWRITE NATP-WHEN-INTEGERP))
 )
(FTY::TMP-DEFFIXTYPE-IDEMPOTENT
 (33 33 (:TYPE-PRESCRIPTION AIGNET::GATESIMP-LEVEL-FIX))
 (5 5 (:REWRITE DEFAULT-<-2))
 (5 5 (:REWRITE DEFAULT-<-1))
 (5 3 (:REWRITE NATP-WHEN-GTE-0))
 (3 3 (:REWRITE NATP-WHEN-INTEGERP))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 )
(AIGNET::GATESIMP-LEVEL-EQUIV$INLINE
 (4 4 (:TYPE-PRESCRIPTION AIGNET::GATESIMP-LEVEL-FIX))
 )
(AIGNET::GATESIMP-LEVEL-EQUIV-IS-AN-EQUIVALENCE)
(AIGNET::GATESIMP-LEVEL-EQUIV-IMPLIES-EQUAL-GATESIMP-LEVEL-FIX-1)
(AIGNET::GATESIMP-LEVEL-FIX-UNDER-GATESIMP-LEVEL-EQUIV)
(AIGNET::GATESIMP-LEVEL-P-COMPOUND-RECOGNIZER)
(AIGNET::UNSIGNED-BYTE-P-WHEN-GATESIMP-LEVEL-P)
(AIGNET::BOUND-WHEN-GATESIMP-LEVEL-P)
(AIGNET::GATESIMP-XOR-MODE-P)
(AIGNET::GATESIMP-XOR-MODE-FIX
 (1 1 (:TYPE-PRESCRIPTION AIGNET::GATESIMP-XOR-MODE-FIX))
 )
(AIGNET::GATESIMP-XOR-MODE-P-OF-GATESIMP-XOR-MODE-FIX
 (33 33 (:TYPE-PRESCRIPTION AIGNET::GATESIMP-XOR-MODE-FIX))
 (6 2 (:REWRITE NATP-WHEN-GTE-0))
 (5 5 (:REWRITE DEFAULT-<-2))
 (5 5 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE NATP-WHEN-INTEGERP))
 )
(AIGNET::GATESIMP-XOR-MODE-FIX-WHEN-GATESIMP-XOR-MODE-P
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 (3 1 (:REWRITE NATP-WHEN-GTE-0))
 (1 1 (:REWRITE NATP-WHEN-INTEGERP))
 )
(FTY::TMP-DEFFIXTYPE-IDEMPOTENT
 (33 33 (:TYPE-PRESCRIPTION AIGNET::GATESIMP-XOR-MODE-FIX))
 (5 5 (:REWRITE DEFAULT-<-2))
 (5 5 (:REWRITE DEFAULT-<-1))
 (5 3 (:REWRITE NATP-WHEN-GTE-0))
 (3 3 (:REWRITE NATP-WHEN-INTEGERP))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 )
(AIGNET::GATESIMP-XOR-MODE-EQUIV$INLINE
 (4 4 (:TYPE-PRESCRIPTION AIGNET::GATESIMP-XOR-MODE-FIX))
 )
(AIGNET::GATESIMP-XOR-MODE-EQUIV-IS-AN-EQUIVALENCE)
(AIGNET::GATESIMP-XOR-MODE-EQUIV-IMPLIES-EQUAL-GATESIMP-XOR-MODE-FIX-1)
(AIGNET::GATESIMP-XOR-MODE-FIX-UNDER-GATESIMP-XOR-MODE-EQUIV)
(AIGNET::GATESIMP-XOR-MODE-P-COMPOUND-RECOGNIZER)
(AIGNET::UNSIGNED-BYTE-P-WHEN-GATESIMP-XOR-MODE-P)
(AIGNET::BOUND-WHEN-GATESIMP-XOR-MODE-P)
(AIGNET::GATESIMP-P
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (4 4 (:META CANCEL_PLUS-LESSP-CORRECT))
 (4 1 (:REWRITE NATP-WHEN-GTE-0))
 (1 1 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (1 1 (:REWRITE NATP-WHEN-INTEGERP))
 (1 1 (:REWRITE NATP-RW))
 (1 1 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (1 1 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(AIGNET::UNSIGNED-BYTE-P-WHEN-GATESIMP-P)
(AIGNET::GATESIMP-P-COMPOUND-RECOGNIZER)
(AIGNET::GATESIMP-FIX
 (50 5 (:REWRITE AIGNET::UNSIGNED-BYTE-P-WHEN-GATESIMP-P))
 (21 21 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (21 21 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (7 7 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (1 1 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (1 1 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(AIGNET::GATESIMP-P-OF-GATESIMP-FIX
 (35 35 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (35 35 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (26 2 (:REWRITE BITOPS::UNSIGNED-BYTE-P-OF-0-X))
 (18 3 (:REWRITE AIGNET::GATESIMP-XOR-MODE-FIX-WHEN-GATESIMP-XOR-MODE-P))
 (18 3 (:REWRITE AIGNET::GATESIMP-LEVEL-FIX-WHEN-GATESIMP-LEVEL-P))
 (15 15 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (15 3 (:REWRITE FTY::UNSIGNED-BYTE-P-1-WHEN-BITP))
 (6 6 (:TYPE-PRESCRIPTION BITP))
 (6 3 (:REWRITE FTY::BITP-WHEN-UNSIGNED-BYTE-P-1))
 (2 2 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (2 2 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(AIGNET::GATESIMP-FIX-WHEN-GATESIMP-P
 (50 5 (:REWRITE AIGNET::UNSIGNED-BYTE-P-WHEN-GATESIMP-P))
 (21 21 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (21 21 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (5 5 (:TYPE-PRESCRIPTION AIGNET::GATESIMP-P))
 (5 5 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (1 1 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (1 1 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(FTY::TMP-DEFFIXTYPE-IDEMPOTENT)
(AIGNET::GATESIMP-EQUIV$INLINE)
(AIGNET::GATESIMP-EQUIV-IS-AN-EQUIVALENCE)
(AIGNET::GATESIMP-EQUIV-IMPLIES-EQUAL-GATESIMP-FIX-1)
(AIGNET::GATESIMP-FIX-UNDER-GATESIMP-EQUIV)
(AIGNET::GATESIMP
 (1 1 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (1 1 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 )
(AIGNET::GATESIMP-P-OF-GATESIMP
 (44 44 (:TYPE-PRESCRIPTION AIGNET::GATESIMP-XOR-MODE-FIX))
 (18 18 (:TYPE-PRESCRIPTION AIGNET::GATESIMP-LEVEL-FIX))
 (18 2 (:REWRITE BITOPS::UNSIGNED-BYTE-P-OF-0-X))
 (14 14 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (14 14 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (9 9 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (9 3 (:REWRITE AIGNET::GATESIMP-XOR-MODE-FIX-WHEN-GATESIMP-XOR-MODE-P))
 (9 3 (:REWRITE AIGNET::GATESIMP-LEVEL-FIX-WHEN-GATESIMP-LEVEL-P))
 (2 2 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (2 2 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(AIGNET::GATESIMP-OF-BOOL-FIX-HASHP
 (28 28 (:TYPE-PRESCRIPTION AIGNET::GATESIMP-XOR-MODE-FIX))
 (14 14 (:TYPE-PRESCRIPTION AIGNET::GATESIMP-LEVEL-FIX))
 )
(AIGNET::GATESIMP-IFF-CONGRUENCE-ON-HASHP)
(AIGNET::GATESIMP-OF-GATESIMP-LEVEL-FIX-LEVEL
 (28 28 (:TYPE-PRESCRIPTION AIGNET::GATESIMP-XOR-MODE-FIX))
 (22 22 (:TYPE-PRESCRIPTION AIGNET::GATESIMP-LEVEL-FIX))
 )
(AIGNET::GATESIMP-GATESIMP-LEVEL-EQUIV-CONGRUENCE-ON-LEVEL)
(AIGNET::GATESIMP-OF-GATESIMP-XOR-MODE-FIX-XOR-MODE
 (44 44 (:TYPE-PRESCRIPTION AIGNET::GATESIMP-XOR-MODE-FIX))
 (14 14 (:TYPE-PRESCRIPTION AIGNET::GATESIMP-LEVEL-FIX))
 )
(AIGNET::GATESIMP-GATESIMP-XOR-MODE-EQUIV-CONGRUENCE-ON-XOR-MODE)
(AIGNET::GATESIMP-EQUIV-UNDER-MASK)
(AIGNET::GATESIMP->HASHP
 (19 3 (:REWRITE LOGHEAD-IDENTITY))
 (10 2 (:REWRITE FTY::UNSIGNED-BYTE-P-1-WHEN-BITP))
 (4 4 (:TYPE-PRESCRIPTION BITP))
 (4 2 (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
 (4 2 (:REWRITE FTY::BITP-WHEN-UNSIGNED-BYTE-P-1))
 (3 3 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (2 2 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (1 1 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 )
(AIGNET::BOOLEANP-OF-GATESIMP->HASHP)
(AIGNET::GATESIMP->HASHP-OF-GATESIMP-FIX-X)
(AIGNET::GATESIMP->HASHP-GATESIMP-EQUIV-CONGRUENCE-ON-X)
(AIGNET::GATESIMP->HASHP-OF-GATESIMP
 (182 37 (:TYPE-PRESCRIPTION FTY::LOGAPP-NATP))
 (91 5 (:REWRITE UNSIGNED-BYTE-P-OF-LOGAPP))
 (75 3 (:REWRITE BITOPS::UNSIGNED-BYTE-P-OF-0-X))
 (68 68 (:TYPE-PRESCRIPTION AIGNET::GATESIMP-XOR-MODE-FIX))
 (45 1 (:REWRITE AIGNET::GATESIMP-FIX-WHEN-GATESIMP-P))
 (37 37 (:TYPE-PRESCRIPTION NEGP))
 (37 37 (:TYPE-PRESCRIPTION LOGAPP-TYPE))
 (32 32 (:TYPE-PRESCRIPTION AIGNET::GATESIMP-LEVEL-FIX))
 (13 13 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (13 13 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (11 11 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (4 4 (:TYPE-PRESCRIPTION BITP))
 (4 4 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (4 4 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (4 2 (:REWRITE FTY::BITP-WHEN-UNSIGNED-BYTE-P-1))
 (3 1 (:REWRITE BOOL-FIX-WHEN-BOOLEANP))
 (2 2 (:TYPE-PRESCRIPTION AIGNET::GATESIMP-P))
 (2 2 (:TYPE-PRESCRIPTION BOOLEANP))
 )
(FTY::DEFBITSTRUCT-WRITE-WITH-MASK-LEMMA
 (354 28 (:REWRITE BITOPS::LOGBITP-NONZERO-OF-BIT))
 (350 31 (:REWRITE LOGHEAD-IDENTITY))
 (336 65 (:REWRITE FTY::UNSIGNED-BYTE-P-1-WHEN-BITP))
 (310 69 (:REWRITE FTY::BITP-WHEN-UNSIGNED-BYTE-P-1))
 (184 16 (:REWRITE BITOPS::LOGBITP-0-OF-BIT))
 (172 172 (:TYPE-PRESCRIPTION BITP))
 (159 159 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (118 40 (:REWRITE AIGNET::GATESIMP-FIX-WHEN-GATESIMP-P))
 (114 38 (:REWRITE BITOPS::LOGBITP-WHEN-BITMASKP))
 (78 78 (:TYPE-PRESCRIPTION AIGNET::GATESIMP-P))
 (65 65 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (55 55 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (54 54 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (52 36 (:REWRITE DEFAULT-<-1))
 (48 6 (:REWRITE BFIX-WHEN-NOT-1))
 (42 15 (:REWRITE NATP-WHEN-GTE-0))
 (40 10 (:REWRITE NFIX-WHEN-NOT-NATP))
 (40 2 (:LINEAR BITOPS::LOGXOR->=-0-LINEAR-1))
 (40 2 (:LINEAR BITOPS::LOGXOR-<-0-LINEAR-2))
 (40 2 (:LINEAR BITOPS::LOGXOR-<-0-LINEAR-1))
 (38 38 (:REWRITE BITOPS::LOGBITP-OF-NEGATIVE-CONST))
 (38 38 (:REWRITE BITOPS::LOGBITP-OF-MASK))
 (38 38 (:REWRITE BITOPS::LOGBITP-OF-CONST-SPLIT))
 (38 38 (:REWRITE BITOPS::LOGBITP-OF-CONST))
 (38 38 (:META BITOPS::OPEN-LOGBITP-OF-CONST-LITE-META))
 (36 36 (:REWRITE DEFAULT-<-2))
 (36 36 (:META CANCEL_PLUS-LESSP-CORRECT))
 (34 14 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
 (27 1 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
 (26 26 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (26 26 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (24 3 (:REWRITE ZP-WHEN-INTEGERP))
 (22 10 (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
 (15 15 (:REWRITE NATP-WHEN-INTEGERP))
 (15 15 (:REWRITE NATP-RW))
 (12 12 (:TYPE-PRESCRIPTION BIT->BOOL$INLINE))
 (12 6 (:REWRITE BFIX-WHEN-NOT-BITP))
 (12 6 (:REWRITE BFIX-WHEN-NOT-BIT->BOOL))
 (12 6 (:REWRITE BFIX-WHEN-BIT->BOOL))
 (12 3 (:REWRITE ZP-WHEN-GT-0))
 (6 6 (:REWRITE INEQUALITY-WITH-NFIX-HYP-2))
 (3 3 (:TYPE-PRESCRIPTION ZP))
 )
(AIGNET::GATESIMP->HASHP-OF-WRITE-WITH-MASK
 (168 7 (:REWRITE LOGHEAD-IDENTITY))
 (140 7 (:REWRITE FTY::UNSIGNED-BYTE-P-1-WHEN-BITP))
 (104 52 (:TYPE-PRESCRIPTION BITOPS::LOGNOT-NEGP))
 (104 52 (:TYPE-PRESCRIPTION BITOPS::LOGNOT-NATP))
 (52 52 (:TYPE-PRESCRIPTION NEGP))
 (52 52 (:TYPE-PRESCRIPTION NATP))
 (35 1 (:LINEAR BITOPS::LOGAND->=-0-LINEAR-1))
 (35 1 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
 (31 8 (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
 (30 3 (:REWRITE BITOPS::LOGNOT-<-CONST))
 (27 1 (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 1))
 (26 10 (:REWRITE AIGNET::GATESIMP-FIX-WHEN-GATESIMP-P))
 (21 21 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (18 8 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
 (18 8 (:REWRITE IFIX-WHEN-INTEGERP))
 (16 16 (:TYPE-PRESCRIPTION AIGNET::GATESIMP-P))
 (14 14 (:TYPE-PRESCRIPTION BITP))
 (14 7 (:REWRITE FTY::BITP-WHEN-UNSIGNED-BYTE-P-1))
 (12 3 (:REWRITE BITOPS::LOGNOT-OF-LOGNOT))
 (11 11 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (8 8 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (7 7 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (6 6 (:META CANCEL_PLUS-LESSP-CORRECT))
 (6 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE IFIX-UNDER-INT-EQUIV))
 (3 3 (:REWRITE DEFAULT-<-1))
 (3 3 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (3 3 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(AIGNET::GATESIMP->LEVEL
 (146 26 (:REWRITE LOGTAIL-IDENTITY))
 (60 12 (:REWRITE FTY::UNSIGNED-BYTE-P-1-WHEN-BITP))
 (51 51 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (48 8 (:REWRITE AIGNET::UNSIGNED-BYTE-P-WHEN-GATESIMP-LEVEL-P))
 (46 46 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (32 8 (:REWRITE UNSIGNED-BYTE-P-OF-ASH))
 (29 25 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
 (24 24 (:TYPE-PRESCRIPTION BITP))
 (24 12 (:REWRITE FTY::BITP-WHEN-UNSIGNED-BYTE-P-1))
 (18 10 (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
 (4 2 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
 (3 3 (:TYPE-PRESCRIPTION NATP))
 )
(AIGNET::GATESIMP-LEVEL-P-OF-GATESIMP->LEVEL
 (17 1 (:REWRITE UNSIGNED-BYTE-P-OF-LOGAPP))
 (15 3 (:TYPE-PRESCRIPTION FTY::LOGAPP-NATP))
 (13 1 (:REWRITE BITOPS::UNSIGNED-BYTE-P-OF-0-X))
 (11 11 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (11 11 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (6 1 (:REWRITE AIGNET::GATESIMP-XOR-MODE-FIX-WHEN-GATESIMP-XOR-MODE-P))
 (6 1 (:REWRITE AIGNET::GATESIMP-LEVEL-FIX-WHEN-GATESIMP-LEVEL-P))
 (5 5 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (5 1 (:REWRITE FTY::UNSIGNED-BYTE-P-1-WHEN-BITP))
 (3 1 (:REWRITE AIGNET::GATESIMP-FIX-WHEN-GATESIMP-P))
 (2 2 (:TYPE-PRESCRIPTION AIGNET::GATESIMP-P))
 (2 2 (:TYPE-PRESCRIPTION BITP))
 (2 1 (:REWRITE FTY::BITP-WHEN-UNSIGNED-BYTE-P-1))
 (1 1 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (1 1 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(AIGNET::GATESIMP->LEVEL-OF-GATESIMP-FIX-X)
(AIGNET::GATESIMP->LEVEL-GATESIMP-EQUIV-CONGRUENCE-ON-X)
(AIGNET::GATESIMP->LEVEL-OF-GATESIMP
 (133 27 (:TYPE-PRESCRIPTION FTY::LOGAPP-NATP))
 (65 4 (:REWRITE UNSIGNED-BYTE-P-OF-LOGAPP))
 (60 60 (:TYPE-PRESCRIPTION AIGNET::GATESIMP-XOR-MODE-FIX))
 (51 3 (:REWRITE BITOPS::UNSIGNED-BYTE-P-OF-0-X))
 (46 46 (:TYPE-PRESCRIPTION AIGNET::GATESIMP-LEVEL-FIX))
 (45 1 (:REWRITE AIGNET::GATESIMP-FIX-WHEN-GATESIMP-P))
 (27 27 (:TYPE-PRESCRIPTION NEGP))
 (27 27 (:TYPE-PRESCRIPTION LOGAPP-TYPE))
 (13 13 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (13 13 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (11 11 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (3 3 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (3 3 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (2 2 (:TYPE-PRESCRIPTION AIGNET::GATESIMP-P))
 (2 2 (:TYPE-PRESCRIPTION BITP))
 (2 1 (:REWRITE FTY::BITP-WHEN-UNSIGNED-BYTE-P-1))
 )
(FTY::DEFBITSTRUCT-WRITE-WITH-MASK-LEMMA
 (656 40 (:REWRITE BITOPS::LOGBITP-NONZERO-OF-BIT))
 (462 22 (:REWRITE ASH-0))
 (367 87 (:REWRITE NFIX-WHEN-NOT-NATP))
 (336 56 (:REWRITE AIGNET::GATESIMP-LEVEL-FIX-WHEN-GATESIMP-LEVEL-P))
 (314 40 (:REWRITE FTY::BITP-WHEN-UNSIGNED-BYTE-P-1))
 (292 14 (:REWRITE BITOPS::LOGBITP-OF-ASH-IN-RANGE))
 (286 112 (:REWRITE NATP-WHEN-GTE-0))
 (208 112 (:REWRITE NATP-WHEN-INTEGERP))
 (208 112 (:REWRITE NATP-RW))
 (203 203 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (192 64 (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
 (180 180 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (168 56 (:REWRITE BITOPS::LOGBITP-WHEN-BITMASKP))
 (162 112 (:REWRITE DEFAULT-<-1))
 (154 40 (:REWRITE FTY::UNSIGNED-BYTE-P-1-WHEN-BITP))
 (121 95 (:REWRITE DEFAULT-+-2))
 (120 120 (:TYPE-PRESCRIPTION BITP))
 (112 112 (:REWRITE DEFAULT-<-2))
 (112 112 (:META CANCEL_PLUS-LESSP-CORRECT))
 (106 95 (:REWRITE DEFAULT-+-1))
 (87 87 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (56 56 (:REWRITE BITOPS::LOGBITP-OF-NEGATIVE-CONST))
 (56 56 (:REWRITE BITOPS::LOGBITP-OF-MASK))
 (56 56 (:REWRITE BITOPS::LOGBITP-OF-CONST-SPLIT))
 (56 56 (:REWRITE BITOPS::LOGBITP-OF-CONST))
 (56 56 (:META BITOPS::OPEN-LOGBITP-OF-CONST-LITE-META))
 (48 48 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (48 48 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (46 46 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (43 43 (:REWRITE INEQUALITY-WITH-NFIX-HYP-2))
 (38 22 (:REWRITE RIGHT-SHIFT-TO-LOGTAIL))
 (37 20 (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
 (29 2 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
 (25 8 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
 (24 4 (:REWRITE AIGNET::GATESIMP-XOR-MODE-FIX-WHEN-GATESIMP-XOR-MODE-P))
 (19 1 (:LINEAR BITOPS::LOGXOR->=-0-LINEAR-2))
 (13 1 (:LINEAR BITOPS::LOGXOR->=-0-LINEAR-1))
 (13 1 (:LINEAR BITOPS::LOGXOR-<-0-LINEAR-2))
 (13 1 (:LINEAR BITOPS::LOGXOR-<-0-LINEAR-1))
 (12 4 (:REWRITE AIGNET::GATESIMP-FIX-WHEN-GATESIMP-P))
 (8 8 (:TYPE-PRESCRIPTION AIGNET::GATESIMP-P))
 )
(AIGNET::GATESIMP->LEVEL-OF-WRITE-WITH-MASK
 (122 61 (:TYPE-PRESCRIPTION BITOPS::LOGNOT-NEGP))
 (122 61 (:TYPE-PRESCRIPTION BITOPS::LOGNOT-NATP))
 (70 7 (:REWRITE BITOPS::LOGNOT-<-CONST))
 (61 61 (:TYPE-PRESCRIPTION NEGP))
 (61 61 (:TYPE-PRESCRIPTION NATP))
 (39 3 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
 (37 11 (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
 (34 14 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
 (34 14 (:REWRITE IFIX-WHEN-INTEGERP))
 (28 28 (:TYPE-PRESCRIPTION BITMASKP$INLINE))
 (26 10 (:REWRITE AIGNET::GATESIMP-FIX-WHEN-GATESIMP-P))
 (25 11 (:REWRITE BITOPS::LOGAND-WITH-BITMASK))
 (16 16 (:TYPE-PRESCRIPTION AIGNET::GATESIMP-P))
 (14 14 (:META CANCEL_PLUS-LESSP-CORRECT))
 (14 7 (:REWRITE DEFAULT-<-2))
 (12 3 (:REWRITE BITOPS::LOGNOT-OF-LOGNOT))
 (11 11 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (8 8 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (7 7 (:REWRITE DEFAULT-<-1))
 (3 3 (:REWRITE IFIX-UNDER-INT-EQUIV))
 (3 3 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (3 3 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(AIGNET::GATESIMP->XOR-MODE
 (205 38 (:REWRITE LOGTAIL-IDENTITY))
 (80 16 (:REWRITE FTY::UNSIGNED-BYTE-P-1-WHEN-BITP))
 (75 75 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (70 70 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (62 1 (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 2))
 (39 36 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
 (32 32 (:TYPE-PRESCRIPTION BITP))
 (32 16 (:REWRITE FTY::BITP-WHEN-UNSIGNED-BYTE-P-1))
 (12 6 (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
 (3 3 (:TYPE-PRESCRIPTION NATP))
 (2 1 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
 )
(AIGNET::GATESIMP-XOR-MODE-P-OF-GATESIMP->XOR-MODE
 (11 11 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (11 11 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (6 1 (:REWRITE AIGNET::GATESIMP-XOR-MODE-FIX-WHEN-GATESIMP-XOR-MODE-P))
 (6 1 (:REWRITE AIGNET::GATESIMP-LEVEL-FIX-WHEN-GATESIMP-LEVEL-P))
 (5 1 (:REWRITE FTY::UNSIGNED-BYTE-P-1-WHEN-BITP))
 (3 3 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (3 1 (:REWRITE AIGNET::GATESIMP-FIX-WHEN-GATESIMP-P))
 (2 2 (:TYPE-PRESCRIPTION AIGNET::GATESIMP-P))
 (2 2 (:TYPE-PRESCRIPTION AIGNET::GATESIMP-LEVEL-P))
 (2 2 (:TYPE-PRESCRIPTION BITP))
 (2 1 (:REWRITE FTY::BITP-WHEN-UNSIGNED-BYTE-P-1))
 )
(AIGNET::GATESIMP->XOR-MODE-OF-GATESIMP-FIX-X)
(AIGNET::GATESIMP->XOR-MODE-GATESIMP-EQUIV-CONGRUENCE-ON-X)
(AIGNET::GATESIMP->XOR-MODE-OF-GATESIMP
 (118 24 (:TYPE-PRESCRIPTION FTY::LOGAPP-NATP))
 (69 69 (:TYPE-PRESCRIPTION AIGNET::GATESIMP-XOR-MODE-FIX))
 (52 3 (:REWRITE UNSIGNED-BYTE-P-OF-LOGAPP))
 (45 1 (:REWRITE AIGNET::GATESIMP-FIX-WHEN-GATESIMP-P))
 (42 2 (:REWRITE BITOPS::UNSIGNED-BYTE-P-OF-0-X))
 (24 24 (:TYPE-PRESCRIPTION NEGP))
 (24 24 (:TYPE-PRESCRIPTION LOGAPP-TYPE))
 (22 22 (:TYPE-PRESCRIPTION AIGNET::GATESIMP-LEVEL-FIX))
 (13 13 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (13 13 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (9 9 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (2 2 (:TYPE-PRESCRIPTION AIGNET::GATESIMP-P))
 (2 2 (:TYPE-PRESCRIPTION BITP))
 (2 2 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (2 2 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (2 1 (:REWRITE FTY::BITP-WHEN-UNSIGNED-BYTE-P-1))
 )
(FTY::DEFBITSTRUCT-WRITE-WITH-MASK-LEMMA
 (656 40 (:REWRITE BITOPS::LOGBITP-NONZERO-OF-BIT))
 (464 24 (:REWRITE ASH-0))
 (372 90 (:REWRITE NFIX-WHEN-NOT-NATP))
 (336 56 (:REWRITE AIGNET::GATESIMP-XOR-MODE-FIX-WHEN-GATESIMP-XOR-MODE-P))
 (314 40 (:REWRITE FTY::BITP-WHEN-UNSIGNED-BYTE-P-1))
 (292 14 (:REWRITE BITOPS::LOGBITP-OF-ASH-IN-RANGE))
 (286 112 (:REWRITE NATP-WHEN-GTE-0))
 (208 112 (:REWRITE NATP-WHEN-INTEGERP))
 (208 112 (:REWRITE NATP-RW))
 (205 205 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (192 64 (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
 (180 180 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (168 56 (:REWRITE BITOPS::LOGBITP-WHEN-BITMASKP))
 (167 115 (:REWRITE DEFAULT-<-1))
 (154 40 (:REWRITE FTY::UNSIGNED-BYTE-P-1-WHEN-BITP))
 (136 104 (:REWRITE DEFAULT-+-2))
 (120 120 (:TYPE-PRESCRIPTION BITP))
 (117 104 (:REWRITE DEFAULT-+-1))
 (115 115 (:REWRITE DEFAULT-<-2))
 (87 87 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (56 56 (:REWRITE BITOPS::LOGBITP-OF-NEGATIVE-CONST))
 (56 56 (:REWRITE BITOPS::LOGBITP-OF-MASK))
 (56 56 (:REWRITE BITOPS::LOGBITP-OF-CONST-SPLIT))
 (56 56 (:REWRITE BITOPS::LOGBITP-OF-CONST))
 (56 56 (:META BITOPS::OPEN-LOGBITP-OF-CONST-LITE-META))
 (48 48 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (48 48 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (46 46 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (45 45 (:REWRITE INEQUALITY-WITH-NFIX-HYP-2))
 (42 24 (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
 (41 24 (:REWRITE RIGHT-SHIFT-TO-LOGTAIL))
 (29 2 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
 (25 8 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
 (24 4 (:REWRITE AIGNET::GATESIMP-LEVEL-FIX-WHEN-GATESIMP-LEVEL-P))
 (19 1 (:LINEAR BITOPS::LOGXOR->=-0-LINEAR-2))
 (13 1 (:LINEAR BITOPS::LOGXOR->=-0-LINEAR-1))
 (13 1 (:LINEAR BITOPS::LOGXOR-<-0-LINEAR-2))
 (13 1 (:LINEAR BITOPS::LOGXOR-<-0-LINEAR-1))
 (12 4 (:REWRITE AIGNET::GATESIMP-FIX-WHEN-GATESIMP-P))
 (8 8 (:TYPE-PRESCRIPTION AIGNET::GATESIMP-P))
 (8 8 (:TYPE-PRESCRIPTION AIGNET::GATESIMP-LEVEL-P))
 )
(AIGNET::GATESIMP->XOR-MODE-OF-WRITE-WITH-MASK
 (122 61 (:TYPE-PRESCRIPTION BITOPS::LOGNOT-NEGP))
 (122 61 (:TYPE-PRESCRIPTION BITOPS::LOGNOT-NATP))
 (70 7 (:REWRITE BITOPS::LOGNOT-<-CONST))
 (61 61 (:TYPE-PRESCRIPTION NEGP))
 (61 61 (:TYPE-PRESCRIPTION NATP))
 (39 3 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
 (37 11 (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
 (34 14 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
 (34 14 (:REWRITE IFIX-WHEN-INTEGERP))
 (28 28 (:TYPE-PRESCRIPTION BITMASKP$INLINE))
 (26 10 (:REWRITE AIGNET::GATESIMP-FIX-WHEN-GATESIMP-P))
 (25 11 (:REWRITE BITOPS::LOGAND-WITH-BITMASK))
 (16 16 (:TYPE-PRESCRIPTION AIGNET::GATESIMP-P))
 (14 14 (:META CANCEL_PLUS-LESSP-CORRECT))
 (14 7 (:REWRITE DEFAULT-<-2))
 (12 3 (:REWRITE BITOPS::LOGNOT-OF-LOGNOT))
 (11 11 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (8 8 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (7 7 (:REWRITE DEFAULT-<-1))
 (3 3 (:REWRITE IFIX-UNDER-INT-EQUIV))
 (3 3 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (3 3 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(AIGNET::GATESIMP-FIX-IN-TERMS-OF-GATESIMP
 (110 110 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (110 110 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (8 8 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (8 1 (:REWRITE BFIX-WHEN-NOT-1))
 (6 4 (:REWRITE AIGNET::GATESIMP-FIX-WHEN-GATESIMP-P))
 (4 4 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (4 4 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (2 2 (:TYPE-PRESCRIPTION AIGNET::GATESIMP-P))
 (2 2 (:TYPE-PRESCRIPTION BITP))
 (2 2 (:TYPE-PRESCRIPTION BIT->BOOL$INLINE))
 (2 1 (:REWRITE FTY::BITP-WHEN-UNSIGNED-BYTE-P-1))
 (2 1 (:REWRITE BFIX-WHEN-NOT-BITP))
 (2 1 (:REWRITE BFIX-WHEN-NOT-BIT->BOOL))
 (2 1 (:REWRITE BFIX-WHEN-BIT->BOOL))
 )
(AIGNET::!GATESIMP->HASHP
 (64 28 (:REWRITE BITOPS::LOGAND-WITH-BITMASK))
 (61 61 (:TYPE-PRESCRIPTION BITOPS::LOGAND-NATP-TYPE-2))
 (36 36 (:TYPE-PRESCRIPTION BITMASKP$INLINE))
 (20 20 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (8 8 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (8 4 (:REWRITE UNSIGNED-BYTE-P-OF-LOGAND-1))
 (8 4 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
 (6 2 (:REWRITE FTY::BITP-WHEN-UNSIGNED-BYTE-P-1))
 )
(AIGNET::GATESIMP-P-OF-!GATESIMP->HASHP
 (69 3 (:REWRITE AIGNET::GATESIMP-FIX-WHEN-GATESIMP-P))
 (53 53 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (53 53 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (26 2 (:REWRITE BITOPS::UNSIGNED-BYTE-P-OF-0-X))
 (18 18 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (18 3 (:REWRITE AIGNET::GATESIMP-XOR-MODE-FIX-WHEN-GATESIMP-XOR-MODE-P))
 (18 3 (:REWRITE AIGNET::GATESIMP-LEVEL-FIX-WHEN-GATESIMP-LEVEL-P))
 (15 3 (:REWRITE FTY::UNSIGNED-BYTE-P-1-WHEN-BITP))
 (9 3 (:REWRITE FTY::PART-INSTALL-OF-LOGAPP-ABOVE))
 (6 6 (:TYPE-PRESCRIPTION BITP))
 (6 3 (:REWRITE FTY::BITP-WHEN-UNSIGNED-BYTE-P-1))
 (2 2 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (2 2 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(AIGNET::!GATESIMP->HASHP-OF-BOOL-FIX-HASHP)
(AIGNET::!GATESIMP->HASHP-IFF-CONGRUENCE-ON-HASHP)
(AIGNET::!GATESIMP->HASHP-OF-GATESIMP-FIX-X)
(AIGNET::!GATESIMP->HASHP-GATESIMP-EQUIV-CONGRUENCE-ON-X)
(AIGNET::!GATESIMP->HASHP-IS-GATESIMP
 (6 6 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (6 6 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (3 1 (:REWRITE FTY::PART-INSTALL-OF-LOGAPP-ABOVE))
 (2 2 (:TYPE-PRESCRIPTION NFIX))
 (2 2 (:REWRITE AIGNET::GATESIMP->XOR-MODE-OF-WRITE-WITH-MASK))
 (2 2 (:REWRITE AIGNET::GATESIMP->LEVEL-OF-WRITE-WITH-MASK))
 (1 1 (:REWRITE AIGNET::GATESIMP->HASHP-OF-WRITE-WITH-MASK))
 )
(AIGNET::GATESIMP->HASHP-OF-!GATESIMP->HASHP
 (12 4 (:REWRITE BOOL-FIX-WHEN-BOOLEANP))
 (8 8 (:TYPE-PRESCRIPTION BOOLEANP))
 (7 7 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (7 7 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (4 4 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (4 4 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (1 1 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 )
(AIGNET::!GATESIMP->HASHP-EQUIV-UNDER-MASK
 (411 25 (:REWRITE BITOPS::LOGSQUASH-CANCEL))
 (314 41 (:REWRITE FTY::UNSIGNED-BYTE-P-1-WHEN-BITP))
 (120 34 (:REWRITE FTY::BITP-WHEN-UNSIGNED-BYTE-P-1))
 (116 6 (:REWRITE BITOPS::LOGBITP-NONZERO-OF-BIT))
 (75 8 (:REWRITE BITOPS::UNSIGNED-BYTE-P-=-N-OF-PART-INSTALL-WIDTH-LOW))
 (73 73 (:TYPE-PRESCRIPTION BITP))
 (54 24 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
 (47 3 (:LINEAR BITOPS::LOGXOR->=-0-LINEAR-1))
 (47 3 (:LINEAR BITOPS::LOGXOR-<-0-LINEAR-2))
 (47 3 (:LINEAR BITOPS::LOGXOR-<-0-LINEAR-1))
 (41 41 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (36 3 (:REWRITE UNSIGNED-BYTE-P-OF-LOGXOR))
 (31 18 (:REWRITE DEFAULT-<-1))
 (30 10 (:REWRITE BITOPS::LOGBITP-WHEN-BITMASKP))
 (29 29 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (28 28 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (27 1 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
 (23 23 (:META CANCEL_PLUS-LESSP-CORRECT))
 (18 18 (:REWRITE DEFAULT-<-2))
 (10 10 (:REWRITE BITOPS::LOGBITP-OF-NEGATIVE-CONST))
 (10 10 (:REWRITE BITOPS::LOGBITP-OF-MASK))
 (10 10 (:REWRITE BITOPS::LOGBITP-OF-CONST-SPLIT))
 (10 10 (:REWRITE BITOPS::LOGBITP-OF-CONST))
 (10 10 (:META BITOPS::OPEN-LOGBITP-OF-CONST-LITE-META))
 (9 3 (:REWRITE BITOPS::LOGAND-WITH-BITMASK))
 (8 8 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (8 8 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (8 2 (:REWRITE NATP-WHEN-GTE-0))
 (6 6 (:REWRITE NFIX-WHEN-NOT-NATP))
 (2 2 (:REWRITE NATP-WHEN-INTEGERP))
 (2 2 (:REWRITE NATP-RW))
 (2 1 (:LINEAR BITOPS::LOGAND->=-0-LINEAR-2))
 (1 1 (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 2))
 )
(AIGNET::!GATESIMP->LEVEL
 (374 12 (:LINEAR BITOPS::LOGIOR-<-0-LINEAR-2))
 (344 12 (:LINEAR BITOPS::LOGIOR-<-0-LINEAR-1))
 (156 84 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
 (152 12 (:REWRITE BITOPS::ASH-<-0))
 (142 24 (:REWRITE ASH-0))
 (138 66 (:REWRITE BITOPS::LOGAND-WITH-BITMASK))
 (96 12 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
 (78 12 (:LINEAR BITOPS::LOGAND->=-0-LINEAR-2))
 (72 72 (:TYPE-PRESCRIPTION BITMASKP$INLINE))
 (70 22 (:REWRITE ZIP-OPEN))
 (60 12 (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 2))
 (56 36 (:REWRITE DEFAULT-<-1))
 (48 48 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (48 48 (:META CANCEL_PLUS-LESSP-CORRECT))
 (48 12 (:LINEAR LOGHEAD-UPPER-BOUND))
 (42 24 (:REWRITE RIGHT-SHIFT-TO-LOGTAIL))
 (40 40 (:TYPE-PRESCRIPTION ZIP))
 (36 36 (:REWRITE DEFAULT-<-2))
 (24 12 (:LINEAR BITOPS::LOGAND->=-0-LINEAR-1))
 (12 12 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (12 12 (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 1))
 (10 5 (:REWRITE UNSIGNED-BYTE-P-OF-LOGAND-1))
 (8 8 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (8 8 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(AIGNET::GATESIMP-P-OF-!GATESIMP->LEVEL
 (46 2 (:REWRITE AIGNET::GATESIMP-FIX-WHEN-GATESIMP-P))
 (37 37 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (37 37 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (21 5 (:REWRITE AIGNET::GATESIMP-LEVEL-FIX-WHEN-GATESIMP-LEVEL-P))
 (13 13 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (13 1 (:REWRITE BITOPS::UNSIGNED-BYTE-P-OF-0-X))
 (12 12 (:TYPE-PRESCRIPTION AIGNET::GATESIMP-LEVEL-FIX))
 (12 2 (:REWRITE AIGNET::GATESIMP-XOR-MODE-FIX-WHEN-GATESIMP-XOR-MODE-P))
 (10 2 (:REWRITE FTY::UNSIGNED-BYTE-P-1-WHEN-BITP))
 (4 4 (:TYPE-PRESCRIPTION BITP))
 (4 2 (:REWRITE FTY::BITP-WHEN-UNSIGNED-BYTE-P-1))
 (1 1 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (1 1 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(AIGNET::!GATESIMP->LEVEL-OF-GATESIMP-LEVEL-FIX-LEVEL
 (23 23 (:TYPE-PRESCRIPTION AIGNET::GATESIMP-LEVEL-FIX))
 )
(AIGNET::!GATESIMP->LEVEL-GATESIMP-LEVEL-EQUIV-CONGRUENCE-ON-LEVEL)
(AIGNET::!GATESIMP->LEVEL-OF-GATESIMP-FIX-X
 (15 15 (:TYPE-PRESCRIPTION AIGNET::GATESIMP-LEVEL-FIX))
 )
(AIGNET::!GATESIMP->LEVEL-GATESIMP-EQUIV-CONGRUENCE-ON-X)
(AIGNET::!GATESIMP->LEVEL-IS-GATESIMP
 (6 6 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (6 6 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (2 2 (:REWRITE AIGNET::GATESIMP->XOR-MODE-OF-WRITE-WITH-MASK))
 (2 2 (:REWRITE AIGNET::GATESIMP->HASHP-OF-WRITE-WITH-MASK))
 (1 1 (:REWRITE AIGNET::GATESIMP->LEVEL-OF-WRITE-WITH-MASK))
 )
(AIGNET::GATESIMP->LEVEL-OF-!GATESIMP->LEVEL
 (65 65 (:TYPE-PRESCRIPTION AIGNET::GATESIMP-LEVEL-FIX))
 (13 5 (:REWRITE AIGNET::GATESIMP-LEVEL-FIX-WHEN-GATESIMP-LEVEL-P))
 (7 7 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (7 7 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (3 3 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (3 3 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (3 3 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(AIGNET::!GATESIMP->LEVEL-EQUIV-UNDER-MASK
 (274 19 (:REWRITE BITOPS::LOGBITP-NONZERO-OF-BIT))
 (253 8 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
 (184 56 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
 (181 181 (:TYPE-PRESCRIPTION AIGNET::GATESIMP-LEVEL-FIX))
 (167 22 (:REWRITE FTY::BITP-WHEN-UNSIGNED-BYTE-P-1))
 (140 8 (:LINEAR BITOPS::LOGXOR-<-0-LINEAR-2))
 (121 53 (:REWRITE DEFAULT-<-1))
 (104 8 (:LINEAR BITOPS::LOGXOR->=-0-LINEAR-1))
 (104 8 (:LINEAR BITOPS::LOGXOR-<-0-LINEAR-1))
 (94 94 (:TYPE-PRESCRIPTION BITMASKP$INLINE))
 (79 22 (:REWRITE FTY::UNSIGNED-BYTE-P-1-WHEN-BITP))
 (67 23 (:REWRITE BITOPS::LOGBITP-WHEN-BITMASKP))
 (64 64 (:TYPE-PRESCRIPTION BITP))
 (53 53 (:REWRITE DEFAULT-<-2))
 (53 53 (:META CANCEL_PLUS-LESSP-CORRECT))
 (53 28 (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
 (53 28 (:REWRITE BITOPS::LOGAND-WITH-BITMASK))
 (45 45 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (44 4 (:REWRITE BFIX-WHEN-NOT-1))
 (27 9 (:REWRITE AIGNET::GATESIMP-LEVEL-FIX-WHEN-GATESIMP-LEVEL-P))
 (26 2 (:REWRITE BITOPS::LOGBITP-0-OF-BIT))
 (25 25 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (23 23 (:REWRITE BITOPS::LOGBITP-OF-NEGATIVE-CONST))
 (23 23 (:REWRITE BITOPS::LOGBITP-OF-MASK))
 (23 23 (:REWRITE BITOPS::LOGBITP-OF-CONST))
 (23 2 (:REWRITE BITOPS::UNSIGNED-BYTE-P-=-N-OF-PART-INSTALL-WIDTH-LOW))
 (22 22 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (18 18 (:TYPE-PRESCRIPTION AIGNET::GATESIMP-LEVEL-P))
 (16 4 (:REWRITE NATP-WHEN-GTE-0))
 (15 15 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (14 14 (:REWRITE NFIX-WHEN-NOT-NATP))
 (12 12 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (12 12 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (10 2 (:REWRITE EQUAL-1-OF-BOOL->BIT))
 (8 4 (:REWRITE BFIX-WHEN-NOT-BITP))
 (8 4 (:REWRITE BFIX-WHEN-NOT-BIT->BOOL))
 (8 4 (:REWRITE BFIX-WHEN-BIT->BOOL))
 (7 7 (:REWRITE DEFAULT-+-2))
 (7 7 (:REWRITE DEFAULT-+-1))
 (4 4 (:REWRITE NATP-WHEN-INTEGERP))
 (4 4 (:REWRITE NATP-RW))
 (4 2 (:LINEAR BITOPS::B-XOR-BOUND))
 (3 3 (:REWRITE-QUOTED-CONSTANT BFIX-UNDER-BIT-EQUIV))
 )
(AIGNET::!GATESIMP->XOR-MODE
 (187 6 (:LINEAR BITOPS::LOGIOR-<-0-LINEAR-2))
 (172 6 (:LINEAR BITOPS::LOGIOR-<-0-LINEAR-1))
 (85 40 (:REWRITE BITOPS::LOGAND-WITH-BITMASK))
 (84 16 (:REWRITE ASH-0))
 (78 42 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
 (76 6 (:REWRITE BITOPS::ASH-<-0))
 (48 6 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
 (45 45 (:TYPE-PRESCRIPTION BITMASKP$INLINE))
 (39 6 (:LINEAR BITOPS::LOGAND->=-0-LINEAR-2))
 (38 14 (:REWRITE ZIP-OPEN))
 (32 32 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (30 6 (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 2))
 (28 18 (:REWRITE DEFAULT-<-1))
 (28 16 (:REWRITE RIGHT-SHIFT-TO-LOGTAIL))
 (26 26 (:TYPE-PRESCRIPTION ZIP))
 (24 24 (:META CANCEL_PLUS-LESSP-CORRECT))
 (24 6 (:LINEAR LOGHEAD-UPPER-BOUND))
 (18 18 (:REWRITE DEFAULT-<-2))
 (12 6 (:LINEAR BITOPS::LOGAND->=-0-LINEAR-1))
 (8 8 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (8 4 (:REWRITE UNSIGNED-BYTE-P-OF-LOGAND-1))
 (6 6 (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 1))
 (4 4 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (4 4 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(AIGNET::GATESIMP-P-OF-!GATESIMP->XOR-MODE
 (183 4 (:REWRITE AIGNET::UNSIGNED-BYTE-P-WHEN-GATESIMP-P))
 (96 24 (:TYPE-PRESCRIPTION BITOPS::NATP-PART-INSTALL-WIDTH-LOW))
 (69 12 (:TYPE-PRESCRIPTION FTY::LOGAPP-NATP))
 (46 2 (:REWRITE BITOPS::UNSIGNED-BYTE-P-OF-0-X))
 (46 2 (:REWRITE AIGNET::GATESIMP-FIX-WHEN-GATESIMP-P))
 (37 37 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (37 37 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (21 5 (:REWRITE AIGNET::GATESIMP-XOR-MODE-FIX-WHEN-GATESIMP-XOR-MODE-P))
 (19 19 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (12 2 (:REWRITE AIGNET::GATESIMP-LEVEL-FIX-WHEN-GATESIMP-LEVEL-P))
 (10 2 (:REWRITE FTY::UNSIGNED-BYTE-P-1-WHEN-BITP))
 (4 4 (:TYPE-PRESCRIPTION BITP))
 (4 2 (:REWRITE FTY::BITP-WHEN-UNSIGNED-BYTE-P-1))
 (3 3 (:TYPE-PRESCRIPTION FTY::PART-SELECT-WIDTH-1-TYPE))
 (2 2 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (2 2 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(AIGNET::!GATESIMP->XOR-MODE-OF-GATESIMP-XOR-MODE-FIX-XOR-MODE
 (23 23 (:TYPE-PRESCRIPTION AIGNET::GATESIMP-XOR-MODE-FIX))
 )
(AIGNET::!GATESIMP->XOR-MODE-GATESIMP-XOR-MODE-EQUIV-CONGRUENCE-ON-XOR-MODE)
(AIGNET::!GATESIMP->XOR-MODE-OF-GATESIMP-FIX-X
 (15 15 (:TYPE-PRESCRIPTION AIGNET::GATESIMP-XOR-MODE-FIX))
 )
(AIGNET::!GATESIMP->XOR-MODE-GATESIMP-EQUIV-CONGRUENCE-ON-X)
(AIGNET::!GATESIMP->XOR-MODE-IS-GATESIMP
 (24 24 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (24 24 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (8 8 (:REWRITE AIGNET::GATESIMP->LEVEL-OF-WRITE-WITH-MASK))
 (8 8 (:REWRITE AIGNET::GATESIMP->HASHP-OF-WRITE-WITH-MASK))
 (4 4 (:REWRITE AIGNET::GATESIMP->XOR-MODE-OF-WRITE-WITH-MASK))
 (3 3 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (3 3 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (2 2 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 )
(AIGNET::GATESIMP->XOR-MODE-OF-!GATESIMP->XOR-MODE
 (65 65 (:TYPE-PRESCRIPTION AIGNET::GATESIMP-XOR-MODE-FIX))
 (13 5 (:REWRITE AIGNET::GATESIMP-XOR-MODE-FIX-WHEN-GATESIMP-XOR-MODE-P))
 (7 7 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (7 7 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (3 3 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (3 3 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (3 3 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(AIGNET::!GATESIMP->XOR-MODE-EQUIV-UNDER-MASK
 (211 45 (:REWRITE LOGHEAD-IDENTITY))
 (122 122 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (116 6 (:REWRITE BITOPS::LOGBITP-NONZERO-OF-BIT))
 (68 8 (:REWRITE FTY::BITP-WHEN-UNSIGNED-BYTE-P-1))
 (64 12 (:REWRITE BITOPS::UNSIGNED-BYTE-P-=-N-OF-PART-INSTALL-WIDTH-LOW))
 (60 60 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (46 3 (:LINEAR BITOPS::LOGXOR->=-0-LINEAR-1))
 (46 3 (:LINEAR BITOPS::LOGXOR-<-0-LINEAR-2))
 (46 3 (:LINEAR BITOPS::LOGXOR-<-0-LINEAR-1))
 (44 19 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
 (36 8 (:REWRITE FTY::UNSIGNED-BYTE-P-1-WHEN-BITP))
 (33 20 (:REWRITE DEFAULT-<-1))
 (30 10 (:REWRITE BITOPS::LOGBITP-WHEN-BITMASKP))
 (29 29 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (28 28 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (27 1 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
 (26 26 (:TYPE-PRESCRIPTION AIGNET::GATESIMP-XOR-MODE-FIX))
 (22 10 (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
 (21 21 (:TYPE-PRESCRIPTION BITP))
 (20 20 (:REWRITE DEFAULT-<-2))
 (20 20 (:META CANCEL_PLUS-LESSP-CORRECT))
 (18 6 (:REWRITE AIGNET::GATESIMP-XOR-MODE-FIX-WHEN-GATESIMP-XOR-MODE-P))
 (12 12 (:TYPE-PRESCRIPTION AIGNET::GATESIMP-XOR-MODE-P))
 (10 10 (:REWRITE BITOPS::LOGBITP-OF-NEGATIVE-CONST))
 (10 10 (:REWRITE BITOPS::LOGBITP-OF-MASK))
 (10 10 (:REWRITE BITOPS::LOGBITP-OF-CONST-SPLIT))
 (10 10 (:REWRITE BITOPS::LOGBITP-OF-CONST))
 (10 10 (:META BITOPS::OPEN-LOGBITP-OF-CONST-LITE-META))
 (8 8 (:REWRITE NFIX-WHEN-NOT-NATP))
 (8 8 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (8 8 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (8 2 (:REWRITE NATP-WHEN-GTE-0))
 (2 2 (:REWRITE NATP-WHEN-INTEGERP))
 (2 2 (:REWRITE NATP-RW))
 )
(AIGNET::GATESIMP-DEBUG)
(AIGNET::GATESIMP->LEVEL-BOUND)
(AIGNET::GATESIMP->XOR-MODE-BOUND)
(AIGNET::DEFAULT-GATESIMP)
