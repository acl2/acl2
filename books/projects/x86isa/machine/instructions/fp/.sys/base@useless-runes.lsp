(X86ISA::FP-ROUND-OVERFLOW-GENERIC)
(X86ISA::INTEGERP-FP-ROUND-OVERFLOW-GENERIC-0)
(X86ISA::INTEGERP-FP-ROUND-OVERFLOW-GENERIC-1
 (36 9 (:REWRITE DEFAULT-+-2))
 (18 18 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (9 9 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (9 9 (:REWRITE DEFAULT-<-2))
 (9 9 (:REWRITE DEFAULT-<-1))
 (9 9 (:REWRITE DEFAULT-+-1))
 (9 9 (:META CANCEL_PLUS-LESSP-CORRECT))
 (6 6 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (6 6 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(X86ISA::INTEGERP-FP-ROUND-OVERFLOW-GENERIC-2
 (36 9 (:REWRITE DEFAULT-+-2))
 (18 18 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (9 9 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (9 9 (:REWRITE DEFAULT-<-2))
 (9 9 (:REWRITE DEFAULT-<-1))
 (9 9 (:REWRITE DEFAULT-+-1))
 (9 9 (:META CANCEL_PLUS-LESSP-CORRECT))
 (6 6 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (6 6 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(X86ISA::FP-ENCODE-INTEGER)
(X86ISA::INTEGERP-FP-ENCODE-INTEGER)
(X86ISA::FP-DECODE)
(X86ISA::N01P-FP-DECODE-SIGN-BIT
 (98 3 (:REWRITE LOGHEAD-IDENTITY))
 (80 3 (:REWRITE FTY::BITP-WHEN-UNSIGNED-BYTE-P-1))
 (72 2 (:REWRITE BITOPS::LOGBITP-NONZERO-OF-BIT))
 (72 1 (:REWRITE BITOPS::LOGBITP-OF-LOGHEAD-OUT-OF-BOUNDS))
 (42 28 (:REWRITE DEFAULT-<-2))
 (36 5 (:REWRITE NFIX-WHEN-NATP))
 (36 2 (:REWRITE NATP-POSP--1))
 (35 1 (:REWRITE LOGTAIL-IDENTITY))
 (34 28 (:REWRITE DEFAULT-<-1))
 (29 29 (:META CANCEL_PLUS-LESSP-CORRECT))
 (26 5 (:REWRITE NFIX-WHEN-NOT-NATP))
 (24 24 (:TYPE-PRESCRIPTION NFIX))
 (22 4 (:REWRITE FTY::UNSIGNED-BYTE-P-1-WHEN-BITP))
 (21 2 (:REWRITE POSP-REDEFINITION))
 (19 19 (:TYPE-PRESCRIPTION NATP))
 (19 1 (:REWRITE BITOPS::LOGBITP-OF-LOGHEAD-IN-BOUNDS))
 (16 12 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (16 8 (:TYPE-PRESCRIPTION BITOPS::LOGTAIL-NATP))
 (16 1 (:LINEAR LOGHEAD-UPPER-BOUND))
 (13 3 (:LINEAR EXPT->-1))
 (12 5 (:REWRITE DEFAULT-+-2))
 (12 1 (:REWRITE UNSIGNED-BYTE-P-OF-LOGHEAD))
 (11 2 (:REWRITE NATP-POSP))
 (10 10 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (10 4 (:REWRITE NATP-WHEN-GTE-0))
 (9 1 (:REWRITE UNSIGNED-BYTE-P-OF-LOGTAIL))
 (8 8 (:TYPE-PRESCRIPTION LOGTAIL-TYPE))
 (8 8 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (7 5 (:REWRITE DEFAULT-+-1))
 (7 4 (:REWRITE ZP-WHEN-GT-0))
 (6 6 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (6 6 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (6 6 (:LINEAR EXPT-IS-INCREASING-FOR-BASE>1))
 (6 2 (:REWRITE BITOPS::LOGBITP-WHEN-BITMASKP))
 (5 1 (:REWRITE UNSIGNED-BYTE-P-LOGHEAD))
 (4 4 (:TYPE-PRESCRIPTION BITMASKP$INLINE))
 (4 4 (:REWRITE ZP-WHEN-INTEGERP))
 (4 4 (:REWRITE ZP-OPEN))
 (4 4 (:REWRITE NATP-WHEN-INTEGERP))
 (4 4 (:REWRITE NATP-RW))
 (3 3 (:REWRITE INEQUALITY-WITH-NFIX-HYP-1))
 (3 3 (:LINEAR BITOPS::EXPT-2-LOWER-BOUND-BY-LOGBITP))
 (2 2 (:TYPE-PRESCRIPTION ZP))
 (2 2 (:TYPE-PRESCRIPTION INTEGER-RANGE-P))
 (2 2 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (2 2 (:REWRITE POSP-RW))
 (2 2 (:REWRITE BITOPS::NORMALIZE-LOGBITP-WHEN-MODS-EQUAL))
 (2 2 (:REWRITE INEQUALITY-WITH-NFIX-HYP-2))
 (1 1 (:REWRITE EXPONENTS-ADD-FOR-NONNEG-EXPONENTS))
 (1 1 (:REWRITE EXPONENTS-ADD))
 (1 1 (:REWRITE EQUAL-CONSTANT-+))
 )
(X86ISA::NATP-EXP-FP-DECODE
 (341 7 (:DEFINITION UNSIGNED-BYTE-P))
 (309 3 (:REWRITE LOGHEAD-IDENTITY))
 (297 7 (:DEFINITION INTEGER-RANGE-P))
 (267 1 (:REWRITE UNSIGNED-BYTE-P-OF-LOGTAIL))
 (116 2 (:REWRITE UNSIGNED-BYTE-P-PLUS))
 (72 2 (:REWRITE BITOPS::LOGBITP-NONZERO-OF-BIT))
 (72 1 (:REWRITE BITOPS::LOGBITP-OF-LOGHEAD-OUT-OF-BOUNDS))
 (65 7 (:LINEAR EXPT->-1))
 (65 2 (:REWRITE FTY::BITP-WHEN-UNSIGNED-BYTE-P-1))
 (62 33 (:REWRITE DEFAULT-<-2))
 (62 1 (:LINEAR X*Y>1-POSITIVE))
 (54 54 (:TYPE-PRESCRIPTION NFIX))
 (45 6 (:REWRITE NFIX-WHEN-NATP))
 (39 39 (:META CANCEL_PLUS-LESSP-CORRECT))
 (39 33 (:REWRITE DEFAULT-<-1))
 (35 1 (:REWRITE LOGTAIL-IDENTITY))
 (32 6 (:REWRITE NFIX-WHEN-NOT-NATP))
 (28 22 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (24 2 (:REWRITE NFIX-POSITIVE-TO-NON-ZP))
 (22 22 (:TYPE-PRESCRIPTION IFIX))
 (21 9 (:REWRITE ZP-WHEN-GT-0))
 (21 3 (:REWRITE IFIX-NEGATIVE-TO-NEGP))
 (20 3 (:REWRITE NATP-POSP))
 (19 7 (:REWRITE NATP-WHEN-GTE-0))
 (19 1 (:REWRITE BITOPS::LOGBITP-OF-LOGHEAD-IN-BOUNDS))
 (17 2 (:REWRITE EXPONENTS-ADD))
 (16 1 (:LINEAR LOGHEAD-UPPER-BOUND))
 (14 14 (:LINEAR EXPT-IS-INCREASING-FOR-BASE>1))
 (13 6 (:REWRITE DEFAULT-+-2))
 (12 3 (:REWRITE NEGP-WHEN-LESS-THAN-0))
 (12 1 (:REWRITE UNSIGNED-BYTE-P-OF-LOGHEAD))
 (10 10 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (9 9 (:REWRITE ZP-WHEN-INTEGERP))
 (9 9 (:REWRITE ZP-OPEN))
 (8 8 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (8 8 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (7 7 (:REWRITE NATP-WHEN-INTEGERP))
 (7 7 (:REWRITE NATP-RW))
 (7 6 (:REWRITE DEFAULT-+-1))
 (6 6 (:TYPE-PRESCRIPTION BITP))
 (6 6 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (6 6 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (6 6 (:LINEAR BITOPS::EXPT-2-LOWER-BOUND-BY-LOGBITP))
 (6 2 (:REWRITE BITOPS::LOGBITP-WHEN-BITMASKP))
 (5 5 (:REWRITE INEQUALITY-WITH-NFIX-HYP-1))
 (5 1 (:REWRITE UNSIGNED-BYTE-P-LOGHEAD))
 (5 1 (:REWRITE DEFAULT-*-2))
 (4 4 (:TYPE-PRESCRIPTION ZP))
 (4 4 (:TYPE-PRESCRIPTION BITMASKP$INLINE))
 (4 2 (:REWRITE FTY::UNSIGNED-BYTE-P-1-WHEN-BITP))
 (4 1 (:REWRITE DEFAULT-*-1))
 (3 3 (:TYPE-PRESCRIPTION NEGP))
 (3 3 (:REWRITE POSP-RW))
 (3 3 (:REWRITE NEGP-WHEN-INTEGERP))
 (2 2 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (2 2 (:REWRITE BITOPS::NORMALIZE-LOGBITP-WHEN-MODS-EQUAL))
 (2 2 (:REWRITE INEQUALITY-WITH-NFIX-HYP-2))
 (1 1 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
 (1 1 (:REWRITE IFIX-WHEN-INTEGERP))
 (1 1 (:REWRITE EXPONENTS-ADD-FOR-NONNEG-EXPONENTS))
 (1 1 (:REWRITE EQUAL-CONSTANT-+))
 )
(X86ISA::EXP-WIDTH-WIDE-EXP-FROM-FP-DECODE-LEMMA
 (2562 12 (:REWRITE LOGHEAD-IDENTITY))
 (2502 10 (:REWRITE UNSIGNED-BYTE-P-OF-LOGTAIL))
 (1069 20 (:REWRITE UNSIGNED-BYTE-P-PLUS))
 (543 10 (:LINEAR X*Y>1-POSITIVE))
 (372 157 (:REWRITE DEFAULT-<-2))
 (326 326 (:TYPE-PRESCRIPTION NFIX))
 (245 7 (:REWRITE LOGTAIL-IDENTITY))
 (240 20 (:REWRITE NFIX-POSITIVE-TO-NON-ZP))
 (213 213 (:TYPE-PRESCRIPTION IFIX))
 (210 30 (:REWRITE IFIX-NEGATIVE-TO-NEGP))
 (193 157 (:REWRITE DEFAULT-<-1))
 (164 140 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (161 11 (:REWRITE EXPONENTS-ADD))
 (129 18 (:REWRITE NFIX-WHEN-NATP))
 (123 48 (:REWRITE ZP-WHEN-GT-0))
 (120 30 (:REWRITE NEGP-WHEN-LESS-THAN-0))
 (89 18 (:REWRITE NFIX-WHEN-NOT-NATP))
 (76 76 (:LINEAR EXPT-IS-INCREASING-FOR-BASE>1))
 (72 2 (:REWRITE BITOPS::LOGBITP-NONZERO-OF-BIT))
 (72 1 (:REWRITE BITOPS::LOGBITP-OF-LOGHEAD-OUT-OF-BOUNDS))
 (65 2 (:REWRITE FTY::BITP-WHEN-UNSIGNED-BYTE-P-1))
 (60 24 (:REWRITE NATP-WHEN-GTE-0))
 (51 51 (:TYPE-PRESCRIPTION NATP))
 (50 10 (:REWRITE DEFAULT-*-2))
 (48 48 (:REWRITE ZP-WHEN-INTEGERP))
 (48 48 (:REWRITE ZP-OPEN))
 (43 18 (:REWRITE DEFAULT-+-2))
 (42 42 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (40 10 (:REWRITE DEFAULT-*-1))
 (36 2 (:REWRITE NATP-POSP--1))
 (35 35 (:LINEAR BITOPS::EXPT-2-LOWER-BOUND-BY-LOGBITP))
 (34 3 (:REWRITE BITOPS::EXPT-2-LOWER-BOUND-BY-LOGBITP))
 (30 30 (:TYPE-PRESCRIPTION NEGP))
 (30 30 (:REWRITE NEGP-WHEN-INTEGERP))
 (29 2 (:REWRITE BITOPS::LOGBITP-OF-LOGHEAD-IN-BOUNDS))
 (24 24 (:REWRITE NATP-WHEN-INTEGERP))
 (24 24 (:REWRITE NATP-RW))
 (23 23 (:REWRITE INEQUALITY-WITH-NFIX-HYP-1))
 (20 3 (:REWRITE NATP-POSP))
 (19 18 (:REWRITE DEFAULT-+-1))
 (19 5 (:REWRITE BITOPS::LOGBITP-WHEN-BITMASKP))
 (12 6 (:TYPE-PRESCRIPTION X86ISA::NATP-EXP-FP-DECODE))
 (12 1 (:REWRITE UNSIGNED-BYTE-P-OF-LOGHEAD))
 (10 10 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
 (10 10 (:REWRITE IFIX-WHEN-INTEGERP))
 (10 10 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (10 10 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (9 9 (:TYPE-PRESCRIPTION BITMASKP$INLINE))
 (8 8 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (6 6 (:TYPE-PRESCRIPTION BITP))
 (5 5 (:REWRITE BITOPS::NORMALIZE-LOGBITP-WHEN-MODS-EQUAL))
 (5 1 (:REWRITE UNSIGNED-BYTE-P-LOGHEAD))
 (4 2 (:REWRITE FTY::UNSIGNED-BYTE-P-1-WHEN-BITP))
 (3 3 (:REWRITE POSP-RW))
 (3 3 (:REWRITE EQUAL-CONSTANT-+))
 (2 2 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (2 2 (:REWRITE INEQUALITY-WITH-NFIX-HYP-2))
 (1 1 (:REWRITE EXPONENTS-ADD-FOR-NONNEG-EXPONENTS))
 )
(X86ISA::N01P-IMPLICIT-BIT-FP-DECODE
 (98 3 (:REWRITE LOGHEAD-IDENTITY))
 (80 3 (:REWRITE FTY::BITP-WHEN-UNSIGNED-BYTE-P-1))
 (72 2 (:REWRITE BITOPS::LOGBITP-NONZERO-OF-BIT))
 (72 1 (:REWRITE BITOPS::LOGBITP-OF-LOGHEAD-OUT-OF-BOUNDS))
 (42 28 (:REWRITE DEFAULT-<-2))
 (36 5 (:REWRITE NFIX-WHEN-NATP))
 (36 2 (:REWRITE NATP-POSP--1))
 (35 1 (:REWRITE LOGTAIL-IDENTITY))
 (34 28 (:REWRITE DEFAULT-<-1))
 (29 29 (:META CANCEL_PLUS-LESSP-CORRECT))
 (26 5 (:REWRITE NFIX-WHEN-NOT-NATP))
 (24 24 (:TYPE-PRESCRIPTION NFIX))
 (22 4 (:REWRITE FTY::UNSIGNED-BYTE-P-1-WHEN-BITP))
 (21 2 (:REWRITE POSP-REDEFINITION))
 (19 19 (:TYPE-PRESCRIPTION NATP))
 (19 1 (:REWRITE BITOPS::LOGBITP-OF-LOGHEAD-IN-BOUNDS))
 (16 12 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (16 8 (:TYPE-PRESCRIPTION BITOPS::LOGTAIL-NATP))
 (16 1 (:LINEAR LOGHEAD-UPPER-BOUND))
 (13 3 (:LINEAR EXPT->-1))
 (12 5 (:REWRITE DEFAULT-+-2))
 (12 1 (:REWRITE UNSIGNED-BYTE-P-OF-LOGHEAD))
 (11 2 (:REWRITE NATP-POSP))
 (10 10 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (10 4 (:REWRITE NATP-WHEN-GTE-0))
 (9 1 (:REWRITE UNSIGNED-BYTE-P-OF-LOGTAIL))
 (8 8 (:TYPE-PRESCRIPTION LOGTAIL-TYPE))
 (8 8 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (7 5 (:REWRITE DEFAULT-+-1))
 (7 4 (:REWRITE ZP-WHEN-GT-0))
 (6 6 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (6 6 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (6 6 (:LINEAR EXPT-IS-INCREASING-FOR-BASE>1))
 (6 2 (:REWRITE BITOPS::LOGBITP-WHEN-BITMASKP))
 (5 1 (:REWRITE UNSIGNED-BYTE-P-LOGHEAD))
 (4 4 (:TYPE-PRESCRIPTION BITMASKP$INLINE))
 (4 4 (:REWRITE ZP-WHEN-INTEGERP))
 (4 4 (:REWRITE ZP-OPEN))
 (4 4 (:REWRITE NATP-WHEN-INTEGERP))
 (4 4 (:REWRITE NATP-RW))
 (3 3 (:REWRITE INEQUALITY-WITH-NFIX-HYP-1))
 (3 3 (:LINEAR BITOPS::EXPT-2-LOWER-BOUND-BY-LOGBITP))
 (2 2 (:TYPE-PRESCRIPTION ZP))
 (2 2 (:TYPE-PRESCRIPTION INTEGER-RANGE-P))
 (2 2 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (2 2 (:REWRITE POSP-RW))
 (2 2 (:REWRITE BITOPS::NORMALIZE-LOGBITP-WHEN-MODS-EQUAL))
 (2 2 (:REWRITE INEQUALITY-WITH-NFIX-HYP-2))
 (1 1 (:REWRITE EXPONENTS-ADD-FOR-NONNEG-EXPONENTS))
 (1 1 (:REWRITE EXPONENTS-ADD))
 (1 1 (:REWRITE EQUAL-CONSTANT-+))
 )
(X86ISA::NATP-FRAC-FROM-FP-DECODE
 (130 5 (:DEFINITION UNSIGNED-BYTE-P))
 (116 5 (:DEFINITION INTEGER-RANGE-P))
 (95 2 (:REWRITE LOGHEAD-IDENTITY))
 (37 1 (:REWRITE LOGTAIL-IDENTITY))
 (32 2 (:REWRITE BITOPS::LOGBITP-NONZERO-OF-BIT))
 (26 17 (:REWRITE DEFAULT-<-2))
 (26 2 (:REWRITE FTY::BITP-WHEN-UNSIGNED-BYTE-P-1))
 (20 17 (:REWRITE DEFAULT-<-1))
 (19 19 (:META CANCEL_PLUS-LESSP-CORRECT))
 (18 2 (:LINEAR EXPT->-1))
 (16 8 (:TYPE-PRESCRIPTION BITOPS::LOGTAIL-NATP))
 (15 14 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (12 3 (:REWRITE NATP-WHEN-GTE-0))
 (11 1 (:REWRITE BITOPS::LOGBITP-OF-LOGHEAD-OUT-OF-BOUNDS))
 (9 5 (:REWRITE DEFAULT-+-2))
 (9 3 (:REWRITE BITOPS::LOGBITP-WHEN-BITMASKP))
 (9 1 (:REWRITE UNSIGNED-BYTE-P-OF-LOGTAIL))
 (9 1 (:REWRITE NATP-POSP))
 (8 8 (:TYPE-PRESCRIPTION LOGTAIL-TYPE))
 (6 6 (:TYPE-PRESCRIPTION BITP))
 (6 6 (:TYPE-PRESCRIPTION BITMASKP$INLINE))
 (6 6 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (6 6 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (6 5 (:REWRITE DEFAULT-+-1))
 (6 4 (:REWRITE NFIX-WHEN-NOT-NATP))
 (5 5 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (5 5 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (4 4 (:LINEAR EXPT-IS-INCREASING-FOR-BASE>1))
 (4 2 (:REWRITE FTY::UNSIGNED-BYTE-P-1-WHEN-BITP))
 (4 1 (:REWRITE ZP-WHEN-GT-0))
 (3 3 (:REWRITE BITOPS::NORMALIZE-LOGBITP-WHEN-MODS-EQUAL))
 (3 3 (:REWRITE NATP-WHEN-INTEGERP))
 (3 3 (:REWRITE NATP-RW))
 (2 2 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 2 (:LINEAR BITOPS::EXPT-2-LOWER-BOUND-BY-LOGBITP))
 (1 1 (:REWRITE ZP-WHEN-INTEGERP))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE POSP-RW))
 (1 1 (:REWRITE EXPONENTS-ADD-FOR-NONNEG-EXPONENTS))
 (1 1 (:REWRITE EXPONENTS-ADD))
 (1 1 (:REWRITE EQUAL-CONSTANT-+))
 )
(X86ISA::FRAC-WIDTH-WIDE-FRAC-FROM-FP-DECODE-LEMMA
 (1160 21 (:REWRITE LOGHEAD-IDENTITY))
 (521 11 (:REWRITE UNSIGNED-BYTE-P-OF-LOGTAIL))
 (227 108 (:REWRITE DEFAULT-<-2))
 (222 6 (:REWRITE UNSIGNED-BYTE-P-PLUS))
 (198 6 (:REWRITE LOGTAIL-IDENTITY))
 (141 108 (:REWRITE DEFAULT-<-1))
 (131 130 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (124 124 (:META CANCEL_PLUS-LESSP-CORRECT))
 (102 7 (:REWRITE BITOPS::EXPT-2-LOWER-BOUND-BY-LOGBITP))
 (96 48 (:TYPE-PRESCRIPTION BITOPS::LOGTAIL-NATP))
 (63 63 (:TYPE-PRESCRIPTION IFIX))
 (63 9 (:REWRITE IFIX-NEGATIVE-TO-NEGP))
 (63 3 (:LINEAR X*Y>1-POSITIVE))
 (48 48 (:TYPE-PRESCRIPTION LOGTAIL-TYPE))
 (40 4 (:REWRITE EXPONENTS-ADD))
 (36 36 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (36 9 (:REWRITE NEGP-WHEN-LESS-THAN-0))
 (34 34 (:LINEAR EXPT-IS-INCREASING-FOR-BASE>1))
 (34 10 (:REWRITE BITOPS::LOGBITP-WHEN-BITMASKP))
 (32 2 (:REWRITE BITOPS::LOGBITP-NONZERO-OF-BIT))
 (28 7 (:REWRITE ZP-WHEN-GT-0))
 (26 2 (:REWRITE FTY::BITP-WHEN-UNSIGNED-BYTE-P-1))
 (20 18 (:REWRITE NFIX-WHEN-NOT-NATP))
 (20 10 (:REWRITE DEFAULT-+-2))
 (19 19 (:TYPE-PRESCRIPTION BITMASKP$INLINE))
 (19 7 (:REWRITE NATP-WHEN-GTE-0))
 (17 17 (:LINEAR BITOPS::EXPT-2-LOWER-BOUND-BY-LOGBITP))
 (13 13 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (13 13 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (12 6 (:TYPE-PRESCRIPTION X86ISA::NATP-FRAC-FROM-FP-DECODE))
 (12 3 (:REWRITE DEFAULT-*-2))
 (12 3 (:REWRITE DEFAULT-*-1))
 (11 10 (:REWRITE DEFAULT-+-1))
 (11 1 (:REWRITE BITOPS::LOGBITP-OF-LOGHEAD-OUT-OF-BOUNDS))
 (10 10 (:REWRITE BITOPS::NORMALIZE-LOGBITP-WHEN-MODS-EQUAL))
 (9 9 (:TYPE-PRESCRIPTION NEGP))
 (9 9 (:REWRITE NEGP-WHEN-INTEGERP))
 (9 1 (:REWRITE NATP-POSP))
 (7 7 (:REWRITE ZP-WHEN-INTEGERP))
 (7 7 (:REWRITE ZP-OPEN))
 (7 7 (:REWRITE NATP-RW))
 (6 6 (:TYPE-PRESCRIPTION BITP))
 (6 6 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 4 (:REWRITE NATP-WHEN-INTEGERP))
 (4 2 (:TYPE-PRESCRIPTION X86ISA::FRAC-WIDTH-WIDE-FRAC-FROM-FP-DECODE-LEMMA))
 (4 2 (:REWRITE FTY::UNSIGNED-BYTE-P-1-WHEN-BITP))
 (3 3 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
 (3 3 (:REWRITE IFIX-WHEN-INTEGERP))
 (2 2 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (1 1 (:REWRITE POSP-RW))
 (1 1 (:REWRITE EXPONENTS-ADD-FOR-NONNEG-EXPONENTS))
 )
(X86ISA::SSE-DAZ)
(X86ISA::NATP-SSE-DAZ-1
 (8 2 (:REWRITE NATP-WHEN-GTE-0))
 (2 2 (:REWRITE NATP-WHEN-INTEGERP))
 (2 2 (:REWRITE NATP-RW))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:META CANCEL_PLUS-LESSP-CORRECT))
 (1 1 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (1 1 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(X86ISA::NATP-SSE-DAZ-2
 (8 2 (:REWRITE NATP-WHEN-GTE-0))
 (2 2 (:REWRITE NATP-WHEN-INTEGERP))
 (2 2 (:REWRITE NATP-RW))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:META CANCEL_PLUS-LESSP-CORRECT))
 (1 1 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (1 1 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(X86ISA::DENORMAL-EXCEPTION)
(X86ISA::FP-TO-RAT
 (23 23 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 )
(X86ISA::RATIONALP-FP-TO-RAT
 (116 17 (:REWRITE DEFAULT-*-2))
 (100 4 (:REWRITE /R-WHEN-ABS-NUMERATOR=1))
 (88 17 (:REWRITE DEFAULT-*-1))
 (33 6 (:REWRITE DEFAULT-UNARY-MINUS))
 (32 16 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (28 4 (:REWRITE EXPONENTS-ADD-FOR-NONNEG-EXPONENTS))
 (26 2 (:REWRITE NUMERATOR-WHEN-INTEGERP))
 (20 4 (:REWRITE <-MINUS-ZERO))
 (18 2 (:REWRITE DEFAULT-UNARY-/))
 (17 17 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (13 8 (:REWRITE DEFAULT-<-2))
 (12 12 (:META CANCEL_PLUS-LESSP-CORRECT))
 (12 8 (:REWRITE DEFAULT-<-1))
 (10 7 (:REWRITE DEFAULT-+-2))
 (10 2 (:REWRITE DEFAULT-NUMERATOR))
 (9 9 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (8 8 (:REWRITE FOLD-CONSTS-IN-*))
 (7 7 (:REWRITE DEFAULT-+-1))
 (6 6 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (6 6 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (6 4 (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
 (4 4 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (4 4 (:REWRITE EXPONENTS-ADD))
 )
(X86ISA::RAT-TO-FP)
(X86ISA::RAT-TO-FP)
(X86ISA::INTEGERP-RAT-TO-FP)
(X86ISA::MAKE-SPECIAL-BP)
(X86ISA::INTEGERP-MAKE-SPECIAL-BP-0)
(X86ISA::INTEGERP-MAKE-SPECIAL-BP-1
 (28 8 (:REWRITE DEFAULT-+-2))
 (20 12 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (14 8 (:REWRITE DEFAULT-+-1))
 (8 8 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (8 8 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (8 8 (:META CANCEL_PLUS-LESSP-CORRECT))
 (8 6 (:REWRITE DEFAULT-<-1))
 (6 6 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (6 6 (:REWRITE DEFAULT-<-2))
 (6 6 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (6 6 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (2 2 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP))
 (2 2 (:REWRITE EXPONENTS-ADD-FOR-NONNEG-EXPONENTS))
 (2 2 (:REWRITE EXPONENTS-ADD))
 )
(X86ISA::INTEGERP-MAKE-SPECIAL-BP-2)
(X86ISA::INTEGERP-MAKE-SPECIAL-BP-3
 (27 8 (:REWRITE DEFAULT-+-2))
 (20 12 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (13 8 (:REWRITE DEFAULT-+-1))
 (10 10 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (8 8 (:META CANCEL_PLUS-LESSP-CORRECT))
 (8 6 (:REWRITE DEFAULT-<-1))
 (6 6 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (6 6 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (6 6 (:REWRITE DEFAULT-<-2))
 (6 6 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (6 6 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (2 2 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP))
 (2 2 (:REWRITE EXPONENTS-ADD-FOR-NONNEG-EXPONENTS))
 (2 2 (:REWRITE EXPONENTS-ADD))
 )
(X86ISA::CONVERT-RC-TO-MODE$INLINE)
(X86ISA::RAT-ROUND
 (5 5 (:TYPE-PRESCRIPTION RTL::RND-POSITIVE))
 (5 5 (:TYPE-PRESCRIPTION RTL::RND-NON-POS))
 (5 5 (:TYPE-PRESCRIPTION RTL::RND-NEGATIVE))
 )
(X86ISA::RAT-ROUND
 (5 5 (:TYPE-PRESCRIPTION RTL::RND-POSITIVE))
 (5 5 (:TYPE-PRESCRIPTION RTL::RND-NON-POS))
 (5 5 (:TYPE-PRESCRIPTION RTL::RND-NEGATIVE))
 )
(X86ISA::RATIONALP-RAT-ROUND)
