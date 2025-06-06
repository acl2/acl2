(X86ISA::SSE-CMP-SPECIAL
 (18 2 (:REWRITE NATP-POSP))
 (17 3 (:REWRITE FTY::UNSIGNED-BYTE-P-1-WHEN-BITP))
 (13 1 (:REWRITE FTY::BITP-WHEN-UNSIGNED-BYTE-P-1))
 (10 10 (:REWRITE DEFAULT-<-2))
 (10 10 (:REWRITE DEFAULT-<-1))
 (10 10 (:META CANCEL_PLUS-LESSP-CORRECT))
 (8 2 (:REWRITE ZP-WHEN-GT-0))
 (8 2 (:REWRITE NATP-WHEN-GTE-0))
 (4 4 (:TYPE-PRESCRIPTION NATP))
 (3 3 (:TYPE-PRESCRIPTION BITP))
 (3 3 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (2 2 (:REWRITE ZP-WHEN-INTEGERP))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE POSP-RW))
 (2 2 (:REWRITE NATP-WHEN-INTEGERP))
 (2 2 (:REWRITE NATP-RW))
 )
(X86ISA::INTEGERP-SSE-CMP-SPECIAL-1
 (560 240 (:REWRITE DEFAULT-+-2))
 (320 240 (:REWRITE DEFAULT-+-1))
 (320 80 (:REWRITE EXPONENTS-ADD-FOR-NONNEG-EXPONENTS))
 (277 277 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (277 277 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (160 160 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (160 160 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (160 160 (:REWRITE DEFAULT-<-2))
 (160 160 (:REWRITE DEFAULT-<-1))
 (160 160 (:META CANCEL_PLUS-LESSP-CORRECT))
 (80 80 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (80 80 (:REWRITE FOLD-CONSTS-IN-+))
 (80 80 (:REWRITE EXPONENTS-ADD))
 )
(X86ISA::SSE-CMP
 (223 62 (:REWRITE DEFAULT-<-1))
 (216 62 (:REWRITE DEFAULT-<-2))
 (119 119 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (119 119 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (68 11 (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-32BITS-P))
 (62 62 (:META CANCEL_PLUS-LESSP-CORRECT))
 (62 14 (:REWRITE NATP-WHEN-GTE-0))
 (48 24 (:TYPE-PRESCRIPTION X86ISA::NATP-FRAC-FROM-FP-DECODE))
 (46 2 (:REWRITE NFIX-WHEN-NATP))
 (32 8 (:REWRITE ZP-WHEN-GT-0))
 (29 29 (:REWRITE X86ISA::MXCSRBITS->DAZ-OF-WRITE-WITH-MASK))
 (27 8 (:REWRITE X86ISA::32BITS-P-WHEN-UNSIGNED-BYTE-P))
 (24 2 (:REWRITE NFIX-WHEN-NOT-NATP))
 (22 14 (:REWRITE NATP-WHEN-INTEGERP))
 (22 14 (:REWRITE NATP-RW))
 (22 4 (:REWRITE DEFAULT-*-2))
 (18 2 (:REWRITE NATP-POSP))
 (17 17 (:TYPE-PRESCRIPTION X86ISA::32BITS-P))
 (13 13 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (12 12 (:REWRITE DEFAULT-+-2))
 (12 12 (:REWRITE DEFAULT-+-1))
 (10 4 (:REWRITE DEFAULT-*-1))
 (9 9 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (8 8 (:REWRITE ZP-WHEN-INTEGERP))
 (8 8 (:REWRITE ZP-OPEN))
 (8 8 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (6 6 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (4 4 (:REWRITE-QUOTED-CONSTANT BFIX-UNDER-BIT-EQUIV))
 (4 4 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE POSP-RW))
 (2 2 (:REWRITE X86ISA::MXCSRBITS->DM-OF-WRITE-WITH-MASK))
 (2 2 (:REWRITE FOLD-CONSTS-IN-*))
 (1 1 (:TYPE-PRESCRIPTION BITOPS::LOGNOT-NEGP))
 )
(X86ISA::INTEGERP-RESULT-SSE-CMP
 (11856 912 (:TYPE-PRESCRIPTION X86ISA::NATP-SSE-DAZ-2))
 (6384 6384 (:TYPE-PRESCRIPTION POSP))
 (5016 456 (:TYPE-PRESCRIPTION X86ISA::NATP-SSE-DAZ-1))
 (4560 2280 (:TYPE-PRESCRIPTION X86ISA::NATP-FRAC-FROM-FP-DECODE))
 (4560 2280 (:TYPE-PRESCRIPTION X86ISA::FRAC-WIDTH-WIDE-FRAC-FROM-FP-DECODE-LEMMA))
 (3648 1824 (:TYPE-PRESCRIPTION X86ISA::NATP-EXP-FP-DECODE))
 (1398 82 (:REWRITE DEFAULT-<-1))
 (1394 82 (:REWRITE DEFAULT-<-2))
 (1384 1384 (:TYPE-PRESCRIPTION NATP))
 (378 93 (:REWRITE LOGHEAD-IDENTITY))
 (152 19 (:DEFINITION UNSIGNED-BYTE-P))
 (141 141 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (141 141 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (133 19 (:DEFINITION INTEGER-RANGE-P))
 (110 110 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (101 101 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (95 19 (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-32BITS-P))
 (92 4 (:REWRITE NFIX-WHEN-NATP))
 (85 85 (:REWRITE X86ISA::MXCSRBITS->DAZ-OF-WRITE-WITH-MASK))
 (82 82 (:META CANCEL_PLUS-LESSP-CORRECT))
 (80 80 (:TYPE-PRESCRIPTION RTL::BIAS))
 (48 4 (:REWRITE NFIX-WHEN-NOT-NATP))
 (44 8 (:REWRITE NATP-WHEN-GTE-0))
 (38 38 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (38 38 (:TYPE-PRESCRIPTION X86ISA::32BITS-P))
 (38 19 (:REWRITE X86ISA::32BITS-P-WHEN-UNSIGNED-BYTE-P))
 (36 16 (:REWRITE DEFAULT-+-2))
 (24 8 (:REWRITE NATP-WHEN-INTEGERP))
 (24 8 (:REWRITE NATP-RW))
 (20 16 (:REWRITE DEFAULT-+-1))
 (19 19 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (16 4 (:REWRITE EXPONENTS-ADD-FOR-NONNEG-EXPONENTS))
 (12 12 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (8 8 (:REWRITE-QUOTED-CONSTANT BFIX-UNDER-BIT-EQUIV))
 (8 8 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (5 5 (:TYPE-PRESCRIPTION BITOPS::LOGNOT-NEGP))
 (4 4 (:REWRITE FOLD-CONSTS-IN-+))
 (4 4 (:REWRITE EXPONENTS-ADD))
 )
(X86ISA::N32P-MXCSR-SSE-CMP
 (8944 688 (:TYPE-PRESCRIPTION X86ISA::NATP-SSE-DAZ-2))
 (4816 4816 (:TYPE-PRESCRIPTION POSP))
 (3784 344 (:TYPE-PRESCRIPTION X86ISA::NATP-SSE-DAZ-1))
 (3440 1720 (:TYPE-PRESCRIPTION X86ISA::NATP-FRAC-FROM-FP-DECODE))
 (3440 1720 (:TYPE-PRESCRIPTION X86ISA::FRAC-WIDTH-WIDE-FRAC-FROM-FP-DECODE-LEMMA))
 (2752 1376 (:TYPE-PRESCRIPTION X86ISA::NATP-EXP-FP-DECODE))
 (1360 44 (:REWRITE DEFAULT-<-1))
 (1356 44 (:REWRITE DEFAULT-<-2))
 (587 119 (:REWRITE LOGHEAD-IDENTITY))
 (222 50 (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-32BITS-P))
 (162 162 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (162 162 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (149 43 (:REWRITE X86ISA::MXCSRBITS-P-WHEN-UNSIGNED-BYTE-P))
 (141 141 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (132 132 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (103 103 (:REWRITE X86ISA::MXCSRBITS->DAZ-OF-WRITE-WITH-MASK))
 (92 4 (:REWRITE NFIX-WHEN-NATP))
 (86 86 (:TYPE-PRESCRIPTION X86ISA::32BITS-P))
 (86 43 (:REWRITE X86ISA::32BITS-P-WHEN-UNSIGNED-BYTE-P))
 (80 80 (:TYPE-PRESCRIPTION RTL::BIAS))
 (54 54 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (48 4 (:REWRITE NFIX-WHEN-NOT-NATP))
 (44 44 (:META CANCEL_PLUS-LESSP-CORRECT))
 (44 8 (:REWRITE NATP-WHEN-GTE-0))
 (36 16 (:REWRITE DEFAULT-+-2))
 (24 8 (:REWRITE NATP-WHEN-INTEGERP))
 (24 8 (:REWRITE NATP-RW))
 (20 16 (:REWRITE DEFAULT-+-1))
 (16 4 (:REWRITE EXPONENTS-ADD-FOR-NONNEG-EXPONENTS))
 (13 13 (:REWRITE-QUOTED-CONSTANT BFIX-UNDER-BIT-EQUIV))
 (12 12 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (8 8 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (5 5 (:TYPE-PRESCRIPTION BITOPS::LOGNOT-NEGP))
 (4 4 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE))
 (4 4 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONZERO))
 (4 4 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP))
 (4 4 (:REWRITE FOLD-CONSTS-IN-+))
 (4 4 (:REWRITE EXPONENTS-ADD))
 )
(X86ISA::SP-SSE-CMP
 (17 17 (:REWRITE DEFAULT-<-2))
 (17 17 (:REWRITE DEFAULT-<-1))
 (17 17 (:META CANCEL_PLUS-LESSP-CORRECT))
 (8 8 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 )
(X86ISA::N32P-RESULT-SP-SSE-CMP
 (27 1 (:REWRITE LOGHEAD-IDENTITY))
 (11 11 (:TYPE-PRESCRIPTION X86ISA::INTEGERP-RESULT-SSE-CMP))
 (8 1 (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-32BITS-P))
 (3 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:TYPE-PRESCRIPTION X86ISA::32BITS-P))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:META CANCEL_PLUS-LESSP-CORRECT))
 (2 1 (:REWRITE X86ISA::32BITS-P-WHEN-UNSIGNED-BYTE-P))
 (1 1 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (1 1 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (1 1 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 )
(X86ISA::N32P-MXCSR-SP-SSE-CMP
 (12 1 (:REWRITE LOGHEAD-IDENTITY))
 (8 1 (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-32BITS-P))
 (3 3 (:TYPE-PRESCRIPTION X86ISA::INTEGERP-RESULT-SSE-CMP))
 (2 2 (:TYPE-PRESCRIPTION X86ISA::32BITS-P))
 (2 1 (:REWRITE X86ISA::32BITS-P-WHEN-UNSIGNED-BYTE-P))
 (1 1 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (1 1 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (1 1 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 )
(X86ISA::DP-SSE-CMP
 (32 4 (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-64BITS-P))
 (26 2 (:REWRITE X86ISA::64BITS-P-WHEN-UNSIGNED-BYTE-P))
 (17 17 (:REWRITE DEFAULT-<-2))
 (17 17 (:REWRITE DEFAULT-<-1))
 (17 17 (:META CANCEL_PLUS-LESSP-CORRECT))
 (8 8 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (6 6 (:TYPE-PRESCRIPTION X86ISA::64BITS-P))
 )
(X86ISA::N64P-RESULT-DP-SSE-CMP
 (27 1 (:REWRITE LOGHEAD-IDENTITY))
 (11 11 (:TYPE-PRESCRIPTION X86ISA::INTEGERP-RESULT-SSE-CMP))
 (8 1 (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-64BITS-P))
 (3 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:TYPE-PRESCRIPTION X86ISA::64BITS-P))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:META CANCEL_PLUS-LESSP-CORRECT))
 (2 1 (:REWRITE X86ISA::64BITS-P-WHEN-UNSIGNED-BYTE-P))
 (1 1 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (1 1 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (1 1 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 )
(X86ISA::N32P-MXCSR-DP-SSE-CMP
 (12 1 (:REWRITE LOGHEAD-IDENTITY))
 (8 1 (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-64BITS-P))
 (3 3 (:TYPE-PRESCRIPTION X86ISA::INTEGERP-RESULT-SSE-CMP))
 (2 2 (:TYPE-PRESCRIPTION X86ISA::64BITS-P))
 (2 1 (:REWRITE X86ISA::64BITS-P-WHEN-UNSIGNED-BYTE-P))
 (1 1 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (1 1 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (1 1 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 )
