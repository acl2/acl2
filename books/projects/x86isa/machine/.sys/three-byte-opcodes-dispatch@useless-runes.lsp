(X86ISA::FIRST-THREE-BYTE-OPCODE-EXECUTE
 (6352 289 (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-SIB-P))
 (5934 129 (:REWRITE X86ISA::SIB-P-WHEN-UNSIGNED-BYTE-P))
 (805 289 (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-VEX3-BYTE2-P))
 (805 289 (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-VEX3-BYTE1-P))
 (805 289 (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-VEX2-BYTE1-P))
 (805 289 (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-MODR/M-P))
 (805 289 (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-EVEX-BYTE3-P))
 (805 289 (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-EVEX-BYTE2-P))
 (805 289 (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-EVEX-BYTE1-P))
 (805 289 (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-8BITS-P))
 (387 387 (:TYPE-PRESCRIPTION X86ISA::SIB-P$INLINE))
 (356 356 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (288 64 (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-PREFIXES-P))
 (258 258 (:TYPE-PRESCRIPTION X86ISA::VEX3-BYTE2-P$INLINE))
 (258 258 (:TYPE-PRESCRIPTION X86ISA::VEX3-BYTE1-P$INLINE))
 (258 258 (:TYPE-PRESCRIPTION X86ISA::VEX2-BYTE1-P$INLINE))
 (258 258 (:TYPE-PRESCRIPTION X86ISA::MODR/M-P$INLINE))
 (258 258 (:TYPE-PRESCRIPTION X86ISA::EVEX-BYTE3-P$INLINE))
 (258 258 (:TYPE-PRESCRIPTION X86ISA::EVEX-BYTE2-P$INLINE))
 (258 258 (:TYPE-PRESCRIPTION X86ISA::EVEX-BYTE1-P$INLINE))
 (258 258 (:TYPE-PRESCRIPTION X86ISA::8BITS-P))
 (258 129 (:REWRITE X86ISA::VEX3-BYTE2-P-WHEN-UNSIGNED-BYTE-P))
 (258 129 (:REWRITE X86ISA::VEX3-BYTE1-P-WHEN-UNSIGNED-BYTE-P))
 (258 129 (:REWRITE X86ISA::VEX2-BYTE1-P-WHEN-UNSIGNED-BYTE-P))
 (258 129 (:REWRITE X86ISA::EVEX-BYTE3-P-WHEN-UNSIGNED-BYTE-P))
 (258 129 (:REWRITE X86ISA::EVEX-BYTE2-P-WHEN-UNSIGNED-BYTE-P))
 (258 129 (:REWRITE X86ISA::EVEX-BYTE1-P-WHEN-UNSIGNED-BYTE-P))
 (258 129 (:REWRITE X86ISA::8BITS-P-WHEN-UNSIGNED-BYTE-P))
 (96 64 (:REWRITE DEFAULT-<-2))
 (96 64 (:REWRITE DEFAULT-<-1))
 (64 64 (:REWRITE BITOPS::SIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-P-SMALLER))
 (64 64 (:REWRITE BITOPS::SIGNED-BYTE-P-WHEN-SIGNED-BYTE-P-SMALLER))
 (64 64 (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
 (64 64 (:REWRITE BITOPS::SIGNED-BYTE-P-INCR))
 (64 64 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (32 32 (:REWRITE X86ISA::INTEGERP-ADDR-RANGE-MEMBER))
 (6 6 (:REWRITE X86ISA::PREFIXES->LCK-OF-WRITE-WITH-MASK))
 (4 4 (:REWRITE X86ISA::PREFIXES->REP-OF-WRITE-WITH-MASK))
 (3 3 (:REWRITE X86ISA::SEGMENT-SELECTORBITS->RPL-OF-WRITE-WITH-MASK))
 (3 3 (:REWRITE X86ISA::MODR/M->MOD-OF-WRITE-WITH-MASK))
 )
(X86ISA::X86P-FIRST-THREE-BYTE-OPCODE-EXECUTE
 (10 10 (:REWRITE X86ISA::MODR/M->MOD-OF-WRITE-WITH-MASK))
 (10 5 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
 (9 9 (:REWRITE X86ISA::PREFIXES->LCK-OF-WRITE-WITH-MASK))
 (5 5 (:REWRITE X86ISA::SEGMENT-SELECTORBITS->RPL-OF-WRITE-WITH-MASK))
 (4 4 (:REWRITE X86ISA::PREFIXES->REP-OF-WRITE-WITH-MASK))
 )
(X86ISA::SECOND-THREE-BYTE-OPCODE-EXECUTE
 (836 37 (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-SIB-P))
 (782 17 (:REWRITE X86ISA::SIB-P-WHEN-UNSIGNED-BYTE-P))
 (105 37 (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-VEX3-BYTE2-P))
 (105 37 (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-VEX3-BYTE1-P))
 (105 37 (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-VEX2-BYTE1-P))
 (105 37 (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-MODR/M-P))
 (105 37 (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-EVEX-BYTE3-P))
 (105 37 (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-EVEX-BYTE2-P))
 (105 37 (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-EVEX-BYTE1-P))
 (105 37 (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-8BITS-P))
 (51 51 (:TYPE-PRESCRIPTION X86ISA::SIB-P$INLINE))
 (45 45 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (36 8 (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-PREFIXES-P))
 (34 34 (:TYPE-PRESCRIPTION X86ISA::VEX3-BYTE2-P$INLINE))
 (34 34 (:TYPE-PRESCRIPTION X86ISA::VEX3-BYTE1-P$INLINE))
 (34 34 (:TYPE-PRESCRIPTION X86ISA::VEX2-BYTE1-P$INLINE))
 (34 34 (:TYPE-PRESCRIPTION X86ISA::EVEX-BYTE3-P$INLINE))
 (34 34 (:TYPE-PRESCRIPTION X86ISA::EVEX-BYTE2-P$INLINE))
 (34 34 (:TYPE-PRESCRIPTION X86ISA::EVEX-BYTE1-P$INLINE))
 (34 34 (:TYPE-PRESCRIPTION X86ISA::8BITS-P))
 (34 17 (:REWRITE X86ISA::VEX3-BYTE2-P-WHEN-UNSIGNED-BYTE-P))
 (34 17 (:REWRITE X86ISA::VEX3-BYTE1-P-WHEN-UNSIGNED-BYTE-P))
 (34 17 (:REWRITE X86ISA::VEX2-BYTE1-P-WHEN-UNSIGNED-BYTE-P))
 (34 17 (:REWRITE X86ISA::EVEX-BYTE3-P-WHEN-UNSIGNED-BYTE-P))
 (34 17 (:REWRITE X86ISA::EVEX-BYTE2-P-WHEN-UNSIGNED-BYTE-P))
 (34 17 (:REWRITE X86ISA::EVEX-BYTE1-P-WHEN-UNSIGNED-BYTE-P))
 (34 17 (:REWRITE X86ISA::8BITS-P-WHEN-UNSIGNED-BYTE-P))
 (24 4 (:REWRITE X86ISA::PREFIXES-P-WHEN-UNSIGNED-BYTE-P))
 (12 12 (:TYPE-PRESCRIPTION X86ISA::PREFIXES-P$INLINE))
 (12 8 (:REWRITE DEFAULT-<-2))
 (12 8 (:REWRITE DEFAULT-<-1))
 (8 8 (:REWRITE BITOPS::SIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-P-SMALLER))
 (8 8 (:REWRITE BITOPS::SIGNED-BYTE-P-WHEN-SIGNED-BYTE-P-SMALLER))
 (8 8 (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
 (8 8 (:REWRITE BITOPS::SIGNED-BYTE-P-INCR))
 (8 8 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 4 (:REWRITE X86ISA::INTEGERP-ADDR-RANGE-MEMBER))
 )
(X86ISA::X86P-SECOND-THREE-BYTE-OPCODE-EXECUTE)
(X86ISA::THREE-BYTE-OPCODE-DECODE-AND-EXECUTE
 (1960 80 (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-SIB-P))
 (1840 40 (:REWRITE X86ISA::SIB-P-WHEN-UNSIGNED-BYTE-P))
 (1112 420 (:DEFINITION X86ISA::APP-VIEW))
 (832 420 (:DEFINITION X86ISA::APP-VIEW$A))
 (784 180 (:REWRITE X86ISA::RME08-DOES-NOT-AFFECT-STATE-IN-APP-VIEW))
 (452 408 (:REWRITE DEFAULT-<-1))
 (428 168 (:REWRITE X86ISA::XR-RME08-STATE-SYS-VIEW))
 (414 168 (:REWRITE X86ISA::XR-RME08-STATE-APP-VIEW))
 (410 408 (:REWRITE DEFAULT-<-2))
 (360 80 (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-PREFIXES-P))
 (326 326 (:REWRITE DEFAULT-+-2))
 (326 326 (:REWRITE DEFAULT-+-1))
 (240 80 (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-VEX3-BYTE2-P))
 (240 80 (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-VEX3-BYTE1-P))
 (240 80 (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-VEX2-BYTE1-P))
 (240 80 (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-MODR/M-P))
 (240 80 (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-EVEX-BYTE3-P))
 (240 80 (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-EVEX-BYTE2-P))
 (240 80 (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-EVEX-BYTE1-P))
 (240 80 (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-8BITS-P))
 (236 56 (:REWRITE X86ISA::RML08-DOES-NOT-AFFECT-STATE-IN-APP-VIEW))
 (120 120 (:TYPE-PRESCRIPTION X86ISA::SIB-P$INLINE))
 (120 120 (:TYPE-PRESCRIPTION X86ISA::PREFIXES-P$INLINE))
 (102 102 (:REWRITE BITOPS::SIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-P-SMALLER))
 (102 102 (:REWRITE BITOPS::SIGNED-BYTE-P-WHEN-SIGNED-BYTE-P-SMALLER))
 (86 86 (:REWRITE X86ISA::SAME-PAGE-OFFSET-IMPLIES-SAME-LOGHEADS))
 (86 86 (:REWRITE X86ISA::RML08-VALUE-WHEN-ERROR))
 (86 86 (:REWRITE X86ISA::LOGHEAD-ZERO-SMALLER))
 (84 84 (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
 (84 84 (:REWRITE BITOPS::SIGNED-BYTE-P-INCR))
 (84 84 (:REWRITE X86ISA::INTEGERP-ADDR-RANGE-MEMBER))
 (80 80 (:TYPE-PRESCRIPTION X86ISA::VEX3-BYTE2-P$INLINE))
 (80 80 (:TYPE-PRESCRIPTION X86ISA::VEX3-BYTE1-P$INLINE))
 (80 80 (:TYPE-PRESCRIPTION X86ISA::VEX2-BYTE1-P$INLINE))
 (80 80 (:TYPE-PRESCRIPTION X86ISA::MODR/M-P$INLINE))
 (80 80 (:TYPE-PRESCRIPTION X86ISA::EVEX-BYTE3-P$INLINE))
 (80 80 (:TYPE-PRESCRIPTION X86ISA::EVEX-BYTE2-P$INLINE))
 (80 80 (:TYPE-PRESCRIPTION X86ISA::EVEX-BYTE1-P$INLINE))
 (80 80 (:TYPE-PRESCRIPTION X86ISA::8BITS-P))
 (80 40 (:REWRITE X86ISA::VEX3-BYTE2-P-WHEN-UNSIGNED-BYTE-P))
 (80 40 (:REWRITE X86ISA::VEX3-BYTE1-P-WHEN-UNSIGNED-BYTE-P))
 (80 40 (:REWRITE X86ISA::VEX2-BYTE1-P-WHEN-UNSIGNED-BYTE-P))
 (80 40 (:REWRITE X86ISA::MODR/M-P-WHEN-UNSIGNED-BYTE-P))
 (80 40 (:REWRITE X86ISA::EVEX-BYTE3-P-WHEN-UNSIGNED-BYTE-P))
 (80 40 (:REWRITE X86ISA::EVEX-BYTE2-P-WHEN-UNSIGNED-BYTE-P))
 (80 40 (:REWRITE X86ISA::EVEX-BYTE1-P-WHEN-UNSIGNED-BYTE-P))
 (80 40 (:REWRITE X86ISA::8BITS-P-WHEN-UNSIGNED-BYTE-P))
 (50 50 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (50 50 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (48 18 (:REWRITE X86ISA::XR-RML08-STATE-IN-SYS-VIEW))
 (48 18 (:REWRITE X86ISA::XR-RML08-STATE-IN-APP-VIEW))
 (20 20 (:REWRITE X86ISA::SIGNED-BYTE-P-LIMITS-THM))
 (20 20 (:REWRITE X86ISA::PREFIXES->ADR-OF-WRITE-WITH-MASK))
 (10 10 (:REWRITE X86ISA::RME08-WHEN-64-BIT-MODEP-AND-FS/GS))
 (4 4 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(X86ISA::X86P-THREE-BYTE-OPCODE-DECODE-AND-EXECUTE
 (1049 431 (:REWRITE X86ISA::RME08-DOES-NOT-AFFECT-STATE-IN-APP-VIEW))
 (778 286 (:DEFINITION X86ISA::APP-VIEW))
 (616 286 (:DEFINITION X86ISA::APP-VIEW$A))
 (321 119 (:REWRITE X86ISA::XR-RME08-STATE-SYS-VIEW))
 (300 119 (:REWRITE X86ISA::XR-RME08-STATE-APP-VIEW))
 (13 13 (:REWRITE X86ISA::PREFIXES->ADR-OF-WRITE-WITH-MASK))
 )
