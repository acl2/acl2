(X86ISA::CPUID-INFO-P
 (4 4 (:TYPE-PRESCRIPTION CONSP-ASSOC-EQUAL))
 )
(X86ISA::CPUID-INFO)
(X86ISA::HONSED-CPUID-INFO)
(X86ISA::CPUID-INFO->EAX$INLINE
 (4 4 (:DEFINITION ASSOC-EQUAL))
 )
(X86ISA::CPUID-INFO->EBX$INLINE
 (4 4 (:DEFINITION ASSOC-EQUAL))
 )
(X86ISA::CPUID-INFO->ECX$INLINE
 (4 4 (:DEFINITION ASSOC-EQUAL))
 )
(X86ISA::CPUID-INFO->EDX$INLINE
 (4 4 (:DEFINITION ASSOC-EQUAL))
 )
(X86ISA::CONSP-OF-CPUID-INFO)
(X86ISA::BOOLEANP-OF-CPUID-INFO-P)
(X86ISA::CPUID-INFO-P-OF-CPUID-INFO)
(X86ISA::CONSP-WHEN-CPUID-INFO-P)
(X86ISA::CPUID-INFO->EAX-OF-CPUID-INFO)
(X86ISA::CPUID-INFO->EBX-OF-CPUID-INFO)
(X86ISA::CPUID-INFO->ECX-OF-CPUID-INFO)
(X86ISA::CPUID-INFO->EDX-OF-CPUID-INFO)
(X86ISA::RETURN-TYPE-OF-CPUID-INFO->EAX)
(X86ISA::RETURN-TYPE-OF-CPUID-INFO->EBX)
(X86ISA::RETURN-TYPE-OF-CPUID-INFO->ECX)
(X86ISA::RETURN-TYPE-OF-CPUID-INFO->EDX)
(X86ISA::VALID-CPUID-INFO-LIST-P)
(X86ISA::GET-CPU-INFO
 (9 3 (:REWRITE NATP-WHEN-GTE-0))
 (6 6 (:REWRITE DEFAULT-CDR))
 (6 6 (:REWRITE DEFAULT-<-2))
 (6 6 (:REWRITE DEFAULT-<-1))
 (6 3 (:REWRITE NATP-WHEN-INTEGERP))
 (4 4 (:REWRITE DEFAULT-CAR))
 (4 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 2))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 1))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 2))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 1))
 (4 4 (:REWRITE CONSP-BY-LEN))
 (3 3 (:REWRITE X86ISA::INTEGERP-ADDR-RANGE-MEMBER))
 (2 2 (:REWRITE CONSP-OF-CDR-BY-LEN))
 )
(X86ISA::CPUID-INFO-P-GET-CPU-INFO-NONNIL
 (35 15 (:REWRITE DEFAULT-CAR))
 (27 7 (:REWRITE DEFAULT-CDR))
 (24 8 (:REWRITE NATP-WHEN-GTE-0))
 (17 17 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 2))
 (17 17 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 1))
 (17 17 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 2))
 (17 17 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 1))
 (17 17 (:REWRITE CONSP-BY-LEN))
 (16 8 (:REWRITE NATP-WHEN-INTEGERP))
 (8 8 (:REWRITE X86ISA::INTEGERP-ADDR-RANGE-MEMBER))
 (8 8 (:REWRITE DEFAULT-<-2))
 (8 8 (:REWRITE DEFAULT-<-1))
 (3 3 (:REWRITE DEFAULT-+-2))
 (3 3 (:REWRITE DEFAULT-+-1))
 )
(X86ISA::X86-CPUID
 (440 16 (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-SIB-P))
 (222 188 (:REWRITE DEFAULT-<-1))
 (188 188 (:REWRITE DEFAULT-<-2))
 (138 6 (:DEFINITION LEN))
 (132 12 (:REWRITE LEN-WHEN-ATOM))
 (70 70 (:REWRITE X86ISA::INTEGERP-ADDR-RANGE-MEMBER))
 (57 9 (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-RFLAGSBITS-P))
 (57 9 (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-EVEX-PREFIXES-P))
 (57 9 (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-32BITS-P))
 (48 16 (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-VEX3-BYTE2-P))
 (48 16 (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-VEX3-BYTE1-P))
 (48 16 (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-VEX2-BYTE1-P))
 (48 16 (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-MODR/M-P))
 (48 16 (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-EVEX-BYTE3-P))
 (48 16 (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-EVEX-BYTE2-P))
 (48 16 (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-EVEX-BYTE1-P))
 (48 16 (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-8BITS-P))
 (44 6 (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-31BITS-P))
 (42 20 (:REWRITE DEFAULT-+-2))
 (38 38 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (36 20 (:REWRITE DEFAULT-+-1))
 (30 4 (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-PREFIXES-P))
 (24 6 (:DEFINITION X86ISA::GET-CPU-INFO))
 (18 18 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 2))
 (18 18 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 1))
 (18 18 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 2))
 (18 18 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 1))
 (18 18 (:REWRITE CONSP-BY-LEN))
 (16 16 (:TYPE-PRESCRIPTION X86ISA::VEX3-BYTE2-P$INLINE))
 (16 16 (:TYPE-PRESCRIPTION X86ISA::VEX3-BYTE1-P$INLINE))
 (16 16 (:TYPE-PRESCRIPTION X86ISA::VEX2-BYTE1-P$INLINE))
 (16 16 (:TYPE-PRESCRIPTION X86ISA::EVEX-BYTE3-P$INLINE))
 (16 16 (:TYPE-PRESCRIPTION X86ISA::EVEX-BYTE2-P$INLINE))
 (16 16 (:TYPE-PRESCRIPTION X86ISA::EVEX-BYTE1-P$INLINE))
 (16 16 (:TYPE-PRESCRIPTION X86ISA::8BITS-P))
 (16 8 (:REWRITE X86ISA::VEX3-BYTE2-P-WHEN-UNSIGNED-BYTE-P))
 (16 8 (:REWRITE X86ISA::VEX3-BYTE1-P-WHEN-UNSIGNED-BYTE-P))
 (16 8 (:REWRITE X86ISA::VEX2-BYTE1-P-WHEN-UNSIGNED-BYTE-P))
 (16 8 (:REWRITE X86ISA::EVEX-BYTE3-P-WHEN-UNSIGNED-BYTE-P))
 (16 8 (:REWRITE X86ISA::EVEX-BYTE2-P-WHEN-UNSIGNED-BYTE-P))
 (16 8 (:REWRITE X86ISA::EVEX-BYTE1-P-WHEN-UNSIGNED-BYTE-P))
 (16 8 (:REWRITE X86ISA::8BITS-P-WHEN-UNSIGNED-BYTE-P))
 (12 12 (:TYPE-PRESCRIPTION X86ISA::RFLAGSBITS-P$INLINE))
 (12 12 (:TYPE-PRESCRIPTION X86ISA::EVEX-PREFIXES-P$INLINE))
 (12 12 (:TYPE-PRESCRIPTION X86ISA::32BITS-P))
 (12 12 (:TYPE-PRESCRIPTION X86ISA::31BITS-P))
 (12 6 (:REWRITE X86ISA::RFLAGSBITS-P-WHEN-UNSIGNED-BYTE-P))
 (12 6 (:REWRITE X86ISA::EVEX-PREFIXES-P-WHEN-UNSIGNED-BYTE-P))
 (12 6 (:REWRITE X86ISA::32BITS-P-WHEN-UNSIGNED-BYTE-P))
 (12 6 (:REWRITE X86ISA::31BITS-P-WHEN-UNSIGNED-BYTE-P))
 (10 10 (:REWRITE DEFAULT-CDR))
 (6 6 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (6 6 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (6 6 (:REWRITE X86ISA::SAME-PAGE-OFFSET-IMPLIES-SAME-LOGHEADS))
 (6 6 (:REWRITE X86ISA::LOGHEAD-ZERO-SMALLER))
 (6 6 (:REWRITE DEFAULT-CAR))
 (6 6 (:REWRITE CONSP-OF-CDR-BY-LEN))
 (6 2 (:DEFINITION X86ISA::VALID-CPUID-INFO-LIST-P))
 (4 4 (:LINEAR LEN-WHEN-PREFIXP))
 (2 2 (:LINEAR X86ISA::MEMBER-P-POS-VALUE))
 (2 2 (:LINEAR X86ISA::MEMBER-P-POS-1-VALUE))
 )
(X86ISA::X86P-OF-X86-CPUID
 (27 1 (:REWRITE LOGHEAD-IDENTITY))
 (16 1 (:DEFINITION UNSIGNED-BYTE-P))
 (15 1 (:DEFINITION INTEGER-RANGE-P))
 (12 1 (:DEFINITION LEN))
 (8 2 (:REWRITE LEN-WHEN-ATOM))
 (8 1 (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-31BITS-P))
 (5 3 (:REWRITE DEFAULT-+-2))
 (5 2 (:LINEAR X86ISA::N32P-RR32))
 (4 3 (:REWRITE DEFAULT-+-1))
 (4 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (2 2 (:TYPE-PRESCRIPTION X86ISA::31BITS-P))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 1 (:REWRITE X86ISA::31BITS-P-WHEN-UNSIGNED-BYTE-P))
 (1 1 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (1 1 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (1 1 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (1 1 (:REWRITE X86ISA::SAME-PAGE-OFFSET-IMPLIES-SAME-LOGHEADS))
 (1 1 (:REWRITE X86ISA::LOGHEAD-ZERO-SMALLER))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 2))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 1))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 2))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 1))
 (1 1 (:REWRITE CONSP-OF-CDR-BY-LEN))
 (1 1 (:REWRITE CONSP-BY-LEN))
 )
