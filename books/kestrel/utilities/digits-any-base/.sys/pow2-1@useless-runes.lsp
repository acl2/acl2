(DAB-DIGIT-LISTP-OF-2-REWRITE-UBYTE1-LISTP
 (169 24 (:REWRITE INTEGERP-OF-CAR-WHEN-INTEGER-LISTP))
 (128 11 (:DEFINITION INTEGER-LISTP))
 (92 10 (:REWRITE DAB-DIGITP-OF-CAR-WHEN-DAB-DIGIT-LISTP))
 (72 6 (:REWRITE UBYTE1P-OF-CAR-WHEN-UBYTE1-LISTP))
 (34 34 (:REWRITE DEFAULT-CAR))
 (34 34 (:REWRITE DAB-DIGIT-LISTP-WHEN-SUBSETP-EQUAL))
 (30 30 (:REWRITE UBYTE1-LISTP-WHEN-SUBSETP-EQUAL))
 (27 7 (:REWRITE UNSIGNED-BYTE-P-OF-CAR-WHEN-UNSIGNED-BYTE-LISTP))
 (24 12 (:REWRITE INTEGER-LISTP-OF-CDR-WHEN-INTEGER-LISTP))
 (22 22 (:REWRITE INTEGER-LISTP-WHEN-NOT-CONSP))
 (21 21 (:REWRITE DEFAULT-<-2))
 (21 21 (:REWRITE DEFAULT-<-1))
 (20 20 (:REWRITE DAB-DIGITP-WHEN-MEMBER-EQUAL-OF-DAB-DIGIT-LISTP))
 (19 4 (:REWRITE NATP-OF-CAR-WHEN-NAT-LISTP))
 (16 16 (:REWRITE DEFAULT-CDR))
 (14 2 (:REWRITE UBYTE1-LISTP-OF-CDR-WHEN-UBYTE1-LISTP))
 (14 2 (:REWRITE DAB-DIGIT-LISTP-OF-CDR-WHEN-DAB-DIGIT-LISTP))
 (12 12 (:REWRITE UBYTE1P-WHEN-MEMBER-EQUAL-OF-UBYTE1-LISTP))
 (10 10 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-LISTP))
 (7 7 (:REWRITE-QUOTED-CONSTANT DAB-BASE-FIX-UNDER-DAB-BASE-EQUIV))
 (5 5 (:REWRITE UNSIGNED-BYTE-LISTP-WHEN-TAKE-AND-NTHCDR))
 (5 5 (:REWRITE UNSIGNED-BYTE-LISTP-WHEN-NOT-CONSP))
 (3 3 (:REWRITE NATP-LISTP-WHEN-DAB-DIGIT-LISTP))
 (3 3 (:REWRITE NAT-LISTP-WHEN-UNSIGNED-BYTE-LISTP))
 (3 3 (:REWRITE NAT-LISTP-WHEN-NOT-CONSP))
 (2 2 (:DEFINITION NULL))
 )
(UBYTE1-LISTP-OF-NAT=>BENDIAN*
 (4 2 (:TYPE-PRESCRIPTION CONSP-OF-NAT=>BENDIAN*))
 (2 2 (:TYPE-PRESCRIPTION ZP))
 )
(UBYTE1-LISTP-OF-NAT=>BENDIAN+)
(UBYTE1-LISTP-OF-NAT=>BENDIAN
 (4 2 (:TYPE-PRESCRIPTION CONSP-OF-NAT=>BENDIAN))
 (2 2 (:TYPE-PRESCRIPTION ZP))
 )
(UBYTE1-LISTP-OF-NAT=>LENDIAN*
 (4 2 (:TYPE-PRESCRIPTION CONSP-OF-NAT=>LENDIAN*))
 (2 2 (:TYPE-PRESCRIPTION ZP))
 )
(UBYTE1-LISTP-OF-NAT=>LENDIAN+)
(UBYTE1-LISTP-OF-NAT=>LENDIAN
 (4 2 (:TYPE-PRESCRIPTION CONSP-OF-NAT=>LENDIAN))
 (2 2 (:TYPE-PRESCRIPTION ZP))
 )
