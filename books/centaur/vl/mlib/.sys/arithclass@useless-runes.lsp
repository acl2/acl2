(VL::VL-ARITHCLASS-P)
(VL::TYPE-WHEN-VL-ARITHCLASS-P)
(VL::VL-ARITHCLASS-P-POSSIBILITIES)
(VL::VL-ARITHCLASS-FIX$INLINE)
(VL::RETURN-TYPE-OF-VL-ARITHCLASS-FIX)
(VL::VL-ARITHCLASS-FIX-IDEMPOTENT)
(FTY::TMP-DEFFIXTYPE-IDEMPOTENT)
(VL::VL-ARITHCLASS-EQUIV$INLINE)
(VL::VL-ARITHCLASS-EQUIV-IS-AN-EQUIVALENCE)
(VL::VL-ARITHCLASS-EQUIV-IMPLIES-EQUAL-VL-ARITHCLASS-FIX-1)
(VL::VL-ARITHCLASS-FIX-UNDER-VL-ARITHCLASS-EQUIV)
(VL::VL-CORETYPE-ARITHCLASS)
(VL::VL-ARITHCLASS-P-OF-VL-CORETYPE-ARITHCLASS)
(VL::VL-CORETYPE-ARITHCLASS-OF-VL-COREDATATYPE-INFO-FIX-TYPINFO)
(VL::VL-CORETYPE-ARITHCLASS-VL-COREDATATYPE-INFO-EQUIV-CONGRUENCE-ON-TYPINFO)
(VL::VL-CORETYPE-ARITHCLASS-OF-BOOL-FIX-SIGNEDP
 (3 1 (:REWRITE BOOL-FIX-WHEN-BOOLEANP))
 (2 2 (:TYPE-PRESCRIPTION BOOLEANP))
 )
(VL::VL-CORETYPE-ARITHCLASS-IFF-CONGRUENCE-ON-SIGNEDP)
(VL::VL-DATATYPE-ARITHCLASS
 (24 6 (:DEFINITION EQ))
 (10 5 (:REWRITE VL::VL-DATATYPE-UDIMS-WHEN-VL-USERTYPE))
 (10 5 (:REWRITE VL::VL-DATATYPE-UDIMS-WHEN-VL-UNION))
 (10 5 (:REWRITE VL::VL-DATATYPE-UDIMS-WHEN-VL-STRUCT))
 (10 5 (:REWRITE VL::VL-DATATYPE-UDIMS-WHEN-VL-ENUM))
 (10 5 (:REWRITE VL::VL-DATATYPE-UDIMS-WHEN-VL-CORETYPE))
 (6 2 (:REWRITE DEFAULT-<-2))
 (6 2 (:REWRITE DEFAULT-<-1))
 (5 5 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-TRUELIST-ALISTP . 2))
 (5 5 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-TRUELIST-ALISTP . 1))
 (5 5 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 2))
 (5 5 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 1))
 (5 5 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-TRUELIST-ALISTP . 2))
 (5 5 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-TRUELIST-ALISTP . 1))
 (5 5 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-SYMBOL-ALISTP . 2))
 (5 5 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-SYMBOL-ALISTP . 1))
 )
(VL::VL-ARITHCLASS-P-OF-VL-DATATYPE-ARITHCLASS.CLASS
 (58 38 (:REWRITE VL::VL-DATATYPE-UDIMS-WHEN-VL-USERTYPE))
 (58 38 (:REWRITE VL::VL-DATATYPE-UDIMS-WHEN-VL-UNION))
 (58 38 (:REWRITE VL::VL-DATATYPE-UDIMS-WHEN-VL-STRUCT))
 (58 38 (:REWRITE VL::VL-DATATYPE-UDIMS-WHEN-VL-ENUM))
 (58 38 (:REWRITE VL::VL-DATATYPE-UDIMS-WHEN-VL-CORETYPE))
 (42 14 (:REWRITE VL::VL-DATATYPE-RESOLVED-P-OF-USERTYPE-BASETYPE))
 (38 38 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-TRUELIST-ALISTP . 2))
 (38 38 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-TRUELIST-ALISTP . 1))
 (38 38 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 2))
 (38 38 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 1))
 (38 38 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-TRUELIST-ALISTP . 2))
 (38 38 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-TRUELIST-ALISTP . 1))
 (38 38 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-SYMBOL-ALISTP . 2))
 (38 38 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-SYMBOL-ALISTP . 1))
 (28 28 (:TYPE-PRESCRIPTION VL::VL-DATATYPE-RESOLVED-P))
 (11 11 (:REWRITE VL::VL-DATATYPE-PDIMS-WHEN-VL-USERTYPE))
 (11 11 (:REWRITE VL::VL-DATATYPE-PDIMS-WHEN-VL-UNION))
 (11 11 (:REWRITE VL::VL-DATATYPE-PDIMS-WHEN-VL-STRUCT))
 (11 11 (:REWRITE VL::VL-DATATYPE-PDIMS-WHEN-VL-ENUM))
 (11 11 (:REWRITE VL::VL-DATATYPE-PDIMS-WHEN-VL-CORETYPE))
 )
(VL::VL-DATATYPE-ARITHCLASS-OF-VL-DATATYPE-FIX-X
 (96 39 (:REWRITE VL::VL-DATATYPE-UDIMS-WHEN-VL-USERTYPE))
 (96 39 (:REWRITE VL::VL-DATATYPE-UDIMS-WHEN-VL-UNION))
 (96 39 (:REWRITE VL::VL-DATATYPE-UDIMS-WHEN-VL-STRUCT))
 (96 39 (:REWRITE VL::VL-DATATYPE-UDIMS-WHEN-VL-ENUM))
 (96 39 (:REWRITE VL::VL-DATATYPE-UDIMS-WHEN-VL-CORETYPE))
 (41 15 (:REWRITE VL::VL-DATATYPE-PDIMS-WHEN-VL-USERTYPE))
 (21 15 (:REWRITE VL::VL-DATATYPE-PDIMS-WHEN-VL-UNION))
 (21 15 (:REWRITE VL::VL-DATATYPE-PDIMS-WHEN-VL-STRUCT))
 (21 15 (:REWRITE VL::VL-DATATYPE-PDIMS-WHEN-VL-ENUM))
 (21 15 (:REWRITE VL::VL-DATATYPE-PDIMS-WHEN-VL-CORETYPE))
 (20 20 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-TRUELIST-ALISTP . 2))
 (20 20 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-TRUELIST-ALISTP . 1))
 (20 20 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 2))
 (20 20 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 1))
 (20 20 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-TRUELIST-ALISTP . 2))
 (20 20 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-TRUELIST-ALISTP . 1))
 (20 20 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-SYMBOL-ALISTP . 2))
 (20 20 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-SYMBOL-ALISTP . 1))
 (18 9 (:REWRITE VL::VL-MAYBE-DATATYPE-P-WHEN-VL-DATATYPE-P))
 (9 3 (:REWRITE VL::VL-DATATYPE-RESOLVED-P-OF-USERTYPE-BASETYPE))
 (6 6 (:TYPE-PRESCRIPTION VL::VL-DATATYPE-RESOLVED-P))
 )
(VL::VL-DATATYPE-ARITHCLASS-VL-DATATYPE-EQUIV-CONGRUENCE-ON-X)
(VL::VL-EXPRSIGN->ARITHCLASS$INLINE)
(VL::VL-ARITHCLASS-P-OF-VL-EXPRSIGN->ARITHCLASS
 (8 1 (:REWRITE VL::VL-EXPRSIGN-FIX-IDEMPOTENT))
 (5 1 (:REWRITE VL::VL-EXPRSIGN-P-WHEN-VL-MAYBE-EXPRSIGN-P))
 (3 3 (:TYPE-PRESCRIPTION VL::VL-EXPRSIGN-P))
 (2 2 (:TYPE-PRESCRIPTION VL::VL-MAYBE-EXPRSIGN-P))
 (2 1 (:REWRITE VL::VL-MAYBE-EXPRSIGN-P-WHEN-VL-EXPRSIGN-P))
 )
(VL::VL-EXPRSIGN->ARITHCLASS$INLINE-OF-VL-EXPRSIGN-FIX-X
 (14 2 (:REWRITE VL::VL-EXPRSIGN-P-WHEN-VL-MAYBE-EXPRSIGN-P))
 (5 2 (:REWRITE VL::VL-MAYBE-EXPRSIGN-P-WHEN-VL-EXPRSIGN-P))
 (4 4 (:TYPE-PRESCRIPTION VL::VL-MAYBE-EXPRSIGN-P))
 )
(VL::VL-EXPRSIGN->ARITHCLASS$INLINE-VL-EXPRSIGN-EQUIV-CONGRUENCE-ON-X)
(VL::VL-ARITHCLASS-RANK$INLINE)
(VL::NATP-OF-VL-ARITHCLASS-RANK)
(VL::VL-ARITHCLASS-RANK$INLINE-OF-VL-ARITHCLASS-FIX-X)
(VL::VL-ARITHCLASS-RANK$INLINE-VL-ARITHCLASS-EQUIV-CONGRUENCE-ON-X)
(VL::VL-ARITHCLASS-MAX-FN)
(VL::VL-ARITHCLASS-P-OF-VL-ARITHCLASS-MAX)
(VL::VL-ARITHCLASS-MAX-OF-VL-ARITHCLASS-MAX
 (66 8 (:REWRITE VL::VL-ARITHCLASS-FIX-IDEMPOTENT))
 (10 10 (:TYPE-PRESCRIPTION VL::VL-ARITHCLASS-P))
 (8 4 (:REWRITE DEFAULT-<-2))
 (8 4 (:REWRITE DEFAULT-<-1))
 )
(VL::VL-ARITHCLASS-MAX-FN-OF-VL-ARITHCLASS-FIX-X)
(VL::VL-ARITHCLASS-MAX-FN-VL-ARITHCLASS-EQUIV-CONGRUENCE-ON-X)
(VL::VL-ARITHCLASS-MAX-FN-OF-VL-ARITHCLASS-FIX-Y)
(VL::VL-ARITHCLASS-MAX-FN-VL-ARITHCLASS-EQUIV-CONGRUENCE-ON-Y)
(VL::VL-INTEGER-ARITHCLASS-P$INLINE)
(VL::VL-INTEGER-ARITHCLASS-P-OF-VL-EXPRSIGN->ARITHCLASS
 (24 3 (:REWRITE VL::VL-EXPRSIGN-FIX-IDEMPOTENT))
 (15 3 (:REWRITE VL::VL-EXPRSIGN-P-WHEN-VL-MAYBE-EXPRSIGN-P))
 (9 9 (:TYPE-PRESCRIPTION VL::VL-EXPRSIGN-P))
 (6 6 (:TYPE-PRESCRIPTION VL::VL-MAYBE-EXPRSIGN-P))
 (6 3 (:REWRITE VL::VL-MAYBE-EXPRSIGN-P-WHEN-VL-EXPRSIGN-P))
 (6 1 (:REWRITE VL::VL-ARITHCLASS-FIX-IDEMPOTENT))
 (4 4 (:REWRITE-QUOTED-CONSTANT VL::VL-ARITHCLASS-FIX-UNDER-VL-ARITHCLASS-EQUIV))
 (2 2 (:TYPE-PRESCRIPTION VL::VL-ARITHCLASS-P))
 )
(VL::VL-INTEGER-ARITHCLASS->EXPRSIGN$INLINE)
(VL::VL-EXPRSIGN-P-OF-VL-INTEGER-ARITHCLASS->EXPRSIGN
 (15 2 (:REWRITE VL::VL-EXPRSIGN-P-WHEN-VL-MAYBE-EXPRSIGN-P))
 (9 1 (:REWRITE VL::VL-MAYBE-EXPRSIGN-P-WHEN-VL-EXPRSIGN-P))
 (3 3 (:TYPE-PRESCRIPTION VL::VL-MAYBE-EXPRSIGN-P))
 (3 1 (:REWRITE VL::VL-ARITHCLASS-FIX-IDEMPOTENT))
 (2 2 (:TYPE-PRESCRIPTION VL::VL-ARITHCLASS-P))
 )
(VL::VL-INTEGER-ARITHCLASS->EXPRSIGN$INLINE-OF-VL-ARITHCLASS-FIX-X)
(VL::VL-INTEGER-ARITHCLASS->EXPRSIGN$INLINE-VL-ARITHCLASS-EQUIV-CONGRUENCE-ON-X)
(VL::SYMBOLP-OF-VL-DATATYPE-ARITHCLASS)
(VL::VL-INTEGER-ARITHCLASS-P-OF-VL-ARITHCLASS-MAX
 (18 6 (:REWRITE VL::VL-ARITHCLASS-FIX-IDEMPOTENT))
 (12 12 (:TYPE-PRESCRIPTION VL::VL-ARITHCLASS-P))
 )
(VL::VL-INTEGER-ARITHCLASS-P$INLINE-OF-VL-ARITHCLASS-FIX-X)
(VL::VL-INTEGER-ARITHCLASS-P$INLINE-VL-ARITHCLASS-EQUIV-CONGRUENCE-ON-X)
