(EQUALITY-PAIRP)
(EQUALITY-PAIRSP)
(PSEUDO-TERMP-OF-CAR-OF-CAR-WHEN-EQUALITY-PAIRSP
 (15 15 (:REWRITE DEFAULT-CAR))
 (15 3 (:DEFINITION LEN))
 (14 14 (:REWRITE DEFAULT-CDR))
 (6 3 (:REWRITE DEFAULT-+-2))
 (3 3 (:REWRITE DEFAULT-+-1))
 (3 1 (:DEFINITION SYMBOL-LISTP))
 (2 2 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (2 1 (:DEFINITION TRUE-LISTP))
 (1 1 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 )
(ADD-EQUALITY-PAIRS-FOR-ASSUMPTION
 (462 220 (:REWRITE DEFAULT-+-2))
 (279 279 (:REWRITE DEFAULT-CDR))
 (278 220 (:REWRITE DEFAULT-+-1))
 (182 182 (:REWRITE DEFAULT-CAR))
 (128 32 (:REWRITE COMMUTATIVITY-OF-+))
 (128 32 (:DEFINITION INTEGER-ABS))
 (128 16 (:DEFINITION LENGTH))
 (51 40 (:REWRITE DEFAULT-<-2))
 (48 40 (:REWRITE DEFAULT-<-1))
 (32 32 (:REWRITE DEFAULT-UNARY-MINUS))
 (25 25 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (25 25 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (16 16 (:REWRITE DEFAULT-REALPART))
 (16 16 (:REWRITE DEFAULT-NUMERATOR))
 (16 16 (:REWRITE DEFAULT-IMAGPART))
 (16 16 (:REWRITE DEFAULT-DENOMINATOR))
 (16 16 (:REWRITE DEFAULT-COERCE-2))
 (16 16 (:REWRITE DEFAULT-COERCE-1))
 (16 8 (:DEFINITION TRUE-LISTP))
 (6 6 (:LINEAR ACL2-COUNT-CAR-CDR-LINEAR))
 )
(EQUALITY-PAIRSP-OF-ADD-EQUALITY-PAIRS-FOR-ASSUMPTION
 (2018 2018 (:REWRITE DEFAULT-CDR))
 (1897 1897 (:REWRITE DEFAULT-CAR))
 (776 388 (:REWRITE DEFAULT-+-2))
 (388 388 (:REWRITE DEFAULT-+-1))
 (366 122 (:DEFINITION SYMBOL-LISTP))
 (290 290 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (244 122 (:DEFINITION TRUE-LISTP))
 (187 187 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 )
(ADD-EQUALITY-PAIRS-FOR-ASSUMPTIONS
 (6 2 (:DEFINITION SYMBOL-LISTP))
 (4 4 (:REWRITE DEFAULT-CAR))
 (3 3 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (3 3 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 )
(EQUALITY-PAIRSP-OF-ADD-EQUALITY-PAIRS-FOR-ASSUMPTIONS
 (273 7 (:DEFINITION ADD-EQUALITY-PAIRS-FOR-ASSUMPTION))
 (252 4 (:DEFINITION PSEUDO-TERMP))
 (177 177 (:REWRITE DEFAULT-CDR))
 (154 154 (:REWRITE DEFAULT-CAR))
 (95 19 (:DEFINITION LEN))
 (71 71 (:TYPE-PRESCRIPTION LEN))
 (42 14 (:DEFINITION MEMBER-EQUAL))
 (38 19 (:REWRITE DEFAULT-+-2))
 (23 23 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (19 19 (:REWRITE DEFAULT-+-1))
 (18 4 (:DEFINITION SYMBOL-LISTP))
 (17 17 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (14 14 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (14 7 (:DEFINITION QUOTEP))
 (14 4 (:DEFINITION TRUE-LISTP))
 (12 12 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (8 8 (:TYPE-PRESCRIPTION TRUE-LISTP))
 )
(MAKE-EQUALITY-PAIRS)
(EQUALITY-PAIRSP-OF-MAKE-EQUALITY-PAIRS)
