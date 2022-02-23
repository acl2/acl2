(EXTRACT-BRANCHES
 (776 356 (:REWRITE DEFAULT-+-2))
 (618 72 (:DEFINITION LENGTH))
 (463 356 (:REWRITE DEFAULT-+-1))
 (458 86 (:DEFINITION LEN))
 (240 60 (:REWRITE COMMUTATIVITY-OF-+))
 (240 60 (:DEFINITION INTEGER-ABS))
 (176 88 (:TYPE-PRESCRIPTION SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-TYPE))
 (156 156 (:TYPE-PRESCRIPTION LEN))
 (144 144 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (126 14 (:DEFINITION SYMBOL-LISTP))
 (112 56 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (95 73 (:REWRITE DEFAULT-<-2))
 (81 73 (:REWRITE DEFAULT-<-1))
 (60 60 (:REWRITE DEFAULT-UNARY-MINUS))
 (54 54 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (50 50 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (44 44 (:REWRITE DEFAULT-COERCE-2))
 (44 44 (:REWRITE DEFAULT-COERCE-1))
 (30 30 (:REWRITE DEFAULT-REALPART))
 (30 30 (:REWRITE DEFAULT-NUMERATOR))
 (30 30 (:REWRITE DEFAULT-IMAGPART))
 (30 30 (:REWRITE DEFAULT-DENOMINATOR))
 (14 14 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP))
 )
(PSEUDO-TERM-LISTP-OF-EXTRACT-BRANCHES
 (1998 1743 (:REWRITE DEFAULT-CDR))
 (1561 1306 (:REWRITE DEFAULT-CAR))
 (1512 168 (:DEFINITION LENGTH))
 (1232 224 (:DEFINITION LEN))
 (896 448 (:TYPE-PRESCRIPTION SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-TYPE))
 (672 672 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (504 504 (:TYPE-PRESCRIPTION LEN))
 (504 56 (:DEFINITION SYMBOL-LISTP))
 (448 224 (:REWRITE DEFAULT-+-2))
 (448 224 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (329 329 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (263 263 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (224 224 (:REWRITE DEFAULT-+-1))
 (56 56 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (56 56 (:REWRITE DEFAULT-COERCE-2))
 (56 56 (:REWRITE DEFAULT-COERCE-1))
 )
(REMOVE-CALLS-TO
 (32 16 (:TYPE-PRESCRIPTION SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-TYPE))
 (23 23 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (14 7 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (11 11 (:REWRITE DEFAULT-CAR))
 (8 8 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (6 6 (:REWRITE DEFAULT-CDR))
 (4 4 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 )
(PSEUDO-TERM-LISTP-OF-REMOVE-CALLS-TO
 (144 72 (:TYPE-PRESCRIPTION SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-TYPE))
 (88 88 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (81 79 (:REWRITE DEFAULT-CAR))
 (77 75 (:REWRITE DEFAULT-CDR))
 (54 6 (:DEFINITION LENGTH))
 (47 47 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (44 8 (:DEFINITION LEN))
 (32 16 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (29 29 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (18 18 (:TYPE-PRESCRIPTION LEN))
 (18 2 (:DEFINITION SYMBOL-LISTP))
 (16 8 (:REWRITE DEFAULT-+-2))
 (12 4 (:DEFINITION TRUE-LISTP))
 (8 8 (:REWRITE DEFAULT-+-1))
 (2 2 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (2 2 (:REWRITE DEFAULT-COERCE-2))
 (2 2 (:REWRITE DEFAULT-COERCE-1))
 )
(GUARD-CONJUNCT-FOR-FORMAL
 (102 51 (:TYPE-PRESCRIPTION SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-TYPE))
 (58 58 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (26 26 (:REWRITE DEFAULT-CDR))
 (21 21 (:REWRITE DEFAULT-CAR))
 (14 14 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (14 7 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (12 6 (:REWRITE DEFAULT-+-2))
 (7 7 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (6 6 (:REWRITE DEFAULT-+-1))
 )
(PSEUDO-TERMP-OF-GUARD-CONJUNCT-FOR-FORMAL
 (302 151 (:TYPE-PRESCRIPTION SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-TYPE))
 (274 274 (:REWRITE DEFAULT-CDR))
 (236 236 (:REWRITE DEFAULT-CAR))
 (201 201 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (122 61 (:REWRITE DEFAULT-+-2))
 (117 13 (:DEFINITION SYMBOL-LISTP))
 (100 50 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (90 29 (:DEFINITION TRUE-LISTP))
 (61 61 (:REWRITE DEFAULT-+-1))
 (53 53 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (48 48 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (13 13 (:REWRITE DEFAULT-COERCE-2))
 (13 13 (:REWRITE DEFAULT-COERCE-1))
 )
(MAYBE-STEP-LIMITP)
(TRY-PROOF)
(THEOREMS-FOR-RETURNED-FORMAL)
(SOME-TERM-CONSES-ITEMP
 (90 45 (:TYPE-PRESCRIPTION SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-TYPE))
 (53 53 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (23 23 (:REWRITE DEFAULT-CDR))
 (20 20 (:REWRITE DEFAULT-CAR))
 (16 8 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (14 14 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (10 5 (:REWRITE DEFAULT-+-2))
 (7 7 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (5 5 (:REWRITE DEFAULT-+-1))
 )
(THEOREMS-FOR-RETURNED-CONSED-FORMAL)
(SOME-TERM-CONSES-THE-CARP
 (90 45 (:TYPE-PRESCRIPTION SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-TYPE))
 (53 53 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (23 23 (:REWRITE DEFAULT-CDR))
 (20 20 (:REWRITE DEFAULT-CAR))
 (16 8 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (14 14 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (10 5 (:REWRITE DEFAULT-+-2))
 (7 7 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (5 5 (:REWRITE DEFAULT-+-1))
 )
(THEOREMS-FOR-RETURNED-CONSED-CAR)
(THEOREMS-FOR-RETURNED-CAR)
(RETURN-TYPE-THEOREMS-BASED-ON-FORMAL)
(RETURN-TYPE-THEOREMS-BASED-ON-FORMALS)
(AUTO-RETURN-TYPE-FN)