(RETURNS-LEMMA
 (150 147 (:REWRITE DEFAULT-CAR))
 (128 125 (:REWRITE DEFAULT-CDR))
 (105 21 (:DEFINITION LEN))
 (42 21 (:REWRITE DEFAULT-+-2))
 (23 23 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (22 22 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (21 21 (:REWRITE DEFAULT-+-1))
 (21 7 (:DEFINITION SYMBOL-LISTP))
 (14 7 (:DEFINITION TRUE-LISTP))
 )
(FSUBLIS-VAR
 (51 51 (:REWRITE DEFAULT-CAR))
 (46 46 (:REWRITE DEFAULT-CDR))
 (30 6 (:DEFINITION LEN))
 (15 15 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (14 14 (:TYPE-PRESCRIPTION LEN))
 (12 6 (:REWRITE DEFAULT-+-2))
 (11 11 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (8 2 (:DEFINITION STRIP-CDRS))
 (6 6 (:REWRITE DEFAULT-+-1))
 (6 2 (:DEFINITION SYMBOL-LISTP))
 (5 1 (:DEFINITION ASSOC-EQUAL))
 (4 2 (:DEFINITION TRUE-LISTP))
 (2 2 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 )
(FSUBLIS-VAR-FLAG
 (216 104 (:REWRITE DEFAULT-+-2))
 (145 104 (:REWRITE DEFAULT-+-1))
 (88 22 (:REWRITE COMMUTATIVITY-OF-+))
 (88 22 (:DEFINITION INTEGER-ABS))
 (88 11 (:DEFINITION LENGTH))
 (55 11 (:DEFINITION LEN))
 (32 32 (:REWRITE DEFAULT-CDR))
 (30 30 (:REWRITE FOLD-CONSTS-IN-+))
 (29 25 (:REWRITE DEFAULT-<-2))
 (28 25 (:REWRITE DEFAULT-<-1))
 (22 22 (:REWRITE DEFAULT-UNARY-MINUS))
 (21 21 (:REWRITE DEFAULT-CAR))
 (11 11 (:TYPE-PRESCRIPTION LEN))
 (11 11 (:REWRITE DEFAULT-REALPART))
 (11 11 (:REWRITE DEFAULT-NUMERATOR))
 (11 11 (:REWRITE DEFAULT-IMAGPART))
 (11 11 (:REWRITE DEFAULT-DENOMINATOR))
 (11 11 (:REWRITE DEFAULT-COERCE-2))
 (11 11 (:REWRITE DEFAULT-COERCE-1))
 (4 2 (:TYPE-PRESCRIPTION RETURN-LAST))
 (2 2 (:TYPE-PRESCRIPTION THROW-NONEXEC-ERROR))
 )
(FLAG::FLAG-EQUIV-LEMMA)
(FSUBLIS-VAR-FLAG-EQUIVALENCES)
(FLAG-LEMMA-FOR-RETURN-TYPE-OF-FSUBLIS-VAR.NEW-TERM
 (346 329 (:REWRITE DEFAULT-CAR))
 (334 328 (:REWRITE DEFAULT-CDR))
 (120 60 (:REWRITE DEFAULT-+-2))
 (90 90 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (80 20 (:DEFINITION STRIP-CDRS))
 (65 65 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (60 60 (:REWRITE DEFAULT-+-1))
 )
(RETURN-TYPE-OF-FSUBLIS-VAR.NEW-TERM)
(RETURN-TYPE-OF-FSUBLIS-VAR-LST.NEW-TERMS)
