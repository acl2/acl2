(EQUAL-OF-ASSOC-EQUAL-SAME
 (46 46 (:REWRITE DEFAULT-CAR))
 (7 7 (:REWRITE DEFAULT-CDR))
 )
(ALEN1)
(NORMALIZE-ALEN1-NAME)
(ALEN1-INTRO)
(ALEN1-INTRO2
 (18 12 (:REWRITE DEFAULT-CAR))
 (13 10 (:REWRITE DEFAULT-CDR))
 (10 2 (:DEFINITION ASSOC-EQUAL))
 (8 2 (:DEFINITION ASSOC-KEYWORD))
 )
(ALEN1-OF-COMPRESS1
 (201 145 (:REWRITE DEFAULT-CAR))
 (131 97 (:REWRITE DEFAULT-CDR))
 (56 14 (:DEFINITION ASSOC-KEYWORD))
 (48 4 (:REWRITE COMMUTATIVITY-OF-+))
 (36 8 (:REWRITE DEFAULT-+-1))
 (24 12 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (24 8 (:REWRITE DEFAULT-+-2))
 (24 4 (:REWRITE ZP-OPEN))
 (20 4 (:REWRITE UNICITY-OF-0))
 (16 4 (:DEFINITION FIX))
 (10 2 (:DEFINITION REVAPPEND))
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 )
(INTEGERP-OF-ALEN1-GEN)
(INTEGERP-OF-ALEN1
 (34 22 (:REWRITE DEFAULT-CAR))
 (28 20 (:REWRITE DEFAULT-CDR))
 (20 4 (:DEFINITION ASSOC-EQUAL))
 (16 4 (:DEFINITION ASSOC-KEYWORD))
 (2 2 (:LINEAR ARRAY2P-LINEAR))
 )
(POSP-OF-ALEN1)
(ALEN1-OF-CONS
 (38 20 (:REWRITE DEFAULT-CAR))
 (24 15 (:REWRITE DEFAULT-CDR))
 (12 3 (:DEFINITION ASSOC-KEYWORD))
 )
(ALEN1-OF-ACONS-OF-HEADER
 (13 7 (:REWRITE DEFAULT-CAR))
 (10 7 (:REWRITE DEFAULT-CDR))
 (8 2 (:DEFINITION ASSOC-KEYWORD))
 )
(RATIONALP-OF-ALEN1-WHEN-ARRAY1P)
