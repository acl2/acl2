(HYPOTHESIS-PARITY)
(CONCLUSION-PARITY)
(APPLY-FOR-DEFEVALUATOR
 (4 2 (:TYPE-PRESCRIPTION RETURN-LAST))
 (2 2 (:TYPE-PRESCRIPTION THROW-NONEXEC-ERROR))
 )
(CONS-EV
 (63 2 (:DEFINITION ACL2-COUNT))
 (21 10 (:REWRITE DEFAULT-+-2))
 (14 14 (:TYPE-PRESCRIPTION ACL2-COUNT))
 (14 10 (:REWRITE DEFAULT-+-1))
 (8 2 (:REWRITE COMMUTATIVITY-OF-+))
 (8 2 (:DEFINITION INTEGER-ABS))
 (8 1 (:DEFINITION LENGTH))
 (6 6 (:REWRITE DEFAULT-CAR))
 (6 3 (:TYPE-PRESCRIPTION RETURN-LAST))
 (5 5 (:REWRITE DEFAULT-CDR))
 (5 1 (:DEFINITION LEN))
 (3 3 (:TYPE-PRESCRIPTION THROW-NONEXEC-ERROR))
 (3 3 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (1 1 (:TYPE-PRESCRIPTION LEN))
 (1 1 (:REWRITE DEFAULT-REALPART))
 (1 1 (:REWRITE DEFAULT-NUMERATOR))
 (1 1 (:REWRITE DEFAULT-IMAGPART))
 (1 1 (:REWRITE DEFAULT-DENOMINATOR))
 (1 1 (:REWRITE DEFAULT-COERCE-2))
 (1 1 (:REWRITE DEFAULT-COERCE-1))
 )
(EVAL-LIST-KWOTE-LST
 (9 8 (:REWRITE DEFAULT-CAR))
 (8 7 (:REWRITE DEFAULT-CDR))
 )
(TRUE-LIST-FIX-EV-LST
 (7 6 (:REWRITE DEFAULT-CDR))
 (5 4 (:REWRITE DEFAULT-CAR))
 )
(EV-COMMUTES-CAR
 (1 1 (:REWRITE DEFAULT-CDR))
 )
(EV-LST-COMMUTES-CDR
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(CONS-EV-CONSTRAINT-0)
(CONS-EV-CONSTRAINT-1
 (10 2 (:DEFINITION ASSOC-EQUAL))
 (6 6 (:REWRITE DEFAULT-CAR))
 (4 4 (:REWRITE DEFAULT-CDR))
 )
(CONS-EV-CONSTRAINT-2
 (4 4 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE DEFAULT-CDR))
 )
(CONS-EV-CONSTRAINT-3
 (15 15 (:REWRITE DEFAULT-CAR))
 (14 2 (:DEFINITION PAIRLIS$))
 (12 12 (:REWRITE DEFAULT-CDR))
 (4 2 (:REWRITE EV-LST-COMMUTES-CDR))
 (4 2 (:REWRITE EV-COMMUTES-CAR))
 )
(CONS-EV-CONSTRAINT-4)
(CONS-EV-CONSTRAINT-5
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 )
(CONS-EV-CONSTRAINT-6)
(CONS-EV-CONSTRAINT-7
 (5 5 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE DEFAULT-CDR))
 )
(CONS-EV-CONSTRAINT-8
 (9 9 (:REWRITE DEFAULT-CAR))
 (5 5 (:REWRITE DEFAULT-CDR))
 )
(CONS-EV-CONSTRAINT-9
 (9 9 (:REWRITE DEFAULT-CAR))
 (5 5 (:REWRITE DEFAULT-CDR))
 )
(CONS-EV-CONSTRAINT-10
 (11 11 (:REWRITE DEFAULT-CAR))
 (10 10 (:REWRITE DEFAULT-CDR))
 )
(CONS-EQUAL-META-FUNCTION-HELPER
 (97 47 (:REWRITE DEFAULT-+-2))
 (62 47 (:REWRITE DEFAULT-+-1))
 (32 8 (:REWRITE COMMUTATIVITY-OF-+))
 (32 8 (:DEFINITION INTEGER-ABS))
 (32 4 (:DEFINITION LENGTH))
 (24 24 (:REWRITE DEFAULT-CDR))
 (20 4 (:DEFINITION LEN))
 (14 14 (:REWRITE FOLD-CONSTS-IN-+))
 (14 14 (:REWRITE DEFAULT-CAR))
 (10 9 (:REWRITE DEFAULT-<-2))
 (10 9 (:REWRITE DEFAULT-<-1))
 (8 8 (:REWRITE DEFAULT-UNARY-MINUS))
 (4 4 (:TYPE-PRESCRIPTION LEN))
 (4 4 (:REWRITE DEFAULT-REALPART))
 (4 4 (:REWRITE DEFAULT-NUMERATOR))
 (4 4 (:REWRITE DEFAULT-IMAGPART))
 (4 4 (:REWRITE DEFAULT-DENOMINATOR))
 (4 4 (:REWRITE DEFAULT-COERCE-2))
 (4 4 (:REWRITE DEFAULT-COERCE-1))
 )
(CONS-EQUAL-SMART-META-HELPER
 (337 282 (:REWRITE DEFAULT-CAR))
 (299 299 (:REWRITE DEFAULT-CDR))
 (145 79 (:REWRITE CONS-EV-CONSTRAINT-3))
 (88 77 (:REWRITE CONS-EV-CONSTRAINT-1))
 )
(CONS-EQUAL-META-FUNCTION)
(CONS-EQUAL-SMART-META
 (64 64 (:REWRITE DEFAULT-CDR))
 (49 49 (:REWRITE DEFAULT-CAR))
 (29 1 (:DEFINITION CONS-EQUAL-META-FUNCTION-HELPER))
 (24 16 (:REWRITE CONS-EV-CONSTRAINT-10))
 (18 18 (:TYPE-PRESCRIPTION CONS-EQUAL-META-FUNCTION-HELPER))
 (16 10 (:REWRITE CONS-EV-CONSTRAINT-3))
 (16 10 (:REWRITE CONS-EV-CONSTRAINT-2))
 (16 10 (:REWRITE CONS-EV-CONSTRAINT-1))
 (6 2 (:DEFINITION MEMBER-EQUAL))
 )
(CONS-EQUAL-REWRITE
 (3 3 (:REWRITE DEFAULT-CDR))
 (3 3 (:REWRITE DEFAULT-CAR))
 )
(CONS-ONTO-CDR-EQUALS-ALL-REWRITE
 (4 4 (:REWRITE DEFAULT-CDR))
 (4 4 (:REWRITE DEFAULT-CAR))
 )
(LIST-CAR-EQUAL-ALL-REWRITE
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 )
(CONS-EQUAL-CONS-SAME-REWRITE-ONE
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 )
(CONS-EQUAL-CONS-SAME-REWRITE-TWO
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 )
