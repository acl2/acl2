(SUM1)
(FOLD-CONSTS-IN-*)
(MINUS-CANCELLATION-ON-LEFT
 (7 7 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (5 3 (:REWRITE DEFAULT-+-1))
 (4 2 (:REWRITE DEFAULT-UNARY-MINUS))
 (1 1 (:REWRITE FOLD-CONSTS-IN-+))
 )
(LEFT-DISTRIBUTIVITY-OF-*-OVER-+
 (7 5 (:REWRITE DEFAULT-*-2))
 (6 5 (:REWRITE DEFAULT-*-1))
 (5 5 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 3 (:REWRITE DEFAULT-+-2))
 (4 3 (:REWRITE DEFAULT-+-1))
 )
(UNIQUENESS-OF-+-INVERSE)
(COMMUTATIVITY-OF---*-RIGHT)
(COMMUTATIVITY-OF---*-LEFT
 (6 4 (:REWRITE DEFAULT-*-2))
 (6 4 (:REWRITE DEFAULT-*-1))
 (5 5 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 3 (:REWRITE DEFAULT-UNARY-MINUS))
 )
(SUM1-THM
 (75 43 (:REWRITE DEFAULT-+-2))
 (43 43 (:REWRITE DEFAULT-+-1))
 (30 25 (:REWRITE DEFAULT-*-2))
 (25 25 (:REWRITE DEFAULT-*-1))
 (15 15 (:REWRITE FOLD-CONSTS-IN-+))
 (6 6 (:REWRITE FOLD-CONSTS-IN-*))
 (5 5 (:REWRITE DEFAULT-UNARY-MINUS))
 (4 4 (:REWRITE ZP-OPEN))
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 )
(SUM2)
(SUM2-THM
 (251 91 (:REWRITE DEFAULT-+-2))
 (122 91 (:REWRITE DEFAULT-+-1))
 (56 56 (:REWRITE FOLD-CONSTS-IN-+))
 (44 37 (:REWRITE DEFAULT-*-2))
 (37 37 (:REWRITE DEFAULT-*-1))
 (21 16 (:REWRITE DEFAULT-UNARY-MINUS))
 (8 8 (:REWRITE FOLD-CONSTS-IN-*))
 (3 3 (:REWRITE ZP-OPEN))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 )
(SUM3)
(SUM3-THM
 (972 278 (:REWRITE DEFAULT-+-2))
 (376 278 (:REWRITE DEFAULT-+-1))
 (119 95 (:REWRITE DEFAULT-*-2))
 (95 95 (:REWRITE DEFAULT-*-1))
 (38 30 (:REWRITE DEFAULT-UNARY-MINUS))
 (4 4 (:REWRITE ZP-OPEN))
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 )
(SUM4)
(RIGHT-UNICITY-OF-1-FOR-EXPT
 (16 16 (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (16 16 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
 (7 7 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (7 3 (:REWRITE DEFAULT-*-2))
 (5 3 (:REWRITE DEFAULT-*-1))
 )
(SUM4-THM
 (759 248 (:REWRITE DEFAULT-+-2))
 (335 248 (:REWRITE DEFAULT-+-1))
 (150 115 (:REWRITE DEFAULT-*-2))
 (115 115 (:REWRITE DEFAULT-*-1))
 (38 30 (:REWRITE DEFAULT-UNARY-MINUS))
 (4 4 (:REWRITE ZP-OPEN))
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 )
(SUM5)
(SUM5-THM
 (4061 822 (:REWRITE DEFAULT-+-2))
 (1380 822 (:REWRITE DEFAULT-+-1))
 (283 214 (:REWRITE DEFAULT-*-2))
 (214 214 (:REWRITE DEFAULT-*-1))
 (175 115 (:REWRITE DEFAULT-UNARY-MINUS))
 (85 85 (:REWRITE FOLD-CONSTS-IN-*))
 (4 4 (:REWRITE ZP-OPEN))
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 )
(SUM6)
(ABSORB-1
 (7 6 (:REWRITE DEFAULT-*-2))
 (7 6 (:REWRITE DEFAULT-*-1))
 (5 5 (:REWRITE DEFAULT-+-2))
 (5 5 (:REWRITE DEFAULT-+-1))
 (4 3 (:REWRITE DEFAULT-UNARY-MINUS))
 (3 3 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 2 (:REWRITE DEFAULT-UNARY-/))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(COMBINE-NUMERATOR
 (9 7 (:REWRITE DEFAULT-*-2))
 (9 7 (:REWRITE DEFAULT-*-1))
 (8 8 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (8 6 (:REWRITE DEFAULT-UNARY-MINUS))
 (6 3 (:REWRITE DEFAULT-UNARY-/))
 (3 3 (:REWRITE DEFAULT-+-2))
 (3 3 (:REWRITE DEFAULT-+-1))
 (2 1 (:DEFINITION NOT))
 )
(COMBINE-FRACTIONS
 (34 34 (:TYPE-PRESCRIPTION NONNEGATIVE-PRODUCT))
 (9 5 (:REWRITE DEFAULT-UNARY-MINUS))
 (8 5 (:REWRITE DEFAULT-+-2))
 (7 5 (:REWRITE DEFAULT-+-1))
 (5 5 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (5 4 (:REWRITE DEFAULT-*-2))
 (5 4 (:REWRITE DEFAULT-*-1))
 )
(SIMPLIFY-FRACTIONS-*
 (9 7 (:REWRITE DEFAULT-UNARY-MINUS))
 (8 8 (:REWRITE DEFAULT-*-2))
 (8 8 (:REWRITE DEFAULT-*-1))
 (6 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE FOLD-CONSTS-IN-*))
 (1 1 (:REWRITE DEFAULT-UNARY-/))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(SIMPLIFY-FRACTIONS-+
 (6 5 (:REWRITE DEFAULT-UNARY-MINUS))
 (6 5 (:REWRITE DEFAULT-+-2))
 (5 5 (:REWRITE DEFAULT-+-1))
 (4 4 (:REWRITE DEFAULT-*-2))
 (4 4 (:REWRITE DEFAULT-*-1))
 (3 3 (:REWRITE DEFAULT-UNARY-/))
 (1 1 (:REWRITE FOLD-CONSTS-IN-*))
 )
(RIGHT-CANCELLATION-FOR-*
 (23 16 (:REWRITE DEFAULT-*-1))
 (21 21 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (19 16 (:REWRITE DEFAULT-*-2))
 (7 4 (:REWRITE DEFAULT-UNARY-/))
 (2 2 (:REWRITE FOLD-CONSTS-IN-*))
 )
(EQUAL-/
 (5 4 (:REWRITE DEFAULT-*-2))
 (5 4 (:REWRITE DEFAULT-*-1))
 (3 3 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 2 (:REWRITE DEFAULT-UNARY-/))
 )
(SUM6-THM-AUX
 (16 14 (:REWRITE DEFAULT-*-1))
 (14 14 (:REWRITE DEFAULT-*-2))
 (10 9 (:REWRITE DEFAULT-+-2))
 (9 9 (:REWRITE DEFAULT-+-1))
 (5 5 (:REWRITE DEFAULT-UNARY-MINUS))
 (5 3 (:REWRITE DEFAULT-UNARY-/))
 (3 3 (:REWRITE FOLD-CONSTS-IN-*))
 (1 1 (:REWRITE FOLD-CONSTS-IN-+))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(SUM6-THM
 (45 38 (:REWRITE DEFAULT-+-2))
 (42 38 (:REWRITE DEFAULT-+-1))
 (31 13 (:REWRITE DEFAULT-UNARY-/))
 (29 29 (:TYPE-PRESCRIPTION NONNEGATIVE-PRODUCT))
 (25 23 (:REWRITE DEFAULT-*-2))
 (23 23 (:REWRITE DEFAULT-*-1))
 (11 5 (:REWRITE ZP-OPEN))
 (9 5 (:REWRITE FOLD-CONSTS-IN-+))
 (7 7 (:REWRITE DEFAULT-UNARY-MINUS))
 (5 5 (:REWRITE DEFAULT-<-2))
 (5 5 (:REWRITE DEFAULT-<-1))
 )
(SUM7)
(SUM7-THM
 (84 52 (:REWRITE DEFAULT-+-2))
 (60 52 (:REWRITE DEFAULT-+-1))
 (29 24 (:REWRITE DEFAULT-*-2))
 (24 24 (:REWRITE DEFAULT-*-1))
 (6 6 (:REWRITE FOLD-CONSTS-IN-*))
 (5 5 (:REWRITE DEFAULT-UNARY-MINUS))
 (4 4 (:REWRITE ZP-OPEN))
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 )
(SUM8-THM
 (92 40 (:REWRITE DEFAULT-+-2))
 (74 50 (:REWRITE DEFAULT-*-2))
 (64 40 (:REWRITE DEFAULT-+-1))
 (58 50 (:REWRITE DEFAULT-*-1))
 (17 17 (:REWRITE FOLD-CONSTS-IN-+))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
