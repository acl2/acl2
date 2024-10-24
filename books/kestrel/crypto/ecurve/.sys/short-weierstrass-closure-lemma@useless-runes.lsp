(ECURVE::*-OF-/P-2-INSTANCE
 (28 18 (:REWRITE DEFAULT-*-2))
 (24 18 (:REWRITE DEFAULT-*-1))
 (4 4 (:REWRITE *-OF-*-COMBINE-CONSTANTS))
 )
(ECURVE::*-2-X
 (3 3 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (3 2 (:REWRITE DEFAULT-+-2))
 (3 2 (:REWRITE DEFAULT-+-1))
 (3 2 (:REWRITE DEFAULT-*-2))
 (2 2 (:REWRITE DEFAULT-*-1))
 (1 1 (:REWRITE EQUAL-OF-*-AND-CONSTANT))
 (1 1 (:META CANCEL_IPLUS-EQUAL-CORRECT))
 )
(ECURVE::*-3-X
 (5 4 (:REWRITE DEFAULT-+-2))
 (5 4 (:REWRITE DEFAULT-+-1))
 (3 3 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (3 2 (:REWRITE DEFAULT-*-2))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE DEFAULT-*-1))
 (1 1 (:REWRITE EQUAL-OF-*-AND-CONSTANT))
 (1 1 (:META CANCEL_IPLUS-EQUAL-CORRECT))
 )
(ECURVE::X3
 (3 3 (:TYPE-PRESCRIPTION NONNEGATIVE-IPRODUCT))
 )
(ECURVE::Y3)
(ECURVE::P[X])
(ECURVE::P[X1]
 (2 2 (:TYPE-PRESCRIPTION NONNEGATIVE-IPRODUCT))
 )
(ECURVE::P[X2]
 (2 2 (:TYPE-PRESCRIPTION NONNEGATIVE-IPRODUCT))
 )
(ECURVE::P[X3])
(ECURVE::QUOTIENT)
(ECURVE::Q[X]
 (6 6 (:TYPE-PRESCRIPTION NONNEGATIVE-IPRODUCT))
 )
(ECURVE::R[X])
(ECURVE::DELTA-X)
(ECURVE::ALPHA{X1=X2}
 (1 1 (:TYPE-PRESCRIPTION NONNEGATIVE-IPRODUCT))
 )
(ECURVE::ALPHA{X1=/=X2})
(ECURVE::INTEGERP-OF-ALPHA{X1=X2})
(ECURVE::INTEGERP-OF-ALPHA{X1=/=X2})
(ECURVE::INTEGERP-OF-X3)
(ECURVE::INTEGERP-OF-Y3)
(ECURVE::INTEGERP-OF-DELTA-X)
(ECURVE::DELTA-X-NON-ZERO-WHENEVER-X1=/=X2
 (108 4 (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
 (70 2 (:REWRITE COMMUTATIVITY-2-OF-I+))
 (59 5 (:REWRITE DISTRIBUTIVITY-OF-IMINUS-OVER-I+))
 (42 18 (:REWRITE DEFAULT-+-2))
 (30 10 (:REWRITE DEFAULT-UNARY-MINUS))
 (30 10 (:REWRITE DEFAULT-UNARY-/))
 (24 18 (:REWRITE DEFAULT-+-1))
 (24 8 (:REWRITE DEFAULT-*-2))
 (24 8 (:REWRITE DEFAULT-*-1))
 (24 4 (:DEFINITION NFIX))
 (16 10 (:REWRITE DEFAULT-<-1))
 (14 10 (:REWRITE DEFAULT-<-2))
 (4 4 (:META CANCEL_IPLUS-EQUAL-CORRECT))
 (4 2 (:REWRITE DEFAULT-NUMERATOR))
 (4 2 (:REWRITE DEFAULT-DENOMINATOR))
 )
(ECURVE::S
 (3 3 (:TYPE-PRESCRIPTION NONNEGATIVE-IPRODUCT))
 )
(ECURVE::INTEGERP-OF-S)
(ECURVE::STEP0-1)
(ECURVE::STEP0-2
 (4558 1200 (:REWRITE ECURVE::|x =p -y --> x + y =p 0|))
 (6 6 (:TYPE-PRESCRIPTION NONNEGATIVE-IPRODUCT))
 )
(ECURVE::STEP1
 (2967 1100 (:REWRITE DEFAULT-+-2))
 (1932 1627 (:REWRITE DEFAULT-*-2))
 (1633 1627 (:REWRITE DEFAULT-*-1))
 (1509 1100 (:REWRITE DEFAULT-+-1))
 (622 384 (:REWRITE DEFAULT-UNARY-MINUS))
 (592 592 (:REWRITE FOLD-CONSTS-IN-+))
 (475 475 (:REWRITE *-OF-*-COMBINE-CONSTANTS))
 (26 26 (:META CANCEL_IPLUS-EQUAL-CORRECT))
 )
(ECURVE::STEP2
 (71 17 (:REWRITE ECURVE::|x =p -y --> x + y =p 0|))
 (64 16 (:REWRITE ECURVE::|x + x =p 0 --> x =p 0|))
 (20 7 (:REWRITE FUNCTIONAL-SELF-INVERSION-OF-IMINUS))
 (14 1 (:REWRITE DISTRIBUTIVITY-OF-IMINUS-OVER-I+))
 (6 6 (:TYPE-PRESCRIPTION INTEGERP-OF-I*))
 (3 3 (:META CANCEL_IPLUS-EQUAL-CORRECT))
 )
(ECURVE::STEP3
 (10 10 (:REWRITE DEFAULT-*-2))
 (10 10 (:REWRITE DEFAULT-*-1))
 )
(ECURVE::STEP4.1
 (11804 3716 (:REWRITE ECURVE::|x =p -y --> x + y =p 0|))
 (293 48 (:REWRITE DEFAULT-+-2))
 (139 6 (:REWRITE ECURVE::|x + x =p 0 --> x =p 0|))
 (72 48 (:REWRITE DEFAULT-+-1))
 (41 41 (:REWRITE FOLD-CONSTS-IN-+))
 (26 22 (:REWRITE DEFAULT-*-2))
 (23 23 (:TYPE-PRESCRIPTION INTEGERP-OF-I+))
 (22 22 (:REWRITE DEFAULT-*-1))
 (18 12 (:REWRITE DEFAULT-UNARY-MINUS))
 (6 1 (:REWRITE DISTRIBUTIVITY-OF-MINUS-OVER-+))
 (4 4 (:REWRITE FOLD-CONSTS-IN-*))
 (4 4 (:REWRITE *-OF-*-COMBINE-CONSTANTS))
 (2 1 (:REWRITE FUNCTIONAL-SELF-INVERSION-OF-MINUS))
 )
(ECURVE::STEP5.1
 (1949 565 (:REWRITE ECURVE::|x =p -y --> x + y =p 0|))
 (151 151 (:TYPE-PRESCRIPTION INTEGERP-OF-I*))
 (68 18 (:REWRITE DEFAULT-+-2))
 (30 18 (:REWRITE DEFAULT-+-1))
 (25 19 (:REWRITE DEFAULT-*-2))
 (21 19 (:REWRITE DEFAULT-*-1))
 (16 16 (:REWRITE FOLD-CONSTS-IN-+))
 (16 8 (:REWRITE DEFAULT-UNARY-MINUS))
 (4 4 (:REWRITE *-OF-*-COMBINE-CONSTANTS))
 (2 1 (:REWRITE ECURVE::=P-OF-I+-AND-I+-CANCEL))
 )
(ECURVE::STEP6.1
 (3 1 (:REWRITE FUNCTIONAL-SELF-INVERSION-OF-IMINUS))
 (1 1 (:TYPE-PRESCRIPTION INTEGERP-OF-I*))
 )
(ECURVE::STEP7.1
 (27 7 (:REWRITE ECURVE::|x =p -y --> x + y =p 0|))
 )
(ECURVE::STEP8.1
 (83 21 (:REWRITE ECURVE::|x =p -y --> x + y =p 0|))
 (20 7 (:REWRITE FUNCTIONAL-SELF-INVERSION-OF-IMINUS))
 (14 1 (:REWRITE DISTRIBUTIVITY-OF-IMINUS-OVER-I+))
 (6 6 (:TYPE-PRESCRIPTION INTEGERP-OF-I*))
 (3 3 (:META CANCEL_IPLUS-EQUAL-CORRECT))
 )
(ECURVE::STEP9.1
 (855 171 (:REWRITE ECURVE::|x =p -y --> x + y =p 0|))
 (2 2 (:TYPE-PRESCRIPTION NONNEGATIVE-IPRODUCT))
 )
(ECURVE::STEP10.1
 (124 28 (:REWRITE ECURVE::|x =p -y --> x + y =p 0|))
 (8 4 (:TYPE-PRESCRIPTION NONNEGATIVE-IPRODUCT))
 (4 4 (:TYPE-PRESCRIPTION ECURVE::X3))
 )
(ECURVE::STEP4.2
 (750 750 (:TYPE-PRESCRIPTION INTEGERP-OF-I*))
 )
(ECURVE::STEP5.2
 (62 14 (:REWRITE ECURVE::|x =p -y --> x + y =p 0|))
 (20 7 (:REWRITE FUNCTIONAL-SELF-INVERSION-OF-IMINUS))
 (14 1 (:REWRITE DISTRIBUTIVITY-OF-IMINUS-OVER-I+))
 (6 6 (:TYPE-PRESCRIPTION INTEGERP-OF-I*))
 (3 3 (:META CANCEL_IPLUS-EQUAL-CORRECT))
 )
(ECURVE::STEP6.2
 (409 93 (:REWRITE ECURVE::|x =p -y --> x + y =p 0|))
 )
(ECURVE::STEP7.2
 (107 27 (:REWRITE ECURVE::|x =p -y --> x + y =p 0|))
 (7 7 (:TYPE-PRESCRIPTION INTEGERP-OF-I*))
 (3 3 (:TYPE-PRESCRIPTION ECURVE::X3))
 )
(ECURVE::P[X1]=0-AND-P[X2]=0-IMPLIES-P[X3]=0
 (39 13 (:REWRITE ECURVE::|x =p -y --> x + y =p 0|))
 (4 4 (:META CANCEL_IPLUS-EQUAL-CORRECT))
 )
(ECURVE::P[X.Y]
 (2 2 (:TYPE-PRESCRIPTION NONNEGATIVE-IPRODUCT))
 )
(ECURVE::=P-IMPLIES-=P-P[X.Y]-1
 (204 48 (:REWRITE ECURVE::|x =p -y --> x + y =p 0|))
 (138 22 (:REWRITE DISTRIBUTIVITY-OF-IMINUS-OVER-I+))
 (64 20 (:REWRITE FUNCTIONAL-SELF-INVERSION-OF-IMINUS))
 (44 20 (:DEFINITION IFIX))
 (20 20 (:TYPE-PRESCRIPTION INTEGERP-OF-I*))
 (4 4 (:TYPE-PRESCRIPTION NONNEGATIVE-IPRODUCT))
 )
(ECURVE::=P-IMPLIES-=P-P[X.Y]-2
 (204 48 (:REWRITE ECURVE::|x =p -y --> x + y =p 0|))
 (138 22 (:REWRITE DISTRIBUTIVITY-OF-IMINUS-OVER-I+))
 (64 20 (:REWRITE FUNCTIONAL-SELF-INVERSION-OF-IMINUS))
 (44 20 (:DEFINITION IFIX))
 (20 20 (:TYPE-PRESCRIPTION INTEGERP-OF-I*))
 (4 4 (:TYPE-PRESCRIPTION NONNEGATIVE-IPRODUCT))
 )
(ECURVE::P[X.Y]=0-IMPLIES-P[X]=0
 (54414 25456 (:REWRITE ECURVE::|x =p -y --> x + y =p 0|))
 (85 1 (:REWRITE ECURVE::STEP6.2))
 (72 72 (:TYPE-PRESCRIPTION NONNEGATIVE-IPRODUCT))
 )
(ECURVE::P[X1]=P[X][X=X1]
 (134 22 (:REWRITE DISTRIBUTIVITY-OF-IMINUS-OVER-I+))
 (85 1 (:REWRITE ECURVE::STEP6.2))
 (16 16 (:TYPE-PRESCRIPTION INTEGERP-OF-I*))
 (12 6 (:REWRITE ECURVE::|x + x =p 0 --> x =p 0|))
 (4 4 (:TYPE-PRESCRIPTION NONNEGATIVE-IPRODUCT))
 )
(ECURVE::Y2=ALPHA*X2+Y1-ALPHA*X1
 (30 6 (:REWRITE ECURVE::|x =p -y --> x + y =p 0|))
 (12 1 (:REWRITE DISTRIBUTIVITY-OF-IMINUS-OVER-I+))
 (10 5 (:REWRITE FUNCTIONAL-SELF-INVERSION-OF-IMINUS))
 (6 1 (:REWRITE COMMUTATIVITY-OF-I+))
 )
(ECURVE::P[X2]=P[X][X=X2]
 (296 46 (:REWRITE DISTRIBUTIVITY-OF-IMINUS-OVER-I+))
 (226 2 (:REWRITE ECURVE::STEP6.2))
 (42 21 (:REWRITE ECURVE::|x + x =p 0 --> x =p 0|))
 (38 38 (:TYPE-PRESCRIPTION INTEGERP-OF-I*))
 (8 8 (:TYPE-PRESCRIPTION NONNEGATIVE-IPRODUCT))
 (2 2 (:META CANCEL_IPLUS-EQUAL-CORRECT))
 )
(ECURVE::P[X1.Y1]=0-AND-P[X2.Y2]=0-IMPLIES-P[X3.Y3]=0
 (1355 11 (:REWRITE ECURVE::STEP6.2))
 (540 36 (:DEFINITION ECURVE::QUOTIENT))
 (36 36 (:TYPE-PRESCRIPTION ECURVE::QUOTIENT))
 (26 2 (:REWRITE ECURVE::STEP7.2))
 (25 25 (:META CANCEL_IPLUS-EQUAL-CORRECT))
 (16 16 (:TYPE-PRESCRIPTION ECURVE::X3))
 )
