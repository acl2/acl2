(ZCASH::ZERO-WHEN-EQUAL-TO-NEG-WITH-ODD-P
 (166 166 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (166 166 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (166 166 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (130 26 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (130 26 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (130 26 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (130 26 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (72 11 (:REWRITE |(< (- x) c)|))
 (67 3 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (64 3 (:REWRITE MOD-ZERO . 4))
 (53 53 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (53 53 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (40 3 (:REWRITE DEFAULT-MOD-RATIO))
 (40 2 (:REWRITE MOD-X-Y-=-X . 4))
 (38 34 (:REWRITE DEFAULT-TIMES-2))
 (34 34 (:REWRITE DEFAULT-TIMES-1))
 (26 26 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (26 26 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (26 26 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (26 26 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (26 26 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (24 1 (:REWRITE CANCEL-MOD-+))
 (22 10 (:REWRITE DEFAULT-MINUS))
 (22 8 (:REWRITE |(equal (- x) c)|))
 (15 15 (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (15 3 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (15 3 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (15 3 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (13 13 (:REWRITE THE-FLOOR-BELOW))
 (13 13 (:REWRITE THE-FLOOR-ABOVE))
 (13 13 (:REWRITE DEFAULT-LESS-THAN-2))
 (13 13 (:REWRITE DEFAULT-LESS-THAN-1))
 (12 12 (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (12 12 (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (12 12 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (11 11 (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (11 11 (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (11 11 (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (11 11 (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (11 11 (:REWRITE |(< c (- x))|))
 (11 11 (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (11 11 (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (11 11 (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (11 11 (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (11 11 (:REWRITE |(< (/ x) (/ y))|))
 (11 11 (:REWRITE |(< (- x) (- y))|))
 (10 8 (:REWRITE DEFAULT-PLUS-1))
 (9 9 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (9 9 (:REWRITE INTEGERP-<-CONSTANT))
 (9 9 (:REWRITE CONSTANT-<-INTEGERP))
 (8 8 (:REWRITE SIMPLIFY-SUMS-<))
 (8 8 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (8 8 (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (8 8 (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (8 8 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (8 8 (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (8 8 (:REWRITE DEFAULT-PLUS-2))
 (8 8 (:REWRITE DEFAULT-DIVIDE))
 (8 8 (:REWRITE |(equal c (/ x))|))
 (8 8 (:REWRITE |(equal c (- x))|))
 (8 8 (:REWRITE |(equal (/ x) c)|))
 (8 8 (:REWRITE |(equal (/ x) (/ y))|))
 (8 8 (:REWRITE |(equal (- x) (- y))|))
 (7 7 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (7 7 (:REWRITE REDUCE-INTEGERP-+))
 (7 7 (:REWRITE INTEGERP-MINUS-X))
 (7 7 (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (7 7 (:META META-INTEGERP-CORRECT))
 (6 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (6 6 (:REWRITE |(< 0 (* x y))|))
 (5 5 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (5 5 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (5 5 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (5 5 (:REWRITE |(< 0 (/ x))|))
 (5 1 (:REWRITE MOD-X-Y-=-X . 2))
 (5 1 (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (5 1 (:REWRITE MOD-CANCEL-*-CONST))
 (5 1 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (5 1 (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (4 4 (:REWRITE |(< (/ x) 0)|))
 (4 4 (:REWRITE |(< (* x y) 0)|))
 (3 3 (:REWRITE DEFAULT-MOD-2))
 (3 3 (:REWRITE DEFAULT-MOD-1))
 (3 3 (:REWRITE |(- (* c x))|))
 (2 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (2 2 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (1 1 (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (1 1 (:REWRITE |(mod x (- y))| . 3))
 (1 1 (:REWRITE |(mod x (- y))| . 2))
 (1 1 (:REWRITE |(mod x (- y))| . 1))
 (1 1 (:REWRITE |(mod (- x) y)| . 3))
 (1 1 (:REWRITE |(mod (- x) y)| . 2))
 (1 1 (:REWRITE |(equal (+ (- c) x) y)|))
 (1 1 (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (1 1 (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (1 1 (:REWRITE |(< x (/ y)) with (< y 0)|))
 )
(ZCASH::SOLVE-BY-DIV
 (21 7 (:DEFINITION NATP))
 (7 7 (:TYPE-PRESCRIPTION NATP))
 (7 7 (:REWRITE PFIELD::FEP-WHEN-CONSTANT))
 (7 7 (:REWRITE DEFAULT-<-2))
 (7 7 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE PFIELD::MUL-WHEN-EQUAL-OF-MOD-SUBST-ARG2))
 (4 4 (:REWRITE PFIELD::MUL-WHEN-EQUAL-OF-MOD-SUBST-ARG1))
 (4 4 (:REWRITE PFIELD::MUL-WHEN-CONSTANT-REDUCE-ARG1))
 (4 4 (:REWRITE PFIELD::MUL-OF--1-BECOMES-NEG-ALT))
 (3 3 (:REWRITE NOT-PRIMEP-WHEN-DIVIDES))
 (3 3 (:REWRITE PFIELD::MUL-WHEN-NOT-INTEGERP-ARG2-CHEAP))
 (3 3 (:REWRITE PFIELD::MUL-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (1 1 (:REWRITE PFIELD::EQUAL-OF-MUL-CONSTANTS-ALT))
 (1 1 (:REWRITE PFIELD::EQUAL-OF-MUL-CONSTANTS))
 )
(ZCASH::NOT-JUBJUB-R-POINTP-WHEN-LOWER-ORDER
 (79 4 (:REWRITE ZCASH::JUBJUB-POINTP-WHEN-JUBJUB-R-POINTP))
 (16 8 (:REWRITE DEFAULT-CDR))
 (16 8 (:REWRITE DEFAULT-CAR))
 (13 9 (:REWRITE DEFAULT-<-1))
 (12 9 (:REWRITE DEFAULT-<-2))
 (6 2 (:REWRITE ZCASH::JUBJUB-R-POINTP-WHEN-JUBJUB-RSTAR-POINTP))
 (4 4 (:TYPE-PRESCRIPTION ZCASH::JUBJUB-RSTAR-POINTP))
 )
(ZCASH::POINT-0-M1)
(ZCASH::POINT-0-M1-NOT-ZERO)
(ZCASH::2-POINT-0-M1-IS-ZERO)
(ZCASH::POINT-0-M1-NOT-IN-JUBJUB-R
 (8 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:TYPE-PRESCRIPTION ZCASH::JUBJUB-Q))
 (4 4 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (4 4 (:REWRITE DEFAULT-+-1))
 (3 1 (:REWRITE ZCASH::JUBJUB-R-POINTP-WHEN-JUBJUB-RSTAR-POINTP))
 (2 2 (:TYPE-PRESCRIPTION ZCASH::JUBJUB-RSTAR-POINTP))
 )
(ZCASH::NOT-JUBJUB-R-POINTP-WHEN-0-ORDINATE<ASSOCIATIVITY>)
(ZCASH::NOT-JUBJUB-R-POINTP-WHEN-0-ORDINATE<POINT>)
(ZCASH::NOT-JUBJUB-R-POINTP-WHEN-0-ORDINATE<V-IS-0>)
(ZCASH::NOT-JUBJUB-R-POINTP-WHEN-0-ORDINATE<A.U2-IS-1>
 (11 6 (:REWRITE PFIELD::MUL-WHEN-NOT-INTEGERP-ARG2-CHEAP))
 (10 10 (:REWRITE PFIELD::MUL-WHEN-EQUAL-OF-MOD-SUBST-ARG2))
 (10 10 (:REWRITE PFIELD::MUL-WHEN-EQUAL-OF-MOD-SUBST-ARG1))
 (10 10 (:REWRITE PFIELD::MUL-WHEN-CONSTANT-REDUCE-ARG1))
 (10 10 (:REWRITE PFIELD::MUL-OF--1-BECOMES-NEG-ALT))
 (8 6 (:REWRITE PFIELD::MUL-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (6 1 (:REWRITE ZCASH::JUBJUB-POINTP-WHEN-JUBJUB-R-POINTP))
 (3 3 (:REWRITE PFIELD::ADD-SUBST-CONSTANT-ARG2))
 (3 3 (:REWRITE PFIELD::ADD-SUBST-CONSTANT-ARG1))
 (3 1 (:REWRITE ZCASH::JUBJUB-R-POINTP-WHEN-JUBJUB-RSTAR-POINTP))
 (2 2 (:TYPE-PRESCRIPTION ZCASH::JUBJUB-RSTAR-POINTP))
 (2 2 (:TYPE-PRESCRIPTION ZCASH::JUBJUB-R-POINTP))
 (2 1 (:REWRITE IFIX-WHEN-NOT-INTEGERP-UNLIMITED))
 (2 1 (:REWRITE PFIELD::ADD-WHEN-NOT-INTEGERP-ARG2-CHEAP))
 (1 1 (:TYPE-PRESCRIPTION ZCASH::JUBJUB-D))
 (1 1 (:TYPE-PRESCRIPTION ZCASH::JUBJUB-A))
 (1 1 (:REWRITE PFIELD::MUL-OF-MUL-COMBINE-CONSTANTS))
 (1 1 (:REWRITE PFIELD::MUL-COMMUTATIVE-2))
 (1 1 (:REWRITE PFIELD::ADD-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (1 1 (:REWRITE PFIELD::ADD-COMMUTATIVE))
 )
(ZCASH::NOT-JUBJUB-R-POINTP-WHEN-0-ORDINATE<2-POINT-IS-POINT-0-M1>
 (11 11 (:REWRITE PFIELD::MUL-WHEN-EQUAL-OF-MOD-SUBST-ARG2))
 (11 11 (:REWRITE PFIELD::MUL-WHEN-EQUAL-OF-MOD-SUBST-ARG1))
 (11 11 (:REWRITE PFIELD::MUL-WHEN-CONSTANT-REDUCE-ARG1))
 (10 8 (:REWRITE PFIELD::MUL-WHEN-NOT-INTEGERP-ARG2-CHEAP))
 (8 8 (:REWRITE PFIELD::MUL-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (2 2 (:REWRITE PFIELD::MUL-OF-MUL-COMBINE-CONSTANTS))
 (2 2 (:REWRITE PFIELD::MUL-COMMUTATIVE-2))
 (1 1 (:REWRITE-QUOTED-CONSTANT ECURVE::TWISTED-EDWARDS-CURVE-FIX-UNDER-TWISTED-EDWARDS-CURVE-EQUIV))
 )
(ZCASH::NOT-JUBJUB-R-POINTP-WHEN-0-ORDINATE<2-2-POINT-IS-2-POINT-0-M1>
 (4 2 (:REWRITE DEFAULT-CDR))
 (4 2 (:REWRITE DEFAULT-CAR))
 )
(ZCASH::NOT-JUBJUB-R-POINTP-WHEN-0-ORDINATE<4-POINT-IS-ZERO>
 (2 2 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 )
(ZCASH::NOT-JUBJUB-R-POINTP-WHEN-0-ORDINATE<POINT-NOT-ZERO>)
(ZCASH::NOT-JUBJUB-R-POINTP-WHEN-0-ORDINATE<NOT-JUBJUB-R-POINTP>)
(ZCASH::NOT-JUBJUB-R-POINTP-WHEN-0-ORDINATE)
(ZCASH::JUBJUB-R-DOUBLING-OF-NONZERO-IS-NONZERO)
(ZCASH::JUBJBUB-R-DOUBLING-INJECTIVITY-WHEN-FIRST-IS-ZERO)
(ZCASH::JUBJBUB-R-DOUBLING-INJECTIVITY-WHEN-SECOND-IS-ZERO)
(ZCASH::JUBJUB-R-DOUBLING-INJECTIVITY-WHEN-NEITHER-IS-ZERO<ASSOCIATIVITY>)
(ZCASH::JUBJUB-R-DOUBLING-INJECTIVITY-WHEN-NEITHER-IS-ZERO<POINT-X>)
(ZCASH::JUBJUB-R-DOUBLING-INJECTIVITY-WHEN-NEITHER-IS-ZERO<POINT-Y>)
(ZCASH::JUBJUB-R-DOUBLING-INJECTIVITY-WHEN-NEITHER-IS-ZERO<NOT-ZERO-X>)
(ZCASH::JUBJUB-R-DOUBLING-INJECTIVITY-WHEN-NEITHER-IS-ZERO<NOT-ZERO-Y>)
(ZCASH::JUBJUB-R-DOUBLING-INJECTIVITY-WHEN-NEITHER-IS-ZERO<DOUBLES-EQUAL>)
(ZCASH::JUBJUB-R-DOUBLING-INJECTIVITY-WHEN-NEITHER-IS-ZERO<R-TIMES-X>
 (19 2 (:REWRITE ZCASH::JUBJUB-POINTP-WHEN-JUBJUB-R-POINTP))
 (5 3 (:REWRITE DEFAULT-<-1))
 (4 3 (:REWRITE DEFAULT-<-2))
 (3 1 (:REWRITE ZCASH::JUBJUB-R-POINTP-WHEN-JUBJUB-RSTAR-POINTP))
 (2 2 (:TYPE-PRESCRIPTION ZCASH::JUBJUB-RSTAR-POINTP))
 )
(ZCASH::JUBJUB-R-DOUBLING-INJECTIVITY-WHEN-NEITHER-IS-ZERO<R-TIMES-Y>
 (19 2 (:REWRITE ZCASH::JUBJUB-POINTP-WHEN-JUBJUB-R-POINTP))
 (5 3 (:REWRITE DEFAULT-<-1))
 (4 3 (:REWRITE DEFAULT-<-2))
 (3 1 (:REWRITE ZCASH::JUBJUB-R-POINTP-WHEN-JUBJUB-RSTAR-POINTP))
 (2 2 (:TYPE-PRESCRIPTION ZCASH::JUBJUB-RSTAR-POINTP))
 )
(ZCASH::JUBJUB-R-DOUBLING-INJECTIVITY-WHEN-NEITHER-IS-ZERO<INTEGER-K>)
(ZCASH::JUBJUB-R-DOUBLING-INJECTIVITY-WHEN-NEITHER-IS-ZERO<DECOMPOSE>
 (11 6 (:REWRITE DEFAULT-+-2))
 (9 5 (:REWRITE DEFAULT-*-2))
 (7 6 (:REWRITE DEFAULT-+-1))
 (6 5 (:REWRITE DEFAULT-*-1))
 )
(ZCASH::JUBJUB-R-DOUBLING-INJECTIVITY-WHEN-NEITHER-IS-ZERO<2K+1-TIMES-X>
 (22 12 (:REWRITE DEFAULT-+-2))
 (18 10 (:REWRITE DEFAULT-*-2))
 (14 12 (:REWRITE DEFAULT-+-1))
 (12 10 (:REWRITE DEFAULT-*-1))
 (4 2 (:REWRITE DEFAULT-CDR))
 (4 2 (:REWRITE DEFAULT-CAR))
 )
(ZCASH::JUBJUB-R-DOUBLING-INJECTIVITY-WHEN-NEITHER-IS-ZERO<2K+1-TIMES-Y>
 (22 12 (:REWRITE DEFAULT-+-2))
 (18 10 (:REWRITE DEFAULT-*-2))
 (14 12 (:REWRITE DEFAULT-+-1))
 (12 10 (:REWRITE DEFAULT-*-1))
 (4 2 (:REWRITE DEFAULT-CDR))
 (4 2 (:REWRITE DEFAULT-CAR))
 )
(ZCASH::JUBJUB-R-DOUBLING-INJECTIVITY-WHEN-NEITHER-IS-ZERO<2K-TIMES-X-PLUS-X>
 (20 10 (:REWRITE DEFAULT-CDR))
 (20 10 (:REWRITE DEFAULT-CAR))
 (12 12 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (1 1 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 )
(ZCASH::JUBJUB-R-DOUBLING-INJECTIVITY-WHEN-NEITHER-IS-ZERO<2K-TIMES-Y-PLUS-Y>
 (20 10 (:REWRITE DEFAULT-CDR))
 (20 10 (:REWRITE DEFAULT-CAR))
 (12 12 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (1 1 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 )
(ZCASH::JUBJUB-R-DOUBLING-INJECTIVITY-WHEN-NEITHER-IS-ZERO<K-TIMES-2-TIMES-X-PLUS-X>
 (28 14 (:REWRITE DEFAULT-CDR))
 (28 14 (:REWRITE DEFAULT-CAR))
 (18 18 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (1 1 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 )
(ZCASH::JUBJUB-R-DOUBLING-INJECTIVITY-WHEN-NEITHER-IS-ZERO<K-TIMES-2-TIMES-Y-PLUS-Y>
 (28 14 (:REWRITE DEFAULT-CDR))
 (28 14 (:REWRITE DEFAULT-CAR))
 (18 18 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (1 1 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 )
(ZCASH::JUBJUB-R-DOUBLING-INJECTIVITY-WHEN-NEITHER-IS-ZERO<K-TIMES-2-TIMES-Y-PLUS-X>
 (10 6 (:REWRITE DEFAULT-*-2))
 (8 6 (:REWRITE DEFAULT-*-1))
 (8 4 (:REWRITE DEFAULT-CDR))
 (8 4 (:REWRITE DEFAULT-CAR))
 (8 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 )
(ZCASH::JUBJUB-R-DOUBLING-INJECTIVITY-WHEN-NEITHER-IS-ZERO<EQUALITY>
 (8 4 (:REWRITE DEFAULT-CDR))
 (8 4 (:REWRITE DEFAULT-CAR))
 (5 3 (:REWRITE DEFAULT-*-2))
 (4 3 (:REWRITE DEFAULT-*-1))
 (4 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 )
(ZCASH::JUBJUB-R-DOUBLING-INJECTIVITY-WHEN-NEITHER-IS-ZERO<ADD-SAME>
 (5 3 (:REWRITE DEFAULT-*-2))
 (4 3 (:REWRITE DEFAULT-*-1))
 (4 2 (:REWRITE DEFAULT-CDR))
 (4 2 (:REWRITE DEFAULT-CAR))
 (4 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 )
(ZCASH::JUBJUB-R-DOUBLING-INJECTIVITY-WHEN-NEITHER-IS-ZERO<POINT-COMMON>)
(ZCASH::JUBJUB-R-DOUBLING-INJECTIVITY-WHEN-NEITHER-IS-ZERO<POINT-NEG-COMMON>)
(ZCASH::JUBJUB-R-DOUBLING-INJECTIVITY-WHEN-NEITHER-IS-ZERO<SIMP-X>
 (25 13 (:REWRITE DEFAULT-*-2))
 (24 12 (:REWRITE DEFAULT-+-2))
 (14 13 (:REWRITE DEFAULT-*-1))
 (12 12 (:REWRITE DEFAULT-+-1))
 )
(ZCASH::JUBJUB-R-DOUBLING-INJECTIVITY-WHEN-NEITHER-IS-ZERO<SIMP-Y>
 (25 13 (:REWRITE DEFAULT-*-2))
 (24 12 (:REWRITE DEFAULT-+-2))
 (14 13 (:REWRITE DEFAULT-*-1))
 (12 12 (:REWRITE DEFAULT-+-1))
 )
(ZCASH::JUBJUB-R-DOUBLING-INJECTIVITY-WHEN-NEITHER-IS-ZERO<FINAL-EQUAL>)
(ZCASH::JUBJUB-R-DOUBLING-INJECTIVITY-WHEN-NEITHER-IS-ZERO)
(ZCASH::JUBJUB-R-DOUBLING-INJECTIVITY
 (697 52 (:REWRITE ZCASH::NOT-JUBJUB-R-POINTP-WHEN-0-ORDINATE))
 (232 232 (:TYPE-PRESCRIPTION ZCASH::NATP-OF-JUBJUB-POINT->V))
 (232 58 (:LINEAR ZCASH::JUBJUB-POINT->V-UPPER-BOUND))
 (172 77 (:REWRITE ZCASH::JUBJUB-POINTP-WHEN-JUBJUB-R-POINTP))
 (167 71 (:REWRITE ZCASH::JUBJUB-R-POINTP-WHEN-JUBJUB-RSTAR-POINTP))
 (96 96 (:TYPE-PRESCRIPTION ZCASH::JUBJUB-RSTAR-POINTP))
 (96 96 (:TYPE-PRESCRIPTION ZCASH::JUBJUB-POINTP))
 (58 58 (:TYPE-PRESCRIPTION ZCASH::JUBJUB-Q))
 (29 29 (:LINEAR ZCASH::JUBJUB-POINT->U-UPPER-BOUND))
 (28 14 (:REWRITE DEFAULT-CDR))
 (28 14 (:REWRITE DEFAULT-CAR))
 )
(ZCASH::ZERO-CASE<ZERO>)
(ZCASH::ZERO-CASE<POINT-0-M1>)
(ZCASH::ZERO-CASE<CONCLUSION>
 (6 2 (:REWRITE ZCASH::NOT-JUBJUB-R-POINTP-WHEN-0-ORDINATE))
 (6 2 (:REWRITE ZCASH::JUBJUB-R-POINTP-WHEN-JUBJUB-RSTAR-POINTP))
 (4 4 (:TYPE-PRESCRIPTION ECURVE::TWISTED-EDWARDS-ADD-ASSOCIATIVITY))
 (4 4 (:TYPE-PRESCRIPTION ZCASH::JUBJUB-RSTAR-POINTP))
 (4 2 (:REWRITE PFIELD::NEG-WHEN-NOT-POSP-ARG2-CHEAP))
 (4 2 (:REWRITE PFIELD::NEG-WHEN-NOT-INTEGERP-CHEAP))
 (4 2 (:REWRITE DEFAULT-CDR))
 (4 2 (:REWRITE DEFAULT-CAR))
 (2 2 (:TYPE-PRESCRIPTION ZCASH::NATP-OF-JUBJUB-POINT->V))
 (2 2 (:TYPE-PRESCRIPTION ZCASH::JUBJUB-Q))
 (2 2 (:REWRITE PFIELD::NEG-WHEN-CONSTANT-ARG1))
 )
(ZCASH::ZERO-CASE)
(ZCASH::NONZERO-CASE<ASSOCIATIVITY>)
(ZCASH::NONZERO-CASE<POINT>)
(ZCASH::NONZERO-CASE<NONZERO>)
(ZCASH::NONZERO-CASE<QOINT>)
(ZCASH::NONZERO-CASE<2-POINT>)
(ZCASH::NONZERO-CASE<2-QOINT-IS-MINUS-2-POINT>
 (249 128 (:REWRITE DEFAULT-CDR))
 (241 120 (:REWRITE DEFAULT-CAR))
 (189 127 (:REWRITE DEFAULT-<-2))
 (187 127 (:REWRITE DEFAULT-<-1))
 (166 17 (:REWRITE INTEGERP-OF-CAR-WHEN-INTEGER-LISTP))
 (131 82 (:REWRITE PFIELD::MUL-WHEN-NOT-INTEGERP-ARG2-CHEAP))
 (130 130 (:REWRITE PFIELD::MUL-OF--1-BECOMES-NEG-ALT))
 (109 109 (:REWRITE PFIELD::MUL-WHEN-EQUAL-OF-MOD-SUBST-ARG2))
 (109 109 (:REWRITE PFIELD::MUL-WHEN-EQUAL-OF-MOD-SUBST-ARG1))
 (109 109 (:REWRITE PFIELD::MUL-WHEN-CONSTANT-REDUCE-ARG1))
 (109 40 (:REWRITE PFIELD::NEG-WHEN-NOT-INTEGERP-CHEAP))
 (95 7 (:DEFINITION INTEGER-LISTP))
 (91 82 (:REWRITE PFIELD::MUL-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (89 40 (:REWRITE PFIELD::NEG-WHEN-NOT-POSP-ARG2-CHEAP))
 (80 9 (:REWRITE NATP-OF-CAR-WHEN-NAT-LISTP))
 (69 69 (:REWRITE PFIELD::EQUAL-OF-ADD-MOVE-NEGATIONS-BIND-FREE-2B))
 (69 69 (:REWRITE PFIELD::EQUAL-OF-ADD-MOVE-NEGATIONS-BIND-FREE-2A))
 (69 69 (:REWRITE PFIELD::EQUAL-OF-ADD-CANCEL-BIND-FREE))
 (38 2 (:REWRITE PFIELD::EQUAL-OF-NEG-SOLVE))
 (37 13 (:REWRITE INTEGER-LISTP-WHEN-NOT-CONSP))
 (36 20 (:REWRITE PFIELD::ADD-WHEN-NOT-INTEGERP-ARG2-CHEAP))
 (33 33 (:REWRITE PFIELD::NEG-WHEN-CONSTANT-ARG1))
 (33 3 (:REWRITE PFIELD::EQUAL-OF-ADD-COMBINE-CONSTANTS-ALT))
 (32 32 (:REWRITE PFIELD::MUL-OF-MUL-COMBINE-CONSTANTS))
 (32 32 (:REWRITE PFIELD::MUL-COMMUTATIVE-2))
 (31 31 (:REWRITE PFIELD::ADD-SUBST-CONSTANT-ARG2))
 (31 31 (:REWRITE PFIELD::ADD-SUBST-CONSTANT-ARG1))
 (30 20 (:REWRITE PFIELD::ADD-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (28 28 (:LINEAR ZCASH::JUBJUB-POINT->V-UPPER-BOUND))
 (28 28 (:LINEAR ZCASH::JUBJUB-POINT->U-UPPER-BOUND))
 (23 23 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 2))
 (23 23 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 1))
 (23 23 (:REWRITE ISAR::CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-FACT-INFO-ALISTP . 2))
 (23 23 (:REWRITE ISAR::CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-FACT-INFO-ALISTP . 1))
 (22 22 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (20 20 (:REWRITE PFIELD::NEG-OF-MUL-WHEN-CONSTANT))
 (20 20 (:REWRITE PFIELD::ADD-COMMUTATIVE))
 (20 8 (:REWRITE ZCASH::JUBJUB-R-POINTP-WHEN-JUBJUB-RSTAR-POINTP))
 (15 3 (:REWRITE PFIELD::EQUAL-OF-ADD-COMBINE-CONSTANTS))
 (15 3 (:REWRITE PFIELD::EQUAL-OF-0-AND-ADD-SAFE))
 (12 12 (:TYPE-PRESCRIPTION ZCASH::JUBJUB-RSTAR-POINTP))
 (12 6 (:REWRITE INTEGER-LISTP-OF-CDR-WHEN-INTEGER-LISTP))
 (11 11 (:TYPE-PRESCRIPTION PFIELD::NATP-OF-INV))
 (11 11 (:REWRITE PFIELD::FEP-WHEN-CONSTANT))
 (8 4 (:REWRITE IFIX-WHEN-NOT-INTEGERP-UNLIMITED))
 (6 6 (:REWRITE NATP-LISTP-WHEN-DAB-DIGIT-LISTP))
 (6 6 (:REWRITE NAT-LISTP-WHEN-UNSIGNED-BYTE-LISTP))
 (6 6 (:REWRITE NAT-LISTP-WHEN-NOT-CONSP))
 (4 4 (:REWRITE PFIELD::ADD-OF-MUL-AND-MUL-COMBINE-CONSTANTS))
 )
(ZCASH::NONZERO-CASE<2-QOINT-IS-M1-2-POINT>
 (10 2 (:REWRITE ECURVE::TWISTED-EDWARDS-NEG-OF-MUL))
 (6 6 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (5 1 (:REWRITE ECURVE::POINT-ON-TWISTED-EDWARDS-P-OF-TWISTED-EDWARDS-MUL))
 (4 2 (:REWRITE DEFAULT-CDR))
 (4 2 (:REWRITE DEFAULT-CAR))
 (3 3 (:TYPE-PRESCRIPTION ECURVE::TWISTED-EDWARDS-CURVE-COMPLETEP))
 (3 3 (:REWRITE ZCASH::TWISTED-EDWARDS-CURVE-COMPLETEP-OF-JUBJUB-CURVE))
 (3 1 (:REWRITE ECURVE::TWISTED-EDWARDS-MUL-OF-MUL))
 (2 2 (:TYPE-PRESCRIPTION ECURVE::TWISTED-EDWARDS-ADD-ASSOCIATIVITY))
 (2 1 (:REWRITE PFIELD::NEG-WHEN-NOT-POSP-ARG2-CHEAP))
 (2 1 (:REWRITE PFIELD::NEG-WHEN-NOT-INTEGERP-CHEAP))
 (1 1 (:TYPE-PRESCRIPTION ZCASH::JUBJUB-Q))
 (1 1 (:REWRITE PFIELD::NEG-WHEN-CONSTANT-ARG1))
 )
(ZCASH::NONZERO-CASE<2-QOINT-IS-2-M1-POINT>
 (20 20 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (16 8 (:REWRITE DEFAULT-CDR))
 (16 8 (:REWRITE DEFAULT-CAR))
 (6 3 (:REWRITE PFIELD::NEG-WHEN-NOT-POSP-ARG2-CHEAP))
 (6 3 (:REWRITE PFIELD::NEG-WHEN-NOT-INTEGERP-CHEAP))
 (3 3 (:TYPE-PRESCRIPTION ZCASH::JUBJUB-Q))
 (3 3 (:REWRITE PFIELD::NEG-WHEN-CONSTANT-ARG1))
 )
(ZCASH::NONZERO-CASE<2-QOINT-IS-2-MINUS-POINT>
 (17 17 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (16 8 (:REWRITE DEFAULT-CDR))
 (16 8 (:REWRITE DEFAULT-CAR))
 (6 3 (:REWRITE PFIELD::NEG-WHEN-NOT-POSP-ARG2-CHEAP))
 (6 3 (:REWRITE PFIELD::NEG-WHEN-NOT-INTEGERP-CHEAP))
 (3 3 (:TYPE-PRESCRIPTION ZCASH::JUBJUB-Q))
 (3 3 (:REWRITE PFIELD::NEG-WHEN-CONSTANT-ARG1))
 (3 1 (:REWRITE ECURVE::TWISTED-EDWARDS-MUL-OF-MUL))
 (2 2 (:TYPE-PRESCRIPTION ECURVE::TWISTED-EDWARDS-ADD-ASSOCIATIVITY))
 )
(ZCASH::NONZERO-CASE<QOINT-IS-MINUS-POINT>
 (99 13 (:REWRITE ZCASH::NOT-JUBJUB-R-POINTP-WHEN-0-ORDINATE))
 (50 20 (:REWRITE ZCASH::JUBJUB-R-POINTP-WHEN-JUBJUB-RSTAR-POINTP))
 (44 9 (:REWRITE ZCASH::JUBJUB-POINTP-WHEN-JUBJUB-R-POINTP))
 (32 16 (:REWRITE DEFAULT-CDR))
 (32 16 (:REWRITE DEFAULT-CAR))
 (30 30 (:TYPE-PRESCRIPTION ZCASH::JUBJUB-RSTAR-POINTP))
 (25 5 (:REWRITE ZCASH::ZERO-CASE))
 (22 11 (:REWRITE PFIELD::NEG-WHEN-NOT-POSP-ARG2-CHEAP))
 (22 11 (:REWRITE PFIELD::NEG-WHEN-NOT-INTEGERP-CHEAP))
 (20 20 (:TYPE-PRESCRIPTION ECURVE::TWISTED-EDWARDS-ZERO))
 (16 2 (:LINEAR ZCASH::JUBJUB-POINT->V-UPPER-BOUND))
 (15 3 (:REWRITE ZCASH::JUBJUB-POINTP-OF-JUBJUB-NEG))
 (14 14 (:TYPE-PRESCRIPTION ZCASH::JUBJUB-POINTP))
 (13 13 (:TYPE-PRESCRIPTION ZCASH::JUBJUB-Q))
 (11 11 (:REWRITE PFIELD::NEG-WHEN-CONSTANT-ARG1))
 (1 1 (:LINEAR ZCASH::JUBJUB-POINT->U-UPPER-BOUND))
 )
(ZCASH::NONZERO-CASE<NEG-V-IS-V>
 (232 24 (:REWRITE INTEGERP-OF-CAR-WHEN-INTEGER-LISTP))
 (183 12 (:DEFINITION INTEGER-LISTP))
 (72 24 (:REWRITE INTEGER-LISTP-WHEN-NOT-CONSP))
 (66 63 (:REWRITE DEFAULT-CAR))
 (66 11 (:REWRITE NATP-OF-CAR-WHEN-NAT-LISTP))
 (60 57 (:REWRITE DEFAULT-CDR))
 (39 35 (:REWRITE DEFAULT-<-1))
 (35 35 (:REWRITE DEFAULT-<-2))
 (31 31 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 2))
 (31 31 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 1))
 (31 31 (:REWRITE ISAR::CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-FACT-INFO-ALISTP . 2))
 (31 31 (:REWRITE ISAR::CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-FACT-INFO-ALISTP . 1))
 (27 11 (:REWRITE PFIELD::NEG-WHEN-NOT-POSP-ARG2-CHEAP))
 (24 12 (:REWRITE INTEGER-LISTP-OF-CDR-WHEN-INTEGER-LISTP))
 (14 11 (:REWRITE PFIELD::NEG-WHEN-NOT-INTEGERP-CHEAP))
 (11 11 (:REWRITE NATP-LISTP-WHEN-DAB-DIGIT-LISTP))
 (11 11 (:REWRITE NAT-LISTP-WHEN-UNSIGNED-BYTE-LISTP))
 (11 11 (:REWRITE NAT-LISTP-WHEN-NOT-CONSP))
 (8 8 (:REWRITE PFIELD::NEG-WHEN-CONSTANT-ARG1))
 (7 7 (:REWRITE PFIELD::EQUAL-OF-NEG-SOLVE))
 (6 6 (:TYPE-PRESCRIPTION ZCASH::JUBJUB-Q))
 (5 5 (:TYPE-PRESCRIPTION ECURVE::TWISTED-EDWARDS-CURVE->P$INLINE))
 (5 5 (:TYPE-PRESCRIPTION ECURVE::POSP-OF-TWISTED-EDWARDS-CURVE->P))
 (4 4 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 )
(ZCASH::NONZERO-CASE<V-IS-0>
 (9 3 (:REWRITE ZCASH::JUBJUB-R-POINTP-WHEN-JUBJUB-RSTAR-POINTP))
 (6 6 (:TYPE-PRESCRIPTION ZCASH::JUBJUB-RSTAR-POINTP))
 (6 4 (:REWRITE PFIELD::NEG-WHEN-NOT-INTEGERP-CHEAP))
 (4 4 (:REWRITE PFIELD::NEG-WHEN-NOT-POSP-ARG2-CHEAP))
 (4 4 (:REWRITE PFIELD::NEG-WHEN-CONSTANT-ARG1))
 (3 3 (:REWRITE PFIELD::FEP-WHEN-CONSTANT))
 (2 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE PFIELD::EQUAL-OF-NEG-SOLVE))
 (1 1 (:REWRITE DEFAULT-<-2))
 )
(ZCASH::NONZERO-CASE<NOT-POINT>
 (3 1 (:REWRITE ZCASH::JUBJUB-R-POINTP-WHEN-JUBJUB-RSTAR-POINTP))
 (2 2 (:TYPE-PRESCRIPTION ZCASH::JUBJUB-RSTAR-POINTP))
 (2 1 (:REWRITE PFIELD::NEG-WHEN-NOT-POSP-ARG2-CHEAP))
 (2 1 (:REWRITE PFIELD::NEG-WHEN-NOT-INTEGERP-CHEAP))
 (1 1 (:TYPE-PRESCRIPTION ZCASH::JUBJUB-Q))
 (1 1 (:REWRITE PFIELD::NEG-WHEN-CONSTANT-ARG1))
 )
(ZCASH::NONZERO-CASE<CONTRADICTION>)
(ZCASH::NONZERO-CASE)
(ZCASH::NOT-JUBJUB-R-POINTP-OF-JUBJUB-R-POINT-WITH-NEG-ORDINATE)
(ZCASH::D-SQUARE-WHEN-1-D-USQUARE-IS-ZERO<Q>)
(ZCASH::D-SQUARE-WHEN-1-D-USQUARE-IS-ZERO<U>)
(ZCASH::D-SQUARE-WHEN-1-D-USQUARE-IS-ZERO<D>)
(ZCASH::D-SQUARE-WHEN-1-D-USQUARE-IS-ZERO<1-D.U^2=0>)
(ZCASH::D-SQUARE-WHEN-1-D-USQUARE-IS-ZERO<U^2=1/D>
 (6 4 (:REWRITE PFIELD::MUL-WHEN-NOT-INTEGERP-ARG2-CHEAP))
 (6 2 (:DEFINITION NATP))
 (5 5 (:REWRITE PFIELD::ADD-SUBST-CONSTANT-ARG2))
 (5 5 (:REWRITE PFIELD::ADD-SUBST-CONSTANT-ARG1))
 (4 4 (:REWRITE PFIELD::MUL-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (4 4 (:REWRITE PFIELD::MUL-WHEN-EQUAL-OF-MOD-SUBST-ARG2))
 (4 4 (:REWRITE PFIELD::MUL-WHEN-EQUAL-OF-MOD-SUBST-ARG1))
 (4 4 (:REWRITE PFIELD::MUL-WHEN-CONSTANT-REDUCE-ARG1))
 (4 4 (:REWRITE PFIELD::MUL-OF--1-BECOMES-NEG-ALT))
 (4 4 (:REWRITE PFIELD::MUL-COMMUTATIVE))
 (4 4 (:REWRITE PFIELD::EQUAL-OF-ADD-MOVE-NEGATIONS-BIND-FREE-2B))
 (4 2 (:REWRITE PFIELD::ADD-WHEN-NOT-INTEGERP-ARG2-CHEAP))
 (3 3 (:REWRITE PFIELD::EQUAL-OF-ADD-CANCEL-BIND-FREE))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 (2 2 (:REWRITE PFIELD::MUL-OF-MUL-COMBINE-CONSTANTS))
 (2 2 (:REWRITE PFIELD::MUL-COMMUTATIVE-2))
 (2 2 (:REWRITE PFIELD::FEP-WHEN-CONSTANT))
 (2 2 (:REWRITE PFIELD::EQUAL-OF-MUL-CONSTANTS-ALT))
 (2 2 (:REWRITE PFIELD::EQUAL-OF-MUL-CONSTANTS))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE PFIELD::ADD-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (2 2 (:REWRITE PFIELD::ADD-COMMUTATIVE))
 (2 1 (:REWRITE PFIELD::NEG-WHEN-NOT-INTEGERP-CHEAP))
 (2 1 (:REWRITE IFIX-WHEN-NOT-INTEGERP-UNLIMITED))
 (1 1 (:TYPE-PRESCRIPTION PFIELD::NATP-OF-NEG))
 (1 1 (:REWRITE PFIELD::SUB-WHEN-CONSTANTS))
 (1 1 (:REWRITE NOT-PRIMEP-WHEN-DIVIDES))
 (1 1 (:REWRITE PFIELD::NEG-WHEN-NOT-POSP-ARG2-CHEAP))
 (1 1 (:REWRITE PFIELD::NEG-WHEN-CONSTANT-ARG1))
 (1 1 (:REWRITE PFIELD::NEG-OF-MUL-WHEN-CONSTANT))
 )
(ZCASH::D-SQUARE-WHEN-1-D-USQUARE-IS-ZERO<1/D-SQUARE>)
(ZCASH::D-SQUARE-WHEN-1-D-USQUARE-IS-ZERO<D-SQUARE>)
(ZCASH::D-SQUARE-WHEN-1-D-USQUARE-IS-ZERO)
(ZCASH::JUBJUB-POINT-RESOLVE-SQUARE-ORDINATE<POINT>)
(ZCASH::JUBJUB-POINT-RESOLVE-SQUARE-ORDINATE<CURVE-EQUATION>
 (22 11 (:REWRITE PFIELD::MUL-WHEN-NOT-INTEGERP-ARG2-CHEAP))
 (22 11 (:REWRITE PFIELD::MUL-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (13 13 (:REWRITE PFIELD::MUL-WHEN-EQUAL-OF-MOD-SUBST-ARG2))
 (13 13 (:REWRITE PFIELD::MUL-WHEN-EQUAL-OF-MOD-SUBST-ARG1))
 (13 13 (:REWRITE PFIELD::MUL-WHEN-CONSTANT-REDUCE-ARG1))
 (11 11 (:REWRITE PFIELD::MUL-COMMUTATIVE))
 (9 9 (:REWRITE PFIELD::MUL-OF-MUL-COMBINE-CONSTANTS))
 (7 7 (:REWRITE PFIELD::MUL-COMMUTATIVE-2))
 (6 1 (:REWRITE ZCASH::JUBJUB-POINTP-WHEN-JUBJUB-R-POINTP))
 (4 2 (:REWRITE PFIELD::ADD-WHEN-NOT-INTEGERP-ARG2-CHEAP))
 (3 1 (:REWRITE ZCASH::JUBJUB-R-POINTP-WHEN-JUBJUB-RSTAR-POINTP))
 (2 2 (:TYPE-PRESCRIPTION ZCASH::JUBJUB-RSTAR-POINTP))
 (2 2 (:TYPE-PRESCRIPTION ZCASH::JUBJUB-R-POINTP))
 (2 2 (:TYPE-PRESCRIPTION ZCASH::JUBJUB-D))
 (2 2 (:REWRITE PFIELD::ADD-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (2 2 (:REWRITE PFIELD::ADD-OF-CONSTANTS))
 (2 2 (:REWRITE PFIELD::ADD-COMMUTATIVE))
 (1 1 (:TYPE-PRESCRIPTION ZCASH::JUBJUB-A))
 )
(ZCASH::JUBJUB-POINT-RESOLVE-SQUARE-ORDINATE<SEPARATE>
 (38 19 (:REWRITE PFIELD::MUL-WHEN-NOT-INTEGERP-ARG2-CHEAP))
 (37 19 (:REWRITE PFIELD::MUL-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (31 31 (:REWRITE PFIELD::MUL-OF--1-BECOMES-NEG-ALT))
 (27 27 (:REWRITE PFIELD::MUL-WHEN-EQUAL-OF-MOD-SUBST-ARG2))
 (27 27 (:REWRITE PFIELD::MUL-WHEN-EQUAL-OF-MOD-SUBST-ARG1))
 (27 27 (:REWRITE PFIELD::MUL-WHEN-CONSTANT-REDUCE-ARG1))
 (24 12 (:REWRITE PFIELD::ADD-WHEN-NOT-INTEGERP-ARG2-CHEAP))
 (20 20 (:REWRITE PFIELD::ADD-SUBST-CONSTANT-ARG2))
 (20 20 (:REWRITE PFIELD::ADD-SUBST-CONSTANT-ARG1))
 (17 17 (:REWRITE PFIELD::MUL-OF-MUL-COMBINE-CONSTANTS))
 (17 12 (:REWRITE PFIELD::ADD-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (16 16 (:REWRITE PFIELD::ADD-OF-CONSTANTS))
 (12 2 (:REWRITE ZCASH::JUBJUB-POINTP-WHEN-JUBJUB-R-POINTP))
 (9 1 (:REWRITE ZCASH::FEP-OF-JUBJUB-POINT->V))
 (9 1 (:LINEAR ZCASH::JUBJUB-POINT->V-UPPER-BOUND))
 (8 4 (:REWRITE PFIELD::NEG-WHEN-NOT-POSP-ARG2-CHEAP))
 (8 4 (:REWRITE PFIELD::NEG-WHEN-NOT-INTEGERP-CHEAP))
 (6 3 (:REWRITE IFIX-WHEN-NOT-INTEGERP-UNLIMITED))
 (6 2 (:REWRITE ZCASH::JUBJUB-R-POINTP-WHEN-JUBJUB-RSTAR-POINTP))
 (5 5 (:TYPE-PRESCRIPTION PFIELD::NATP-OF-NEG))
 (4 4 (:TYPE-PRESCRIPTION ZCASH::JUBJUB-RSTAR-POINTP))
 (4 4 (:TYPE-PRESCRIPTION ZCASH::JUBJUB-R-POINTP))
 (4 4 (:TYPE-PRESCRIPTION ZCASH::JUBJUB-POINTP))
 (4 4 (:TYPE-PRESCRIPTION ZCASH::JUBJUB-D))
 (4 4 (:REWRITE PFIELD::NEG-WHEN-CONSTANT-ARG1))
 (4 4 (:REWRITE PFIELD::NEG-OF-MUL-WHEN-CONSTANT))
 (2 2 (:TYPE-PRESCRIPTION ZCASH::JUBJUB-A))
 (2 2 (:REWRITE PFIELD::SUB-WHEN-CONSTANTS))
 (2 2 (:REWRITE PFIELD::ADD-OF-ADD-COMBINE-CONSTANTS))
 (2 1 (:REWRITE DEFAULT-<-2))
 (2 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE PFIELD::FEP-WHEN-CONSTANT))
 (1 1 (:REWRITE PFIELD::EQUAL-OF-ADD-COMBINE-CONSTANTS-ALT))
 (1 1 (:REWRITE PFIELD::EQUAL-OF-ADD-COMBINE-CONSTANTS))
 (1 1 (:REWRITE PFIELD::EQUAL-OF-ADD-CANCEL-BIND-FREE))
 )
(ZCASH::JUBJUB-POINT-RESOLVE-SQUARE-ORDINATE<NONZERO>
 (18 3 (:REWRITE ZCASH::JUBJUB-POINTP-WHEN-JUBJUB-R-POINTP))
 (11 6 (:REWRITE PFIELD::MUL-WHEN-NOT-INTEGERP-ARG2-CHEAP))
 (11 6 (:REWRITE PFIELD::MUL-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (9 3 (:REWRITE ZCASH::JUBJUB-R-POINTP-WHEN-JUBJUB-RSTAR-POINTP))
 (9 1 (:REWRITE ZCASH::FEP-OF-JUBJUB-POINT->U))
 (6 6 (:TYPE-PRESCRIPTION PFIELD::NATP-OF-MUL))
 (6 6 (:TYPE-PRESCRIPTION ZCASH::JUBJUB-RSTAR-POINTP))
 (6 6 (:TYPE-PRESCRIPTION ZCASH::JUBJUB-R-POINTP))
 (6 6 (:REWRITE PFIELD::MUL-WHEN-EQUAL-OF-MOD-SUBST-ARG2))
 (6 6 (:REWRITE PFIELD::MUL-WHEN-EQUAL-OF-MOD-SUBST-ARG1))
 (6 6 (:REWRITE PFIELD::MUL-WHEN-CONSTANT-REDUCE-ARG1))
 (6 6 (:REWRITE PFIELD::MUL-COMMUTATIVE))
 (6 3 (:REWRITE PFIELD::NEG-WHEN-NOT-POSP-ARG2-CHEAP))
 (6 3 (:REWRITE PFIELD::NEG-WHEN-NOT-INTEGERP-CHEAP))
 (6 3 (:REWRITE PFIELD::ADD-WHEN-NOT-INTEGERP-ARG2-CHEAP))
 (3 3 (:TYPE-PRESCRIPTION PFIELD::NATP-OF-NEG))
 (3 3 (:REWRITE PFIELD::SUB-WHEN-CONSTANTS))
 (3 3 (:REWRITE PFIELD::NEG-WHEN-CONSTANT-ARG1))
 (3 3 (:REWRITE PFIELD::MUL-OF-MUL-COMBINE-CONSTANTS))
 (3 3 (:REWRITE PFIELD::MUL-COMMUTATIVE-2))
 (3 3 (:REWRITE PFIELD::ADD-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (3 3 (:REWRITE PFIELD::ADD-OF-CONSTANTS))
 (3 3 (:REWRITE PFIELD::ADD-COMMUTATIVE))
 (2 1 (:REWRITE DEFAULT-<-2))
 (2 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE PFIELD::FEP-WHEN-CONSTANT))
 )
(ZCASH::JUBJUB-POINT-RESOLVE-SQUARE-ORDINATE<CONCLUSION>
 (38 19 (:REWRITE PFIELD::MUL-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (37 19 (:REWRITE PFIELD::MUL-WHEN-NOT-INTEGERP-ARG2-CHEAP))
 (19 19 (:REWRITE PFIELD::MUL-WHEN-EQUAL-OF-MOD-SUBST-ARG2))
 (19 19 (:REWRITE PFIELD::MUL-WHEN-EQUAL-OF-MOD-SUBST-ARG1))
 (19 19 (:REWRITE PFIELD::MUL-WHEN-CONSTANT-REDUCE-ARG1))
 (19 19 (:REWRITE PFIELD::MUL-COMMUTATIVE))
 (14 7 (:REWRITE PFIELD::NEG-WHEN-NOT-POSP-ARG2-CHEAP))
 (14 7 (:REWRITE PFIELD::NEG-WHEN-NOT-INTEGERP-CHEAP))
 (14 7 (:REWRITE PFIELD::ADD-WHEN-NOT-INTEGERP-ARG2-CHEAP))
 (8 2 (:LINEAR ZCASH::JUBJUB-POINT->V-UPPER-BOUND))
 (7 7 (:TYPE-PRESCRIPTION PFIELD::NATP-OF-NEG))
 (7 7 (:REWRITE PFIELD::NEG-WHEN-CONSTANT-ARG1))
 (7 7 (:REWRITE PFIELD::MUL-OF-MUL-COMBINE-CONSTANTS))
 (7 7 (:REWRITE PFIELD::MUL-COMMUTATIVE-2))
 (7 7 (:REWRITE PFIELD::ADD-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (7 7 (:REWRITE PFIELD::ADD-OF-CONSTANTS))
 (7 7 (:REWRITE PFIELD::ADD-COMMUTATIVE))
 (7 2 (:LINEAR ZCASH::JUBJUB-POINT->U-UPPER-BOUND))
 (6 1 (:REWRITE ZCASH::JUBJUB-POINTP-WHEN-JUBJUB-R-POINTP))
 (5 5 (:REWRITE PFIELD::SUB-WHEN-CONSTANTS))
 (4 4 (:TYPE-PRESCRIPTION ZCASH::JUBJUB-D))
 (3 3 (:TYPE-PRESCRIPTION ZCASH::JUBJUB-A))
 (3 1 (:REWRITE ZCASH::JUBJUB-R-POINTP-WHEN-JUBJUB-RSTAR-POINTP))
 (3 1 (:REWRITE PFIELD::FEP-OF-DIV))
 (2 2 (:TYPE-PRESCRIPTION ZCASH::JUBJUB-RSTAR-POINTP))
 (2 2 (:TYPE-PRESCRIPTION ZCASH::JUBJUB-R-POINTP))
 (2 2 (:REWRITE ZCASH::FEP-OF-JUBJUB-POINT->V))
 )
(ZCASH::JUBJUB-POINT-RESOLVE-SQUARE-ORDINATE)
(ZCASH::INJECTIVITY-LEMMA<ASSOCIATIVITY>)
(ZCASH::INJECTIVITY-LEMMA<POINT>)
(ZCASH::INJECTIVITY-LEMMA<QOINT>)
(ZCASH::INJECTIVITY-LEMMA<EQUAL-U-U>)
(ZCASH::INJECTIVITY-LEMMA<EQUAL-VP^2-VQ^2>
 (76 38 (:REWRITE PFIELD::MUL-WHEN-NOT-INTEGERP-ARG2-CHEAP))
 (76 38 (:REWRITE PFIELD::MUL-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (38 38 (:REWRITE PFIELD::MUL-WHEN-EQUAL-OF-MOD-SUBST-ARG2))
 (38 38 (:REWRITE PFIELD::MUL-WHEN-EQUAL-OF-MOD-SUBST-ARG1))
 (38 38 (:REWRITE PFIELD::MUL-WHEN-CONSTANT-REDUCE-ARG1))
 (38 38 (:REWRITE PFIELD::MUL-COMMUTATIVE))
 (33 11 (:REWRITE ZCASH::JUBJUB-R-POINTP-WHEN-JUBJUB-RSTAR-POINTP))
 (24 12 (:REWRITE PFIELD::NEG-WHEN-NOT-POSP-ARG2-CHEAP))
 (24 12 (:REWRITE PFIELD::NEG-WHEN-NOT-INTEGERP-CHEAP))
 (24 12 (:REWRITE PFIELD::ADD-WHEN-NOT-INTEGERP-ARG2-CHEAP))
 (24 8 (:REWRITE ZCASH::NOT-JUBJUB-R-POINTP-WHEN-0-ORDINATE))
 (22 22 (:TYPE-PRESCRIPTION ZCASH::JUBJUB-RSTAR-POINTP))
 (16 16 (:TYPE-PRESCRIPTION ECURVE::TWISTED-EDWARDS-ADD-ASSOCIATIVITY))
 (12 12 (:TYPE-PRESCRIPTION PFIELD::NATP-OF-NEG))
 (12 12 (:REWRITE PFIELD::NEG-WHEN-CONSTANT-ARG1))
 (12 12 (:REWRITE PFIELD::MUL-OF-MUL-COMBINE-CONSTANTS))
 (12 12 (:REWRITE PFIELD::MUL-COMMUTATIVE-2))
 (12 12 (:REWRITE PFIELD::ADD-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (12 12 (:REWRITE PFIELD::ADD-OF-CONSTANTS))
 (12 12 (:REWRITE PFIELD::ADD-COMMUTATIVE))
 (6 6 (:TYPE-PRESCRIPTION ZCASH::JUBJUB-D))
 (6 6 (:TYPE-PRESCRIPTION ZCASH::JUBJUB-A))
 (6 6 (:REWRITE PFIELD::SUB-WHEN-CONSTANTS))
 (3 3 (:LINEAR ZCASH::JUBJUB-POINT->V-UPPER-BOUND))
 )
(ZCASH::INJECTIVITY-LEMMA<REFACTOR>
 (15 15 (:REWRITE PFIELD::ADD-SUBST-CONSTANT-ARG2))
 (15 15 (:REWRITE PFIELD::ADD-SUBST-CONSTANT-ARG1))
 (13 1 (:REWRITE PFIELD::FEP-HOLDS))
 (12 12 (:REWRITE PFIELD::ADD-OF-CONSTANTS))
 (12 6 (:REWRITE PFIELD::MUL-WHEN-NOT-INTEGERP-ARG2-CHEAP))
 (12 6 (:REWRITE PFIELD::MUL-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (12 6 (:REWRITE PFIELD::ADD-WHEN-NOT-INTEGERP-ARG2-CHEAP))
 (11 11 (:REWRITE PFIELD::MUL-OF--1-BECOMES-NEG-ALT))
 (11 6 (:REWRITE PFIELD::ADD-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (7 7 (:REWRITE PFIELD::MUL-WHEN-EQUAL-OF-MOD-SUBST-ARG2))
 (7 7 (:REWRITE PFIELD::MUL-WHEN-EQUAL-OF-MOD-SUBST-ARG1))
 (7 7 (:REWRITE PFIELD::MUL-WHEN-CONSTANT-REDUCE-ARG1))
 (6 3 (:REWRITE PFIELD::NEG-WHEN-NOT-POSP-ARG2-CHEAP))
 (6 3 (:REWRITE PFIELD::NEG-WHEN-NOT-INTEGERP-CHEAP))
 (3 3 (:REWRITE PFIELD::NEG-WHEN-CONSTANT-ARG1))
 (3 1 (:REWRITE ZCASH::NOT-JUBJUB-R-POINTP-WHEN-0-ORDINATE))
 (3 1 (:REWRITE ZCASH::JUBJUB-R-POINTP-WHEN-JUBJUB-RSTAR-POINTP))
 (2 2 (:TYPE-PRESCRIPTION ECURVE::TWISTED-EDWARDS-ADD-ASSOCIATIVITY))
 (2 2 (:TYPE-PRESCRIPTION ZCASH::JUBJUB-RSTAR-POINTP))
 (2 2 (:REWRITE PFIELD::NEG-OF-MUL-WHEN-CONSTANT))
 (2 2 (:REWRITE PFIELD::ADD-OF-ADD-COMBINE-CONSTANTS))
 (2 2 (:REWRITE PFIELD::ADD-ASSOCIATIVE-WHEN-CONSTANT))
 (2 1 (:REWRITE IFIX-WHEN-NOT-INTEGERP-UNLIMITED))
 (2 1 (:REWRITE DEFAULT-<-2))
 (2 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE PFIELD::SUB-WHEN-CONSTANTS))
 (1 1 (:REWRITE PFIELD::EQUAL-OF-MUL-CONSTANTS-ALT))
 (1 1 (:REWRITE PFIELD::EQUAL-OF-MUL-CONSTANTS))
 (1 1 (:REWRITE PFIELD::EQUAL-OF-ADD-MOVE-NEGATIONS-BIND-FREE-2B))
 (1 1 (:REWRITE PFIELD::EQUAL-OF-ADD-MOVE-NEGATIONS-BIND-FREE-2A))
 (1 1 (:REWRITE PFIELD::EQUAL-OF-ADD-CANCEL-BIND-FREE))
 (1 1 (:REWRITE PFIELD::ADD-COMMUTATIVE-2-WHEN-CONSTANT))
 )
(ZCASH::INJECTIVITY-LEMMA<VQ-DISJUNCTION>
 (78 39 (:REWRITE PFIELD::ADD-WHEN-NOT-INTEGERP-ARG2-CHEAP))
 (76 76 (:REWRITE PFIELD::ADD-SUBST-CONSTANT-ARG2))
 (76 76 (:REWRITE PFIELD::ADD-SUBST-CONSTANT-ARG1))
 (69 39 (:REWRITE PFIELD::ADD-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (36 12 (:REWRITE ZCASH::JUBJUB-R-POINTP-WHEN-JUBJUB-RSTAR-POINTP))
 (36 4 (:REWRITE ZCASH::FEP-OF-JUBJUB-POINT->V))
 (35 35 (:REWRITE PFIELD::MUL-OF--1-BECOMES-NEG-ALT))
 (32 16 (:REWRITE PFIELD::NEG-WHEN-NOT-POSP-ARG2-CHEAP))
 (32 16 (:REWRITE PFIELD::MUL-WHEN-NOT-INTEGERP-ARG2-CHEAP))
 (31 16 (:REWRITE PFIELD::NEG-WHEN-NOT-INTEGERP-CHEAP))
 (30 16 (:REWRITE PFIELD::MUL-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (24 24 (:TYPE-PRESCRIPTION ZCASH::JUBJUB-RSTAR-POINTP))
 (22 11 (:REWRITE IFIX-WHEN-NOT-INTEGERP-UNLIMITED))
 (21 21 (:REWRITE PFIELD::MUL-WHEN-EQUAL-OF-MOD-SUBST-ARG2))
 (21 21 (:REWRITE PFIELD::MUL-WHEN-EQUAL-OF-MOD-SUBST-ARG1))
 (21 21 (:REWRITE PFIELD::MUL-WHEN-CONSTANT-REDUCE-ARG1))
 (15 15 (:REWRITE PFIELD::NEG-WHEN-CONSTANT-ARG1))
 (12 4 (:REWRITE ZCASH::NOT-JUBJUB-R-POINTP-WHEN-0-ORDINATE))
 (10 10 (:REWRITE PFIELD::ADD-OF-ADD-COMBINE-CONSTANTS))
 (10 5 (:REWRITE DEFAULT-<-2))
 (10 5 (:REWRITE DEFAULT-<-1))
 (9 9 (:REWRITE PFIELD::EQUAL-OF-ADD-CANCEL-BIND-FREE))
 (8 8 (:TYPE-PRESCRIPTION ECURVE::TWISTED-EDWARDS-ADD-ASSOCIATIVITY))
 (7 7 (:REWRITE PFIELD::SUB-WHEN-CONSTANTS))
 (6 6 (:REWRITE PFIELD::NEG-OF-MUL-WHEN-CONSTANT))
 (6 6 (:REWRITE PFIELD::ADD-ASSOCIATIVE-WHEN-CONSTANT))
 (4 4 (:REWRITE PFIELD::FEP-WHEN-CONSTANT))
 (4 4 (:LINEAR ZCASH::JUBJUB-POINT->U-UPPER-BOUND))
 (3 3 (:REWRITE PFIELD::ADD-COMMUTATIVE-2-WHEN-CONSTANT))
 (2 2 (:REWRITE PFIELD::EQUAL-OF-MUL-CONSTANTS-ALT))
 (2 2 (:REWRITE PFIELD::EQUAL-OF-MUL-CONSTANTS))
 (2 2 (:REWRITE PFIELD::EQUAL-OF-ADD-COMBINE-CONSTANTS-ALT))
 (2 2 (:REWRITE PFIELD::EQUAL-OF-ADD-COMBINE-CONSTANTS))
 (2 2 (:REWRITE PFIELD::EQUAL-OF-0-AND-ADD-SAFE))
 (2 2 (:REWRITE PFIELD::ADD-OF-MUL-AND-MUL-COMBINE-CONSTANTS))
 )
(ZCASH::INJECTIVITY-LEMMA<QOINT-DISJUNCTION>
 (825 90 (:REWRITE INTEGERP-OF-CAR-WHEN-INTEGER-LISTP))
 (645 43 (:DEFINITION INTEGER-LISTP))
 (328 282 (:REWRITE DEFAULT-CAR))
 (296 260 (:REWRITE DEFAULT-CDR))
 (258 86 (:REWRITE INTEGER-LISTP-WHEN-NOT-CONSP))
 (258 43 (:REWRITE NATP-OF-CAR-WHEN-NAT-LISTP))
 (124 116 (:REWRITE DEFAULT-<-1))
 (116 116 (:REWRITE DEFAULT-<-2))
 (107 107 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 2))
 (107 107 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 1))
 (107 107 (:REWRITE ISAR::CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-FACT-INFO-ALISTP . 2))
 (107 107 (:REWRITE ISAR::CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-FACT-INFO-ALISTP . 1))
 (86 43 (:REWRITE INTEGER-LISTP-OF-CDR-WHEN-INTEGER-LISTP))
 (43 43 (:REWRITE NATP-LISTP-WHEN-DAB-DIGIT-LISTP))
 (43 43 (:REWRITE NAT-LISTP-WHEN-UNSIGNED-BYTE-LISTP))
 (43 43 (:REWRITE NAT-LISTP-WHEN-NOT-CONSP))
 (38 19 (:REWRITE PFIELD::NEG-WHEN-NOT-POSP-ARG2-CHEAP))
 (25 19 (:REWRITE PFIELD::NEG-WHEN-NOT-INTEGERP-CHEAP))
 (19 19 (:TYPE-PRESCRIPTION ZCASH::JUBJUB-Q))
 (16 16 (:REWRITE PFIELD::NEG-WHEN-CONSTANT-ARG1))
 (9 6 (:REWRITE PFIELD::EQUAL-OF-NEG-SOLVE))
 (4 4 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (2 2 (:TYPE-PRESCRIPTION PFIELD::FEP))
 (1 1 (:REWRITE PFIELD::FEP-WHEN-CONSTANT))
 )
(ZCASH::INJECTIVITY-LEMMA<POINT=QOINT>
 (34 5 (:REWRITE ZCASH::NOT-JUBJUB-R-POINTP-WHEN-0-ORDINATE))
 (19 4 (:REWRITE ZCASH::JUBJUB-POINTP-WHEN-JUBJUB-R-POINTP))
 (18 8 (:REWRITE ZCASH::JUBJUB-R-POINTP-WHEN-JUBJUB-RSTAR-POINTP))
 (10 10 (:TYPE-PRESCRIPTION ZCASH::JUBJUB-RSTAR-POINTP))
 (8 8 (:TYPE-PRESCRIPTION ZCASH::JUBJUB-POINTP))
 (8 4 (:REWRITE PFIELD::NEG-WHEN-NOT-POSP-ARG2-CHEAP))
 (8 4 (:REWRITE PFIELD::NEG-WHEN-NOT-INTEGERP-CHEAP))
 (4 4 (:TYPE-PRESCRIPTION ZCASH::JUBJUB-Q))
 (4 4 (:REWRITE PFIELD::NEG-WHEN-CONSTANT-ARG1))
 )
(ZCASH::INJECTIVITY-LEMMA)
(ZCASH::JUBJUB-POINT->U-INJECTIVE-ON-JUBJUB-R-POINTP
 (90 6 (:REWRITE ZCASH::NOT-JUBJUB-R-POINTP-WHEN-0-ORDINATE))
 (32 32 (:TYPE-PRESCRIPTION ZCASH::NATP-OF-JUBJUB-POINT->V))
 (32 8 (:LINEAR ZCASH::JUBJUB-POINT->V-UPPER-BOUND))
 (20 10 (:REWRITE ZCASH::JUBJUB-POINTP-WHEN-JUBJUB-R-POINTP))
 (20 8 (:REWRITE ZCASH::JUBJUB-R-POINTP-WHEN-JUBJUB-RSTAR-POINTP))
 (12 12 (:TYPE-PRESCRIPTION ZCASH::JUBJUB-RSTAR-POINTP))
 (12 12 (:TYPE-PRESCRIPTION ZCASH::JUBJUB-POINTP))
 (8 8 (:TYPE-PRESCRIPTION ZCASH::JUBJUB-Q))
 (4 4 (:LINEAR ZCASH::JUBJUB-POINT->U-UPPER-BOUND))
 )
