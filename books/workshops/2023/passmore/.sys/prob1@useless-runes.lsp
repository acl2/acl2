(SQUARE
 (5 5 (:TYPE-PRESCRIPTION NONNEGATIVE-PRODUCT))
 )
(SQUARE-PSD
 (2 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-*-2))
 (1 1 (:REWRITE DEFAULT-*-1))
 )
(SQUARE-TYPE
 (1 1 (:REWRITE DEFAULT-*-2))
 (1 1 (:REWRITE DEFAULT-*-1))
 )
(PROB-0)
(PROB-1)
(GOAL)
(IDEAL-CF-0)
(IDEAL-CF-0-TYPE)
(CONE-CF-0
 (15 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (15 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (15 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (15 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 )
(CONE-CF-0-TYPE
 (37 7 (:REWRITE DEFAULT-PLUS-2))
 (25 7 (:REWRITE DEFAULT-PLUS-1))
 (15 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (15 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (15 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (15 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (15 5 (:REWRITE DEFAULT-TIMES-2))
 (12 3 (:REWRITE RATIONALP-X))
 (5 5 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (5 5 (:REWRITE NORMALIZE-ADDENDS))
 (5 5 (:REWRITE DEFAULT-TIMES-1))
 (4 4 (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (3 3 (:REWRITE REDUCE-RATIONALP-+))
 (3 3 (:REWRITE REDUCE-RATIONALP-*))
 (3 3 (:REWRITE REDUCE-INTEGERP-+))
 (3 3 (:REWRITE RATIONALP-MINUS-X))
 (3 3 (:REWRITE INTEGERP-MINUS-X))
 (3 3 (:REWRITE |(* (- x) y)|))
 (3 3 (:META META-RATIONALP-CORRECT))
 (3 3 (:META META-INTEGERP-CORRECT))
 (1 1 (:REWRITE FOLD-CONSTS-IN-+))
 (1 1 (:REWRITE DEFAULT-MINUS))
 (1 1 (:REWRITE |(+ c (+ d x))|))
 )
(CONE-CF-0-PSD
 (315 32 (:REWRITE DEFAULT-PLUS-2))
 (149 32 (:REWRITE DEFAULT-PLUS-1))
 (130 130 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (130 130 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (130 130 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (130 130 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (130 130 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (130 130 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (130 130 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (130 130 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (130 130 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (130 130 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (55 12 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (55 12 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (45 12 (:REWRITE DEFAULT-LESS-THAN-2))
 (43 43 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (43 43 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (43 43 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (43 43 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (34 1 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (34 1 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (31 21 (:REWRITE DEFAULT-TIMES-2))
 (31 1 (:LINEAR EXPT-<=-1-ONE))
 (30 1 (:LINEAR EXPT->=-1-TWO))
 (30 1 (:LINEAR EXPT->-1-TWO))
 (30 1 (:LINEAR EXPT-<-1-ONE))
 (27 1 (:LINEAR EXPT-X->=-X))
 (27 1 (:LINEAR EXPT->=-1-ONE))
 (27 1 (:LINEAR EXPT-<=-1-TWO))
 (26 1 (:LINEAR EXPT-X->-X))
 (26 1 (:LINEAR EXPT->-1-ONE))
 (26 1 (:LINEAR EXPT-<-1-TWO))
 (25 21 (:REWRITE DEFAULT-TIMES-1))
 (24 24 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (24 24 (:REWRITE NORMALIZE-ADDENDS))
 (22 12 (:REWRITE DEFAULT-LESS-THAN-1))
 (15 15 (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (13 13 (:REWRITE FOLD-CONSTS-IN-+))
 (13 13 (:REWRITE |(+ c (+ d x))|))
 (12 12 (:REWRITE THE-FLOOR-BELOW))
 (12 12 (:REWRITE THE-FLOOR-ABOVE))
 (12 12 (:REWRITE SIMPLIFY-SUMS-<))
 (12 12 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (12 12 (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (12 12 (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (12 12 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (12 12 (:REWRITE INTEGERP-<-CONSTANT))
 (12 12 (:REWRITE CONSTANT-<-INTEGERP))
 (12 12 (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (12 12 (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (12 12 (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (12 12 (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (12 12 (:REWRITE |(< c (- x))|))
 (12 12 (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (12 12 (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (12 12 (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (12 12 (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (12 12 (:REWRITE |(< (/ x) (/ y))|))
 (12 12 (:REWRITE |(< (- x) c)|))
 (12 12 (:REWRITE |(< (- x) (- y))|))
 (12 3 (:REWRITE RATIONALP-X))
 (8 8 (:REWRITE DEFAULT-EXPT-2))
 (8 8 (:REWRITE DEFAULT-EXPT-1))
 (8 8 (:REWRITE |(expt 1/c n)|))
 (8 8 (:REWRITE |(expt (- x) n)|))
 (6 6 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (4 4 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (4 4 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (4 4 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (4 4 (:REWRITE |(< 0 (/ x))|))
 (4 4 (:REWRITE |(< 0 (* x y))|))
 (3 3 (:REWRITE REDUCE-RATIONALP-+))
 (3 3 (:REWRITE REDUCE-RATIONALP-*))
 (3 3 (:REWRITE REDUCE-INTEGERP-+))
 (3 3 (:REWRITE RATIONALP-MINUS-X))
 (3 3 (:REWRITE INTEGERP-MINUS-X))
 (3 3 (:REWRITE |(* c (* d x))|))
 (3 3 (:REWRITE |(* (- x) y)|))
 (3 3 (:META META-RATIONALP-CORRECT))
 (3 3 (:META META-INTEGERP-CORRECT))
 (2 2 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2 (:REWRITE |(< (/ x) 0)|))
 (2 2 (:REWRITE |(< (* x y) 0)|))
 (2 2 (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (2 2 (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2 2 (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2 2 (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (1 1 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (1 1 (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (1 1 (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (1 1 (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (1 1 (:REWRITE DEFAULT-MINUS))
 (1 1 (:REWRITE |(equal c (/ x))|))
 (1 1 (:REWRITE |(equal c (- x))|))
 (1 1 (:REWRITE |(equal (/ x) c)|))
 (1 1 (:REWRITE |(equal (/ x) (/ y))|))
 (1 1 (:REWRITE |(equal (- x) c)|))
 (1 1 (:REWRITE |(equal (- x) (- y))|))
 (1 1 (:REWRITE |(equal (+ (- c) x) y)|))
 (1 1 (:REWRITE |(< y (+ (- c) x))|))
 (1 1 (:REWRITE |(< x (+ c/d y))|))
 (1 1 (:REWRITE |(< (+ c/d x) y)|))
 (1 1 (:REWRITE |(< (+ (- c) x) y)|))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<))
 )
(MONOID-CF-0)
(CERT)
(CERT-KEY
 (3718 243 (:REWRITE DEFAULT-PLUS-2))
 (1882 243 (:REWRITE DEFAULT-PLUS-1))
 (595 122 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (594 96 (:REWRITE DEFAULT-TIMES-2))
 (487 487 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (487 487 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (487 487 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (487 487 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (487 487 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (487 487 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (487 487 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (487 487 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (487 487 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (487 487 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (179 27 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (122 122 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (122 122 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (122 122 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (122 96 (:REWRITE DEFAULT-TIMES-1))
 (115 115 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (93 93 (:REWRITE |(+ c (+ d x))|))
 (93 20 (:REWRITE DEFAULT-MINUS))
 (85 85 (:REWRITE FOLD-CONSTS-IN-+))
 (53 21 (:REWRITE DEFAULT-EXPT-1))
 (21 21 (:REWRITE DEFAULT-EXPT-2))
 (16 16 (:REWRITE |(expt 1/c n)|))
 (12 3 (:REWRITE RATIONALP-X))
 (3 3 (:REWRITE REDUCE-RATIONALP-+))
 (3 3 (:REWRITE REDUCE-RATIONALP-*))
 (3 3 (:REWRITE REDUCE-INTEGERP-+))
 (3 3 (:REWRITE RATIONALP-MINUS-X))
 (3 3 (:REWRITE INTEGERP-MINUS-X))
 (3 3 (:META META-RATIONALP-CORRECT))
 (3 3 (:META META-INTEGERP-CORRECT))
 (2 2 (:REWRITE |(expt (- c) n)|))
 )
(CERT-CONTRA-M-0
 (487 47 (:REWRITE DEFAULT-PLUS-2))
 (223 47 (:REWRITE DEFAULT-PLUS-1))
 (116 116 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (116 116 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (116 116 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (116 116 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (116 116 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (116 116 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (116 116 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (116 116 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (116 116 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (116 116 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (35 35 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (35 35 (:REWRITE NORMALIZE-ADDENDS))
 (35 2 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (35 2 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (35 2 (:REWRITE DEFAULT-LESS-THAN-2))
 (34 1 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (34 1 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (31 26 (:REWRITE DEFAULT-TIMES-1))
 (26 26 (:REWRITE DEFAULT-TIMES-2))
 (22 22 (:REWRITE FOLD-CONSTS-IN-+))
 (22 22 (:REWRITE |(+ c (+ d x))|))
 (13 13 (:REWRITE DEFAULT-EXPT-2))
 (13 13 (:REWRITE DEFAULT-EXPT-1))
 (13 13 (:REWRITE |(expt 1/c n)|))
 (13 13 (:REWRITE |(expt (- x) n)|))
 (12 3 (:REWRITE RATIONALP-X))
 (9 9 (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (6 6 (:REWRITE |(* c (* d x))|))
 (5 5 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (3 3 (:REWRITE REDUCE-RATIONALP-+))
 (3 3 (:REWRITE REDUCE-RATIONALP-*))
 (3 3 (:REWRITE REDUCE-INTEGERP-+))
 (3 3 (:REWRITE RATIONALP-MINUS-X))
 (3 3 (:REWRITE INTEGERP-MINUS-X))
 (3 3 (:META META-RATIONALP-CORRECT))
 (3 3 (:META META-INTEGERP-CORRECT))
 (2 2 (:REWRITE THE-FLOOR-BELOW))
 (2 2 (:REWRITE THE-FLOOR-ABOVE))
 (2 2 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2 (:REWRITE SIMPLIFY-SUMS-<))
 (2 2 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (2 2 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (2 2 (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (2 2 (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (2 2 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (2 2 (:REWRITE INTEGERP-<-CONSTANT))
 (2 2 (:REWRITE DEFAULT-LESS-THAN-1))
 (2 2 (:REWRITE CONSTANT-<-INTEGERP))
 (2 2 (:REWRITE |(< y (+ (- c) x))|))
 (2 2 (:REWRITE |(< x (+ c/d y))|))
 (2 2 (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (2 2 (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (2 2 (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (2 2 (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (2 2 (:REWRITE |(< c (- x))|))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:REWRITE |(< 0 (* x y))|))
 (2 2 (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (2 2 (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (2 2 (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (2 2 (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (2 2 (:REWRITE |(< (/ x) (/ y))|))
 (2 2 (:REWRITE |(< (- x) c)|))
 (2 2 (:REWRITE |(< (- x) (- y))|))
 (1 1 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (1 1 (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (1 1 (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (1 1 (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (1 1 (:REWRITE |(equal c (/ x))|))
 (1 1 (:REWRITE |(equal c (- x))|))
 (1 1 (:REWRITE |(equal (/ x) c)|))
 (1 1 (:REWRITE |(equal (/ x) (/ y))|))
 (1 1 (:REWRITE |(equal (- x) c)|))
 (1 1 (:REWRITE |(equal (- x) (- y))|))
 (1 1 (:REWRITE |(equal (+ (- c) x) y)|))
 )
(CERT-CONTRA-C-0)
(CERT-CONTRA-I-0)
(CERT-CONTRA
 (14 8 (:REWRITE DEFAULT-PLUS-2))
 (14 8 (:REWRITE DEFAULT-PLUS-1))
 (12 3 (:REWRITE RATIONALP-X))
 (6 4 (:REWRITE DEFAULT-TIMES-2))
 (6 4 (:REWRITE DEFAULT-TIMES-1))
 (6 3 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (6 3 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (5 3 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (5 3 (:REWRITE DEFAULT-LESS-THAN-1))
 (4 4 (:TYPE-PRESCRIPTION IDEAL-CF-0))
 (4 3 (:REWRITE DEFAULT-LESS-THAN-2))
 (3 3 (:REWRITE THE-FLOOR-BELOW))
 (3 3 (:REWRITE THE-FLOOR-ABOVE))
 (3 3 (:REWRITE SIMPLIFY-SUMS-<))
 (3 3 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (3 3 (:REWRITE REDUCE-RATIONALP-+))
 (3 3 (:REWRITE REDUCE-RATIONALP-*))
 (3 3 (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (3 3 (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (3 3 (:REWRITE REDUCE-INTEGERP-+))
 (3 3 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (3 3 (:REWRITE RATIONALP-MINUS-X))
 (3 3 (:REWRITE INTEGERP-MINUS-X))
 (3 3 (:REWRITE INTEGERP-<-CONSTANT))
 (3 3 (:REWRITE CONSTANT-<-INTEGERP))
 (3 3 (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (3 3 (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (3 3 (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (3 3 (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (3 3 (:REWRITE |(< c (- x))|))
 (3 3 (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (3 3 (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (3 3 (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (3 3 (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (3 3 (:REWRITE |(< (/ x) (/ y))|))
 (3 3 (:REWRITE |(< (- x) c)|))
 (3 3 (:REWRITE |(< (- x) (- y))|))
 (3 3 (:META META-RATIONALP-CORRECT))
 (3 3 (:META META-INTEGERP-CORRECT))
 (2 2 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (2 2 (:REWRITE NORMALIZE-ADDENDS))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:REWRITE |(< 0 (* x y))|))
 (2 1 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (2 1 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (1 1 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (1 1 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (1 1 (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (1 1 (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (1 1 (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (1 1 (:REWRITE |(equal c (/ x))|))
 (1 1 (:REWRITE |(equal c (- x))|))
 (1 1 (:REWRITE |(equal (/ x) c)|))
 (1 1 (:REWRITE |(equal (/ x) (/ y))|))
 (1 1 (:REWRITE |(equal (- x) c)|))
 (1 1 (:REWRITE |(equal (- x) (- y))|))
 (1 1 (:REWRITE |(< y (+ (- c) x))|))
 (1 1 (:REWRITE |(< x (+ c/d y))|))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (+ c/d x) y)|))
 (1 1 (:REWRITE |(< (+ (- c) x) y)|))
 (1 1 (:REWRITE |(< (* x y) 0)|))
 )
(MAIN
 (42 12 (:REWRITE DEFAULT-PLUS-2))
 (24 12 (:REWRITE DEFAULT-PLUS-1))
 (9 9 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (9 9 (:REWRITE NORMALIZE-ADDENDS))
 (6 3 (:REWRITE DEFAULT-TIMES-2))
 (6 3 (:REWRITE DEFAULT-TIMES-1))
 (5 1 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (5 1 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (3 3 (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (3 3 (:REWRITE FOLD-CONSTS-IN-+))
 (3 3 (:REWRITE |(+ c (+ d x))|))
 (1 1 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (1 1 (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (1 1 (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (1 1 (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (1 1 (:REWRITE |(equal c (/ x))|))
 (1 1 (:REWRITE |(equal c (- x))|))
 (1 1 (:REWRITE |(equal (/ x) c)|))
 (1 1 (:REWRITE |(equal (/ x) (/ y))|))
 (1 1 (:REWRITE |(equal (- x) c)|))
 (1 1 (:REWRITE |(equal (- x) (- y))|))
 (1 1 (:REWRITE |(equal (+ (- c) x) y)|))
 )
(FINAL
 (523 50 (:REWRITE DEFAULT-PLUS-2))
 (270 50 (:REWRITE DEFAULT-PLUS-1))
 (234 234 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (234 234 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (234 234 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (234 234 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (234 234 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (234 234 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (234 234 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (234 234 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (234 234 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (234 234 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (102 3 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (102 3 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (68 2 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (68 2 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (68 2 (:REWRITE DEFAULT-LESS-THAN-2))
 (54 54 (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (49 38 (:REWRITE DEFAULT-TIMES-1))
 (38 38 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (38 38 (:REWRITE NORMALIZE-ADDENDS))
 (38 38 (:REWRITE DEFAULT-TIMES-2))
 (24 6 (:REWRITE RATIONALP-X))
 (23 23 (:REWRITE FOLD-CONSTS-IN-+))
 (23 23 (:REWRITE |(+ c (+ d x))|))
 (19 19 (:REWRITE DEFAULT-EXPT-2))
 (19 19 (:REWRITE DEFAULT-EXPT-1))
 (19 19 (:REWRITE |(expt 1/c n)|))
 (19 19 (:REWRITE |(expt (- x) n)|))
 (11 11 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (6 6 (:REWRITE REDUCE-RATIONALP-+))
 (6 6 (:REWRITE REDUCE-RATIONALP-*))
 (6 6 (:REWRITE REDUCE-INTEGERP-+))
 (6 6 (:REWRITE RATIONALP-MINUS-X))
 (6 6 (:REWRITE INTEGERP-MINUS-X))
 (6 6 (:REWRITE |(* c (* d x))|))
 (6 6 (:META META-RATIONALP-CORRECT))
 (6 6 (:META META-INTEGERP-CORRECT))
 (3 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (3 3 (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (3 3 (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (3 3 (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (3 3 (:REWRITE |(equal c (/ x))|))
 (3 3 (:REWRITE |(equal c (- x))|))
 (3 3 (:REWRITE |(equal (/ x) c)|))
 (3 3 (:REWRITE |(equal (/ x) (/ y))|))
 (3 3 (:REWRITE |(equal (- x) c)|))
 (3 3 (:REWRITE |(equal (- x) (- y))|))
 (3 3 (:REWRITE |(equal (+ (- c) x) y)|))
 (2 2 (:REWRITE THE-FLOOR-BELOW))
 (2 2 (:REWRITE THE-FLOOR-ABOVE))
 (2 2 (:REWRITE SIMPLIFY-SUMS-<))
 (2 2 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (2 2 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (2 2 (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (2 2 (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (2 2 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (2 2 (:REWRITE INTEGERP-<-CONSTANT))
 (2 2 (:REWRITE DEFAULT-LESS-THAN-1))
 (2 2 (:REWRITE CONSTANT-<-INTEGERP))
 (2 2 (:REWRITE |(< y (+ (- c) x))|))
 (2 2 (:REWRITE |(< x (+ c/d y))|))
 (2 2 (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (2 2 (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (2 2 (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (2 2 (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (2 2 (:REWRITE |(< c (- x))|))
 (2 2 (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (2 2 (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (2 2 (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (2 2 (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (2 2 (:REWRITE |(< (/ x) (/ y))|))
 (2 2 (:REWRITE |(< (- x) c)|))
 (2 2 (:REWRITE |(< (- x) (- y))|))
 (1 1 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (1 1 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (1 1 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (1 1 (:REWRITE |(< 0 (/ x))|))
 (1 1 (:REWRITE |(< 0 (* x y))|))
 )
