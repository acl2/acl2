(RTL::RLE-1
     (139 139
          (:TYPE-PRESCRIPTION RTL::RND-NON-POS))
     (139 139
          (:TYPE-PRESCRIPTION RTL::RND-NEGATIVE))
     (30 1 (:LINEAR RTL::RND-NON-POS))
     (30 1 (:LINEAR RTL::RND-NON-NEG))
     (20 2
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (18 2 (:REWRITE ACL2-NUMBERP-X))
     (16 4 (:REWRITE RATIONALP-X))
     (11 6 (:REWRITE SIMPLIFY-SUMS-<))
     (11 6
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (11 6 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (11 6 (:REWRITE DEFAULT-LESS-THAN-1))
     (6 6 (:REWRITE THE-FLOOR-BELOW))
     (6 6 (:REWRITE THE-FLOOR-ABOVE))
     (6 6 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (6 6 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (6 6
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (6 6
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (6 6 (:REWRITE INTEGERP-<-CONSTANT))
     (6 6 (:REWRITE DEFAULT-LESS-THAN-2))
     (6 6 (:REWRITE CONSTANT-<-INTEGERP))
     (6 6
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (6 6
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (6 6
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (6 6
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (6 6 (:REWRITE |(< c (- x))|))
     (6 6
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (6 6
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (6 6
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (6 6
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (6 6 (:REWRITE |(< (/ x) (/ y))|))
     (6 6 (:REWRITE |(< (- x) c)|))
     (6 6 (:REWRITE |(< (- x) (- y))|))
     (5 5 (:REWRITE REDUCE-INTEGERP-+))
     (5 5 (:REWRITE INTEGERP-MINUS-X))
     (5 5 (:META META-INTEGERP-CORRECT))
     (4 4 (:REWRITE REDUCE-RATIONALP-+))
     (4 4 (:REWRITE REDUCE-RATIONALP-*))
     (4 4 (:REWRITE RATIONALP-MINUS-X))
     (4 4 (:META META-RATIONALP-CORRECT))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (2 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (2 2
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (2 2
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (2 2
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (2 2 (:REWRITE |(equal c (/ x))|))
     (2 2 (:REWRITE |(equal c (- x))|))
     (2 2 (:REWRITE |(equal (/ x) c)|))
     (2 2 (:REWRITE |(equal (/ x) (/ y))|))
     (2 2 (:REWRITE |(equal (- x) c)|))
     (2 2 (:REWRITE |(equal (- x) (- y))|))
     (2 2 (:REWRITE |(< 0 (/ x))|))
     (2 2 (:REWRITE |(< 0 (* x y))|))
     (2 2 (:REWRITE |(< (/ x) 0)|))
     (2 2 (:REWRITE |(< (* x y) 0)|)))
(RTL::RLE-2
     (30 2 (:LINEAR RTL::TRUNC-NEGATIVE))
     (6 6 (:REWRITE RTL::TRUNC-TO-0))
     (6 3 (:REWRITE SIMPLIFY-SUMS-<))
     (6 3
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (6 3 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (5 3 (:REWRITE DEFAULT-LESS-THAN-2))
     (4 3 (:REWRITE DEFAULT-LESS-THAN-1))
     (3 3 (:REWRITE THE-FLOOR-BELOW))
     (3 3 (:REWRITE THE-FLOOR-ABOVE))
     (3 3 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (3 3
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (3 3
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (3 3 (:REWRITE INTEGERP-<-CONSTANT))
     (3 3 (:REWRITE CONSTANT-<-INTEGERP))
     (3 3
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (3 3
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (3 3
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (3 3
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (3 3 (:REWRITE |(< c (- x))|))
     (3 3
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (3 3
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (3 3
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (3 3
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (3 3 (:REWRITE |(< (/ x) (/ y))|))
     (3 3 (:REWRITE |(< (- x) c)|))
     (3 3 (:REWRITE |(< (- x) (- y))|))
     (2 2 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (1 1 (:REWRITE |(< (/ x) 0)|))
     (1 1 (:REWRITE |(< (* x y) 0)|)))
(RTL::RLE-3
     (19 11 (:REWRITE SIMPLIFY-SUMS-<))
     (19 11
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (19 11 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (17 12 (:REWRITE DEFAULT-LESS-THAN-2))
     (17 12 (:REWRITE DEFAULT-LESS-THAN-1))
     (13 11
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (12 12 (:REWRITE THE-FLOOR-BELOW))
     (12 12 (:REWRITE THE-FLOOR-ABOVE))
     (11 11 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (11 11
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (11 11
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (11 11 (:REWRITE INTEGERP-<-CONSTANT))
     (11 11 (:REWRITE CONSTANT-<-INTEGERP))
     (11 11
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (11 11
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (11 11
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (11 11
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (11 11 (:REWRITE |(< c (- x))|))
     (11 11
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (11 11
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (11 11
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (11 11
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (11 11 (:REWRITE |(< (/ x) (/ y))|))
     (11 11 (:REWRITE |(< (- x) c)|))
     (11 11 (:REWRITE |(< (- x) (- y))|))
     (9 9 (:REWRITE RTL::TRUNC-TO-0))
     (8 2 (:REWRITE RATIONALP-X))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (3 3 (:REWRITE REDUCE-INTEGERP-+))
     (3 3 (:REWRITE INTEGERP-MINUS-X))
     (3 3 (:REWRITE |(< (/ x) 0)|))
     (3 3 (:REWRITE |(< (* x y) 0)|))
     (3 3 (:META META-INTEGERP-CORRECT))
     (3 1 (:REWRITE RTL::BVECP-EXACTP))
     (2 2 (:TYPE-PRESCRIPTION RTL::BVECP))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (2 2 (:REWRITE REDUCE-RATIONALP-+))
     (2 2 (:REWRITE REDUCE-RATIONALP-*))
     (2 2 (:REWRITE RATIONALP-MINUS-X))
     (2 2 (:REWRITE RTL::AWAY-TO-0))
     (2 2 (:REWRITE |(< 0 (/ x))|))
     (2 2 (:REWRITE |(< 0 (* x y))|))
     (2 2 (:META META-RATIONALP-CORRECT))
     (2 2 (:LINEAR RTL::TRUNC-NEGATIVE))
     (1 1
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (1 1 (:REWRITE NORMALIZE-ADDENDS))
     (1 1 (:REWRITE DEFAULT-PLUS-2))
     (1 1 (:REWRITE DEFAULT-PLUS-1))
     (1 1 (:LINEAR RTL::AWAY-POSITIVE)))
(RTL::RLE-4
 (89 51 (:REWRITE DEFAULT-PLUS-2))
 (64 51 (:REWRITE DEFAULT-PLUS-1))
 (58
  58
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (58 58
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (58 58
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (58 58
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (58 58
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (58 58
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (31 31
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (29 18
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (28 18 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (26 19 (:REWRITE DEFAULT-LESS-THAN-1))
 (23 19 (:REWRITE DEFAULT-LESS-THAN-2))
 (19 19 (:REWRITE THE-FLOOR-BELOW))
 (19 19 (:REWRITE THE-FLOOR-ABOVE))
 (19 19
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (19 19
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (19 19 (:REWRITE INTEGERP-<-CONSTANT))
 (19 19 (:REWRITE CONSTANT-<-INTEGERP))
 (19 19
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (19 19
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (19 19
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (19 19
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (19 19 (:REWRITE |(< c (- x))|))
 (19 19
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (19 19
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (19 19
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (19 19
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (19 19 (:REWRITE |(< (/ x) (/ y))|))
 (19 19 (:REWRITE |(< (- x) c)|))
 (19 19 (:REWRITE |(< (- x) (- y))|))
 (19 7 (:REWRITE RTL::BVECP-EXACTP))
 (18 18 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (14 14 (:REWRITE RTL::AWAY-TO-0))
 (13 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (13 1
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (12 12 (:TYPE-PRESCRIPTION RTL::BVECP))
 (8 2 (:REWRITE RATIONALP-X))
 (6 3 (:REWRITE DEFAULT-EXPT-2))
 (5 5 (:REWRITE RTL::TRUNC-TO-0))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (5 5 (:REWRITE |(< (/ x) 0)|))
 (5 5 (:REWRITE |(< (* x y) 0)|))
 (4 4 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (4 4 (:REWRITE |(< 0 (/ x))|))
 (4 4 (:REWRITE |(< 0 (* x y))|))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (3 3 (:REWRITE REDUCE-INTEGERP-+))
 (3 3 (:REWRITE INTEGERP-MINUS-X))
 (3 3 (:REWRITE FOLD-CONSTS-IN-+))
 (3 3 (:REWRITE DEFAULT-MINUS))
 (3 3 (:REWRITE DEFAULT-EXPT-1))
 (3 3 (:REWRITE |(expt 1/c n)|))
 (3 3 (:REWRITE |(expt (- x) n)|))
 (3 3 (:REWRITE |(+ c (+ d x))|))
 (3 3 (:META META-INTEGERP-CORRECT))
 (2 2 (:REWRITE REDUCE-RATIONALP-+))
 (2 2 (:REWRITE REDUCE-RATIONALP-*))
 (2 2 (:REWRITE RATIONALP-MINUS-X))
 (2 2 (:REWRITE RTL::AWAY-NEGATIVE))
 (2 2 (:REWRITE |(< (+ c/d x) y)|))
 (2 2 (:REWRITE |(< (+ (- c) x) y)|))
 (2 2 (:META META-RATIONALP-CORRECT))
 (1 1
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (1 1
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (1 1
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (1 1 (:REWRITE |(equal c (/ x))|))
 (1 1 (:REWRITE |(equal c (- x))|))
 (1 1 (:REWRITE |(equal (/ x) c)|))
 (1 1 (:REWRITE |(equal (/ x) (/ y))|))
 (1 1 (:REWRITE |(equal (- x) c)|))
 (1 1 (:REWRITE |(equal (- x) (- y))|))
 (1 1 (:REWRITE |(equal (+ (- c) x) y)|))
 (1 1 (:LINEAR RTL::TRUNC-NEGATIVE)))
(RTL::RLE-5
 (484 54 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (391
  391
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (391 391
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (391
     391
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (391 391
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (391 391
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (391 391
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (153 71 (:REWRITE DEFAULT-PLUS-2))
 (138 6 (:REWRITE |(+ y (+ x z))|))
 (107 35 (:REWRITE NORMALIZE-ADDENDS))
 (102 1 (:LINEAR EXPT->=-1-ONE))
 (102 1 (:LINEAR EXPT-<=-1-TWO))
 (101 1 (:LINEAR EXPT-X->=-X))
 (101 1 (:LINEAR EXPT-X->-X))
 (100 1 (:LINEAR EXPT->-1-ONE))
 (100 1 (:LINEAR EXPT-<-1-TWO))
 (95 54
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (88 71 (:REWRITE DEFAULT-PLUS-1))
 (84 57 (:REWRITE DEFAULT-LESS-THAN-2))
 (82 48 (:REWRITE SIMPLIFY-SUMS-<))
 (72 57 (:REWRITE DEFAULT-LESS-THAN-1))
 (57 57 (:REWRITE THE-FLOOR-BELOW))
 (57 57 (:REWRITE THE-FLOOR-ABOVE))
 (57 57
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (57 57
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (57 57 (:REWRITE INTEGERP-<-CONSTANT))
 (57 57 (:REWRITE CONSTANT-<-INTEGERP))
 (57 57
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (57 57
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (57 57
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (57 57
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (57 57 (:REWRITE |(< c (- x))|))
 (57 57
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (57 57
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (57 57
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (57 57
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (57 57 (:REWRITE |(< (/ x) (/ y))|))
 (57 57 (:REWRITE |(< (- x) c)|))
 (57 57 (:REWRITE |(< (- x) (- y))|))
 (42 42 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (42 6 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
 (32 8 (:REWRITE RATIONALP-X))
 (30 30 (:REWRITE RTL::AWAY-TO-0))
 (29 29
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (25 5 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (25 5
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (19 19 (:REWRITE |(< 0 (/ x))|))
 (19 19 (:REWRITE |(< 0 (* x y))|))
 (18 18 (:REWRITE RTL::TRUNC-TO-0))
 (16 16
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (16 16
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (16 10 (:REWRITE |(+ 0 x)|))
 (15 5 (:REWRITE RTL::BVECP-EXACTP))
 (12 12 (:REWRITE REDUCE-INTEGERP-+))
 (12 12 (:REWRITE INTEGERP-MINUS-X))
 (12 12 (:META META-INTEGERP-CORRECT))
 (12 12 (:DEFINITION FIX))
 (10 10 (:TYPE-PRESCRIPTION RTL::BVECP))
 (10 10 (:REWRITE |(< (/ x) 0)|))
 (10 10 (:REWRITE |(< (* x y) 0)|))
 (10 10 (:REWRITE |(+ c (+ d x))|))
 (9 9 (:REWRITE |(< y (+ (- c) x))|))
 (9 9 (:REWRITE |(< x (+ c/d y))|))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (8 8 (:REWRITE REDUCE-RATIONALP-+))
 (8 8 (:REWRITE REDUCE-RATIONALP-*))
 (8 8 (:REWRITE RATIONALP-MINUS-X))
 (8 8 (:META META-RATIONALP-CORRECT))
 (8 4 (:REWRITE DEFAULT-EXPT-2))
 (6 6 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (6 6 (:REWRITE |(< (+ c/d x) y)|))
 (6 6 (:REWRITE |(< (+ (- c) x) y)|))
 (6 6 (:REWRITE |(+ x (- x))|))
 (5 5
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (5 5
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (5 5
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (5 5 (:REWRITE |(equal c (/ x))|))
 (5 5 (:REWRITE |(equal c (- x))|))
 (5 5 (:REWRITE |(equal (/ x) c)|))
 (5 5 (:REWRITE |(equal (/ x) (/ y))|))
 (5 5 (:REWRITE |(equal (- x) c)|))
 (5 5 (:REWRITE |(equal (- x) (- y))|))
 (4 4 (:REWRITE FOLD-CONSTS-IN-+))
 (4 4 (:REWRITE DEFAULT-MINUS))
 (4 4 (:REWRITE DEFAULT-EXPT-1))
 (4 4 (:REWRITE |(expt 1/c n)|))
 (4 4 (:REWRITE |(expt (- x) n)|))
 (3 3 (:LINEAR RTL::TRUNC-NEGATIVE))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (1 1 (:REWRITE |(equal (+ (- c) x) y)|))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<))
 (1 1 (:LINEAR EXPT->=-1-TWO))
 (1 1 (:LINEAR EXPT->-1-TWO))
 (1 1 (:LINEAR EXPT-<=-1-ONE))
 (1 1 (:LINEAR EXPT-<-1-ONE)))
(RTL::RLE-6
     (13 11 (:REWRITE DEFAULT-LESS-THAN-1))
     (11 11 (:REWRITE THE-FLOOR-BELOW))
     (11 11 (:REWRITE THE-FLOOR-ABOVE))
     (11 11
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (11 11
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (11 11 (:REWRITE INTEGERP-<-CONSTANT))
     (11 11 (:REWRITE DEFAULT-LESS-THAN-2))
     (11 11 (:REWRITE CONSTANT-<-INTEGERP))
     (11 11
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (11 11
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (11 11
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (11 11
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (11 11 (:REWRITE |(< c (- x))|))
     (11 11
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (11 11
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (11 11
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (11 11
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (11 11 (:REWRITE |(< (/ x) (/ y))|))
     (11 11 (:REWRITE |(< (- x) c)|))
     (11 11 (:REWRITE |(< (- x) (- y))|))
     (9 8 (:REWRITE SIMPLIFY-SUMS-<))
     (9 8
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (9 8 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (8 8 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (8 2 (:REWRITE RATIONALP-X))
     (7 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (7 2
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (6 2 (:REWRITE RTL::BVECP-EXACTP))
     (5 5 (:REWRITE RTL::TRUNC-TO-0))
     (5 5 (:REWRITE RTL::AWAY-TO-0))
     (4 4 (:TYPE-PRESCRIPTION RTL::BVECP))
     (4 4 (:REWRITE |(< 0 (/ x))|))
     (4 4 (:REWRITE |(< 0 (* x y))|))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (3 3 (:REWRITE REDUCE-INTEGERP-+))
     (3 3 (:REWRITE INTEGERP-MINUS-X))
     (3 3 (:REWRITE |(< (/ x) 0)|))
     (3 3 (:REWRITE |(< (* x y) 0)|))
     (3 3 (:META META-INTEGERP-CORRECT))
     (2 2 (:REWRITE REDUCE-RATIONALP-+))
     (2 2 (:REWRITE REDUCE-RATIONALP-*))
     (2 2
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (2 2
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (2 2 (:REWRITE RATIONALP-MINUS-X))
     (2 2
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (2 2 (:REWRITE NORMALIZE-ADDENDS))
     (2 2
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (2 2 (:REWRITE DEFAULT-PLUS-2))
     (2 2 (:REWRITE DEFAULT-PLUS-1))
     (2 2 (:REWRITE |(equal c (/ x))|))
     (2 2 (:REWRITE |(equal c (- x))|))
     (2 2 (:REWRITE |(equal (/ x) c)|))
     (2 2 (:REWRITE |(equal (/ x) (/ y))|))
     (2 2 (:REWRITE |(equal (- x) c)|))
     (2 2 (:REWRITE |(equal (- x) (- y))|))
     (2 2 (:META META-RATIONALP-CORRECT))
     (2 2 (:LINEAR RTL::TRUNC-NEGATIVE))
     (1 1 (:LINEAR RTL::AWAY-POSITIVE)))
(RTL::RLE-7
 (84 43 (:REWRITE DEFAULT-PLUS-2))
 (58
  58
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (58 58
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (58 58
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (58 58
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (58 58
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (58 58
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (53 43 (:REWRITE DEFAULT-PLUS-1))
 (30 30
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (30 30 (:REWRITE NORMALIZE-ADDENDS))
 (19 12
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (18 12 (:REWRITE SIMPLIFY-SUMS-<))
 (18 12 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (17 13 (:REWRITE DEFAULT-LESS-THAN-1))
 (16 13 (:REWRITE DEFAULT-LESS-THAN-2))
 (13 13 (:REWRITE THE-FLOOR-BELOW))
 (13 13 (:REWRITE THE-FLOOR-ABOVE))
 (13 13
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (13 13
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (13 13 (:REWRITE INTEGERP-<-CONSTANT))
 (13 13 (:REWRITE CONSTANT-<-INTEGERP))
 (13 13
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (13 13
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (13 13
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (13 13
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (13 13 (:REWRITE |(< c (- x))|))
 (13 13
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (13 13
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (13 13
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (13 13
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (13 13 (:REWRITE |(< (/ x) (/ y))|))
 (13 13 (:REWRITE |(< (- x) c)|))
 (13 13 (:REWRITE |(< (- x) (- y))|))
 (13 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (13 1
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (12 12 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (12 3 (:REWRITE RATIONALP-X))
 (8 8 (:REWRITE RTL::AWAY-TO-0))
 (6 3 (:REWRITE DEFAULT-EXPT-2))
 (6 2 (:REWRITE RTL::BVECP-EXACTP))
 (5 5 (:REWRITE RTL::TRUNC-TO-0))
 (5 5 (:REWRITE DEFAULT-MINUS))
 (4 4 (:TYPE-PRESCRIPTION RTL::BVECP))
 (4 4 (:REWRITE REDUCE-INTEGERP-+))
 (4 4 (:REWRITE INTEGERP-MINUS-X))
 (4 4 (:REWRITE |(< 0 (/ x))|))
 (4 4 (:REWRITE |(< 0 (* x y))|))
 (4 4 (:META META-INTEGERP-CORRECT))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (3 3 (:REWRITE REDUCE-RATIONALP-+))
 (3 3 (:REWRITE REDUCE-RATIONALP-*))
 (3 3 (:REWRITE RATIONALP-MINUS-X))
 (3 3 (:REWRITE DEFAULT-EXPT-1))
 (3 3 (:REWRITE |(expt 1/c n)|))
 (3 3 (:REWRITE |(expt (- x) n)|))
 (3 3 (:REWRITE |(< (/ x) 0)|))
 (3 3 (:REWRITE |(< (* x y) 0)|))
 (3 3 (:META META-RATIONALP-CORRECT))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 (1 1
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (1 1
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (1 1
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (1 1 (:REWRITE RTL::AWAY-NEGATIVE))
 (1 1 (:REWRITE |(equal c (/ x))|))
 (1 1 (:REWRITE |(equal c (- x))|))
 (1 1 (:REWRITE |(equal (/ x) c)|))
 (1 1 (:REWRITE |(equal (/ x) (/ y))|))
 (1 1 (:REWRITE |(equal (- x) c)|))
 (1 1 (:REWRITE |(equal (- x) (- y))|))
 (1 1 (:REWRITE |(equal (+ (- c) x) y)|))
 (1 1 (:REWRITE |(< y (+ (- c) x))|))
 (1 1 (:REWRITE |(< x (+ c/d y))|))
 (1 1 (:LINEAR RTL::TRUNC-NEGATIVE)))
(RTL::RLE-8
     (10 10 (:REWRITE RTL::TRUNC-TO-0))
     (10 6
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (10 6 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (9 6 (:REWRITE SIMPLIFY-SUMS-<))
     (8 6 (:REWRITE DEFAULT-LESS-THAN-2))
     (8 6 (:REWRITE DEFAULT-LESS-THAN-1))
     (6 6 (:REWRITE THE-FLOOR-BELOW))
     (6 6 (:REWRITE THE-FLOOR-ABOVE))
     (6 6 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (6 6 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (6 6
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (6 6
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (6 6 (:REWRITE INTEGERP-<-CONSTANT))
     (6 6 (:REWRITE CONSTANT-<-INTEGERP))
     (6 6
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (6 6
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (6 6
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (6 6
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (6 6 (:REWRITE |(< c (- x))|))
     (6 6
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (6 6
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (6 6
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (6 6
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (6 6 (:REWRITE |(< (/ x) (/ y))|))
     (6 6 (:REWRITE |(< (- x) c)|))
     (6 6 (:REWRITE |(< (- x) (- y))|))
     (5 5
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (5 5 (:REWRITE NORMALIZE-ADDENDS))
     (5 5 (:REWRITE DEFAULT-PLUS-2))
     (5 5 (:REWRITE DEFAULT-PLUS-1))
     (4 1 (:REWRITE RATIONALP-X))
     (3 3 (:LINEAR RTL::TRUNC-NEGATIVE))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (2 2 (:REWRITE REDUCE-INTEGERP-+))
     (2 2 (:REWRITE INTEGERP-MINUS-X))
     (2 2 (:REWRITE |(< 0 (/ x))|))
     (2 2 (:REWRITE |(< 0 (* x y))|))
     (2 2 (:REWRITE |(< (/ x) 0)|))
     (2 2 (:REWRITE |(< (* x y) 0)|))
     (2 2 (:META META-INTEGERP-CORRECT))
     (1 1 (:REWRITE RTL::TRUNC-NEGATIVE))
     (1 1 (:REWRITE REDUCE-RATIONALP-+))
     (1 1 (:REWRITE REDUCE-RATIONALP-*))
     (1 1 (:REWRITE RATIONALP-MINUS-X))
     (1 1 (:META META-RATIONALP-CORRECT)))
(RTL::RLE-9
 (1902 127
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (486 126 (:REWRITE NORMALIZE-ADDENDS))
 (461 256 (:REWRITE DEFAULT-PLUS-2))
 (455 5 (:LINEAR EXPT->=-1-ONE))
 (455 5 (:LINEAR EXPT-<=-1-TWO))
 (450 5 (:LINEAR EXPT-X->=-X))
 (450 5 (:LINEAR EXPT-X->-X))
 (445 5 (:LINEAR EXPT->-1-ONE))
 (445 5 (:LINEAR EXPT-<-1-TWO))
 (381
  381
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (381 381
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (381
     381
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (381 381
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (381 381
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (381 381
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (335 147 (:REWRITE DEFAULT-LESS-THAN-2))
 (307 256 (:REWRITE DEFAULT-PLUS-1))
 (241 145 (:REWRITE DEFAULT-LESS-THAN-1))
 (211 97 (:REWRITE SIMPLIFY-SUMS-<))
 (210 30 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
 (147 147 (:REWRITE THE-FLOOR-BELOW))
 (147 147 (:REWRITE THE-FLOOR-ABOVE))
 (144 144
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (144 144
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (140 140 (:REWRITE INTEGERP-<-CONSTANT))
 (140 140 (:REWRITE CONSTANT-<-INTEGERP))
 (140 140
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (140 140
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (140 140
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (140 140
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (140 140 (:REWRITE |(< c (- x))|))
 (140 140
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (140 140
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (140 140
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (140 140
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (140 140 (:REWRITE |(< (/ x) (/ y))|))
 (140 140 (:REWRITE |(< (- x) c)|))
 (140 140 (:REWRITE |(< (- x) (- y))|))
 (96 96
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (95 83 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (67 8 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (67 8
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (56 14 (:REWRITE RATIONALP-X))
 (55 5 (:LINEAR RTL::AWAY-NEGATIVE))
 (54 6 (:REWRITE ACL2-NUMBERP-X))
 (50 1 (:REWRITE RTL::AWAY-POSITIVE))
 (45 45 (:REWRITE |(< 0 (* x y))|))
 (44 44 (:REWRITE RTL::TRUNC-TO-0))
 (41 41 (:REWRITE |(< 0 (/ x))|))
 (30 30 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (30 30 (:REWRITE |(+ x (- x))|))
 (26 26
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (26 26
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (23 23 (:REWRITE |(< y (+ (- c) x))|))
 (23 23 (:REWRITE |(< x (+ c/d y))|))
 (21 21 (:REWRITE RTL::AWAY-TO-0))
 (20 20 (:REWRITE REDUCE-INTEGERP-+))
 (20 20 (:REWRITE INTEGERP-MINUS-X))
 (20 20 (:REWRITE |(< (+ c/d x) y)|))
 (20 20 (:REWRITE |(< (+ (- c) x) y)|))
 (20 20 (:META META-INTEGERP-CORRECT))
 (19 19 (:REWRITE |(< (/ x) 0)|))
 (19 19 (:REWRITE |(< (* x y) 0)|))
 (18 9 (:REWRITE DEFAULT-EXPT-2))
 (18 6 (:REWRITE RTL::BVECP-EXACTP))
 (16 16 (:REWRITE DEFAULT-TIMES-2))
 (16 16 (:REWRITE DEFAULT-TIMES-1))
 (14 14 (:REWRITE REDUCE-RATIONALP-+))
 (14 14 (:REWRITE REDUCE-RATIONALP-*))
 (14 14 (:REWRITE RATIONALP-MINUS-X))
 (14 14 (:META META-RATIONALP-CORRECT))
 (13 13 (:REWRITE DEFAULT-MINUS))
 (12 12 (:TYPE-PRESCRIPTION RTL::BVECP))
 (11 11 (:LINEAR RTL::TRUNC-NEGATIVE))
 (10 10
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (10 10
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (10 10
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (10 10
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (9 9
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (9 9
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (9 9 (:REWRITE DEFAULT-EXPT-1))
 (9 9 (:REWRITE |(expt 1/c n)|))
 (9 9 (:REWRITE |(expt (- x) n)|))
 (8 8
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (8 8
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (8 8
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (8 8 (:REWRITE |(equal c (/ x))|))
 (8 8 (:REWRITE |(equal c (- x))|))
 (8 8 (:REWRITE |(equal (/ x) c)|))
 (8 8 (:REWRITE |(equal (/ x) (/ y))|))
 (8 8 (:REWRITE |(equal (- x) c)|))
 (8 8 (:REWRITE |(equal (- x) (- y))|))
 (7 7 (:REWRITE RTL::NEAR-MONOTONE))
 (5 5 (:REWRITE |(equal (+ (- c) x) y)|))
 (5 5 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (5 5 (:LINEAR EXPT-LINEAR-UPPER-<))
 (5 5 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (5 5 (:LINEAR EXPT-LINEAR-LOWER-<))
 (5 5 (:LINEAR EXPT->=-1-TWO))
 (5 5 (:LINEAR EXPT->-1-TWO))
 (5 5 (:LINEAR EXPT-<=-1-ONE))
 (5 5 (:LINEAR EXPT-<-1-ONE))
 (4 4 (:REWRITE FOLD-CONSTS-IN-+))
 (4 4
    (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (4 4
    (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (4 4
    (:REWRITE |(< x (/ y)) with (< y 0)|)))
(RTL::RLE-10
 (1908 144
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (486 126 (:REWRITE NORMALIZE-ADDENDS))
 (461 256 (:REWRITE DEFAULT-PLUS-2))
 (455 5 (:LINEAR EXPT->=-1-ONE))
 (455 5 (:LINEAR EXPT-<=-1-TWO))
 (450 5 (:LINEAR EXPT-X->=-X))
 (450 5 (:LINEAR EXPT-X->-X))
 (445 5 (:LINEAR EXPT->-1-ONE))
 (445 5 (:LINEAR EXPT-<-1-TWO))
 (371 14 (:REWRITE RTL::NEAR+-EXACTP-D))
 (343 14 (:REWRITE RTL::NEAR+-EXACTP-C))
 (340
  340
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (340 340
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (340
     340
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (340 340
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (340 340
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (340 340
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (336 160 (:REWRITE DEFAULT-LESS-THAN-2))
 (307 256 (:REWRITE DEFAULT-PLUS-1))
 (254 158 (:REWRITE DEFAULT-LESS-THAN-1))
 (216 114 (:REWRITE SIMPLIFY-SUMS-<))
 (210 30 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
 (160 160 (:REWRITE THE-FLOOR-BELOW))
 (160 160 (:REWRITE THE-FLOOR-ABOVE))
 (157 157
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (157 157
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (155 155 (:REWRITE INTEGERP-<-CONSTANT))
 (155 155 (:REWRITE CONSTANT-<-INTEGERP))
 (155 155
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (155 155
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (155 155
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (155 155
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (155 155 (:REWRITE |(< c (- x))|))
 (155 155
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (155 155
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (155 155
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (155 155
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (155 155 (:REWRITE |(< (/ x) (/ y))|))
 (155 155 (:REWRITE |(< (- x) c)|))
 (155 155 (:REWRITE |(< (- x) (- y))|))
 (153 13 (:LINEAR RTL::NEAR+-NEGATIVE))
 (105 93 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (96 96
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (67 8 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (67 8
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (60 20 (:REWRITE RTL::BVECP-EXACTP))
 (56 14 (:REWRITE RATIONALP-X))
 (55 5 (:LINEAR RTL::AWAY-NEGATIVE))
 (54 6 (:REWRITE ACL2-NUMBERP-X))
 (50 1 (:REWRITE RTL::AWAY-POSITIVE))
 (44 44 (:REWRITE RTL::TRUNC-TO-0))
 (43 43 (:REWRITE |(< 0 (* x y))|))
 (41 41 (:REWRITE |(< 0 (/ x))|))
 (40 40 (:TYPE-PRESCRIPTION RTL::BVECP))
 (30 30 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (30 30 (:REWRITE |(+ x (- x))|))
 (26 26
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (26 26
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (24 24 (:REWRITE |(< (/ x) 0)|))
 (24 24 (:REWRITE |(< (* x y) 0)|))
 (22 22 (:REWRITE |(< y (+ (- c) x))|))
 (22 22 (:REWRITE |(< x (+ c/d y))|))
 (21 21 (:REWRITE RTL::AWAY-TO-0))
 (20 20 (:REWRITE REDUCE-INTEGERP-+))
 (20 20 (:REWRITE INTEGERP-MINUS-X))
 (20 20 (:REWRITE |(< (+ c/d x) y)|))
 (20 20 (:REWRITE |(< (+ (- c) x) y)|))
 (20 20 (:META META-INTEGERP-CORRECT))
 (18 9 (:REWRITE DEFAULT-EXPT-2))
 (14 14
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (14 14
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (14 14 (:REWRITE REDUCE-RATIONALP-+))
 (14 14 (:REWRITE REDUCE-RATIONALP-*))
 (14 14 (:REWRITE RATIONALP-MINUS-X))
 (14 14 (:REWRITE RTL::NEAR+-EXACTP-A))
 (14 14 (:META META-RATIONALP-CORRECT))
 (13 13 (:REWRITE DEFAULT-MINUS))
 (11 11 (:LINEAR RTL::TRUNC-NEGATIVE))
 (10 10
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (10 10
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (10 10
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (10 10
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (9 9 (:REWRITE DEFAULT-EXPT-1))
 (9 9 (:REWRITE |(expt 1/c n)|))
 (9 9 (:REWRITE |(expt (- x) n)|))
 (8 8
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (8 8
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (8 8
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (8 8 (:REWRITE DEFAULT-TIMES-2))
 (8 8 (:REWRITE DEFAULT-TIMES-1))
 (8 8 (:REWRITE |(equal c (/ x))|))
 (8 8 (:REWRITE |(equal c (- x))|))
 (8 8 (:REWRITE |(equal (/ x) c)|))
 (8 8 (:REWRITE |(equal (/ x) (/ y))|))
 (8 8 (:REWRITE |(equal (- x) c)|))
 (8 8 (:REWRITE |(equal (- x) (- y))|))
 (7 7 (:REWRITE RTL::NEAR+-MONOTONE))
 (5 5 (:REWRITE |(equal (+ (- c) x) y)|))
 (5 5 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (5 5 (:LINEAR EXPT-LINEAR-UPPER-<))
 (5 5 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (5 5 (:LINEAR EXPT-LINEAR-LOWER-<))
 (5 5 (:LINEAR EXPT->=-1-TWO))
 (5 5 (:LINEAR EXPT->-1-TWO))
 (5 5 (:LINEAR EXPT-<=-1-ONE))
 (5 5 (:LINEAR EXPT-<-1-ONE))
 (4 4 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2
    (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (2 2
    (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (2 2
    (:REWRITE |(< x (/ y)) with (< y 0)|)))
(RTL::RND<EQUAL
 (8930 1835
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (4234 177 (:REWRITE RTL::NEAR+-EXACTP-C))
 (4099 2318 (:REWRITE DEFAULT-LESS-THAN-2))
 (4030 177 (:REWRITE RTL::NEAR+-EXACTP-D))
 (3889 1745 (:REWRITE SIMPLIFY-SUMS-<))
 (3303 1901 (:REWRITE DEFAULT-PLUS-2))
 (3200
  3200
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (3200
      3200
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (3200
     3200
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (3200 3200
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (3200 3200
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (3200 3200
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (3092 2318 (:REWRITE DEFAULT-LESS-THAN-1))
 (2318 2318 (:REWRITE THE-FLOOR-BELOW))
 (2318 2318 (:REWRITE THE-FLOOR-ABOVE))
 (2281 1201 (:REWRITE NORMALIZE-ADDENDS))
 (2279 1901 (:REWRITE DEFAULT-PLUS-1))
 (2278 2278
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (2278 2278
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (2272 2272 (:REWRITE INTEGERP-<-CONSTANT))
 (2272 2272 (:REWRITE CONSTANT-<-INTEGERP))
 (2272 2272
       (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (2272 2272
       (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (2272 2272
       (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (2272 2272
       (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (2272 2272 (:REWRITE |(< c (- x))|))
 (2272 2272
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (2272 2272
       (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (2272 2272
       (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (2272 2272
       (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (2272 2272 (:REWRITE |(< (/ x) (/ y))|))
 (2272 2272 (:REWRITE |(< (- x) c)|))
 (2272 2272 (:REWRITE |(< (- x) (- y))|))
 (1365 15 (:LINEAR EXPT->=-1-ONE))
 (1365 15 (:LINEAR EXPT-<=-1-TWO))
 (1350 15 (:LINEAR EXPT-X->=-X))
 (1350 15 (:LINEAR EXPT-X->-X))
 (1335 15 (:LINEAR EXPT->-1-ONE))
 (1335 15 (:LINEAR EXPT-<-1-TWO))
 (1121 77 (:LINEAR RTL::RND-NON-POS))
 (1111 1111
       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (988 190
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (975 325 (:REWRITE RTL::BVECP-EXACTP))
 (929 929 (:REWRITE RTL::TRUNC-TO-0))
 (784 784 (:REWRITE |(< 0 (* x y))|))
 (784 196 (:REWRITE RATIONALP-X))
 (778 778 (:REWRITE |(< 0 (/ x))|))
 (675 179 (:LINEAR RTL::NEAR+-NEGATIVE))
 (663 159 (:LINEAR RTL::TRUNC-NEGATIVE))
 (650 650 (:TYPE-PRESCRIPTION RTL::BVECP))
 (630 90 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
 (566 566
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (566 566
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (551 75 (:LINEAR RTL::AWAY-NEGATIVE))
 (522 58 (:REWRITE ACL2-NUMBERP-X))
 (457 190 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (358 358 (:REWRITE |(< (/ x) 0)|))
 (358 358 (:REWRITE |(< (* x y) 0)|))
 (328 328
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (328 328
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (273 273 (:REWRITE REDUCE-INTEGERP-+))
 (273 273 (:REWRITE INTEGERP-MINUS-X))
 (273 273 (:META META-INTEGERP-CORRECT))
 (236 236 (:REWRITE RTL::AWAY-TO-0))
 (196 196 (:REWRITE REDUCE-RATIONALP-+))
 (196 196 (:REWRITE REDUCE-RATIONALP-*))
 (196 196 (:REWRITE RATIONALP-MINUS-X))
 (196 196 (:META META-RATIONALP-CORRECT))
 (190 190
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (190 190
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (190 190
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (190 190 (:REWRITE |(equal c (/ x))|))
 (190 190 (:REWRITE |(equal c (- x))|))
 (190 190 (:REWRITE |(equal (/ x) c)|))
 (190 190 (:REWRITE |(equal (/ x) (/ y))|))
 (190 190 (:REWRITE |(equal (- x) c)|))
 (190 190 (:REWRITE |(equal (- x) (- y))|))
 (163 163 (:REWRITE |(< y (+ (- c) x))|))
 (163 163 (:REWRITE |(< x (+ c/d y))|))
 (152 76 (:REWRITE DEFAULT-EXPT-2))
 (150 150 (:REWRITE RTL::NEAR+-EXACTP-A))
 (150 150 (:REWRITE DEFAULT-MINUS))
 (90 90 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (90 90 (:REWRITE |(+ x (- x))|))
 (76 76 (:REWRITE DEFAULT-EXPT-1))
 (76 76 (:REWRITE |(expt 1/c n)|))
 (76 76 (:REWRITE |(expt (- x) n)|))
 (74 74 (:REWRITE FOLD-CONSTS-IN-+))
 (72 24 (:REWRITE DEFAULT-TIMES-2))
 (72 24 (:REWRITE DEFAULT-TIMES-1))
 (60 60 (:REWRITE |(< (+ c/d x) y)|))
 (60 60 (:REWRITE |(< (+ (- c) x) y)|))
 (42 6
     (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (30 30
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (30 30
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (30 30
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (30 30
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (30 6
     (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (30 6 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (15 15 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (15 15 (:LINEAR EXPT-LINEAR-UPPER-<))
 (15 15 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (15 15 (:LINEAR EXPT-LINEAR-LOWER-<))
 (15 15 (:LINEAR EXPT->=-1-TWO))
 (15 15 (:LINEAR EXPT->-1-TWO))
 (15 15 (:LINEAR EXPT-<=-1-ONE))
 (15 15 (:LINEAR EXPT-<-1-ONE))
 (9 9
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RTL::RGE-1
     (157 157
          (:TYPE-PRESCRIPTION RTL::RND-NON-POS))
     (157 157
          (:TYPE-PRESCRIPTION RTL::RND-NEGATIVE))
     (20 2
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (18 2 (:REWRITE ACL2-NUMBERP-X))
     (16 4 (:REWRITE RATIONALP-X))
     (14 4 (:REWRITE SIMPLIFY-SUMS-<))
     (14 4
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (14 4 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (9 4 (:REWRITE DEFAULT-LESS-THAN-2))
     (9 4 (:REWRITE DEFAULT-LESS-THAN-1))
     (5 5 (:REWRITE REDUCE-INTEGERP-+))
     (5 5 (:REWRITE INTEGERP-MINUS-X))
     (5 5 (:META META-INTEGERP-CORRECT))
     (4 4 (:REWRITE THE-FLOOR-BELOW))
     (4 4 (:REWRITE THE-FLOOR-ABOVE))
     (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (4 4 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (4 4 (:REWRITE REDUCE-RATIONALP-+))
     (4 4 (:REWRITE REDUCE-RATIONALP-*))
     (4 4
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (4 4
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (4 4 (:REWRITE RATIONALP-MINUS-X))
     (4 4 (:REWRITE INTEGERP-<-CONSTANT))
     (4 4 (:REWRITE CONSTANT-<-INTEGERP))
     (4 4
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (4 4
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (4 4
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (4 4
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (4 4 (:REWRITE |(< c (- x))|))
     (4 4
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (4 4
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (4 4
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (4 4
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (4 4 (:REWRITE |(< (/ x) (/ y))|))
     (4 4 (:REWRITE |(< (- x) c)|))
     (4 4 (:REWRITE |(< (- x) (- y))|))
     (4 4 (:META META-RATIONALP-CORRECT))
     (2 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (2 2
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (2 2
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (2 2
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (2 2 (:REWRITE |(equal c (/ x))|))
     (2 2 (:REWRITE |(equal c (- x))|))
     (2 2 (:REWRITE |(equal (/ x) c)|))
     (2 2 (:REWRITE |(equal (/ x) (/ y))|))
     (2 2 (:REWRITE |(equal (- x) c)|))
     (2 2 (:REWRITE |(equal (- x) (- y))|))
     (2 2 (:LINEAR RTL::RND-NON-POS))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (1 1 (:REWRITE |(< 0 (/ x))|))
     (1 1 (:REWRITE |(< 0 (* x y))|))
     (1 1 (:REWRITE |(< (/ x) 0)|))
     (1 1 (:REWRITE |(< (* x y) 0)|)))
(RTL::RGE-2
     (8 8 (:REWRITE RTL::AWAY-TO-0))
     (8 4
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (8 4 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (7 4 (:REWRITE SIMPLIFY-SUMS-<))
     (7 4 (:REWRITE DEFAULT-LESS-THAN-1))
     (5 4 (:REWRITE DEFAULT-LESS-THAN-2))
     (4 4 (:REWRITE THE-FLOOR-BELOW))
     (4 4 (:REWRITE THE-FLOOR-ABOVE))
     (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (4 4 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (4 4
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (4 4
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (4 4
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (4 4 (:REWRITE NORMALIZE-ADDENDS))
     (4 4 (:REWRITE INTEGERP-<-CONSTANT))
     (4 4 (:REWRITE DEFAULT-PLUS-2))
     (4 4 (:REWRITE DEFAULT-PLUS-1))
     (4 4 (:REWRITE CONSTANT-<-INTEGERP))
     (4 4
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (4 4
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (4 4
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (4 4
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (4 4 (:REWRITE |(< c (- x))|))
     (4 4
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (4 4
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (4 4
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (4 4
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (4 4 (:REWRITE |(< (/ x) (/ y))|))
     (4 4 (:REWRITE |(< (- x) c)|))
     (4 4 (:REWRITE |(< (- x) (- y))|))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (2 2 (:REWRITE |(< (/ x) 0)|))
     (2 2 (:REWRITE |(< (* x y) 0)|))
     (2 2 (:LINEAR RTL::AWAY-NEGATIVE))
     (1 1 (:REWRITE RTL::AWAY-NEGATIVE)))
(RTL::RGE-3
 (59 34 (:REWRITE DEFAULT-PLUS-2))
 (44
  44
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (44 44
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (44 44
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (44 44
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (44 44
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (44 44
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (44 34 (:REWRITE DEFAULT-PLUS-1))
 (19 7 (:REWRITE RTL::BVECP-EXACTP))
 (16 16
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (13 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (13 1
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (12 12 (:TYPE-PRESCRIPTION RTL::BVECP))
 (10 9 (:REWRITE DEFAULT-LESS-THAN-2))
 (9 9 (:REWRITE THE-FLOOR-BELOW))
 (9 9 (:REWRITE THE-FLOOR-ABOVE))
 (9 9
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (9 9
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (9 9 (:REWRITE INTEGERP-<-CONSTANT))
 (9 9 (:REWRITE DEFAULT-LESS-THAN-1))
 (9 9 (:REWRITE CONSTANT-<-INTEGERP))
 (9 9
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (9 9
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (9 9
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (9 9
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (9 9 (:REWRITE |(< c (- x))|))
 (9 9
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (9 9
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (9 9
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (9 9
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (9 9 (:REWRITE |(< (/ x) (/ y))|))
 (9 9 (:REWRITE |(< (- x) c)|))
 (9 9 (:REWRITE |(< (- x) (- y))|))
 (9 8
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (9 8 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (8 8 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (8 2 (:REWRITE RATIONALP-X))
 (4 4 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (4 4 (:REWRITE RTL::AWAY-TO-0))
 (4 4 (:REWRITE |(< 0 (/ x))|))
 (4 4 (:REWRITE |(< 0 (* x y))|))
 (4 2 (:REWRITE DEFAULT-EXPT-2))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (3 3 (:REWRITE REDUCE-INTEGERP-+))
 (3 3 (:REWRITE INTEGERP-MINUS-X))
 (3 3 (:META META-INTEGERP-CORRECT))
 (2 2 (:REWRITE RTL::TRUNC-TO-0))
 (2 2 (:REWRITE REDUCE-RATIONALP-+))
 (2 2 (:REWRITE REDUCE-RATIONALP-*))
 (2 2 (:REWRITE RATIONALP-MINUS-X))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE DEFAULT-MINUS))
 (2 2 (:REWRITE DEFAULT-EXPT-1))
 (2 2 (:REWRITE |(expt 1/c n)|))
 (2 2 (:REWRITE |(expt (- x) n)|))
 (2 2 (:REWRITE |(< (+ c/d x) y)|))
 (2 2 (:REWRITE |(< (+ (- c) x) y)|))
 (2 2 (:REWRITE |(+ c (+ d x))|))
 (2 2 (:META META-RATIONALP-CORRECT))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (1 1
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (1 1
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (1 1 (:REWRITE |(equal c (/ x))|))
 (1 1 (:REWRITE |(equal c (- x))|))
 (1 1 (:REWRITE |(equal (/ x) c)|))
 (1 1 (:REWRITE |(equal (/ x) (/ y))|))
 (1 1 (:REWRITE |(equal (- x) c)|))
 (1 1 (:REWRITE |(equal (- x) (- y))|))
 (1 1 (:REWRITE |(equal (+ (- c) x) y)|))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (* x y) 0)|))
 (1 1 (:LINEAR RTL::AWAY-NEGATIVE)))
(RTL::RGE-4
 (47
  47
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (47 47
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (47 47
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (47 47
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (47 47
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (47 47
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (44 18 (:REWRITE DEFAULT-PLUS-2))
 (30 21 (:REWRITE DEFAULT-LESS-THAN-2))
 (25 15
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (25 15 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (24 21 (:REWRITE DEFAULT-LESS-THAN-1))
 (24 18 (:REWRITE DEFAULT-PLUS-1))
 (24 15 (:REWRITE SIMPLIFY-SUMS-<))
 (21 21 (:REWRITE THE-FLOOR-BELOW))
 (21 21 (:REWRITE THE-FLOOR-ABOVE))
 (21 21
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (21 21
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (21 21 (:REWRITE INTEGERP-<-CONSTANT))
 (21 21 (:REWRITE CONSTANT-<-INTEGERP))
 (21 21
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (21 21
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (21 21
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (21 21
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (21 21 (:REWRITE |(< c (- x))|))
 (21 21
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (21 21
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (21 21
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (21 21
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (21 21 (:REWRITE |(< (/ x) (/ y))|))
 (21 21 (:REWRITE |(< (- x) c)|))
 (21 21 (:REWRITE |(< (- x) (- y))|))
 (15 15 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (14 14
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (14 14 (:REWRITE NORMALIZE-ADDENDS))
 (13 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (13 1
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (12 12 (:REWRITE RTL::TRUNC-TO-0))
 (9 3 (:REWRITE RTL::BVECP-EXACTP))
 (8 8 (:REWRITE |(< 0 (/ x))|))
 (8 8 (:REWRITE |(< 0 (* x y))|))
 (8 2 (:REWRITE RATIONALP-X))
 (6 6 (:TYPE-PRESCRIPTION RTL::BVECP))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (6 6 (:REWRITE RTL::AWAY-TO-0))
 (4 2 (:REWRITE DEFAULT-EXPT-2))
 (3 3 (:REWRITE REDUCE-INTEGERP-+))
 (3 3 (:REWRITE INTEGERP-MINUS-X))
 (3 3 (:META META-INTEGERP-CORRECT))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2 (:REWRITE REDUCE-RATIONALP-+))
 (2 2 (:REWRITE REDUCE-RATIONALP-*))
 (2 2 (:REWRITE RATIONALP-MINUS-X))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE DEFAULT-MINUS))
 (2 2 (:REWRITE DEFAULT-EXPT-1))
 (2 2 (:REWRITE |(expt 1/c n)|))
 (2 2 (:REWRITE |(expt (- x) n)|))
 (2 2 (:REWRITE |(< (/ x) 0)|))
 (2 2 (:REWRITE |(< (* x y) 0)|))
 (2 2 (:REWRITE |(+ c (+ d x))|))
 (2 2 (:META META-RATIONALP-CORRECT))
 (1 1
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (1 1
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (1 1
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (1 1 (:REWRITE |(equal c (/ x))|))
 (1 1 (:REWRITE |(equal c (- x))|))
 (1 1 (:REWRITE |(equal (/ x) c)|))
 (1 1 (:REWRITE |(equal (/ x) (/ y))|))
 (1 1 (:REWRITE |(equal (- x) c)|))
 (1 1 (:REWRITE |(equal (- x) (- y))|))
 (1 1 (:REWRITE |(equal (+ (- c) x) y)|))
 (1 1 (:LINEAR RTL::TRUNC-NEGATIVE))
 (1 1 (:LINEAR RTL::AWAY-NEGATIVE)))
(RTL::RGE-5
     (19 14 (:REWRITE DEFAULT-LESS-THAN-2))
     (18 11 (:REWRITE SIMPLIFY-SUMS-<))
     (18 11
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (18 11 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (17 14 (:REWRITE DEFAULT-LESS-THAN-1))
     (14 14 (:REWRITE THE-FLOOR-BELOW))
     (14 14 (:REWRITE THE-FLOOR-ABOVE))
     (14 14
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (14 14
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (14 14 (:REWRITE INTEGERP-<-CONSTANT))
     (14 14 (:REWRITE CONSTANT-<-INTEGERP))
     (14 14
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (14 14
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (14 14
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (14 14
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (14 14 (:REWRITE |(< c (- x))|))
     (14 14
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (14 14
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (14 14
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (14 14
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (14 14 (:REWRITE |(< (/ x) (/ y))|))
     (14 14 (:REWRITE |(< (- x) c)|))
     (14 14 (:REWRITE |(< (- x) (- y))|))
     (12 12 (:REWRITE RTL::AWAY-TO-0))
     (11 11 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (8 2 (:REWRITE RATIONALP-X))
     (6 2 (:REWRITE RTL::BVECP-EXACTP))
     (5 5 (:REWRITE |(< 0 (/ x))|))
     (5 5 (:REWRITE |(< 0 (* x y))|))
     (4 4 (:TYPE-PRESCRIPTION RTL::BVECP))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (4 4
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (4 4 (:REWRITE NORMALIZE-ADDENDS))
     (4 4 (:REWRITE DEFAULT-PLUS-2))
     (4 4 (:REWRITE DEFAULT-PLUS-1))
     (3 3 (:REWRITE REDUCE-INTEGERP-+))
     (3 3 (:REWRITE INTEGERP-MINUS-X))
     (3 3 (:META META-INTEGERP-CORRECT))
     (2 2 (:REWRITE REDUCE-RATIONALP-+))
     (2 2 (:REWRITE REDUCE-RATIONALP-*))
     (2 2 (:REWRITE RATIONALP-MINUS-X))
     (2 2 (:META META-RATIONALP-CORRECT))
     (2 2 (:LINEAR RTL::AWAY-NEGATIVE))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (1 1 (:REWRITE |(< (/ x) 0)|))
     (1 1 (:REWRITE |(< (* x y) 0)|)))
(RTL::RGE-6
 (1512 101
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (395
  395
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (395 395
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (395
     395
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (395 395
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (395 395
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (395 395
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (364 4 (:LINEAR EXPT->=-1-ONE))
 (364 4 (:LINEAR EXPT-<=-1-TWO))
 (360 4 (:LINEAR EXPT-X->=-X))
 (360 4 (:LINEAR EXPT-X->-X))
 (356 4 (:LINEAR EXPT->-1-ONE))
 (356 4 (:LINEAR EXPT-<-1-TWO))
 (348 206 (:REWRITE DEFAULT-PLUS-2))
 (242 206 (:REWRITE DEFAULT-PLUS-1))
 (191 112 (:REWRITE DEFAULT-LESS-THAN-2))
 (168 24 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
 (141 112 (:REWRITE DEFAULT-LESS-THAN-1))
 (112 112 (:REWRITE THE-FLOOR-BELOW))
 (112 112 (:REWRITE THE-FLOOR-ABOVE))
 (112 112
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (112 112
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (109 109 (:REWRITE INTEGERP-<-CONSTANT))
 (109 109 (:REWRITE CONSTANT-<-INTEGERP))
 (109 109
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (109 109
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (109 109
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (109 109
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (109 109 (:REWRITE |(< c (- x))|))
 (109 109
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (109 109
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (109 109
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (109 109
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (109 109 (:REWRITE |(< (/ x) (/ y))|))
 (109 109 (:REWRITE |(< (- x) c)|))
 (109 109 (:REWRITE |(< (- x) (- y))|))
 (78 72 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (69 69
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (68 8 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (68 8
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (47 17 (:REWRITE RTL::BVECP-EXACTP))
 (30 30 (:TYPE-PRESCRIPTION RTL::BVECP))
 (30 30 (:REWRITE |(< 0 (* x y))|))
 (28 28 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (28 7 (:REWRITE RATIONALP-X))
 (27 27 (:REWRITE |(< 0 (/ x))|))
 (25 25 (:REWRITE RTL::TRUNC-TO-0))
 (24 24 (:REWRITE RTL::AWAY-TO-0))
 (20 20 (:REWRITE |(< y (+ (- c) x))|))
 (20 20 (:REWRITE |(< x (+ c/d y))|))
 (18 18 (:REWRITE |(< (+ c/d x) y)|))
 (18 18 (:REWRITE |(< (+ (- c) x) y)|))
 (16 16
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (16 16
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (15 15 (:REWRITE |(< (/ x) 0)|))
 (15 15 (:REWRITE |(< (* x y) 0)|))
 (12 12 (:REWRITE REDUCE-INTEGERP-+))
 (12 12 (:REWRITE INTEGERP-MINUS-X))
 (12 12 (:REWRITE DEFAULT-TIMES-2))
 (12 12 (:REWRITE DEFAULT-TIMES-1))
 (12 12 (:META META-INTEGERP-CORRECT))
 (12 6 (:REWRITE DEFAULT-EXPT-2))
 (9 9 (:LINEAR RTL::AWAY-NEGATIVE))
 (8 8
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (8 8
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (8 8
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (8 8 (:REWRITE |(equal c (/ x))|))
 (8 8 (:REWRITE |(equal c (- x))|))
 (8 8 (:REWRITE |(equal (/ x) c)|))
 (8 8 (:REWRITE |(equal (/ x) (/ y))|))
 (8 8 (:REWRITE |(equal (- x) c)|))
 (8 8 (:REWRITE |(equal (- x) (- y))|))
 (8 8 (:LINEAR RTL::TRUNC-NEGATIVE))
 (8 8
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (8 8
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (8 8
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (8 8
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (7 7 (:REWRITE REDUCE-RATIONALP-+))
 (7 7 (:REWRITE REDUCE-RATIONALP-*))
 (7 7 (:REWRITE RATIONALP-MINUS-X))
 (7 7 (:REWRITE DEFAULT-MINUS))
 (7 7 (:META META-RATIONALP-CORRECT))
 (6 6 (:REWRITE RTL::NEAR-MONOTONE))
 (6 6 (:REWRITE DEFAULT-EXPT-1))
 (6 6 (:REWRITE |(expt 1/c n)|))
 (6 6 (:REWRITE |(expt (- x) n)|))
 (5 5 (:REWRITE |(equal (+ (- c) x) y)|))
 (4 4 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (4 4 (:LINEAR EXPT-LINEAR-UPPER-<))
 (4 4 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (4 4 (:LINEAR EXPT-LINEAR-LOWER-<))
 (4 4 (:LINEAR EXPT->=-1-TWO))
 (4 4 (:LINEAR EXPT->-1-TWO))
 (4 4 (:LINEAR EXPT-<=-1-ONE))
 (4 4 (:LINEAR EXPT-<-1-ONE))
 (3 3
    (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (3 3
    (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (3 3 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (1 1 (:REWRITE FOLD-CONSTS-IN-+)))
(RTL::RGE-7
 (1486 102
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (364 4 (:LINEAR EXPT->=-1-ONE))
 (364 4 (:LINEAR EXPT-<=-1-TWO))
 (360 4 (:LINEAR EXPT-X->=-X))
 (360 4 (:LINEAR EXPT-X->-X))
 (356 4 (:LINEAR EXPT->-1-ONE))
 (356 4 (:LINEAR EXPT-<-1-TWO))
 (314 183 (:REWRITE DEFAULT-PLUS-2))
 (285
  285
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (285 285
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (285
     285
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (285 285
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (285 285
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (285 285
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (240 10 (:REWRITE RTL::NEAR+-EXACTP-C))
 (220 10 (:REWRITE RTL::NEAR+-EXACTP-D))
 (215 183 (:REWRITE DEFAULT-PLUS-1))
 (168 24 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
 (166 111 (:REWRITE DEFAULT-LESS-THAN-2))
 (139 111 (:REWRITE DEFAULT-LESS-THAN-1))
 (111 111 (:REWRITE THE-FLOOR-BELOW))
 (111 111 (:REWRITE THE-FLOOR-ABOVE))
 (111 111
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (111 111
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (109 109 (:REWRITE INTEGERP-<-CONSTANT))
 (109 109 (:REWRITE CONSTANT-<-INTEGERP))
 (109 109
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (109 109
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (109 109
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (109 109
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (109 109 (:REWRITE |(< c (- x))|))
 (109 109
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (109 109
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (109 109
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (109 109
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (109 109 (:REWRITE |(< (/ x) (/ y))|))
 (109 109 (:REWRITE |(< (- x) c)|))
 (109 109 (:REWRITE |(< (- x) (- y))|))
 (78 72 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (56 56
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (54 7 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (54 7
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (49 17 (:REWRITE RTL::BVECP-EXACTP))
 (32 32 (:TYPE-PRESCRIPTION RTL::BVECP))
 (26 26 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (25 25 (:REWRITE |(< 0 (* x y))|))
 (24 24 (:REWRITE RTL::TRUNC-TO-0))
 (23 23 (:REWRITE |(< 0 (/ x))|))
 (22 22 (:REWRITE RTL::AWAY-TO-0))
 (20 5 (:REWRITE RATIONALP-X))
 (17 17 (:REWRITE |(< y (+ (- c) x))|))
 (17 17 (:REWRITE |(< x (+ c/d y))|))
 (17 17 (:REWRITE |(< (+ c/d x) y)|))
 (17 17 (:REWRITE |(< (+ (- c) x) y)|))
 (14 14 (:REWRITE |(< (/ x) 0)|))
 (14 14 (:REWRITE |(< (* x y) 0)|))
 (13 13
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (13 13
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (10 10 (:REWRITE RTL::NEAR+-EXACTP-A))
 (10 10 (:LINEAR RTL::NEAR+-NEGATIVE))
 (10 5 (:REWRITE DEFAULT-EXPT-2))
 (9 9 (:REWRITE REDUCE-INTEGERP-+))
 (9 9 (:REWRITE INTEGERP-MINUS-X))
 (9 9 (:META META-INTEGERP-CORRECT))
 (9 9 (:LINEAR RTL::AWAY-NEGATIVE))
 (8 8 (:REWRITE DEFAULT-TIMES-2))
 (8 8 (:REWRITE DEFAULT-TIMES-1))
 (8 8 (:LINEAR RTL::TRUNC-NEGATIVE))
 (8 8
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (8 8
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (8 8
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (8 8
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (7 7
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (7 7
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (7 7
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (7 7 (:REWRITE |(equal c (/ x))|))
 (7 7 (:REWRITE |(equal c (- x))|))
 (7 7 (:REWRITE |(equal (/ x) c)|))
 (7 7 (:REWRITE |(equal (/ x) (/ y))|))
 (7 7 (:REWRITE |(equal (- x) c)|))
 (7 7 (:REWRITE |(equal (- x) (- y))|))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (6 6 (:REWRITE DEFAULT-MINUS))
 (5 5 (:REWRITE REDUCE-RATIONALP-+))
 (5 5 (:REWRITE REDUCE-RATIONALP-*))
 (5 5 (:REWRITE RATIONALP-MINUS-X))
 (5 5 (:REWRITE RTL::NEAR+-MONOTONE))
 (5 5 (:REWRITE DEFAULT-EXPT-1))
 (5 5 (:REWRITE |(expt 1/c n)|))
 (5 5 (:REWRITE |(expt (- x) n)|))
 (5 5 (:META META-RATIONALP-CORRECT))
 (4 4 (:REWRITE |(equal (+ (- c) x) y)|))
 (4 4 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (4 4 (:LINEAR EXPT-LINEAR-UPPER-<))
 (4 4 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (4 4 (:LINEAR EXPT-LINEAR-LOWER-<))
 (4 4 (:LINEAR EXPT->=-1-TWO))
 (4 4 (:LINEAR EXPT->-1-TWO))
 (4 4 (:LINEAR EXPT-<=-1-ONE))
 (4 4 (:LINEAR EXPT-<-1-ONE))
 (2 2
    (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (2 2
    (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (2 2 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (1 1 (:REWRITE FOLD-CONSTS-IN-+)))
(RTL::RND>EQUAL
 (2874 362
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (1067 47 (:REWRITE RTL::NEAR+-EXACTP-D))
 (1067 47 (:REWRITE RTL::NEAR+-EXACTP-C))
 (1009 481 (:REWRITE DEFAULT-LESS-THAN-2))
 (938 545 (:REWRITE DEFAULT-PLUS-2))
 (913 362
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (841 326 (:REWRITE SIMPLIFY-SUMS-<))
 (750 318 (:REWRITE NORMALIZE-ADDENDS))
 (721 721
      (:TYPE-PRESCRIPTION RTL::RND-NON-POS))
 (721 721
      (:TYPE-PRESCRIPTION RTL::RND-NEGATIVE))
 (659 481 (:REWRITE DEFAULT-LESS-THAN-1))
 (657 545 (:REWRITE DEFAULT-PLUS-1))
 (546 6 (:LINEAR EXPT->=-1-ONE))
 (546 6 (:LINEAR EXPT-<=-1-TWO))
 (540 6 (:LINEAR EXPT-X->=-X))
 (540 6 (:LINEAR EXPT-X->-X))
 (534 6 (:LINEAR EXPT->-1-ONE))
 (534 6 (:LINEAR EXPT-<-1-TWO))
 (487
  487
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (487 487
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (487
     487
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (487 487
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (487 487
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (487 487
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (481 481 (:REWRITE THE-FLOOR-BELOW))
 (481 481 (:REWRITE THE-FLOOR-ABOVE))
 (448 448
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (448 448
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (448 448 (:REWRITE INTEGERP-<-CONSTANT))
 (448 448 (:REWRITE CONSTANT-<-INTEGERP))
 (448 448
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (448 448
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (448 448
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (448 448
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (448 448 (:REWRITE |(< c (- x))|))
 (448 448
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (448 448
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (448 448
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (448 448
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (448 448 (:REWRITE |(< (/ x) (/ y))|))
 (448 448 (:REWRITE |(< (- x) c)|))
 (448 448 (:REWRITE |(< (- x) (- y))|))
 (441 53
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (360 40 (:REWRITE ACL2-NUMBERP-X))
 (314 314 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (282 282
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (272 68 (:REWRITE RATIONALP-X))
 (252 36 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
 (240 80 (:REWRITE RTL::BVECP-EXACTP))
 (160 160 (:TYPE-PRESCRIPTION RTL::BVECP))
 (139 139 (:REWRITE |(< 0 (/ x))|))
 (139 139 (:REWRITE |(< 0 (* x y))|))
 (138 138 (:REWRITE RTL::TRUNC-TO-0))
 (109 109 (:REWRITE RTL::AWAY-TO-0))
 (98 98
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (98 98
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (81 53 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (80 80 (:REWRITE REDUCE-INTEGERP-+))
 (80 80 (:REWRITE INTEGERP-MINUS-X))
 (80 80 (:META META-INTEGERP-CORRECT))
 (72 72 (:DEFINITION FIX))
 (68 68 (:REWRITE REDUCE-RATIONALP-+))
 (68 68 (:REWRITE REDUCE-RATIONALP-*))
 (68 68 (:REWRITE RATIONALP-MINUS-X))
 (68 68 (:META META-RATIONALP-CORRECT))
 (64 64 (:LINEAR RTL::NEAR+-NEGATIVE))
 (53 53
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (53 53
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (53 53
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (53 53 (:REWRITE |(equal c (/ x))|))
 (53 53 (:REWRITE |(equal c (- x))|))
 (53 53 (:REWRITE |(equal (/ x) c)|))
 (53 53 (:REWRITE |(equal (/ x) (/ y))|))
 (53 53 (:REWRITE |(equal (- x) c)|))
 (53 53 (:REWRITE |(equal (- x) (- y))|))
 (50 50 (:REWRITE |(< y (+ (- c) x))|))
 (50 50 (:REWRITE |(< x (+ c/d y))|))
 (42 42 (:REWRITE |(< (/ x) 0)|))
 (42 42 (:REWRITE |(< (* x y) 0)|))
 (40 40 (:REWRITE RTL::NEAR+-EXACTP-A))
 (38 38 (:REWRITE DEFAULT-MINUS))
 (38 19 (:REWRITE DEFAULT-EXPT-2))
 (37 37 (:LINEAR RTL::AWAY-NEGATIVE))
 (36 36 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (36 36 (:REWRITE |(+ x (- x))|))
 (30 30
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (30 30
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (30 30 (:LINEAR RTL::TRUNC-NEGATIVE))
 (24 24 (:REWRITE |(< (+ c/d x) y)|))
 (24 24 (:REWRITE |(< (+ (- c) x) y)|))
 (19 19 (:REWRITE FOLD-CONSTS-IN-+))
 (19 19 (:REWRITE DEFAULT-EXPT-1))
 (19 19 (:REWRITE |(expt 1/c n)|))
 (19 19 (:REWRITE |(expt (- x) n)|))
 (12 12
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (12 12
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (12 12
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (12 12
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (6 6 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (6 6 (:LINEAR EXPT-LINEAR-UPPER-<))
 (6 6 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (6 6 (:LINEAR EXPT-LINEAR-LOWER-<))
 (6 6 (:LINEAR EXPT->=-1-TWO))
 (6 6 (:LINEAR EXPT->-1-TWO))
 (6 6 (:LINEAR EXPT-<=-1-ONE))
 (6 6 (:LINEAR EXPT-<-1-ONE))
 (3 3 (:LINEAR RTL::RND-NON-POS)))
(RTL::RND-NEAR-EQUAL
 (36678 36678
        (:TYPE-PRESCRIPTION RTL::RND-NEGATIVE))
 (24126 16126 (:REWRITE DEFAULT-PLUS-2))
 (20565 16126 (:REWRITE DEFAULT-PLUS-1))
 (12992 6346 (:REWRITE DEFAULT-LESS-THAN-2))
 (8099 89 (:LINEAR EXPT->=-1-ONE))
 (8099 89 (:LINEAR EXPT-<=-1-TWO))
 (8010 89 (:LINEAR EXPT-X->=-X))
 (8010 89 (:LINEAR EXPT-X->-X))
 (7921 89 (:LINEAR EXPT->-1-ONE))
 (7921 89 (:LINEAR EXPT-<-1-TWO))
 (7619 6346 (:REWRITE DEFAULT-LESS-THAN-1))
 (7345
  7345
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (7345
      7345
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (7345
     7345
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (7345 7345
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (7345 7345
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (7345 7345
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (6346 6346 (:REWRITE THE-FLOOR-BELOW))
 (6346 6346 (:REWRITE THE-FLOOR-ABOVE))
 (5874 5782 (:REWRITE |(< c (- x))|))
 (5866 5782 (:REWRITE |(< (- x) (- y))|))
 (5831 5831
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (5831 5831
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (5782 5782 (:REWRITE INTEGERP-<-CONSTANT))
 (5782 5782 (:REWRITE CONSTANT-<-INTEGERP))
 (5782 5782
       (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (5782 5782
       (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (5782 5782
       (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (5782 5782
       (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (5782 5782
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (5782 5782
       (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (5782 5782
       (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (5782 5782
       (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (5782 5782 (:REWRITE |(< (/ x) (/ y))|))
 (5782 5782 (:REWRITE |(< (- x) c)|))
 (4667 4667
       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (4322 458 (:LINEAR RTL::NEAR+-NEGATIVE))
 (3518 136 (:REWRITE RTL::NEAR+-EXACTP-C))
 (3472 136 (:REWRITE RTL::NEAR+-EXACTP-D))
 (2664 2362 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (2439 557
       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (2136 2136 (:REWRITE |(< y (+ (- c) x))|))
 (2136 2136 (:REWRITE |(< x (+ c/d y))|))
 (1936 557 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (1408 352 (:REWRITE RATIONALP-X))
 (1329 1329 (:REWRITE RTL::TRUNC-TO-0))
 (1295 1295 (:REWRITE |(< 0 (* x y))|))
 (1246 1246 (:REWRITE |(< 0 (/ x))|))
 (1237 49
       (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (1237 49
       (:REWRITE |(< x (/ y)) with (< y 0)|))
 (1102 1102 (:REWRITE RTL::AWAY-TO-0))
 (1075 1075 (:REWRITE |(< (+ c/d x) y)|))
 (1075 1075 (:REWRITE |(< (+ (- c) x) y)|))
 (1020 340 (:REWRITE RTL::BVECP-EXACTP))
 (1011 927 (:REWRITE DEFAULT-MINUS))
 (902 902 (:REWRITE |(< (/ x) 0)|))
 (902 902 (:REWRITE |(< (* x y) 0)|))
 (762 762
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (762 762
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (680 680 (:TYPE-PRESCRIPTION RTL::BVECP))
 (627 592 (:REWRITE |(equal (/ x) (/ y))|))
 (625 501 (:REWRITE DEFAULT-TIMES-2))
 (625 501 (:REWRITE DEFAULT-TIMES-1))
 (592 592
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (592 592
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (592 592 (:REWRITE |(equal c (/ x))|))
 (592 592 (:REWRITE |(equal (- x) (- y))|))
 (562 562 (:LINEAR RTL::AWAY-NEGATIVE))
 (557 557
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (557 557 (:REWRITE |(equal c (- x))|))
 (557 557 (:REWRITE |(equal (- x) c)|))
 (521 521 (:LINEAR RTL::TRUNC-NEGATIVE))
 (470 470
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (470 470
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (468 52 (:REWRITE ACL2-NUMBERP-X))
 (435 435 (:REWRITE FOLD-CONSTS-IN-+))
 (372 372 (:REWRITE REDUCE-INTEGERP-+))
 (372 372 (:REWRITE INTEGERP-MINUS-X))
 (372 372 (:META META-INTEGERP-CORRECT))
 (352 352 (:REWRITE REDUCE-RATIONALP-+))
 (352 352 (:REWRITE REDUCE-RATIONALP-*))
 (352 352 (:REWRITE RATIONALP-MINUS-X))
 (352 352 (:META META-RATIONALP-CORRECT))
 (305 305
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (282 141 (:REWRITE DEFAULT-EXPT-2))
 (245 49
      (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (178 178
      (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (178 178
      (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (178 178
      (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (178 178
      (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (141 141 (:REWRITE DEFAULT-EXPT-1))
 (141 141 (:REWRITE |(expt 1/c n)|))
 (141 141 (:REWRITE |(expt (- x) n)|))
 (136 136 (:REWRITE RTL::NEAR+-EXACTP-A))
 (105 35 (:REWRITE |(equal x (/ y))|))
 (89 89 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (89 89 (:LINEAR EXPT-LINEAR-UPPER-<))
 (89 89 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (89 89 (:LINEAR EXPT-LINEAR-LOWER-<))
 (89 89 (:LINEAR EXPT->=-1-TWO))
 (89 89 (:LINEAR EXPT->-1-TWO))
 (89 89 (:LINEAR EXPT-<=-1-ONE))
 (89 89 (:LINEAR EXPT-<-1-ONE))
 (70 35 (:REWRITE DEFAULT-DIVIDE))
 (70 35 (:REWRITE |(not (equal x (/ y)))|))
 (66 66
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
