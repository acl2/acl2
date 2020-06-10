(RTL::NEAR-DOWN-1
 (542 30
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (156 12 (:REWRITE |(+ y (+ x z))|))
 (139 3 (:LINEAR EXPT->=-1-ONE))
 (139 3 (:LINEAR EXPT-<=-1-TWO))
 (138 3 (:LINEAR EXPT-X->=-X))
 (138 3 (:LINEAR EXPT-X->-X))
 (136 3 (:LINEAR EXPT->-1-ONE))
 (136 3 (:LINEAR EXPT-<-1-TWO))
 (62 26 (:REWRITE |(+ c (+ d x))|))
 (56
  56
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (56 56
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (56 56
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (56 56
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (56 56
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (52 52 (:REWRITE DEFAULT-PLUS-2))
 (52 52 (:REWRITE DEFAULT-PLUS-1))
 (30 30 (:REWRITE THE-FLOOR-BELOW))
 (30 30 (:REWRITE THE-FLOOR-ABOVE))
 (30 30
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (30 30
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (30 30 (:REWRITE DEFAULT-LESS-THAN-2))
 (30 30 (:REWRITE DEFAULT-LESS-THAN-1))
 (21 3 (:REWRITE DEFAULT-TIMES-2))
 (20 20 (:REWRITE |(< x (+ c/d y))|))
 (18 18 (:REWRITE SIMPLIFY-SUMS-<))
 (18 18
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (18 18
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (18 18 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (18 18 (:REWRITE INTEGERP-<-CONSTANT))
 (18 18 (:REWRITE CONSTANT-<-INTEGERP))
 (18 18
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (18 18
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (18 18
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (18 18
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (18 18 (:REWRITE |(< c (- x))|))
 (18 18
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (18 18
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (18 18
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (18 18
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (18 18 (:REWRITE |(< (/ x) (/ y))|))
 (18 18 (:REWRITE |(< (- x) c)|))
 (18 18 (:REWRITE |(< (- x) (- y))|))
 (16 16
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (16 16 (:REWRITE NORMALIZE-ADDENDS))
 (14 14 (:REWRITE FOLD-CONSTS-IN-+))
 (12 12 (:REWRITE |(< y (+ (- c) x))|))
 (12 12 (:REWRITE |(+ 0 x)|))
 (10 10 (:REWRITE |(< 0 (* x y))|))
 (10 10 (:REWRITE |(< (+ c/d x) y)|))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (6 6 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (6 6 (:REWRITE |(< 0 (/ x))|))
 (6 6 (:REWRITE |(< (+ (- c) x) y)|))
 (6 6 (:REWRITE |(< (* x y) 0)|))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (6 6
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (4 3 (:REWRITE DEFAULT-TIMES-1))
 (3 3 (:REWRITE DEFAULT-EXPT-2))
 (3 3 (:REWRITE DEFAULT-EXPT-1))
 (3 3 (:REWRITE |(expt 1/c n)|))
 (3 3 (:REWRITE |(expt (- x) n)|))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<))
 (3 3 (:LINEAR EXPT->=-1-TWO))
 (3 3 (:LINEAR EXPT->-1-TWO))
 (3 3 (:LINEAR EXPT-<=-1-ONE))
 (3 3 (:LINEAR EXPT-<-1-ONE))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2 (:REWRITE REDUCE-INTEGERP-+))
 (2 2 (:REWRITE INTEGERP-MINUS-X))
 (2 2 (:REWRITE |(< (/ x) 0)|))
 (2 2 (:META META-INTEGERP-CORRECT))
 (1 1 (:TYPE-PRESCRIPTION BUBBLE-DOWN)))
(RTL::R-EXACTP-1 (37 1
                     (:REWRITE |(<= x (/ y)) with (< 0 y)|))
                 (33 1 (:REWRITE |(< (/ x) y) with (< 0 x)|))
                 (21 17 (:REWRITE DEFAULT-TIMES-2))
                 (17 17 (:REWRITE DEFAULT-TIMES-1))
                 (16 12
                     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
                 (16 12
                     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
                 (13 10 (:REWRITE CONSTANT-<-INTEGERP))
                 (13 10
                     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
                 (13 10
                     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
                 (12 12 (:REWRITE THE-FLOOR-BELOW))
                 (12 12 (:REWRITE THE-FLOOR-ABOVE))
                 (12 12
                     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
                 (12 12 (:REWRITE DEFAULT-LESS-THAN-2))
                 (12 12 (:REWRITE DEFAULT-LESS-THAN-1))
                 (10 10
                     (:REWRITE REMOVE-STRICT-INEQUALITIES))
                 (10 10 (:REWRITE INTEGERP-<-CONSTANT))
                 (10 10
                     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
                 (10 10
                     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
                 (10 10
                     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
                 (10 10 (:REWRITE |(< c (- x))|))
                 (10 10
                     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
                 (10 10
                     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
                 (10 10
                     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
                 (10 10 (:REWRITE |(< (/ x) (/ y))|))
                 (10 10 (:REWRITE |(< (- x) c)|))
                 (10 10 (:REWRITE |(< (- x) (- y))|))
                 (8 2 (:REWRITE RATIONALP-X))
                 (6 6 (:REWRITE SIMPLIFY-SUMS-<))
                 (6 6 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
                 (5 5 (:REWRITE REDUCE-INTEGERP-+))
                 (5 5
                    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                 (5 5 (:REWRITE INTEGERP-MINUS-X))
                 (5 5 (:META META-INTEGERP-CORRECT))
                 (4 4 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
                 (4 4 (:TYPE-PRESCRIPTION ABS))
                 (2 2 (:REWRITE REDUCE-RATIONALP-+))
                 (2 2 (:REWRITE REDUCE-RATIONALP-*))
                 (2 2 (:REWRITE RATIONALP-MINUS-X))
                 (2 2
                    (:REWRITE |(<= (/ x) y) with (< x 0)|))
                 (2 2
                    (:REWRITE |(<= (/ x) y) with (< 0 x)|))
                 (2 2 (:REWRITE |(< x (/ y)) with (< y 0)|))
                 (2 2 (:REWRITE |(< 0 (* x y))|))
                 (2 2 (:META META-RATIONALP-CORRECT))
                 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
                 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                 (1 1
                    (:REWRITE |(<= x (/ y)) with (< y 0)|))
                 (1 1
                    (:REWRITE |(< (/ x) y) with (< x 0)|)))
(RTL::R-EXACTP-2 (88 3
                     (:REWRITE |(<= x (/ y)) with (< 0 y)|))
                 (24 15 (:REWRITE CONSTANT-<-INTEGERP))
                 (21 15
                     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
                 (21 15
                     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
                 (15 15 (:REWRITE THE-FLOOR-BELOW))
                 (15 15 (:REWRITE THE-FLOOR-ABOVE))
                 (15 15 (:REWRITE SIMPLIFY-SUMS-<))
                 (15 15
                     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
                 (15 15
                     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
                 (15 15
                     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
                 (15 15 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
                 (15 15 (:REWRITE INTEGERP-<-CONSTANT))
                 (15 15 (:REWRITE DEFAULT-LESS-THAN-2))
                 (15 15 (:REWRITE DEFAULT-LESS-THAN-1))
                 (15 15
                     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
                 (15 15
                     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
                 (15 15
                     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
                 (15 15 (:REWRITE |(< c (- x))|))
                 (15 15
                     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
                 (15 15
                     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
                 (15 15
                     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
                 (15 15 (:REWRITE |(< (/ x) (/ y))|))
                 (15 15 (:REWRITE |(< (- x) c)|))
                 (15 15 (:REWRITE |(< (- x) (- y))|))
                 (9 9 (:REWRITE REDUCE-INTEGERP-+))
                 (9 9 (:REWRITE INTEGERP-MINUS-X))
                 (9 9 (:REWRITE DEFAULT-TIMES-2))
                 (9 9 (:REWRITE DEFAULT-TIMES-1))
                 (9 9 (:META META-INTEGERP-CORRECT))
                 (8 8
                    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                 (8 2 (:REWRITE RATIONALP-X))
                 (8 1 (:REWRITE |(* (* x y) z)|))
                 (3 3
                    (:REWRITE |(<= x (/ y)) with (< y 0)|))
                 (3 3 (:REWRITE |(< (/ x) y) with (< x 0)|))
                 (2 2 (:REWRITE REDUCE-RATIONALP-+))
                 (2 2 (:REWRITE REDUCE-RATIONALP-*))
                 (2 2 (:REWRITE RATIONALP-MINUS-X))
                 (2 2 (:META META-RATIONALP-CORRECT))
                 (1 1 (:REWRITE |(* c (* d x))|)))
(RTL::R-EXACTP-3 (114 1
                      (:REWRITE |(<= x (/ y)) with (< 0 y)|))
                 (110 110
                      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
                 (110 110
                      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                 (110 110
                      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                 (110 110
                      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                 (34 10 (:REWRITE DEFAULT-LESS-THAN-2))
                 (28 4
                     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
                 (28 4 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
                 (26 14 (:REWRITE DEFAULT-TIMES-2))
                 (25 1 (:REWRITE |(* (* x y) z)|))
                 (21 6 (:REWRITE CONSTANT-<-INTEGERP))
                 (18 14 (:REWRITE DEFAULT-TIMES-1))
                 (18 10
                     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
                 (18 10
                     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
                 (18 10 (:REWRITE DEFAULT-LESS-THAN-1))
                 (12 1 (:REWRITE |(* y (* x z))|))
                 (11 11 (:TYPE-PRESCRIPTION NOT-INTEGERP-4E))
                 (11 11 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
                 (11 11 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
                 (11 11 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
                 (10 10 (:REWRITE THE-FLOOR-BELOW))
                 (10 10 (:REWRITE THE-FLOOR-ABOVE))
                 (10 10
                     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
                 (9 6
                    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
                 (8 8 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
                 (8 8 (:TYPE-PRESCRIPTION ABS))
                 (8 8
                    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                 (6 6 (:REWRITE INTEGERP-<-CONSTANT))
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
                    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
                 (6 6
                    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
                 (6 6
                    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
                 (6 6 (:REWRITE |(< (/ x) (/ y))|))
                 (6 6 (:REWRITE |(< (- x) c)|))
                 (6 6 (:REWRITE |(< (- x) (- y))|))
                 (6 2 (:REWRITE |(< (/ x) y) with (< x 0)|))
                 (5 5
                    (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
                 (5 5 (:REWRITE DEFAULT-DIVIDE))
                 (5 1
                    (:REWRITE |(<= x (/ y)) with (< y 0)|))
                 (4 4 (:REWRITE SIMPLIFY-SUMS-<))
                 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
                 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                 (2 2 (:REWRITE REDUCE-INTEGERP-+))
                 (2 2 (:REWRITE INTEGERP-MINUS-X))
                 (2 2
                    (:REWRITE |(<= (/ x) y) with (< x 0)|))
                 (2 2 (:REWRITE |(* c (* d x))|))
                 (2 2 (:META META-INTEGERP-CORRECT))
                 (1 1
                    (:REWRITE |(< 1 (* x (/ y))) with (< y 0)|))
                 (1 1
                    (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
                 (1 1
                    (:REWRITE |(< (* (/ x) y) 1) with (< 0 x)|)))
(RTL::R-EXACTP-4
 (170 170
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (170 170
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (170 170
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (170 170
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (114 1
      (:REWRITE |(<= x (/ y)) with (< 0 y)|))
 (94 1 (:REWRITE |(< (/ x) y) with (< 0 x)|))
 (77 1 (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (63 1
     (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (49 15 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (48 15
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (46 2 (:REWRITE |(* (* x y) z)|))
 (44 28 (:REWRITE DEFAULT-TIMES-2))
 (40 19 (:REWRITE DEFAULT-LESS-THAN-2))
 (34 19 (:REWRITE CONSTANT-<-INTEGERP))
 (32 28 (:REWRITE DEFAULT-TIMES-1))
 (32 19 (:REWRITE DEFAULT-LESS-THAN-1))
 (31 19
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (27 19
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (27 19
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (26 19 (:REWRITE INTEGERP-<-CONSTANT))
 (22 22 (:TYPE-PRESCRIPTION NOT-INTEGERP-4E))
 (22 22 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
 (22 22 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
 (22 22 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
 (22 22
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (20 2 (:REWRITE |(* y (* x z))|))
 (19 19 (:REWRITE THE-FLOOR-BELOW))
 (19 19 (:REWRITE THE-FLOOR-ABOVE))
 (19 19
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
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
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (19 19
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (19 19
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (19 19 (:REWRITE |(< (/ x) (/ y))|))
 (19 19 (:REWRITE |(< (- x) c)|))
 (19 19 (:REWRITE |(< (- x) (- y))|))
 (15 15 (:REWRITE SIMPLIFY-SUMS-<))
 (14 14
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (14 14 (:REWRITE DEFAULT-DIVIDE))
 (8 8 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
 (8 8 (:TYPE-PRESCRIPTION ABS))
 (8 8 (:REWRITE REDUCE-INTEGERP-+))
 (8 8 (:REWRITE INTEGERP-MINUS-X))
 (8 8 (:META META-INTEGERP-CORRECT))
 (8 2 (:REWRITE RATIONALP-X))
 (8 2 (:REWRITE |(* y x)|))
 (6
   6
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (6
  6
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (5 5 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (5 5
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (5 5
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (5 5
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (5 5
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (5 5
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (5 5 (:REWRITE |(equal c (/ x))|))
 (5 5 (:REWRITE |(equal c (- x))|))
 (5 5 (:REWRITE |(equal (/ x) c)|))
 (5 5 (:REWRITE |(equal (/ x) (/ y))|))
 (5 5 (:REWRITE |(equal (- x) c)|))
 (5 5 (:REWRITE |(equal (- x) (- y))|))
 (5 1
    (:REWRITE |(<= x (/ y)) with (< y 0)|))
 (5 1 (:REWRITE |(< (/ x) y) with (< x 0)|))
 (4 4 (:REWRITE |(* c (* d x))|))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2 (:REWRITE REDUCE-RATIONALP-+))
 (2 2 (:REWRITE REDUCE-RATIONALP-*))
 (2 2 (:REWRITE RATIONALP-MINUS-X))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:REWRITE |(< 0 (* x y))|))
 (2 2 (:META META-RATIONALP-CORRECT))
 (1 1
    (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (1 1 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (1 1
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (1 1
    (:REWRITE |(< 0 (* x (/ y))) rationalp (* x (/ y))|)))
(RTL::R-EXACTP-5
 (128 128
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (128 128
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (128 128
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (128 128
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (114 1
      (:REWRITE |(<= x (/ y)) with (< 0 y)|))
 (94 1 (:REWRITE |(< (/ x) y) with (< 0 x)|))
 (30 10 (:REWRITE DEFAULT-LESS-THAN-2))
 (30 6
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (30 6 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (25 1 (:REWRITE |(* (* x y) z)|))
 (24 12 (:REWRITE DEFAULT-TIMES-2))
 (24 9 (:REWRITE CONSTANT-<-INTEGERP))
 (16 12 (:REWRITE DEFAULT-TIMES-1))
 (15 9
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (14 10
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (14 10
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (14 10 (:REWRITE DEFAULT-LESS-THAN-1))
 (12 1 (:REWRITE |(* y (* x z))|))
 (11 11 (:TYPE-PRESCRIPTION NOT-INTEGERP-4E))
 (11 11 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
 (11 11 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
 (11 11 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
 (10 10 (:REWRITE THE-FLOOR-BELOW))
 (10 10 (:REWRITE THE-FLOOR-ABOVE))
 (10 10
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (9 9
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (9 9 (:REWRITE INTEGERP-<-CONSTANT))
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
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (9 9
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (9 9
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (9 9 (:REWRITE |(< (/ x) (/ y))|))
 (9 9 (:REWRITE |(< (- x) c)|))
 (9 9 (:REWRITE |(< (- x) (- y))|))
 (6
   6
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (6
  6
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (6 6 (:REWRITE SIMPLIFY-SUMS-<))
 (5 5
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (5 5 (:REWRITE DEFAULT-DIVIDE))
 (5 1
    (:REWRITE |(<= x (/ y)) with (< y 0)|))
 (5 1 (:REWRITE |(< (/ x) y) with (< x 0)|))
 (4 4 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
 (4 4 (:TYPE-PRESCRIPTION ABS))
 (4 1 (:REWRITE |(* y x)|))
 (3 3 (:REWRITE REDUCE-INTEGERP-+))
 (3 3 (:REWRITE INTEGERP-MINUS-X))
 (3 3 (:META META-INTEGERP-CORRECT))
 (2 2 (:REWRITE |(* c (* d x))|))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (* x y) 0)|))
 (1 1
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (1 1
    (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|)))
(M
 (4
  4
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE)))
(RTL::R-EXACTP-6
 (6
   6
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (6
  6
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (2 2 (:REWRITE THE-FLOOR-BELOW))
 (2 2 (:REWRITE THE-FLOOR-ABOVE))
 (2 2 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (2 2
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (2 2
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (2 2 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (2 2 (:REWRITE INTEGERP-<-CONSTANT))
 (2 2 (:REWRITE DEFAULT-LESS-THAN-2))
 (2 2 (:REWRITE DEFAULT-LESS-THAN-1))
 (2 2 (:REWRITE CONSTANT-<-INTEGERP))
 (2 2
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (2 2
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (2 2
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (2 2
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (2 2 (:REWRITE |(< c (- x))|))
 (2 2
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (2 2
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (2 2
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (2 2
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (2 2 (:REWRITE |(< (/ x) (/ y))|))
 (2 2 (:REWRITE |(< (- x) c)|))
 (2 2 (:REWRITE |(< (- x) (- y))|))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1 (:REWRITE SIMPLIFY-SUMS-<))
 (1 1
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (1 1 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (* x y) 0)|)))
(RTL::R-EXACTP-7
 (289 46 (:REWRITE DEFAULT-TIMES-2))
 (249 46 (:REWRITE DEFAULT-TIMES-1))
 (148
  148
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (148 148
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (148
     148
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (148 148
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (148 148
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (103 43 (:REWRITE DEFAULT-PLUS-1))
 (70 43 (:REWRITE DEFAULT-PLUS-2))
 (65 11 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (47 11 (:REWRITE DEFAULT-LESS-THAN-2))
 (42 11
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (30 3 (:REWRITE DEFAULT-MINUS))
 (29 11 (:REWRITE DEFAULT-LESS-THAN-1))
 (28 10 (:REWRITE |(< (- x) (- y))|))
 (19 10 (:REWRITE |(< (- x) c)|))
 (13 13
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (13 10
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (11 11 (:REWRITE THE-FLOOR-BELOW))
 (11 11 (:REWRITE THE-FLOOR-ABOVE))
 (11 11
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (11 11
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (10 10
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (10 10 (:REWRITE INTEGERP-<-CONSTANT))
 (10 10 (:REWRITE CONSTANT-<-INTEGERP))
 (10 10
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (10 10
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (10 10
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (10 10
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (10 10 (:REWRITE |(< c (- x))|))
 (10 10
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (10 10
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (10 10
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (10 10 (:REWRITE |(< (/ x) (/ y))|))
 (5 5 (:REWRITE DEFAULT-EXPT-2))
 (5 5 (:REWRITE DEFAULT-EXPT-1))
 (5 5 (:REWRITE |(expt 1/c n)|))
 (5 5 (:REWRITE |(expt (- x) n)|))
 (5 2 (:REWRITE |(+ c (+ d x))|))
 (4 4 (:REWRITE SIMPLIFY-SUMS-<))
 (4 1 (:REWRITE RATIONALP-X))
 (3 3 (:REWRITE REDUCE-INTEGERP-+))
 (3 3 (:REWRITE INTEGERP-MINUS-X))
 (3 3 (:REWRITE |(< 0 (* x y))|))
 (3 3 (:REWRITE |(< (+ c/d x) y)|))
 (3 3 (:REWRITE |(< (+ (- c) x) y)|))
 (3 3 (:REWRITE |(* (- x) y)|))
 (3 3 (:META META-INTEGERP-CORRECT))
 (3 1 (:REWRITE RTL::BVECP-EXACTP))
 (2 2 (:TYPE-PRESCRIPTION RTL::BVECP))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE REDUCE-RATIONALP-+))
 (1 1 (:REWRITE REDUCE-RATIONALP-*))
 (1 1 (:REWRITE RATIONALP-MINUS-X))
 (1 1 (:REWRITE |(< x (+ c/d y))|))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (* x y) 0)|))
 (1 1 (:META META-RATIONALP-CORRECT)))
(RTL::R-EXACTP-8
 (290 52 (:REWRITE DEFAULT-TIMES-1))
 (286 52 (:REWRITE DEFAULT-TIMES-2))
 (214
  214
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (214 214
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (214
     214
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (214 214
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (214 214
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (182 27 (:REWRITE DEFAULT-LESS-THAN-2))
 (173 27 (:REWRITE DEFAULT-LESS-THAN-1))
 (72 15
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (69 1 (:REWRITE ODD-EXPT-THM))
 (56 34 (:REWRITE DEFAULT-PLUS-1))
 (44 8 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (41 14 (:REWRITE |(< c (- x))|))
 (29 12 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (28 28 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (28 28 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (28 28 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (28 4 (:REWRITE ACL2-NUMBERP-X))
 (27 27 (:REWRITE THE-FLOOR-BELOW))
 (27 27 (:REWRITE THE-FLOOR-ABOVE))
 (23 14 (:REWRITE |(< (- x) (- y))|))
 (21 3 (:REWRITE DEFAULT-MINUS))
 (20 14
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (20 12 (:REWRITE SIMPLIFY-SUMS-<))
 (20 5 (:REWRITE RATIONALP-X))
 (15 15
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (15 15
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (15 15 (:REWRITE REDUCE-INTEGERP-+))
 (15 15 (:REWRITE INTEGERP-MINUS-X))
 (15 15 (:META META-INTEGERP-CORRECT))
 (14 14
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (14 14
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (14 14
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (14 14
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (14 14
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (14 14
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (14 14
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (14 14 (:REWRITE |(< (/ x) (/ y))|))
 (13 13 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (13 13
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (13 13 (:REWRITE INTEGERP-<-CONSTANT))
 (13 13 (:REWRITE CONSTANT-<-INTEGERP))
 (13 13 (:REWRITE |(< (- x) c)|))
 (11 11
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (7 7 (:REWRITE |(< x (+ c/d y))|))
 (6 6 (:REWRITE |(< y (+ (- c) x))|))
 (6 6 (:REWRITE |(< (+ c/d x) y)|))
 (6 6 (:REWRITE |(< (+ (- c) x) y)|))
 (5 5 (:REWRITE REDUCE-RATIONALP-+))
 (5 5 (:REWRITE REDUCE-RATIONALP-*))
 (5 5 (:REWRITE RATIONALP-MINUS-X))
 (5 5 (:META META-RATIONALP-CORRECT))
 (4 4 (:REWRITE DEFAULT-EXPT-1))
 (4 1 (:REWRITE |(+ c (+ d x))|))
 (2 2 (:REWRITE |(expt 1/c n)|))
 (2 2 (:REWRITE |(expt (- x) n)|))
 (2 2 (:REWRITE |(< 0 (* x y))|))
 (2 2 (:REWRITE |(* (- x) y)|))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (1 1 (:REWRITE |(< 0 (/ x))|))
 (1 1 (:REWRITE |(- (- x))|)))
(RTL::MD)
(RTL::R-EXACTP-9
 (157
  157
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (157 157
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (157
     157
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (157 157
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (157 157
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (87 25
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (84 2 (:REWRITE ODD-EXPT-THM))
 (44 25 (:REWRITE DEFAULT-LESS-THAN-2))
 (41 23
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (36 16
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (35 15 (:REWRITE SIMPLIFY-SUMS-<))
 (26 25 (:REWRITE DEFAULT-LESS-THAN-1))
 (25 25 (:REWRITE THE-FLOOR-BELOW))
 (25 25 (:REWRITE THE-FLOOR-ABOVE))
 (25 25
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (25 25
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (23 23 (:REWRITE INTEGERP-<-CONSTANT))
 (23 23 (:REWRITE CONSTANT-<-INTEGERP))
 (23 23
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (23 23
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (23 23
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (23 23
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (23 23 (:REWRITE |(< c (- x))|))
 (23 23
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (23 23
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (23 23
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (23 23 (:REWRITE |(< (/ x) (/ y))|))
 (23 23 (:REWRITE |(< (- x) c)|))
 (23 23 (:REWRITE |(< (- x) (- y))|))
 (15 14 (:REWRITE DEFAULT-PLUS-1))
 (14 14 (:REWRITE DEFAULT-PLUS-2))
 (12 4 (:REWRITE RTL::BVECP-EXACTP))
 (10 10 (:REWRITE REDUCE-INTEGERP-+))
 (10 10 (:REWRITE INTEGERP-MINUS-X))
 (10 10 (:META META-INTEGERP-CORRECT))
 (8 8 (:TYPE-PRESCRIPTION RTL::BVECP))
 (8 2 (:REWRITE RATIONALP-X))
 (8 2 (:REWRITE |(+ c (+ d x))|))
 (4 4
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (3 3 (:REWRITE |(< x (+ c/d y))|))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2 (:REWRITE REDUCE-RATIONALP-+))
 (2 2 (:REWRITE REDUCE-RATIONALP-*))
 (2 2 (:REWRITE RATIONALP-MINUS-X))
 (2 2 (:REWRITE DEFAULT-EXPT-2))
 (2 2 (:REWRITE DEFAULT-EXPT-1))
 (2 2 (:REWRITE |(expt 1/c n)|))
 (2 2 (:REWRITE |(expt (- x) n)|))
 (2 2 (:REWRITE |(< 0 (* x y))|))
 (2 2 (:REWRITE |(< (/ x) 0)|))
 (2 2 (:REWRITE |(< (* x y) 0)|))
 (2 2 (:META META-RATIONALP-CORRECT))
 (1 1 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE DEFAULT-MINUS))
 (1 1 (:REWRITE |(< y (+ (- c) x))|))
 (1 1 (:REWRITE |(< (+ c/d x) y)|))
 (1 1 (:REWRITE |(< (+ (- c) x) y)|)))
(RTL::R-EXACTP-10
 (1895 191 (:REWRITE DEFAULT-TIMES-2))
 (840 191 (:REWRITE DEFAULT-TIMES-1))
 (830 158 (:REWRITE DEFAULT-PLUS-1))
 (599
  599
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (599 599
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (599
     599
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (599 599
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (599 599
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (300 300
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (300 300
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (300 300
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (209 145
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
 (192 4
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (177 145
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
 (164 105
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (137 137
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
 (105 105
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (100 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-4D))
 (100 10 (:REWRITE DEFAULT-DIVIDE))
 (99 11 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (96 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (86 86 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (58 10 (:REWRITE ACL2-NUMBERP-X))
 (57 57
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (39 4 (:REWRITE |(equal (- x) (- y))|))
 (32 8 (:REWRITE RATIONALP-X))
 (30 30 (:REWRITE REDUCE-INTEGERP-+))
 (30 30 (:REWRITE INTEGERP-MINUS-X))
 (30 30 (:META META-INTEGERP-CORRECT))
 (11 11 (:REWRITE FOLD-CONSTS-IN-+))
 (11 5
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-3D))
 (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-2D))
 (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-1D))
 (10 10 (:REWRITE DEFAULT-EXPT-1))
 (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-4G))
 (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-3G))
 (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-2G))
 (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-1G))
 (8 8 (:REWRITE REDUCE-RATIONALP-+))
 (8 8 (:REWRITE REDUCE-RATIONALP-*))
 (8 8 (:REWRITE RATIONALP-MINUS-X))
 (8 8 (:META META-RATIONALP-CORRECT))
 (7 7 (:REWRITE |(* c (* d x))|))
 (6 6
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (5 5 (:REWRITE THE-FLOOR-BELOW))
 (5 5 (:REWRITE THE-FLOOR-ABOVE))
 (5 5 (:REWRITE SIMPLIFY-SUMS-<))
 (5 5
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (5 5 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (5 5 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (5 5
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (5 5
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (5 5 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (5 5 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (5 5 (:REWRITE INTEGERP-<-CONSTANT))
 (5 5 (:REWRITE DEFAULT-LESS-THAN-2))
 (5 5 (:REWRITE DEFAULT-LESS-THAN-1))
 (5 5 (:REWRITE CONSTANT-<-INTEGERP))
 (5 5 (:REWRITE |(expt 1/c n)|))
 (5 5 (:REWRITE |(expt (- x) n)|))
 (5 5
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (5 5
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (5 5
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (5 5
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (5 5 (:REWRITE |(< c (- x))|))
 (5 5
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (5 5
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (5 5
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (5 5 (:REWRITE |(< (/ x) (/ y))|))
 (5 5 (:REWRITE |(< (- x) c)|))
 (5 5 (:REWRITE |(< (- x) (- y))|))
 (4 4
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (4 4
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (4 4
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (4 4 (:REWRITE |(equal c (/ x))|))
 (4 4 (:REWRITE |(equal c (- x))|))
 (4 4 (:REWRITE |(equal (/ x) c)|))
 (4 4 (:REWRITE |(equal (/ x) (/ y))|))
 (4 4 (:REWRITE |(equal (- x) c)|))
 (4 4 (:REWRITE |(equal (+ (- c) x) y)|)))
(RTL::R-EXACTP-11
 (464
  464
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (464 464
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (464
     464
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (464 464
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (464 464
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (384 39
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (257 8 (:REWRITE RATIONALP-X))
 (223 39 (:REWRITE DEFAULT-PLUS-2))
 (211 22 (:REWRITE DEFAULT-TIMES-2))
 (205 205
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (205 205
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (205 205
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (141 22 (:REWRITE DEFAULT-TIMES-1))
 (126 3 (:REWRITE ODD-EXPT-THM))
 (107 1
      (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (107 1
      (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (106 39 (:REWRITE DEFAULT-LESS-THAN-2))
 (106 39 (:REWRITE DEFAULT-LESS-THAN-1))
 (98 1 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (98 1 (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (86 33 (:REWRITE |(< (- x) c)|))
 (77 22 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (70 1 (:LINEAR EXPT->=-1-ONE))
 (69 1 (:LINEAR EXPT-<-1-TWO))
 (51 33
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (51 33 (:REWRITE |(< (/ x) (/ y))|))
 (41 39 (:REWRITE DEFAULT-PLUS-1))
 (40 22 (:REWRITE SIMPLIFY-SUMS-<))
 (39 39 (:REWRITE THE-FLOOR-BELOW))
 (39 39 (:REWRITE THE-FLOOR-ABOVE))
 (39 39
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (39 39
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (33 33
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (33 33
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (33 33
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (33 33
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (33 33 (:REWRITE |(< c (- x))|))
 (33 33
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (33 33
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (33 33
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (33 33 (:REWRITE |(< (- x) (- y))|))
 (31 31 (:REWRITE INTEGERP-<-CONSTANT))
 (31 31 (:REWRITE CONSTANT-<-INTEGERP))
 (22 4 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (21 3 (:REWRITE DEFAULT-DIVIDE))
 (18 6 (:REWRITE RTL::BVECP-EXACTP))
 (16 16 (:REWRITE REDUCE-INTEGERP-+))
 (16 16 (:REWRITE INTEGERP-MINUS-X))
 (16 16 (:META META-INTEGERP-CORRECT))
 (14 1 (:LINEAR EXPT-<=-1-TWO))
 (13 13
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (12 12 (:TYPE-PRESCRIPTION RTL::BVECP))
 (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
 (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
 (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
 (8 8 (:REWRITE REDUCE-RATIONALP-+))
 (8 8 (:REWRITE REDUCE-RATIONALP-*))
 (8 8 (:REWRITE RATIONALP-MINUS-X))
 (8 8 (:META META-RATIONALP-CORRECT))
 (7 7 (:REWRITE DEFAULT-EXPT-2))
 (7 7 (:REWRITE DEFAULT-EXPT-1))
 (7 7 (:REWRITE |(expt 1/c n)|))
 (7 7 (:REWRITE |(expt (- x) n)|))
 (6 6 (:REWRITE DEFAULT-MINUS))
 (5 5 (:REWRITE |(< 0 (* x y))|))
 (4 4 (:REWRITE |(< x (+ c/d y))|))
 (4 4 (:REWRITE |(< (* x y) 0)|))
 (3 3
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (3 3 (:REWRITE |(< (+ c/d x) y)|))
 (3 3 (:REWRITE |(* c (* d x))|))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:REWRITE |(< (/ x) 0)|))
 (2 2 (:REWRITE |(- (- x))|))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE |(< y (+ (- c) x))|))
 (1 1 (:LINEAR EXPT-X->=-X))
 (1 1 (:LINEAR EXPT-X->-X))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<))
 (1 1 (:LINEAR EXPT->=-1-TWO))
 (1 1 (:LINEAR EXPT->-1-TWO))
 (1 1 (:LINEAR EXPT->-1-ONE))
 (1 1 (:LINEAR EXPT-<=-1-ONE))
 (1 1 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-EXACTP-12
 (238 238
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (238 238
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (238 238
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (217
  217
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (217 217
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (217
     217
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (217 217
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (217 217
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (160 25 (:REWRITE DEFAULT-TIMES-2))
 (135 25 (:REWRITE DEFAULT-TIMES-1))
 (55 55 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (55 55 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (55 55 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (42 8 (:REWRITE SIMPLIFY-SUMS-<))
 (42 8
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (42 8 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (38 12 (:REWRITE DEFAULT-LESS-THAN-2))
 (36 19 (:REWRITE DEFAULT-PLUS-2))
 (30 19 (:REWRITE DEFAULT-PLUS-1))
 (24 12
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (22 4 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (20 12 (:REWRITE DEFAULT-LESS-THAN-1))
 (13 4 (:REWRITE DEFAULT-MINUS))
 (12 12 (:REWRITE THE-FLOOR-BELOW))
 (12 12 (:REWRITE THE-FLOOR-ABOVE))
 (12 12
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (12 12
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (12 12
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (12 12 (:REWRITE INTEGERP-<-CONSTANT))
 (12 12 (:REWRITE CONSTANT-<-INTEGERP))
 (12 12
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (12 12
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (12 12
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (12 12
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (12 12 (:REWRITE |(< c (- x))|))
 (12 12
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (12 12
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (12 12
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (12 12 (:REWRITE |(< (/ x) (/ y))|))
 (12 12 (:REWRITE |(< (- x) c)|))
 (12 12 (:REWRITE |(< (- x) (- y))|))
 (12 4 (:REWRITE RTL::BVECP-EXACTP))
 (9 9
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (8 8 (:TYPE-PRESCRIPTION RTL::BVECP))
 (8 2 (:REWRITE RATIONALP-X))
 (6 6 (:REWRITE REDUCE-INTEGERP-+))
 (6 6 (:REWRITE INTEGERP-MINUS-X))
 (6 6 (:META META-INTEGERP-CORRECT))
 (4 4
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (4 4 (:REWRITE DEFAULT-EXPT-2))
 (4 4 (:REWRITE DEFAULT-EXPT-1))
 (4 4 (:REWRITE DEFAULT-DIVIDE))
 (4 4 (:REWRITE |(expt 1/c n)|))
 (4 4 (:REWRITE |(expt (- x) n)|))
 (2 2 (:REWRITE REDUCE-RATIONALP-+))
 (2 2 (:REWRITE REDUCE-RATIONALP-*))
 (2 2 (:REWRITE RATIONALP-MINUS-X))
 (2 2 (:REWRITE |(< (+ c/d x) y)|))
 (2 2 (:REWRITE |(< (+ (- c) x) y)|))
 (2 2 (:META META-RATIONALP-CORRECT))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE |(* (- x) y)|)))
(RTL::R-EXACTP-13
 (135
  135
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (135 135
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (135
     135
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (135 135
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (72 14 (:REWRITE DEFAULT-TIMES-2))
 (70 14 (:REWRITE DEFAULT-TIMES-1))
 (51 51 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (51 51 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (51 51 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (22 4 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (18 2 (:REWRITE ACL2-NUMBERP-X))
 (16 7 (:REWRITE DEFAULT-LESS-THAN-1))
 (14 5 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (12 3 (:REWRITE RATIONALP-X))
 (9 7
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (9 7
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (9 6
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (8 8 (:REWRITE THE-FLOOR-BELOW))
 (8 8 (:REWRITE THE-FLOOR-ABOVE))
 (8 6 (:REWRITE DEFAULT-PLUS-1))
 (7 7 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (6 6 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (6 6 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (6 6 (:REWRITE INTEGERP-<-CONSTANT))
 (6 6 (:REWRITE DEFAULT-PLUS-2))
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
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (6 6
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (6 6
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (6 6 (:REWRITE |(< (/ x) (/ y))|))
 (6 6 (:REWRITE |(< (- x) c)|))
 (6 6 (:REWRITE |(< (- x) (- y))|))
 (5 5 (:REWRITE SIMPLIFY-SUMS-<))
 (4 4 (:REWRITE REDUCE-INTEGERP-+))
 (4 4 (:REWRITE INTEGERP-MINUS-X))
 (4 4 (:REWRITE DEFAULT-EXPT-2))
 (4 4 (:REWRITE DEFAULT-EXPT-1))
 (4 4 (:REWRITE |(expt 1/c n)|))
 (4 4 (:REWRITE |(expt (- x) n)|))
 (4 4 (:META META-INTEGERP-CORRECT))
 (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (3 3 (:REWRITE REDUCE-RATIONALP-+))
 (3 3 (:REWRITE REDUCE-RATIONALP-*))
 (3 3 (:REWRITE RATIONALP-MINUS-X))
 (3 3 (:REWRITE DEFAULT-MINUS))
 (3 3 (:META META-RATIONALP-CORRECT))
 (2 2 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
 (2 2 (:TYPE-PRESCRIPTION ABS))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (1 1 (:REWRITE ODD-EXPT-THM))
 (1 1
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (1 1
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (1 1 (:REWRITE DEFAULT-DIVIDE))
 (1 1
    (:REWRITE |(<= (* x (/ y)) 1) with (< y 0)|))
 (1 1
    (:REWRITE |(<= (* x (/ y)) 1) with (< 0 y)|))
 (1 1
    (:REWRITE |(< 1 (* x (/ y))) with (< y 0)|))
 (1 1 (:REWRITE |(< 0 (/ x))|))
 (1 1 (:REWRITE |(< 0 (* x y))|))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (* x y) 0)|))
 (1 1 (:LINEAR EXPT-X->=-X))
 (1 1 (:LINEAR EXPT-X->-X))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<))
 (1 1 (:LINEAR EXPT->=-1-TWO))
 (1 1 (:LINEAR EXPT->=-1-ONE))
 (1 1 (:LINEAR EXPT->-1-TWO))
 (1 1 (:LINEAR EXPT->-1-ONE))
 (1 1 (:LINEAR EXPT-<=-1-ONE))
 (1 1 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-EXACTP-14)
(RTL::R-EXACTP-15
 (67
  67
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (67 67
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (67 67
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (67 67
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (67 67
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (64 64 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (64 64 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (64 64 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (64 64 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (15 6 (:REWRITE DEFAULT-LESS-THAN-1))
 (15 2 (:REWRITE SIMPLIFY-SUMS-<))
 (15 2
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (15 2 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (12 6
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (10 6 (:REWRITE DEFAULT-LESS-THAN-2))
 (6 6 (:REWRITE THE-FLOOR-BELOW))
 (6 6 (:REWRITE THE-FLOOR-ABOVE))
 (6 6
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (6 6
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (6 6 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
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
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (6 6
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (6 6
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (6 6 (:REWRITE |(< (/ x) (/ y))|))
 (6 6 (:REWRITE |(< (- x) c)|))
 (6 6 (:REWRITE |(< (- x) (- y))|))
 (6 2 (:REWRITE RTL::BVECP-EXACTP))
 (5 1 (:REWRITE DEFAULT-PLUS-2))
 (4 4 (:TYPE-PRESCRIPTION RTL::BVECP))
 (3 3 (:REWRITE DEFAULT-EXPT-2))
 (3 3 (:REWRITE DEFAULT-EXPT-1))
 (3 3 (:REWRITE |(expt 1/c n)|))
 (3 3 (:REWRITE |(expt (- x) n)|))
 (2 2 (:REWRITE REDUCE-INTEGERP-+))
 (2 2 (:REWRITE INTEGERP-MINUS-X))
 (2 2 (:META META-INTEGERP-CORRECT))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (1 1
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (1 1
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (1 1
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (1 1 (:REWRITE NORMALIZE-ADDENDS))
 (1 1 (:REWRITE DEFAULT-TIMES-2))
 (1 1 (:REWRITE DEFAULT-TIMES-1))
 (1 1 (:REWRITE DEFAULT-PLUS-1))
 (1 1 (:REWRITE DEFAULT-MINUS))
 (1 1 (:REWRITE DEFAULT-DIVIDE))
 (1 1 (:REWRITE |(< y (+ (- c) x))|))
 (1 1 (:REWRITE |(< x (+ c/d y))|))
 (1 1 (:LINEAR EXPT-X->=-X))
 (1 1 (:LINEAR EXPT-X->-X))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<))
 (1 1 (:LINEAR EXPT->=-1-TWO))
 (1 1 (:LINEAR EXPT->=-1-ONE))
 (1 1 (:LINEAR EXPT->-1-TWO))
 (1 1 (:LINEAR EXPT->-1-ONE))
 (1 1 (:LINEAR EXPT-<=-1-ONE))
 (1 1 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-EXACTP-16
 (539
  539
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (539 539
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (539
     539
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (539 539
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (539 539
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (296 53 (:REWRITE DEFAULT-PLUS-2))
 (193 53 (:REWRITE DEFAULT-PLUS-1))
 (142 27
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (140 140
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (140 140
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (140 140
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (140 140
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (140 19
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (95 28 (:REWRITE DEFAULT-LESS-THAN-2))
 (91 28 (:REWRITE DEFAULT-LESS-THAN-1))
 (81 14 (:REWRITE SIMPLIFY-SUMS-<))
 (78 25 (:REWRITE |(< (- x) c)|))
 (71 2 (:LINEAR EXPT->=-1-ONE))
 (43 25 (:REWRITE |(< (- x) (- y))|))
 (37 25
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (32 14 (:REWRITE DEFAULT-MINUS))
 (28 28 (:REWRITE THE-FLOOR-BELOW))
 (28 28 (:REWRITE THE-FLOOR-ABOVE))
 (27 27
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (27 27
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (25 25
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (25 25
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (25 25
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (25 25
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (25 25 (:REWRITE |(< c (- x))|))
 (25 25
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (25 25
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (25 25
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (25 25 (:REWRITE |(< (/ x) (/ y))|))
 (23 23 (:REWRITE INTEGERP-<-CONSTANT))
 (23 23 (:REWRITE CONSTANT-<-INTEGERP))
 (23 5 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (18 18
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (18 2 (:REWRITE ODD-EXPT-THM))
 (15 5 (:REWRITE RTL::BVECP-EXACTP))
 (12 6 (:REWRITE |(+ c (+ d x))|))
 (12 3 (:REWRITE RATIONALP-X))
 (10 10 (:TYPE-PRESCRIPTION RTL::BVECP))
 (10 10 (:REWRITE |(< (+ c/d x) y)|))
 (9 9 (:REWRITE REDUCE-INTEGERP-+))
 (9 9 (:REWRITE INTEGERP-MINUS-X))
 (9 9 (:REWRITE DEFAULT-EXPT-2))
 (9 9 (:REWRITE DEFAULT-EXPT-1))
 (9 9 (:REWRITE |(expt 1/c n)|))
 (9 9 (:REWRITE |(expt (- x) n)|))
 (9 9 (:META META-INTEGERP-CORRECT))
 (8 8 (:REWRITE |(< (+ (- c) x) y)|))
 (4 4 (:REWRITE |(< y (+ (- c) x))|))
 (4 4 (:REWRITE |(< x (+ c/d y))|))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (3 3 (:REWRITE REDUCE-RATIONALP-+))
 (3 3 (:REWRITE REDUCE-RATIONALP-*))
 (3 3 (:REWRITE RATIONALP-MINUS-X))
 (3 3 (:REWRITE |(< (* x y) 0)|))
 (3 3 (:META META-RATIONALP-CORRECT))
 (2 2
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (2 2
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (2 2 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE DEFAULT-TIMES-2))
 (2 2 (:REWRITE DEFAULT-TIMES-1))
 (2 2 (:REWRITE DEFAULT-DIVIDE))
 (2 2 (:LINEAR EXPT-X->=-X))
 (2 2 (:LINEAR EXPT-X->-X))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT->-1-ONE))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-ONE))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(- (* c x))|)))
(RTL::R-EXACTP-17
 (242 12
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (172 19
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (172 19
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (142 4 (:LINEAR EXPT->=-1-ONE))
 (114 8 (:REWRITE |(< (- x) c)|))
 (99
  99
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (99 99
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (99 99
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (99 99
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (44 4 (:REWRITE |(+ y (+ x z))|))
 (22 4 (:REWRITE DEFAULT-TIMES-2))
 (19 19
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (19 19
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (18 18 (:REWRITE DEFAULT-PLUS-2))
 (18 18 (:REWRITE DEFAULT-PLUS-1))
 (16 4 (:REWRITE |(+ c (+ d x))|))
 (12 12 (:REWRITE THE-FLOOR-BELOW))
 (12 12 (:REWRITE THE-FLOOR-ABOVE))
 (12 12
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (12 12
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (12 12 (:REWRITE DEFAULT-LESS-THAN-2))
 (12 12 (:REWRITE DEFAULT-LESS-THAN-1))
 (9 9 (:REWRITE DEFAULT-EXPT-2))
 (9 9 (:REWRITE DEFAULT-EXPT-1))
 (9 9 (:REWRITE |(expt 1/c n)|))
 (9 9 (:REWRITE |(expt (- x) n)|))
 (8 8
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (8 8
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (8 8
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (8 8
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (8 8 (:REWRITE |(< c (- x))|))
 (8 8
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (8 8
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (8 8
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (8 8
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (8 8 (:REWRITE |(< (/ x) (/ y))|))
 (8 8 (:REWRITE |(< (- x) (- y))|))
 (8 8
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (8 8
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (8 8
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (8 8
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (7 7 (:REWRITE DEFAULT-MINUS))
 (6 6
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (6 6 (:REWRITE NORMALIZE-ADDENDS))
 (5 4 (:REWRITE DEFAULT-TIMES-1))
 (4 4 (:REWRITE SIMPLIFY-SUMS-<))
 (4 4
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (4 4 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (4 4 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (4 4 (:REWRITE INTEGERP-<-CONSTANT))
 (4 4 (:REWRITE CONSTANT-<-INTEGERP))
 (4 4 (:REWRITE |(< (+ c/d x) y)|))
 (4 4 (:REWRITE |(< (* x y) 0)|))
 (4 4 (:REWRITE |(- (- x))|))
 (4 4 (:REWRITE |(+ 0 x)|))
 (4 4 (:LINEAR EXPT-X->=-X))
 (4 4 (:LINEAR EXPT-X->-X))
 (4 4 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (4 4 (:LINEAR EXPT-LINEAR-UPPER-<))
 (4 4 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (4 4 (:LINEAR EXPT-LINEAR-LOWER-<))
 (4 4 (:LINEAR EXPT->=-1-TWO))
 (4 4 (:LINEAR EXPT->-1-TWO))
 (4 4 (:LINEAR EXPT->-1-ONE))
 (4 4 (:LINEAR EXPT-<=-1-ONE))
 (4 4 (:LINEAR EXPT-<-1-ONE))
 (2 2 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (1 1 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (1 1 (:REWRITE ZP-OPEN)))
(RTL::R-EXACTP-18
 (973 172
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (973 172
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (926
  926
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (926 926
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (926
     926
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (926 926
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (926 926
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (640 97 (:REWRITE DEFAULT-PLUS-2))
 (604 604
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (604 604
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (604 604
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (604 604
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (532 44
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (509 54 (:REWRITE DEFAULT-LESS-THAN-2))
 (394 97 (:REWRITE DEFAULT-PLUS-1))
 (257 31 (:REWRITE SIMPLIFY-SUMS-<))
 (199 172
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (199 172
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (189 54 (:REWRITE DEFAULT-LESS-THAN-1))
 (167 52
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (115 33 (:REWRITE DEFAULT-MINUS))
 (103 50 (:REWRITE |(< (- x) c)|))
 (89 50 (:REWRITE |(< (- x) (- y))|))
 (84 12 (:REWRITE DEFAULT-TIMES-2))
 (74 50
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (71 2 (:LINEAR EXPT->=-1-ONE))
 (62 14 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (54 54 (:REWRITE THE-FLOOR-BELOW))
 (54 54 (:REWRITE THE-FLOOR-ABOVE))
 (52 52
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (52 52
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (50 50
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (50 50
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (50 50
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (50 50
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (50 50 (:REWRITE |(< c (- x))|))
 (50 50
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (50 50
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (50 50
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (50 50 (:REWRITE |(< (/ x) (/ y))|))
 (48 48 (:REWRITE INTEGERP-<-CONSTANT))
 (48 48 (:REWRITE CONSTANT-<-INTEGERP))
 (36 12 (:REWRITE RTL::BVECP-EXACTP))
 (36 9 (:REWRITE RATIONALP-X))
 (26 26
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (24 24 (:TYPE-PRESCRIPTION RTL::BVECP))
 (17 17 (:REWRITE REDUCE-INTEGERP-+))
 (17 17 (:REWRITE INTEGERP-MINUS-X))
 (17 17 (:META META-INTEGERP-CORRECT))
 (15 15 (:REWRITE |(< (+ c/d x) y)|))
 (15 9 (:REWRITE |(+ c (+ d x))|))
 (13 13 (:REWRITE |(< (+ (- c) x) y)|))
 (12 12 (:REWRITE DEFAULT-TIMES-1))
 (11 11 (:REWRITE DEFAULT-EXPT-2))
 (11 11 (:REWRITE DEFAULT-EXPT-1))
 (11 11 (:REWRITE |(expt 1/c n)|))
 (11 11 (:REWRITE |(expt (- x) n)|))
 (9 9 (:REWRITE REDUCE-RATIONALP-+))
 (9 9 (:REWRITE REDUCE-RATIONALP-*))
 (9 9 (:REWRITE RATIONALP-MINUS-X))
 (9 9 (:REWRITE |(< y (+ (- c) x))|))
 (9 9 (:REWRITE |(< x (+ c/d y))|))
 (9 9 (:META META-RATIONALP-CORRECT))
 (6 6 (:REWRITE |(< (* x y) 0)|))
 (4 4
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (4 4 (:REWRITE DEFAULT-DIVIDE))
 (4 4 (:REWRITE |(< (/ x) 0)|))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (3 3 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE |(* (- x) y)|))
 (2 2 (:LINEAR EXPT-X->=-X))
 (2 2 (:LINEAR EXPT-X->-X))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT->-1-ONE))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-EXACTP-19
 (3336 5 (:REWRITE RTL::R-EXACTP-6))
 (2749 38
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (1807 27 (:REWRITE |(< (- x) c)|))
 (1087 11 (:REWRITE |(< 0 (/ x))|))
 (400
  400
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (400 400
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (400
     400
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (400 400
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (400 400
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (394 43 (:REWRITE DEFAULT-PLUS-2))
 (175 31 (:REWRITE DEFAULT-MINUS))
 (165 38 (:REWRITE DEFAULT-LESS-THAN-1))
 (147 38 (:REWRITE DEFAULT-LESS-THAN-2))
 (145 20 (:LINEAR EXPT-X->=-X))
 (145 20 (:LINEAR EXPT-X->-X))
 (130 20 (:LINEAR EXPT->-1-ONE))
 (117 43 (:REWRITE DEFAULT-PLUS-1))
 (110 5 (:REWRITE |(+ c (+ d x))|))
 (87 22
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (86 32 (:REWRITE |(< (- x) (- y))|))
 (85 20 (:LINEAR EXPT->=-1-ONE))
 (59 59 (:REWRITE DEFAULT-EXPT-2))
 (59 59 (:REWRITE DEFAULT-EXPT-1))
 (59 59 (:REWRITE |(expt 1/c n)|))
 (59 59 (:REWRITE |(expt (- x) n)|))
 (55 10 (:REWRITE |(- (- x))|))
 (50 5 (:REWRITE DEFAULT-DIVIDE))
 (40 40
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (40 40
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (40 40
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (40 40
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (40 4 (:REWRITE DEFAULT-TIMES-2))
 (38 38 (:REWRITE THE-FLOOR-BELOW))
 (38 38 (:REWRITE THE-FLOOR-ABOVE))
 (38 38
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (38 38
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (36 27 (:REWRITE |(< c (- x))|))
 (35 5 (:REWRITE |(/ (expt x n))|))
 (32 32
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (32 32
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (32 32
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (32 32
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (32 32
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (32 32
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (32 32
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (32 32
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (32 32 (:REWRITE |(< (/ x) (/ y))|))
 (22 22
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (22 22 (:REWRITE INTEGERP-<-CONSTANT))
 (22 22 (:REWRITE CONSTANT-<-INTEGERP))
 (22 22 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (22 22 (:LINEAR EXPT-LINEAR-UPPER-<))
 (22 22 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (22 22 (:LINEAR EXPT-LINEAR-LOWER-<))
 (21 3 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (20 20 (:REWRITE SIMPLIFY-SUMS-<))
 (20 20 (:LINEAR EXPT->=-1-TWO))
 (20 20 (:LINEAR EXPT->-1-TWO))
 (20 20 (:LINEAR EXPT-<=-1-ONE))
 (20 20 (:LINEAR EXPT-<-1-ONE))
 (18 18
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (12 12 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (11 11 (:REWRITE |(< 0 (* x y))|))
 (10 1
     (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (10 1 (:REWRITE |(* c (expt d n))|))
 (7 7 (:REWRITE |(< (+ c/d x) y)|))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (5 5 (:REWRITE ODD-EXPT-THM))
 (5 5 (:REWRITE |(< (/ x) 0)|))
 (5 5 (:REWRITE |(< (* x y) 0)|))
 (5 4 (:REWRITE DEFAULT-TIMES-1))
 (5 3
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (5 3
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (3 3 (:REWRITE ZP-OPEN))
 (3 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (3 3
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (3 3
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (3 3
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (3 3 (:REWRITE |(equal c (/ x))|))
 (3 3 (:REWRITE |(equal c (- x))|))
 (3 3 (:REWRITE |(equal (/ x) c)|))
 (3 3 (:REWRITE |(equal (/ x) (/ y))|))
 (3 3 (:REWRITE |(equal (- x) c)|))
 (3 3 (:REWRITE |(equal (- x) (- y))|))
 (2 2 (:REWRITE |(< y (+ (- c) x))|))
 (2 2 (:REWRITE |(< x (+ c/d y))|))
 (2 2 (:REWRITE |(< (+ (- c) x) y)|)))
(RTL::R-EXACTP-20
 (1338 2 (:REWRITE RTL::R-EXACTP-6))
 (1100 12
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (720 8 (:REWRITE |(< (- x) c)|))
 (438 4 (:REWRITE |(< 0 (/ x))|))
 (140 8 (:LINEAR EXPT-<=-1-TWO))
 (140 8 (:LINEAR EXPT-<-1-TWO))
 (121 22 (:REWRITE DEFAULT-PLUS-2))
 (112
  112
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (112 112
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (112
     112
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (112 112
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (65 10 (:REWRITE DEFAULT-TIMES-1))
 (64 10 (:REWRITE DEFAULT-TIMES-2))
 (58 8 (:LINEAR EXPT-X->=-X))
 (58 8 (:LINEAR EXPT-X->-X))
 (52 8 (:LINEAR EXPT->-1-ONE))
 (48 12 (:REWRITE DEFAULT-LESS-THAN-2))
 (48 12 (:REWRITE DEFAULT-LESS-THAN-1))
 (45 9 (:REWRITE DEFAULT-MINUS))
 (34 8 (:LINEAR EXPT->=-1-ONE))
 (32 22 (:REWRITE DEFAULT-PLUS-1))
 (28 10 (:REWRITE |(< (- x) (- y))|))
 (24 6
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (24 6 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (22 4 (:REWRITE |(- (- x))|))
 (21 21 (:REWRITE DEFAULT-EXPT-2))
 (21 21 (:REWRITE DEFAULT-EXPT-1))
 (21 21 (:REWRITE |(expt 1/c n)|))
 (21 21 (:REWRITE |(expt (- x) n)|))
 (20 2 (:REWRITE DEFAULT-DIVIDE))
 (16 16
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (16 16
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (16 16
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (16 16
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (14 2 (:REWRITE |(/ (expt x n))|))
 (12 12 (:REWRITE THE-FLOOR-BELOW))
 (12 12 (:REWRITE THE-FLOOR-ABOVE))
 (12 12
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (12 12
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (11 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (10 10
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (10 10
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (10 10
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (10 10
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (10 10
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (10 10
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (10 10
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (10 10
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (10 10 (:REWRITE |(< (/ x) (/ y))|))
 (8 8
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (8 8 (:REWRITE |(< c (- x))|))
 (8 8 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (8 8 (:LINEAR EXPT-LINEAR-UPPER-<))
 (8 8 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (8 8 (:LINEAR EXPT-LINEAR-LOWER-<))
 (8 8 (:LINEAR EXPT->=-1-TWO))
 (8 8 (:LINEAR EXPT->-1-TWO))
 (8 8 (:LINEAR EXPT-<=-1-ONE))
 (8 8 (:LINEAR EXPT-<-1-ONE))
 (6 6 (:REWRITE SIMPLIFY-SUMS-<))
 (6 6 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (6 6 (:REWRITE INTEGERP-<-CONSTANT))
 (6 6 (:REWRITE CONSTANT-<-INTEGERP))
 (4 4 (:REWRITE |(< 0 (* x y))|))
 (3 1 (:REWRITE RTL::BVECP-EXACTP))
 (2 2 (:TYPE-PRESCRIPTION RTL::BVECP))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (2 2 (:REWRITE ODD-EXPT-THM))
 (2 2 (:REWRITE |(< (/ x) 0)|))
 (2 2 (:REWRITE |(< (+ c/d x) y)|))
 (2 2 (:REWRITE |(< (* x y) 0)|))
 (2 1
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (2 1
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
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
 (1 1 (:REWRITE |(equal (- x) (- y))|)))
(RTL::R-EXACTP-21
 (3987 6 (:REWRITE RTL::R-EXACTP-6))
 (3477 125
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (2273 111 (:REWRITE |(< (- x) c)|))
 (1563
  1563
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1563
      1563
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1563
     1563
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1563 1563
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1563 1563
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (1293 18 (:REWRITE |(< 0 (/ x))|))
 (1270 200 (:REWRITE DEFAULT-PLUS-2))
 (1109 1109
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (1109 1109
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (1109 1109
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (1109 1109
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (708 200 (:REWRITE DEFAULT-PLUS-1))
 (499 99
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (485 127 (:REWRITE DEFAULT-LESS-THAN-2))
 (443 127 (:REWRITE DEFAULT-LESS-THAN-1))
 (369 85 (:REWRITE DEFAULT-MINUS))
 (223 117 (:REWRITE |(< (- x) (- y))|))
 (206 78 (:REWRITE SIMPLIFY-SUMS-<))
 (175 25 (:LINEAR EXPT-X->=-X))
 (175 25 (:LINEAR EXPT-X->-X))
 (172 25 (:LINEAR EXPT->=-1-ONE))
 (168 117
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (158 14 (:REWRITE ODD-EXPT-THM))
 (157 25 (:LINEAR EXPT->-1-ONE))
 (150 18 (:REWRITE |(+ c (+ d x))|))
 (138 111 (:REWRITE |(< c (- x))|))
 (130 24 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (127 127 (:REWRITE THE-FLOOR-BELOW))
 (127 127 (:REWRITE THE-FLOOR-ABOVE))
 (125 125
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (125 125
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (117 117
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (117 117
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (117 117
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (117 117
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (117 117
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (117 117
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (117 117
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (117 117 (:REWRITE |(< (/ x) (/ y))|))
 (103 103 (:REWRITE INTEGERP-<-CONSTANT))
 (103 103 (:REWRITE CONSTANT-<-INTEGERP))
 (90 90 (:REWRITE DEFAULT-EXPT-2))
 (90 90 (:REWRITE DEFAULT-EXPT-1))
 (90 90 (:REWRITE |(expt 1/c n)|))
 (90 90 (:REWRITE |(expt (- x) n)|))
 (81 27 (:REWRITE RTL::BVECP-EXACTP))
 (66 12 (:REWRITE DEFAULT-DIVIDE))
 (60 15 (:REWRITE RATIONALP-X))
 (58 58
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (56 40 (:REWRITE INTEGERP-MINUS-X))
 (54 54 (:TYPE-PRESCRIPTION RTL::BVECP))
 (50 50
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (50 50
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (50 50
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (50 50
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (42 6 (:REWRITE |(/ (expt x n))|))
 (40 40 (:REWRITE REDUCE-INTEGERP-+))
 (40 40 (:META META-INTEGERP-CORRECT))
 (27 27 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (27 27 (:LINEAR EXPT-LINEAR-UPPER-<))
 (27 27 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (27 27 (:LINEAR EXPT-LINEAR-LOWER-<))
 (26 26 (:REWRITE |(< (+ c/d x) y)|))
 (25 25 (:LINEAR EXPT->=-1-TWO))
 (25 25 (:LINEAR EXPT->-1-TWO))
 (25 25 (:LINEAR EXPT-<=-1-ONE))
 (25 25 (:LINEAR EXPT-<-1-ONE))
 (18 18 (:REWRITE |(< 0 (* x y))|))
 (18 18 (:REWRITE |(< (+ (- c) x) y)|))
 (17 17 (:REWRITE |(< y (+ (- c) x))|))
 (17 17 (:REWRITE |(< x (+ c/d y))|))
 (15 15 (:REWRITE REDUCE-RATIONALP-+))
 (15 15 (:REWRITE REDUCE-RATIONALP-*))
 (15 15 (:REWRITE RATIONALP-MINUS-X))
 (15 15 (:META META-RATIONALP-CORRECT))
 (14 14 (:REWRITE |(< (* x y) 0)|))
 (12 12 (:REWRITE |(< (/ x) 0)|))
 (9 9
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (9 9
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (8 8 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (6 6
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (6 6
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (6 6 (:REWRITE DEFAULT-TIMES-2))
 (6 6 (:REWRITE DEFAULT-TIMES-1))
 (6 3
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (6 3
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (5 5 (:REWRITE ZP-OPEN))
 (4 4 (:REWRITE |(- (* c x))|))
 (3 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (3 3
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (3 3
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (3 3
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (3 3 (:REWRITE |(equal c (/ x))|))
 (3 3 (:REWRITE |(equal c (- x))|))
 (3 3 (:REWRITE |(equal (/ x) c)|))
 (3 3 (:REWRITE |(equal (/ x) (/ y))|))
 (3 3 (:REWRITE |(equal (- x) c)|))
 (3 3 (:REWRITE |(equal (- x) (- y))|)))
(RTL::R-EXACTP-22
 (598 598
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (598 598
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (598 598
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (384 5 (:REWRITE RTL::R-EXACTP-6))
 (349
  349
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (349 349
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (349
     349
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (349 349
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (349 349
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (198 50 (:REWRITE DEFAULT-PLUS-2))
 (196 50
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (161 67 (:REWRITE DEFAULT-LESS-THAN-1))
 (160 67 (:REWRITE DEFAULT-LESS-THAN-2))
 (119 50 (:REWRITE DEFAULT-PLUS-1))
 (107 43 (:REWRITE SIMPLIFY-SUMS-<))
 (99 63
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (78 3
     (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (76 4 (:REWRITE ODD-EXPT-THM))
 (71 63 (:REWRITE |(< (- x) (- y))|))
 (67 67 (:REWRITE THE-FLOOR-BELOW))
 (67 67 (:REWRITE THE-FLOOR-ABOVE))
 (66 66
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (66 66
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (66 66
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (63 63 (:REWRITE INTEGERP-<-CONSTANT))
 (63 63 (:REWRITE CONSTANT-<-INTEGERP))
 (63 63
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (63 63
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (63 63
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (63 63
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (63 63 (:REWRITE |(< c (- x))|))
 (63 63
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (63 63
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (63 63
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (63 63 (:REWRITE |(< (/ x) (/ y))|))
 (63 63 (:REWRITE |(< (- x) c)|))
 (41 1 (:LINEAR EXPT->=-1-ONE))
 (40 1 (:LINEAR EXPT->-1-ONE))
 (40 1 (:LINEAR EXPT-<=-1-TWO))
 (39 1 (:LINEAR EXPT-<-1-TWO))
 (36 1 (:LINEAR EXPT-X->=-X))
 (36 1 (:LINEAR EXPT-X->-X))
 (30 22 (:REWRITE INTEGERP-MINUS-X))
 (28 12 (:REWRITE DEFAULT-MINUS))
 (27 9 (:REWRITE RTL::BVECP-EXACTP))
 (24 6 (:REWRITE RATIONALP-X))
 (22 22 (:REWRITE REDUCE-INTEGERP-+))
 (22 22 (:META META-INTEGERP-CORRECT))
 (18 18 (:TYPE-PRESCRIPTION RTL::BVECP))
 (15 7 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (12 12
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (9 9 (:REWRITE |(< (+ c/d x) y)|))
 (9 9 (:REWRITE |(< (+ (- c) x) y)|))
 (8 8 (:REWRITE |(< y (+ (- c) x))|))
 (8 8 (:REWRITE |(< x (+ c/d y))|))
 (7 7 (:REWRITE |(< (/ x) 0)|))
 (7 7 (:REWRITE |(< (* x y) 0)|))
 (6 6 (:REWRITE REDUCE-RATIONALP-+))
 (6 6 (:REWRITE REDUCE-RATIONALP-*))
 (6 6 (:REWRITE RATIONALP-MINUS-X))
 (6 6
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (6 6
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (6 6 (:REWRITE DEFAULT-TIMES-2))
 (6 6 (:REWRITE DEFAULT-TIMES-1))
 (6 6 (:REWRITE DEFAULT-DIVIDE))
 (6 6 (:META META-RATIONALP-CORRECT))
 (6 3
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (6 3
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (5 5 (:REWRITE |(+ c (+ d x))|))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (3 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (3 3
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (3 3
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (3 3
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (3 3 (:REWRITE DEFAULT-EXPT-2))
 (3 3 (:REWRITE DEFAULT-EXPT-1))
 (3 3 (:REWRITE |(expt 1/c n)|))
 (3 3 (:REWRITE |(expt (- x) n)|))
 (3 3 (:REWRITE |(equal c (/ x))|))
 (3 3 (:REWRITE |(equal c (- x))|))
 (3 3 (:REWRITE |(equal (/ x) c)|))
 (3 3 (:REWRITE |(equal (/ x) (/ y))|))
 (3 3 (:REWRITE |(equal (- x) c)|))
 (3 3 (:REWRITE |(equal (- x) (- y))|))
 (3 3
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (3 3
    (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (3 3
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:REWRITE |(< 0 (* x y))|))
 (2 2 (:REWRITE |(- (* c x))|))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<))
 (1 1 (:LINEAR EXPT->=-1-TWO))
 (1 1 (:LINEAR EXPT->-1-TWO))
 (1 1 (:LINEAR EXPT-<=-1-ONE))
 (1 1 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-EXACTP-23
 (211 31 (:REWRITE DEFAULT-PLUS-2))
 (181
  181
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (181 181
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (181
     181
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (181 181
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (181 181
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (142 31 (:REWRITE DEFAULT-PLUS-1))
 (88 16 (:REWRITE DEFAULT-MINUS))
 (52 7
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (43 7 (:REWRITE DEFAULT-LESS-THAN-1))
 (34 7 (:REWRITE DEFAULT-LESS-THAN-2))
 (30 3 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (25 7 (:REWRITE |(< (- x) c)|))
 (25 7 (:REWRITE |(< (- x) (- y))|))
 (18 18
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (16 7 (:REWRITE |(< c (- x))|))
 (11 11 (:REWRITE DEFAULT-EXPT-2))
 (11 11 (:REWRITE DEFAULT-EXPT-1))
 (11 11 (:REWRITE |(expt 1/c n)|))
 (11 11 (:REWRITE |(expt (- x) n)|))
 (7 7 (:REWRITE THE-FLOOR-BELOW))
 (7 7 (:REWRITE THE-FLOOR-ABOVE))
 (7 7 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (7 7 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (7 7
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (7 7
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (7 7 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (7 7 (:REWRITE INTEGERP-<-CONSTANT))
 (7 7 (:REWRITE CONSTANT-<-INTEGERP))
 (7 7
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (7 7
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (7 7
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (7 7
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (7 7
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (7 7
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (7 7
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (7 7
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (7 7 (:REWRITE |(< (/ x) (/ y))|))
 (4 4 (:REWRITE SIMPLIFY-SUMS-<))
 (3 3 (:REWRITE |(< y (+ (- c) x))|))
 (3 3 (:REWRITE |(< x (+ c/d y))|))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:REWRITE EXPT-X->=-X))
 (2 2 (:REWRITE |(< (+ c/d x) y)|))
 (2 2 (:REWRITE |(< (+ (- c) x) y)|))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE |(< 0 (/ x))|))
 (1 1 (:REWRITE |(< 0 (* x y))|)))
(RTL::R-EXACTP-24
 (74 11 (:REWRITE DEFAULT-TIMES-2))
 (67 11 (:REWRITE DEFAULT-TIMES-1))
 (44 17 (:REWRITE DEFAULT-PLUS-2))
 (43
  43
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (43 43
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (43 43
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (43 43
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (43 43
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (27 17 (:REWRITE DEFAULT-PLUS-1))
 (22 4 (:REWRITE DEFAULT-MINUS))
 (12 3 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (7 7
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (6 6 (:REWRITE DEFAULT-EXPT-2))
 (6 6 (:REWRITE DEFAULT-EXPT-1))
 (6 6 (:REWRITE |(expt 1/c n)|))
 (6 6 (:REWRITE |(expt (- x) n)|))
 (3 1 (:REWRITE RTL::BVECP-EXACTP))
 (2 2 (:TYPE-PRESCRIPTION RTL::BVECP))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (1 1 (:REWRITE ZP-OPEN)))
(RTL::R-EXACTP-25
 (351
  351
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (351 351
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (351
     351
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (351 351
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (351 351
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (351 351
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (312 51 (:REWRITE DEFAULT-PLUS-2))
 (236 51 (:REWRITE DEFAULT-PLUS-1))
 (140 25
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (102 21 (:REWRITE DEFAULT-MINUS))
 (92 20
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (76 23 (:REWRITE |(< (- x) c)|))
 (70 25 (:REWRITE DEFAULT-LESS-THAN-2))
 (70 1 (:LINEAR EXPT->=-1-ONE))
 (69 1 (:LINEAR EXPT-<-1-TWO))
 (61 25 (:REWRITE DEFAULT-LESS-THAN-1))
 (50 23 (:REWRITE |(< (- x) (- y))|))
 (50 5 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (38 23
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (32 23 (:REWRITE |(< c (- x))|))
 (25 25 (:REWRITE THE-FLOOR-BELOW))
 (25 25 (:REWRITE THE-FLOOR-ABOVE))
 (25 25
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (25 25
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (24 24
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (23 23
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (23 23
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (23 23
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (23 23
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (23 23
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (23 23
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (23 23
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (23 23 (:REWRITE |(< (/ x) (/ y))|))
 (21 21 (:REWRITE INTEGERP-<-CONSTANT))
 (21 21 (:REWRITE CONSTANT-<-INTEGERP))
 (21 7 (:REWRITE RTL::BVECP-EXACTP))
 (19 19 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (16 16 (:REWRITE SIMPLIFY-SUMS-<))
 (16 4 (:REWRITE RATIONALP-X))
 (14 14 (:TYPE-PRESCRIPTION RTL::BVECP))
 (12 12 (:REWRITE DEFAULT-EXPT-2))
 (12 12 (:REWRITE DEFAULT-EXPT-1))
 (12 12 (:REWRITE |(expt 1/c n)|))
 (12 12 (:REWRITE |(expt (- x) n)|))
 (9 9 (:REWRITE REDUCE-INTEGERP-+))
 (9 9 (:REWRITE INTEGERP-MINUS-X))
 (9 9 (:META META-INTEGERP-CORRECT))
 (8 2 (:REWRITE |(+ c (+ d x))|))
 (5 5 (:REWRITE |(< y (+ (- c) x))|))
 (5 5 (:REWRITE |(< x (+ c/d y))|))
 (5 5 (:REWRITE |(< (+ c/d x) y)|))
 (4 4 (:REWRITE REDUCE-RATIONALP-+))
 (4 4 (:REWRITE REDUCE-RATIONALP-*))
 (4 4 (:REWRITE RATIONALP-MINUS-X))
 (4 4 (:META META-RATIONALP-CORRECT))
 (3 3 (:REWRITE |(< (+ (- c) x) y)|))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:REWRITE |(< 0 (* x y))|))
 (2 2 (:REWRITE |(< (* x y) 0)|))
 (2 2 (:REWRITE |(- (- x))|))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (1 1 (:REWRITE EXPT-X->=-X))
 (1 1 (:LINEAR EXPT-X->=-X))
 (1 1 (:LINEAR EXPT-X->-X))
 (1 1 (:LINEAR EXPT->=-1-TWO))
 (1 1 (:LINEAR EXPT->-1-TWO))
 (1 1 (:LINEAR EXPT->-1-ONE))
 (1 1 (:LINEAR EXPT-<=-1-ONE))
 (1 1 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-EXACTP-26
 (682 3
      (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (666 32
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (540 54 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (391 3
      (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (391 3 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (361
  361
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (361 361
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (361
     361
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (361 361
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (361 361
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (361 361
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (360 43 (:REWRITE DEFAULT-PLUS-2))
 (325 26 (:REWRITE |(< (- x) c)|))
 (239 43 (:REWRITE DEFAULT-PLUS-1))
 (236 1
      (:REWRITE |(<= x (/ y)) with (< 0 y)|))
 (185 1 (:REWRITE |(< (/ x) y) with (< 0 x)|))
 (170 44 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (170 2 (:REWRITE INTEGERP-/))
 (148 18
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (147 1 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (138 32 (:REWRITE DEFAULT-LESS-THAN-2))
 (134 2 (:REWRITE |(* x (+ y z))|))
 (128 32 (:REWRITE DEFAULT-LESS-THAN-1))
 (116 1 (:REWRITE |(integerp (- x))|))
 (97 4 (:REWRITE |(* y x)|))
 (97 1 (:REWRITE |(integerp (expt x n))|))
 (88 26 (:REWRITE |(< (- x) (- y))|))
 (86 14 (:REWRITE DEFAULT-TIMES-2))
 (71 9 (:REWRITE DEFAULT-MINUS))
 (56 2 (:REWRITE |(* x (- y))|))
 (54 54 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (54 54 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (54 54 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (48 14 (:REWRITE SIMPLIFY-SUMS-<))
 (48 4 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (48 3 (:REWRITE |(+ c (+ d x))|))
 (44 44 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (44 44 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (44 44 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (41 6 (:REWRITE |(+ 0 x)|))
 (38 26
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (38 2
     (:REWRITE |(< 1 (* x (/ y))) with (< y 0)|))
 (38 2
     (:REWRITE |(< 1 (* x (/ y))) with (< 0 y)|))
 (32 32 (:REWRITE THE-FLOOR-BELOW))
 (32 32 (:REWRITE THE-FLOOR-ABOVE))
 (32 32
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (32 32
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (32 14 (:REWRITE DEFAULT-TIMES-1))
 (26 26
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (26 26
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (26 26
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (26 26
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (26 26 (:REWRITE |(< c (- x))|))
 (26 26
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (26 26
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (26 26
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (23 23 (:REWRITE INTEGERP-<-CONSTANT))
 (23 23 (:REWRITE CONSTANT-<-INTEGERP))
 (22 4 (:REWRITE DEFAULT-DIVIDE))
 (21 3 (:REWRITE |(- (- x))|))
 (19 1
     (:REWRITE |(<= (* x (/ y)) 1) with (< y 0)|))
 (19 1
     (:REWRITE |(<= (* x (/ y)) 1) with (< 0 y)|))
 (13 13
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (12 12 (:REWRITE DEFAULT-EXPT-2))
 (12 12 (:REWRITE DEFAULT-EXPT-1))
 (12 12 (:REWRITE |(expt 1/c n)|))
 (12 12 (:REWRITE |(expt (- x) n)|))
 (12 12
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (12 12
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (12 12
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (12 12
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (12 4 (:REWRITE RTL::BVECP-EXACTP))
 (10 10 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (10 10 (:LINEAR EXPT-LINEAR-UPPER-<))
 (10 10 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (10 10 (:LINEAR EXPT-LINEAR-LOWER-<))
 (10 1
     (:REWRITE |(<= x (/ y)) with (< y 0)|))
 (10 1 (:REWRITE |(< (/ x) y) with (< x 0)|))
 (9 9 (:REWRITE REDUCE-INTEGERP-+))
 (9 9 (:REWRITE INTEGERP-MINUS-X))
 (9 9 (:META META-INTEGERP-CORRECT))
 (8 8 (:TYPE-PRESCRIPTION RTL::BVECP))
 (8 8
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (8 2 (:REWRITE RATIONALP-X))
 (7 7 (:REWRITE |(< (+ c/d x) y)|))
 (6 6 (:LINEAR EXPT-X->=-X))
 (6 6 (:LINEAR EXPT-X->-X))
 (6 6 (:LINEAR EXPT->=-1-TWO))
 (6 6 (:LINEAR EXPT->=-1-ONE))
 (6 6 (:LINEAR EXPT->-1-TWO))
 (6 6 (:LINEAR EXPT->-1-ONE))
 (6 6 (:LINEAR EXPT-<=-1-ONE))
 (6 6 (:LINEAR EXPT-<-1-TWO))
 (6 6 (:LINEAR EXPT-<-1-ONE))
 (4 4 (:REWRITE |(< y (+ (- c) x))|))
 (4 4 (:REWRITE |(< x (+ c/d y))|))
 (4 4 (:REWRITE |(< (+ (- c) x) y)|))
 (3 3 (:REWRITE |(< (* x y) 0)|))
 (2 2 (:REWRITE REDUCE-RATIONALP-+))
 (2 2 (:REWRITE REDUCE-RATIONALP-*))
 (2 2 (:REWRITE RATIONALP-MINUS-X))
 (2 2 (:REWRITE ODD-EXPT-THM))
 (2 2
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (2 2 (:REWRITE EXPT-X->-X))
 (2 2 (:REWRITE |(< 0 (* x y))|))
 (2 2 (:REWRITE |(- (* c x))|))
 (2 2 (:META META-RATIONALP-CORRECT))
 (1 1 (:REWRITE ZP-OPEN)))
(RTL::R-EXACTP-27
     (75 75 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (75 75 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (75 75 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (11 5
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (10 6 (:REWRITE DEFAULT-LESS-THAN-1))
     (9 5 (:REWRITE DEFAULT-TIMES-2))
     (8 2 (:REWRITE RATIONALP-X))
     (6 6 (:REWRITE THE-FLOOR-BELOW))
     (6 6 (:REWRITE THE-FLOOR-ABOVE))
     (6 6
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (6 6
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (6 6 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (6 6 (:REWRITE DEFAULT-LESS-THAN-2))
     (6 2 (:REWRITE RTL::BVECP-EXACTP))
     (5 5 (:REWRITE SIMPLIFY-SUMS-<))
     (5 5
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (5 5 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (5 5 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (5 5 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (5 5 (:REWRITE INTEGERP-<-CONSTANT))
     (5 5 (:REWRITE DEFAULT-TIMES-1))
     (5 5 (:REWRITE CONSTANT-<-INTEGERP))
     (5 5
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (5 5
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (5 5
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (5 5
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (5 5 (:REWRITE |(< c (- x))|))
     (5 5
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (5 5
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (5 5
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (5 5 (:REWRITE |(< (/ x) (/ y))|))
     (5 5 (:REWRITE |(< (- x) c)|))
     (5 5 (:REWRITE |(< (- x) (- y))|))
     (5 1
        (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (4 4 (:TYPE-PRESCRIPTION RTL::BVECP))
     (4 4 (:REWRITE REDUCE-INTEGERP-+))
     (4 4 (:REWRITE INTEGERP-MINUS-X))
     (4 4 (:META META-INTEGERP-CORRECT))
     (2 2 (:REWRITE REDUCE-RATIONALP-+))
     (2 2 (:REWRITE REDUCE-RATIONALP-*))
     (2 2 (:REWRITE RATIONALP-MINUS-X))
     (2 2
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (2 2 (:REWRITE DEFAULT-DIVIDE))
     (2 2 (:META META-RATIONALP-CORRECT))
     (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-4E))
     (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
     (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
     (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
     (1 1 (:REWRITE ZP-OPEN))
     (1 1
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS)))
(RTL::R-EXACTP-28)
(RTL::R-EXACTP-29
 (1872 16 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (1826 2
       (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (1806 2 (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (1184 32
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (1040 104
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4D))
 (841 66 (:REWRITE DEFAULT-PLUS-2))
 (786 2
      (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (786 2 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (688 8 (:REWRITE |(+ y (+ x z))|))
 (681
  681
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (681 681
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (681
     681
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (681 681
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (681 681
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (668 8 (:REWRITE |(* x (+ y z))|))
 (588 28 (:REWRITE |(< (- x) c)|))
 (554 66 (:REWRITE DEFAULT-PLUS-1))
 (448 6 (:REWRITE |(* y (* x z))|))
 (440 57 (:REWRITE DEFAULT-TIMES-2))
 (400 2 (:REWRITE |(* (* x y) z)|))
 (390 390
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (390 390
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (332 16 (:LINEAR EXPT-<=-1-TWO))
 (304 124
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (260 8 (:REWRITE |(* x (- y))|))
 (244 32 (:REWRITE DEFAULT-LESS-THAN-1))
 (242 16
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (240 22 (:REWRITE DEFAULT-MINUS))
 (168 6 (:REWRITE |(* y x)|))
 (154 32 (:REWRITE DEFAULT-LESS-THAN-2))
 (138 12 (:REWRITE SIMPLIFY-SUMS-<))
 (137 57 (:REWRITE DEFAULT-TIMES-1))
 (132 28 (:REWRITE |(< (- x) (- y))|))
 (124 124
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (124 124
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (124 124
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (104 104
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3D))
 (104 104
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2D))
 (104 104
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1D))
 (99 5 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (88 4 (:REWRITE |(+ c (+ d x))|))
 (80 62 (:TYPE-PRESCRIPTION NOT-INTEGERP-4E))
 (79 79
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4A-EXPT))
 (79 79
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (79 79
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (79 79
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (62 62 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
 (62 62 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
 (62 62 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
 (40 28
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (40 4 (:REWRITE |(- (- x))|))
 (33 33
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (32 32 (:REWRITE THE-FLOOR-BELOW))
 (32 32 (:REWRITE THE-FLOOR-ABOVE))
 (32 32
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (32 32
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (32 5 (:REWRITE DEFAULT-DIVIDE))
 (28 28
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (28 28
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (28 28
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (28 28
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (28 28 (:REWRITE |(< c (- x))|))
 (28 28
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (28 28
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (28 28
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (28 28 (:REWRITE |(< (/ x) (/ y))|))
 (24 24
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (24 24 (:REWRITE INTEGERP-<-CONSTANT))
 (24 24 (:REWRITE CONSTANT-<-INTEGERP))
 (24 24
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (24 24
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (24 24
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (24 24
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (21 21 (:REWRITE DEFAULT-EXPT-2))
 (21 21 (:REWRITE DEFAULT-EXPT-1))
 (21 21 (:REWRITE |(expt 1/c n)|))
 (21 21 (:REWRITE |(expt (- x) n)|))
 (16 16 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (16 16 (:LINEAR EXPT-LINEAR-UPPER-<))
 (16 16 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (16 16 (:LINEAR EXPT-LINEAR-LOWER-<))
 (12 12 (:LINEAR EXPT-X->=-X))
 (12 12 (:LINEAR EXPT-X->-X))
 (12 12 (:LINEAR EXPT->=-1-TWO))
 (12 12 (:LINEAR EXPT->=-1-ONE))
 (12 12 (:LINEAR EXPT->-1-TWO))
 (12 12 (:LINEAR EXPT->-1-ONE))
 (12 12 (:LINEAR EXPT-<=-1-ONE))
 (12 12 (:LINEAR EXPT-<-1-TWO))
 (12 12 (:LINEAR EXPT-<-1-ONE))
 (12 4 (:REWRITE RTL::BVECP-EXACTP))
 (9 9 (:REWRITE |(- (* c x))|))
 (8 8 (:TYPE-PRESCRIPTION RTL::BVECP))
 (8 8 (:REWRITE |(< (+ c/d x) y)|))
 (8 8 (:REWRITE |(* c (* d x))|))
 (8 2 (:REWRITE RATIONALP-X))
 (6 6 (:REWRITE REDUCE-INTEGERP-+))
 (6 6 (:REWRITE INTEGERP-MINUS-X))
 (6 6 (:META META-INTEGERP-CORRECT))
 (5 5
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (4 4 (:REWRITE ODD-EXPT-THM))
 (4 4 (:REWRITE EXPT-X->-X))
 (4 4 (:REWRITE |(< y (+ (- c) x))|))
 (4 4 (:REWRITE |(< x (+ c/d y))|))
 (4 4 (:REWRITE |(< (+ (- c) x) y)|))
 (4 4 (:REWRITE |(< (* x y) 0)|))
 (2 2 (:REWRITE REDUCE-RATIONALP-+))
 (2 2 (:REWRITE REDUCE-RATIONALP-*))
 (2 2 (:REWRITE RATIONALP-MINUS-X))
 (2 2 (:META META-RATIONALP-CORRECT))
 (1 1 (:REWRITE ZP-OPEN)))
(RTL::R-EXACTP-30
 (116
  116
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (116 116
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (116
     116
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (116 116
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (55 10 (:REWRITE DEFAULT-MINUS))
 (52 7 (:REWRITE DEFAULT-PLUS-2))
 (42 6 (:REWRITE DEFAULT-TIMES-2))
 (11 5
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (8 2 (:REWRITE RATIONALP-X))
 (7 7
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (7 7 (:REWRITE NORMALIZE-ADDENDS))
 (7 7 (:REWRITE DEFAULT-PLUS-1))
 (7 6 (:REWRITE DEFAULT-TIMES-1))
 (6 2 (:REWRITE RTL::BVECP-EXACTP))
 (5 5 (:REWRITE THE-FLOOR-BELOW))
 (5 5 (:REWRITE THE-FLOOR-ABOVE))
 (5 5 (:REWRITE SIMPLIFY-SUMS-<))
 (5 5
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (5 5 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (5 5 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (5 5
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (5 5
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (5 5 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (5 5 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (5 5 (:REWRITE INTEGERP-<-CONSTANT))
 (5 5 (:REWRITE DEFAULT-LESS-THAN-2))
 (5 5 (:REWRITE DEFAULT-LESS-THAN-1))
 (5 5 (:REWRITE DEFAULT-EXPT-2))
 (5 5 (:REWRITE DEFAULT-EXPT-1))
 (5 5 (:REWRITE CONSTANT-<-INTEGERP))
 (5 5 (:REWRITE |(expt 1/c n)|))
 (5 5 (:REWRITE |(expt (- x) n)|))
 (5 5
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (5 5
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (5 5
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (5 5
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (5 5 (:REWRITE |(< c (- x))|))
 (5 5
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (5 5
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (5 5
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (5 5 (:REWRITE |(< (/ x) (/ y))|))
 (5 5 (:REWRITE |(< (- x) c)|))
 (5 5 (:REWRITE |(< (- x) (- y))|))
 (4 4 (:TYPE-PRESCRIPTION RTL::BVECP))
 (4 4 (:REWRITE REDUCE-INTEGERP-+))
 (4 4 (:REWRITE INTEGERP-MINUS-X))
 (4 4 (:META META-INTEGERP-CORRECT))
 (2 2 (:REWRITE REDUCE-RATIONALP-+))
 (2 2 (:REWRITE REDUCE-RATIONALP-*))
 (2 2 (:REWRITE RATIONALP-MINUS-X))
 (2 2 (:META META-RATIONALP-CORRECT))
 (1 1 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (1 1 (:REWRITE ZP-OPEN)))
(RTL::R-EXACTP-31 (204 204
                       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                  (204 204
                       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                  (204 204
                       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                  (112 24 (:TYPE-PRESCRIPTION NOT-INTEGERP-4E))
                  (112 24 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
                  (112 24 (:TYPE-PRESCRIPTION NOT-INTEGERP-3D))
                  (112 24 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
                  (112 24 (:TYPE-PRESCRIPTION NOT-INTEGERP-2D))
                  (112 24 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
                  (112 24 (:TYPE-PRESCRIPTION NOT-INTEGERP-1D))
                  (25 25 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
                  (25 25 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                  (25 25 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                  (25 25 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                  (24 24 (:TYPE-PRESCRIPTION NOT-INTEGERP-4H))
                  (24 24 (:TYPE-PRESCRIPTION NOT-INTEGERP-3H))
                  (24 24 (:TYPE-PRESCRIPTION NOT-INTEGERP-2H))
                  (24 24 (:TYPE-PRESCRIPTION NOT-INTEGERP-1H))
                  (11 3 (:REWRITE DEFAULT-TIMES-2))
                  (4 1 (:REWRITE RATIONALP-X))
                  (3 3 (:REWRITE DEFAULT-TIMES-1))
                  (1 1
                     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
                  (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                  (1 1
                     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                  (1 1 (:REWRITE REDUCE-RATIONALP-+))
                  (1 1 (:REWRITE REDUCE-RATIONALP-*))
                  (1 1
                     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                  (1 1 (:REWRITE REDUCE-INTEGERP-+))
                  (1 1
                     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
                  (1 1 (:REWRITE RATIONALP-MINUS-X))
                  (1 1
                     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                  (1 1
                     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
                  (1 1
                     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                  (1 1 (:REWRITE INTEGERP-MINUS-X))
                  (1 1
                     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
                  (1 1 (:REWRITE DEFAULT-DIVIDE))
                  (1 1 (:REWRITE |(equal c (/ x))|))
                  (1 1 (:REWRITE |(equal c (- x))|))
                  (1 1 (:REWRITE |(equal (/ x) c)|))
                  (1 1 (:REWRITE |(equal (/ x) (/ y))|))
                  (1 1 (:REWRITE |(equal (- x) c)|))
                  (1 1 (:REWRITE |(equal (- x) (- y))|))
                  (1 1 (:META META-RATIONALP-CORRECT))
                  (1 1 (:META META-INTEGERP-CORRECT)))
(RTL::R-EXACTP-32)
(RTL::R-EXACTP-33)
(RTL::R-EXACTP-34
 (1091 19
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (791 1
      (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (568 14 (:REWRITE |(< (- x) c)|))
 (389 1
      (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (389 1 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (284
  284
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (284 284
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (284
     284
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (284 284
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (284 284
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (236 1
      (:REWRITE |(<= x (/ y)) with (< 0 y)|))
 (185 1 (:REWRITE |(< (/ x) y) with (< 0 x)|))
 (170 26 (:REWRITE DEFAULT-PLUS-2))
 (170 3 (:REWRITE |(< 0 (/ x))|))
 (125 2 (:REWRITE |(* y x)|))
 (120 12 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (102 12 (:REWRITE DEFAULT-TIMES-2))
 (99 19 (:REWRITE DEFAULT-LESS-THAN-2))
 (76 10 (:LINEAR EXPT-<-1-TWO))
 (75 12 (:REWRITE DEFAULT-MINUS))
 (73 19 (:REWRITE DEFAULT-LESS-THAN-1))
 (43 8
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (43 8 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (42 15 (:REWRITE |(< (- x) (- y))|))
 (38 2
     (:REWRITE |(< 1 (* x (/ y))) with (< y 0)|))
 (38 2
     (:REWRITE |(< 1 (* x (/ y))) with (< 0 y)|))
 (32 12 (:REWRITE DEFAULT-TIMES-1))
 (32 10 (:LINEAR EXPT->-1-ONE))
 (31 4 (:REWRITE |(- (- x))|))
 (30 3 (:REWRITE DEFAULT-DIVIDE))
 (26 26 (:REWRITE DEFAULT-PLUS-1))
 (23 23 (:REWRITE DEFAULT-EXPT-2))
 (23 23 (:REWRITE DEFAULT-EXPT-1))
 (23 23 (:REWRITE |(expt 1/c n)|))
 (23 23 (:REWRITE |(expt (- x) n)|))
 (23 19
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (23 19
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (23 10 (:LINEAR EXPT->=-1-ONE))
 (21 15
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (20 20
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (20 20
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (20 20
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (20 20
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (20 2 (:REWRITE |(* (/ c) (expt d n))|))
 (19 19 (:REWRITE THE-FLOOR-BELOW))
 (19 19 (:REWRITE THE-FLOOR-ABOVE))
 (19 1
     (:REWRITE |(<= (* x (/ y)) 1) with (< y 0)|))
 (19 1
     (:REWRITE |(<= (* x (/ y)) 1) with (< 0 y)|))
 (15 15
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (15 15
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (15 15
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (15 15
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (15 15
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (15 15
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (15 15
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (15 15 (:REWRITE |(< (/ x) (/ y))|))
 (14 14 (:REWRITE |(< c (- x))|))
 (12 12 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (12 12 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (12 12 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (12 12 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (12 12 (:LINEAR EXPT-LINEAR-UPPER-<))
 (12 12 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (12 12 (:LINEAR EXPT-LINEAR-LOWER-<))
 (11 11
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (11 11
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (11 11 (:REWRITE NORMALIZE-ADDENDS))
 (11 11 (:REWRITE INTEGERP-<-CONSTANT))
 (11 11 (:REWRITE CONSTANT-<-INTEGERP))
 (10 10 (:LINEAR EXPT-X->=-X))
 (10 10 (:LINEAR EXPT-X->-X))
 (10 10 (:LINEAR EXPT->=-1-TWO))
 (10 10 (:LINEAR EXPT->-1-TWO))
 (10 10 (:LINEAR EXPT-<=-1-ONE))
 (10 10 (:LINEAR EXPT-<-1-ONE))
 (10 1
     (:REWRITE |(<= x (/ y)) with (< y 0)|))
 (10 1 (:REWRITE |(< (/ x) y) with (< x 0)|))
 (8 8 (:REWRITE SIMPLIFY-SUMS-<))
 (8 8 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (8 2 (:REWRITE RATIONALP-X))
 (7 1 (:REWRITE |(/ (expt x n))|))
 (6 2 (:REWRITE RTL::BVECP-EXACTP))
 (4 4 (:TYPE-PRESCRIPTION RTL::BVECP))
 (4 4 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
 (4 4 (:TYPE-PRESCRIPTION ABS))
 (4 4 (:REWRITE REDUCE-INTEGERP-+))
 (4 4 (:REWRITE INTEGERP-MINUS-X))
 (4 4 (:META META-INTEGERP-CORRECT))
 (3 3 (:REWRITE |(< 0 (* x y))|))
 (3 3 (:REWRITE |(< (+ c/d x) y)|))
 (3 3 (:REWRITE |(< (* x y) 0)|))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (2 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (2 2 (:REWRITE REDUCE-RATIONALP-+))
 (2 2 (:REWRITE REDUCE-RATIONALP-*))
 (2 2 (:REWRITE RATIONALP-MINUS-X))
 (2 2
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (2 2 (:REWRITE EXPT-X->-X))
 (2 2 (:META META-RATIONALP-CORRECT))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (1 1 (:REWRITE |(< (/ x) 0)|)))
(RTL::R-EXACTP-35
     (47 47 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (47 47 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (47 47 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (47 47 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (37 1
         (:REWRITE |(<= x (/ y)) with (< 0 y)|))
     (20 12 (:REWRITE DEFAULT-TIMES-2))
     (12 12 (:REWRITE DEFAULT-TIMES-1))
     (11 7
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (11 7
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (11 7 (:REWRITE DEFAULT-LESS-THAN-1))
     (8 5 (:REWRITE CONSTANT-<-INTEGERP))
     (8 5
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (8 2 (:REWRITE RATIONALP-X))
     (7 7 (:REWRITE THE-FLOOR-BELOW))
     (7 7 (:REWRITE THE-FLOOR-ABOVE))
     (7 7 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (7 7 (:REWRITE DEFAULT-LESS-THAN-2))
     (6 6
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (5 5 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (5 5 (:REWRITE INTEGERP-<-CONSTANT))
     (5 5
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (5 5
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (5 5
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (5 5 (:REWRITE |(< c (- x))|))
     (5 5
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (5 5
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (5 5
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (5 5
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (5 5 (:REWRITE |(< (/ x) (/ y))|))
     (5 5 (:REWRITE |(< (- x) c)|))
     (5 5 (:REWRITE |(< (- x) (- y))|))
     (4 4 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
     (4 4 (:TYPE-PRESCRIPTION ABS))
     (4 4 (:REWRITE SIMPLIFY-SUMS-<))
     (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (4 4 (:REWRITE REDUCE-INTEGERP-+))
     (4 4 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (4 4 (:REWRITE INTEGERP-MINUS-X))
     (4 4 (:META META-INTEGERP-CORRECT))
     (2 2 (:REWRITE REDUCE-RATIONALP-+))
     (2 2 (:REWRITE REDUCE-RATIONALP-*))
     (2 2 (:REWRITE RATIONALP-MINUS-X))
     (2 2 (:REWRITE |(< 0 (* x y))|))
     (2 2 (:REWRITE |(< (/ x) y) with (< x 0)|))
     (2 2 (:META META-RATIONALP-CORRECT))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (1 1
        (:REWRITE |(<= x (/ y)) with (< y 0)|))
     (1 1
        (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (1 1
        (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (1 1 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (1 1 (:REWRITE |(< 0 (/ x))|)))
(RTL::R-EXACTP-36)
(RTL::R-EXACTP-37
 (534
  534
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (534 534
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (534
     534
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (534 534
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (398 65 (:REWRITE DEFAULT-TIMES-2))
 (292 85 (:REWRITE DEFAULT-PLUS-2))
 (256 85 (:REWRITE DEFAULT-PLUS-1))
 (231 65 (:REWRITE DEFAULT-TIMES-1))
 (180 30 (:REWRITE DEFAULT-LESS-THAN-2))
 (180 18
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (180 18
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (174 30
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (168 2
      (:REWRITE EXPT-EXCEEDS-ANOTHER-BY-MORE-THAN-Y))
 (113 14 (:REWRITE DEFAULT-DIVIDE))
 (111 30 (:REWRITE DEFAULT-LESS-THAN-1))
 (103 22 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (96 24 (:REWRITE DEFAULT-MINUS))
 (94 94
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4A-EXPT))
 (94 94 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (94 94
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (94 94 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (94 94
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (94 94 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (94 94
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (69 24 (:REWRITE |(< (- x) (- y))|))
 (36 24
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (32 5 (:REWRITE |(< 0 (/ x))|))
 (30 30 (:REWRITE THE-FLOOR-BELOW))
 (30 30 (:REWRITE THE-FLOOR-ABOVE))
 (30 30
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (30 30
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (28 28
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (24 24 (:REWRITE INTEGERP-<-CONSTANT))
 (24 24 (:REWRITE CONSTANT-<-INTEGERP))
 (24 24
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (24 24
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (24 24
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (24 24
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (24 24 (:REWRITE |(< c (- x))|))
 (24 24
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (24 24
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (24 24
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (24 24 (:REWRITE |(< (- x) c)|))
 (22 22 (:REWRITE DEFAULT-EXPT-2))
 (22 22 (:REWRITE DEFAULT-EXPT-1))
 (22 22 (:REWRITE |(expt 1/c n)|))
 (22 22 (:REWRITE |(expt (- x) n)|))
 (18 18
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (18 18
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (12 4 (:REWRITE RTL::BVECP-EXACTP))
 (10 10 (:REWRITE SIMPLIFY-SUMS-<))
 (9 9 (:REWRITE |(* (- x) y)|))
 (8 8 (:TYPE-PRESCRIPTION RTL::BVECP))
 (8 2 (:REWRITE RATIONALP-X))
 (7 7 (:REWRITE |(< 0 (* x y))|))
 (6 6 (:REWRITE REDUCE-INTEGERP-+))
 (6 6 (:REWRITE INTEGERP-MINUS-X))
 (6 6 (:META META-INTEGERP-CORRECT))
 (5 5 (:REWRITE |(< x (+ c/d y))|))
 (5 5 (:REWRITE |(< (+ c/d x) y)|))
 (4 4 (:REWRITE |(* a (/ a))|))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (3 3 (:REWRITE |(< y (+ (- c) x))|))
 (3 3
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (3 3
    (:REWRITE |(< 0 (* x (/ y))) rationalp (* x (/ y))|))
 (3 3 (:REWRITE |(< (+ (- c) x) y)|))
 (2 2 (:REWRITE REDUCE-RATIONALP-+))
 (2 2 (:REWRITE REDUCE-RATIONALP-*))
 (2 2 (:REWRITE RATIONALP-MINUS-X))
 (2 2
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (2 2
    (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (2 2
    (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (2 2 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (2 2 (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (2 2 (:META META-RATIONALP-CORRECT))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (* x y) 0)|)))
(RTL::R-EXACTP-38)
(RTL::R-EXACTP-39
 (172 172
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (172 172
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (172 172
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (114 1
      (:REWRITE |(<= x (/ y)) with (< 0 y)|))
 (94 1 (:REWRITE |(< (/ x) y) with (< 0 x)|))
 (77 1 (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (63 1
     (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (50 16 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (46 16
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (46 2 (:REWRITE |(* (* x y) z)|))
 (44 23 (:REWRITE DEFAULT-LESS-THAN-2))
 (40 24 (:REWRITE DEFAULT-TIMES-2))
 (36 23 (:REWRITE DEFAULT-LESS-THAN-1))
 (31 23
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (31 23
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (31 19
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (30 3 (:REWRITE RTL::R-EXACTP-6))
 (28 24 (:REWRITE DEFAULT-TIMES-1))
 (23 23 (:REWRITE THE-FLOOR-BELOW))
 (23 23 (:REWRITE THE-FLOOR-ABOVE))
 (23 23
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (23 19 (:REWRITE CONSTANT-<-INTEGERP))
 (22 22 (:TYPE-PRESCRIPTION NOT-INTEGERP-4E))
 (22 22 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
 (22 22 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
 (22 22 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
 (20 2 (:REWRITE |(* y (* x z))|))
 (19 19 (:REWRITE INTEGERP-<-CONSTANT))
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
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (19 19
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (19 19
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (19 19 (:REWRITE |(< (/ x) (/ y))|))
 (19 19 (:REWRITE |(< (- x) c)|))
 (19 19 (:REWRITE |(< (- x) (- y))|))
 (18 18
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (16 16 (:REWRITE SIMPLIFY-SUMS-<))
 (10 10
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (10 10 (:REWRITE DEFAULT-DIVIDE))
 (8 8 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
 (8 8 (:TYPE-PRESCRIPTION ABS))
 (8 2 (:REWRITE RATIONALP-X))
 (8 2 (:REWRITE |(* y x)|))
 (6
   6
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (6
  6
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (6 6 (:REWRITE REDUCE-INTEGERP-+))
 (6 6 (:REWRITE INTEGERP-MINUS-X))
 (6 6 (:META META-INTEGERP-CORRECT))
 (5 1
    (:REWRITE |(<= x (/ y)) with (< y 0)|))
 (5 1 (:REWRITE |(< (/ x) y) with (< x 0)|))
 (4 4
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (4 4 (:REWRITE |(* c (* d x))|))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (2 2 (:REWRITE REDUCE-RATIONALP-+))
 (2 2 (:REWRITE REDUCE-RATIONALP-*))
 (2 2 (:REWRITE RATIONALP-MINUS-X))
 (2 2 (:META META-RATIONALP-CORRECT))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (1 1
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (1 1
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (1 1
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (1 1
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (1 1
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (1 1 (:REWRITE |(equal c (/ x))|))
 (1 1 (:REWRITE |(equal c (- x))|))
 (1 1 (:REWRITE |(equal (/ x) c)|))
 (1 1 (:REWRITE |(equal (/ x) (/ y))|))
 (1 1 (:REWRITE |(equal (- x) c)|))
 (1 1 (:REWRITE |(equal (- x) (- y))|))
 (1 1
    (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (1 1 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (1 1 (:REWRITE |(< 0 (/ x))|))
 (1 1
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (1 1 (:REWRITE |(< 0 (* x y))|))
 (1 1
    (:REWRITE |(< 0 (* x (/ y))) rationalp (* x (/ y))|)))
(RTL::R-EXACTP-40
 (547
  547
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (547 547
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (547
     547
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (547 547
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (547 547
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (304 43 (:REWRITE DEFAULT-PLUS-2))
 (165 43 (:REWRITE DEFAULT-PLUS-1))
 (139 139
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (139 139
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (139 139
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (138 17
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (89 22 (:REWRITE DEFAULT-LESS-THAN-2))
 (85 22 (:REWRITE DEFAULT-LESS-THAN-1))
 (79 12 (:REWRITE SIMPLIFY-SUMS-<))
 (39 21 (:REWRITE |(< (- x) (- y))|))
 (33 21
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (30 12 (:REWRITE DEFAULT-MINUS))
 (23 5 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (22 22 (:REWRITE THE-FLOOR-BELOW))
 (22 22 (:REWRITE THE-FLOOR-ABOVE))
 (21 21
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (21 21
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (21 21
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
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
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (21 21
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (21 21
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (21 21 (:REWRITE |(< (/ x) (/ y))|))
 (21 21 (:REWRITE |(< (- x) c)|))
 (16 16
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (15 5 (:REWRITE RTL::BVECP-EXACTP))
 (12 3 (:REWRITE RATIONALP-X))
 (10 10 (:TYPE-PRESCRIPTION RTL::BVECP))
 (10 10 (:REWRITE DEFAULT-EXPT-2))
 (10 10 (:REWRITE DEFAULT-EXPT-1))
 (10 10 (:REWRITE |(expt 1/c n)|))
 (10 10 (:REWRITE |(expt (- x) n)|))
 (10 2 (:REWRITE ODD-EXPT-THM))
 (9 9 (:REWRITE REDUCE-INTEGERP-+))
 (9 9 (:REWRITE INTEGERP-MINUS-X))
 (9 9 (:META META-INTEGERP-CORRECT))
 (8 8 (:REWRITE |(< (+ c/d x) y)|))
 (8 8 (:REWRITE |(< (+ (- c) x) y)|))
 (6 6 (:REWRITE |(+ c (+ d x))|))
 (4 4 (:REWRITE |(< y (+ (- c) x))|))
 (4 4 (:REWRITE |(< x (+ c/d y))|))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (3 3 (:REWRITE REDUCE-RATIONALP-+))
 (3 3 (:REWRITE REDUCE-RATIONALP-*))
 (3 3 (:REWRITE RATIONALP-MINUS-X))
 (3 3 (:META META-RATIONALP-CORRECT))
 (2 2
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (2 2
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (2 2 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE DEFAULT-TIMES-2))
 (2 2 (:REWRITE DEFAULT-TIMES-1))
 (2 2 (:REWRITE DEFAULT-DIVIDE))
 (2 2 (:LINEAR EXPT-X->=-X))
 (2 2 (:LINEAR EXPT-X->-X))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->=-1-ONE))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT->-1-ONE))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-ONE))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (* x y) 0)|))
 (1 1 (:REWRITE |(- (* c x))|)))
(RTL::R-EXACTP-41
 (75
  75
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (75 75
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (75 75
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (75 75
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (30 3
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (30 3
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (21 3 (:REWRITE DEFAULT-TIMES-2))
 (11 11 (:REWRITE DEFAULT-EXPT-2))
 (11 11 (:REWRITE DEFAULT-EXPT-1))
 (11 11 (:REWRITE |(expt 1/c n)|))
 (11 11 (:REWRITE |(expt (- x) n)|))
 (8 8
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (8 8
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (8 8
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (8 8
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (4 4 (:LINEAR EXPT-X->=-X))
 (4 4 (:LINEAR EXPT-X->-X))
 (4 4 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (4 4 (:LINEAR EXPT-LINEAR-UPPER-<))
 (4 4 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (4 4 (:LINEAR EXPT-LINEAR-LOWER-<))
 (4 4 (:LINEAR EXPT->=-1-TWO))
 (4 4 (:LINEAR EXPT->=-1-ONE))
 (4 4 (:LINEAR EXPT->-1-TWO))
 (4 4 (:LINEAR EXPT->-1-ONE))
 (4 4 (:LINEAR EXPT-<=-1-ONE))
 (4 4 (:LINEAR EXPT-<-1-ONE))
 (4 3 (:REWRITE DEFAULT-TIMES-1))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (3 3 (:REWRITE DEFAULT-PLUS-2))
 (3 3 (:REWRITE DEFAULT-PLUS-1))
 (2 2 (:REWRITE DEFAULT-MINUS))
 (1 1 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (1 1 (:REWRITE NORMALIZE-ADDENDS)))
(RTL::R-EXACTP-42
 (767
  767
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (767 767
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (767
     767
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (767 767
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (767 767
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (604 604
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (604 604
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (604 604
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (528 107 (:REWRITE DEFAULT-PLUS-2))
 (338 107 (:REWRITE DEFAULT-PLUS-1))
 (266 42
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (247 31 (:REWRITE DEFAULT-TIMES-2))
 (213 51 (:REWRITE DEFAULT-LESS-THAN-1))
 (198 51 (:REWRITE DEFAULT-LESS-THAN-2))
 (129 42 (:REWRITE DEFAULT-MINUS))
 (123 29 (:REWRITE SIMPLIFY-SUMS-<))
 (70 46
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (62 14 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (58 46 (:REWRITE |(< (- x) (- y))|))
 (51 51 (:REWRITE THE-FLOOR-BELOW))
 (51 51 (:REWRITE THE-FLOOR-ABOVE))
 (46 46
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (46 46
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (46 46
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (46 46 (:REWRITE INTEGERP-<-CONSTANT))
 (46 46 (:REWRITE CONSTANT-<-INTEGERP))
 (46 46
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (46 46
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (46 46
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (46 46
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (46 46 (:REWRITE |(< c (- x))|))
 (46 46
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (46 46
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (46 46
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (46 46 (:REWRITE |(< (/ x) (/ y))|))
 (46 46 (:REWRITE |(< (- x) c)|))
 (42 42
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (36 12 (:REWRITE RTL::BVECP-EXACTP))
 (36 9 (:REWRITE RATIONALP-X))
 (31 31 (:REWRITE DEFAULT-TIMES-1))
 (24 24 (:TYPE-PRESCRIPTION RTL::BVECP))
 (17 17 (:REWRITE REDUCE-INTEGERP-+))
 (17 17 (:REWRITE INTEGERP-MINUS-X))
 (17 17 (:META META-INTEGERP-CORRECT))
 (13 13 (:REWRITE |(< (+ (- c) x) y)|))
 (12 12 (:REWRITE DEFAULT-EXPT-2))
 (12 12 (:REWRITE DEFAULT-EXPT-1))
 (12 12 (:REWRITE |(expt 1/c n)|))
 (12 12 (:REWRITE |(expt (- x) n)|))
 (9 9 (:REWRITE REDUCE-RATIONALP-+))
 (9 9 (:REWRITE REDUCE-RATIONALP-*))
 (9 9 (:REWRITE RATIONALP-MINUS-X))
 (9 9 (:REWRITE |(< y (+ (- c) x))|))
 (9 9 (:REWRITE |(< x (+ c/d y))|))
 (9 9 (:META META-RATIONALP-CORRECT))
 (7 7 (:REWRITE |(+ c (+ d x))|))
 (5 5 (:REWRITE |(* (- x) y)|))
 (4 4
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (4 4 (:REWRITE DEFAULT-DIVIDE))
 (4 4 (:REWRITE |(< (/ x) 0)|))
 (4 4 (:REWRITE |(< (* x y) 0)|))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (3 3 (:REWRITE ZP-OPEN))
 (2 2 (:LINEAR EXPT-X->=-X))
 (2 2 (:LINEAR EXPT-X->-X))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->=-1-ONE))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT->-1-ONE))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-EXACTP-43
 (2040 3 (:REWRITE RTL::R-EXACTP-6))
 (1869 31
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (1699 13 (:REWRITE |(< (+ c/d x) y)|))
 (1170 3
       (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (841 18 (:REWRITE |(< (- x) c)|))
 (592 128 (:REWRITE DEFAULT-PLUS-2))
 (516 1 (:REWRITE |(< (/ x) y) with (< 0 x)|))
 (478 55 (:REWRITE DEFAULT-TIMES-2))
 (460
  460
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (460 460
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (460
     460
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (460 460
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (460 460
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (228 14 (:REWRITE |(* c (expt d n))|))
 (202 128 (:REWRITE DEFAULT-PLUS-1))
 (197 31 (:REWRITE DEFAULT-MINUS))
 (178 36 (:REWRITE DEFAULT-LESS-THAN-1))
 (170 3 (:REWRITE |(< 0 (/ x))|))
 (138 36 (:REWRITE DEFAULT-LESS-THAN-2))
 (138 12 (:REWRITE INTEGERP-<-CONSTANT))
 (108 1 (:REWRITE EVEN-AND-ODD-ALTERNATE))
 (105 55 (:REWRITE DEFAULT-TIMES-1))
 (66 19 (:REWRITE |(< (- x) (- y))|))
 (64 64 (:REWRITE DEFAULT-EXPT-2))
 (64 64 (:REWRITE DEFAULT-EXPT-1))
 (64 64 (:REWRITE |(expt 1/c n)|))
 (64 64 (:REWRITE |(expt (- x) n)|))
 (60 60 (:TYPE-PRESCRIPTION COLLECT-*))
 (56 56
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (48 8
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (45 7 (:REWRITE |(- (- x))|))
 (43 21 (:LINEAR EXPT->-1-ONE))
 (42 42
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (42 42
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (42 42
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (42 42
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (36 36 (:REWRITE THE-FLOOR-BELOW))
 (36 36 (:REWRITE THE-FLOOR-ABOVE))
 (34 21 (:LINEAR EXPT->=-1-ONE))
 (34 16 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (31 31
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (31 31
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (30 3
     (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (30 3 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (27 18 (:REWRITE |(< c (- x))|))
 (23 23 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (23 23 (:LINEAR EXPT-LINEAR-UPPER-<))
 (23 23 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (23 23 (:LINEAR EXPT-LINEAR-LOWER-<))
 (21 21 (:LINEAR EXPT-X->=-X))
 (21 21 (:LINEAR EXPT-X->-X))
 (21 21 (:LINEAR EXPT->=-1-TWO))
 (21 21 (:LINEAR EXPT->-1-TWO))
 (21 21 (:LINEAR EXPT-<=-1-ONE))
 (21 21 (:LINEAR EXPT-<-1-ONE))
 (19 19
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (19 19
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (19 19
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (19 19
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (19 19
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (19 19
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (19 19
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (19 19
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (19 19 (:REWRITE |(< (/ x) (/ y))|))
 (12 12
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (12 12 (:REWRITE CONSTANT-<-INTEGERP))
 (10 10 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (10 1 (:REWRITE DEFAULT-DIVIDE))
 (10 1
     (:REWRITE |(<= x (/ y)) with (< y 0)|))
 (10 1 (:REWRITE |(< (/ x) y) with (< x 0)|))
 (7 1 (:REWRITE |(/ (expt x n))|))
 (6 6 (:REWRITE SIMPLIFY-SUMS-<))
 (5 5 (:REWRITE ODD-EXPT-THM))
 (4 4 (:REWRITE |(* 1 x)|))
 (4 2 (:REWRITE COLLECT-*-PROBLEM-FINDER))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (3 3 (:REWRITE |(< 0 (* x y))|))
 (3 3 (:REWRITE |(< (* x y) 0)|))
 (2 2
    (:TYPE-PRESCRIPTION FMT-TO-COMMENT-WINDOW))
 (2 2 (:REWRITE |(< y (+ (- c) x))|))
 (2 2 (:REWRITE |(< (+ (- c) x) y)|))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (1 1
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (1 1
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (1 1
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (1 1
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (1 1
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (1 1 (:REWRITE |(equal c (/ x))|))
 (1 1 (:REWRITE |(equal c (- x))|))
 (1 1 (:REWRITE |(equal (/ x) c)|))
 (1 1 (:REWRITE |(equal (/ x) (/ y))|))
 (1 1 (:REWRITE |(equal (- x) c)|))
 (1 1 (:REWRITE |(equal (- x) (- y))|))
 (1 1 (:REWRITE |(< (/ x) 0)|)))
(RTL::R-EXACTP-44
 (1360 2 (:REWRITE RTL::R-EXACTP-6))
 (1128 4 (:REWRITE |(< (+ c/d x) y)|))
 (670 6 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (294 4 (:REWRITE |(< (- x) c)|))
 (184 8 (:LINEAR EXPT-<=-1-TWO))
 (184 8 (:LINEAR EXPT-<-1-TWO))
 (171 36 (:REWRITE DEFAULT-PLUS-2))
 (156 21 (:REWRITE DEFAULT-TIMES-2))
 (127
  127
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (127 127
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (127
     127
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (127 127
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (79 21 (:REWRITE DEFAULT-TIMES-1))
 (64 2 (:REWRITE |(* c (expt d n))|))
 (62 8 (:REWRITE DEFAULT-MINUS))
 (62 8 (:REWRITE DEFAULT-LESS-THAN-1))
 (46 36 (:REWRITE DEFAULT-PLUS-1))
 (26 8 (:REWRITE DEFAULT-LESS-THAN-2))
 (22 22 (:REWRITE DEFAULT-EXPT-2))
 (22 22 (:REWRITE DEFAULT-EXPT-1))
 (22 22 (:REWRITE |(expt 1/c n)|))
 (22 22 (:REWRITE |(expt (- x) n)|))
 (22 4 (:REWRITE |(< (- x) (- y))|))
 (20 2 (:REWRITE |(- (- x))|))
 (16 16
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (16 16
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (16 16
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (16 16
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (15 15
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (14 5 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (8 8 (:REWRITE THE-FLOOR-BELOW))
 (8 8 (:REWRITE THE-FLOOR-ABOVE))
 (8 8 (:LINEAR EXPT-X->=-X))
 (8 8 (:LINEAR EXPT-X->-X))
 (8 8 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (8 8 (:LINEAR EXPT-LINEAR-UPPER-<))
 (8 8 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (8 8 (:LINEAR EXPT-LINEAR-LOWER-<))
 (8 8 (:LINEAR EXPT->=-1-TWO))
 (8 8 (:LINEAR EXPT->=-1-ONE))
 (8 8 (:LINEAR EXPT->-1-TWO))
 (8 8 (:LINEAR EXPT->-1-ONE))
 (8 8 (:LINEAR EXPT-<=-1-ONE))
 (8 8 (:LINEAR EXPT-<-1-ONE))
 (6 6
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (6 6
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
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
 (3 1 (:REWRITE RTL::BVECP-EXACTP))
 (2 2 (:TYPE-PRESCRIPTION RTL::BVECP))
 (2 2 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (2 2 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (2 2 (:REWRITE ODD-EXPT-THM))
 (2 2 (:REWRITE INTEGERP-<-CONSTANT))
 (2 2 (:REWRITE CONSTANT-<-INTEGERP))
 (2 1
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (2 1
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
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
 (1 1 (:REWRITE |(equal (- x) (- y))|)))
(RTL::R-EXACTP-45
 (2892 6 (:REWRITE RTL::R-EXACTP-6))
 (2207 23 (:REWRITE |(< (+ c/d x) y)|))
 (1395 293 (:REWRITE DEFAULT-PLUS-2))
 (1338 14 (:REWRITE |(* x (+ y z))|))
 (1283 83
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (1156
  1156
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1156
      1156
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1156
     1156
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1156 1156
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1156 1156
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (826 6
      (:REWRITE |(<= x (/ y)) with (< 0 y)|))
 (783 6 (:REWRITE |(< (/ x) y) with (< 0 x)|))
 (732 293 (:REWRITE DEFAULT-PLUS-1))
 (618 6
      (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (615 93 (:REWRITE DEFAULT-TIMES-2))
 (569 569
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (569 569
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (569 569
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (545 71 (:REWRITE |(< (- x) c)|))
 (468 6 (:REWRITE |(* x (- y))|))
 (410 90 (:REWRITE DEFAULT-LESS-THAN-1))
 (393 71 (:REWRITE DEFAULT-MINUS))
 (377 90 (:REWRITE DEFAULT-LESS-THAN-2))
 (372 55
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (332 20 (:REWRITE |(* c (expt d n))|))
 (171 65 (:REWRITE CONSTANT-<-INTEGERP))
 (169 71 (:REWRITE |(< (- x) (- y))|))
 (167 93 (:REWRITE DEFAULT-TIMES-1))
 (135 37 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (114 114
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (105 41 (:REWRITE SIMPLIFY-SUMS-<))
 (98 71 (:REWRITE |(< c (- x))|))
 (90 90 (:REWRITE THE-FLOOR-BELOW))
 (90 90 (:REWRITE THE-FLOOR-ABOVE))
 (89 83
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (89 83
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (89 71
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (82 10 (:REWRITE ODD-EXPT-THM))
 (71 71
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (71 71
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (71 71
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (71 71
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (71 71
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (71 71
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (71 71
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (71 71 (:REWRITE |(< (/ x) (/ y))|))
 (65 65 (:REWRITE INTEGERP-<-CONSTANT))
 (62 62 (:REWRITE DEFAULT-EXPT-2))
 (62 62 (:REWRITE DEFAULT-EXPT-1))
 (62 62 (:REWRITE |(expt 1/c n)|))
 (62 62 (:REWRITE |(expt (- x) n)|))
 (54 18 (:REWRITE RTL::BVECP-EXACTP))
 (51 6
     (:REWRITE |(<= x (/ y)) with (< y 0)|))
 (51 6 (:REWRITE |(< (/ x) y) with (< x 0)|))
 (36 36 (:TYPE-PRESCRIPTION RTL::BVECP))
 (33 6
     (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (33 6 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (28 20 (:REWRITE INTEGERP-MINUS-X))
 (24 6 (:REWRITE RATIONALP-X))
 (21 21 (:REWRITE |(< y (+ (- c) x))|))
 (21 21 (:REWRITE |(< x (+ c/d y))|))
 (20 20 (:REWRITE REDUCE-INTEGERP-+))
 (20 20 (:META META-INTEGERP-CORRECT))
 (14 14
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (14 14
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (14 14
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (14 14
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (11 11 (:REWRITE |(< (+ (- c) x) y)|))
 (8 8 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (7 7 (:LINEAR EXPT-X->=-X))
 (7 7 (:LINEAR EXPT-X->-X))
 (7 7 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (7 7 (:LINEAR EXPT-LINEAR-UPPER-<))
 (7 7 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (7 7 (:LINEAR EXPT-LINEAR-LOWER-<))
 (7 7 (:LINEAR EXPT->=-1-TWO))
 (7 7 (:LINEAR EXPT->=-1-ONE))
 (7 7 (:LINEAR EXPT->-1-TWO))
 (7 7 (:LINEAR EXPT->-1-ONE))
 (7 7 (:LINEAR EXPT-<=-1-ONE))
 (7 7 (:LINEAR EXPT-<-1-ONE))
 (6 6 (:REWRITE REDUCE-RATIONALP-+))
 (6 6 (:REWRITE REDUCE-RATIONALP-*))
 (6 6 (:REWRITE RATIONALP-MINUS-X))
 (6 6 (:REWRITE |(< 0 (/ x))|))
 (6 6 (:REWRITE |(< 0 (* x y))|))
 (6 6 (:REWRITE |(* 1 x)|))
 (6 6 (:META META-RATIONALP-CORRECT))
 (6 3
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (6 3
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (3 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (3 3
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (3 3
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (3 3
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (3 3
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (3 3 (:REWRITE DEFAULT-DIVIDE))
 (3 3 (:REWRITE |(equal c (/ x))|))
 (3 3 (:REWRITE |(equal c (- x))|))
 (3 3 (:REWRITE |(equal (/ x) c)|))
 (3 3 (:REWRITE |(equal (/ x) (/ y))|))
 (3 3 (:REWRITE |(equal (- x) c)|))
 (3 3 (:REWRITE |(equal (- x) (- y))|))
 (3 3 (:REWRITE |(< (/ x) 0)|))
 (3 3 (:REWRITE |(< (* x y) 0)|))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE |(- (* c x))|)))
(RTL::R-EXACTP-46
 (553 553
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (553 553
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (553 553
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (331
  331
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (331 331
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (331
     331
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (331 331
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (331 331
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (199 51 (:REWRITE DEFAULT-PLUS-2))
 (181 47
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (160 67 (:REWRITE DEFAULT-LESS-THAN-2))
 (149 67 (:REWRITE DEFAULT-LESS-THAN-1))
 (144 5 (:REWRITE RTL::R-EXACTP-6))
 (120 51 (:REWRITE DEFAULT-PLUS-1))
 (108 3 (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (104 40 (:REWRITE SIMPLIFY-SUMS-<))
 (102 3
      (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (99 63
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (78 66
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (78 66
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (76 4 (:REWRITE ODD-EXPT-THM))
 (72 63 (:REWRITE INTEGERP-<-CONSTANT))
 (71 63 (:REWRITE |(< (- x) (- y))|))
 (67 67 (:REWRITE THE-FLOOR-BELOW))
 (67 67 (:REWRITE THE-FLOOR-ABOVE))
 (66 66
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (63 63 (:REWRITE CONSTANT-<-INTEGERP))
 (63 63
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (63 63
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (63 63
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (63 63
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (63 63 (:REWRITE |(< c (- x))|))
 (63 63
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (63 63
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (63 63
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (63 63 (:REWRITE |(< (/ x) (/ y))|))
 (63 63 (:REWRITE |(< (- x) c)|))
 (41 1 (:LINEAR EXPT->=-1-ONE))
 (40 1 (:LINEAR EXPT->-1-ONE))
 (40 1 (:LINEAR EXPT-<=-1-TWO))
 (39 1 (:LINEAR EXPT-<-1-TWO))
 (36 1 (:LINEAR EXPT-X->=-X))
 (36 1 (:LINEAR EXPT-X->-X))
 (33 25 (:REWRITE INTEGERP-MINUS-X))
 (28 12 (:REWRITE DEFAULT-MINUS))
 (27 9 (:REWRITE RTL::BVECP-EXACTP))
 (25 25 (:REWRITE REDUCE-INTEGERP-+))
 (25 25 (:META META-INTEGERP-CORRECT))
 (24 6 (:REWRITE RATIONALP-X))
 (18 18 (:TYPE-PRESCRIPTION RTL::BVECP))
 (15 15 (:REWRITE DEFAULT-TIMES-2))
 (15 15 (:REWRITE DEFAULT-TIMES-1))
 (15 7 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (12 12
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (12 3 (:REWRITE |(* y x)|))
 (11 11
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (9 9 (:REWRITE |(< (+ c/d x) y)|))
 (9 9 (:REWRITE |(< (+ (- c) x) y)|))
 (8 8 (:REWRITE |(< y (+ (- c) x))|))
 (8 8 (:REWRITE |(< x (+ c/d y))|))
 (6 6 (:REWRITE REDUCE-RATIONALP-+))
 (6 6 (:REWRITE REDUCE-RATIONALP-*))
 (6 6 (:REWRITE RATIONALP-MINUS-X))
 (6 6
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (6 6 (:REWRITE DEFAULT-DIVIDE))
 (6 6 (:META META-RATIONALP-CORRECT))
 (6 3
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (6 3
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (5 5 (:REWRITE |(< (/ x) 0)|))
 (5 5 (:REWRITE |(< (* x y) 0)|))
 (4 4 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (3 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (3 3
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (3 3
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (3 3
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (3 3 (:REWRITE DEFAULT-EXPT-2))
 (3 3 (:REWRITE DEFAULT-EXPT-1))
 (3 3 (:REWRITE |(expt 1/c n)|))
 (3 3 (:REWRITE |(expt (- x) n)|))
 (3 3 (:REWRITE |(equal c (/ x))|))
 (3 3 (:REWRITE |(equal c (- x))|))
 (3 3 (:REWRITE |(equal (/ x) c)|))
 (3 3 (:REWRITE |(equal (/ x) (/ y))|))
 (3 3 (:REWRITE |(equal (- x) c)|))
 (3 3 (:REWRITE |(equal (- x) (- y))|))
 (3 3
    (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (3 3 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (3 3
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (3 3
    (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:REWRITE |(< 0 (* x y))|))
 (2 2 (:REWRITE |(- (* c x))|))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<))
 (1 1 (:LINEAR EXPT->=-1-TWO))
 (1 1 (:LINEAR EXPT->-1-TWO))
 (1 1 (:LINEAR EXPT-<=-1-ONE))
 (1 1 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-EXACTP-47
 (2344 2344
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (2344 2344
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (2344 2344
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (1345
  1345
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1345
      1345
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1345
     1345
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1345 1345
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1345 1345
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (1197 30 (:REWRITE RTL::R-EXACTP-6))
 (951 261
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (934 282 (:REWRITE DEFAULT-PLUS-2))
 (764 182
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (661 264 (:REWRITE DEFAULT-LESS-THAN-2))
 (628 264 (:REWRITE DEFAULT-LESS-THAN-1))
 (593 11 (:LINEAR EXPT->=-1-ONE))
 (581 11 (:LINEAR EXPT-<-1-TWO))
 (558 240 (:REWRITE |(< (- x) c)|))
 (550 282 (:REWRITE DEFAULT-PLUS-1))
 (421 153 (:REWRITE SIMPLIFY-SUMS-<))
 (348 240
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (304 16 (:REWRITE ODD-EXPT-THM))
 (272 240 (:REWRITE |(< (- x) (- y))|))
 (264 264 (:REWRITE THE-FLOOR-BELOW))
 (264 264 (:REWRITE THE-FLOOR-ABOVE))
 (261 261
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (261 261
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (240 240
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (240 240
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (240 240
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (240 240
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (240 240 (:REWRITE |(< c (- x))|))
 (240 240
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (240 240
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (240 240
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (240 240 (:REWRITE |(< (/ x) (/ y))|))
 (228 228 (:REWRITE INTEGERP-<-CONSTANT))
 (228 228 (:REWRITE CONSTANT-<-INTEGERP))
 (130 66 (:REWRITE DEFAULT-MINUS))
 (117 39 (:REWRITE RTL::BVECP-EXACTP))
 (113 13
      (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (112 8
      (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (111 79 (:REWRITE INTEGERP-MINUS-X))
 (108 27 (:REWRITE RATIONALP-X))
 (79 79 (:REWRITE REDUCE-INTEGERP-+))
 (79 79 (:META META-INTEGERP-CORRECT))
 (78 78 (:TYPE-PRESCRIPTION RTL::BVECP))
 (78 78
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (77 41 (:REWRITE |(+ c (+ d x))|))
 (61 29 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (51 51 (:REWRITE |(< (+ c/d x) y)|))
 (50 11 (:LINEAR EXPT->-1-ONE))
 (48 48 (:REWRITE |(< (* x y) 0)|))
 (46 11 (:LINEAR EXPT-X->=-X))
 (46 11 (:LINEAR EXPT-X->-X))
 (39 39 (:REWRITE |(< (+ (- c) x) y)|))
 (36 36
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (36 36
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (36 36 (:REWRITE DEFAULT-TIMES-2))
 (36 36 (:REWRITE DEFAULT-TIMES-1))
 (36 36 (:REWRITE DEFAULT-DIVIDE))
 (36 36 (:REWRITE |(< (/ x) 0)|))
 (33 27 (:REWRITE DEFAULT-EXPT-2))
 (27 27 (:REWRITE REDUCE-RATIONALP-+))
 (27 27 (:REWRITE REDUCE-RATIONALP-*))
 (27 27 (:REWRITE RATIONALP-MINUS-X))
 (27 27 (:REWRITE DEFAULT-EXPT-1))
 (27 27 (:REWRITE |(expt 1/c n)|))
 (27 27 (:REWRITE |(expt (- x) n)|))
 (27 27 (:META META-RATIONALP-CORRECT))
 (24 24 (:REWRITE |(< y (+ (- c) x))|))
 (24 24 (:REWRITE |(< x (+ c/d y))|))
 (23 23
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (23 23
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (22 22
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (22 22
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (22 22
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (22 22
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (22 17
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (22 17
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (17 17 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (17 17
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (17 17
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (17 17
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (17 17 (:REWRITE |(equal c (/ x))|))
 (17 17 (:REWRITE |(equal c (- x))|))
 (17 17 (:REWRITE |(equal (/ x) c)|))
 (17 17 (:REWRITE |(equal (/ x) (/ y))|))
 (17 17 (:REWRITE |(equal (- x) c)|))
 (17 17 (:REWRITE |(equal (- x) (- y))|))
 (16 16
     (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (13 13
     (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (11 11 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (11 11 (:LINEAR EXPT-LINEAR-UPPER-<))
 (11 11 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (11 11 (:LINEAR EXPT-LINEAR-LOWER-<))
 (11 11 (:LINEAR EXPT->=-1-TWO))
 (11 11 (:LINEAR EXPT->-1-TWO))
 (11 11 (:LINEAR EXPT-<=-1-ONE))
 (11 11 (:LINEAR EXPT-<-1-ONE))
 (9 9 (:REWRITE ZP-OPEN))
 (8 8 (:REWRITE FOLD-CONSTS-IN-+))
 (8 8
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (8 8 (:REWRITE |(- (* c x))|))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:REWRITE |(< 0 (* x y))|)))
(RTL::R-EXACTP-48
 (542 542
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (542 542
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (542 542
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (542 542
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (533
  533
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (533 533
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (533
     533
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (533 533
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (533 533
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (533 533
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (476 6 (:REWRITE RTL::R-EXACTP-6))
 (284 80 (:REWRITE DEFAULT-PLUS-2))
 (235 53
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (186 65 (:REWRITE DEFAULT-LESS-THAN-2))
 (179 64
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (173 80 (:REWRITE DEFAULT-PLUS-1))
 (162 65 (:REWRITE DEFAULT-LESS-THAN-1))
 (115 62 (:REWRITE |(< (- x) c)|))
 (111 43 (:REWRITE SIMPLIFY-SUMS-<))
 (111 2 (:LINEAR EXPT->=-1-ONE))
 (108 4
      (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (108 2 (:LINEAR EXPT-<-1-TWO))
 (104 4
      (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (86 62
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (85 5 (:REWRITE ODD-EXPT-THM))
 (79 62 (:REWRITE |(< (- x) (- y))|))
 (65 65 (:REWRITE THE-FLOOR-BELOW))
 (65 65 (:REWRITE THE-FLOOR-ABOVE))
 (64 64
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (64 64
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (62 62
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (62 62
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (62 62
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (62 62
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (62 62 (:REWRITE |(< c (- x))|))
 (62 62
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (62 62
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (62 62
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (62 62 (:REWRITE |(< (/ x) (/ y))|))
 (60 60 (:REWRITE INTEGERP-<-CONSTANT))
 (60 60 (:REWRITE CONSTANT-<-INTEGERP))
 (43 18 (:REWRITE DEFAULT-MINUS))
 (41 2 (:LINEAR EXPT->-1-ONE))
 (37 2 (:LINEAR EXPT-X->=-X))
 (37 2 (:LINEAR EXPT-X->-X))
 (36 12 (:REWRITE RTL::BVECP-EXACTP))
 (28 20 (:REWRITE INTEGERP-MINUS-X))
 (28 7 (:REWRITE RATIONALP-X))
 (27 10 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (24 24 (:TYPE-PRESCRIPTION RTL::BVECP))
 (23 23
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (20 20 (:REWRITE REDUCE-INTEGERP-+))
 (20 20 (:META META-INTEGERP-CORRECT))
 (16 10 (:REWRITE |(+ c (+ d x))|))
 (14 14 (:REWRITE |(< (+ c/d x) y)|))
 (12 12 (:REWRITE |(< (+ (- c) x) y)|))
 (12 5 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (11 11
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (11 11 (:REWRITE DEFAULT-TIMES-2))
 (11 11 (:REWRITE DEFAULT-TIMES-1))
 (11 11 (:REWRITE DEFAULT-DIVIDE))
 (10 10 (:REWRITE |(< y (+ (- c) x))|))
 (10 10 (:REWRITE |(< x (+ c/d y))|))
 (9 9 (:REWRITE |(< (* x y) 0)|))
 (9 6 (:REWRITE DEFAULT-EXPT-2))
 (7 7 (:REWRITE REDUCE-RATIONALP-+))
 (7 7 (:REWRITE REDUCE-RATIONALP-*))
 (7 7 (:REWRITE RATIONALP-MINUS-X))
 (7 7
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (7 7 (:REWRITE |(< (/ x) 0)|))
 (7 7 (:META META-RATIONALP-CORRECT))
 (6 6 (:REWRITE DEFAULT-EXPT-1))
 (6 6 (:REWRITE |(expt 1/c n)|))
 (6 6 (:REWRITE |(expt (- x) n)|))
 (4 4
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (4 4
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (4 1 (:REWRITE |(integerp (- x))|))
 (3 3 (:REWRITE ZP-OPEN))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (3 3 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:REWRITE |(< 0 (* x y))|))
 (2 2 (:REWRITE |(- (* c x))|))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-ONE))
 (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (1 1
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (1 1
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (1 1
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (1 1
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (1 1
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (1 1 (:REWRITE |(equal c (/ x))|))
 (1 1 (:REWRITE |(equal c (- x))|))
 (1 1 (:REWRITE |(equal (/ x) c)|))
 (1 1 (:REWRITE |(equal (/ x) (/ y))|))
 (1 1 (:REWRITE |(equal (- x) c)|))
 (1 1 (:REWRITE |(equal (- x) (- y))|)))
(RTL::R-EXACTP-49
 (6451 11 (:REWRITE RTL::R-EXACTP-6))
 (6042 149
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (2977 106 (:REWRITE |(< (- x) c)|))
 (1968 36 (:LINEAR EXPT->=-1-ONE))
 (1149 249 (:REWRITE DEFAULT-PLUS-2))
 (798
  798
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (798 798
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (798
     798
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (798 798
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (570 1 (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (559 1
      (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (466 150 (:REWRITE DEFAULT-LESS-THAN-1))
 (434 249 (:REWRITE DEFAULT-PLUS-1))
 (388 82 (:REWRITE DEFAULT-MINUS))
 (333 150 (:REWRITE DEFAULT-LESS-THAN-2))
 (250 106 (:REWRITE |(< (- x) (- y))|))
 (158 41 (:REWRITE |(- (- x))|))
 (157 54
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (156 2 (:REWRITE |(* x (- y))|))
 (150 150 (:REWRITE THE-FLOOR-BELOW))
 (150 150 (:REWRITE THE-FLOOR-ABOVE))
 (149 149
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (149 149
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (124 106 (:REWRITE |(< c (- x))|))
 (116 1 (:REWRITE |(* y x)|))
 (112 13 (:REWRITE DEFAULT-TIMES-2))
 (106 106
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (106 106
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (106 106
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (106 106
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (106 106
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (106 106
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (106 106
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (106 106
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (106 106 (:REWRITE |(< (/ x) (/ y))|))
 (95 95
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (84 84 (:REWRITE DEFAULT-EXPT-2))
 (84 84 (:REWRITE DEFAULT-EXPT-1))
 (84 84 (:REWRITE |(expt 1/c n)|))
 (84 84 (:REWRITE |(expt (- x) n)|))
 (83 65 (:REWRITE INTEGERP-<-CONSTANT))
 (72 72
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (72 72
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (72 72
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (72 72
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (66 64 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (65 65
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (65 65 (:REWRITE CONSTANT-<-INTEGERP))
 (53 8 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (49 49 (:REWRITE SIMPLIFY-SUMS-<))
 (46 46 (:REWRITE |(< (+ c/d x) y)|))
 (44 2 (:REWRITE |(* x (expt x n))|))
 (41 41 (:REWRITE |(< (* x y) 0)|))
 (39 39 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (39 39 (:LINEAR EXPT-LINEAR-UPPER-<))
 (39 39 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (39 39 (:LINEAR EXPT-LINEAR-LOWER-<))
 (36 36 (:LINEAR EXPT-X->=-X))
 (36 36 (:LINEAR EXPT-X->-X))
 (36 36 (:LINEAR EXPT->=-1-TWO))
 (36 36 (:LINEAR EXPT->-1-TWO))
 (36 36 (:LINEAR EXPT->-1-ONE))
 (36 36 (:LINEAR EXPT-<=-1-ONE))
 (36 36 (:LINEAR EXPT-<-1-ONE))
 (30 2 (:REWRITE |(+ (+ x y) z)|))
 (25 13 (:REWRITE DEFAULT-TIMES-1))
 (13 13 (:REWRITE ODD-EXPT-THM))
 (13 13 (:REWRITE |(< 0 (/ x))|))
 (13 13 (:REWRITE |(< 0 (* x y))|))
 (11 11 (:REWRITE |(< (/ x) 0)|))
 (11 7
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (11 7
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (10 1
     (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (10 1 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (7 7 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (7 7
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (7 7 (:REWRITE REDUCE-INTEGERP-+))
 (7 7
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (7 7 (:REWRITE INTEGERP-MINUS-X))
 (7 7
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (7 7 (:REWRITE |(equal c (/ x))|))
 (7 7 (:REWRITE |(equal c (- x))|))
 (7 7 (:REWRITE |(equal (/ x) c)|))
 (7 7 (:REWRITE |(equal (/ x) (/ y))|))
 (7 7 (:REWRITE |(equal (- x) c)|))
 (7 7 (:REWRITE |(equal (- x) (- y))|))
 (7 7 (:META META-INTEGERP-CORRECT))
 (6 6 (:REWRITE |(< y (+ (- c) x))|))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (3 3 (:REWRITE |(< (+ (- c) x) y)|)))
(RTL::R-EXACTP-50
 (1330 2 (:REWRITE RTL::R-EXACTP-6))
 (1078 26
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (554 18 (:REWRITE |(< (- x) c)|))
 (420 6 (:LINEAR EXPT->=-1-ONE))
 (148 49 (:REWRITE DEFAULT-PLUS-2))
 (138 6 (:LINEAR EXPT-<=-1-TWO))
 (138 6 (:LINEAR EXPT-<-1-TWO))
 (90
  90
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (90 90
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (90 90
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (90 90
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (64 9 (:REWRITE DEFAULT-TIMES-1))
 (63 9 (:REWRITE DEFAULT-TIMES-2))
 (62 26 (:REWRITE DEFAULT-LESS-THAN-1))
 (59 49 (:REWRITE DEFAULT-PLUS-1))
 (48 12 (:REWRITE DEFAULT-MINUS))
 (44 26 (:REWRITE DEFAULT-LESS-THAN-2))
 (36 18 (:REWRITE |(< (- x) (- y))|))
 (26 26 (:REWRITE THE-FLOOR-BELOW))
 (26 26 (:REWRITE THE-FLOOR-ABOVE))
 (26 26
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (26 26
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (26 8 (:REWRITE |(- (- x))|))
 (18 18
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (18 18
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (18 18
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (18 18
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (18 18 (:REWRITE |(< c (- x))|))
 (18 18
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (18 18
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (18 18
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (18 18
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (18 18 (:REWRITE |(< (/ x) (/ y))|))
 (16 16
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (15 15 (:REWRITE DEFAULT-EXPT-2))
 (15 15 (:REWRITE DEFAULT-EXPT-1))
 (15 15 (:REWRITE |(expt 1/c n)|))
 (15 15 (:REWRITE |(expt (- x) n)|))
 (12 12
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (12 12
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (12 12
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (12 12
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (11 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (10 10 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (10 10
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (10 10 (:REWRITE INTEGERP-<-CONSTANT))
 (10 10 (:REWRITE CONSTANT-<-INTEGERP))
 (8 8 (:REWRITE SIMPLIFY-SUMS-<))
 (8 8
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (8 8 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (8 8 (:REWRITE |(< (+ c/d x) y)|))
 (8 8 (:REWRITE |(< (* x y) 0)|))
 (6 6 (:LINEAR EXPT-X->=-X))
 (6 6 (:LINEAR EXPT-X->-X))
 (6 6 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (6 6 (:LINEAR EXPT-LINEAR-UPPER-<))
 (6 6 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (6 6 (:LINEAR EXPT-LINEAR-LOWER-<))
 (6 6 (:LINEAR EXPT->=-1-TWO))
 (6 6 (:LINEAR EXPT->-1-TWO))
 (6 6 (:LINEAR EXPT->-1-ONE))
 (6 6 (:LINEAR EXPT-<=-1-ONE))
 (6 6 (:LINEAR EXPT-<-1-ONE))
 (3 1 (:REWRITE RTL::BVECP-EXACTP))
 (2 2 (:TYPE-PRESCRIPTION RTL::BVECP))
 (2 2 (:REWRITE ODD-EXPT-THM))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:REWRITE |(< 0 (* x y))|))
 (2 2 (:REWRITE |(< (/ x) 0)|))
 (2 1
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (2 1
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (1 1
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (1 1 (:REWRITE REDUCE-INTEGERP-+))
 (1 1
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (1 1 (:REWRITE INTEGERP-MINUS-X))
 (1 1
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (1 1 (:REWRITE |(equal c (/ x))|))
 (1 1 (:REWRITE |(equal c (- x))|))
 (1 1 (:REWRITE |(equal (/ x) c)|))
 (1 1 (:REWRITE |(equal (/ x) (/ y))|))
 (1 1 (:REWRITE |(equal (- x) c)|))
 (1 1 (:REWRITE |(equal (- x) (- y))|))
 (1 1 (:META META-INTEGERP-CORRECT)))
(RTL::R-EXACTP-51
 (386 34
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (298
  298
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (298 298
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (298
     298
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (298 298
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (298 298
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (224 26
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (224 26
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (133 19 (:REWRITE |(< (- x) c)|))
 (129 21 (:REWRITE DEFAULT-TIMES-2))
 (124 2 (:LINEAR EXPT->=-1-ONE))
 (122 2 (:LINEAR EXPT-<=-1-TWO))
 (122 2 (:LINEAR EXPT-<-1-TWO))
 (120 2 (:LINEAR EXPT->-1-ONE))
 (119 2 (:LINEAR EXPT-X->=-X))
 (119 2 (:LINEAR EXPT-X->-X))
 (63 61 (:REWRITE DEFAULT-PLUS-1))
 (61 61 (:REWRITE DEFAULT-PLUS-2))
 (51 51 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (51 51 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (51 51 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (34 34 (:REWRITE THE-FLOOR-BELOW))
 (34 34 (:REWRITE THE-FLOOR-ABOVE))
 (34 34
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (34 34
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (34 34 (:REWRITE DEFAULT-LESS-THAN-2))
 (34 34 (:REWRITE DEFAULT-LESS-THAN-1))
 (30 30 (:REWRITE DEFAULT-MINUS))
 (28 28
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (28 28
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (28 28
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (28 28
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (28 28
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (28 28
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (28 28
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (28 28
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (28 28 (:REWRITE |(< (/ x) (/ y))|))
 (28 28 (:REWRITE |(< (- x) (- y))|))
 (27 21 (:REWRITE DEFAULT-TIMES-1))
 (26 26
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (26 26
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (20 20
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (16 16 (:REWRITE DEFAULT-EXPT-2))
 (16 16 (:REWRITE DEFAULT-EXPT-1))
 (16 16 (:REWRITE |(expt 1/c n)|))
 (16 16 (:REWRITE |(expt (- x) n)|))
 (15 15
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (15 15
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (15 15 (:REWRITE INTEGERP-<-CONSTANT))
 (15 15 (:REWRITE CONSTANT-<-INTEGERP))
 (14 14 (:REWRITE SIMPLIFY-SUMS-<))
 (10 10 (:REWRITE |(< 0 (* x y))|))
 (9 9 (:REWRITE |(< (* x y) 0)|))
 (8 8 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (8 8 (:REWRITE |(< 0 (/ x))|))
 (7 7 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (7 7
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (7 7
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (7 7 (:REWRITE |(equal c (/ x))|))
 (7 7 (:REWRITE |(equal c (- x))|))
 (7 7 (:REWRITE |(equal (/ x) c)|))
 (7 7 (:REWRITE |(equal (/ x) (/ y))|))
 (7 7 (:REWRITE |(equal (- x) (- y))|))
 (7 7 (:REWRITE |(< (/ x) 0)|))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (5 5 (:REWRITE |(< x (+ c/d y))|))
 (4 4
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (4 4
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (3 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2 (:REWRITE REDUCE-INTEGERP-+))
 (2 2 (:REWRITE INTEGERP-MINUS-X))
 (2 2 (:REWRITE |(equal (+ (- c) x) y)|))
 (2 2 (:REWRITE |(< (+ c/d x) y)|))
 (2 2 (:META META-INTEGERP-CORRECT))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-ONE))
 (1 1 (:REWRITE |(< y (+ (- c) x))|)))
(RTL::R-EXACTP-52
 (6588 25 (:REWRITE RTL::R-EXACTP-6))
 (4219 202
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (3826
  3826
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (3826
      3826
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (3826
     3826
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (3826 3826
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (3826 3826
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (3615 316 (:REWRITE DEFAULT-PLUS-2))
 (3084 717
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (3078 711
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (2571 208
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (2328 717
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (2268 711
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (1855 316 (:REWRITE DEFAULT-PLUS-1))
 (1844 1844
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (1844 1844
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (1844 1844
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (1844 1844
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (1415 20 (:REWRITE |(< 0 (/ x))|))
 (1154 185
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (1143 211 (:REWRITE DEFAULT-LESS-THAN-1))
 (953 95 (:REWRITE DEFAULT-TIMES-2))
 (933 211 (:REWRITE DEFAULT-LESS-THAN-2))
 (915 122 (:REWRITE DEFAULT-MINUS))
 (420 30 (:REWRITE |(+ c (+ d x))|))
 (378 14
      (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (369 38 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (364 14
      (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (362 150 (:REWRITE SIMPLIFY-SUMS-<))
 (288 6 (:REWRITE |(* y (* x z))|))
 (250 196
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (234 18 (:REWRITE ODD-EXPT-THM))
 (220 196 (:REWRITE |(< (- x) (- y))|))
 (211 211 (:REWRITE THE-FLOOR-BELOW))
 (211 211 (:REWRITE THE-FLOOR-ABOVE))
 (210 202
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (196 196
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (196 196
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (196 196
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (196 196
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (196 196
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (196 196
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (196 196
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (196 196 (:REWRITE |(< (/ x) (/ y))|))
 (190 190 (:REWRITE INTEGERP-<-CONSTANT))
 (190 190 (:REWRITE CONSTANT-<-INTEGERP))
 (190 190 (:REWRITE |(< c (- x))|))
 (190 190 (:REWRITE |(< (- x) c)|))
 (179 8 (:LINEAR EXPT->-1-ONE))
 (148 16
      (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (142 10 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (126 8 (:LINEAR EXPT->=-1-ONE))
 (121 8 (:LINEAR EXPT-X->=-X))
 (121 8 (:LINEAR EXPT-X->-X))
 (113 113
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (108 36 (:REWRITE RTL::BVECP-EXACTP))
 (96 24 (:REWRITE RATIONALP-X))
 (95 95 (:REWRITE DEFAULT-TIMES-1))
 (94 85 (:REWRITE DEFAULT-EXPT-2))
 (86 62 (:REWRITE INTEGERP-MINUS-X))
 (85 85 (:REWRITE DEFAULT-EXPT-1))
 (85 85 (:REWRITE |(expt 1/c n)|))
 (85 85 (:REWRITE |(expt (- x) n)|))
 (83 29 (:REWRITE DEFAULT-DIVIDE))
 (72 72 (:TYPE-PRESCRIPTION RTL::BVECP))
 (62 62 (:REWRITE REDUCE-INTEGERP-+))
 (62 62 (:META META-INTEGERP-CORRECT))
 (60 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (60 6 (:REWRITE |(* a (/ a) b)|))
 (43 43 (:REWRITE |(* (- x) y)|))
 (42 6 (:REWRITE |(/ (expt x n))|))
 (40 40 (:REWRITE |(< (+ c/d x) y)|))
 (34 34 (:REWRITE |(< (+ (- c) x) y)|))
 (32 32 (:REWRITE |(< y (+ (- c) x))|))
 (32 32 (:REWRITE |(< x (+ c/d y))|))
 (24 24 (:REWRITE REDUCE-RATIONALP-+))
 (24 24 (:REWRITE REDUCE-RATIONALP-*))
 (24 24 (:REWRITE RATIONALP-MINUS-X))
 (24 24 (:META META-RATIONALP-CORRECT))
 (23 23
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (20 20 (:REWRITE |(< 0 (* x y))|))
 (17 17 (:REWRITE |(< (* x y) 0)|))
 (16 16
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (16 16
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (16 16
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (14 14
     (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (14 14
     (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (12 12
     (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (11 11
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (11 11
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (11 11 (:REWRITE |(< (/ x) 0)|))
 (10 10 (:LINEAR EXPT-LINEAR-LOWER-<))
 (9 9 (:REWRITE FOLD-CONSTS-IN-+))
 (8 8 (:LINEAR EXPT-LINEAR-UPPER-<))
 (8 8 (:LINEAR EXPT->=-1-TWO))
 (8 8 (:LINEAR EXPT->-1-TWO))
 (8 8 (:LINEAR EXPT-<=-1-ONE))
 (8 8 (:LINEAR EXPT-<-1-ONE))
 (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (6 6
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (6 3
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (6 3
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (3 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (3 3
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (3 3
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (3 3
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (3 3 (:REWRITE |(equal c (/ x))|))
 (3 3 (:REWRITE |(equal c (- x))|))
 (3 3 (:REWRITE |(equal (/ x) c)|))
 (3 3 (:REWRITE |(equal (/ x) (/ y))|))
 (3 3 (:REWRITE |(equal (- x) c)|))
 (3 3 (:REWRITE |(equal (- x) (- y))|))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON)))
(RTL::R-EXACTP-53
 (8669 26 (:REWRITE RTL::R-EXACTP-6))
 (6382 269
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (4230 248 (:REWRITE |(< (- x) c)|))
 (3443
  3443
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (3443
      3443
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (3443
     3443
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (3443 3443
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (3443 3443
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (2357 32 (:REWRITE |(< 0 (/ x))|))
 (2223 408 (:REWRITE DEFAULT-PLUS-2))
 (1846 1846
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (1846 1846
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (1846 1846
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (1846 1846
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (1232 408 (:REWRITE DEFAULT-PLUS-1))
 (956 208
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (937 270 (:REWRITE DEFAULT-LESS-THAN-2))
 (747 270 (:REWRITE DEFAULT-LESS-THAN-1))
 (621 149 (:REWRITE DEFAULT-MINUS))
 (413 258 (:REWRITE |(< (- x) (- y))|))
 (354 258
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (340 164 (:REWRITE SIMPLIFY-SUMS-<))
 (310 90
      (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (304 45 (:LINEAR EXPT->-1-ONE))
 (293 248 (:REWRITE |(< c (- x))|))
 (284 45 (:LINEAR EXPT->=-1-ONE))
 (270 270 (:REWRITE THE-FLOOR-BELOW))
 (270 270 (:REWRITE THE-FLOOR-ABOVE))
 (270 10
      (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (269 269
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (269 269
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (266 46 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (263 27 (:REWRITE ODD-EXPT-THM))
 (260 10
      (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (258 258
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (258 258
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (258 258
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (258 258
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (258 258
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (258 258
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (258 258
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (258 258 (:REWRITE |(< (/ x) (/ y))|))
 (247 34 (:REWRITE |(+ c (+ d x))|))
 (240 231 (:REWRITE DEFAULT-EXPT-2))
 (237 237 (:REWRITE INTEGERP-<-CONSTANT))
 (237 237 (:REWRITE CONSTANT-<-INTEGERP))
 (233 51 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (231 231 (:REWRITE DEFAULT-EXPT-1))
 (231 231 (:REWRITE |(expt 1/c n)|))
 (231 231 (:REWRITE |(expt (- x) n)|))
 (210 45 (:LINEAR EXPT-X->=-X))
 (210 45 (:LINEAR EXPT-X->-X))
 (187 63 (:REWRITE RTL::BVECP-EXACTP))
 (139 49 (:REWRITE DEFAULT-DIVIDE))
 (124 124 (:TYPE-PRESCRIPTION RTL::BVECP))
 (120 120
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (105 85 (:REWRITE INTEGERP-MINUS-X))
 (96 24 (:REWRITE RATIONALP-X))
 (90 90
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (90 90
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (90 90
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (85 85 (:REWRITE REDUCE-INTEGERP-+))
 (85 85 (:META META-INTEGERP-CORRECT))
 (70 10 (:REWRITE |(/ (expt x n))|))
 (66 17
     (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (52 52 (:REWRITE |(< (+ c/d x) y)|))
 (46 46 (:LINEAR EXPT-LINEAR-LOWER-<))
 (45 45 (:LINEAR EXPT-LINEAR-UPPER-<))
 (45 45 (:LINEAR EXPT->=-1-TWO))
 (45 45 (:LINEAR EXPT->-1-TWO))
 (45 45 (:LINEAR EXPT-<=-1-ONE))
 (45 45 (:LINEAR EXPT-<-1-ONE))
 (41 41 (:REWRITE |(< (+ (- c) x) y)|))
 (39 39
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (39 39 (:REWRITE DEFAULT-TIMES-2))
 (39 39 (:REWRITE DEFAULT-TIMES-1))
 (37 37 (:REWRITE |(< y (+ (- c) x))|))
 (37 37 (:REWRITE |(< x (+ c/d y))|))
 (34 34 (:REWRITE |(< (* x y) 0)|))
 (33 33 (:REWRITE |(< (/ x) 0)|))
 (33 10
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (32 32 (:REWRITE |(< 0 (* x y))|))
 (28 7 (:REWRITE |(integerp (- x))|))
 (24 24 (:REWRITE REDUCE-RATIONALP-+))
 (24 24 (:REWRITE REDUCE-RATIONALP-*))
 (24 24 (:REWRITE RATIONALP-MINUS-X))
 (24 24 (:META META-RATIONALP-CORRECT))
 (19 19
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (17 17
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (17 17
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (10 10
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (10 10
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (10 10
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (10 10 (:REWRITE |(equal c (/ x))|))
 (10 10 (:REWRITE |(equal c (- x))|))
 (10 10 (:REWRITE |(equal (/ x) c)|))
 (10 10 (:REWRITE |(equal (/ x) (/ y))|))
 (10 10 (:REWRITE |(equal (- x) c)|))
 (10 10 (:REWRITE |(equal (- x) (- y))|))
 (10 10
     (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (10 10
     (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (9 9 (:REWRITE FOLD-CONSTS-IN-+))
 (8 8 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (5 5 (:REWRITE |(- (* c x))|))
 (4 4 (:REWRITE |(equal (+ (- c) x) y)|)))
(RTL::R-EXACTP-54
 (598 598
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (598 598
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (598 598
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (598 598
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (476 6 (:REWRITE RTL::R-EXACTP-6))
 (414
  414
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (414 414
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (414
     414
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (414 414
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (414 414
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (394 71 (:REWRITE DEFAULT-PLUS-2))
 (225 52
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (181 60 (:REWRITE DEFAULT-LESS-THAN-2))
 (148 60 (:REWRITE DEFAULT-LESS-THAN-1))
 (144 26 (:REWRITE DEFAULT-MINUS))
 (128 71 (:REWRITE DEFAULT-PLUS-1))
 (111 43 (:REWRITE SIMPLIFY-SUMS-<))
 (108 4
      (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (104 4
      (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (100 10
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (100 10
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (85 5 (:REWRITE ODD-EXPT-THM))
 (83 59
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (76 22 (:REWRITE DEFAULT-TIMES-2))
 (67 59 (:REWRITE |(< (- x) (- y))|))
 (60 60 (:REWRITE THE-FLOOR-BELOW))
 (60 60 (:REWRITE THE-FLOOR-ABOVE))
 (60 22 (:REWRITE RTL::BVECP-EXACTP))
 (59 59
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (59 59
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (59 59
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (59 59 (:REWRITE INTEGERP-<-CONSTANT))
 (59 59 (:REWRITE CONSTANT-<-INTEGERP))
 (59 59
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (59 59
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (59 59
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (59 59
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (59 59 (:REWRITE |(< c (- x))|))
 (59 59
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (59 59
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (59 59
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (59 59 (:REWRITE |(< (/ x) (/ y))|))
 (59 59 (:REWRITE |(< (- x) c)|))
 (49 22 (:REWRITE DEFAULT-TIMES-1))
 (41 1 (:LINEAR EXPT->=-1-ONE))
 (40 1 (:LINEAR EXPT->-1-ONE))
 (40 1 (:LINEAR EXPT-<=-1-TWO))
 (39 1 (:LINEAR EXPT-<-1-TWO))
 (38 38 (:TYPE-PRESCRIPTION RTL::BVECP))
 (36 1 (:LINEAR EXPT-X->=-X))
 (36 1 (:LINEAR EXPT-X->-X))
 (31 23 (:REWRITE INTEGERP-MINUS-X))
 (28 7 (:REWRITE RATIONALP-X))
 (23 23 (:REWRITE REDUCE-INTEGERP-+))
 (23 23 (:META META-INTEGERP-CORRECT))
 (21 21
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (18 10 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (12 12
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (12 5 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (11 11
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (11 11 (:REWRITE DEFAULT-DIVIDE))
 (11 11 (:REWRITE |(< (+ c/d x) y)|))
 (11 11 (:REWRITE |(< (+ (- c) x) y)|))
 (11 8 (:REWRITE DEFAULT-EXPT-2))
 (10 10
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (10 10
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (9 9 (:REWRITE |(< y (+ (- c) x))|))
 (9 9 (:REWRITE |(< x (+ c/d y))|))
 (9 9 (:REWRITE |(+ c (+ d x))|))
 (8 8 (:REWRITE DEFAULT-EXPT-1))
 (8 8 (:REWRITE |(expt 1/c n)|))
 (8 8 (:REWRITE |(expt (- x) n)|))
 (7 7 (:REWRITE REDUCE-RATIONALP-+))
 (7 7 (:REWRITE REDUCE-RATIONALP-*))
 (7 7 (:REWRITE RATIONALP-MINUS-X))
 (7 7 (:REWRITE |(< (/ x) 0)|))
 (7 7 (:REWRITE |(< (* x y) 0)|))
 (7 7 (:META META-RATIONALP-CORRECT))
 (4 4
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (4 4
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (4 1 (:REWRITE |(integerp (- x))|))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (3 3 (:REWRITE FOLD-CONSTS-IN-+))
 (3 3 (:REWRITE |(- (* c x))|))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:REWRITE |(< 0 (* x y))|))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (1 1
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (1 1
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (1 1
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (1 1
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (1 1
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (1 1 (:REWRITE |(equal c (/ x))|))
 (1 1 (:REWRITE |(equal c (- x))|))
 (1 1 (:REWRITE |(equal (/ x) c)|))
 (1 1 (:REWRITE |(equal (/ x) (/ y))|))
 (1 1 (:REWRITE |(equal (- x) c)|))
 (1 1 (:REWRITE |(equal (- x) (- y))|))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<))
 (1 1 (:LINEAR EXPT->=-1-TWO))
 (1 1 (:LINEAR EXPT->-1-TWO))
 (1 1 (:LINEAR EXPT-<=-1-ONE))
 (1 1 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-EXACTP-55)
(RTL::R-EXACTP-56
     (26 18 (:REWRITE DEFAULT-TIMES-2))
     (18 18 (:REWRITE DEFAULT-TIMES-1))
     (14 8
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (12 3 (:REWRITE RATIONALP-X))
     (10 10 (:REWRITE THE-FLOOR-BELOW))
     (10 10 (:REWRITE THE-FLOOR-ABOVE))
     (10 10
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (10 10
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (10 10
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (10 10 (:REWRITE DEFAULT-LESS-THAN-2))
     (10 10 (:REWRITE DEFAULT-LESS-THAN-1))
     (8 8 (:REWRITE INTEGERP-<-CONSTANT))
     (8 8 (:REWRITE CONSTANT-<-INTEGERP))
     (8 8
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (8 8
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (8 8
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (8 8
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (8 8 (:REWRITE |(< c (- x))|))
     (8 8
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (8 8
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (8 8
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (8 8 (:REWRITE |(< (/ x) (/ y))|))
     (8 8 (:REWRITE |(< (- x) c)|))
     (8 8 (:REWRITE |(< (- x) (- y))|))
     (6 6 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (6 6
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (5 5 (:REWRITE REDUCE-INTEGERP-+))
     (5 5 (:REWRITE INTEGERP-MINUS-X))
     (5 5 (:META META-INTEGERP-CORRECT))
     (4 4 (:REWRITE SIMPLIFY-SUMS-<))
     (4 4 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (3 3 (:REWRITE REDUCE-RATIONALP-+))
     (3 3 (:REWRITE REDUCE-RATIONALP-*))
     (3 3 (:REWRITE RATIONALP-MINUS-X))
     (3 3 (:META META-RATIONALP-CORRECT))
     (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (2 2
        (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (2 2
        (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (2 2 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (2 2 (:REWRITE |(< 0 (* x y))|))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (1 1 (:REWRITE |(< (/ x) 0)|))
     (1 1 (:REWRITE |(< (* x y) 0)|)))
(RTL::R-EXACTP-57)
(RTL::R-EXACTP-58
 (1390
  1390
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1390
      1390
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1390
     1390
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1390 1390
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1390 1390
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (456 78 (:REWRITE DEFAULT-TIMES-2))
 (371 139
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (277 142 (:REWRITE DEFAULT-LESS-THAN-2))
 (237 120 (:REWRITE SIMPLIFY-SUMS-<))
 (237 120
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (237 120
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (184 133
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (178 178 (:REWRITE DEFAULT-PLUS-2))
 (178 178 (:REWRITE DEFAULT-PLUS-1))
 (142 142 (:REWRITE THE-FLOOR-BELOW))
 (142 142 (:REWRITE THE-FLOOR-ABOVE))
 (142 142 (:REWRITE DEFAULT-LESS-THAN-1))
 (139 139
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (139 139
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (133 133
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (133 133
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (133 133
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (133 133
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (133 133 (:REWRITE |(< c (- x))|))
 (133 133
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (133 133
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (133 133
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (133 133 (:REWRITE |(< (/ x) (/ y))|))
 (133 133 (:REWRITE |(< (- x) (- y))|))
 (128 32 (:REWRITE RATIONALP-X))
 (122 122 (:REWRITE INTEGERP-<-CONSTANT))
 (122 122 (:REWRITE CONSTANT-<-INTEGERP))
 (99 78 (:REWRITE DEFAULT-TIMES-1))
 (88 16 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (88 16
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (88 16
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (84 84
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (84 84 (:REWRITE NORMALIZE-ADDENDS))
 (80 2 (:LINEAR EXPT->=-1-ONE))
 (80 2 (:LINEAR EXPT-<=-1-TWO))
 (78 2 (:LINEAR EXPT->-1-ONE))
 (78 2 (:LINEAR EXPT-<-1-TWO))
 (77 77 (:REWRITE DEFAULT-EXPT-2))
 (77 77 (:REWRITE DEFAULT-EXPT-1))
 (77 77 (:REWRITE |(expt 1/c n)|))
 (77 77 (:REWRITE |(expt (- x) n)|))
 (77 2 (:LINEAR EXPT-X->=-X))
 (77 2 (:LINEAR EXPT-X->-X))
 (76 76 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (76 76 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (76 76 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (74 74 (:REWRITE REDUCE-INTEGERP-+))
 (74 74 (:REWRITE INTEGERP-MINUS-X))
 (74 74 (:META META-INTEGERP-CORRECT))
 (59 13 (:REWRITE ODD-EXPT-THM))
 (37 37 (:REWRITE |(< (* x y) 0)|))
 (35 35 (:REWRITE |(< (/ x) 0)|))
 (34 34
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (34 34
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (32 32 (:REWRITE REDUCE-RATIONALP-+))
 (32 32 (:REWRITE REDUCE-RATIONALP-*))
 (32 32 (:REWRITE RATIONALP-MINUS-X))
 (32 32 (:META META-RATIONALP-CORRECT))
 (31 31 (:REWRITE DEFAULT-MINUS))
 (28 28
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (28 28
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (28 28 (:REWRITE |(equal c (/ x))|))
 (28 28 (:REWRITE |(equal c (- x))|))
 (28 28 (:REWRITE |(equal (/ x) c)|))
 (28 28 (:REWRITE |(equal (/ x) (/ y))|))
 (28 28 (:REWRITE |(equal (- x) c)|))
 (28 28 (:REWRITE |(equal (- x) (- y))|))
 (28 7 (:REWRITE |(integerp (- x))|))
 (21 21 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (19 19 (:REWRITE |(< 0 (* x y))|))
 (17 17
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (17 17
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (17 17 (:REWRITE |(< 0 (/ x))|))
 (16 16
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (12 12 (:REWRITE |(equal (+ (- c) x) y)|))
 (12 12 (:REWRITE |(< x (+ c/d y))|))
 (11 11
     (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (8 8 (:REWRITE |(< y (+ (- c) x))|))
 (8 8 (:REWRITE |(- (* c x))|))
 (4 4 (:REWRITE |(equal x (if a b c))|))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (2 2 (:REWRITE |(< (+ c/d x) y)|))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-EXACTP-59
 (1576 19 (:REWRITE RTL::R-EXACTP-6))
 (911
  911
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (911 911
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (911
     911
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (911 911
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (911 911
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (911 911
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (864 864
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (864 864
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (864 864
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (864 864
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (567 127
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (556 192 (:REWRITE DEFAULT-PLUS-2))
 (481 133 (:REWRITE DEFAULT-LESS-THAN-2))
 (351 13
      (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (341 133 (:REWRITE DEFAULT-LESS-THAN-1))
 (338 13
      (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (319 192 (:REWRITE DEFAULT-PLUS-1))
 (303 103 (:REWRITE SIMPLIFY-SUMS-<))
 (182 14 (:REWRITE ODD-EXPT-THM))
 (156 129
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (145 129 (:REWRITE |(< (- x) (- y))|))
 (133 133 (:REWRITE THE-FLOOR-BELOW))
 (133 133 (:REWRITE THE-FLOOR-ABOVE))
 (129 129
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (129 129
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (129 129
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (129 129 (:REWRITE INTEGERP-<-CONSTANT))
 (129 129 (:REWRITE CONSTANT-<-INTEGERP))
 (129 129
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (129 129
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (129 129
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (129 129
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (129 129 (:REWRITE |(< c (- x))|))
 (129 129
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (129 129
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (129 129
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (129 129 (:REWRITE |(< (/ x) (/ y))|))
 (129 129 (:REWRITE |(< (- x) c)|))
 (82 2 (:LINEAR EXPT-<=-1-TWO))
 (80 2 (:LINEAR EXPT->=-1-ONE))
 (80 2 (:LINEAR EXPT-<-1-TWO))
 (78 2 (:LINEAR EXPT->-1-ONE))
 (76 44 (:REWRITE DEFAULT-MINUS))
 (70 2 (:LINEAR EXPT-X->=-X))
 (70 2 (:LINEAR EXPT-X->-X))
 (56 56
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (55 39 (:REWRITE INTEGERP-MINUS-X))
 (48 12 (:REWRITE RATIONALP-X))
 (41 33 (:REWRITE DEFAULT-TIMES-2))
 (40 24 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (39 39 (:REWRITE REDUCE-INTEGERP-+))
 (39 39 (:META META-INTEGERP-CORRECT))
 (36 12 (:REWRITE RTL::BVECP-EXACTP))
 (33 33 (:REWRITE DEFAULT-TIMES-1))
 (28 28
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (28 28 (:REWRITE |(< (+ c/d x) y)|))
 (28 28 (:REWRITE |(< (+ (- c) x) y)|))
 (24 24 (:TYPE-PRESCRIPTION RTL::BVECP))
 (22 22
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (22 22 (:REWRITE DEFAULT-DIVIDE))
 (22 22 (:REWRITE |(< y (+ (- c) x))|))
 (22 22 (:REWRITE |(< x (+ c/d y))|))
 (20 10 (:REWRITE DEFAULT-EXPT-2))
 (14 14
     (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (14 14 (:REWRITE |(< (/ x) 0)|))
 (14 14 (:REWRITE |(< (* x y) 0)|))
 (13 13
     (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (13 13
     (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (12 12 (:REWRITE REDUCE-RATIONALP-+))
 (12 12 (:REWRITE REDUCE-RATIONALP-*))
 (12 12 (:REWRITE RATIONALP-MINUS-X))
 (12 12 (:REWRITE FOLD-CONSTS-IN-+))
 (12 12 (:META META-RATIONALP-CORRECT))
 (10 10 (:REWRITE DEFAULT-EXPT-1))
 (10 10 (:REWRITE |(expt 1/c n)|))
 (10 10 (:REWRITE |(expt (- x) n)|))
 (9 9 (:REWRITE |(- (* c x))|))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (4 4 (:REWRITE |(< 0 (/ x))|))
 (4 4 (:REWRITE |(< 0 (* x y))|))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-EXACTP-60
 (4982 57 (:REWRITE RTL::R-EXACTP-6))
 (3561 477
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (2764 2764
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (2764 2764
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (2764 2764
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (2764 2764
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (2081
  2081
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (2081
      2081
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (2081
     2081
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (2081 2081
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (2081 2081
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (2071 1005 (:REWRITE DEFAULT-PLUS-2))
 (1408 424
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (1359 1005 (:REWRITE DEFAULT-PLUS-1))
 (1213 488 (:REWRITE DEFAULT-LESS-THAN-2))
 (987 488 (:REWRITE DEFAULT-LESS-THAN-1))
 (918 34
      (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (884 34
      (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (753 309 (:REWRITE SIMPLIFY-SUMS-<))
 (675 6 (:LINEAR EXPT-<=-1-TWO))
 (665 6 (:LINEAR EXPT-<-1-TWO))
 (659 6 (:LINEAR EXPT->=-1-ONE))
 (649 6 (:LINEAR EXPT->-1-ONE))
 (647 6 (:LINEAR EXPT-X->=-X))
 (647 6 (:LINEAR EXPT-X->-X))
 (613 125 (:REWRITE |(< (+ (- c) x) y)|))
 (513 429
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (488 488 (:REWRITE THE-FLOOR-BELOW))
 (488 488 (:REWRITE THE-FLOOR-ABOVE))
 (477 477
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (477 477
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (465 429 (:REWRITE |(< (- x) (- y))|))
 (429 429 (:REWRITE INTEGERP-<-CONSTANT))
 (429 429 (:REWRITE CONSTANT-<-INTEGERP))
 (429 429
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (429 429
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (429 429
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (429 429
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (429 429 (:REWRITE |(< c (- x))|))
 (429 429
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (429 429
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (429 429
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (429 429 (:REWRITE |(< (/ x) (/ y))|))
 (429 429 (:REWRITE |(< (- x) c)|))
 (422 94 (:REWRITE |(< y (+ (- c) x))|))
 (382 26 (:REWRITE ODD-EXPT-THM))
 (263 263
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (220 148 (:REWRITE DEFAULT-MINUS))
 (179 95 (:REWRITE DEFAULT-TIMES-2))
 (161 125 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (156 39 (:REWRITE RATIONALP-X))
 (142 106 (:REWRITE INTEGERP-MINUS-X))
 (133 133 (:REWRITE |(< (+ c/d x) y)|))
 (126 42 (:REWRITE RTL::BVECP-EXACTP))
 (114 114 (:REWRITE |(< x (+ c/d y))|))
 (106 106 (:REWRITE REDUCE-INTEGERP-+))
 (106 106 (:META META-INTEGERP-CORRECT))
 (99 95 (:REWRITE DEFAULT-TIMES-1))
 (84 84 (:TYPE-PRESCRIPTION RTL::BVECP))
 (65 65 (:REWRITE FOLD-CONSTS-IN-+))
 (54 54
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (54 54 (:REWRITE DEFAULT-DIVIDE))
 (54 27 (:REWRITE DEFAULT-EXPT-2))
 (49 49 (:REWRITE |(< (* x y) 0)|))
 (41 41 (:REWRITE |(< (/ x) 0)|))
 (39 39 (:REWRITE REDUCE-RATIONALP-+))
 (39 39 (:REWRITE REDUCE-RATIONALP-*))
 (39 39 (:REWRITE RATIONALP-MINUS-X))
 (39 39 (:META META-RATIONALP-CORRECT))
 (38 38 (:REWRITE |(- (* c x))|))
 (34 34
     (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (34 34
     (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (27 27 (:REWRITE DEFAULT-EXPT-1))
 (27 27 (:REWRITE |(expt 1/c n)|))
 (27 27 (:REWRITE |(expt (- x) n)|))
 (26 26
     (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (26 26 (:REWRITE |(< 0 (* x y))|))
 (14 14 (:REWRITE |(< 0 (/ x))|))
 (12 12
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (12 12
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (12 12
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (12 12
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (12 12 (:REWRITE |(equal c (/ x))|))
 (12 12 (:REWRITE |(equal c (- x))|))
 (12 12 (:REWRITE |(equal (/ x) c)|))
 (12 12 (:REWRITE |(equal (/ x) (/ y))|))
 (12 12 (:REWRITE |(equal (- x) c)|))
 (12 12 (:REWRITE |(equal (- x) (- y))|))
 (12 12
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (12 12
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (12 12
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (6 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (6 6 (:REWRITE |(equal (+ (- c) x) y)|))
 (6 6 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (6 6 (:LINEAR EXPT-LINEAR-UPPER-<))
 (6 6 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (6 6 (:LINEAR EXPT-LINEAR-LOWER-<))
 (6 6 (:LINEAR EXPT->=-1-TWO))
 (6 6 (:LINEAR EXPT->-1-TWO))
 (6 6 (:LINEAR EXPT-<=-1-ONE))
 (6 6 (:LINEAR EXPT-<-1-ONE))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON)))
(RTL::R-EXACTP-61
 (21304 100 (:REWRITE RTL::R-EXACTP-6))
 (10375 523
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (2806 496 (:REWRITE DEFAULT-TIMES-2))
 (2670 531 (:REWRITE DEFAULT-LESS-THAN-1))
 (2531 2531
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (2531 2531
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (2531 2531
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (2531 2531
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (2510 1646
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (2142 414
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
 (2070 23
       (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (1914 454
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (1646 1646
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (1620 1620
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (1512 1512
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (1332 324
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
 (1315 59 (:REWRITE |(* y (* x z))|))
 (1278 414
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4E))
 (1278 414
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
 (1251 683 (:REWRITE DEFAULT-PLUS-2))
 (1104 424
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (954 36 (:REWRITE |(* (* x y) z)|))
 (940 683 (:REWRITE DEFAULT-PLUS-1))
 (782 531 (:REWRITE DEFAULT-LESS-THAN-2))
 (716 431 (:REWRITE INTEGERP-<-CONSTANT))
 (640 496 (:REWRITE DEFAULT-TIMES-1))
 (564
  564
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (564 564
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (564
     564
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (564 564
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (564 564
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (564 564
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (561 347 (:REWRITE SIMPLIFY-SUMS-<))
 (531 531 (:REWRITE THE-FLOOR-BELOW))
 (531 531 (:REWRITE THE-FLOOR-ABOVE))
 (515 434 (:REWRITE |(< (- x) c)|))
 (500 454
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (477 35
      (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (470 434
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (460 35
      (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (446 434 (:REWRITE |(< (- x) (- y))|))
 (434 434
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (434 434
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (434 434
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (434 434
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (434 434 (:REWRITE |(< c (- x))|))
 (434 434
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (434 434
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (434 434
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (434 434 (:REWRITE |(< (/ x) (/ y))|))
 (431 431 (:REWRITE CONSTANT-<-INTEGERP))
 (397 52 (:REWRITE |(* y x)|))
 (377 4 (:LINEAR EXPT-<=-1-TWO))
 (371 4 (:LINEAR EXPT-<-1-TWO))
 (369 4 (:LINEAR EXPT->=-1-ONE))
 (363 4 (:LINEAR EXPT->-1-ONE))
 (316 12 (:REWRITE |(* x (+ y z))|))
 (315 4 (:LINEAR EXPT-X->=-X))
 (315 4 (:LINEAR EXPT-X->-X))
 (285 69 (:REWRITE |(* a (/ a) b)|))
 (254 254
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (250 86 (:REWRITE |(< (+ (- c) x) y)|))
 (240 76 (:REWRITE |(< y (+ (- c) x))|))
 (239 23
      (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (216 216
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4G))
 (216 216
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3G))
 (216 216
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2G))
 (216 216
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1G))
 (206 206
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (154 94 (:REWRITE |(+ c (+ d x))|))
 (148 12 (:REWRITE |(* x (- y))|))
 (131 83 (:REWRITE DEFAULT-MINUS))
 (124 88 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (114 6 (:REWRITE ODD-EXPT-THM))
 (95 23
     (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (95 23
     (:REWRITE |(< x (/ y)) with (< y 0)|))
 (90 90 (:REWRITE |(< (+ c/d x) y)|))
 (86 86 (:REWRITE |(* c (* d x))|))
 (84 84 (:REWRITE |(< x (+ c/d y))|))
 (78 28 (:REWRITE |(- (* c x))|))
 (78 1 (:REWRITE |(* (if a b c) x)|))
 (73 61 (:REWRITE INTEGERP-MINUS-X))
 (61 61 (:REWRITE REDUCE-INTEGERP-+))
 (61 61 (:META META-INTEGERP-CORRECT))
 (60 15 (:REWRITE RATIONALP-X))
 (54 18 (:REWRITE RTL::BVECP-EXACTP))
 (50 1 (:REWRITE |(* x (if a b c))|))
 (48 12 (:REWRITE |(+ (* c x) (* d x))|))
 (46 46 (:REWRITE |(< (* x y) 0)|))
 (45 1 (:REWRITE |(equal (if a b c) x)|))
 (42 42 (:REWRITE |(< (/ x) 0)|))
 (36 36 (:TYPE-PRESCRIPTION RTL::BVECP))
 (35 35
     (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (35 35
     (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (27 27
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (27 27
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (26 26
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (26 26 (:REWRITE DEFAULT-DIVIDE))
 (21 21 (:REWRITE FOLD-CONSTS-IN-+))
 (20 10 (:REWRITE DEFAULT-EXPT-2))
 (19 19
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (19 19
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (19 19
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (19 19
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (19 19 (:REWRITE |(equal c (/ x))|))
 (19 19 (:REWRITE |(equal c (- x))|))
 (19 19 (:REWRITE |(equal (/ x) c)|))
 (19 19 (:REWRITE |(equal (/ x) (/ y))|))
 (19 19 (:REWRITE |(equal (- x) c)|))
 (19 19 (:REWRITE |(equal (- x) (- y))|))
 (18 18
     (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (18 18
     (:REWRITE |(< (* x (/ y)) 0) rationalp (* x (/ y))|))
 (15 15 (:REWRITE REDUCE-RATIONALP-+))
 (15 15 (:REWRITE REDUCE-RATIONALP-*))
 (15 15 (:REWRITE RATIONALP-MINUS-X))
 (15 15 (:META META-RATIONALP-CORRECT))
 (12 12 (:REWRITE |(< 0 (* x y))|))
 (12 12 (:REWRITE |(* 0 x)|))
 (12 12 (:REWRITE |(* (- x) y)|))
 (11 11 (:REWRITE |(equal (+ (- c) x) y)|))
 (11 1 (:REWRITE |(- (if a b c))|))
 (10 10 (:REWRITE DEFAULT-EXPT-1))
 (10 10 (:REWRITE |(expt 1/c n)|))
 (10 10 (:REWRITE |(expt (- x) n)|))
 (8 8 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (8 8 (:REWRITE |(< 0 (/ x))|))
 (8 8
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (8 8
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (8 8
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (6 6 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (4 4 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (4 4 (:LINEAR EXPT-LINEAR-UPPER-<))
 (4 4 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (4 4 (:LINEAR EXPT-LINEAR-LOWER-<))
 (4 4 (:LINEAR EXPT->=-1-TWO))
 (4 4 (:LINEAR EXPT->-1-TWO))
 (4 4 (:LINEAR EXPT-<=-1-ONE))
 (4 4 (:LINEAR EXPT-<-1-ONE))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RTL::R-EXACTP-62
 (1
   1
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (1
  1
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A)))
(RTL::R-EXACTP-63
 (111 15 (:REWRITE DEFAULT-TIMES-2))
 (110 6 (:REWRITE RTL::R-EXACTP-6))
 (105
  105
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (105 105
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (105
     105
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (105 105
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (105 105
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (81 15 (:REWRITE DEFAULT-TIMES-1))
 (64 46 (:REWRITE DEFAULT-PLUS-2))
 (56 46 (:REWRITE DEFAULT-PLUS-1))
 (22 22
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (14 3 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (12 8 (:REWRITE DEFAULT-MINUS))
 (11 8 (:REWRITE DEFAULT-LESS-THAN-2))
 (10 7
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (10 7 (:REWRITE DEFAULT-EXPT-2))
 (9 9 (:REWRITE |(+ c (+ d x))|))
 (9 8 (:REWRITE DEFAULT-LESS-THAN-1))
 (9 8 (:REWRITE |(< (- x) c)|))
 (9 8 (:REWRITE |(< (- x) (- y))|))
 (8 8 (:REWRITE THE-FLOOR-BELOW))
 (8 8 (:REWRITE THE-FLOOR-ABOVE))
 (8 8 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (8 8
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (8 8
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (8 8 (:REWRITE REDUCE-INTEGERP-+))
 (8 8 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (8 8 (:REWRITE INTEGERP-MINUS-X))
 (8 8 (:REWRITE INTEGERP-<-CONSTANT))
 (8 8 (:REWRITE FOLD-CONSTS-IN-+))
 (8 8 (:REWRITE CONSTANT-<-INTEGERP))
 (8 8
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (8 8
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (8 8
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (8 8
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (8 8 (:REWRITE |(< c (- x))|))
 (8 8
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (8 8
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (8 8
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (8 8
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (8 8 (:REWRITE |(< (/ x) (/ y))|))
 (8 8 (:META META-INTEGERP-CORRECT))
 (8 6 (:REWRITE SIMPLIFY-SUMS-<))
 (8 2 (:REWRITE RATIONALP-X))
 (7 7 (:REWRITE DEFAULT-EXPT-1))
 (7 7 (:REWRITE |(expt 1/c n)|))
 (7 7 (:REWRITE |(expt (- x) n)|))
 (3 1 (:REWRITE RTL::BVECP-EXACTP))
 (2 2 (:TYPE-PRESCRIPTION RTL::BVECP))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE REDUCE-RATIONALP-+))
 (2 2 (:REWRITE REDUCE-RATIONALP-*))
 (2 2 (:REWRITE RATIONALP-MINUS-X))
 (2 2 (:META META-RATIONALP-CORRECT))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (+ c/d x) y)|))
 (1 1 (:REWRITE |(< (+ (- c) x) y)|))
 (1 1 (:REWRITE |(< (* x y) 0)|)))
(RTL::R-EXACTP-64
 (10 1 (:REWRITE DEFAULT-TIMES-2))
 (5 5 (:REWRITE DEFAULT-PLUS-2))
 (5 5 (:REWRITE DEFAULT-PLUS-1))
 (3 1 (:REWRITE RTL::BVECP-EXACTP))
 (2 2 (:TYPE-PRESCRIPTION RTL::BVECP))
 (2 2
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (2 2 (:REWRITE NORMALIZE-ADDENDS))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (1
   1
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (1
  1
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (1 1 (:REWRITE REDUCE-INTEGERP-+))
 (1 1 (:REWRITE INTEGERP-MINUS-X))
 (1 1 (:REWRITE DEFAULT-TIMES-1))
 (1 1 (:REWRITE DEFAULT-EXPT-2))
 (1 1 (:REWRITE DEFAULT-EXPT-1))
 (1 1 (:REWRITE |(expt 1/c n)|))
 (1 1 (:REWRITE |(expt (- x) n)|))
 (1 1 (:META META-INTEGERP-CORRECT)))
(RTL::R-EXACTP-65
 (3499 42 (:REWRITE RTL::R-EXACTP-6))
 (1610
  1610
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1610
      1610
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1610
     1610
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1610 1610
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1610 1610
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (1610 1610
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (1521 1521
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (1521 1521
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (1521 1521
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (1521 1521
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (1122 72 (:META META-INTEGERP-CORRECT))
 (980 5 (:REWRITE |(integerp (expt x n))|))
 (910 364 (:REWRITE DEFAULT-PLUS-2))
 (897 72 (:REWRITE REDUCE-INTEGERP-+))
 (839 204 (:REWRITE |(< (- x) c)|))
 (738 3 (:REWRITE |(integerp (- x))|))
 (729 27
      (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (702 27
      (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (653 194
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (564 364 (:REWRITE DEFAULT-PLUS-1))
 (513 207 (:REWRITE DEFAULT-LESS-THAN-1))
 (489 207 (:REWRITE DEFAULT-LESS-THAN-2))
 (419 129 (:REWRITE DEFAULT-TIMES-2))
 (358 163 (:REWRITE SIMPLIFY-SUMS-<))
 (269 129 (:REWRITE DEFAULT-TIMES-1))
 (246 204
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (229 204 (:REWRITE |(< (- x) (- y))|))
 (207 207 (:REWRITE THE-FLOOR-BELOW))
 (207 207 (:REWRITE THE-FLOOR-ABOVE))
 (204 204
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (204 204
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (204 204
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (204 204
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (204 204
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (204 204
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (204 204
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (204 204 (:REWRITE |(< c (- x))|))
 (204 204
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (204 204
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (204 204
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (204 204 (:REWRITE |(< (/ x) (/ y))|))
 (199 199 (:REWRITE INTEGERP-<-CONSTANT))
 (199 199 (:REWRITE CONSTANT-<-INTEGERP))
 (198 101 (:REWRITE DEFAULT-MINUS))
 (190 10 (:REWRITE ODD-EXPT-THM))
 (143 143
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (122 72 (:REWRITE INTEGERP-MINUS-X))
 (103 103
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (72 24 (:REWRITE RTL::BVECP-EXACTP))
 (68 17 (:REWRITE RATIONALP-X))
 (62 42 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (48 48 (:TYPE-PRESCRIPTION RTL::BVECP))
 (47 27 (:REWRITE |(- (* c x))|))
 (41 41 (:REWRITE FOLD-CONSTS-IN-+))
 (41 1 (:LINEAR EXPT-<=-1-TWO))
 (40 40
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (40 40 (:REWRITE DEFAULT-DIVIDE))
 (40 1 (:LINEAR EXPT->=-1-ONE))
 (40 1 (:LINEAR EXPT-<-1-TWO))
 (39 1 (:LINEAR EXPT->-1-ONE))
 (38 38 (:REWRITE |(< (+ c/d x) y)|))
 (38 38 (:REWRITE |(< (+ (- c) x) y)|))
 (38 19 (:REWRITE DEFAULT-EXPT-2))
 (37 37 (:REWRITE |(< y (+ (- c) x))|))
 (37 37 (:REWRITE |(< x (+ c/d y))|))
 (35 1 (:LINEAR EXPT-X->=-X))
 (35 1 (:LINEAR EXPT-X->-X))
 (27 27
     (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (27 27
     (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (20 5 (:REWRITE |(+ (* c x) (* d x))|))
 (19 19 (:REWRITE DEFAULT-EXPT-1))
 (19 19 (:REWRITE |(expt 1/c n)|))
 (19 19 (:REWRITE |(expt (- x) n)|))
 (17 17 (:REWRITE REDUCE-RATIONALP-+))
 (17 17 (:REWRITE REDUCE-RATIONALP-*))
 (17 17 (:REWRITE RATIONALP-MINUS-X))
 (17 17 (:META META-RATIONALP-CORRECT))
 (15 15 (:REWRITE |(< (/ x) 0)|))
 (15 15 (:REWRITE |(< (* x y) 0)|))
 (13 13
     (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (7 7 (:REWRITE |(< 0 (/ x))|))
 (7 7 (:REWRITE |(< 0 (* x y))|))
 (5 5 (:REWRITE |(* c (* d x))|))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
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
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (1 1 (:REWRITE |(equal (+ (- c) x) y)|))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<))
 (1 1 (:LINEAR EXPT->=-1-TWO))
 (1 1 (:LINEAR EXPT->-1-TWO))
 (1 1 (:LINEAR EXPT-<=-1-ONE))
 (1 1 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-EXACTP-66
 (169
  169
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (169 169
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (169
     169
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (169 169
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (169 169
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (108 4
      (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (104 4
      (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (102 21 (:REWRITE DEFAULT-TIMES-2))
 (67 21 (:REWRITE DEFAULT-TIMES-1))
 (42 40 (:REWRITE DEFAULT-PLUS-1))
 (42 24
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (41 25 (:REWRITE DEFAULT-LESS-THAN-1))
 (40 40 (:REWRITE DEFAULT-PLUS-2))
 (37 25
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (32 32 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (32 32 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (32 32 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (32 32 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (27 25 (:REWRITE DEFAULT-LESS-THAN-2))
 (25 25 (:REWRITE THE-FLOOR-BELOW))
 (25 25 (:REWRITE THE-FLOOR-ABOVE))
 (25 25
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (25 25
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (25 25
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (25 25
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (25 25
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (25 25
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (25 25
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (25 25 (:REWRITE |(< c (- x))|))
 (25 25
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (25 25
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (25 25
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (25 25 (:REWRITE |(< (/ x) (/ y))|))
 (25 25 (:REWRITE |(< (- x) (- y))|))
 (24 24
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (24 24 (:REWRITE INTEGERP-<-CONSTANT))
 (24 24 (:REWRITE CONSTANT-<-INTEGERP))
 (24 20 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (23 23 (:REWRITE SIMPLIFY-SUMS-<))
 (21 21
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (16 4 (:REWRITE RATIONALP-X))
 (12 12 (:REWRITE REDUCE-INTEGERP-+))
 (12 12 (:REWRITE INTEGERP-MINUS-X))
 (12 12 (:META META-INTEGERP-CORRECT))
 (12 3 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (8 8 (:REWRITE DEFAULT-MINUS))
 (7 7 (:REWRITE FOLD-CONSTS-IN-+))
 (7 7 (:REWRITE DEFAULT-EXPT-2))
 (7 7 (:REWRITE DEFAULT-EXPT-1))
 (7 7 (:REWRITE |(expt 1/c n)|))
 (7 7 (:REWRITE |(expt (- x) n)|))
 (6 6
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (6 6 (:REWRITE DEFAULT-DIVIDE))
 (6 2 (:REWRITE RTL::BVECP-EXACTP))
 (4 4 (:TYPE-PRESCRIPTION RTL::BVECP))
 (4 4 (:REWRITE REDUCE-RATIONALP-+))
 (4 4 (:REWRITE REDUCE-RATIONALP-*))
 (4 4 (:REWRITE RATIONALP-MINUS-X))
 (4 4
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (4 4
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (4 4 (:META META-RATIONALP-CORRECT))
 (3 3 (:REWRITE |(< 0 (/ x))|))
 (3 3 (:REWRITE |(< 0 (* x y))|))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2 (:REWRITE |(< y (+ (- c) x))|))
 (2 2 (:REWRITE |(< x (+ c/d y))|))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (+ c/d x) y)|))
 (1 1 (:REWRITE |(< (+ (- c) x) y)|))
 (1 1 (:REWRITE |(< (* x y) 0)|)))
(RTL::R-EXACTP-67
 (328 5 (:REWRITE RTL::R-EXACTP-6))
 (81 3
     (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (78 3
     (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (27
  27
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (27 27
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (27 27
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (27 27
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (27 27
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (25 13 (:REWRITE DEFAULT-LESS-THAN-1))
 (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (19 13
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (13 13 (:REWRITE THE-FLOOR-BELOW))
 (13 13 (:REWRITE THE-FLOOR-ABOVE))
 (13 13
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (13 13
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (13 13
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (13 13 (:REWRITE INTEGERP-<-CONSTANT))
 (13 13 (:REWRITE DEFAULT-LESS-THAN-2))
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
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (13 13
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (13 13
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (13 13 (:REWRITE |(< (/ x) (/ y))|))
 (13 13 (:REWRITE |(< (- x) c)|))
 (13 13 (:REWRITE |(< (- x) (- y))|))
 (13 9
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (13 9 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (9 9 (:REWRITE SIMPLIFY-SUMS-<))
 (9 5
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (9 5
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (5 5 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (5 5
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (5 5
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (5 5
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (5 5
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (5 5
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (5 5 (:REWRITE DEFAULT-TIMES-2))
 (5 5 (:REWRITE DEFAULT-TIMES-1))
 (5 5 (:REWRITE DEFAULT-DIVIDE))
 (5 5 (:REWRITE |(equal c (/ x))|))
 (5 5 (:REWRITE |(equal c (- x))|))
 (5 5 (:REWRITE |(equal (/ x) c)|))
 (5 5 (:REWRITE |(equal (/ x) (/ y))|))
 (5 5 (:REWRITE |(equal (- x) c)|))
 (5 5 (:REWRITE |(equal (- x) (- y))|))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (3 3
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (3 3
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (2 2 (:REWRITE REDUCE-INTEGERP-+))
 (2 2 (:REWRITE INTEGERP-MINUS-X))
 (2 2 (:META META-INTEGERP-CORRECT)))
(RTL::R-EXACTP-68
 (271
  271
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (271 271
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (271
     271
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (271 271
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (271 271
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (206 206
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (206 206
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (206 206
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (206 206
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (109 31
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (106 37 (:REWRITE DEFAULT-PLUS-2))
 (92 32 (:REWRITE DEFAULT-LESS-THAN-2))
 (88 32 (:REWRITE DEFAULT-LESS-THAN-1))
 (81 3
     (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (78 3
     (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (64 28 (:REWRITE SIMPLIFY-SUMS-<))
 (61 37 (:REWRITE DEFAULT-PLUS-1))
 (57 11 (:REWRITE DEFAULT-TIMES-2))
 (41 1 (:LINEAR EXPT-<=-1-TWO))
 (40 1 (:LINEAR EXPT->=-1-ONE))
 (40 1 (:LINEAR EXPT-<-1-TWO))
 (39 1 (:LINEAR EXPT->-1-ONE))
 (38 2 (:REWRITE ODD-EXPT-THM))
 (37 31
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (35 31 (:REWRITE |(< (- x) (- y))|))
 (35 1 (:LINEAR EXPT-X->=-X))
 (35 1 (:LINEAR EXPT-X->-X))
 (32 32 (:REWRITE THE-FLOOR-BELOW))
 (32 32 (:REWRITE THE-FLOOR-ABOVE))
 (31 31
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (31 31
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (31 31
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (31 31
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (31 31 (:REWRITE INTEGERP-<-CONSTANT))
 (31 31 (:REWRITE CONSTANT-<-INTEGERP))
 (31 31
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (31 31
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (31 31
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (31 31
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (31 31 (:REWRITE |(< c (- x))|))
 (31 31
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (31 31
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (31 31
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (31 31 (:REWRITE |(< (/ x) (/ y))|))
 (31 31 (:REWRITE |(< (- x) c)|))
 (30 24 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (29 11 (:REWRITE DEFAULT-TIMES-1))
 (15 15
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (15 11 (:REWRITE INTEGERP-MINUS-X))
 (15 6 (:REWRITE DEFAULT-MINUS))
 (12 3 (:REWRITE RATIONALP-X))
 (11 11 (:REWRITE REDUCE-INTEGERP-+))
 (11 11 (:META META-INTEGERP-CORRECT))
 (9 9
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (9 3 (:REWRITE RTL::BVECP-EXACTP))
 (8 6 (:REWRITE DEFAULT-EXPT-2))
 (7 3 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (6 6 (:TYPE-PRESCRIPTION RTL::BVECP))
 (6 6 (:REWRITE DEFAULT-EXPT-1))
 (6 6 (:REWRITE |(expt 1/c n)|))
 (6 6 (:REWRITE |(expt (- x) n)|))
 (6 6 (:REWRITE |(< y (+ (- c) x))|))
 (6 6 (:REWRITE |(< x (+ c/d y))|))
 (5 5 (:REWRITE |(< (+ c/d x) y)|))
 (5 5 (:REWRITE |(< (+ (- c) x) y)|))
 (4 4
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (4 4 (:REWRITE DEFAULT-DIVIDE))
 (4 4 (:REWRITE |(+ c (+ d x))|))
 (3 3 (:REWRITE REDUCE-RATIONALP-+))
 (3 3 (:REWRITE REDUCE-RATIONALP-*))
 (3 3 (:REWRITE RATIONALP-MINUS-X))
 (3 3
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (3 3 (:REWRITE |(< (/ x) 0)|))
 (3 3 (:REWRITE |(< (* x y) 0)|))
 (3 3
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (3 3 (:META META-RATIONALP-CORRECT))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:REWRITE |(< 0 (* x y))|))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (1 1 (:REWRITE |(- (* c x))|))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<))
 (1 1 (:LINEAR EXPT->=-1-TWO))
 (1 1 (:LINEAR EXPT->-1-TWO))
 (1 1 (:LINEAR EXPT-<=-1-ONE))
 (1 1 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-EXACTP-69
 (138 8 (:REWRITE RTL::R-EXACTP-6))
 (114 14 (:REWRITE DEFAULT-TIMES-2))
 (101
  101
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (101 101
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (101
     101
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (101 101
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (101 101
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (74 14 (:REWRITE DEFAULT-TIMES-1))
 (68 43 (:REWRITE DEFAULT-PLUS-2))
 (53 43 (:REWRITE DEFAULT-PLUS-1))
 (21 21
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (14 3 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (12 8 (:REWRITE DEFAULT-MINUS))
 (12 7 (:REWRITE DEFAULT-EXPT-2))
 (11 8 (:REWRITE DEFAULT-LESS-THAN-1))
 (9 7
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (8 8 (:REWRITE THE-FLOOR-BELOW))
 (8 8 (:REWRITE THE-FLOOR-ABOVE))
 (8 8 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (8 8
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (8 8
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (8 8 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (8 8 (:REWRITE INTEGERP-<-CONSTANT))
 (8 8 (:REWRITE DEFAULT-LESS-THAN-2))
 (8 8 (:REWRITE CONSTANT-<-INTEGERP))
 (8 8
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (8 8
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (8 8
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (8 8
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (8 8 (:REWRITE |(< c (- x))|))
 (8 8
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (8 8
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (8 8
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (8 8
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (8 8 (:REWRITE |(< (/ x) (/ y))|))
 (8 8 (:REWRITE |(< (- x) c)|))
 (8 8 (:REWRITE |(< (- x) (- y))|))
 (8 2 (:REWRITE RATIONALP-X))
 (7 7 (:REWRITE REDUCE-INTEGERP-+))
 (7 7 (:REWRITE INTEGERP-MINUS-X))
 (7 7 (:REWRITE DEFAULT-EXPT-1))
 (7 7 (:REWRITE |(expt 1/c n)|))
 (7 7 (:REWRITE |(expt (- x) n)|))
 (7 7 (:REWRITE |(+ c (+ d x))|))
 (7 7 (:META META-INTEGERP-CORRECT))
 (7 6 (:REWRITE SIMPLIFY-SUMS-<))
 (6 6 (:REWRITE FOLD-CONSTS-IN-+))
 (6 2 (:REWRITE RTL::BVECP-EXACTP))
 (4 4 (:TYPE-PRESCRIPTION RTL::BVECP))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE REDUCE-RATIONALP-+))
 (2 2 (:REWRITE REDUCE-RATIONALP-*))
 (2 2 (:REWRITE RATIONALP-MINUS-X))
 (2 2 (:META META-RATIONALP-CORRECT))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (+ c/d x) y)|))
 (1 1 (:REWRITE |(< (+ (- c) x) y)|))
 (1 1 (:REWRITE |(< (* x y) 0)|)))
(RTL::R-EXACTP-70
 (759 11 (:REWRITE RTL::R-EXACTP-6))
 (223 223
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (223 223
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (223 223
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (223 223
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (214
  214
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (214 214
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (214
     214
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (214 214
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (214 214
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (214 214
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (162 6
      (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (156 6
      (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (130 40
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (111 42 (:REWRITE DEFAULT-LESS-THAN-1))
 (103 42 (:REWRITE DEFAULT-LESS-THAN-2))
 (103 29 (:REWRITE DEFAULT-PLUS-2))
 (73 37 (:REWRITE SIMPLIFY-SUMS-<))
 (53 29 (:REWRITE DEFAULT-PLUS-1))
 (47 41
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (45 41 (:REWRITE |(< (- x) (- y))|))
 (45 15 (:REWRITE DEFAULT-TIMES-2))
 (45 15 (:REWRITE DEFAULT-TIMES-1))
 (42 42 (:REWRITE THE-FLOOR-BELOW))
 (42 42 (:REWRITE THE-FLOOR-ABOVE))
 (41 41
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (41 41
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (41 41
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (41 41
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (41 41 (:REWRITE INTEGERP-<-CONSTANT))
 (41 41 (:REWRITE CONSTANT-<-INTEGERP))
 (41 41
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (41 41
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (41 41
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (41 41
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (41 41 (:REWRITE |(< c (- x))|))
 (41 41
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (41 41
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (41 41
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (41 41 (:REWRITE |(< (/ x) (/ y))|))
 (41 41 (:REWRITE |(< (- x) c)|))
 (41 1 (:LINEAR EXPT-<=-1-TWO))
 (40 1 (:LINEAR EXPT->=-1-ONE))
 (40 1 (:LINEAR EXPT-<-1-TWO))
 (39 1 (:LINEAR EXPT->-1-ONE))
 (38 2 (:REWRITE ODD-EXPT-THM))
 (35 1 (:LINEAR EXPT-X->=-X))
 (35 1 (:LINEAR EXPT-X->-X))
 (19 8 (:REWRITE DEFAULT-MINUS))
 (13 13
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (13 9 (:REWRITE INTEGERP-MINUS-X))
 (12 12
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (12 4 (:REWRITE RTL::BVECP-EXACTP))
 (12 3 (:REWRITE RATIONALP-X))
 (9 9 (:REWRITE REDUCE-INTEGERP-+))
 (9 9
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (9 9 (:REWRITE DEFAULT-DIVIDE))
 (9 9 (:META META-INTEGERP-CORRECT))
 (8 8 (:TYPE-PRESCRIPTION RTL::BVECP))
 (8 4 (:REWRITE DEFAULT-EXPT-2))
 (7 3 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (6 6
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (6 6 (:REWRITE |(< y (+ (- c) x))|))
 (6 6 (:REWRITE |(< x (+ c/d y))|))
 (6 6
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (6 6 (:REWRITE |(+ c (+ d x))|))
 (5 5 (:REWRITE |(< (+ c/d x) y)|))
 (5 5 (:REWRITE |(< (+ (- c) x) y)|))
 (4 4 (:REWRITE FOLD-CONSTS-IN-+))
 (4 4 (:REWRITE DEFAULT-EXPT-1))
 (4 4 (:REWRITE |(expt 1/c n)|))
 (4 4 (:REWRITE |(expt (- x) n)|))
 (3 3 (:REWRITE REDUCE-RATIONALP-+))
 (3 3 (:REWRITE REDUCE-RATIONALP-*))
 (3 3 (:REWRITE RATIONALP-MINUS-X))
 (3 3 (:REWRITE |(< (/ x) 0)|))
 (3 3 (:REWRITE |(< (* x y) 0)|))
 (3 3 (:META META-RATIONALP-CORRECT))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:REWRITE |(< 0 (* x y))|))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (1 1 (:REWRITE |(- (* c x))|))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<))
 (1 1 (:LINEAR EXPT->=-1-TWO))
 (1 1 (:LINEAR EXPT->-1-TWO))
 (1 1 (:LINEAR EXPT-<=-1-ONE))
 (1 1 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-EXACTP-71)
(RTL::R-EXACTP-72
 (21
  21
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (21 21
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (21 21
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (21 21
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (21 21
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (11 11 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (11 11 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (11 11 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (11 11
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1B)))
(RTL::R-EXACTP-73
 (1092 13 (:REWRITE RTL::R-EXACTP-6))
 (706 706
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (706 706
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (706 706
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (706 706
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (549
  549
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (549 549
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (549
     549
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (549 549
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (549 549
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (342 101 (:REWRITE DEFAULT-PLUS-2))
 (314 77
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (247 85 (:REWRITE DEFAULT-LESS-THAN-2))
 (243 9
      (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (239 29 (:META META-INTEGERP-CORRECT))
 (235 85 (:REWRITE DEFAULT-LESS-THAN-1))
 (234 9
      (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (210 83 (:REWRITE |(< (- x) c)|))
 (196 1 (:REWRITE |(integerp (expt x n))|))
 (181 101 (:REWRITE DEFAULT-PLUS-1))
 (172 66 (:REWRITE SIMPLIFY-SUMS-<))
 (161 40 (:REWRITE DEFAULT-TIMES-2))
 (127 40 (:REWRITE DEFAULT-TIMES-1))
 (114 6 (:REWRITE ODD-EXPT-THM))
 (107 83
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (96 83 (:REWRITE |(< (- x) (- y))|))
 (85 85 (:REWRITE THE-FLOOR-BELOW))
 (85 85 (:REWRITE THE-FLOOR-ABOVE))
 (83 83
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (83 83
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (83 83
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (83 83
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (83 83
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (83 83
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (83 83
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (83 83 (:REWRITE |(< c (- x))|))
 (83 83
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (83 83
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (83 83
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (83 83 (:REWRITE |(< (/ x) (/ y))|))
 (82 82 (:REWRITE INTEGERP-<-CONSTANT))
 (82 82 (:REWRITE CONSTANT-<-INTEGERP))
 (54 24 (:REWRITE DEFAULT-MINUS))
 (41 29 (:REWRITE INTEGERP-MINUS-X))
 (41 1 (:LINEAR EXPT-<=-1-TWO))
 (40 1 (:LINEAR EXPT->=-1-ONE))
 (40 1 (:LINEAR EXPT-<-1-TWO))
 (39 1 (:LINEAR EXPT->-1-ONE))
 (36 36
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (36 12 (:REWRITE RTL::BVECP-EXACTP))
 (36 9 (:REWRITE RATIONALP-X))
 (35 1 (:LINEAR EXPT-X->=-X))
 (35 1 (:LINEAR EXPT-X->-X))
 (34 13 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (29 29 (:REWRITE REDUCE-INTEGERP-+))
 (24 24 (:TYPE-PRESCRIPTION RTL::BVECP))
 (17 9 (:REWRITE DEFAULT-EXPT-2))
 (14 14
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (14 14 (:REWRITE DEFAULT-DIVIDE))
 (13 13 (:REWRITE |(< y (+ (- c) x))|))
 (13 13 (:REWRITE |(< x (+ c/d y))|))
 (13 13 (:REWRITE |(< (+ c/d x) y)|))
 (13 13 (:REWRITE |(< (+ (- c) x) y)|))
 (10 10 (:REWRITE FOLD-CONSTS-IN-+))
 (9 9 (:REWRITE REDUCE-RATIONALP-+))
 (9 9 (:REWRITE REDUCE-RATIONALP-*))
 (9 9 (:REWRITE RATIONALP-MINUS-X))
 (9 9 (:REWRITE DEFAULT-EXPT-1))
 (9 9 (:REWRITE |(expt 1/c n)|))
 (9 9 (:REWRITE |(expt (- x) n)|))
 (9 9
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (9 9
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (9 9 (:META META-RATIONALP-CORRECT))
 (8 4 (:REWRITE |(- (* c x))|))
 (7 7 (:REWRITE |(< (/ x) 0)|))
 (7 7 (:REWRITE |(< (* x y) 0)|))
 (6 6 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (4 4 (:REWRITE |(* c (* d x))|))
 (4 1 (:REWRITE |(+ (* c x) (* d x))|))
 (3 3 (:REWRITE |(< 0 (/ x))|))
 (3 3 (:REWRITE |(< 0 (* x y))|))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (1 1 (:REWRITE |(* 0 x)|))
 (1 1 (:REWRITE |(* (- x) y)|))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<))
 (1 1 (:LINEAR EXPT->=-1-TWO))
 (1 1 (:LINEAR EXPT->-1-TWO))
 (1 1 (:LINEAR EXPT-<=-1-ONE))
 (1 1 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-EXACTP-74
 (2466 2466
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (2466 2466
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (2466 2466
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (2466 2466
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (2015
  2015
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (2015
      2015
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (2015
     2015
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (2015 2015
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1058 302 (:REWRITE DEFAULT-PLUS-2))
 (803 143
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (655 215 (:REWRITE DEFAULT-LESS-THAN-2))
 (652 302 (:REWRITE DEFAULT-PLUS-1))
 (559 215 (:REWRITE DEFAULT-LESS-THAN-1))
 (436 9 (:REWRITE RTL::R-EXACTP-6))
 (431 107 (:REWRITE SIMPLIFY-SUMS-<))
 (380 20 (:REWRITE ODD-EXPT-THM))
 (361 211
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (251 211 (:REWRITE |(< (- x) (- y))|))
 (239 77 (:REWRITE DEFAULT-TIMES-2))
 (239 77 (:REWRITE DEFAULT-TIMES-1))
 (215 215 (:REWRITE THE-FLOOR-BELOW))
 (215 215 (:REWRITE THE-FLOOR-ABOVE))
 (211 211
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (211 211
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (211 211
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (211 211 (:REWRITE INTEGERP-<-CONSTANT))
 (211 211 (:REWRITE CONSTANT-<-INTEGERP))
 (211 211
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (211 211
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (211 211
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (211 211
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (211 211 (:REWRITE |(< c (- x))|))
 (211 211
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (211 211
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (211 211
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (211 211 (:REWRITE |(< (/ x) (/ y))|))
 (211 211 (:REWRITE |(< (- x) c)|))
 (174 58 (:REWRITE RTL::BVECP-EXACTP))
 (156 116 (:REWRITE INTEGERP-MINUS-X))
 (144 64 (:REWRITE DEFAULT-MINUS))
 (142 116 (:META META-INTEGERP-CORRECT))
 (116 116 (:TYPE-PRESCRIPTION RTL::BVECP))
 (116 116 (:REWRITE REDUCE-INTEGERP-+))
 (96 24 (:REWRITE RATIONALP-X))
 (81 3
     (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (78 78
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (78 3
     (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (76 36 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (59 59
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (41 1 (:LINEAR EXPT-<=-1-TWO))
 (40 1 (:LINEAR EXPT->=-1-ONE))
 (40 1 (:LINEAR EXPT-<-1-TWO))
 (39 1 (:LINEAR EXPT->-1-ONE))
 (38 38 (:REWRITE |(< (+ c/d x) y)|))
 (38 38 (:REWRITE |(< (+ (- c) x) y)|))
 (35 1 (:LINEAR EXPT-X->=-X))
 (35 1 (:LINEAR EXPT-X->-X))
 (30 30 (:REWRITE DEFAULT-EXPT-2))
 (30 30 (:REWRITE DEFAULT-EXPT-1))
 (30 30 (:REWRITE |(expt 1/c n)|))
 (30 30 (:REWRITE |(expt (- x) n)|))
 (24 24 (:REWRITE REDUCE-RATIONALP-+))
 (24 24 (:REWRITE REDUCE-RATIONALP-*))
 (24 24 (:REWRITE RATIONALP-MINUS-X))
 (24 24 (:REWRITE |(< y (+ (- c) x))|))
 (24 24 (:REWRITE |(< x (+ c/d y))|))
 (24 24 (:META META-RATIONALP-CORRECT))
 (21 21
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (21 21 (:REWRITE DEFAULT-DIVIDE))
 (20 20
     (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (20 20 (:REWRITE |(< (/ x) 0)|))
 (20 20 (:REWRITE |(< (* x y) 0)|))
 (12 12 (:REWRITE |(- (* c x))|))
 (9 5
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (9 5
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (5 5 (:REWRITE SIMPLIFY-SUMS-EQUAL))
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
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4 (:REWRITE |(* c (* d x))|))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (3 3
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (3 3
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:REWRITE |(< 0 (* x y))|))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<))
 (1 1 (:LINEAR EXPT->=-1-TWO))
 (1 1 (:LINEAR EXPT->-1-TWO))
 (1 1 (:LINEAR EXPT-<=-1-ONE))
 (1 1 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-EXACTP-75
 (11 11 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (11 11 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (11 11 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (11 11 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (11
  11
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (11 11
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (11 11
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (11 11
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (11 11
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (11 11
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE)))
(RTL::R-EXACTP-76
     (259 4 (:REWRITE RTL::R-EXACTP-6))
     (60 30
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (55 35 (:REWRITE DEFAULT-LESS-THAN-1))
     (35 35 (:REWRITE THE-FLOOR-BELOW))
     (35 35 (:REWRITE THE-FLOOR-ABOVE))
     (35 35 (:REWRITE DEFAULT-LESS-THAN-2))
     (33 33
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (33 33
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (33 33
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (30 30 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (30 30 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (30 30 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (30 30 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (30 30 (:REWRITE INTEGERP-<-CONSTANT))
     (30 30 (:REWRITE CONSTANT-<-INTEGERP))
     (30 30
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (30 30
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (30 30
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (30 30
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (30 30 (:REWRITE |(< c (- x))|))
     (30 30
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (30 30
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (30 30
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (30 30 (:REWRITE |(< (/ x) (/ y))|))
     (30 30 (:REWRITE |(< (- x) c)|))
     (30 30 (:REWRITE |(< (- x) (- y))|))
     (29 4
         (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
     (28 2
         (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
     (26 18
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (26 18 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (18 18 (:REWRITE SIMPLIFY-SUMS-<))
     (16 4 (:REWRITE RATIONALP-X))
     (14 14 (:REWRITE REDUCE-INTEGERP-+))
     (14 14 (:REWRITE INTEGERP-MINUS-X))
     (14 14 (:META META-INTEGERP-CORRECT))
     (4 4 (:REWRITE REDUCE-RATIONALP-+))
     (4 4 (:REWRITE REDUCE-RATIONALP-*))
     (4 4 (:REWRITE RATIONALP-MINUS-X))
     (4 4
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (4 4
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (4 4 (:REWRITE DEFAULT-TIMES-2))
     (4 4 (:REWRITE DEFAULT-TIMES-1))
     (4 4 (:REWRITE DEFAULT-DIVIDE))
     (4 4
        (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
     (4 4 (:META META-RATIONALP-CORRECT))
     (4 2
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (4 2
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
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
     (2 2
        (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RTL::R-EXACTP-77
 (342 3 (:REWRITE RTL::R-EXACTP-6))
 (252 2
      (:REWRITE EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (94
  94
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (94 94
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (94 94
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (94 94
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (94 94
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (94 94
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (81 3
     (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (78 3
     (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (75 38 (:REWRITE DEFAULT-LESS-THAN-1))
 (66 46 (:REWRITE DEFAULT-PLUS-2))
 (59 38 (:REWRITE DEFAULT-LESS-THAN-2))
 (53 46 (:REWRITE DEFAULT-PLUS-1))
 (52 34
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (46 28
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (38 38 (:REWRITE THE-FLOOR-BELOW))
 (38 38 (:REWRITE THE-FLOOR-ABOVE))
 (37 37
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (37 37
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (34 34 (:REWRITE INTEGERP-<-CONSTANT))
 (34 34 (:REWRITE CONSTANT-<-INTEGERP))
 (34 34
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (34 34
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (34 34
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (34 34
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (34 34 (:REWRITE |(< c (- x))|))
 (34 34
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (34 34
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (34 34
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (34 34 (:REWRITE |(< (/ x) (/ y))|))
 (34 34 (:REWRITE |(< (- x) c)|))
 (34 34 (:REWRITE |(< (- x) (- y))|))
 (25 25 (:REWRITE SIMPLIFY-SUMS-<))
 (24 24 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (24 24 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (24 24 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (24 24 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (16 4 (:REWRITE RATIONALP-X))
 (12 12 (:REWRITE REDUCE-INTEGERP-+))
 (12 12
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (12 12 (:REWRITE INTEGERP-MINUS-X))
 (12 12 (:META META-INTEGERP-CORRECT))
 (6 6 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (5 4 (:REWRITE DEFAULT-EXPT-2))
 (4 4 (:REWRITE REDUCE-RATIONALP-+))
 (4 4 (:REWRITE REDUCE-RATIONALP-*))
 (4 4 (:REWRITE RATIONALP-MINUS-X))
 (4 4 (:REWRITE DEFAULT-MINUS))
 (4 4 (:REWRITE DEFAULT-EXPT-1))
 (4 4 (:REWRITE |(expt 1/c n)|))
 (4 4 (:REWRITE |(expt (- x) n)|))
 (4 4 (:REWRITE |(< x (+ c/d y))|))
 (4 4 (:META META-RATIONALP-CORRECT))
 (3 3
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (3 3
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (3 3 (:REWRITE FOLD-CONSTS-IN-+))
 (3 3 (:REWRITE DEFAULT-TIMES-2))
 (3 3 (:REWRITE DEFAULT-TIMES-1))
 (3 3 (:REWRITE DEFAULT-DIVIDE))
 (3 3
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (3 3 (:REWRITE |(< (+ c/d x) y)|))
 (3 3
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (2 2 (:REWRITE |(< y (+ (- c) x))|))
 (2 2 (:REWRITE |(< 0 (* x y))|))
 (2 2 (:REWRITE |(< (* x y) 0)|))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (1 1 (:REWRITE |(< 0 (/ x))|))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (+ (- c) x) y)|)))
(RTL::R-EXACTP)
(RTL::EXPO-Q-1
 (292 292
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (292 292
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (292 292
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (230
  230
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (230 230
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (230
     230
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (230 230
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (230 230
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (230 230
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (148 33
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (128 1 (:REWRITE RTL::R-EXACTP-6))
 (127 35 (:REWRITE DEFAULT-PLUS-2))
 (121 25
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (113 34 (:REWRITE DEFAULT-LESS-THAN-2))
 (110 2 (:LINEAR EXPT->=-1-ONE))
 (108 2 (:LINEAR EXPT-<-1-TWO))
 (93 35 (:REWRITE DEFAULT-PLUS-1))
 (83 30 (:REWRITE |(< (- x) c)|))
 (78 22 (:REWRITE SIMPLIFY-SUMS-<))
 (72 34 (:REWRITE DEFAULT-LESS-THAN-1))
 (42 30
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (40 2 (:LINEAR EXPT->-1-ONE))
 (38 2 (:REWRITE ODD-EXPT-THM))
 (36 2 (:LINEAR EXPT-X->=-X))
 (36 2 (:LINEAR EXPT-X->-X))
 (34 34 (:REWRITE THE-FLOOR-BELOW))
 (34 34 (:REWRITE THE-FLOOR-ABOVE))
 (34 30 (:REWRITE |(< (- x) (- y))|))
 (33 33
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (33 33
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (30 30
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (30 30
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (30 30
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (30 30
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (30 30 (:REWRITE |(< c (- x))|))
 (30 30
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (30 30
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (30 30
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (30 30 (:REWRITE |(< (/ x) (/ y))|))
 (28 28 (:REWRITE INTEGERP-<-CONSTANT))
 (28 28 (:REWRITE CONSTANT-<-INTEGERP))
 (26 1
     (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (17 9 (:REWRITE DEFAULT-MINUS))
 (13 9 (:REWRITE INTEGERP-MINUS-X))
 (12 3 (:REWRITE RATIONALP-X))
 (11 11
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (10 4 (:REWRITE |(+ c (+ d x))|))
 (9 9 (:REWRITE REDUCE-INTEGERP-+))
 (9 9 (:META META-INTEGERP-CORRECT))
 (9 3 (:REWRITE RTL::BVECP-EXACTP))
 (8 8 (:REWRITE |(< y (+ (- c) x))|))
 (8 8 (:REWRITE |(< x (+ c/d y))|))
 (7 7 (:REWRITE |(< (+ c/d x) y)|))
 (7 3 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (6 6 (:TYPE-PRESCRIPTION RTL::BVECP))
 (5 5 (:REWRITE |(< (+ (- c) x) y)|))
 (5 5 (:REWRITE |(< (* x y) 0)|))
 (4 4
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (4 4
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (4 4 (:REWRITE DEFAULT-TIMES-2))
 (4 4 (:REWRITE DEFAULT-TIMES-1))
 (4 4 (:REWRITE DEFAULT-EXPT-2))
 (4 4 (:REWRITE DEFAULT-EXPT-1))
 (4 4 (:REWRITE DEFAULT-DIVIDE))
 (4 4 (:REWRITE |(expt 1/c n)|))
 (4 4 (:REWRITE |(expt (- x) n)|))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (3 3 (:REWRITE REDUCE-RATIONALP-+))
 (3 3 (:REWRITE REDUCE-RATIONALP-*))
 (3 3 (:REWRITE RATIONALP-MINUS-X))
 (3 3 (:REWRITE |(< (/ x) 0)|))
 (3 3 (:META META-RATIONALP-CORRECT))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:REWRITE |(< 0 (* x y))|))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-ONE))
 (2 1
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (2 1
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
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
 (1 1
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (1 1
    (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (1 1
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (1 1 (:REWRITE |(- (* c x))|)))
(RTL::EXPO-Q-2
 (312 51 (:REWRITE DEFAULT-PLUS-2))
 (287
  287
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (287 287
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (287
     287
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (287 287
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (287 287
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (287 287
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (236 51 (:REWRITE DEFAULT-PLUS-1))
 (136 21
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (102 21 (:REWRITE DEFAULT-MINUS))
 (88 16
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (72 19 (:REWRITE |(< (- x) c)|))
 (70 1 (:LINEAR EXPT->=-1-ONE))
 (69 1 (:LINEAR EXPT-<-1-TWO))
 (66 21 (:REWRITE DEFAULT-LESS-THAN-2))
 (57 21 (:REWRITE DEFAULT-LESS-THAN-1))
 (50 5 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (46 19 (:REWRITE |(< (- x) (- y))|))
 (28 19 (:REWRITE |(< c (- x))|))
 (28 19
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (24 24
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (21 21 (:REWRITE THE-FLOOR-BELOW))
 (21 21 (:REWRITE THE-FLOOR-ABOVE))
 (21 21
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (21 21
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (19 19
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (19 19
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (19 19
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (19 19
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (19 19
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (19 19
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (19 19
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (19 19 (:REWRITE |(< (/ x) (/ y))|))
 (17 17 (:REWRITE INTEGERP-<-CONSTANT))
 (17 17 (:REWRITE CONSTANT-<-INTEGERP))
 (15 15 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (15 5 (:REWRITE RTL::BVECP-EXACTP))
 (12 12 (:REWRITE SIMPLIFY-SUMS-<))
 (12 12 (:REWRITE DEFAULT-EXPT-2))
 (12 12 (:REWRITE DEFAULT-EXPT-1))
 (12 12 (:REWRITE |(expt 1/c n)|))
 (12 12 (:REWRITE |(expt (- x) n)|))
 (10 10 (:TYPE-PRESCRIPTION RTL::BVECP))
 (8 2 (:REWRITE RATIONALP-X))
 (8 2 (:REWRITE |(+ c (+ d x))|))
 (5 5 (:REWRITE REDUCE-INTEGERP-+))
 (5 5 (:REWRITE INTEGERP-MINUS-X))
 (5 5 (:REWRITE |(< y (+ (- c) x))|))
 (5 5 (:REWRITE |(< x (+ c/d y))|))
 (5 5 (:REWRITE |(< (+ c/d x) y)|))
 (5 5 (:META META-INTEGERP-CORRECT))
 (3 3 (:REWRITE |(< (+ (- c) x) y)|))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE REDUCE-RATIONALP-+))
 (2 2 (:REWRITE REDUCE-RATIONALP-*))
 (2 2 (:REWRITE RATIONALP-MINUS-X))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:REWRITE |(< 0 (* x y))|))
 (2 2 (:REWRITE |(< (* x y) 0)|))
 (2 2 (:REWRITE |(- (- x))|))
 (2 2 (:META META-RATIONALP-CORRECT))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (1 1 (:REWRITE EXPT-X->=-X))
 (1 1 (:LINEAR EXPT-X->=-X))
 (1 1 (:LINEAR EXPT-X->-X))
 (1 1 (:LINEAR EXPT->=-1-TWO))
 (1 1 (:LINEAR EXPT->-1-TWO))
 (1 1 (:LINEAR EXPT->-1-ONE))
 (1 1 (:LINEAR EXPT-<=-1-ONE))
 (1 1 (:LINEAR EXPT-<-1-ONE)))
(RTL::EXPO-Q-3
 (193
  193
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (193 193
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (193
     193
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (193 193
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (193 193
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (193 193
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (153 153
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (153 153
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (153 153
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (128 16 (:REWRITE DEFAULT-PLUS-2))
 (94 16 (:REWRITE DEFAULT-TIMES-2))
 (94 16 (:REWRITE DEFAULT-PLUS-1))
 (48 13 (:REWRITE DEFAULT-LESS-THAN-1))
 (46 6 (:REWRITE DEFAULT-MINUS))
 (44 13 (:REWRITE |(< (- x) (- y))|))
 (35 13 (:REWRITE DEFAULT-LESS-THAN-2))
 (25 16 (:REWRITE DEFAULT-TIMES-1))
 (22 13
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (20 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (13 13 (:REWRITE THE-FLOOR-BELOW))
 (13 13 (:REWRITE THE-FLOOR-ABOVE))
 (13 13
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (13 13
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (13 13
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
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
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (13 13
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (13 13
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (13 13 (:REWRITE |(< (/ x) (/ y))|))
 (13 13 (:REWRITE |(< (- x) c)|))
 (12 12 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (9 9 (:REWRITE SIMPLIFY-SUMS-<))
 (9 3 (:REWRITE RTL::BVECP-EXACTP))
 (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (8 8
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (8 2 (:REWRITE RATIONALP-X))
 (6 6 (:TYPE-PRESCRIPTION RTL::BVECP))
 (5 5 (:REWRITE REDUCE-INTEGERP-+))
 (5 5
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (5 5 (:REWRITE INTEGERP-MINUS-X))
 (5 5 (:META META-INTEGERP-CORRECT))
 (3 3 (:REWRITE |(< (+ c/d x) y)|))
 (3 3 (:REWRITE |(< (+ (- c) x) y)|))
 (2 2 (:REWRITE REDUCE-RATIONALP-+))
 (2 2 (:REWRITE REDUCE-RATIONALP-*))
 (2 2 (:REWRITE RATIONALP-MINUS-X))
 (2 2
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (2 2 (:REWRITE DEFAULT-EXPT-2))
 (2 2 (:REWRITE DEFAULT-EXPT-1))
 (2 2 (:REWRITE DEFAULT-DIVIDE))
 (2 2 (:REWRITE |(expt 1/c n)|))
 (2 2 (:REWRITE |(expt (- x) n)|))
 (2 2 (:REWRITE |(< y (+ (- c) x))|))
 (2 2 (:REWRITE |(< x (+ c/d y))|))
 (2 2 (:META META-RATIONALP-CORRECT))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (1 1 (:REWRITE |(< 0 (/ x))|))
 (1 1 (:REWRITE |(< 0 (* x y))|))
 (1 1 (:REWRITE |(- (* c x))|)))
(RTL::EXPO-Q-4
     (50 50 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (50 50 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (50 50 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (50 50 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (15 11 (:REWRITE DEFAULT-TIMES-2))
     (11 11 (:REWRITE DEFAULT-TIMES-1))
     (10 6 (:REWRITE DEFAULT-LESS-THAN-2))
     (8 2 (:REWRITE RATIONALP-X))
     (7 4
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (6 6 (:REWRITE THE-FLOOR-BELOW))
     (6 6 (:REWRITE THE-FLOOR-ABOVE))
     (6 6
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (6 6
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (6 6 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (6 6 (:REWRITE DEFAULT-LESS-THAN-1))
     (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (4 4 (:REWRITE REMOVE-STRICT-INEQUALITIES))
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
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (4 4
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (4 4
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (4 4 (:REWRITE |(< (/ x) (/ y))|))
     (4 4 (:REWRITE |(< (- x) c)|))
     (4 4 (:REWRITE |(< (- x) (- y))|))
     (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (3 3 (:REWRITE SIMPLIFY-SUMS-<))
     (3 3 (:REWRITE REDUCE-INTEGERP-+))
     (3 3 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (3 3 (:REWRITE INTEGERP-MINUS-X))
     (3 3 (:META META-INTEGERP-CORRECT))
     (2 2 (:REWRITE REDUCE-RATIONALP-+))
     (2 2 (:REWRITE REDUCE-RATIONALP-*))
     (2 2 (:REWRITE RATIONALP-MINUS-X))
     (2 2
        (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (2 2 (:REWRITE |(< 0 (* x y))|))
     (2 2 (:META META-RATIONALP-CORRECT))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (1 1
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (1 1
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (1 1 (:REWRITE DEFAULT-DIVIDE))
     (1 1 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (1 1 (:REWRITE |(< 0 (/ x))|)))
(RTL::EXPO-Q-5
 (185
  185
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (185 185
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (185
     185
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (185 185
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (185 185
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (156 21 (:REWRITE DEFAULT-PLUS-2))
 (132 21 (:REWRITE DEFAULT-PLUS-1))
 (106 106
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (106 106
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (106 106
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (61 17 (:REWRITE DEFAULT-LESS-THAN-2))
 (55 15
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (35 17 (:REWRITE DEFAULT-LESS-THAN-1))
 (33 6 (:REWRITE DEFAULT-MINUS))
 (30 3 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (30 3 (:REWRITE DEFAULT-TIMES-2))
 (30 3 (:REWRITE DEFAULT-DIVIDE))
 (28 16
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (25 16 (:REWRITE |(< c (- x))|))
 (25 16 (:REWRITE |(< (- x) c)|))
 (25 16 (:REWRITE |(< (- x) (- y))|))
 (17 17 (:REWRITE THE-FLOOR-BELOW))
 (17 17 (:REWRITE THE-FLOOR-ABOVE))
 (16 16 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (16 16
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (16 16
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (16 16
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (16 16
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (16 16 (:REWRITE INTEGERP-<-CONSTANT))
 (16 16 (:REWRITE CONSTANT-<-INTEGERP))
 (16 16
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (16 16
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (16 16
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (16 16
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (16 16
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (16 16
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (16 16
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (16 16 (:REWRITE |(< (/ x) (/ y))|))
 (16 4 (:REWRITE RATIONALP-X))
 (13 13 (:REWRITE SIMPLIFY-SUMS-<))
 (12 4 (:REWRITE RTL::BVECP-EXACTP))
 (12 3 (:REWRITE |(< 0 (/ x))|))
 (11 2 (:REWRITE |(equal (- x) c)|))
 (11 2 (:REWRITE |(equal (- x) (- y))|))
 (10 1
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (8 8 (:TYPE-PRESCRIPTION RTL::BVECP))
 (8 8 (:REWRITE REDUCE-INTEGERP-+))
 (8 8 (:REWRITE INTEGERP-MINUS-X))
 (8 8 (:META META-INTEGERP-CORRECT))
 (6 6
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (4 4 (:REWRITE REDUCE-RATIONALP-+))
 (4 4 (:REWRITE REDUCE-RATIONALP-*))
 (4 4 (:REWRITE RATIONALP-MINUS-X))
 (4 4 (:REWRITE DEFAULT-EXPT-2))
 (4 4 (:REWRITE DEFAULT-EXPT-1))
 (4 4 (:REWRITE |(expt 1/c n)|))
 (4 4 (:REWRITE |(expt (- x) n)|))
 (4 4 (:META META-RATIONALP-CORRECT))
 (3 3
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (3 3
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (3 3 (:REWRITE DEFAULT-TIMES-1))
 (3 3 (:REWRITE |(< 0 (* x y))|))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (2 2
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (2 2 (:REWRITE |(equal c (/ x))|))
 (2 2 (:REWRITE |(equal c (- x))|))
 (2 2 (:REWRITE |(equal (/ x) c)|))
 (2 2 (:REWRITE |(equal (/ x) (/ y))|))
 (1 1 (:REWRITE EXPT-X->=-X))
 (1 1 (:REWRITE EXPT-X->-X))
 (1 1
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (1 1 (:REWRITE |(equal (+ (- c) x) y)|))
 (1 1 (:REWRITE |(< y (+ (- c) x))|))
 (1 1 (:REWRITE |(< x (+ c/d y))|))
 (1 1
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (+ c/d x) y)|))
 (1 1 (:REWRITE |(< (+ (- c) x) y)|))
 (1 1 (:REWRITE |(< (* x y) 0)|))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<)))
(RTL::EXPO-Q-6)
(RTL::EXPO-Q-7
 (1037 1037
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (1037 1037
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (1037 1037
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (1037 1037
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (754
  754
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (754 754
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (754
     754
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (754 754
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (754 754
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (754 754
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (443 94 (:REWRITE DEFAULT-PLUS-2))
 (440 4 (:REWRITE RTL::R-EXACTP-6))
 (375 62
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (304 84 (:REWRITE DEFAULT-LESS-THAN-2))
 (296 94 (:REWRITE DEFAULT-PLUS-1))
 (253 84 (:REWRITE DEFAULT-LESS-THAN-1))
 (162 49 (:REWRITE SIMPLIFY-SUMS-<))
 (120 78
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (117 78 (:REWRITE |(< (- x) (- y))|))
 (114 6 (:REWRITE ODD-EXPT-THM))
 (104 4
      (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (84 84 (:REWRITE THE-FLOOR-BELOW))
 (84 84 (:REWRITE THE-FLOOR-ABOVE))
 (82 82
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (82 82
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (82 82
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (78 78 (:REWRITE INTEGERP-<-CONSTANT))
 (78 78 (:REWRITE CONSTANT-<-INTEGERP))
 (78 78
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (78 78
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (78 78
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (78 78
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (78 78 (:REWRITE |(< c (- x))|))
 (78 78
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (78 78
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (78 78
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (78 78 (:REWRITE |(< (/ x) (/ y))|))
 (78 78 (:REWRITE |(< (- x) c)|))
 (75 24 (:REWRITE DEFAULT-MINUS))
 (54 18 (:REWRITE RTL::BVECP-EXACTP))
 (52 13 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (41 29 (:REWRITE INTEGERP-MINUS-X))
 (40 1 (:LINEAR EXPT->=-1-ONE))
 (40 1 (:LINEAR EXPT-<=-1-TWO))
 (39 1 (:LINEAR EXPT->-1-ONE))
 (39 1 (:LINEAR EXPT-<-1-TWO))
 (36 36 (:TYPE-PRESCRIPTION RTL::BVECP))
 (36 9 (:REWRITE RATIONALP-X))
 (35 1 (:LINEAR EXPT-X->=-X))
 (35 1 (:LINEAR EXPT-X->-X))
 (32 32
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (29 29 (:REWRITE REDUCE-INTEGERP-+))
 (29 29 (:META META-INTEGERP-CORRECT))
 (15 15 (:REWRITE |(< (+ c/d x) y)|))
 (15 15 (:REWRITE |(< (+ (- c) x) y)|))
 (14 14 (:REWRITE |(< y (+ (- c) x))|))
 (14 14 (:REWRITE |(< x (+ c/d y))|))
 (12 12
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (12 12
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (12 12 (:REWRITE DEFAULT-TIMES-2))
 (12 12 (:REWRITE DEFAULT-TIMES-1))
 (12 12 (:REWRITE DEFAULT-DIVIDE))
 (12 8 (:REWRITE DEFAULT-EXPT-2))
 (11 11 (:REWRITE |(+ c (+ d x))|))
 (9 9 (:REWRITE REDUCE-RATIONALP-+))
 (9 9 (:REWRITE REDUCE-RATIONALP-*))
 (9 9 (:REWRITE RATIONALP-MINUS-X))
 (9 9 (:META META-RATIONALP-CORRECT))
 (8 8 (:REWRITE DEFAULT-EXPT-1))
 (8 8 (:REWRITE |(expt 1/c n)|))
 (8 8 (:REWRITE |(expt (- x) n)|))
 (6 6 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (6 6 (:REWRITE |(< (/ x) 0)|))
 (6 6 (:REWRITE |(< (* x y) 0)|))
 (4 4 (:REWRITE FOLD-CONSTS-IN-+))
 (4 4
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (4 4
    (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (4 4
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (3 3 (:REWRITE ZP-OPEN))
 (3 3 (:REWRITE |(- (* c x))|))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:REWRITE |(< 0 (* x y))|))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<))
 (1 1 (:LINEAR EXPT->=-1-TWO))
 (1 1 (:LINEAR EXPT->-1-TWO))
 (1 1 (:LINEAR EXPT-<=-1-ONE))
 (1 1 (:LINEAR EXPT-<-1-ONE)))
(RTL::EXPO-Q-8
 (57
   57
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (57
  57
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (57 57
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (57 57
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (57 57
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (57 57
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (57 57
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (31 1 (:LINEAR EXPT->=-1-ONE))
 (31 1 (:LINEAR EXPT-<=-1-TWO))
 (30 1 (:LINEAR EXPT->-1-ONE))
 (30 1 (:LINEAR EXPT-<-1-TWO))
 (4 4 (:REWRITE THE-FLOOR-BELOW))
 (4 4 (:REWRITE THE-FLOOR-ABOVE))
 (4 4 (:REWRITE SIMPLIFY-SUMS-<))
 (4 4
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (4 4 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (4 4
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (4 4
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (4 4 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (4 4 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (4 4 (:REWRITE INTEGERP-<-CONSTANT))
 (4 4 (:REWRITE DEFAULT-LESS-THAN-2))
 (4 4 (:REWRITE DEFAULT-LESS-THAN-1))
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
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (2 2 (:REWRITE DEFAULT-EXPT-2))
 (2 2 (:REWRITE DEFAULT-EXPT-1))
 (2 2 (:REWRITE |(expt 1/c n)|))
 (2 2 (:REWRITE |(expt (- x) n)|))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:REWRITE |(< 0 (* x y))|))
 (2 2 (:REWRITE |(< (/ x) 0)|))
 (2 2 (:REWRITE |(< (* x y) 0)|))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<))
 (1 1 (:LINEAR EXPT->=-1-TWO))
 (1 1 (:LINEAR EXPT->-1-TWO))
 (1 1 (:LINEAR EXPT-<=-1-ONE))
 (1 1 (:LINEAR EXPT-<-1-ONE)))
(RTL::EXPO-Q-9
 (201 1
      (:REWRITE |(<= x (/ y)) with (< 0 y)|))
 (188 1 (:REWRITE |(< (/ x) y) with (< 0 x)|))
 (112 2
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (96
  96
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (96 96
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (96 96
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (96 96
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (96 96
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (72 3 (:LINEAR EXPT->=-1-ONE))
 (68 1 (:REWRITE |(* y x)|))
 (67 9 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (66 2 (:REWRITE BUBBLE-DOWN-*-MATCH-1))
 (44 2 (:REWRITE |(* x (expt x n))|))
 (41 5 (:REWRITE DEFAULT-TIMES-2))
 (36 9 (:REWRITE DEFAULT-LESS-THAN-2))
 (35 8 (:REWRITE |(< (- x) c)|))
 (34 7
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (30 2 (:REWRITE |(+ (+ x y) z)|))
 (25 7 (:REWRITE CONSTANT-<-INTEGERP))
 (23 22 (:REWRITE DEFAULT-PLUS-1))
 (22 22 (:REWRITE DEFAULT-PLUS-2))
 (20 2 (:REWRITE |(* c (expt d n))|))
 (17 8
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (16 5 (:REWRITE DEFAULT-TIMES-1))
 (14 3 (:REWRITE |(+ c (+ d x))|))
 (10 1
     (:REWRITE |(<= x (/ y)) with (< y 0)|))
 (10 1 (:REWRITE |(< (/ x) y) with (< x 0)|))
 (9 9 (:REWRITE THE-FLOOR-BELOW))
 (9 9 (:REWRITE THE-FLOOR-ABOVE))
 (9 9
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (9 9
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (9 9
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (9 9 (:REWRITE DEFAULT-LESS-THAN-1))
 (8 8
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (8 8
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (8 8
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (8 8 (:REWRITE |(< c (- x))|))
 (8 8
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (8 8
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (8 8
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (8 8
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (8 8 (:REWRITE |(< (/ x) (/ y))|))
 (8 8 (:REWRITE |(< (- x) (- y))|))
 (7 7 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (7 7 (:REWRITE INTEGERP-<-CONSTANT))
 (6 6 (:REWRITE SIMPLIFY-SUMS-<))
 (6 6 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (6 6
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (5 5 (:REWRITE DEFAULT-EXPT-2))
 (5 5 (:REWRITE DEFAULT-EXPT-1))
 (5 5 (:REWRITE |(expt 1/c n)|))
 (5 5 (:REWRITE |(expt (- x) n)|))
 (4 4 (:REWRITE DEFAULT-MINUS))
 (3 3 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (3 3 (:REWRITE ODD-EXPT-THM))
 (3 3 (:LINEAR EXPT-X->=-X))
 (3 3 (:LINEAR EXPT-X->-X))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<))
 (3 3 (:LINEAR EXPT->=-1-TWO))
 (3 3 (:LINEAR EXPT->-1-TWO))
 (3 3 (:LINEAR EXPT->-1-ONE))
 (3 3 (:LINEAR EXPT-<=-1-ONE))
 (3 3 (:LINEAR EXPT-<-1-ONE))
 (2 2 (:REWRITE |(< (+ c/d x) y)|))
 (1 1 (:REWRITE REDUCE-INTEGERP-+))
 (1 1 (:REWRITE INTEGERP-MINUS-X))
 (1 1 (:REWRITE |(< y (+ (- c) x))|))
 (1 1 (:REWRITE |(< x (+ c/d y))|))
 (1 1 (:REWRITE |(< (+ (- c) x) y)|))
 (1 1 (:REWRITE |(< (* x y) 0)|))
 (1 1 (:REWRITE |(- (- x))|))
 (1 1 (:REWRITE |(+ 0 x)|))
 (1 1 (:META META-INTEGERP-CORRECT)))
(RTL::EXPO-Q-10
 (420 3
      (:REWRITE |(<= x (/ y)) with (< 0 y)|))
 (415
  415
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (415 415
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (415
     415
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (415 415
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (415 415
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (367 3 (:REWRITE |(< (/ x) y) with (< 0 x)|))
 (332 332
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (332 332
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (332 332
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (332 332
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (328 5 (:REWRITE RTL::R-EXACTP-6))
 (166 59 (:REWRITE DEFAULT-LESS-THAN-2))
 (150 47
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (131 21
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (107 59 (:REWRITE CONSTANT-<-INTEGERP))
 (90 30 (:REWRITE DEFAULT-TIMES-2))
 (89 59
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (81 59 (:REWRITE DEFAULT-LESS-THAN-1))
 (81 3
     (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (78 3
     (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (76 3 (:REWRITE |(* y x)|))
 (67 59
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (67 59
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (66 2 (:REWRITE BUBBLE-DOWN-*-MATCH-1))
 (61 43 (:REWRITE SIMPLIFY-SUMS-<))
 (59 59 (:REWRITE THE-FLOOR-BELOW))
 (59 59 (:REWRITE THE-FLOOR-ABOVE))
 (59 59
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (59 59 (:REWRITE INTEGERP-<-CONSTANT))
 (59 59
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (59 59
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (59 59
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (59 59
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (59 59 (:REWRITE |(< c (- x))|))
 (59 59
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (59 59
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (59 59
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (59 59 (:REWRITE |(< (/ x) (/ y))|))
 (59 59 (:REWRITE |(< (- x) c)|))
 (59 59 (:REWRITE |(< (- x) (- y))|))
 (56 38 (:REWRITE DEFAULT-PLUS-2))
 (50 2 (:REWRITE |(* (* x y) z)|))
 (49 30 (:REWRITE DEFAULT-TIMES-1))
 (44 2 (:REWRITE |(* x (expt x n))|))
 (42 38 (:REWRITE DEFAULT-PLUS-1))
 (42 3 (:LINEAR EXPT->=-1-ONE))
 (42 3 (:LINEAR EXPT-<=-1-TWO))
 (41 3 (:LINEAR EXPT->-1-ONE))
 (41 3 (:LINEAR EXPT-<-1-TWO))
 (37 3 (:LINEAR EXPT-X->=-X))
 (37 3 (:LINEAR EXPT-X->-X))
 (24 6 (:REWRITE RATIONALP-X))
 (24 2 (:REWRITE |(* y (* x z))|))
 (22 22 (:TYPE-PRESCRIPTION NOT-INTEGERP-4E))
 (22 22 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
 (22 22 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
 (22 22 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
 (21 5 (:REWRITE ODD-EXPT-THM))
 (20 20 (:REWRITE REDUCE-INTEGERP-+))
 (20 20 (:REWRITE INTEGERP-MINUS-X))
 (20 20 (:META META-INTEGERP-CORRECT))
 (20 3
     (:REWRITE |(<= x (/ y)) with (< y 0)|))
 (20 3 (:REWRITE |(< (/ x) y) with (< x 0)|))
 (20 2 (:REWRITE |(* c (expt d n))|))
 (18 6 (:REWRITE RTL::BVECP-EXACTP))
 (12 12 (:TYPE-PRESCRIPTION RTL::BVECP))
 (11 11
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (11 11
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (11 11 (:REWRITE DEFAULT-DIVIDE))
 (9 5
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (9 5
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (6 6 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (6 6 (:REWRITE REDUCE-RATIONALP-+))
 (6 6 (:REWRITE REDUCE-RATIONALP-*))
 (6 6 (:REWRITE RATIONALP-MINUS-X))
 (6 6 (:REWRITE DEFAULT-EXPT-2))
 (6 6 (:REWRITE DEFAULT-EXPT-1))
 (6 6 (:REWRITE |(expt 1/c n)|))
 (6 6 (:REWRITE |(expt (- x) n)|))
 (6 6 (:REWRITE |(< y (+ (- c) x))|))
 (6 6 (:REWRITE |(< x (+ c/d y))|))
 (6 6 (:REWRITE |(< (+ c/d x) y)|))
 (6 6 (:REWRITE |(< (+ (- c) x) y)|))
 (6 6 (:META META-RATIONALP-CORRECT))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (6 6
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (5 5 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (5 5
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (5 5
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (5 5
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (5 5 (:REWRITE DEFAULT-MINUS))
 (5 5 (:REWRITE |(equal c (/ x))|))
 (5 5 (:REWRITE |(equal c (- x))|))
 (5 5 (:REWRITE |(equal (/ x) c)|))
 (5 5 (:REWRITE |(equal (/ x) (/ y))|))
 (5 5 (:REWRITE |(equal (- x) c)|))
 (5 5 (:REWRITE |(equal (- x) (- y))|))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (4 4 (:REWRITE |(< 0 (/ x))|))
 (4 4 (:REWRITE |(< 0 (* x y))|))
 (4 4 (:REWRITE |(< (/ x) 0)|))
 (4 4 (:REWRITE |(< (* x y) 0)|))
 (4 4 (:REWRITE |(* c (* d x))|))
 (4 4 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (4 4 (:LINEAR EXPT-LINEAR-LOWER-<))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (3 3
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (3 3
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<))
 (3 3 (:LINEAR EXPT->=-1-TWO))
 (3 3 (:LINEAR EXPT->-1-TWO))
 (3 3 (:LINEAR EXPT-<=-1-ONE))
 (3 3 (:LINEAR EXPT-<-1-ONE))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2
    (:REWRITE INTEGERP-+-REDUCE-CONSTANT)))
(RTL::EXPO-Q-11
 (1717
  1717
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1717
      1717
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1717
     1717
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1717 1717
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (947 947
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (947 947
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (947 947
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (665 236 (:REWRITE DEFAULT-LESS-THAN-2))
 (607 195
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (471 282 (:REWRITE DEFAULT-PLUS-2))
 (402 282 (:REWRITE DEFAULT-PLUS-1))
 (352 232
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (345 156 (:REWRITE SIMPLIFY-SUMS-<))
 (299 8 (:REWRITE RTL::R-EXACTP-6))
 (250 236 (:REWRITE DEFAULT-LESS-THAN-1))
 (247 232 (:REWRITE CONSTANT-<-INTEGERP))
 (237 233
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (237 233
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (236 236 (:REWRITE THE-FLOOR-BELOW))
 (236 236 (:REWRITE THE-FLOOR-ABOVE))
 (233 233
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (232 232 (:REWRITE INTEGERP-<-CONSTANT))
 (232 232
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (232 232
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (232 232
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (232 232
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (232 232 (:REWRITE |(< c (- x))|))
 (232 232
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (232 232
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (232 232
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (232 232 (:REWRITE |(< (/ x) (/ y))|))
 (232 232 (:REWRITE |(< (- x) c)|))
 (232 232 (:REWRITE |(< (- x) (- y))|))
 (189 21 (:REWRITE ODD-EXPT-THM))
 (162 54 (:REWRITE RTL::BVECP-EXACTP))
 (132 33 (:REWRITE RATIONALP-X))
 (114 1
      (:REWRITE |(<= x (/ y)) with (< 0 y)|))
 (108 108 (:TYPE-PRESCRIPTION RTL::BVECP))
 (95 95 (:REWRITE REDUCE-INTEGERP-+))
 (95 95 (:REWRITE INTEGERP-MINUS-X))
 (95 95 (:META META-INTEGERP-CORRECT))
 (94 1 (:REWRITE |(< (/ x) y) with (< 0 x)|))
 (66 66
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (63 63 (:REWRITE DEFAULT-MINUS))
 (41 41 (:REWRITE |(< (+ c/d x) y)|))
 (41 41 (:REWRITE |(< (+ (- c) x) y)|))
 (40 28 (:REWRITE DEFAULT-TIMES-2))
 (40 1 (:LINEAR EXPT->=-1-ONE))
 (40 1 (:LINEAR EXPT-<=-1-TWO))
 (39 39 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (39 1 (:LINEAR EXPT->-1-ONE))
 (39 1 (:LINEAR EXPT-<-1-TWO))
 (35 1 (:LINEAR EXPT-X->=-X))
 (35 1 (:LINEAR EXPT-X->-X))
 (33 33 (:REWRITE REDUCE-RATIONALP-+))
 (33 33 (:REWRITE REDUCE-RATIONALP-*))
 (33 33 (:REWRITE RATIONALP-MINUS-X))
 (33 33 (:META META-RATIONALP-CORRECT))
 (32 28 (:REWRITE DEFAULT-TIMES-1))
 (30 30 (:REWRITE |(+ c (+ d x))|))
 (26 1
     (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (25 25
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (25 25 (:REWRITE |(< y (+ (- c) x))|))
 (25 25 (:REWRITE |(< x (+ c/d y))|))
 (25 1 (:REWRITE |(* (* x y) z)|))
 (21 21
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (21 21
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (21 21
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (21 21
     (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (21 21 (:REWRITE DEFAULT-DIVIDE))
 (21 21 (:REWRITE |(< 0 (/ x))|))
 (21 21 (:REWRITE |(< 0 (* x y))|))
 (21 21 (:REWRITE |(< (/ x) 0)|))
 (21 21 (:REWRITE |(< (* x y) 0)|))
 (18 18 (:REWRITE DEFAULT-EXPT-2))
 (18 18 (:REWRITE DEFAULT-EXPT-1))
 (18 18 (:REWRITE |(expt 1/c n)|))
 (18 18 (:REWRITE |(expt (- x) n)|))
 (12 1 (:REWRITE |(* y (* x z))|))
 (11 11 (:TYPE-PRESCRIPTION NOT-INTEGERP-4E))
 (11 11 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
 (11 11 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
 (11 11 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
 (9 9 (:REWRITE ZP-OPEN))
 (9 9 (:REWRITE |(- (* c x))|))
 (5 1
    (:REWRITE |(<= x (/ y)) with (< y 0)|))
 (5 1 (:REWRITE |(< (/ x) y) with (< x 0)|))
 (4 1 (:REWRITE |(* y x)|))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2 (:REWRITE |(* c (* d x))|))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (2 1
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (2 1
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
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
 (1 1
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (1 1
    (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (1 1
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<))
 (1 1 (:LINEAR EXPT->=-1-TWO))
 (1 1 (:LINEAR EXPT->-1-TWO))
 (1 1 (:LINEAR EXPT-<=-1-ONE))
 (1 1 (:LINEAR EXPT-<-1-ONE)))
(RTL::EXPO-Q-12
 (110 2 (:LINEAR EXPT->=-1-ONE))
 (75
  75
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (75 75
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (75 75
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (75 75
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (75 75
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (71 13
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (40 2 (:LINEAR EXPT->-1-ONE))
 (39 12 (:REWRITE |(< (- x) c)|))
 (36 2 (:LINEAR EXPT-X->=-X))
 (36 2 (:LINEAR EXPT-X->-X))
 (30 30 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (30 30 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (30 30 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (26 13 (:REWRITE DEFAULT-LESS-THAN-2))
 (25 10
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (25 10 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (19 10 (:REWRITE SIMPLIFY-SUMS-<))
 (15 13 (:REWRITE DEFAULT-LESS-THAN-1))
 (15 6 (:REWRITE DEFAULT-PLUS-2))
 (13 13 (:REWRITE THE-FLOOR-BELOW))
 (13 13 (:REWRITE THE-FLOOR-ABOVE))
 (13 13
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (13 13
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (12 12
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (12 12
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (12 12
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (12 12
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (12 12 (:REWRITE |(< c (- x))|))
 (12 12
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (12 12
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (12 12
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (12 12
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (12 12 (:REWRITE |(< (/ x) (/ y))|))
 (12 12 (:REWRITE |(< (- x) (- y))|))
 (11 11 (:REWRITE INTEGERP-<-CONSTANT))
 (11 11 (:REWRITE CONSTANT-<-INTEGERP))
 (11 1 (:REWRITE |(+ y (+ x z))|))
 (6 6 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (6 6 (:REWRITE DEFAULT-PLUS-1))
 (6 2 (:REWRITE RTL::BVECP-EXACTP))
 (5 5 (:REWRITE |(< y (+ (- c) x))|))
 (5 5 (:REWRITE |(< x (+ c/d y))|))
 (4 4 (:TYPE-PRESCRIPTION RTL::BVECP))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (4 4 (:REWRITE |(< 0 (/ x))|))
 (4 4 (:REWRITE |(< 0 (* x y))|))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (4 1 (:REWRITE |(+ c (+ d x))|))
 (3 3
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (3 3 (:REWRITE NORMALIZE-ADDENDS))
 (3 3 (:REWRITE DEFAULT-EXPT-2))
 (3 3 (:REWRITE DEFAULT-EXPT-1))
 (3 3 (:REWRITE |(expt 1/c n)|))
 (3 3 (:REWRITE |(expt (- x) n)|))
 (3 3 (:REWRITE |(< (+ c/d x) y)|))
 (3 3 (:REWRITE |(< (* x y) 0)|))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2 (:REWRITE DEFAULT-MINUS))
 (2 2 (:REWRITE |(< (/ x) 0)|))
 (2 2 (:REWRITE |(< (+ (- c) x) y)|))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-ONE))
 (1 1 (:REWRITE |(- (- x))|))
 (1 1 (:REWRITE |(+ 0 x)|)))
(RTL::EXPO-Q-13
 (1082 1082
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (1082 1082
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (728
  728
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (728 728
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (728
     728
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (728 728
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (728 728
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (322 79 (:REWRITE DEFAULT-PLUS-2))
 (261 65 (:REWRITE DEFAULT-LESS-THAN-1))
 (238 65 (:REWRITE DEFAULT-LESS-THAN-2))
 (164 26 (:REWRITE DEFAULT-TIMES-2))
 (157 79 (:REWRITE DEFAULT-PLUS-1))
 (146 37 (:REWRITE SIMPLIFY-SUMS-<))
 (120 4 (:REWRITE RTL::R-EXACTP-6))
 (114 6 (:REWRITE ODD-EXPT-THM))
 (77 53
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (71 53 (:REWRITE |(< (/ x) (/ y))|))
 (65 65 (:REWRITE THE-FLOOR-BELOW))
 (65 65 (:REWRITE THE-FLOOR-ABOVE))
 (65 53 (:REWRITE |(< (- x) (- y))|))
 (63 63
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (63 63
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (63 63
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (53 53 (:REWRITE INTEGERP-<-CONSTANT))
 (53 53 (:REWRITE CONSTANT-<-INTEGERP))
 (53 53
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (53 53
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (53 53
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (53 53
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (53 53 (:REWRITE |(< c (- x))|))
 (53 53
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (53 53
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (53 53
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (53 53 (:REWRITE |(< (- x) c)|))
 (44 20 (:REWRITE DEFAULT-MINUS))
 (42 6
     (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (42 6
     (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (40 1 (:LINEAR EXPT->=-1-ONE))
 (40 1 (:LINEAR EXPT-<=-1-TWO))
 (39 1 (:LINEAR EXPT->-1-ONE))
 (39 1 (:LINEAR EXPT-<-1-TWO))
 (38 2
     (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (38 2 (:REWRITE |(< (/ x) y) with (< x 0)|))
 (36 12 (:REWRITE RTL::BVECP-EXACTP))
 (36 9 (:REWRITE RATIONALP-X))
 (35 23 (:REWRITE INTEGERP-MINUS-X))
 (35 1 (:LINEAR EXPT-X->=-X))
 (35 1 (:LINEAR EXPT-X->-X))
 (30 12 (:REWRITE DEFAULT-DIVIDE))
 (27 27
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (26 26 (:REWRITE DEFAULT-TIMES-1))
 (24 24 (:TYPE-PRESCRIPTION RTL::BVECP))
 (23 23 (:REWRITE REDUCE-INTEGERP-+))
 (23 23 (:META META-INTEGERP-CORRECT))
 (22 10 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (22 4
     (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (18 18
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (12 12
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (12 12 (:REWRITE |(< (+ c/d x) y)|))
 (12 12 (:REWRITE |(< (+ (- c) x) y)|))
 (11 11 (:REWRITE |(< y (+ (- c) x))|))
 (11 11 (:REWRITE |(< x (+ c/d y))|))
 (11 11 (:REWRITE |(+ c (+ d x))|))
 (11 7 (:REWRITE DEFAULT-EXPT-2))
 (9 9 (:REWRITE REDUCE-RATIONALP-+))
 (9 9 (:REWRITE REDUCE-RATIONALP-*))
 (9 9 (:REWRITE RATIONALP-MINUS-X))
 (9 9 (:META META-RATIONALP-CORRECT))
 (7 7 (:REWRITE DEFAULT-EXPT-1))
 (7 7 (:REWRITE |(expt 1/c n)|))
 (7 7 (:REWRITE |(expt (- x) n)|))
 (6 6 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (6 6 (:REWRITE |(< (/ x) 0)|))
 (6 6 (:REWRITE |(< (* x y) 0)|))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (4 4 (:REWRITE FOLD-CONSTS-IN-+))
 (4 4 (:REWRITE |(< 0 (* x y))|))
 (3 3 (:REWRITE ZP-OPEN))
 (3 3 (:REWRITE |(- (* c x))|))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<))
 (1 1 (:LINEAR EXPT->=-1-TWO))
 (1 1 (:LINEAR EXPT->-1-TWO))
 (1 1 (:LINEAR EXPT-<=-1-ONE))
 (1 1 (:LINEAR EXPT-<-1-ONE)))
(RTL::EXPO-Q-14
 (523 59 (:REWRITE DEFAULT-PLUS-2))
 (412
  412
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (412 412
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (412
     412
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (412 412
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (412 412
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (369 59 (:REWRITE DEFAULT-PLUS-1))
 (323 323
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (323 323
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (156 14 (:REWRITE DEFAULT-TIMES-2))
 (88 18
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (82 10 (:REWRITE DEFAULT-DIVIDE))
 (78 20 (:REWRITE DEFAULT-LESS-THAN-2))
 (72 2
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (67 15 (:REWRITE DEFAULT-MINUS))
 (66 20 (:REWRITE DEFAULT-LESS-THAN-1))
 (55 7 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (50 14 (:REWRITE DEFAULT-TIMES-1))
 (47 15 (:REWRITE SIMPLIFY-SUMS-<))
 (40 1 (:LINEAR EXPT->=-1-ONE))
 (40 1 (:LINEAR EXPT-<=-1-TWO))
 (39 1 (:LINEAR EXPT->-1-ONE))
 (39 1 (:LINEAR EXPT-<-1-TWO))
 (38 2 (:REWRITE ODD-EXPT-THM))
 (35 1 (:LINEAR EXPT-X->=-X))
 (35 1 (:LINEAR EXPT-X->-X))
 (30 1 (:REWRITE RTL::R-EXACTP-6))
 (24 18
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (22 18 (:REWRITE |(< (- x) (- y))|))
 (20 20 (:REWRITE THE-FLOOR-BELOW))
 (20 20 (:REWRITE THE-FLOOR-ABOVE))
 (20 2 (:REWRITE |(equal (/ x) (/ y))|))
 (19 19
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (19 19
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (19 19
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (18 18
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (18 18 (:REWRITE INTEGERP-<-CONSTANT))
 (18 18 (:REWRITE CONSTANT-<-INTEGERP))
 (18 18
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (18 18
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (18 18
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (18 18
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (18 18 (:REWRITE |(< c (- x))|))
 (18 18
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (18 18
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (18 18
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (18 18 (:REWRITE |(< (/ x) (/ y))|))
 (18 18 (:REWRITE |(< (- x) c)|))
 (14 14 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (12 3 (:REWRITE RATIONALP-X))
 (11 7 (:REWRITE INTEGERP-MINUS-X))
 (10 10
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (10 10
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (9 3 (:REWRITE RTL::BVECP-EXACTP))
 (8 7 (:REWRITE DEFAULT-EXPT-2))
 (7 7 (:REWRITE REDUCE-INTEGERP-+))
 (7 7 (:REWRITE DEFAULT-EXPT-1))
 (7 7 (:REWRITE |(expt 1/c n)|))
 (7 7 (:REWRITE |(expt (- x) n)|))
 (7 7 (:META META-INTEGERP-CORRECT))
 (6 6 (:TYPE-PRESCRIPTION RTL::BVECP))
 (6 6 (:REWRITE |(< y (+ (- c) x))|))
 (6 6 (:REWRITE |(< x (+ c/d y))|))
 (5 5 (:REWRITE |(< (+ c/d x) y)|))
 (5 5 (:REWRITE |(< (+ (- c) x) y)|))
 (5 5 (:REWRITE |(+ c (+ d x))|))
 (3 3 (:REWRITE REDUCE-RATIONALP-+))
 (3 3 (:REWRITE REDUCE-RATIONALP-*))
 (3 3 (:REWRITE RATIONALP-MINUS-X))
 (3 3 (:REWRITE |(< (/ x) 0)|))
 (3 3 (:REWRITE |(< (* x y) 0)|))
 (3 3 (:REWRITE |(- (* c x))|))
 (3 3 (:META META-RATIONALP-CORRECT))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (2 2
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (2 2 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (2 2
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (2 2 (:REWRITE |(equal c (/ x))|))
 (2 2 (:REWRITE |(equal c (- x))|))
 (2 2 (:REWRITE |(equal (/ x) c)|))
 (2 2 (:REWRITE |(equal (- x) c)|))
 (2 2 (:REWRITE |(equal (- x) (- y))|))
 (2 2 (:REWRITE |(equal (+ (- c) x) y)|))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:REWRITE |(< 0 (* x y))|))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE FOLD-CONSTS-IN-+))
 (1 1
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (1 1
    (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<))
 (1 1 (:LINEAR EXPT->=-1-TWO))
 (1 1 (:LINEAR EXPT->-1-TWO))
 (1 1 (:LINEAR EXPT-<=-1-ONE))
 (1 1 (:LINEAR EXPT-<-1-ONE)))
(RTL::EXPO-Q-15
 (110
  110
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (110 110
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (110
     110
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (110 110
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (110 110
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (110 2 (:LINEAR EXPT->=-1-ONE))
 (71 13
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (56 11 (:REWRITE DEFAULT-PLUS-2))
 (48 11 (:REWRITE DEFAULT-PLUS-1))
 (46 12
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (40 2 (:LINEAR EXPT->-1-ONE))
 (39 12 (:REWRITE |(< (- x) c)|))
 (36 2 (:LINEAR EXPT-X->=-X))
 (36 2 (:LINEAR EXPT-X->-X))
 (35 11
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (30 30 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (30 30 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (30 30 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (26 13 (:REWRITE DEFAULT-LESS-THAN-2))
 (24 13 (:REWRITE DEFAULT-LESS-THAN-1))
 (21 12 (:REWRITE |(< (- x) (- y))|))
 (15 12
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (14 3 (:REWRITE REDUCE-INTEGERP-+))
 (13 13 (:REWRITE THE-FLOOR-BELOW))
 (13 13 (:REWRITE THE-FLOOR-ABOVE))
 (13 13
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (13 13
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (12 12
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (12 12
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (12 12
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (12 12 (:REWRITE |(< c (- x))|))
 (12 12
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (12 12
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (12 12
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (12 12 (:REWRITE |(< (/ x) (/ y))|))
 (12 3 (:REWRITE DEFAULT-MINUS))
 (11 11
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (11 11 (:REWRITE INTEGERP-<-CONSTANT))
 (11 11 (:REWRITE CONSTANT-<-INTEGERP))
 (10 10 (:REWRITE SIMPLIFY-SUMS-<))
 (10 1 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (7 7 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (5 5 (:REWRITE |(< y (+ (- c) x))|))
 (5 5 (:REWRITE |(< x (+ c/d y))|))
 (4 4
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (4 4 (:REWRITE |(< (+ c/d x) y)|))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (4 1 (:REWRITE |(+ c (+ d x))|))
 (3 3 (:REWRITE INTEGERP-MINUS-X))
 (3 3 (:REWRITE DEFAULT-EXPT-2))
 (3 3 (:REWRITE DEFAULT-EXPT-1))
 (3 3 (:REWRITE |(expt 1/c n)|))
 (3 3 (:REWRITE |(expt (- x) n)|))
 (3 3 (:REWRITE |(< (+ (- c) x) y)|))
 (3 3 (:REWRITE |(< (* x y) 0)|))
 (3 3 (:META META-INTEGERP-CORRECT))
 (3 1 (:REWRITE RTL::BVECP-EXACTP))
 (2 2 (:TYPE-PRESCRIPTION RTL::BVECP))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:REWRITE |(< 0 (* x y))|))
 (2 2 (:REWRITE |(< (/ x) 0)|))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-ONE))
 (1 1 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (1 1 (:REWRITE |(- (- x))|))
 (1 1 (:REWRITE |(+ 0 x)|)))
(RTL::EXPO-Q-16
 (1181
  1181
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1181
      1181
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1181
     1181
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1181 1181
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (869 869
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (869 869
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (334 91 (:REWRITE DEFAULT-PLUS-2))
 (264 63 (:REWRITE DEFAULT-LESS-THAN-2))
 (259 63 (:REWRITE DEFAULT-LESS-THAN-1))
 (206 10 (:REWRITE ODD-EXPT-THM))
 (190 30 (:REWRITE DEFAULT-TIMES-2))
 (173 91 (:REWRITE DEFAULT-PLUS-1))
 (139 39 (:REWRITE SIMPLIFY-SUMS-<))
 (124 30 (:REWRITE DEFAULT-TIMES-1))
 (120 4 (:REWRITE RTL::R-EXACTP-6))
 (79 55
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (73 55 (:REWRITE |(< (/ x) (/ y))|))
 (67 55 (:REWRITE |(< (- x) (- y))|))
 (66 18 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (65 61
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (65 61
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (63 63 (:REWRITE THE-FLOOR-BELOW))
 (63 63 (:REWRITE THE-FLOOR-ABOVE))
 (61 61
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (55 55 (:REWRITE INTEGERP-<-CONSTANT))
 (55 55 (:REWRITE CONSTANT-<-INTEGERP))
 (55 55
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (55 55
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (55 55
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (55 55
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (55 55 (:REWRITE |(< c (- x))|))
 (55 55
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (55 55
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (55 55
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (55 55 (:REWRITE |(< (- x) c)|))
 (50 26 (:REWRITE DEFAULT-MINUS))
 (42 6
     (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (42 6
     (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (41 2 (:LINEAR EXPT->=-1-ONE))
 (40 2 (:LINEAR EXPT->-1-ONE))
 (38 2
     (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (36 12 (:REWRITE RTL::BVECP-EXACTP))
 (36 9 (:REWRITE RATIONALP-X))
 (36 2 (:LINEAR EXPT-X->=-X))
 (36 2 (:LINEAR EXPT-X->-X))
 (35 23 (:REWRITE INTEGERP-MINUS-X))
 (29 29
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (28 10 (:REWRITE DEFAULT-DIVIDE))
 (24 24 (:TYPE-PRESCRIPTION RTL::BVECP))
 (23 23 (:REWRITE REDUCE-INTEGERP-+))
 (23 23 (:META META-INTEGERP-CORRECT))
 (18 14 (:REWRITE DEFAULT-EXPT-2))
 (14 14 (:REWRITE DEFAULT-EXPT-1))
 (14 14 (:REWRITE |(expt 1/c n)|))
 (14 14 (:REWRITE |(expt (- x) n)|))
 (12 12 (:REWRITE |(< (+ c/d x) y)|))
 (12 12 (:REWRITE |(< (+ (- c) x) y)|))
 (11 11 (:REWRITE |(< y (+ (- c) x))|))
 (11 11 (:REWRITE |(< x (+ c/d y))|))
 (11 11 (:REWRITE |(+ c (+ d x))|))
 (10 10
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (9 9 (:REWRITE REDUCE-RATIONALP-+))
 (9 9 (:REWRITE REDUCE-RATIONALP-*))
 (9 9 (:REWRITE RATIONALP-MINUS-X))
 (9 9 (:META META-RATIONALP-CORRECT))
 (6 6 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (6 6 (:REWRITE |(< (/ x) 0)|))
 (6 6 (:REWRITE |(< (* x y) 0)|))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (4 4 (:REWRITE FOLD-CONSTS-IN-+))
 (4 4 (:REWRITE |(< 0 (/ x))|))
 (4 4 (:REWRITE |(< 0 (* x y))|))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (3 3 (:REWRITE ZP-OPEN))
 (3 3 (:REWRITE |(- (* c x))|))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2 (:REWRITE |(* c (* d x))|))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-ONE)))
(RTL::EXPO-Q-17)
(RTL::EXPO-Q-18
 (758 758
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (758 758
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (758 758
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (496
  496
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (496 496
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (496
     496
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (496 496
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (496 496
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (335 81 (:REWRITE DEFAULT-PLUS-2))
 (258 51
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (221 62 (:REWRITE DEFAULT-LESS-THAN-2))
 (219 81 (:REWRITE DEFAULT-PLUS-1))
 (185 62 (:REWRITE DEFAULT-LESS-THAN-1))
 (134 40 (:REWRITE SIMPLIFY-SUMS-<))
 (114 6 (:REWRITE ODD-EXPT-THM))
 (89 59
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (80 59 (:REWRITE |(< (- x) (- y))|))
 (62 62 (:REWRITE THE-FLOOR-BELOW))
 (62 62 (:REWRITE THE-FLOOR-ABOVE))
 (60 60
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (60 60
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (60 60
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (59 59 (:REWRITE INTEGERP-<-CONSTANT))
 (59 59 (:REWRITE CONSTANT-<-INTEGERP))
 (59 59
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (59 59
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (59 59
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (59 59
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (59 59 (:REWRITE |(< c (- x))|))
 (59 59
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (59 59
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (59 59
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (59 59 (:REWRITE |(< (/ x) (/ y))|))
 (59 59 (:REWRITE |(< (- x) c)|))
 (52 19 (:REWRITE DEFAULT-MINUS))
 (40 1 (:LINEAR EXPT->=-1-ONE))
 (40 1 (:LINEAR EXPT-<=-1-TWO))
 (39 1 (:LINEAR EXPT->-1-ONE))
 (39 1 (:LINEAR EXPT-<-1-TWO))
 (37 25 (:REWRITE INTEGERP-MINUS-X))
 (36 12 (:REWRITE RTL::BVECP-EXACTP))
 (36 9 (:REWRITE RATIONALP-X))
 (35 1 (:LINEAR EXPT-X->=-X))
 (35 1 (:LINEAR EXPT-X->-X))
 (32 11 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (30 1 (:REWRITE RTL::R-EXACTP-6))
 (25 25 (:REWRITE REDUCE-INTEGERP-+))
 (25 25 (:META META-INTEGERP-CORRECT))
 (24 24 (:TYPE-PRESCRIPTION RTL::BVECP))
 (19 19
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (13 13 (:REWRITE |(< (+ c/d x) y)|))
 (13 13 (:REWRITE |(< (+ (- c) x) y)|))
 (11 11 (:REWRITE |(< y (+ (- c) x))|))
 (11 11 (:REWRITE |(< x (+ c/d y))|))
 (9 9 (:REWRITE REDUCE-RATIONALP-+))
 (9 9 (:REWRITE REDUCE-RATIONALP-*))
 (9 9 (:REWRITE RATIONALP-MINUS-X))
 (9 9 (:META META-RATIONALP-CORRECT))
 (6 6
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (6 6
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (6 6 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (6 6 (:REWRITE DEFAULT-TIMES-2))
 (6 6 (:REWRITE DEFAULT-TIMES-1))
 (6 6 (:REWRITE DEFAULT-DIVIDE))
 (6 6 (:REWRITE |(< (/ x) 0)|))
 (6 6 (:REWRITE |(< (* x y) 0)|))
 (5 5 (:REWRITE DEFAULT-EXPT-2))
 (5 5 (:REWRITE DEFAULT-EXPT-1))
 (5 5 (:REWRITE |(expt 1/c n)|))
 (5 5 (:REWRITE |(expt (- x) n)|))
 (3 3 (:REWRITE ZP-OPEN))
 (3 3 (:REWRITE |(- (* c x))|))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:REWRITE |(< 0 (* x y))|))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (2 1
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (2 1
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
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
 (1 1
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (1 1
    (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<))
 (1 1 (:LINEAR EXPT->=-1-TWO))
 (1 1 (:LINEAR EXPT->-1-TWO))
 (1 1 (:LINEAR EXPT-<=-1-ONE))
 (1 1 (:LINEAR EXPT-<-1-ONE)))
(RTL::EXPO-Q-19
 (3630 3630
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (3630 3630
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (3630 3630
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (2115
  2115
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (2115
      2115
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (2115
     2115
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (2115 2115
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (2115 2115
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (1480 404 (:REWRITE DEFAULT-PLUS-2))
 (1189 255
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (900 297 (:REWRITE DEFAULT-LESS-THAN-2))
 (877 404 (:REWRITE DEFAULT-PLUS-1))
 (748 297 (:REWRITE DEFAULT-LESS-THAN-1))
 (663 203 (:REWRITE SIMPLIFY-SUMS-<))
 (528 28 (:REWRITE ODD-EXPT-THM))
 (442 292
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (344 292 (:REWRITE |(< (- x) (- y))|))
 (297 297 (:REWRITE THE-FLOOR-BELOW))
 (297 297 (:REWRITE THE-FLOOR-ABOVE))
 (293 293
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (293 293
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (293 293
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (292 292 (:REWRITE INTEGERP-<-CONSTANT))
 (292 292 (:REWRITE CONSTANT-<-INTEGERP))
 (292 292
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (292 292
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (292 292
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (292 292
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (292 292 (:REWRITE |(< c (- x))|))
 (292 292
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (292 292
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (292 292
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (292 292 (:REWRITE |(< (/ x) (/ y))|))
 (292 292 (:REWRITE |(< (- x) c)|))
 (222 11 (:REWRITE RTL::R-EXACTP-6))
 (216 72 (:REWRITE RTL::BVECP-EXACTP))
 (196 49 (:REWRITE RATIONALP-X))
 (191 87 (:REWRITE DEFAULT-MINUS))
 (179 127 (:REWRITE INTEGERP-MINUS-X))
 (144 144 (:TYPE-PRESCRIPTION RTL::BVECP))
 (127 127 (:REWRITE REDUCE-INTEGERP-+))
 (127 127 (:META META-INTEGERP-CORRECT))
 (104 52 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (89 89
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (54 54 (:REWRITE |(< (+ c/d x) y)|))
 (54 54 (:REWRITE |(< (+ (- c) x) y)|))
 (49 49 (:REWRITE REDUCE-RATIONALP-+))
 (49 49 (:REWRITE REDUCE-RATIONALP-*))
 (49 49 (:REWRITE RATIONALP-MINUS-X))
 (49 49 (:META META-RATIONALP-CORRECT))
 (42 3 (:LINEAR EXPT->=-1-ONE))
 (41 3 (:LINEAR EXPT->-1-ONE))
 (37 3 (:LINEAR EXPT-X->=-X))
 (37 3 (:LINEAR EXPT-X->-X))
 (32 32 (:REWRITE |(< y (+ (- c) x))|))
 (32 32 (:REWRITE |(< x (+ c/d y))|))
 (30 30 (:REWRITE DEFAULT-EXPT-2))
 (30 30 (:REWRITE DEFAULT-EXPT-1))
 (30 30 (:REWRITE |(expt 1/c n)|))
 (30 30 (:REWRITE |(expt (- x) n)|))
 (28 28
     (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (26 26 (:REWRITE |(< (/ x) 0)|))
 (26 26 (:REWRITE |(< (* x y) 0)|))
 (25 25
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (25 25
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (25 25 (:REWRITE DEFAULT-TIMES-2))
 (25 25 (:REWRITE DEFAULT-TIMES-1))
 (25 25 (:REWRITE DEFAULT-DIVIDE))
 (15 15 (:REWRITE ZP-OPEN))
 (14 14
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (14 14
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (14 14 (:REWRITE |(< 0 (/ x))|))
 (14 14 (:REWRITE |(< 0 (* x y))|))
 (13 13 (:REWRITE |(- (* c x))|))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (6 6
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (4 3
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (4 3
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (3 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (3 3
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (3 3
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (3 3
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (3 3 (:REWRITE |(equal c (/ x))|))
 (3 3 (:REWRITE |(equal c (- x))|))
 (3 3 (:REWRITE |(equal (/ x) c)|))
 (3 3 (:REWRITE |(equal (/ x) (/ y))|))
 (3 3 (:REWRITE |(equal (- x) c)|))
 (3 3 (:REWRITE |(equal (- x) (- y))|))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<))
 (3 3 (:LINEAR EXPT->=-1-TWO))
 (3 3 (:LINEAR EXPT->-1-TWO))
 (3 3 (:LINEAR EXPT-<=-1-ONE))
 (3 3 (:LINEAR EXPT-<-1-ONE))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (1 1
    (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|)))
(RTL::EXPO-Q-20
 (131
  131
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (131 131
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (131
     131
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (131 131
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (71 2 (:LINEAR EXPT->=-1-ONE))
 (64 6 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (60 6
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (60 6
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (50 1
     (:REWRITE EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (32 5 (:REWRITE |(< (- x) c)|))
 (25 3 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (22 4 (:REWRITE DEFAULT-TIMES-2))
 (21 2 (:REWRITE |(+ y (+ x z))|))
 (18 6 (:REWRITE NORMALIZE-ADDENDS))
 (15 6 (:REWRITE DEFAULT-LESS-THAN-2))
 (15 6 (:REWRITE DEFAULT-LESS-THAN-1))
 (14 12 (:REWRITE DEFAULT-PLUS-1))
 (12 12 (:REWRITE DEFAULT-PLUS-2))
 (10 10 (:REWRITE DEFAULT-EXPT-2))
 (10 10 (:REWRITE DEFAULT-EXPT-1))
 (10 10 (:REWRITE |(expt 1/c n)|))
 (10 10 (:REWRITE |(expt (- x) n)|))
 (6 6
    (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (6 6
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (6 6 (:REWRITE THE-FLOOR-BELOW))
 (6 6 (:REWRITE THE-FLOOR-ABOVE))
 (6 6
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (6 6
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (6 6 (:REWRITE DEFAULT-MINUS))
 (5 5
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (5 5
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (5 5
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (5 5
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (5 5 (:REWRITE |(< c (- x))|))
 (5 5
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (5 5
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (5 5
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (5 5
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (5 5 (:REWRITE |(< (/ x) (/ y))|))
 (5 5 (:REWRITE |(< (- x) (- y))|))
 (5 4 (:REWRITE DEFAULT-TIMES-1))
 (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (4 4 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (4 4
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (4 4 (:REWRITE INTEGERP-<-CONSTANT))
 (4 4 (:REWRITE CONSTANT-<-INTEGERP))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (4 2 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
 (4 1 (:REWRITE RATIONALP-X))
 (4 1 (:REWRITE |(+ c (+ d x))|))
 (3 3 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (3 3
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (2 2 (:REWRITE SIMPLIFY-SUMS-<))
 (2 2 (:REWRITE REDUCE-INTEGERP-+))
 (2 2 (:REWRITE INTEGERP-MINUS-X))
 (2 2 (:REWRITE |(+ x (- x))|))
 (2 2 (:META META-INTEGERP-CORRECT))
 (2 2 (:LINEAR EXPT-X->=-X))
 (2 2 (:LINEAR EXPT-X->-X))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT->-1-ONE))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-ONE))
 (1 1 (:REWRITE REDUCE-RATIONALP-+))
 (1 1 (:REWRITE REDUCE-RATIONALP-*))
 (1 1 (:REWRITE RATIONALP-MINUS-X))
 (1 1 (:REWRITE |(< y (+ (- c) x))|))
 (1 1 (:REWRITE |(< x (+ c/d y))|))
 (1 1 (:REWRITE |(< (+ c/d x) y)|))
 (1 1 (:REWRITE |(< (* x y) 0)|))
 (1 1 (:REWRITE |(- (- x))|))
 (1 1 (:REWRITE |(+ 0 x)|))
 (1 1 (:META META-RATIONALP-CORRECT)))
(RTL::EXPO-Q-21
 (220
  220
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (220 220
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (220
     220
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (220 220
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (220 220
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (144 27 (:REWRITE DEFAULT-PLUS-2))
 (103 27 (:REWRITE DEFAULT-PLUS-1))
 (94 13
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (86 14 (:REWRITE DEFAULT-LESS-THAN-2))
 (45 9 (:REWRITE SIMPLIFY-SUMS-<))
 (32 14 (:REWRITE DEFAULT-LESS-THAN-1))
 (31 13 (:REWRITE |(< (- x) (- y))|))
 (28 10 (:REWRITE DEFAULT-MINUS))
 (22 4 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (17 2 (:REWRITE ODD-EXPT-THM))
 (15 2 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (14 14 (:REWRITE THE-FLOOR-BELOW))
 (14 14 (:REWRITE THE-FLOOR-ABOVE))
 (13 13 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (13 13
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (13 13
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (13 13
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (13 13
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
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
 (9 9
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (8 8 (:REWRITE DEFAULT-EXPT-2))
 (8 8 (:REWRITE DEFAULT-EXPT-1))
 (8 8 (:REWRITE |(expt 1/c n)|))
 (8 8 (:REWRITE |(expt (- x) n)|))
 (6 6 (:REWRITE |(< y (+ (- c) x))|))
 (6 6 (:REWRITE |(< x (+ c/d y))|))
 (5 5 (:REWRITE |(< (+ c/d x) y)|))
 (5 5 (:REWRITE |(< (+ (- c) x) y)|))
 (4 4 (:REWRITE REDUCE-INTEGERP-+))
 (4 4 (:REWRITE INTEGERP-MINUS-X))
 (4 4 (:META META-INTEGERP-CORRECT))
 (4 1 (:REWRITE RATIONALP-X))
 (4 1 (:REWRITE |(integerp (- x))|))
 (3 1 (:REWRITE RTL::BVECP-EXACTP))
 (2 2 (:TYPE-PRESCRIPTION RTL::BVECP))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (1 1 (:REWRITE REDUCE-RATIONALP-+))
 (1 1 (:REWRITE REDUCE-RATIONALP-*))
 (1 1 (:REWRITE RATIONALP-MINUS-X))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (* x y) 0)|))
 (1 1 (:META META-RATIONALP-CORRECT))
 (1 1 (:LINEAR EXPT-X->=-X))
 (1 1 (:LINEAR EXPT-X->-X))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<))
 (1 1 (:LINEAR EXPT->=-1-TWO))
 (1 1 (:LINEAR EXPT->=-1-ONE))
 (1 1 (:LINEAR EXPT->-1-TWO))
 (1 1 (:LINEAR EXPT->-1-ONE))
 (1 1 (:LINEAR EXPT-<=-1-ONE))
 (1 1 (:LINEAR EXPT-<-1-ONE)))
(RTL::EXPO-Q-22)
(RTL::EXPO-Q-23
 (3410 7 (:REWRITE RTL::R-EXACTP-6))
 (3238 111
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (2306 95 (:REWRITE |(< (- x) c)|))
 (1655 23 (:REWRITE |(< 0 (/ x))|))
 (1565
  1565
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1565
      1565
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1565
     1565
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1565 1565
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1235 218 (:REWRITE DEFAULT-PLUS-2))
 (677 218 (:REWRITE DEFAULT-PLUS-1))
 (490 112 (:REWRITE DEFAULT-LESS-THAN-2))
 (410 86
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (402 96 (:REWRITE DEFAULT-MINUS))
 (328 112 (:REWRITE DEFAULT-LESS-THAN-1))
 (241 12 (:LINEAR EXPT->=-1-ONE))
 (210 102 (:REWRITE |(< (- x) (- y))|))
 (178 24
      (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (168 14 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (166 12 (:LINEAR EXPT->-1-ONE))
 (162 9 (:REWRITE |(+ c (+ d x))|))
 (135 27 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (131 95 (:REWRITE |(< c (- x))|))
 (112 112 (:REWRITE THE-FLOOR-BELOW))
 (112 112 (:REWRITE THE-FLOOR-ABOVE))
 (111 111
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (111 111
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (109 109 (:REWRITE DEFAULT-EXPT-2))
 (109 109 (:REWRITE DEFAULT-EXPT-1))
 (109 109 (:REWRITE |(expt 1/c n)|))
 (109 109 (:REWRITE |(expt (- x) n)|))
 (107 62 (:REWRITE SIMPLIFY-SUMS-<))
 (103 12 (:LINEAR EXPT-X->=-X))
 (103 12 (:LINEAR EXPT-X->-X))
 (102 102
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (102 102
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (102 102
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (102 102
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (102 102
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (102 102
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (102 102
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (102 102
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (102 102 (:REWRITE |(< (/ x) (/ y))|))
 (86 86 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (86 86
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (86 86 (:REWRITE INTEGERP-<-CONSTANT))
 (86 86 (:REWRITE CONSTANT-<-INTEGERP))
 (82 30 (:REWRITE RTL::BVECP-EXACTP))
 (70 16 (:REWRITE ODD-EXPT-THM))
 (70 7 (:REWRITE DEFAULT-DIVIDE))
 (68 68
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (54 7 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (52 52 (:TYPE-PRESCRIPTION RTL::BVECP))
 (49 7 (:REWRITE |(/ (expt x n))|))
 (40 4 (:REWRITE DEFAULT-TIMES-2))
 (31 31 (:REWRITE |(< (+ c/d x) y)|))
 (24 24
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (24 24
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (24 24
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (23 23 (:REWRITE |(< 0 (* x y))|))
 (22 22 (:REWRITE |(< (+ (- c) x) y)|))
 (22 7 (:REWRITE RATIONALP-X))
 (21 21 (:REWRITE |(< y (+ (- c) x))|))
 (21 21 (:REWRITE |(< x (+ c/d y))|))
 (20 5 (:REWRITE |(integerp (- x))|))
 (19 19 (:REWRITE REDUCE-INTEGERP-+))
 (19 19 (:REWRITE INTEGERP-MINUS-X))
 (19 19 (:META META-INTEGERP-CORRECT))
 (17 17 (:REWRITE |(< (* x y) 0)|))
 (15 15 (:REWRITE |(< (/ x) 0)|))
 (14 14 (:LINEAR EXPT-LINEAR-LOWER-<))
 (12 12
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (12 12
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (12 12 (:LINEAR EXPT-LINEAR-UPPER-<))
 (12 12 (:LINEAR EXPT->=-1-TWO))
 (12 12 (:LINEAR EXPT->-1-TWO))
 (12 12 (:LINEAR EXPT-<=-1-ONE))
 (12 12 (:LINEAR EXPT-<-1-ONE))
 (12 8
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (12 8
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (8 8 (:REWRITE SIMPLIFY-SUMS-EQUAL))
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
 (7 7 (:REWRITE REDUCE-RATIONALP-+))
 (7 7 (:REWRITE REDUCE-RATIONALP-*))
 (7 7 (:REWRITE RATIONALP-MINUS-X))
 (7 7 (:META META-RATIONALP-CORRECT))
 (4 4 (:REWRITE DEFAULT-TIMES-1)))
(RTL::EXPO-Q-24
 (251
  251
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (251 251
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (251
     251
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (251 251
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (251 251
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (135 135
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (135 135
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (135 135
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (135 135
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (96 24 (:REWRITE DEFAULT-LESS-THAN-2))
 (67 22
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (52 34 (:REWRITE DEFAULT-PLUS-2))
 (40 34 (:REWRITE DEFAULT-PLUS-1))
 (35 17 (:REWRITE SIMPLIFY-SUMS-<))
 (32 23
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (30 4 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (24 24 (:REWRITE THE-FLOOR-BELOW))
 (24 24 (:REWRITE THE-FLOOR-ABOVE))
 (24 24 (:REWRITE DEFAULT-LESS-THAN-1))
 (23 23 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (23 23
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (23 23
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (23 23
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (23 23
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (23 23 (:REWRITE INTEGERP-<-CONSTANT))
 (23 23 (:REWRITE CONSTANT-<-INTEGERP))
 (23 23
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (23 23
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (23 23
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (23 23
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (23 23 (:REWRITE |(< c (- x))|))
 (23 23
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (23 23
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (23 23
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (23 23 (:REWRITE |(< (/ x) (/ y))|))
 (23 23 (:REWRITE |(< (- x) c)|))
 (23 23 (:REWRITE |(< (- x) (- y))|))
 (21 7 (:REWRITE RTL::BVECP-EXACTP))
 (20 5 (:REWRITE RATIONALP-X))
 (14 14 (:TYPE-PRESCRIPTION RTL::BVECP))
 (12 12 (:REWRITE REDUCE-INTEGERP-+))
 (12 12 (:REWRITE INTEGERP-MINUS-X))
 (12 12 (:REWRITE DEFAULT-MINUS))
 (12 12 (:META META-INTEGERP-CORRECT))
 (8 2 (:REWRITE |(integerp (- x))|))
 (7 7
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (7 7 (:REWRITE DEFAULT-EXPT-2))
 (7 7 (:REWRITE DEFAULT-EXPT-1))
 (7 7 (:REWRITE |(expt 1/c n)|))
 (7 7 (:REWRITE |(expt (- x) n)|))
 (7 7 (:REWRITE |(< (+ c/d x) y)|))
 (7 7 (:REWRITE |(< (+ (- c) x) y)|))
 (6 6 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (5 5 (:REWRITE REDUCE-RATIONALP-+))
 (5 5 (:REWRITE REDUCE-RATIONALP-*))
 (5 5 (:REWRITE RATIONALP-MINUS-X))
 (5 5 (:REWRITE DEFAULT-TIMES-2))
 (5 5 (:REWRITE DEFAULT-TIMES-1))
 (5 5 (:META META-RATIONALP-CORRECT))
 (3 3 (:REWRITE ZP-OPEN))
 (3 3
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (3 3 (:REWRITE DEFAULT-DIVIDE))
 (3 3 (:REWRITE |(< (/ x) 0)|))
 (3 3 (:REWRITE |(< (* x y) 0)|))
 (2 2 (:REWRITE |(< y (+ (- c) x))|))
 (2 2 (:REWRITE |(< x (+ c/d y))|))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (1 1
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (1 1
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (1 1
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (1 1
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (1 1
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (1 1 (:REWRITE |(equal c (/ x))|))
 (1 1 (:REWRITE |(equal c (- x))|))
 (1 1 (:REWRITE |(equal (/ x) c)|))
 (1 1 (:REWRITE |(equal (/ x) (/ y))|))
 (1 1 (:REWRITE |(equal (- x) c)|))
 (1 1 (:REWRITE |(equal (- x) (- y))|))
 (1 1 (:REWRITE |(< 0 (/ x))|))
 (1 1 (:REWRITE |(< 0 (* x y))|))
 (1 1 (:LINEAR EXPT-X->=-X))
 (1 1 (:LINEAR EXPT-X->-X))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<))
 (1 1 (:LINEAR EXPT->=-1-TWO))
 (1 1 (:LINEAR EXPT->=-1-ONE))
 (1 1 (:LINEAR EXPT->-1-TWO))
 (1 1 (:LINEAR EXPT->-1-ONE))
 (1 1 (:LINEAR EXPT-<=-1-ONE))
 (1 1 (:LINEAR EXPT-<-1-ONE)))
(RTL::EXPO-Q
 (11705 11705
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (11705 11705
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (9838
  9838
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (9838
      9838
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (9838
     9838
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (9838 9838
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (9838 9838
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (4402 100 (:REWRITE RTL::R-EXACTP-6))
 (3822 1122 (:REWRITE DEFAULT-PLUS-2))
 (3337 1219 (:REWRITE DEFAULT-LESS-THAN-2))
 (3123 123 (:LINEAR EXPT->=-1-ONE))
 (2379 1219 (:REWRITE DEFAULT-LESS-THAN-1))
 (2301 1122 (:REWRITE DEFAULT-PLUS-1))
 (2215 1119 (:REWRITE |(< (- x) c)|))
 (1749 1119
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (1629 1165
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (1243 1119 (:REWRITE |(< (- x) (- y))|))
 (1219 1219 (:REWRITE THE-FLOOR-BELOW))
 (1219 1219 (:REWRITE THE-FLOOR-ABOVE))
 (1165 1165
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (1165 1165
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (1149 1119
       (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (1119 1119
       (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (1119 1119
       (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (1119 1119
       (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (1119 1119 (:REWRITE |(< c (- x))|))
 (1119 1119
       (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (1119 1119
       (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (1119 1119
       (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (1119 1119 (:REWRITE |(< (/ x) (/ y))|))
 (1095 1095 (:REWRITE INTEGERP-<-CONSTANT))
 (1095 1095 (:REWRITE CONSTANT-<-INTEGERP))
 (531 407 (:REWRITE INTEGERP-MINUS-X))
 (465 40
      (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (463 21
      (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (460 115 (:REWRITE RATIONALP-X))
 (453 269 (:REWRITE DEFAULT-MINUS))
 (453 151 (:REWRITE RTL::BVECP-EXACTP))
 (428 424 (:REWRITE DEFAULT-EXPT-2))
 (424 424 (:REWRITE DEFAULT-EXPT-1))
 (408 408 (:REWRITE |(expt 1/c n)|))
 (408 408 (:REWRITE |(expt (- x) n)|))
 (407 407 (:REWRITE REDUCE-INTEGERP-+))
 (407 407 (:META META-INTEGERP-CORRECT))
 (369 309 (:REWRITE DEFAULT-TIMES-2))
 (309 309 (:REWRITE DEFAULT-TIMES-1))
 (302 302 (:TYPE-PRESCRIPTION RTL::BVECP))
 (280 280
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (247 123 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (246 246
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4E))
 (246 246
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
 (246 246
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
 (246 246
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
 (246 246
      (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (246 246
      (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (246 246
      (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (246 246
      (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (188 14
      (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (188 14
      (:REWRITE |(< x (/ y)) with (< y 0)|))
 (182 182 (:REWRITE |(< (+ c/d x) y)|))
 (168 168 (:REWRITE DEFAULT-DIVIDE))
 (162 162
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (155 155
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (146 146
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (146 146
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (146 146 (:REWRITE |(equal c (/ x))|))
 (146 146 (:REWRITE |(equal (/ x) (/ y))|))
 (146 146 (:REWRITE |(equal (- x) (- y))|))
 (140 140
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (140 140 (:REWRITE |(equal c (- x))|))
 (140 140 (:REWRITE |(equal (- x) c)|))
 (137 72
      (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (129 129 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (123 123 (:LINEAR EXPT-X->=-X))
 (123 123 (:LINEAR EXPT-X->-X))
 (123 123 (:LINEAR EXPT-LINEAR-UPPER-<))
 (123 123 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (123 123 (:LINEAR EXPT-LINEAR-LOWER-<))
 (123 123 (:LINEAR EXPT->=-1-TWO))
 (123 123 (:LINEAR EXPT->-1-TWO))
 (123 123 (:LINEAR EXPT->-1-ONE))
 (123 123 (:LINEAR EXPT-<=-1-ONE))
 (123 123 (:LINEAR EXPT-<-1-ONE))
 (118 118 (:REWRITE |(< (* x y) 0)|))
 (115 115 (:REWRITE REDUCE-RATIONALP-+))
 (115 115 (:REWRITE REDUCE-RATIONALP-*))
 (115 115 (:REWRITE RATIONALP-MINUS-X))
 (115 115 (:META META-RATIONALP-CORRECT))
 (110 110 (:REWRITE |(< (/ x) 0)|))
 (106 106 (:REWRITE |(< y (+ (- c) x))|))
 (106 106 (:REWRITE |(< x (+ c/d y))|))
 (101 14
      (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (73 73
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (49 49
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (49 49
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (44 44 (:REWRITE ZP-OPEN))
 (40 40
     (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (39 39 (:REWRITE |(< 0 (* x y))|))
 (28 28 (:REWRITE |(< 0 (/ x))|))
 (28 28 (:REWRITE |(- (* c x))|))
 (25 25
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (25 25
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (21 21
     (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (20 5 (:REWRITE |(integerp (- x))|))
 (15 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (15 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (15 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (15 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (6 6 (:REWRITE |(not (equal x (/ y)))|))
 (6 6 (:REWRITE |(equal x (/ y))|))
 (5 5 (:REWRITE |(equal (+ (- c) x) y)|))
 (4 4 (:REWRITE FOLD-CONSTS-IN-+)))
(RTL::EXPO-Q-ALT
 (2054 2054
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (2054 2054
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (2054 2054
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (1225
  1225
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1225
      1225
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1225
     1225
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1225 1225
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1225 1225
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (821 14 (:REWRITE RTL::R-EXACTP-6))
 (605 165 (:REWRITE DEFAULT-PLUS-2))
 (530 124
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (485 187 (:REWRITE DEFAULT-LESS-THAN-2))
 (397 187 (:REWRITE DEFAULT-LESS-THAN-1))
 (372 165 (:REWRITE DEFAULT-PLUS-1))
 (304 178
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (300 184
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (295 103 (:REWRITE SIMPLIFY-SUMS-<))
 (232 178 (:REWRITE |(< (- x) c)|))
 (228 12 (:REWRITE ODD-EXPT-THM))
 (202 178 (:REWRITE |(< (- x) (- y))|))
 (187 187 (:REWRITE THE-FLOOR-BELOW))
 (187 187 (:REWRITE THE-FLOOR-ABOVE))
 (184 184
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (184 184
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (182 5 (:LINEAR EXPT->=-1-ONE))
 (178 178
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (178 178
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (178 178
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (178 178
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (178 178 (:REWRITE |(< c (- x))|))
 (178 178
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (178 178
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (178 178
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (178 178 (:REWRITE |(< (/ x) (/ y))|))
 (176 176 (:REWRITE INTEGERP-<-CONSTANT))
 (176 176 (:REWRITE CONSTANT-<-INTEGERP))
 (135 5
      (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (134 9
      (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (102 78 (:REWRITE INTEGERP-MINUS-X))
 (96 24 (:REWRITE RATIONALP-X))
 (81 27 (:REWRITE RTL::BVECP-EXACTP))
 (78 78 (:REWRITE REDUCE-INTEGERP-+))
 (78 78 (:META META-INTEGERP-CORRECT))
 (75 35 (:REWRITE DEFAULT-MINUS))
 (54 54 (:TYPE-PRESCRIPTION RTL::BVECP))
 (45 21 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (43 5 (:LINEAR EXPT->-1-ONE))
 (39 5 (:LINEAR EXPT-X->=-X))
 (39 5 (:LINEAR EXPT-X->-X))
 (37 37
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (32 20
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (32 20
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (25 25 (:REWRITE |(< (+ c/d x) y)|))
 (24 24 (:REWRITE REDUCE-RATIONALP-+))
 (24 24 (:REWRITE REDUCE-RATIONALP-*))
 (24 24 (:REWRITE RATIONALP-MINUS-X))
 (24 24 (:META META-RATIONALP-CORRECT))
 (23 23 (:REWRITE |(< (+ (- c) x) y)|))
 (21 21 (:REWRITE DEFAULT-EXPT-2))
 (21 21 (:REWRITE DEFAULT-EXPT-1))
 (20 20 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (20 20
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (20 20
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (20 20
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (20 20 (:REWRITE |(expt 1/c n)|))
 (20 20 (:REWRITE |(expt (- x) n)|))
 (20 20 (:REWRITE |(equal c (/ x))|))
 (20 20 (:REWRITE |(equal c (- x))|))
 (20 20 (:REWRITE |(equal (/ x) c)|))
 (20 20 (:REWRITE |(equal (/ x) (/ y))|))
 (20 20 (:REWRITE |(equal (- x) c)|))
 (20 20 (:REWRITE |(equal (- x) (- y))|))
 (18 18
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (18 18
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (18 18 (:REWRITE DEFAULT-TIMES-2))
 (18 18 (:REWRITE DEFAULT-TIMES-1))
 (18 18 (:REWRITE DEFAULT-DIVIDE))
 (16 16 (:REWRITE |(< y (+ (- c) x))|))
 (16 16 (:REWRITE |(< x (+ c/d y))|))
 (13 13 (:REWRITE |(< (* x y) 0)|))
 (12 12
     (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (11 11 (:REWRITE |(< (/ x) 0)|))
 (10 10
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (10 10
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (10 10
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (10 10
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (9 9
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (8 8 (:REWRITE ZP-OPEN))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (5 5
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (5 5 (:REWRITE |(- (* c x))|))
 (5 5 (:LINEAR EXPT-LINEAR-UPPER-<))
 (5 5 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (5 5 (:LINEAR EXPT-LINEAR-LOWER-<))
 (5 5 (:LINEAR EXPT->=-1-TWO))
 (5 5 (:LINEAR EXPT->-1-TWO))
 (5 5 (:LINEAR EXPT-<=-1-ONE))
 (5 5 (:LINEAR EXPT-<-1-ONE))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:REWRITE |(< 0 (* x y))|)))
(RTL::R-POS-1
 (805 805
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (805 805
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (805 805
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (805 805
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (397 6 (:REWRITE RTL::R-EXACTP-6))
 (281
  281
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (281 281
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (281
     281
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (281 281
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (281 281
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (281 281
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (247 62 (:REWRITE DEFAULT-PLUS-2))
 (241 47
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (193 53 (:REWRITE DEFAULT-LESS-THAN-2))
 (158 158
      (:TYPE-PRESCRIPTION RTL::FP+-POSITIVE))
 (143 53 (:REWRITE DEFAULT-LESS-THAN-1))
 (133 39 (:REWRITE SIMPLIFY-SUMS-<))
 (119 62 (:REWRITE DEFAULT-PLUS-1))
 (93 5 (:REWRITE ODD-EXPT-THM))
 (81 3
     (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (78 3
     (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (69 51
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (59 51 (:REWRITE |(< (- x) (- y))|))
 (53 53 (:REWRITE THE-FLOOR-BELOW))
 (53 53 (:REWRITE THE-FLOOR-ABOVE))
 (51 51
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (51 51
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (51 51
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (51 51 (:REWRITE INTEGERP-<-CONSTANT))
 (51 51 (:REWRITE CONSTANT-<-INTEGERP))
 (51 51
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (51 51
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (51 51
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (51 51
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (51 51 (:REWRITE |(< c (- x))|))
 (51 51
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (51 51
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (51 51
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (51 51 (:REWRITE |(< (/ x) (/ y))|))
 (51 51 (:REWRITE |(< (- x) c)|))
 (40 1 (:LINEAR EXPT->=-1-ONE))
 (40 1 (:LINEAR EXPT-<=-1-TWO))
 (39 1 (:LINEAR EXPT->-1-ONE))
 (39 1 (:LINEAR EXPT-<-1-TWO))
 (35 1 (:LINEAR EXPT-X->=-X))
 (35 1 (:LINEAR EXPT-X->-X))
 (29 13 (:REWRITE DEFAULT-MINUS))
 (27 9 (:REWRITE RTL::BVECP-EXACTP))
 (25 17 (:REWRITE INTEGERP-MINUS-X))
 (24 6 (:REWRITE RATIONALP-X))
 (20 20
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (18 18 (:TYPE-PRESCRIPTION RTL::BVECP))
 (17 17 (:REWRITE REDUCE-INTEGERP-+))
 (17 17 (:META META-INTEGERP-CORRECT))
 (16 8 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (10 10
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (10 10
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (10 10 (:REWRITE DEFAULT-TIMES-2))
 (10 10 (:REWRITE DEFAULT-TIMES-1))
 (10 10 (:REWRITE DEFAULT-DIVIDE))
 (10 10 (:REWRITE |(< y (+ (- c) x))|))
 (10 10 (:REWRITE |(< x (+ c/d y))|))
 (10 10 (:REWRITE |(< (+ c/d x) y)|))
 (10 10 (:REWRITE |(< (+ (- c) x) y)|))
 (10 10 (:REWRITE |(+ c (+ d x))|))
 (8 4 (:REWRITE DEFAULT-EXPT-2))
 (6 6 (:REWRITE REDUCE-RATIONALP-+))
 (6 6 (:REWRITE REDUCE-RATIONALP-*))
 (6 6 (:REWRITE RATIONALP-MINUS-X))
 (6 6 (:META META-RATIONALP-CORRECT))
 (5 5 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (5 5 (:REWRITE |(< (/ x) 0)|))
 (5 5 (:REWRITE |(< (* x y) 0)|))
 (5 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (5 3
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (5 3
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (4 4 (:REWRITE FOLD-CONSTS-IN-+))
 (4 4 (:REWRITE DEFAULT-EXPT-1))
 (4 4 (:REWRITE |(expt 1/c n)|))
 (4 4 (:REWRITE |(expt (- x) n)|))
 (3 3
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (3 3
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (3 3
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (3 3 (:REWRITE |(equal c (/ x))|))
 (3 3 (:REWRITE |(equal c (- x))|))
 (3 3 (:REWRITE |(equal (/ x) c)|))
 (3 3 (:REWRITE |(equal (/ x) (/ y))|))
 (3 3 (:REWRITE |(equal (- x) c)|))
 (3 3 (:REWRITE |(equal (- x) (- y))|))
 (3 3
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (3 3
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:REWRITE |(< 0 (* x y))|))
 (2 2 (:REWRITE |(- (* c x))|))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<))
 (1 1 (:LINEAR EXPT->=-1-TWO))
 (1 1 (:LINEAR EXPT->-1-TWO))
 (1 1 (:LINEAR EXPT-<=-1-ONE))
 (1 1 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-POS-2
 (787 787
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (787 787
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (787 787
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (787 787
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (463
  463
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (463 463
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (463
     463
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (463 463
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (463 463
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (463 463
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (424 7 (:REWRITE RTL::R-EXACTP-6))
 (302 74 (:REWRITE DEFAULT-PLUS-2))
 (289 55
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (237 63 (:REWRITE DEFAULT-LESS-THAN-2))
 (167 63 (:REWRITE DEFAULT-LESS-THAN-1))
 (145 45 (:REWRITE SIMPLIFY-SUMS-<))
 (141 74 (:REWRITE DEFAULT-PLUS-1))
 (127 7 (:REWRITE ODD-EXPT-THM))
 (81 3
     (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (80 2 (:LINEAR EXPT->=-1-ONE))
 (80 2 (:LINEAR EXPT-<=-1-TWO))
 (79 61
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (78 3
     (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (78 2 (:LINEAR EXPT->-1-ONE))
 (78 2 (:LINEAR EXPT-<-1-TWO))
 (70 2 (:LINEAR EXPT-X->=-X))
 (70 2 (:LINEAR EXPT-X->-X))
 (69 61 (:REWRITE |(< (- x) (- y))|))
 (63 63 (:REWRITE THE-FLOOR-BELOW))
 (63 63 (:REWRITE THE-FLOOR-ABOVE))
 (61 61
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (61 61
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (61 61
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (61 61 (:REWRITE INTEGERP-<-CONSTANT))
 (61 61 (:REWRITE CONSTANT-<-INTEGERP))
 (61 61
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (61 61
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (61 61
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (61 61
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (61 61 (:REWRITE |(< c (- x))|))
 (61 61
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (61 61
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (61 61
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (61 61 (:REWRITE |(< (/ x) (/ y))|))
 (61 61 (:REWRITE |(< (- x) c)|))
 (32 16 (:REWRITE DEFAULT-MINUS))
 (27 19 (:REWRITE INTEGERP-MINUS-X))
 (27 9 (:REWRITE RTL::BVECP-EXACTP))
 (24 24
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (24 6 (:REWRITE RATIONALP-X))
 (19 19 (:REWRITE REDUCE-INTEGERP-+))
 (19 19 (:META META-INTEGERP-CORRECT))
 (18 18 (:TYPE-PRESCRIPTION RTL::BVECP))
 (18 10 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (15 15 (:REWRITE |(< y (+ (- c) x))|))
 (15 15 (:REWRITE |(< x (+ c/d y))|))
 (14 14 (:REWRITE |(< (+ c/d x) y)|))
 (14 14 (:REWRITE |(< (+ (- c) x) y)|))
 (13 13 (:REWRITE |(+ c (+ d x))|))
 (11 11
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (11 11
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (11 11 (:REWRITE DEFAULT-TIMES-2))
 (11 11 (:REWRITE DEFAULT-TIMES-1))
 (11 11 (:REWRITE DEFAULT-DIVIDE))
 (10 5 (:REWRITE DEFAULT-EXPT-2))
 (7 7 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (7 7 (:REWRITE |(< (/ x) 0)|))
 (7 7 (:REWRITE |(< (* x y) 0)|))
 (6 6 (:REWRITE REDUCE-RATIONALP-+))
 (6 6 (:REWRITE REDUCE-RATIONALP-*))
 (6 6 (:REWRITE RATIONALP-MINUS-X))
 (6 6 (:META META-RATIONALP-CORRECT))
 (5 5 (:REWRITE FOLD-CONSTS-IN-+))
 (5 5 (:REWRITE DEFAULT-EXPT-1))
 (5 5 (:REWRITE |(expt 1/c n)|))
 (5 5 (:REWRITE |(expt (- x) n)|))
 (5 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (5 3
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (5 3
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (4 4 (:REWRITE |(< 0 (/ x))|))
 (4 4 (:REWRITE |(< 0 (* x y))|))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (3 3
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (3 3
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (3 3
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (3 3 (:REWRITE |(equal c (/ x))|))
 (3 3 (:REWRITE |(equal c (- x))|))
 (3 3 (:REWRITE |(equal (/ x) c)|))
 (3 3 (:REWRITE |(equal (/ x) (/ y))|))
 (3 3 (:REWRITE |(equal (- x) c)|))
 (3 3 (:REWRITE |(equal (- x) (- y))|))
 (3 3
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (3 3
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE |(- (* c x))|))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-POS-3 (16 8 (:REWRITE DEFAULT-TIMES-2))
              (12 3 (:REWRITE RATIONALP-X))
              (8 8 (:REWRITE DEFAULT-TIMES-1))
              (8 5
                 (:REWRITE |(< (/ x) c) positive c --- present in goal|))
              (6 6 (:REWRITE THE-FLOOR-BELOW))
              (6 6 (:REWRITE THE-FLOOR-ABOVE))
              (6 6
                 (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
              (6 6
                 (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
              (6 6 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
              (6 6 (:REWRITE DEFAULT-LESS-THAN-2))
              (6 6 (:REWRITE DEFAULT-LESS-THAN-1))
              (5 5 (:REWRITE INTEGERP-<-CONSTANT))
              (5 5 (:REWRITE CONSTANT-<-INTEGERP))
              (5 5
                 (:REWRITE |(< c (/ x)) positive c --- present in goal|))
              (5 5
                 (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
              (5 5
                 (:REWRITE |(< c (/ x)) negative c --- present in goal|))
              (5 5
                 (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
              (5 5 (:REWRITE |(< c (- x))|))
              (5 5
                 (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
              (5 5
                 (:REWRITE |(< (/ x) c) negative c --- present in goal|))
              (5 5
                 (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
              (5 5 (:REWRITE |(< (/ x) (/ y))|))
              (5 5 (:REWRITE |(< (- x) c)|))
              (5 5 (:REWRITE |(< (- x) (- y))|))
              (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
              (4 4 (:REWRITE REDUCE-INTEGERP-+))
              (4 4
                 (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
              (4 4 (:REWRITE INTEGERP-MINUS-X))
              (4 4 (:META META-INTEGERP-CORRECT))
              (3 3 (:REWRITE SIMPLIFY-SUMS-<))
              (3 3 (:REWRITE REDUCE-RATIONALP-+))
              (3 3 (:REWRITE REDUCE-RATIONALP-*))
              (3 3 (:REWRITE RATIONALP-MINUS-X))
              (3 3 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
              (3 3 (:META META-RATIONALP-CORRECT))
              (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
              (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
              (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
              (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
              (1 1
                 (:REWRITE |(<= (/ x) y) with (< x 0)|))
              (1 1
                 (:REWRITE |(<= (/ x) y) with (< 0 x)|))
              (1 1 (:REWRITE |(< x (/ y)) with (< y 0)|))
              (1 1 (:REWRITE |(< 0 (* x y))|)))
(RTL::R-POS-4
 (7 7 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (7 7 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (7 7 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (7 7 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (4
  4
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE)))
(RTL::R-POS-5
 (32 32 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (32 32 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (32 32 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (32 32 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (27
  27
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (27 27
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (27 27
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (27 27
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (27 27
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (27 27
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE)))
(RTL::R-POS-6
 (685 685
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (685 685
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (685 685
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (685 685
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (541
  541
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (541 541
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (541
     541
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (541 541
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (541 541
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (541 541
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (396 5 (:REWRITE RTL::R-EXACTP-6))
 (280 50
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (279 79 (:REWRITE DEFAULT-PLUS-2))
 (241 57 (:REWRITE DEFAULT-LESS-THAN-2))
 (150 40 (:REWRITE SIMPLIFY-SUMS-<))
 (143 57 (:REWRITE DEFAULT-LESS-THAN-1))
 (142 79 (:REWRITE DEFAULT-PLUS-1))
 (93 5 (:REWRITE ODD-EXPT-THM))
 (81 3
     (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (78 3
     (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (73 55
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (63 55 (:REWRITE |(< (- x) (- y))|))
 (57 57 (:REWRITE THE-FLOOR-BELOW))
 (57 57 (:REWRITE THE-FLOOR-ABOVE))
 (55 55
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (55 55
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (55 55
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (55 55 (:REWRITE INTEGERP-<-CONSTANT))
 (55 55 (:REWRITE CONSTANT-<-INTEGERP))
 (55 55
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (55 55
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (55 55
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (55 55
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (55 55 (:REWRITE |(< c (- x))|))
 (55 55
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (55 55
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (55 55
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (55 55 (:REWRITE |(< (/ x) (/ y))|))
 (55 55 (:REWRITE |(< (- x) c)|))
 (48 20 (:REWRITE DEFAULT-TIMES-2))
 (40 1 (:LINEAR EXPT->=-1-ONE))
 (40 1 (:LINEAR EXPT-<=-1-TWO))
 (39 1 (:LINEAR EXPT->-1-ONE))
 (39 1 (:LINEAR EXPT-<-1-TWO))
 (35 1 (:LINEAR EXPT-X->=-X))
 (35 1 (:LINEAR EXPT-X->-X))
 (33 17 (:REWRITE DEFAULT-MINUS))
 (27 9 (:REWRITE RTL::BVECP-EXACTP))
 (25 25
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (25 17 (:REWRITE INTEGERP-MINUS-X))
 (24 6 (:REWRITE RATIONALP-X))
 (20 20 (:REWRITE DEFAULT-TIMES-1))
 (18 18 (:TYPE-PRESCRIPTION RTL::BVECP))
 (18 10 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (17 17 (:REWRITE REDUCE-INTEGERP-+))
 (17 17 (:META META-INTEGERP-CORRECT))
 (15 15
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (12 12 (:REWRITE |(< (+ c/d x) y)|))
 (12 12 (:REWRITE |(< (+ (- c) x) y)|))
 (11 11 (:REWRITE |(< y (+ (- c) x))|))
 (11 11 (:REWRITE |(< x (+ c/d y))|))
 (11 11 (:REWRITE |(+ c (+ d x))|))
 (10 10
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (10 10 (:REWRITE DEFAULT-DIVIDE))
 (10 5 (:REWRITE DEFAULT-EXPT-2))
 (6 6 (:REWRITE REDUCE-RATIONALP-+))
 (6 6 (:REWRITE REDUCE-RATIONALP-*))
 (6 6 (:REWRITE RATIONALP-MINUS-X))
 (6 6 (:META META-RATIONALP-CORRECT))
 (5 5 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (5 5 (:REWRITE FOLD-CONSTS-IN-+))
 (5 5 (:REWRITE DEFAULT-EXPT-1))
 (5 5 (:REWRITE |(expt 1/c n)|))
 (5 5 (:REWRITE |(expt (- x) n)|))
 (5 5 (:REWRITE |(< (/ x) 0)|))
 (5 5 (:REWRITE |(< (* x y) 0)|))
 (4 4 (:REWRITE |(- (* c x))|))
 (3 3
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (3 3
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (2 2 (:REWRITE ZP-OPEN))
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
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (2 2
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (2 2
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (2 2
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
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
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<))
 (1 1 (:LINEAR EXPT->=-1-TWO))
 (1 1 (:LINEAR EXPT->-1-TWO))
 (1 1 (:LINEAR EXPT-<=-1-ONE))
 (1 1 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-POS-7
     (15 11 (:REWRITE DEFAULT-TIMES-2))
     (12 3 (:REWRITE RATIONALP-X))
     (11 11 (:REWRITE DEFAULT-TIMES-1))
     (5 5 (:REWRITE THE-FLOOR-BELOW))
     (5 5 (:REWRITE THE-FLOOR-ABOVE))
     (5 5
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (5 5
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (5 5 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (5 5 (:REWRITE DEFAULT-LESS-THAN-2))
     (5 5 (:REWRITE DEFAULT-LESS-THAN-1))
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
     (3 3 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (3 3 (:REWRITE REDUCE-RATIONALP-+))
     (3 3 (:REWRITE REDUCE-RATIONALP-*))
     (3 3 (:REWRITE REDUCE-INTEGERP-+))
     (3 3 (:REWRITE RATIONALP-MINUS-X))
     (3 3
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (3 3 (:REWRITE INTEGERP-MINUS-X))
     (3 3 (:META META-RATIONALP-CORRECT))
     (3 3 (:META META-INTEGERP-CORRECT))
     (2 2 (:REWRITE SIMPLIFY-SUMS-<))
     (2 2 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (2 2 (:REWRITE |(< 0 (* x y))|))
     (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (1 1
        (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (1 1
        (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (1 1 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (1 1 (:REWRITE |(< 0 (/ x))|)))
(RTL::R-POS-8
 (24
  24
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (24 24
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (24 24
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (24 24
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (24 24
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (24 24
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (16 16
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4A-EXPT))
 (16 16
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (16 16
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (16 16
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT)))
(RTL::R-POS-9
 (218
  218
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (218 218
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (218
     218
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (218 218
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (218 218
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (107 17 (:REWRITE DEFAULT-TIMES-2))
 (86 86
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (86 86
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (86 86
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (72 17 (:REWRITE DEFAULT-TIMES-1))
 (53 1 (:REWRITE ODD-EXPT-THM))
 (49 5
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (49 5 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (40 5 (:REWRITE SIMPLIFY-SUMS-<))
 (38 7 (:REWRITE |(< c (- x))|))
 (34 7 (:REWRITE DEFAULT-LESS-THAN-2))
 (33 7 (:REWRITE DEFAULT-LESS-THAN-1))
 (28 28
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (28 28
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (28 28
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (28 28
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (11 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (9 9 (:REWRITE DEFAULT-EXPT-2))
 (9 9 (:REWRITE DEFAULT-EXPT-1))
 (9 9 (:REWRITE |(expt 1/c n)|))
 (9 9 (:REWRITE |(expt (- x) n)|))
 (8 2 (:REWRITE RATIONALP-X))
 (7 7 (:REWRITE THE-FLOOR-BELOW))
 (7 7 (:REWRITE THE-FLOOR-ABOVE))
 (7 7
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (7 7
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (7 7 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (7 7 (:REWRITE DEFAULT-MINUS))
 (7 7
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (7 7
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (7 7
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (7 7
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (7 7
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (7 7
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (7 7
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (7 7
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (7 7 (:REWRITE |(< (/ x) (/ y))|))
 (7 7 (:REWRITE |(< (- x) (- y))|))
 (6 6 (:REWRITE INTEGERP-<-CONSTANT))
 (6 6 (:REWRITE CONSTANT-<-INTEGERP))
 (6 6 (:REWRITE |(< (- x) c)|))
 (5 5 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (3 3 (:REWRITE REDUCE-INTEGERP-+))
 (3 3 (:REWRITE INTEGERP-MINUS-X))
 (3 3 (:META META-INTEGERP-CORRECT))
 (3 2 (:REWRITE DEFAULT-PLUS-1))
 (2 2 (:REWRITE REDUCE-RATIONALP-+))
 (2 2 (:REWRITE REDUCE-RATIONALP-*))
 (2 2 (:REWRITE RATIONALP-MINUS-X))
 (2 2 (:REWRITE DEFAULT-PLUS-2))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:REWRITE |(< 0 (* x y))|))
 (2 2 (:META META-RATIONALP-CORRECT))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (* x y) 0)|))
 (1 1 (:REWRITE |(- (- x))|)))
(RTL::R-POS-10)
(RTL::R-POS-11
 (664
  664
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (664 664
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (664
     664
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (664 664
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (664 664
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (664 664
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (663 663
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (663 663
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (663 663
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (663 663
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (405 85 (:REWRITE DEFAULT-PLUS-2))
 (397 6 (:REWRITE RTL::R-EXACTP-6))
 (320 50
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (264 85 (:REWRITE DEFAULT-PLUS-1))
 (221 57 (:REWRITE DEFAULT-LESS-THAN-2))
 (203 57 (:REWRITE DEFAULT-LESS-THAN-1))
 (170 40 (:REWRITE SIMPLIFY-SUMS-<))
 (129 29 (:REWRITE DEFAULT-TIMES-1))
 (93 5 (:REWRITE ODD-EXPT-THM))
 (89 29 (:REWRITE DEFAULT-TIMES-2))
 (83 55 (:REWRITE |(< (- x) (- y))|))
 (81 3
     (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (78 3
     (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (73 55
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (60 22 (:REWRITE DEFAULT-MINUS))
 (57 57 (:REWRITE THE-FLOOR-BELOW))
 (57 57 (:REWRITE THE-FLOOR-ABOVE))
 (57 55 (:REWRITE |(< (/ x) (/ y))|))
 (55 55
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (55 55
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (55 55
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (55 55 (:REWRITE INTEGERP-<-CONSTANT))
 (55 55 (:REWRITE CONSTANT-<-INTEGERP))
 (55 55
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (55 55
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (55 55
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (55 55
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (55 55 (:REWRITE |(< c (- x))|))
 (55 55
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (55 55
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (55 55
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (55 55 (:REWRITE |(< (- x) c)|))
 (40 1 (:LINEAR EXPT->=-1-ONE))
 (40 1 (:LINEAR EXPT-<=-1-TWO))
 (39 1 (:LINEAR EXPT->-1-ONE))
 (39 1 (:LINEAR EXPT-<-1-TWO))
 (38 10 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (35 1 (:LINEAR EXPT-X->=-X))
 (35 1 (:LINEAR EXPT-X->-X))
 (30 30
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (27 9 (:REWRITE RTL::BVECP-EXACTP))
 (25 17 (:REWRITE INTEGERP-MINUS-X))
 (24 6 (:REWRITE RATIONALP-X))
 (21 21
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (18 18 (:TYPE-PRESCRIPTION RTL::BVECP))
 (17 17 (:REWRITE REDUCE-INTEGERP-+))
 (17 17 (:META META-INTEGERP-CORRECT))
 (12 12 (:REWRITE |(< (+ c/d x) y)|))
 (12 12 (:REWRITE |(< (+ (- c) x) y)|))
 (12 12 (:REWRITE |(+ c (+ d x))|))
 (11 11 (:REWRITE |(< y (+ (- c) x))|))
 (11 11 (:REWRITE |(< x (+ c/d y))|))
 (10 10
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (10 10 (:REWRITE DEFAULT-DIVIDE))
 (10 5 (:REWRITE DEFAULT-EXPT-2))
 (7 7 (:REWRITE |(- (* c x))|))
 (6 6 (:REWRITE REDUCE-RATIONALP-+))
 (6 6 (:REWRITE REDUCE-RATIONALP-*))
 (6 6 (:REWRITE RATIONALP-MINUS-X))
 (6 6 (:REWRITE FOLD-CONSTS-IN-+))
 (6 6 (:META META-RATIONALP-CORRECT))
 (5 5 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (5 5 (:REWRITE DEFAULT-EXPT-1))
 (5 5 (:REWRITE |(expt 1/c n)|))
 (5 5 (:REWRITE |(expt (- x) n)|))
 (5 5 (:REWRITE |(< (/ x) 0)|))
 (5 5 (:REWRITE |(< (* x y) 0)|))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (3 3
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (3 3
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (2 2 (:REWRITE ZP-OPEN))
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
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (2 2
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (2 2
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (2 2
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
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
 (2 2 (:REWRITE |(* c (* d x))|))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<))
 (1 1 (:LINEAR EXPT->=-1-TWO))
 (1 1 (:LINEAR EXPT->-1-TWO))
 (1 1 (:LINEAR EXPT-<=-1-ONE))
 (1 1 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-POS-12
 (99
  99
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (99 99
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (99 99
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (99 99
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (28 10
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (28 10 (:REWRITE DEFAULT-LESS-THAN-2))
 (23 12 (:REWRITE DEFAULT-PLUS-1))
 (21 12 (:REWRITE DEFAULT-PLUS-2))
 (16 10
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (12 3 (:REWRITE RATIONALP-X))
 (10 10 (:REWRITE THE-FLOOR-BELOW))
 (10 10 (:REWRITE THE-FLOOR-ABOVE))
 (10 10 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (10 10
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (10 10
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (10 10
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (10 10
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (10 10 (:REWRITE INTEGERP-<-CONSTANT))
 (10 10 (:REWRITE DEFAULT-LESS-THAN-1))
 (10 10 (:REWRITE CONSTANT-<-INTEGERP))
 (10 10
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (10 10
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (10 10
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (10 10
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (10 10 (:REWRITE |(< c (- x))|))
 (10 10
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (10 10
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (10 10
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (10 10 (:REWRITE |(< (/ x) (/ y))|))
 (10 10 (:REWRITE |(< (- x) c)|))
 (10 10 (:REWRITE |(< (- x) (- y))|))
 (9 1 (:REWRITE ODD-EXPT-THM))
 (8 8 (:REWRITE SIMPLIFY-SUMS-<))
 (8 1 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (6 6 (:REWRITE REDUCE-INTEGERP-+))
 (6 6 (:REWRITE INTEGERP-MINUS-X))
 (6 6 (:META META-INTEGERP-CORRECT))
 (6 2 (:REWRITE RTL::BVECP-EXACTP))
 (5 5
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (5 5
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (5 5 (:REWRITE DEFAULT-EXPT-2))
 (5 5 (:REWRITE DEFAULT-EXPT-1))
 (5 5 (:REWRITE |(expt 1/c n)|))
 (5 5 (:REWRITE |(expt (- x) n)|))
 (4 4 (:TYPE-PRESCRIPTION RTL::BVECP))
 (4 1 (:REWRITE |(integerp (- x))|))
 (3 3 (:REWRITE REDUCE-RATIONALP-+))
 (3 3 (:REWRITE REDUCE-RATIONALP-*))
 (3 3 (:REWRITE RATIONALP-MINUS-X))
 (3 3 (:META META-RATIONALP-CORRECT))
 (2 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (2 2
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (2 2 (:REWRITE DEFAULT-MINUS))
 (2 2 (:REWRITE |(< (+ c/d x) y)|))
 (2 2 (:REWRITE |(< (+ (- c) x) y)|))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (1 1
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (1 1 (:REWRITE DEFAULT-TIMES-2))
 (1 1 (:REWRITE DEFAULT-TIMES-1))
 (1 1 (:REWRITE |(< y (+ (- c) x))|))
 (1 1 (:REWRITE |(< x (+ c/d y))|))
 (1 1 (:REWRITE |(< 0 (/ x))|))
 (1 1 (:REWRITE |(< 0 (* x y))|))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (* x y) 0)|))
 (1 1 (:REWRITE |(- (* c x))|))
 (1 1 (:LINEAR EXPT-X->=-X))
 (1 1 (:LINEAR EXPT-X->-X))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1 1 (:LINEAR EXPT->=-1-TWO))
 (1 1 (:LINEAR EXPT->=-1-ONE))
 (1 1 (:LINEAR EXPT->-1-TWO))
 (1 1 (:LINEAR EXPT->-1-ONE))
 (1 1 (:LINEAR EXPT-<=-1-ONE))
 (1 1 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-POS-13
 (202
  202
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (202 202
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (202
     202
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (202 202
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (67 13 (:REWRITE DEFAULT-LESS-THAN-2))
 (57 12
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (43 16 (:REWRITE DEFAULT-PLUS-2))
 (37 10 (:REWRITE SIMPLIFY-SUMS-<))
 (27 16 (:REWRITE DEFAULT-PLUS-1))
 (18 12
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (17 2 (:REWRITE ODD-EXPT-THM))
 (15 2 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (13 13 (:REWRITE THE-FLOOR-BELOW))
 (13 13 (:REWRITE THE-FLOOR-ABOVE))
 (13 13 (:REWRITE DEFAULT-LESS-THAN-1))
 (12 12 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (12 12
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (12 12
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (12 12
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (12 12
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (12 12 (:REWRITE INTEGERP-<-CONSTANT))
 (12 12 (:REWRITE CONSTANT-<-INTEGERP))
 (12 12
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (12 12
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (12 12
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (12 12
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (12 12 (:REWRITE |(< c (- x))|))
 (12 12
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (12 12
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (12 12
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (12 12 (:REWRITE |(< (/ x) (/ y))|))
 (12 12 (:REWRITE |(< (- x) c)|))
 (12 12 (:REWRITE |(< (- x) (- y))|))
 (12 3 (:REWRITE RATIONALP-X))
 (10 10
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (10 10
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (7 7 (:REWRITE REDUCE-INTEGERP-+))
 (7 7 (:REWRITE INTEGERP-MINUS-X))
 (7 7 (:META META-INTEGERP-CORRECT))
 (6 6 (:REWRITE DEFAULT-MINUS))
 (6 6 (:REWRITE DEFAULT-EXPT-2))
 (6 6 (:REWRITE DEFAULT-EXPT-1))
 (6 6 (:REWRITE |(expt 1/c n)|))
 (6 6 (:REWRITE |(expt (- x) n)|))
 (6 2 (:REWRITE RTL::BVECP-EXACTP))
 (5 5
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (4 4 (:TYPE-PRESCRIPTION RTL::BVECP))
 (4 1 (:REWRITE |(integerp (- x))|))
 (3 3 (:REWRITE REDUCE-RATIONALP-+))
 (3 3 (:REWRITE REDUCE-RATIONALP-*))
 (3 3 (:REWRITE RATIONALP-MINUS-X))
 (3 3
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (3 3 (:REWRITE DEFAULT-TIMES-2))
 (3 3 (:REWRITE DEFAULT-TIMES-1))
 (3 3 (:REWRITE |(< y (+ (- c) x))|))
 (3 3 (:REWRITE |(< x (+ c/d y))|))
 (3 3 (:REWRITE |(< (+ c/d x) y)|))
 (3 3 (:REWRITE |(< (+ (- c) x) y)|))
 (3 3 (:META META-RATIONALP-CORRECT))
 (2 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (* x y) 0)|))
 (1 1 (:REWRITE |(- (* c x))|))
 (1 1 (:LINEAR EXPT-X->=-X))
 (1 1 (:LINEAR EXPT-X->-X))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<))
 (1 1 (:LINEAR EXPT->=-1-TWO))
 (1 1 (:LINEAR EXPT->=-1-ONE))
 (1 1 (:LINEAR EXPT->-1-TWO))
 (1 1 (:LINEAR EXPT->-1-ONE))
 (1 1 (:LINEAR EXPT-<=-1-ONE))
 (1 1 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-POS-14
     (126 126
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (126 126
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (126 126
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (126 126
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (35 11 (:REWRITE DEFAULT-TIMES-2))
     (30 2
         (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (17 9 (:REWRITE DEFAULT-LESS-THAN-2))
     (17 9 (:REWRITE DEFAULT-LESS-THAN-1))
     (12 3 (:REWRITE RATIONALP-X))
     (11 11 (:REWRITE DEFAULT-TIMES-1))
     (9 9 (:REWRITE THE-FLOOR-BELOW))
     (9 9 (:REWRITE THE-FLOOR-ABOVE))
     (9 9
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (9 9
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (9 9 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (6 6
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (5 5 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (5 5 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (5 5 (:REWRITE INTEGERP-<-CONSTANT))
     (5 5 (:REWRITE CONSTANT-<-INTEGERP))
     (5 5
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (5 5
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (5 5
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (5 5
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (5 5 (:REWRITE |(< c (- x))|))
     (5 5
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (5 5
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (5 5
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (5 5
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (5 5 (:REWRITE |(< (/ x) (/ y))|))
     (5 5 (:REWRITE |(< (- x) c)|))
     (5 5 (:REWRITE |(< (- x) (- y))|))
     (4 4 (:REWRITE SIMPLIFY-SUMS-<))
     (4 4 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (4 4 (:REWRITE |(< 0 (* x y))|))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (3 3 (:REWRITE REDUCE-RATIONALP-+))
     (3 3 (:REWRITE REDUCE-RATIONALP-*))
     (3 3 (:REWRITE REDUCE-INTEGERP-+))
     (3 3 (:REWRITE RATIONALP-MINUS-X))
     (3 3 (:REWRITE INTEGERP-MINUS-X))
     (3 3 (:REWRITE |(< 0 (/ x))|))
     (3 3 (:META META-RATIONALP-CORRECT))
     (3 3 (:META META-INTEGERP-CORRECT))
     (2 2
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (2 2 (:REWRITE DEFAULT-DIVIDE))
     (2 2
        (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (1 1 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (1 1
        (:REWRITE |(< 1 (* (/ x) y)) with (< x 0)|))
     (1 1 (:REWRITE |(< (/ x) y) with (< x 0)|))
     (1 1
        (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
     (1 1
        (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|)))
(RTL::R-POS-15
 (4015 4015
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (4015 4015
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (4015 4015
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (2742 350
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
 (2742 350
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
 (1774 350
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3D))
 (1774 350
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1D))
 (1621
  1621
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1621
      1621
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1621
     1621
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1621 1621
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1618 350
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
 (1546 350
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2D))
 (491 95 (:REWRITE DEFAULT-PLUS-2))
 (352 352
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (352 352
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (352 352
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (352 352
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (350 350
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4H))
 (350 350
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3H))
 (350 350
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2H))
 (350 350
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1H))
 (333 108 (:REWRITE DEFAULT-LESS-THAN-2))
 (198 73
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (145 65 (:REWRITE SIMPLIFY-SUMS-<))
 (134 108 (:REWRITE DEFAULT-LESS-THAN-1))
 (130 95 (:REWRITE DEFAULT-PLUS-1))
 (113 83
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (108 108 (:REWRITE THE-FLOOR-BELOW))
 (108 108 (:REWRITE THE-FLOOR-ABOVE))
 (101 101
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (101 101
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (101 83 (:REWRITE |(< (/ x) (/ y))|))
 (92 8
     (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (92 8
     (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (92 8 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (83 83 (:REWRITE INTEGERP-<-CONSTANT))
 (83 83 (:REWRITE CONSTANT-<-INTEGERP))
 (83 83
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (83 83
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (83 83
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (83 83
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (83 83 (:REWRITE |(< c (- x))|))
 (83 83
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (83 83
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (83 83
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (83 83 (:REWRITE |(< (- x) c)|))
 (83 83 (:REWRITE |(< (- x) (- y))|))
 (60 26 (:REWRITE DEFAULT-TIMES-2))
 (48 12 (:REWRITE RATIONALP-X))
 (45 6 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (36 18 (:REWRITE DEFAULT-DIVIDE))
 (34 34
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (33 33 (:REWRITE DEFAULT-MINUS))
 (30 30 (:REWRITE |(< 0 (* x y))|))
 (30 10 (:REWRITE RTL::BVECP-EXACTP))
 (28 28 (:REWRITE REDUCE-INTEGERP-+))
 (28 28 (:REWRITE INTEGERP-MINUS-X))
 (28 28 (:META META-INTEGERP-CORRECT))
 (26 26
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (26 26
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (26 26 (:REWRITE DEFAULT-TIMES-1))
 (25 25 (:REWRITE DEFAULT-EXPT-2))
 (25 25 (:REWRITE DEFAULT-EXPT-1))
 (25 25 (:REWRITE |(expt 1/c n)|))
 (25 25 (:REWRITE |(expt (- x) n)|))
 (24 24
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (21 21 (:REWRITE |(< (* x y) 0)|))
 (20 20 (:TYPE-PRESCRIPTION RTL::BVECP))
 (18 18
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (18 18
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (18 18
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (18 18 (:REWRITE |(< 0 (/ x))|))
 (15 15 (:REWRITE |(< (/ x) 0)|))
 (12 12 (:REWRITE REDUCE-RATIONALP-+))
 (12 12 (:REWRITE REDUCE-RATIONALP-*))
 (12 12 (:REWRITE RATIONALP-MINUS-X))
 (12 12 (:REWRITE |(< x (+ c/d y))|))
 (12 12 (:META META-RATIONALP-CORRECT))
 (12 3 (:REWRITE |(integerp (- x))|))
 (11 11 (:REWRITE |(< (+ c/d x) y)|))
 (11 11 (:REWRITE |(< (+ (- c) x) y)|))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (8 8 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (6 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (6 6
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (6 6
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (6 6
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (6 6
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (6 6
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (6 6 (:REWRITE |(equal c (/ x))|))
 (6 6 (:REWRITE |(equal c (- x))|))
 (6 6 (:REWRITE |(equal (/ x) c)|))
 (6 6 (:REWRITE |(equal (/ x) (/ y))|))
 (6 6 (:REWRITE |(equal (- x) c)|))
 (6 6 (:REWRITE |(equal (- x) (- y))|))
 (6 6
    (:REWRITE |(<= x (/ y)) with (< y 0)|))
 (6 6 (:REWRITE |(< y (+ (- c) x))|))
 (6 6 (:REWRITE |(< (/ x) y) with (< x 0)|))
 (6 6 (:REWRITE |(< (/ x) y) with (< 0 x)|))
 (5 5 (:REWRITE |(- (* c x))|))
 (4 4 (:REWRITE ZP-OPEN))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (1 1 (:LINEAR EXPT-X->=-X))
 (1 1 (:LINEAR EXPT-X->-X))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<))
 (1 1 (:LINEAR EXPT->=-1-TWO))
 (1 1 (:LINEAR EXPT->=-1-ONE))
 (1 1 (:LINEAR EXPT->-1-TWO))
 (1 1 (:LINEAR EXPT->-1-ONE))
 (1 1 (:LINEAR EXPT-<=-1-ONE))
 (1 1 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-POS-16
 (609
  609
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (609 609
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (609
     609
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (609 609
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (409 409
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (409 409
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (409 409
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (139 49 (:REWRITE DEFAULT-LESS-THAN-2))
 (135 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
 (135 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
 (133 44
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (113 50 (:REWRITE DEFAULT-PLUS-2))
 (86 2
     (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (86 2
     (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (86 2 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (86 2 (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (84 50 (:REWRITE DEFAULT-PLUS-1))
 (81 37 (:REWRITE SIMPLIFY-SUMS-<))
 (75 49 (:REWRITE DEFAULT-LESS-THAN-1))
 (75 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-3D))
 (75 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
 (75 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-2D))
 (75 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-1D))
 (72 48
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (66 48 (:REWRITE |(< (/ x) (/ y))|))
 (49 49 (:REWRITE THE-FLOOR-BELOW))
 (49 49 (:REWRITE THE-FLOOR-ABOVE))
 (48 48
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (48 48
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (48 48
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (48 48 (:REWRITE INTEGERP-<-CONSTANT))
 (48 48 (:REWRITE CONSTANT-<-INTEGERP))
 (48 48
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (48 48
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (48 48
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (48 48
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (48 48 (:REWRITE |(< c (- x))|))
 (48 48
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (48 48
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (48 48
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (48 48 (:REWRITE |(< (- x) c)|))
 (48 48 (:REWRITE |(< (- x) (- y))|))
 (43 5 (:REWRITE ODD-EXPT-THM))
 (38 5 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (36 10 (:REWRITE DEFAULT-TIMES-2))
 (36 9 (:REWRITE RATIONALP-X))
 (24 8 (:REWRITE RTL::BVECP-EXACTP))
 (23 5 (:REWRITE DEFAULT-DIVIDE))
 (22 22 (:REWRITE REDUCE-INTEGERP-+))
 (22 22 (:REWRITE INTEGERP-MINUS-X))
 (22 22 (:META META-INTEGERP-CORRECT))
 (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (16 16 (:TYPE-PRESCRIPTION RTL::BVECP))
 (16 16 (:REWRITE DEFAULT-MINUS))
 (15 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-4H))
 (15 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-3H))
 (15 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-2H))
 (15 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-1H))
 (13 13
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (13 13
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (13 13
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (12 12 (:REWRITE DEFAULT-EXPT-2))
 (12 12 (:REWRITE DEFAULT-EXPT-1))
 (12 12 (:REWRITE |(expt 1/c n)|))
 (12 12 (:REWRITE |(expt (- x) n)|))
 (12 3 (:REWRITE |(integerp (- x))|))
 (10 10 (:REWRITE DEFAULT-TIMES-1))
 (9 9 (:REWRITE REDUCE-RATIONALP-+))
 (9 9 (:REWRITE REDUCE-RATIONALP-*))
 (9 9 (:REWRITE RATIONALP-MINUS-X))
 (9 9
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (9 9 (:REWRITE |(< (+ c/d x) y)|))
 (9 9 (:REWRITE |(< (+ (- c) x) y)|))
 (9 9 (:META META-RATIONALP-CORRECT))
 (8 8 (:REWRITE |(< (/ x) 0)|))
 (8 8 (:REWRITE |(< (* x y) 0)|))
 (7 7 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (6 6 (:REWRITE |(< 0 (/ x))|))
 (6 6 (:REWRITE |(< 0 (* x y))|))
 (5 5
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4 (:REWRITE |(< y (+ (- c) x))|))
 (4 4 (:REWRITE |(< x (+ c/d y))|))
 (4 4 (:REWRITE |(- (* c x))|))
 (3 3 (:REWRITE ZP-OPEN))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (1 1
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (1 1 (:LINEAR EXPT-X->=-X))
 (1 1 (:LINEAR EXPT-X->-X))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1 1 (:LINEAR EXPT->=-1-TWO))
 (1 1 (:LINEAR EXPT->=-1-ONE))
 (1 1 (:LINEAR EXPT->-1-TWO))
 (1 1 (:LINEAR EXPT->-1-ONE))
 (1 1 (:LINEAR EXPT-<=-1-ONE))
 (1 1 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-POS-17
 (591 591
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (591 591
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (591 591
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (591 591
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (413
  413
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (413 413
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (413
     413
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (413 413
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (370 5 (:REWRITE RTL::R-EXACTP-6))
 (249 76 (:REWRITE DEFAULT-PLUS-2))
 (232 43
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (191 49 (:REWRITE DEFAULT-LESS-THAN-2))
 (135 76 (:REWRITE DEFAULT-PLUS-1))
 (123 49 (:REWRITE DEFAULT-LESS-THAN-1))
 (119 34 (:REWRITE SIMPLIFY-SUMS-<))
 (89 6 (:REWRITE ODD-EXPT-THM))
 (81 3
     (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (78 3
     (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (71 21 (:REWRITE DEFAULT-TIMES-1))
 (59 47
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (51 47 (:REWRITE |(< (- x) (- y))|))
 (51 21 (:REWRITE DEFAULT-TIMES-2))
 (49 49 (:REWRITE THE-FLOOR-BELOW))
 (49 49 (:REWRITE THE-FLOOR-ABOVE))
 (47 47
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (47 47
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (47 47
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (47 47 (:REWRITE INTEGERP-<-CONSTANT))
 (47 47 (:REWRITE CONSTANT-<-INTEGERP))
 (47 47
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (47 47
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (47 47
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (47 47
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (47 47 (:REWRITE |(< c (- x))|))
 (47 47
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (47 47
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (47 47
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (47 47 (:REWRITE |(< (/ x) (/ y))|))
 (47 47 (:REWRITE |(< (- x) c)|))
 (41 2 (:LINEAR EXPT->=-1-ONE))
 (40 20 (:REWRITE DEFAULT-MINUS))
 (40 2 (:LINEAR EXPT->-1-ONE))
 (36 2 (:LINEAR EXPT-X->=-X))
 (36 2 (:LINEAR EXPT-X->-X))
 (30 10 (:REWRITE RTL::BVECP-EXACTP))
 (28 28
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (20 20 (:TYPE-PRESCRIPTION RTL::BVECP))
 (20 5 (:REWRITE RATIONALP-X))
 (19 15 (:REWRITE INTEGERP-MINUS-X))
 (19 6 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (17 17
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (15 15 (:REWRITE REDUCE-INTEGERP-+))
 (15 15 (:META META-INTEGERP-CORRECT))
 (13 9 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (12 12 (:REWRITE |(< (+ c/d x) y)|))
 (12 12 (:REWRITE |(< (+ (- c) x) y)|))
 (12 8 (:REWRITE DEFAULT-EXPT-2))
 (11 11 (:REWRITE |(+ c (+ d x))|))
 (9 9 (:REWRITE |(< y (+ (- c) x))|))
 (9 9 (:REWRITE |(< x (+ c/d y))|))
 (8 8
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (8 8 (:REWRITE DEFAULT-EXPT-1))
 (8 8 (:REWRITE DEFAULT-DIVIDE))
 (8 8 (:REWRITE |(expt 1/c n)|))
 (8 8 (:REWRITE |(expt (- x) n)|))
 (7 7 (:REWRITE |(- (* c x))|))
 (6 6 (:REWRITE |(< (/ x) 0)|))
 (6 6 (:REWRITE |(< (* x y) 0)|))
 (5 5
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (5 5
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (5 5 (:REWRITE REDUCE-RATIONALP-+))
 (5 5 (:REWRITE REDUCE-RATIONALP-*))
 (5 5 (:REWRITE RATIONALP-MINUS-X))
 (5 5 (:REWRITE FOLD-CONSTS-IN-+))
 (5 5 (:META META-RATIONALP-CORRECT))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (4 1 (:REWRITE |(integerp (- x))|))
 (3 3
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (3 3
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (3 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (3 2
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (3 2
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
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
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-ONE))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE |(* c (* d x))|)))
(RTL::R-POS-18
 (102 102
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (102 102
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (102 102
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (102 102
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (70
  70
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (70 70
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (70 70
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (70 70
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (48 48 (:TYPE-PRESCRIPTION NOT-INTEGERP-4E))
 (48 48 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
 (48 48 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
 (48 48 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
 (41 2 (:LINEAR EXPT->=-1-ONE))
 (40 2 (:LINEAR EXPT->-1-ONE))
 (36 2 (:LINEAR EXPT-X->=-X))
 (36 2 (:LINEAR EXPT-X->-X))
 (12 6
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (12 6 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (10 6 (:REWRITE DEFAULT-LESS-THAN-2))
 (8 6 (:REWRITE DEFAULT-LESS-THAN-1))
 (6 6 (:REWRITE THE-FLOOR-BELOW))
 (6 6 (:REWRITE THE-FLOOR-ABOVE))
 (6 6 (:REWRITE SIMPLIFY-SUMS-<))
 (6 6 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (6 6
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (6 6
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (6 6 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
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
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (5 5
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (4 4 (:REWRITE |(< y (+ (- c) x))|))
 (4 4 (:REWRITE |(< x (+ c/d y))|))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (3 3 (:REWRITE DEFAULT-EXPT-2))
 (3 3 (:REWRITE DEFAULT-EXPT-1))
 (3 3 (:REWRITE |(expt 1/c n)|))
 (3 3 (:REWRITE |(expt (- x) n)|))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:REWRITE |(< 0 (* x y))|))
 (2 2 (:REWRITE |(< (/ x) 0)|))
 (2 2 (:REWRITE |(< (+ c/d x) y)|))
 (2 2 (:REWRITE |(< (+ (- c) x) y)|))
 (2 2 (:REWRITE |(< (* x y) 0)|))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-POS-19
 (841 841
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (841 841
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (841 841
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (841 841
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (759
  759
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (759 759
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (759
     759
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (759 759
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (342 3 (:REWRITE RTL::R-EXACTP-6))
 (299 65
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (282 73 (:REWRITE DEFAULT-LESS-THAN-2))
 (270 97 (:REWRITE DEFAULT-PLUS-2))
 (169 97 (:REWRITE DEFAULT-PLUS-1))
 (154 51 (:REWRITE SIMPLIFY-SUMS-<))
 (147 73 (:REWRITE DEFAULT-LESS-THAN-1))
 (123 10 (:REWRITE ODD-EXPT-THM))
 (94 70
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (81 3
     (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (78 3
     (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (74 70 (:REWRITE |(< (- x) (- y))|))
 (73 73 (:REWRITE THE-FLOOR-BELOW))
 (73 73 (:REWRITE THE-FLOOR-ABOVE))
 (70 70
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (70 70
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (70 70
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (70 70 (:REWRITE INTEGERP-<-CONSTANT))
 (70 70 (:REWRITE CONSTANT-<-INTEGERP))
 (70 70
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (70 70
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (70 70
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (70 70
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (70 70 (:REWRITE |(< c (- x))|))
 (70 70
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (70 70
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (70 70
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (70 70 (:REWRITE |(< (/ x) (/ y))|))
 (70 70 (:REWRITE |(< (- x) c)|))
 (49 10
     (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (44 11 (:REWRITE RATIONALP-X))
 (41 2 (:LINEAR EXPT->=-1-ONE))
 (40 2 (:LINEAR EXPT->-1-ONE))
 (36 2 (:LINEAR EXPT-X->=-X))
 (36 2 (:LINEAR EXPT-X->-X))
 (33 29 (:REWRITE INTEGERP-MINUS-X))
 (33 11 (:REWRITE RTL::BVECP-EXACTP))
 (31 23 (:REWRITE DEFAULT-MINUS))
 (29 29 (:REWRITE REDUCE-INTEGERP-+))
 (29 29 (:META META-INTEGERP-CORRECT))
 (24 24
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (23 19 (:REWRITE DEFAULT-TIMES-2))
 (22 22 (:TYPE-PRESCRIPTION RTL::BVECP))
 (19 19 (:REWRITE DEFAULT-TIMES-1))
 (19 19 (:REWRITE |(< (+ c/d x) y)|))
 (19 19 (:REWRITE |(< (+ (- c) x) y)|))
 (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-4E))
 (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
 (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
 (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
 (18 14 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (15 15
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (13 10 (:REWRITE DEFAULT-EXPT-2))
 (12 3 (:REWRITE |(integerp (- x))|))
 (11 11 (:REWRITE REDUCE-RATIONALP-+))
 (11 11 (:REWRITE REDUCE-RATIONALP-*))
 (11 11 (:REWRITE RATIONALP-MINUS-X))
 (11 11 (:REWRITE |(< y (+ (- c) x))|))
 (11 11 (:REWRITE |(< x (+ c/d y))|))
 (11 11 (:META META-RATIONALP-CORRECT))
 (10 10
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (10 10 (:REWRITE DEFAULT-EXPT-1))
 (10 10 (:REWRITE DEFAULT-DIVIDE))
 (10 10 (:REWRITE |(expt 1/c n)|))
 (10 10 (:REWRITE |(expt (- x) n)|))
 (9 9 (:REWRITE |(< (/ x) 0)|))
 (9 9 (:REWRITE |(< (* x y) 0)|))
 (9 9 (:REWRITE |(+ c (+ d x))|))
 (8 8
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (8 8
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (5 5 (:REWRITE |(- (* c x))|))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (3 3 (:REWRITE ZP-OPEN))
 (3 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (3 3
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (3 3
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (3 3
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (3 3
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (3 3 (:REWRITE FOLD-CONSTS-IN-+))
 (3 3
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (3 3 (:REWRITE |(equal c (/ x))|))
 (3 3 (:REWRITE |(equal c (- x))|))
 (3 3 (:REWRITE |(equal (/ x) c)|))
 (3 3 (:REWRITE |(equal (/ x) (/ y))|))
 (3 3 (:REWRITE |(equal (- x) c)|))
 (3 3 (:REWRITE |(equal (- x) (- y))|))
 (3 3
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (3 3
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:REWRITE |(< 0 (* x y))|))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-POS-20
 (14098
  14098
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (14098
      14098
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (14098
     14098
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (14098 14098
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (6283 1578 (:REWRITE DEFAULT-PLUS-2))
 (5869 5869
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (5869 5869
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (5869 5869
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (5869 5869
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (4596 1578 (:REWRITE DEFAULT-PLUS-1))
 (3406 630 (:REWRITE DEFAULT-TIMES-1))
 (3268 646 (:REWRITE DEFAULT-LESS-THAN-2))
 (2542 630 (:REWRITE DEFAULT-TIMES-2))
 (2072 81 (:REWRITE ODD-EXPT-THM))
 (1768 646 (:REWRITE DEFAULT-LESS-THAN-1))
 (1706 421 (:REWRITE SIMPLIFY-SUMS-<))
 (1650 626
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (930 316 (:REWRITE DEFAULT-MINUS))
 (810 610 (:REWRITE |(< (- x) (- y))|))
 (778 610
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (755 199 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (702 26
      (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (690 610 (:REWRITE |(< c (- x))|))
 (676 26
      (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (670 610
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (646 646 (:REWRITE THE-FLOOR-BELOW))
 (646 646 (:REWRITE THE-FLOOR-ABOVE))
 (627 610 (:REWRITE |(< (/ x) (/ y))|))
 (626 626
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (626 626
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (610 610 (:REWRITE INTEGERP-<-CONSTANT))
 (610 610 (:REWRITE CONSTANT-<-INTEGERP))
 (610 610
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (610 610
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (610 610
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (610 610
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (610 610
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (610 610
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (610 610 (:REWRITE |(< (- x) c)|))
 (503 503
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (493 165 (:REWRITE |(< (+ (- c) x) y)|))
 (346 73
      (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (320 80 (:REWRITE RATIONALP-X))
 (297 99 (:REWRITE RTL::BVECP-EXACTP))
 (249 229 (:REWRITE INTEGERP-MINUS-X))
 (229 229 (:REWRITE REDUCE-INTEGERP-+))
 (229 229 (:META META-INTEGERP-CORRECT))
 (198 198 (:TYPE-PRESCRIPTION RTL::BVECP))
 (196 156 (:REWRITE |(+ c (+ d x))|))
 (180 110 (:REWRITE DEFAULT-EXPT-2))
 (165 165 (:REWRITE |(< (+ c/d x) y)|))
 (128 128 (:REWRITE |(< x (+ c/d y))|))
 (121 121 (:REWRITE |(- (* c x))|))
 (120 120 (:REWRITE |(< y (+ (- c) x))|))
 (110 110 (:REWRITE DEFAULT-EXPT-1))
 (110 110 (:REWRITE |(expt 1/c n)|))
 (110 110 (:REWRITE |(expt (- x) n)|))
 (88 88 (:REWRITE FOLD-CONSTS-IN-+))
 (84 21 (:REWRITE |(integerp (- x))|))
 (80 80 (:REWRITE REDUCE-RATIONALP-+))
 (80 80 (:REWRITE REDUCE-RATIONALP-*))
 (80 80 (:REWRITE RATIONALP-MINUS-X))
 (80 80 (:META META-RATIONALP-CORRECT))
 (78 78
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (78 78 (:REWRITE DEFAULT-DIVIDE))
 (55 55 (:REWRITE |(< (/ x) 0)|))
 (55 55 (:REWRITE |(< (* x y) 0)|))
 (44 44 (:REWRITE |(* c (* d x))|))
 (41 2 (:LINEAR EXPT->=-1-ONE))
 (40 2 (:LINEAR EXPT->-1-ONE))
 (36 2 (:LINEAR EXPT-X->=-X))
 (36 2 (:LINEAR EXPT-X->-X))
 (35 35 (:REWRITE |(< 0 (* x y))|))
 (27 27 (:REWRITE |(< 0 (/ x))|))
 (26 26
     (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (26 26
     (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (20 20 (:REWRITE ZP-OPEN))
 (20 20 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (20 20
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (20 20
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (20 20
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (20 20
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (20 20
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (20 20 (:REWRITE |(equal c (/ x))|))
 (20 20 (:REWRITE |(equal c (- x))|))
 (20 20 (:REWRITE |(equal (/ x) c)|))
 (20 20 (:REWRITE |(equal (/ x) (/ y))|))
 (20 20 (:REWRITE |(equal (- x) c)|))
 (20 20 (:REWRITE |(equal (- x) (- y))|))
 (18 18
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (18 18
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (11 11
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (11 11
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-POS-21
 (1001 52 (:REWRITE DEFAULT-PLUS-2))
 (393
  393
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (393 393
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (393
     393
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (393 393
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (380 38
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (380 38
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (279 52 (:REWRITE DEFAULT-PLUS-1))
 (210 35 (:REWRITE DEFAULT-TIMES-2))
 (171 11 (:REWRITE DEFAULT-LESS-THAN-2))
 (165 35 (:REWRITE DEFAULT-TIMES-1))
 (66 12 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (65 11 (:REWRITE DEFAULT-LESS-THAN-1))
 (55 10 (:REWRITE DEFAULT-MINUS))
 (38 38
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (38 38
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (19 19
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (17 11
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (14 11
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (11 11 (:REWRITE THE-FLOOR-BELOW))
 (11 11 (:REWRITE THE-FLOOR-ABOVE))
 (11 11 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (11 11
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (11 11
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (11 11
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (11 11
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (11 11 (:REWRITE INTEGERP-<-CONSTANT))
 (11 11 (:REWRITE CONSTANT-<-INTEGERP))
 (11 11
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (11 11
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (11 11
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (11 11 (:REWRITE |(< c (- x))|))
 (11 11
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (11 11
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (11 11
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (11 11 (:REWRITE |(< (/ x) (/ y))|))
 (11 11 (:REWRITE |(< (- x) c)|))
 (11 11 (:REWRITE |(< (- x) (- y))|))
 (9 9 (:REWRITE |(+ c (+ d x))|))
 (8 2 (:REWRITE RATIONALP-X))
 (6 2 (:REWRITE RTL::BVECP-EXACTP))
 (5 5 (:REWRITE REDUCE-INTEGERP-+))
 (5 5 (:REWRITE INTEGERP-MINUS-X))
 (5 5 (:REWRITE FOLD-CONSTS-IN-+))
 (5 5 (:META META-INTEGERP-CORRECT))
 (4 4 (:TYPE-PRESCRIPTION RTL::BVECP))
 (4 4 (:REWRITE DEFAULT-EXPT-2))
 (4 4 (:REWRITE DEFAULT-EXPT-1))
 (4 4 (:REWRITE |(expt 1/c n)|))
 (4 4 (:REWRITE |(expt (- x) n)|))
 (4 4 (:REWRITE |(< (+ c/d x) y)|))
 (4 4 (:REWRITE |(< (+ (- c) x) y)|))
 (3 3 (:REWRITE |(< y (+ (- c) x))|))
 (3 3 (:REWRITE |(< x (+ c/d y))|))
 (2 2 (:REWRITE REDUCE-RATIONALP-+))
 (2 2 (:REWRITE REDUCE-RATIONALP-*))
 (2 2 (:REWRITE RATIONALP-MINUS-X))
 (2 2 (:REWRITE |(* (- x) y)|))
 (2 2 (:META META-RATIONALP-CORRECT))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (1 1 (:REWRITE ODD-EXPT-THM))
 (1 1 (:REWRITE |(< 0 (/ x))|))
 (1 1 (:REWRITE |(< 0 (* x y))|)))
(RTL::R-POS-22
     (103 103
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (103 103
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (103 103
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (103 103
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (18 10 (:REWRITE DEFAULT-TIMES-2))
     (12 3 (:REWRITE RATIONALP-X))
     (10 10 (:REWRITE DEFAULT-TIMES-1))
     (9 5 (:REWRITE DEFAULT-LESS-THAN-2))
     (9 5 (:REWRITE DEFAULT-LESS-THAN-1))
     (5 5 (:REWRITE THE-FLOOR-BELOW))
     (5 5 (:REWRITE THE-FLOOR-ABOVE))
     (5 5
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (5 5
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (5 5 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (5 5 (:REWRITE INTEGERP-<-CONSTANT))
     (5 5 (:REWRITE CONSTANT-<-INTEGERP))
     (5 5
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (5 5
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (5 5
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (5 5
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (5 5 (:REWRITE |(< c (- x))|))
     (5 5
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (5 5
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (5 5
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (5 5
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (5 5 (:REWRITE |(< (/ x) (/ y))|))
     (5 5 (:REWRITE |(< (- x) c)|))
     (5 5 (:REWRITE |(< (- x) (- y))|))
     (3 3 (:REWRITE REDUCE-RATIONALP-+))
     (3 3 (:REWRITE REDUCE-RATIONALP-*))
     (3 3 (:REWRITE REDUCE-INTEGERP-+))
     (3 3 (:REWRITE RATIONALP-MINUS-X))
     (3 3 (:REWRITE INTEGERP-MINUS-X))
     (3 3 (:META META-RATIONALP-CORRECT))
     (3 3 (:META META-INTEGERP-CORRECT))
     (2 2 (:REWRITE SIMPLIFY-SUMS-<))
     (2 2 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (2 2
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (2 2
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (2 2 (:REWRITE DEFAULT-DIVIDE))
     (2 2 (:REWRITE |(< 0 (/ x))|))
     (2 2 (:REWRITE |(< 0 (* x y))|))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON)))
(RTL::R-POS-23
 (2510 148 (:REWRITE DEFAULT-PLUS-2))
 (1216
  1216
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1216
      1216
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1216
     1216
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1216 1216
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (847 115 (:REWRITE DEFAULT-TIMES-2))
 (840 84
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (840 84
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (832 148 (:REWRITE DEFAULT-PLUS-1))
 (610 115 (:REWRITE DEFAULT-TIMES-1))
 (374 27 (:REWRITE DEFAULT-LESS-THAN-2))
 (259 44 (:REWRITE DEFAULT-MINUS))
 (252 252
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (252 252
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (252 252
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (205 27 (:REWRITE DEFAULT-LESS-THAN-1))
 (190 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (163 28 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (84 84
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (84 84
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (82 82 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
 (82 82 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
 (82 82 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
 (66 66
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (45 27 (:REWRITE |(< (/ x) (/ y))|))
 (40 4 (:REWRITE DEFAULT-DIVIDE))
 (39 27
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (33 27
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (27 27 (:REWRITE THE-FLOOR-BELOW))
 (27 27 (:REWRITE THE-FLOOR-ABOVE))
 (27 27
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (27 27
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (27 27
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (27 27 (:REWRITE INTEGERP-<-CONSTANT))
 (27 27 (:REWRITE CONSTANT-<-INTEGERP))
 (27 27
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (27 27
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (27 27
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (27 27 (:REWRITE |(< c (- x))|))
 (27 27
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (27 27
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (27 27
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (27 27 (:REWRITE |(< (- x) c)|))
 (27 27 (:REWRITE |(< (- x) (- y))|))
 (21 21 (:REWRITE DEFAULT-EXPT-2))
 (21 21 (:REWRITE DEFAULT-EXPT-1))
 (21 21 (:REWRITE |(expt 1/c n)|))
 (21 21 (:REWRITE |(expt (- x) n)|))
 (20 20 (:REWRITE |(+ c (+ d x))|))
 (12 12 (:REWRITE FOLD-CONSTS-IN-+))
 (12 4 (:REWRITE RTL::BVECP-EXACTP))
 (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (10 10 (:REWRITE |(< (+ c/d x) y)|))
 (10 10 (:REWRITE |(< (+ (- c) x) y)|))
 (9 9 (:REWRITE |(< y (+ (- c) x))|))
 (9 9 (:REWRITE |(< x (+ c/d y))|))
 (8 8 (:TYPE-PRESCRIPTION RTL::BVECP))
 (8 8 (:REWRITE REDUCE-INTEGERP-+))
 (8 8 (:REWRITE INTEGERP-MINUS-X))
 (8 8 (:META META-INTEGERP-CORRECT))
 (8 2 (:REWRITE RATIONALP-X))
 (5 5 (:REWRITE |(* (- x) y)|))
 (4 4
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (3 3 (:REWRITE |(< 0 (/ x))|))
 (3 3 (:REWRITE |(< 0 (* x y))|))
 (2 2 (:REWRITE REDUCE-RATIONALP-+))
 (2 2 (:REWRITE REDUCE-RATIONALP-*))
 (2 2 (:REWRITE RATIONALP-MINUS-X))
 (2 2 (:REWRITE ODD-EXPT-THM))
 (2 2 (:META META-RATIONALP-CORRECT))
 (1 1 (:REWRITE ZP-OPEN)))
(RTL::R-POS-24
 (203
  203
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (203 203
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (203
     203
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (203 203
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (203 203
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (160 14 (:REWRITE DEFAULT-TIMES-2))
 (115 17 (:REWRITE DEFAULT-PLUS-2))
 (95 14 (:REWRITE DEFAULT-TIMES-1))
 (95 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (91 91 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (91 91 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (91 91 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (70 1 (:LINEAR EXPT->=-1-ONE))
 (68 10
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (67 17 (:REWRITE DEFAULT-PLUS-1))
 (48 8 (:REWRITE DEFAULT-MINUS))
 (45 10 (:REWRITE DEFAULT-LESS-THAN-1))
 (39 4
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (36 9 (:REWRITE |(< (- x) c)|))
 (25 3 (:REWRITE SIMPLIFY-SUMS-<))
 (20 2 (:REWRITE DEFAULT-DIVIDE))
 (18 9 (:REWRITE |(< (/ x) (/ y))|))
 (15 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
 (15 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
 (15 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
 (15 9
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (12 9
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (10 10 (:REWRITE THE-FLOOR-BELOW))
 (10 10 (:REWRITE THE-FLOOR-ABOVE))
 (10 10
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (10 10
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (10 10 (:REWRITE DEFAULT-LESS-THAN-2))
 (10 1 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (9 9
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (9 9
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (9 9
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (9 9
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (9 9 (:REWRITE |(< c (- x))|))
 (9 9
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (9 9
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (9 9
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (9 9 (:REWRITE |(< (- x) (- y))|))
 (8 8 (:REWRITE INTEGERP-<-CONSTANT))
 (8 8 (:REWRITE CONSTANT-<-INTEGERP))
 (6 6 (:REWRITE DEFAULT-EXPT-2))
 (6 6 (:REWRITE DEFAULT-EXPT-1))
 (6 6 (:REWRITE |(expt 1/c n)|))
 (6 6 (:REWRITE |(expt (- x) n)|))
 (6 2 (:REWRITE RTL::BVECP-EXACTP))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (5 5
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (4 4 (:TYPE-PRESCRIPTION RTL::BVECP))
 (4 1 (:REWRITE |(+ c (+ d x))|))
 (3 3 (:REWRITE REDUCE-INTEGERP-+))
 (3 3 (:REWRITE INTEGERP-MINUS-X))
 (3 3 (:META META-INTEGERP-CORRECT))
 (2 2
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (2 2 (:REWRITE |(< (+ c/d x) y)|))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (1 1 (:REWRITE |(< y (+ (- c) x))|))
 (1 1 (:REWRITE |(< x (+ c/d y))|))
 (1 1 (:REWRITE |(< (+ (- c) x) y)|))
 (1 1 (:REWRITE |(< (* x y) 0)|))
 (1 1 (:REWRITE |(- (- x))|))
 (1 1 (:REWRITE |(- (* c x))|))
 (1 1 (:LINEAR EXPT-X->=-X))
 (1 1 (:LINEAR EXPT-X->-X))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<))
 (1 1 (:LINEAR EXPT->=-1-TWO))
 (1 1 (:LINEAR EXPT->-1-TWO))
 (1 1 (:LINEAR EXPT->-1-ONE))
 (1 1 (:LINEAR EXPT-<=-1-ONE))
 (1 1 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-POS-25
 (4081
  4081
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (4081
      4081
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (4081
     4081
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (4081 4081
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (2414 2414
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (2414 2414
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (2414 2414
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (1326 311 (:REWRITE DEFAULT-PLUS-2))
 (1080 168
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (938 311 (:REWRITE DEFAULT-PLUS-1))
 (808 215 (:REWRITE DEFAULT-LESS-THAN-2))
 (655 215 (:REWRITE DEFAULT-LESS-THAN-1))
 (651 8 (:REWRITE RTL::R-EXACTP-6))
 (553 128 (:REWRITE SIMPLIFY-SUMS-<))
 (304 208
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (273 208 (:REWRITE |(< (/ x) (/ y))|))
 (267 22 (:REWRITE ODD-EXPT-THM))
 (253 208
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (249 208 (:REWRITE |(< (- x) (- y))|))
 (215 215 (:REWRITE THE-FLOOR-BELOW))
 (215 215 (:REWRITE THE-FLOOR-ABOVE))
 (212 59 (:REWRITE DEFAULT-TIMES-2))
 (209 59 (:REWRITE DEFAULT-TIMES-1))
 (208 208
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (208 208
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (208 208
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (208 208 (:REWRITE INTEGERP-<-CONSTANT))
 (208 208 (:REWRITE CONSTANT-<-INTEGERP))
 (208 208
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (208 208
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (208 208
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (208 208 (:REWRITE |(< c (- x))|))
 (208 208
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (208 208
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (208 208
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (208 208 (:REWRITE |(< (- x) c)|))
 (203 83 (:REWRITE DEFAULT-MINUS))
 (145 40 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (143 3
      (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (143 3
      (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (143 3 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (143 3 (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (135 5
      (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (130 5
      (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (113 22
      (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (111 37 (:REWRITE RTL::BVECP-EXACTP))
 (103 91 (:REWRITE INTEGERP-MINUS-X))
 (97 97
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (91 91 (:REWRITE REDUCE-INTEGERP-+))
 (91 91 (:META META-INTEGERP-CORRECT))
 (88 25 (:REWRITE DEFAULT-DIVIDE))
 (88 22 (:REWRITE RATIONALP-X))
 (74 74 (:TYPE-PRESCRIPTION RTL::BVECP))
 (49 49 (:REWRITE |(< (+ c/d x) y)|))
 (49 49 (:REWRITE |(< (+ (- c) x) y)|))
 (47 47
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (43 35 (:REWRITE DEFAULT-EXPT-2))
 (41 2 (:LINEAR EXPT->=-1-ONE))
 (40 2 (:LINEAR EXPT->-1-ONE))
 (36 2 (:LINEAR EXPT-X->=-X))
 (36 2 (:LINEAR EXPT-X->-X))
 (35 35 (:REWRITE DEFAULT-EXPT-1))
 (35 35 (:REWRITE |(expt 1/c n)|))
 (35 35 (:REWRITE |(expt (- x) n)|))
 (30 30 (:REWRITE |(< y (+ (- c) x))|))
 (30 30 (:REWRITE |(< x (+ c/d y))|))
 (28 7 (:REWRITE |(integerp (- x))|))
 (25 25
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (23 23 (:REWRITE |(< (/ x) 0)|))
 (23 23 (:REWRITE |(< (* x y) 0)|))
 (22 22 (:REWRITE REDUCE-RATIONALP-+))
 (22 22 (:REWRITE REDUCE-RATIONALP-*))
 (22 22 (:REWRITE RATIONALP-MINUS-X))
 (22 22 (:META META-RATIONALP-CORRECT))
 (19 19 (:REWRITE |(- (* c x))|))
 (19 19 (:REWRITE |(+ c (+ d x))|))
 (11 11
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (11 11
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (9 9 (:REWRITE FOLD-CONSTS-IN-+))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (8 8 (:REWRITE |(< 0 (/ x))|))
 (8 8 (:REWRITE |(< 0 (* x y))|))
 (6 6 (:REWRITE ZP-OPEN))
 (6 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (6 6
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (6 6
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (6 6
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (6 6
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (6 6
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (6 6 (:REWRITE |(equal c (/ x))|))
 (6 6 (:REWRITE |(equal c (- x))|))
 (6 6 (:REWRITE |(equal (/ x) c)|))
 (6 6 (:REWRITE |(equal (/ x) (/ y))|))
 (6 6 (:REWRITE |(equal (- x) c)|))
 (6 6 (:REWRITE |(equal (- x) (- y))|))
 (5 5
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (5 5
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (3 3 (:REWRITE |(* c (* d x))|))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-POS-26
 (13965
  13965
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (13965
      13965
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (13965
     13965
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (13965 13965
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (5999 1843 (:REWRITE DEFAULT-PLUS-2))
 (4628 1843 (:REWRITE DEFAULT-PLUS-1))
 (3737 664 (:REWRITE DEFAULT-LESS-THAN-2))
 (3030 654 (:REWRITE DEFAULT-TIMES-2))
 (2055 111 (:REWRITE ODD-EXPT-THM))
 (1782 630
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (1662 654 (:REWRITE DEFAULT-TIMES-1))
 (1512 403 (:REWRITE SIMPLIFY-SUMS-<))
 (1205 664 (:REWRITE DEFAULT-LESS-THAN-1))
 (1008 414 (:REWRITE DEFAULT-MINUS))
 (817 240 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (812 612 (:REWRITE |(< c (- x))|))
 (791 612 (:REWRITE |(< (- x) (- y))|))
 (726 612
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (692 612 (:REWRITE |(< (- x) c)|))
 (664 664 (:REWRITE THE-FLOOR-BELOW))
 (664 664 (:REWRITE THE-FLOOR-ABOVE))
 (630 630
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (630 630
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (629 612 (:REWRITE |(< (/ x) (/ y))|))
 (612 612 (:REWRITE INTEGERP-<-CONSTANT))
 (612 612 (:REWRITE CONSTANT-<-INTEGERP))
 (612 612
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (612 612
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (612 612
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (612 612
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (612 612
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (612 612
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (612 612
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (594 594 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (580 211 (:REWRITE |(< (+ (- c) x) y)|))
 (542 542
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (531 102
      (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (417 139 (:REWRITE RTL::BVECP-EXACTP))
 (336 84 (:REWRITE RATIONALP-X))
 (278 278 (:TYPE-PRESCRIPTION RTL::BVECP))
 (224 224 (:REWRITE REDUCE-INTEGERP-+))
 (224 224 (:REWRITE INTEGERP-MINUS-X))
 (224 224 (:META META-INTEGERP-CORRECT))
 (211 211 (:REWRITE |(< (+ c/d x) y)|))
 (172 127 (:REWRITE DEFAULT-EXPT-2))
 (151 151 (:REWRITE |(< x (+ c/d y))|))
 (146 101 (:REWRITE |(+ c (+ d x))|))
 (142 142 (:REWRITE |(< y (+ (- c) x))|))
 (132 33 (:REWRITE |(integerp (- x))|))
 (127 127 (:REWRITE DEFAULT-EXPT-1))
 (127 127 (:REWRITE |(expt 1/c n)|))
 (127 127 (:REWRITE |(expt (- x) n)|))
 (114 114
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (114 114
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (114 114
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (114 114
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (84 84 (:REWRITE REDUCE-RATIONALP-+))
 (84 84 (:REWRITE REDUCE-RATIONALP-*))
 (84 84 (:REWRITE RATIONALP-MINUS-X))
 (84 84 (:META META-RATIONALP-CORRECT))
 (70 70 (:REWRITE |(< (/ x) 0)|))
 (70 70 (:REWRITE |(< (* x y) 0)|))
 (65 65 (:REWRITE FOLD-CONSTS-IN-+))
 (45 45 (:REWRITE |(- (* c x))|))
 (41 2 (:LINEAR EXPT->=-1-ONE))
 (40 2 (:LINEAR EXPT->-1-ONE))
 (37 37 (:REWRITE |(< 0 (* x y))|))
 (36 2 (:LINEAR EXPT-X->=-X))
 (36 2 (:LINEAR EXPT-X->-X))
 (28 28 (:REWRITE |(< 0 (/ x))|))
 (24 24 (:REWRITE ZP-OPEN))
 (24 24 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (24 24
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (24 24
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (24 24
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (24 24
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (24 24
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (24 24 (:REWRITE |(equal c (/ x))|))
 (24 24 (:REWRITE |(equal c (- x))|))
 (24 24 (:REWRITE |(equal (/ x) c)|))
 (24 24 (:REWRITE |(equal (/ x) (/ y))|))
 (24 24 (:REWRITE |(equal (- x) c)|))
 (24 24 (:REWRITE |(equal (- x) (- y))|))
 (18 18
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (18 18
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (11 11
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (11 11
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-POS-27
 (1113 1 (:REWRITE |(< (/ x) y) with (< 0 x)|))
 (540 8 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (359 5 (:REWRITE |(< c (- x))|))
 (271
  271
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (271 271
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (271
     271
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (271 271
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (271 271
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (254 20 (:REWRITE DEFAULT-PLUS-2))
 (215 2 (:REWRITE |(< (/ x) 0)|))
 (184 22 (:REWRITE DEFAULT-TIMES-2))
 (177 22 (:REWRITE DEFAULT-TIMES-1))
 (112 20 (:REWRITE DEFAULT-PLUS-1))
 (101 11 (:REWRITE DEFAULT-MINUS))
 (57 57 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (57 57 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (47 1 (:REWRITE |(+ y (+ x z))|))
 (40 4 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (35 8 (:REWRITE DEFAULT-LESS-THAN-2))
 (35 8 (:REWRITE DEFAULT-LESS-THAN-1))
 (32 10
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (28 1
     (:REWRITE |(<= x (/ y)) with (< y 0)|))
 (28 1 (:REWRITE |(< (/ x) y) with (< x 0)|))
 (27 5 (:LINEAR EXPT->-1-ONE))
 (24 3 (:REWRITE |(+ c (+ d x))|))
 (20 2 (:REWRITE DEFAULT-DIVIDE))
 (19 19 (:REWRITE DEFAULT-EXPT-2))
 (19 19 (:REWRITE DEFAULT-EXPT-1))
 (19 19 (:REWRITE |(expt 1/c n)|))
 (19 19 (:REWRITE |(expt (- x) n)|))
 (18 5 (:LINEAR EXPT-X->=-X))
 (18 5 (:LINEAR EXPT-X->-X))
 (18 5 (:LINEAR EXPT->=-1-ONE))
 (13 4
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (13 4 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (11 2 (:REWRITE |(- (- x))|))
 (10 10
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (10 10
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (10 10
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (9 9
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (9 6
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (8 8 (:REWRITE THE-FLOOR-BELOW))
 (8 8 (:REWRITE THE-FLOOR-ABOVE))
 (8 8
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (8 8
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (7 1 (:REWRITE |(/ (expt x n))|))
 (6 6
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (6 6
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (6 6
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (6 6
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (6 6
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (6 6
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (6 6
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (6 6 (:REWRITE |(< (/ x) (/ y))|))
 (6 6 (:REWRITE |(< (- x) (- y))|))
 (6 2 (:REWRITE RTL::BVECP-EXACTP))
 (5 5 (:LINEAR EXPT-LINEAR-UPPER-<))
 (5 5 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (5 5 (:LINEAR EXPT-LINEAR-LOWER-<))
 (5 5 (:LINEAR EXPT->=-1-TWO))
 (5 5 (:LINEAR EXPT->-1-TWO))
 (5 5 (:LINEAR EXPT-<=-1-ONE))
 (5 5 (:LINEAR EXPT-<-1-ONE))
 (4 4 (:TYPE-PRESCRIPTION RTL::BVECP))
 (4 4 (:REWRITE SIMPLIFY-SUMS-<))
 (4 4 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (4 4 (:REWRITE INTEGERP-<-CONSTANT))
 (4 4 (:REWRITE CONSTANT-<-INTEGERP))
 (4 4 (:REWRITE |(< (- x) c)|))
 (4 1 (:REWRITE RATIONALP-X))
 (3 3 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (2 2 (:REWRITE REDUCE-INTEGERP-+))
 (2 2 (:REWRITE INTEGERP-MINUS-X))
 (2 2 (:REWRITE |(< x (+ c/d y))|))
 (2 2 (:REWRITE |(< (* x y) 0)|))
 (2 2 (:META META-INTEGERP-CORRECT))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1 (:REWRITE REDUCE-RATIONALP-+))
 (1 1 (:REWRITE REDUCE-RATIONALP-*))
 (1 1 (:REWRITE RATIONALP-MINUS-X))
 (1 1
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (1 1 (:REWRITE |(< y (+ (- c) x))|))
 (1 1 (:REWRITE |(< 0 (/ x))|))
 (1 1 (:REWRITE |(< 0 (* x y))|))
 (1 1 (:META META-RATIONALP-CORRECT)))
(RTL::R-POS-28)
(RTL::R-POS-29
 (17607
  17607
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (17607
      17607
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (17607
     17607
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (17607 17607
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (15013 1517
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (10103 3005 (:REWRITE DEFAULT-PLUS-2))
 (9520 9520
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (9520 9520
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (9520 9520
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (9520 9520
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (7063 3005 (:REWRITE DEFAULT-PLUS-1))
 (6884 1281
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (5763 1578 (:REWRITE DEFAULT-LESS-THAN-2))
 (4865 34
       (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (4760 34
       (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (4340 1578 (:REWRITE DEFAULT-LESS-THAN-1))
 (3721 931 (:REWRITE SIMPLIFY-SUMS-<))
 (3229 46 (:LINEAR EXPT->=-1-ONE))
 (2747 627 (:REWRITE DEFAULT-TIMES-2))
 (2640 46 (:LINEAR EXPT->-1-ONE))
 (2427 627 (:REWRITE DEFAULT-TIMES-1))
 (2276 46 (:LINEAR EXPT-X->=-X))
 (2276 46 (:LINEAR EXPT-X->-X))
 (2053 149 (:REWRITE ODD-EXPT-THM))
 (1901 1329 (:REWRITE |(< (- x) (- y))|))
 (1846 388 (:REWRITE |(< (+ (- c) x) y)|))
 (1772 314 (:REWRITE |(< y (+ (- c) x))|))
 (1645 1329 (:REWRITE |(< (- x) c)|))
 (1578 1578 (:REWRITE THE-FLOOR-BELOW))
 (1578 1578 (:REWRITE THE-FLOOR-ABOVE))
 (1575 1329
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (1555 34
       (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (1555 34
       (:REWRITE |(< x (/ y)) with (< y 0)|))
 (1517 1517
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (1517 1517
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (1363 1329 (:REWRITE |(< (/ x) (/ y))|))
 (1329 1329
       (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (1329 1329
       (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (1329 1329
       (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (1329 1329
       (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (1329 1329 (:REWRITE |(< c (- x))|))
 (1329 1329
       (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (1329 1329
       (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (1329 1329
       (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (1321 1321 (:REWRITE INTEGERP-<-CONSTANT))
 (1321 1321 (:REWRITE CONSTANT-<-INTEGERP))
 (1215 45
       (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (1208 470 (:REWRITE DEFAULT-MINUS))
 (1170 45
       (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (1066 502 (:REWRITE |(+ c (+ d x))|))
 (922 350 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (858 858
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (596 149
      (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (593 149 (:REWRITE RATIONALP-X))
 (511 379 (:REWRITE INTEGERP-MINUS-X))
 (432 432 (:REWRITE |(< (+ c/d x) y)|))
 (426 142 (:REWRITE RTL::BVECP-EXACTP))
 (403 403
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (386 386 (:REWRITE |(< x (+ c/d y))|))
 (379 379 (:REWRITE REDUCE-INTEGERP-+))
 (379 379 (:META META-INTEGERP-CORRECT))
 (284 284 (:TYPE-PRESCRIPTION RTL::BVECP))
 (283 204 (:REWRITE DEFAULT-EXPT-2))
 (204 204 (:REWRITE DEFAULT-EXPT-1))
 (204 204 (:REWRITE |(expt 1/c n)|))
 (204 204 (:REWRITE |(expt (- x) n)|))
 (189 189 (:REWRITE |(< (* x y) 0)|))
 (187 187 (:REWRITE FOLD-CONSTS-IN-+))
 (169 169
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (169 169 (:REWRITE DEFAULT-DIVIDE))
 (149 149 (:REWRITE REDUCE-RATIONALP-+))
 (149 149 (:REWRITE REDUCE-RATIONALP-*))
 (149 149 (:REWRITE RATIONALP-MINUS-X))
 (149 149 (:REWRITE |(- (* c x))|))
 (149 149 (:META META-RATIONALP-CORRECT))
 (145 145 (:REWRITE |(< (/ x) 0)|))
 (132 132 (:REWRITE |(< 0 (* x y))|))
 (132 33 (:REWRITE |(integerp (- x))|))
 (96 96 (:REWRITE |(< 0 (/ x))|))
 (92 92
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (92 92
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (92 92
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (92 92
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (64 64 (:REWRITE |(* c (* d x))|))
 (60 60
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (60 60
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (60 60
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (60 60
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (46 46 (:LINEAR EXPT-LINEAR-UPPER-<))
 (46 46 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (46 46 (:LINEAR EXPT-LINEAR-LOWER-<))
 (46 46 (:LINEAR EXPT->=-1-TWO))
 (46 46 (:LINEAR EXPT->-1-TWO))
 (46 46 (:LINEAR EXPT-<=-1-ONE))
 (46 46 (:LINEAR EXPT-<-1-ONE))
 (45 45
     (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (45 45
     (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (38 38 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (38 38
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (38 38
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (38 38
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (38 38
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (38 38
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (38 38 (:REWRITE |(equal c (/ x))|))
 (38 38 (:REWRITE |(equal c (- x))|))
 (38 38 (:REWRITE |(equal (/ x) c)|))
 (38 38 (:REWRITE |(equal (/ x) (/ y))|))
 (38 38 (:REWRITE |(equal (- x) c)|))
 (38 38 (:REWRITE |(equal (- x) (- y))|))
 (37 37 (:REWRITE ZP-OPEN))
 (11 11
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (11 11
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1)))
(RTL::R-POS-30)
(RTL::R-POS-31
 (3478
  3478
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (3478
      3478
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (3478
     3478
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (3478 3478
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1891 1891
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (1891 1891
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (1891 1891
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (1891 1891
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (1670 222
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (1584 501 (:REWRITE DEFAULT-PLUS-2))
 (1120 501 (:REWRITE DEFAULT-PLUS-1))
 (1080 24 (:REWRITE RTL::R-EXACTP-6))
 (1002 194
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (866 232 (:REWRITE DEFAULT-LESS-THAN-2))
 (679 171 (:REWRITE DEFAULT-TIMES-2))
 (672 232 (:REWRITE DEFAULT-LESS-THAN-1))
 (635 171 (:REWRITE DEFAULT-TIMES-1))
 (581 146 (:REWRITE SIMPLIFY-SUMS-<))
 (333 6 (:LINEAR EXPT->=-1-ONE))
 (328 6 (:LINEAR EXPT->-1-ONE))
 (309 22 (:REWRITE ODD-EXPT-THM))
 (284 6 (:LINEAR EXPT-X->=-X))
 (284 6 (:LINEAR EXPT-X->-X))
 (282 202 (:REWRITE |(< (- x) (- y))|))
 (260 200 (:REWRITE |(< (- x) c)|))
 (244 202
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (236 202
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (232 232 (:REWRITE THE-FLOOR-BELOW))
 (232 232 (:REWRITE THE-FLOOR-ABOVE))
 (224 94 (:REWRITE DEFAULT-MINUS))
 (222 222
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (222 222
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (217 55 (:REWRITE |(< (+ (- c) x) y)|))
 (216 8
      (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (209 202 (:REWRITE |(< (/ x) (/ y))|))
 (208 8
      (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (207 45 (:REWRITE |(< y (+ (- c) x))|))
 (202 202
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (202 202
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (202 202
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (202 202
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (202 202
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (202 202
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (200 200 (:REWRITE INTEGERP-<-CONSTANT))
 (200 200 (:REWRITE CONSTANT-<-INTEGERP))
 (200 200 (:REWRITE |(< c (- x))|))
 (184 60 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (159 159
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (134 74 (:REWRITE |(+ c (+ d x))|))
 (100 25 (:REWRITE RATIONALP-X))
 (90 3
     (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (90 3
     (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (90 3 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (90 3 (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (88 23
     (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (83 63 (:REWRITE INTEGERP-MINUS-X))
 (74 63 (:REWRITE REDUCE-INTEGERP-+))
 (66 22 (:REWRITE RTL::BVECP-EXACTP))
 (65 41 (:REWRITE DEFAULT-EXPT-2))
 (63 63 (:META META-INTEGERP-CORRECT))
 (59 59 (:REWRITE |(< (+ c/d x) y)|))
 (53 53 (:REWRITE |(< x (+ c/d y))|))
 (44 44 (:TYPE-PRESCRIPTION RTL::BVECP))
 (41 41 (:REWRITE DEFAULT-EXPT-1))
 (41 41 (:REWRITE |(expt 1/c n)|))
 (41 41 (:REWRITE |(expt (- x) n)|))
 (36 36 (:REWRITE FOLD-CONSTS-IN-+))
 (31 31 (:REWRITE DEFAULT-DIVIDE))
 (29 29
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (28 28 (:REWRITE |(- (* c x))|))
 (26 26 (:REWRITE |(< (* x y) 0)|))
 (25 25 (:REWRITE REDUCE-RATIONALP-+))
 (25 25 (:REWRITE REDUCE-RATIONALP-*))
 (25 25 (:REWRITE RATIONALP-MINUS-X))
 (25 25 (:META META-RATIONALP-CORRECT))
 (24 24 (:REWRITE |(* c (* d x))|))
 (22 22 (:REWRITE |(< (/ x) 0)|))
 (21 21 (:REWRITE |(< 0 (* x y))|))
 (20 5 (:REWRITE |(integerp (- x))|))
 (12 12
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (12 12
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (12 12
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (12 12
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (11 11
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (11 11
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (8 8
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (8 8
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (8 8
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (8 8
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (7 7 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (7 7
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (7 7
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (7 7
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (7 7
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (7 7
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (7 7 (:REWRITE |(equal c (/ x))|))
 (7 7 (:REWRITE |(equal c (- x))|))
 (7 7 (:REWRITE |(equal (/ x) c)|))
 (7 7 (:REWRITE |(equal (/ x) (/ y))|))
 (7 7 (:REWRITE |(equal (- x) c)|))
 (7 7 (:REWRITE |(equal (- x) (- y))|))
 (7 7 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (7 7 (:LINEAR EXPT-LINEAR-LOWER-<))
 (6 6 (:REWRITE ZP-OPEN))
 (6 6 (:LINEAR EXPT-LINEAR-UPPER-<))
 (6 6 (:LINEAR EXPT->=-1-TWO))
 (6 6 (:LINEAR EXPT->-1-TWO))
 (6 6 (:LINEAR EXPT-<=-1-ONE))
 (6 6 (:LINEAR EXPT-<-1-ONE))
 (5 5
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (5 5
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (5 5
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RTL::R-POS-32)
(RTL::R-POS-33
 (1553
  1553
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1553
      1553
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1553
     1553
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1553 1553
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1161 1161
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (1161 1161
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (1161 1161
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (1161 1161
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (652 13 (:REWRITE RTL::R-EXACTP-6))
 (645 241 (:REWRITE DEFAULT-PLUS-2))
 (564 103
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (535 114 (:REWRITE DEFAULT-LESS-THAN-2))
 (443 241 (:REWRITE DEFAULT-PLUS-1))
 (358 106 (:REWRITE DEFAULT-TIMES-1))
 (330 106 (:REWRITE DEFAULT-TIMES-2))
 (292 78 (:REWRITE SIMPLIFY-SUMS-<))
 (252 114 (:REWRITE DEFAULT-LESS-THAN-1))
 (231 19 (:REWRITE ODD-EXPT-THM))
 (138 108
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (135 5
      (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (130 5
      (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (120 108 (:REWRITE |(< (- x) (- y))|))
 (115 62 (:REWRITE DEFAULT-MINUS))
 (114 114 (:REWRITE THE-FLOOR-BELOW))
 (114 114 (:REWRITE THE-FLOOR-ABOVE))
 (108 108
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (108 108
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (108 108
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (108 108 (:REWRITE INTEGERP-<-CONSTANT))
 (108 108 (:REWRITE CONSTANT-<-INTEGERP))
 (108 108
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (108 108
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (108 108
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (108 108
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (108 108 (:REWRITE |(< c (- x))|))
 (108 108
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (108 108
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (108 108
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (108 108 (:REWRITE |(< (/ x) (/ y))|))
 (108 108 (:REWRITE |(< (- x) c)|))
 (77 77
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (71 19
     (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (65 31 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (64 16 (:REWRITE RATIONALP-X))
 (57 45 (:REWRITE INTEGERP-MINUS-X))
 (45 45 (:REWRITE REDUCE-INTEGERP-+))
 (45 45 (:META META-INTEGERP-CORRECT))
 (45 15 (:REWRITE RTL::BVECP-EXACTP))
 (41 2 (:LINEAR EXPT->=-1-ONE))
 (40 2 (:LINEAR EXPT->-1-ONE))
 (36 2 (:LINEAR EXPT-X->=-X))
 (36 2 (:LINEAR EXPT-X->-X))
 (32 20 (:REWRITE DEFAULT-EXPT-2))
 (31 31 (:REWRITE |(< (+ c/d x) y)|))
 (31 31 (:REWRITE |(< (+ (- c) x) y)|))
 (30 30 (:TYPE-PRESCRIPTION RTL::BVECP))
 (23 23 (:REWRITE |(+ c (+ d x))|))
 (20 20 (:REWRITE DEFAULT-EXPT-1))
 (20 20 (:REWRITE |(expt 1/c n)|))
 (20 20 (:REWRITE |(expt (- x) n)|))
 (19 19 (:REWRITE |(< y (+ (- c) x))|))
 (19 19 (:REWRITE |(< x (+ c/d y))|))
 (19 19 (:REWRITE |(- (* c x))|))
 (16 16 (:REWRITE REDUCE-RATIONALP-+))
 (16 16 (:REWRITE REDUCE-RATIONALP-*))
 (16 16 (:REWRITE RATIONALP-MINUS-X))
 (16 16 (:META META-RATIONALP-CORRECT))
 (16 4 (:REWRITE |(integerp (- x))|))
 (15 15
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (15 15 (:REWRITE DEFAULT-DIVIDE))
 (13 13 (:REWRITE FOLD-CONSTS-IN-+))
 (12 12 (:REWRITE |(< (/ x) 0)|))
 (12 12 (:REWRITE |(< (* x y) 0)|))
 (11 11 (:REWRITE |(* c (* d x))|))
 (8 8
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (8 8
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (5 5
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (5 5
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (4 4 (:REWRITE ZP-OPEN))
 (4 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (4 4
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (4 4
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (4 4
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (4 4
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (4 4
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (4 4 (:REWRITE |(equal c (/ x))|))
 (4 4 (:REWRITE |(equal c (- x))|))
 (4 4 (:REWRITE |(equal (/ x) c)|))
 (4 4 (:REWRITE |(equal (/ x) (/ y))|))
 (4 4 (:REWRITE |(equal (- x) c)|))
 (4 4 (:REWRITE |(equal (- x) (- y))|))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:REWRITE |(< 0 (* x y))|))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-POS-34
 (4748
  4748
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (4748
      4748
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (4748
     4748
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (4748 4748
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (4196 4196
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (4196 4196
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (4196 4196
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (4196 4196
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (1763 693 (:REWRITE DEFAULT-PLUS-2))
 (1707 21 (:REWRITE RTL::R-EXACTP-6))
 (1654 441 (:REWRITE DEFAULT-LESS-THAN-2))
 (1154 693 (:REWRITE DEFAULT-PLUS-1))
 (791 441 (:REWRITE DEFAULT-LESS-THAN-1))
 (688 60 (:REWRITE ODD-EXPT-THM))
 (603 423
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (443 423 (:REWRITE |(< (- x) (- y))|))
 (441 441 (:REWRITE THE-FLOOR-BELOW))
 (441 441 (:REWRITE THE-FLOOR-ABOVE))
 (425 425
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (425 425
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (425 425
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (423 423 (:REWRITE INTEGERP-<-CONSTANT))
 (423 423 (:REWRITE CONSTANT-<-INTEGERP))
 (423 423
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (423 423
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (423 423
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (423 423
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (423 423 (:REWRITE |(< c (- x))|))
 (423 423
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (423 423
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (423 423
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (423 423 (:REWRITE |(< (/ x) (/ y))|))
 (423 423 (:REWRITE |(< (- x) c)|))
 (378 14
      (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (364 14
      (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (320 60
      (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (222 74 (:REWRITE RTL::BVECP-EXACTP))
 (197 157 (:REWRITE DEFAULT-MINUS))
 (184 164 (:REWRITE INTEGERP-MINUS-X))
 (183 183
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (176 44 (:REWRITE RATIONALP-X))
 (164 164 (:REWRITE REDUCE-INTEGERP-+))
 (164 164 (:META META-INTEGERP-CORRECT))
 (150 150 (:REWRITE DEFAULT-TIMES-2))
 (150 150 (:REWRITE DEFAULT-TIMES-1))
 (148 148 (:TYPE-PRESCRIPTION RTL::BVECP))
 (116 96 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (111 111 (:REWRITE |(< (+ c/d x) y)|))
 (111 111 (:REWRITE |(< (+ (- c) x) y)|))
 (103 103
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (80 20 (:REWRITE |(integerp (- x))|))
 (70 51 (:REWRITE DEFAULT-EXPT-2))
 (63 63 (:REWRITE |(+ c (+ d x))|))
 (57 57 (:REWRITE |(< y (+ (- c) x))|))
 (57 57 (:REWRITE |(< x (+ c/d y))|))
 (51 51 (:REWRITE DEFAULT-EXPT-1))
 (51 51 (:REWRITE |(expt 1/c n)|))
 (51 51 (:REWRITE |(expt (- x) n)|))
 (46 46
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (46 46 (:REWRITE DEFAULT-DIVIDE))
 (45 45 (:REWRITE |(< (/ x) 0)|))
 (45 45 (:REWRITE |(< (* x y) 0)|))
 (45 45 (:REWRITE |(- (* c x))|))
 (44 44 (:REWRITE REDUCE-RATIONALP-+))
 (44 44 (:REWRITE REDUCE-RATIONALP-*))
 (44 44 (:REWRITE RATIONALP-MINUS-X))
 (44 44 (:META META-RATIONALP-CORRECT))
 (41 2 (:LINEAR EXPT->=-1-ONE))
 (40 2 (:LINEAR EXPT->-1-ONE))
 (36 2 (:LINEAR EXPT-X->=-X))
 (36 2 (:LINEAR EXPT-X->-X))
 (27 27 (:REWRITE FOLD-CONSTS-IN-+))
 (15 13 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (15 13
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (15 13
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (14 14
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (14 14
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (14 14
     (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (14 14
     (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (13 13
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (13 13
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (13 13
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (13 13 (:REWRITE |(equal c (/ x))|))
 (13 13 (:REWRITE |(equal c (- x))|))
 (13 13 (:REWRITE |(equal (/ x) c)|))
 (13 13 (:REWRITE |(equal (/ x) (/ y))|))
 (13 13 (:REWRITE |(equal (- x) c)|))
 (13 13 (:REWRITE |(equal (- x) (- y))|))
 (12 12 (:REWRITE ZP-OPEN))
 (7 7 (:REWRITE |(< 0 (* x y))|))
 (5 5 (:REWRITE |(< 0 (/ x))|))
 (5 5 (:REWRITE |(* c (* d x))|))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2
    (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (2 2
    (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (2 2 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-POS-DIRECTED
 (109780
  109780
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (109780
      109780
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (109780
     109780
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (109780 109780
         (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (94530 94530
        (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (94530 94530
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (94530 94530
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (94530 94530
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (38155 569 (:REWRITE RTL::R-EXACTP-6))
 (35513 14783 (:REWRITE DEFAULT-PLUS-2))
 (28774 6139
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (21516 6385 (:REWRITE DEFAULT-LESS-THAN-2))
 (20935 14783 (:REWRITE DEFAULT-PLUS-1))
 (12975 6385 (:REWRITE DEFAULT-LESS-THAN-1))
 (8270 729 (:REWRITE ODD-EXPT-THM))
 (7958 6224
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (7560 280
       (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (7280 280
       (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (6385 6385 (:REWRITE THE-FLOOR-BELOW))
 (6385 6385 (:REWRITE THE-FLOOR-ABOVE))
 (6268 6224 (:REWRITE |(< (- x) (- y))|))
 (6224 6224
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (6224 6224
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (6224 6224
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (6224 6224 (:REWRITE INTEGERP-<-CONSTANT))
 (6224 6224 (:REWRITE CONSTANT-<-INTEGERP))
 (6224 6224
       (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (6224 6224
       (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (6224 6224
       (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (6224 6224
       (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (6224 6224 (:REWRITE |(< c (- x))|))
 (6224 6224
       (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (6224 6224
       (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (6224 6224
       (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (6224 6224 (:REWRITE |(< (/ x) (/ y))|))
 (6224 6224 (:REWRITE |(< (- x) c)|))
 (6212 6212 (:REWRITE DEFAULT-TIMES-2))
 (6212 6212 (:REWRITE DEFAULT-TIMES-1))
 (5357 5357
       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (3802 3802
       (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (3724 931 (:REWRITE RATIONALP-X))
 (3524 729
       (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (3039 1013 (:REWRITE RTL::BVECP-EXACTP))
 (2965 2877 (:REWRITE DEFAULT-MINUS))
 (2397 602
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (2397 602
       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (2312 716 (:REWRITE |(equal (/ x) c)|))
 (2282 2238 (:REWRITE INTEGERP-MINUS-X))
 (2238 2238 (:REWRITE REDUCE-INTEGERP-+))
 (2238 2238 (:META META-INTEGERP-CORRECT))
 (2083 2083 (:REWRITE |(+ c (+ d x))|))
 (2026 2026 (:TYPE-PRESCRIPTION RTL::BVECP))
 (1745 1745 (:REWRITE |(< (+ c/d x) y)|))
 (1745 1745 (:REWRITE |(< (+ (- c) x) y)|))
 (1733 1689 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (1429 860 (:REWRITE DEFAULT-EXPT-2))
 (1272 1272 (:REWRITE |(- (* c x))|))
 (1217 1217 (:REWRITE DEFAULT-DIVIDE))
 (1171 1171 (:REWRITE FOLD-CONSTS-IN-+))
 (1103 1103
       (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (964 964 (:REWRITE |(< y (+ (- c) x))|))
 (964 964 (:REWRITE |(< x (+ c/d y))|))
 (931 931 (:REWRITE REDUCE-RATIONALP-+))
 (931 931 (:REWRITE REDUCE-RATIONALP-*))
 (931 931 (:REWRITE RATIONALP-MINUS-X))
 (931 931 (:META META-RATIONALP-CORRECT))
 (860 860 (:REWRITE DEFAULT-EXPT-1))
 (860 860 (:REWRITE |(expt 1/c n)|))
 (860 860 (:REWRITE |(expt (- x) n)|))
 (860 215 (:REWRITE |(integerp (- x))|))
 (716 716
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (716 716
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (716 716 (:REWRITE |(equal c (/ x))|))
 (716 716 (:REWRITE |(equal (/ x) (/ y))|))
 (716 716 (:REWRITE |(equal (- x) (- y))|))
 (634 634 (:REWRITE |(< (/ x) 0)|))
 (634 634 (:REWRITE |(< (* x y) 0)|))
 (602 602
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (602 602 (:REWRITE |(equal c (- x))|))
 (602 602 (:REWRITE |(equal (- x) c)|))
 (482 482 (:REWRITE |(* c (* d x))|))
 (281 281 (:REWRITE ZP-OPEN))
 (280 280
      (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (280 280
      (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (180 180 (:REWRITE RTL::RAZ-NEG-BITS))
 (172 172 (:REWRITE |(< 0 (/ x))|))
 (172 172 (:REWRITE |(< 0 (* x y))|))
 (171 171
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (171 171
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (114 114
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (114 114 (:REWRITE |(not (equal x (/ y)))|))
 (114 114 (:REWRITE |(equal x (/ y))|))
 (114 114 (:REWRITE |(/ (/ x))|))
 (103 103 (:REWRITE RTL::RTZ-NEG-BITS))
 (96 96 (:REWRITE |(equal (+ (- c) x) y)|))
 (41 2 (:LINEAR EXPT->=-1-ONE))
 (40 2 (:LINEAR EXPT->-1-ONE))
 (36 2 (:LINEAR EXPT-X->=-X))
 (36 2 (:LINEAR EXPT-X->-X))
 (34 34
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (34 34
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (32 32
     (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (32 32
     (:REWRITE |(< (* x (/ y)) 0) rationalp (* x (/ y))|))
 (11 11
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (11 11
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-ONE)))
(RTL::NOT-MIDPOINT-1
 (367 15 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (283 65 (:REWRITE DEFAULT-PLUS-2))
 (167 1
      (:REWRITE EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (165 1
      (:REWRITE EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (144
  144
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (144 144
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (144
     144
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (144 144
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (144 144
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (144 144
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (96 65 (:REWRITE DEFAULT-PLUS-1))
 (94 1 (:REWRITE ODD-EXPT-THM))
 (62 16 (:REWRITE DEFAULT-LESS-THAN-2))
 (55 15
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (52 52
     (:TYPE-PRESCRIPTION RTL::FP+-POSITIVE))
 (40 16 (:REWRITE DEFAULT-LESS-THAN-1))
 (29 3 (:REWRITE RTL::R-EXACTP-6))
 (22 16
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (17 13 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (16 16 (:REWRITE THE-FLOOR-BELOW))
 (16 16 (:REWRITE THE-FLOOR-ABOVE))
 (16 16
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (16 16
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (16 16
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (16 16
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (16 16 (:REWRITE INTEGERP-<-CONSTANT))
 (16 16 (:REWRITE CONSTANT-<-INTEGERP))
 (16 16
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (16 16
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (16 16
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (16 16
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (16 16 (:REWRITE |(< c (- x))|))
 (16 16
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (16 16
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (16 16
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (16 16 (:REWRITE |(< (/ x) (/ y))|))
 (16 16 (:REWRITE |(< (- x) c)|))
 (16 16 (:REWRITE |(< (- x) (- y))|))
 (14 14 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (13 13
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (12 3 (:REWRITE RATIONALP-X))
 (9 9 (:REWRITE |(+ c (+ d x))|))
 (9 3 (:REWRITE RTL::BVECP-EXACTP))
 (6 6 (:TYPE-PRESCRIPTION RTL::BVECP))
 (6 6 (:REWRITE |(< y (+ (- c) x))|))
 (6 6 (:REWRITE |(< x (+ c/d y))|))
 (6 3 (:REWRITE DEFAULT-EXPT-2))
 (5 5 (:REWRITE REDUCE-INTEGERP-+))
 (5 5 (:REWRITE INTEGERP-MINUS-X))
 (5 5 (:META META-INTEGERP-CORRECT))
 (5 1
    (:REWRITE EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4 (:REWRITE |(< (+ c/d x) y)|))
 (4 4 (:REWRITE |(< (+ (- c) x) y)|))
 (3 3 (:REWRITE REDUCE-RATIONALP-+))
 (3 3 (:REWRITE REDUCE-RATIONALP-*))
 (3 3 (:REWRITE RATIONALP-MINUS-X))
 (3 3 (:REWRITE DEFAULT-MINUS))
 (3 3 (:REWRITE DEFAULT-EXPT-1))
 (3 3 (:REWRITE |(expt 1/c n)|))
 (3 3 (:REWRITE |(expt (- x) n)|))
 (3 3 (:META META-RATIONALP-CORRECT))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:REWRITE |(< 0 (* x y))|))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (1 1 (:REWRITE FOLD-CONSTS-IN-+)))
(RTL::NOT-MIDPOINT-2
 (46273 536 (:REWRITE RTL::R-EXACTP-6))
 (37902 3239
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (28294
  28294
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (28294
      28294
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (28294
     28294
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (28294 28294
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (19001 7067 (:REWRITE DEFAULT-PLUS-2))
 (18263 18263
        (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (18263 18263
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (18263 18263
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (18263 18263
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (11552 110 (:LINEAR EXPT->=-1-ONE))
 (11351 110 (:LINEAR EXPT-<=-1-TWO))
 (11160 110 (:LINEAR EXPT-<-1-TWO))
 (11064 110 (:LINEAR EXPT->-1-ONE))
 (10285 110 (:LINEAR EXPT-X->=-X))
 (10285 110 (:LINEAR EXPT-X->-X))
 (9302 7067 (:REWRITE DEFAULT-PLUS-1))
 (7545 3258 (:REWRITE DEFAULT-LESS-THAN-2))
 (7309 3258 (:REWRITE DEFAULT-LESS-THAN-1))
 (4227 825 (:REWRITE |(< (+ (- c) x) y)|))
 (4197 729 (:REWRITE |(< y (+ (- c) x))|))
 (3897 43
       (:REWRITE EXPT-EXCEEDS-ANOTHER-BY-MORE-THAN-Y))
 (3258 3258 (:REWRITE THE-FLOOR-BELOW))
 (3258 3258 (:REWRITE THE-FLOOR-ABOVE))
 (3239 3239
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (3239 3239
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (3233 2729
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (2755 2728 (:REWRITE |(< (- x) c)|))
 (2734 2734 (:REWRITE |(< (/ x) (/ y))|))
 (2729 2729
       (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (2729 2729
       (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (2729 2729
       (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (2729 2729
       (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (2729 2729
       (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (2729 2729
       (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (2729 2729
       (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (2727 2727 (:REWRITE INTEGERP-<-CONSTANT))
 (2727 2727 (:REWRITE CONSTANT-<-INTEGERP))
 (2187 81
       (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (2106 81
       (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (1865 1865
       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (1685 383 (:REWRITE DEFAULT-TIMES-2))
 (1320 8
       (:REWRITE EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (1124 936 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (1010 528 (:REWRITE DEFAULT-MINUS))
 (956 239 (:REWRITE RATIONALP-X))
 (953 953 (:REWRITE |(< x (+ c/d y))|))
 (936 936 (:REWRITE |(< (+ c/d x) y)|))
 (931 492 (:REWRITE DEFAULT-EXPT-2))
 (786 262 (:REWRITE RTL::BVECP-EXACTP))
 (758 13
      (:REWRITE EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (602 526 (:REWRITE INTEGERP-MINUS-X))
 (526 526 (:REWRITE REDUCE-INTEGERP-+))
 (526 526 (:META META-INTEGERP-CORRECT))
 (524 524 (:TYPE-PRESCRIPTION RTL::BVECP))
 (492 492 (:REWRITE DEFAULT-EXPT-1))
 (492 492 (:REWRITE |(expt 1/c n)|))
 (492 492 (:REWRITE |(expt (- x) n)|))
 (463 51
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (463 51
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (438 383 (:REWRITE DEFAULT-TIMES-1))
 (433 433 (:REWRITE |(< 0 (* x y))|))
 (407 407 (:REWRITE FOLD-CONSTS-IN-+))
 (352 352 (:REWRITE |(< (* x y) 0)|))
 (317 317 (:REWRITE |(< 0 (/ x))|))
 (241 241 (:REWRITE |(< (/ x) 0)|))
 (239 239 (:REWRITE REDUCE-RATIONALP-+))
 (239 239 (:REWRITE REDUCE-RATIONALP-*))
 (239 239 (:REWRITE RATIONALP-MINUS-X))
 (239 239 (:META META-RATIONALP-CORRECT))
 (220 220
      (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (220 220
      (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (220 220
      (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (176 110 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (170 170
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (170 170 (:REWRITE DEFAULT-DIVIDE))
 (136 136
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (136 136
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (118 118
      (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (110 110 (:LINEAR EXPT-LINEAR-UPPER-<))
 (110 110 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (110 110 (:LINEAR EXPT-LINEAR-LOWER-<))
 (110 110 (:LINEAR EXPT->=-1-TWO))
 (110 110 (:LINEAR EXPT->-1-TWO))
 (110 110 (:LINEAR EXPT-<=-1-ONE))
 (110 110 (:LINEAR EXPT-<-1-ONE))
 (81 81
     (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (81 81
     (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (80 80 (:REWRITE ZP-OPEN))
 (51 51
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (51 51
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (51 51
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (51 51 (:REWRITE |(equal c (/ x))|))
 (51 51 (:REWRITE |(equal c (- x))|))
 (51 51 (:REWRITE |(equal (/ x) c)|))
 (51 51 (:REWRITE |(equal (/ x) (/ y))|))
 (51 51 (:REWRITE |(equal (- x) c)|))
 (51 51 (:REWRITE |(equal (- x) (- y))|))
 (38 38
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (38 38
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (28 28 (:REWRITE |(equal (+ (- c) x) y)|))
 (19 19 (:REWRITE |(- (* c x))|))
 (17 17 (:REWRITE |(equal (expt 2 n) c)|))
 (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (2 2 (:REWRITE EXPT-X->=-X))
 (1 1
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (1 1
    (:REWRITE |(< (* x (/ y)) 0) rationalp (* x (/ y))|)))
(RTL::NOT-MIDPOINT-3
 (1756
  1756
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1756
      1756
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1756
     1756
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1756 1756
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1756 1756
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (1325 1325
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (1325 1325
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (1325 1325
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (1325 1325
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (809 447 (:REWRITE DEFAULT-PLUS-2))
 (570 447 (:REWRITE DEFAULT-PLUS-1))
 (557 65 (:REWRITE DEFAULT-TIMES-2))
 (392 138
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (324 144 (:REWRITE DEFAULT-LESS-THAN-2))
 (319 4 (:LINEAR EXPT->=-1-ONE))
 (319 4 (:LINEAR EXPT-<=-1-TWO))
 (312 144 (:REWRITE DEFAULT-LESS-THAN-1))
 (312 4 (:LINEAR EXPT->-1-ONE))
 (312 4 (:LINEAR EXPT-<-1-TWO))
 (311 4 (:LINEAR EXPT-X->=-X))
 (311 4 (:LINEAR EXPT-X->-X))
 (190 142
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (167 65 (:REWRITE DEFAULT-TIMES-1))
 (154 142 (:REWRITE |(< (- x) (- y))|))
 (152 152
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (144 144 (:REWRITE THE-FLOOR-BELOW))
 (144 144 (:REWRITE THE-FLOOR-ABOVE))
 (142 142
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (142 142
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (142 142
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (142 142 (:REWRITE INTEGERP-<-CONSTANT))
 (142 142 (:REWRITE CONSTANT-<-INTEGERP))
 (142 142
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (142 142
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (142 142
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (142 142
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (142 142 (:REWRITE |(< c (- x))|))
 (142 142
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (142 142
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (142 142
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (142 142 (:REWRITE |(< (/ x) (/ y))|))
 (142 142 (:REWRITE |(< (- x) c)|))
 (129 43 (:REWRITE RTL::BVECP-EXACTP))
 (116 29 (:REWRITE RATIONALP-X))
 (114 6 (:REWRITE ODD-EXPT-THM))
 (108 4
      (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (104 4
      (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (100 88 (:REWRITE INTEGERP-MINUS-X))
 (88 88 (:REWRITE REDUCE-INTEGERP-+))
 (88 88 (:META META-INTEGERP-CORRECT))
 (86 86 (:TYPE-PRESCRIPTION RTL::BVECP))
 (86 41 (:REWRITE DEFAULT-MINUS))
 (78 50 (:REWRITE DEFAULT-EXPT-2))
 (78 44 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (50 50 (:REWRITE DEFAULT-EXPT-1))
 (50 50 (:REWRITE |(expt 1/c n)|))
 (50 50 (:REWRITE |(expt (- x) n)|))
 (32 32 (:REWRITE |(< (+ c/d x) y)|))
 (32 32 (:REWRITE |(< (+ (- c) x) y)|))
 (29 29 (:REWRITE REDUCE-RATIONALP-+))
 (29 29 (:REWRITE REDUCE-RATIONALP-*))
 (29 29 (:REWRITE RATIONALP-MINUS-X))
 (29 29 (:META META-RATIONALP-CORRECT))
 (22 22 (:REWRITE |(< y (+ (- c) x))|))
 (22 22 (:REWRITE |(< x (+ c/d y))|))
 (18 18 (:REWRITE FOLD-CONSTS-IN-+))
 (12 12 (:REWRITE |(< (/ x) 0)|))
 (12 12 (:REWRITE |(< (* x y) 0)|))
 (11 11 (:REWRITE ZP-OPEN))
 (8 8
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (8 8 (:REWRITE DEFAULT-DIVIDE))
 (8 8 (:REWRITE |(< 0 (/ x))|))
 (8 8 (:REWRITE |(< 0 (* x y))|))
 (8 8
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (8 8
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (8 8
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (8 8
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (6 6 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (4 4
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (4 4
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (4 4 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (4 4 (:LINEAR EXPT-LINEAR-UPPER-<))
 (4 4 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (4 4 (:LINEAR EXPT-LINEAR-LOWER-<))
 (4 4 (:LINEAR EXPT->=-1-TWO))
 (4 4 (:LINEAR EXPT->-1-TWO))
 (4 4 (:LINEAR EXPT-<=-1-ONE))
 (4 4 (:LINEAR EXPT-<-1-ONE))
 (3 3 (:REWRITE |(- (* c x))|))
 (3 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (3 1
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (3 1
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
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
 (1 1 (:REWRITE |(equal (- x) (- y))|)))
(RTL::NOT-MIDPOINT-4
 (1587 371 (:REWRITE DEFAULT-PLUS-2))
 (894 894
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (894 894
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (894 894
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (894 894
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (786
  786
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (786 786
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (786
     786
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (786 786
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (786 786
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (786 786
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (746 25 (:REWRITE RTL::R-EXACTP-6))
 (668 4
      (:REWRITE EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (660 4
      (:REWRITE EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (588 371 (:REWRITE DEFAULT-PLUS-1))
 (535 116
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (504 11 (:REWRITE ODD-EXPT-THM))
 (490 130 (:REWRITE DEFAULT-LESS-THAN-2))
 (372 130 (:REWRITE DEFAULT-LESS-THAN-1))
 (164 128
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (140 128 (:REWRITE |(< (- x) (- y))|))
 (135 5
      (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (130 130 (:REWRITE THE-FLOOR-BELOW))
 (130 130 (:REWRITE THE-FLOOR-ABOVE))
 (130 5
      (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (128 128
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (128 128
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (128 128
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (128 128 (:REWRITE INTEGERP-<-CONSTANT))
 (128 128 (:REWRITE CONSTANT-<-INTEGERP))
 (128 128
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (128 128
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (128 128
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (128 128
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (128 128 (:REWRITE |(< c (- x))|))
 (128 128
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (128 128
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (128 128
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (128 128 (:REWRITE |(< (/ x) (/ y))|))
 (128 128 (:REWRITE |(< (- x) c)|))
 (93 93
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (92 64 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (78 26 (:REWRITE RTL::BVECP-EXACTP))
 (63 39 (:REWRITE DEFAULT-MINUS))
 (56 14 (:REWRITE RATIONALP-X))
 (52 52 (:TYPE-PRESCRIPTION RTL::BVECP))
 (50 50 (:REWRITE |(+ c (+ d x))|))
 (50 25 (:REWRITE DEFAULT-EXPT-2))
 (45 33 (:REWRITE INTEGERP-MINUS-X))
 (40 1 (:LINEAR EXPT->=-1-ONE))
 (40 1 (:LINEAR EXPT-<=-1-TWO))
 (39 1 (:LINEAR EXPT->-1-ONE))
 (39 1 (:LINEAR EXPT-<-1-TWO))
 (35 35 (:REWRITE |(< y (+ (- c) x))|))
 (35 35 (:REWRITE |(< x (+ c/d y))|))
 (35 1 (:LINEAR EXPT-X->=-X))
 (35 1 (:LINEAR EXPT-X->-X))
 (33 33 (:REWRITE REDUCE-INTEGERP-+))
 (33 33 (:META META-INTEGERP-CORRECT))
 (30 30 (:REWRITE |(< (+ c/d x) y)|))
 (30 30 (:REWRITE |(< (+ (- c) x) y)|))
 (25 25 (:REWRITE DEFAULT-EXPT-1))
 (25 25 (:REWRITE |(expt 1/c n)|))
 (25 25 (:REWRITE |(expt (- x) n)|))
 (20 4
     (:REWRITE EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (17 17 (:REWRITE |(< 0 (/ x))|))
 (17 17 (:REWRITE |(< 0 (* x y))|))
 (14 14 (:REWRITE REDUCE-RATIONALP-+))
 (14 14 (:REWRITE REDUCE-RATIONALP-*))
 (14 14 (:REWRITE RATIONALP-MINUS-X))
 (14 14 (:META META-RATIONALP-CORRECT))
 (13 13
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (13 13
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (10 10
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (10 10
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (10 10 (:REWRITE DEFAULT-TIMES-2))
 (10 10 (:REWRITE DEFAULT-TIMES-1))
 (10 10 (:REWRITE DEFAULT-DIVIDE))
 (9 9 (:REWRITE FOLD-CONSTS-IN-+))
 (7 7 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (7 7 (:REWRITE |(< (/ x) 0)|))
 (7 7 (:REWRITE |(< (* x y) 0)|))
 (5 5
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (5 5
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (4 4 (:REWRITE ZP-OPEN))
 (3 3 (:REWRITE |(- (* c x))|))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<))
 (1 1 (:LINEAR EXPT->=-1-TWO))
 (1 1 (:LINEAR EXPT->-1-TWO))
 (1 1 (:LINEAR EXPT-<=-1-ONE))
 (1 1 (:LINEAR EXPT-<-1-ONE)))
(RTL::NOT-MIDPOINT
 (2298 2298
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (2298 2298
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (2298 2298
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (2298 2298
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (1662 214
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (1269 18 (:REWRITE RTL::R-EXACTP-6))
 (1163
  1163
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1163
      1163
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1163
     1163
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1163 1163
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1163 1163
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (1163 1163
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (1087 396 (:REWRITE DEFAULT-PLUS-2))
 (708 176
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (610 218 (:REWRITE DEFAULT-LESS-THAN-2))
 (563 396 (:REWRITE DEFAULT-PLUS-1))
 (556 6 (:LINEAR EXPT->=-1-ONE))
 (556 6 (:LINEAR EXPT-<=-1-TWO))
 (546 6 (:LINEAR EXPT->-1-ONE))
 (546 6 (:LINEAR EXPT-<-1-TWO))
 (500 6 (:LINEAR EXPT-X->=-X))
 (500 6 (:LINEAR EXPT-X->-X))
 (474 218 (:REWRITE DEFAULT-LESS-THAN-1))
 (248 194
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (243 9
      (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (237 13 (:REWRITE ODD-EXPT-THM))
 (234 9
      (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (218 218 (:REWRITE THE-FLOOR-BELOW))
 (218 218 (:REWRITE THE-FLOOR-ABOVE))
 (214 214
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (214 214
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (211 49 (:REWRITE |(< (+ (- c) x) y)|))
 (210 194 (:REWRITE |(< (- x) (- y))|))
 (207 45 (:REWRITE |(< y (+ (- c) x))|))
 (194 194 (:REWRITE INTEGERP-<-CONSTANT))
 (194 194 (:REWRITE CONSTANT-<-INTEGERP))
 (194 194
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (194 194
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (194 194
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (194 194
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (194 194 (:REWRITE |(< c (- x))|))
 (194 194
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (194 194
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (194 194
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (194 194 (:REWRITE |(< (/ x) (/ y))|))
 (194 194 (:REWRITE |(< (- x) c)|))
 (153 53 (:REWRITE RTL::BVECP-EXACTP))
 (135 75 (:REWRITE |(+ c (+ d x))|))
 (115 115
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (100 100 (:TYPE-PRESCRIPTION RTL::BVECP))
 (72 18 (:REWRITE RATIONALP-X))
 (71 39 (:REWRITE DEFAULT-MINUS))
 (68 52 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (66 10 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (66 10
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (66 10
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (65 49 (:REWRITE INTEGERP-MINUS-X))
 (53 53 (:REWRITE |(< x (+ c/d y))|))
 (53 53 (:REWRITE |(< (+ c/d x) y)|))
 (52 52 (:REWRITE DEFAULT-TIMES-2))
 (52 52 (:REWRITE DEFAULT-TIMES-1))
 (49 49 (:REWRITE REDUCE-INTEGERP-+))
 (49 49 (:META META-INTEGERP-CORRECT))
 (43 43
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (43 43 (:REWRITE DEFAULT-DIVIDE))
 (40 40
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (36 18 (:REWRITE DEFAULT-EXPT-2))
 (21 21 (:REWRITE FOLD-CONSTS-IN-+))
 (21 21 (:REWRITE |(< (* x y) 0)|))
 (18 18 (:REWRITE REDUCE-RATIONALP-+))
 (18 18 (:REWRITE REDUCE-RATIONALP-*))
 (18 18 (:REWRITE RATIONALP-MINUS-X))
 (18 18 (:REWRITE DEFAULT-EXPT-1))
 (18 18 (:REWRITE |(expt 1/c n)|))
 (18 18 (:REWRITE |(expt (- x) n)|))
 (18 18 (:META META-RATIONALP-CORRECT))
 (17 17 (:REWRITE |(< (/ x) 0)|))
 (16 16 (:REWRITE |(< 0 (* x y))|))
 (13 13
     (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (12 12 (:REWRITE |(< 0 (/ x))|))
 (12 12
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (12 12
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (12 12
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (12 12
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (10 10
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (10 10
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (10 10
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (10 10 (:REWRITE |(equal c (/ x))|))
 (10 10 (:REWRITE |(equal c (- x))|))
 (10 10 (:REWRITE |(equal (/ x) c)|))
 (10 10 (:REWRITE |(equal (/ x) (/ y))|))
 (10 10 (:REWRITE |(equal (- x) c)|))
 (10 10 (:REWRITE |(equal (- x) (- y))|))
 (9 9
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (9 9
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (6 6 (:REWRITE ZP-OPEN))
 (6 6 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (6 6 (:LINEAR EXPT-LINEAR-UPPER-<))
 (6 6 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (6 6 (:LINEAR EXPT-LINEAR-LOWER-<))
 (6 6 (:LINEAR EXPT->=-1-TWO))
 (6 6 (:LINEAR EXPT->-1-TWO))
 (6 6 (:LINEAR EXPT-<=-1-ONE))
 (6 6 (:LINEAR EXPT-<-1-ONE))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (4 4 (:REWRITE |(equal (+ (- c) x) y)|))
 (4 4 (:REWRITE |(- (* c x))|)))
(RTL::R-POS-RNE-4
 (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (7
  7
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (7 7
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (7 7
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (7 7
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (7 7
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (7 7
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE)))
(RTL::R-POS-RNE-5
 (940 940
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (940 940
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (940 940
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (940 940
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (754
  754
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (754 754
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (754
     754
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (754 754
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (754 754
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (754 754
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (365 9 (:REWRITE RTL::R-EXACTP-6))
 (311 89 (:REWRITE DEFAULT-PLUS-2))
 (308 56
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (273 65 (:REWRITE DEFAULT-LESS-THAN-2))
 (181 47 (:REWRITE SIMPLIFY-SUMS-<))
 (167 89 (:REWRITE DEFAULT-PLUS-1))
 (149 65 (:REWRITE DEFAULT-LESS-THAN-1))
 (93 5 (:REWRITE ODD-EXPT-THM))
 (84 63
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (80 2 (:LINEAR EXPT->=-1-ONE))
 (80 2 (:LINEAR EXPT-<=-1-TWO))
 (78 2 (:LINEAR EXPT->-1-ONE))
 (78 2 (:LINEAR EXPT-<-1-TWO))
 (71 63 (:REWRITE |(< (- x) (- y))|))
 (70 2 (:LINEAR EXPT-X->=-X))
 (70 2 (:LINEAR EXPT-X->-X))
 (66 30 (:REWRITE DEFAULT-TIMES-2))
 (65 65 (:REWRITE THE-FLOOR-BELOW))
 (65 65 (:REWRITE THE-FLOOR-ABOVE))
 (63 63
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (63 63
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (63 63
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (63 63 (:REWRITE INTEGERP-<-CONSTANT))
 (63 63 (:REWRITE CONSTANT-<-INTEGERP))
 (63 63
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (63 63
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (63 63
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (63 63
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (63 63 (:REWRITE |(< c (- x))|))
 (63 63
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (63 63
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (63 63
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (63 63 (:REWRITE |(< (/ x) (/ y))|))
 (63 63 (:REWRITE |(< (- x) c)|))
 (54 2
     (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (52 2
     (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (40 24 (:REWRITE DEFAULT-MINUS))
 (32 32
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (30 30 (:REWRITE DEFAULT-TIMES-1))
 (27 9 (:REWRITE RTL::BVECP-EXACTP))
 (26 18 (:REWRITE INTEGERP-MINUS-X))
 (24 6 (:REWRITE RATIONALP-X))
 (20 20
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (18 18 (:TYPE-PRESCRIPTION RTL::BVECP))
 (18 18 (:REWRITE REDUCE-INTEGERP-+))
 (18 18 (:META META-INTEGERP-CORRECT))
 (18 9 (:REWRITE DEFAULT-EXPT-2))
 (17 17 (:REWRITE |(< y (+ (- c) x))|))
 (17 17 (:REWRITE |(< x (+ c/d y))|))
 (17 9 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (14 14
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (14 14 (:REWRITE DEFAULT-DIVIDE))
 (13 13 (:REWRITE |(< (+ c/d x) y)|))
 (13 13 (:REWRITE |(< (+ (- c) x) y)|))
 (9 9 (:REWRITE DEFAULT-EXPT-1))
 (9 9 (:REWRITE |(expt 1/c n)|))
 (9 9 (:REWRITE |(expt (- x) n)|))
 (8 8 (:REWRITE |(+ c (+ d x))|))
 (6 6 (:REWRITE REDUCE-RATIONALP-+))
 (6 6 (:REWRITE REDUCE-RATIONALP-*))
 (6 6 (:REWRITE RATIONALP-MINUS-X))
 (6 6 (:REWRITE |(< (/ x) 0)|))
 (6 6 (:REWRITE |(< (* x y) 0)|))
 (6 6 (:META META-RATIONALP-CORRECT))
 (5 5 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (4 4 (:REWRITE |(< 0 (/ x))|))
 (4 4 (:REWRITE |(< 0 (* x y))|))
 (4 4 (:REWRITE |(- (* c x))|))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (3 3 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (2 2
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (2 2
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (2 2
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (2 2
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (2 2
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (2 2 (:REWRITE |(equal c (/ x))|))
 (2 2 (:REWRITE |(equal c (- x))|))
 (2 2 (:REWRITE |(equal (/ x) c)|))
 (2 2 (:REWRITE |(equal (/ x) (/ y))|))
 (2 2 (:REWRITE |(equal (- x) c)|))
 (2 2 (:REWRITE |(equal (- x) (- y))|))
 (2 2
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (2 2
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-POS-RNE-6
 (1145 1145
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (1145 1145
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (1145 1145
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (1145 1145
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (1003
  1003
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1003
      1003
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1003
     1003
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1003 1003
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1003 1003
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (1003 1003
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (474 9 (:REWRITE RTL::R-EXACTP-6))
 (361 69
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (331 89 (:REWRITE DEFAULT-PLUS-2))
 (308 76 (:REWRITE DEFAULT-LESS-THAN-2))
 (229 59 (:REWRITE SIMPLIFY-SUMS-<))
 (180 76 (:REWRITE DEFAULT-LESS-THAN-1))
 (156 89 (:REWRITE DEFAULT-PLUS-1))
 (98 74
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (93 5 (:REWRITE ODD-EXPT-THM))
 (82 74 (:REWRITE |(< (- x) (- y))|))
 (81 3
     (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (80 2 (:LINEAR EXPT->=-1-ONE))
 (80 2 (:LINEAR EXPT-<=-1-TWO))
 (78 3
     (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (78 2 (:LINEAR EXPT->-1-ONE))
 (78 2 (:LINEAR EXPT-<-1-TWO))
 (76 76 (:REWRITE THE-FLOOR-BELOW))
 (76 76 (:REWRITE THE-FLOOR-ABOVE))
 (74 74
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (74 74
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (74 74
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (74 74 (:REWRITE INTEGERP-<-CONSTANT))
 (74 74 (:REWRITE CONSTANT-<-INTEGERP))
 (74 74
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (74 74
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (74 74
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (74 74
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (74 74 (:REWRITE |(< c (- x))|))
 (74 74
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (74 74
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (74 74
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (74 74 (:REWRITE |(< (/ x) (/ y))|))
 (74 74 (:REWRITE |(< (- x) c)|))
 (70 2 (:LINEAR EXPT-X->=-X))
 (70 2 (:LINEAR EXPT-X->-X))
 (53 25 (:REWRITE DEFAULT-TIMES-2))
 (37 21 (:REWRITE DEFAULT-MINUS))
 (36 12 (:REWRITE RTL::BVECP-EXACTP))
 (36 9 (:REWRITE RATIONALP-X))
 (31 31
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (30 22 (:REWRITE INTEGERP-MINUS-X))
 (25 25 (:REWRITE DEFAULT-TIMES-1))
 (24 24 (:TYPE-PRESCRIPTION RTL::BVECP))
 (22 22 (:REWRITE REDUCE-INTEGERP-+))
 (22 22 (:META META-INTEGERP-CORRECT))
 (20 20
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (19 19 (:REWRITE |(< y (+ (- c) x))|))
 (19 19 (:REWRITE |(< x (+ c/d y))|))
 (18 10 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (18 9 (:REWRITE DEFAULT-EXPT-2))
 (15 15
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (15 15 (:REWRITE DEFAULT-DIVIDE))
 (14 14 (:REWRITE |(< (+ c/d x) y)|))
 (14 14 (:REWRITE |(< (+ (- c) x) y)|))
 (9 9 (:REWRITE REDUCE-RATIONALP-+))
 (9 9 (:REWRITE REDUCE-RATIONALP-*))
 (9 9 (:REWRITE RATIONALP-MINUS-X))
 (9 9 (:REWRITE DEFAULT-EXPT-1))
 (9 9 (:REWRITE |(expt 1/c n)|))
 (9 9 (:REWRITE |(expt (- x) n)|))
 (9 9 (:REWRITE |(+ c (+ d x))|))
 (9 9 (:META META-RATIONALP-CORRECT))
 (7 7 (:REWRITE |(< (/ x) 0)|))
 (7 7 (:REWRITE |(< (* x y) 0)|))
 (5 5 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (4 4 (:REWRITE |(< 0 (/ x))|))
 (4 4 (:REWRITE |(< 0 (* x y))|))
 (4 4 (:REWRITE |(- (* c x))|))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (3 3 (:REWRITE ZP-OPEN))
 (3 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (3 3
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (3 3
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (3 3
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (3 3
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (3 3 (:REWRITE FOLD-CONSTS-IN-+))
 (3 3
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (3 3 (:REWRITE |(equal c (/ x))|))
 (3 3 (:REWRITE |(equal c (- x))|))
 (3 3 (:REWRITE |(equal (/ x) c)|))
 (3 3 (:REWRITE |(equal (/ x) (/ y))|))
 (3 3 (:REWRITE |(equal (- x) c)|))
 (3 3 (:REWRITE |(equal (- x) (- y))|))
 (3 3
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (3 3
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-POS-RNE-10)
(RTL::R-POS-RNE-11
 (1130 1130
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (1130 1130
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (1130 1130
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (1130 1130
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (1130
  1130
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1130
      1130
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1130
     1130
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1130 1130
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1130 1130
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (1130 1130
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (584 10 (:REWRITE RTL::R-EXACTP-6))
 (451 92 (:REWRITE DEFAULT-PLUS-2))
 (408 72
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (291 79 (:REWRITE DEFAULT-LESS-THAN-2))
 (275 92 (:REWRITE DEFAULT-PLUS-1))
 (252 62 (:REWRITE SIMPLIFY-SUMS-<))
 (247 79 (:REWRITE DEFAULT-LESS-THAN-1))
 (134 34 (:REWRITE DEFAULT-TIMES-1))
 (108 4
      (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (105 77 (:REWRITE |(< (- x) (- y))|))
 (104 4
      (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (101 77
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (94 34 (:REWRITE DEFAULT-TIMES-2))
 (93 5 (:REWRITE ODD-EXPT-THM))
 (80 2 (:LINEAR EXPT->=-1-ONE))
 (80 2 (:LINEAR EXPT-<=-1-TWO))
 (79 79 (:REWRITE THE-FLOOR-BELOW))
 (79 79 (:REWRITE THE-FLOOR-ABOVE))
 (79 77 (:REWRITE |(< (/ x) (/ y))|))
 (78 2 (:LINEAR EXPT->-1-ONE))
 (78 2 (:LINEAR EXPT-<-1-TWO))
 (77 77
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (77 77
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (77 77
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (77 77 (:REWRITE INTEGERP-<-CONSTANT))
 (77 77 (:REWRITE CONSTANT-<-INTEGERP))
 (77 77
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (77 77
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (77 77
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (77 77
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (77 77 (:REWRITE |(< c (- x))|))
 (77 77
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (77 77
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (77 77
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (77 77 (:REWRITE |(< (- x) c)|))
 (70 2 (:LINEAR EXPT-X->=-X))
 (70 2 (:LINEAR EXPT-X->-X))
 (64 26 (:REWRITE DEFAULT-MINUS))
 (38 10 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (36 12 (:REWRITE RTL::BVECP-EXACTP))
 (36 9 (:REWRITE RATIONALP-X))
 (34 34
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (30 22 (:REWRITE INTEGERP-MINUS-X))
 (26 26
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (24 24 (:TYPE-PRESCRIPTION RTL::BVECP))
 (22 22 (:REWRITE REDUCE-INTEGERP-+))
 (22 22 (:META META-INTEGERP-CORRECT))
 (19 19 (:REWRITE |(< y (+ (- c) x))|))
 (19 19 (:REWRITE |(< x (+ c/d y))|))
 (18 9 (:REWRITE DEFAULT-EXPT-2))
 (15 15
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (15 15 (:REWRITE DEFAULT-DIVIDE))
 (14 14 (:REWRITE |(< (+ c/d x) y)|))
 (14 14 (:REWRITE |(< (+ (- c) x) y)|))
 (9 9 (:REWRITE REDUCE-RATIONALP-+))
 (9 9 (:REWRITE REDUCE-RATIONALP-*))
 (9 9 (:REWRITE RATIONALP-MINUS-X))
 (9 9 (:REWRITE DEFAULT-EXPT-1))
 (9 9 (:REWRITE |(expt 1/c n)|))
 (9 9 (:REWRITE |(expt (- x) n)|))
 (9 9 (:REWRITE |(+ c (+ d x))|))
 (9 9 (:META META-RATIONALP-CORRECT))
 (7 7 (:REWRITE |(< (/ x) 0)|))
 (7 7 (:REWRITE |(< (* x y) 0)|))
 (7 7 (:REWRITE |(- (* c x))|))
 (5 5 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (4 4
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (4 4 (:REWRITE |(< 0 (/ x))|))
 (4 4 (:REWRITE |(< 0 (* x y))|))
 (4 4
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (3 3 (:REWRITE ZP-OPEN))
 (3 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (3 3
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (3 3
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (3 3
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (3 3
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (3 3 (:REWRITE FOLD-CONSTS-IN-+))
 (3 3
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (3 3 (:REWRITE |(equal c (/ x))|))
 (3 3 (:REWRITE |(equal c (- x))|))
 (3 3 (:REWRITE |(equal (/ x) c)|))
 (3 3 (:REWRITE |(equal (/ x) (/ y))|))
 (3 3 (:REWRITE |(equal (- x) c)|))
 (3 3 (:REWRITE |(equal (- x) (- y))|))
 (2 2 (:REWRITE |(* c (* d x))|))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-POS-RNE-17
 (759 759
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (759 759
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (759 759
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (759 759
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (574
  574
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (574 574
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (574
     574
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (574 574
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (424 7 (:REWRITE RTL::R-EXACTP-6))
 (276 53
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (265 76 (:REWRITE DEFAULT-PLUS-2))
 (225 59 (:REWRITE DEFAULT-LESS-THAN-2))
 (157 44 (:REWRITE SIMPLIFY-SUMS-<))
 (143 59 (:REWRITE DEFAULT-LESS-THAN-1))
 (137 76 (:REWRITE DEFAULT-PLUS-1))
 (89 6 (:REWRITE ODD-EXPT-THM))
 (81 3
     (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (81 3 (:LINEAR EXPT->=-1-ONE))
 (79 3 (:LINEAR EXPT->-1-ONE))
 (78 3
     (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (73 23 (:REWRITE DEFAULT-TIMES-1))
 (71 3 (:LINEAR EXPT-X->=-X))
 (71 3 (:LINEAR EXPT-X->-X))
 (69 57
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (61 57 (:REWRITE |(< (- x) (- y))|))
 (59 59 (:REWRITE THE-FLOOR-BELOW))
 (59 59 (:REWRITE THE-FLOOR-ABOVE))
 (57 57
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (57 57
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (57 57
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
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
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (57 57
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (57 57
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (57 57 (:REWRITE |(< (/ x) (/ y))|))
 (57 57 (:REWRITE |(< (- x) c)|))
 (53 23 (:REWRITE DEFAULT-TIMES-2))
 (42 22 (:REWRITE DEFAULT-MINUS))
 (30 10 (:REWRITE RTL::BVECP-EXACTP))
 (28 28
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (20 20 (:TYPE-PRESCRIPTION RTL::BVECP))
 (20 5 (:REWRITE RATIONALP-X))
 (19 19
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (19 15 (:REWRITE INTEGERP-MINUS-X))
 (19 6 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (16 10 (:REWRITE DEFAULT-EXPT-2))
 (15 15 (:REWRITE REDUCE-INTEGERP-+))
 (15 15 (:REWRITE |(< y (+ (- c) x))|))
 (15 15 (:REWRITE |(< x (+ c/d y))|))
 (15 15 (:META META-INTEGERP-CORRECT))
 (14 14 (:REWRITE |(< (+ c/d x) y)|))
 (14 14 (:REWRITE |(< (+ (- c) x) y)|))
 (13 9 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (10 10
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (10 10 (:REWRITE DEFAULT-EXPT-1))
 (10 10 (:REWRITE DEFAULT-DIVIDE))
 (10 10 (:REWRITE |(expt 1/c n)|))
 (10 10 (:REWRITE |(expt (- x) n)|))
 (9 9 (:REWRITE |(+ c (+ d x))|))
 (8 8 (:REWRITE |(< (/ x) 0)|))
 (8 8 (:REWRITE |(< (* x y) 0)|))
 (7 7 (:REWRITE |(- (* c x))|))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (6 6
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (5 5
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (5 5
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (5 5 (:REWRITE REDUCE-RATIONALP-+))
 (5 5 (:REWRITE REDUCE-RATIONALP-*))
 (5 5 (:REWRITE RATIONALP-MINUS-X))
 (5 5 (:META META-RATIONALP-CORRECT))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (4 4 (:REWRITE |(< 0 (/ x))|))
 (4 4 (:REWRITE |(< 0 (* x y))|))
 (4 1 (:REWRITE |(integerp (- x))|))
 (3 3 (:REWRITE FOLD-CONSTS-IN-+))
 (3 3
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (3 3
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<))
 (3 3 (:LINEAR EXPT->=-1-TWO))
 (3 3 (:LINEAR EXPT->-1-TWO))
 (3 3 (:LINEAR EXPT-<=-1-ONE))
 (3 3 (:LINEAR EXPT-<-1-ONE))
 (3 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (3 2
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (3 2
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
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
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE |(* c (* d x))|)))
(RTL::R-POS-RNE-20
 (34837
  34837
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (34837
      34837
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (34837
     34837
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (34837 34837
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (16779 16779
        (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (16779 16779
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (16779 16779
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (16779 16779
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (10565 2446 (:REWRITE DEFAULT-PLUS-2))
 (7987 2446 (:REWRITE DEFAULT-PLUS-1))
 (6932 1260 (:REWRITE DEFAULT-TIMES-1))
 (6174 1179 (:REWRITE DEFAULT-LESS-THAN-2))
 (5284 1260 (:REWRITE DEFAULT-TIMES-2))
 (3549 834 (:REWRITE SIMPLIFY-SUMS-<))
 (3031 1179 (:REWRITE DEFAULT-LESS-THAN-1))
 (2842 137 (:REWRITE ODD-EXPT-THM))
 (1756 614 (:REWRITE DEFAULT-MINUS))
 (1502 1142 (:REWRITE |(< (- x) (- y))|))
 (1484 1142
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (1398 346 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (1302 1142 (:REWRITE |(< c (- x))|))
 (1280 1142
       (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (1179 1179 (:REWRITE THE-FLOOR-BELOW))
 (1179 1179 (:REWRITE THE-FLOOR-ABOVE))
 (1175 1142 (:REWRITE |(< (/ x) (/ y))|))
 (1142 1142
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (1142 1142
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (1142 1142
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (1142 1142 (:REWRITE INTEGERP-<-CONSTANT))
 (1142 1142 (:REWRITE CONSTANT-<-INTEGERP))
 (1142 1142
       (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (1142 1142
       (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (1142 1142
       (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (1142 1142
       (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (1142 1142
       (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (1142 1142
       (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (1142 1142 (:REWRITE |(< (- x) c)|))
 (756 28
      (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (728 182 (:REWRITE RATIONALP-X))
 (728 28
      (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (726 726
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (680 121
      (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (600 200 (:REWRITE RTL::BVECP-EXACTP))
 (491 463 (:REWRITE INTEGERP-MINUS-X))
 (463 463 (:REWRITE REDUCE-INTEGERP-+))
 (463 463 (:META META-INTEGERP-CORRECT))
 (400 400 (:TYPE-PRESCRIPTION RTL::BVECP))
 (397 237 (:REWRITE DEFAULT-EXPT-2))
 (262 262 (:REWRITE |(< (+ c/d x) y)|))
 (262 262 (:REWRITE |(< (+ (- c) x) y)|))
 (240 240 (:REWRITE |(< y (+ (- c) x))|))
 (240 240 (:REWRITE |(< x (+ c/d y))|))
 (237 237 (:REWRITE DEFAULT-EXPT-1))
 (237 237 (:REWRITE |(expt 1/c n)|))
 (237 237 (:REWRITE |(expt (- x) n)|))
 (234 234 (:REWRITE |(- (* c x))|))
 (182 182 (:REWRITE REDUCE-RATIONALP-+))
 (182 182 (:REWRITE REDUCE-RATIONALP-*))
 (182 182 (:REWRITE RATIONALP-MINUS-X))
 (182 182 (:META META-RATIONALP-CORRECT))
 (172 43 (:REWRITE |(integerp (- x))|))
 (157 157
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (157 157 (:REWRITE DEFAULT-DIVIDE))
 (118 118 (:REWRITE |(+ c (+ d x))|))
 (88 88 (:REWRITE |(< (/ x) 0)|))
 (88 88 (:REWRITE |(< (* x y) 0)|))
 (84 84 (:REWRITE |(* c (* d x))|))
 (81 3 (:LINEAR EXPT->=-1-ONE))
 (79 3 (:LINEAR EXPT->-1-ONE))
 (71 71 (:REWRITE |(< 0 (/ x))|))
 (71 71 (:REWRITE |(< 0 (* x y))|))
 (71 3 (:LINEAR EXPT-X->=-X))
 (71 3 (:LINEAR EXPT-X->-X))
 (46 46 (:REWRITE ZP-OPEN))
 (46 46 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (46 46
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (46 46
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (46 46
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (46 46
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (46 46 (:REWRITE FOLD-CONSTS-IN-+))
 (46 46
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (46 46 (:REWRITE |(equal c (/ x))|))
 (46 46 (:REWRITE |(equal c (- x))|))
 (46 46 (:REWRITE |(equal (/ x) c)|))
 (46 46 (:REWRITE |(equal (/ x) (/ y))|))
 (46 46 (:REWRITE |(equal (- x) c)|))
 (46 46 (:REWRITE |(equal (- x) (- y))|))
 (36 36
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (36 36
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (28 28
     (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (28 28
     (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (11 11
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (11 11
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (6 6
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<))
 (3 3 (:LINEAR EXPT->=-1-TWO))
 (3 3 (:LINEAR EXPT->-1-TWO))
 (3 3 (:LINEAR EXPT-<=-1-ONE))
 (3 3 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-POS-RNE-25
 (5500
  5500
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (5500
      5500
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (5500
     5500
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (5500 5500
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (3581 3581
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (3581 3581
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (3581 3581
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (1496 346 (:REWRITE DEFAULT-PLUS-2))
 (1293 202
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (1028 346 (:REWRITE DEFAULT-PLUS-1))
 (974 254 (:REWRITE DEFAULT-LESS-THAN-2))
 (810 15 (:REWRITE RTL::R-EXACTP-6))
 (759 254 (:REWRITE DEFAULT-LESS-THAN-1))
 (721 159 (:REWRITE SIMPLIFY-SUMS-<))
 (354 246
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (320 246 (:REWRITE |(< (/ x) (/ y))|))
 (297 246
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (287 246 (:REWRITE |(< (- x) (- y))|))
 (284 24 (:REWRITE ODD-EXPT-THM))
 (254 254 (:REWRITE THE-FLOOR-BELOW))
 (254 254 (:REWRITE THE-FLOOR-ABOVE))
 (246 246
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (246 246
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (246 246
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (246 246 (:REWRITE INTEGERP-<-CONSTANT))
 (246 246 (:REWRITE CONSTANT-<-INTEGERP))
 (246 246
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (246 246
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (246 246
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (246 246 (:REWRITE |(< c (- x))|))
 (246 246
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (246 246
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (246 246
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (246 246 (:REWRITE |(< (- x) c)|))
 (232 70 (:REWRITE DEFAULT-TIMES-2))
 (226 97 (:REWRITE DEFAULT-MINUS))
 (220 70 (:REWRITE DEFAULT-TIMES-1))
 (157 43 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (143 3
      (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (143 3
      (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (143 3 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (143 3 (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (135 5
      (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (130 5
      (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (129 43 (:REWRITE RTL::BVECP-EXACTP))
 (128 24
      (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (116 104 (:REWRITE INTEGERP-MINUS-X))
 (112 112
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (108 27 (:REWRITE RATIONALP-X))
 (107 35 (:REWRITE DEFAULT-DIVIDE))
 (104 104 (:REWRITE REDUCE-INTEGERP-+))
 (104 104 (:META META-INTEGERP-CORRECT))
 (86 86 (:TYPE-PRESCRIPTION RTL::BVECP))
 (81 3 (:LINEAR EXPT->=-1-ONE))
 (79 3 (:LINEAR EXPT->-1-ONE))
 (71 3 (:LINEAR EXPT-X->=-X))
 (71 3 (:LINEAR EXPT-X->-X))
 (60 45 (:REWRITE DEFAULT-EXPT-2))
 (58 58
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (55 55 (:REWRITE |(< (+ c/d x) y)|))
 (55 55 (:REWRITE |(< (+ (- c) x) y)|))
 (45 45 (:REWRITE DEFAULT-EXPT-1))
 (45 45 (:REWRITE |(expt 1/c n)|))
 (45 45 (:REWRITE |(expt (- x) n)|))
 (43 43 (:REWRITE |(< y (+ (- c) x))|))
 (43 43 (:REWRITE |(< x (+ c/d y))|))
 (35 35
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (32 8 (:REWRITE |(integerp (- x))|))
 (27 27 (:REWRITE REDUCE-RATIONALP-+))
 (27 27 (:REWRITE REDUCE-RATIONALP-*))
 (27 27 (:REWRITE RATIONALP-MINUS-X))
 (27 27 (:META META-RATIONALP-CORRECT))
 (26 26 (:REWRITE |(< (/ x) 0)|))
 (26 26 (:REWRITE |(< (* x y) 0)|))
 (20 20 (:REWRITE |(- (* c x))|))
 (16 16 (:REWRITE |(+ c (+ d x))|))
 (11 11
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (11 11
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (10 10 (:REWRITE |(< 0 (/ x))|))
 (10 10 (:REWRITE |(< 0 (* x y))|))
 (7 7 (:REWRITE ZP-OPEN))
 (7 7 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (7 7
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (7 7
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (7 7
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (7 7
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (7 7
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (7 7 (:REWRITE |(equal c (/ x))|))
 (7 7 (:REWRITE |(equal c (- x))|))
 (7 7 (:REWRITE |(equal (/ x) c)|))
 (7 7 (:REWRITE |(equal (/ x) (/ y))|))
 (7 7 (:REWRITE |(equal (- x) c)|))
 (7 7 (:REWRITE |(equal (- x) (- y))|))
 (6 6 (:REWRITE FOLD-CONSTS-IN-+))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (6 6
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (5 5
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (5 5
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (3 3 (:REWRITE |(* c (* d x))|))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<))
 (3 3 (:LINEAR EXPT->=-1-TWO))
 (3 3 (:LINEAR EXPT->-1-TWO))
 (3 3 (:LINEAR EXPT-<=-1-ONE))
 (3 3 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-POS-RNE-26
 (21113
  21113
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (21113
      21113
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (21113
     21113
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (21113 21113
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (7201 2024 (:REWRITE DEFAULT-PLUS-2))
 (5404 2024 (:REWRITE DEFAULT-PLUS-1))
 (4997 878 (:REWRITE DEFAULT-LESS-THAN-2))
 (4016 892 (:REWRITE DEFAULT-TIMES-2))
 (2344 892 (:REWRITE DEFAULT-TIMES-1))
 (2285 580 (:REWRITE SIMPLIFY-SUMS-<))
 (1954 137 (:REWRITE ODD-EXPT-THM))
 (1539 878 (:REWRITE DEFAULT-LESS-THAN-1))
 (1259 537 (:REWRITE DEFAULT-MINUS))
 (1072 832 (:REWRITE |(< c (- x))|))
 (1049 832 (:REWRITE |(< (- x) (- y))|))
 (989 290 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (976 832
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (932 832 (:REWRITE |(< (- x) c)|))
 (878 878 (:REWRITE THE-FLOOR-BELOW))
 (878 878 (:REWRITE THE-FLOOR-ABOVE))
 (853 832 (:REWRITE |(< (/ x) (/ y))|))
 (832 832
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (832 832
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (832 832
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (832 832 (:REWRITE INTEGERP-<-CONSTANT))
 (832 832 (:REWRITE CONSTANT-<-INTEGERP))
 (832 832
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (832 832
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (832 832
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (832 832
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (832 832
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (832 832
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (832 832
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (807 807 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (685 126
      (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (563 563
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (540 180 (:REWRITE RTL::BVECP-EXACTP))
 (448 112 (:REWRITE RATIONALP-X))
 (360 360 (:TYPE-PRESCRIPTION RTL::BVECP))
 (286 286 (:REWRITE REDUCE-INTEGERP-+))
 (286 286 (:REWRITE INTEGERP-MINUS-X))
 (286 286 (:META META-INTEGERP-CORRECT))
 (280 188 (:REWRITE DEFAULT-EXPT-2))
 (246 246 (:REWRITE |(< (+ c/d x) y)|))
 (246 246 (:REWRITE |(< (+ (- c) x) y)|))
 (202 202 (:REWRITE |(< y (+ (- c) x))|))
 (202 202 (:REWRITE |(< x (+ c/d y))|))
 (188 188 (:REWRITE DEFAULT-EXPT-1))
 (188 188 (:REWRITE |(expt 1/c n)|))
 (188 188 (:REWRITE |(expt (- x) n)|))
 (172 43 (:REWRITE |(integerp (- x))|))
 (158 158
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (158 158
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (158 158
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (158 158
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (112 112 (:REWRITE REDUCE-RATIONALP-+))
 (112 112 (:REWRITE REDUCE-RATIONALP-*))
 (112 112 (:REWRITE RATIONALP-MINUS-X))
 (112 112 (:META META-RATIONALP-CORRECT))
 (84 84 (:REWRITE |(< (/ x) 0)|))
 (84 84 (:REWRITE |(< (* x y) 0)|))
 (81 3 (:LINEAR EXPT->=-1-ONE))
 (79 3 (:LINEAR EXPT->-1-ONE))
 (71 3 (:LINEAR EXPT-X->=-X))
 (71 3 (:LINEAR EXPT-X->-X))
 (55 55 (:REWRITE |(- (* c x))|))
 (49 49 (:REWRITE |(< 0 (/ x))|))
 (49 49 (:REWRITE |(< 0 (* x y))|))
 (44 44 (:REWRITE |(+ c (+ d x))|))
 (31 31 (:REWRITE ZP-OPEN))
 (31 31 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (31 31
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (31 31
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (31 31
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (31 31
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (31 31
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (31 31 (:REWRITE |(equal c (/ x))|))
 (31 31 (:REWRITE |(equal c (- x))|))
 (31 31 (:REWRITE |(equal (/ x) c)|))
 (31 31 (:REWRITE |(equal (/ x) (/ y))|))
 (31 31 (:REWRITE |(equal (- x) c)|))
 (31 31 (:REWRITE |(equal (- x) (- y))|))
 (24 24
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (24 24
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (13 13 (:REWRITE FOLD-CONSTS-IN-+))
 (11 11
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (11 11
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (6 6
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<))
 (3 3 (:LINEAR EXPT->=-1-TWO))
 (3 3 (:LINEAR EXPT->-1-TWO))
 (3 3 (:LINEAR EXPT-<=-1-ONE))
 (3 3 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-POS-RNE-28)
(RTL::R-POS-RNE-29
 (29146
  29146
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (29146
      29146
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (29146
     29146
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (29146 29146
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (18658 2266
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (17363 17363
        (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (17363 17363
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (17363 17363
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (17363 17363
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (13630 4369 (:REWRITE DEFAULT-PLUS-2))
 (9860 1984
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (9231 4369 (:REWRITE DEFAULT-PLUS-1))
 (8359 2343 (:REWRITE DEFAULT-LESS-THAN-2))
 (5899 77 (:LINEAR EXPT->=-1-ONE))
 (5841 2343 (:REWRITE DEFAULT-LESS-THAN-1))
 (5822 1429 (:REWRITE SIMPLIFY-SUMS-<))
 (5257 77 (:LINEAR EXPT->-1-ONE))
 (5115 39
       (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (5010 39
       (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (4831 77 (:LINEAR EXPT-X->=-X))
 (4831 77 (:LINEAR EXPT-X->-X))
 (3074 804 (:REWRITE DEFAULT-TIMES-2))
 (2854 804 (:REWRITE DEFAULT-TIMES-1))
 (2680 2038 (:REWRITE |(< (- x) (- y))|))
 (2489 186 (:REWRITE ODD-EXPT-THM))
 (2368 2038
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (2354 2038 (:REWRITE |(< (- x) c)|))
 (2346 564 (:REWRITE |(< (+ (- c) x) y)|))
 (2343 2343 (:REWRITE THE-FLOOR-BELOW))
 (2343 2343 (:REWRITE THE-FLOOR-ABOVE))
 (2323 541 (:REWRITE |(< y (+ (- c) x))|))
 (2266 2266
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (2266 2266
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (2077 2038 (:REWRITE |(< (/ x) (/ y))|))
 (2038 2038
       (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (2038 2038
       (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (2038 2038
       (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (2038 2038
       (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (2038 2038 (:REWRITE |(< c (- x))|))
 (2038 2038
       (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (2038 2038
       (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (2038 2038
       (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (2030 2030 (:REWRITE INTEGERP-<-CONSTANT))
 (2030 2030 (:REWRITE CONSTANT-<-INTEGERP))
 (1805 39
       (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (1805 39
       (:REWRITE |(< x (/ y)) with (< y 0)|))
 (1472 639 (:REWRITE DEFAULT-MINUS))
 (1404 52
       (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (1377 693 (:REWRITE |(+ c (+ d x))|))
 (1352 52
       (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (1197 555 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (1133 1133
       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (841 211 (:REWRITE RATIONALP-X))
 (795 186
      (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (658 506 (:REWRITE INTEGERP-MINUS-X))
 (629 629 (:REWRITE |(< x (+ c/d y))|))
 (616 616 (:REWRITE |(< (+ c/d x) y)|))
 (585 195 (:REWRITE RTL::BVECP-EXACTP))
 (542 542
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (506 506 (:REWRITE REDUCE-INTEGERP-+))
 (506 506 (:META META-INTEGERP-CORRECT))
 (480 316 (:REWRITE DEFAULT-EXPT-2))
 (390 390 (:TYPE-PRESCRIPTION RTL::BVECP))
 (316 316 (:REWRITE DEFAULT-EXPT-1))
 (316 316 (:REWRITE |(expt 1/c n)|))
 (316 316 (:REWRITE |(expt (- x) n)|))
 (275 275
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (275 275 (:REWRITE DEFAULT-DIVIDE))
 (273 273 (:REWRITE |(< (* x y) 0)|))
 (221 221 (:REWRITE |(< (/ x) 0)|))
 (211 211 (:REWRITE REDUCE-RATIONALP-+))
 (211 211 (:REWRITE REDUCE-RATIONALP-*))
 (211 211 (:REWRITE RATIONALP-MINUS-X))
 (211 211 (:META META-RATIONALP-CORRECT))
 (204 204 (:REWRITE |(< 0 (* x y))|))
 (184 184 (:REWRITE FOLD-CONSTS-IN-+))
 (180 45 (:REWRITE |(integerp (- x))|))
 (177 177 (:REWRITE |(- (* c x))|))
 (160 160 (:REWRITE |(< 0 (/ x))|))
 (154 154
      (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (154 154
      (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (154 154
      (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (154 154
      (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (77 77 (:LINEAR EXPT-LINEAR-UPPER-<))
 (77 77 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (77 77 (:LINEAR EXPT-LINEAR-LOWER-<))
 (77 77 (:LINEAR EXPT->=-1-TWO))
 (77 77 (:LINEAR EXPT->-1-TWO))
 (77 77 (:LINEAR EXPT-<=-1-ONE))
 (77 77 (:LINEAR EXPT-<-1-ONE))
 (72 72
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (72 72
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (72 72
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (72 72
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (69 69 (:REWRITE |(* c (* d x))|))
 (52 52 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (52 52
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (52 52
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (52 52
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (52 52
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (52 52
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (52 52 (:REWRITE |(equal c (/ x))|))
 (52 52 (:REWRITE |(equal c (- x))|))
 (52 52 (:REWRITE |(equal (/ x) c)|))
 (52 52 (:REWRITE |(equal (/ x) (/ y))|))
 (52 52 (:REWRITE |(equal (- x) c)|))
 (52 52 (:REWRITE |(equal (- x) (- y))|))
 (52 52
     (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (52 52
     (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (51 51 (:REWRITE ZP-OPEN))
 (11 11
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (11 11
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1)))
(RTL::R-POS-RNE-30)
(RTL::R-POS-RNE-31
 (4874
  4874
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (4874
      4874
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (4874
     4874
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (4874 4874
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (2931 2931
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (2931 2931
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (2931 2931
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (2931 2931
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (1734 544 (:REWRITE DEFAULT-PLUS-2))
 (1731 283
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (1324 34 (:REWRITE RTL::R-EXACTP-6))
 (1268 255
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (1191 544 (:REWRITE DEFAULT-PLUS-1))
 (1092 294 (:REWRITE DEFAULT-LESS-THAN-2))
 (797 193 (:REWRITE SIMPLIFY-SUMS-<))
 (784 294 (:REWRITE DEFAULT-LESS-THAN-1))
 (736 188 (:REWRITE DEFAULT-TIMES-2))
 (692 188 (:REWRITE DEFAULT-TIMES-1))
 (559 9 (:LINEAR EXPT->=-1-ONE))
 (549 9 (:LINEAR EXPT->-1-ONE))
 (503 9 (:LINEAR EXPT-X->=-X))
 (503 9 (:LINEAR EXPT-X->-X))
 (343 263 (:REWRITE |(< (- x) (- y))|))
 (326 24 (:REWRITE ODD-EXPT-THM))
 (321 261 (:REWRITE |(< (- x) c)|))
 (311 263
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (297 263
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (294 294 (:REWRITE THE-FLOOR-BELOW))
 (294 294 (:REWRITE THE-FLOOR-ABOVE))
 (283 283
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (283 283
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (270 263 (:REWRITE |(< (/ x) (/ y))|))
 (263 263
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (263 263
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (263 263
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (263 263
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (263 263
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (263 263
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (261 261 (:REWRITE INTEGERP-<-CONSTANT))
 (261 261 (:REWRITE CONSTANT-<-INTEGERP))
 (261 261 (:REWRITE |(< c (- x))|))
 (238 108 (:REWRITE DEFAULT-MINUS))
 (230 68 (:REWRITE |(< y (+ (- c) x))|))
 (230 68 (:REWRITE |(< (+ (- c) x) y)|))
 (216 8
      (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (208 8
      (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (198 74 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (152 152
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (130 70 (:REWRITE |(+ c (+ d x))|))
 (120 30 (:REWRITE RATIONALP-X))
 (103 25
      (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (92 72 (:REWRITE INTEGERP-MINUS-X))
 (90 3
     (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (90 3
     (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (90 3 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (90 3 (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (86 52 (:REWRITE DEFAULT-EXPT-2))
 (83 72 (:REWRITE REDUCE-INTEGERP-+))
 (78 26 (:REWRITE RTL::BVECP-EXACTP))
 (76 76 (:REWRITE |(< x (+ c/d y))|))
 (72 72 (:REWRITE |(< (+ c/d x) y)|))
 (72 72 (:META META-INTEGERP-CORRECT))
 (52 52 (:TYPE-PRESCRIPTION RTL::BVECP))
 (52 52 (:REWRITE DEFAULT-EXPT-1))
 (52 52 (:REWRITE |(expt 1/c n)|))
 (52 52 (:REWRITE |(expt (- x) n)|))
 (43 43 (:REWRITE DEFAULT-DIVIDE))
 (41 41
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (33 33 (:REWRITE |(< (* x y) 0)|))
 (30 30 (:REWRITE REDUCE-RATIONALP-+))
 (30 30 (:REWRITE REDUCE-RATIONALP-*))
 (30 30 (:REWRITE RATIONALP-MINUS-X))
 (30 30 (:META META-RATIONALP-CORRECT))
 (29 29 (:REWRITE |(< (/ x) 0)|))
 (29 29 (:REWRITE |(- (* c x))|))
 (27 27 (:REWRITE |(< 0 (* x y))|))
 (24 24 (:REWRITE |(* c (* d x))|))
 (24 6 (:REWRITE |(integerp (- x))|))
 (20 20 (:REWRITE FOLD-CONSTS-IN-+))
 (18 18
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (18 18
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (18 18
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (18 18
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (13 13
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (13 13
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (10 10 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (10 10 (:LINEAR EXPT-LINEAR-LOWER-<))
 (9 9 (:LINEAR EXPT-LINEAR-UPPER-<))
 (9 9 (:LINEAR EXPT->=-1-TWO))
 (9 9 (:LINEAR EXPT->-1-TWO))
 (9 9 (:LINEAR EXPT-<=-1-ONE))
 (9 9 (:LINEAR EXPT-<-1-ONE))
 (8 8
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (8 8
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (8 8 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (8 8
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (8 8
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (8 8
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (8 8
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (8 8
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (8 8 (:REWRITE |(equal c (/ x))|))
 (8 8 (:REWRITE |(equal c (- x))|))
 (8 8 (:REWRITE |(equal (/ x) c)|))
 (8 8 (:REWRITE |(equal (/ x) (/ y))|))
 (8 8 (:REWRITE |(equal (- x) c)|))
 (8 8 (:REWRITE |(equal (- x) (- y))|))
 (8 8
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (8 8
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (7 7 (:REWRITE ZP-OPEN))
 (5 5
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (5 5
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (5 5
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RTL::R-POS-RNE-32)
(RTL::R-POS-RNE-33
 (2427
  2427
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (2427
      2427
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (2427
     2427
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (2427 2427
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1926 1926
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (1926 1926
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (1926 1926
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (1926 1926
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (815 20 (:REWRITE RTL::R-EXACTP-6))
 (734 134
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (716 248 (:REWRITE DEFAULT-PLUS-2))
 (685 146 (:REWRITE DEFAULT-LESS-THAN-2))
 (466 248 (:REWRITE DEFAULT-PLUS-1))
 (436 107 (:REWRITE SIMPLIFY-SUMS-<))
 (390 118 (:REWRITE DEFAULT-TIMES-1))
 (362 118 (:REWRITE DEFAULT-TIMES-2))
 (314 146 (:REWRITE DEFAULT-LESS-THAN-1))
 (248 21 (:REWRITE ODD-EXPT-THM))
 (175 139
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (151 139 (:REWRITE |(< (- x) (- y))|))
 (146 146 (:REWRITE THE-FLOOR-BELOW))
 (146 146 (:REWRITE THE-FLOOR-ABOVE))
 (139 139
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (139 139
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (139 139
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (139 139 (:REWRITE INTEGERP-<-CONSTANT))
 (139 139 (:REWRITE CONSTANT-<-INTEGERP))
 (139 139
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (139 139
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (139 139
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (139 139
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (139 139 (:REWRITE |(< c (- x))|))
 (139 139
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (139 139
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (139 139
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (139 139 (:REWRITE |(< (/ x) (/ y))|))
 (139 139 (:REWRITE |(< (- x) c)|))
 (135 5
      (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (130 5
      (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (126 73 (:REWRITE DEFAULT-MINUS))
 (86 21
     (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (84 21 (:REWRITE RATIONALP-X))
 (81 3 (:LINEAR EXPT->=-1-ONE))
 (79 3 (:LINEAR EXPT->-1-ONE))
 (78 78
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (71 3 (:LINEAR EXPT-X->=-X))
 (71 3 (:LINEAR EXPT-X->-X))
 (67 33 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (66 54 (:REWRITE INTEGERP-MINUS-X))
 (57 19 (:REWRITE RTL::BVECP-EXACTP))
 (54 54 (:REWRITE REDUCE-INTEGERP-+))
 (54 54 (:META META-INTEGERP-CORRECT))
 (47 28 (:REWRITE DEFAULT-EXPT-2))
 (38 38 (:TYPE-PRESCRIPTION RTL::BVECP))
 (36 36 (:REWRITE |(< (+ c/d x) y)|))
 (36 36 (:REWRITE |(< (+ (- c) x) y)|))
 (31 31 (:REWRITE |(< y (+ (- c) x))|))
 (31 31 (:REWRITE |(< x (+ c/d y))|))
 (28 28 (:REWRITE DEFAULT-EXPT-1))
 (28 28 (:REWRITE |(expt 1/c n)|))
 (28 28 (:REWRITE |(expt (- x) n)|))
 (24 24
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (24 24 (:REWRITE DEFAULT-DIVIDE))
 (21 21 (:REWRITE REDUCE-RATIONALP-+))
 (21 21 (:REWRITE REDUCE-RATIONALP-*))
 (21 21 (:REWRITE RATIONALP-MINUS-X))
 (21 21 (:META META-RATIONALP-CORRECT))
 (20 20 (:REWRITE |(- (* c x))|))
 (20 5 (:REWRITE |(integerp (- x))|))
 (15 15 (:REWRITE |(< (/ x) 0)|))
 (15 15 (:REWRITE |(< (* x y) 0)|))
 (15 15 (:REWRITE |(+ c (+ d x))|))
 (11 11 (:REWRITE |(* c (* d x))|))
 (8 8
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (8 8
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (6 6
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (5 5 (:REWRITE ZP-OPEN))
 (5 5 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (5 5
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (5 5
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (5 5
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (5 5
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (5 5 (:REWRITE FOLD-CONSTS-IN-+))
 (5 5
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (5 5 (:REWRITE |(equal c (/ x))|))
 (5 5 (:REWRITE |(equal c (- x))|))
 (5 5 (:REWRITE |(equal (/ x) c)|))
 (5 5 (:REWRITE |(equal (/ x) (/ y))|))
 (5 5 (:REWRITE |(equal (- x) c)|))
 (5 5 (:REWRITE |(equal (- x) (- y))|))
 (5 5
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (5 5
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (4 4 (:REWRITE |(< 0 (/ x))|))
 (4 4 (:REWRITE |(< 0 (* x y))|))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<))
 (3 3 (:LINEAR EXPT->=-1-TWO))
 (3 3 (:LINEAR EXPT->-1-TWO))
 (3 3 (:LINEAR EXPT-<=-1-ONE))
 (3 3 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-POS-RNE-34
 (5211
  5211
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (5211
      5211
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (5211
     5211
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (5211 5211
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (5098 5098
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (5098 5098
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (5098 5098
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (5098 5098
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (2020 34 (:REWRITE RTL::R-EXACTP-6))
 (1958 741 (:REWRITE DEFAULT-PLUS-2))
 (1876 485 (:REWRITE DEFAULT-LESS-THAN-2))
 (1226 741 (:REWRITE DEFAULT-PLUS-1))
 (889 485 (:REWRITE DEFAULT-LESS-THAN-1))
 (705 62 (:REWRITE ODD-EXPT-THM))
 (652 466
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (486 466 (:REWRITE |(< (- x) (- y))|))
 (485 485 (:REWRITE THE-FLOOR-BELOW))
 (485 485 (:REWRITE THE-FLOOR-ABOVE))
 (468 468
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (468 468
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (468 468
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (466 466 (:REWRITE INTEGERP-<-CONSTANT))
 (466 466 (:REWRITE CONSTANT-<-INTEGERP))
 (466 466
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (466 466
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (466 466
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (466 466
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (466 466 (:REWRITE |(< c (- x))|))
 (466 466
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (466 466
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (466 466
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (466 466 (:REWRITE |(< (/ x) (/ y))|))
 (466 466 (:REWRITE |(< (- x) c)|))
 (378 14
      (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (364 14
      (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (335 62
      (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (234 78 (:REWRITE RTL::BVECP-EXACTP))
 (214 174 (:REWRITE DEFAULT-MINUS))
 (207 207
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (196 49 (:REWRITE RATIONALP-X))
 (193 173 (:REWRITE INTEGERP-MINUS-X))
 (173 173 (:REWRITE REDUCE-INTEGERP-+))
 (173 173 (:META META-INTEGERP-CORRECT))
 (166 166 (:REWRITE DEFAULT-TIMES-2))
 (166 166 (:REWRITE DEFAULT-TIMES-1))
 (156 156 (:TYPE-PRESCRIPTION RTL::BVECP))
 (119 119
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (118 98 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (116 116 (:REWRITE |(< (+ c/d x) y)|))
 (116 116 (:REWRITE |(< (+ (- c) x) y)|))
 (97 65 (:REWRITE DEFAULT-EXPT-2))
 (84 21 (:REWRITE |(integerp (- x))|))
 (81 3 (:LINEAR EXPT->=-1-ONE))
 (79 3 (:LINEAR EXPT->-1-ONE))
 (75 75 (:REWRITE |(< y (+ (- c) x))|))
 (75 75 (:REWRITE |(< x (+ c/d y))|))
 (71 3 (:LINEAR EXPT-X->=-X))
 (71 3 (:LINEAR EXPT-X->-X))
 (65 65 (:REWRITE DEFAULT-EXPT-1))
 (65 65 (:REWRITE |(expt 1/c n)|))
 (65 65 (:REWRITE |(expt (- x) n)|))
 (61 61
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (61 61 (:REWRITE DEFAULT-DIVIDE))
 (58 58 (:REWRITE |(+ c (+ d x))|))
 (49 49 (:REWRITE REDUCE-RATIONALP-+))
 (49 49 (:REWRITE REDUCE-RATIONALP-*))
 (49 49 (:REWRITE RATIONALP-MINUS-X))
 (49 49 (:META META-RATIONALP-CORRECT))
 (48 48 (:REWRITE |(< (/ x) 0)|))
 (48 48 (:REWRITE |(< (* x y) 0)|))
 (46 46 (:REWRITE |(- (* c x))|))
 (22 22 (:REWRITE FOLD-CONSTS-IN-+))
 (16 14 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (16 14
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (16 14
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (14 14
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (14 14
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (14 14
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (14 14
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (14 14
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (14 14 (:REWRITE |(equal c (/ x))|))
 (14 14 (:REWRITE |(equal c (- x))|))
 (14 14 (:REWRITE |(equal (/ x) c)|))
 (14 14 (:REWRITE |(equal (/ x) (/ y))|))
 (14 14 (:REWRITE |(equal (- x) c)|))
 (14 14 (:REWRITE |(equal (- x) (- y))|))
 (14 14
     (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (14 14
     (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (13 13 (:REWRITE ZP-OPEN))
 (9 9 (:REWRITE |(< 0 (* x y))|))
 (7 7 (:REWRITE |(< 0 (/ x))|))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (6 6
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (5 5 (:REWRITE |(* c (* d x))|))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<))
 (3 3 (:LINEAR EXPT->=-1-TWO))
 (3 3 (:LINEAR EXPT->-1-TWO))
 (3 3 (:LINEAR EXPT-<=-1-ONE))
 (3 3 (:LINEAR EXPT-<-1-ONE))
 (2 2
    (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (2 2
    (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (2 2
    (:REWRITE |(< x (/ y)) with (< y 0)|)))
(RTL::R-POS-RNE-DOWN
 (20657 20657
        (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (20657 20657
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (20657 20657
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (20657 20657
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (19984
  19984
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (19984
      19984
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (19984
     19984
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (19984 19984
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (6569 2407 (:REWRITE DEFAULT-PLUS-2))
 (5847 1104
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (5599 115 (:REWRITE RTL::R-EXACTP-6))
 (4980 1181 (:REWRITE DEFAULT-LESS-THAN-2))
 (3621 2407 (:REWRITE DEFAULT-PLUS-1))
 (2173 1181 (:REWRITE DEFAULT-LESS-THAN-1))
 (1496 1142
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (1422 127 (:REWRITE ODD-EXPT-THM))
 (1181 1181 (:REWRITE THE-FLOOR-BELOW))
 (1181 1181 (:REWRITE THE-FLOOR-ABOVE))
 (1170 1142 (:REWRITE |(< (- x) (- y))|))
 (1142 1142
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (1142 1142
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (1142 1142
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (1142 1142 (:REWRITE INTEGERP-<-CONSTANT))
 (1142 1142 (:REWRITE CONSTANT-<-INTEGERP))
 (1142 1142
       (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (1142 1142
       (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (1142 1142
       (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (1142 1142
       (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (1142 1142 (:REWRITE |(< c (- x))|))
 (1142 1142
       (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (1142 1142
       (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (1142 1142
       (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (1142 1142 (:REWRITE |(< (/ x) (/ y))|))
 (1142 1142 (:REWRITE |(< (- x) c)|))
 (1036 1036 (:REWRITE DEFAULT-TIMES-2))
 (1036 1036 (:REWRITE DEFAULT-TIMES-1))
 (847 847
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (810 30
      (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (780 30
      (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (712 127
      (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (700 175 (:REWRITE RATIONALP-X))
 (656 656
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (612 204 (:REWRITE RTL::BVECP-EXACTP))
 (581 525 (:REWRITE DEFAULT-MINUS))
 (448 420 (:REWRITE INTEGERP-MINUS-X))
 (420 420 (:REWRITE REDUCE-INTEGERP-+))
 (420 420 (:META META-INTEGERP-CORRECT))
 (408 408 (:TYPE-PRESCRIPTION RTL::BVECP))
 (382 116 (:REWRITE |(equal (/ x) c)|))
 (310 282 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (292 292 (:REWRITE |(< (+ c/d x) y)|))
 (292 292 (:REWRITE |(< (+ (- c) x) y)|))
 (291 176 (:REWRITE DEFAULT-EXPT-2))
 (276 276 (:REWRITE |(+ c (+ d x))|))
 (236 236 (:REWRITE DEFAULT-DIVIDE))
 (234 234 (:REWRITE |(< y (+ (- c) x))|))
 (234 234 (:REWRITE |(< x (+ c/d y))|))
 (218 218 (:REWRITE |(- (* c x))|))
 (217 217
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (183 97 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (183 97
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (183 97
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (180 45 (:REWRITE |(integerp (- x))|))
 (176 176 (:REWRITE DEFAULT-EXPT-1))
 (176 176 (:REWRITE |(expt 1/c n)|))
 (176 176 (:REWRITE |(expt (- x) n)|))
 (175 175 (:REWRITE REDUCE-RATIONALP-+))
 (175 175 (:REWRITE REDUCE-RATIONALP-*))
 (175 175 (:REWRITE RATIONALP-MINUS-X))
 (175 175 (:META META-RATIONALP-CORRECT))
 (142 142 (:REWRITE FOLD-CONSTS-IN-+))
 (116 116
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (116 116
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (116 116 (:REWRITE |(equal c (/ x))|))
 (116 116 (:REWRITE |(equal (/ x) (/ y))|))
 (116 116 (:REWRITE |(equal (- x) (- y))|))
 (97 97
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (97 97 (:REWRITE |(equal c (- x))|))
 (97 97 (:REWRITE |(equal (- x) c)|))
 (92 92 (:REWRITE |(< (/ x) 0)|))
 (92 92 (:REWRITE |(< (* x y) 0)|))
 (81 3 (:LINEAR EXPT->=-1-ONE))
 (79 3 (:LINEAR EXPT->-1-ONE))
 (76 76 (:REWRITE |(* c (* d x))|))
 (71 3 (:LINEAR EXPT-X->=-X))
 (71 3 (:LINEAR EXPT-X->-X))
 (64 2 (:LINEAR RTL::RNE-POSITIVE))
 (51 51 (:REWRITE ZP-OPEN))
 (35 35 (:REWRITE |(< 0 (/ x))|))
 (35 35 (:REWRITE |(< 0 (* x y))|))
 (34 34
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (34 34
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (30 30
     (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (30 30
     (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (19 19
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (19 19 (:REWRITE |(not (equal x (/ y)))|))
 (19 19 (:REWRITE |(equal x (/ y))|))
 (19 19 (:REWRITE |(/ (/ x))|))
 (11 11
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (11 11
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (6 6
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<))
 (3 3 (:LINEAR EXPT->=-1-TWO))
 (3 3 (:LINEAR EXPT->-1-TWO))
 (3 3 (:LINEAR EXPT-<=-1-ONE))
 (3 3 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-POS-RNE-UP-4
 (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (7
  7
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (7 7
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (7 7
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (7 7
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (7 7
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (7 7
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE)))
(RTL::R-POS-RNE-UP-5
 (929 929
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (929 929
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (929 929
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (929 929
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (769
  769
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (769 769
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (769
     769
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (769 769
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (769 769
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (769 769
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (392 10 (:REWRITE RTL::R-EXACTP-6))
 (338 101 (:REWRITE DEFAULT-PLUS-2))
 (321 57
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (248 68 (:REWRITE DEFAULT-LESS-THAN-1))
 (212 68 (:REWRITE DEFAULT-LESS-THAN-2))
 (185 101 (:REWRITE DEFAULT-PLUS-1))
 (183 47 (:REWRITE SIMPLIFY-SUMS-<))
 (93 39 (:REWRITE DEFAULT-TIMES-2))
 (87 66
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (80 2 (:LINEAR EXPT->=-1-ONE))
 (80 2 (:LINEAR EXPT-<=-1-TWO))
 (78 2 (:LINEAR EXPT->-1-ONE))
 (78 2 (:LINEAR EXPT-<-1-TWO))
 (76 4 (:REWRITE ODD-EXPT-THM))
 (74 66 (:REWRITE |(< (- x) (- y))|))
 (70 2 (:LINEAR EXPT-X->=-X))
 (70 2 (:LINEAR EXPT-X->-X))
 (68 68 (:REWRITE THE-FLOOR-BELOW))
 (68 68 (:REWRITE THE-FLOOR-ABOVE))
 (66 66
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (66 66
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (66 66
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (66 66 (:REWRITE INTEGERP-<-CONSTANT))
 (66 66 (:REWRITE CONSTANT-<-INTEGERP))
 (66 66
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (66 66
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (66 66
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (66 66
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (66 66 (:REWRITE |(< c (- x))|))
 (66 66
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (66 66
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (66 66
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (66 66 (:REWRITE |(< (/ x) (/ y))|))
 (66 66 (:REWRITE |(< (- x) c)|))
 (54 2
     (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (52 2
     (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (43 27 (:REWRITE DEFAULT-MINUS))
 (39 39 (:REWRITE DEFAULT-TIMES-1))
 (36 36
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (27 9 (:REWRITE RTL::BVECP-EXACTP))
 (25 17 (:REWRITE INTEGERP-MINUS-X))
 (24 24
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (24 6 (:REWRITE RATIONALP-X))
 (20 10 (:REWRITE DEFAULT-EXPT-2))
 (18 18 (:TYPE-PRESCRIPTION RTL::BVECP))
 (18 10 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (17 17 (:REWRITE REDUCE-INTEGERP-+))
 (17 17 (:META META-INTEGERP-CORRECT))
 (16 16 (:REWRITE |(< y (+ (- c) x))|))
 (16 16 (:REWRITE |(< x (+ c/d y))|))
 (16 16 (:REWRITE |(< (+ c/d x) y)|))
 (16 16 (:REWRITE |(< (+ (- c) x) y)|))
 (15 15
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (15 15 (:REWRITE DEFAULT-DIVIDE))
 (10 10 (:REWRITE DEFAULT-EXPT-1))
 (10 10 (:REWRITE |(expt 1/c n)|))
 (10 10 (:REWRITE |(expt (- x) n)|))
 (8 8 (:REWRITE |(+ c (+ d x))|))
 (6 6 (:REWRITE REDUCE-RATIONALP-+))
 (6 6 (:REWRITE REDUCE-RATIONALP-*))
 (6 6 (:REWRITE RATIONALP-MINUS-X))
 (6 6 (:REWRITE |(< (/ x) 0)|))
 (6 6 (:REWRITE |(< (* x y) 0)|))
 (6 6 (:META META-RATIONALP-CORRECT))
 (5 5 (:REWRITE |(- (* c x))|))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (4 4 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (4 4 (:REWRITE |(< 0 (/ x))|))
 (4 4 (:REWRITE |(< 0 (* x y))|))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (3 3 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (2 2
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (2 2
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (2 2
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (2 2
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (2 2
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (2 2 (:REWRITE |(equal c (/ x))|))
 (2 2 (:REWRITE |(equal c (- x))|))
 (2 2 (:REWRITE |(equal (/ x) c)|))
 (2 2 (:REWRITE |(equal (/ x) (/ y))|))
 (2 2 (:REWRITE |(equal (- x) c)|))
 (2 2 (:REWRITE |(equal (- x) (- y))|))
 (2 2
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (2 2
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-POS-RNE-UP-6
 (1116 1116
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (1116 1116
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (1116 1116
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (1116 1116
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (1018
  1018
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1018
      1018
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1018
     1018
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1018 1018
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1018 1018
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (1018 1018
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (501 10 (:REWRITE RTL::R-EXACTP-6))
 (369 69
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (351 98 (:REWRITE DEFAULT-PLUS-2))
 (279 79 (:REWRITE DEFAULT-LESS-THAN-1))
 (247 79 (:REWRITE DEFAULT-LESS-THAN-2))
 (226 58 (:REWRITE SIMPLIFY-SUMS-<))
 (167 98 (:REWRITE DEFAULT-PLUS-1))
 (101 77
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (93 5 (:REWRITE ODD-EXPT-THM))
 (85 77 (:REWRITE |(< (- x) (- y))|))
 (81 3
     (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (80 2 (:LINEAR EXPT->=-1-ONE))
 (80 2 (:LINEAR EXPT-<=-1-TWO))
 (79 79 (:REWRITE THE-FLOOR-BELOW))
 (79 79 (:REWRITE THE-FLOOR-ABOVE))
 (78 3
     (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (78 2 (:LINEAR EXPT->-1-ONE))
 (78 2 (:LINEAR EXPT-<-1-TWO))
 (77 77
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (77 77
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (77 77
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (77 77 (:REWRITE INTEGERP-<-CONSTANT))
 (77 77 (:REWRITE CONSTANT-<-INTEGERP))
 (77 77
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (77 77
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (77 77
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (77 77
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (77 77 (:REWRITE |(< c (- x))|))
 (77 77
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (77 77
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (77 77
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (77 77 (:REWRITE |(< (/ x) (/ y))|))
 (77 77 (:REWRITE |(< (- x) c)|))
 (70 2 (:LINEAR EXPT-X->=-X))
 (70 2 (:LINEAR EXPT-X->-X))
 (65 27 (:REWRITE DEFAULT-TIMES-2))
 (39 23 (:REWRITE DEFAULT-MINUS))
 (36 12 (:REWRITE RTL::BVECP-EXACTP))
 (36 9 (:REWRITE RATIONALP-X))
 (34 34
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (30 22 (:REWRITE INTEGERP-MINUS-X))
 (27 27 (:REWRITE DEFAULT-TIMES-1))
 (24 24 (:TYPE-PRESCRIPTION RTL::BVECP))
 (22 22 (:REWRITE REDUCE-INTEGERP-+))
 (22 22
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (22 22 (:META META-INTEGERP-CORRECT))
 (20 10 (:REWRITE DEFAULT-EXPT-2))
 (19 19 (:REWRITE |(< (+ c/d x) y)|))
 (19 19 (:REWRITE |(< (+ (- c) x) y)|))
 (19 11 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (16 16 (:REWRITE |(< y (+ (- c) x))|))
 (16 16 (:REWRITE |(< x (+ c/d y))|))
 (15 15
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (15 15 (:REWRITE DEFAULT-DIVIDE))
 (10 10 (:REWRITE DEFAULT-EXPT-1))
 (10 10 (:REWRITE |(expt 1/c n)|))
 (10 10 (:REWRITE |(expt (- x) n)|))
 (9 9 (:REWRITE REDUCE-RATIONALP-+))
 (9 9 (:REWRITE REDUCE-RATIONALP-*))
 (9 9 (:REWRITE RATIONALP-MINUS-X))
 (9 9 (:REWRITE |(+ c (+ d x))|))
 (9 9 (:META META-RATIONALP-CORRECT))
 (7 7 (:REWRITE |(< (/ x) 0)|))
 (7 7 (:REWRITE |(< (* x y) 0)|))
 (5 5 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (5 5 (:REWRITE |(- (* c x))|))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (4 4 (:REWRITE |(< 0 (/ x))|))
 (4 4 (:REWRITE |(< 0 (* x y))|))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (3 3 (:REWRITE ZP-OPEN))
 (3 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (3 3
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (3 3
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (3 3
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (3 3
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (3 3 (:REWRITE FOLD-CONSTS-IN-+))
 (3 3
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (3 3 (:REWRITE |(equal c (/ x))|))
 (3 3 (:REWRITE |(equal c (- x))|))
 (3 3 (:REWRITE |(equal (/ x) c)|))
 (3 3 (:REWRITE |(equal (/ x) (/ y))|))
 (3 3 (:REWRITE |(equal (- x) c)|))
 (3 3 (:REWRITE |(equal (- x) (- y))|))
 (3 3
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (3 3
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-POS-UP-8
 (24
  24
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (24 24
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (24 24
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (24 24
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (24 24
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (24 24
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (16 16
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4A-EXPT))
 (16 16
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (16 16
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (16 16
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT)))
(RTL::R-POS-UP-9
 (218
  218
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (218 218
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (218
     218
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (218 218
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (218 218
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (107 17 (:REWRITE DEFAULT-TIMES-2))
 (86 86
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (86 86
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (86 86
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (72 17 (:REWRITE DEFAULT-TIMES-1))
 (53 1 (:REWRITE ODD-EXPT-THM))
 (49 5
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (49 5 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (42 7 (:REWRITE DEFAULT-LESS-THAN-2))
 (40 5 (:REWRITE SIMPLIFY-SUMS-<))
 (38 7 (:REWRITE |(< c (- x))|))
 (28 28
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (28 28
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (28 28
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (28 28
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (25 7 (:REWRITE DEFAULT-LESS-THAN-1))
 (11 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (9 9 (:REWRITE DEFAULT-EXPT-2))
 (9 9 (:REWRITE DEFAULT-EXPT-1))
 (9 9 (:REWRITE |(expt 1/c n)|))
 (9 9 (:REWRITE |(expt (- x) n)|))
 (8 2 (:REWRITE RATIONALP-X))
 (7 7 (:REWRITE THE-FLOOR-BELOW))
 (7 7 (:REWRITE THE-FLOOR-ABOVE))
 (7 7
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (7 7
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (7 7 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (7 7 (:REWRITE DEFAULT-MINUS))
 (7 7
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (7 7
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (7 7
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (7 7
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (7 7
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (7 7
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (7 7
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (7 7
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (7 7 (:REWRITE |(< (/ x) (/ y))|))
 (7 7 (:REWRITE |(< (- x) (- y))|))
 (6 6 (:REWRITE INTEGERP-<-CONSTANT))
 (6 6 (:REWRITE CONSTANT-<-INTEGERP))
 (6 6 (:REWRITE |(< (- x) c)|))
 (5 5 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (3 3 (:REWRITE REDUCE-INTEGERP-+))
 (3 3 (:REWRITE INTEGERP-MINUS-X))
 (3 3 (:META META-INTEGERP-CORRECT))
 (3 2 (:REWRITE DEFAULT-PLUS-1))
 (2 2 (:REWRITE REDUCE-RATIONALP-+))
 (2 2 (:REWRITE REDUCE-RATIONALP-*))
 (2 2 (:REWRITE RATIONALP-MINUS-X))
 (2 2 (:REWRITE DEFAULT-PLUS-2))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:REWRITE |(< 0 (* x y))|))
 (2 2 (:META META-RATIONALP-CORRECT))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (* x y) 0)|))
 (1 1 (:REWRITE |(- (- x))|)))
(RTL::R-POS-RNE-UP-10)
(RTL::R-POS-RNE-UP-11
 (1180
  1180
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1180
      1180
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1180
     1180
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1180 1180
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1180 1180
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (1180 1180
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (1101 1101
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (1101 1101
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (1101 1101
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (1101 1101
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (611 11 (:REWRITE RTL::R-EXACTP-6))
 (532 102 (:REWRITE DEFAULT-PLUS-2))
 (436 72
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (346 102 (:REWRITE DEFAULT-PLUS-1))
 (340 82 (:REWRITE DEFAULT-LESS-THAN-2))
 (259 61 (:REWRITE SIMPLIFY-SUMS-<))
 (256 82 (:REWRITE DEFAULT-LESS-THAN-1))
 (193 43 (:REWRITE DEFAULT-TIMES-1))
 (133 43 (:REWRITE DEFAULT-TIMES-2))
 (108 4
      (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (104 80
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (104 4
      (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (93 5 (:REWRITE ODD-EXPT-THM))
 (88 80 (:REWRITE |(< (- x) (- y))|))
 (82 82 (:REWRITE THE-FLOOR-BELOW))
 (82 82 (:REWRITE THE-FLOOR-ABOVE))
 (80 80
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (80 80
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (80 80
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (80 80 (:REWRITE INTEGERP-<-CONSTANT))
 (80 80 (:REWRITE CONSTANT-<-INTEGERP))
 (80 80
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (80 80
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (80 80
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (80 80
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (80 80 (:REWRITE |(< c (- x))|))
 (80 80
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (80 80
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (80 80
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (80 80 (:REWRITE |(< (/ x) (/ y))|))
 (80 80 (:REWRITE |(< (- x) c)|))
 (80 2 (:LINEAR EXPT->=-1-ONE))
 (80 2 (:LINEAR EXPT-<=-1-TWO))
 (78 29 (:REWRITE DEFAULT-MINUS))
 (78 2 (:LINEAR EXPT->-1-ONE))
 (78 2 (:LINEAR EXPT-<-1-TWO))
 (70 2 (:LINEAR EXPT-X->=-X))
 (70 2 (:LINEAR EXPT-X->-X))
 (49 11 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (38 38
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (36 12 (:REWRITE RTL::BVECP-EXACTP))
 (36 9 (:REWRITE RATIONALP-X))
 (31 31
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (30 22 (:REWRITE INTEGERP-MINUS-X))
 (24 24 (:TYPE-PRESCRIPTION RTL::BVECP))
 (22 22 (:REWRITE REDUCE-INTEGERP-+))
 (22 22 (:META META-INTEGERP-CORRECT))
 (20 10 (:REWRITE DEFAULT-EXPT-2))
 (19 19 (:REWRITE |(< (+ c/d x) y)|))
 (19 19 (:REWRITE |(< (+ (- c) x) y)|))
 (16 16 (:REWRITE |(< y (+ (- c) x))|))
 (16 16 (:REWRITE |(< x (+ c/d y))|))
 (15 15
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (15 15 (:REWRITE DEFAULT-DIVIDE))
 (10 10 (:REWRITE DEFAULT-EXPT-1))
 (10 10 (:REWRITE |(expt 1/c n)|))
 (10 10 (:REWRITE |(expt (- x) n)|))
 (9 9 (:REWRITE REDUCE-RATIONALP-+))
 (9 9 (:REWRITE REDUCE-RATIONALP-*))
 (9 9 (:REWRITE RATIONALP-MINUS-X))
 (9 9 (:REWRITE |(- (* c x))|))
 (9 9 (:REWRITE |(+ c (+ d x))|))
 (9 9 (:META META-RATIONALP-CORRECT))
 (7 7 (:REWRITE |(< (/ x) 0)|))
 (7 7 (:REWRITE |(< (* x y) 0)|))
 (5 5 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (4 4
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (4 4 (:REWRITE |(< 0 (/ x))|))
 (4 4 (:REWRITE |(< 0 (* x y))|))
 (4 4
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (3 3 (:REWRITE ZP-OPEN))
 (3 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (3 3
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (3 3
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (3 3
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (3 3
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (3 3 (:REWRITE FOLD-CONSTS-IN-+))
 (3 3
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (3 3 (:REWRITE |(equal c (/ x))|))
 (3 3 (:REWRITE |(equal c (- x))|))
 (3 3 (:REWRITE |(equal (/ x) c)|))
 (3 3 (:REWRITE |(equal (/ x) (/ y))|))
 (3 3 (:REWRITE |(equal (- x) c)|))
 (3 3 (:REWRITE |(equal (- x) (- y))|))
 (3 3 (:REWRITE |(* c (* d x))|))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-POS-RNE-UP-17
 (739 739
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (739 739
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (739 739
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (739 739
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (577
  577
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (577 577
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (577
     577
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (577 577
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (424 7 (:REWRITE RTL::R-EXACTP-6))
 (266 51
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (265 76 (:REWRITE DEFAULT-PLUS-2))
 (213 59 (:REWRITE DEFAULT-LESS-THAN-2))
 (155 59 (:REWRITE DEFAULT-LESS-THAN-1))
 (147 42 (:REWRITE SIMPLIFY-SUMS-<))
 (137 76 (:REWRITE DEFAULT-PLUS-1))
 (89 6 (:REWRITE ODD-EXPT-THM))
 (81 3
     (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (81 3 (:LINEAR EXPT->=-1-ONE))
 (79 3 (:LINEAR EXPT->-1-ONE))
 (78 3
     (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (73 23 (:REWRITE DEFAULT-TIMES-1))
 (71 3 (:LINEAR EXPT-X->=-X))
 (71 3 (:LINEAR EXPT-X->-X))
 (69 57
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (61 57 (:REWRITE |(< (- x) (- y))|))
 (59 59 (:REWRITE THE-FLOOR-BELOW))
 (59 59 (:REWRITE THE-FLOOR-ABOVE))
 (57 57
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (57 57
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (57 57
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
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
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (57 57
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (57 57
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (57 57 (:REWRITE |(< (/ x) (/ y))|))
 (57 57 (:REWRITE |(< (- x) c)|))
 (53 23 (:REWRITE DEFAULT-TIMES-2))
 (42 22 (:REWRITE DEFAULT-MINUS))
 (30 10 (:REWRITE RTL::BVECP-EXACTP))
 (28 28
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (20 20 (:TYPE-PRESCRIPTION RTL::BVECP))
 (20 5 (:REWRITE RATIONALP-X))
 (19 19
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (19 15 (:REWRITE INTEGERP-MINUS-X))
 (19 6 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (16 16 (:REWRITE |(< (+ c/d x) y)|))
 (16 16 (:REWRITE |(< (+ (- c) x) y)|))
 (16 10 (:REWRITE DEFAULT-EXPT-2))
 (15 15 (:REWRITE REDUCE-INTEGERP-+))
 (15 15 (:META META-INTEGERP-CORRECT))
 (13 13 (:REWRITE |(< y (+ (- c) x))|))
 (13 13 (:REWRITE |(< x (+ c/d y))|))
 (13 9 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (10 10
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (10 10 (:REWRITE DEFAULT-EXPT-1))
 (10 10 (:REWRITE DEFAULT-DIVIDE))
 (10 10 (:REWRITE |(expt 1/c n)|))
 (10 10 (:REWRITE |(expt (- x) n)|))
 (9 9 (:REWRITE |(+ c (+ d x))|))
 (8 8 (:REWRITE |(< (/ x) 0)|))
 (8 8 (:REWRITE |(< (* x y) 0)|))
 (7 7 (:REWRITE |(- (* c x))|))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (6 6
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (5 5
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (5 5
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (5 5 (:REWRITE REDUCE-RATIONALP-+))
 (5 5 (:REWRITE REDUCE-RATIONALP-*))
 (5 5 (:REWRITE RATIONALP-MINUS-X))
 (5 5 (:META META-RATIONALP-CORRECT))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (4 4 (:REWRITE |(< 0 (/ x))|))
 (4 4 (:REWRITE |(< 0 (* x y))|))
 (4 1 (:REWRITE |(integerp (- x))|))
 (3 3 (:REWRITE FOLD-CONSTS-IN-+))
 (3 3
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (3 3
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<))
 (3 3 (:LINEAR EXPT->=-1-TWO))
 (3 3 (:LINEAR EXPT->-1-TWO))
 (3 3 (:LINEAR EXPT-<=-1-ONE))
 (3 3 (:LINEAR EXPT-<-1-ONE))
 (3 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (3 2
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (3 2
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
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
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE |(* c (* d x))|)))
(RTL::R-POS-RNE-UP-20
 (26406
  26406
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (26406
      26406
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (26406
     26406
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (26406 26406
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (12288 12288
        (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (12288 12288
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (12288 12288
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (12288 12288
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (7270 1574 (:REWRITE DEFAULT-PLUS-2))
 (5238 1574 (:REWRITE DEFAULT-PLUS-1))
 (5042 757
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (4301 801 (:REWRITE DEFAULT-TIMES-1))
 (4099 876 (:REWRITE DEFAULT-LESS-THAN-2))
 (2901 801 (:REWRITE DEFAULT-TIMES-2))
 (2841 589 (:REWRITE SIMPLIFY-SUMS-<))
 (2578 876 (:REWRITE DEFAULT-LESS-THAN-1))
 (1316 490 (:REWRITE DEFAULT-MINUS))
 (1108 844
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (1099 97 (:REWRITE ODD-EXPT-THM))
 (1072 844 (:REWRITE |(< (- x) (- y))|))
 (876 876 (:REWRITE THE-FLOOR-BELOW))
 (876 876 (:REWRITE THE-FLOOR-ABOVE))
 (864 844 (:REWRITE |(< (/ x) (/ y))|))
 (844 844
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (844 844
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (844 844
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (844 844 (:REWRITE INTEGERP-<-CONSTANT))
 (844 844 (:REWRITE CONSTANT-<-INTEGERP))
 (844 844
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (844 844
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (844 844
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (844 844
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (844 844 (:REWRITE |(< c (- x))|))
 (844 844
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (844 844
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (844 844
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (844 844 (:REWRITE |(< (- x) c)|))
 (599 599
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (594 22
      (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (572 22
      (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (566 168 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (539 97
      (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (532 133 (:REWRITE RATIONALP-X))
 (521 521
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (492 164 (:REWRITE RTL::BVECP-EXACTP))
 (346 318 (:REWRITE INTEGERP-MINUS-X))
 (328 328 (:TYPE-PRESCRIPTION RTL::BVECP))
 (326 196 (:REWRITE DEFAULT-EXPT-2))
 (318 318 (:REWRITE REDUCE-INTEGERP-+))
 (318 318 (:META META-INTEGERP-CORRECT))
 (241 241 (:REWRITE |(< (+ c/d x) y)|))
 (241 241 (:REWRITE |(< (+ (- c) x) y)|))
 (196 196 (:REWRITE DEFAULT-EXPT-1))
 (196 196 (:REWRITE |(expt 1/c n)|))
 (196 196 (:REWRITE |(expt (- x) n)|))
 (193 193 (:REWRITE |(- (* c x))|))
 (136 34 (:REWRITE |(integerp (- x))|))
 (133 133 (:REWRITE REDUCE-RATIONALP-+))
 (133 133 (:REWRITE REDUCE-RATIONALP-*))
 (133 133 (:REWRITE RATIONALP-MINUS-X))
 (133 133 (:META META-RATIONALP-CORRECT))
 (131 131 (:REWRITE |(< y (+ (- c) x))|))
 (131 131 (:REWRITE |(< x (+ c/d y))|))
 (125 125
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (125 125 (:REWRITE DEFAULT-DIVIDE))
 (86 86 (:REWRITE |(+ c (+ d x))|))
 (81 3 (:LINEAR EXPT->=-1-ONE))
 (79 3 (:LINEAR EXPT->-1-ONE))
 (71 3 (:LINEAR EXPT-X->=-X))
 (71 3 (:LINEAR EXPT-X->-X))
 (70 70 (:REWRITE |(* c (* d x))|))
 (69 69 (:REWRITE |(< (/ x) 0)|))
 (69 69 (:REWRITE |(< (* x y) 0)|))
 (42 42 (:REWRITE FOLD-CONSTS-IN-+))
 (39 39 (:REWRITE |(< 0 (/ x))|))
 (39 39 (:REWRITE |(< 0 (* x y))|))
 (36 36
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (36 36
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (33 33 (:REWRITE ZP-OPEN))
 (33 33 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (33 33
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (33 33
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (33 33
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (33 33
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (33 33
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (33 33 (:REWRITE |(equal c (/ x))|))
 (33 33 (:REWRITE |(equal c (- x))|))
 (33 33 (:REWRITE |(equal (/ x) c)|))
 (33 33 (:REWRITE |(equal (/ x) (/ y))|))
 (33 33 (:REWRITE |(equal (- x) c)|))
 (33 33 (:REWRITE |(equal (- x) (- y))|))
 (22 22
     (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (22 22
     (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (11 11
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (11 11
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (6 6
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<))
 (3 3 (:LINEAR EXPT->=-1-TWO))
 (3 3 (:LINEAR EXPT->-1-TWO))
 (3 3 (:LINEAR EXPT-<=-1-ONE))
 (3 3 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-POS-UP-13
 (216
  216
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (216 216
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (216
     216
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (216 216
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (109 24 (:REWRITE DEFAULT-PLUS-1))
 (105 24 (:REWRITE DEFAULT-PLUS-2))
 (68 14
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (60 15 (:REWRITE DEFAULT-LESS-THAN-2))
 (33 15 (:REWRITE DEFAULT-LESS-THAN-1))
 (32 14 (:REWRITE |(< (- x) (- y))|))
 (26 8 (:REWRITE DEFAULT-MINUS))
 (22 4 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (20 14
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (19 10 (:REWRITE SIMPLIFY-SUMS-<))
 (17 2 (:REWRITE ODD-EXPT-THM))
 (15 15 (:REWRITE THE-FLOOR-BELOW))
 (15 15 (:REWRITE THE-FLOOR-ABOVE))
 (15 2 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (14 14 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (14 14
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (14 14
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (14 14
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (14 14
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
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
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (14 14
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (14 14
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (14 14 (:REWRITE |(< (/ x) (/ y))|))
 (14 14 (:REWRITE |(< (- x) c)|))
 (12 3 (:REWRITE RATIONALP-X))
 (10 10
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (10 10
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (7 7 (:REWRITE REDUCE-INTEGERP-+))
 (7 7
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (7 7 (:REWRITE INTEGERP-MINUS-X))
 (7 7 (:META META-INTEGERP-CORRECT))
 (6 6 (:REWRITE DEFAULT-EXPT-2))
 (6 6 (:REWRITE DEFAULT-EXPT-1))
 (6 6 (:REWRITE |(expt 1/c n)|))
 (6 6 (:REWRITE |(expt (- x) n)|))
 (6 2 (:REWRITE RTL::BVECP-EXACTP))
 (5 5 (:REWRITE |(< (+ c/d x) y)|))
 (5 5 (:REWRITE |(< (+ (- c) x) y)|))
 (4 4 (:TYPE-PRESCRIPTION RTL::BVECP))
 (4 1 (:REWRITE |(integerp (- x))|))
 (3 3 (:REWRITE REDUCE-RATIONALP-+))
 (3 3 (:REWRITE REDUCE-RATIONALP-*))
 (3 3 (:REWRITE RATIONALP-MINUS-X))
 (3 3
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (3 3 (:REWRITE DEFAULT-TIMES-2))
 (3 3 (:REWRITE DEFAULT-TIMES-1))
 (3 3 (:REWRITE |(< y (+ (- c) x))|))
 (3 3 (:REWRITE |(< x (+ c/d y))|))
 (3 3 (:META META-RATIONALP-CORRECT))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (* x y) 0)|))
 (1 1 (:REWRITE |(- (* c x))|))
 (1 1 (:LINEAR EXPT-X->=-X))
 (1 1 (:LINEAR EXPT-X->-X))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<))
 (1 1 (:LINEAR EXPT->=-1-TWO))
 (1 1 (:LINEAR EXPT->=-1-ONE))
 (1 1 (:LINEAR EXPT->-1-TWO))
 (1 1 (:LINEAR EXPT->-1-ONE))
 (1 1 (:LINEAR EXPT-<=-1-ONE))
 (1 1 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-POS-UP-15
 (7379 7379
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (7379 7379
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (7379 7379
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (5037 685
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
 (5037 685
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
 (3213 633
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3D))
 (3213 633
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1D))
 (3009 685
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
 (2809 633
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2D))
 (2707
  2707
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (2707
      2707
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (2707
     2707
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (2707 2707
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (965 173 (:REWRITE DEFAULT-PLUS-2))
 (961 18
      (:REWRITE |(< (/ x) y) with (< 0 x)|))
 (783 214 (:REWRITE DEFAULT-LESS-THAN-2))
 (640 640
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (640 640
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (640 640
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (640 640
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (633 633
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4H))
 (633 633
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3H))
 (633 633
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2H))
 (633 633
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1H))
 (594 151
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (413 89 (:REWRITE DEFAULT-MINUS))
 (401 81 (:REWRITE DEFAULT-TIMES-2))
 (387 173 (:REWRITE DEFAULT-PLUS-1))
 (313 214 (:REWRITE DEFAULT-LESS-THAN-1))
 (235 135 (:REWRITE SIMPLIFY-SUMS-<))
 (220 166
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (214 214 (:REWRITE THE-FLOOR-BELOW))
 (214 214 (:REWRITE THE-FLOOR-ABOVE))
 (202 166 (:REWRITE |(< (/ x) (/ y))|))
 (202 166 (:REWRITE |(< (- x) (- y))|))
 (199 199
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (199 199
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (169 81 (:REWRITE DEFAULT-TIMES-1))
 (169 18
      (:REWRITE |(<= x (/ y)) with (< y 0)|))
 (169 18
      (:REWRITE |(< (/ x) y) with (< x 0)|))
 (168 4 (:REWRITE |(* (* x y) z)|))
 (166 166
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (166 166
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (166 166
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (166 166
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (166 166
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (166 166
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (166 166
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (155 155 (:REWRITE INTEGERP-<-CONSTANT))
 (155 155 (:REWRITE CONSTANT-<-INTEGERP))
 (155 155 (:REWRITE |(< (- x) c)|))
 (120 4 (:REWRITE |(* y (* x z))|))
 (96 24 (:REWRITE RATIONALP-X))
 (86 10 (:REWRITE ODD-EXPT-THM))
 (79 43 (:REWRITE DEFAULT-DIVIDE))
 (76 10
     (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (64 64
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (62 62
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (54 18 (:REWRITE RTL::BVECP-EXACTP))
 (53 53 (:REWRITE |(< 0 (* x y))|))
 (52 52 (:REWRITE REDUCE-INTEGERP-+))
 (52 52 (:REWRITE INTEGERP-MINUS-X))
 (52 52 (:META META-INTEGERP-CORRECT))
 (52 16 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (52 4 (:REWRITE |(* y x)|))
 (43 43
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (42 42 (:REWRITE DEFAULT-EXPT-2))
 (42 42 (:REWRITE DEFAULT-EXPT-1))
 (42 42 (:REWRITE |(expt 1/c n)|))
 (42 42 (:REWRITE |(expt (- x) n)|))
 (36 36 (:TYPE-PRESCRIPTION RTL::BVECP))
 (34 34 (:REWRITE |(< (* x y) 0)|))
 (31 31
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (31 31
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (31 31 (:REWRITE |(< 0 (/ x))|))
 (24 24 (:REWRITE REDUCE-RATIONALP-+))
 (24 24 (:REWRITE REDUCE-RATIONALP-*))
 (24 24 (:REWRITE RATIONALP-MINUS-X))
 (24 24 (:META META-RATIONALP-CORRECT))
 (24 6 (:REWRITE |(integerp (- x))|))
 (23 23 (:REWRITE |(< (/ x) 0)|))
 (21 21 (:REWRITE |(< x (+ c/d y))|))
 (20 20 (:REWRITE |(< (+ c/d x) y)|))
 (20 20 (:REWRITE |(< (+ (- c) x) y)|))
 (19 19
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (19 19
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (17 17
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (17 17
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (11 11
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (11 11 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (11 11
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (11 11
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (11 11
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (11 11
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (11 11
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (11 11 (:REWRITE |(equal c (/ x))|))
 (11 11 (:REWRITE |(equal c (- x))|))
 (11 11 (:REWRITE |(equal (/ x) c)|))
 (11 11 (:REWRITE |(equal (/ x) (/ y))|))
 (11 11 (:REWRITE |(equal (- x) c)|))
 (11 11 (:REWRITE |(equal (- x) (- y))|))
 (11 11
     (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (11 11
     (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (11 11
     (:REWRITE |(< x (/ y)) with (< y 0)|))
 (10 10 (:REWRITE |(< y (+ (- c) x))|))
 (8 8 (:REWRITE ZP-OPEN))
 (8 8 (:REWRITE |(* c (* d x))|))
 (6 6 (:REWRITE |(- (* c x))|))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (1 1 (:LINEAR EXPT-X->=-X))
 (1 1 (:LINEAR EXPT-X->-X))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<))
 (1 1 (:LINEAR EXPT->=-1-TWO))
 (1 1 (:LINEAR EXPT->=-1-ONE))
 (1 1 (:LINEAR EXPT->-1-TWO))
 (1 1 (:LINEAR EXPT->-1-ONE))
 (1 1 (:LINEAR EXPT-<=-1-ONE))
 (1 1 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-POS-UP-16
 (856
  856
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (856 856
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (856
     856
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (856 856
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (489 489
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (489 489
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (489 489
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (249 71 (:REWRITE DEFAULT-LESS-THAN-2))
 (216 65
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (197 71 (:REWRITE DEFAULT-PLUS-2))
 (172 4
      (:REWRITE |(<= x (/ y)) with (< y 0)|))
 (172 4
      (:REWRITE |(<= x (/ y)) with (< 0 y)|))
 (172 4 (:REWRITE |(< (/ x) y) with (< x 0)|))
 (172 4 (:REWRITE |(< (/ x) y) with (< 0 x)|))
 (153 71 (:REWRITE DEFAULT-PLUS-1))
 (135 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
 (135 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
 (134 55 (:REWRITE SIMPLIFY-SUMS-<))
 (105 69 (:REWRITE |(< (/ x) (/ y))|))
 (99 69
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (80 71 (:REWRITE DEFAULT-LESS-THAN-1))
 (78 69 (:REWRITE |(< c (- x))|))
 (75 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-3D))
 (75 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
 (75 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-2D))
 (75 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-1D))
 (72 27 (:REWRITE DEFAULT-MINUS))
 (71 71 (:REWRITE THE-FLOOR-BELOW))
 (71 71 (:REWRITE THE-FLOOR-ABOVE))
 (69 69
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (69 69
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (69 69
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (69 69 (:REWRITE INTEGERP-<-CONSTANT))
 (69 69 (:REWRITE CONSTANT-<-INTEGERP))
 (69 69
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (69 69
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (69 69
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (69 69
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (69 69
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (69 69
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (69 69
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (69 69 (:REWRITE |(< (- x) c)|))
 (69 69 (:REWRITE |(< (- x) (- y))|))
 (60 7 (:REWRITE ODD-EXPT-THM))
 (57 13 (:REWRITE DEFAULT-TIMES-2))
 (53 7 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (48 12 (:REWRITE RATIONALP-X))
 (45 9 (:REWRITE DEFAULT-DIVIDE))
 (30 10 (:REWRITE RTL::BVECP-EXACTP))
 (29 29 (:REWRITE REDUCE-INTEGERP-+))
 (29 29 (:REWRITE INTEGERP-MINUS-X))
 (29 29 (:META META-INTEGERP-CORRECT))
 (20 20 (:TYPE-PRESCRIPTION RTL::BVECP))
 (19 10 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (18 18
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (17 17 (:REWRITE DEFAULT-EXPT-2))
 (17 17 (:REWRITE DEFAULT-EXPT-1))
 (17 17 (:REWRITE |(expt 1/c n)|))
 (17 17 (:REWRITE |(expt (- x) n)|))
 (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (16 4 (:REWRITE |(integerp (- x))|))
 (15 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-4H))
 (15 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-3H))
 (15 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-2H))
 (15 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-1H))
 (13 13 (:REWRITE DEFAULT-TIMES-1))
 (13 13 (:REWRITE |(< (/ x) 0)|))
 (13 13 (:REWRITE |(< (* x y) 0)|))
 (12 12 (:REWRITE REDUCE-RATIONALP-+))
 (12 12 (:REWRITE REDUCE-RATIONALP-*))
 (12 12 (:REWRITE RATIONALP-MINUS-X))
 (12 12
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (12 12 (:REWRITE |(< (+ c/d x) y)|))
 (12 12 (:REWRITE |(< (+ (- c) x) y)|))
 (12 12 (:META META-RATIONALP-CORRECT))
 (11 11
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (11 11
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (10 10 (:REWRITE |(< 0 (/ x))|))
 (10 10 (:REWRITE |(< 0 (* x y))|))
 (9 9
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (9 9
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (9 9
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (5 5 (:REWRITE |(< y (+ (- c) x))|))
 (5 5 (:REWRITE |(< x (+ c/d y))|))
 (5 5 (:REWRITE |(- (* c x))|))
 (4 4 (:REWRITE ZP-OPEN))
 (4 4 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (4 4 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (1 1
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (1 1 (:LINEAR EXPT-X->=-X))
 (1 1 (:LINEAR EXPT-X->-X))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1 1 (:LINEAR EXPT->=-1-TWO))
 (1 1 (:LINEAR EXPT->=-1-ONE))
 (1 1 (:LINEAR EXPT->-1-TWO))
 (1 1 (:LINEAR EXPT->-1-ONE))
 (1 1 (:LINEAR EXPT-<=-1-ONE))
 (1 1 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-POS-UP-21
 (668 74
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (668 74
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (505
  505
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (505 505
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (505
     505
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (505 505
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (144 23 (:REWRITE DEFAULT-TIMES-2))
 (124 25 (:REWRITE DEFAULT-PLUS-2))
 (116 23 (:REWRITE DEFAULT-TIMES-1))
 (111 25 (:REWRITE DEFAULT-PLUS-1))
 (74 74
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4A-EXPT))
 (74 74
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (73 15 (:REWRITE DEFAULT-LESS-THAN-2))
 (53 8 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (51 15 (:REWRITE DEFAULT-LESS-THAN-1))
 (42 15 (:REWRITE |(< (- x) (- y))|))
 (36 9 (:REWRITE DEFAULT-MINUS))
 (30 3
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (30 3
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (27 15
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (15 15 (:REWRITE THE-FLOOR-BELOW))
 (15 15 (:REWRITE THE-FLOOR-ABOVE))
 (15 15
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (15 15
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (15 15
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (15 15 (:REWRITE INTEGERP-<-CONSTANT))
 (15 15 (:REWRITE CONSTANT-<-INTEGERP))
 (15 15
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (15 15
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (15 15
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (15 15
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (15 15 (:REWRITE |(< c (- x))|))
 (15 15
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (15 15
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (15 15
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (15 15 (:REWRITE |(< (/ x) (/ y))|))
 (15 15 (:REWRITE |(< (- x) c)|))
 (12 4 (:REWRITE RTL::BVECP-EXACTP))
 (9 9
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (8 8 (:TYPE-PRESCRIPTION RTL::BVECP))
 (8 8 (:REWRITE SIMPLIFY-SUMS-<))
 (8 2 (:REWRITE RATIONALP-X))
 (6 6 (:REWRITE REDUCE-INTEGERP-+))
 (6 6 (:REWRITE INTEGERP-MINUS-X))
 (6 6 (:META META-INTEGERP-CORRECT))
 (5 5 (:REWRITE DEFAULT-EXPT-2))
 (5 5 (:REWRITE DEFAULT-EXPT-1))
 (5 5 (:REWRITE |(expt 1/c n)|))
 (5 5 (:REWRITE |(expt (- x) n)|))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (3 3 (:REWRITE |(< (+ c/d x) y)|))
 (3 3 (:REWRITE |(< (+ (- c) x) y)|))
 (2 2 (:REWRITE REDUCE-RATIONALP-+))
 (2 2 (:REWRITE REDUCE-RATIONALP-*))
 (2 2 (:REWRITE RATIONALP-MINUS-X))
 (2 2 (:REWRITE |(< y (+ (- c) x))|))
 (2 2 (:REWRITE |(< x (+ c/d y))|))
 (2 2 (:REWRITE |(* (- x) y)|))
 (2 2 (:META META-RATIONALP-CORRECT))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (1 1 (:REWRITE ODD-EXPT-THM))
 (1 1 (:REWRITE |(< 0 (/ x))|))
 (1 1 (:REWRITE |(< 0 (* x y))|)))
(RTL::R-POS-UP-22
 (1143 74 (:REWRITE DEFAULT-PLUS-2))
 (654
  654
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (654 654
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (654
     654
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (654 654
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (550 55
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (550 55
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (518 74 (:REWRITE DEFAULT-PLUS-1))
 (407 62 (:REWRITE DEFAULT-TIMES-2))
 (312 62 (:REWRITE DEFAULT-TIMES-1))
 (180 18
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (180 18
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (176 20 (:REWRITE DEFAULT-LESS-THAN-2))
 (154 20 (:REWRITE DEFAULT-LESS-THAN-1))
 (131 19 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (109 20 (:REWRITE |(< (- x) (- y))|))
 (83 16 (:REWRITE DEFAULT-MINUS))
 (55 55
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (55 55
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (32 20
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (25 25
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (20 20 (:REWRITE THE-FLOOR-BELOW))
 (20 20 (:REWRITE THE-FLOOR-ABOVE))
 (20 20
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (20 20
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (20 20
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (20 20 (:REWRITE INTEGERP-<-CONSTANT))
 (20 20 (:REWRITE CONSTANT-<-INTEGERP))
 (20 20
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (20 20
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (20 20
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (20 20
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (20 20 (:REWRITE |(< c (- x))|))
 (20 20
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (20 20
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (20 20
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (20 20 (:REWRITE |(< (/ x) (/ y))|))
 (20 20 (:REWRITE |(< (- x) c)|))
 (18 18
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4A-EXPT))
 (18 18
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (12 4 (:REWRITE RTL::BVECP-EXACTP))
 (8 8 (:TYPE-PRESCRIPTION RTL::BVECP))
 (8 8 (:REWRITE DEFAULT-EXPT-2))
 (8 8 (:REWRITE DEFAULT-EXPT-1))
 (8 8 (:REWRITE |(expt 1/c n)|))
 (8 8 (:REWRITE |(expt (- x) n)|))
 (8 8 (:REWRITE |(+ c (+ d x))|))
 (8 2 (:REWRITE RATIONALP-X))
 (6 6 (:REWRITE REDUCE-INTEGERP-+))
 (6 6 (:REWRITE INTEGERP-MINUS-X))
 (6 6 (:META META-INTEGERP-CORRECT))
 (5 5 (:REWRITE FOLD-CONSTS-IN-+))
 (5 5 (:REWRITE |(< y (+ (- c) x))|))
 (5 5 (:REWRITE |(< x (+ c/d y))|))
 (5 5 (:REWRITE |(< (+ c/d x) y)|))
 (5 5 (:REWRITE |(< (+ (- c) x) y)|))
 (4 4 (:REWRITE |(* (- x) y)|))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2 (:REWRITE REDUCE-RATIONALP-+))
 (2 2 (:REWRITE REDUCE-RATIONALP-*))
 (2 2 (:REWRITE RATIONALP-MINUS-X))
 (2 2 (:REWRITE ODD-EXPT-THM))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:REWRITE |(< 0 (* x y))|))
 (2 2 (:META META-RATIONALP-CORRECT))
 (1 1 (:REWRITE ZP-OPEN)))
(RTL::R-POS-UP-23
 (2663 155 (:REWRITE DEFAULT-PLUS-2))
 (1575
  1575
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1575
      1575
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1575
     1575
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1575 1575
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1147 147 (:REWRITE DEFAULT-TIMES-2))
 (1142 155 (:REWRITE DEFAULT-PLUS-1))
 (1130 113
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (1130 113
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (840 147 (:REWRITE DEFAULT-TIMES-1))
 (353 353
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (353 353
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (353 353
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (296 50 (:REWRITE DEFAULT-MINUS))
 (295 33 (:REWRITE DEFAULT-LESS-THAN-2))
 (292 33 (:REWRITE DEFAULT-LESS-THAN-1))
 (197 27 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (175 33 (:REWRITE |(< (- x) (- y))|))
 (129 129
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
 (129 129
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
 (129 129
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
 (113 113
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (113 113
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (70 70
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (60 6 (:REWRITE DEFAULT-DIVIDE))
 (51 33
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (42 33 (:REWRITE |(< c (- x))|))
 (33 33 (:REWRITE THE-FLOOR-BELOW))
 (33 33 (:REWRITE THE-FLOOR-ABOVE))
 (33 33
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (33 33
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (33 33
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (33 33 (:REWRITE INTEGERP-<-CONSTANT))
 (33 33 (:REWRITE CONSTANT-<-INTEGERP))
 (33 33
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (33 33
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (33 33
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (33 33
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (33 33
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (33 33
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (33 33
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (33 33 (:REWRITE |(< (/ x) (/ y))|))
 (33 33 (:REWRITE |(< (- x) c)|))
 (26 26 (:REWRITE DEFAULT-EXPT-2))
 (26 26 (:REWRITE DEFAULT-EXPT-1))
 (26 26 (:REWRITE |(expt 1/c n)|))
 (26 26 (:REWRITE |(expt (- x) n)|))
 (18 18 (:REWRITE |(+ c (+ d x))|))
 (18 6 (:REWRITE RTL::BVECP-EXACTP))
 (16 4 (:REWRITE RATIONALP-X))
 (12 12 (:TYPE-PRESCRIPTION RTL::BVECP))
 (12 12 (:REWRITE FOLD-CONSTS-IN-+))
 (10 10 (:REWRITE REDUCE-INTEGERP-+))
 (10 10 (:REWRITE INTEGERP-MINUS-X))
 (10 10 (:META META-INTEGERP-CORRECT))
 (9 9 (:REWRITE |(< y (+ (- c) x))|))
 (9 9 (:REWRITE |(< x (+ c/d y))|))
 (9 9 (:REWRITE |(< (+ c/d x) y)|))
 (9 9 (:REWRITE |(< (+ (- c) x) y)|))
 (6 6
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (5 5 (:REWRITE |(* (- x) y)|))
 (4 4 (:REWRITE REDUCE-RATIONALP-+))
 (4 4 (:REWRITE REDUCE-RATIONALP-*))
 (4 4 (:REWRITE RATIONALP-MINUS-X))
 (4 4 (:META META-RATIONALP-CORRECT))
 (3 3 (:REWRITE |(< 0 (/ x))|))
 (3 3 (:REWRITE |(< 0 (* x y))|))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2 (:REWRITE ODD-EXPT-THM))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<)))
(RTL::R-POS-UP-24
 (153
  153
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (153 153
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (153
     153
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (153 153
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (153 153
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (141 16 (:REWRITE DEFAULT-TIMES-2))
 (115 16 (:REWRITE DEFAULT-TIMES-1))
 (74 7 (:REWRITE DEFAULT-PLUS-2))
 (63 63 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (63 63 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (63 63 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (34 7 (:REWRITE DEFAULT-MINUS))
 (20 2 (:REWRITE DEFAULT-DIVIDE))
 (15 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
 (15 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
 (15 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
 (15 6 (:REWRITE DEFAULT-LESS-THAN-1))
 (12 6
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (11 2 (:REWRITE SIMPLIFY-SUMS-<))
 (11 2
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (11 2 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (7 7
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (7 7 (:REWRITE NORMALIZE-ADDENDS))
 (7 7 (:REWRITE DEFAULT-PLUS-1))
 (6 6 (:REWRITE THE-FLOOR-BELOW))
 (6 6 (:REWRITE THE-FLOOR-ABOVE))
 (6 6
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (6 6
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (6 6 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
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
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (6 6
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (6 6
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (6 6 (:REWRITE |(< (/ x) (/ y))|))
 (6 6 (:REWRITE |(< (- x) c)|))
 (6 6 (:REWRITE |(< (- x) (- y))|))
 (6 2 (:REWRITE RTL::BVECP-EXACTP))
 (5 5
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (4 4 (:TYPE-PRESCRIPTION RTL::BVECP))
 (4 4 (:REWRITE DEFAULT-EXPT-2))
 (4 4 (:REWRITE DEFAULT-EXPT-1))
 (4 4 (:REWRITE |(expt 1/c n)|))
 (4 4 (:REWRITE |(expt (- x) n)|))
 (2 2 (:REWRITE REDUCE-INTEGERP-+))
 (2 2
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (2 2 (:REWRITE INTEGERP-MINUS-X))
 (2 2 (:META META-INTEGERP-CORRECT))
 (1 1 (:REWRITE |(< (+ c/d x) y)|))
 (1 1 (:REWRITE |(< (+ (- c) x) y)|)))
(RTL::R-POS-RNE-UP-25
 (5602
  5602
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (5602
      5602
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (5602
     5602
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (5602 5602
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (3547 3547
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (3547 3547
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (3547 3547
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (1281 318 (:REWRITE DEFAULT-PLUS-2))
 (1165 201
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (1039 260 (:REWRITE DEFAULT-LESS-THAN-2))
 (864 17 (:REWRITE RTL::R-EXACTP-6))
 (826 318 (:REWRITE DEFAULT-PLUS-1))
 (742 164 (:REWRITE SIMPLIFY-SUMS-<))
 (627 260 (:REWRITE DEFAULT-LESS-THAN-1))
 (360 252
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (338 88 (:REWRITE DEFAULT-TIMES-1))
 (310 88 (:REWRITE DEFAULT-TIMES-2))
 (284 24 (:REWRITE ODD-EXPT-THM))
 (274 252 (:REWRITE |(< (- x) (- y))|))
 (262 252 (:REWRITE |(< (/ x) (/ y))|))
 (260 260 (:REWRITE THE-FLOOR-BELOW))
 (260 260 (:REWRITE THE-FLOOR-ABOVE))
 (254 103 (:REWRITE DEFAULT-MINUS))
 (252 252
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (252 252
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (252 252
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (252 252 (:REWRITE INTEGERP-<-CONSTANT))
 (252 252 (:REWRITE CONSTANT-<-INTEGERP))
 (252 252
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (252 252
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (252 252
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (252 252
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (252 252 (:REWRITE |(< c (- x))|))
 (252 252
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (252 252
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (252 252
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (252 252 (:REWRITE |(< (- x) c)|))
 (243 5
      (:REWRITE |(<= x (/ y)) with (< y 0)|))
 (243 5
      (:REWRITE |(<= x (/ y)) with (< 0 y)|))
 (243 5 (:REWRITE |(< (/ x) y) with (< x 0)|))
 (243 5 (:REWRITE |(< (/ x) y) with (< 0 x)|))
 (135 5
      (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (130 5
      (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (129 43 (:REWRITE RTL::BVECP-EXACTP))
 (128 24
      (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (112 112
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (109 37 (:REWRITE DEFAULT-DIVIDE))
 (108 27 (:REWRITE RATIONALP-X))
 (99 87 (:REWRITE INTEGERP-MINUS-X))
 (99 37 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (87 87 (:REWRITE REDUCE-INTEGERP-+))
 (87 87 (:META META-INTEGERP-CORRECT))
 (86 86 (:TYPE-PRESCRIPTION RTL::BVECP))
 (81 3 (:LINEAR EXPT->=-1-ONE))
 (79 3 (:LINEAR EXPT->-1-ONE))
 (71 3 (:LINEAR EXPT-X->=-X))
 (71 3 (:LINEAR EXPT-X->-X))
 (68 68
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (64 47 (:REWRITE DEFAULT-EXPT-2))
 (63 63 (:REWRITE |(< (+ c/d x) y)|))
 (63 63 (:REWRITE |(< (+ (- c) x) y)|))
 (47 47 (:REWRITE DEFAULT-EXPT-1))
 (47 47 (:REWRITE |(expt 1/c n)|))
 (47 47 (:REWRITE |(expt (- x) n)|))
 (37 37
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (32 8 (:REWRITE |(integerp (- x))|))
 (30 30 (:REWRITE |(< y (+ (- c) x))|))
 (30 30 (:REWRITE |(< x (+ c/d y))|))
 (30 30 (:REWRITE |(< (/ x) 0)|))
 (30 30 (:REWRITE |(< (* x y) 0)|))
 (27 27 (:REWRITE REDUCE-RATIONALP-+))
 (27 27 (:REWRITE REDUCE-RATIONALP-*))
 (27 27 (:REWRITE RATIONALP-MINUS-X))
 (27 27 (:META META-RATIONALP-CORRECT))
 (24 24 (:REWRITE |(- (* c x))|))
 (16 16 (:REWRITE |(+ c (+ d x))|))
 (14 14
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (14 14
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (14 14
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (14 14
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (14 14 (:REWRITE |(< 0 (/ x))|))
 (14 14 (:REWRITE |(< 0 (* x y))|))
 (11 11
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (11 11
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (7 7 (:REWRITE ZP-OPEN))
 (7 7 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (7 7
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (7 7
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (7 7
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (7 7
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (7 7
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (7 7 (:REWRITE |(equal c (/ x))|))
 (7 7 (:REWRITE |(equal c (- x))|))
 (7 7 (:REWRITE |(equal (/ x) c)|))
 (7 7 (:REWRITE |(equal (/ x) (/ y))|))
 (7 7 (:REWRITE |(equal (- x) c)|))
 (7 7 (:REWRITE |(equal (- x) (- y))|))
 (6 6 (:REWRITE FOLD-CONSTS-IN-+))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (6 6
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (5 5
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (5 5
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (5 5 (:REWRITE |(* c (* d x))|))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<))
 (3 3 (:LINEAR EXPT->=-1-TWO))
 (3 3 (:LINEAR EXPT->-1-TWO))
 (3 3 (:LINEAR EXPT-<=-1-ONE))
 (3 3 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-POS-RNE-UP-30)
(RTL::R-POS-RNE-UP-31
 (3899
  3899
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (3899
      3899
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (3899
     3899
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (3899 3899
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (2759 2759
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (2759 2759
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (2759 2759
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (2759 2759
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (1990 544 (:REWRITE DEFAULT-PLUS-2))
 (1742 294
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (1455 258
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (1424 30 (:REWRITE RTL::R-EXACTP-6))
 (1407 544 (:REWRITE DEFAULT-PLUS-1))
 (1299 305 (:REWRITE DEFAULT-LESS-THAN-2))
 (915 255 (:REWRITE DEFAULT-TIMES-1))
 (875 255 (:REWRITE DEFAULT-TIMES-2))
 (840 192 (:REWRITE SIMPLIFY-SUMS-<))
 (803 305 (:REWRITE DEFAULT-LESS-THAN-1))
 (559 9 (:LINEAR EXPT->=-1-ONE))
 (549 9 (:LINEAR EXPT->-1-ONE))
 (503 9 (:LINEAR EXPT-X->=-X))
 (503 9 (:LINEAR EXPT-X->-X))
 (372 272 (:REWRITE |(< c (- x))|))
 (326 24 (:REWRITE ODD-EXPT-THM))
 (322 274
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (308 274
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (305 305 (:REWRITE THE-FLOOR-BELOW))
 (305 305 (:REWRITE THE-FLOOR-ABOVE))
 (294 294
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (294 294
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (294 274 (:REWRITE |(< (- x) (- y))|))
 (275 274 (:REWRITE |(< (/ x) (/ y))|))
 (274 274
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (274 274
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (274 274
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (274 274
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (274 274
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (274 274
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (272 272 (:REWRITE INTEGERP-<-CONSTANT))
 (272 272 (:REWRITE CONSTANT-<-INTEGERP))
 (272 272 (:REWRITE |(< (- x) c)|))
 (270 108 (:REWRITE DEFAULT-MINUS))
 (244 82 (:REWRITE |(< (+ (- c) x) y)|))
 (224 62 (:REWRITE |(< y (+ (- c) x))|))
 (216 8
      (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (208 8
      (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (186 66 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (164 164
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (154 154
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (130 70 (:REWRITE |(+ c (+ d x))|))
 (120 30 (:REWRITE RATIONALP-X))
 (103 25
      (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (92 72 (:REWRITE INTEGERP-MINUS-X))
 (90 3
     (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (90 3
     (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (90 3 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (90 3 (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (86 86 (:REWRITE |(< (+ c/d x) y)|))
 (83 72 (:REWRITE REDUCE-INTEGERP-+))
 (78 48 (:REWRITE DEFAULT-EXPT-2))
 (78 26 (:REWRITE RTL::BVECP-EXACTP))
 (72 72 (:META META-INTEGERP-CORRECT))
 (70 70 (:REWRITE |(< x (+ c/d y))|))
 (52 52 (:TYPE-PRESCRIPTION RTL::BVECP))
 (48 48 (:REWRITE DEFAULT-EXPT-1))
 (48 48 (:REWRITE |(expt 1/c n)|))
 (48 48 (:REWRITE |(expt (- x) n)|))
 (42 42 (:REWRITE DEFAULT-DIVIDE))
 (41 41 (:REWRITE |(- (* c x))|))
 (40 40
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (40 40 (:REWRITE |(* c (* d x))|))
 (32 32 (:REWRITE |(< (* x y) 0)|))
 (30 30 (:REWRITE REDUCE-RATIONALP-+))
 (30 30 (:REWRITE REDUCE-RATIONALP-*))
 (30 30 (:REWRITE RATIONALP-MINUS-X))
 (30 30 (:META META-RATIONALP-CORRECT))
 (28 28 (:REWRITE |(< 0 (* x y))|))
 (28 28 (:REWRITE |(< (/ x) 0)|))
 (24 6 (:REWRITE |(integerp (- x))|))
 (20 20 (:REWRITE FOLD-CONSTS-IN-+))
 (18 18
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (18 18
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (18 18
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (18 18
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (13 13
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (13 13
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (10 10 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (10 10 (:LINEAR EXPT-LINEAR-LOWER-<))
 (9 9 (:LINEAR EXPT-LINEAR-UPPER-<))
 (9 9 (:LINEAR EXPT->=-1-TWO))
 (9 9 (:LINEAR EXPT->-1-TWO))
 (9 9 (:LINEAR EXPT-<=-1-ONE))
 (9 9 (:LINEAR EXPT-<-1-ONE))
 (8 8
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (8 8
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (8 8 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (8 8
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (8 8
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (8 8
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (8 8
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (8 8
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (8 8 (:REWRITE |(equal c (/ x))|))
 (8 8 (:REWRITE |(equal c (- x))|))
 (8 8 (:REWRITE |(equal (/ x) c)|))
 (8 8 (:REWRITE |(equal (/ x) (/ y))|))
 (8 8 (:REWRITE |(equal (- x) c)|))
 (8 8 (:REWRITE |(equal (- x) (- y))|))
 (8 8
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (8 8
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (7 7 (:REWRITE ZP-OPEN))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RTL::R-POS-RNE-UP-32
 (6762
  6762
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (6762
      6762
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (6762
     6762
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (6762 6762
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (3636 3636
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (3636 3636
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (3636 3636
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (3636 3636
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (2155 68 (:REWRITE RTL::R-EXACTP-6))
 (1998 548 (:REWRITE DEFAULT-TIMES-2))
 (1768 507 (:REWRITE DEFAULT-PLUS-2))
 (1618 548 (:REWRITE DEFAULT-TIMES-1))
 (1381 248
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (1323 507 (:REWRITE DEFAULT-PLUS-1))
 (1060 272 (:REWRITE DEFAULT-LESS-THAN-2))
 (826 272 (:REWRITE DEFAULT-LESS-THAN-1))
 (802 198 (:REWRITE SIMPLIFY-SUMS-<))
 (537 234 (:REWRITE DEFAULT-MINUS))
 (323 263 (:REWRITE |(< c (- x))|))
 (323 263
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (318 26 (:REWRITE ODD-EXPT-THM))
 (297 297
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (275 263 (:REWRITE |(< (- x) (- y))|))
 (272 272 (:REWRITE THE-FLOOR-BELOW))
 (272 272 (:REWRITE THE-FLOOR-ABOVE))
 (263 263
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (263 263
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (263 263
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (263 263 (:REWRITE INTEGERP-<-CONSTANT))
 (263 263 (:REWRITE CONSTANT-<-INTEGERP))
 (263 263
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (263 263
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (263 263
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (263 263
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (263 263
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (263 263
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (263 263
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (263 263 (:REWRITE |(< (/ x) (/ y))|))
 (263 263 (:REWRITE |(< (- x) c)|))
 (223 223
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (189 7
      (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (182 7
      (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (148 37 (:REWRITE RATIONALP-X))
 (130 26
      (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (122 50 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (119 66 (:REWRITE DEFAULT-EXPT-2))
 (95 83 (:REWRITE INTEGERP-MINUS-X))
 (93 31 (:REWRITE RTL::BVECP-EXACTP))
 (89 89 (:REWRITE |(- (* c x))|))
 (83 83 (:REWRITE REDUCE-INTEGERP-+))
 (83 83 (:META META-INTEGERP-CORRECT))
 (81 3 (:LINEAR EXPT->=-1-ONE))
 (79 3 (:LINEAR EXPT->-1-ONE))
 (78 78 (:REWRITE |(* c (* d x))|))
 (73 73 (:REWRITE |(< (+ c/d x) y)|))
 (73 73 (:REWRITE |(< (+ (- c) x) y)|))
 (71 3 (:LINEAR EXPT-X->=-X))
 (71 3 (:LINEAR EXPT-X->-X))
 (66 66 (:REWRITE DEFAULT-EXPT-1))
 (66 66 (:REWRITE |(expt 1/c n)|))
 (66 66 (:REWRITE |(expt (- x) n)|))
 (62 62 (:TYPE-PRESCRIPTION RTL::BVECP))
 (41 41 (:REWRITE |(< y (+ (- c) x))|))
 (41 41 (:REWRITE |(< x (+ c/d y))|))
 (37 37 (:REWRITE REDUCE-RATIONALP-+))
 (37 37 (:REWRITE REDUCE-RATIONALP-*))
 (37 37 (:REWRITE RATIONALP-MINUS-X))
 (37 37 (:META META-RATIONALP-CORRECT))
 (36 36
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (36 36 (:REWRITE DEFAULT-DIVIDE))
 (32 8 (:REWRITE |(integerp (- x))|))
 (30 3
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (30 3
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (21 21 (:REWRITE |(< (/ x) 0)|))
 (21 21 (:REWRITE |(< (* x y) 0)|))
 (21 21 (:REWRITE |(+ c (+ d x))|))
 (9 9 (:REWRITE ZP-OPEN))
 (9 9 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (9 9
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (9 9
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (9 9
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (9 9
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (9 9
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (9 9 (:REWRITE |(equal c (/ x))|))
 (9 9 (:REWRITE |(equal c (- x))|))
 (9 9 (:REWRITE |(equal (/ x) c)|))
 (9 9 (:REWRITE |(equal (/ x) (/ y))|))
 (9 9 (:REWRITE |(equal (- x) c)|))
 (9 9 (:REWRITE |(equal (- x) (- y))|))
 (8 8
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (8 8
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (7 7 (:REWRITE FOLD-CONSTS-IN-+))
 (7 7
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (7 7
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (6 6
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (4 4 (:REWRITE |(< 0 (/ x))|))
 (4 4 (:REWRITE |(< 0 (* x y))|))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-4A-EXPT))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<))
 (3 3 (:LINEAR EXPT->=-1-TWO))
 (3 3 (:LINEAR EXPT->-1-TWO))
 (3 3 (:LINEAR EXPT-<=-1-ONE))
 (3 3 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-POS-RNE-UP-33
 (2372
  2372
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (2372
      2372
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (2372
     2372
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (2372 2372
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1868 1868
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (1868 1868
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (1868 1868
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (1868 1868
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (867 20 (:REWRITE RTL::R-EXACTP-6))
 (750 134
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (716 248 (:REWRITE DEFAULT-PLUS-2))
 (589 152 (:REWRITE DEFAULT-LESS-THAN-2))
 (486 152 (:REWRITE DEFAULT-LESS-THAN-1))
 (466 248 (:REWRITE DEFAULT-PLUS-1))
 (430 105 (:REWRITE SIMPLIFY-SUMS-<))
 (233 18 (:REWRITE ODD-EXPT-THM))
 (181 145
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (172 102 (:REWRITE DEFAULT-TIMES-1))
 (157 145 (:REWRITE |(< (- x) (- y))|))
 (152 152 (:REWRITE THE-FLOOR-BELOW))
 (152 152 (:REWRITE THE-FLOOR-ABOVE))
 (152 102 (:REWRITE DEFAULT-TIMES-2))
 (145 145
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (145 145
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (145 145
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (145 145 (:REWRITE INTEGERP-<-CONSTANT))
 (145 145 (:REWRITE CONSTANT-<-INTEGERP))
 (145 145
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (145 145
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (145 145
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (145 145
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (145 145 (:REWRITE |(< c (- x))|))
 (145 145
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (145 145
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (145 145
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (145 145 (:REWRITE |(< (/ x) (/ y))|))
 (145 145 (:REWRITE |(< (- x) c)|))
 (135 5
      (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (130 5
      (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (113 73 (:REWRITE DEFAULT-MINUS))
 (84 21 (:REWRITE RATIONALP-X))
 (83 18
     (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (82 82
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (81 3 (:LINEAR EXPT->=-1-ONE))
 (79 3 (:LINEAR EXPT->-1-ONE))
 (71 3 (:LINEAR EXPT-X->=-X))
 (71 3 (:LINEAR EXPT-X->-X))
 (66 66
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (63 51 (:REWRITE INTEGERP-MINUS-X))
 (57 19 (:REWRITE RTL::BVECP-EXACTP))
 (51 51 (:REWRITE REDUCE-INTEGERP-+))
 (51 51 (:META META-INTEGERP-CORRECT))
 (47 28 (:REWRITE DEFAULT-EXPT-2))
 (45 45 (:REWRITE |(< (+ c/d x) y)|))
 (45 45 (:REWRITE |(< (+ (- c) x) y)|))
 (41 29 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (38 38 (:TYPE-PRESCRIPTION RTL::BVECP))
 (28 28 (:REWRITE DEFAULT-EXPT-1))
 (28 28 (:REWRITE |(expt 1/c n)|))
 (28 28 (:REWRITE |(expt (- x) n)|))
 (26 26 (:REWRITE |(< y (+ (- c) x))|))
 (26 26 (:REWRITE |(< x (+ c/d y))|))
 (24 24
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (24 24 (:REWRITE DEFAULT-DIVIDE))
 (22 22 (:REWRITE |(- (* c x))|))
 (21 21 (:REWRITE REDUCE-RATIONALP-+))
 (21 21 (:REWRITE REDUCE-RATIONALP-*))
 (21 21 (:REWRITE RATIONALP-MINUS-X))
 (21 21 (:META META-RATIONALP-CORRECT))
 (20 5 (:REWRITE |(integerp (- x))|))
 (15 15 (:REWRITE |(< (/ x) 0)|))
 (15 15 (:REWRITE |(< (* x y) 0)|))
 (15 15 (:REWRITE |(+ c (+ d x))|))
 (9 9 (:REWRITE |(* c (* d x))|))
 (8 8
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (8 8
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (6 6
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (5 5 (:REWRITE ZP-OPEN))
 (5 5 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (5 5
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (5 5
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (5 5
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (5 5
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (5 5 (:REWRITE FOLD-CONSTS-IN-+))
 (5 5
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (5 5 (:REWRITE |(equal c (/ x))|))
 (5 5 (:REWRITE |(equal c (- x))|))
 (5 5 (:REWRITE |(equal (/ x) c)|))
 (5 5 (:REWRITE |(equal (/ x) (/ y))|))
 (5 5 (:REWRITE |(equal (- x) c)|))
 (5 5 (:REWRITE |(equal (- x) (- y))|))
 (5 5
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (5 5
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (4 4 (:REWRITE |(< 0 (/ x))|))
 (4 4 (:REWRITE |(< 0 (* x y))|))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<))
 (3 3 (:LINEAR EXPT->=-1-TWO))
 (3 3 (:LINEAR EXPT->-1-TWO))
 (3 3 (:LINEAR EXPT-<=-1-ONE))
 (3 3 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-POS-RNE-UP-34
 (9959
  9959
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (9959
      9959
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (9959
     9959
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (9959 9959
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (7420 7420
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (7420 7420
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (7420 7420
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (7420 7420
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (3405 1167 (:REWRITE DEFAULT-PLUS-2))
 (2872 56 (:REWRITE RTL::R-EXACTP-6))
 (2732 535
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (2605 699 (:REWRITE DEFAULT-LESS-THAN-2))
 (1925 1167 (:REWRITE DEFAULT-PLUS-1))
 (1555 699 (:REWRITE DEFAULT-LESS-THAN-1))
 (998 89 (:REWRITE ODD-EXPT-THM))
 (952 676
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (700 676 (:REWRITE |(< (- x) (- y))|))
 (699 699 (:REWRITE THE-FLOOR-BELOW))
 (699 699 (:REWRITE THE-FLOOR-ABOVE))
 (676 676
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (676 676
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (676 676
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (676 676 (:REWRITE INTEGERP-<-CONSTANT))
 (676 676 (:REWRITE CONSTANT-<-INTEGERP))
 (676 676
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (676 676
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (676 676
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (676 676
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (676 676 (:REWRITE |(< c (- x))|))
 (676 676
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (676 676
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (676 676
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (676 676 (:REWRITE |(< (/ x) (/ y))|))
 (676 676 (:REWRITE |(< (- x) c)|))
 (540 20
      (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (520 20
      (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (492 89
      (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (345 345
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (342 114 (:REWRITE RTL::BVECP-EXACTP))
 (313 265 (:REWRITE DEFAULT-MINUS))
 (265 241 (:REWRITE INTEGERP-MINUS-X))
 (241 241 (:REWRITE REDUCE-INTEGERP-+))
 (241 241 (:META META-INTEGERP-CORRECT))
 (240 60 (:REWRITE RATIONALP-X))
 (232 232 (:REWRITE DEFAULT-TIMES-2))
 (232 232 (:REWRITE DEFAULT-TIMES-1))
 (228 228 (:TYPE-PRESCRIPTION RTL::BVECP))
 (199 199 (:REWRITE |(< (+ c/d x) y)|))
 (199 199 (:REWRITE |(< (+ (- c) x) y)|))
 (182 182
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (173 149 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (156 102 (:REWRITE DEFAULT-EXPT-2))
 (124 31 (:REWRITE |(integerp (- x))|))
 (109 109 (:REWRITE |(+ c (+ d x))|))
 (102 102 (:REWRITE DEFAULT-EXPT-1))
 (102 102 (:REWRITE |(expt 1/c n)|))
 (102 102 (:REWRITE |(expt (- x) n)|))
 (92 92 (:REWRITE |(< y (+ (- c) x))|))
 (92 92 (:REWRITE |(< x (+ c/d y))|))
 (86 86
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (86 86 (:REWRITE DEFAULT-DIVIDE))
 (81 3 (:LINEAR EXPT->=-1-ONE))
 (79 3 (:LINEAR EXPT->-1-ONE))
 (72 72 (:REWRITE |(- (* c x))|))
 (71 3 (:LINEAR EXPT-X->=-X))
 (71 3 (:LINEAR EXPT-X->-X))
 (69 69 (:REWRITE |(< (/ x) 0)|))
 (69 69 (:REWRITE |(< (* x y) 0)|))
 (60 60 (:REWRITE REDUCE-RATIONALP-+))
 (60 60 (:REWRITE REDUCE-RATIONALP-*))
 (60 60 (:REWRITE RATIONALP-MINUS-X))
 (60 60 (:META META-RATIONALP-CORRECT))
 (53 53 (:REWRITE FOLD-CONSTS-IN-+))
 (20 20
     (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (20 20
     (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (19 17 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (19 17
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (19 17
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (17 17
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (17 17
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (17 17
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (17 17
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (17 17
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (17 17 (:REWRITE |(equal c (/ x))|))
 (17 17 (:REWRITE |(equal c (- x))|))
 (17 17 (:REWRITE |(equal (/ x) c)|))
 (17 17 (:REWRITE |(equal (/ x) (/ y))|))
 (17 17 (:REWRITE |(equal (- x) c)|))
 (17 17 (:REWRITE |(equal (- x) (- y))|))
 (16 16 (:REWRITE ZP-OPEN))
 (10 10 (:REWRITE |(* c (* d x))|))
 (7 7 (:REWRITE |(< 0 (/ x))|))
 (7 7 (:REWRITE |(< 0 (* x y))|))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (6 6
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<))
 (3 3 (:LINEAR EXPT->=-1-TWO))
 (3 3 (:LINEAR EXPT->-1-TWO))
 (3 3 (:LINEAR EXPT-<=-1-ONE))
 (3 3 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-POS-RNE-UP
 (32797
  32797
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (32797
      32797
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (32797
     32797
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (32797 32797
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (30362 30362
        (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (30362 30362
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (30362 30362
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (30362 30362
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (12032 3754 (:REWRITE DEFAULT-PLUS-2))
 (9683 231 (:REWRITE RTL::R-EXACTP-6))
 (8022 1523
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (6280 1683 (:REWRITE DEFAULT-LESS-THAN-2))
 (5726 3754 (:REWRITE DEFAULT-PLUS-1))
 (4519 1683 (:REWRITE DEFAULT-LESS-THAN-1))
 (2120 1634
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (2068 181 (:REWRITE ODD-EXPT-THM))
 (1683 1683 (:REWRITE THE-FLOOR-BELOW))
 (1683 1683 (:REWRITE THE-FLOOR-ABOVE))
 (1662 1634 (:REWRITE |(< (- x) (- y))|))
 (1634 1634
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (1634 1634
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (1634 1634
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (1634 1634 (:REWRITE INTEGERP-<-CONSTANT))
 (1634 1634 (:REWRITE CONSTANT-<-INTEGERP))
 (1634 1634
       (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (1634 1634
       (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (1634 1634
       (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (1634 1634
       (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (1634 1634 (:REWRITE |(< c (- x))|))
 (1634 1634
       (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (1634 1634
       (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (1634 1634
       (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (1634 1634 (:REWRITE |(< (/ x) (/ y))|))
 (1634 1634 (:REWRITE |(< (- x) c)|))
 (1462 1462
       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (1456 1456 (:REWRITE DEFAULT-TIMES-2))
 (1456 1456 (:REWRITE DEFAULT-TIMES-1))
 (1404 52
       (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (1352 52
       (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (1172 293 (:REWRITE RATIONALP-X))
 (974 181
      (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (921 921
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (857 801 (:REWRITE DEFAULT-MINUS))
 (825 275 (:REWRITE RTL::BVECP-EXACTP))
 (664 636 (:REWRITE INTEGERP-MINUS-X))
 (636 636 (:REWRITE REDUCE-INTEGERP-+))
 (636 636 (:META META-INTEGERP-CORRECT))
 (550 550 (:TYPE-PRESCRIPTION RTL::BVECP))
 (545 314 (:REWRITE DEFAULT-EXPT-2))
 (530 530 (:REWRITE |(< (+ c/d x) y)|))
 (530 530 (:REWRITE |(< (+ (- c) x) y)|))
 (498 498 (:REWRITE |(+ c (+ d x))|))
 (459 109 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (459 109
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (459 109
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (415 387 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (314 314 (:REWRITE DEFAULT-EXPT-1))
 (314 314 (:REWRITE |(expt 1/c n)|))
 (314 314 (:REWRITE |(expt (- x) n)|))
 (310 310 (:REWRITE FOLD-CONSTS-IN-+))
 (305 305
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (305 305 (:REWRITE DEFAULT-DIVIDE))
 (302 302 (:REWRITE |(- (* c x))|))
 (293 293 (:REWRITE REDUCE-RATIONALP-+))
 (293 293 (:REWRITE REDUCE-RATIONALP-*))
 (293 293 (:REWRITE RATIONALP-MINUS-X))
 (293 293 (:META META-RATIONALP-CORRECT))
 (251 251 (:REWRITE |(< y (+ (- c) x))|))
 (251 251 (:REWRITE |(< x (+ c/d y))|))
 (244 61 (:REWRITE |(integerp (- x))|))
 (136 136 (:REWRITE |(< (/ x) 0)|))
 (136 136 (:REWRITE |(< (* x y) 0)|))
 (109 109
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (109 109
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (109 109
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (109 109 (:REWRITE |(equal c (/ x))|))
 (109 109 (:REWRITE |(equal c (- x))|))
 (109 109 (:REWRITE |(equal (/ x) c)|))
 (109 109 (:REWRITE |(equal (/ x) (/ y))|))
 (109 109 (:REWRITE |(equal (- x) c)|))
 (109 109 (:REWRITE |(equal (- x) (- y))|))
 (107 107 (:REWRITE |(* c (* d x))|))
 (81 3 (:LINEAR EXPT->=-1-ONE))
 (79 3 (:LINEAR EXPT->-1-ONE))
 (73 73 (:REWRITE ZP-OPEN))
 (71 3 (:LINEAR EXPT-X->=-X))
 (71 3 (:LINEAR EXPT-X->-X))
 (64 2 (:LINEAR RTL::RNE-POSITIVE))
 (52 52
     (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (52 52
     (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (42 42 (:REWRITE |(< 0 (/ x))|))
 (42 42 (:REWRITE |(< 0 (* x y))|))
 (41 41
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (41 41
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (24 24 (:REWRITE |(equal (+ (- c) x) y)|))
 (11 11
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (11 11
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (6 6
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<))
 (3 3 (:LINEAR EXPT->=-1-TWO))
 (3 3 (:LINEAR EXPT->-1-TWO))
 (3 3 (:LINEAR EXPT-<=-1-ONE))
 (3 3 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-POS-RND
 (20479 20479
        (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (20479 20479
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (20479 20479
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (20479 20479
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (11852
  11852
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (11852
      11852
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (11852
     11852
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (11852 11852
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (6360 1292
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (6149 2897 (:REWRITE DEFAULT-PLUS-2))
 (5409 53 (:REWRITE RTL::R-EXACTP-6))
 (4984 1133
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (4602 1341 (:REWRITE DEFAULT-LESS-THAN-2))
 (4148 2897 (:REWRITE DEFAULT-PLUS-1))
 (2851 1341 (:REWRITE DEFAULT-LESS-THAN-1))
 (2646 2646
       (:TYPE-PRESCRIPTION RTL::RND-NON-POS))
 (2646 2646
       (:TYPE-PRESCRIPTION RTL::RND-NEGATIVE))
 (2564 786 (:REWRITE SIMPLIFY-SUMS-<))
 (1969 239
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (1863 141 (:REWRITE ODD-EXPT-THM))
 (1714 23 (:LINEAR EXPT->=-1-ONE))
 (1685 23 (:LINEAR EXPT->-1-ONE))
 (1680 336 (:REWRITE ACL2-NUMBERP-X))
 (1548 23 (:LINEAR EXPT-X->=-X))
 (1548 23 (:LINEAR EXPT-X->-X))
 (1504 1222
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (1341 1341 (:REWRITE THE-FLOOR-BELOW))
 (1341 1341 (:REWRITE THE-FLOOR-ABOVE))
 (1310 1222 (:REWRITE |(< (- x) (- y))|))
 (1292 1292
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (1292 1292
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (1247 1247 (:REWRITE DEFAULT-TIMES-2))
 (1247 1247 (:REWRITE DEFAULT-TIMES-1))
 (1242 46
       (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (1222 1222 (:REWRITE INTEGERP-<-CONSTANT))
 (1222 1222 (:REWRITE CONSTANT-<-INTEGERP))
 (1222 1222
       (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (1222 1222
       (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (1222 1222
       (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (1222 1222
       (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (1222 1222 (:REWRITE |(< c (- x))|))
 (1222 1222
       (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (1222 1222
       (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (1222 1222
       (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (1222 1222 (:REWRITE |(< (/ x) (/ y))|))
 (1222 1222 (:REWRITE |(< (- x) c)|))
 (1196 46
       (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (1140 285 (:REWRITE RATIONALP-X))
 (994 427 (:REWRITE |(< (+ (- c) x) y)|))
 (918 918
      (:TYPE-PRESCRIPTION RTL::COMMON-MODE-P))
 (829 829
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (782 215 (:REWRITE |(< y (+ (- c) x))|))
 (767 767
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (701 525 (:REWRITE DEFAULT-MINUS))
 (625 239
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (614 141
      (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (612 402 (:REWRITE |(+ c (+ d x))|))
 (608 520 (:REWRITE INTEGERP-MINUS-X))
 (520 520 (:REWRITE REDUCE-INTEGERP-+))
 (520 520 (:META META-INTEGERP-CORRECT))
 (457 239 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (450 7 (:LINEAR RTL::RTZ-NEGATIVE))
 (441 441 (:REWRITE |(< (+ c/d x) y)|))
 (440 5 (:LINEAR RTL::RAZ-POSITIVE))
 (435 347 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (420 140 (:REWRITE RTL::BVECP-EXACTP))
 (285 285 (:REWRITE REDUCE-RATIONALP-+))
 (285 285 (:REWRITE REDUCE-RATIONALP-*))
 (285 285 (:REWRITE RATIONALP-MINUS-X))
 (285 285 (:META META-RATIONALP-CORRECT))
 (280 280 (:TYPE-PRESCRIPTION RTL::BVECP))
 (260 260 (:REWRITE |(- (* c x))|))
 (243 243 (:REWRITE |(< x (+ c/d y))|))
 (241 241
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (241 241 (:REWRITE DEFAULT-DIVIDE))
 (239 239
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (239 239
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (239 239
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (239 239 (:REWRITE |(equal c (/ x))|))
 (239 239 (:REWRITE |(equal c (- x))|))
 (239 239 (:REWRITE |(equal (/ x) c)|))
 (239 239 (:REWRITE |(equal (/ x) (/ y))|))
 (239 239 (:REWRITE |(equal (- x) c)|))
 (239 239 (:REWRITE |(equal (- x) (- y))|))
 (230 230 (:REWRITE |(< (* x y) 0)|))
 (216 216 (:REWRITE |(< (/ x) 0)|))
 (184 184 (:REWRITE FOLD-CONSTS-IN-+))
 (176 123 (:REWRITE DEFAULT-EXPT-2))
 (140 35 (:REWRITE |(integerp (- x))|))
 (123 123 (:REWRITE DEFAULT-EXPT-1))
 (123 123 (:REWRITE |(expt 1/c n)|))
 (123 123 (:REWRITE |(expt (- x) n)|))
 (101 101 (:REWRITE RTL::RTZ-NEG-BITS))
 (96 96 (:REWRITE |(* c (* d x))|))
 (66 2 (:LINEAR RTL::RND-NON-POS))
 (66 2 (:LINEAR RTL::RND-NON-NEG))
 (56 56 (:REWRITE |(< 0 (* x y))|))
 (53 53 (:REWRITE RTL::RAZ-NEG-BITS))
 (52 52
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (52 52
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (48 48
     (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (48 48
     (:REWRITE |(< (* x (/ y)) 0) rationalp (* x (/ y))|))
 (46 46
     (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (46 46
     (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (46 46
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (46 46
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (46 46
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (46 46
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (42 42 (:REWRITE |(< 0 (/ x))|))
 (28 28 (:REWRITE ZP-OPEN))
 (23 23 (:LINEAR EXPT-LINEAR-UPPER-<))
 (23 23 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (23 23 (:LINEAR EXPT-LINEAR-LOWER-<))
 (23 23 (:LINEAR EXPT->=-1-TWO))
 (23 23 (:LINEAR EXPT->-1-TWO))
 (23 23 (:LINEAR EXPT-<=-1-ONE))
 (23 23 (:LINEAR EXPT-<-1-ONE))
 (14 14
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (14 14
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (1 1 (:REWRITE |(equal (+ (- c) x) y)|)))
(RTL::Q-NOT-EXPO-Q
 (456 6 (:REWRITE RTL::R-EXACTP-6))
 (416
  416
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (416 416
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (416
     416
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (416 416
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (416 416
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (416 416
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (318 318
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (318 318
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (318 318
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (318 318
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (139 41
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (110 48 (:REWRITE DEFAULT-LESS-THAN-2))
 (108 4
      (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (104 4
      (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (92 48 (:REWRITE DEFAULT-LESS-THAN-1))
 (90 34 (:REWRITE DEFAULT-PLUS-2))
 (78 2 (:LINEAR EXPT->=-1-ONE))
 (78 2 (:LINEAR EXPT-<=-1-TWO))
 (76 2 (:LINEAR EXPT->-1-ONE))
 (76 2 (:LINEAR EXPT-<-1-TWO))
 (75 37 (:REWRITE SIMPLIFY-SUMS-<))
 (68 2 (:LINEAR EXPT-X->=-X))
 (68 2 (:LINEAR EXPT-X->-X))
 (60 48
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (60 34 (:REWRITE DEFAULT-PLUS-1))
 (52 48 (:REWRITE |(< (- x) (- y))|))
 (48 48 (:REWRITE THE-FLOOR-BELOW))
 (48 48 (:REWRITE THE-FLOOR-ABOVE))
 (48 48
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (48 48
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (48 48
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (48 48 (:REWRITE INTEGERP-<-CONSTANT))
 (48 48 (:REWRITE CONSTANT-<-INTEGERP))
 (48 48
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (48 48
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (48 48
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (48 48
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (48 48 (:REWRITE |(< c (- x))|))
 (48 48
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (48 48
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (48 48
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (48 48 (:REWRITE |(< (/ x) (/ y))|))
 (48 48 (:REWRITE |(< (- x) c)|))
 (46 3 (:REWRITE ODD-EXPT-THM))
 (18 10 (:REWRITE DEFAULT-MINUS))
 (18 6 (:REWRITE RTL::BVECP-EXACTP))
 (14 14
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (14 14
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (14 14 (:REWRITE DEFAULT-TIMES-2))
 (14 14 (:REWRITE DEFAULT-TIMES-1))
 (14 14 (:REWRITE DEFAULT-DIVIDE))
 (13 9 (:REWRITE INTEGERP-MINUS-X))
 (12 12 (:TYPE-PRESCRIPTION RTL::BVECP))
 (10 10
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (9 9 (:REWRITE REDUCE-INTEGERP-+))
 (9 9 (:META META-INTEGERP-CORRECT))
 (8 8 (:REWRITE |(< (/ x) 0)|))
 (8 8 (:REWRITE |(< (* x y) 0)|))
 (8 4 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (8 4 (:REWRITE DEFAULT-EXPT-2))
 (8 2 (:REWRITE RATIONALP-X))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (6 6 (:REWRITE |(< y (+ (- c) x))|))
 (6 6 (:REWRITE |(< x (+ c/d y))|))
 (6 6 (:REWRITE |(< (+ c/d x) y)|))
 (6 6 (:REWRITE |(< (+ (- c) x) y)|))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (4 4 (:REWRITE DEFAULT-EXPT-1))
 (4 4 (:REWRITE |(expt 1/c n)|))
 (4 4 (:REWRITE |(expt (- x) n)|))
 (4 4
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (4 4 (:REWRITE |(< 0 (/ x))|))
 (4 4 (:REWRITE |(< 0 (* x y))|))
 (4 4
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (4 4 (:REWRITE |(+ c (+ d x))|))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (4 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (4 2
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (4 2
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (2 2 (:REWRITE REDUCE-RATIONALP-+))
 (2 2 (:REWRITE REDUCE-RATIONALP-*))
 (2 2
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (2 2
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (2 2 (:REWRITE RATIONALP-MINUS-X))
 (2 2 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (2 2 (:REWRITE |(equal c (/ x))|))
 (2 2 (:REWRITE |(equal c (- x))|))
 (2 2 (:REWRITE |(equal (/ x) c)|))
 (2 2 (:REWRITE |(equal (/ x) (/ y))|))
 (2 2 (:REWRITE |(equal (- x) c)|))
 (2 2 (:REWRITE |(equal (- x) (- y))|))
 (2 2
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (2 2
    (:REWRITE |(< (* x (/ y)) 0) rationalp (* x (/ y))|))
 (2 2 (:REWRITE |(- (* c x))|))
 (2 2 (:META META-RATIONALP-CORRECT))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-ONE))
 (1 1 (:REWRITE ZP-OPEN)))
(RTL::R-NEG-1
 (1107 1107
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (1107 1107
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (1107 1107
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (1107 1107
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (767 11 (:REWRITE RTL::R-EXACTP-6))
 (516
  516
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (516 516
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (516
     516
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (516 516
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (516 516
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (516 516
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (436 115 (:REWRITE DEFAULT-PLUS-2))
 (330 68
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (300 115 (:REWRITE DEFAULT-PLUS-1))
 (253 87 (:REWRITE DEFAULT-LESS-THAN-2))
 (211 87 (:REWRITE DEFAULT-LESS-THAN-1))
 (165 55 (:REWRITE SIMPLIFY-SUMS-<))
 (162 6
      (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (156 6
      (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (126 6 (:REWRITE ODD-EXPT-THM))
 (123 87
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (121 87 (:REWRITE |(< (- x) (- y))|))
 (90 32 (:REWRITE DEFAULT-MINUS))
 (87 87 (:REWRITE THE-FLOOR-BELOW))
 (87 87 (:REWRITE THE-FLOOR-ABOVE))
 (87 87
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (87 87
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (87 87
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (87 87 (:REWRITE INTEGERP-<-CONSTANT))
 (87 87 (:REWRITE CONSTANT-<-INTEGERP))
 (87 87
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (87 87
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (87 87
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (87 87
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (87 87 (:REWRITE |(< c (- x))|))
 (87 87
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (87 87
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (87 87
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (87 87 (:REWRITE |(< (/ x) (/ y))|))
 (87 87 (:REWRITE |(< (- x) c)|))
 (54 18 (:REWRITE RTL::BVECP-EXACTP))
 (51 27 (:REWRITE INTEGERP-MINUS-X))
 (47 13 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (40 1 (:LINEAR EXPT->=-1-ONE))
 (40 1 (:LINEAR EXPT-<=-1-TWO))
 (39 1 (:LINEAR EXPT->-1-ONE))
 (39 1 (:LINEAR EXPT-<-1-TWO))
 (36 36 (:TYPE-PRESCRIPTION RTL::BVECP))
 (36 9 (:REWRITE RATIONALP-X))
 (35 35
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (35 1 (:LINEAR EXPT-X->=-X))
 (35 1 (:LINEAR EXPT-X->-X))
 (27 27 (:REWRITE REDUCE-INTEGERP-+))
 (27 27 (:META META-INTEGERP-CORRECT))
 (18 18
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (18 18
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (18 18 (:REWRITE DEFAULT-TIMES-2))
 (18 18 (:REWRITE DEFAULT-TIMES-1))
 (18 18 (:REWRITE DEFAULT-DIVIDE))
 (18 9 (:REWRITE DEFAULT-EXPT-2))
 (17 5 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (17 5
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (17 5
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (15 15 (:REWRITE |(< (+ c/d x) y)|))
 (15 15 (:REWRITE |(< (+ (- c) x) y)|))
 (13 13 (:REWRITE |(+ c (+ d x))|))
 (11 11 (:REWRITE |(< y (+ (- c) x))|))
 (11 11 (:REWRITE |(< x (+ c/d y))|))
 (9 9 (:REWRITE REDUCE-RATIONALP-+))
 (9 9 (:REWRITE REDUCE-RATIONALP-*))
 (9 9 (:REWRITE RATIONALP-MINUS-X))
 (9 9 (:REWRITE DEFAULT-EXPT-1))
 (9 9 (:REWRITE |(expt 1/c n)|))
 (9 9 (:REWRITE |(expt (- x) n)|))
 (9 9 (:META META-RATIONALP-CORRECT))
 (8 8 (:REWRITE |(< (/ x) 0)|))
 (8 8 (:REWRITE |(< (* x y) 0)|))
 (7 7 (:REWRITE FOLD-CONSTS-IN-+))
 (6 6 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (6 6
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (6 6
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (6 6 (:REWRITE |(- (* c x))|))
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
 (3 3 (:REWRITE ZP-OPEN))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:REWRITE |(< 0 (* x y))|))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (1 1 (:REWRITE |(equal (expt 2 n) c)|))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<))
 (1 1 (:LINEAR EXPT->=-1-TWO))
 (1 1 (:LINEAR EXPT->-1-TWO))
 (1 1 (:LINEAR EXPT-<=-1-ONE))
 (1 1 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-NEG-2
 (656 656
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (656 656
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (656 656
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (656 656
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (412
  412
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (412 412
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (412
     412
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (412 412
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (412 412
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (412 412
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (397 6 (:REWRITE RTL::R-EXACTP-6))
 (209 61 (:REWRITE DEFAULT-PLUS-2))
 (181 45
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (158 54 (:REWRITE DEFAULT-LESS-THAN-2))
 (148 61 (:REWRITE DEFAULT-PLUS-1))
 (106 54 (:REWRITE DEFAULT-LESS-THAN-1))
 (94 38 (:REWRITE SIMPLIFY-SUMS-<))
 (81 3
     (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (80 2 (:LINEAR EXPT->=-1-ONE))
 (80 2 (:LINEAR EXPT-<=-1-TWO))
 (78 3
     (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (78 2 (:LINEAR EXPT->-1-ONE))
 (78 2 (:LINEAR EXPT-<-1-TWO))
 (72 54
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (70 54 (:REWRITE |(< (- x) (- y))|))
 (70 2 (:LINEAR EXPT-X->=-X))
 (70 2 (:LINEAR EXPT-X->-X))
 (60 4 (:REWRITE ODD-EXPT-THM))
 (54 54 (:REWRITE THE-FLOOR-BELOW))
 (54 54 (:REWRITE THE-FLOOR-ABOVE))
 (54 54
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (54 54
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (54 54
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (54 54 (:REWRITE INTEGERP-<-CONSTANT))
 (54 54 (:REWRITE CONSTANT-<-INTEGERP))
 (54 54
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (54 54
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (54 54
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (54 54
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (54 54 (:REWRITE |(< c (- x))|))
 (54 54
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (54 54
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (54 54
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (54 54 (:REWRITE |(< (/ x) (/ y))|))
 (54 54 (:REWRITE |(< (- x) c)|))
 (45 17 (:REWRITE DEFAULT-MINUS))
 (32 16 (:REWRITE INTEGERP-MINUS-X))
 (27 9 (:REWRITE RTL::BVECP-EXACTP))
 (24 6 (:REWRITE RATIONALP-X))
 (23 7 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (19 19
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (18 18 (:TYPE-PRESCRIPTION RTL::BVECP))
 (16 16 (:REWRITE REDUCE-INTEGERP-+))
 (16 16 (:META META-INTEGERP-CORRECT))
 (12 12 (:REWRITE |(< y (+ (- c) x))|))
 (12 12 (:REWRITE |(< x (+ c/d y))|))
 (11 11 (:REWRITE |(< (+ c/d x) y)|))
 (11 11 (:REWRITE |(< (+ (- c) x) y)|))
 (10 10
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (10 10
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (10 10 (:REWRITE DEFAULT-TIMES-2))
 (10 10 (:REWRITE DEFAULT-TIMES-1))
 (10 10 (:REWRITE DEFAULT-DIVIDE))
 (8 4 (:REWRITE DEFAULT-EXPT-2))
 (7 7 (:REWRITE |(< (/ x) 0)|))
 (7 7 (:REWRITE |(< (* x y) 0)|))
 (7 7 (:REWRITE |(+ c (+ d x))|))
 (6 6 (:REWRITE REDUCE-RATIONALP-+))
 (6 6 (:REWRITE REDUCE-RATIONALP-*))
 (6 6 (:REWRITE RATIONALP-MINUS-X))
 (6 6 (:META META-RATIONALP-CORRECT))
 (5 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (5 3
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (5 3
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (4 4 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (4 4 (:REWRITE FOLD-CONSTS-IN-+))
 (4 4 (:REWRITE DEFAULT-EXPT-1))
 (4 4 (:REWRITE |(expt 1/c n)|))
 (4 4 (:REWRITE |(expt (- x) n)|))
 (4 4 (:REWRITE |(< 0 (/ x))|))
 (4 4 (:REWRITE |(< 0 (* x y))|))
 (4 4 (:REWRITE |(- (* c x))|))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (3 3
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (3 3
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (3 3
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (3 3 (:REWRITE |(equal c (/ x))|))
 (3 3 (:REWRITE |(equal c (- x))|))
 (3 3 (:REWRITE |(equal (/ x) c)|))
 (3 3 (:REWRITE |(equal (/ x) (/ y))|))
 (3 3 (:REWRITE |(equal (- x) c)|))
 (3 3 (:REWRITE |(equal (- x) (- y))|))
 (3 3
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (3 3
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-NEG-4
 (7 7 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (7 7 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (7 7 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (7 7 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (4
  4
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE)))
(RTL::R-NEG-5
 (32 32 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (32 32 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (32 32 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (32 32 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (27
  27
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (27 27
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (27 27
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (27 27
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (27 27
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (27 27
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE)))
(RTL::R-NEG-6
 (555 555
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (555 555
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (555 555
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (555 555
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (504
  504
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (504 504
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (504
     504
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (504 504
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (504 504
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (504 504
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (396 5 (:REWRITE RTL::R-EXACTP-6))
 (230 70 (:REWRITE DEFAULT-PLUS-2))
 (205 43
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (167 51 (:REWRITE DEFAULT-LESS-THAN-2))
 (143 70 (:REWRITE DEFAULT-PLUS-1))
 (113 51 (:REWRITE DEFAULT-LESS-THAN-1))
 (105 35 (:REWRITE SIMPLIFY-SUMS-<))
 (81 3
     (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (78 3
     (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (69 51
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (63 51 (:REWRITE |(< (- x) (- y))|))
 (63 3 (:REWRITE ODD-EXPT-THM))
 (52 20 (:REWRITE DEFAULT-TIMES-2))
 (51 51 (:REWRITE THE-FLOOR-BELOW))
 (51 51 (:REWRITE THE-FLOOR-ABOVE))
 (51 51
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (51 51
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (51 51
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (51 51 (:REWRITE INTEGERP-<-CONSTANT))
 (51 51 (:REWRITE CONSTANT-<-INTEGERP))
 (51 51
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (51 51
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (51 51
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (51 51
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (51 51 (:REWRITE |(< c (- x))|))
 (51 51
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (51 51
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (51 51
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (51 51 (:REWRITE |(< (/ x) (/ y))|))
 (51 51 (:REWRITE |(< (- x) c)|))
 (48 20 (:REWRITE DEFAULT-MINUS))
 (40 1 (:LINEAR EXPT->=-1-ONE))
 (40 1 (:LINEAR EXPT-<=-1-TWO))
 (39 1 (:LINEAR EXPT->-1-ONE))
 (39 1 (:LINEAR EXPT-<-1-TWO))
 (35 1 (:LINEAR EXPT-X->=-X))
 (35 1 (:LINEAR EXPT-X->-X))
 (27 15 (:REWRITE INTEGERP-MINUS-X))
 (27 9 (:REWRITE RTL::BVECP-EXACTP))
 (24 24
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (24 6 (:REWRITE RATIONALP-X))
 (20 20 (:REWRITE DEFAULT-TIMES-1))
 (20 8 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (18 18 (:TYPE-PRESCRIPTION RTL::BVECP))
 (15 15 (:REWRITE REDUCE-INTEGERP-+))
 (15 15
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (15 15 (:META META-INTEGERP-CORRECT))
 (10 10
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (10 10 (:REWRITE DEFAULT-DIVIDE))
 (10 10 (:REWRITE |(< (+ c/d x) y)|))
 (10 10 (:REWRITE |(< (+ (- c) x) y)|))
 (10 10 (:REWRITE |(+ c (+ d x))|))
 (10 5 (:REWRITE DEFAULT-EXPT-2))
 (9 9 (:REWRITE |(< y (+ (- c) x))|))
 (9 9 (:REWRITE |(< x (+ c/d y))|))
 (6 6 (:REWRITE REDUCE-RATIONALP-+))
 (6 6 (:REWRITE REDUCE-RATIONALP-*))
 (6 6 (:REWRITE RATIONALP-MINUS-X))
 (6 6 (:META META-RATIONALP-CORRECT))
 (5 5 (:REWRITE FOLD-CONSTS-IN-+))
 (5 5 (:REWRITE DEFAULT-EXPT-1))
 (5 5 (:REWRITE |(expt 1/c n)|))
 (5 5 (:REWRITE |(expt (- x) n)|))
 (5 5 (:REWRITE |(< (/ x) 0)|))
 (5 5 (:REWRITE |(< (* x y) 0)|))
 (4 4 (:REWRITE |(- (* c x))|))
 (3 3 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (3 3
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (3 3
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (2 2 (:REWRITE ZP-OPEN))
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
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (2 2
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (2 2
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (2 2
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
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
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<))
 (1 1 (:LINEAR EXPT->=-1-TWO))
 (1 1 (:LINEAR EXPT->-1-TWO))
 (1 1 (:LINEAR EXPT-<=-1-ONE))
 (1 1 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-NEG-10)
(RTL::R-NEG-11
 (620
  620
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (620 620
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (620
     620
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (620 620
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (620 620
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (620 620
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (532 532
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (532 532
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (532 532
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (532 532
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (397 6 (:REWRITE RTL::R-EXACTP-6))
 (358 78 (:REWRITE DEFAULT-PLUS-2))
 (245 43
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (231 78 (:REWRITE DEFAULT-PLUS-1))
 (173 51 (:REWRITE DEFAULT-LESS-THAN-1))
 (147 51 (:REWRITE DEFAULT-LESS-THAN-2))
 (129 29 (:REWRITE DEFAULT-TIMES-1))
 (125 35 (:REWRITE SIMPLIFY-SUMS-<))
 (89 29 (:REWRITE DEFAULT-TIMES-2))
 (83 51 (:REWRITE |(< (- x) (- y))|))
 (81 3
     (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (78 3
     (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (71 25 (:REWRITE DEFAULT-MINUS))
 (69 51
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (63 3 (:REWRITE ODD-EXPT-THM))
 (53 51 (:REWRITE |(< (/ x) (/ y))|))
 (51 51 (:REWRITE THE-FLOOR-BELOW))
 (51 51 (:REWRITE THE-FLOOR-ABOVE))
 (51 51
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (51 51
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (51 51
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (51 51 (:REWRITE INTEGERP-<-CONSTANT))
 (51 51 (:REWRITE CONSTANT-<-INTEGERP))
 (51 51
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (51 51
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (51 51
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (51 51
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (51 51 (:REWRITE |(< c (- x))|))
 (51 51
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (51 51
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (51 51
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (51 51 (:REWRITE |(< (- x) c)|))
 (40 8 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (40 1 (:LINEAR EXPT->=-1-ONE))
 (40 1 (:LINEAR EXPT-<=-1-TWO))
 (39 1 (:LINEAR EXPT->-1-ONE))
 (39 1 (:LINEAR EXPT-<-1-TWO))
 (35 1 (:LINEAR EXPT-X->=-X))
 (35 1 (:LINEAR EXPT-X->-X))
 (29 29
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (27 15 (:REWRITE INTEGERP-MINUS-X))
 (27 9 (:REWRITE RTL::BVECP-EXACTP))
 (24 6 (:REWRITE RATIONALP-X))
 (21 21
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (18 18 (:TYPE-PRESCRIPTION RTL::BVECP))
 (15 15 (:REWRITE REDUCE-INTEGERP-+))
 (15 15 (:META META-INTEGERP-CORRECT))
 (11 11 (:REWRITE |(+ c (+ d x))|))
 (10 10
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (10 10 (:REWRITE DEFAULT-DIVIDE))
 (10 10 (:REWRITE |(< (+ c/d x) y)|))
 (10 10 (:REWRITE |(< (+ (- c) x) y)|))
 (10 5 (:REWRITE DEFAULT-EXPT-2))
 (9 9 (:REWRITE |(< y (+ (- c) x))|))
 (9 9 (:REWRITE |(< x (+ c/d y))|))
 (6 6 (:REWRITE REDUCE-RATIONALP-+))
 (6 6 (:REWRITE REDUCE-RATIONALP-*))
 (6 6 (:REWRITE RATIONALP-MINUS-X))
 (6 6 (:REWRITE FOLD-CONSTS-IN-+))
 (6 6 (:REWRITE |(- (* c x))|))
 (6 6 (:META META-RATIONALP-CORRECT))
 (5 5 (:REWRITE DEFAULT-EXPT-1))
 (5 5 (:REWRITE |(expt 1/c n)|))
 (5 5 (:REWRITE |(expt (- x) n)|))
 (5 5 (:REWRITE |(< (/ x) 0)|))
 (5 5 (:REWRITE |(< (* x y) 0)|))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (3 3 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (3 3
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (3 3
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (2 2 (:REWRITE ZP-OPEN))
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
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (2 2
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (2 2
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (2 2
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
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
 (2 2 (:REWRITE |(* c (* d x))|))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<))
 (1 1 (:LINEAR EXPT->=-1-TWO))
 (1 1 (:LINEAR EXPT->-1-TWO))
 (1 1 (:LINEAR EXPT-<=-1-ONE))
 (1 1 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-NEG-17
 (769 769
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (769 769
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (769 769
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (769 769
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (680 11 (:REWRITE RTL::R-EXACTP-6))
 (644
  644
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (644 644
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (644
     644
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (644 644
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (468 166 (:REWRITE DEFAULT-PLUS-2))
 (343 166 (:REWRITE DEFAULT-PLUS-1))
 (321 65
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (272 76 (:REWRITE DEFAULT-LESS-THAN-2))
 (261 61 (:REWRITE DEFAULT-TIMES-1))
 (181 61 (:REWRITE DEFAULT-TIMES-2))
 (174 76 (:REWRITE DEFAULT-LESS-THAN-1))
 (155 51 (:REWRITE SIMPLIFY-SUMS-<))
 (146 60 (:REWRITE DEFAULT-MINUS))
 (139 9 (:REWRITE ODD-EXPT-THM))
 (135 5
      (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (130 5
      (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (94 74 (:REWRITE |(< (- x) (- y))|))
 (92 74
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (76 76 (:REWRITE THE-FLOOR-BELOW))
 (76 76 (:REWRITE THE-FLOOR-ABOVE))
 (74 74
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (74 74
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (74 74
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (74 74 (:REWRITE INTEGERP-<-CONSTANT))
 (74 74 (:REWRITE CONSTANT-<-INTEGERP))
 (74 74
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (74 74
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (74 74
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (74 74
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (74 74 (:REWRITE |(< c (- x))|))
 (74 74
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (74 74
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (74 74
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (74 74 (:REWRITE |(< (/ x) (/ y))|))
 (74 74 (:REWRITE |(< (- x) c)|))
 (68 24 (:REWRITE RTL::BVECP-EXACTP))
 (66 66
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (45 45
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (45 25 (:REWRITE INTEGERP-MINUS-X))
 (44 44 (:TYPE-PRESCRIPTION RTL::BVECP))
 (41 2 (:LINEAR EXPT->=-1-ONE))
 (40 10 (:REWRITE RATIONALP-X))
 (40 2 (:LINEAR EXPT->-1-ONE))
 (36 2 (:LINEAR EXPT-X->=-X))
 (36 2 (:LINEAR EXPT-X->-X))
 (35 9 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (34 14 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (25 25 (:REWRITE REDUCE-INTEGERP-+))
 (25 25 (:META META-INTEGERP-CORRECT))
 (23 14 (:REWRITE DEFAULT-EXPT-2))
 (18 18 (:REWRITE |(< (+ c/d x) y)|))
 (18 18 (:REWRITE |(< (+ (- c) x) y)|))
 (16 16 (:REWRITE |(+ c (+ d x))|))
 (14 14
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (14 14 (:REWRITE DEFAULT-EXPT-1))
 (14 14 (:REWRITE DEFAULT-DIVIDE))
 (14 14 (:REWRITE |(expt 1/c n)|))
 (14 14 (:REWRITE |(expt (- x) n)|))
 (14 14 (:REWRITE |(- (* c x))|))
 (11 11 (:REWRITE FOLD-CONSTS-IN-+))
 (11 11 (:REWRITE |(< y (+ (- c) x))|))
 (11 11 (:REWRITE |(< x (+ c/d y))|))
 (10 10 (:REWRITE REDUCE-RATIONALP-+))
 (10 10 (:REWRITE REDUCE-RATIONALP-*))
 (10 10 (:REWRITE RATIONALP-MINUS-X))
 (10 10 (:META META-RATIONALP-CORRECT))
 (9 9 (:REWRITE |(< (/ x) 0)|))
 (9 9 (:REWRITE |(< (* x y) 0)|))
 (8 2 (:REWRITE |(integerp (- x))|))
 (6 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (6 4
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (6 4
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (5 5
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (5 5
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (5 5
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (5 5
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (4 4
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (4 4
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (4 4
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (4 4 (:REWRITE |(equal c (/ x))|))
 (4 4 (:REWRITE |(equal c (- x))|))
 (4 4 (:REWRITE |(equal (/ x) c)|))
 (4 4 (:REWRITE |(equal (/ x) (/ y))|))
 (4 4 (:REWRITE |(equal (- x) c)|))
 (4 4 (:REWRITE |(equal (- x) (- y))|))
 (4 4 (:REWRITE |(* c (* d x))|))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:REWRITE |(< 0 (* x y))|))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-NEG-18
 (102 102
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (102 102
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (102 102
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (102 102
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (70
  70
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (70 70
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (70 70
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (70 70
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (48 48 (:TYPE-PRESCRIPTION NOT-INTEGERP-4E))
 (48 48 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
 (48 48 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
 (48 48 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
 (41 2 (:LINEAR EXPT->=-1-ONE))
 (40 2 (:LINEAR EXPT->-1-ONE))
 (36 2 (:LINEAR EXPT-X->=-X))
 (36 2 (:LINEAR EXPT-X->-X))
 (12 6
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (12 6 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (10 6 (:REWRITE DEFAULT-LESS-THAN-2))
 (8 6 (:REWRITE DEFAULT-LESS-THAN-1))
 (6 6 (:REWRITE THE-FLOOR-BELOW))
 (6 6 (:REWRITE THE-FLOOR-ABOVE))
 (6 6 (:REWRITE SIMPLIFY-SUMS-<))
 (6 6 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (6 6
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (6 6
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (6 6 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
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
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (5 5
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (4 4 (:REWRITE |(< y (+ (- c) x))|))
 (4 4 (:REWRITE |(< x (+ c/d y))|))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (3 3 (:REWRITE DEFAULT-EXPT-2))
 (3 3 (:REWRITE DEFAULT-EXPT-1))
 (3 3 (:REWRITE |(expt 1/c n)|))
 (3 3 (:REWRITE |(expt (- x) n)|))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:REWRITE |(< 0 (* x y))|))
 (2 2 (:REWRITE |(< (/ x) 0)|))
 (2 2 (:REWRITE |(< (+ c/d x) y)|))
 (2 2 (:REWRITE |(< (+ (- c) x) y)|))
 (2 2 (:REWRITE |(< (* x y) 0)|))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-NEG-19
 (738
  738
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (738 738
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (738
     738
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (738 738
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (733 733
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (733 733
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (733 733
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (733 733
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (342 3 (:REWRITE RTL::R-EXACTP-6))
 (258 99 (:REWRITE DEFAULT-PLUS-2))
 (254 60
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (245 70 (:REWRITE DEFAULT-LESS-THAN-2))
 (202 99 (:REWRITE DEFAULT-PLUS-1))
 (132 70 (:REWRITE DEFAULT-LESS-THAN-1))
 (124 47 (:REWRITE SIMPLIFY-SUMS-<))
 (114 9 (:REWRITE ODD-EXPT-THM))
 (92 68
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (81 3
     (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (80 68 (:REWRITE |(< (- x) (- y))|))
 (78 3
     (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (70 70 (:REWRITE THE-FLOOR-BELOW))
 (70 70 (:REWRITE THE-FLOOR-ABOVE))
 (68 68
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (68 68
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (68 68
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (68 68 (:REWRITE INTEGERP-<-CONSTANT))
 (68 68 (:REWRITE CONSTANT-<-INTEGERP))
 (68 68
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (68 68
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (68 68
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (68 68
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (68 68 (:REWRITE |(< c (- x))|))
 (68 68
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (68 68
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (68 68
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (68 68 (:REWRITE |(< (/ x) (/ y))|))
 (68 68 (:REWRITE |(< (- x) c)|))
 (53 29 (:REWRITE DEFAULT-MINUS))
 (48 9 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (44 11 (:REWRITE RATIONALP-X))
 (41 2 (:LINEAR EXPT->=-1-ONE))
 (40 28 (:REWRITE INTEGERP-MINUS-X))
 (40 2 (:LINEAR EXPT->-1-ONE))
 (36 2 (:LINEAR EXPT-X->=-X))
 (36 2 (:LINEAR EXPT-X->-X))
 (33 11 (:REWRITE RTL::BVECP-EXACTP))
 (28 28 (:REWRITE REDUCE-INTEGERP-+))
 (28 28 (:META META-INTEGERP-CORRECT))
 (25 25
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (25 13 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (23 19 (:REWRITE DEFAULT-TIMES-2))
 (22 22 (:TYPE-PRESCRIPTION RTL::BVECP))
 (19 19 (:REWRITE DEFAULT-TIMES-1))
 (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-4E))
 (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
 (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
 (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
 (18 18 (:REWRITE |(< (+ c/d x) y)|))
 (18 18 (:REWRITE |(< (+ (- c) x) y)|))
 (15 15
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (13 10 (:REWRITE DEFAULT-EXPT-2))
 (12 3 (:REWRITE |(integerp (- x))|))
 (11 11 (:REWRITE REDUCE-RATIONALP-+))
 (11 11 (:REWRITE REDUCE-RATIONALP-*))
 (11 11 (:REWRITE RATIONALP-MINUS-X))
 (11 11 (:META META-RATIONALP-CORRECT))
 (10 10
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (10 10 (:REWRITE DEFAULT-EXPT-1))
 (10 10 (:REWRITE DEFAULT-DIVIDE))
 (10 10 (:REWRITE |(expt 1/c n)|))
 (10 10 (:REWRITE |(expt (- x) n)|))
 (10 10 (:REWRITE |(< y (+ (- c) x))|))
 (10 10 (:REWRITE |(< x (+ c/d y))|))
 (9 9 (:REWRITE |(< (/ x) 0)|))
 (9 9 (:REWRITE |(< (* x y) 0)|))
 (8 8
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (8 8
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (7 7 (:REWRITE |(- (* c x))|))
 (6 6 (:REWRITE |(+ c (+ d x))|))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (3 3 (:REWRITE ZP-OPEN))
 (3 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (3 3
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (3 3
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (3 3
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (3 3
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (3 3 (:REWRITE FOLD-CONSTS-IN-+))
 (3 3
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (3 3 (:REWRITE |(equal c (/ x))|))
 (3 3 (:REWRITE |(equal c (- x))|))
 (3 3 (:REWRITE |(equal (/ x) c)|))
 (3 3 (:REWRITE |(equal (/ x) (/ y))|))
 (3 3 (:REWRITE |(equal (- x) c)|))
 (3 3 (:REWRITE |(equal (- x) (- y))|))
 (3 3
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (3 3
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:REWRITE |(< 0 (* x y))|))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-NEG-20
 (13876
  13876
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (13876
      13876
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (13876
     13876
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (13876 13876
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (6289 1610 (:REWRITE DEFAULT-PLUS-2))
 (5053 5053
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (5053 5053
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (5053 5053
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (5053 5053
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (4419 1610 (:REWRITE DEFAULT-PLUS-1))
 (3406 630 (:REWRITE DEFAULT-TIMES-1))
 (3083 631 (:REWRITE DEFAULT-LESS-THAN-2))
 (2542 630 (:REWRITE DEFAULT-TIMES-2))
 (2071 76 (:REWRITE ODD-EXPT-THM))
 (1693 631 (:REWRITE DEFAULT-LESS-THAN-1))
 (1640 616
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (1501 390 (:REWRITE SIMPLIFY-SUMS-<))
 (1161 379 (:REWRITE DEFAULT-MINUS))
 (884 600 (:REWRITE |(< (- x) (- y))|))
 (834 194 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (768 600
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (702 26
      (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (680 600 (:REWRITE |(< c (- x))|))
 (676 26
      (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (660 600
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (631 631 (:REWRITE THE-FLOOR-BELOW))
 (631 631 (:REWRITE THE-FLOOR-ABOVE))
 (617 600 (:REWRITE |(< (/ x) (/ y))|))
 (616 616
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (616 616
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (600 600 (:REWRITE INTEGERP-<-CONSTANT))
 (600 600 (:REWRITE CONSTANT-<-INTEGERP))
 (600 600
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (600 600
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (600 600
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (600 600
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (600 600
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (600 600
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (600 600 (:REWRITE |(< (- x) c)|))
 (519 519
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (488 160 (:REWRITE |(< (+ (- c) x) y)|))
 (341 68
      (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (328 224 (:REWRITE INTEGERP-MINUS-X))
 (320 80 (:REWRITE RATIONALP-X))
 (297 99 (:REWRITE RTL::BVECP-EXACTP))
 (224 224 (:REWRITE REDUCE-INTEGERP-+))
 (224 224 (:META META-INTEGERP-CORRECT))
 (198 198 (:TYPE-PRESCRIPTION RTL::BVECP))
 (198 158 (:REWRITE |(+ c (+ d x))|))
 (180 110 (:REWRITE DEFAULT-EXPT-2))
 (160 160 (:REWRITE |(< (+ c/d x) y)|))
 (123 123 (:REWRITE |(< x (+ c/d y))|))
 (115 115 (:REWRITE |(< y (+ (- c) x))|))
 (110 110 (:REWRITE DEFAULT-EXPT-1))
 (110 110 (:REWRITE |(expt 1/c n)|))
 (110 110 (:REWRITE |(expt (- x) n)|))
 (97 97 (:REWRITE |(- (* c x))|))
 (88 88 (:REWRITE FOLD-CONSTS-IN-+))
 (84 21 (:REWRITE |(integerp (- x))|))
 (80 80 (:REWRITE REDUCE-RATIONALP-+))
 (80 80 (:REWRITE REDUCE-RATIONALP-*))
 (80 80 (:REWRITE RATIONALP-MINUS-X))
 (80 80 (:META META-RATIONALP-CORRECT))
 (78 78
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (78 78 (:REWRITE DEFAULT-DIVIDE))
 (55 55 (:REWRITE |(< (/ x) 0)|))
 (55 55 (:REWRITE |(< (* x y) 0)|))
 (44 44 (:REWRITE |(* c (* d x))|))
 (41 2 (:LINEAR EXPT->=-1-ONE))
 (40 2 (:LINEAR EXPT->-1-ONE))
 (36 2 (:LINEAR EXPT-X->=-X))
 (36 2 (:LINEAR EXPT-X->-X))
 (35 35 (:REWRITE |(< 0 (* x y))|))
 (27 27 (:REWRITE |(< 0 (/ x))|))
 (26 26
     (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (26 26
     (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (20 20 (:REWRITE ZP-OPEN))
 (20 20 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (20 20
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (20 20
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (20 20
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (20 20
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (20 20
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (20 20 (:REWRITE |(equal c (/ x))|))
 (20 20 (:REWRITE |(equal c (- x))|))
 (20 20 (:REWRITE |(equal (/ x) c)|))
 (20 20 (:REWRITE |(equal (/ x) (/ y))|))
 (20 20 (:REWRITE |(equal (- x) c)|))
 (20 20 (:REWRITE |(equal (- x) (- y))|))
 (18 18
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (18 18
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (11 11
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (11 11
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-NEG-25
 (3982
  3982
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (3982
      3982
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (3982
     3982
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (3982 3982
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (2197 2197
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (2197 2197
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (2197 2197
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (1259 302 (:REWRITE DEFAULT-PLUS-2))
 (965 157
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (898 302 (:REWRITE DEFAULT-PLUS-1))
 (697 206 (:REWRITE DEFAULT-LESS-THAN-2))
 (651 8 (:REWRITE RTL::R-EXACTP-6))
 (610 206 (:REWRITE DEFAULT-LESS-THAN-1))
 (483 120 (:REWRITE SIMPLIFY-SUMS-<))
 (298 202
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (267 202 (:REWRITE |(< (/ x) (/ y))|))
 (251 202 (:REWRITE |(< (- x) (- y))|))
 (247 202
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (225 89 (:REWRITE DEFAULT-MINUS))
 (224 19 (:REWRITE ODD-EXPT-THM))
 (212 59 (:REWRITE DEFAULT-TIMES-2))
 (209 59 (:REWRITE DEFAULT-TIMES-1))
 (206 206 (:REWRITE THE-FLOOR-BELOW))
 (206 206 (:REWRITE THE-FLOOR-ABOVE))
 (202 202
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (202 202
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (202 202
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (202 202 (:REWRITE INTEGERP-<-CONSTANT))
 (202 202 (:REWRITE CONSTANT-<-INTEGERP))
 (202 202
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (202 202
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (202 202
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (202 202 (:REWRITE |(< c (- x))|))
 (202 202
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (202 202
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (202 202
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (202 202 (:REWRITE |(< (- x) c)|))
 (150 37 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (143 3
      (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (143 3
      (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (143 3 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (143 3 (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (135 5
      (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (130 5
      (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (111 37 (:REWRITE RTL::BVECP-EXACTP))
 (110 19
      (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (108 88 (:REWRITE INTEGERP-MINUS-X))
 (96 96
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (88 88 (:REWRITE REDUCE-INTEGERP-+))
 (88 88 (:META META-INTEGERP-CORRECT))
 (88 25 (:REWRITE DEFAULT-DIVIDE))
 (88 22 (:REWRITE RATIONALP-X))
 (74 74 (:TYPE-PRESCRIPTION RTL::BVECP))
 (47 47
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (46 46 (:REWRITE |(< (+ c/d x) y)|))
 (46 46 (:REWRITE |(< (+ (- c) x) y)|))
 (43 35 (:REWRITE DEFAULT-EXPT-2))
 (41 2 (:LINEAR EXPT->=-1-ONE))
 (40 2 (:LINEAR EXPT->-1-ONE))
 (36 2 (:LINEAR EXPT-X->=-X))
 (36 2 (:LINEAR EXPT-X->-X))
 (35 35 (:REWRITE DEFAULT-EXPT-1))
 (35 35 (:REWRITE |(expt 1/c n)|))
 (35 35 (:REWRITE |(expt (- x) n)|))
 (28 7 (:REWRITE |(integerp (- x))|))
 (27 27 (:REWRITE |(< y (+ (- c) x))|))
 (27 27 (:REWRITE |(< x (+ c/d y))|))
 (25 25
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (23 23 (:REWRITE |(< (/ x) 0)|))
 (23 23 (:REWRITE |(< (* x y) 0)|))
 (22 22 (:REWRITE REDUCE-RATIONALP-+))
 (22 22 (:REWRITE REDUCE-RATIONALP-*))
 (22 22 (:REWRITE RATIONALP-MINUS-X))
 (22 22 (:META META-RATIONALP-CORRECT))
 (18 18 (:REWRITE |(- (* c x))|))
 (17 17 (:REWRITE |(+ c (+ d x))|))
 (11 11
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (11 11
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (9 9 (:REWRITE FOLD-CONSTS-IN-+))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (8 8 (:REWRITE |(< 0 (/ x))|))
 (8 8 (:REWRITE |(< 0 (* x y))|))
 (6 6 (:REWRITE ZP-OPEN))
 (6 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (6 6
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (6 6
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (6 6
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (6 6
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (6 6
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (6 6 (:REWRITE |(equal c (/ x))|))
 (6 6 (:REWRITE |(equal c (- x))|))
 (6 6 (:REWRITE |(equal (/ x) c)|))
 (6 6 (:REWRITE |(equal (/ x) (/ y))|))
 (6 6 (:REWRITE |(equal (- x) c)|))
 (6 6 (:REWRITE |(equal (- x) (- y))|))
 (5 5
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (5 5
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (3 3 (:REWRITE |(* c (* d x))|))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-NEG-26
 (9557
  9557
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (9557
      9557
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (9557
     9557
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (9557 9557
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (4073 1237 (:REWRITE DEFAULT-PLUS-2))
 (2785 1237 (:REWRITE DEFAULT-PLUS-1))
 (2413 449 (:REWRITE DEFAULT-LESS-THAN-2))
 (2226 458 (:REWRITE DEFAULT-TIMES-2))
 (1503 71 (:REWRITE ODD-EXPT-THM))
 (1326 430
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (1222 458 (:REWRITE DEFAULT-TIMES-1))
 (976 277 (:REWRITE SIMPLIFY-SUMS-<))
 (834 449 (:REWRITE DEFAULT-LESS-THAN-1))
 (730 304 (:REWRITE DEFAULT-MINUS))
 (580 163 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (556 416 (:REWRITE |(< c (- x))|))
 (539 416 (:REWRITE |(< (- x) (- y))|))
 (500 416
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (476 416 (:REWRITE |(< (- x) c)|))
 (449 449 (:REWRITE THE-FLOOR-BELOW))
 (449 449 (:REWRITE THE-FLOOR-ABOVE))
 (430 430
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (430 430
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (429 416 (:REWRITE |(< (/ x) (/ y))|))
 (425 138 (:REWRITE |(< (+ (- c) x) y)|))
 (416 416 (:REWRITE INTEGERP-<-CONSTANT))
 (416 416 (:REWRITE CONSTANT-<-INTEGERP))
 (416 416
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (416 416
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (416 416
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (416 416
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (416 416
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (416 416
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (416 416
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (401 401 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (380 380
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (363 64
      (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (294 98 (:REWRITE RTL::BVECP-EXACTP))
 (224 56 (:REWRITE RATIONALP-X))
 (196 196 (:TYPE-PRESCRIPTION RTL::BVECP))
 (148 148 (:REWRITE REDUCE-INTEGERP-+))
 (148 148 (:REWRITE INTEGERP-MINUS-X))
 (148 148 (:META META-INTEGERP-CORRECT))
 (138 138 (:REWRITE |(< (+ c/d x) y)|))
 (135 100 (:REWRITE |(+ c (+ d x))|))
 (121 88 (:REWRITE DEFAULT-EXPT-2))
 (114 114
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (114 114
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (114 114
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (114 114
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (101 101 (:REWRITE |(< x (+ c/d y))|))
 (94 94 (:REWRITE |(< y (+ (- c) x))|))
 (92 23 (:REWRITE |(integerp (- x))|))
 (88 88 (:REWRITE DEFAULT-EXPT-1))
 (88 88 (:REWRITE |(expt 1/c n)|))
 (88 88 (:REWRITE |(expt (- x) n)|))
 (56 56 (:REWRITE REDUCE-RATIONALP-+))
 (56 56 (:REWRITE REDUCE-RATIONALP-*))
 (56 56 (:REWRITE RATIONALP-MINUS-X))
 (56 56 (:META META-RATIONALP-CORRECT))
 (47 47 (:REWRITE FOLD-CONSTS-IN-+))
 (47 47 (:REWRITE |(< (/ x) 0)|))
 (47 47 (:REWRITE |(< (* x y) 0)|))
 (41 2 (:LINEAR EXPT->=-1-ONE))
 (40 2 (:LINEAR EXPT->-1-ONE))
 (36 2 (:LINEAR EXPT-X->=-X))
 (36 2 (:LINEAR EXPT-X->-X))
 (33 33 (:REWRITE |(- (* c x))|))
 (29 29 (:REWRITE |(< 0 (* x y))|))
 (22 22 (:REWRITE |(< 0 (/ x))|))
 (17 17 (:REWRITE ZP-OPEN))
 (17 17 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (17 17
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (17 17
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (17 17
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (17 17
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (17 17
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (17 17 (:REWRITE |(equal c (/ x))|))
 (17 17 (:REWRITE |(equal c (- x))|))
 (17 17 (:REWRITE |(equal (/ x) c)|))
 (17 17 (:REWRITE |(equal (/ x) (/ y))|))
 (17 17 (:REWRITE |(equal (- x) c)|))
 (17 17 (:REWRITE |(equal (- x) (- y))|))
 (14 14
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (14 14
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (11 11
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (11 11
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-NEG-28)
(RTL::R-NEG-29
 (13716
  13716
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (13716
      13716
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (13716
     13716
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (13716 13716
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (11549 1181
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (7815 2338 (:REWRITE DEFAULT-PLUS-2))
 (6551 6551
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (6551 6551
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (6551 6551
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (6551 6551
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (5219 2338 (:REWRITE DEFAULT-PLUS-1))
 (4760 965
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (4490 29
       (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (4485 29
       (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (3759 1204 (:REWRITE DEFAULT-LESS-THAN-2))
 (3248 1204 (:REWRITE DEFAULT-LESS-THAN-1))
 (2524 703 (:REWRITE SIMPLIFY-SUMS-<))
 (2513 543 (:REWRITE DEFAULT-TIMES-2))
 (2365 34 (:LINEAR EXPT->=-1-ONE))
 (2093 543 (:REWRITE DEFAULT-TIMES-1))
 (2060 34 (:LINEAR EXPT->-1-ONE))
 (1776 34 (:LINEAR EXPT-X->=-X))
 (1776 34 (:LINEAR EXPT-X->-X))
 (1579 1037 (:REWRITE |(< (- x) (- y))|))
 (1428 294 (:REWRITE |(< (+ (- c) x) y)|))
 (1362 228 (:REWRITE |(< y (+ (- c) x))|))
 (1305 29
       (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (1305 29
       (:REWRITE |(< x (/ y)) with (< y 0)|))
 (1295 97 (:REWRITE ODD-EXPT-THM))
 (1245 1037 (:REWRITE |(< (- x) c)|))
 (1241 1037
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (1204 1204 (:REWRITE THE-FLOOR-BELOW))
 (1204 1204 (:REWRITE THE-FLOOR-ABOVE))
 (1181 1181
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (1181 1181
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (1149 426 (:REWRITE DEFAULT-MINUS))
 (1066 1037 (:REWRITE |(< (/ x) (/ y))|))
 (1037 1037
       (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (1037 1037
       (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (1037 1037
       (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (1037 1037
       (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (1037 1037 (:REWRITE |(< c (- x))|))
 (1037 1037
       (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (1037 1037
       (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (1037 1037
       (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (1033 1033 (:REWRITE INTEGERP-<-CONSTANT))
 (1033 1033 (:REWRITE CONSTANT-<-INTEGERP))
 (1026 38
       (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (988 38
      (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (833 401 (:REWRITE |(+ c (+ d x))|))
 (804 262 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (689 689
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (485 122 (:REWRITE RATIONALP-X))
 (473 97
      (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (438 286 (:REWRITE INTEGERP-MINUS-X))
 (351 351
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (351 117 (:REWRITE RTL::BVECP-EXACTP))
 (326 326 (:REWRITE |(< (+ c/d x) y)|))
 (286 286 (:REWRITE REDUCE-INTEGERP-+))
 (286 286 (:META META-INTEGERP-CORRECT))
 (284 284 (:REWRITE |(< x (+ c/d y))|))
 (234 234 (:TYPE-PRESCRIPTION RTL::BVECP))
 (229 162 (:REWRITE DEFAULT-EXPT-2))
 (162 162 (:REWRITE DEFAULT-EXPT-1))
 (162 162 (:REWRITE |(expt 1/c n)|))
 (162 162 (:REWRITE |(expt (- x) n)|))
 (154 154 (:REWRITE |(< (* x y) 0)|))
 (151 151 (:REWRITE FOLD-CONSTS-IN-+))
 (143 143
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (143 143 (:REWRITE DEFAULT-DIVIDE))
 (122 122 (:REWRITE REDUCE-RATIONALP-+))
 (122 122 (:REWRITE REDUCE-RATIONALP-*))
 (122 122 (:REWRITE RATIONALP-MINUS-X))
 (122 122 (:REWRITE |(< (/ x) 0)|))
 (122 122 (:META META-RATIONALP-CORRECT))
 (112 28 (:REWRITE |(integerp (- x))|))
 (109 109 (:REWRITE |(- (* c x))|))
 (106 106 (:REWRITE |(< 0 (* x y))|))
 (78 78 (:REWRITE |(< 0 (/ x))|))
 (68 68
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (68 68
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (68 68
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (68 68
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (59 59 (:REWRITE |(* c (* d x))|))
 (50 50
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (50 50
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (50 50
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (50 50
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (38 38
     (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (38 38
     (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (34 34 (:LINEAR EXPT-LINEAR-UPPER-<))
 (34 34 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (34 34 (:LINEAR EXPT-LINEAR-LOWER-<))
 (34 34 (:LINEAR EXPT->=-1-TWO))
 (34 34 (:LINEAR EXPT->-1-TWO))
 (34 34 (:LINEAR EXPT-<=-1-ONE))
 (34 34 (:LINEAR EXPT-<-1-ONE))
 (31 31 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (31 31
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (31 31
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (31 31
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (31 31
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (31 31
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (31 31 (:REWRITE |(equal c (/ x))|))
 (31 31 (:REWRITE |(equal c (- x))|))
 (31 31 (:REWRITE |(equal (/ x) c)|))
 (31 31 (:REWRITE |(equal (/ x) (/ y))|))
 (31 31 (:REWRITE |(equal (- x) c)|))
 (31 31 (:REWRITE |(equal (- x) (- y))|))
 (30 30 (:REWRITE ZP-OPEN))
 (11 11
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (11 11
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1)))
(RTL::R-NEG-30)
(RTL::R-NEG-31
 (3348
  3348
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (3348
      3348
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (3348
     3348
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (3348 3348
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1659 211
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (1525 1525
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (1525 1525
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (1525 1525
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (1525 1525
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (1462 481 (:REWRITE DEFAULT-PLUS-2))
 (1080 24 (:REWRITE RTL::R-EXACTP-6))
 (1011 481 (:REWRITE DEFAULT-PLUS-1))
 (817 177
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (680 216 (:REWRITE DEFAULT-LESS-THAN-2))
 (678 170 (:REWRITE DEFAULT-TIMES-2))
 (634 170 (:REWRITE DEFAULT-TIMES-1))
 (592 216 (:REWRITE DEFAULT-LESS-THAN-1))
 (471 134 (:REWRITE SIMPLIFY-SUMS-<))
 (333 6 (:LINEAR EXPT->=-1-ONE))
 (328 6 (:LINEAR EXPT->-1-ONE))
 (284 6 (:LINEAR EXPT-X->=-X))
 (284 6 (:LINEAR EXPT-X->-X))
 (279 191 (:REWRITE |(< (- x) (- y))|))
 (249 189 (:REWRITE |(< (- x) c)|))
 (246 100 (:REWRITE DEFAULT-MINUS))
 (233 191
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (232 17 (:REWRITE ODD-EXPT-THM))
 (225 191
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (216 216 (:REWRITE THE-FLOOR-BELOW))
 (216 216 (:REWRITE THE-FLOOR-ABOVE))
 (216 8
      (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (212 50 (:REWRITE |(< (+ (- c) x) y)|))
 (211 211
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (211 211
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (208 8
      (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (202 40 (:REWRITE |(< y (+ (- c) x))|))
 (198 191 (:REWRITE |(< (/ x) (/ y))|))
 (191 191
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (191 191
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (191 191
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (191 191
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (191 191
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (191 191
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (189 189 (:REWRITE INTEGERP-<-CONSTANT))
 (189 189 (:REWRITE CONSTANT-<-INTEGERP))
 (189 189 (:REWRITE |(< c (- x))|))
 (187 55 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (156 156
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (133 73 (:REWRITE |(+ c (+ d x))|))
 (100 25 (:REWRITE RATIONALP-X))
 (90 3
     (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (90 3
     (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (90 3 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (90 3 (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (86 58 (:REWRITE INTEGERP-MINUS-X))
 (83 18
     (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (69 58 (:REWRITE REDUCE-INTEGERP-+))
 (66 22 (:REWRITE RTL::BVECP-EXACTP))
 (65 41 (:REWRITE DEFAULT-EXPT-2))
 (58 58 (:META META-INTEGERP-CORRECT))
 (54 54 (:REWRITE |(< (+ c/d x) y)|))
 (48 48 (:REWRITE |(< x (+ c/d y))|))
 (44 44 (:TYPE-PRESCRIPTION RTL::BVECP))
 (41 41 (:REWRITE DEFAULT-EXPT-1))
 (41 41 (:REWRITE |(expt 1/c n)|))
 (41 41 (:REWRITE |(expt (- x) n)|))
 (36 36 (:REWRITE FOLD-CONSTS-IN-+))
 (30 30 (:REWRITE DEFAULT-DIVIDE))
 (28 28
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (26 26 (:REWRITE |(< (* x y) 0)|))
 (25 25 (:REWRITE REDUCE-RATIONALP-+))
 (25 25 (:REWRITE REDUCE-RATIONALP-*))
 (25 25 (:REWRITE RATIONALP-MINUS-X))
 (25 25 (:META META-RATIONALP-CORRECT))
 (24 24 (:REWRITE |(- (* c x))|))
 (24 24 (:REWRITE |(* c (* d x))|))
 (22 22 (:REWRITE |(< (/ x) 0)|))
 (21 21 (:REWRITE |(< 0 (* x y))|))
 (20 5 (:REWRITE |(integerp (- x))|))
 (12 12
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (12 12
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (12 12
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (12 12
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (11 11
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (11 11
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (8 8
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (8 8
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (8 8
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (8 8
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (7 7 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (7 7
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (7 7
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (7 7
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (7 7
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (7 7
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (7 7 (:REWRITE |(equal c (/ x))|))
 (7 7 (:REWRITE |(equal c (- x))|))
 (7 7 (:REWRITE |(equal (/ x) c)|))
 (7 7 (:REWRITE |(equal (/ x) (/ y))|))
 (7 7 (:REWRITE |(equal (- x) c)|))
 (7 7 (:REWRITE |(equal (- x) (- y))|))
 (7 7 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (7 7 (:LINEAR EXPT-LINEAR-LOWER-<))
 (6 6 (:REWRITE ZP-OPEN))
 (6 6 (:LINEAR EXPT-LINEAR-UPPER-<))
 (6 6 (:LINEAR EXPT->=-1-TWO))
 (6 6 (:LINEAR EXPT->-1-TWO))
 (6 6 (:LINEAR EXPT-<=-1-ONE))
 (6 6 (:LINEAR EXPT-<-1-ONE))
 (5 5
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (5 5
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (5 5
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RTL::R-NEG-32)
(RTL::R-NEG-33
 (1488
  1488
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1488
      1488
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1488
     1488
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1488 1488
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (975 975
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (975 975
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (975 975
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (975 975
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (652 13 (:REWRITE RTL::R-EXACTP-6))
 (576 230 (:REWRITE DEFAULT-PLUS-2))
 (449 92
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (431 230 (:REWRITE DEFAULT-PLUS-1))
 (424 105 (:REWRITE DEFAULT-LESS-THAN-2))
 (358 106 (:REWRITE DEFAULT-TIMES-1))
 (330 106 (:REWRITE DEFAULT-TIMES-2))
 (222 70 (:REWRITE SIMPLIFY-SUMS-<))
 (207 105 (:REWRITE DEFAULT-LESS-THAN-1))
 (188 16 (:REWRITE ODD-EXPT-THM))
 (137 68 (:REWRITE DEFAULT-MINUS))
 (135 5
      (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (132 102
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (130 5
      (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (122 102 (:REWRITE |(< (- x) (- y))|))
 (105 105 (:REWRITE THE-FLOOR-BELOW))
 (105 105 (:REWRITE THE-FLOOR-ABOVE))
 (102 102
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (102 102
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (102 102
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (102 102 (:REWRITE INTEGERP-<-CONSTANT))
 (102 102 (:REWRITE CONSTANT-<-INTEGERP))
 (102 102
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (102 102
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (102 102
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (102 102
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (102 102 (:REWRITE |(< c (- x))|))
 (102 102
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (102 102
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (102 102
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (102 102 (:REWRITE |(< (/ x) (/ y))|))
 (102 102 (:REWRITE |(< (- x) c)|))
 (76 76
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (70 28 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (68 16
     (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (64 16 (:REWRITE RATIONALP-X))
 (62 42 (:REWRITE INTEGERP-MINUS-X))
 (45 15 (:REWRITE RTL::BVECP-EXACTP))
 (42 42 (:REWRITE REDUCE-INTEGERP-+))
 (42 42 (:META META-INTEGERP-CORRECT))
 (41 2 (:LINEAR EXPT->=-1-ONE))
 (40 2 (:LINEAR EXPT->-1-ONE))
 (36 2 (:LINEAR EXPT-X->=-X))
 (36 2 (:LINEAR EXPT-X->-X))
 (32 20 (:REWRITE DEFAULT-EXPT-2))
 (30 30 (:TYPE-PRESCRIPTION RTL::BVECP))
 (28 28 (:REWRITE |(< (+ c/d x) y)|))
 (28 28 (:REWRITE |(< (+ (- c) x) y)|))
 (21 21 (:REWRITE |(+ c (+ d x))|))
 (20 20 (:REWRITE DEFAULT-EXPT-1))
 (20 20 (:REWRITE |(expt 1/c n)|))
 (20 20 (:REWRITE |(expt (- x) n)|))
 (17 17 (:REWRITE |(- (* c x))|))
 (16 16 (:REWRITE REDUCE-RATIONALP-+))
 (16 16 (:REWRITE REDUCE-RATIONALP-*))
 (16 16 (:REWRITE RATIONALP-MINUS-X))
 (16 16 (:REWRITE |(< y (+ (- c) x))|))
 (16 16 (:REWRITE |(< x (+ c/d y))|))
 (16 16 (:META META-RATIONALP-CORRECT))
 (16 4 (:REWRITE |(integerp (- x))|))
 (15 15
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (15 15 (:REWRITE DEFAULT-DIVIDE))
 (13 13 (:REWRITE FOLD-CONSTS-IN-+))
 (12 12 (:REWRITE |(< (/ x) 0)|))
 (12 12 (:REWRITE |(< (* x y) 0)|))
 (11 11 (:REWRITE |(* c (* d x))|))
 (8 8
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (8 8
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (5 5
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (5 5
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (4 4 (:REWRITE ZP-OPEN))
 (4 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (4 4
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (4 4
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (4 4
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (4 4
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (4 4
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (4 4 (:REWRITE |(equal c (/ x))|))
 (4 4 (:REWRITE |(equal c (- x))|))
 (4 4 (:REWRITE |(equal (/ x) c)|))
 (4 4 (:REWRITE |(equal (/ x) (/ y))|))
 (4 4 (:REWRITE |(equal (- x) c)|))
 (4 4 (:REWRITE |(equal (- x) (- y))|))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:REWRITE |(< 0 (* x y))|))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-NEG-34
 (4704
  4704
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (4704
      4704
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (4704
     4704
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (4704 4704
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (3658 3658
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (3658 3658
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (3658 3658
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (3658 3658
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (1995 731 (:REWRITE DEFAULT-PLUS-2))
 (1707 21 (:REWRITE RTL::R-EXACTP-6))
 (1533 731 (:REWRITE DEFAULT-PLUS-1))
 (1525 430 (:REWRITE DEFAULT-LESS-THAN-2))
 (756 430 (:REWRITE DEFAULT-LESS-THAN-1))
 (639 55 (:REWRITE ODD-EXPT-THM))
 (597 417
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (513 417 (:REWRITE |(< (- x) (- y))|))
 (430 430 (:REWRITE THE-FLOOR-BELOW))
 (430 430 (:REWRITE THE-FLOOR-ABOVE))
 (419 419
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (419 419
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (419 419
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (417 417 (:REWRITE INTEGERP-<-CONSTANT))
 (417 417 (:REWRITE CONSTANT-<-INTEGERP))
 (417 417
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (417 417
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (417 417
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (417 417
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (417 417 (:REWRITE |(< c (- x))|))
 (417 417
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (417 417
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (417 417
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (417 417 (:REWRITE |(< (/ x) (/ y))|))
 (417 417 (:REWRITE |(< (- x) c)|))
 (378 14
      (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (364 14
      (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (340 188 (:REWRITE DEFAULT-MINUS))
 (315 55
      (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (222 74 (:REWRITE RTL::BVECP-EXACTP))
 (215 159 (:REWRITE INTEGERP-MINUS-X))
 (195 195
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (191 95 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (176 44 (:REWRITE RATIONALP-X))
 (159 159 (:REWRITE REDUCE-INTEGERP-+))
 (159 159 (:META META-INTEGERP-CORRECT))
 (150 150 (:REWRITE DEFAULT-TIMES-2))
 (150 150 (:REWRITE DEFAULT-TIMES-1))
 (148 148 (:TYPE-PRESCRIPTION RTL::BVECP))
 (110 110 (:REWRITE |(< (+ c/d x) y)|))
 (110 110 (:REWRITE |(< (+ (- c) x) y)|))
 (103 103
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (80 20 (:REWRITE |(integerp (- x))|))
 (70 51 (:REWRITE DEFAULT-EXPT-2))
 (55 55 (:REWRITE |(+ c (+ d x))|))
 (52 52 (:REWRITE |(< y (+ (- c) x))|))
 (52 52 (:REWRITE |(< x (+ c/d y))|))
 (52 52 (:REWRITE |(- (* c x))|))
 (51 51 (:REWRITE DEFAULT-EXPT-1))
 (51 51 (:REWRITE |(expt 1/c n)|))
 (51 51 (:REWRITE |(expt (- x) n)|))
 (46 46
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (46 46 (:REWRITE DEFAULT-DIVIDE))
 (45 45 (:REWRITE |(< (/ x) 0)|))
 (45 45 (:REWRITE |(< (* x y) 0)|))
 (44 44 (:REWRITE REDUCE-RATIONALP-+))
 (44 44 (:REWRITE REDUCE-RATIONALP-*))
 (44 44 (:REWRITE RATIONALP-MINUS-X))
 (44 44 (:META META-RATIONALP-CORRECT))
 (41 2 (:LINEAR EXPT->=-1-ONE))
 (40 2 (:LINEAR EXPT->-1-ONE))
 (36 2 (:LINEAR EXPT-X->=-X))
 (36 2 (:LINEAR EXPT-X->-X))
 (31 31 (:REWRITE FOLD-CONSTS-IN-+))
 (15 13 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (15 13
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (15 13
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (14 14
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (14 14
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (14 14
     (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (14 14
     (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (13 13
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (13 13
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (13 13
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (13 13 (:REWRITE |(equal c (/ x))|))
 (13 13 (:REWRITE |(equal c (- x))|))
 (13 13 (:REWRITE |(equal (/ x) c)|))
 (13 13 (:REWRITE |(equal (/ x) (/ y))|))
 (13 13 (:REWRITE |(equal (- x) c)|))
 (13 13 (:REWRITE |(equal (- x) (- y))|))
 (12 12 (:REWRITE ZP-OPEN))
 (7 7 (:REWRITE |(< 0 (* x y))|))
 (5 5 (:REWRITE |(< 0 (/ x))|))
 (5 5 (:REWRITE |(* c (* d x))|))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2
    (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (2 2
    (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (2 2 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-NEG-DIRECTED
 (2380265 7071 (:REWRITE RTL::R-EXACTP-6))
 (1637137 84881
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (1248923
  1248923
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1248923
      1248923
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1248923
     1248923
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1248923 1248923
          (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (814014 250788 (:REWRITE DEFAULT-PLUS-2))
 (651302 651302
         (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (651302 651302
         (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (651302 651302
         (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (651302 651302
         (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (531314 250788 (:REWRITE DEFAULT-PLUS-1))
 (311075 2152 (:LINEAR EXPT->=-1-ONE))
 (306782 2152 (:LINEAR EXPT->-1-ONE))
 (263882 2152 (:LINEAR EXPT-X->=-X))
 (263882 2152 (:LINEAR EXPT-X->-X))
 (260343 61926
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (237276 85591 (:REWRITE DEFAULT-LESS-THAN-2))
 (199338 25674 (:REWRITE |(< y (+ (- c) x))|))
 (197392 23728 (:REWRITE |(< (+ (- c) x) y)|))
 (172913 85591 (:REWRITE DEFAULT-LESS-THAN-1))
 (120444 56124 (:REWRITE |(+ c (+ d x))|))
 (90297 63441 (:REWRITE |(< (- x) (- y))|))
 (85591 85591 (:REWRITE THE-FLOOR-BELOW))
 (85591 85591 (:REWRITE THE-FLOOR-ABOVE))
 (84881 84881
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (84881 84881
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (83024 26932 (:REWRITE DEFAULT-MINUS))
 (75379 75379
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (74141 63441 (:REWRITE |(< (- x) c)|))
 (73521 25695 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (73359 63441
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (72171 63441 (:REWRITE |(< c (- x))|))
 (63441 63441 (:REWRITE INTEGERP-<-CONSTANT))
 (63441 63441 (:REWRITE CONSTANT-<-INTEGERP))
 (63441 63441
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (63441 63441
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (63441 63441
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (63441 63441
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (63441 63441
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (63441 63441
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (63441 63441
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (63441 63441 (:REWRITE |(< (/ x) (/ y))|))
 (49913 3778 (:REWRITE ODD-EXPT-THM))
 (38448 1424
        (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (37024 1424
        (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (34250 34250 (:REWRITE |(< x (+ c/d y))|))
 (28016 28016 (:REWRITE |(< (+ c/d x) y)|))
 (27622 27622 (:REWRITE DEFAULT-TIMES-2))
 (27622 27622 (:REWRITE DEFAULT-TIMES-1))
 (26203 26203 (:REWRITE FOLD-CONSTS-IN-+))
 (19822 2872
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (19740 4935 (:REWRITE RATIONALP-X))
 (19079 3778
        (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (17715 12019 (:REWRITE INTEGERP-MINUS-X))
 (17192 17192
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (16431 5477 (:REWRITE RTL::BVECP-EXACTP))
 (15743 8698 (:REWRITE DEFAULT-EXPT-2))
 (12019 12019 (:REWRITE REDUCE-INTEGERP-+))
 (12019 12019 (:META META-INTEGERP-CORRECT))
 (10954 10954 (:TYPE-PRESCRIPTION RTL::BVECP))
 (9563 9563 (:REWRITE |(< 0 (* x y))|))
 (8698 8698 (:REWRITE DEFAULT-EXPT-1))
 (8698 8698 (:REWRITE |(expt 1/c n)|))
 (8698 8698 (:REWRITE |(expt (- x) n)|))
 (7434 7434 (:REWRITE |(< (* x y) 0)|))
 (7240 7240 (:REWRITE |(- (* c x))|))
 (5377 3039 (:REWRITE |(equal (/ x) c)|))
 (5284 5284 (:REWRITE DEFAULT-DIVIDE))
 (5275 5275 (:REWRITE |(< 0 (/ x))|))
 (5117 5117
       (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (4935 4935 (:REWRITE REDUCE-RATIONALP-+))
 (4935 4935 (:REWRITE REDUCE-RATIONALP-*))
 (4935 4935 (:REWRITE RATIONALP-MINUS-X))
 (4935 4935 (:META META-RATIONALP-CORRECT))
 (4708 1177 (:REWRITE |(integerp (- x))|))
 (4304 4304
       (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4304 4304
       (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4304 4304
       (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4304 4304
       (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (3146 3146 (:REWRITE |(< (/ x) 0)|))
 (3039 3039
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (3039 3039
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (3039 3039 (:REWRITE |(equal c (/ x))|))
 (3039 3039 (:REWRITE |(equal (/ x) (/ y))|))
 (3039 3039 (:REWRITE |(equal (- x) (- y))|))
 (2872 2872
       (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (2872 2872 (:REWRITE |(equal c (- x))|))
 (2872 2872 (:REWRITE |(equal (- x) c)|))
 (2152 2152 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2152 2152 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2152 2152 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2152 2152 (:LINEAR EXPT->=-1-TWO))
 (2152 2152 (:LINEAR EXPT->-1-TWO))
 (2152 2152 (:LINEAR EXPT-<=-1-ONE))
 (2152 2152 (:LINEAR EXPT-<-1-ONE))
 (2086 2086 (:REWRITE |(* c (* d x))|))
 (1637 1637 (:REWRITE ZP-OPEN))
 (1424 1424
       (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (1424 1424
       (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (700 700 (:REWRITE |(equal (+ (- c) x) y)|))
 (545 545 (:REWRITE RTL::RAZ-NEG-BITS))
 (167 167
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (167 167 (:REWRITE |(not (equal x (/ y)))|))
 (167 167 (:REWRITE |(equal x (/ y))|))
 (167 167 (:REWRITE |(/ (/ x))|))
 (155 155 (:REWRITE RTL::RTZ-NEG-BITS))
 (113 113
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (113 113
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (102 4 (:LINEAR RTL::RTZ-NEGATIVE))
 (102 4 (:LINEAR RTL::RAZ-NEGATIVE))
 (46 46
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (46 46
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (32 32
     (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (32 32
     (:REWRITE |(< (* x (/ y)) 0) rationalp (* x (/ y))|))
 (13 13 (:REWRITE |(equal (expt 2 n) c)|))
 (11 11
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (11 11
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1)))
(RTL::NOT-MIDPOINT-DOWN-1
 (699 139 (:REWRITE DEFAULT-PLUS-2))
 (613
  613
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (613 613
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (613
     613
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (613 613
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (613 613
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (613 613
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (532 532
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (532 532
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (532 532
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (532 532
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (399 8 (:REWRITE RTL::R-EXACTP-6))
 (382 139 (:REWRITE DEFAULT-PLUS-1))
 (263 51
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (212 60 (:REWRITE DEFAULT-LESS-THAN-2))
 (167 1
      (:REWRITE EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (166 60 (:REWRITE DEFAULT-LESS-THAN-1))
 (165 1
      (:REWRITE EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (157 4 (:REWRITE ODD-EXPT-THM))
 (92 60 (:REWRITE |(< (- x) (- y))|))
 (81 3
     (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (78 60
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (78 3
     (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (75 21 (:REWRITE DEFAULT-MINUS))
 (68 22 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (60 60 (:REWRITE THE-FLOOR-BELOW))
 (60 60 (:REWRITE THE-FLOOR-ABOVE))
 (60 60
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (60 60
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (60 60
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (60 60 (:REWRITE INTEGERP-<-CONSTANT))
 (60 60 (:REWRITE CONSTANT-<-INTEGERP))
 (60 60
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (60 60
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (60 60
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (60 60
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (60 60 (:REWRITE |(< c (- x))|))
 (60 60
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (60 60
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (60 60
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (60 60 (:REWRITE |(< (/ x) (/ y))|))
 (60 60 (:REWRITE |(< (- x) c)|))
 (40 1 (:LINEAR EXPT->=-1-ONE))
 (40 1 (:LINEAR EXPT-<=-1-TWO))
 (39 1 (:LINEAR EXPT->-1-ONE))
 (39 1 (:LINEAR EXPT-<-1-TWO))
 (35 1 (:LINEAR EXPT-X->=-X))
 (35 1 (:LINEAR EXPT-X->-X))
 (33 33
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (27 15 (:REWRITE INTEGERP-MINUS-X))
 (27 9 (:REWRITE RTL::BVECP-EXACTP))
 (24 6 (:REWRITE RATIONALP-X))
 (18 18 (:TYPE-PRESCRIPTION RTL::BVECP))
 (17 17 (:REWRITE |(+ c (+ d x))|))
 (16 8 (:REWRITE DEFAULT-EXPT-2))
 (15 15 (:REWRITE REDUCE-INTEGERP-+))
 (15 15 (:REWRITE |(< y (+ (- c) x))|))
 (15 15 (:REWRITE |(< x (+ c/d y))|))
 (15 15 (:META META-INTEGERP-CORRECT))
 (14 14 (:REWRITE |(< (+ c/d x) y)|))
 (14 14 (:REWRITE |(< (+ (- c) x) y)|))
 (13 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (13 3
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (13 3
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (9 9
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (9 9
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (9 9 (:REWRITE DEFAULT-TIMES-2))
 (9 9 (:REWRITE DEFAULT-TIMES-1))
 (9 9 (:REWRITE DEFAULT-DIVIDE))
 (8 8 (:REWRITE DEFAULT-EXPT-1))
 (8 8 (:REWRITE |(expt 1/c n)|))
 (8 8 (:REWRITE |(expt (- x) n)|))
 (6 6 (:REWRITE REDUCE-RATIONALP-+))
 (6 6 (:REWRITE REDUCE-RATIONALP-*))
 (6 6 (:REWRITE RATIONALP-MINUS-X))
 (6 6 (:META META-RATIONALP-CORRECT))
 (5 5 (:REWRITE FOLD-CONSTS-IN-+))
 (5 5 (:REWRITE |(< (/ x) 0)|))
 (5 5 (:REWRITE |(< (* x y) 0)|))
 (5 1
    (:REWRITE EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4 (:REWRITE |(< 0 (/ x))|))
 (4 4 (:REWRITE |(< 0 (* x y))|))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (3 3
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (3 3
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (3 3 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (3 3
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (3 3 (:REWRITE |(equal c (/ x))|))
 (3 3 (:REWRITE |(equal c (- x))|))
 (3 3 (:REWRITE |(equal (/ x) c)|))
 (3 3 (:REWRITE |(equal (/ x) (/ y))|))
 (3 3 (:REWRITE |(equal (- x) c)|))
 (3 3 (:REWRITE |(equal (- x) (- y))|))
 (3 3
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (3 3
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (3 3 (:REWRITE |(- (* c x))|))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (1 1 (:REWRITE |(equal (expt 2 n) c)|))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<))
 (1 1 (:LINEAR EXPT->=-1-TWO))
 (1 1 (:LINEAR EXPT->-1-TWO))
 (1 1 (:LINEAR EXPT-<=-1-ONE))
 (1 1 (:LINEAR EXPT-<-1-ONE)))
(RTL::NOT-MIDPOINT-DOWN-2
 (1050 29 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (764 40
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (269 41 (:REWRITE NORMALIZE-ADDENDS))
 (238 2 (:LINEAR EXPT->=-1-ONE))
 (238 2 (:LINEAR EXPT-<=-1-TWO))
 (234 2 (:LINEAR EXPT->-1-ONE))
 (234 2 (:LINEAR EXPT-<-1-TWO))
 (218 121 (:REWRITE DEFAULT-PLUS-2))
 (215 2 (:LINEAR EXPT-X->=-X))
 (215 2 (:LINEAR EXPT-X->-X))
 (188 10 (:REWRITE |(+ y (+ x z))|))
 (167 1
      (:REWRITE EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (165 1
      (:REWRITE EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (155 121 (:REWRITE DEFAULT-PLUS-1))
 (121 15 (:REWRITE SIMPLIFY-SUMS-<))
 (114 16 (:REWRITE |(+ y x)|))
 (112 16 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
 (96 15 (:REWRITE |(< y (+ (- c) x))|))
 (94 13 (:REWRITE |(< (+ (- c) x) y)|))
 (78
  78
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (78 78
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (78 78
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (78 78
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (78 78
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (78 78
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (76 40 (:REWRITE DEFAULT-LESS-THAN-2))
 (66 40 (:REWRITE DEFAULT-LESS-THAN-1))
 (61 29
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (59 29 (:REWRITE |(+ c (+ d x))|))
 (50 28 (:REWRITE |(+ 0 x)|))
 (42 36 (:DEFINITION FIX))
 (40 40 (:REWRITE THE-FLOOR-BELOW))
 (40 40 (:REWRITE THE-FLOOR-ABOVE))
 (40 40
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (40 40
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (30 30
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (30 30 (:REWRITE INTEGERP-<-CONSTANT))
 (30 30 (:REWRITE CONSTANT-<-INTEGERP))
 (30 30
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (30 30
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (30 30
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (30 30
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (30 30 (:REWRITE |(< c (- x))|))
 (30 30
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (30 30
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (30 30
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (30 30
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (30 30 (:REWRITE |(< (/ x) (/ y))|))
 (30 30 (:REWRITE |(< (- x) c)|))
 (30 30 (:REWRITE |(< (- x) (- y))|))
 (28 2 (:REWRITE RTL::R-EXACTP-6))
 (24 20 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (21 21
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (20 20 (:REWRITE |(+ x (- x))|))
 (19 19 (:REWRITE |(< x (+ c/d y))|))
 (15 15 (:REWRITE |(< (+ c/d x) y)|))
 (12 12 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (8 4 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
 (7 7 (:REWRITE FOLD-CONSTS-IN-+))
 (6 6 (:REWRITE |(< 0 (* x y))|))
 (5 1
    (:REWRITE EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4 (:REWRITE |(< 0 (/ x))|))
 (4 4 (:REWRITE |(< (* x y) 0)|))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (4 2 (:REWRITE DEFAULT-EXPT-2))
 (4 1 (:REWRITE RATIONALP-X))
 (2 2 (:REWRITE DEFAULT-MINUS))
 (2 2 (:REWRITE DEFAULT-EXPT-1))
 (2 2 (:REWRITE |(expt 1/c n)|))
 (2 2 (:REWRITE |(expt (- x) n)|))
 (2 2 (:REWRITE |(< (/ x) 0)|))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-ONE))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE REDUCE-RATIONALP-+))
 (1 1 (:REWRITE REDUCE-RATIONALP-*))
 (1 1 (:REWRITE REDUCE-INTEGERP-+))
 (1 1 (:REWRITE RATIONALP-MINUS-X))
 (1 1 (:REWRITE INTEGERP-MINUS-X))
 (1 1 (:META META-RATIONALP-CORRECT))
 (1 1 (:META META-INTEGERP-CORRECT)))
(RTL::NOT-MIDPOINT-DOWN-3
 (103153 448 (:REWRITE RTL::R-EXACTP-6))
 (53421 3325
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (24482 8480 (:REWRITE DEFAULT-PLUS-2))
 (19246
  19246
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (19246
      19246
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (19246
     19246
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (19246 19246
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (16369 8480 (:REWRITE DEFAULT-PLUS-1))
 (14988 135 (:LINEAR EXPT-<=-1-TWO))
 (14900 135 (:LINEAR EXPT->=-1-ONE))
 (14739 135 (:LINEAR EXPT-<-1-TWO))
 (14651 135 (:LINEAR EXPT->-1-ONE))
 (13267 135 (:LINEAR EXPT-X->=-X))
 (13267 135 (:LINEAR EXPT-X->-X))
 (9550 9550
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (9550 9550
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (9550 9550
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (9550 9550
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (8973 3353 (:REWRITE DEFAULT-LESS-THAN-2))
 (7102 3353 (:REWRITE DEFAULT-LESS-THAN-1))
 (6568 962 (:REWRITE |(< y (+ (- c) x))|))
 (6454 848 (:REWRITE |(< (+ (- c) x) y)|))
 (3736 2623 (:REWRITE |(< (- x) (- y))|))
 (3468 2623 (:REWRITE |(< (- x) c)|))
 (3353 3353 (:REWRITE THE-FLOOR-BELOW))
 (3353 3353 (:REWRITE THE-FLOOR-ABOVE))
 (3325 3325
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (3325 3325
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (3002 631 (:REWRITE DEFAULT-MINUS))
 (2893 2623
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (2703 2623 (:REWRITE |(< c (- x))|))
 (2671 1116 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (2623 2623 (:REWRITE INTEGERP-<-CONSTANT))
 (2623 2623 (:REWRITE CONSTANT-<-INTEGERP))
 (2623 2623
       (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (2623 2623
       (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (2623 2623
       (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (2623 2623
       (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (2623 2623
       (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (2623 2623
       (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (2623 2623
       (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (2623 2623 (:REWRITE |(< (/ x) (/ y))|))
 (1925 1925
       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (1242 1242 (:REWRITE |(< x (+ c/d y))|))
 (1215 45
       (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (1170 45
       (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (1155 7
       (:REWRITE EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (1140 84 (:REWRITE ODD-EXPT-THM))
 (1001 282 (:REWRITE DEFAULT-TIMES-2))
 (988 988 (:REWRITE |(< (+ c/d x) y)|))
 (748 387 (:REWRITE DEFAULT-EXPT-2))
 (611 130
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (565 565 (:REWRITE FOLD-CONSTS-IN-+))
 (556 14
      (:REWRITE EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (495 165 (:REWRITE RTL::BVECP-EXACTP))
 (491 491 (:REWRITE |(< 0 (* x y))|))
 (444 276 (:REWRITE INTEGERP-MINUS-X))
 (434 115 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (412 103 (:REWRITE RATIONALP-X))
 (387 387 (:REWRITE DEFAULT-EXPT-1))
 (387 387 (:REWRITE |(expt 1/c n)|))
 (387 387 (:REWRITE |(expt (- x) n)|))
 (349 349 (:REWRITE |(< 0 (/ x))|))
 (342 342 (:REWRITE |(< (* x y) 0)|))
 (330 330 (:TYPE-PRESCRIPTION RTL::BVECP))
 (305 282 (:REWRITE DEFAULT-TIMES-1))
 (284 134 (:REWRITE |(equal (- x) (- y))|))
 (280 130 (:REWRITE |(equal (- x) c)|))
 (276 276 (:REWRITE REDUCE-INTEGERP-+))
 (276 276 (:META META-INTEGERP-CORRECT))
 (270 270
      (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (270 270
      (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (270 270
      (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (226 134 (:REWRITE |(equal (/ x) c)|))
 (223 135 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (202 202 (:REWRITE |(< (/ x) 0)|))
 (142 138 (:REWRITE DEFAULT-DIVIDE))
 (138 134 (:REWRITE |(equal (/ x) (/ y))|))
 (135 135 (:LINEAR EXPT-LINEAR-UPPER-<))
 (135 135 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (135 135 (:LINEAR EXPT-LINEAR-LOWER-<))
 (135 135 (:LINEAR EXPT->=-1-TWO))
 (135 135 (:LINEAR EXPT->-1-TWO))
 (135 135 (:LINEAR EXPT-<=-1-ONE))
 (135 135 (:LINEAR EXPT-<-1-ONE))
 (134 134
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (134 134
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (134 134
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (134 134 (:REWRITE |(equal c (/ x))|))
 (130 130
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (130 130 (:REWRITE |(equal c (- x))|))
 (103 103 (:REWRITE REDUCE-RATIONALP-+))
 (103 103 (:REWRITE REDUCE-RATIONALP-*))
 (103 103 (:REWRITE RATIONALP-MINUS-X))
 (103 103 (:META META-RATIONALP-CORRECT))
 (100 100
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (100 100
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (45 45
     (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (45 45
     (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (42 42
     (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (42 42 (:REWRITE |(- (* c x))|))
 (39 39 (:REWRITE ZP-OPEN))
 (36 36
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (36 36
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (26 26 (:REWRITE |(equal (expt 2 n) c)|))
 (16 16
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (15 15 (:REWRITE |(equal (+ (- c) x) y)|))
 (14 14 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (14 14 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (14 14 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (14 14 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (12 4 (:REWRITE |(equal x (/ y))|))
 (8 4 (:REWRITE |(not (equal x (/ y)))|))
 (8 4 (:REWRITE |(/ (/ x))|))
 (2 2
    (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (2 2
    (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (2 2
    (:REWRITE |(< x (/ y)) with (< y 0)|)))
(RTL::NOT-MIDPOINT-DOWN-4
 (1447
  1447
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1447
      1447
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1447
     1447
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1447 1447
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1447 1447
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (1319 1319
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (1319 1319
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (1319 1319
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (1319 1319
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (751 402 (:REWRITE DEFAULT-PLUS-2))
 (594 402 (:REWRITE DEFAULT-PLUS-1))
 (425 51 (:REWRITE DEFAULT-TIMES-2))
 (412 5 (:LINEAR EXPT->=-1-ONE))
 (412 5 (:LINEAR EXPT-<=-1-TWO))
 (403 5 (:LINEAR EXPT-X->=-X))
 (403 5 (:LINEAR EXPT-X->-X))
 (403 5 (:LINEAR EXPT->-1-ONE))
 (403 5 (:LINEAR EXPT-<-1-TWO))
 (310 124
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (260 132 (:REWRITE DEFAULT-LESS-THAN-2))
 (230 132 (:REWRITE DEFAULT-LESS-THAN-1))
 (168 132
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (164 132 (:REWRITE |(< (- x) (- y))|))
 (152 132 (:REWRITE |(< (- x) c)|))
 (132 132 (:REWRITE THE-FLOOR-BELOW))
 (132 132 (:REWRITE THE-FLOOR-ABOVE))
 (132 132
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (132 132
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (132 132
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (132 132 (:REWRITE INTEGERP-<-CONSTANT))
 (132 132 (:REWRITE CONSTANT-<-INTEGERP))
 (132 132
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (132 132
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (132 132
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (132 132
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (132 132 (:REWRITE |(< c (- x))|))
 (132 132
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (132 132
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (132 132
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (132 132 (:REWRITE |(< (/ x) (/ y))|))
 (122 122
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (112 51 (:REWRITE DEFAULT-TIMES-1))
 (102 34 (:REWRITE RTL::BVECP-EXACTP))
 (95 35 (:REWRITE DEFAULT-MINUS))
 (92 23 (:REWRITE RATIONALP-X))
 (86 43 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (81 3
     (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (79 67 (:REWRITE INTEGERP-MINUS-X))
 (78 3
     (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (68 68 (:TYPE-PRESCRIPTION RTL::BVECP))
 (67 67 (:REWRITE REDUCE-INTEGERP-+))
 (67 67 (:META META-INTEGERP-CORRECT))
 (63 3 (:REWRITE ODD-EXPT-THM))
 (60 39 (:REWRITE DEFAULT-EXPT-2))
 (39 39 (:REWRITE DEFAULT-EXPT-1))
 (39 39 (:REWRITE |(expt 1/c n)|))
 (39 39 (:REWRITE |(expt (- x) n)|))
 (30 30 (:REWRITE |(< (+ c/d x) y)|))
 (30 30 (:REWRITE |(< (+ (- c) x) y)|))
 (25 25 (:REWRITE |(< y (+ (- c) x))|))
 (25 25 (:REWRITE |(< x (+ c/d y))|))
 (23 23 (:REWRITE REDUCE-RATIONALP-+))
 (23 23 (:REWRITE REDUCE-RATIONALP-*))
 (23 23 (:REWRITE RATIONALP-MINUS-X))
 (23 23 (:META META-RATIONALP-CORRECT))
 (14 14 (:REWRITE FOLD-CONSTS-IN-+))
 (13 13 (:REWRITE |(< (/ x) 0)|))
 (13 13 (:REWRITE |(< (* x y) 0)|))
 (10 10 (:REWRITE |(< 0 (/ x))|))
 (10 10 (:REWRITE |(< 0 (* x y))|))
 (10 10
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (10 10
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (10 10
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (10 10
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (9 9 (:REWRITE ZP-OPEN))
 (9 9
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (9 9 (:REWRITE DEFAULT-DIVIDE))
 (8 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (8 6
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (8 6
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (6 6
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (6 6
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (6 6
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (6 6 (:REWRITE |(equal c (/ x))|))
 (6 6 (:REWRITE |(equal c (- x))|))
 (6 6 (:REWRITE |(equal (/ x) c)|))
 (6 6 (:REWRITE |(equal (/ x) (/ y))|))
 (6 6 (:REWRITE |(equal (- x) c)|))
 (6 6 (:REWRITE |(equal (- x) (- y))|))
 (5 5 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (5 5 (:LINEAR EXPT-LINEAR-UPPER-<))
 (5 5 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (5 5 (:LINEAR EXPT-LINEAR-LOWER-<))
 (5 5 (:LINEAR EXPT->=-1-TWO))
 (5 5 (:LINEAR EXPT->-1-TWO))
 (5 5 (:LINEAR EXPT-<=-1-ONE))
 (5 5 (:LINEAR EXPT-<-1-ONE))
 (3 3 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (3 3
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (3 3
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (3 3 (:REWRITE |(- (* c x))|))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON)))
(RTL::NOT-MIDPOINT-DOWN-5
 (13796 105 (:REWRITE RTL::R-EXACTP-6))
 (9191 503
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (5379 1510 (:REWRITE DEFAULT-PLUS-2))
 (3330 1510 (:REWRITE DEFAULT-PLUS-1))
 (2053
  2053
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (2053
      2053
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (2053
     2053
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (2053 2053
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (2053 2053
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (2053 2053
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (1780 13 (:LINEAR EXPT->=-1-ONE))
 (1780 13 (:LINEAR EXPT-<=-1-TWO))
 (1755 13 (:LINEAR EXPT->-1-ONE))
 (1755 13 (:LINEAR EXPT-<-1-TWO))
 (1511 13 (:LINEAR EXPT-X->=-X))
 (1511 13 (:LINEAR EXPT-X->-X))
 (1318 504 (:REWRITE DEFAULT-LESS-THAN-2))
 (1277 1277
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (1277 1277
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (1277 1277
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (1277 1277
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (1127 155 (:REWRITE |(< y (+ (- c) x))|))
 (1100 504 (:REWRITE DEFAULT-LESS-THAN-1))
 (1092 120 (:REWRITE |(< (+ (- c) x) y)|))
 (718 142 (:REWRITE DEFAULT-MINUS))
 (668 4
      (:REWRITE EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (661 301 (:REWRITE |(+ c (+ d x))|))
 (660 4
      (:REWRITE EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (569 381 (:REWRITE |(< (- x) (- y))|))
 (545 171 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (520 11 (:REWRITE ODD-EXPT-THM))
 (504 504 (:REWRITE THE-FLOOR-BELOW))
 (504 504 (:REWRITE THE-FLOOR-ABOVE))
 (503 503
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (503 503
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (461 381 (:REWRITE |(< c (- x))|))
 (441 381 (:REWRITE |(< (- x) c)|))
 (423 381
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (418 418
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (381 381 (:REWRITE INTEGERP-<-CONSTANT))
 (381 381 (:REWRITE CONSTANT-<-INTEGERP))
 (381 381
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (381 381
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (381 381
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (381 381
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (381 381
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (381 381
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (381 381
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (381 381 (:REWRITE |(< (/ x) (/ y))|))
 (203 203 (:REWRITE |(< x (+ c/d y))|))
 (198 99 (:REWRITE DEFAULT-EXPT-2))
 (189 7
      (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (182 7
      (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (144 144 (:REWRITE |(< (+ c/d x) y)|))
 (114 114 (:REWRITE FOLD-CONSTS-IN-+))
 (111 37 (:REWRITE RTL::BVECP-EXACTP))
 (99 99 (:REWRITE DEFAULT-EXPT-1))
 (99 99 (:REWRITE |(expt 1/c n)|))
 (99 99 (:REWRITE |(expt (- x) n)|))
 (93 93 (:REWRITE |(< 0 (* x y))|))
 (74 74 (:TYPE-PRESCRIPTION RTL::BVECP))
 (67 67 (:REWRITE |(< 0 (/ x))|))
 (60 32 (:REWRITE INTEGERP-MINUS-X))
 (44 11 (:REWRITE RATIONALP-X))
 (35 9 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (35 9
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (35 9
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (33 33 (:REWRITE |(< (* x y) 0)|))
 (32 32 (:REWRITE REDUCE-INTEGERP-+))
 (32 32 (:META META-INTEGERP-CORRECT))
 (31 31
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (31 31
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (27 27 (:REWRITE DEFAULT-TIMES-2))
 (27 27 (:REWRITE DEFAULT-TIMES-1))
 (26 26
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (26 26
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (26 26
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (26 26
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (20 4
     (:REWRITE EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (19 19
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (19 19
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (19 19 (:REWRITE DEFAULT-DIVIDE))
 (13 13 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (13 13 (:LINEAR EXPT-LINEAR-UPPER-<))
 (13 13 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (13 13 (:LINEAR EXPT-LINEAR-LOWER-<))
 (13 13 (:LINEAR EXPT->=-1-TWO))
 (13 13 (:LINEAR EXPT->-1-TWO))
 (13 13 (:LINEAR EXPT-<=-1-ONE))
 (13 13 (:LINEAR EXPT-<-1-ONE))
 (11 11 (:REWRITE REDUCE-RATIONALP-+))
 (11 11 (:REWRITE REDUCE-RATIONALP-*))
 (11 11 (:REWRITE RATIONALP-MINUS-X))
 (11 11 (:META META-RATIONALP-CORRECT))
 (9 9
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (9 9
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (9 9
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (9 9 (:REWRITE |(equal c (/ x))|))
 (9 9 (:REWRITE |(equal c (- x))|))
 (9 9 (:REWRITE |(equal (/ x) c)|))
 (9 9 (:REWRITE |(equal (/ x) (/ y))|))
 (9 9 (:REWRITE |(equal (- x) c)|))
 (9 9 (:REWRITE |(equal (- x) (- y))|))
 (9 9 (:REWRITE |(< (/ x) 0)|))
 (7 7 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (7 7
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (7 7
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (7 7 (:REWRITE |(- (* c x))|))
 (4 4 (:REWRITE ZP-OPEN))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2 (:REWRITE |(equal (expt 2 n) c)|))
 (2 2
    (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (2 2
    (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (2 2
    (:REWRITE |(< x (/ y)) with (< y 0)|)))
(RTL::NOT-MIDPOINT-DOWN
 (8563 82 (:REWRITE RTL::R-EXACTP-6))
 (6437 645
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (3780 1445 (:REWRITE DEFAULT-PLUS-2))
 (3371 3371
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (3371 3371
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (3371 3371
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (3371 3371
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (2728 26 (:LINEAR EXPT->=-1-ONE))
 (2728 26 (:LINEAR EXPT-<=-1-TWO))
 (2678 26 (:LINEAR EXPT->-1-ONE))
 (2678 26 (:LINEAR EXPT-<-1-TWO))
 (2548
  2548
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (2548
      2548
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (2548
     2548
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (2548 2548
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (2548 2548
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (2548 2548
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (2526 26 (:LINEAR EXPT-X->=-X))
 (2526 26 (:LINEAR EXPT-X->-X))
 (2297 1445 (:REWRITE DEFAULT-PLUS-1))
 (1499 533
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (1263 645 (:REWRITE DEFAULT-LESS-THAN-2))
 (1185 645 (:REWRITE DEFAULT-LESS-THAN-1))
 (819 171 (:REWRITE |(< y (+ (- c) x))|))
 (811 163 (:REWRITE |(< (+ (- c) x) y)|))
 (679 565
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (645 645 (:REWRITE THE-FLOOR-BELOW))
 (645 645 (:REWRITE THE-FLOOR-ABOVE))
 (645 645
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (645 645
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (601 565 (:REWRITE |(< (- x) (- y))|))
 (565 565 (:REWRITE INTEGERP-<-CONSTANT))
 (565 565 (:REWRITE CONSTANT-<-INTEGERP))
 (565 565
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (565 565
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (565 565
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (565 565
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (565 565 (:REWRITE |(< c (- x))|))
 (565 565
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (565 565
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (565 565
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (565 565 (:REWRITE |(< (/ x) (/ y))|))
 (565 565 (:REWRITE |(< (- x) c)|))
 (540 300 (:REWRITE |(+ c (+ d x))|))
 (513 19
      (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (494 19
      (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (483 141 (:REWRITE DEFAULT-MINUS))
 (479 11 (:REWRITE ODD-EXPT-THM))
 (392 392
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (363 123 (:REWRITE RTL::BVECP-EXACTP))
 (301 199 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (252 2
      (:REWRITE EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (252 2
      (:REWRITE EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (248 2
      (:REWRITE EXPT-IS-INCREASING-FOR-BASE->-1))
 (248 2
      (:REWRITE EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (248 2 (:REWRITE |(integerp (expt x n))|))
 (246 66 (:REWRITE RATIONALP-X))
 (240 240 (:TYPE-PRESCRIPTION RTL::BVECP))
 (203 203 (:REWRITE |(< x (+ c/d y))|))
 (202 26
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (179 179 (:REWRITE |(< (+ c/d x) y)|))
 (156 78 (:REWRITE DEFAULT-EXPT-2))
 (143 107 (:REWRITE INTEGERP-MINUS-X))
 (142 24 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (115 115 (:REWRITE DEFAULT-TIMES-2))
 (115 115 (:REWRITE DEFAULT-TIMES-1))
 (107 107 (:REWRITE REDUCE-INTEGERP-+))
 (107 107 (:META META-INTEGERP-CORRECT))
 (106 106
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (106 106 (:REWRITE DEFAULT-DIVIDE))
 (103 103
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (78 78 (:REWRITE DEFAULT-EXPT-1))
 (78 78 (:REWRITE |(expt 1/c n)|))
 (78 78 (:REWRITE |(expt (- x) n)|))
 (73 73 (:REWRITE FOLD-CONSTS-IN-+))
 (68 68 (:REWRITE |(< 0 (* x y))|))
 (66 66 (:REWRITE REDUCE-RATIONALP-+))
 (66 66 (:REWRITE REDUCE-RATIONALP-*))
 (66 66 (:REWRITE RATIONALP-MINUS-X))
 (66 66 (:META META-RATIONALP-CORRECT))
 (63 63 (:REWRITE |(< (* x y) 0)|))
 (52 52 (:REWRITE |(< 0 (/ x))|))
 (52 52
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (52 52
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (52 52
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (52 52
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (48 18 (:REWRITE ACL2-NUMBERP-X))
 (47 47 (:REWRITE |(< (/ x) 0)|))
 (26 26
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (26 26
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (26 26
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (26 26 (:REWRITE |(equal c (/ x))|))
 (26 26 (:REWRITE |(equal c (- x))|))
 (26 26 (:REWRITE |(equal (/ x) c)|))
 (26 26 (:REWRITE |(equal (/ x) (/ y))|))
 (26 26 (:REWRITE |(equal (- x) c)|))
 (26 26 (:REWRITE |(equal (- x) (- y))|))
 (26 26 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (26 26 (:LINEAR EXPT-LINEAR-UPPER-<))
 (26 26 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (26 26 (:LINEAR EXPT-LINEAR-LOWER-<))
 (26 26 (:LINEAR EXPT->=-1-TWO))
 (26 26 (:LINEAR EXPT->-1-TWO))
 (26 26 (:LINEAR EXPT-<=-1-ONE))
 (26 26 (:LINEAR EXPT-<-1-ONE))
 (19 19
     (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (19 19
     (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (16 16 (:REWRITE ZP-OPEN))
 (10 10 (:REWRITE |(equal (+ (- c) x) y)|))
 (9 9 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (9 9 (:REWRITE |(- (* c x))|))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON)))
(RTL::R-NEG-RNE-4
 (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (7
  7
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (7 7
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (7 7
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (7 7
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (7 7
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (7 7
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE)))
(RTL::R-NEG-RNE-5
 (893 893
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (893 893
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (893 893
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (893 893
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (759
  759
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (759 759
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (759
     759
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (759 759
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (759 759
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (759 759
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (365 9 (:REWRITE RTL::R-EXACTP-6))
 (354 88 (:REWRITE DEFAULT-PLUS-2))
 (268 52
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (250 88 (:REWRITE DEFAULT-PLUS-1))
 (217 61 (:REWRITE DEFAULT-LESS-THAN-2))
 (141 43 (:REWRITE SIMPLIFY-SUMS-<))
 (133 61 (:REWRITE DEFAULT-LESS-THAN-1))
 (93 61 (:REWRITE |(< (- x) (- y))|))
 (82 61
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (82 26 (:REWRITE DEFAULT-MINUS))
 (80 2 (:LINEAR EXPT->=-1-ONE))
 (80 2 (:LINEAR EXPT-<=-1-TWO))
 (78 2 (:LINEAR EXPT->-1-ONE))
 (78 2 (:LINEAR EXPT-<-1-TWO))
 (74 30 (:REWRITE DEFAULT-TIMES-2))
 (70 2 (:LINEAR EXPT-X->=-X))
 (70 2 (:LINEAR EXPT-X->-X))
 (63 3 (:REWRITE ODD-EXPT-THM))
 (61 61 (:REWRITE THE-FLOOR-BELOW))
 (61 61 (:REWRITE THE-FLOOR-ABOVE))
 (61 61
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (61 61
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (61 61
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (61 61 (:REWRITE INTEGERP-<-CONSTANT))
 (61 61 (:REWRITE CONSTANT-<-INTEGERP))
 (61 61
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (61 61
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (61 61
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (61 61
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (61 61 (:REWRITE |(< c (- x))|))
 (61 61
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (61 61
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (61 61
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (61 61 (:REWRITE |(< (/ x) (/ y))|))
 (61 61 (:REWRITE |(< (- x) c)|))
 (54 2
     (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (52 2
     (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (41 9 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (32 32
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (30 30 (:REWRITE DEFAULT-TIMES-1))
 (28 16 (:REWRITE INTEGERP-MINUS-X))
 (27 9 (:REWRITE RTL::BVECP-EXACTP))
 (24 6 (:REWRITE RATIONALP-X))
 (20 20
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (18 18 (:TYPE-PRESCRIPTION RTL::BVECP))
 (18 9 (:REWRITE DEFAULT-EXPT-2))
 (16 16 (:REWRITE REDUCE-INTEGERP-+))
 (16 16 (:META META-INTEGERP-CORRECT))
 (15 15 (:REWRITE |(< y (+ (- c) x))|))
 (15 15 (:REWRITE |(< x (+ c/d y))|))
 (14 14
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (14 14 (:REWRITE DEFAULT-DIVIDE))
 (13 13 (:REWRITE |(< (+ c/d x) y)|))
 (13 13 (:REWRITE |(< (+ (- c) x) y)|))
 (9 9 (:REWRITE DEFAULT-EXPT-1))
 (9 9 (:REWRITE |(expt 1/c n)|))
 (9 9 (:REWRITE |(expt (- x) n)|))
 (7 7 (:REWRITE |(- (* c x))|))
 (7 7 (:REWRITE |(+ c (+ d x))|))
 (6 6 (:REWRITE REDUCE-RATIONALP-+))
 (6 6 (:REWRITE REDUCE-RATIONALP-*))
 (6 6 (:REWRITE RATIONALP-MINUS-X))
 (6 6 (:REWRITE |(< (/ x) 0)|))
 (6 6 (:REWRITE |(< (* x y) 0)|))
 (6 6 (:META META-RATIONALP-CORRECT))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (4 4 (:REWRITE |(< 0 (/ x))|))
 (4 4 (:REWRITE |(< 0 (* x y))|))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (3 3 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (3 3 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (2 2
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (2 2
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (2 2
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (2 2
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (2 2
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (2 2 (:REWRITE |(equal c (/ x))|))
 (2 2 (:REWRITE |(equal c (- x))|))
 (2 2 (:REWRITE |(equal (/ x) c)|))
 (2 2 (:REWRITE |(equal (/ x) (/ y))|))
 (2 2 (:REWRITE |(equal (- x) c)|))
 (2 2 (:REWRITE |(equal (- x) (- y))|))
 (2 2
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (2 2
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-NEG-RNE-6
 (1024 1024
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (1024 1024
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (1024 1024
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (1024 1024
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (1022
  1022
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1022
      1022
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1022
     1022
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1022 1022
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1022 1022
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (1022 1022
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (486 108 (:REWRITE DEFAULT-PLUS-2))
 (474 9 (:REWRITE RTL::R-EXACTP-6))
 (365 108 (:REWRITE DEFAULT-PLUS-1))
 (346 66
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (266 74 (:REWRITE DEFAULT-LESS-THAN-2))
 (184 54 (:REWRITE SIMPLIFY-SUMS-<))
 (182 74 (:REWRITE DEFAULT-LESS-THAN-1))
 (126 74 (:REWRITE |(< (- x) (- y))|))
 (98 74
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (96 28 (:REWRITE DEFAULT-MINUS))
 (81 3
     (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (80 2 (:LINEAR EXPT->=-1-ONE))
 (80 2 (:LINEAR EXPT-<=-1-TWO))
 (78 3
     (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (78 2 (:LINEAR EXPT->-1-ONE))
 (78 2 (:LINEAR EXPT-<-1-TWO))
 (74 74 (:REWRITE THE-FLOOR-BELOW))
 (74 74 (:REWRITE THE-FLOOR-ABOVE))
 (74 74
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (74 74
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (74 74
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (74 74 (:REWRITE INTEGERP-<-CONSTANT))
 (74 74 (:REWRITE CONSTANT-<-INTEGERP))
 (74 74
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (74 74
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (74 74
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (74 74
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (74 74 (:REWRITE |(< c (- x))|))
 (74 74
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (74 74
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (74 74
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (74 74 (:REWRITE |(< (/ x) (/ y))|))
 (74 74 (:REWRITE |(< (- x) c)|))
 (70 2 (:LINEAR EXPT-X->=-X))
 (70 2 (:LINEAR EXPT-X->-X))
 (64 12 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (63 3 (:REWRITE ODD-EXPT-THM))
 (57 25 (:REWRITE DEFAULT-TIMES-2))
 (36 12 (:REWRITE RTL::BVECP-EXACTP))
 (36 9 (:REWRITE RATIONALP-X))
 (34 34
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (32 20 (:REWRITE INTEGERP-MINUS-X))
 (25 25 (:REWRITE DEFAULT-TIMES-1))
 (24 24 (:TYPE-PRESCRIPTION RTL::BVECP))
 (20 20 (:REWRITE REDUCE-INTEGERP-+))
 (20 20
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (20 20 (:META META-INTEGERP-CORRECT))
 (18 9 (:REWRITE DEFAULT-EXPT-2))
 (17 17 (:REWRITE |(< y (+ (- c) x))|))
 (17 17 (:REWRITE |(< x (+ c/d y))|))
 (16 16 (:REWRITE |(< (+ c/d x) y)|))
 (16 16 (:REWRITE |(< (+ (- c) x) y)|))
 (15 15
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (15 15 (:REWRITE DEFAULT-DIVIDE))
 (9 9 (:REWRITE REDUCE-RATIONALP-+))
 (9 9 (:REWRITE REDUCE-RATIONALP-*))
 (9 9 (:REWRITE RATIONALP-MINUS-X))
 (9 9 (:REWRITE DEFAULT-EXPT-1))
 (9 9 (:REWRITE |(expt 1/c n)|))
 (9 9 (:REWRITE |(expt (- x) n)|))
 (9 9 (:META META-RATIONALP-CORRECT))
 (8 8 (:REWRITE |(+ c (+ d x))|))
 (7 7 (:REWRITE |(< (/ x) 0)|))
 (7 7 (:REWRITE |(< (* x y) 0)|))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (4 4 (:REWRITE |(< 0 (/ x))|))
 (4 4 (:REWRITE |(< 0 (* x y))|))
 (4 4 (:REWRITE |(- (* c x))|))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (3 3 (:REWRITE ZP-OPEN))
 (3 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (3 3
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (3 3
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (3 3
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (3 3
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (3 3 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (3 3 (:REWRITE FOLD-CONSTS-IN-+))
 (3 3
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (3 3 (:REWRITE |(equal c (/ x))|))
 (3 3 (:REWRITE |(equal c (- x))|))
 (3 3 (:REWRITE |(equal (/ x) c)|))
 (3 3 (:REWRITE |(equal (/ x) (/ y))|))
 (3 3 (:REWRITE |(equal (- x) c)|))
 (3 3 (:REWRITE |(equal (- x) (- y))|))
 (3 3
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (3 3
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-NEG-RNE-10)
(RTL::R-NEG-RNE-11
 (1142
  1142
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1142
      1142
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1142
     1142
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1142 1142
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1142 1142
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (1142 1142
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (1008 1008
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (1008 1008
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (1008 1008
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (1008 1008
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (609 114 (:REWRITE DEFAULT-PLUS-2))
 (584 10 (:REWRITE RTL::R-EXACTP-6))
 (451 114 (:REWRITE DEFAULT-PLUS-1))
 (393 69
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (249 77 (:REWRITE DEFAULT-LESS-THAN-2))
 (249 77 (:REWRITE DEFAULT-LESS-THAN-1))
 (207 57 (:REWRITE SIMPLIFY-SUMS-<))
 (149 77 (:REWRITE |(< (- x) (- y))|))
 (134 34 (:REWRITE DEFAULT-TIMES-1))
 (119 33 (:REWRITE DEFAULT-MINUS))
 (108 4
      (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (104 4
      (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (101 77
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (94 34 (:REWRITE DEFAULT-TIMES-2))
 (84 12 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (80 2 (:LINEAR EXPT->=-1-ONE))
 (80 2 (:LINEAR EXPT-<=-1-TWO))
 (79 77 (:REWRITE |(< (/ x) (/ y))|))
 (78 2 (:LINEAR EXPT->-1-ONE))
 (78 2 (:LINEAR EXPT-<-1-TWO))
 (77 77 (:REWRITE THE-FLOOR-BELOW))
 (77 77 (:REWRITE THE-FLOOR-ABOVE))
 (77 77
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (77 77
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (77 77
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (77 77 (:REWRITE INTEGERP-<-CONSTANT))
 (77 77 (:REWRITE CONSTANT-<-INTEGERP))
 (77 77
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (77 77
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (77 77
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (77 77
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (77 77 (:REWRITE |(< c (- x))|))
 (77 77
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (77 77
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (77 77
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (77 77 (:REWRITE |(< (- x) c)|))
 (70 2 (:LINEAR EXPT-X->=-X))
 (70 2 (:LINEAR EXPT-X->-X))
 (63 3 (:REWRITE ODD-EXPT-THM))
 (37 37
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (36 12 (:REWRITE RTL::BVECP-EXACTP))
 (36 9 (:REWRITE RATIONALP-X))
 (32 20 (:REWRITE INTEGERP-MINUS-X))
 (26 26
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (24 24 (:TYPE-PRESCRIPTION RTL::BVECP))
 (20 20 (:REWRITE REDUCE-INTEGERP-+))
 (20 20 (:META META-INTEGERP-CORRECT))
 (18 9 (:REWRITE DEFAULT-EXPT-2))
 (17 17 (:REWRITE |(< y (+ (- c) x))|))
 (17 17 (:REWRITE |(< x (+ c/d y))|))
 (16 16 (:REWRITE |(< (+ c/d x) y)|))
 (16 16 (:REWRITE |(< (+ (- c) x) y)|))
 (15 15
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (15 15 (:REWRITE DEFAULT-DIVIDE))
 (9 9 (:REWRITE REDUCE-RATIONALP-+))
 (9 9 (:REWRITE REDUCE-RATIONALP-*))
 (9 9 (:REWRITE RATIONALP-MINUS-X))
 (9 9 (:REWRITE DEFAULT-EXPT-1))
 (9 9 (:REWRITE |(expt 1/c n)|))
 (9 9 (:REWRITE |(expt (- x) n)|))
 (9 9 (:META META-RATIONALP-CORRECT))
 (8 8 (:REWRITE |(+ c (+ d x))|))
 (7 7 (:REWRITE |(< (/ x) 0)|))
 (7 7 (:REWRITE |(< (* x y) 0)|))
 (5 5 (:REWRITE |(- (* c x))|))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (4 4
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (4 4 (:REWRITE |(< 0 (/ x))|))
 (4 4 (:REWRITE |(< 0 (* x y))|))
 (4 4
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (3 3 (:REWRITE ZP-OPEN))
 (3 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (3 3
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (3 3
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (3 3
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (3 3
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (3 3 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (3 3 (:REWRITE FOLD-CONSTS-IN-+))
 (3 3
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (3 3 (:REWRITE |(equal c (/ x))|))
 (3 3 (:REWRITE |(equal c (- x))|))
 (3 3 (:REWRITE |(equal (/ x) c)|))
 (3 3 (:REWRITE |(equal (/ x) (/ y))|))
 (3 3 (:REWRITE |(equal (- x) c)|))
 (3 3 (:REWRITE |(equal (- x) (- y))|))
 (2 2 (:REWRITE |(* c (* d x))|))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-NEG-RNE-17
 (1071 1071
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (1071 1071
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (1071 1071
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (1071 1071
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (991
  991
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (991 991
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (991
     991
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (991 991
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (788 15 (:REWRITE RTL::R-EXACTP-6))
 (692 188 (:REWRITE DEFAULT-PLUS-2))
 (549 188 (:REWRITE DEFAULT-PLUS-1))
 (457 83
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (366 94 (:REWRITE DEFAULT-LESS-THAN-2))
 (265 65 (:REWRITE DEFAULT-TIMES-1))
 (234 94 (:REWRITE DEFAULT-LESS-THAN-1))
 (225 65 (:REWRITE SIMPLIFY-SUMS-<))
 (194 68 (:REWRITE DEFAULT-MINUS))
 (185 65 (:REWRITE DEFAULT-TIMES-2))
 (152 92 (:REWRITE |(< (- x) (- y))|))
 (139 9 (:REWRITE ODD-EXPT-THM))
 (135 5
      (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (130 5
      (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (110 92
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (94 94 (:REWRITE THE-FLOOR-BELOW))
 (94 94 (:REWRITE THE-FLOOR-ABOVE))
 (92 92
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (92 92
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (92 92
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (92 92 (:REWRITE INTEGERP-<-CONSTANT))
 (92 92 (:REWRITE CONSTANT-<-INTEGERP))
 (92 92
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (92 92
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (92 92
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (92 92
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (92 92 (:REWRITE |(< c (- x))|))
 (92 92
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (92 92
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (92 92
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (92 92 (:REWRITE |(< (/ x) (/ y))|))
 (92 92 (:REWRITE |(< (- x) c)|))
 (81 3 (:LINEAR EXPT->=-1-ONE))
 (79 3 (:LINEAR EXPT->-1-ONE))
 (78 18 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (71 3 (:LINEAR EXPT-X->=-X))
 (71 3 (:LINEAR EXPT-X->-X))
 (68 24 (:REWRITE RTL::BVECP-EXACTP))
 (66 66
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (49 49
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (45 25 (:REWRITE INTEGERP-MINUS-X))
 (44 44 (:TYPE-PRESCRIPTION RTL::BVECP))
 (40 10 (:REWRITE RATIONALP-X))
 (35 9 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (31 18 (:REWRITE DEFAULT-EXPT-2))
 (25 25 (:REWRITE REDUCE-INTEGERP-+))
 (25 25 (:META META-INTEGERP-CORRECT))
 (24 24 (:REWRITE |(< (+ c/d x) y)|))
 (24 24 (:REWRITE |(< (+ (- c) x) y)|))
 (19 19 (:REWRITE |(< y (+ (- c) x))|))
 (19 19 (:REWRITE |(< x (+ c/d y))|))
 (18 18
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (18 18 (:REWRITE DEFAULT-EXPT-1))
 (18 18 (:REWRITE DEFAULT-DIVIDE))
 (18 18 (:REWRITE |(expt 1/c n)|))
 (18 18 (:REWRITE |(expt (- x) n)|))
 (14 14 (:REWRITE |(- (* c x))|))
 (11 11 (:REWRITE |(< (/ x) 0)|))
 (11 11 (:REWRITE |(< (* x y) 0)|))
 (10 10 (:REWRITE REDUCE-RATIONALP-+))
 (10 10 (:REWRITE REDUCE-RATIONALP-*))
 (10 10 (:REWRITE RATIONALP-MINUS-X))
 (10 10 (:REWRITE |(+ c (+ d x))|))
 (10 10 (:META META-RATIONALP-CORRECT))
 (8 2 (:REWRITE |(integerp (- x))|))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (6 6
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (6 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (6 4
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (6 4
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (5 5
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (5 5
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (5 5 (:REWRITE FOLD-CONSTS-IN-+))
 (5 5
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (5 5
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (4 4
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (4 4
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (4 4
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (4 4 (:REWRITE |(equal c (/ x))|))
 (4 4 (:REWRITE |(equal c (- x))|))
 (4 4 (:REWRITE |(equal (/ x) c)|))
 (4 4 (:REWRITE |(equal (/ x) (/ y))|))
 (4 4 (:REWRITE |(equal (- x) c)|))
 (4 4 (:REWRITE |(equal (- x) (- y))|))
 (4 4 (:REWRITE |(< 0 (/ x))|))
 (4 4 (:REWRITE |(< 0 (* x y))|))
 (4 4 (:REWRITE |(* c (* d x))|))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<))
 (3 3 (:LINEAR EXPT->=-1-TWO))
 (3 3 (:LINEAR EXPT->-1-TWO))
 (3 3 (:LINEAR EXPT-<=-1-ONE))
 (3 3 (:LINEAR EXPT-<-1-ONE))
 (2 2 (:REWRITE ZP-OPEN)))
(RTL::R-NEG-RNE-20
 (35194
  35194
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (35194
      35194
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (35194
     35194
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (35194 35194
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (15423 15423
        (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (15423 15423
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (15423 15423
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (15423 15423
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (12957 2796 (:REWRITE DEFAULT-PLUS-2))
 (9806 2796 (:REWRITE DEFAULT-PLUS-1))
 (6932 1260 (:REWRITE DEFAULT-TIMES-1))
 (6247 1206 (:REWRITE DEFAULT-LESS-THAN-2))
 (5284 1260 (:REWRITE DEFAULT-TIMES-2))
 (3362 1206 (:REWRITE DEFAULT-LESS-THAN-1))
 (3304 799 (:REWRITE SIMPLIFY-SUMS-<))
 (2807 130 (:REWRITE ODD-EXPT-THM))
 (2515 725 (:REWRITE DEFAULT-MINUS))
 (2100 1176 (:REWRITE |(< (- x) (- y))|))
 (2003 387 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (1518 1176
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (1336 1176 (:REWRITE |(< c (- x))|))
 (1314 1176
       (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (1209 1176 (:REWRITE |(< (/ x) (/ y))|))
 (1206 1206 (:REWRITE THE-FLOOR-BELOW))
 (1206 1206 (:REWRITE THE-FLOOR-ABOVE))
 (1176 1176
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (1176 1176
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (1176 1176
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (1176 1176 (:REWRITE INTEGERP-<-CONSTANT))
 (1176 1176 (:REWRITE CONSTANT-<-INTEGERP))
 (1176 1176
       (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (1176 1176
       (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (1176 1176
       (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (1176 1176
       (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (1176 1176
       (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (1176 1176
       (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (1176 1176 (:REWRITE |(< (- x) c)|))
 (788 788
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (756 28
      (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (728 182 (:REWRITE RATIONALP-X))
 (728 28
      (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (673 114
      (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (600 200 (:REWRITE RTL::BVECP-EXACTP))
 (568 456 (:REWRITE INTEGERP-MINUS-X))
 (456 456 (:REWRITE REDUCE-INTEGERP-+))
 (456 456 (:META META-INTEGERP-CORRECT))
 (400 400 (:TYPE-PRESCRIPTION RTL::BVECP))
 (397 237 (:REWRITE DEFAULT-EXPT-2))
 (303 303 (:REWRITE |(< (+ c/d x) y)|))
 (303 303 (:REWRITE |(< (+ (- c) x) y)|))
 (237 237 (:REWRITE DEFAULT-EXPT-1))
 (237 237 (:REWRITE |(expt 1/c n)|))
 (237 237 (:REWRITE |(expt (- x) n)|))
 (233 233 (:REWRITE |(< y (+ (- c) x))|))
 (233 233 (:REWRITE |(< x (+ c/d y))|))
 (182 182 (:REWRITE REDUCE-RATIONALP-+))
 (182 182 (:REWRITE REDUCE-RATIONALP-*))
 (182 182 (:REWRITE RATIONALP-MINUS-X))
 (182 182 (:META META-RATIONALP-CORRECT))
 (172 43 (:REWRITE |(integerp (- x))|))
 (168 168 (:REWRITE |(- (* c x))|))
 (157 157
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (157 157 (:REWRITE DEFAULT-DIVIDE))
 (144 144 (:REWRITE |(+ c (+ d x))|))
 (88 88 (:REWRITE |(< (/ x) 0)|))
 (88 88 (:REWRITE |(< (* x y) 0)|))
 (84 84 (:REWRITE |(* c (* d x))|))
 (81 3 (:LINEAR EXPT->=-1-ONE))
 (79 3 (:LINEAR EXPT->-1-ONE))
 (71 71 (:REWRITE |(< 0 (/ x))|))
 (71 71 (:REWRITE |(< 0 (* x y))|))
 (71 3 (:LINEAR EXPT-X->=-X))
 (71 3 (:LINEAR EXPT-X->-X))
 (46 46 (:REWRITE ZP-OPEN))
 (46 46 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (46 46
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (46 46
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (46 46
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (46 46
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (46 46 (:REWRITE FOLD-CONSTS-IN-+))
 (46 46
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (46 46 (:REWRITE |(equal c (/ x))|))
 (46 46 (:REWRITE |(equal c (- x))|))
 (46 46 (:REWRITE |(equal (/ x) c)|))
 (46 46 (:REWRITE |(equal (/ x) (/ y))|))
 (46 46 (:REWRITE |(equal (- x) c)|))
 (46 46 (:REWRITE |(equal (- x) (- y))|))
 (36 36
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (36 36
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (28 28
     (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (28 28
     (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (11 11
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (11 11
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (6 6
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<))
 (3 3 (:LINEAR EXPT->=-1-TWO))
 (3 3 (:LINEAR EXPT->-1-TWO))
 (3 3 (:LINEAR EXPT-<=-1-ONE))
 (3 3 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-NEG-RNE-25
 (5501
  5501
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (5501
      5501
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (5501
     5501
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (5501 5501
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (3381 3381
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (3381 3381
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (3381 3381
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (1786 386 (:REWRITE DEFAULT-PLUS-2))
 (1352 386 (:REWRITE DEFAULT-PLUS-1))
 (1283 198
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (918 252 (:REWRITE DEFAULT-LESS-THAN-2))
 (810 15 (:REWRITE RTL::R-EXACTP-6))
 (771 252 (:REWRITE DEFAULT-LESS-THAN-1))
 (651 151 (:REWRITE SIMPLIFY-SUMS-<))
 (366 247 (:REWRITE |(< (- x) (- y))|))
 (355 247
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (325 110 (:REWRITE DEFAULT-MINUS))
 (321 247 (:REWRITE |(< (/ x) (/ y))|))
 (298 247
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (252 252 (:REWRITE THE-FLOOR-BELOW))
 (252 252 (:REWRITE THE-FLOOR-ABOVE))
 (247 247
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (247 247
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (247 247
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (247 247 (:REWRITE INTEGERP-<-CONSTANT))
 (247 247 (:REWRITE CONSTANT-<-INTEGERP))
 (247 247
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (247 247
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (247 247
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (247 247 (:REWRITE |(< c (- x))|))
 (247 247
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (247 247
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (247 247
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (247 247 (:REWRITE |(< (- x) c)|))
 (241 21 (:REWRITE ODD-EXPT-THM))
 (239 47 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (232 70 (:REWRITE DEFAULT-TIMES-2))
 (220 70 (:REWRITE DEFAULT-TIMES-1))
 (143 3
      (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (143 3
      (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (143 3 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (143 3 (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (135 5
      (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (130 5
      (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (129 43 (:REWRITE RTL::BVECP-EXACTP))
 (125 21
      (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (121 101 (:REWRITE INTEGERP-MINUS-X))
 (118 118
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (108 27 (:REWRITE RATIONALP-X))
 (107 35 (:REWRITE DEFAULT-DIVIDE))
 (101 101 (:REWRITE REDUCE-INTEGERP-+))
 (101 101 (:META META-INTEGERP-CORRECT))
 (86 86 (:TYPE-PRESCRIPTION RTL::BVECP))
 (81 3 (:LINEAR EXPT->=-1-ONE))
 (79 3 (:LINEAR EXPT->-1-ONE))
 (71 3 (:LINEAR EXPT-X->=-X))
 (71 3 (:LINEAR EXPT-X->-X))
 (60 45 (:REWRITE DEFAULT-EXPT-2))
 (59 59 (:REWRITE |(< (+ c/d x) y)|))
 (59 59 (:REWRITE |(< (+ (- c) x) y)|))
 (58 58
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (45 45 (:REWRITE DEFAULT-EXPT-1))
 (45 45 (:REWRITE |(expt 1/c n)|))
 (45 45 (:REWRITE |(expt (- x) n)|))
 (40 40 (:REWRITE |(< y (+ (- c) x))|))
 (40 40 (:REWRITE |(< x (+ c/d y))|))
 (35 35
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (32 8 (:REWRITE |(integerp (- x))|))
 (27 27 (:REWRITE REDUCE-RATIONALP-+))
 (27 27 (:REWRITE REDUCE-RATIONALP-*))
 (27 27 (:REWRITE RATIONALP-MINUS-X))
 (27 27 (:META META-RATIONALP-CORRECT))
 (26 26 (:REWRITE |(< (/ x) 0)|))
 (26 26 (:REWRITE |(< (* x y) 0)|))
 (19 19 (:REWRITE |(- (* c x))|))
 (14 14 (:REWRITE |(+ c (+ d x))|))
 (11 11
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (11 11
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (10 10 (:REWRITE |(< 0 (/ x))|))
 (10 10 (:REWRITE |(< 0 (* x y))|))
 (7 7 (:REWRITE ZP-OPEN))
 (7 7 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (7 7
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (7 7
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (7 7
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (7 7
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (7 7
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (7 7 (:REWRITE |(equal c (/ x))|))
 (7 7 (:REWRITE |(equal c (- x))|))
 (7 7 (:REWRITE |(equal (/ x) c)|))
 (7 7 (:REWRITE |(equal (/ x) (/ y))|))
 (7 7 (:REWRITE |(equal (- x) c)|))
 (7 7 (:REWRITE |(equal (- x) (- y))|))
 (6 6 (:REWRITE FOLD-CONSTS-IN-+))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (6 6
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (5 5
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (5 5
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (3 3 (:REWRITE |(* c (* d x))|))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<))
 (3 3 (:LINEAR EXPT->=-1-TWO))
 (3 3 (:LINEAR EXPT->-1-TWO))
 (3 3 (:LINEAR EXPT-<=-1-ONE))
 (3 3 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-NEG-RNE-26
 (16185
  16185
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (16185
      16185
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (16185
     16185
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (16185 16185
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (6421 1613 (:REWRITE DEFAULT-PLUS-2))
 (4693 1613 (:REWRITE DEFAULT-PLUS-1))
 (3515 665 (:REWRITE DEFAULT-LESS-THAN-2))
 (3146 670 (:REWRITE DEFAULT-TIMES-2))
 (1838 670 (:REWRITE DEFAULT-TIMES-1))
 (1597 430 (:REWRITE SIMPLIFY-SUMS-<))
 (1498 95 (:REWRITE ODD-EXPT-THM))
 (1430 665 (:REWRITE DEFAULT-LESS-THAN-1))
 (1256 442 (:REWRITE DEFAULT-MINUS))
 (1057 636 (:REWRITE |(< (- x) (- y))|))
 (1036 237 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (816 636 (:REWRITE |(< c (- x))|))
 (750 636
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (716 636 (:REWRITE |(< (- x) c)|))
 (665 665 (:REWRITE THE-FLOOR-BELOW))
 (665 665 (:REWRITE THE-FLOOR-ABOVE))
 (653 636 (:REWRITE |(< (/ x) (/ y))|))
 (636 636
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (636 636
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (636 636
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (636 636 (:REWRITE INTEGERP-<-CONSTANT))
 (636 636 (:REWRITE CONSTANT-<-INTEGERP))
 (636 636
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (636 636
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (636 636
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (636 636
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (636 636
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (636 636
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (636 636
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (614 614 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (515 86
      (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (437 437
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (417 139 (:REWRITE RTL::BVECP-EXACTP))
 (336 84 (:REWRITE RATIONALP-X))
 (278 278 (:TYPE-PRESCRIPTION RTL::BVECP))
 (208 208 (:REWRITE REDUCE-INTEGERP-+))
 (208 208 (:REWRITE INTEGERP-MINUS-X))
 (208 208 (:META META-INTEGERP-CORRECT))
 (207 138 (:REWRITE DEFAULT-EXPT-2))
 (199 199 (:REWRITE |(< (+ c/d x) y)|))
 (199 199 (:REWRITE |(< (+ (- c) x) y)|))
 (158 158
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (158 158
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (158 158
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (158 158
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (143 143 (:REWRITE |(< y (+ (- c) x))|))
 (143 143 (:REWRITE |(< x (+ c/d y))|))
 (138 138 (:REWRITE DEFAULT-EXPT-1))
 (138 138 (:REWRITE |(expt 1/c n)|))
 (138 138 (:REWRITE |(expt (- x) n)|))
 (132 33 (:REWRITE |(integerp (- x))|))
 (84 84 (:REWRITE REDUCE-RATIONALP-+))
 (84 84 (:REWRITE REDUCE-RATIONALP-*))
 (84 84 (:REWRITE RATIONALP-MINUS-X))
 (84 84 (:META META-RATIONALP-CORRECT))
 (81 3 (:LINEAR EXPT->=-1-ONE))
 (79 3 (:LINEAR EXPT->-1-ONE))
 (71 3 (:LINEAR EXPT-X->=-X))
 (71 3 (:LINEAR EXPT-X->-X))
 (67 67 (:REWRITE |(+ c (+ d x))|))
 (61 61 (:REWRITE |(< (/ x) 0)|))
 (61 61 (:REWRITE |(< (* x y) 0)|))
 (43 43 (:REWRITE |(- (* c x))|))
 (41 41 (:REWRITE |(< 0 (/ x))|))
 (41 41 (:REWRITE |(< 0 (* x y))|))
 (24 24 (:REWRITE ZP-OPEN))
 (24 24 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (24 24
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (24 24
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (24 24
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (24 24
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (24 24
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (24 24 (:REWRITE |(equal c (/ x))|))
 (24 24 (:REWRITE |(equal c (- x))|))
 (24 24 (:REWRITE |(equal (/ x) c)|))
 (24 24 (:REWRITE |(equal (/ x) (/ y))|))
 (24 24 (:REWRITE |(equal (- x) c)|))
 (24 24 (:REWRITE |(equal (- x) (- y))|))
 (20 20
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (20 20
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (11 11
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (11 11
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (9 9 (:REWRITE FOLD-CONSTS-IN-+))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (6 6
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<))
 (3 3 (:LINEAR EXPT->=-1-TWO))
 (3 3 (:LINEAR EXPT->-1-TWO))
 (3 3 (:LINEAR EXPT-<=-1-ONE))
 (3 3 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-NEG-RNE-28)
(RTL::R-NEG-RNE-29
 (24738
  24738
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (24738
      24738
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (24738
     24738
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (24738 24738
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (15165 1901
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (13864 3943 (:REWRITE DEFAULT-PLUS-2))
 (13392 13392
        (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (13392 13392
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (13392 13392
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (13392 13392
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (10117 3943 (:REWRITE DEFAULT-PLUS-1))
 (8155 1632
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (6412 1934 (:REWRITE DEFAULT-LESS-THAN-2))
 (5002 1934 (:REWRITE DEFAULT-LESS-THAN-1))
 (4740 34
       (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (4735 34
       (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (4663 61 (:LINEAR EXPT->=-1-ONE))
 (4317 1138 (:REWRITE SIMPLIFY-SUMS-<))
 (4313 61 (:LINEAR EXPT->-1-ONE))
 (3963 61 (:LINEAR EXPT-X->=-X))
 (3963 61 (:LINEAR EXPT-X->-X))
 (2917 1717 (:REWRITE |(< (- x) (- y))|))
 (2828 708 (:REWRITE DEFAULT-TIMES-2))
 (2508 708 (:REWRITE DEFAULT-TIMES-1))
 (2060 646 (:REWRITE DEFAULT-MINUS))
 (1999 1717
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (1962 504 (:REWRITE |(< (+ (- c) x) y)|))
 (1934 1934 (:REWRITE THE-FLOOR-BELOW))
 (1934 1934 (:REWRITE THE-FLOOR-ABOVE))
 (1925 1717 (:REWRITE |(< (- x) c)|))
 (1901 1901
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (1901 1901
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (1882 424 (:REWRITE |(< y (+ (- c) x))|))
 (1751 1717 (:REWRITE |(< (/ x) (/ y))|))
 (1717 1717
       (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (1717 1717
       (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (1717 1717
       (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (1717 1717
       (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (1717 1717 (:REWRITE |(< c (- x))|))
 (1717 1717
       (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (1717 1717
       (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (1717 1717
       (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (1713 1713 (:REWRITE INTEGERP-<-CONSTANT))
 (1713 1713 (:REWRITE CONSTANT-<-INTEGERP))
 (1694 494 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (1637 127 (:REWRITE ODD-EXPT-THM))
 (1555 34
       (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (1555 34
       (:REWRITE |(< x (/ y)) with (< y 0)|))
 (1215 45
       (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (1170 45
       (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (1123 571 (:REWRITE |(+ c (+ d x))|))
 (1000 1000
       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (713 179 (:REWRITE RATIONALP-X))
 (652 127
      (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (579 399 (:REWRITE INTEGERP-MINUS-X))
 (544 544 (:REWRITE |(< (+ c/d x) y)|))
 (498 166 (:REWRITE RTL::BVECP-EXACTP))
 (496 496 (:REWRITE |(< x (+ c/d y))|))
 (478 478
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (407 264 (:REWRITE DEFAULT-EXPT-2))
 (399 399 (:REWRITE REDUCE-INTEGERP-+))
 (399 399 (:META META-INTEGERP-CORRECT))
 (332 332 (:TYPE-PRESCRIPTION RTL::BVECP))
 (264 264 (:REWRITE DEFAULT-EXPT-1))
 (264 264 (:REWRITE |(expt 1/c n)|))
 (264 264 (:REWRITE |(expt (- x) n)|))
 (238 238
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (238 238 (:REWRITE DEFAULT-DIVIDE))
 (229 229 (:REWRITE |(< (* x y) 0)|))
 (189 189 (:REWRITE |(< (/ x) 0)|))
 (179 179 (:REWRITE REDUCE-RATIONALP-+))
 (179 179 (:REWRITE REDUCE-RATIONALP-*))
 (179 179 (:REWRITE RATIONALP-MINUS-X))
 (179 179 (:META META-RATIONALP-CORRECT))
 (170 170 (:REWRITE |(< 0 (* x y))|))
 (156 39 (:REWRITE |(integerp (- x))|))
 (153 153 (:REWRITE FOLD-CONSTS-IN-+))
 (134 134 (:REWRITE |(< 0 (/ x))|))
 (133 133 (:REWRITE |(- (* c x))|))
 (122 122
      (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (122 122
      (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (122 122
      (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (122 122
      (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (64 64 (:REWRITE |(* c (* d x))|))
 (62 62
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (62 62
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (62 62
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (62 62
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (61 61 (:LINEAR EXPT-LINEAR-UPPER-<))
 (61 61 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (61 61 (:LINEAR EXPT-LINEAR-LOWER-<))
 (61 61 (:LINEAR EXPT->=-1-TWO))
 (61 61 (:LINEAR EXPT->-1-TWO))
 (61 61 (:LINEAR EXPT-<=-1-ONE))
 (61 61 (:LINEAR EXPT-<-1-ONE))
 (45 45
     (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (45 45
     (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (44 44 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (44 44
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (44 44
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (44 44
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (44 44
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (44 44
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (44 44 (:REWRITE |(equal c (/ x))|))
 (44 44 (:REWRITE |(equal c (- x))|))
 (44 44 (:REWRITE |(equal (/ x) c)|))
 (44 44 (:REWRITE |(equal (/ x) (/ y))|))
 (44 44 (:REWRITE |(equal (- x) c)|))
 (44 44 (:REWRITE |(equal (- x) (- y))|))
 (43 43 (:REWRITE ZP-OPEN))
 (11 11
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (11 11
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1)))
(RTL::R-NEG-RNE-30)
(RTL::R-NEG-RNE-31
 (4865
  4865
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (4865
      4865
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (4865
     4865
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (4865 4865
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (2579 2579
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (2579 2579
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (2579 2579
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (2579 2579
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (2071 587 (:REWRITE DEFAULT-PLUS-2))
 (1729 281
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (1554 587 (:REWRITE DEFAULT-PLUS-1))
 (1324 34 (:REWRITE RTL::R-EXACTP-6))
 (1218 247
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (983 287 (:REWRITE DEFAULT-LESS-THAN-2))
 (771 287 (:REWRITE DEFAULT-LESS-THAN-1))
 (735 187 (:REWRITE DEFAULT-TIMES-2))
 (691 187 (:REWRITE DEFAULT-TIMES-1))
 (687 181 (:REWRITE SIMPLIFY-SUMS-<))
 (559 9 (:LINEAR EXPT->=-1-ONE))
 (549 9 (:LINEAR EXPT->-1-ONE))
 (503 9 (:LINEAR EXPT-X->=-X))
 (503 9 (:LINEAR EXPT-X->-X))
 (439 261 (:REWRITE |(< (- x) (- y))|))
 (359 123 (:REWRITE DEFAULT-MINUS))
 (319 259 (:REWRITE |(< (- x) c)|))
 (309 261
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (300 78 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (295 261
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (287 287 (:REWRITE THE-FLOOR-BELOW))
 (287 287 (:REWRITE THE-FLOOR-ABOVE))
 (281 281
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (281 281
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (268 261 (:REWRITE |(< (/ x) (/ y))|))
 (261 261
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (261 261
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (261 261
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (261 261
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (261 261
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (261 261
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (259 259 (:REWRITE INTEGERP-<-CONSTANT))
 (259 259 (:REWRITE CONSTANT-<-INTEGERP))
 (259 259 (:REWRITE |(< c (- x))|))
 (249 19 (:REWRITE ODD-EXPT-THM))
 (234 72 (:REWRITE |(< (+ (- c) x) y)|))
 (225 63 (:REWRITE |(< y (+ (- c) x))|))
 (216 8
      (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (208 8
      (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (158 158
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (129 69 (:REWRITE |(+ c (+ d x))|))
 (120 30 (:REWRITE RATIONALP-X))
 (98 20
     (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (95 67 (:REWRITE INTEGERP-MINUS-X))
 (90 3
     (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (90 3
     (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (90 3 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (90 3 (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (86 52 (:REWRITE DEFAULT-EXPT-2))
 (78 67 (:REWRITE REDUCE-INTEGERP-+))
 (78 26 (:REWRITE RTL::BVECP-EXACTP))
 (76 76 (:REWRITE |(< (+ c/d x) y)|))
 (71 71 (:REWRITE |(< x (+ c/d y))|))
 (67 67 (:META META-INTEGERP-CORRECT))
 (52 52 (:TYPE-PRESCRIPTION RTL::BVECP))
 (52 52 (:REWRITE DEFAULT-EXPT-1))
 (52 52 (:REWRITE |(expt 1/c n)|))
 (52 52 (:REWRITE |(expt (- x) n)|))
 (42 42 (:REWRITE DEFAULT-DIVIDE))
 (40 40
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (33 33 (:REWRITE |(< (* x y) 0)|))
 (30 30 (:REWRITE REDUCE-RATIONALP-+))
 (30 30 (:REWRITE REDUCE-RATIONALP-*))
 (30 30 (:REWRITE RATIONALP-MINUS-X))
 (30 30 (:META META-RATIONALP-CORRECT))
 (29 29 (:REWRITE |(< (/ x) 0)|))
 (27 27 (:REWRITE |(< 0 (* x y))|))
 (25 25 (:REWRITE |(- (* c x))|))
 (24 24 (:REWRITE |(* c (* d x))|))
 (24 6 (:REWRITE |(integerp (- x))|))
 (20 20 (:REWRITE FOLD-CONSTS-IN-+))
 (18 18
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (18 18
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (18 18
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (18 18
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (13 13
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (13 13
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (10 10 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (10 10 (:LINEAR EXPT-LINEAR-LOWER-<))
 (9 9 (:LINEAR EXPT-LINEAR-UPPER-<))
 (9 9 (:LINEAR EXPT->=-1-TWO))
 (9 9 (:LINEAR EXPT->-1-TWO))
 (9 9 (:LINEAR EXPT-<=-1-ONE))
 (9 9 (:LINEAR EXPT-<-1-ONE))
 (8 8
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (8 8
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (8 8 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (8 8
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (8 8
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (8 8
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (8 8
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (8 8
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (8 8 (:REWRITE |(equal c (/ x))|))
 (8 8 (:REWRITE |(equal c (- x))|))
 (8 8 (:REWRITE |(equal (/ x) c)|))
 (8 8 (:REWRITE |(equal (/ x) (/ y))|))
 (8 8 (:REWRITE |(equal (- x) c)|))
 (8 8 (:REWRITE |(equal (- x) (- y))|))
 (8 8
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (8 8
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (7 7 (:REWRITE ZP-OPEN))
 (5 5
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (5 5
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (5 5
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RTL::R-NEG-RNE-32)
(RTL::R-NEG-RNE-33
 (2460
  2460
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (2460
      2460
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (2460
     2460
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (2460 2460
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1757 1757
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (1757 1757
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (1757 1757
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (1757 1757
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (1004 286 (:REWRITE DEFAULT-PLUS-2))
 (818 286 (:REWRITE DEFAULT-PLUS-1))
 (815 20 (:REWRITE RTL::R-EXACTP-6))
 (724 130
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (629 144 (:REWRITE DEFAULT-LESS-THAN-2))
 (390 118 (:REWRITE DEFAULT-TIMES-1))
 (366 99 (:REWRITE SIMPLIFY-SUMS-<))
 (362 118 (:REWRITE DEFAULT-TIMES-2))
 (326 144 (:REWRITE DEFAULT-LESS-THAN-1))
 (230 140 (:REWRITE |(< (- x) (- y))|))
 (225 86 (:REWRITE DEFAULT-MINUS))
 (205 18 (:REWRITE ODD-EXPT-THM))
 (176 140
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (149 37 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (144 144 (:REWRITE THE-FLOOR-BELOW))
 (144 144 (:REWRITE THE-FLOOR-ABOVE))
 (140 140
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (140 140
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (140 140
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
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
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (140 140
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (140 140
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (140 140 (:REWRITE |(< (/ x) (/ y))|))
 (140 140 (:REWRITE |(< (- x) c)|))
 (135 5
      (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (130 5
      (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (84 84
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (84 21 (:REWRITE RATIONALP-X))
 (83 18
     (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (81 3 (:LINEAR EXPT->=-1-ONE))
 (79 3 (:LINEAR EXPT->-1-ONE))
 (71 51 (:REWRITE INTEGERP-MINUS-X))
 (71 3 (:LINEAR EXPT-X->=-X))
 (71 3 (:LINEAR EXPT-X->-X))
 (57 19 (:REWRITE RTL::BVECP-EXACTP))
 (51 51 (:REWRITE REDUCE-INTEGERP-+))
 (51 51 (:META META-INTEGERP-CORRECT))
 (47 28 (:REWRITE DEFAULT-EXPT-2))
 (40 40 (:REWRITE |(< (+ c/d x) y)|))
 (40 40 (:REWRITE |(< (+ (- c) x) y)|))
 (38 38 (:TYPE-PRESCRIPTION RTL::BVECP))
 (28 28 (:REWRITE DEFAULT-EXPT-1))
 (28 28 (:REWRITE |(expt 1/c n)|))
 (28 28 (:REWRITE |(expt (- x) n)|))
 (28 28 (:REWRITE |(< y (+ (- c) x))|))
 (28 28 (:REWRITE |(< x (+ c/d y))|))
 (24 24
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (24 24 (:REWRITE DEFAULT-DIVIDE))
 (21 21 (:REWRITE REDUCE-RATIONALP-+))
 (21 21 (:REWRITE REDUCE-RATIONALP-*))
 (21 21 (:REWRITE RATIONALP-MINUS-X))
 (21 21 (:META META-RATIONALP-CORRECT))
 (20 5 (:REWRITE |(integerp (- x))|))
 (18 18 (:REWRITE |(- (* c x))|))
 (15 15 (:REWRITE |(< (/ x) 0)|))
 (15 15 (:REWRITE |(< (* x y) 0)|))
 (13 13 (:REWRITE |(+ c (+ d x))|))
 (11 11 (:REWRITE |(* c (* d x))|))
 (8 8
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (8 8
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (6 6
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (5 5 (:REWRITE ZP-OPEN))
 (5 5 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (5 5
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (5 5
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (5 5
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (5 5
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (5 5 (:REWRITE FOLD-CONSTS-IN-+))
 (5 5
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (5 5 (:REWRITE |(equal c (/ x))|))
 (5 5 (:REWRITE |(equal c (- x))|))
 (5 5 (:REWRITE |(equal (/ x) c)|))
 (5 5 (:REWRITE |(equal (/ x) (/ y))|))
 (5 5 (:REWRITE |(equal (- x) c)|))
 (5 5 (:REWRITE |(equal (- x) (- y))|))
 (5 5
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (5 5
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (4 4 (:REWRITE |(< 0 (/ x))|))
 (4 4 (:REWRITE |(< 0 (* x y))|))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<))
 (3 3 (:LINEAR EXPT->=-1-TWO))
 (3 3 (:LINEAR EXPT->-1-TWO))
 (3 3 (:LINEAR EXPT-<=-1-ONE))
 (3 3 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-NEG-RNE-34
 (5869
  5869
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (5869
      5869
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (5869
     5869
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (5869 5869
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (4589 4589
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (4589 4589
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (4589 4589
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (4589 4589
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (2853 870 (:REWRITE DEFAULT-PLUS-2))
 (2281 870 (:REWRITE DEFAULT-PLUS-1))
 (2020 34 (:REWRITE RTL::R-EXACTP-6))
 (1856 487 (:REWRITE DEFAULT-LESS-THAN-2))
 (953 487 (:REWRITE DEFAULT-LESS-THAN-1))
 (699 473 (:REWRITE |(< (- x) (- y))|))
 (659 473
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (656 57 (:REWRITE ODD-EXPT-THM))
 (500 218 (:REWRITE DEFAULT-MINUS))
 (487 487 (:REWRITE THE-FLOOR-BELOW))
 (487 487 (:REWRITE THE-FLOOR-ABOVE))
 (475 475
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (475 475
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (475 475
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (473 473 (:REWRITE INTEGERP-<-CONSTANT))
 (473 473 (:REWRITE CONSTANT-<-INTEGERP))
 (473 473
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (473 473
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (473 473
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (473 473
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (473 473 (:REWRITE |(< c (- x))|))
 (473 473
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (473 473
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (473 473
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (473 473 (:REWRITE |(< (/ x) (/ y))|))
 (473 473 (:REWRITE |(< (- x) c)|))
 (378 14
      (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (364 14
      (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (336 110 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (330 57
      (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (234 78 (:REWRITE RTL::BVECP-EXACTP))
 (232 232
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (224 168 (:REWRITE INTEGERP-MINUS-X))
 (196 49 (:REWRITE RATIONALP-X))
 (168 168 (:REWRITE REDUCE-INTEGERP-+))
 (168 168 (:META META-INTEGERP-CORRECT))
 (166 166 (:REWRITE DEFAULT-TIMES-2))
 (166 166 (:REWRITE DEFAULT-TIMES-1))
 (156 156 (:TYPE-PRESCRIPTION RTL::BVECP))
 (128 128 (:REWRITE |(< (+ c/d x) y)|))
 (128 128 (:REWRITE |(< (+ (- c) x) y)|))
 (119 119
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (97 65 (:REWRITE DEFAULT-EXPT-2))
 (84 21 (:REWRITE |(integerp (- x))|))
 (81 3 (:LINEAR EXPT->=-1-ONE))
 (79 3 (:LINEAR EXPT->-1-ONE))
 (71 3 (:LINEAR EXPT-X->=-X))
 (71 3 (:LINEAR EXPT-X->-X))
 (70 70 (:REWRITE |(< y (+ (- c) x))|))
 (70 70 (:REWRITE |(< x (+ c/d y))|))
 (65 65 (:REWRITE DEFAULT-EXPT-1))
 (65 65 (:REWRITE |(expt 1/c n)|))
 (65 65 (:REWRITE |(expt (- x) n)|))
 (61 61
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (61 61 (:REWRITE DEFAULT-DIVIDE))
 (53 53 (:REWRITE |(- (* c x))|))
 (50 50 (:REWRITE |(+ c (+ d x))|))
 (49 49 (:REWRITE REDUCE-RATIONALP-+))
 (49 49 (:REWRITE REDUCE-RATIONALP-*))
 (49 49 (:REWRITE RATIONALP-MINUS-X))
 (49 49 (:META META-RATIONALP-CORRECT))
 (48 48 (:REWRITE |(< (/ x) 0)|))
 (48 48 (:REWRITE |(< (* x y) 0)|))
 (26 26 (:REWRITE FOLD-CONSTS-IN-+))
 (16 14 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (16 14
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (16 14
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (14 14
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (14 14
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (14 14
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (14 14
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (14 14
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (14 14 (:REWRITE |(equal c (/ x))|))
 (14 14 (:REWRITE |(equal c (- x))|))
 (14 14 (:REWRITE |(equal (/ x) c)|))
 (14 14 (:REWRITE |(equal (/ x) (/ y))|))
 (14 14 (:REWRITE |(equal (- x) c)|))
 (14 14 (:REWRITE |(equal (- x) (- y))|))
 (14 14
     (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (14 14
     (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (13 13 (:REWRITE ZP-OPEN))
 (9 9 (:REWRITE |(< 0 (* x y))|))
 (7 7 (:REWRITE |(< 0 (/ x))|))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (6 6
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (5 5 (:REWRITE |(* c (* d x))|))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<))
 (3 3 (:LINEAR EXPT->=-1-TWO))
 (3 3 (:LINEAR EXPT->-1-TWO))
 (3 3 (:LINEAR EXPT-<=-1-ONE))
 (3 3 (:LINEAR EXPT-<-1-ONE))
 (2 2
    (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (2 2
    (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (2 2
    (:REWRITE |(< x (/ y)) with (< y 0)|)))
(RTL::R-NEG-RNE-DOWN
 (290154 1813 (:REWRITE RTL::R-EXACTP-6))
 (124656
  124656
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (124656
      124656
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (124656
     124656
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (124656 124656
         (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (103860 27583 (:REWRITE DEFAULT-PLUS-2))
 (70359 70359
        (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (70359 70359
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (70359 70359
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (70359 70359
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (70171 27583 (:REWRITE DEFAULT-PLUS-1))
 (36981 8738
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (32259 349 (:LINEAR EXPT->=-1-ONE))
 (31903 349 (:LINEAR EXPT-X->=-X))
 (31903 349 (:LINEAR EXPT-X->-X))
 (31565 349 (:LINEAR EXPT->-1-ONE))
 (27705 9032 (:REWRITE DEFAULT-LESS-THAN-2))
 (19890 9032 (:REWRITE DEFAULT-LESS-THAN-1))
 (16989 4299 (:REWRITE DEFAULT-TIMES-2))
 (12612 3420 (:REWRITE DEFAULT-MINUS))
 (12401 8945 (:REWRITE |(< (- x) (- y))|))
 (11305 3639 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (9989 8945
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (9665 8945 (:REWRITE |(< (- x) c)|))
 (9395 8945 (:REWRITE |(< c (- x))|))
 (9032 9032 (:REWRITE THE-FLOOR-BELOW))
 (9032 9032 (:REWRITE THE-FLOOR-ABOVE))
 (8945 8945
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (8945 8945
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (8945 8945
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (8945 8945 (:REWRITE INTEGERP-<-CONSTANT))
 (8945 8945 (:REWRITE CONSTANT-<-INTEGERP))
 (8945 8945
       (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (8945 8945
       (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (8945 8945
       (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (8945 8945
       (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (8945 8945
       (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (8945 8945
       (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (8945 8945
       (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (8945 8945 (:REWRITE |(< (/ x) (/ y))|))
 (7367 7367
       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (4299 4299 (:REWRITE DEFAULT-TIMES-1))
 (3932 3932 (:REWRITE |(+ c (+ d x))|))
 (3733 1950 (:REWRITE DEFAULT-EXPT-2))
 (2943 109
       (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (2834 109
       (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (2709 2709 (:REWRITE |(< (+ c/d x) y)|))
 (2709 2709 (:REWRITE |(< (+ (- c) x) y)|))
 (2454 2454 (:REWRITE |(< y (+ (- c) x))|))
 (2454 2454 (:REWRITE |(< x (+ c/d y))|))
 (2389 347
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (2057 242 (:REWRITE ODD-EXPT-THM))
 (1964 491 (:REWRITE RATIONALP-X))
 (1953 651 (:REWRITE RTL::BVECP-EXACTP))
 (1950 1950 (:REWRITE DEFAULT-EXPT-1))
 (1950 1950 (:REWRITE |(expt 1/c n)|))
 (1950 1950 (:REWRITE |(expt (- x) n)|))
 (1815 242
       (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (1396 1396 (:REWRITE FOLD-CONSTS-IN-+))
 (1302 1302 (:TYPE-PRESCRIPTION RTL::BVECP))
 (1081 1081 (:REWRITE REDUCE-INTEGERP-+))
 (1081 1081 (:REWRITE INTEGERP-MINUS-X))
 (1081 1081 (:META META-INTEGERP-CORRECT))
 (969 969 (:REWRITE |(< (/ x) 0)|))
 (969 969 (:REWRITE |(< (* x y) 0)|))
 (920 920 (:REWRITE |(< 0 (/ x))|))
 (920 920 (:REWRITE |(< 0 (* x y))|))
 (782 376 (:REWRITE |(equal (/ x) c)|))
 (698 698
      (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (698 698
      (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (698 698
      (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (698 698
      (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (654 654 (:REWRITE DEFAULT-DIVIDE))
 (625 625
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (491 491 (:REWRITE REDUCE-RATIONALP-+))
 (491 491 (:REWRITE REDUCE-RATIONALP-*))
 (491 491 (:REWRITE RATIONALP-MINUS-X))
 (491 491 (:META META-RATIONALP-CORRECT))
 (484 121 (:REWRITE |(integerp (- x))|))
 (402 402 (:REWRITE |(* (- x) y)|))
 (376 376
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (376 376
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (376 376 (:REWRITE |(equal c (/ x))|))
 (376 376 (:REWRITE |(equal (/ x) (/ y))|))
 (376 376 (:REWRITE |(equal (- x) (- y))|))
 (349 349 (:LINEAR EXPT-LINEAR-UPPER-<))
 (349 349 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (349 349 (:LINEAR EXPT-LINEAR-LOWER-<))
 (349 349 (:LINEAR EXPT->=-1-TWO))
 (349 349 (:LINEAR EXPT->-1-TWO))
 (349 349 (:LINEAR EXPT-<=-1-ONE))
 (349 349 (:LINEAR EXPT-<-1-ONE))
 (347 347
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (347 347 (:REWRITE |(equal c (- x))|))
 (347 347 (:REWRITE |(equal (- x) c)|))
 (224 224 (:REWRITE |(* c (* d x))|))
 (157 157 (:REWRITE ZP-OPEN))
 (124 124
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (124 124
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (109 109
      (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (109 109
      (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (72 72 (:REWRITE |(equal (+ (- c) x) y)|))
 (64 2 (:LINEAR RTL::RNE-POSITIVE))
 (29 29
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (29 29 (:REWRITE |(not (equal x (/ y)))|))
 (29 29 (:REWRITE |(equal x (/ y))|))
 (29 29 (:REWRITE |(/ (/ x))|))
 (24 24 (:REWRITE |(equal (expt 2 n) c)|))
 (11 11
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (11 11
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON)))
(RTL::R-NEG-RNE-UP-4
 (7 7 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (7 7 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (7 7 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (7 7 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (7
  7
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (7 7
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (7 7
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (7 7
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (7 7
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (7 7
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE)))
(RTL::R-NEG-RNE-UP-5
 (756 756
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (756 756
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (756 756
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (756 756
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (753
  753
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (753 753
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (753
     753
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (753 753
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (753 753
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (753 753
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (404 101 (:REWRITE DEFAULT-PLUS-2))
 (392 10 (:REWRITE RTL::R-EXACTP-6))
 (326 58
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (266 101 (:REWRITE DEFAULT-PLUS-1))
 (253 65 (:REWRITE DEFAULT-LESS-THAN-1))
 (175 65 (:REWRITE DEFAULT-LESS-THAN-2))
 (173 47 (:REWRITE SIMPLIFY-SUMS-<))
 (103 37 (:REWRITE DEFAULT-TIMES-2))
 (89 29 (:REWRITE DEFAULT-MINUS))
 (85 64
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (80 2 (:LINEAR EXPT->=-1-ONE))
 (80 2 (:LINEAR EXPT-<=-1-TWO))
 (78 2 (:LINEAR EXPT->-1-ONE))
 (78 2 (:LINEAR EXPT-<-1-TWO))
 (72 64 (:REWRITE |(< (- x) (- y))|))
 (70 2 (:LINEAR EXPT-X->=-X))
 (70 2 (:LINEAR EXPT-X->-X))
 (65 65 (:REWRITE THE-FLOOR-BELOW))
 (65 65 (:REWRITE THE-FLOOR-ABOVE))
 (64 64
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (64 64
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (64 64
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (64 64 (:REWRITE INTEGERP-<-CONSTANT))
 (64 64 (:REWRITE CONSTANT-<-INTEGERP))
 (64 64
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (64 64
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (64 64
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (64 64
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (64 64 (:REWRITE |(< c (- x))|))
 (64 64
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (64 64
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (64 64
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (64 64 (:REWRITE |(< (/ x) (/ y))|))
 (64 64 (:REWRITE |(< (- x) c)|))
 (59 3 (:REWRITE ODD-EXPT-THM))
 (54 2
     (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (52 2
     (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (43 11 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (37 37
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (37 37 (:REWRITE DEFAULT-TIMES-1))
 (27 9 (:REWRITE RTL::BVECP-EXACTP))
 (24 16 (:REWRITE INTEGERP-MINUS-X))
 (24 6 (:REWRITE RATIONALP-X))
 (22 22
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (20 10 (:REWRITE DEFAULT-EXPT-2))
 (18 18 (:TYPE-PRESCRIPTION RTL::BVECP))
 (17 17 (:REWRITE |(< y (+ (- c) x))|))
 (17 17 (:REWRITE |(< x (+ c/d y))|))
 (16 16 (:REWRITE REDUCE-INTEGERP-+))
 (16 16 (:META META-INTEGERP-CORRECT))
 (15 15 (:REWRITE |(< (+ c/d x) y)|))
 (15 15 (:REWRITE |(< (+ (- c) x) y)|))
 (13 13
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (13 13 (:REWRITE DEFAULT-DIVIDE))
 (10 10 (:REWRITE DEFAULT-EXPT-1))
 (10 10 (:REWRITE |(expt 1/c n)|))
 (10 10 (:REWRITE |(expt (- x) n)|))
 (9 9 (:REWRITE |(+ c (+ d x))|))
 (8 8 (:REWRITE |(- (* c x))|))
 (6 6 (:REWRITE REDUCE-RATIONALP-+))
 (6 6 (:REWRITE REDUCE-RATIONALP-*))
 (6 6 (:REWRITE RATIONALP-MINUS-X))
 (6 6 (:REWRITE |(< (/ x) 0)|))
 (6 6 (:REWRITE |(< (* x y) 0)|))
 (6 6 (:META META-RATIONALP-CORRECT))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (4 4 (:REWRITE |(< 0 (/ x))|))
 (4 4 (:REWRITE |(< 0 (* x y))|))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (3 3 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (3 3 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (2 2
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (2 2
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (2 2
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (2 2
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (2 2
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (2 2 (:REWRITE |(equal c (/ x))|))
 (2 2 (:REWRITE |(equal c (- x))|))
 (2 2 (:REWRITE |(equal (/ x) c)|))
 (2 2 (:REWRITE |(equal (/ x) (/ y))|))
 (2 2 (:REWRITE |(equal (- x) c)|))
 (2 2 (:REWRITE |(equal (- x) (- y))|))
 (2 2
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (2 2
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-NEG-RNE-UP-6
 (1023
  1023
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1023
      1023
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1023
     1023
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1023 1023
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1023 1023
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (1023 1023
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (889 889
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (889 889
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (889 889
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (889 889
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (557 124 (:REWRITE DEFAULT-PLUS-2))
 (501 10 (:REWRITE RTL::R-EXACTP-6))
 (429 73
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (385 124 (:REWRITE DEFAULT-PLUS-1))
 (307 79 (:REWRITE DEFAULT-LESS-THAN-1))
 (259 79 (:REWRITE DEFAULT-LESS-THAN-2))
 (226 58 (:REWRITE SIMPLIFY-SUMS-<))
 (101 77
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (98 30 (:REWRITE DEFAULT-MINUS))
 (97 5 (:REWRITE ODD-EXPT-THM))
 (89 77 (:REWRITE |(< (- x) (- y))|))
 (81 3
     (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (80 2 (:LINEAR EXPT->=-1-ONE))
 (80 2 (:LINEAR EXPT-<=-1-TWO))
 (79 79 (:REWRITE THE-FLOOR-BELOW))
 (79 79 (:REWRITE THE-FLOOR-ABOVE))
 (78 3
     (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (78 2 (:LINEAR EXPT->-1-ONE))
 (78 2 (:LINEAR EXPT-<-1-TWO))
 (77 77
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (77 77
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (77 77
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (77 77 (:REWRITE INTEGERP-<-CONSTANT))
 (77 77 (:REWRITE CONSTANT-<-INTEGERP))
 (77 77
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (77 77
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (77 77
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (77 77
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (77 77 (:REWRITE |(< c (- x))|))
 (77 77
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (77 77
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (77 77
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (77 77 (:REWRITE |(< (/ x) (/ y))|))
 (77 77 (:REWRITE |(< (- x) c)|))
 (70 2 (:LINEAR EXPT-X->=-X))
 (70 2 (:LINEAR EXPT-X->-X))
 (67 15 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (65 23 (:REWRITE DEFAULT-TIMES-2))
 (39 39
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (36 12 (:REWRITE RTL::BVECP-EXACTP))
 (36 9 (:REWRITE RATIONALP-X))
 (34 22 (:REWRITE INTEGERP-MINUS-X))
 (24 24 (:TYPE-PRESCRIPTION RTL::BVECP))
 (23 23 (:REWRITE DEFAULT-TIMES-1))
 (22 22 (:REWRITE REDUCE-INTEGERP-+))
 (22 22 (:META META-INTEGERP-CORRECT))
 (20 20 (:REWRITE |(< y (+ (- c) x))|))
 (20 20 (:REWRITE |(< x (+ c/d y))|))
 (20 10 (:REWRITE DEFAULT-EXPT-2))
 (19 19 (:REWRITE |(< (+ c/d x) y)|))
 (19 19 (:REWRITE |(< (+ (- c) x) y)|))
 (18 18
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (11 11
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (11 11 (:REWRITE DEFAULT-DIVIDE))
 (11 11 (:REWRITE |(+ c (+ d x))|))
 (10 10 (:REWRITE DEFAULT-EXPT-1))
 (10 10 (:REWRITE |(expt 1/c n)|))
 (10 10 (:REWRITE |(expt (- x) n)|))
 (9 9 (:REWRITE REDUCE-RATIONALP-+))
 (9 9 (:REWRITE REDUCE-RATIONALP-*))
 (9 9 (:REWRITE RATIONALP-MINUS-X))
 (9 9 (:META META-RATIONALP-CORRECT))
 (7 7 (:REWRITE |(< (/ x) 0)|))
 (7 7 (:REWRITE |(< (* x y) 0)|))
 (5 5 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (4 4 (:REWRITE |(< 0 (/ x))|))
 (4 4 (:REWRITE |(< 0 (* x y))|))
 (4 4 (:REWRITE |(- (* c x))|))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (3 3 (:REWRITE ZP-OPEN))
 (3 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (3 3
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (3 3
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (3 3
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (3 3
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (3 3 (:REWRITE FOLD-CONSTS-IN-+))
 (3 3
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (3 3 (:REWRITE |(equal c (/ x))|))
 (3 3 (:REWRITE |(equal c (- x))|))
 (3 3 (:REWRITE |(equal (/ x) c)|))
 (3 3 (:REWRITE |(equal (/ x) (/ y))|))
 (3 3 (:REWRITE |(equal (- x) c)|))
 (3 3 (:REWRITE |(equal (- x) (- y))|))
 (3 3
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (3 3
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-NEG-UP-8
 (24
  24
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (24 24
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (24 24
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (24 24
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (24 24
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (24 24
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (16 16
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4A-EXPT))
 (16 16
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (16 16
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (16 16
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT)))
(RTL::R-NEG-UP-9
 (218
  218
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (218 218
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (218
     218
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (218 218
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (218 218
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (107 17 (:REWRITE DEFAULT-TIMES-2))
 (86 86
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (86 86
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (86 86
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (72 17 (:REWRITE DEFAULT-TIMES-1))
 (53 1 (:REWRITE ODD-EXPT-THM))
 (49 5
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (49 5 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (42 7 (:REWRITE DEFAULT-LESS-THAN-2))
 (40 5 (:REWRITE SIMPLIFY-SUMS-<))
 (38 7 (:REWRITE |(< c (- x))|))
 (28 28
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (28 28
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (28 28
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (28 28
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (25 7 (:REWRITE DEFAULT-LESS-THAN-1))
 (11 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (9 9 (:REWRITE DEFAULT-EXPT-2))
 (9 9 (:REWRITE DEFAULT-EXPT-1))
 (9 9 (:REWRITE |(expt 1/c n)|))
 (9 9 (:REWRITE |(expt (- x) n)|))
 (8 2 (:REWRITE RATIONALP-X))
 (7 7 (:REWRITE THE-FLOOR-BELOW))
 (7 7 (:REWRITE THE-FLOOR-ABOVE))
 (7 7
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (7 7
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (7 7 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (7 7 (:REWRITE DEFAULT-MINUS))
 (7 7
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (7 7
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (7 7
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (7 7
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (7 7
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (7 7
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (7 7
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (7 7
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (7 7 (:REWRITE |(< (/ x) (/ y))|))
 (7 7 (:REWRITE |(< (- x) (- y))|))
 (6 6 (:REWRITE INTEGERP-<-CONSTANT))
 (6 6 (:REWRITE CONSTANT-<-INTEGERP))
 (6 6 (:REWRITE |(< (- x) c)|))
 (5 5 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (3 3 (:REWRITE REDUCE-INTEGERP-+))
 (3 3 (:REWRITE INTEGERP-MINUS-X))
 (3 3 (:META META-INTEGERP-CORRECT))
 (3 2 (:REWRITE DEFAULT-PLUS-1))
 (2 2 (:REWRITE REDUCE-RATIONALP-+))
 (2 2 (:REWRITE REDUCE-RATIONALP-*))
 (2 2 (:REWRITE RATIONALP-MINUS-X))
 (2 2 (:REWRITE DEFAULT-PLUS-2))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:REWRITE |(< 0 (* x y))|))
 (2 2 (:META META-RATIONALP-CORRECT))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (* x y) 0)|))
 (1 1 (:REWRITE |(- (- x))|)))
(RTL::R-NEG-RNE-UP-10)
(RTL::R-NEG-RNE-UP-11
 (1175
  1175
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1175
      1175
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1175
     1175
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1175 1175
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1175 1175
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (1175 1175
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (873 873
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (873 873
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (873 873
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (873 873
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (741 131 (:REWRITE DEFAULT-PLUS-2))
 (611 11 (:REWRITE RTL::R-EXACTP-6))
 (511 131 (:REWRITE DEFAULT-PLUS-1))
 (496 76
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (352 82 (:REWRITE DEFAULT-LESS-THAN-2))
 (284 82 (:REWRITE DEFAULT-LESS-THAN-1))
 (259 61 (:REWRITE SIMPLIFY-SUMS-<))
 (189 39 (:REWRITE DEFAULT-TIMES-1))
 (133 36 (:REWRITE DEFAULT-MINUS))
 (129 39 (:REWRITE DEFAULT-TIMES-2))
 (108 4
      (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (104 80
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (104 4
      (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (97 15 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (97 5 (:REWRITE ODD-EXPT-THM))
 (92 80 (:REWRITE |(< (- x) (- y))|))
 (82 82 (:REWRITE THE-FLOOR-BELOW))
 (82 82 (:REWRITE THE-FLOOR-ABOVE))
 (80 80
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (80 80
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (80 80
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (80 80 (:REWRITE INTEGERP-<-CONSTANT))
 (80 80 (:REWRITE CONSTANT-<-INTEGERP))
 (80 80
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (80 80
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (80 80
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (80 80
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (80 80 (:REWRITE |(< c (- x))|))
 (80 80
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (80 80
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (80 80
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (80 80 (:REWRITE |(< (/ x) (/ y))|))
 (80 80 (:REWRITE |(< (- x) c)|))
 (80 2 (:LINEAR EXPT->=-1-ONE))
 (80 2 (:LINEAR EXPT-<=-1-TWO))
 (78 2 (:LINEAR EXPT->-1-ONE))
 (78 2 (:LINEAR EXPT-<-1-TWO))
 (70 2 (:LINEAR EXPT-X->=-X))
 (70 2 (:LINEAR EXPT-X->-X))
 (43 43
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (36 12 (:REWRITE RTL::BVECP-EXACTP))
 (36 9 (:REWRITE RATIONALP-X))
 (34 22 (:REWRITE INTEGERP-MINUS-X))
 (27 27
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (24 24 (:TYPE-PRESCRIPTION RTL::BVECP))
 (22 22 (:REWRITE REDUCE-INTEGERP-+))
 (22 22 (:META META-INTEGERP-CORRECT))
 (20 20 (:REWRITE |(< y (+ (- c) x))|))
 (20 20 (:REWRITE |(< x (+ c/d y))|))
 (20 10 (:REWRITE DEFAULT-EXPT-2))
 (19 19 (:REWRITE |(< (+ c/d x) y)|))
 (19 19 (:REWRITE |(< (+ (- c) x) y)|))
 (11 11
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (11 11 (:REWRITE DEFAULT-DIVIDE))
 (11 11 (:REWRITE |(+ c (+ d x))|))
 (10 10 (:REWRITE DEFAULT-EXPT-1))
 (10 10 (:REWRITE |(expt 1/c n)|))
 (10 10 (:REWRITE |(expt (- x) n)|))
 (9 9 (:REWRITE REDUCE-RATIONALP-+))
 (9 9 (:REWRITE REDUCE-RATIONALP-*))
 (9 9 (:REWRITE RATIONALP-MINUS-X))
 (9 9 (:META META-RATIONALP-CORRECT))
 (7 7 (:REWRITE |(< (/ x) 0)|))
 (7 7 (:REWRITE |(< (* x y) 0)|))
 (6 6 (:REWRITE |(- (* c x))|))
 (5 5 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (4 4
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (4 4 (:REWRITE |(< 0 (/ x))|))
 (4 4 (:REWRITE |(< 0 (* x y))|))
 (4 4
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (3 3 (:REWRITE ZP-OPEN))
 (3 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (3 3
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (3 3
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (3 3
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (3 3
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (3 3 (:REWRITE FOLD-CONSTS-IN-+))
 (3 3
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (3 3 (:REWRITE |(equal c (/ x))|))
 (3 3 (:REWRITE |(equal c (- x))|))
 (3 3 (:REWRITE |(equal (/ x) c)|))
 (3 3 (:REWRITE |(equal (/ x) (/ y))|))
 (3 3 (:REWRITE |(equal (- x) c)|))
 (3 3 (:REWRITE |(equal (- x) (- y))|))
 (3 3 (:REWRITE |(* c (* d x))|))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-NEG-RNE-UP-17
 (1018
  1018
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1018
      1018
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1018
     1018
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1018 1018
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1003 1003
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (1003 1003
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (1003 1003
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (1003 1003
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (842 17 (:REWRITE RTL::R-EXACTP-6))
 (800 208 (:REWRITE DEFAULT-PLUS-2))
 (592 208 (:REWRITE DEFAULT-PLUS-1))
 (554 92
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (431 101 (:REWRITE DEFAULT-LESS-THAN-2))
 (379 79 (:REWRITE DEFAULT-TIMES-1))
 (329 101 (:REWRITE DEFAULT-LESS-THAN-1))
 (277 71 (:REWRITE SIMPLIFY-SUMS-<))
 (259 79 (:REWRITE DEFAULT-TIMES-2))
 (222 74 (:REWRITE DEFAULT-MINUS))
 (190 12 (:REWRITE ODD-EXPT-THM))
 (135 5
      (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (130 5
      (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (116 96 (:REWRITE |(< (- x) (- y))|))
 (114 96
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (101 101 (:REWRITE THE-FLOOR-BELOW))
 (101 101 (:REWRITE THE-FLOOR-ABOVE))
 (96 96
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (96 96
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (96 96
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (96 96 (:REWRITE INTEGERP-<-CONSTANT))
 (96 96 (:REWRITE CONSTANT-<-INTEGERP))
 (96 96
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (96 96
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (96 96
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (96 96
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (96 96 (:REWRITE |(< c (- x))|))
 (96 96
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (96 96
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (96 96
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (96 96 (:REWRITE |(< (/ x) (/ y))|))
 (96 96 (:REWRITE |(< (- x) c)|))
 (81 21 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (81 3 (:LINEAR EXPT->=-1-ONE))
 (79 3 (:LINEAR EXPT->-1-ONE))
 (75 75
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (74 26 (:REWRITE RTL::BVECP-EXACTP))
 (71 3 (:LINEAR EXPT-X->=-X))
 (71 3 (:LINEAR EXPT-X->-X))
 (55 55
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (48 48 (:TYPE-PRESCRIPTION RTL::BVECP))
 (48 28 (:REWRITE INTEGERP-MINUS-X))
 (40 10 (:REWRITE RATIONALP-X))
 (38 12
     (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (35 20 (:REWRITE DEFAULT-EXPT-2))
 (28 28 (:REWRITE REDUCE-INTEGERP-+))
 (28 28 (:META META-INTEGERP-CORRECT))
 (27 27 (:REWRITE |(< (+ c/d x) y)|))
 (27 27 (:REWRITE |(< (+ (- c) x) y)|))
 (22 22 (:REWRITE |(< y (+ (- c) x))|))
 (22 22 (:REWRITE |(< x (+ c/d y))|))
 (20 20 (:REWRITE DEFAULT-EXPT-1))
 (20 20 (:REWRITE |(expt 1/c n)|))
 (20 20 (:REWRITE |(expt (- x) n)|))
 (16 16 (:REWRITE |(- (* c x))|))
 (14 14
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (14 14 (:REWRITE DEFAULT-DIVIDE))
 (13 13 (:REWRITE |(+ c (+ d x))|))
 (11 11 (:REWRITE |(< (/ x) 0)|))
 (11 11 (:REWRITE |(< (* x y) 0)|))
 (10 10 (:REWRITE REDUCE-RATIONALP-+))
 (10 10 (:REWRITE REDUCE-RATIONALP-*))
 (10 10 (:REWRITE RATIONALP-MINUS-X))
 (10 10 (:META META-RATIONALP-CORRECT))
 (8 2 (:REWRITE |(integerp (- x))|))
 (6 6 (:REWRITE |(* c (* d x))|))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (6 6
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (6 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (6 4
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (6 4
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (5 5
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (5 5
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (5 5 (:REWRITE FOLD-CONSTS-IN-+))
 (5 5
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (5 5
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (4 4
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (4 4
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (4 4
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (4 4 (:REWRITE |(equal c (/ x))|))
 (4 4 (:REWRITE |(equal c (- x))|))
 (4 4 (:REWRITE |(equal (/ x) c)|))
 (4 4 (:REWRITE |(equal (/ x) (/ y))|))
 (4 4 (:REWRITE |(equal (- x) c)|))
 (4 4 (:REWRITE |(equal (- x) (- y))|))
 (4 4 (:REWRITE |(< 0 (/ x))|))
 (4 4 (:REWRITE |(< 0 (* x y))|))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<))
 (3 3 (:LINEAR EXPT->=-1-TWO))
 (3 3 (:LINEAR EXPT->-1-TWO))
 (3 3 (:LINEAR EXPT-<=-1-ONE))
 (3 3 (:LINEAR EXPT-<-1-ONE))
 (2 2 (:REWRITE ZP-OPEN)))
(RTL::R-NEG-RNE-UP-20
 (25812
  25812
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (25812
      25812
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (25812
     25812
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (25812 25812
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (9490 1900 (:REWRITE DEFAULT-PLUS-2))
 (9202 9202
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (9202 9202
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (9202 9202
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (9202 9202
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (6893 1900 (:REWRITE DEFAULT-PLUS-1))
 (5729 804
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (4381 781 (:REWRITE DEFAULT-TIMES-1))
 (4244 879 (:REWRITE DEFAULT-LESS-THAN-2))
 (2941 781 (:REWRITE DEFAULT-TIMES-2))
 (2913 879 (:REWRITE DEFAULT-LESS-THAN-1))
 (2913 597 (:REWRITE SIMPLIFY-SUMS-<))
 (1929 581 (:REWRITE DEFAULT-MINUS))
 (1156 848 (:REWRITE |(< (- x) (- y))|))
 (1142 96 (:REWRITE ODD-EXPT-THM))
 (1112 848
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (1065 207 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (879 879 (:REWRITE THE-FLOOR-BELOW))
 (879 879 (:REWRITE THE-FLOOR-ABOVE))
 (870 848 (:REWRITE |(< (/ x) (/ y))|))
 (848 848
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (848 848
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (848 848
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (848 848 (:REWRITE INTEGERP-<-CONSTANT))
 (848 848 (:REWRITE CONSTANT-<-INTEGERP))
 (848 848
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (848 848
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (848 848
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (848 848
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (848 848 (:REWRITE |(< c (- x))|))
 (848 848
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (848 848
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (848 848
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (848 848 (:REWRITE |(< (- x) c)|))
 (665 665
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (594 22
      (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (572 22
      (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (538 96
      (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (532 133 (:REWRITE RATIONALP-X))
 (493 493
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (492 164 (:REWRITE RTL::BVECP-EXACTP))
 (405 317 (:REWRITE INTEGERP-MINUS-X))
 (332 200 (:REWRITE DEFAULT-EXPT-2))
 (328 328 (:TYPE-PRESCRIPTION RTL::BVECP))
 (317 317 (:REWRITE REDUCE-INTEGERP-+))
 (317 317 (:META META-INTEGERP-CORRECT))
 (242 242 (:REWRITE |(< (+ c/d x) y)|))
 (242 242 (:REWRITE |(< (+ (- c) x) y)|))
 (200 200 (:REWRITE DEFAULT-EXPT-1))
 (200 200 (:REWRITE |(expt 1/c n)|))
 (200 200 (:REWRITE |(expt (- x) n)|))
 (172 172 (:REWRITE |(< y (+ (- c) x))|))
 (172 172 (:REWRITE |(< x (+ c/d y))|))
 (137 137 (:REWRITE |(- (* c x))|))
 (136 34 (:REWRITE |(integerp (- x))|))
 (133 133 (:REWRITE REDUCE-RATIONALP-+))
 (133 133 (:REWRITE REDUCE-RATIONALP-*))
 (133 133 (:REWRITE RATIONALP-MINUS-X))
 (133 133 (:META META-RATIONALP-CORRECT))
 (114 114 (:REWRITE |(+ c (+ d x))|))
 (87 87
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (87 87 (:REWRITE DEFAULT-DIVIDE))
 (81 3 (:LINEAR EXPT->=-1-ONE))
 (79 3 (:LINEAR EXPT->-1-ONE))
 (72 72 (:REWRITE |(* c (* d x))|))
 (71 3 (:LINEAR EXPT-X->=-X))
 (71 3 (:LINEAR EXPT-X->-X))
 (69 69 (:REWRITE |(< (/ x) 0)|))
 (69 69 (:REWRITE |(< (* x y) 0)|))
 (44 44 (:REWRITE FOLD-CONSTS-IN-+))
 (39 39 (:REWRITE |(< 0 (/ x))|))
 (39 39 (:REWRITE |(< 0 (* x y))|))
 (36 36
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (36 36
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (33 33 (:REWRITE ZP-OPEN))
 (33 33 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (33 33
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (33 33
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (33 33
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (33 33
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (33 33
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (33 33 (:REWRITE |(equal c (/ x))|))
 (33 33 (:REWRITE |(equal c (- x))|))
 (33 33 (:REWRITE |(equal (/ x) c)|))
 (33 33 (:REWRITE |(equal (/ x) (/ y))|))
 (33 33 (:REWRITE |(equal (- x) c)|))
 (33 33 (:REWRITE |(equal (- x) (- y))|))
 (22 22
     (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (22 22
     (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (11 11
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (11 11
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (6 6
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<))
 (3 3 (:LINEAR EXPT->=-1-TWO))
 (3 3 (:LINEAR EXPT->-1-TWO))
 (3 3 (:LINEAR EXPT-<=-1-ONE))
 (3 3 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-NEG-UP-13
 (216
  216
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (216 216
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (216
     216
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (216 216
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (109 24 (:REWRITE DEFAULT-PLUS-1))
 (105 24 (:REWRITE DEFAULT-PLUS-2))
 (68 14
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (60 15 (:REWRITE DEFAULT-LESS-THAN-2))
 (33 15 (:REWRITE DEFAULT-LESS-THAN-1))
 (32 14 (:REWRITE |(< (- x) (- y))|))
 (26 8 (:REWRITE DEFAULT-MINUS))
 (22 4 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (20 14
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (19 10 (:REWRITE SIMPLIFY-SUMS-<))
 (17 2 (:REWRITE ODD-EXPT-THM))
 (15 15 (:REWRITE THE-FLOOR-BELOW))
 (15 15 (:REWRITE THE-FLOOR-ABOVE))
 (15 2 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (14 14 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (14 14
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (14 14
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (14 14
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (14 14
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
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
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (14 14
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (14 14
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (14 14 (:REWRITE |(< (/ x) (/ y))|))
 (14 14 (:REWRITE |(< (- x) c)|))
 (12 3 (:REWRITE RATIONALP-X))
 (10 10
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (10 10
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (7 7 (:REWRITE REDUCE-INTEGERP-+))
 (7 7
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (7 7 (:REWRITE INTEGERP-MINUS-X))
 (7 7 (:META META-INTEGERP-CORRECT))
 (6 6 (:REWRITE DEFAULT-EXPT-2))
 (6 6 (:REWRITE DEFAULT-EXPT-1))
 (6 6 (:REWRITE |(expt 1/c n)|))
 (6 6 (:REWRITE |(expt (- x) n)|))
 (6 2 (:REWRITE RTL::BVECP-EXACTP))
 (5 5 (:REWRITE |(< (+ c/d x) y)|))
 (5 5 (:REWRITE |(< (+ (- c) x) y)|))
 (4 4 (:TYPE-PRESCRIPTION RTL::BVECP))
 (4 1 (:REWRITE |(integerp (- x))|))
 (3 3 (:REWRITE REDUCE-RATIONALP-+))
 (3 3 (:REWRITE REDUCE-RATIONALP-*))
 (3 3 (:REWRITE RATIONALP-MINUS-X))
 (3 3
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (3 3 (:REWRITE DEFAULT-TIMES-2))
 (3 3 (:REWRITE DEFAULT-TIMES-1))
 (3 3 (:REWRITE |(< y (+ (- c) x))|))
 (3 3 (:REWRITE |(< x (+ c/d y))|))
 (3 3 (:META META-RATIONALP-CORRECT))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (* x y) 0)|))
 (1 1 (:REWRITE |(- (* c x))|))
 (1 1 (:LINEAR EXPT-X->=-X))
 (1 1 (:LINEAR EXPT-X->-X))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<))
 (1 1 (:LINEAR EXPT->=-1-TWO))
 (1 1 (:LINEAR EXPT->=-1-ONE))
 (1 1 (:LINEAR EXPT->-1-TWO))
 (1 1 (:LINEAR EXPT->-1-ONE))
 (1 1 (:LINEAR EXPT-<=-1-ONE))
 (1 1 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-NEG-UP-15
 (7379 7379
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (7379 7379
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (7379 7379
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (5037 685
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
 (5037 685
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
 (3213 633
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3D))
 (3213 633
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1D))
 (3009 685
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
 (2809 633
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2D))
 (2707
  2707
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (2707
      2707
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (2707
     2707
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (2707 2707
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (965 173 (:REWRITE DEFAULT-PLUS-2))
 (961 18
      (:REWRITE |(< (/ x) y) with (< 0 x)|))
 (783 214 (:REWRITE DEFAULT-LESS-THAN-2))
 (640 640
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (640 640
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (640 640
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (640 640
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (633 633
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4H))
 (633 633
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3H))
 (633 633
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2H))
 (633 633
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1H))
 (594 151
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (413 89 (:REWRITE DEFAULT-MINUS))
 (401 81 (:REWRITE DEFAULT-TIMES-2))
 (387 173 (:REWRITE DEFAULT-PLUS-1))
 (313 214 (:REWRITE DEFAULT-LESS-THAN-1))
 (235 135 (:REWRITE SIMPLIFY-SUMS-<))
 (220 166
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (214 214 (:REWRITE THE-FLOOR-BELOW))
 (214 214 (:REWRITE THE-FLOOR-ABOVE))
 (202 166 (:REWRITE |(< (/ x) (/ y))|))
 (202 166 (:REWRITE |(< (- x) (- y))|))
 (199 199
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (199 199
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (169 81 (:REWRITE DEFAULT-TIMES-1))
 (169 18
      (:REWRITE |(<= x (/ y)) with (< y 0)|))
 (169 18
      (:REWRITE |(< (/ x) y) with (< x 0)|))
 (168 4 (:REWRITE |(* (* x y) z)|))
 (166 166
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (166 166
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (166 166
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (166 166
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (166 166
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (166 166
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (166 166
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (155 155 (:REWRITE INTEGERP-<-CONSTANT))
 (155 155 (:REWRITE CONSTANT-<-INTEGERP))
 (155 155 (:REWRITE |(< (- x) c)|))
 (120 4 (:REWRITE |(* y (* x z))|))
 (96 24 (:REWRITE RATIONALP-X))
 (86 10 (:REWRITE ODD-EXPT-THM))
 (79 43 (:REWRITE DEFAULT-DIVIDE))
 (76 10
     (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (64 64
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (62 62
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (54 18 (:REWRITE RTL::BVECP-EXACTP))
 (53 53 (:REWRITE |(< 0 (* x y))|))
 (52 52 (:REWRITE REDUCE-INTEGERP-+))
 (52 52 (:REWRITE INTEGERP-MINUS-X))
 (52 52 (:META META-INTEGERP-CORRECT))
 (52 16 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (52 4 (:REWRITE |(* y x)|))
 (43 43
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (42 42 (:REWRITE DEFAULT-EXPT-2))
 (42 42 (:REWRITE DEFAULT-EXPT-1))
 (42 42 (:REWRITE |(expt 1/c n)|))
 (42 42 (:REWRITE |(expt (- x) n)|))
 (36 36 (:TYPE-PRESCRIPTION RTL::BVECP))
 (34 34 (:REWRITE |(< (* x y) 0)|))
 (31 31
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (31 31
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (31 31 (:REWRITE |(< 0 (/ x))|))
 (24 24 (:REWRITE REDUCE-RATIONALP-+))
 (24 24 (:REWRITE REDUCE-RATIONALP-*))
 (24 24 (:REWRITE RATIONALP-MINUS-X))
 (24 24 (:META META-RATIONALP-CORRECT))
 (24 6 (:REWRITE |(integerp (- x))|))
 (23 23 (:REWRITE |(< (/ x) 0)|))
 (21 21 (:REWRITE |(< x (+ c/d y))|))
 (20 20 (:REWRITE |(< (+ c/d x) y)|))
 (20 20 (:REWRITE |(< (+ (- c) x) y)|))
 (19 19
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (19 19
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (17 17
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (17 17
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (11 11
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (11 11 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (11 11
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (11 11
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (11 11
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (11 11
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (11 11
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (11 11 (:REWRITE |(equal c (/ x))|))
 (11 11 (:REWRITE |(equal c (- x))|))
 (11 11 (:REWRITE |(equal (/ x) c)|))
 (11 11 (:REWRITE |(equal (/ x) (/ y))|))
 (11 11 (:REWRITE |(equal (- x) c)|))
 (11 11 (:REWRITE |(equal (- x) (- y))|))
 (11 11
     (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (11 11
     (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (11 11
     (:REWRITE |(< x (/ y)) with (< y 0)|))
 (10 10 (:REWRITE |(< y (+ (- c) x))|))
 (8 8 (:REWRITE ZP-OPEN))
 (8 8 (:REWRITE |(* c (* d x))|))
 (6 6 (:REWRITE |(- (* c x))|))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (1 1 (:LINEAR EXPT-X->=-X))
 (1 1 (:LINEAR EXPT-X->-X))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<))
 (1 1 (:LINEAR EXPT->=-1-TWO))
 (1 1 (:LINEAR EXPT->=-1-ONE))
 (1 1 (:LINEAR EXPT->-1-TWO))
 (1 1 (:LINEAR EXPT->-1-ONE))
 (1 1 (:LINEAR EXPT-<=-1-ONE))
 (1 1 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-NEG-UP-16
 (856
  856
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (856 856
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (856
     856
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (856 856
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (489 489
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (489 489
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (489 489
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (249 71 (:REWRITE DEFAULT-LESS-THAN-2))
 (216 65
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (197 71 (:REWRITE DEFAULT-PLUS-2))
 (172 4
      (:REWRITE |(<= x (/ y)) with (< y 0)|))
 (172 4
      (:REWRITE |(<= x (/ y)) with (< 0 y)|))
 (172 4 (:REWRITE |(< (/ x) y) with (< x 0)|))
 (172 4 (:REWRITE |(< (/ x) y) with (< 0 x)|))
 (153 71 (:REWRITE DEFAULT-PLUS-1))
 (135 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
 (135 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
 (134 55 (:REWRITE SIMPLIFY-SUMS-<))
 (105 69 (:REWRITE |(< (/ x) (/ y))|))
 (99 69
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (80 71 (:REWRITE DEFAULT-LESS-THAN-1))
 (78 69 (:REWRITE |(< c (- x))|))
 (75 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-3D))
 (75 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
 (75 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-2D))
 (75 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-1D))
 (72 27 (:REWRITE DEFAULT-MINUS))
 (71 71 (:REWRITE THE-FLOOR-BELOW))
 (71 71 (:REWRITE THE-FLOOR-ABOVE))
 (69 69
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (69 69
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (69 69
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (69 69 (:REWRITE INTEGERP-<-CONSTANT))
 (69 69 (:REWRITE CONSTANT-<-INTEGERP))
 (69 69
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (69 69
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (69 69
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (69 69
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (69 69
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (69 69
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (69 69
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (69 69 (:REWRITE |(< (- x) c)|))
 (69 69 (:REWRITE |(< (- x) (- y))|))
 (60 7 (:REWRITE ODD-EXPT-THM))
 (57 13 (:REWRITE DEFAULT-TIMES-2))
 (53 7 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (48 12 (:REWRITE RATIONALP-X))
 (45 9 (:REWRITE DEFAULT-DIVIDE))
 (30 10 (:REWRITE RTL::BVECP-EXACTP))
 (29 29 (:REWRITE REDUCE-INTEGERP-+))
 (29 29 (:REWRITE INTEGERP-MINUS-X))
 (29 29 (:META META-INTEGERP-CORRECT))
 (20 20 (:TYPE-PRESCRIPTION RTL::BVECP))
 (19 10 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (18 18
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (17 17 (:REWRITE DEFAULT-EXPT-2))
 (17 17 (:REWRITE DEFAULT-EXPT-1))
 (17 17 (:REWRITE |(expt 1/c n)|))
 (17 17 (:REWRITE |(expt (- x) n)|))
 (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (16 4 (:REWRITE |(integerp (- x))|))
 (15 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-4H))
 (15 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-3H))
 (15 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-2H))
 (15 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-1H))
 (13 13 (:REWRITE DEFAULT-TIMES-1))
 (13 13 (:REWRITE |(< (/ x) 0)|))
 (13 13 (:REWRITE |(< (* x y) 0)|))
 (12 12 (:REWRITE REDUCE-RATIONALP-+))
 (12 12 (:REWRITE REDUCE-RATIONALP-*))
 (12 12 (:REWRITE RATIONALP-MINUS-X))
 (12 12
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (12 12 (:REWRITE |(< (+ c/d x) y)|))
 (12 12 (:REWRITE |(< (+ (- c) x) y)|))
 (12 12 (:META META-RATIONALP-CORRECT))
 (11 11
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (11 11
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (10 10 (:REWRITE |(< 0 (/ x))|))
 (10 10 (:REWRITE |(< 0 (* x y))|))
 (9 9
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (9 9
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (9 9
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (5 5 (:REWRITE |(< y (+ (- c) x))|))
 (5 5 (:REWRITE |(< x (+ c/d y))|))
 (5 5 (:REWRITE |(- (* c x))|))
 (4 4 (:REWRITE ZP-OPEN))
 (4 4 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (4 4 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (1 1
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (1 1 (:LINEAR EXPT-X->=-X))
 (1 1 (:LINEAR EXPT-X->-X))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1 1 (:LINEAR EXPT->=-1-TWO))
 (1 1 (:LINEAR EXPT->=-1-ONE))
 (1 1 (:LINEAR EXPT->-1-TWO))
 (1 1 (:LINEAR EXPT->-1-ONE))
 (1 1 (:LINEAR EXPT-<=-1-ONE))
 (1 1 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-NEG-UP-21
 (668 74
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (668 74
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (505
  505
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (505 505
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (505
     505
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (505 505
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (144 23 (:REWRITE DEFAULT-TIMES-2))
 (124 25 (:REWRITE DEFAULT-PLUS-2))
 (116 23 (:REWRITE DEFAULT-TIMES-1))
 (111 25 (:REWRITE DEFAULT-PLUS-1))
 (74 74
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4A-EXPT))
 (74 74
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (73 15 (:REWRITE DEFAULT-LESS-THAN-2))
 (53 8 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (51 15 (:REWRITE DEFAULT-LESS-THAN-1))
 (42 15 (:REWRITE |(< (- x) (- y))|))
 (36 9 (:REWRITE DEFAULT-MINUS))
 (30 3
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (30 3
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (27 15
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (15 15 (:REWRITE THE-FLOOR-BELOW))
 (15 15 (:REWRITE THE-FLOOR-ABOVE))
 (15 15
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (15 15
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (15 15
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (15 15 (:REWRITE INTEGERP-<-CONSTANT))
 (15 15 (:REWRITE CONSTANT-<-INTEGERP))
 (15 15
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (15 15
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (15 15
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (15 15
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (15 15 (:REWRITE |(< c (- x))|))
 (15 15
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (15 15
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (15 15
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (15 15 (:REWRITE |(< (/ x) (/ y))|))
 (15 15 (:REWRITE |(< (- x) c)|))
 (12 4 (:REWRITE RTL::BVECP-EXACTP))
 (9 9
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (8 8 (:TYPE-PRESCRIPTION RTL::BVECP))
 (8 8 (:REWRITE SIMPLIFY-SUMS-<))
 (8 2 (:REWRITE RATIONALP-X))
 (6 6 (:REWRITE REDUCE-INTEGERP-+))
 (6 6 (:REWRITE INTEGERP-MINUS-X))
 (6 6 (:META META-INTEGERP-CORRECT))
 (5 5 (:REWRITE DEFAULT-EXPT-2))
 (5 5 (:REWRITE DEFAULT-EXPT-1))
 (5 5 (:REWRITE |(expt 1/c n)|))
 (5 5 (:REWRITE |(expt (- x) n)|))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (3 3 (:REWRITE |(< (+ c/d x) y)|))
 (3 3 (:REWRITE |(< (+ (- c) x) y)|))
 (2 2 (:REWRITE REDUCE-RATIONALP-+))
 (2 2 (:REWRITE REDUCE-RATIONALP-*))
 (2 2 (:REWRITE RATIONALP-MINUS-X))
 (2 2 (:REWRITE |(< y (+ (- c) x))|))
 (2 2 (:REWRITE |(< x (+ c/d y))|))
 (2 2 (:REWRITE |(* (- x) y)|))
 (2 2 (:META META-RATIONALP-CORRECT))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (1 1 (:REWRITE ODD-EXPT-THM))
 (1 1 (:REWRITE |(< 0 (/ x))|))
 (1 1 (:REWRITE |(< 0 (* x y))|)))
(RTL::R-NEG-UP-22
 (1143 74 (:REWRITE DEFAULT-PLUS-2))
 (654
  654
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (654 654
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (654
     654
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (654 654
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (550 55
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (550 55
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (518 74 (:REWRITE DEFAULT-PLUS-1))
 (407 62 (:REWRITE DEFAULT-TIMES-2))
 (312 62 (:REWRITE DEFAULT-TIMES-1))
 (180 18
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (180 18
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (176 20 (:REWRITE DEFAULT-LESS-THAN-2))
 (154 20 (:REWRITE DEFAULT-LESS-THAN-1))
 (131 19 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (109 20 (:REWRITE |(< (- x) (- y))|))
 (83 16 (:REWRITE DEFAULT-MINUS))
 (55 55
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (55 55
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (32 20
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (25 25
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (20 20 (:REWRITE THE-FLOOR-BELOW))
 (20 20 (:REWRITE THE-FLOOR-ABOVE))
 (20 20
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (20 20
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (20 20
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (20 20 (:REWRITE INTEGERP-<-CONSTANT))
 (20 20 (:REWRITE CONSTANT-<-INTEGERP))
 (20 20
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (20 20
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (20 20
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (20 20
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (20 20 (:REWRITE |(< c (- x))|))
 (20 20
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (20 20
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (20 20
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (20 20 (:REWRITE |(< (/ x) (/ y))|))
 (20 20 (:REWRITE |(< (- x) c)|))
 (18 18
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4A-EXPT))
 (18 18
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (12 4 (:REWRITE RTL::BVECP-EXACTP))
 (8 8 (:TYPE-PRESCRIPTION RTL::BVECP))
 (8 8 (:REWRITE DEFAULT-EXPT-2))
 (8 8 (:REWRITE DEFAULT-EXPT-1))
 (8 8 (:REWRITE |(expt 1/c n)|))
 (8 8 (:REWRITE |(expt (- x) n)|))
 (8 8 (:REWRITE |(+ c (+ d x))|))
 (8 2 (:REWRITE RATIONALP-X))
 (6 6 (:REWRITE REDUCE-INTEGERP-+))
 (6 6 (:REWRITE INTEGERP-MINUS-X))
 (6 6 (:META META-INTEGERP-CORRECT))
 (5 5 (:REWRITE FOLD-CONSTS-IN-+))
 (5 5 (:REWRITE |(< y (+ (- c) x))|))
 (5 5 (:REWRITE |(< x (+ c/d y))|))
 (5 5 (:REWRITE |(< (+ c/d x) y)|))
 (5 5 (:REWRITE |(< (+ (- c) x) y)|))
 (4 4 (:REWRITE |(* (- x) y)|))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2 (:REWRITE REDUCE-RATIONALP-+))
 (2 2 (:REWRITE REDUCE-RATIONALP-*))
 (2 2 (:REWRITE RATIONALP-MINUS-X))
 (2 2 (:REWRITE ODD-EXPT-THM))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:REWRITE |(< 0 (* x y))|))
 (2 2 (:META META-RATIONALP-CORRECT))
 (1 1 (:REWRITE ZP-OPEN)))
(RTL::R-NEG-UP-23
 (2663 155 (:REWRITE DEFAULT-PLUS-2))
 (1575
  1575
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1575
      1575
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1575
     1575
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1575 1575
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1147 147 (:REWRITE DEFAULT-TIMES-2))
 (1142 155 (:REWRITE DEFAULT-PLUS-1))
 (1130 113
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (1130 113
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (840 147 (:REWRITE DEFAULT-TIMES-1))
 (353 353
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (353 353
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (353 353
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (296 50 (:REWRITE DEFAULT-MINUS))
 (295 33 (:REWRITE DEFAULT-LESS-THAN-2))
 (292 33 (:REWRITE DEFAULT-LESS-THAN-1))
 (197 27 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (175 33 (:REWRITE |(< (- x) (- y))|))
 (129 129
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
 (129 129
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
 (129 129
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
 (113 113
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (113 113
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (70 70
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (60 6 (:REWRITE DEFAULT-DIVIDE))
 (51 33
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (42 33 (:REWRITE |(< c (- x))|))
 (33 33 (:REWRITE THE-FLOOR-BELOW))
 (33 33 (:REWRITE THE-FLOOR-ABOVE))
 (33 33
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (33 33
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (33 33
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (33 33 (:REWRITE INTEGERP-<-CONSTANT))
 (33 33 (:REWRITE CONSTANT-<-INTEGERP))
 (33 33
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (33 33
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (33 33
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (33 33
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (33 33
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (33 33
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (33 33
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (33 33 (:REWRITE |(< (/ x) (/ y))|))
 (33 33 (:REWRITE |(< (- x) c)|))
 (26 26 (:REWRITE DEFAULT-EXPT-2))
 (26 26 (:REWRITE DEFAULT-EXPT-1))
 (26 26 (:REWRITE |(expt 1/c n)|))
 (26 26 (:REWRITE |(expt (- x) n)|))
 (18 18 (:REWRITE |(+ c (+ d x))|))
 (18 6 (:REWRITE RTL::BVECP-EXACTP))
 (16 4 (:REWRITE RATIONALP-X))
 (12 12 (:TYPE-PRESCRIPTION RTL::BVECP))
 (12 12 (:REWRITE FOLD-CONSTS-IN-+))
 (10 10 (:REWRITE REDUCE-INTEGERP-+))
 (10 10 (:REWRITE INTEGERP-MINUS-X))
 (10 10 (:META META-INTEGERP-CORRECT))
 (9 9 (:REWRITE |(< y (+ (- c) x))|))
 (9 9 (:REWRITE |(< x (+ c/d y))|))
 (9 9 (:REWRITE |(< (+ c/d x) y)|))
 (9 9 (:REWRITE |(< (+ (- c) x) y)|))
 (6 6
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (5 5 (:REWRITE |(* (- x) y)|))
 (4 4 (:REWRITE REDUCE-RATIONALP-+))
 (4 4 (:REWRITE REDUCE-RATIONALP-*))
 (4 4 (:REWRITE RATIONALP-MINUS-X))
 (4 4 (:META META-RATIONALP-CORRECT))
 (3 3 (:REWRITE |(< 0 (/ x))|))
 (3 3 (:REWRITE |(< 0 (* x y))|))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2 (:REWRITE ODD-EXPT-THM))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<)))
(RTL::R-NEG-UP-24
 (153
  153
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (153 153
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (153
     153
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (153 153
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (153 153
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (141 16 (:REWRITE DEFAULT-TIMES-2))
 (115 16 (:REWRITE DEFAULT-TIMES-1))
 (74 7 (:REWRITE DEFAULT-PLUS-2))
 (63 63 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (63 63 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (63 63 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (34 7 (:REWRITE DEFAULT-MINUS))
 (20 2 (:REWRITE DEFAULT-DIVIDE))
 (15 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
 (15 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
 (15 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
 (15 6 (:REWRITE DEFAULT-LESS-THAN-1))
 (12 6
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (11 2 (:REWRITE SIMPLIFY-SUMS-<))
 (11 2
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (11 2 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (7 7
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (7 7 (:REWRITE NORMALIZE-ADDENDS))
 (7 7 (:REWRITE DEFAULT-PLUS-1))
 (6 6 (:REWRITE THE-FLOOR-BELOW))
 (6 6 (:REWRITE THE-FLOOR-ABOVE))
 (6 6
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (6 6
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (6 6 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
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
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (6 6
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (6 6
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (6 6 (:REWRITE |(< (/ x) (/ y))|))
 (6 6 (:REWRITE |(< (- x) c)|))
 (6 6 (:REWRITE |(< (- x) (- y))|))
 (6 2 (:REWRITE RTL::BVECP-EXACTP))
 (5 5
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (4 4 (:TYPE-PRESCRIPTION RTL::BVECP))
 (4 4 (:REWRITE DEFAULT-EXPT-2))
 (4 4 (:REWRITE DEFAULT-EXPT-1))
 (4 4 (:REWRITE |(expt 1/c n)|))
 (4 4 (:REWRITE |(expt (- x) n)|))
 (2 2 (:REWRITE REDUCE-INTEGERP-+))
 (2 2
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (2 2 (:REWRITE INTEGERP-MINUS-X))
 (2 2 (:META META-INTEGERP-CORRECT))
 (1 1 (:REWRITE |(< (+ c/d x) y)|))
 (1 1 (:REWRITE |(< (+ (- c) x) y)|)))
(RTL::R-NEG-RNE-UP-25
 (5484
  5484
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (5484
      5484
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (5484
     5484
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (5484 5484
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (2921 2921
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (2921 2921
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (2921 2921
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (1647 368 (:REWRITE DEFAULT-PLUS-2))
 (1270 208
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (1123 368 (:REWRITE DEFAULT-PLUS-1))
 (1061 260 (:REWRITE DEFAULT-LESS-THAN-2))
 (864 17 (:REWRITE RTL::R-EXACTP-6))
 (742 164 (:REWRITE SIMPLIFY-SUMS-<))
 (675 260 (:REWRITE DEFAULT-LESS-THAN-1))
 (360 252
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (353 116 (:REWRITE DEFAULT-MINUS))
 (331 81 (:REWRITE DEFAULT-TIMES-1))
 (303 81 (:REWRITE DEFAULT-TIMES-2))
 (292 24 (:REWRITE ODD-EXPT-THM))
 (282 252 (:REWRITE |(< (- x) (- y))|))
 (262 252 (:REWRITE |(< (/ x) (/ y))|))
 (260 260 (:REWRITE THE-FLOOR-BELOW))
 (260 260 (:REWRITE THE-FLOOR-ABOVE))
 (252 252
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (252 252
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (252 252
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (252 252 (:REWRITE INTEGERP-<-CONSTANT))
 (252 252 (:REWRITE CONSTANT-<-INTEGERP))
 (252 252
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (252 252
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (252 252
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (252 252
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (252 252 (:REWRITE |(< c (- x))|))
 (252 252
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (252 252
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (252 252
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (252 252 (:REWRITE |(< (- x) c)|))
 (243 5
      (:REWRITE |(<= x (/ y)) with (< y 0)|))
 (243 5
      (:REWRITE |(<= x (/ y)) with (< 0 y)|))
 (243 5 (:REWRITE |(< (/ x) y) with (< x 0)|))
 (243 5 (:REWRITE |(< (/ x) y) with (< 0 x)|))
 (184 44 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (135 5
      (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (130 5
      (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (129 43 (:REWRITE RTL::BVECP-EXACTP))
 (128 24
      (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (121 121
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (108 27 (:REWRITE RATIONALP-X))
 (107 87 (:REWRITE INTEGERP-MINUS-X))
 (102 30 (:REWRITE DEFAULT-DIVIDE))
 (87 87 (:REWRITE REDUCE-INTEGERP-+))
 (87 87 (:META META-INTEGERP-CORRECT))
 (86 86 (:TYPE-PRESCRIPTION RTL::BVECP))
 (81 3 (:LINEAR EXPT->=-1-ONE))
 (79 3 (:LINEAR EXPT->-1-ONE))
 (71 3 (:LINEAR EXPT-X->=-X))
 (71 3 (:LINEAR EXPT-X->-X))
 (64 47 (:REWRITE DEFAULT-EXPT-2))
 (63 63 (:REWRITE |(< (+ c/d x) y)|))
 (63 63 (:REWRITE |(< (+ (- c) x) y)|))
 (61 61
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (47 47 (:REWRITE DEFAULT-EXPT-1))
 (47 47 (:REWRITE |(expt 1/c n)|))
 (47 47 (:REWRITE |(expt (- x) n)|))
 (37 37 (:REWRITE |(< y (+ (- c) x))|))
 (37 37 (:REWRITE |(< x (+ c/d y))|))
 (32 8 (:REWRITE |(integerp (- x))|))
 (30 30
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (30 30 (:REWRITE |(< (/ x) 0)|))
 (30 30 (:REWRITE |(< (* x y) 0)|))
 (27 27 (:REWRITE REDUCE-RATIONALP-+))
 (27 27 (:REWRITE REDUCE-RATIONALP-*))
 (27 27 (:REWRITE RATIONALP-MINUS-X))
 (27 27 (:META META-RATIONALP-CORRECT))
 (21 21 (:REWRITE |(- (* c x))|))
 (19 19 (:REWRITE |(+ c (+ d x))|))
 (14 14
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (14 14
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (14 14
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (14 14
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (14 14 (:REWRITE |(< 0 (/ x))|))
 (14 14 (:REWRITE |(< 0 (* x y))|))
 (11 11
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (11 11
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (7 7 (:REWRITE ZP-OPEN))
 (7 7 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (7 7
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (7 7
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (7 7
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (7 7
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (7 7
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (7 7 (:REWRITE |(equal c (/ x))|))
 (7 7 (:REWRITE |(equal c (- x))|))
 (7 7 (:REWRITE |(equal (/ x) c)|))
 (7 7 (:REWRITE |(equal (/ x) (/ y))|))
 (7 7 (:REWRITE |(equal (- x) c)|))
 (7 7 (:REWRITE |(equal (- x) (- y))|))
 (6 6 (:REWRITE FOLD-CONSTS-IN-+))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (6 6
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (5 5
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (5 5
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (5 5 (:REWRITE |(* c (* d x))|))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<))
 (3 3 (:LINEAR EXPT->=-1-TWO))
 (3 3 (:LINEAR EXPT->-1-TWO))
 (3 3 (:LINEAR EXPT-<=-1-ONE))
 (3 3 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-NEG-RNE-UP-30
 (7671
  7671
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (7671
      7671
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (7671
     7671
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (7671 7671
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (4064 584 (:REWRITE DEFAULT-TIMES-2))
 (4015 644 (:REWRITE DEFAULT-PLUS-2))
 (3463 3463
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (3463 3463
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (3463 3463
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (3463 3463
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (3400 6
       (:REWRITE |(<= x (/ y)) with (< 0 y)|))
 (3275 6 (:REWRITE |(< (/ x) y) with (< 0 x)|))
 (2824 644 (:REWRITE DEFAULT-PLUS-1))
 (2184 584 (:REWRITE DEFAULT-TIMES-1))
 (2008 362 (:REWRITE DEFAULT-LESS-THAN-2))
 (1615 48 (:REWRITE RTL::R-EXACTP-6))
 (1142 248 (:REWRITE SIMPLIFY-SUMS-<))
 (1048 362 (:REWRITE DEFAULT-LESS-THAN-1))
 (888 202 (:REWRITE DEFAULT-MINUS))
 (573 333 (:REWRITE |(< c (- x))|))
 (514 76 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (408 348
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (376 348 (:REWRITE |(< (- x) (- y))|))
 (362 362 (:REWRITE THE-FLOOR-BELOW))
 (362 362 (:REWRITE THE-FLOOR-ABOVE))
 (353 348 (:REWRITE |(< (/ x) (/ y))|))
 (348 348
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (348 348
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (348 348
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (348 348
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (348 348
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (348 348
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (348 348
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (348 348
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (348 348
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (348 348
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (334 26 (:REWRITE ODD-EXPT-THM))
 (333 333 (:REWRITE INTEGERP-<-CONSTANT))
 (333 333 (:REWRITE CONSTANT-<-INTEGERP))
 (333 333 (:REWRITE |(< (- x) c)|))
 (309 309
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (305 15
      (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (305 15
      (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (305 15
      (:REWRITE |(< x (/ y)) with (< y 0)|))
 (305 15
      (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (231 231
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (189 7
      (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (182 7
      (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (155 6
      (:REWRITE |(<= x (/ y)) with (< y 0)|))
 (155 6 (:REWRITE |(< (/ x) y) with (< x 0)|))
 (148 37 (:REWRITE RATIONALP-X))
 (130 26
      (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (111 83 (:REWRITE INTEGERP-MINUS-X))
 (110 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (109 61 (:REWRITE DEFAULT-EXPT-2))
 (93 31 (:REWRITE RTL::BVECP-EXACTP))
 (87 87 (:REWRITE |(* c (* d x))|))
 (83 83 (:REWRITE REDUCE-INTEGERP-+))
 (83 83 (:REWRITE |(< (+ c/d x) y)|))
 (83 83 (:REWRITE |(< (+ (- c) x) y)|))
 (83 83 (:META META-INTEGERP-CORRECT))
 (81 3 (:LINEAR EXPT->=-1-ONE))
 (79 3 (:LINEAR EXPT->-1-ONE))
 (76 76 (:REWRITE |(- (* c x))|))
 (71 3 (:LINEAR EXPT-X->=-X))
 (71 3 (:LINEAR EXPT-X->-X))
 (70 70 (:REWRITE DEFAULT-DIVIDE))
 (67 67 (:REWRITE |(< y (+ (- c) x))|))
 (67 67 (:REWRITE |(< x (+ c/d y))|))
 (62 62 (:TYPE-PRESCRIPTION RTL::BVECP))
 (62 62 (:REWRITE |(< 0 (* x y))|))
 (61 61 (:REWRITE DEFAULT-EXPT-1))
 (61 61 (:REWRITE |(expt 1/c n)|))
 (61 61 (:REWRITE |(expt (- x) n)|))
 (55 55
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (47 47 (:REWRITE |(+ c (+ d x))|))
 (43 43 (:REWRITE |(< (/ x) 0)|))
 (43 43 (:REWRITE |(< (* x y) 0)|))
 (42 42
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (42 42
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (37 37 (:REWRITE REDUCE-RATIONALP-+))
 (37 37 (:REWRITE REDUCE-RATIONALP-*))
 (37 37 (:REWRITE RATIONALP-MINUS-X))
 (37 37 (:META META-RATIONALP-CORRECT))
 (32 8 (:REWRITE |(integerp (- x))|))
 (26 26
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (26 26
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (14 14 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (14 14
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (14 14
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (14 14
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (14 14
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (14 14
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (14 14 (:REWRITE |(equal c (/ x))|))
 (14 14 (:REWRITE |(equal c (- x))|))
 (14 14 (:REWRITE |(equal (/ x) c)|))
 (14 14 (:REWRITE |(equal (/ x) (/ y))|))
 (14 14 (:REWRITE |(equal (- x) c)|))
 (14 14 (:REWRITE |(equal (- x) (- y))|))
 (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (9 9 (:REWRITE ZP-OPEN))
 (8 8
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (8 8
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (7 7 (:REWRITE FOLD-CONSTS-IN-+))
 (7 7
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (7 7
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (6 6
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<))
 (3 3 (:LINEAR EXPT->=-1-TWO))
 (3 3 (:LINEAR EXPT->-1-TWO))
 (3 3 (:LINEAR EXPT-<=-1-ONE))
 (3 3 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-NEG-RNE-UP-31
 (3849
  3849
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (3849
      3849
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (3849
     3849
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (3849 3849
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (2452 602 (:REWRITE DEFAULT-PLUS-2))
 (2240 2240
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (2240 2240
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (2240 2240
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (2240 2240
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (1742 294
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (1710 602 (:REWRITE DEFAULT-PLUS-1))
 (1590 267
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (1424 30 (:REWRITE RTL::R-EXACTP-6))
 (1325 305 (:REWRITE DEFAULT-LESS-THAN-2))
 (906 246 (:REWRITE DEFAULT-TIMES-1))
 (867 305 (:REWRITE DEFAULT-LESS-THAN-1))
 (866 246 (:REWRITE DEFAULT-TIMES-2))
 (840 192 (:REWRITE SIMPLIFY-SUMS-<))
 (559 9 (:LINEAR EXPT->=-1-ONE))
 (549 9 (:LINEAR EXPT->-1-ONE))
 (503 9 (:LINEAR EXPT-X->=-X))
 (503 9 (:LINEAR EXPT-X->-X))
 (391 123 (:REWRITE DEFAULT-MINUS))
 (372 272 (:REWRITE |(< c (- x))|))
 (334 24 (:REWRITE ODD-EXPT-THM))
 (322 274
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (308 274
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (305 305 (:REWRITE THE-FLOOR-BELOW))
 (305 305 (:REWRITE THE-FLOOR-ABOVE))
 (302 274 (:REWRITE |(< (- x) (- y))|))
 (294 294
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (294 294
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (293 75 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (275 274 (:REWRITE |(< (/ x) (/ y))|))
 (274 274
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (274 274
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (274 274
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (274 274
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (274 274
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (274 274
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (272 272 (:REWRITE INTEGERP-<-CONSTANT))
 (272 272 (:REWRITE CONSTANT-<-INTEGERP))
 (272 272 (:REWRITE |(< (- x) c)|))
 (244 82 (:REWRITE |(< (+ (- c) x) y)|))
 (233 71 (:REWRITE |(< y (+ (- c) x))|))
 (216 8
      (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (208 8
      (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (175 175
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (145 145
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (138 78 (:REWRITE |(+ c (+ d x))|))
 (120 30 (:REWRITE RATIONALP-X))
 (103 25
      (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (100 72 (:REWRITE INTEGERP-MINUS-X))
 (90 3
     (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (90 3
     (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (90 3 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (90 3 (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (86 86 (:REWRITE |(< (+ c/d x) y)|))
 (83 72 (:REWRITE REDUCE-INTEGERP-+))
 (79 79 (:REWRITE |(< x (+ c/d y))|))
 (78 48 (:REWRITE DEFAULT-EXPT-2))
 (78 26 (:REWRITE RTL::BVECP-EXACTP))
 (72 72 (:META META-INTEGERP-CORRECT))
 (52 52 (:TYPE-PRESCRIPTION RTL::BVECP))
 (48 48 (:REWRITE DEFAULT-EXPT-1))
 (48 48 (:REWRITE |(expt 1/c n)|))
 (48 48 (:REWRITE |(expt (- x) n)|))
 (40 40 (:REWRITE |(* c (* d x))|))
 (34 34 (:REWRITE |(- (* c x))|))
 (33 33 (:REWRITE DEFAULT-DIVIDE))
 (32 32 (:REWRITE |(< (* x y) 0)|))
 (31 31
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (30 30 (:REWRITE REDUCE-RATIONALP-+))
 (30 30 (:REWRITE REDUCE-RATIONALP-*))
 (30 30 (:REWRITE RATIONALP-MINUS-X))
 (30 30 (:META META-RATIONALP-CORRECT))
 (28 28 (:REWRITE |(< 0 (* x y))|))
 (28 28 (:REWRITE |(< (/ x) 0)|))
 (24 6 (:REWRITE |(integerp (- x))|))
 (20 20 (:REWRITE FOLD-CONSTS-IN-+))
 (18 18
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (18 18
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (18 18
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (18 18
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (13 13
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (13 13
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (10 10 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (10 10 (:LINEAR EXPT-LINEAR-LOWER-<))
 (9 9 (:LINEAR EXPT-LINEAR-UPPER-<))
 (9 9 (:LINEAR EXPT->=-1-TWO))
 (9 9 (:LINEAR EXPT->-1-TWO))
 (9 9 (:LINEAR EXPT-<=-1-ONE))
 (9 9 (:LINEAR EXPT-<-1-ONE))
 (8 8
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (8 8
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (8 8 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (8 8
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (8 8
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (8 8
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (8 8
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (8 8
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (8 8 (:REWRITE |(equal c (/ x))|))
 (8 8 (:REWRITE |(equal c (- x))|))
 (8 8 (:REWRITE |(equal (/ x) c)|))
 (8 8 (:REWRITE |(equal (/ x) (/ y))|))
 (8 8 (:REWRITE |(equal (- x) c)|))
 (8 8 (:REWRITE |(equal (- x) (- y))|))
 (8 8
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (8 8
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (7 7 (:REWRITE ZP-OPEN))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RTL::R-NEG-RNE-UP-32
 (6633
  6633
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (6633
      6633
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (6633
     6633
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (6633 6633
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (2791 2791
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (2791 2791
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (2791 2791
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (2791 2791
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (2348 587 (:REWRITE DEFAULT-PLUS-2))
 (2155 68 (:REWRITE RTL::R-EXACTP-6))
 (1987 537 (:REWRITE DEFAULT-TIMES-2))
 (1752 587 (:REWRITE DEFAULT-PLUS-1))
 (1607 537 (:REWRITE DEFAULT-TIMES-1))
 (1546 259
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (1098 272 (:REWRITE DEFAULT-LESS-THAN-2))
 (898 272 (:REWRITE DEFAULT-LESS-THAN-1))
 (802 198 (:REWRITE SIMPLIFY-SUMS-<))
 (702 257 (:REWRITE DEFAULT-MINUS))
 (334 26 (:REWRITE ODD-EXPT-THM))
 (323 263 (:REWRITE |(< c (- x))|))
 (323 263
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (291 263 (:REWRITE |(< (- x) (- y))|))
 (286 286
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (272 272 (:REWRITE THE-FLOOR-BELOW))
 (272 272 (:REWRITE THE-FLOOR-ABOVE))
 (263 263
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (263 263
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (263 263
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (263 263 (:REWRITE INTEGERP-<-CONSTANT))
 (263 263 (:REWRITE CONSTANT-<-INTEGERP))
 (263 263
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (263 263
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (263 263
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (263 263
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (263 263
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (263 263
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (263 263
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (263 263 (:REWRITE |(< (/ x) (/ y))|))
 (263 263 (:REWRITE |(< (- x) c)|))
 (259 61 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (238 238
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (189 7
      (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (182 7
      (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (148 37 (:REWRITE RATIONALP-X))
 (130 26
      (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (119 66 (:REWRITE DEFAULT-EXPT-2))
 (111 83 (:REWRITE INTEGERP-MINUS-X))
 (93 31 (:REWRITE RTL::BVECP-EXACTP))
 (83 83 (:REWRITE REDUCE-INTEGERP-+))
 (83 83 (:META META-INTEGERP-CORRECT))
 (81 3 (:LINEAR EXPT->=-1-ONE))
 (79 3 (:LINEAR EXPT->-1-ONE))
 (78 78 (:REWRITE |(* c (* d x))|))
 (73 73 (:REWRITE |(< (+ c/d x) y)|))
 (73 73 (:REWRITE |(< (+ (- c) x) y)|))
 (71 3 (:LINEAR EXPT-X->=-X))
 (71 3 (:LINEAR EXPT-X->-X))
 (66 66 (:REWRITE DEFAULT-EXPT-1))
 (66 66 (:REWRITE |(expt 1/c n)|))
 (66 66 (:REWRITE |(expt (- x) n)|))
 (63 63 (:REWRITE |(- (* c x))|))
 (62 62 (:TYPE-PRESCRIPTION RTL::BVECP))
 (52 52 (:REWRITE |(< y (+ (- c) x))|))
 (52 52 (:REWRITE |(< x (+ c/d y))|))
 (37 37 (:REWRITE REDUCE-RATIONALP-+))
 (37 37 (:REWRITE REDUCE-RATIONALP-*))
 (37 37 (:REWRITE RATIONALP-MINUS-X))
 (37 37 (:META META-RATIONALP-CORRECT))
 (32 32 (:REWRITE |(+ c (+ d x))|))
 (32 8 (:REWRITE |(integerp (- x))|))
 (30 3
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (30 3
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (25 25
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (25 25 (:REWRITE DEFAULT-DIVIDE))
 (21 21 (:REWRITE |(< (/ x) 0)|))
 (21 21 (:REWRITE |(< (* x y) 0)|))
 (9 9 (:REWRITE ZP-OPEN))
 (9 9 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (9 9
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (9 9
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (9 9
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (9 9
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (9 9
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (9 9 (:REWRITE |(equal c (/ x))|))
 (9 9 (:REWRITE |(equal c (- x))|))
 (9 9 (:REWRITE |(equal (/ x) c)|))
 (9 9 (:REWRITE |(equal (/ x) (/ y))|))
 (9 9 (:REWRITE |(equal (- x) c)|))
 (9 9 (:REWRITE |(equal (- x) (- y))|))
 (8 8
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (8 8
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (7 7 (:REWRITE FOLD-CONSTS-IN-+))
 (7 7
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (7 7
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (6 6
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (4 4 (:REWRITE |(< 0 (/ x))|))
 (4 4 (:REWRITE |(< 0 (* x y))|))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-4A-EXPT))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<))
 (3 3 (:LINEAR EXPT->=-1-TWO))
 (3 3 (:LINEAR EXPT->-1-TWO))
 (3 3 (:LINEAR EXPT-<=-1-ONE))
 (3 3 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-NEG-RNE-UP-33
 (2345
  2345
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (2345
      2345
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (2345
     2345
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (2345 2345
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1451 1451
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (1451 1451
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (1451 1451
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (1451 1451
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (1078 294 (:REWRITE DEFAULT-PLUS-2))
 (867 20 (:REWRITE RTL::R-EXACTP-6))
 (855 141
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (809 294 (:REWRITE DEFAULT-PLUS-1))
 (611 152 (:REWRITE DEFAULT-LESS-THAN-2))
 (534 152 (:REWRITE DEFAULT-LESS-THAN-1))
 (430 105 (:REWRITE SIMPLIFY-SUMS-<))
 (241 18 (:REWRITE ODD-EXPT-THM))
 (212 86 (:REWRITE DEFAULT-MINUS))
 (181 145
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (165 145 (:REWRITE |(< (- x) (- y))|))
 (165 95 (:REWRITE DEFAULT-TIMES-1))
 (152 152 (:REWRITE THE-FLOOR-BELOW))
 (152 152 (:REWRITE THE-FLOOR-ABOVE))
 (145 145
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (145 145
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (145 145
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (145 145 (:REWRITE INTEGERP-<-CONSTANT))
 (145 145 (:REWRITE CONSTANT-<-INTEGERP))
 (145 145
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (145 145
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (145 145
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (145 145
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (145 145 (:REWRITE |(< c (- x))|))
 (145 145
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (145 145
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (145 145
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (145 145 (:REWRITE |(< (/ x) (/ y))|))
 (145 145 (:REWRITE |(< (- x) c)|))
 (145 95 (:REWRITE DEFAULT-TIMES-2))
 (135 5
      (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (130 5
      (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (126 36 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (91 91
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (84 21 (:REWRITE RATIONALP-X))
 (83 18
     (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (81 3 (:LINEAR EXPT->=-1-ONE))
 (79 3 (:LINEAR EXPT->-1-ONE))
 (71 51 (:REWRITE INTEGERP-MINUS-X))
 (71 3 (:LINEAR EXPT-X->=-X))
 (71 3 (:LINEAR EXPT-X->-X))
 (59 59
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (57 19 (:REWRITE RTL::BVECP-EXACTP))
 (51 51 (:REWRITE REDUCE-INTEGERP-+))
 (51 51 (:META META-INTEGERP-CORRECT))
 (47 28 (:REWRITE DEFAULT-EXPT-2))
 (45 45 (:REWRITE |(< (+ c/d x) y)|))
 (45 45 (:REWRITE |(< (+ (- c) x) y)|))
 (38 38 (:TYPE-PRESCRIPTION RTL::BVECP))
 (33 33 (:REWRITE |(< y (+ (- c) x))|))
 (33 33 (:REWRITE |(< x (+ c/d y))|))
 (28 28 (:REWRITE DEFAULT-EXPT-1))
 (28 28 (:REWRITE |(expt 1/c n)|))
 (28 28 (:REWRITE |(expt (- x) n)|))
 (21 21 (:REWRITE REDUCE-RATIONALP-+))
 (21 21 (:REWRITE REDUCE-RATIONALP-*))
 (21 21 (:REWRITE RATIONALP-MINUS-X))
 (21 21 (:META META-RATIONALP-CORRECT))
 (20 5 (:REWRITE |(integerp (- x))|))
 (18 18 (:REWRITE |(- (* c x))|))
 (18 18 (:REWRITE |(+ c (+ d x))|))
 (17 17
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (17 17 (:REWRITE DEFAULT-DIVIDE))
 (15 15 (:REWRITE |(< (/ x) 0)|))
 (15 15 (:REWRITE |(< (* x y) 0)|))
 (9 9 (:REWRITE |(* c (* d x))|))
 (8 8
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (8 8
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (6 6
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (5 5 (:REWRITE ZP-OPEN))
 (5 5 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (5 5
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (5 5
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (5 5
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (5 5
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (5 5 (:REWRITE FOLD-CONSTS-IN-+))
 (5 5
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (5 5 (:REWRITE |(equal c (/ x))|))
 (5 5 (:REWRITE |(equal c (- x))|))
 (5 5 (:REWRITE |(equal (/ x) c)|))
 (5 5 (:REWRITE |(equal (/ x) (/ y))|))
 (5 5 (:REWRITE |(equal (- x) c)|))
 (5 5 (:REWRITE |(equal (- x) (- y))|))
 (5 5
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (5 5
    (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (4 4 (:REWRITE |(< 0 (/ x))|))
 (4 4 (:REWRITE |(< 0 (* x y))|))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<))
 (3 3 (:LINEAR EXPT->=-1-TWO))
 (3 3 (:LINEAR EXPT->-1-TWO))
 (3 3 (:LINEAR EXPT-<=-1-ONE))
 (3 3 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-NEG-RNE-UP-34
 (15455
  15455
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (15455
      15455
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (15455
     15455
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (15455 15455
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (10085 10085
        (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (10085 10085
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (10085 10085
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (10085 10085
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (9126 2258 (:REWRITE DEFAULT-PLUS-2))
 (6514 2258 (:REWRITE DEFAULT-PLUS-1))
 (5187 834
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (4334 94 (:REWRITE RTL::R-EXACTP-6))
 (4275 991 (:REWRITE DEFAULT-LESS-THAN-2))
 (2835 991 (:REWRITE DEFAULT-LESS-THAN-1))
 (1494 121 (:REWRITE ODD-EXPT-THM))
 (1317 493 (:REWRITE DEFAULT-MINUS))
 (1290 954
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (1226 954 (:REWRITE |(< (- x) (- y))|))
 (991 991 (:REWRITE THE-FLOOR-BELOW))
 (991 991 (:REWRITE THE-FLOOR-ABOVE))
 (989 277 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (954 954
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (954 954
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (954 954
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (954 954 (:REWRITE INTEGERP-<-CONSTANT))
 (954 954 (:REWRITE CONSTANT-<-INTEGERP))
 (954 954
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (954 954
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (954 954
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (954 954
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (954 954 (:REWRITE |(< c (- x))|))
 (954 954
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (954 954
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (954 954
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (954 954 (:REWRITE |(< (/ x) (/ y))|))
 (954 954 (:REWRITE |(< (- x) c)|))
 (756 28
      (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (728 28
      (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (661 661
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (628 121
      (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (447 335 (:REWRITE INTEGERP-MINUS-X))
 (438 146 (:REWRITE RTL::BVECP-EXACTP))
 (408 102 (:REWRITE RATIONALP-X))
 (362 362 (:REWRITE DEFAULT-TIMES-2))
 (362 362 (:REWRITE DEFAULT-TIMES-1))
 (335 335 (:REWRITE REDUCE-INTEGERP-+))
 (335 335 (:META META-INTEGERP-CORRECT))
 (303 303 (:REWRITE |(< (+ c/d x) y)|))
 (303 303 (:REWRITE |(< (+ (- c) x) y)|))
 (292 292 (:TYPE-PRESCRIPTION RTL::BVECP))
 (262 262
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (242 150 (:REWRITE DEFAULT-EXPT-2))
 (204 204 (:REWRITE |(+ c (+ d x))|))
 (194 194 (:REWRITE |(< y (+ (- c) x))|))
 (194 194 (:REWRITE |(< x (+ c/d y))|))
 (156 39 (:REWRITE |(integerp (- x))|))
 (150 150 (:REWRITE DEFAULT-EXPT-1))
 (150 150 (:REWRITE |(expt 1/c n)|))
 (150 150 (:REWRITE |(expt (- x) n)|))
 (119 119 (:REWRITE |(- (* c x))|))
 (117 117 (:REWRITE FOLD-CONSTS-IN-+))
 (106 106
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (106 106 (:REWRITE DEFAULT-DIVIDE))
 (102 102 (:REWRITE REDUCE-RATIONALP-+))
 (102 102 (:REWRITE REDUCE-RATIONALP-*))
 (102 102 (:REWRITE RATIONALP-MINUS-X))
 (102 102 (:META META-RATIONALP-CORRECT))
 (87 87 (:REWRITE |(< (/ x) 0)|))
 (87 87 (:REWRITE |(< (* x y) 0)|))
 (81 3 (:LINEAR EXPT->=-1-ONE))
 (79 3 (:LINEAR EXPT->-1-ONE))
 (71 3 (:LINEAR EXPT-X->=-X))
 (71 3 (:LINEAR EXPT-X->-X))
 (29 27 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (29 27
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (29 27
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (28 28
     (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (28 28
     (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (27 27
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (27 27
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (27 27
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (27 27 (:REWRITE |(equal c (/ x))|))
 (27 27 (:REWRITE |(equal c (- x))|))
 (27 27 (:REWRITE |(equal (/ x) c)|))
 (27 27 (:REWRITE |(equal (/ x) (/ y))|))
 (27 27 (:REWRITE |(equal (- x) c)|))
 (27 27 (:REWRITE |(equal (- x) (- y))|))
 (26 26 (:REWRITE ZP-OPEN))
 (20 20 (:REWRITE |(* c (* d x))|))
 (17 17
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (17 17
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (7 7 (:REWRITE |(< 0 (/ x))|))
 (7 7 (:REWRITE |(< 0 (* x y))|))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (6 6
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<))
 (3 3 (:LINEAR EXPT->=-1-TWO))
 (3 3 (:LINEAR EXPT->-1-TWO))
 (3 3 (:LINEAR EXPT-<=-1-ONE))
 (3 3 (:LINEAR EXPT-<-1-ONE)))
(RTL::R-NEG-RNE-UP
 (264493 2565 (:REWRITE RTL::R-EXACTP-6))
 (194070
  194070
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (194070
      194070
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (194070
     194070
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (194070 194070
         (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (130840 33910 (:REWRITE DEFAULT-PLUS-2))
 (104458 104458
         (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (104458 104458
         (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (104458 104458
         (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (104458 104458
         (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (90841 33910 (:REWRITE DEFAULT-PLUS-1))
 (51046 10727
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (37891 11020 (:REWRITE DEFAULT-LESS-THAN-2))
 (28626 11020 (:REWRITE DEFAULT-LESS-THAN-1))
 (27019 297 (:LINEAR EXPT->=-1-ONE))
 (26701 297 (:LINEAR EXPT-X->=-X))
 (26701 297 (:LINEAR EXPT-X->-X))
 (26437 297 (:LINEAR EXPT->-1-ONE))
 (24810 6960 (:REWRITE DEFAULT-TIMES-2))
 (19735 5287 (:REWRITE DEFAULT-MINUS))
 (14721 4157 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (12513 10815
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (11999 10815 (:REWRITE |(< (- x) (- y))|))
 (11435 10815 (:REWRITE |(< c (- x))|))
 (11295 10815 (:REWRITE |(< (- x) c)|))
 (11020 11020 (:REWRITE THE-FLOOR-BELOW))
 (11020 11020 (:REWRITE THE-FLOOR-ABOVE))
 (10815 10815
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (10815 10815
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (10815 10815
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (10815 10815 (:REWRITE INTEGERP-<-CONSTANT))
 (10815 10815 (:REWRITE CONSTANT-<-INTEGERP))
 (10815 10815
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (10815 10815
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (10815 10815
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (10815 10815
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (10815 10815
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (10815 10815
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (10815 10815
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (10815 10815 (:REWRITE |(< (/ x) (/ y))|))
 (10247 10247
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (6960 6960 (:REWRITE DEFAULT-TIMES-1))
 (5327 2802 (:REWRITE DEFAULT-EXPT-2))
 (4752 176
       (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (4576 176
       (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (4441 4441 (:REWRITE |(+ c (+ d x))|))
 (4433 597
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (3426 3426 (:REWRITE |(< (+ c/d x) y)|))
 (3426 3426 (:REWRITE |(< (+ (- c) x) y)|))
 (3356 839 (:REWRITE RATIONALP-X))
 (3315 390 (:REWRITE ODD-EXPT-THM))
 (3090 1030 (:REWRITE RTL::BVECP-EXACTP))
 (2925 390
       (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (2818 2818 (:REWRITE |(< y (+ (- c) x))|))
 (2818 2818 (:REWRITE |(< x (+ c/d y))|))
 (2802 2802 (:REWRITE DEFAULT-EXPT-1))
 (2802 2802 (:REWRITE |(expt 1/c n)|))
 (2802 2802 (:REWRITE |(expt (- x) n)|))
 (2762 478 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (2060 2060 (:TYPE-PRESCRIPTION RTL::BVECP))
 (1897 1897 (:REWRITE FOLD-CONSTS-IN-+))
 (1795 1795 (:REWRITE REDUCE-INTEGERP-+))
 (1795 1795 (:REWRITE INTEGERP-MINUS-X))
 (1795 1795 (:META META-INTEGERP-CORRECT))
 (1032 1032 (:REWRITE |(< (/ x) 0)|))
 (1032 1032 (:REWRITE |(< (* x y) 0)|))
 (910 910 (:REWRITE |(< 0 (/ x))|))
 (910 910 (:REWRITE |(< 0 (* x y))|))
 (839 839 (:REWRITE REDUCE-RATIONALP-+))
 (839 839 (:REWRITE REDUCE-RATIONALP-*))
 (839 839 (:REWRITE RATIONALP-MINUS-X))
 (839 839 (:META META-RATIONALP-CORRECT))
 (786 786
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (786 786 (:REWRITE DEFAULT-DIVIDE))
 (780 195 (:REWRITE |(integerp (- x))|))
 (673 673 (:REWRITE |(* (- x) y)|))
 (597 597
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (597 597
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (597 597
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (597 597 (:REWRITE |(equal c (/ x))|))
 (597 597 (:REWRITE |(equal c (- x))|))
 (597 597 (:REWRITE |(equal (/ x) c)|))
 (597 597 (:REWRITE |(equal (/ x) (/ y))|))
 (597 597 (:REWRITE |(equal (- x) c)|))
 (597 597 (:REWRITE |(equal (- x) (- y))|))
 (594 594
      (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (594 594
      (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (594 594
      (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (594 594
      (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (412 412 (:REWRITE |(* c (* d x))|))
 (297 297 (:LINEAR EXPT-LINEAR-UPPER-<))
 (297 297 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (297 297 (:LINEAR EXPT-LINEAR-LOWER-<))
 (297 297 (:LINEAR EXPT->=-1-TWO))
 (297 297 (:LINEAR EXPT->-1-TWO))
 (297 297 (:LINEAR EXPT-<=-1-ONE))
 (297 297 (:LINEAR EXPT-<-1-ONE))
 (261 261 (:REWRITE ZP-OPEN))
 (238 238 (:REWRITE |(equal (+ (- c) x) y)|))
 (177 177
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (177 177
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (176 176
      (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (176 176
      (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (34 34 (:REWRITE |(equal (expt 2 n) c)|))
 (12 12
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (12 12
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (11 11
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (11 11
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1)))
(RTL::R-NEG-RND
 (13099 13099
        (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (13099 13099
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (13099 13099
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (13099 13099
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (8500
  8500
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (8500
      8500
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (8500
     8500
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (8500 8500
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (4626 2069 (:REWRITE DEFAULT-PLUS-2))
 (4383 44 (:REWRITE RTL::R-EXACTP-6))
 (3840 944
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (3688 2069 (:REWRITE DEFAULT-PLUS-1))
 (3305 782
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (3104 968 (:REWRITE DEFAULT-LESS-THAN-2))
 (1954 968 (:REWRITE DEFAULT-LESS-THAN-1))
 (1902 1902
       (:TYPE-PRESCRIPTION RTL::RND-NON-POS))
 (1902 1902
       (:TYPE-PRESCRIPTION RTL::RND-NEGATIVE))
 (1578 544 (:REWRITE SIMPLIFY-SUMS-<))
 (1321 101 (:REWRITE ODD-EXPT-THM))
 (1222 150
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (1150 904
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (1072 904 (:REWRITE |(< (- x) (- y))|))
 (999 37
      (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (997 14 (:LINEAR EXPT->=-1-ONE))
 (980 14 (:LINEAR EXPT->-1-ONE))
 (968 968 (:REWRITE THE-FLOOR-BELOW))
 (968 968 (:REWRITE THE-FLOOR-ABOVE))
 (962 37
      (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (960 192 (:REWRITE ACL2-NUMBERP-X))
 (944 944
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (944 944
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (904 904 (:REWRITE INTEGERP-<-CONSTANT))
 (904 904 (:REWRITE CONSTANT-<-INTEGERP))
 (904 904
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (904 904
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (904 904
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (904 904
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (904 904 (:REWRITE |(< c (- x))|))
 (904 904
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (904 904
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (904 904
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (904 904 (:REWRITE |(< (/ x) (/ y))|))
 (904 904 (:REWRITE |(< (- x) c)|))
 (900 14 (:LINEAR EXPT-X->=-X))
 (900 14 (:LINEAR EXPT-X->-X))
 (829 463 (:REWRITE DEFAULT-MINUS))
 (814 814 (:REWRITE DEFAULT-TIMES-2))
 (814 814 (:REWRITE DEFAULT-TIMES-1))
 (744 186 (:REWRITE RATIONALP-X))
 (660 660
      (:TYPE-PRESCRIPTION RTL::COMMON-MODE-P))
 (620 296 (:REWRITE |(< (+ (- c) x) y)|))
 (592 592
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (517 369 (:REWRITE INTEGERP-MINUS-X))
 (517 101
      (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (514 514
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (461 137 (:REWRITE |(< y (+ (- c) x))|))
 (457 239 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (369 369 (:REWRITE REDUCE-INTEGERP-+))
 (369 369 (:META META-INTEGERP-CORRECT))
 (357 119 (:REWRITE RTL::BVECP-EXACTP))
 (350 230 (:REWRITE |(+ c (+ d x))|))
 (343 149 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (304 304 (:REWRITE |(< (+ c/d x) y)|))
 (238 238 (:TYPE-PRESCRIPTION RTL::BVECP))
 (197 197 (:REWRITE |(- (* c x))|))
 (186 186 (:REWRITE REDUCE-RATIONALP-+))
 (186 186 (:REWRITE REDUCE-RATIONALP-*))
 (186 186 (:REWRITE RATIONALP-MINUS-X))
 (186 186 (:META META-RATIONALP-CORRECT))
 (186 4 (:LINEAR RTL::RTZ-NEGATIVE))
 (176 2 (:LINEAR RTL::RAZ-POSITIVE))
 (174 174
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (174 174 (:REWRITE DEFAULT-DIVIDE))
 (161 161 (:REWRITE |(< (* x y) 0)|))
 (153 153 (:REWRITE |(< x (+ c/d y))|))
 (153 153 (:REWRITE |(< (/ x) 0)|))
 (150 150
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (150 150
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (150 150
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (150 150 (:REWRITE |(equal c (/ x))|))
 (150 150 (:REWRITE |(equal c (- x))|))
 (150 150 (:REWRITE |(equal (/ x) c)|))
 (150 150 (:REWRITE |(equal (/ x) (/ y))|))
 (150 150 (:REWRITE |(equal (- x) c)|))
 (150 150 (:REWRITE |(equal (- x) (- y))|))
 (143 99 (:REWRITE DEFAULT-EXPT-2))
 (128 32 (:REWRITE |(integerp (- x))|))
 (121 121 (:REWRITE FOLD-CONSTS-IN-+))
 (99 99 (:REWRITE DEFAULT-EXPT-1))
 (99 99 (:REWRITE |(expt 1/c n)|))
 (99 99 (:REWRITE |(expt (- x) n)|))
 (66 2 (:LINEAR RTL::RND-NON-POS))
 (66 2 (:LINEAR RTL::RND-NON-NEG))
 (65 65 (:REWRITE RTL::RTZ-NEG-BITS))
 (60 60 (:REWRITE |(* c (* d x))|))
 (37 37
     (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (37 37
     (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (35 35 (:REWRITE RTL::RAZ-NEG-BITS))
 (34 34
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (34 34
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (32 32 (:REWRITE |(< 0 (* x y))|))
 (30 30
     (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (30 30
     (:REWRITE |(< (* x (/ y)) 0) rationalp (* x (/ y))|))
 (28 28
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (28 28
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (28 28
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (28 28
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (24 24 (:REWRITE |(< 0 (/ x))|))
 (22 22 (:REWRITE ZP-OPEN))
 (14 14
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (14 14
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (14 14 (:LINEAR EXPT-LINEAR-UPPER-<))
 (14 14 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (14 14 (:LINEAR EXPT-LINEAR-LOWER-<))
 (14 14 (:LINEAR EXPT->=-1-TWO))
 (14 14 (:LINEAR EXPT->-1-TWO))
 (14 14 (:LINEAR EXPT-<=-1-ONE))
 (14 14 (:LINEAR EXPT-<-1-ONE))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2 (:REWRITE |(equal (+ (- c) x) y)|)))
(RTL::R-RND-1
 (3868 3868
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (3868 3868
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (3868 3868
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (3868 3868
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (3565 413
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (2698
  2698
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (2698
      2698
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (2698
     2698
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (2698 2698
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (2032 825 (:REWRITE DEFAULT-PLUS-2))
 (1994 1443
       (:TYPE-PRESCRIPTION RTL::RND-POSITIVE))
 (1710 15 (:REWRITE RTL::R-EXACTP-6))
 (1587 429 (:REWRITE DEFAULT-LESS-THAN-2))
 (1443 1443
       (:TYPE-PRESCRIPTION RTL::RND-NON-POS))
 (1443 1443
       (:TYPE-PRESCRIPTION RTL::RND-NEGATIVE))
 (1323 825 (:REWRITE DEFAULT-PLUS-1))
 (1086 10 (:LINEAR RTL::RND-NON-NEG))
 (1038 10 (:LINEAR RTL::RND-NON-POS))
 (983 429 (:REWRITE DEFAULT-LESS-THAN-1))
 (872 46 (:REWRITE ODD-EXPT-THM))
 (625 10 (:LINEAR EXPT->=-1-ONE))
 (616 10 (:LINEAR EXPT->-1-ONE))
 (551 551
      (:TYPE-PRESCRIPTION RTL::COMMON-MODE-P))
 (532 10 (:LINEAR EXPT-X->=-X))
 (532 10 (:LINEAR EXPT-X->-X))
 (466 364
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (448 364 (:REWRITE |(< (- x) (- y))|))
 (429 429 (:REWRITE THE-FLOOR-BELOW))
 (429 429 (:REWRITE THE-FLOOR-ABOVE))
 (416 92 (:REWRITE |(< y (+ (- c) x))|))
 (413 413
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (413 413
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (412 364 (:REWRITE |(< c (- x))|))
 (412 364 (:REWRITE |(< (- x) c)|))
 (405 15
      (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (401 364
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (390 15
      (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (364 364 (:REWRITE INTEGERP-<-CONSTANT))
 (364 364 (:REWRITE CONSTANT-<-INTEGERP))
 (364 364
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (364 364
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (364 364
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (364 364
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (364 364
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (364 364
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (364 364 (:REWRITE |(< (/ x) (/ y))|))
 (338 258 (:REWRITE DEFAULT-TIMES-2))
 (264 134 (:REWRITE |(+ c (+ d x))|))
 (258 258 (:REWRITE DEFAULT-TIMES-1))
 (233 233
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (215 143 (:REWRITE DEFAULT-MINUS))
 (201 45
      (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (174 174
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (174 174
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (174 174
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (174 174
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (172 43 (:REWRITE RATIONALP-X))
 (169 169
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (166 166
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4D))
 (166 166
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3D))
 (166 166
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2D))
 (166 166
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1D))
 (164 164
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4K))
 (164 164
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3K))
 (164 164
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2K))
 (164 164
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1K))
 (160 124 (:REWRITE INTEGERP-MINUS-X))
 (152 100 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (150 50 (:REWRITE RTL::BVECP-EXACTP))
 (135 124 (:REWRITE REDUCE-INTEGERP-+))
 (124 124 (:META META-INTEGERP-CORRECT))
 (123 123 (:REWRITE |(< (+ c/d x) y)|))
 (110 110 (:REWRITE |(< x (+ c/d y))|))
 (107 17 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (107 17
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (107 17
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (100 100 (:TYPE-PRESCRIPTION RTL::BVECP))
 (65 65
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (65 65 (:REWRITE DEFAULT-DIVIDE))
 (62 47 (:REWRITE DEFAULT-EXPT-2))
 (56 56 (:REWRITE FOLD-CONSTS-IN-+))
 (56 56 (:REWRITE |(- (* c x))|))
 (48 48 (:REWRITE |(< (* x y) 0)|))
 (48 12 (:REWRITE |(integerp (- x))|))
 (47 47 (:REWRITE DEFAULT-EXPT-1))
 (47 47 (:REWRITE |(expt 1/c n)|))
 (47 47 (:REWRITE |(expt (- x) n)|))
 (43 43 (:REWRITE REDUCE-RATIONALP-+))
 (43 43 (:REWRITE REDUCE-RATIONALP-*))
 (43 43 (:REWRITE RATIONALP-MINUS-X))
 (43 43 (:META META-RATIONALP-CORRECT))
 (40 40 (:REWRITE |(< (/ x) 0)|))
 (34 34 (:REWRITE |(< 0 (* x y))|))
 (22 22 (:REWRITE |(< 0 (/ x))|))
 (20 20
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (20 20
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (20 20
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (20 20
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (17 17
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (17 17
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (17 17
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (17 17 (:REWRITE |(equal c (/ x))|))
 (17 17 (:REWRITE |(equal c (- x))|))
 (17 17 (:REWRITE |(equal (/ x) c)|))
 (17 17 (:REWRITE |(equal (/ x) (/ y))|))
 (17 17 (:REWRITE |(equal (- x) c)|))
 (17 17 (:REWRITE |(equal (- x) (- y))|))
 (17 17 (:REWRITE |(* c (* d x))|))
 (15 15
     (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (15 15
     (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (11 11
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (11 11
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (11 11 (:REWRITE ZP-OPEN))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (10 10 (:LINEAR EXPT-LINEAR-UPPER-<))
 (10 10 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (10 10 (:LINEAR EXPT-LINEAR-LOWER-<))
 (10 10 (:LINEAR EXPT->=-1-TWO))
 (10 10 (:LINEAR EXPT->-1-TWO))
 (10 10 (:LINEAR EXPT-<=-1-ONE))
 (10 10 (:LINEAR EXPT-<-1-ONE))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4
    (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (2 2 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (2 2
    (:REWRITE |(< (/ x) y) with (< x 0)|)))
(RTL::R-RND-2
 (4449 4449
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (4449 4449
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (4449 4449
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (3731
  3731
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (3731
      3731
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (3731
     3731
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (3731 3731
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (2946 34 (:LINEAR RTL::RND-NON-POS))
 (2946 34 (:LINEAR RTL::RND-NON-NEG))
 (2629 1881
       (:TYPE-PRESCRIPTION RTL::RND-POSITIVE))
 (2461 1266 (:REWRITE DEFAULT-PLUS-2))
 (1999 1266 (:REWRITE DEFAULT-PLUS-1))
 (1925 513 (:REWRITE DEFAULT-LESS-THAN-2))
 (1881 1881
       (:TYPE-PRESCRIPTION RTL::RND-NON-POS))
 (1881 1881
       (:TYPE-PRESCRIPTION RTL::RND-NEGATIVE))
 (1638 388
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (1077 513 (:REWRITE DEFAULT-LESS-THAN-1))
 (910 30 (:LINEAR EXPT->=-1-ONE))
 (834 257 (:REWRITE SIMPLIFY-SUMS-<))
 (834 11 (:REWRITE RTL::R-EXACTP-6))
 (804 476 (:REWRITE |(< (- x) c)|))
 (799 52 (:REWRITE ODD-EXPT-THM))
 (748 748
      (:TYPE-PRESCRIPTION RTL::COMMON-MODE-P))
 (717 485
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (632 476
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (544 476 (:REWRITE |(< (- x) (- y))|))
 (513 513 (:REWRITE THE-FLOOR-BELOW))
 (513 513 (:REWRITE THE-FLOOR-ABOVE))
 (485 485
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (485 485
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (476 476
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (476 476
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (476 476
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (476 476
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (476 476 (:REWRITE |(< c (- x))|))
 (476 476
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (476 476
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (476 476
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (476 476 (:REWRITE |(< (/ x) (/ y))|))
 (468 468 (:REWRITE INTEGERP-<-CONSTANT))
 (468 468 (:REWRITE CONSTANT-<-INTEGERP))
 (414 414 (:REWRITE DEFAULT-TIMES-2))
 (414 414 (:REWRITE DEFAULT-TIMES-1))
 (302 302
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (302 37
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (302 37
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (292 37 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (255 183 (:REWRITE DEFAULT-MINUS))
 (249 249
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (214 146 (:REWRITE INTEGERP-MINUS-X))
 (199 131 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (169 52
      (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (168 42 (:REWRITE RATIONALP-X))
 (162 6
      (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
 (161 11
      (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
 (159 159 (:REWRITE |(< (+ c/d x) y)|))
 (155 155 (:REWRITE |(< (+ (- c) x) y)|))
 (146 146 (:REWRITE REDUCE-INTEGERP-+))
 (146 146 (:META META-INTEGERP-CORRECT))
 (130 129 (:REWRITE DEFAULT-EXPT-2))
 (129 129 (:REWRITE DEFAULT-EXPT-1))
 (117 117 (:REWRITE |(expt 1/c n)|))
 (117 117 (:REWRITE |(expt (- x) n)|))
 (117 117 (:REWRITE |(< y (+ (- c) x))|))
 (117 117 (:REWRITE |(< x (+ c/d y))|))
 (105 35 (:REWRITE RTL::BVECP-EXACTP))
 (86 86 (:REWRITE |(- (* c x))|))
 (75 75 (:REWRITE |(< (* x y) 0)|))
 (73 73
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (73 73 (:REWRITE DEFAULT-DIVIDE))
 (71 71 (:REWRITE |(< (/ x) 0)|))
 (70 70 (:TYPE-PRESCRIPTION RTL::BVECP))
 (60 60
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (60 60
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (60 60
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (60 60
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (42 42 (:REWRITE REDUCE-RATIONALP-+))
 (42 42 (:REWRITE REDUCE-RATIONALP-*))
 (42 42 (:REWRITE RATIONALP-MINUS-X))
 (42 42 (:META META-RATIONALP-CORRECT))
 (38 38 (:REWRITE |(< 0 (/ x))|))
 (38 38 (:REWRITE |(< 0 (* x y))|))
 (37 37
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (37 37
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (37 37
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (37 37 (:REWRITE |(equal c (/ x))|))
 (37 37 (:REWRITE |(equal c (- x))|))
 (37 37 (:REWRITE |(equal (/ x) c)|))
 (37 37 (:REWRITE |(equal (/ x) (/ y))|))
 (37 37 (:REWRITE |(equal (- x) c)|))
 (37 37 (:REWRITE |(equal (- x) (- y))|))
 (36 9 (:REWRITE |(integerp (- x))|))
 (34 34 (:REWRITE FOLD-CONSTS-IN-+))
 (33 33 (:REWRITE |(* c (* d x))|))
 (30 30 (:LINEAR EXPT-X->=-X))
 (30 30 (:LINEAR EXPT-X->-X))
 (30 30 (:LINEAR EXPT-LINEAR-UPPER-<))
 (30 30 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (30 30 (:LINEAR EXPT-LINEAR-LOWER-<))
 (30 30 (:LINEAR EXPT->=-1-TWO))
 (30 30 (:LINEAR EXPT->-1-TWO))
 (30 30 (:LINEAR EXPT->-1-ONE))
 (30 30 (:LINEAR EXPT-<=-1-ONE))
 (30 30 (:LINEAR EXPT-<-1-ONE))
 (12 12
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (12 12
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (11 11
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (11 11
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (11 11
     (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
 (10 10 (:REWRITE ZP-OPEN))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (6 6
    (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RTL::R-RND-3 (16 8 (:REWRITE DEFAULT-TIMES-2))
              (12 3 (:REWRITE RATIONALP-X))
              (8 8 (:REWRITE DEFAULT-TIMES-1))
              (5 5 (:REWRITE THE-FLOOR-BELOW))
              (5 5 (:REWRITE THE-FLOOR-ABOVE))
              (5 5
                 (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
              (5 5
                 (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
              (5 5 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
              (5 5 (:REWRITE DEFAULT-LESS-THAN-2))
              (5 5 (:REWRITE DEFAULT-LESS-THAN-1))
              (4 4
                 (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
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
              (3 3 (:REWRITE REMOVE-WEAK-INEQUALITIES))
              (3 3 (:REWRITE REDUCE-RATIONALP-+))
              (3 3 (:REWRITE REDUCE-RATIONALP-*))
              (3 3 (:REWRITE REDUCE-INTEGERP-+))
              (3 3 (:REWRITE RATIONALP-MINUS-X))
              (3 3 (:REWRITE INTEGERP-MINUS-X))
              (3 3 (:META META-RATIONALP-CORRECT))
              (3 3 (:META META-INTEGERP-CORRECT))
              (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
              (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
              (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
              (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
              (2 2 (:REWRITE SIMPLIFY-SUMS-<))
              (2 2 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
              (1 1
                 (:REWRITE |(<= (/ x) y) with (< x 0)|))
              (1 1
                 (:REWRITE |(<= (/ x) y) with (< 0 x)|))
              (1 1 (:REWRITE |(< x (/ y)) with (< y 0)|))
              (1 1 (:REWRITE |(< 0 (* x y))|)))
(RTL::R-RND-4 (24 20 (:REWRITE DEFAULT-TIMES-2))
              (20 20 (:REWRITE DEFAULT-TIMES-1))
              (9 9 (:REWRITE THE-FLOOR-BELOW))
              (9 9 (:REWRITE THE-FLOOR-ABOVE))
              (9 9
                 (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
              (9 9
                 (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
              (9 9 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
              (9 9 (:REWRITE DEFAULT-LESS-THAN-2))
              (9 9 (:REWRITE DEFAULT-LESS-THAN-1))
              (7 7 (:REWRITE REMOVE-STRICT-INEQUALITIES))
              (7 7 (:REWRITE INTEGERP-<-CONSTANT))
              (7 7 (:REWRITE CONSTANT-<-INTEGERP))
              (7 7
                 (:REWRITE |(< c (/ x)) positive c --- present in goal|))
              (7 7
                 (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
              (7 7
                 (:REWRITE |(< c (/ x)) negative c --- present in goal|))
              (7 7
                 (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
              (7 7 (:REWRITE |(< c (- x))|))
              (7 7
                 (:REWRITE |(< (/ x) c) positive c --- present in goal|))
              (7 7
                 (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
              (7 7
                 (:REWRITE |(< (/ x) c) negative c --- present in goal|))
              (7 7
                 (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
              (7 7 (:REWRITE |(< (/ x) (/ y))|))
              (7 7 (:REWRITE |(< (- x) c)|))
              (7 7 (:REWRITE |(< (- x) (- y))|))
              (5 2 (:REWRITE RATIONALP-X))
              (4 4
                 (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
              (3 3 (:REWRITE SIMPLIFY-SUMS-<))
              (3 3 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
              (2 2 (:REWRITE REDUCE-RATIONALP-+))
              (2 2 (:REWRITE REDUCE-RATIONALP-*))
              (2 2 (:REWRITE RATIONALP-MINUS-X))
              (2 2
                 (:REWRITE |(<= (/ x) y) with (< x 0)|))
              (2 2
                 (:REWRITE |(<= (/ x) y) with (< 0 x)|))
              (2 2 (:REWRITE |(< x (/ y)) with (< y 0)|))
              (2 2 (:REWRITE |(< 0 (* x y))|))
              (2 2 (:META META-RATIONALP-CORRECT))
              (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
              (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
              (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
              (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
              (1 1
                 (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
              (1 1 (:REWRITE REDUCE-INTEGERP-+))
              (1 1
                 (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
              (1 1 (:REWRITE INTEGERP-MINUS-X))
              (1 1
                 (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
              (1 1 (:REWRITE |(equal c (/ x))|))
              (1 1 (:REWRITE |(equal c (- x))|))
              (1 1 (:REWRITE |(equal (/ x) c)|))
              (1 1 (:REWRITE |(equal (/ x) (/ y))|))
              (1 1 (:REWRITE |(equal (- x) c)|))
              (1 1 (:REWRITE |(equal (- x) (- y))|))
              (1 1 (:META META-INTEGERP-CORRECT)))
(RTL::MARKSTEIN-LEMMA
 (10628 10628
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (10628 10628
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (10628 10628
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (10233
  10233
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (10233
      10233
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (10233
     10233
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (10233 10233
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (10233 10233
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (6293 4578
       (:TYPE-PRESCRIPTION RTL::RND-POSITIVE))
 (4592 1678 (:REWRITE DEFAULT-PLUS-2))
 (4578 4578
       (:TYPE-PRESCRIPTION RTL::RND-NEGATIVE))
 (4340 982 (:REWRITE DEFAULT-LESS-THAN-2))
 (3205 1678 (:REWRITE DEFAULT-PLUS-1))
 (1970 982 (:REWRITE DEFAULT-LESS-THAN-1))
 (1715 1715
       (:TYPE-PRESCRIPTION RTL::COMMON-MODE-P))
 (1153 917 (:REWRITE DEFAULT-TIMES-2))
 (1145 857
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (1107 875
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (1005 857
       (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (993 857 (:REWRITE |(< (- x) (- y))|))
 (982 982 (:REWRITE THE-FLOOR-BELOW))
 (982 982 (:REWRITE THE-FLOOR-ABOVE))
 (965 857 (:REWRITE |(< (- x) c)|))
 (917 917 (:REWRITE DEFAULT-TIMES-1))
 (875 875
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (875 875
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (857 857
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (857 857
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (857 857
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (857 857 (:REWRITE |(< c (- x))|))
 (857 857
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (857 857
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (857 857
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (857 857 (:REWRITE |(< (/ x) (/ y))|))
 (853 853 (:REWRITE INTEGERP-<-CONSTANT))
 (853 853 (:REWRITE CONSTANT-<-INTEGERP))
 (642 148
      (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (615 415 (:REWRITE DEFAULT-MINUS))
 (561 425 (:REWRITE INTEGERP-MINUS-X))
 (536 134 (:REWRITE RATIONALP-X))
 (498 26 (:LINEAR RTL::RND-NON-POS))
 (469 425 (:REWRITE REDUCE-INTEGERP-+))
 (452 452
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (430 144 (:REWRITE RTL::BVECP-EXACTP))
 (425 425 (:META META-INTEGERP-CORRECT))
 (419 419
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (361 225 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (322 14 (:LINEAR EXPT->=-1-ONE))
 (286 286 (:TYPE-PRESCRIPTION RTL::BVECP))
 (250 18
      (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (250 18
      (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (250 18
      (:REWRITE |(< x (/ y)) with (< y 0)|))
 (248 248 (:REWRITE |(< (+ c/d x) y)|))
 (248 109 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (156 156
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (156 156
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (156 156 (:REWRITE |(equal c (/ x))|))
 (156 156 (:REWRITE |(equal (/ x) (/ y))|))
 (156 156 (:REWRITE |(equal (- x) (- y))|))
 (154 154 (:REWRITE DEFAULT-EXPT-2))
 (154 154 (:REWRITE DEFAULT-EXPT-1))
 (152 38 (:REWRITE |(integerp (- x))|))
 (148 148
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (148 148 (:REWRITE |(equal c (- x))|))
 (148 148 (:REWRITE |(equal (- x) c)|))
 (145 145 (:REWRITE |(expt 1/c n)|))
 (145 145 (:REWRITE |(expt (- x) n)|))
 (134 134 (:REWRITE REDUCE-RATIONALP-+))
 (134 134 (:REWRITE REDUCE-RATIONALP-*))
 (134 134 (:REWRITE RATIONALP-MINUS-X))
 (134 134 (:META META-RATIONALP-CORRECT))
 (128 128 (:REWRITE |(< y (+ (- c) x))|))
 (128 128 (:REWRITE |(< x (+ c/d y))|))
 (123 123 (:REWRITE |(- (* c x))|))
 (122 122 (:REWRITE DEFAULT-DIVIDE))
 (120 120 (:REWRITE |(< (* x y) 0)|))
 (116 116 (:REWRITE |(< (/ x) 0)|))
 (114 114
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (59 59 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (59 59 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (59 59 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (59 59 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (54 54 (:REWRITE |(< 0 (* x y))|))
 (44 44 (:REWRITE |(< 0 (/ x))|))
 (41 41 (:REWRITE |(* c (* d x))|))
 (40 40
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (38 38
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (38 38
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (31 31
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (31 31
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (28 28
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (28 28
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (28 28
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (28 28
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (25 25 (:REWRITE FOLD-CONSTS-IN-+))
 (18 18
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (18 18
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (14 14 (:LINEAR EXPT-X->=-X))
 (14 14 (:LINEAR EXPT-X->-X))
 (14 14 (:LINEAR EXPT-LINEAR-UPPER-<))
 (14 14 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (14 14 (:LINEAR EXPT-LINEAR-LOWER-<))
 (14 14 (:LINEAR EXPT->=-1-TWO))
 (14 14 (:LINEAR EXPT->-1-TWO))
 (14 14 (:LINEAR EXPT->-1-ONE))
 (14 14 (:LINEAR EXPT-<=-1-ONE))
 (14 14 (:LINEAR EXPT-<-1-ONE))
 (8 8 (:REWRITE |(not (equal x (/ y)))|))
 (8 8 (:REWRITE |(equal x (/ y))|))
 (8 8 (:REWRITE |(equal (+ (- c) x) y)|)))
