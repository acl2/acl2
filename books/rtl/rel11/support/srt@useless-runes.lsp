(RTL::E$)
(RTL::D$)
(RTL::X$)
(RTL::A$)
(RTL::Q$)
(RTL::R$
 (5
  5
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (5 5
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (5 5
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (5 5
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (5 5
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A)))
(RTL::RHO$ (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
           (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
           (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B)))
(RTL::E$-CONSTRAINT)
(RTL::D$-CONSTRAINT)
(RTL::X$-CONSTRAINT)
(RTL::A$-CONSTRAINT)
(RTL::Q$-CONSTRAINT (4 2
                       (:TYPE-PRESCRIPTION RTL::Q$-CONSTRAINT))
                    (2 2 (:TYPE-PRESCRIPTION ZP)))
(RTL::RHO$-CONSTRAINT)
(RTL::NATP-E$)
(RTL::RATP-X$)
(RTL::RATP-D$)
(RTL::INTP-A$)
(RTL::INTP-Q$ (3 3 (:TYPE-PRESCRIPTION ZP))
              (2 1 (:TYPE-PRESCRIPTION RTL::INTP-Q$)))
(RTL::NATP-R$
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
(RTL::RATP-RHO$ (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B)))
(RTL::QUOT$
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
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE)))
(RTL::REM$
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
(RTL::REM0-DIV-REWRITE (15 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                       (15 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                       (15 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                       (11 5 (:REWRITE DEFAULT-TIMES-1))
                       (10 5 (:REWRITE DEFAULT-TIMES-2))
                       (6 2 (:REWRITE DEFAULT-DIVIDE))
                       (3 2 (:REWRITE DEFAULT-PLUS-2))
                       (3 2 (:REWRITE DEFAULT-PLUS-1))
                       (3 1 (:REWRITE DEFAULT-EXPT-1))
                       (2 2 (:TYPE-PRESCRIPTION RTL::RATP-D$))
                       (2 2
                          (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
                       (2 2
                          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                       (1 1 (:REWRITE DEFAULT-EXPT-2))
                       (1 1 (:REWRITE |(expt 1/c n)|))
                       (1 1 (:REWRITE |(expt (- x) n)|)))
(RTL::REM-DIV-RECURRENCE
 (500 47 (:REWRITE DEFAULT-TIMES-2))
 (268 47 (:REWRITE DEFAULT-TIMES-1))
 (263 52 (:REWRITE DEFAULT-PLUS-2))
 (166 52 (:REWRITE DEFAULT-PLUS-1))
 (105 14 (:REWRITE DEFAULT-MINUS))
 (77
  77
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (77 77
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (77 77
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (77 77
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (77 77
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (77 77
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (46 46 (:TYPE-PRESCRIPTION RTL::QUOT$))
 (45 9
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4E-EXPT))
 (37 7 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (33 15
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (29 29
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (27 9 (:REWRITE DEFAULT-EXPT-1))
 (17 17 (:TYPE-PRESCRIPTION RTL::RATP-X$))
 (15 15
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (15 15
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (15 15
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (9 9
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3E-EXPT))
 (9 9
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2E-EXPT))
 (9 9
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1E-EXPT))
 (9 9 (:REWRITE DEFAULT-EXPT-2))
 (9 9 (:REWRITE |(expt 1/c n)|))
 (9 9 (:REWRITE |(expt (- x) n)|))
 (8 8 (:REWRITE |(- (* c x))|))
 (8 4
    (:TYPE-PRESCRIPTION RTL::Q$-CONSTRAINT))
 (7 7 (:REWRITE |(* c (* d x))|))
 (3 3 (:REWRITE FOLD-CONSTS-IN-+))
 (3 3 (:REWRITE BUBBLE-DOWN-*-MATCH-3))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE |(* c (expt d n))|))
 (1 1 (:REWRITE THE-FLOOR-BELOW))
 (1 1 (:REWRITE THE-FLOOR-ABOVE))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1 (:REWRITE SIMPLIFY-SUMS-<))
 (1 1
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (1 1 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (1 1 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (1 1
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (1 1
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (1 1 (:REWRITE REDUCE-INTEGERP-+))
 (1 1 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (1 1 (:REWRITE INTEGERP-MINUS-X))
 (1 1 (:REWRITE INTEGERP-<-CONSTANT))
 (1 1 (:REWRITE DEFAULT-LESS-THAN-2))
 (1 1 (:REWRITE DEFAULT-LESS-THAN-1))
 (1 1 (:REWRITE CONSTANT-<-INTEGERP))
 (1 1
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (1 1
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (1 1
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (1 1
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (1 1 (:REWRITE |(< c (- x))|))
 (1 1
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (1 1
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (1 1
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (1 1
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (/ x) (/ y))|))
 (1 1 (:REWRITE |(< (- x) c)|))
 (1 1 (:REWRITE |(< (- x) (- y))|))
 (1 1 (:REWRITE |(< (* x y) 0)|))
 (1 1
    (:REWRITE |(* (expt c m) (expt d n))|))
 (1 1 (:META META-INTEGERP-CORRECT)))
(RTL::REM0-DIV-BOUND
 (874 91
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (874 91
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (695
  695
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (695 695
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (695
     695
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (695 695
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (590 1
      (:REWRITE |(<= (* x (/ y)) 1) with (< 0 y)|))
 (583 1
      (:REWRITE |(< 1 (* x (/ y))) with (< 0 y)|))
 (568 2 (:REWRITE |(< (+ (- c) x) y)|))
 (314 2
      (:REWRITE |(<= x (/ y)) with (< 0 y)|))
 (241 2 (:REWRITE |(< (/ x) y) with (< 0 x)|))
 (217 217
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (217 217
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (217 217
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (187 19
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (187 19 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (160 12 (:LINEAR EXPT->-1-ONE))
 (143 26 (:REWRITE DEFAULT-TIMES-2))
 (136 10 (:LINEAR EXPT-X->-X))
 (129 22 (:REWRITE DEFAULT-LESS-THAN-1))
 (122 12 (:LINEAR EXPT->=-1-ONE))
 (116 116
      (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
 (108 108 (:REWRITE |arith (expt x c)|))
 (108 108 (:REWRITE |arith (expt 1/c n)|))
 (104 22 (:REWRITE DEFAULT-LESS-THAN-2))
 (98 10 (:LINEAR EXPT-X->=-X))
 (96 19 (:REWRITE SIMPLIFY-SUMS-<))
 (94 94 (:REWRITE |arith (* c (* d x))|))
 (91 91
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (84 84 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
 (84 84 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
 (84 84 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
 (82 82 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (82 82 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (82 82 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (82 82 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (69 20
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (66 26 (:REWRITE DEFAULT-TIMES-1))
 (64 64 (:TYPE-PRESCRIPTION NOT-INTEGERP-3D))
 (64 64 (:TYPE-PRESCRIPTION NOT-INTEGERP-2D))
 (64 64 (:TYPE-PRESCRIPTION NOT-INTEGERP-1D))
 (58 58 (:REWRITE ARITH-NORMALIZE-ADDENDS))
 (53 19
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (34 5 (:REWRITE DEFAULT-PLUS-2))
 (32 22
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (32 22
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (32 1 (:REWRITE |(* y (* x z))|))
 (30 3 (:REWRITE DEFAULT-DIVIDE))
 (22 22 (:REWRITE THE-FLOOR-BELOW))
 (22 22 (:REWRITE THE-FLOOR-ABOVE))
 (20 20
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (20 20
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (20 20
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (20 20 (:REWRITE |(< c (- x))|))
 (20 20
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (20 20
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (20 20
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (20 20
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (20 20 (:REWRITE |(< (/ x) (/ y))|))
 (20 20 (:REWRITE |(< (- x) c)|))
 (20 20 (:REWRITE |(< (- x) (- y))|))
 (20 20
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (20 20
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (20 20
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (20 20
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (20 1
     (:REWRITE |(<= (* x (/ y)) 1) with (< y 0)|))
 (20 1
     (:REWRITE |(< 1 (* x (/ y))) with (< y 0)|))
 (19 19 (:REWRITE INTEGERP-<-CONSTANT))
 (17 2
     (:REWRITE |(<= x (/ y)) with (< y 0)|))
 (17 2 (:REWRITE |(< (/ x) y) with (< x 0)|))
 (16 16 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (15 15
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (12 12 (:LINEAR EXPT-LINEAR-UPPER-<))
 (12 12 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (12 12 (:LINEAR EXPT-LINEAR-LOWER-<))
 (12 12 (:LINEAR EXPT->=-1-TWO))
 (12 12 (:LINEAR EXPT->-1-TWO))
 (12 12 (:LINEAR EXPT-<=-1-ONE))
 (12 12 (:LINEAR EXPT-<-1-ONE))
 (11 2
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3E-EXPT))
 (11 2
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2E-EXPT))
 (11 2
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1E-EXPT))
 (8 8 (:REWRITE |arith (* (- x) y)|))
 (7 7 (:REWRITE |arith (- (* c x))|))
 (5 5
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (5 5 (:REWRITE NORMALIZE-ADDENDS))
 (5 5 (:REWRITE DEFAULT-PLUS-1))
 (4 4 (:REWRITE DEFAULT-EXPT-2))
 (4 4 (:REWRITE DEFAULT-EXPT-1))
 (4 4 (:REWRITE |(expt 1/c n)|))
 (4 4 (:REWRITE |(expt (- x) n)|))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (3 3
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (3 3 (:REWRITE |(< 0 (/ x))|))
 (3 3 (:REWRITE |(< 0 (* x y))|))
 (3 3 (:REWRITE |(* c (* d x))|))
 (3 2
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (2 2
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (2 2 (:REWRITE REDUCE-INTEGERP-+))
 (2 2
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (2 2 (:REWRITE INTEGERP-MINUS-X))
 (2 2
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (2 2 (:REWRITE |(equal c (/ x))|))
 (2 2 (:REWRITE |(equal c (- x))|))
 (2 2 (:REWRITE |(equal (/ x) c)|))
 (2 2 (:REWRITE |(equal (/ x) (/ y))|))
 (2 2 (:REWRITE |(equal (- x) c)|))
 (2 2 (:REWRITE |(equal (- x) (- y))|))
 (2 2 (:REWRITE |(< y (+ (- c) x))|))
 (2 2 (:REWRITE |(< x (+ c/d y))|))
 (2 2 (:REWRITE |(< (/ x) 0)|))
 (2 2 (:REWRITE |(< (+ c/d x) y)|))
 (2 2
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (2 2 (:REWRITE |(< (* x y) 0)|))
 (2 2 (:META META-INTEGERP-CORRECT))
 (1 1 (:REWRITE DEFAULT-MINUS)))
(RTL::SEL-UPPER-DIV)
(RTL::SEL-LOWER-DIV)
(RTL::REM-DIV-BND-NEXT
     (107 35 (:REWRITE DEFAULT-PLUS-2))
     (94 35 (:REWRITE DEFAULT-PLUS-1))
     (69 10
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (62 11 (:REWRITE DEFAULT-LESS-THAN-2))
     (46 11 (:REWRITE DEFAULT-LESS-THAN-1))
     (39 6 (:REWRITE SIMPLIFY-SUMS-<))
     (37 16 (:REWRITE DEFAULT-TIMES-1))
     (34 16 (:REWRITE DEFAULT-TIMES-2))
     (32 16
         (:TYPE-PRESCRIPTION RTL::Q$-CONSTRAINT))
     (21 6 (:REWRITE DEFAULT-MINUS))
     (13 13
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (13 4 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (12 10 (:REWRITE |(< (- x) c)|))
     (12 10 (:REWRITE |(< (- x) (- y))|))
     (11 11 (:REWRITE THE-FLOOR-BELOW))
     (11 11 (:REWRITE THE-FLOOR-ABOVE))
     (11 11
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (10 10 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (10 10
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (10 10
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (10 10
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
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
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (10 10
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (10 10
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (10 10
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (10 10 (:REWRITE |(< (/ x) (/ y))|))
     (5 5 (:REWRITE |(< (+ c/d x) y)|))
     (5 5 (:REWRITE |(< (+ (- c) x) y)|))
     (3 3 (:REWRITE |(< y (+ (- c) x))|))
     (3 3 (:REWRITE |(< x (+ c/d y))|))
     (3 3 (:REWRITE |(- (* c x))|))
     (2 2 (:REWRITE |(< (/ x) 0)|))
     (2 2 (:REWRITE |(< (* x y) 0)|))
     (2 2 (:REWRITE |(+ c (+ d x))|))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (1 1 (:REWRITE REDUCE-INTEGERP-+))
     (1 1 (:REWRITE INTEGERP-MINUS-X))
     (1 1 (:META META-INTEGERP-CORRECT)))
(RTL::SELECT-OVERLAP
     (192 126 (:REWRITE DEFAULT-TIMES-2))
     (132 116 (:REWRITE DEFAULT-PLUS-1))
     (127 126 (:REWRITE DEFAULT-TIMES-1))
     (116 116 (:REWRITE DEFAULT-PLUS-2))
     (61 61
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (46 1
         (:REWRITE |(<= x (/ y)) with (< 0 y)|))
     (45 45
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (41 1 (:REWRITE |(< (/ x) y) with (< 0 x)|))
     (31 23
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (31 23
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (27 23 (:REWRITE DEFAULT-LESS-THAN-2))
     (25 19 (:REWRITE CONSTANT-<-INTEGERP))
     (24 19
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (23 23 (:REWRITE THE-FLOOR-BELOW))
     (23 23 (:REWRITE THE-FLOOR-ABOVE))
     (23 23 (:REWRITE DEFAULT-LESS-THAN-1))
     (23 19
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (20 20 (:REWRITE |(+ c (+ d x))|))
     (19 19 (:REWRITE INTEGERP-<-CONSTANT))
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
     (18 18 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (16 16 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (12 12 (:REWRITE FOLD-CONSTS-IN-+))
     (12 12 (:REWRITE DEFAULT-MINUS))
     (12 12 (:REWRITE |(< y (+ (- c) x))|))
     (12 12 (:REWRITE |(< x (+ c/d y))|))
     (10 10 (:REWRITE |(< (+ c/d x) y)|))
     (10 10 (:REWRITE |(< (+ (- c) x) y)|))
     (8 8 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
     (8 8 (:TYPE-PRESCRIPTION ABS))
     (5 5 (:REWRITE |(< 0 (* x y))|))
     (4 4
        (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (4 4
        (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (4 4 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (4 4 (:REWRITE |(- (* c x))|))
     (3 3 (:REWRITE REDUCE-INTEGERP-+))
     (3 3 (:REWRITE INTEGERP-MINUS-X))
     (3 3 (:META META-INTEGERP-CORRECT))
     (2 1
        (:REWRITE |(<= x (/ y)) with (< y 0)|))
     (2 1 (:REWRITE |(< (/ x) y) with (< x 0)|))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (1 1 (:REWRITE |(< 0 (/ x))|)))
(RTL::R$-BOUND
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
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A)))
(RTL::A$+RHO$-1 (25 25 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                (25 25 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                (25 25 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                (22 22 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
                (22 22 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
                (22 22 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
                (9 6 (:REWRITE DEFAULT-TIMES-1))
                (8 6 (:REWRITE DEFAULT-TIMES-2))
                (5 1 (:REWRITE REMOVE-WEAK-INEQUALITIES))
                (4 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                (4 2
                   (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                (3 1
                   (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
                (3 1 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
                (3 1 (:REWRITE DEFAULT-LESS-THAN-1))
                (2 2
                   (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                (2 2
                   (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
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
                (1 1 (:REWRITE THE-FLOOR-BELOW))
                (1 1 (:REWRITE THE-FLOOR-ABOVE))
                (1 1
                   (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
                (1 1 (:REWRITE SIMPLIFY-SUMS-<))
                (1 1 (:REWRITE REMOVE-STRICT-INEQUALITIES))
                (1 1
                   (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
                (1 1
                   (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
                (1 1
                   (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
                (1 1 (:REWRITE INTEGERP-<-CONSTANT))
                (1 1 (:REWRITE DEFAULT-LESS-THAN-2))
                (1 1 (:REWRITE DEFAULT-DIVIDE))
                (1 1 (:REWRITE CONSTANT-<-INTEGERP))
                (1 1 (:REWRITE |(equal (+ (- c) x) y)|))
                (1 1
                   (:REWRITE |(< c (/ x)) positive c --- present in goal|))
                (1 1
                   (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
                (1 1
                   (:REWRITE |(< c (/ x)) negative c --- present in goal|))
                (1 1
                   (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
                (1 1 (:REWRITE |(< c (- x))|))
                (1 1
                   (:REWRITE |(< (/ x) c) positive c --- present in goal|))
                (1 1
                   (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
                (1 1
                   (:REWRITE |(< (/ x) c) negative c --- present in goal|))
                (1 1
                   (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
                (1 1 (:REWRITE |(< (/ x) (/ y))|))
                (1 1 (:REWRITE |(< (- x) c)|))
                (1 1 (:REWRITE |(< (- x) (- y))|)))
(RTL::A$+RHO$-2 (13 4 (:REWRITE DEFAULT-PLUS-2))
                (12 5 (:REWRITE DEFAULT-TIMES-2))
                (9 5 (:REWRITE DEFAULT-TIMES-1))
                (9 4 (:REWRITE DEFAULT-PLUS-1))
                (4 2 (:REWRITE DEFAULT-MINUS))
                (3 3
                   (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                (3 3
                   (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                (3 3 (:REWRITE NORMALIZE-ADDENDS))
                (1 1 (:REWRITE |(* x (- y))|))
                (1 1 (:REWRITE |(* (- x) y)|)))
(RTL::A$+RHO$-3)
(RTL::A$+RHO$-4 (104 14 (:REWRITE DEFAULT-PLUS-2))
                (84 84 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                (84 84 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                (84 84 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                (70 14 (:REWRITE DEFAULT-PLUS-1))
                (33 15 (:REWRITE DEFAULT-TIMES-2))
                (26 26 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
                (26 26 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
                (26 26 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
                (23 15 (:REWRITE DEFAULT-TIMES-1))
                (9 9
                   (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                (8 2 (:REWRITE DEFAULT-MINUS))
                (7 7
                   (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                (6 1 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
                (5 1 (:REWRITE REMOVE-WEAK-INEQUALITIES))
                (3 3
                   (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
                (3 3 (:REWRITE DEFAULT-DIVIDE))
                (3 1
                   (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
                (3 1 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
                (3 1 (:REWRITE DEFAULT-LESS-THAN-1))
                (2 2 (:REWRITE |(* c (* d x))|))
                (1 1 (:REWRITE THE-FLOOR-BELOW))
                (1 1 (:REWRITE THE-FLOOR-ABOVE))
                (1 1 (:REWRITE SIMPLIFY-SUMS-<))
                (1 1 (:REWRITE REMOVE-STRICT-INEQUALITIES))
                (1 1
                   (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
                (1 1
                   (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
                (1 1 (:REWRITE INTEGERP-<-CONSTANT))
                (1 1 (:REWRITE DEFAULT-LESS-THAN-2))
                (1 1 (:REWRITE CONSTANT-<-INTEGERP))
                (1 1
                   (:REWRITE |(< c (/ x)) positive c --- present in goal|))
                (1 1
                   (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
                (1 1
                   (:REWRITE |(< c (/ x)) negative c --- present in goal|))
                (1 1
                   (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
                (1 1 (:REWRITE |(< c (- x))|))
                (1 1
                   (:REWRITE |(< (/ x) c) positive c --- present in goal|))
                (1 1
                   (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
                (1 1
                   (:REWRITE |(< (/ x) c) negative c --- present in goal|))
                (1 1
                   (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
                (1 1 (:REWRITE |(< (/ x) (/ y))|))
                (1 1 (:REWRITE |(< (- x) c)|))
                (1 1 (:REWRITE |(< (- x) (- y))|))
                (1 1 (:REWRITE |(- (* c x))|))
                (1 1 (:REWRITE |(+ c (+ d x))|)))
(RTL::A$+RHO$)
(RTL::DIV-CONTAINMENT (95 40 (:REWRITE DEFAULT-TIMES-2))
                      (94 40 (:REWRITE DEFAULT-TIMES-1))
                      (45 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                      (45 6
                          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                      (31 9 (:REWRITE DEFAULT-MINUS))
                      (30 12 (:REWRITE DEFAULT-PLUS-2))
                      (30 12 (:REWRITE DEFAULT-PLUS-1))
                      (28 28
                          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                      (12 12
                          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                      (12 12 (:REWRITE NORMALIZE-ADDENDS))
                      (7 7
                         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                      (7 7
                         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
                      (7 7 (:REWRITE |(equal (/ x) (/ y))|))
                      (7 7 (:REWRITE |(equal (+ (- c) x) y)|))
                      (6 6
                         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
                      (6 6 (:REWRITE |(equal c (/ x))|))
                      (6 6 (:REWRITE |(equal c (- x))|))
                      (6 6 (:REWRITE |(equal (/ x) c)|))
                      (6 6 (:REWRITE |(equal (- x) c)|))
                      (5 5 (:REWRITE |(* c (* d x))|))
                      (3 3 (:REWRITE |(- (* c x))|)))
(RTL::MD4)
(RTL::SELECT-DIGIT-D4)
(RTL::SEL-LIMITS-4
     (108 108
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (108 108
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (108 108
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (106 13
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (90 10 (:REWRITE ACL2-NUMBERP-X))
     (85 2 (:REWRITE |(< (/ x) y) with (< 0 x)|))
     (64 2 (:REWRITE |(< (/ x) y) with (< x 0)|))
     (56 42 (:REWRITE DEFAULT-TIMES-2))
     (53 19
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (53 19
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (49 42 (:REWRITE DEFAULT-TIMES-1))
     (45 1 (:REWRITE |(< x (/ y)) with (< 0 y)|))
     (41 41 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (41 41 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (40 10 (:REWRITE RATIONALP-X))
     (36 36 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (34 34 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
     (34 34 (:TYPE-PRESCRIPTION ABS))
     (34 12 (:REWRITE INTEGERP-<-CONSTANT))
     (29 19 (:REWRITE DEFAULT-LESS-THAN-2))
     (28 19 (:REWRITE DEFAULT-LESS-THAN-1))
     (27 27
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (24 12 (:REWRITE CONSTANT-<-INTEGERP))
     (19 19 (:REWRITE THE-FLOOR-BELOW))
     (19 19 (:REWRITE THE-FLOOR-ABOVE))
     (19 12
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (19 12 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (18 18 (:REWRITE REDUCE-INTEGERP-+))
     (18 18 (:REWRITE INTEGERP-MINUS-X))
     (18 18 (:META META-INTEGERP-CORRECT))
     (15 15
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (15 15
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (15 15
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (15 15
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (15 15
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (15 15
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (15 15
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (15 15
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (15 15 (:REWRITE |(< (/ x) (/ y))|))
     (15 15 (:REWRITE |(< (- x) (- y))|))
     (13 13 (:REWRITE SIMPLIFY-SUMS-EQUAL))
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
     (13 13 (:REWRITE |(* (- x) y)|))
     (12 12 (:REWRITE SIMPLIFY-SUMS-<))
     (12 12
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (11 9 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (10 10 (:REWRITE REDUCE-RATIONALP-+))
     (10 10 (:REWRITE REDUCE-RATIONALP-*))
     (10 10 (:REWRITE RATIONALP-MINUS-X))
     (10 10 (:META META-RATIONALP-CORRECT))
     (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-4D))
     (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-3D))
     (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-2D))
     (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-1D))
     (3 3 (:REWRITE DEFAULT-MINUS))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (2 2 (:REWRITE |(* x (- y))|))
     (2 1 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (1 1
        (:REWRITE |(< 1 (* (/ x) y)) with (< x 0)|))
     (1 1
        (:REWRITE |(< 1 (* (/ x) y)) with (< 0 x)|)))
(RTL::SEL-LIMITS-CHECK-4
     (90 90 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (90 90 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (90 90 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (86 11
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (72 8 (:REWRITE ACL2-NUMBERP-X))
     (45 1 (:REWRITE |(< x (/ y)) with (< 0 y)|))
     (42 1
         (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (32 8 (:REWRITE RATIONALP-X))
     (11 11 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (11 11
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (11 11
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (11 11
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (11 11 (:REWRITE |(equal c (/ x))|))
     (11 11 (:REWRITE |(equal c (- x))|))
     (11 11 (:REWRITE |(equal (/ x) c)|))
     (11 11 (:REWRITE |(equal (/ x) (/ y))|))
     (11 11 (:REWRITE |(equal (- x) c)|))
     (11 11 (:REWRITE |(equal (- x) (- y))|))
     (10 10 (:REWRITE REDUCE-INTEGERP-+))
     (10 10 (:REWRITE INTEGERP-MINUS-X))
     (10 10 (:META META-INTEGERP-CORRECT))
     (10 4 (:REWRITE INTEGERP-<-CONSTANT))
     (8 8 (:REWRITE REDUCE-RATIONALP-+))
     (8 8 (:REWRITE REDUCE-RATIONALP-*))
     (8 8 (:REWRITE RATIONALP-MINUS-X))
     (8 8 (:META META-RATIONALP-CORRECT))
     (8 4
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (8 4
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (8 4 (:REWRITE CONSTANT-<-INTEGERP))
     (7 4
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (7 4 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (7 4 (:REWRITE DEFAULT-LESS-THAN-1))
     (5 3 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (5 3 (:REWRITE DEFAULT-TIMES-2))
     (5 1 (:REWRITE |(* y x)|))
     (4 4 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
     (4 4 (:TYPE-PRESCRIPTION ABS))
     (4 4 (:REWRITE THE-FLOOR-BELOW))
     (4 4 (:REWRITE THE-FLOOR-ABOVE))
     (4 4 (:REWRITE SIMPLIFY-SUMS-<))
     (4 4 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (4 4 (:REWRITE DEFAULT-LESS-THAN-2))
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
     (4 3 (:REWRITE DEFAULT-TIMES-1))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (2 2
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (2 1
        (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (2 1
        (:REWRITE |(< x (/ y)) with (< y 0)|)))
(RTL::MD4-K-BOUNDS
     (628 628
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (317 7 (:REWRITE |(< x (/ y)) with (< 0 y)|))
     (260 26 (:REWRITE RATIONALP-X))
     (213 83 (:REWRITE DEFAULT-PLUS-2))
     (203 83 (:REWRITE DEFAULT-LESS-THAN-1))
     (195 4 (:REWRITE |(< (/ x) y) with (< x 0)|))
     (174 174
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (174 174
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (174 174
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (174 118 (:REWRITE DEFAULT-TIMES-2))
     (171 83 (:REWRITE DEFAULT-LESS-THAN-2))
     (166 22 (:REWRITE ACL2-NUMBERP-X))
     (149 4 (:REWRITE |(< (/ x) y) with (< 0 x)|))
     (143 47 (:REWRITE CONSTANT-<-INTEGERP))
     (132 118 (:REWRITE DEFAULT-TIMES-1))
     (131 23
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (122 19
          (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (116 47 (:REWRITE INTEGERP-<-CONSTANT))
     (111 41
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (105 63
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (105 63
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (83 83 (:REWRITE THE-FLOOR-BELOW))
     (83 83 (:REWRITE THE-FLOOR-ABOVE))
     (72 72
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (71 51 (:REWRITE INTEGERP-MINUS-X))
     (69 13 (:REWRITE |(< x (+ c/d y))|))
     (66 12 (:REWRITE |(< (+ c/d x) y)|))
     (59 7 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (50 50 (:REWRITE REDUCE-INTEGERP-+))
     (50 50 (:META META-INTEGERP-CORRECT))
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
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (48 48
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (48 48
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (48 48
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (48 48 (:REWRITE |(< (/ x) (/ y))|))
     (48 48 (:REWRITE |(< (- x) (- y))|))
     (47 47
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (42 42 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
     (42 42 (:TYPE-PRESCRIPTION ABS))
     (40 11 (:REWRITE |(< (+ (- c) x) y)|))
     (39 39
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (26 26 (:REWRITE REDUCE-RATIONALP-+))
     (26 26 (:REWRITE REDUCE-RATIONALP-*))
     (26 26 (:REWRITE RATIONALP-MINUS-X))
     (26 26 (:META META-RATIONALP-CORRECT))
     (23 23 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (23 23
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (23 23
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (23 23
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (23 23 (:REWRITE |(equal c (/ x))|))
     (23 23 (:REWRITE |(equal c (- x))|))
     (23 23 (:REWRITE |(equal (/ x) c)|))
     (23 23 (:REWRITE |(equal (/ x) (/ y))|))
     (23 23 (:REWRITE |(equal (- x) c)|))
     (23 23 (:REWRITE |(equal (- x) (- y))|))
     (23 7 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (22 22 (:REWRITE |(* (- x) y)|))
     (12 12 (:REWRITE |(< y (+ (- c) x))|))
     (10 1 (:REWRITE |(- (+ x y))|))
     (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-4D))
     (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-3D))
     (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-2D))
     (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-1D))
     (4 4 (:REWRITE |(+ c (+ d x))|))
     (4 4 (:REWRITE |(* x (- y))|))
     (3 3 (:REWRITE DEFAULT-MINUS))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (2 2 (:REWRITE FOLD-CONSTS-IN-+)))
(RTL::R-BOUND-INV-1
     (146 146
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (146 146
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (54 54 (:TYPE-PRESCRIPTION NOT-INTEGERP-4D))
     (54 54 (:TYPE-PRESCRIPTION NOT-INTEGERP-3K))
     (54 54 (:TYPE-PRESCRIPTION NOT-INTEGERP-3D))
     (54 54 (:TYPE-PRESCRIPTION NOT-INTEGERP-2K))
     (54 54 (:TYPE-PRESCRIPTION NOT-INTEGERP-2D))
     (54 54 (:TYPE-PRESCRIPTION NOT-INTEGERP-1K))
     (45 1 (:REWRITE |(< x (/ y)) with (< 0 y)|))
     (42 1
         (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (36 18 (:REWRITE DEFAULT-TIMES-2))
     (29 13 (:REWRITE DEFAULT-LESS-THAN-1))
     (24 12
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (24 12 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (20 12 (:REWRITE SIMPLIFY-SUMS-<))
     (19 18 (:REWRITE DEFAULT-TIMES-1))
     (18 12 (:REWRITE INTEGERP-<-CONSTANT))
     (16 12
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (16 12
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (16 12 (:REWRITE CONSTANT-<-INTEGERP))
     (15 13 (:REWRITE DEFAULT-LESS-THAN-2))
     (13 13 (:REWRITE THE-FLOOR-BELOW))
     (13 13 (:REWRITE THE-FLOOR-ABOVE))
     (13 13
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (13 11 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (12 12
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
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
     (12 12 (:REWRITE |(< (- x) c)|))
     (12 12 (:REWRITE |(< (- x) (- y))|))
     (9 4
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (6 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (5 1 (:REWRITE |(* y x)|))
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
     (3 3 (:REWRITE REDUCE-INTEGERP-+))
     (3 3 (:REWRITE INTEGERP-MINUS-X))
     (3 3 (:META META-INTEGERP-CORRECT))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (2 2 (:REWRITE DEFAULT-MINUS))
     (2 2 (:REWRITE |(< (/ x) 0)|))
     (2 2 (:REWRITE |(< (* x y) 0)|))
     (2 1
        (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (2 1
        (:REWRITE |(< x (/ y)) with (< y 0)|)))
(RTL::R-BOUND-INV-2
     (585 12
          (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (262 67 (:REWRITE |(< c (- x))|))
     (204 8 (:REWRITE |(* x (+ y z))|))
     (199 12
          (:REWRITE |(< x (/ y)) with (< y 0)|))
     (150 11 (:REWRITE |(* y x)|))
     (127 61 (:REWRITE INTEGERP-<-CONSTANT))
     (116 102 (:REWRITE DEFAULT-PLUS-1))
     (110 108 (:REWRITE DEFAULT-TIMES-2))
     (109 108 (:REWRITE DEFAULT-TIMES-1))
     (109 69
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (109 69
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (107 107
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (107 107
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (102 102 (:REWRITE DEFAULT-PLUS-2))
     (88 72 (:REWRITE DEFAULT-LESS-THAN-1))
     (88 8 (:REWRITE |(* y (* x z))|))
     (74 72 (:REWRITE DEFAULT-LESS-THAN-2))
     (73 61
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (72 72 (:REWRITE THE-FLOOR-BELOW))
     (72 72 (:REWRITE THE-FLOOR-ABOVE))
     (67 67
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (67 67
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (67 67
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (67 67
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (67 67
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (67 67
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (67 67
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (67 67
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (67 67 (:REWRITE |(< (/ x) (/ y))|))
     (67 67 (:REWRITE |(< (- x) (- y))|))
     (66 61 (:REWRITE CONSTANT-<-INTEGERP))
     (65 65
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (61 61
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (61 61 (:REWRITE |(< (- x) c)|))
     (55 47 (:REWRITE SIMPLIFY-SUMS-<))
     (48 46 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (43 7 (:REWRITE |(* x (- y))|))
     (36 8 (:REWRITE |(* c (* d x))|))
     (28 28
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (23 23 (:REWRITE REDUCE-INTEGERP-+))
     (23 23 (:REWRITE INTEGERP-MINUS-X))
     (23 23 (:META META-INTEGERP-CORRECT))
     (20 20 (:REWRITE |(* (- x) y)|))
     (19 19 (:REWRITE DEFAULT-MINUS))
     (14 14 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (14 14 (:REWRITE |(< (+ c/d x) y)|))
     (14 14 (:REWRITE |(< (+ (- c) x) y)|))
     (13 6
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (12 12 (:REWRITE |(< y (+ (- c) x))|))
     (12 12 (:REWRITE |(< x (+ c/d y))|))
     (10 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (8 4
        (:TYPE-PRESCRIPTION RTL::Q$-CONSTRAINT))
     (8 2 (:REWRITE RATIONALP-X))
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
     (6 6 (:REWRITE |(+ c (+ d x))|))
     (4 4 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (4 4 (:REWRITE |(< (/ x) 0)|))
     (4 4 (:REWRITE |(< (* x y) 0)|))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (2 2 (:REWRITE REDUCE-RATIONALP-+))
     (2 2 (:REWRITE REDUCE-RATIONALP-*))
     (2 2 (:REWRITE RATIONALP-MINUS-X))
     (2 2 (:META META-RATIONALP-CORRECT)))
(RTL::R-BOUND-INV-3
     (8 2 (:REWRITE RATIONALP-X))
     (5 5
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (5 5 (:REWRITE DEFAULT-TIMES-2))
     (5 5 (:REWRITE DEFAULT-TIMES-1))
     (4 4 (:REWRITE REDUCE-INTEGERP-+))
     (4 4 (:REWRITE INTEGERP-MINUS-X))
     (4 4 (:META META-INTEGERP-CORRECT))
     (3 3 (:REWRITE THE-FLOOR-BELOW))
     (3 3 (:REWRITE THE-FLOOR-ABOVE))
     (3 3
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (3 3 (:REWRITE NORMALIZE-ADDENDS))
     (3 3 (:REWRITE DEFAULT-PLUS-2))
     (3 3 (:REWRITE DEFAULT-PLUS-1))
     (3 3 (:REWRITE DEFAULT-LESS-THAN-2))
     (3 3 (:REWRITE DEFAULT-LESS-THAN-1))
     (2 2 (:REWRITE SIMPLIFY-SUMS-<))
     (2 2
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (2 2 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (2 2 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (2 2 (:REWRITE REDUCE-RATIONALP-+))
     (2 2 (:REWRITE REDUCE-RATIONALP-*))
     (2 2
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (2 2
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (2 2 (:REWRITE RATIONALP-MINUS-X))
     (2 2 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (2 2 (:REWRITE INTEGERP-<-CONSTANT))
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
     (2 2 (:META META-RATIONALP-CORRECT))
     (1 1 (:REWRITE |(< (+ (- c) x) y)|)))
(RTL::R-BOUND-INV-4
     (14176 14176
            (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (14176 14176
            (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (13841 3578 (:REWRITE |(< c (- x))|))
     (6560 4082
           (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (6560 4082
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (6349 3241 (:REWRITE INTEGERP-<-CONSTANT))
     (5862 5764 (:REWRITE DEFAULT-TIMES-1))
     (5654 4282 (:REWRITE DEFAULT-LESS-THAN-1))
     (4675 4171 (:REWRITE DEFAULT-PLUS-1))
     (4307 4307 (:REWRITE THE-FLOOR-BELOW))
     (4307 4307 (:REWRITE THE-FLOOR-ABOVE))
     (4220 3578
           (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (4045 3265 (:REWRITE |(< (- x) c)|))
     (3920 2942
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (3877 3241 (:REWRITE CONSTANT-<-INTEGERP))
     (3740 3578
           (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (3660 3660
           (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (3578 3578
           (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (3578 3578
           (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (3578 3578
           (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (3578 3578
           (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (3578 3578
           (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (3578 3578
           (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (3578 3578 (:REWRITE |(< (/ x) (/ y))|))
     (3578 3578 (:REWRITE |(< (- x) (- y))|))
     (3046 2454 (:REWRITE SIMPLIFY-SUMS-<))
     (2224 196 (:REWRITE ACL2-NUMBERP-X))
     (1545 1545 (:REWRITE REDUCE-INTEGERP-+))
     (1545 1545 (:REWRITE INTEGERP-MINUS-X))
     (1545 1545 (:META META-INTEGERP-CORRECT))
     (1453 1453
           (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (1448 724
           (:TYPE-PRESCRIPTION RTL::Q$-CONSTRAINT))
     (1099 1099 (:REWRITE |(* (- x) y)|))
     (1063 511
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (1031 340 (:REWRITE RATIONALP-X))
     (1000 997 (:REWRITE DEFAULT-MINUS))
     (549 549 (:REWRITE |(< (+ c/d x) y)|))
     (549 549 (:REWRITE |(< (+ (- c) x) y)|))
     (539 539
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (536 511 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (511 511
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (511 511 (:REWRITE |(equal c (/ x))|))
     (511 511 (:REWRITE |(equal c (- x))|))
     (511 511 (:REWRITE |(equal (/ x) c)|))
     (511 511 (:REWRITE |(equal (/ x) (/ y))|))
     (511 511 (:REWRITE |(equal (- x) c)|))
     (511 511 (:REWRITE |(equal (- x) (- y))|))
     (492 488 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (410 410 (:REWRITE |(< y (+ (- c) x))|))
     (384 384 (:REWRITE |(< (/ x) 0)|))
     (384 384 (:REWRITE |(< (* x y) 0)|))
     (340 340 (:REWRITE REDUCE-RATIONALP-+))
     (340 340 (:REWRITE REDUCE-RATIONALP-*))
     (340 340 (:REWRITE RATIONALP-MINUS-X))
     (340 340 (:META META-RATIONALP-CORRECT))
     (269 52
          (:REWRITE |(< (/ x) y) with (< 0 x)|))
     (225 225
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (225 225
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (191 191 (:REWRITE |(equal (+ (- c) x) y)|))
     (104 104
          (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (90 90
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RTL::R-BOUND-INV-5
     (585 12
          (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (283 88 (:REWRITE |(< c (- x))|))
     (216 82 (:REWRITE |(< (- x) c)|))
     (215 215
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (215 215
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (204 8 (:REWRITE |(* x (+ y z))|))
     (199 12
          (:REWRITE |(< x (/ y)) with (< y 0)|))
     (175 91
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (175 91
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (171 5
          (:REWRITE |(<= x (/ y)) with (< y 0)|))
     (168 15 (:REWRITE |(* y x)|))
     (160 158 (:REWRITE DEFAULT-TIMES-2))
     (159 158 (:REWRITE DEFAULT-TIMES-1))
     (144 78 (:REWRITE INTEGERP-<-CONSTANT))
     (133 5 (:REWRITE |(< (/ x) y) with (< x 0)|))
     (132 12 (:REWRITE |(* y (* x z))|))
     (128 78 (:REWRITE CONSTANT-<-INTEGERP))
     (116 102 (:REWRITE DEFAULT-PLUS-1))
     (110 94 (:REWRITE DEFAULT-LESS-THAN-1))
     (102 102 (:REWRITE DEFAULT-PLUS-2))
     (96 94 (:REWRITE DEFAULT-LESS-THAN-2))
     (95 95
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (94 94 (:REWRITE THE-FLOOR-BELOW))
     (94 94 (:REWRITE THE-FLOOR-ABOVE))
     (90 78
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (88 88
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (88 88
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (88 88
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (88 88
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (88 88
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (88 88
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (88 88
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (88 88
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (88 88 (:REWRITE |(< (/ x) (/ y))|))
     (88 88 (:REWRITE |(< (- x) (- y))|))
     (87 5 (:REWRITE |(< (/ x) y) with (< 0 x)|))
     (78 78
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (72 64 (:REWRITE SIMPLIFY-SUMS-<))
     (72 16 (:REWRITE |(* c (* d x))|))
     (72 4 (:REWRITE |(* (* x y) z)|))
     (61 59 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (47 11 (:REWRITE |(* x (- y))|))
     (32 32 (:REWRITE REDUCE-INTEGERP-+))
     (32 32 (:REWRITE INTEGERP-MINUS-X))
     (32 32 (:META META-INTEGERP-CORRECT))
     (30 30 (:REWRITE |(* (- x) y)|))
     (28 28
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (23 23 (:REWRITE DEFAULT-MINUS))
     (14 14 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (14 14 (:REWRITE |(< (+ c/d x) y)|))
     (14 14 (:REWRITE |(< (+ (- c) x) y)|))
     (13 6
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (12 12 (:REWRITE |(< y (+ (- c) x))|))
     (12 12 (:REWRITE |(< x (+ c/d y))|))
     (10 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (8 4
        (:TYPE-PRESCRIPTION RTL::Q$-CONSTRAINT))
     (8 2 (:REWRITE RATIONALP-X))
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
     (6 6 (:REWRITE |(+ c (+ d x))|))
     (4 4 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (4 4 (:REWRITE |(< (/ x) 0)|))
     (4 4 (:REWRITE |(< (* x y) 0)|))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (2 2 (:REWRITE REDUCE-RATIONALP-+))
     (2 2 (:REWRITE REDUCE-RATIONALP-*))
     (2 2 (:REWRITE RATIONALP-MINUS-X))
     (2 2 (:META META-RATIONALP-CORRECT)))
(RTL::R-BOUND-INV-6
     (34589 34589
            (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (34589 34589
            (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (25783 12867 (:REWRITE INTEGERP-<-CONSTANT))
     (25742 15324
            (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (22447 13111 (:REWRITE |(< (- x) c)|))
     (20785 18773 (:REWRITE DEFAULT-TIMES-2))
     (19353 18773 (:REWRITE DEFAULT-TIMES-1))
     (16939 11923
            (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (16653 16653 (:REWRITE THE-FLOOR-BELOW))
     (16653 16653 (:REWRITE THE-FLOOR-ABOVE))
     (16653 12867 (:REWRITE CONSTANT-<-INTEGERP))
     (15623 14222
            (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (14528 14222
            (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (14222 14222
            (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (14222 14222
            (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (14222 14222
            (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (14222 14222
            (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (14222 14222
            (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (14222 14222
            (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (14222 14222 (:REWRITE |(< (/ x) (/ y))|))
     (14222 14222 (:REWRITE |(< (- x) (- y))|))
     (13404 11847 (:REWRITE DEFAULT-PLUS-1))
     (13034 10482 (:REWRITE SIMPLIFY-SUMS-<))
     (12252 12252
            (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (7610 1736 (:REWRITE RATIONALP-X))
     (6156 690 (:REWRITE ACL2-NUMBERP-X))
     (6050 6050 (:REWRITE REDUCE-INTEGERP-+))
     (6050 6050 (:REWRITE INTEGERP-MINUS-X))
     (6050 6050 (:META META-INTEGERP-CORRECT))
     (3865 3865 (:REWRITE |(* (- x) y)|))
     (3720 2047
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (3659 3659
           (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (3211 3055 (:REWRITE DEFAULT-MINUS))
     (2128 2047 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (2061 2061
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (2047 2047
           (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (2047 2047 (:REWRITE |(equal c (/ x))|))
     (2047 2047 (:REWRITE |(equal c (- x))|))
     (2047 2047 (:REWRITE |(equal (/ x) c)|))
     (2047 2047 (:REWRITE |(equal (/ x) (/ y))|))
     (2047 2047 (:REWRITE |(equal (- x) c)|))
     (2047 2047 (:REWRITE |(equal (- x) (- y))|))
     (1736 1736 (:REWRITE REDUCE-RATIONALP-+))
     (1736 1736 (:REWRITE REDUCE-RATIONALP-*))
     (1736 1736 (:REWRITE RATIONALP-MINUS-X))
     (1736 1736 (:META META-RATIONALP-CORRECT))
     (1664 1664 (:REWRITE |(< (+ c/d x) y)|))
     (1664 1664 (:REWRITE |(< (+ (- c) x) y)|))
     (1445 1441 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (1354 1354 (:REWRITE |(< y (+ (- c) x))|))
     (1204 602
           (:TYPE-PRESCRIPTION RTL::Q$-CONSTRAINT))
     (1129 1129 (:REWRITE |(< (/ x) 0)|))
     (1129 1129 (:REWRITE |(< (* x y) 0)|))
     (625 625
          (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (595 595
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (595 595
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (285 285
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (174 174 (:REWRITE |(equal (+ (- c) x) y)|))
     (82 82
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (82 82
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (82 82 (:REWRITE |(< 0 (/ x))|))
     (82 82 (:REWRITE |(< 0 (* x y))|))
     (25 25
         (:REWRITE |(< (* x y) 0) rationalp (* x y)|)))
(RTL::SRT-DIV-RAD-4
     (13087 13087
            (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (13087 13087
            (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (11406 3568 (:REWRITE |(< c (- x))|))
     (5924 3328 (:REWRITE INTEGERP-<-CONSTANT))
     (5660 3948
           (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (5660 3948
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (5549 5260 (:REWRITE DEFAULT-TIMES-2))
     (5491 4123 (:REWRITE DEFAULT-LESS-THAN-1))
     (5352 5260 (:REWRITE DEFAULT-TIMES-1))
     (5154 4510 (:REWRITE DEFAULT-PLUS-1))
     (4634 4510 (:REWRITE DEFAULT-PLUS-2))
     (4386 4123 (:REWRITE DEFAULT-LESS-THAN-2))
     (4305 3176
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (4240 3568
           (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (4123 4123 (:REWRITE THE-FLOOR-BELOW))
     (4123 4123 (:REWRITE THE-FLOOR-ABOVE))
     (3772 3568
           (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (3680 3328 (:REWRITE CONSTANT-<-INTEGERP))
     (3568 3568
           (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (3568 3568
           (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (3568 3568
           (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (3568 3568
           (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (3568 3568
           (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (3568 3568
           (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (3568 3568 (:REWRITE |(< (/ x) (/ y))|))
     (3568 3568 (:REWRITE |(< (- x) (- y))|))
     (3385 3385
           (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (3330 2596 (:REWRITE SIMPLIFY-SUMS-<))
     (3328 3328 (:REWRITE |(< (- x) c)|))
     (1376 1376 (:REWRITE REDUCE-INTEGERP-+))
     (1376 1376 (:REWRITE INTEGERP-MINUS-X))
     (1376 1376 (:META META-INTEGERP-CORRECT))
     (1332 1332
           (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (978 978 (:REWRITE |(* (- x) y)|))
     (906 894 (:REWRITE DEFAULT-MINUS))
     (888 444
          (:TYPE-PRESCRIPTION RTL::Q$-CONSTRAINT))
     (680 298
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (596 580 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (592 592 (:REWRITE |(< (+ c/d x) y)|))
     (592 592 (:REWRITE |(< (+ (- c) x) y)|))
     (494 494 (:REWRITE |(< y (+ (- c) x))|))
     (488 122 (:REWRITE RATIONALP-X))
     (433 433 (:REWRITE |(< (/ x) 0)|))
     (433 433 (:REWRITE |(< (* x y) 0)|))
     (315 315
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (315 315
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (302 298 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (298 298
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (298 298
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (298 298
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (298 298 (:REWRITE |(equal c (/ x))|))
     (298 298 (:REWRITE |(equal c (- x))|))
     (298 298 (:REWRITE |(equal (/ x) c)|))
     (298 298 (:REWRITE |(equal (/ x) (/ y))|))
     (298 298 (:REWRITE |(equal (- x) c)|))
     (298 298 (:REWRITE |(equal (- x) (- y))|))
     (210 210 (:REWRITE |(+ c (+ d x))|))
     (150 150
          (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (122 122 (:REWRITE REDUCE-RATIONALP-+))
     (122 122 (:REWRITE REDUCE-RATIONALP-*))
     (122 122 (:REWRITE RATIONALP-MINUS-X))
     (122 122 (:META META-RATIONALP-CORRECT))
     (36 36
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (15 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-3D))
     (15 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-2D))
     (15 15
         (:TYPE-PRESCRIPTION NOT-INTEGERP-1D)))
(RTL::MD8*64 (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
             (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
             (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
             (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B)))
(RTL::MD8 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
          (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
          (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B)))
(RTL::MAX-LOWER (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B)))
(RTL::MIN-UPPER (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B)))
(RTL::SEL-LIMITS-CHECK-8
     (10753 1345
            (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (9216 1024 (:REWRITE ACL2-NUMBERP-X))
     (4096 1024 (:REWRITE RATIONALP-X))
     (1345 1345 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (1345 1345
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (1345 1345
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (1345 1345
           (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (1345 1345 (:REWRITE |(equal c (/ x))|))
     (1345 1345 (:REWRITE |(equal c (- x))|))
     (1345 1345 (:REWRITE |(equal (/ x) c)|))
     (1345 1345 (:REWRITE |(equal (/ x) (/ y))|))
     (1345 1345 (:REWRITE |(equal (- x) c)|))
     (1345 1345 (:REWRITE |(equal (- x) (- y))|))
     (1182 1182
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (1182 1182
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (1182 1182
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (1024 1024 (:REWRITE REDUCE-RATIONALP-+))
     (1024 1024 (:REWRITE REDUCE-RATIONALP-*))
     (1024 1024 (:REWRITE REDUCE-INTEGERP-+))
     (1024 1024 (:REWRITE RATIONALP-MINUS-X))
     (1024 1024 (:REWRITE INTEGERP-MINUS-X))
     (1024 1024 (:META META-RATIONALP-CORRECT))
     (1024 1024 (:META META-INTEGERP-CORRECT))
     (131 131
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RTL::I64)
(RTL::BVECP-I$
     (45 1 (:REWRITE |(< x (/ y)) with (< 0 y)|))
     (42 1
         (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (24 4 (:REWRITE RTL::INTEGERP-FL))
     (12 6 (:REWRITE INTEGERP-<-CONSTANT))
     (10 6
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (10 6
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (10 6
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (10 6 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (10 6 (:REWRITE DEFAULT-LESS-THAN-1))
     (10 6
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (8 5 (:REWRITE DEFAULT-PLUS-2))
     (7 5 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (7 5 (:REWRITE DEFAULT-TIMES-2))
     (6 6 (:REWRITE THE-FLOOR-BELOW))
     (6 6 (:REWRITE THE-FLOOR-ABOVE))
     (6 6 (:REWRITE SIMPLIFY-SUMS-<))
     (6 6 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (6 6 (:REWRITE REDUCE-INTEGERP-+))
     (6 6 (:REWRITE INTEGERP-MINUS-X))
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
     (6 6 (:META META-INTEGERP-CORRECT))
     (6 5 (:REWRITE DEFAULT-TIMES-1))
     (5 5
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (5 5 (:REWRITE NORMALIZE-ADDENDS))
     (5 5 (:REWRITE DEFAULT-PLUS-1))
     (5 1 (:REWRITE |(* y x)|))
     (4 4 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
     (4 4 (:TYPE-PRESCRIPTION ABS))
     (4 4
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (4 4 (:LINEAR RTL::FL-MONOTONE-LINEAR))
     (2 2 (:REWRITE |(< (+ c/d x) y)|))
     (2 2 (:REWRITE |(< (+ (- c) x) y)|))
     (2 2 (:LINEAR RTL::N<=FL-LINEAR))
     (2 1
        (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (2 1 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (1 1 (:REWRITE |(< (/ x) 0)|))
     (1 1 (:REWRITE |(< (* x y) 0)|)))
(RTL::D$-I$-BOUNDS
     (52 16 (:REWRITE DEFAULT-PLUS-2))
     (48 48 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (48 48 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (48 48 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (45 1 (:REWRITE |(< x (/ y)) with (< 0 y)|))
     (42 1
         (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (41 41 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (41 41 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (41 41 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (28 5 (:REWRITE RTL::INTEGERP-FL))
     (19 13 (:REWRITE DEFAULT-TIMES-2))
     (19 6
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (19 6 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (16 16 (:REWRITE DEFAULT-PLUS-1))
     (16 13 (:REWRITE DEFAULT-TIMES-1))
     (16 6 (:REWRITE SIMPLIFY-SUMS-<))
     (16 6 (:REWRITE DEFAULT-LESS-THAN-2))
     (12 12
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (12 12 (:REWRITE NORMALIZE-ADDENDS))
     (12 6 (:REWRITE INTEGERP-<-CONSTANT))
     (10 10
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (10 6
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (10 6
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (10 6
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (9 6 (:REWRITE DEFAULT-LESS-THAN-1))
     (7 7 (:REWRITE REDUCE-INTEGERP-+))
     (7 7 (:REWRITE INTEGERP-MINUS-X))
     (7 7 (:META META-INTEGERP-CORRECT))
     (7 5 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (6 6 (:REWRITE THE-FLOOR-BELOW))
     (6 6 (:REWRITE THE-FLOOR-ABOVE))
     (6 6 (:REWRITE REMOVE-STRICT-INEQUALITIES))
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
     (4 4 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
     (4 4 (:TYPE-PRESCRIPTION ABS))
     (4 4 (:LINEAR RTL::FL-MONOTONE-LINEAR))
     (2 2 (:LINEAR RTL::N<=FL-LINEAR))
     (2 1
        (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (2 1 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (1 1 (:REWRITE |(< y (+ (- c) x))|))
     (1 1 (:REWRITE |(< x (+ c/d y))|)))
(RTL::SEL-LIMITS-8
     (1736 302 (:REWRITE DEFAULT-PLUS-2))
     (1412 1412
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (1408 1408
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (1058 302 (:REWRITE DEFAULT-PLUS-1))
     (815 297 (:REWRITE DEFAULT-TIMES-2))
     (341 42
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (341 42 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (337 63 (:REWRITE DEFAULT-MINUS))
     (336 297 (:REWRITE DEFAULT-TIMES-1))
     (287 62 (:REWRITE DEFAULT-LESS-THAN-2))
     (275 62 (:REWRITE DEFAULT-LESS-THAN-1))
     (216 36 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (186 186
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (186 21
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (162 18 (:REWRITE ACL2-NUMBERP-X))
     (139 139
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (72 18 (:REWRITE RATIONALP-X))
     (66 62
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (66 62
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (63 63 (:REWRITE |(* (- x) y)|))
     (62 62 (:REWRITE THE-FLOOR-BELOW))
     (62 62 (:REWRITE THE-FLOOR-ABOVE))
     (61 61 (:REWRITE |(< (/ x) (/ y))|))
     (54 54 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (54 54 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (54 54 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (51 43
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (49 43 (:REWRITE INTEGERP-<-CONSTANT))
     (45 1 (:REWRITE |(< x (/ y)) with (< 0 y)|))
     (43 43 (:REWRITE CONSTANT-<-INTEGERP))
     (43 43 (:REWRITE |(< y (+ (- c) x))|))
     (43 43 (:REWRITE |(< x (+ c/d y))|))
     (43 43
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (43 43
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (43 43
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (43 43
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (43 43 (:REWRITE |(< c (- x))|))
     (43 43
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (43 43
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (43 43
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (43 43 (:REWRITE |(< (- x) c)|))
     (43 41 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (40 40 (:REWRITE |(< (+ c/d x) y)|))
     (40 40 (:REWRITE |(< (+ (- c) x) y)|))
     (21 21 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (21 21
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (21 21 (:REWRITE REDUCE-INTEGERP-+))
     (21 21
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (21 21 (:REWRITE INTEGERP-MINUS-X))
     (21 21
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (21 21 (:REWRITE |(equal c (/ x))|))
     (21 21 (:REWRITE |(equal c (- x))|))
     (21 21 (:REWRITE |(equal (/ x) c)|))
     (21 21 (:REWRITE |(equal (/ x) (/ y))|))
     (21 21 (:REWRITE |(equal (- x) c)|))
     (21 21 (:REWRITE |(equal (- x) (- y))|))
     (21 21 (:META META-INTEGERP-CORRECT))
     (18 18 (:REWRITE REDUCE-RATIONALP-+))
     (18 18 (:REWRITE REDUCE-RATIONALP-*))
     (18 18 (:REWRITE RATIONALP-MINUS-X))
     (18 18 (:META META-RATIONALP-CORRECT))
     (4 4 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
     (4 4 (:TYPE-PRESCRIPTION ABS))
     (3 2
        (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (2 1
        (:REWRITE |(< x (/ y)) with (< y 0)|)))
(RTL::MD8-K-BOUNDS
     (810 18
          (:REWRITE |(< x (/ y)) with (< 0 y)|))
     (308 44 (:REWRITE ACL2-NUMBERP-X))
     (288 72
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (282 124
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (282 124
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (234 128 (:REWRITE DEFAULT-LESS-THAN-1))
     (234 126 (:REWRITE INTEGERP-<-CONSTANT))
     (228 124 (:REWRITE SIMPLIFY-SUMS-<))
     (206 126
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (200 128
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (200 128
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (180 128 (:REWRITE DEFAULT-LESS-THAN-2))
     (142 106 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (132 33 (:REWRITE RATIONALP-X))
     (128 128 (:REWRITE THE-FLOOR-BELOW))
     (128 128 (:REWRITE THE-FLOOR-ABOVE))
     (126 126 (:REWRITE CONSTANT-<-INTEGERP))
     (126 126
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (126 126
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (126 126
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (126 126
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (126 126 (:REWRITE |(< c (- x))|))
     (126 126
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (126 126
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (126 126
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (126 126 (:REWRITE |(< (/ x) (/ y))|))
     (126 126 (:REWRITE |(< (- x) c)|))
     (126 126 (:REWRITE |(< (- x) (- y))|))
     (101 76 (:REWRITE DEFAULT-PLUS-1))
     (92 56 (:REWRITE DEFAULT-TIMES-2))
     (90 18 (:REWRITE |(* y x)|))
     (74 56 (:REWRITE DEFAULT-TIMES-1))
     (72 72 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
     (72 72 (:TYPE-PRESCRIPTION ABS))
     (72 72 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (72 72
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (72 72
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (72 72
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (72 72 (:REWRITE |(equal c (/ x))|))
     (72 72 (:REWRITE |(equal c (- x))|))
     (72 72 (:REWRITE |(equal (/ x) c)|))
     (72 72 (:REWRITE |(equal (/ x) (/ y))|))
     (72 72 (:REWRITE |(equal (- x) c)|))
     (72 72 (:REWRITE |(equal (- x) (- y))|))
     (71 71 (:REWRITE REDUCE-INTEGERP-+))
     (71 71 (:REWRITE INTEGERP-MINUS-X))
     (71 71 (:META META-INTEGERP-CORRECT))
     (47 47
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (47 47 (:REWRITE NORMALIZE-ADDENDS))
     (38 38
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (38 20
         (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (36 18
         (:REWRITE |(< x (/ y)) with (< y 0)|))
     (33 33 (:REWRITE REDUCE-RATIONALP-+))
     (33 33 (:REWRITE REDUCE-RATIONALP-*))
     (33 33 (:REWRITE RATIONALP-MINUS-X))
     (33 33 (:META META-RATIONALP-CORRECT))
     (25 25 (:REWRITE |(< y (+ (- c) x))|))
     (25 25 (:REWRITE |(< x (+ c/d y))|))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RTL::R-BOUND-INV-8-1
     (132 132
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (132 132
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (132 132
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (45 45 (:TYPE-PRESCRIPTION NOT-INTEGERP-4D))
     (45 45 (:TYPE-PRESCRIPTION NOT-INTEGERP-3K))
     (45 45 (:TYPE-PRESCRIPTION NOT-INTEGERP-3D))
     (45 45 (:TYPE-PRESCRIPTION NOT-INTEGERP-2K))
     (45 45 (:TYPE-PRESCRIPTION NOT-INTEGERP-2D))
     (45 45 (:TYPE-PRESCRIPTION NOT-INTEGERP-1K))
     (45 45 (:TYPE-PRESCRIPTION NOT-INTEGERP-1D))
     (32 15 (:REWRITE DEFAULT-TIMES-2))
     (25 9 (:REWRITE DEFAULT-LESS-THAN-1))
     (19 8
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (19 8 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (18 8 (:REWRITE SIMPLIFY-SUMS-<))
     (15 15 (:REWRITE DEFAULT-TIMES-1))
     (11 11
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (11 9 (:REWRITE DEFAULT-LESS-THAN-2))
     (10 4
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (9 9 (:REWRITE THE-FLOOR-BELOW))
     (9 9 (:REWRITE THE-FLOOR-ABOVE))
     (8 8 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (8 8 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (8 8
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (8 8
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
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
     (7 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
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
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (2 2 (:REWRITE DEFAULT-MINUS))
     (2 2 (:REWRITE |(< (/ x) 0)|))
     (2 2 (:REWRITE |(< (* x y) 0)|))
     (1 1 (:REWRITE REDUCE-INTEGERP-+))
     (1 1 (:REWRITE INTEGERP-MINUS-X))
     (1 1 (:META META-INTEGERP-CORRECT)))
(RTL::SELECT-DIGIT-D8)
(RTL::R-BOUND-INV-8-2
     (444 4 (:REWRITE |(< x (/ y)) with (< 0 y)|))
     (440 4
          (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (204 8 (:REWRITE |(* x (+ y z))|))
     (118 4 (:REWRITE |(* y x)|))
     (116 102 (:REWRITE DEFAULT-PLUS-1))
     (109 6
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (107 64
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (106 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (102 102 (:REWRITE DEFAULT-PLUS-2))
     (101 67 (:REWRITE DEFAULT-LESS-THAN-2))
     (92 50 (:REWRITE SIMPLIFY-SUMS-<))
     (91 91 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (91 91 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (91 91 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (88 64 (:REWRITE INTEGERP-<-CONSTANT))
     (88 8 (:REWRITE |(* y (* x z))|))
     (83 67 (:REWRITE DEFAULT-LESS-THAN-1))
     (82 81 (:REWRITE DEFAULT-TIMES-2))
     (81 81 (:REWRITE DEFAULT-TIMES-1))
     (67 67 (:REWRITE THE-FLOOR-BELOW))
     (67 67 (:REWRITE THE-FLOOR-ABOVE))
     (64 64
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (64 64
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (64 64
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
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
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (64 64
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (64 64
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (64 64
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (64 64 (:REWRITE |(< (/ x) (/ y))|))
     (64 64 (:REWRITE |(< (- x) c)|))
     (64 64 (:REWRITE |(< (- x) (- y))|))
     (56 56 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (45 45
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (40 4 (:REWRITE |(* x (- y))|))
     (36 8 (:REWRITE |(* c (* d x))|))
     (28 28
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (14 14 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (14 14 (:REWRITE |(< (+ c/d x) y)|))
     (14 14 (:REWRITE |(< (+ (- c) x) y)|))
     (14 14 (:REWRITE |(* (- x) y)|))
     (13 13 (:REWRITE DEFAULT-MINUS))
     (12 12 (:REWRITE |(< y (+ (- c) x))|))
     (12 12 (:REWRITE |(< x (+ c/d y))|))
     (9 9 (:REWRITE REDUCE-INTEGERP-+))
     (9 9 (:REWRITE INTEGERP-MINUS-X))
     (9 9 (:META META-INTEGERP-CORRECT))
     (8 4
        (:TYPE-PRESCRIPTION RTL::Q$-CONSTRAINT))
     (8 2 (:REWRITE RATIONALP-X))
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
     (6 6 (:REWRITE |(+ c (+ d x))|))
     (4 4 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (4 4
        (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (4 4 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (4 4 (:REWRITE |(< (/ x) 0)|))
     (4 4 (:REWRITE |(< (* x y) 0)|))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (2 2 (:REWRITE REDUCE-RATIONALP-+))
     (2 2 (:REWRITE REDUCE-RATIONALP-*))
     (2 2 (:REWRITE RATIONALP-MINUS-X))
     (2 2 (:META META-RATIONALP-CORRECT)))
(RTL::R-BOUND-INV-8-3
     (8 2 (:REWRITE RATIONALP-X))
     (5 5
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (5 5 (:REWRITE DEFAULT-TIMES-2))
     (5 5 (:REWRITE DEFAULT-TIMES-1))
     (4 4 (:REWRITE REDUCE-INTEGERP-+))
     (4 4 (:REWRITE INTEGERP-MINUS-X))
     (4 4 (:META META-INTEGERP-CORRECT))
     (3 3 (:REWRITE THE-FLOOR-BELOW))
     (3 3 (:REWRITE THE-FLOOR-ABOVE))
     (3 3
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (3 3 (:REWRITE NORMALIZE-ADDENDS))
     (3 3 (:REWRITE DEFAULT-PLUS-2))
     (3 3 (:REWRITE DEFAULT-PLUS-1))
     (3 3 (:REWRITE DEFAULT-LESS-THAN-2))
     (3 3 (:REWRITE DEFAULT-LESS-THAN-1))
     (2 2 (:REWRITE SIMPLIFY-SUMS-<))
     (2 2
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (2 2 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (2 2 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (2 2 (:REWRITE REDUCE-RATIONALP-+))
     (2 2 (:REWRITE REDUCE-RATIONALP-*))
     (2 2
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (2 2
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (2 2 (:REWRITE RATIONALP-MINUS-X))
     (2 2 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (2 2 (:REWRITE INTEGERP-<-CONSTANT))
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
     (2 2 (:META META-RATIONALP-CORRECT))
     (1 1 (:REWRITE |(< (+ (- c) x) y)|)))
(RTL::RAT-M (2 1 (:TYPE-PRESCRIPTION RTL::RAT-M)))
(RTL::INT-64-M (564 52 (:REWRITE ACL2-NUMBERP-X))
               (465 277
                    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
               (277 277 (:REWRITE SIMPLIFY-SUMS-EQUAL))
               (277 277
                    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
               (277 277
                    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
               (277 277
                    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
               (277 277 (:REWRITE |(equal c (/ x))|))
               (277 277 (:REWRITE |(equal c (- x))|))
               (277 277 (:REWRITE |(equal (/ x) c)|))
               (277 277 (:REWRITE |(equal (/ x) (/ y))|))
               (277 277 (:REWRITE |(equal (- x) c)|))
               (277 277 (:REWRITE |(equal (- x) (- y))|))
               (256 52 (:REWRITE RATIONALP-X))
               (136 64 (:REWRITE DEFAULT-TIMES-2))
               (128 8 (:REWRITE RTL::INTEGERP-FL))
               (60 60 (:REWRITE REDUCE-INTEGERP-+))
               (60 60 (:REWRITE INTEGERP-MINUS-X))
               (60 60 (:META META-INTEGERP-CORRECT))
               (52 52 (:REWRITE REDUCE-RATIONALP-+))
               (52 52 (:REWRITE REDUCE-RATIONALP-*))
               (52 52 (:REWRITE RATIONALP-MINUS-X))
               (52 52 (:META META-RATIONALP-CORRECT))
               (40 40 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
               (40 40 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
               (40 40 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
               (40 40 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
               (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
               (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
               (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
               (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
               (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
               (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
               (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
               (16 16
                   (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
               (12 12
                   (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
               (10 5 (:TYPE-PRESCRIPTION RTL::RAT-M))
               (2 1 (:TYPE-PRESCRIPTION RTL::INT-64-M)))
(RTL::R-BOUND-INV-8-4
     (22473 202
            (:REWRITE |(< x (/ y)) with (< 0 y)|))
     (22269 202
            (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (13588 35 (:REWRITE RTL::INT-64-M))
     (13529 216 (:DEFINITION MEMBER-EQUAL))
     (10294 404 (:REWRITE |(* x (+ y z))|))
     (8157 7119 (:REWRITE DEFAULT-PLUS-2))
     (7866 7119 (:REWRITE DEFAULT-PLUS-1))
     (7433 895
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (6878 3439
           (:TYPE-PRESCRIPTION RTL::Q$-CONSTRAINT))
     (5957 202 (:REWRITE |(* y x)|))
     (5627 2789
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (5190 5190
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (5190 5190
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (5190 5190
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (5011 2916 (:REWRITE DEFAULT-LESS-THAN-2))
     (4838 2058 (:REWRITE SIMPLIFY-SUMS-<))
     (4595 4354 (:REWRITE DEFAULT-TIMES-2))
     (4464 404 (:REWRITE |(* y (* x z))|))
     (4356 4354 (:REWRITE DEFAULT-TIMES-1))
     (4009 2916 (:REWRITE DEFAULT-LESS-THAN-1))
     (3803 2789 (:REWRITE INTEGERP-<-CONSTANT))
     (2916 2916 (:REWRITE THE-FLOOR-BELOW))
     (2916 2916 (:REWRITE THE-FLOOR-ABOVE))
     (2790 2789
           (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (2790 2789
           (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (2789 2789
           (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (2789 2789
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (2789 2789 (:REWRITE CONSTANT-<-INTEGERP))
     (2789 2789
           (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (2789 2789
           (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (2789 2789
           (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (2789 2789
           (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (2789 2789 (:REWRITE |(< c (- x))|))
     (2789 2789
           (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (2789 2789
           (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (2789 2789
           (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (2789 2789 (:REWRITE |(< (/ x) (/ y))|))
     (2789 2789 (:REWRITE |(< (- x) c)|))
     (2789 2789 (:REWRITE |(< (- x) (- y))|))
     (2514 2514
           (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (2509 2509
           (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (2385 2385
           (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (1980 198 (:REWRITE |(* x (- y))|))
     (1826 404 (:REWRITE |(* c (* d x))|))
     (1720 560 (:REWRITE |(+ c (+ d x))|))
     (1692 632
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (998 632 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (895 895
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (775 775 (:REWRITE |(< (+ c/d x) y)|))
     (775 775 (:REWRITE |(< (+ (- c) x) y)|))
     (735 735 (:REWRITE |(* (- x) y)|))
     (735 731 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (686 683 (:REWRITE DEFAULT-MINUS))
     (632 632
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (632 632 (:REWRITE |(equal c (/ x))|))
     (632 632 (:REWRITE |(equal c (- x))|))
     (632 632 (:REWRITE |(equal (/ x) c)|))
     (632 632 (:REWRITE |(equal (/ x) (/ y))|))
     (632 632 (:REWRITE |(equal (- x) c)|))
     (632 632 (:REWRITE |(equal (- x) (- y))|))
     (606 606 (:REWRITE |(< y (+ (- c) x))|))
     (606 606 (:REWRITE |(< x (+ c/d y))|))
     (566 566 (:REWRITE REDUCE-INTEGERP-+))
     (566 566 (:REWRITE INTEGERP-MINUS-X))
     (566 566 (:META META-INTEGERP-CORRECT))
     (496 124 (:REWRITE RATIONALP-X))
     (288 288 (:REWRITE |(< (/ x) 0)|))
     (288 288 (:REWRITE |(< (* x y) 0)|))
     (204 202
          (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (204 202
          (:REWRITE |(< x (/ y)) with (< y 0)|))
     (202 202
          (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (163 163
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (163 163
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (124 124 (:REWRITE REDUCE-RATIONALP-+))
     (124 124 (:REWRITE REDUCE-RATIONALP-*))
     (124 124 (:REWRITE RATIONALP-MINUS-X))
     (124 124 (:META META-RATIONALP-CORRECT))
     (50 50
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RTL::R-BOUND-INV-8-5
     (444 4 (:REWRITE |(< x (/ y)) with (< 0 y)|))
     (440 4
          (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (363 363
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (363 363
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (363 363
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (219 96
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (205 6
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (204 82 (:REWRITE SIMPLIFY-SUMS-<))
     (204 8 (:REWRITE |(* x (+ y z))|))
     (202 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (182 134 (:REWRITE DEFAULT-PLUS-2))
     (165 99 (:REWRITE DEFAULT-LESS-THAN-2))
     (163 99 (:REWRITE DEFAULT-LESS-THAN-1))
     (148 134 (:REWRITE DEFAULT-PLUS-1))
     (120 96 (:REWRITE INTEGERP-<-CONSTANT))
     (118 4 (:REWRITE |(* y x)|))
     (114 113 (:REWRITE DEFAULT-TIMES-2))
     (113 113 (:REWRITE DEFAULT-TIMES-1))
     (99 99 (:REWRITE THE-FLOOR-BELOW))
     (99 99 (:REWRITE THE-FLOOR-ABOVE))
     (96 96
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (96 96
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (96 96
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
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
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (96 96
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (96 96
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (96 96
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (96 96 (:REWRITE |(< (/ x) (/ y))|))
     (96 96 (:REWRITE |(< (- x) c)|))
     (96 96 (:REWRITE |(< (- x) (- y))|))
     (88 88 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (88 8 (:REWRITE |(* y (* x z))|))
     (77 77
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (60 60
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (46 46 (:REWRITE |(< (+ c/d x) y)|))
     (46 46 (:REWRITE |(< (+ (- c) x) y)|))
     (40 4 (:REWRITE |(* x (- y))|))
     (36 8 (:REWRITE |(* c (* d x))|))
     (14 14 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (14 14 (:REWRITE |(* (- x) y)|))
     (13 13 (:REWRITE DEFAULT-MINUS))
     (12 12 (:REWRITE |(< y (+ (- c) x))|))
     (12 12 (:REWRITE |(< x (+ c/d y))|))
     (12 6
         (:TYPE-PRESCRIPTION RTL::Q$-CONSTRAINT))
     (9 9 (:REWRITE REDUCE-INTEGERP-+))
     (9 9 (:REWRITE INTEGERP-MINUS-X))
     (9 9 (:META META-INTEGERP-CORRECT))
     (8 2 (:REWRITE RATIONALP-X))
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
     (6 6 (:REWRITE |(+ c (+ d x))|))
     (4 4 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (4 4
        (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (4 4 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (4 4 (:REWRITE |(< (/ x) 0)|))
     (4 4 (:REWRITE |(< (* x y) 0)|))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (2 2 (:REWRITE REDUCE-RATIONALP-+))
     (2 2 (:REWRITE REDUCE-RATIONALP-*))
     (2 2 (:REWRITE RATIONALP-MINUS-X))
     (2 2 (:META META-RATIONALP-CORRECT)))
(RTL::R-BOUND-INV-8-6
     (50963 50963
            (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (50963 50963
            (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (45749 40365 (:REWRITE DEFAULT-PLUS-1))
     (41291 40365 (:REWRITE DEFAULT-PLUS-2))
     (37289 23438 (:REWRITE DEFAULT-LESS-THAN-2))
     (34430 32468 (:REWRITE DEFAULT-TIMES-2))
     (34135 18360
            (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (33767 22319 (:REWRITE INTEGERP-<-CONSTANT))
     (33591 23438 (:REWRITE DEFAULT-LESS-THAN-1))
     (33174 32468 (:REWRITE DEFAULT-TIMES-1))
     (27025 22319
            (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (26481 13319 (:REWRITE SIMPLIFY-SUMS-<))
     (25236 22508
            (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (25236 22508
            (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (24280 12140
            (:TYPE-PRESCRIPTION RTL::Q$-CONSTRAINT))
     (23438 23438 (:REWRITE THE-FLOOR-BELOW))
     (23438 23438 (:REWRITE THE-FLOOR-ABOVE))
     (22319 22319 (:REWRITE CONSTANT-<-INTEGERP))
     (22319 22319
            (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (22319 22319
            (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (22319 22319
            (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (22319 22319
            (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (22319 22319 (:REWRITE |(< c (- x))|))
     (22319 22319
            (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (22319 22319
            (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (22319 22319
            (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (22319 22319 (:REWRITE |(< (/ x) (/ y))|))
     (22319 22319 (:REWRITE |(< (- x) c)|))
     (22319 22319 (:REWRITE |(< (- x) (- y))|))
     (18932 18932
            (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (13043 13043
            (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (11174 3546
            (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (5290 5290 (:REWRITE |(< (+ c/d x) y)|))
     (5290 5290 (:REWRITE |(< (+ (- c) x) y)|))
     (5245 5245 (:REWRITE REDUCE-INTEGERP-+))
     (5245 5245 (:REWRITE INTEGERP-MINUS-X))
     (5245 5245 (:META META-INTEGERP-CORRECT))
     (5239 3546 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (5161 5161 (:REWRITE |(* (- x) y)|))
     (5136 5100 (:REWRITE DEFAULT-MINUS))
     (5089 5041 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (4301 4301 (:REWRITE |(< y (+ (- c) x))|))
     (3684 921 (:REWRITE RATIONALP-X))
     (3546 3546
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (3546 3546
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (3546 3546
           (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (3546 3546 (:REWRITE |(equal c (/ x))|))
     (3546 3546 (:REWRITE |(equal c (- x))|))
     (3546 3546 (:REWRITE |(equal (/ x) c)|))
     (3546 3546 (:REWRITE |(equal (/ x) (/ y))|))
     (3546 3546 (:REWRITE |(equal (- x) c)|))
     (3546 3546 (:REWRITE |(equal (- x) (- y))|))
     (2871 2165
           (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (2749 2043
           (:REWRITE |(< x (/ y)) with (< y 0)|))
     (2010 2010 (:REWRITE |(+ c (+ d x))|))
     (1930 1930 (:REWRITE |(< (/ x) 0)|))
     (1930 1930 (:REWRITE |(< (* x y) 0)|))
     (1294 1294
           (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (921 921 (:REWRITE REDUCE-RATIONALP-+))
     (921 921 (:REWRITE REDUCE-RATIONALP-*))
     (921 921 (:REWRITE RATIONALP-MINUS-X))
     (921 921 (:META META-RATIONALP-CORRECT))
     (721 721
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (721 721
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (168 168
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RTL::SRT-DIV-RAD-8
     (26442 292
            (:REWRITE |(< x (/ y)) with (< 0 y)|))
     (10184 400 (:REWRITE |(* x (+ y z))|))
     (7663 7663
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (7663 7663
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (6356 292 (:REWRITE |(* y x)|))
     (6271 5507 (:REWRITE DEFAULT-PLUS-1))
     (5684 3463
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (5569 5507 (:REWRITE DEFAULT-PLUS-2))
     (5536 3580 (:REWRITE DEFAULT-LESS-THAN-2))
     (5025 3465 (:REWRITE INTEGERP-<-CONSTANT))
     (4927 4679 (:REWRITE DEFAULT-TIMES-2))
     (4775 4679 (:REWRITE DEFAULT-TIMES-1))
     (4617 2731 (:REWRITE SIMPLIFY-SUMS-<))
     (4440 400 (:REWRITE |(* y (* x z))|))
     (3949 3580 (:REWRITE DEFAULT-LESS-THAN-1))
     (3841 3465
           (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (3835 3467
           (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (3835 3467
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (3580 3580 (:REWRITE THE-FLOOR-BELOW))
     (3580 3580 (:REWRITE THE-FLOOR-ABOVE))
     (3465 3465 (:REWRITE CONSTANT-<-INTEGERP))
     (3465 3465
           (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (3465 3465
           (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (3465 3465
           (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (3465 3465
           (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (3465 3465 (:REWRITE |(< c (- x))|))
     (3465 3465
           (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (3465 3465
           (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (3465 3465
           (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (3465 3465 (:REWRITE |(< (/ x) (/ y))|))
     (3465 3465 (:REWRITE |(< (- x) c)|))
     (3465 3465 (:REWRITE |(< (- x) (- y))|))
     (3155 2971
           (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (2758 2758
           (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (2524 1262
           (:TYPE-PRESCRIPTION RTL::Q$-CONSTRAINT))
     (1920 192 (:REWRITE |(* x (- y))|))
     (1784 302
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (1559 1559
           (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (864 302 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (778 772 (:REWRITE DEFAULT-MINUS))
     (740 740 (:REWRITE |(* (- x) y)|))
     (740 732 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (738 738 (:REWRITE REDUCE-INTEGERP-+))
     (738 738 (:REWRITE INTEGERP-MINUS-X))
     (738 738 (:META META-INTEGERP-CORRECT))
     (732 732 (:REWRITE |(< (+ c/d x) y)|))
     (732 732 (:REWRITE |(< (+ (- c) x) y)|))
     (600 600 (:REWRITE |(< y (+ (- c) x))|))
     (600 600 (:REWRITE |(< x (+ c/d y))|))
     (520 130 (:REWRITE RATIONALP-X))
     (505 505 (:REWRITE |(< (/ x) 0)|))
     (505 505 (:REWRITE |(< (* x y) 0)|))
     (390 294
          (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (388 292
          (:REWRITE |(< x (/ y)) with (< y 0)|))
     (373 373
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (373 373
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (302 302
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (302 302
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (302 302
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (302 302 (:REWRITE |(equal c (/ x))|))
     (302 302 (:REWRITE |(equal c (- x))|))
     (302 302 (:REWRITE |(equal (/ x) c)|))
     (302 302 (:REWRITE |(equal (/ x) (/ y))|))
     (302 302 (:REWRITE |(equal (- x) c)|))
     (302 302 (:REWRITE |(equal (- x) (- y))|))
     (288 288 (:REWRITE |(+ c (+ d x))|))
     (200 200
          (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (130 130 (:REWRITE REDUCE-RATIONALP-+))
     (130 130 (:REWRITE REDUCE-RATIONALP-*))
     (130 130 (:REWRITE RATIONALP-MINUS-X))
     (130 130 (:META META-RATIONALP-CORRECT))
     (15 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-3D))
     (15 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-2D))
     (15 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-1D))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RTL::E%)
(RTL::X%)
(RTL::A%)
(RTL::Q%)
(RTL::R%
 (5
  5
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (5 5
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (5 5
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (5 5
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (5 5
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A)))
(RTL::RHO% (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
           (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
           (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B)))
(RTL::E%-CONSTRAINT)
(RTL::X%-CONSTRAINT)
(RTL::A%-CONSTRAINT)
(RTL::Q%-CONSTRAINT (4 2
                       (:TYPE-PRESCRIPTION RTL::Q%-CONSTRAINT))
                    (2 2 (:TYPE-PRESCRIPTION ZP)))
(RTL::RHO%-CONSTRAINT)
(RTL::NATP-E%)
(RTL::RATP-X%)
(RTL::INTP-A%)
(RTL::INTP-Q% (3 3 (:TYPE-PRESCRIPTION ZP))
              (2 1 (:TYPE-PRESCRIPTION RTL::INTP-Q%)))
(RTL::NATP-R%
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
(RTL::RATP-RHO% (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B)))
(RTL::QUOT%
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
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (5 5
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (5 5
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (5 5
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT)))
(RTL::REM%
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
(RTL::INT-R%*N)
(RTL::INT-QUOT-SQRT
 (180 19 (:REWRITE DEFAULT-TIMES-2))
 (123 19 (:REWRITE DEFAULT-TIMES-1))
 (115
  115
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (115 115
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (115
     115
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (115 115
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (115 115
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (35 18 (:REWRITE DEFAULT-PLUS-2))
 (24 8 (:REWRITE DEFAULT-EXPT-1))
 (21 18 (:REWRITE DEFAULT-PLUS-1))
 (19 4 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (12 3
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (10 10
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (8 8 (:REWRITE DEFAULT-EXPT-2))
 (8 8 (:REWRITE |(expt 1/c n)|))
 (8 8 (:REWRITE |(expt (- x) n)|))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (3 3 (:REWRITE REDUCE-INTEGERP-+))
 (3 3 (:REWRITE INTEGERP-MINUS-X))
 (3 3 (:META META-INTEGERP-CORRECT))
 (2 2 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE THE-FLOOR-BELOW))
 (1 1 (:REWRITE THE-FLOOR-ABOVE))
 (1 1 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (1 1
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (1 1
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (1 1 (:REWRITE INTEGERP-<-CONSTANT))
 (1 1 (:REWRITE DEFAULT-MINUS))
 (1 1 (:REWRITE DEFAULT-LESS-THAN-2))
 (1 1 (:REWRITE DEFAULT-LESS-THAN-1))
 (1 1 (:REWRITE CONSTANT-<-INTEGERP))
 (1 1 (:REWRITE BUBBLE-DOWN-*-MATCH-3))
 (1 1
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (1 1
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (1 1
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (1 1
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (1 1 (:REWRITE |(< c (- x))|))
 (1 1
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (1 1
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (1 1
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (1 1
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (/ x) (/ y))|))
 (1 1 (:REWRITE |(< (- x) c)|))
 (1 1 (:REWRITE |(< (- x) (- y))|))
 (1 1 (:REWRITE |(< (* x y) 0)|))
 (1 1 (:REWRITE |(* c (expt d n))|))
 (1 1 (:REWRITE |(* c (* d x))|))
 (1 1
    (:REWRITE |(* (expt c m) (expt d n))|)))
(RTL::REM0-SQRT-REWRITE (5 3 (:REWRITE DEFAULT-PLUS-2))
                        (4 3 (:REWRITE DEFAULT-PLUS-1))
                        (3 1 (:REWRITE DEFAULT-EXPT-1))
                        (2 2
                           (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                        (2 2 (:REWRITE NORMALIZE-ADDENDS))
                        (2 1 (:REWRITE DEFAULT-TIMES-2))
                        (1 1 (:TYPE-PRESCRIPTION RTL::R%))
                        (1 1 (:TYPE-PRESCRIPTION RTL::NATP-R%))
                        (1 1 (:REWRITE DEFAULT-TIMES-1))
                        (1 1 (:REWRITE DEFAULT-EXPT-2))
                        (1 1 (:REWRITE |(expt 1/c n)|))
                        (1 1 (:REWRITE |(expt (- x) n)|)))
(RTL::REM-SQRT-RECURRENCE
 (879 72 (:REWRITE DEFAULT-TIMES-2))
 (810 71 (:REWRITE DEFAULT-PLUS-2))
 (435 72 (:REWRITE DEFAULT-TIMES-1))
 (380 71 (:REWRITE DEFAULT-PLUS-1))
 (313 27 (:REWRITE DEFAULT-MINUS))
 (239
  239
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (239 239
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (239
     239
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (239 239
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (239 239
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (98 24 (:REWRITE DEFAULT-EXPT-1))
 (69 69
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (65 11 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (49 49
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (35 35
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE))
 (24 24 (:REWRITE DEFAULT-EXPT-2))
 (22 22 (:REWRITE |(expt 1/c n)|))
 (22 22 (:REWRITE |(expt (- x) n)|))
 (20 5
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (17 17 (:TYPE-PRESCRIPTION RTL::RATP-X%))
 (16 8
     (:TYPE-PRESCRIPTION RTL::Q%-CONSTRAINT))
 (10 10 (:REWRITE |(* c (* d x))|))
 (7 7 (:REWRITE FOLD-CONSTS-IN-+))
 (5 5
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (5 5
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (5 5
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (5 5 (:REWRITE ZP-OPEN))
 (5 5 (:REWRITE |(* (- x) y)|))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (2 2 (:REWRITE |(* c (expt d n))|))
 (2 2
    (:REWRITE |(* (expt c m) (expt d n))|))
 (1 1 (:REWRITE THE-FLOOR-BELOW))
 (1 1 (:REWRITE THE-FLOOR-ABOVE))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1 (:REWRITE SIMPLIFY-SUMS-<))
 (1 1
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (1 1 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (1 1 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (1 1
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (1 1
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (1 1 (:REWRITE REDUCE-INTEGERP-+))
 (1 1 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (1 1 (:REWRITE INTEGERP-MINUS-X))
 (1 1 (:REWRITE INTEGERP-<-CONSTANT))
 (1 1 (:REWRITE DEFAULT-LESS-THAN-2))
 (1 1 (:REWRITE DEFAULT-LESS-THAN-1))
 (1 1 (:REWRITE CONSTANT-<-INTEGERP))
 (1 1
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (1 1
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (1 1
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (1 1
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (1 1 (:REWRITE |(< c (- x))|))
 (1 1
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (1 1
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (1 1
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (1 1
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (/ x) (/ y))|))
 (1 1 (:REWRITE |(< (- x) c)|))
 (1 1 (:REWRITE |(< (- x) (- y))|))
 (1 1 (:REWRITE |(< (* x y) 0)|))
 (1 1 (:META META-INTEGERP-CORRECT)))
(RTL::BLO%
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
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (5 5
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (5 5
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (5 5
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (4 4
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3E-EXPT))
 (4 4
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2E-EXPT))
 (4 4
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1E-EXPT)))
(RTL::BHI%
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
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (5 5
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (5 5
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (5 5
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (4 4
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3E-EXPT))
 (4 4
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2E-EXPT))
 (4 4
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1E-EXPT)))
(RTL::BLOHI
 (2001 75 (:REWRITE DEFAULT-PLUS-2))
 (1686
  1686
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1686
      1686
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1686
     1686
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1686 1686
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1686 1686
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (1125 126
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (1085 75 (:REWRITE DEFAULT-PLUS-1))
 (765 78 (:REWRITE DEFAULT-TIMES-2))
 (762 134 (:REWRITE DEFAULT-LESS-THAN-2))
 (736 16 (:LINEAR EXPT->=-1-TWO))
 (736 16 (:LINEAR EXPT-<=-1-ONE))
 (688 16 (:LINEAR EXPT-X->-X))
 (688 16 (:LINEAR EXPT->-1-ONE))
 (688 16 (:LINEAR EXPT-<-1-TWO))
 (590 590
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (505 134 (:REWRITE DEFAULT-LESS-THAN-1))
 (497 119 (:REWRITE SIMPLIFY-SUMS-<))
 (392 32
      (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (374 134 (:REWRITE |(< (- x) c)|))
 (372 372
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (372 372
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (372 372
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (371 78 (:REWRITE DEFAULT-TIMES-1))
 (258 258 (:REWRITE |arith (expt 1/c n)|))
 (246 28 (:REWRITE DEFAULT-MINUS))
 (240 16 (:LINEAR EXPT-X->=-X))
 (180 134 (:REWRITE |(< (- x) (- y))|))
 (171 31 (:REWRITE DEFAULT-EXPT-1))
 (159 159
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3E-EXPT))
 (159 159
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2E-EXPT))
 (159 159
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1E-EXPT))
 (144 15 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (134 134 (:REWRITE THE-FLOOR-BELOW))
 (134 134 (:REWRITE THE-FLOOR-ABOVE))
 (134 134
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (134 134
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (134 134
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (134 134
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (134 134
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (134 134
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (134 134 (:REWRITE |(< c (- x))|))
 (134 134
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (134 134
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (134 134
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (134 134
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (134 134 (:REWRITE |(< (/ x) (/ y))|))
 (126 126
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (126 126 (:REWRITE INTEGERP-<-CONSTANT))
 (126 126 (:REWRITE CONSTANT-<-INTEGERP))
 (123 123
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3L-EXPT))
 (123 123
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2L-EXPT))
 (123 123
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1L-EXPT))
 (110 110 (:REWRITE |arith (* c (* d x))|))
 (80 16 (:LINEAR EXPT->-1-TWO))
 (80 16 (:LINEAR EXPT-<-1-ONE))
 (70 70 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (44 44 (:REWRITE |arith (* (- x) y)|))
 (32 32
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (32 32
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (31 31 (:REWRITE DEFAULT-EXPT-2))
 (30 30
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (26 26 (:REWRITE |(expt 1/c n)|))
 (16 16
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (16 16
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (16 16 (:REWRITE |(< 0 (/ x))|))
 (16 16 (:REWRITE |(< 0 (* x y))|))
 (16 16 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (16 16 (:LINEAR EXPT-LINEAR-UPPER-<))
 (16 16 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (16 16 (:LINEAR EXPT-LINEAR-LOWER-<))
 (13 13 (:REWRITE |(* c (* d x))|))
 (12 12
     (:REWRITE |arith (* (expt c n) (expt d n))|))
 (10 10 (:REWRITE |(< y (+ (- c) x))|))
 (10 10 (:REWRITE |(< x (+ c/d y))|))
 (10 10 (:REWRITE |(< (+ c/d x) y)|))
 (10 10 (:REWRITE |(< (+ (- c) x) y)|))
 (9 9 (:REWRITE |(< (/ x) 0)|))
 (9 9 (:REWRITE |(< (* x y) 0)|))
 (8 8 (:REWRITE |(+ c (+ d x))|))
 (6 6 (:REWRITE |arith (+ c (+ d x))|))
 (6 6 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE |(expt c (* d n))|))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1 (:REWRITE REDUCE-INTEGERP-+))
 (1 1 (:REWRITE INTEGERP-MINUS-X))
 (1 1 (:REWRITE |(expt (- c) n)|))
 (1 1 (:META META-INTEGERP-CORRECT)))
(RTL::R0-BOUNDS-1 (5 5
                     (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
                  (4 4 (:REWRITE |arith (* c (* d x))|))
                  (2 2 (:REWRITE |arith (- (* c x))|))
                  (2 2 (:REWRITE |arith (* (- x) y)|))
                  (1 1 (:REWRITE ARITH-NORMALIZE-ADDENDS)))
(RTL::REM0-SQRT-BOUNDS
 (479 2
      (:REWRITE |(<= x (/ y)) with (< y 0)|))
 (327 66 (:REWRITE DEFAULT-PLUS-2))
 (218 66 (:REWRITE DEFAULT-PLUS-1))
 (199 192
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (192
   192
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (192
  192
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (192 192
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (192
     192
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (192 192
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (192 192
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (135 21
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (118 60 (:REWRITE DEFAULT-TIMES-2))
 (97 22 (:REWRITE DEFAULT-LESS-THAN-2))
 (92 4 (:LINEAR EXPT-<=-1-ONE))
 (79 16 (:REWRITE SIMPLIFY-SUMS-<))
 (76 60 (:REWRITE DEFAULT-TIMES-1))
 (61 22 (:REWRITE DEFAULT-LESS-THAN-1))
 (59 21 (:REWRITE CONSTANT-<-INTEGERP))
 (56 2
     (:REWRITE |(<= x (/ y)) with (< 0 y)|))
 (51 2 (:REWRITE |(< (/ x) y) with (< 0 x)|))
 (45 1 (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (42 1
     (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (31 13 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (30 22
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (30 22
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (27 21 (:REWRITE INTEGERP-<-CONSTANT))
 (26 26
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (26 21
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (25 21
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (24 2 (:REWRITE |(* y (* x z))|))
 (23 21
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (22 22 (:REWRITE THE-FLOOR-BELOW))
 (22 22 (:REWRITE THE-FLOOR-ABOVE))
 (22 14 (:REWRITE DEFAULT-EXPT-1))
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
 (21 21 (:REWRITE |(< (- x) (- y))|))
 (19 17 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (16 16 (:REWRITE |(* (- x) y)|))
 (14 14 (:REWRITE DEFAULT-EXPT-2))
 (14 14 (:REWRITE |(expt 1/c n)|))
 (14 14 (:REWRITE |(expt (- x) n)|))
 (9 9 (:REWRITE |(< y (+ (- c) x))|))
 (9 9 (:REWRITE |(< x (+ c/d y))|))
 (9 9 (:REWRITE |(< (+ c/d x) y)|))
 (9 9 (:REWRITE |(< (+ (- c) x) y)|))
 (8 8 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
 (8 8 (:TYPE-PRESCRIPTION ABS))
 (8 8
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (8 8
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (8 8
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (8 8
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (8 2 (:REWRITE |(* c (* d x))|))
 (5 5 (:REWRITE REDUCE-INTEGERP-+))
 (5 5 (:REWRITE INTEGERP-MINUS-X))
 (5 5 (:META META-INTEGERP-CORRECT))
 (4 4 (:TYPE-PRESCRIPTION RTL::R%))
 (4 4 (:TYPE-PRESCRIPTION RTL::NATP-R%))
 (4 4 (:REWRITE FOLD-CONSTS-IN-+))
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
 (4 4 (:LINEAR EXPT-<=-1-TWO))
 (4 4 (:LINEAR EXPT-<-1-TWO))
 (4 4 (:LINEAR EXPT-<-1-ONE))
 (3 3 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
 (2 2 (:REWRITE DEFAULT-MINUS))
 (2 1
    (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (2 1 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (1 1 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (1 1 (:REWRITE |(< 0 (/ x))|))
 (1 1 (:REWRITE |(< 0 (* x y))|)))
(RTL::SEL-UPPER-SQRT
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
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (5 5
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (5 5
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (5 5
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (4 4
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3E-EXPT))
 (4 4
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2E-EXPT))
 (4 4
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1E-EXPT)))
(RTL::SEL-LOWER-SQRT
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
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (5 5
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (5 5
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (5 5
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (4 4
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3E-EXPT))
 (4 4
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2E-EXPT))
 (4 4
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1E-EXPT)))
(RTL::REM-SQRT-BNDS-NEXT
 (6463 313 (:REWRITE DEFAULT-PLUS-2))
 (2756 238 (:REWRITE DEFAULT-TIMES-2))
 (2707 313 (:REWRITE DEFAULT-PLUS-1))
 (1591
  1591
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1591
      1591
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1591
     1591
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1591 1591
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1591 1591
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (1275 14
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (1199 238 (:REWRITE DEFAULT-TIMES-1))
 (1038 88 (:REWRITE DEFAULT-MINUS))
 (773 15 (:REWRITE DEFAULT-LESS-THAN-2))
 (615 15 (:REWRITE DEFAULT-LESS-THAN-1))
 (537 537
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (393 5 (:REWRITE SIMPLIFY-SUMS-<))
 (318 37 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (228 60 (:REWRITE DEFAULT-EXPT-1))
 (183 183
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (60 60 (:REWRITE DEFAULT-EXPT-2))
 (56 56 (:REWRITE |(expt 1/c n)|))
 (56 56 (:REWRITE |(expt (- x) n)|))
 (48 12
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (47 47 (:REWRITE FOLD-CONSTS-IN-+))
 (41 41 (:REWRITE |(* c (* d x))|))
 (15 15 (:REWRITE THE-FLOOR-BELOW))
 (15 15 (:REWRITE THE-FLOOR-ABOVE))
 (15 15
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (15 15
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (15 15 (:REWRITE |(< (/ x) (/ y))|))
 (14 14 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (14 14
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
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
 (14 14 (:REWRITE |(< (- x) c)|))
 (13 13 (:REWRITE |(< (+ c/d x) y)|))
 (13 13 (:REWRITE |(< (+ (- c) x) y)|))
 (13 13 (:REWRITE |(* (- x) y)|))
 (12 12
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (12 12
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (12 12
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (12 12 (:REWRITE ZP-OPEN))
 (12 12 (:REWRITE |(< y (+ (- c) x))|))
 (12 12 (:REWRITE |(< x (+ c/d y))|))
 (4 4 (:REWRITE |(* c (expt d n))|))
 (4 4
    (:REWRITE |(* (expt c m) (expt d n))|))
 (2 2
    (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
 (2 2 (:REWRITE ARITH-NORMALIZE-ADDENDS))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1 (:REWRITE REDUCE-INTEGERP-+))
 (1 1 (:REWRITE INTEGERP-MINUS-X))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (* x y) 0)|))
 (1 1 (:META META-INTEGERP-CORRECT)))
(RTL::R%-BOUND
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
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A)))
(RTL::A%+RHO%-1 (25 25 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                (25 25 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                (25 25 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                (22 22 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
                (22 22 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
                (22 22 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
                (9 6 (:REWRITE DEFAULT-TIMES-1))
                (8 6 (:REWRITE DEFAULT-TIMES-2))
                (5 1 (:REWRITE REMOVE-WEAK-INEQUALITIES))
                (4 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                (4 2
                   (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                (3 1
                   (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
                (3 1 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
                (3 1 (:REWRITE DEFAULT-LESS-THAN-1))
                (2 2
                   (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                (2 2
                   (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
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
                (1 1 (:REWRITE THE-FLOOR-BELOW))
                (1 1 (:REWRITE THE-FLOOR-ABOVE))
                (1 1
                   (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
                (1 1 (:REWRITE SIMPLIFY-SUMS-<))
                (1 1 (:REWRITE REMOVE-STRICT-INEQUALITIES))
                (1 1
                   (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
                (1 1
                   (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
                (1 1
                   (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
                (1 1 (:REWRITE INTEGERP-<-CONSTANT))
                (1 1 (:REWRITE DEFAULT-LESS-THAN-2))
                (1 1 (:REWRITE DEFAULT-DIVIDE))
                (1 1 (:REWRITE CONSTANT-<-INTEGERP))
                (1 1 (:REWRITE |(equal (+ (- c) x) y)|))
                (1 1
                   (:REWRITE |(< c (/ x)) positive c --- present in goal|))
                (1 1
                   (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
                (1 1
                   (:REWRITE |(< c (/ x)) negative c --- present in goal|))
                (1 1
                   (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
                (1 1 (:REWRITE |(< c (- x))|))
                (1 1
                   (:REWRITE |(< (/ x) c) positive c --- present in goal|))
                (1 1
                   (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
                (1 1
                   (:REWRITE |(< (/ x) c) negative c --- present in goal|))
                (1 1
                   (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
                (1 1 (:REWRITE |(< (/ x) (/ y))|))
                (1 1 (:REWRITE |(< (- x) c)|))
                (1 1 (:REWRITE |(< (- x) (- y))|)))
(RTL::A%+RHO%-2 (13 4 (:REWRITE DEFAULT-PLUS-2))
                (12 5 (:REWRITE DEFAULT-TIMES-2))
                (9 5 (:REWRITE DEFAULT-TIMES-1))
                (9 4 (:REWRITE DEFAULT-PLUS-1))
                (4 2 (:REWRITE DEFAULT-MINUS))
                (3 3
                   (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                (3 3
                   (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                (3 3 (:REWRITE NORMALIZE-ADDENDS))
                (1 1 (:REWRITE |(* x (- y))|))
                (1 1 (:REWRITE |(* (- x) y)|)))
(RTL::A%+RHO%-3)
(RTL::A%+RHO%-4 (104 14 (:REWRITE DEFAULT-PLUS-2))
                (84 84 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                (84 84 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                (84 84 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                (70 14 (:REWRITE DEFAULT-PLUS-1))
                (33 15 (:REWRITE DEFAULT-TIMES-2))
                (26 26 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
                (26 26 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
                (26 26 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
                (23 15 (:REWRITE DEFAULT-TIMES-1))
                (9 9
                   (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                (8 2 (:REWRITE DEFAULT-MINUS))
                (7 7
                   (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                (6 1 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
                (5 1 (:REWRITE REMOVE-WEAK-INEQUALITIES))
                (3 3
                   (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
                (3 3 (:REWRITE DEFAULT-DIVIDE))
                (3 1
                   (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
                (3 1 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
                (3 1 (:REWRITE DEFAULT-LESS-THAN-1))
                (2 2 (:REWRITE |(* c (* d x))|))
                (1 1 (:REWRITE THE-FLOOR-BELOW))
                (1 1 (:REWRITE THE-FLOOR-ABOVE))
                (1 1 (:REWRITE SIMPLIFY-SUMS-<))
                (1 1 (:REWRITE REMOVE-STRICT-INEQUALITIES))
                (1 1
                   (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
                (1 1
                   (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
                (1 1 (:REWRITE INTEGERP-<-CONSTANT))
                (1 1 (:REWRITE DEFAULT-LESS-THAN-2))
                (1 1 (:REWRITE CONSTANT-<-INTEGERP))
                (1 1
                   (:REWRITE |(< c (/ x)) positive c --- present in goal|))
                (1 1
                   (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
                (1 1
                   (:REWRITE |(< c (/ x)) negative c --- present in goal|))
                (1 1
                   (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
                (1 1 (:REWRITE |(< c (- x))|))
                (1 1
                   (:REWRITE |(< (/ x) c) positive c --- present in goal|))
                (1 1
                   (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
                (1 1
                   (:REWRITE |(< (/ x) c) negative c --- present in goal|))
                (1 1
                   (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
                (1 1 (:REWRITE |(< (/ x) (/ y))|))
                (1 1 (:REWRITE |(< (- x) c)|))
                (1 1 (:REWRITE |(< (- x) (- y))|))
                (1 1 (:REWRITE |(- (* c x))|))
                (1 1 (:REWRITE |(+ c (+ d x))|)))
(RTL::A%+RHO%)
(RTL::SQRT-CONTAINMENT-1
 (918 46 (:REWRITE DEFAULT-PLUS-2))
 (906 82 (:REWRITE DEFAULT-TIMES-2))
 (556 46 (:REWRITE DEFAULT-PLUS-1))
 (338 30 (:REWRITE DEFAULT-MINUS))
 (241
  241
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (241 241
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (241
     241
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (241 241
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (241 241
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (214 82 (:REWRITE DEFAULT-TIMES-1))
 (44 44
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (36 6 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (34 34
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (18 18 (:REWRITE |(* c (* d x))|))
 (14 6 (:REWRITE DEFAULT-EXPT-1))
 (6 6 (:REWRITE FOLD-CONSTS-IN-+))
 (6 6 (:REWRITE DEFAULT-EXPT-2))
 (6 6 (:REWRITE |(expt 1/c n)|))
 (6 6 (:REWRITE |(expt (- x) n)|))
 (6 6 (:REWRITE |(+ c (+ d x))|))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3E-EXPT))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2E-EXPT))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1E-EXPT))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (2 2 (:REWRITE |(+ (* c x) (* d x))|))
 (1 1 (:REWRITE THE-FLOOR-BELOW))
 (1 1 (:REWRITE THE-FLOOR-ABOVE))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1 (:REWRITE SIMPLIFY-SUMS-<))
 (1 1
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (1 1 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (1 1 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (1 1
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (1 1
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (1 1 (:REWRITE REDUCE-INTEGERP-+))
 (1 1 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (1 1 (:REWRITE INTEGERP-MINUS-X))
 (1 1 (:REWRITE INTEGERP-<-CONSTANT))
 (1 1 (:REWRITE DEFAULT-LESS-THAN-2))
 (1 1 (:REWRITE DEFAULT-LESS-THAN-1))
 (1 1 (:REWRITE CONSTANT-<-INTEGERP))
 (1 1
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (1 1
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (1 1
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (1 1
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (1 1 (:REWRITE |(< c (- x))|))
 (1 1
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (1 1
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (1 1
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (1 1
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (/ x) (/ y))|))
 (1 1 (:REWRITE |(< (- x) c)|))
 (1 1 (:REWRITE |(< (- x) (- y))|))
 (1 1 (:REWRITE |(< (* x y) 0)|))
 (1 1 (:META META-INTEGERP-CORRECT)))
(RTL::SQRT-CONTAINMENT-2)
(RTL::SQRT-CONTAINMENT
 (812 65 (:REWRITE DEFAULT-TIMES-2))
 (359 45 (:REWRITE DEFAULT-PLUS-2))
 (258 65 (:REWRITE DEFAULT-TIMES-1))
 (217 22
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (140
  140
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (140 140
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (140
     140
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (140 140
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (140 140
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (140 140
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (97 45 (:REWRITE DEFAULT-PLUS-1))
 (54 18 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (51 51
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (38 14 (:REWRITE DEFAULT-EXPT-1))
 (35 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (23 23
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (22 22
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (22 22
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (22 22
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (21 21 (:REWRITE |(* c (* d x))|))
 (14 14 (:REWRITE DEFAULT-EXPT-2))
 (14 14 (:REWRITE |(expt 1/c n)|))
 (14 14 (:REWRITE |(expt (- x) n)|))
 (14 8 (:REWRITE DEFAULT-MINUS))
 (6 6 (:REWRITE |(* c (expt d n))|))
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
 (4 4 (:REWRITE |(equal (+ (- c) x) y)|))
 (3 3 (:REWRITE |(* (- x) y)|))
 (1 1
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3E-EXPT))
 (1 1
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2E-EXPT))
 (1 1
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1E-EXPT))
 (1 1 (:REWRITE THE-FLOOR-BELOW))
 (1 1 (:REWRITE THE-FLOOR-ABOVE))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1 (:REWRITE SIMPLIFY-SUMS-<))
 (1 1
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (1 1 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (1 1 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (1 1
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (1 1
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (1 1 (:REWRITE REDUCE-INTEGERP-+))
 (1 1 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (1 1 (:REWRITE INTEGERP-MINUS-X))
 (1 1 (:REWRITE INTEGERP-<-CONSTANT))
 (1 1 (:REWRITE DEFAULT-LESS-THAN-2))
 (1 1 (:REWRITE DEFAULT-LESS-THAN-1))
 (1 1 (:REWRITE CONSTANT-<-INTEGERP))
 (1 1
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (1 1
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (1 1
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (1 1
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (1 1 (:REWRITE |(< c (- x))|))
 (1 1
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (1 1
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (1 1
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (1 1
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (/ x) (/ y))|))
 (1 1 (:REWRITE |(< (- x) c)|))
 (1 1 (:REWRITE |(< (- x) (- y))|))
 (1 1 (:REWRITE |(< (* x y) 0)|))
 (1 1 (:META META-INTEGERP-CORRECT)))
(RTL::MS4*8)
(RTL::MS4 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
          (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
          (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B)))
(RTL::I%)
(RTL::SELECT-DIGIT-S4)
(RTL::QUOT%-BNDS-INV)
(RTL::REM%-BNDS-INV)
(RTL::APPROX%)
(RTL::RATP-APPROX%)
(RTL::APPROX%-BOUNDS)
(RTL::APPROX%-INV (14 7
                      (:TYPE-PRESCRIPTION RTL::Q%-CONSTRAINT)))
(RTL::S4-INV)
(RTL::S4-HYP)
(RTL::REM%-BNDS-1
     (138 54 (:REWRITE SIMPLIFY-SUMS-<))
     (138 54
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (138 54 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (100 56 (:REWRITE DEFAULT-LESS-THAN-2))
     (100 56 (:REWRITE DEFAULT-LESS-THAN-1))
     (88 36 (:REWRITE DEFAULT-TIMES-2))
     (87 32
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (60 32 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (56 56 (:REWRITE THE-FLOOR-BELOW))
     (56 56 (:REWRITE THE-FLOOR-ABOVE))
     (54 54 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (54 54
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (54 54
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
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
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (54 54
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (54 54
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (54 54
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (54 54 (:REWRITE |(< (/ x) (/ y))|))
     (54 54 (:REWRITE |(< (- x) c)|))
     (54 54 (:REWRITE |(< (- x) (- y))|))
     (36 36 (:REWRITE DEFAULT-TIMES-1))
     (32 32
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (32 32
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (32 32
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (32 32 (:REWRITE |(equal c (/ x))|))
     (32 32 (:REWRITE |(equal c (- x))|))
     (32 32 (:REWRITE |(equal (/ x) c)|))
     (32 32 (:REWRITE |(equal (/ x) (/ y))|))
     (32 32 (:REWRITE |(equal (- x) c)|))
     (32 32 (:REWRITE |(equal (- x) (- y))|))
     (28 28
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (20 20
         (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
     (9 9 (:REWRITE ZP-OPEN))
     (9 9
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (9 9
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (9 9 (:REWRITE REDUCE-INTEGERP-+))
     (9 9 (:REWRITE INTEGERP-MINUS-X))
     (9 9 (:REWRITE |(< (/ x) 0)|))
     (9 9 (:REWRITE |(< (* x y) 0)|))
     (9 9 (:META META-INTEGERP-CORRECT))
     (8 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (7 7
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (7 7 (:REWRITE NORMALIZE-ADDENDS))
     (7 7 (:REWRITE DEFAULT-PLUS-2))
     (7 7 (:REWRITE DEFAULT-PLUS-1))
     (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A)))
(RTL::REM%-BNDS-2
     (172 2 (:REWRITE |(< (/ x) y) with (< 0 x)|))
     (121 7 (:REWRITE |(< x (+ c/d y))|))
     (65 5 (:REWRITE |(< y (+ (- c) x))|))
     (46 1 (:REWRITE |(< x (/ y)) with (< 0 y)|))
     (43 1
         (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (41 39 (:REWRITE DEFAULT-TIMES-2))
     (40 39 (:REWRITE DEFAULT-TIMES-1))
     (28 22 (:REWRITE DEFAULT-LESS-THAN-1))
     (28 20
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (28 20
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (27 16 (:REWRITE INTEGERP-<-CONSTANT))
     (26 26
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (25 16 (:REWRITE CONSTANT-<-INTEGERP))
     (22 22 (:REWRITE THE-FLOOR-BELOW))
     (22 22 (:REWRITE THE-FLOOR-ABOVE))
     (22 22 (:REWRITE DEFAULT-LESS-THAN-2))
     (22 16
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (22 16 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (20 16
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (17 17 (:REWRITE DEFAULT-PLUS-2))
     (17 17 (:REWRITE DEFAULT-PLUS-1))
     (16 16 (:REWRITE SIMPLIFY-SUMS-<))
     (16 16
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (16 16
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (16 16 (:REWRITE NORMALIZE-ADDENDS))
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
     (16 3
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (15 13 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (13 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (11 11
         (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
     (8 8 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
     (8 8 (:TYPE-PRESCRIPTION ABS))
     (8 8 (:REWRITE ARITH-NORMALIZE-ADDENDS))
     (8 1 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (4 4 (:REWRITE REDUCE-INTEGERP-+))
     (4 4 (:REWRITE INTEGERP-MINUS-X))
     (4 4 (:META META-INTEGERP-CORRECT))
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
        (:REWRITE |(<= x (/ y)) with (< y 0)|))
     (2 2 (:REWRITE |(< (/ x) y) with (< x 0)|))
     (2 1
        (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (2 1 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (1 1 (:REWRITE |(< (+ c/d x) y)|))
     (1 1 (:REWRITE |(< (+ (- c) x) y)|))
     (1 1 (:REWRITE |(+ 0 x)|)))
(RTL::REM%-BNDS-3 (89 89 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                  (89 89 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                  (89 89 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                  (28 13
                      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                  (13 13 (:REWRITE SIMPLIFY-SUMS-EQUAL))
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
                  (3 3
                     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RTL::REM%-BNDS-4 (214 63 (:REWRITE DEFAULT-PLUS-2))
                  (155 69 (:REWRITE DEFAULT-TIMES-2))
                  (97 97 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                  (97 97 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                  (97 97 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                  (84 69 (:REWRITE DEFAULT-TIMES-1))
                  (77 63 (:REWRITE DEFAULT-PLUS-1))
                  (47 47
                      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                  (46 46
                      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                  (46 46 (:REWRITE NORMALIZE-ADDENDS))
                  (45 1 (:REWRITE |(< x (/ y)) with (< 0 y)|))
                  (36 20
                      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                  (27 23
                      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                  (25 7
                      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
                  (25 7 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
                  (23 8 (:REWRITE DEFAULT-LESS-THAN-2))
                  (20 20 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                  (20 20
                      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
                  (20 20 (:REWRITE |(equal c (/ x))|))
                  (20 20 (:REWRITE |(equal c (- x))|))
                  (20 20 (:REWRITE |(equal (/ x) c)|))
                  (20 20 (:REWRITE |(equal (/ x) (/ y))|))
                  (20 20 (:REWRITE |(equal (- x) c)|))
                  (20 20 (:REWRITE |(equal (- x) (- y))|))
                  (16 8 (:REWRITE DEFAULT-LESS-THAN-1))
                  (13 7 (:REWRITE INTEGERP-<-CONSTANT))
                  (12 12 (:REWRITE |(equal (+ (- c) x) y)|))
                  (12 8
                      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
                  (12 8
                      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
                  (12 6 (:REWRITE REMOVE-WEAK-INEQUALITIES))
                  (8 8 (:REWRITE THE-FLOOR-BELOW))
                  (8 8 (:REWRITE THE-FLOOR-ABOVE))
                  (8 2
                     (:REWRITE |(<= (/ x) y) with (< x 0)|))
                  (7 7 (:REWRITE SIMPLIFY-SUMS-<))
                  (7 7 (:REWRITE REMOVE-STRICT-INEQUALITIES))
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
                  (6 6 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
                  (6 6 (:TYPE-PRESCRIPTION ABS))
                  (3 3 (:REWRITE |(< y (+ (- c) x))|))
                  (3 3 (:REWRITE |(< x (+ c/d y))|))
                  (2 1 (:REWRITE |(< x (/ y)) with (< y 0)|))
                  (1 1 (:REWRITE REDUCE-INTEGERP-+))
                  (1 1 (:REWRITE INTEGERP-MINUS-X))
                  (1 1 (:REWRITE |(equal (* x y) 0)|))
                  (1 1 (:REWRITE |(< (+ c/d x) y)|))
                  (1 1 (:REWRITE |(< (+ (- c) x) y)|))
                  (1 1 (:META META-INTEGERP-CORRECT)))
(RTL::REM%-BNDS-5 (27 27 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                  (27 27 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                  (27 27 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                  (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
                  (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
                  (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
                  (17 5 (:REWRITE DEFAULT-TIMES-2))
                  (14 5 (:REWRITE DEFAULT-PLUS-2))
                  (6 5 (:REWRITE DEFAULT-TIMES-1))
                  (6 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
                  (5 5 (:REWRITE DEFAULT-PLUS-1))
                  (5 2
                     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                  (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                  (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                  (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                  (3 3
                     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                  (3 3
                     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                  (3 3 (:REWRITE NORMALIZE-ADDENDS))
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
                  (2 2 (:REWRITE |(equal (- x) (- y))|)))
(RTL::REM%-BNDS-6 (84 28 (:REWRITE DEFAULT-TIMES-2))
                  (72 28 (:REWRITE DEFAULT-PLUS-2))
                  (44 44 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                  (44 44 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                  (44 44 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                  (35 35 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
                  (35 35 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
                  (35 35 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
                  (32 28 (:REWRITE DEFAULT-TIMES-1))
                  (29 15
                      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                  (28 28 (:REWRITE DEFAULT-PLUS-1))
                  (24 12 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
                  (20 20
                      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                  (20 20
                      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                  (20 20 (:REWRITE NORMALIZE-ADDENDS))
                  (15 15 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                  (15 15
                      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                  (15 15
                      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
                  (15 15
                      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
                  (15 15 (:REWRITE |(equal c (/ x))|))
                  (15 15 (:REWRITE |(equal c (- x))|))
                  (15 15 (:REWRITE |(equal (/ x) c)|))
                  (15 15 (:REWRITE |(equal (/ x) (/ y))|))
                  (15 15 (:REWRITE |(equal (- x) c)|))
                  (15 15 (:REWRITE |(equal (- x) (- y))|))
                  (12 12 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                  (12 12 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                  (12 12 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                  (7 7 (:REWRITE |(equal (+ (- c) x) y)|))
                  (2 2
                     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RTL::Q%-VALS
     (24 24 (:TYPE-PRESCRIPTION ZP))
     (24 12
         (:TYPE-PRESCRIPTION RTL::Q%-CONSTRAINT))
     (19 19
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (19 19
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (19 19 (:REWRITE |(equal c (/ x))|))
     (19 19 (:REWRITE |(equal c (- x))|))
     (19 19 (:REWRITE |(equal (/ x) c)|))
     (19 19 (:REWRITE |(equal (/ x) (/ y))|))
     (19 19 (:REWRITE |(equal (- x) (- y))|))
     (16 16 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (16 16
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (16 16
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (14 12 (:REWRITE DEFAULT-LESS-THAN-2))
     (13 13 (:REWRITE DEFAULT-MINUS))
     (13 12 (:REWRITE DEFAULT-LESS-THAN-1))
     (12 12 (:REWRITE THE-FLOOR-BELOW))
     (12 12 (:REWRITE THE-FLOOR-ABOVE))
     (11 11
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (11 11
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (11 11
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (11 11
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (11 11
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (11 11
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (11 11
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (11 11
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (11 11
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (11 11
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (11 11 (:REWRITE |(< (/ x) (/ y))|))
     (11 11 (:REWRITE |(< (- x) (- y))|))
     (9 8
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (9 8 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (8 8 (:REWRITE SIMPLIFY-SUMS-<))
     (8 8 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (8 8 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (8 8 (:REWRITE INTEGERP-<-CONSTANT))
     (8 8 (:REWRITE CONSTANT-<-INTEGERP))
     (4 4 (:REWRITE |(< (/ x) 0)|))
     (4 4 (:REWRITE |(< (* x y) 0)|))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (1 1 (:REWRITE |(< 0 (/ x))|))
     (1 1 (:REWRITE |(< 0 (* x y))|)))
(RTL::REM%-BNDS-7
     (3399 2116 (:REWRITE DEFAULT-PLUS-2))
     (2880 100 (:REWRITE |(< (+ c/d x) y)|))
     (2809 2116 (:REWRITE DEFAULT-PLUS-1))
     (2205 25
           (:REWRITE |(< x (/ y)) with (< 0 y)|))
     (2130 25
           (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (1505 815 (:REWRITE DEFAULT-TIMES-2))
     (1239 1239
           (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (1239 1239 (:REWRITE NORMALIZE-ADDENDS))
     (967 691
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (840 815 (:REWRITE DEFAULT-TIMES-1))
     (770 60 (:REWRITE |(< (+ (- c) x) y)|))
     (710 710
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (691 691 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (691 691
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (691 691
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (691 691
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (691 691 (:REWRITE |(equal c (/ x))|))
     (691 691 (:REWRITE |(equal c (- x))|))
     (691 691 (:REWRITE |(equal (/ x) c)|))
     (691 691 (:REWRITE |(equal (/ x) (/ y))|))
     (691 691 (:REWRITE |(equal (- x) c)|))
     (691 691 (:REWRITE |(equal (- x) (- y))|))
     (520 40 (:REWRITE |(* y (* x z))|))
     (475 475 (:REWRITE |(equal (+ (- c) x) y)|))
     (340 100 (:REWRITE INTEGERP-<-CONSTANT))
     (325 25 (:REWRITE |(* y x)|))
     (295 160 (:REWRITE DEFAULT-LESS-THAN-1))
     (200 40 (:REWRITE |(* c (* d x))|))
     (180 120
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (180 120
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (175 100
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (175 100
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (160 160 (:REWRITE THE-FLOOR-BELOW))
     (160 160 (:REWRITE THE-FLOOR-ABOVE))
     (160 160 (:REWRITE DEFAULT-LESS-THAN-2))
     (130 30
          (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (100 100 (:REWRITE SIMPLIFY-SUMS-<))
     (100 100
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (100 100 (:REWRITE CONSTANT-<-INTEGERP))
     (100 100
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (100 100
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (100 100
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (100 100
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (100 100 (:REWRITE |(< c (- x))|))
     (100 100
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (100 100
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (100 100
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (100 100
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (100 100 (:REWRITE |(< (/ x) (/ y))|))
     (100 100 (:REWRITE |(< (- x) c)|))
     (100 100 (:REWRITE |(< (- x) (- y))|))
     (75 75 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (72 72
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (60 60 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
     (60 60 (:TYPE-PRESCRIPTION ABS))
     (50 25
         (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (50 25
         (:REWRITE |(< x (/ y)) with (< y 0)|))
     (25 25 (:REWRITE REDUCE-INTEGERP-+))
     (25 25 (:REWRITE INTEGERP-MINUS-X))
     (25 25 (:META META-INTEGERP-CORRECT))
     (20 20 (:REWRITE |(< y (+ (- c) x))|))
     (20 20 (:REWRITE |(< x (+ c/d y))|)))
(RTL::REM%-BNDS-8
     (1436 58 (:REWRITE |(< (+ c/d x) y)|))
     (1073 447 (:REWRITE DEFAULT-TIMES-2))
     (870 369 (:REWRITE DEFAULT-PLUS-2))
     (864 10
          (:REWRITE |(< x (/ y)) with (< 0 y)|))
     (840 10
          (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (785 44 (:REWRITE |(< x (+ c/d y))|))
     (613 10
          (:REWRITE |(< (/ x) y) with (< 0 x)|))
     (606 38 (:REWRITE |(< (+ (- c) x) y)|))
     (573 369 (:REWRITE DEFAULT-PLUS-1))
     (492 447 (:REWRITE DEFAULT-TIMES-1))
     (472 36 (:REWRITE |(* y (* x z))|))
     (460 34 (:REWRITE |(< y (+ (- c) x))|))
     (363 363
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (363 363
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (363 363
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (316 10
          (:REWRITE |(< x (/ y)) with (< y 0)|))
     (300 10
          (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (285 285
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (276 276
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (276 276
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (276 276
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (271 70 (:REWRITE CONSTANT-<-INTEGERP))
     (264 10
          (:REWRITE |(<= x (/ y)) with (< y 0)|))
     (255 70 (:REWRITE INTEGERP-<-CONSTANT))
     (252 10
          (:REWRITE |(< (/ x) y) with (< x 0)|))
     (242 242
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (226 130 (:REWRITE DEFAULT-LESS-THAN-2))
     (216 130 (:REWRITE DEFAULT-LESS-THAN-1))
     (191 28
          (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (172 70
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (165 20 (:REWRITE INTEGERP-MINUS-X))
     (156 100
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (156 100
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (135 70
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (130 130 (:REWRITE THE-FLOOR-BELOW))
     (130 130 (:REWRITE THE-FLOOR-ABOVE))
     (70 70 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (70 70
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (70 70
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (70 70
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (70 70
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (70 70 (:REWRITE |(equal c (/ x))|))
     (70 70 (:REWRITE |(equal c (- x))|))
     (70 70 (:REWRITE |(equal (/ x) c)|))
     (70 70 (:REWRITE |(equal (/ x) (/ y))|))
     (70 70 (:REWRITE |(equal (- x) c)|))
     (70 70 (:REWRITE |(equal (- x) (- y))|))
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
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (70 70
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (70 70
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (70 70
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (70 70 (:REWRITE |(< (/ x) (/ y))|))
     (70 70 (:REWRITE |(< (- x) c)|))
     (70 70 (:REWRITE |(< (- x) (- y))|))
     (60 4 (:REWRITE |(- (+ x y))|))
     (58 58 (:REWRITE SIMPLIFY-SUMS-<))
     (56 56 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
     (56 56 (:TYPE-PRESCRIPTION ABS))
     (52 52 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (44 44 (:REWRITE |(* (- x) y)|))
     (36 12 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (24 8 (:REWRITE DEFAULT-MINUS))
     (20 4 (:REWRITE |(- (* c x))|))
     (16 16 (:REWRITE REDUCE-INTEGERP-+))
     (16 16 (:META META-INTEGERP-CORRECT))
     (14 14 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
     (14 14 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
     (14 14 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (7 7 (:REWRITE |(equal (+ (- c) x) y)|))
     (4 4 (:REWRITE |(* x (- y))|)))
(RTL::REM%-BNDS-9
     (4179 170 (:REWRITE |(< (+ c/d x) y)|))
     (3181 1347 (:REWRITE DEFAULT-TIMES-2))
     (2574 1101 (:REWRITE DEFAULT-PLUS-2))
     (2496 29
           (:REWRITE |(< x (/ y)) with (< 0 y)|))
     (2427 29
           (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (2071 134 (:REWRITE |(< x (+ c/d y))|))
     (2020 29
           (:REWRITE |(< (/ x) y) with (< 0 x)|))
     (1816 112 (:REWRITE |(< (+ (- c) x) y)|))
     (1713 1101 (:REWRITE DEFAULT-PLUS-1))
     (1670 108 (:REWRITE |(< y (+ (- c) x))|))
     (1598 122 (:REWRITE |(* y (* x z))|))
     (1480 1347 (:REWRITE DEFAULT-TIMES-1))
     (1226 218 (:REWRITE CONSTANT-<-INTEGERP))
     (1169 218 (:REWRITE INTEGERP-<-CONSTANT))
     (1061 132
           (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (946 946
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (946 946
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (946 946
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (946 29
          (:REWRITE |(< x (/ y)) with (< y 0)|))
     (898 29
          (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (893 112 (:REWRITE INTEGERP-MINUS-X))
     (855 855
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (850 850
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (850 850
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (850 850
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (786 29
          (:REWRITE |(<= x (/ y)) with (< y 0)|))
     (750 29
          (:REWRITE |(< (/ x) y) with (< x 0)|))
     (729 729
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (686 396 (:REWRITE DEFAULT-LESS-THAN-2))
     (650 396 (:REWRITE DEFAULT-LESS-THAN-1))
     (540 218
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (496 312
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (496 312
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (399 208
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (396 396 (:REWRITE THE-FLOOR-BELOW))
     (396 396 (:REWRITE THE-FLOOR-ABOVE))
     (326 22 (:REWRITE |(- (+ x y))|))
     (250 8 (:REWRITE EVEN-AND-ODD-ALTERNATE))
     (218 218
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (218 218
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (218 218
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (218 218
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (218 218
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (218 218 (:REWRITE |(< c (- x))|))
     (218 218
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (218 218
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (218 218
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (218 218
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (218 218 (:REWRITE |(< (/ x) (/ y))|))
     (218 218 (:REWRITE |(< (- x) c)|))
     (218 218 (:REWRITE |(< (- x) (- y))|))
     (208 208 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (208 208
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (208 208
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (208 208
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (208 208 (:REWRITE |(equal c (/ x))|))
     (208 208 (:REWRITE |(equal c (- x))|))
     (208 208 (:REWRITE |(equal (/ x) c)|))
     (208 208 (:REWRITE |(equal (/ x) (/ y))|))
     (208 208 (:REWRITE |(equal (- x) c)|))
     (208 208 (:REWRITE |(equal (- x) (- y))|))
     (184 184 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
     (184 184 (:TYPE-PRESCRIPTION ABS))
     (182 182 (:REWRITE SIMPLIFY-SUMS-<))
     (162 162 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (132 132 (:REWRITE |(* (- x) y)|))
     (128 44 (:REWRITE DEFAULT-MINUS))
     (110 22 (:REWRITE |(- (* c x))|))
     (108 36 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (90 90 (:REWRITE REDUCE-INTEGERP-+))
     (90 90 (:META META-INTEGERP-CORRECT))
     (20 20
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (19 19 (:REWRITE |(equal (+ (- c) x) y)|))
     (12 12 (:REWRITE |(* x (- y))|))
     (9 9 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
     (9 9 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
     (9 9 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E)))
(RTL::REM%-BNDS-10
 (4141 634 (:REWRITE DEFAULT-PLUS-2))
 (1963 634 (:REWRITE DEFAULT-PLUS-1))
 (1826
  1826
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1826
      1826
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1826
     1826
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1826 1826
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1610 179
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (1610 179
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (1178 118
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (1109 140 (:REWRITE DEFAULT-LESS-THAN-2))
 (837 140 (:REWRITE DEFAULT-LESS-THAN-1))
 (665 137 (:REWRITE DEFAULT-TIMES-2))
 (664 169 (:REWRITE DEFAULT-MINUS))
 (495 15 (:REWRITE ZP-OPEN))
 (304 81 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (267 267
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (185 137 (:REWRITE DEFAULT-TIMES-1))
 (179 179
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (179 179
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (178 127 (:REWRITE |(< (- x) (- y))|))
 (142 142 (:TYPE-PRESCRIPTION ZP))
 (142 71
      (:TYPE-PRESCRIPTION RTL::Q%-CONSTRAINT))
 (140 140 (:REWRITE THE-FLOOR-BELOW))
 (140 140 (:REWRITE THE-FLOOR-ABOVE))
 (131 127 (:REWRITE |(< c (- x))|))
 (127 127
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (127 127
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (127 127
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (127 127
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (127 127
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (127 127
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (127 127
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (127 127
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (127 127
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (127 127
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (127 127 (:REWRITE |(< (/ x) (/ y))|))
 (123 123
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (123 123 (:REWRITE INTEGERP-<-CONSTANT))
 (123 123 (:REWRITE CONSTANT-<-INTEGERP))
 (79 79
     (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
 (77 77 (:REWRITE |(< (+ c/d x) y)|))
 (77 77 (:REWRITE |(< (+ (- c) x) y)|))
 (75 15 (:REWRITE |(* y x)|))
 (74 74 (:REWRITE |arith (expt x c)|))
 (67 67 (:REWRITE |(< y (+ (- c) x))|))
 (67 67 (:REWRITE |(< x (+ c/d y))|))
 (61 61 (:REWRITE DEFAULT-EXPT-2))
 (61 61 (:REWRITE DEFAULT-EXPT-1))
 (61 61 (:REWRITE |(expt 1/c n)|))
 (61 61 (:REWRITE |(expt (- x) n)|))
 (50 50 (:REWRITE FOLD-CONSTS-IN-+))
 (42 21
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (37 37 (:REWRITE |arith (expt 1/c n)|))
 (37 37 (:REWRITE |arith (* (- x) y)|))
 (30 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (22 22 (:REWRITE |(* (- x) y)|))
 (21 21 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (21 21
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (21 21
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (21 21
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (21 21 (:REWRITE |(equal c (/ x))|))
 (21 21 (:REWRITE |(equal c (- x))|))
 (21 21 (:REWRITE |(equal (/ x) c)|))
 (21 21 (:REWRITE |(equal (/ x) (/ y))|))
 (21 21 (:REWRITE |(equal (- x) c)|))
 (21 21 (:REWRITE |(equal (- x) (- y))|))
 (20 20 (:REWRITE |(< (/ x) 0)|))
 (20 20 (:REWRITE |(< (* x y) 0)|))
 (20 5 (:REWRITE RATIONALP-X))
 (19 19 (:REWRITE |(< 0 (/ x))|))
 (19 19 (:REWRITE |(< 0 (* x y))|))
 (15 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (15 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (15 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (15 15
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (15 15
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (14 14 (:REWRITE |arith (+ c (+ d x))|))
 (10 10 (:REWRITE REDUCE-INTEGERP-+))
 (10 10 (:REWRITE INTEGERP-MINUS-X))
 (10 10 (:META META-INTEGERP-CORRECT))
 (5 5 (:REWRITE REDUCE-RATIONALP-+))
 (5 5 (:REWRITE REDUCE-RATIONALP-*))
 (5 5 (:REWRITE RATIONALP-MINUS-X))
 (5 5 (:META META-RATIONALP-CORRECT))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RTL::REM%-BNDS-11
 (252 27
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (252 27
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (229
  229
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (229 229
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (229
     229
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (229 229
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (221 28 (:REWRITE DEFAULT-TIMES-2))
 (168 22 (:REWRITE DEFAULT-PLUS-2))
 (110 11 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (88 22 (:REWRITE DEFAULT-PLUS-1))
 (74 12 (:REWRITE DEFAULT-MINUS))
 (60 60 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (60 60 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (60 60 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (57 28 (:REWRITE DEFAULT-TIMES-1))
 (27 27
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (27 27
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (16 16
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (16 16 (:REWRITE NORMALIZE-ADDENDS))
 (11 11 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (11 11 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (11 11 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (6 6 (:REWRITE DEFAULT-EXPT-2))
 (6 6 (:REWRITE DEFAULT-EXPT-1))
 (6 6 (:REWRITE |(expt 1/c n)|))
 (6 6 (:REWRITE |(expt (- x) n)|))
 (5 5 (:REWRITE |(* (- x) y)|))
 (5 2
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (3 3 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (2 2 (:REWRITE THE-FLOOR-BELOW))
 (2 2 (:REWRITE THE-FLOOR-ABOVE))
 (2 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (2 2 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (2 2
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (2 2
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (2 2
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (2 2
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (2 2 (:REWRITE INTEGERP-<-CONSTANT))
 (2 2
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (2 2 (:REWRITE DEFAULT-LESS-THAN-2))
 (2 2 (:REWRITE DEFAULT-LESS-THAN-1))
 (2 2 (:REWRITE CONSTANT-<-INTEGERP))
 (2 2 (:REWRITE |(equal c (/ x))|))
 (2 2 (:REWRITE |(equal c (- x))|))
 (2 2 (:REWRITE |(equal (/ x) c)|))
 (2 2 (:REWRITE |(equal (/ x) (/ y))|))
 (2 2 (:REWRITE |(equal (- x) c)|))
 (2 2 (:REWRITE |(equal (- x) (- y))|))
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
 (1 1 (:REWRITE SIMPLIFY-SUMS-<))
 (1 1
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (1 1 (:REWRITE REDUCE-INTEGERP-+))
 (1 1 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (1 1 (:REWRITE INTEGERP-MINUS-X))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (* x y) 0)|))
 (1 1 (:META META-INTEGERP-CORRECT)))
(RTL::REM%-BNDS-12
 (714 38
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (222 26 (:REWRITE CONSTANT-<-INTEGERP))
 (211 3 (:LINEAR EXPT-X->=-X))
 (211 3 (:LINEAR EXPT-X->-X))
 (134 3 (:LINEAR EXPT->=-1-ONE))
 (134 3 (:LINEAR EXPT-<=-1-TWO))
 (132 12 (:REWRITE |(* y (* x z))|))
 (131 3 (:LINEAR EXPT->-1-ONE))
 (131 3 (:LINEAR EXPT-<-1-TWO))
 (85 37 (:REWRITE DEFAULT-TIMES-2))
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
 (38 38 (:REWRITE THE-FLOOR-BELOW))
 (38 38 (:REWRITE THE-FLOOR-ABOVE))
 (38 38 (:REWRITE DEFAULT-LESS-THAN-2))
 (38 38 (:REWRITE DEFAULT-LESS-THAN-1))
 (37 37 (:REWRITE DEFAULT-TIMES-1))
 (26 26
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
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
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (26 26
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (26 26
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (26 26
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (26 26 (:REWRITE |(< (/ x) (/ y))|))
 (26 26 (:REWRITE |(< (- x) c)|))
 (26 26 (:REWRITE |(< (- x) (- y))|))
 (22 22 (:REWRITE SIMPLIFY-SUMS-<))
 (22 22
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (22 22
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (22 22 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (22 22 (:REWRITE INTEGERP-<-CONSTANT))
 (14 14 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (13 13
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (12 12 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (12 12 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (12 12 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (12 12 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (12 12 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
 (12 12 (:TYPE-PRESCRIPTION ABS))
 (12 12 (:REWRITE |(* a (/ a) b)|))
 (10 10 (:REWRITE |(< 0 (* x y))|))
 (10 10 (:REWRITE |(< (* x y) 0)|))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (6 6 (:REWRITE |(< 0 (/ x))|))
 (6 6 (:REWRITE |(< (/ x) 0)|))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (6 6
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (4 4 (:REWRITE |(< (/ x) y) with (< x 0)|))
 (4 4 (:REWRITE |(< (/ x) y) with (< 0 x)|))
 (4 4
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
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
 (1 1 (:REWRITE REDUCE-INTEGERP-+))
 (1 1 (:REWRITE INTEGERP-MINUS-X))
 (1 1 (:META META-INTEGERP-CORRECT)))
(RTL::REM%-BNDS-13
 (821 37 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (292 4 (:LINEAR EXPT->=-1-ONE))
 (288 4 (:LINEAR EXPT-X->=-X))
 (288 4 (:LINEAR EXPT-X->-X))
 (284 4 (:LINEAR EXPT->-1-ONE))
 (201 109 (:REWRITE DEFAULT-PLUS-1))
 (199
  199
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (199 199
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (199
     199
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (199 199
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (190 109 (:REWRITE DEFAULT-PLUS-2))
 (58 13 (:REWRITE DEFAULT-TIMES-2))
 (39 21 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (38 38 (:REWRITE THE-FLOOR-BELOW))
 (38 38 (:REWRITE THE-FLOOR-ABOVE))
 (38 38
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (38 38
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (38 38
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (38 38 (:REWRITE INTEGERP-<-CONSTANT))
 (38 38 (:REWRITE DEFAULT-LESS-THAN-2))
 (38 38 (:REWRITE DEFAULT-LESS-THAN-1))
 (38 38 (:REWRITE CONSTANT-<-INTEGERP))
 (38 38
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (38 38
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (38 38
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (38 38
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (38 38 (:REWRITE |(< c (- x))|))
 (38 38
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (38 38
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (38 38
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (38 38
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (38 38 (:REWRITE |(< (/ x) (/ y))|))
 (38 38 (:REWRITE |(< (- x) c)|))
 (38 38 (:REWRITE |(< (- x) (- y))|))
 (37 37
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (21 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (19 19 (:REWRITE SIMPLIFY-SUMS-<))
 (18 18
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (18 18 (:REWRITE |(+ x (- x))|))
 (18 9 (:REWRITE DEFAULT-MINUS))
 (14 14 (:REWRITE |(< (+ c/d x) y)|))
 (14 14 (:REWRITE |(< (+ (- c) x) y)|))
 (14 13 (:REWRITE DEFAULT-TIMES-1))
 (12 12 (:REWRITE DEFAULT-EXPT-2))
 (12 12 (:REWRITE DEFAULT-EXPT-1))
 (12 12 (:REWRITE |(expt 1/c n)|))
 (12 12 (:REWRITE |(expt (- x) n)|))
 (12 12 (:REWRITE |(< y (+ (- c) x))|))
 (12 12 (:REWRITE |(< x (+ c/d y))|))
 (8 8
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (8 8
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (8 8
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (8 8
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (7 7 (:REWRITE |(< (/ x) 0)|))
 (7 7 (:REWRITE |(< (* x y) 0)|))
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
 (4 4 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (4 4 (:LINEAR EXPT-LINEAR-UPPER-<))
 (4 4 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (4 4 (:LINEAR EXPT-LINEAR-LOWER-<))
 (4 4 (:LINEAR EXPT->=-1-TWO))
 (4 4 (:LINEAR EXPT->-1-TWO))
 (4 4 (:LINEAR EXPT-<=-1-ONE))
 (4 4 (:LINEAR EXPT-<-1-ONE))
 (3 3 (:REWRITE |(* (- x) y)|))
 (1 1 (:REWRITE REDUCE-INTEGERP-+))
 (1 1 (:REWRITE INTEGERP-MINUS-X))
 (1 1 (:REWRITE |(equal (expt 2 n) c)|))
 (1 1 (:REWRITE |(equal (+ (- c) x) y)|))
 (1 1 (:META META-INTEGERP-CORRECT)))
(RTL::REM%-BNDS-14)
(RTL::REM%-BNDS-15
 (95 95 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (95 95 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (95 95 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (95
  95
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (95 95
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (95 95
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (95 95
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (95 95
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE)))
(RTL::REM%-BNDS-16
 (1617 7 (:REWRITE |(< (/ x) y) with (< 0 x)|))
 (1547 7
       (:REWRITE |(<= x (/ y)) with (< 0 y)|))
 (882 91 (:REWRITE DEFAULT-TIMES-2))
 (691
  691
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (691 691
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (691
     691
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (691 691
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (691 691
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (624 96 (:REWRITE DEFAULT-PLUS-2))
 (611 96 (:REWRITE DEFAULT-PLUS-1))
 (449 37 (:REWRITE CONSTANT-<-INTEGERP))
 (436 33
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (366 37 (:REWRITE DEFAULT-LESS-THAN-2))
 (349 349
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (349 349
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (349 349
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (273 91 (:REWRITE DEFAULT-TIMES-1))
 (191 29 (:REWRITE DEFAULT-MINUS))
 (175 175
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (175 175
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (175 175
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (140 14 (:REWRITE |(* a (/ a) b)|))
 (128 37 (:REWRITE DEFAULT-LESS-THAN-1))
 (126 7
      (:REWRITE |(<= x (/ y)) with (< y 0)|))
 (126 7 (:REWRITE |(< (/ x) y) with (< x 0)|))
 (100 8 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (59 59
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (49 49
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (37 37 (:REWRITE THE-FLOOR-BELOW))
 (37 37 (:REWRITE THE-FLOOR-ABOVE))
 (37 37
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (37 37
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (37 37
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (37 37 (:REWRITE INTEGERP-<-CONSTANT))
 (37 37
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (37 37
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (37 37
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (37 37
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (37 37 (:REWRITE |(< c (- x))|))
 (37 37
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (37 37
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (37 37
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (37 37
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (37 37 (:REWRITE |(< (/ x) (/ y))|))
 (37 37 (:REWRITE |(< (- x) c)|))
 (37 37 (:REWRITE |(< (- x) (- y))|))
 (26 26 (:REWRITE SIMPLIFY-SUMS-<))
 (21 21 (:REWRITE |(< y (+ (- c) x))|))
 (21 21 (:REWRITE |(< x (+ c/d y))|))
 (15 6
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (14 14
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (14 14
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (14 14
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (14 14
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (10 10 (:REWRITE REDUCE-INTEGERP-+))
 (10 10 (:REWRITE INTEGERP-MINUS-X))
 (10 10 (:META META-INTEGERP-CORRECT))
 (9 9 (:REWRITE |(< (+ c/d x) y)|))
 (9 9 (:REWRITE |(< (+ (- c) x) y)|))
 (7 7 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (7 7 (:REWRITE DEFAULT-EXPT-2))
 (7 7 (:REWRITE DEFAULT-EXPT-1))
 (7 7 (:REWRITE |(expt 1/c n)|))
 (7 7 (:REWRITE |(expt (- x) n)|))
 (7 7 (:REWRITE |(* (- x) y)|))
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
 (7 7 (:LINEAR EXPT-<=-1-TWO))
 (7 7 (:LINEAR EXPT-<=-1-ONE))
 (7 7 (:LINEAR EXPT-<-1-TWO))
 (7 7 (:LINEAR EXPT-<-1-ONE))
 (6 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
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
 (3 3 (:REWRITE |(< (/ x) 0)|))
 (3 3 (:REWRITE |(< (* x y) 0)|)))
(RTL::REM%-BNDS-17
 (4665 2
       (:REWRITE |(<= x (/ y)) with (< 0 y)|))
 (4657 2 (:REWRITE |(< (/ x) y) with (< 0 x)|))
 (3856 400
       (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
 (800
  800
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (800 800
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (800
     800
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (800 800
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (800 800
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (707 124 (:REWRITE DEFAULT-PLUS-2))
 (672 96
      (:REWRITE ARITH-BUBBLE-DOWN-*-MATCH-1))
 (576 96
      (:REWRITE |arith (* (expt x m) (expt x n))|))
 (521 137 (:REWRITE ARITH-NORMALIZE-ADDENDS))
 (352 124 (:REWRITE DEFAULT-PLUS-1))
 (350 350 (:REWRITE |arith (expt x c)|))
 (337 67 (:REWRITE DEFAULT-TIMES-2))
 (333 2 (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (330 330 (:REWRITE |arith (expt 1/c n)|))
 (327 2
      (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (288 96
      (:REWRITE ARITH-BUBBLE-DOWN-+-MATCH-1))
 (284 32 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (284 32 (:LINEAR EXPT-<=-1-TWO))
 (280 32 (:LINEAR EXPT-X->-X))
 (280 32 (:LINEAR EXPT->-1-ONE))
 (280 32 (:LINEAR EXPT-<-1-TWO))
 (248 34
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (221 37 (:REWRITE CONSTANT-<-INTEGERP))
 (208 32 (:LINEAR EXPT-X->=-X))
 (208 32 (:LINEAR EXPT->=-1-ONE))
 (203 38 (:REWRITE DEFAULT-LESS-THAN-2))
 (192 96
      (:REWRITE |arith (+ (* c x) (* d x))|))
 (159 159
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (159 159
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (159 159
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (122 122 (:REWRITE |arith (* (- x) y)|))
 (110 67 (:REWRITE DEFAULT-TIMES-1))
 (110 38 (:REWRITE DEFAULT-LESS-THAN-1))
 (109 17 (:REWRITE SIMPLIFY-SUMS-<))
 (96 96 (:REWRITE |arith (* 0 x)|))
 (90 12 (:META META-INTEGERP-CORRECT))
 (64 64
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (64 64
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (64 64
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (64 64
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (61 20 (:REWRITE DEFAULT-MINUS))
 (59 37 (:REWRITE INTEGERP-<-CONSTANT))
 (58 17 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (42 37 (:REWRITE |(< (- x) c)|))
 (42 37 (:REWRITE |(< (- x) (- y))|))
 (40 4 (:REWRITE |(* a (/ a) b)|))
 (39 39
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (39 39
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (39 37 (:REWRITE |(< c (- x))|))
 (38 38 (:REWRITE THE-FLOOR-BELOW))
 (38 38 (:REWRITE THE-FLOOR-ABOVE))
 (37 37
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (37 37
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (37 37
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (37 37
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (37 37
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (37 37
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (37 37
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (37 37
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (37 37
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (37 37
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (37 37
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (37 37 (:REWRITE |(< (/ x) (/ y))|))
 (32 32 (:LINEAR EXPT-LINEAR-UPPER-<))
 (32 32 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (32 32 (:LINEAR EXPT-LINEAR-LOWER-<))
 (32 32 (:LINEAR EXPT->=-1-TWO))
 (32 32 (:LINEAR EXPT->-1-TWO))
 (32 32 (:LINEAR EXPT-<=-1-ONE))
 (32 32 (:LINEAR EXPT-<-1-ONE))
 (32 2
     (:REWRITE |(<= x (/ y)) with (< y 0)|))
 (32 2 (:REWRITE |(< (/ x) y) with (< x 0)|))
 (20 20 (:REWRITE |(< y (+ (- c) x))|))
 (20 20 (:REWRITE |(< x (+ c/d y))|))
 (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (18 18 (:REWRITE |(+ c (+ d x))|))
 (17 17 (:REWRITE |(< (+ c/d x) y)|))
 (17 17 (:REWRITE |(< (+ (- c) x) y)|))
 (16 12 (:REWRITE INTEGERP-MINUS-X))
 (14 2 (:REWRITE |(integerp (- x))|))
 (12 12 (:REWRITE REDUCE-INTEGERP-+))
 (10 4
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (9 9 (:REWRITE |(* (- x) y)|))
 (6 6 (:REWRITE FOLD-CONSTS-IN-+))
 (6 2
    (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (6 2 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (5 5 (:REWRITE |(< (/ x) 0)|))
 (5 5 (:REWRITE |(< (* x y) 0)|))
 (4 4 (:REWRITE |arith (+ c (+ d x))|))
 (4 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (4 4
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (4 4
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (4 4 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (4 4
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (4 4 (:REWRITE |(equal c (/ x))|))
 (4 4 (:REWRITE |(equal c (- x))|))
 (4 4 (:REWRITE |(equal (/ x) c)|))
 (4 4 (:REWRITE |(equal (/ x) (/ y))|))
 (4 4 (:REWRITE |(equal (- x) c)|))
 (4 4 (:REWRITE |(equal (- x) (- y))|))
 (1 1 (:REWRITE DEFAULT-EXPT-2))
 (1 1 (:REWRITE DEFAULT-EXPT-1))
 (1 1 (:REWRITE |(expt 1/c n)|))
 (1 1 (:REWRITE |(expt (- x) n)|)))
(RTL::REM%-BNDS-18
 (7775 949 (:REWRITE DEFAULT-PLUS-2))
 (3365 949 (:REWRITE DEFAULT-PLUS-1))
 (2074
  2074
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (2074
      2074
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (2074
     2074
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (2074 2074
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (2003 165 (:REWRITE DEFAULT-LESS-THAN-2))
 (2001 136
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (1732 1732
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (1732 1732
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (1732 1732
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (1610 179
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (1610 179
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (1466 270 (:REWRITE DEFAULT-MINUS))
 (1192 165 (:REWRITE DEFAULT-LESS-THAN-1))
 (856 240 (:REWRITE DEFAULT-TIMES-2))
 (495 15 (:REWRITE ZP-OPEN))
 (436 436
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (412 99 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (303 240 (:REWRITE DEFAULT-TIMES-1))
 (203 152 (:REWRITE |(< (- x) (- y))|))
 (179 179
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (179 179
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (165 165 (:REWRITE THE-FLOOR-BELOW))
 (165 165 (:REWRITE THE-FLOOR-ABOVE))
 (163 152 (:REWRITE |(< c (- x))|))
 (152 152
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (152 152
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (152 152
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (152 152
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (152 152
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (152 152
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (152 152
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (152 152
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (152 152
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (152 152
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (152 152 (:REWRITE |(< (/ x) (/ y))|))
 (142 142 (:TYPE-PRESCRIPTION ZP))
 (142 71
      (:TYPE-PRESCRIPTION RTL::Q%-CONSTRAINT))
 (141 141
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (141 141 (:REWRITE INTEGERP-<-CONSTANT))
 (141 141 (:REWRITE CONSTANT-<-INTEGERP))
 (141 141
      (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
 (139 139 (:REWRITE FOLD-CONSTS-IN-+))
 (111 111 (:REWRITE |(< y (+ (- c) x))|))
 (111 111 (:REWRITE |(< x (+ c/d y))|))
 (95 95 (:REWRITE |(< (+ c/d x) y)|))
 (95 95 (:REWRITE |(< (+ (- c) x) y)|))
 (74 74 (:REWRITE |arith (expt x c)|))
 (61 61 (:REWRITE DEFAULT-EXPT-2))
 (61 61 (:REWRITE DEFAULT-EXPT-1))
 (61 61 (:REWRITE |(expt 1/c n)|))
 (61 61 (:REWRITE |(expt (- x) n)|))
 (42 21
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (39 39 (:REWRITE |arith (+ c (+ d x))|))
 (37 37 (:REWRITE |arith (expt 1/c n)|))
 (37 37 (:REWRITE |arith (* (- x) y)|))
 (37 37 (:REWRITE |(* (- x) y)|))
 (26 26 (:REWRITE |(< 0 (/ x))|))
 (26 26 (:REWRITE |(< 0 (* x y))|))
 (21 21 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (21 21
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (21 21
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (21 21
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (21 21 (:REWRITE |(equal c (/ x))|))
 (21 21 (:REWRITE |(equal c (- x))|))
 (21 21 (:REWRITE |(equal (/ x) c)|))
 (21 21 (:REWRITE |(equal (/ x) (/ y))|))
 (21 21 (:REWRITE |(equal (- x) c)|))
 (21 21 (:REWRITE |(equal (- x) (- y))|))
 (20 20 (:REWRITE |(< (/ x) 0)|))
 (20 20 (:REWRITE |(< (* x y) 0)|))
 (20 5 (:REWRITE RATIONALP-X))
 (15 15
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (15 15
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (10 10 (:REWRITE REDUCE-INTEGERP-+))
 (10 10 (:REWRITE INTEGERP-MINUS-X))
 (10 10 (:META META-INTEGERP-CORRECT))
 (5 5 (:REWRITE REDUCE-RATIONALP-+))
 (5 5 (:REWRITE REDUCE-RATIONALP-*))
 (5 5 (:REWRITE RATIONALP-MINUS-X))
 (5 5 (:META META-RATIONALP-CORRECT))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RTL::REM%-BNDS-19
 (252 27
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (252 27
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (229
  229
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (229 229
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (229
     229
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (229 229
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (221 28 (:REWRITE DEFAULT-TIMES-2))
 (168 22 (:REWRITE DEFAULT-PLUS-2))
 (110 11 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (88 22 (:REWRITE DEFAULT-PLUS-1))
 (74 12 (:REWRITE DEFAULT-MINUS))
 (60 60 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (60 60 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (60 60 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (57 28 (:REWRITE DEFAULT-TIMES-1))
 (27 27
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (27 27
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (16 16
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (16 16 (:REWRITE NORMALIZE-ADDENDS))
 (11 11 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (11 11 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (11 11 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (6 6 (:REWRITE DEFAULT-EXPT-2))
 (6 6 (:REWRITE DEFAULT-EXPT-1))
 (6 6 (:REWRITE |(expt 1/c n)|))
 (6 6 (:REWRITE |(expt (- x) n)|))
 (5 5 (:REWRITE |(* (- x) y)|))
 (5 2
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (3 3 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (2 2 (:REWRITE THE-FLOOR-BELOW))
 (2 2 (:REWRITE THE-FLOOR-ABOVE))
 (2 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (2 2 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (2 2
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (2 2
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (2 2
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (2 2
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (2 2 (:REWRITE INTEGERP-<-CONSTANT))
 (2 2
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (2 2 (:REWRITE DEFAULT-LESS-THAN-2))
 (2 2 (:REWRITE DEFAULT-LESS-THAN-1))
 (2 2 (:REWRITE CONSTANT-<-INTEGERP))
 (2 2 (:REWRITE |(equal c (/ x))|))
 (2 2 (:REWRITE |(equal c (- x))|))
 (2 2 (:REWRITE |(equal (/ x) c)|))
 (2 2 (:REWRITE |(equal (/ x) (/ y))|))
 (2 2 (:REWRITE |(equal (- x) c)|))
 (2 2 (:REWRITE |(equal (- x) (- y))|))
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
 (1 1 (:REWRITE SIMPLIFY-SUMS-<))
 (1 1
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (1 1 (:REWRITE REDUCE-INTEGERP-+))
 (1 1 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (1 1 (:REWRITE INTEGERP-MINUS-X))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (* x y) 0)|))
 (1 1 (:META META-INTEGERP-CORRECT)))
(RTL::REM%-BNDS-20
 (772 35 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (219 3 (:LINEAR EXPT->=-1-ONE))
 (216 3 (:LINEAR EXPT-X->=-X))
 (216 3 (:LINEAR EXPT-X->-X))
 (213 3 (:LINEAR EXPT->-1-ONE))
 (213 3 (:LINEAR EXPT-<-1-TWO))
 (195 104 (:REWRITE DEFAULT-PLUS-1))
 (188
  188
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (188 188
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (188
     188
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (188 188
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (188 188
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (185 104 (:REWRITE DEFAULT-PLUS-2))
 (58 13 (:REWRITE DEFAULT-TIMES-2))
 (38 20 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (36 36 (:REWRITE THE-FLOOR-BELOW))
 (36 36 (:REWRITE THE-FLOOR-ABOVE))
 (36 36
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (36 36
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (36 36
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (36 36 (:REWRITE INTEGERP-<-CONSTANT))
 (36 36 (:REWRITE DEFAULT-LESS-THAN-2))
 (36 36 (:REWRITE DEFAULT-LESS-THAN-1))
 (36 36 (:REWRITE CONSTANT-<-INTEGERP))
 (36 36
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (36 36
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (36 36
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (36 36
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (36 36 (:REWRITE |(< c (- x))|))
 (36 36
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (36 36
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (36 36
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (36 36
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (36 36 (:REWRITE |(< (/ x) (/ y))|))
 (36 36 (:REWRITE |(< (- x) c)|))
 (36 36 (:REWRITE |(< (- x) (- y))|))
 (35 35
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (21 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (18 18 (:REWRITE SIMPLIFY-SUMS-<))
 (18 9 (:REWRITE DEFAULT-MINUS))
 (17 17 (:REWRITE |(+ x (- x))|))
 (16 16
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (14 13 (:REWRITE DEFAULT-TIMES-1))
 (12 12 (:REWRITE |(< (+ c/d x) y)|))
 (12 12 (:REWRITE |(< (+ (- c) x) y)|))
 (11 11 (:REWRITE |(< y (+ (- c) x))|))
 (11 11 (:REWRITE |(< x (+ c/d y))|))
 (7 7 (:REWRITE DEFAULT-EXPT-2))
 (7 7 (:REWRITE DEFAULT-EXPT-1))
 (7 7 (:REWRITE |(expt 1/c n)|))
 (7 7 (:REWRITE |(expt (- x) n)|))
 (7 7 (:REWRITE |(< (/ x) 0)|))
 (7 7 (:REWRITE |(< (* x y) 0)|))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (6 6
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (5 5 (:REWRITE |(< 0 (/ x))|))
 (5 5 (:REWRITE |(< 0 (* x y))|))
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
 (3 3 (:REWRITE |(* (- x) y)|))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<))
 (3 3 (:LINEAR EXPT->=-1-TWO))
 (3 3 (:LINEAR EXPT->-1-TWO))
 (3 3 (:LINEAR EXPT-<=-1-ONE))
 (3 3 (:LINEAR EXPT-<-1-ONE))
 (1 1 (:REWRITE REDUCE-INTEGERP-+))
 (1 1 (:REWRITE INTEGERP-MINUS-X))
 (1 1 (:REWRITE |(equal (expt 2 n) c)|))
 (1 1 (:REWRITE |(equal (+ (- c) x) y)|))
 (1 1 (:META META-INTEGERP-CORRECT)))
(RTL::REM%-BNDS-21)
(RTL::REM%-BNDS-22
 (95 95 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (95 95 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (95 95 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (95
  95
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (95 95
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (95 95
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (95 95
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (95 95
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE)))
(RTL::REM%-BNDS-23
 (1617 7 (:REWRITE |(< (/ x) y) with (< 0 x)|))
 (1547 7
       (:REWRITE |(<= x (/ y)) with (< 0 y)|))
 (882 91 (:REWRITE DEFAULT-TIMES-2))
 (691
  691
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (691 691
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (691
     691
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (691 691
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (691 691
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (624 96 (:REWRITE DEFAULT-PLUS-2))
 (611 96 (:REWRITE DEFAULT-PLUS-1))
 (449 37 (:REWRITE CONSTANT-<-INTEGERP))
 (436 33
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (366 37 (:REWRITE DEFAULT-LESS-THAN-2))
 (349 349
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (349 349
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (349 349
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (273 91 (:REWRITE DEFAULT-TIMES-1))
 (191 29 (:REWRITE DEFAULT-MINUS))
 (175 175
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (175 175
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (175 175
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (140 14 (:REWRITE |(* a (/ a) b)|))
 (128 37 (:REWRITE DEFAULT-LESS-THAN-1))
 (126 7
      (:REWRITE |(<= x (/ y)) with (< y 0)|))
 (126 7 (:REWRITE |(< (/ x) y) with (< x 0)|))
 (100 8 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (59 59
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (49 49
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (37 37 (:REWRITE THE-FLOOR-BELOW))
 (37 37 (:REWRITE THE-FLOOR-ABOVE))
 (37 37
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (37 37
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (37 37
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (37 37 (:REWRITE INTEGERP-<-CONSTANT))
 (37 37
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (37 37
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (37 37
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (37 37
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (37 37 (:REWRITE |(< c (- x))|))
 (37 37
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (37 37
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (37 37
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (37 37
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (37 37 (:REWRITE |(< (/ x) (/ y))|))
 (37 37 (:REWRITE |(< (- x) c)|))
 (37 37 (:REWRITE |(< (- x) (- y))|))
 (26 26 (:REWRITE SIMPLIFY-SUMS-<))
 (21 21 (:REWRITE |(< y (+ (- c) x))|))
 (21 21 (:REWRITE |(< x (+ c/d y))|))
 (15 6
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (14 14
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (14 14
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (14 14
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (14 14
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (10 10 (:REWRITE REDUCE-INTEGERP-+))
 (10 10 (:REWRITE INTEGERP-MINUS-X))
 (10 10 (:META META-INTEGERP-CORRECT))
 (9 9 (:REWRITE |(< (+ c/d x) y)|))
 (9 9 (:REWRITE |(< (+ (- c) x) y)|))
 (7 7 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (7 7 (:REWRITE DEFAULT-EXPT-2))
 (7 7 (:REWRITE DEFAULT-EXPT-1))
 (7 7 (:REWRITE |(expt 1/c n)|))
 (7 7 (:REWRITE |(expt (- x) n)|))
 (7 7 (:REWRITE |(* (- x) y)|))
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
 (7 7 (:LINEAR EXPT-<=-1-TWO))
 (7 7 (:LINEAR EXPT-<=-1-ONE))
 (7 7 (:LINEAR EXPT-<-1-TWO))
 (7 7 (:LINEAR EXPT-<-1-ONE))
 (6 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
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
 (3 3 (:REWRITE |(< (/ x) 0)|))
 (3 3 (:REWRITE |(< (* x y) 0)|)))
(RTL::REM%-BNDS-24
 (4665 2
       (:REWRITE |(<= x (/ y)) with (< 0 y)|))
 (4657 2 (:REWRITE |(< (/ x) y) with (< 0 x)|))
 (3872 416
       (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
 (804
  804
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (804 804
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (804
     804
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (804 804
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (804 804
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (804 172 (:REWRITE DEFAULT-PLUS-2))
 (672 96
      (:REWRITE ARITH-BUBBLE-DOWN-*-MATCH-1))
 (666 4 (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (654 4
      (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (576 96
      (:REWRITE |arith (* (expt x m) (expt x n))|))
 (533 149 (:REWRITE ARITH-NORMALIZE-ADDENDS))
 (441 172 (:REWRITE DEFAULT-PLUS-1))
 (391 93 (:REWRITE DEFAULT-TIMES-2))
 (350 350 (:REWRITE |arith (expt x c)|))
 (330 330 (:REWRITE |arith (expt 1/c n)|))
 (292 50
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (288 96
      (:REWRITE ARITH-BUBBLE-DOWN-+-MATCH-1))
 (284 32 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (284 32 (:LINEAR EXPT-<=-1-TWO))
 (280 32 (:LINEAR EXPT-X->-X))
 (280 32 (:LINEAR EXPT->-1-ONE))
 (280 32 (:LINEAR EXPT-<-1-TWO))
 (273 53 (:REWRITE CONSTANT-<-INTEGERP))
 (227 55 (:REWRITE DEFAULT-LESS-THAN-2))
 (208 32 (:LINEAR EXPT-X->=-X))
 (208 32 (:LINEAR EXPT->=-1-ONE))
 (192 96
      (:REWRITE |arith (+ (* c x) (* d x))|))
 (159 159
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (159 159
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (159 159
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (158 55 (:REWRITE DEFAULT-LESS-THAN-1))
 (140 93 (:REWRITE DEFAULT-TIMES-1))
 (132 26 (:REWRITE SIMPLIFY-SUMS-<))
 (126 126 (:REWRITE |arith (* (- x) y)|))
 (111 15 (:META META-INTEGERP-CORRECT))
 (97 53 (:REWRITE INTEGERP-<-CONSTANT))
 (96 96 (:REWRITE |arith (* 0 x)|))
 (78 28 (:REWRITE DEFAULT-MINUS))
 (72 24 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (64 64
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (64 64
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (64 64
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (64 64
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (61 53 (:REWRITE |(< (- x) c)|))
 (61 53 (:REWRITE |(< (- x) (- y))|))
 (55 55 (:REWRITE THE-FLOOR-BELOW))
 (55 55 (:REWRITE THE-FLOOR-ABOVE))
 (55 55
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (55 53 (:REWRITE |(< c (- x))|))
 (53 53
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (53 53
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (53 53
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (53 53
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (53 53
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (53 53
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (53 53
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (53 53
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (53 53
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (53 53
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (53 53
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (53 53 (:REWRITE |(< (/ x) (/ y))|))
 (51 51
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (40 4 (:REWRITE |(* a (/ a) b)|))
 (32 32 (:LINEAR EXPT-LINEAR-UPPER-<))
 (32 32 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (32 32 (:LINEAR EXPT-LINEAR-LOWER-<))
 (32 32 (:LINEAR EXPT->=-1-TWO))
 (32 32 (:LINEAR EXPT->-1-TWO))
 (32 32 (:LINEAR EXPT-<=-1-ONE))
 (32 32 (:LINEAR EXPT-<-1-ONE))
 (32 2
     (:REWRITE |(<= x (/ y)) with (< y 0)|))
 (32 2 (:REWRITE |(< (/ x) y) with (< x 0)|))
 (26 26 (:REWRITE |(< y (+ (- c) x))|))
 (26 26 (:REWRITE |(< x (+ c/d y))|))
 (24 24 (:REWRITE |(< (+ c/d x) y)|))
 (24 24 (:REWRITE |(< (+ (- c) x) y)|))
 (22 22 (:REWRITE |(+ c (+ d x))|))
 (21 15 (:REWRITE INTEGERP-MINUS-X))
 (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (15 15 (:REWRITE REDUCE-INTEGERP-+))
 (15 6
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (14 2 (:REWRITE |(integerp (- x))|))
 (13 13 (:REWRITE |(* (- x) y)|))
 (12 4
     (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (12 4 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (7 7 (:REWRITE |(< (/ x) 0)|))
 (7 7 (:REWRITE |(< (* x y) 0)|))
 (6 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (6 6
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (6 6
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (6 6 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (6 6 (:REWRITE FOLD-CONSTS-IN-+))
 (6 6
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (6 6 (:REWRITE |(equal c (/ x))|))
 (6 6 (:REWRITE |(equal c (- x))|))
 (6 6 (:REWRITE |(equal (/ x) c)|))
 (6 6 (:REWRITE |(equal (/ x) (/ y))|))
 (6 6 (:REWRITE |(equal (- x) c)|))
 (6 6 (:REWRITE |(equal (- x) (- y))|))
 (4 4 (:REWRITE |arith (+ c (+ d x))|))
 (1 1 (:REWRITE DEFAULT-EXPT-2))
 (1 1 (:REWRITE DEFAULT-EXPT-1))
 (1 1 (:REWRITE |(expt 1/c n)|))
 (1 1 (:REWRITE |(expt (- x) n)|)))
(RTL::REM%-BNDS-25 (628 76
                        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
                   (505 2 (:REWRITE |(not (equal x (/ y)))|))
                   (468 3 (:REWRITE |(equal x (/ y))|))
                   (207 22 (:REWRITE DEFAULT-PLUS-2))
                   (196 4 (:REWRITE |(* x (+ y z))|))
                   (159 159
                        (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                   (159 159
                        (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                   (159 159
                        (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                   (142 72
                        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                   (106 2 (:REWRITE |(+ y (+ x z))|))
                   (100 26 (:REWRITE DEFAULT-TIMES-2))
                   (87 11 (:REWRITE |(+ c (+ d x))|))
                   (76 76
                       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                   (72 72 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                   (72 72
                       (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
                   (72 72 (:REWRITE |(equal c (/ x))|))
                   (72 72 (:REWRITE |(equal c (- x))|))
                   (72 72 (:REWRITE |(equal (/ x) c)|))
                   (72 72 (:REWRITE |(equal (/ x) (/ y))|))
                   (72 72 (:REWRITE |(equal (- x) c)|))
                   (72 72 (:REWRITE |(equal (- x) (- y))|))
                   (52 22 (:REWRITE DEFAULT-PLUS-1))
                   (52 4 (:REWRITE |(* y (* x z))|))
                   (48 26 (:REWRITE DEFAULT-TIMES-1))
                   (42 2 (:REWRITE |(equal x (- (/ y)))|))
                   (30 2 (:REWRITE |(+ y x)|))
                   (22 2 (:REWRITE |(+ 0 x)|))
                   (21 1
                       (:REWRITE |(not (equal x (- (/ y))))|))
                   (20 4 (:REWRITE |(* c (* d x))|))
                   (14 14
                       (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                   (12 12
                       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
                   (11 11
                       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                   (11 11 (:REWRITE NORMALIZE-ADDENDS))
                   (7 7 (:REWRITE FOLD-CONSTS-IN-+))
                   (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                   (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                   (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                   (3 3 (:REWRITE |(equal (+ (- c) x) y)|)))
(RTL::REM%-BNDS-26
     (696 72 (:REWRITE ACL2-NUMBERP-X))
     (604 118 (:REWRITE |(< c (- x))|))
     (479 12
          (:REWRITE |(< x (/ y)) with (< y 0)|))
     (368 195 (:REWRITE DEFAULT-LESS-THAN-1))
     (312 72 (:REWRITE RATIONALP-X))
     (273 12
          (:REWRITE |(< x (/ y)) with (< 0 y)|))
     (268 106 (:REWRITE INTEGERP-<-CONSTANT))
     (260 48
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (256 12
          (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (219 195 (:REWRITE DEFAULT-LESS-THAN-2))
     (206 106
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (206 106
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (203 121
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (200 141 (:REWRITE DEFAULT-TIMES-2))
     (195 195 (:REWRITE THE-FLOOR-BELOW))
     (195 195 (:REWRITE THE-FLOOR-ABOVE))
     (118 118
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (118 118
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (118 118
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (118 118
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (118 118
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (118 118
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (118 118
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (118 118
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (118 118 (:REWRITE |(< (/ x) (/ y))|))
     (118 118 (:REWRITE |(< (- x) (- y))|))
     (110 106 (:REWRITE CONSTANT-<-INTEGERP))
     (106 106 (:REWRITE SIMPLIFY-SUMS-<))
     (106 106
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (106 106 (:REWRITE |(< (- x) c)|))
     (101 101 (:REWRITE REDUCE-INTEGERP-+))
     (101 101 (:REWRITE INTEGERP-MINUS-X))
     (101 101 (:META META-INTEGERP-CORRECT))
     (94 94 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (75 14 (:REWRITE |(* y x)|))
     (72 72 (:REWRITE REDUCE-RATIONALP-+))
     (72 72 (:REWRITE REDUCE-RATIONALP-*))
     (72 72 (:REWRITE RATIONALP-MINUS-X))
     (72 72 (:META META-RATIONALP-CORRECT))
     (60 12 (:REWRITE |(- (* c x))|))
     (60 2 (:REWRITE |(equal x (/ y))|))
     (52 48
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (49 49
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (48 48 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (48 48
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (48 48
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (48 48 (:REWRITE |(equal c (/ x))|))
     (48 48 (:REWRITE |(equal c (- x))|))
     (48 48 (:REWRITE |(equal (/ x) c)|))
     (48 48 (:REWRITE |(equal (/ x) (/ y))|))
     (48 48 (:REWRITE |(equal (- x) c)|))
     (48 48 (:REWRITE |(equal (- x) (- y))|))
     (40 40
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (40 40
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (40 40 (:REWRITE |(< (/ x) 0)|))
     (40 40 (:REWRITE |(< (* x y) 0)|))
     (40 2 (:REWRITE |(not (equal x (/ y)))|))
     (24 12 (:REWRITE DEFAULT-MINUS))
     (19 19 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (19 19 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (19 19 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (12 12 (:REWRITE |(* (- x) y)|))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (6 6 (:REWRITE |(* x (- y))|))
     (4 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A)))
(RTL::REM%-BNDS-27
     (62 2 (:REWRITE |(equal x (/ y))|))
     (46 1 (:REWRITE |(< x (/ y)) with (< 0 y)|))
     (44 2 (:REWRITE |(not (equal x (/ y)))|))
     (43 1
         (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (23 11
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (18 4 (:REWRITE INTEGERP-<-CONSTANT))
     (16 12 (:REWRITE DEFAULT-TIMES-2))
     (15 12 (:REWRITE DEFAULT-TIMES-1))
     (15 11
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (15 3 (:REWRITE |(* y x)|))
     (11 11 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (11 11
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (11 11
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (11 11 (:REWRITE |(equal c (/ x))|))
     (11 11 (:REWRITE |(equal c (- x))|))
     (11 11 (:REWRITE |(equal (/ x) c)|))
     (11 11 (:REWRITE |(equal (/ x) (/ y))|))
     (11 11 (:REWRITE |(equal (- x) c)|))
     (11 11 (:REWRITE |(equal (- x) (- y))|))
     (8 8
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (8 4
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (8 4
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (8 1 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (7 4
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (7 4 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (7 4 (:REWRITE DEFAULT-LESS-THAN-1))
     (6 6 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
     (6 6 (:TYPE-PRESCRIPTION ABS))
     (5 5 (:REWRITE DEFAULT-PLUS-2))
     (5 5 (:REWRITE DEFAULT-PLUS-1))
     (5 5
        (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
     (4 4 (:REWRITE THE-FLOOR-BELOW))
     (4 4 (:REWRITE THE-FLOOR-ABOVE))
     (4 4 (:REWRITE SIMPLIFY-SUMS-<))
     (4 4 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (4 4 (:REWRITE DEFAULT-LESS-THAN-2))
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
     (3 3
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (3 3 (:REWRITE NORMALIZE-ADDENDS))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (2 2 (:REWRITE REDUCE-INTEGERP-+))
     (2 2 (:REWRITE INTEGERP-MINUS-X))
     (2 2 (:META META-INTEGERP-CORRECT))
     (2 1
        (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (2 1 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (1 1 (:REWRITE ARITH-NORMALIZE-ADDENDS))
     (1 1 (:REWRITE |(< (+ c/d x) y)|))
     (1 1 (:REWRITE |(< (+ (- c) x) y)|))
     (1 1 (:REWRITE |(+ 0 x)|)))
(RTL::REM%-BNDS-28
     (93 12 (:REWRITE |(< c (- x))|))
     (80 2 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (76 2
         (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (47 2 (:REWRITE |(< x (/ y)) with (< 0 y)|))
     (44 2
         (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (38 10 (:REWRITE INTEGERP-<-CONSTANT))
     (26 12
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (26 12
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (19 12 (:REWRITE DEFAULT-LESS-THAN-1))
     (18 10
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (18 10 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (16 10 (:REWRITE CONSTANT-<-INTEGERP))
     (16 9 (:REWRITE DEFAULT-TIMES-2))
     (15 12 (:REWRITE DEFAULT-LESS-THAN-2))
     (15 3
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (14 14 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
     (14 14 (:TYPE-PRESCRIPTION ABS))
     (12 12 (:REWRITE THE-FLOOR-BELOW))
     (12 12 (:REWRITE THE-FLOOR-ABOVE))
     (12 12
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (12 12
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (12 12
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (12 12
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
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
     (11 9 (:REWRITE DEFAULT-TIMES-1))
     (11 2 (:REWRITE |(* y x)|))
     (10 10 (:REWRITE SIMPLIFY-SUMS-<))
     (10 10
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (10 10 (:REWRITE |(< (- x) c)|))
     (10 2 (:REWRITE |(- (* c x))|))
     (8 8 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (7 7
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (6 6 (:REWRITE REDUCE-INTEGERP-+))
     (6 6 (:REWRITE INTEGERP-MINUS-X))
     (6 6 (:META META-INTEGERP-CORRECT))
     (4 2 (:REWRITE DEFAULT-MINUS))
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
     (2 2 (:REWRITE |(* (- x) y)|))
     (1 1 (:REWRITE |(* x (- y))|)))
(RTL::REM%-BNDS-29
     (62 2 (:REWRITE |(equal x (/ y))|))
     (48 1 (:REWRITE |(< x (/ y)) with (< 0 y)|))
     (45 1
         (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (44 2 (:REWRITE |(not (equal x (/ y)))|))
     (25 12
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (21 12 (:REWRITE DEFAULT-TIMES-2))
     (18 4 (:REWRITE CONSTANT-<-INTEGERP))
     (16 12
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (15 12 (:REWRITE DEFAULT-TIMES-1))
     (15 3 (:REWRITE |(* y x)|))
     (12 12 (:REWRITE SIMPLIFY-SUMS-EQUAL))
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
     (12 2 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (10 4 (:REWRITE INTEGERP-<-CONSTANT))
     (9 5 (:REWRITE DEFAULT-PLUS-2))
     (8 8
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (8 4
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (8 4
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (8 4
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (8 4 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (7 4 (:REWRITE DEFAULT-LESS-THAN-1))
     (6 6 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
     (6 6 (:TYPE-PRESCRIPTION ABS))
     (6 5 (:REWRITE DEFAULT-PLUS-1))
     (5 5
        (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
     (5 4 (:REWRITE DEFAULT-LESS-THAN-2))
     (4 4 (:REWRITE THE-FLOOR-BELOW))
     (4 4 (:REWRITE THE-FLOOR-ABOVE))
     (4 4 (:REWRITE SIMPLIFY-SUMS-<))
     (4 4 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (4 4
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (4 4 (:REWRITE NORMALIZE-ADDENDS))
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
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (2 2 (:REWRITE REDUCE-INTEGERP-+))
     (2 2 (:REWRITE INTEGERP-MINUS-X))
     (2 2 (:META META-INTEGERP-CORRECT))
     (2 1
        (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (2 1 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (1 1 (:REWRITE ARITH-NORMALIZE-ADDENDS))
     (1 1 (:REWRITE |(< y (+ (- c) x))|))
     (1 1 (:REWRITE |(< x (+ c/d y))|)))
(RTL::REM%-BNDS-30
     (544 6
          (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (426 14 (:REWRITE |(< (+ (- c) x) y)|))
     (217 1
          (:REWRITE |(<= x (/ y)) with (< y 0)|))
     (213 84 (:REWRITE DEFAULT-TIMES-2))
     (185 1 (:REWRITE |(< (/ x) y) with (< x 0)|))
     (173 71 (:REWRITE DEFAULT-PLUS-2))
     (131 131
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (131 131
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (131 131
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (127 71 (:REWRITE DEFAULT-PLUS-1))
     (120 4 (:REWRITE |(equal x (/ y))|))
     (108 84 (:REWRITE DEFAULT-TIMES-1))
     (105 43 (:REWRITE DEFAULT-LESS-THAN-1))
     (94 48
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (80 4 (:REWRITE |(not (equal x (/ y)))|))
     (73 35 (:REWRITE CONSTANT-<-INTEGERP))
     (73 18 (:REWRITE DEFAULT-MINUS))
     (72 30
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (67 43 (:REWRITE DEFAULT-LESS-THAN-2))
     (59 35 (:REWRITE INTEGERP-<-CONSTANT))
     (58 42
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (58 42
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (56 48
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (51 51
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (48 48 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (48 48
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (48 48
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (48 48 (:REWRITE |(equal c (/ x))|))
     (48 48 (:REWRITE |(equal c (- x))|))
     (48 48 (:REWRITE |(equal (/ x) c)|))
     (48 48 (:REWRITE |(equal (/ x) (/ y))|))
     (48 48 (:REWRITE |(equal (- x) c)|))
     (48 48 (:REWRITE |(equal (- x) (- y))|))
     (43 43 (:REWRITE THE-FLOOR-BELOW))
     (43 43 (:REWRITE THE-FLOOR-ABOVE))
     (38 23 (:REWRITE SIMPLIFY-SUMS-<))
     (37 37
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (37 37
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (37 37
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (37 37
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (37 37 (:REWRITE |(< c (- x))|))
     (37 37
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (37 37
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (37 37
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (37 37
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (37 37 (:REWRITE |(< (/ x) (/ y))|))
     (37 37 (:REWRITE |(< (- x) (- y))|))
     (36 4 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
     (35 35
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (31 31
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (27 11 (:META META-INTEGERP-CORRECT))
     (24 5 (:REWRITE |(+ (* c x) (* d x))|))
     (21 21 (:REWRITE |(* (- x) y)|))
     (20 6
         (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (20 6 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (14 14 (:REWRITE |(< (+ c/d x) y)|))
     (14 14 (:REWRITE |(+ c (+ d x))|))
     (11 11 (:REWRITE REDUCE-INTEGERP-+))
     (11 11 (:REWRITE INTEGERP-MINUS-X))
     (11 7 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (10 10 (:REWRITE FOLD-CONSTS-IN-+))
     (9 9 (:REWRITE |(< y (+ (- c) x))|))
     (9 9 (:REWRITE |(< x (+ c/d y))|))
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (6 1
        (:REWRITE |(<= x (/ y)) with (< 0 y)|))
     (6 1 (:REWRITE |(< (/ x) y) with (< 0 x)|))
     (5 5 (:REWRITE |(< (/ x) 0)|))
     (5 5 (:REWRITE |(< (* x y) 0)|))
     (5 5 (:REWRITE |(* 0 x)|))
     (5 1 (:REWRITE |(integerp (- x))|))
     (1 1 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (1 1 (:REWRITE |(< 0 (/ x))|))
     (1 1 (:REWRITE |(< 0 (* x y))|)))
(RTL::QMIN (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
           (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
           (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
           (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B)))
(RTL::QMAX (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
           (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
           (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
           (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B)))
(RTL::REM%-BNDS-31
     (2519 139 (:REWRITE |(< (+ c/d x) y)|))
     (1244 27
           (:REWRITE |(<= x (/ y)) with (< 0 y)|))
     (1224 754 (:REWRITE DEFAULT-TIMES-2))
     (1144 471 (:REWRITE INTEGERP-<-CONSTANT))
     (1136 27
           (:REWRITE |(< (/ x) y) with (< 0 x)|))
     (852 569 (:REWRITE DEFAULT-LESS-THAN-1))
     (846 754 (:REWRITE DEFAULT-TIMES-1))
     (811 811
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (811 811
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (811 811
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (810 500
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (810 500
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (780 73 (:REWRITE |(< x (+ c/d y))|))
     (726 447 (:REWRITE DEFAULT-PLUS-2))
     (693 569 (:REWRITE DEFAULT-LESS-THAN-2))
     (609 107 (:REWRITE |(< (+ (- c) x) y)|))
     (607 428
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (594 471 (:REWRITE CONSTANT-<-INTEGERP))
     (569 569 (:REWRITE THE-FLOOR-BELOW))
     (569 569 (:REWRITE THE-FLOOR-ABOVE))
     (501 447 (:REWRITE DEFAULT-PLUS-1))
     (479 479
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (473 471 (:REWRITE |(< (- x) c)|))
     (473 471 (:REWRITE |(< (- x) (- y))|))
     (471 471
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (471 471
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (471 471
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (471 471
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (471 471
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (471 471 (:REWRITE |(< c (- x))|))
     (471 471
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (471 471
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (471 471
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (471 471
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (471 471 (:REWRITE |(< (/ x) (/ y))|))
     (433 389 (:REWRITE SIMPLIFY-SUMS-<))
     (348 30 (:REWRITE |(* y (* x z))|))
     (293 293
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (293 293
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (293 293
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (288 62 (:REWRITE |(* c (* d x))|))
     (265 265
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (261 141 (:REWRITE INTEGERP-MINUS-X))
     (240 8 (:REWRITE |(equal x (/ y))|))
     (234 110
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (196 56
          (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (160 8 (:REWRITE |(not (equal x (/ y)))|))
     (155 89
          (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (145 79
          (:REWRITE |(< x (/ y)) with (< y 0)|))
     (134 134 (:REWRITE REDUCE-INTEGERP-+))
     (134 134 (:META META-INTEGERP-CORRECT))
     (126 110
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (121 110 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (110 110
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (110 110
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (110 110 (:REWRITE |(equal c (/ x))|))
     (110 110 (:REWRITE |(equal c (- x))|))
     (110 110 (:REWRITE |(equal (/ x) c)|))
     (110 110 (:REWRITE |(equal (/ x) (/ y))|))
     (110 110 (:REWRITE |(equal (- x) c)|))
     (110 110 (:REWRITE |(equal (- x) (- y))|))
     (102 25 (:REWRITE |(+ (* c x) (* d x))|))
     (69 66 (:REWRITE DEFAULT-MINUS))
     (59 59 (:REWRITE |(< y (+ (- c) x))|))
     (43 39 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (37 37 (:REWRITE |(< (/ x) 0)|))
     (37 37 (:REWRITE |(< (* x y) 0)|))
     (34 34 (:REWRITE |(* (- x) y)|))
     (27 27
         (:REWRITE |(<= x (/ y)) with (< y 0)|))
     (27 27
         (:REWRITE |(< (/ x) y) with (< x 0)|))
     (25 25 (:REWRITE |(* 0 x)|))
     (16 1 (:REWRITE EVEN-AND-ODD-ALTERNATE))
     (10 10
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (9 9
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (9 9
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (8 8 (:REWRITE |(+ c (+ d x))|))
     (5 1 (:REWRITE |(integerp (- x))|))
     (2 2 (:REWRITE |(equal (+ (- c) x) y)|)))
(RTL::REM%-BNDS-32
 (16532 1844
        (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
 (12387 19
        (:REWRITE |(<= x (/ y)) with (< 0 y)|))
 (12240 19
        (:REWRITE |(< (/ x) y) with (< 0 x)|))
 (9380 22
       (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (9290 22
       (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (8568 1224 (:DEFINITION FIX))
 (4531 799 (:REWRITE DEFAULT-TIMES-2))
 (4184
  4184
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (4184
      4184
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (4184
     4184
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (4184 4184
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (2856 408
       (:REWRITE ARITH-BUBBLE-DOWN-*-MATCH-1))
 (2665 2665
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (2665 2665
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (2448 408
       (:REWRITE |arith (* (expt x m) (expt x n))|))
 (2250 618 (:REWRITE ARITH-NORMALIZE-ADDENDS))
 (1764 1764 (:REWRITE |arith (expt x c)|))
 (1600 1600 (:REWRITE |arith (expt 1/c n)|))
 (1540 70 (:REWRITE |(* y (* x z))|))
 (1500 250 (:REWRITE DEFAULT-PLUS-2))
 (1290 169
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (1290 169
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (1224 408
       (:REWRITE ARITH-BUBBLE-DOWN-+-MATCH-1))
 (1167 191 (:REWRITE INTEGERP-<-CONSTANT))
 (1113 191 (:REWRITE CONSTANT-<-INTEGERP))
 (1096 799 (:REWRITE DEFAULT-TIMES-1))
 (853 68 (:REWRITE |(< (+ c/d x) y)|))
 (816 408
      (:REWRITE |arith (+ (* c x) (* d x))|))
 (813 203 (:REWRITE DEFAULT-LESS-THAN-2))
 (787 203 (:REWRITE DEFAULT-LESS-THAN-1))
 (575 104
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (564 564
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3D))
 (564 564
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2D))
 (564 564
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1D))
 (507 507 (:REWRITE |arith (* (- x) y)|))
 (476 476
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (432 48 (:REWRITE ACL2-NUMBERP-X))
 (408 408 (:REWRITE |arith (* 0 x)|))
 (368 368
      (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (368 368
      (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (368 368
      (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (368 368
      (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (346 250 (:REWRITE DEFAULT-PLUS-1))
 (280 169 (:REWRITE SIMPLIFY-SUMS-<))
 (267 191
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (267 191
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (238 238
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (238 238 (:REWRITE NORMALIZE-ADDENDS))
 (203 203 (:REWRITE THE-FLOOR-BELOW))
 (203 203 (:REWRITE THE-FLOOR-ABOVE))
 (192 48 (:REWRITE RATIONALP-X))
 (191 191
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (191 191
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (191 191
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (191 191
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (191 191
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (191 191 (:REWRITE |(< c (- x))|))
 (191 191
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (191 191
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (191 191
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (191 191
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (191 191 (:REWRITE |(< (/ x) (/ y))|))
 (191 191 (:REWRITE |(< (- x) c)|))
 (191 191 (:REWRITE |(< (- x) (- y))|))
 (190 19
      (:REWRITE |(<= x (/ y)) with (< y 0)|))
 (190 19
      (:REWRITE |(< (/ x) y) with (< x 0)|))
 (184 184 (:LINEAR EXPT-LINEAR-UPPER-<))
 (184 184 (:LINEAR EXPT-LINEAR-LOWER-<))
 (184 184 (:LINEAR EXPT->=-1-TWO))
 (184 184 (:LINEAR EXPT->-1-TWO))
 (184 184 (:LINEAR EXPT-<=-1-ONE))
 (184 184 (:LINEAR EXPT-<-1-ONE))
 (138 22
      (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (138 22
      (:REWRITE |(< x (/ y)) with (< y 0)|))
 (127 127 (:REWRITE REDUCE-INTEGERP-+))
 (127 127 (:REWRITE INTEGERP-MINUS-X))
 (127 127 (:META META-INTEGERP-CORRECT))
 (110 110
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (110 110
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (110 110
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (104 104 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (104 104
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (104 104
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (104 104
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (104 104 (:REWRITE |(equal c (/ x))|))
 (104 104 (:REWRITE |(equal c (- x))|))
 (104 104 (:REWRITE |(equal (/ x) c)|))
 (104 104 (:REWRITE |(equal (/ x) (/ y))|))
 (104 104 (:REWRITE |(equal (- x) c)|))
 (104 104 (:REWRITE |(equal (- x) (- y))|))
 (96 96 (:REWRITE DEFAULT-MINUS))
 (76 76 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
 (76 76 (:TYPE-PRESCRIPTION ABS))
 (58 58 (:REWRITE |(< (+ (- c) x) y)|))
 (48 48 (:REWRITE REDUCE-RATIONALP-+))
 (48 48 (:REWRITE REDUCE-RATIONALP-*))
 (48 48 (:REWRITE RATIONALP-MINUS-X))
 (48 48 (:REWRITE DEFAULT-EXPT-2))
 (48 48 (:REWRITE DEFAULT-EXPT-1))
 (48 48 (:REWRITE |(expt 1/c n)|))
 (48 48 (:REWRITE |(expt (- x) n)|))
 (48 48 (:META META-RATIONALP-CORRECT))
 (47 47
     (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (47 47 (:REWRITE |(< y (+ (- c) x))|))
 (47 47 (:REWRITE |(< x (+ c/d y))|))
 (12 12 (:REWRITE |(< (/ x) 0)|))
 (12 12 (:REWRITE |(< (* x y) 0)|))
 (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
 (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
 (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RTL::REM%-BNDS-33
 (36554 3722
        (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
 (24135 25
        (:REWRITE |(< x (/ y)) with (< y 0)|))
 (24105 25
        (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (21500 17
        (:REWRITE |(<= x (/ y)) with (< y 0)|))
 (21475 17
        (:REWRITE |(< (/ x) y) with (< x 0)|))
 (8048
  8048
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (8048
      8048
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (8048
     8048
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (8048 8048
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (7292 285 (:REWRITE |(< (- x) c)|))
 (6384 912
       (:REWRITE ARITH-BUBBLE-DOWN-*-MATCH-1))
 (6080 790 (:REWRITE DEFAULT-PLUS-2))
 (5472 912
       (:REWRITE |arith (* (expt x m) (expt x n))|))
 (5236 942 (:REWRITE DEFAULT-TIMES-2))
 (4862 1214 (:REWRITE ARITH-NORMALIZE-ADDENDS))
 (3805 3805
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (3805 3805
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (3536 3536 (:REWRITE |arith (expt x c)|))
 (3288 3288 (:REWRITE |arith (expt 1/c n)|))
 (3032 790 (:REWRITE DEFAULT-PLUS-1))
 (2736 912
       (:REWRITE ARITH-BUBBLE-DOWN-+-MATCH-1))
 (2598 261
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (2440 108 (:REWRITE |(< (+ (- c) x) y)|))
 (2106 84 (:REWRITE |(* y (* x z))|))
 (1824 912
       (:REWRITE |arith (+ (* c x) (* d x))|))
 (1543 299 (:REWRITE DEFAULT-LESS-THAN-2))
 (1537 299 (:REWRITE DEFAULT-LESS-THAN-1))
 (1367 283 (:REWRITE CONSTANT-<-INTEGERP))
 (1360 25
       (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (1305 25
       (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (1303 283 (:REWRITE INTEGERP-<-CONSTANT))
 (1262 171 (:REWRITE SIMPLIFY-SUMS-<))
 (1259 942 (:REWRITE DEFAULT-TIMES-1))
 (1118 1118 (:REWRITE |arith (* (- x) y)|))
 (912 912 (:REWRITE |arith (* 0 x)|))
 (903 118 (:REWRITE |(< (+ c/d x) y)|))
 (704 704
      (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (704 704
      (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (704 704
      (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (704 704
      (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (618 508
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (604 92 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (575 104
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (564 564
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3D))
 (564 564
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2D))
 (564 564
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1D))
 (478 478 (:REWRITE |(* (- x) y)|))
 (470 17
      (:REWRITE |(<= x (/ y)) with (< 0 y)|))
 (433 17
      (:REWRITE |(< (/ x) y) with (< 0 x)|))
 (432 48 (:REWRITE ACL2-NUMBERP-X))
 (363 287
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (363 287
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (352 352 (:LINEAR EXPT-LINEAR-UPPER-<))
 (352 352 (:LINEAR EXPT-LINEAR-LOWER-<))
 (352 352 (:LINEAR EXPT->=-1-TWO))
 (352 352 (:LINEAR EXPT->-1-TWO))
 (352 352 (:LINEAR EXPT-<=-1-ONE))
 (352 352 (:LINEAR EXPT-<-1-ONE))
 (348 348
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (303 285 (:REWRITE |(< c (- x))|))
 (299 299 (:REWRITE THE-FLOOR-BELOW))
 (299 299 (:REWRITE THE-FLOOR-ABOVE))
 (285 285
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (285 285
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (285 285
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (285 285
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (285 285
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (285 285
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (285 285
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (285 285
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (285 285 (:REWRITE |(< (/ x) (/ y))|))
 (285 285 (:REWRITE |(< (- x) (- y))|))
 (283 283
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (227 135 (:META META-INTEGERP-CORRECT))
 (226 110 (:REWRITE DEFAULT-MINUS))
 (192 48 (:REWRITE RATIONALP-X))
 (153 137 (:REWRITE INTEGERP-MINUS-X))
 (135 135 (:REWRITE REDUCE-INTEGERP-+))
 (104 104 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (104 104
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (104 104
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (104 104
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (104 104 (:REWRITE |(equal c (/ x))|))
 (104 104 (:REWRITE |(equal c (- x))|))
 (104 104 (:REWRITE |(equal (/ x) c)|))
 (104 104 (:REWRITE |(equal (/ x) (/ y))|))
 (104 104 (:REWRITE |(equal (- x) c)|))
 (104 104 (:REWRITE |(equal (- x) (- y))|))
 (102 102
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (102 102
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (102 102
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (101 101 (:REWRITE |(< y (+ (- c) x))|))
 (101 101 (:REWRITE |(< x (+ c/d y))|))
 (76 76 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
 (76 76 (:TYPE-PRESCRIPTION ABS))
 (66 2 (:REWRITE BUBBLE-DOWN-*-MATCH-1))
 (54 8 (:REWRITE |(- (* c x))|))
 (50 50 (:REWRITE DEFAULT-EXPT-2))
 (50 50 (:REWRITE DEFAULT-EXPT-1))
 (50 50 (:REWRITE |(expt 1/c n)|))
 (50 50 (:REWRITE |(expt (- x) n)|))
 (49 49
     (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (48 48 (:REWRITE REDUCE-RATIONALP-+))
 (48 48 (:REWRITE REDUCE-RATIONALP-*))
 (48 48 (:REWRITE RATIONALP-MINUS-X))
 (48 48 (:META META-RATIONALP-CORRECT))
 (44 2 (:REWRITE |(* (- (/ c)) (expt c n))|))
 (38 38
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (24 24 (:REWRITE |(* x (- y))|))
 (20 2 (:REWRITE |(* (- (/ c)) (expt d n))|))
 (12 12 (:REWRITE FOLD-CONSTS-IN-+))
 (12 12 (:REWRITE |(< (/ x) 0)|))
 (12 12 (:REWRITE |(< (* x y) 0)|))
 (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
 (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
 (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
 (6 6 (:REWRITE |arith (+ c (+ d x))|))
 (2 2 (:REWRITE |(+ x (- x))|)))
(RTL::REM%-BNDS-34
 (2904 2904
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (2904 2904
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (2904 2904
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (2120 394 (:REWRITE RATIONALP-X))
 (2048 560 (:REWRITE DEFAULT-TIMES-2))
 (1836 252 (:REWRITE ACL2-NUMBERP-X))
 (1202 542 (:REWRITE DEFAULT-PLUS-1))
 (1014 1014
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (1014 1014
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (1014 1014
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (990 296 (:REWRITE DEFAULT-LESS-THAN-1))
 (988 203
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (613 193
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (613 193
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (578 560 (:REWRITE DEFAULT-TIMES-1))
 (539 193 (:REWRITE SIMPLIFY-SUMS-<))
 (529 529 (:REWRITE REDUCE-INTEGERP-+))
 (529 529 (:REWRITE INTEGERP-MINUS-X))
 (529 529 (:META META-INTEGERP-CORRECT))
 (525 256 (:REWRITE CONSTANT-<-INTEGERP))
 (506 506
      (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (506 506
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE))
 (506 506
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (506
   506
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (506
  506
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (506 506
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (506 506
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (506 506
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (506
     506
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (506 506
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (506 506
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (506 506
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (500 256 (:REWRITE INTEGERP-<-CONSTANT))
 (415 29
      (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (415 29
      (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (415 29
      (:REWRITE |(< x (/ y)) with (< y 0)|))
 (415 29
      (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (394 394 (:REWRITE REDUCE-RATIONALP-+))
 (394 394 (:REWRITE REDUCE-RATIONALP-*))
 (394 394 (:REWRITE RATIONALP-MINUS-X))
 (394 394 (:META META-RATIONALP-CORRECT))
 (370 296 (:REWRITE DEFAULT-LESS-THAN-2))
 (325 325
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (296 296 (:REWRITE THE-FLOOR-BELOW))
 (296 296 (:REWRITE THE-FLOOR-ABOVE))
 (287 20
      (:REWRITE |(<= x (/ y)) with (< y 0)|))
 (287 20
      (:REWRITE |(<= x (/ y)) with (< 0 y)|))
 (287 20
      (:REWRITE |(< (/ x) y) with (< x 0)|))
 (287 20
      (:REWRITE |(< (/ x) y) with (< 0 x)|))
 (256 256
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (256 256
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (256 256
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (256 256
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (256 256
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (256 256
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (256 256
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (256 256 (:REWRITE |(< c (- x))|))
 (256 256
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (256 256
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (256 256
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (256 256
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (256 256 (:REWRITE |(< (/ x) (/ y))|))
 (256 256 (:REWRITE |(< (- x) c)|))
 (256 256 (:REWRITE |(< (- x) (- y))|))
 (203 203 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (203 203
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (203 203
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (203 203
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (203 203 (:REWRITE |(equal c (/ x))|))
 (203 203 (:REWRITE |(equal c (- x))|))
 (203 203 (:REWRITE |(equal (/ x) c)|))
 (203 203 (:REWRITE |(equal (/ x) (/ y))|))
 (203 203 (:REWRITE |(equal (- x) c)|))
 (203 203 (:REWRITE |(equal (- x) (- y))|))
 (153 153
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3D))
 (153 153
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2D))
 (153 153
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1D))
 (72 72 (:REWRITE FOLD-CONSTS-IN-+))
 (72 72 (:REWRITE |(* (- x) y)|))
 (71 71
     (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (56 56 (:REWRITE |(< y (+ (- c) x))|))
 (56 56 (:REWRITE |(< x (+ c/d y))|))
 (45 45 (:REWRITE |(< (/ x) 0)|))
 (45 45 (:REWRITE |(< (* x y) 0)|))
 (40 36 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (36 36 (:REWRITE DEFAULT-EXPT-2))
 (36 36 (:REWRITE DEFAULT-EXPT-1))
 (36 36 (:REWRITE ARITH-NORMALIZE-ADDENDS))
 (36 36 (:REWRITE |(expt 1/c n)|))
 (36 36 (:REWRITE |(expt (- x) n)|))
 (29 29
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (18 18 (:REWRITE |(< (+ c/d x) y)|))
 (18 18 (:REWRITE |(< (+ (- c) x) y)|)))
(RTL::I-J-2
 (600 8 (:DEFINITION RTL::QUOT%))
 (219 28 (:REWRITE DEFAULT-TIMES-2))
 (208 33 (:REWRITE DEFAULT-PLUS-2))
 (187 1 (:REWRITE |(* x (if a b c))|))
 (123 28 (:REWRITE DEFAULT-TIMES-1))
 (120 2 (:REWRITE ACL2-NUMBERP-X))
 (102 2 (:REWRITE RATIONALP-X))
 (95 2 (:REWRITE |(* y x)|))
 (84 2 (:REWRITE RTL::INTP-Q%))
 (80 2 (:REWRITE ZP-OPEN))
 (70 2 (:REWRITE |(< x (if a b c))|))
 (52 2 (:REWRITE |(< y (+ (- c) x))|))
 (50 2 (:REWRITE |(+ x (if a b c))|))
 (48
   22
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (43 33 (:REWRITE DEFAULT-PLUS-1))
 (41 30 (:TYPE-PRESCRIPTION RTL::INTP-Q%))
 (32 32 (:TYPE-PRESCRIPTION RTL::R%))
 (32 32 (:TYPE-PRESCRIPTION RTL::NATP-R%))
 (30 30
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (30 30 (:REWRITE NORMALIZE-ADDENDS))
 (30 10 (:REWRITE DEFAULT-EXPT-1))
 (28 7
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (25 25
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (24 24 (:TYPE-PRESCRIPTION ZP))
 (22 22
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (22
  22
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (22 22
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (22 22
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (22 22
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (22 22
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (22 22
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (22 22
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (22 11
     (:TYPE-PRESCRIPTION RTL::Q%-CONSTRAINT))
 (21 21 (:REWRITE THE-FLOOR-BELOW))
 (21 21 (:REWRITE THE-FLOOR-ABOVE))
 (21 21 (:REWRITE DEFAULT-LESS-THAN-2))
 (21 21 (:REWRITE DEFAULT-LESS-THAN-1))
 (19 19
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (19 19
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (17 17
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (17 17 (:REWRITE INTEGERP-<-CONSTANT))
 (17 17 (:REWRITE CONSTANT-<-INTEGERP))
 (17 17
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (17 17
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (17 17
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (17 17
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (17 17 (:REWRITE |(< c (- x))|))
 (17 17
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (17 17
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (17 17
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (17 17
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (17 17 (:REWRITE |(< (/ x) (/ y))|))
 (17 17 (:REWRITE |(< (- x) c)|))
 (17 17 (:REWRITE |(< (- x) (- y))|))
 (13 1 (:REWRITE |(expt x (if a b c))|))
 (11 11 (:REWRITE SIMPLIFY-SUMS-<))
 (11 11
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (11 11 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (10 10 (:REWRITE DEFAULT-EXPT-2))
 (9 9 (:REWRITE |(expt 1/c n)|))
 (9 9 (:REWRITE |(expt (- x) n)|))
 (8 2
    (:TYPE-PRESCRIPTION NOT-INTEGERP-4A-EXPT))
 (8 1 (:REWRITE |(- (if a b c))|))
 (7 7
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (7 7
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (7 7
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (7 7 (:REWRITE |(< (/ x) 0)|))
 (7 7 (:REWRITE |(< (* x y) 0)|))
 (6 1 (:REWRITE |(- (+ x y))|))
 (5 1 (:REWRITE |(+ c (+ d x))|))
 (3 3 (:REWRITE REDUCE-INTEGERP-+))
 (3 3 (:REWRITE INTEGERP-MINUS-X))
 (3 3 (:REWRITE DEFAULT-MINUS))
 (3 3 (:REWRITE |(< (+ c/d x) y)|))
 (3 3 (:REWRITE |(< (+ (- c) x) y)|))
 (3 3 (:META META-INTEGERP-CORRECT))
 (3 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (3 1
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (2 2
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (2 2
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (2 2
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (2 2 (:REWRITE |(< x (+ c/d y))|))
 (2 2 (:REWRITE |(< 0 (* x y))|))
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
 (1 1 (:REWRITE |(equal (+ (- c) x) y)|)))
(RTL::REM%-BNDS-35
     (140 70
          (:TYPE-PRESCRIPTION RTL::Q%-CONSTRAINT))
     (77 29 (:REWRITE SIMPLIFY-SUMS-<))
     (77 29
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (77 29 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (66 42 (:REWRITE DEFAULT-LESS-THAN-2))
     (66 42 (:REWRITE DEFAULT-LESS-THAN-1))
     (48 36 (:REWRITE DEFAULT-PLUS-2))
     (48 36 (:REWRITE DEFAULT-PLUS-1))
     (42 42 (:REWRITE THE-FLOOR-BELOW))
     (42 42 (:REWRITE THE-FLOOR-ABOVE))
     (42 42
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (42 42
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (42 42
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (42 42 (:REWRITE INTEGERP-<-CONSTANT))
     (42 42 (:REWRITE CONSTANT-<-INTEGERP))
     (42 42
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (42 42
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (42 42
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (42 42
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (42 42 (:REWRITE |(< c (- x))|))
     (42 42
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (42 42
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (42 42
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (42 42
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (42 42 (:REWRITE |(< (/ x) (/ y))|))
     (42 42 (:REWRITE |(< (- x) c)|))
     (42 42 (:REWRITE |(< (- x) (- y))|))
     (42 21
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (24 24
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (24 24 (:REWRITE NORMALIZE-ADDENDS))
     (21 21 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (21 21
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (21 21
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (21 21
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (21 21 (:REWRITE |(equal c (/ x))|))
     (21 21 (:REWRITE |(equal c (- x))|))
     (21 21 (:REWRITE |(equal (/ x) c)|))
     (21 21 (:REWRITE |(equal (/ x) (/ y))|))
     (21 21 (:REWRITE |(equal (- x) c)|))
     (21 21 (:REWRITE |(equal (- x) (- y))|))
     (12 12 (:REWRITE |(< y (+ (- c) x))|))
     (12 12 (:REWRITE |(< x (+ c/d y))|))
     (5 5 (:REWRITE REDUCE-INTEGERP-+))
     (5 5 (:REWRITE INTEGERP-MINUS-X))
     (5 5 (:REWRITE |(< (/ x) 0)|))
     (5 5 (:REWRITE |(< (* x y) 0)|))
     (5 5 (:META META-INTEGERP-CORRECT))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RTL::HYP-INV
     (10 10 (:REWRITE THE-FLOOR-BELOW))
     (10 10 (:REWRITE THE-FLOOR-ABOVE))
     (10 10
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (10 10
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (10 10
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (10 10 (:REWRITE INTEGERP-<-CONSTANT))
     (10 10 (:REWRITE DEFAULT-LESS-THAN-2))
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
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (10 10
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (10 10
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (10 10
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (10 10 (:REWRITE |(< (/ x) (/ y))|))
     (10 10 (:REWRITE |(< (- x) c)|))
     (10 10 (:REWRITE |(< (- x) (- y))|))
     (7 7 (:REWRITE SIMPLIFY-SUMS-<))
     (7 7
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (7 7 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (6 6 (:REWRITE |(< (/ x) 0)|))
     (6 6 (:REWRITE |(< (* x y) 0)|))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (3 3 (:REWRITE REDUCE-INTEGERP-+))
     (3 3 (:REWRITE INTEGERP-MINUS-X))
     (3 3 (:META META-INTEGERP-CORRECT))
     (2 2 (:REWRITE ZP-OPEN))
     (2 2
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (2 2 (:REWRITE NORMALIZE-ADDENDS))
     (2 2 (:REWRITE DEFAULT-PLUS-2))
     (2 2 (:REWRITE DEFAULT-PLUS-1))
     (1 1 (:REWRITE |(< (+ c/d x) y)|))
     (1 1 (:REWRITE |(< (+ (- c) x) y)|)))
(RTL::REM%-BNDS-36)
(RTL::REM%-BNDS-37)
(RTL::REM%-BNDS-38)
(RTL::REM%-BNDS-39)
(RTL::REM%-BNDS-40
     (19595 1070 (:REWRITE RTL::I-J-2))
     (4953 2221 (:REWRITE SIMPLIFY-SUMS-<))
     (4953 2221
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (4953 2221
           (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (3587 2221 (:REWRITE DEFAULT-LESS-THAN-2))
     (3587 2221 (:REWRITE DEFAULT-LESS-THAN-1))
     (2221 2221 (:REWRITE THE-FLOOR-BELOW))
     (2221 2221 (:REWRITE THE-FLOOR-ABOVE))
     (2221 2221
           (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (2221 2221
           (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (2221 2221
           (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (2221 2221
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (2221 2221 (:REWRITE INTEGERP-<-CONSTANT))
     (2221 2221 (:REWRITE CONSTANT-<-INTEGERP))
     (2221 2221
           (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (2221 2221
           (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (2221 2221
           (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (2221 2221
           (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (2221 2221 (:REWRITE |(< c (- x))|))
     (2221 2221
           (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (2221 2221
           (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (2221 2221
           (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (2221 2221
           (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (2221 2221 (:REWRITE |(< (/ x) (/ y))|))
     (2221 2221 (:REWRITE |(< (- x) c)|))
     (2221 2221 (:REWRITE |(< (- x) (- y))|))
     (1980 990
           (:TYPE-PRESCRIPTION RTL::Q%-CONSTRAINT))
     (1330 363
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (1202 601 (:REWRITE DEFAULT-TIMES-2))
     (952 626 (:REWRITE DEFAULT-PLUS-2))
     (665 626 (:REWRITE DEFAULT-PLUS-1))
     (601 601
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (601 601 (:REWRITE DEFAULT-TIMES-1))
     (595 363 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (587 587
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (587 587 (:REWRITE NORMALIZE-ADDENDS))
     (363 363
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (363 363
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (363 363
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (363 363 (:REWRITE |(equal c (/ x))|))
     (363 363 (:REWRITE |(equal c (- x))|))
     (363 363 (:REWRITE |(equal (/ x) c)|))
     (363 363 (:REWRITE |(equal (/ x) (/ y))|))
     (363 363 (:REWRITE |(equal (- x) c)|))
     (363 363 (:REWRITE |(equal (- x) (- y))|))
     (251 251 (:REWRITE |(< (+ c/d x) y)|))
     (251 251 (:REWRITE |(< (+ (- c) x) y)|))
     (114 114
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (114 114
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (114 114 (:REWRITE REDUCE-INTEGERP-+))
     (114 114 (:REWRITE INTEGERP-MINUS-X))
     (114 114 (:REWRITE |(< (/ x) 0)|))
     (114 114 (:REWRITE |(< (* x y) 0)|))
     (114 114 (:META META-INTEGERP-CORRECT))
     (39 39 (:REWRITE |(< y (+ (- c) x))|))
     (39 39 (:REWRITE |(< x (+ c/d y))|)))
(RTL::REM%-BNDS-41
     (13 5 (:REWRITE SIMPLIFY-SUMS-<))
     (13 5
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (13 5 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (9 5 (:REWRITE DEFAULT-LESS-THAN-2))
     (9 5 (:REWRITE DEFAULT-LESS-THAN-1))
     (8 4 (:REWRITE DEFAULT-TIMES-2))
     (5 5 (:REWRITE THE-FLOOR-BELOW))
     (5 5 (:REWRITE THE-FLOOR-ABOVE))
     (5 5 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (5 5 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (5 5
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (5 5
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
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
     (5 2
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (4 4
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (4 4 (:REWRITE DEFAULT-TIMES-1))
     (3 3
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (3 3 (:REWRITE NORMALIZE-ADDENDS))
     (3 3 (:REWRITE DEFAULT-PLUS-2))
     (3 3 (:REWRITE DEFAULT-PLUS-1))
     (2 2 (:REWRITE ZP-OPEN))
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
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (1 1 (:REWRITE REDUCE-INTEGERP-+))
     (1 1 (:REWRITE INTEGERP-MINUS-X))
     (1 1 (:REWRITE |(< (/ x) 0)|))
     (1 1 (:REWRITE |(< (* x y) 0)|))
     (1 1 (:META META-INTEGERP-CORRECT)))
(RTL::REM%-BNDS)
(RTL::QUOT%-BNDS-1
 (94949 8470 (:REWRITE DEFAULT-PLUS-2))
 (78842 9453 (:REWRITE DEFAULT-TIMES-2))
 (37638
  37638
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (37638
      37638
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (37638
     37638
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (37638 37638
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (34452 82
        (:REWRITE |(< (/ x) y) with (< 0 x)|))
 (33662 8470 (:REWRITE DEFAULT-PLUS-1))
 (31982 42
        (:REWRITE |(<= x (/ y)) with (< 0 y)|))
 (29432 516 (:REWRITE |(< (+ (- c) x) y)|))
 (20670 124
        (:REWRITE |(< x (/ y)) with (< y 0)|))
 (20581 525 (:REWRITE |(< x (+ c/d y))|))
 (20343 2088 (:REWRITE DEFAULT-MINUS))
 (19779 42
        (:REWRITE |(<= x (/ y)) with (< y 0)|))
 (17768 536 (:REWRITE |(< (+ c/d x) y)|))
 (14805 517 (:REWRITE |(< y (+ (- c) x))|))
 (12911 1551 (:REWRITE CONSTANT-<-INTEGERP))
 (11697 9249
        (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
 (10991 2009 (:REWRITE DEFAULT-LESS-THAN-2))
 (10670 2009 (:REWRITE DEFAULT-LESS-THAN-1))
 (10642 1511 (:REWRITE INTEGERP-<-CONSTANT))
 (9717 9717
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (8477 8477
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (8477 8477
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (8477 8477
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (8208 1902
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (6981 1117 (:REWRITE SIMPLIFY-SUMS-<))
 (5012 437 (:REWRITE RTL::I-J-2))
 (4870 4870
       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (4785 197
       (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (4281 51 (:REWRITE |(equal x (/ y))|))
 (4145 51 (:REWRITE |(not (equal x (/ y)))|))
 (3981 1426 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (3892 247
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (3142 3142 (:REWRITE |arith (expt 1/c n)|))
 (2800 1677 (:REWRITE |(< (- x) (- y))|))
 (2626 2626 (:REWRITE |arith (* (- x) y)|))
 (2414 1686 (:REWRITE DEFAULT-EXPT-1))
 (2316 21 (:REWRITE EVEN-AND-ODD-ALTERNATE))
 (2273 2001 (:REWRITE ARITH-NORMALIZE-ADDENDS))
 (2138 1802
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (2009 2009 (:REWRITE THE-FLOOR-BELOW))
 (2009 2009 (:REWRITE THE-FLOOR-ABOVE))
 (1898 477 (:REWRITE INTEGERP-MINUS-X))
 (1776 1776 (:TYPE-PRESCRIPTION COLLECT-*))
 (1737 449 (:META META-INTEGERP-CORRECT))
 (1686 1686 (:REWRITE DEFAULT-EXPT-2))
 (1681 1677
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (1677 1677
       (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (1677 1677
       (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (1677 1677
       (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (1677 1677
       (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (1677 1677
       (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (1677 1677
       (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (1677 1677
       (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (1677 1677 (:REWRITE |(< (/ x) (/ y))|))
 (1675 1675 (:REWRITE |(* (- x) y)|))
 (1638 1638 (:REWRITE |(expt (- x) n)|))
 (1511 1511
       (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (1488 1488 (:REWRITE FOLD-CONSTS-IN-+))
 (1267 1265
       (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (904 904
      (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (904 904
      (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (904 904
      (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (904 904
      (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (811 811 (:REWRITE |arith (+ c (+ d x))|))
 (810 405
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (768 207
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (696 72 (:REWRITE ACL2-NUMBERP-X))
 (487 487 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
 (487 487 (:TYPE-PRESCRIPTION ABS))
 (476 68
      (:REWRITE ARITH-BUBBLE-DOWN-*-MATCH-1))
 (468 12 (:REWRITE |(* (- c) (expt c n))|))
 (452 452 (:LINEAR EXPT-LINEAR-UPPER-<))
 (452 452 (:LINEAR EXPT-LINEAR-LOWER-<))
 (452 452 (:LINEAR EXPT->=-1-TWO))
 (452 452 (:LINEAR EXPT->-1-TWO))
 (452 452 (:LINEAR EXPT-<=-1-ONE))
 (452 452 (:LINEAR EXPT-<-1-ONE))
 (449 449 (:REWRITE REDUCE-INTEGERP-+))
 (413 207 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (408 68
      (:REWRITE |arith (* (expt x m) (expt x n))|))
 (405 405
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (405 405
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (405 405
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (384 384 (:REWRITE ZP-OPEN))
 (384 6 (:REWRITE ODD-EXPT-THM))
 (349 247
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (312 72 (:REWRITE RATIONALP-X))
 (243 243 (:REWRITE BUBBLE-DOWN-*-MATCH-3))
 (207 207
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (207 207 (:REWRITE |(equal c (/ x))|))
 (207 207 (:REWRITE |(equal c (- x))|))
 (207 207 (:REWRITE |(equal (/ x) c)|))
 (207 207 (:REWRITE |(equal (/ x) (/ y))|))
 (207 207 (:REWRITE |(equal (- x) c)|))
 (207 207 (:REWRITE |(equal (- x) (- y))|))
 (204 68
      (:REWRITE ARITH-BUBBLE-DOWN-+-MATCH-1))
 (176 88 (:REWRITE COLLECT-*-PROBLEM-FINDER))
 (136 68
      (:REWRITE |arith (+ (* c x) (* d x))|))
 (108 108 (:REWRITE |(< 0 (* x y))|))
 (100 100 (:REWRITE |(* a (/ a) b)|))
 (88 88
     (:TYPE-PRESCRIPTION FMT-TO-COMMENT-WINDOW))
 (73 73 (:REWRITE |(< (* x y) 0)|))
 (72 72 (:REWRITE REDUCE-RATIONALP-+))
 (72 72 (:REWRITE REDUCE-RATIONALP-*))
 (72 72 (:REWRITE RATIONALP-MINUS-X))
 (72 72 (:META META-RATIONALP-CORRECT))
 (68 68 (:REWRITE |arith (* 0 x)|))
 (68 68 (:REWRITE |(< 0 (/ x))|))
 (64 64
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (64 64
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (53 53 (:REWRITE |(< (/ x) 0)|))
 (52 52
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (49 49
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (49 49
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (40 40
     (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (30 10 (:REWRITE |(equal (* (/ x) y) -1)|))
 (20 20 (:REWRITE |(equal (+ (- c) x) y)|))
 (20 20
     (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (15 5
     (:REWRITE |(not (equal (* (/ x) y) -1))|))
 (8 4
    (:TYPE-PRESCRIPTION RTL::Q%-CONSTRAINT)))
(RTL::QUOT%-BNDS-2-1
 (71696 188
        (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (15810 3250 (:REWRITE DEFAULT-TIMES-2))
 (11668
  11668
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (11668
      11668
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (11668
     11668
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (11668 11668
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (11668 11668
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (8346 1922 (:REWRITE DEFAULT-PLUS-2))
 (5994 1922 (:REWRITE DEFAULT-PLUS-1))
 (4860 3250 (:REWRITE DEFAULT-TIMES-1))
 (4810 1070 (:REWRITE INTEGERP-<-CONSTANT))
 (4784 4784
       (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
 (4626 1272 (:REWRITE DEFAULT-LESS-THAN-1))
 (4568 962
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (3534 3534
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (3534 3534
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (3534 3534
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (3528 3528 (:REWRITE |arith (expt x c)|))
 (3514 382 (:REWRITE |(< (+ c/d x) y)|))
 (3240 3240 (:REWRITE |arith (expt 1/c n)|))
 (2830 886 (:REWRITE SIMPLIFY-SUMS-<))
 (2244 1272 (:REWRITE DEFAULT-LESS-THAN-2))
 (2160 216 (:REWRITE DEFAULT-MINUS))
 (2002 328 (:REWRITE |(< (+ (- c) x) y)|))
 (1714 1214
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (1714 1214
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (1462 1070
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (1430 1070 (:REWRITE |(< (- x) c)|))
 (1430 1070 (:REWRITE |(< (- x) (- y))|))
 (1380 1380
       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (1272 1272 (:REWRITE THE-FLOOR-BELOW))
 (1272 1272 (:REWRITE THE-FLOOR-ABOVE))
 (1225 603
       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (1070 1070
       (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (1070 1070 (:REWRITE CONSTANT-<-INTEGERP))
 (1070 1070
       (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (1070 1070
       (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (1070 1070
       (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (1070 1070
       (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (1070 1070 (:REWRITE |(< c (- x))|))
 (1070 1070
       (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (1070 1070
       (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (1070 1070
       (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (1070 1070 (:REWRITE |(< (/ x) (/ y))|))
 (976 292 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (934 188
      (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (934 188
      (:REWRITE |(< x (/ y)) with (< y 0)|))
 (855 603 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (828 828 (:REWRITE |arith (* (- x) y)|))
 (828 828 (:REWRITE ARITH-NORMALIZE-ADDENDS))
 (756 756 (:REWRITE |arith (- (* c x))|))
 (686 326 (:REWRITE INTEGERP-MINUS-X))
 (603 603
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (603 603
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (603 603
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (603 603 (:REWRITE |(equal c (/ x))|))
 (603 603 (:REWRITE |(equal c (- x))|))
 (603 603 (:REWRITE |(equal (/ x) c)|))
 (603 603 (:REWRITE |(equal (/ x) (/ y))|))
 (603 603 (:REWRITE |(equal (- x) c)|))
 (603 603 (:REWRITE |(equal (- x) (- y))|))
 (576 576
      (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (576 576
      (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (576 576
      (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (576 576
      (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (500 500 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
 (500 500 (:TYPE-PRESCRIPTION ABS))
 (472 94
      (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (468 36 (:REWRITE |(+ (* c x) (* d x))|))
 (326 326 (:REWRITE REDUCE-INTEGERP-+))
 (326 326 (:META META-INTEGERP-CORRECT))
 (288 288 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (288 288 (:LINEAR EXPT-LINEAR-UPPER-<))
 (288 288 (:LINEAR EXPT-LINEAR-LOWER-<))
 (288 288 (:LINEAR EXPT->=-1-TWO))
 (288 288 (:LINEAR EXPT->-1-TWO))
 (288 288 (:LINEAR EXPT-<=-1-TWO))
 (288 288 (:LINEAR EXPT-<=-1-ONE))
 (288 288 (:LINEAR EXPT-<-1-TWO))
 (288 288 (:LINEAR EXPT-<-1-ONE))
 (216 216 (:REWRITE DEFAULT-EXPT-2))
 (216 216 (:REWRITE DEFAULT-EXPT-1))
 (216 216 (:REWRITE |(expt 1/c n)|))
 (216 216 (:REWRITE |(expt (- x) n)|))
 (144 144 (:REWRITE |(< (/ x) 0)|))
 (144 144 (:REWRITE |(< (* x y) 0)|))
 (144 144 (:REWRITE |(* (- x) y)|))
 (144 72
      (:TYPE-PRESCRIPTION RTL::Q%-CONSTRAINT))
 (108 108 (:REWRITE |(< y (+ (- c) x))|))
 (108 108 (:REWRITE |(< x (+ c/d y))|))
 (83 83 (:REWRITE |(equal (+ (- c) x) y)|))
 (76 76 (:REWRITE |(+ c (+ d x))|))
 (72 72 (:REWRITE BUBBLE-DOWN-*-MATCH-3))
 (50 50
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (40 40 (:REWRITE RTL::I-J-2))
 (36 36
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (36 36
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (36 36 (:REWRITE |(* 0 x)|)))
(RTL::QUOT%-BNDS-2-2
     (7864 414 (:REWRITE RTL::I-J-2))
     (1486 712 (:REWRITE SIMPLIFY-SUMS-<))
     (1486 712
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (1484 712
           (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (1099 712 (:REWRITE DEFAULT-LESS-THAN-2))
     (1099 712 (:REWRITE DEFAULT-LESS-THAN-1))
     (712 712 (:REWRITE THE-FLOOR-BELOW))
     (712 712 (:REWRITE THE-FLOOR-ABOVE))
     (712 712 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (712 712
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (712 712
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (712 712
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (712 712 (:REWRITE INTEGERP-<-CONSTANT))
     (712 712 (:REWRITE CONSTANT-<-INTEGERP))
     (712 712
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (712 712
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (712 712
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (712 712
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (712 712 (:REWRITE |(< c (- x))|))
     (712 712
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (712 712
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (712 712
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (712 712
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (712 712 (:REWRITE |(< (/ x) (/ y))|))
     (712 712 (:REWRITE |(< (- x) c)|))
     (712 712 (:REWRITE |(< (- x) (- y))|))
     (394 197 (:REWRITE DEFAULT-TIMES-2))
     (272 109
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (248 138 (:REWRITE DEFAULT-PLUS-2))
     (216 108
          (:TYPE-PRESCRIPTION RTL::Q%-CONSTRAINT))
     (197 197
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (197 197 (:REWRITE DEFAULT-TIMES-1))
     (163 109 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (138 138
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (138 138 (:REWRITE NORMALIZE-ADDENDS))
     (138 138 (:REWRITE DEFAULT-PLUS-1))
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
     (108 108 (:REWRITE |(< (+ c/d x) y)|))
     (108 108 (:REWRITE |(< (+ (- c) x) y)|))
     (27 27
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (27 27
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (27 27 (:REWRITE REDUCE-INTEGERP-+))
     (27 27 (:REWRITE INTEGERP-MINUS-X))
     (27 27 (:REWRITE |(< (/ x) 0)|))
     (27 27 (:REWRITE |(< (* x y) 0)|))
     (27 27 (:META META-INTEGERP-CORRECT))
     (2 2 (:REWRITE |(< y (+ (- c) x))|))
     (2 2 (:REWRITE |(< x (+ c/d y))|)))
(RTL::QUOT%-BNDS-2
 (346 82 (:REWRITE DEFAULT-PLUS-2))
 (236 82 (:REWRITE DEFAULT-PLUS-1))
 (156 6 (:REWRITE RTL::I-J-2))
 (148 22 (:REWRITE DEFAULT-TIMES-2))
 (134 32
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (130
  130
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (130 130
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (130
     130
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (130 130
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (124 17 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (114 17
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (83 32 (:REWRITE DEFAULT-LESS-THAN-2))
 (83 32 (:REWRITE DEFAULT-LESS-THAN-1))
 (68 32 (:REWRITE |(< c (- x))|))
 (60 24 (:REWRITE DEFAULT-MINUS))
 (58 28 (:REWRITE SIMPLIFY-SUMS-<))
 (48 24
     (:TYPE-PRESCRIPTION RTL::Q%-CONSTRAINT))
 (46 46
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (42 6 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (32 32 (:REWRITE THE-FLOOR-BELOW))
 (32 32 (:REWRITE THE-FLOOR-ABOVE))
 (32 32 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (32 32
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (32 32
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (32 32
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (32 32 (:REWRITE INTEGERP-<-CONSTANT))
 (32 32 (:REWRITE CONSTANT-<-INTEGERP))
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
 (32 32 (:REWRITE |(< (- x) c)|))
 (32 32 (:REWRITE |(< (- x) (- y))|))
 (30 22 (:REWRITE DEFAULT-TIMES-1))
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
 (14 14 (:REWRITE DEFAULT-EXPT-2))
 (14 14 (:REWRITE DEFAULT-EXPT-1))
 (14 14 (:REWRITE ARITH-NORMALIZE-ADDENDS))
 (14 14 (:REWRITE |(expt 1/c n)|))
 (14 14 (:REWRITE |(expt (- x) n)|))
 (12 6
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (10 10 (:REWRITE |arith (expt x c)|))
 (10 10
     (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
 (6 6
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (6 6
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (6 6
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (6 6 (:REWRITE ZP-OPEN))
 (6 6 (:REWRITE |(* (- x) y)|))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (4 4 (:REWRITE |arith (expt 1/c n)|))
 (4 4 (:REWRITE |arith (* (- x) y)|))
 (4 4 (:REWRITE |(< y (+ (- c) x))|))
 (4 4 (:REWRITE |(< x (+ c/d y))|))
 (4 4 (:REWRITE |(< (+ c/d x) y)|))
 (4 4 (:REWRITE |(< (+ (- c) x) y)|))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (3 3 (:REWRITE REDUCE-INTEGERP-+))
 (3 3 (:REWRITE INTEGERP-MINUS-X))
 (3 3 (:REWRITE |(< (/ x) 0)|))
 (3 3 (:REWRITE |(< (* x y) 0)|))
 (3 3 (:META META-INTEGERP-CORRECT)))
(RTL::QUOT%-BNDS-3
 (530 24
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (212 16 (:REWRITE CONSTANT-<-INTEGERP))
 (188 2 (:LINEAR EXPT-X->=-X))
 (188 2 (:LINEAR EXPT-X->-X))
 (106 2 (:LINEAR EXPT-<=-1-TWO))
 (104 2 (:LINEAR EXPT->-1-ONE))
 (88 8 (:REWRITE |(* y (* x z))|))
 (74
  74
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (74 74
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (74 74
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (74 74
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (74 74
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (56 24 (:REWRITE DEFAULT-TIMES-2))
 (36 36 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (36 36 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (36 36 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (24 24 (:REWRITE THE-FLOOR-BELOW))
 (24 24 (:REWRITE THE-FLOOR-ABOVE))
 (24 24 (:REWRITE DEFAULT-TIMES-1))
 (24 24 (:REWRITE DEFAULT-LESS-THAN-2))
 (24 24 (:REWRITE DEFAULT-LESS-THAN-1))
 (16 16
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (16 16
     (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
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
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (16 16
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (16 16
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (16 16
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (16 16 (:REWRITE |(< (/ x) (/ y))|))
 (16 16 (:REWRITE |(< (- x) c)|))
 (16 16 (:REWRITE |(< (- x) (- y))|))
 (12 12 (:REWRITE SIMPLIFY-SUMS-<))
 (12 12
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (12 12
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (12 12 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (12 12 (:REWRITE INTEGERP-<-CONSTANT))
 (10 10 (:REWRITE |arith (expt x c)|))
 (10 10 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (8 8 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
 (8 8 (:TYPE-PRESCRIPTION ABS))
 (8 8 (:REWRITE |arith (expt 1/c n)|))
 (8 8
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (8 8 (:REWRITE |(< 0 (* x y))|))
 (8 8 (:REWRITE |(* a (/ a) b)|))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (4 4 (:REWRITE |(< 0 (/ x))|))
 (4 4
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (4 4 (:REWRITE |(< (/ x) y) with (< x 0)|))
 (4 4 (:REWRITE |(< (/ x) y) with (< 0 x)|))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (2 2 (:REWRITE |arith (* c (* d x))|))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-TWO))
 (2 2 (:LINEAR EXPT-<-1-ONE)))
(RTL::QUOT%-BNDS-4
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
 (21 3 (:REWRITE DEFAULT-TIMES-2))
 (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (4 3 (:REWRITE DEFAULT-TIMES-1))
 (2 2 (:REWRITE DEFAULT-EXPT-2))
 (2 2 (:REWRITE DEFAULT-EXPT-1))
 (2 2 (:REWRITE |(expt 1/c n)|))
 (2 2 (:REWRITE |(expt (- x) n)|))
 (1 1 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (1 1 (:REWRITE NORMALIZE-ADDENDS))
 (1 1 (:REWRITE DEFAULT-PLUS-2))
 (1 1 (:REWRITE DEFAULT-PLUS-1)))
(RTL::QUOT%-BNDS-5)
(RTL::QUOT%-BNDS-6
 (394
  394
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (394 394
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (394
     394
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (394 394
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (326 72 (:REWRITE DEFAULT-TIMES-2))
 (245 72 (:REWRITE DEFAULT-TIMES-1))
 (108 108
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (108 108
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (108 108
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (53 14 (:REWRITE DEFAULT-LESS-THAN-2))
 (50 14 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (48 9 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (46 1
     (:REWRITE |(<= x (/ y)) with (< 0 y)|))
 (38 20 (:REWRITE DEFAULT-PLUS-2))
 (32 14 (:REWRITE DEFAULT-LESS-THAN-1))
 (27 9 (:REWRITE SIMPLIFY-SUMS-<))
 (25 1 (:LINEAR EXPT-X->=-X))
 (25 1 (:LINEAR EXPT-X->-X))
 (24 20 (:REWRITE DEFAULT-PLUS-1))
 (20 20 (:REWRITE DEFAULT-EXPT-2))
 (20 20 (:REWRITE DEFAULT-EXPT-1))
 (20 20 (:REWRITE |(expt 1/c n)|))
 (20 20 (:REWRITE |(expt (- x) n)|))
 (18 14
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (18 14
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (17 11 (:REWRITE CONSTANT-<-INTEGERP))
 (16 11
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (14 14 (:REWRITE THE-FLOOR-BELOW))
 (14 14 (:REWRITE THE-FLOOR-ABOVE))
 (13 11
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (11 11 (:REWRITE INTEGERP-<-CONSTANT))
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
 (8 8 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (8 8
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (5 4 (:REWRITE |(< (/ x) y) with (< x 0)|))
 (5 2
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (4 4 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
 (4 4 (:TYPE-PRESCRIPTION ABS))
 (4 4 (:REWRITE DEFAULT-MINUS))
 (4 4 (:REWRITE |(* (- x) y)|))
 (3 3 (:REWRITE REDUCE-INTEGERP-+))
 (3 3 (:REWRITE INTEGERP-MINUS-X))
 (3 3 (:META META-INTEGERP-CORRECT))
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
 (2 2 (:REWRITE |(< y (+ (- c) x))|))
 (2 2 (:REWRITE |(< x (+ c/d y))|))
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
    (:REWRITE |(<= x (/ y)) with (< y 0)|))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<))
 (1 1 (:LINEAR EXPT->=-1-TWO))
 (1 1 (:LINEAR EXPT->-1-TWO))
 (1 1 (:LINEAR EXPT-<=-1-TWO))
 (1 1 (:LINEAR EXPT-<=-1-ONE))
 (1 1 (:LINEAR EXPT-<-1-TWO))
 (1 1 (:LINEAR EXPT-<-1-ONE)))
(RTL::QUOT%-BNDS-7
 (339
  339
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (339 339
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (339
     339
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (339 339
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (87 87 (:REWRITE |arith (expt x c)|))
 (83 83 (:REWRITE |arith (expt 1/c n)|))
 (72 16 (:REWRITE DEFAULT-TIMES-2))
 (47 1
     (:REWRITE |(<= x (/ y)) with (< 0 y)|))
 (42 6 (:REWRITE DEFAULT-PLUS-2))
 (37 7 (:REWRITE DEFAULT-LESS-THAN-2))
 (35 5
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (35 5 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (32 32 (:REWRITE |arith (* (- x) y)|))
 (32 5 (:REWRITE SIMPLIFY-SUMS-<))
 (28 16 (:REWRITE DEFAULT-TIMES-1))
 (19 19 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (19 19 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (19 19 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (16 16
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (16 16
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (16 16
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (16 16
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (16 7 (:REWRITE DEFAULT-LESS-THAN-1))
 (11 11 (:REWRITE |arith (* c (* d x))|))
 (11 5 (:REWRITE CONSTANT-<-INTEGERP))
 (10 6
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (10 6
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (10 5
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (8 8 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (8 8 (:LINEAR EXPT-LINEAR-UPPER-<))
 (8 8 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (8 8 (:LINEAR EXPT-LINEAR-LOWER-<))
 (8 8 (:LINEAR EXPT->=-1-TWO))
 (8 8 (:LINEAR EXPT->-1-TWO))
 (8 8 (:LINEAR EXPT-<=-1-ONE))
 (8 8 (:LINEAR EXPT-<-1-ONE))
 (7 7 (:REWRITE THE-FLOOR-BELOW))
 (7 7 (:REWRITE THE-FLOOR-ABOVE))
 (7 5 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (6 6
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (6 6 (:REWRITE NORMALIZE-ADDENDS))
 (6 6 (:REWRITE DEFAULT-PLUS-1))
 (5 5 (:REWRITE INTEGERP-<-CONSTANT))
 (5 5 (:REWRITE DEFAULT-EXPT-2))
 (5 5 (:REWRITE DEFAULT-EXPT-1))
 (5 5 (:REWRITE |(expt 1/c n)|))
 (5 5 (:REWRITE |(expt (- x) n)|))
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
 (5 2
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (4 4 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
 (4 4 (:TYPE-PRESCRIPTION ABS))
 (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (3 2 (:REWRITE |(< (/ x) y) with (< x 0)|))
 (2 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (2 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (2 2
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (2 2 (:REWRITE REDUCE-INTEGERP-+))
 (2 2
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (2 2 (:REWRITE INTEGERP-MINUS-X))
 (2 2
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (2 2 (:REWRITE DEFAULT-MINUS))
 (2 2 (:REWRITE |(equal c (/ x))|))
 (2 2 (:REWRITE |(equal c (- x))|))
 (2 2 (:REWRITE |(equal (/ x) c)|))
 (2 2 (:REWRITE |(equal (/ x) (/ y))|))
 (2 2 (:REWRITE |(equal (- x) c)|))
 (2 2 (:REWRITE |(equal (- x) (- y))|))
 (2 2 (:REWRITE |(< y (+ (- c) x))|))
 (2 2 (:META META-INTEGERP-CORRECT))
 (2 1
    (:REWRITE |(<= x (/ y)) with (< y 0)|))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE |(* (- x) y)|)))
(RTL::QUOT%-BNDS-8
 (4607 33
       (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (2417 265
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (1985
  1985
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1985
      1985
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1985
     1985
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1985 1985
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1801 396 (:REWRITE DEFAULT-TIMES-2))
 (1415 507 (:REWRITE DEFAULT-PLUS-2))
 (1348 37 (:REWRITE |(* y x)|))
 (1139 507 (:REWRITE DEFAULT-PLUS-1))
 (817 221 (:REWRITE CONSTANT-<-INTEGERP))
 (800 209 (:REWRITE INTEGERP-<-CONSTANT))
 (712 356
      (:TYPE-PRESCRIPTION RTL::Q%-CONSTRAINT))
 (619 209
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (570 12 (:LINEAR EXPT-X->=-X))
 (570 12 (:LINEAR EXPT-X->-X))
 (567 396 (:REWRITE DEFAULT-TIMES-1))
 (541 265 (:REWRITE DEFAULT-LESS-THAN-1))
 (435 265 (:REWRITE DEFAULT-LESS-THAN-2))
 (420 36 (:REWRITE |(* y (* x z))|))
 (373 221 (:REWRITE |(< (- x) c)|))
 (373 221 (:REWRITE |(< (- x) (- y))|))
 (355 185 (:REWRITE SIMPLIFY-SUMS-<))
 (342 12 (:LINEAR EXPT-<-1-TWO))
 (336 336 (:TYPE-PRESCRIPTION COLLECT-*))
 (318 12 (:LINEAR EXPT->-1-ONE))
 (317 229
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (265 265 (:REWRITE THE-FLOOR-BELOW))
 (265 265 (:REWRITE THE-FLOOR-ABOVE))
 (255 129
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (245 245 (:REWRITE |arith (expt x c)|))
 (240 88 (:REWRITE DEFAULT-MINUS))
 (224 224
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (221 221
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (221 221
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (221 221
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (221 221
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (221 221 (:REWRITE |(< c (- x))|))
 (221 221
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (221 221
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (221 221
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (221 221
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (221 221 (:REWRITE |(< (/ x) (/ y))|))
 (216 64 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (209 209
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (205 41
      (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (174 154 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (161 33
      (:REWRITE |(< x (/ y)) with (< y 0)|))
 (137 65 (:REWRITE INTEGERP-MINUS-X))
 (133 133 (:REWRITE |arith (expt 1/c n)|))
 (133 129
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (129 129 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (129 129
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (129 129
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (129 129 (:REWRITE |(equal c (/ x))|))
 (129 129 (:REWRITE |(equal c (- x))|))
 (129 129 (:REWRITE |(equal (/ x) c)|))
 (129 129 (:REWRITE |(equal (/ x) (/ y))|))
 (129 129 (:REWRITE |(equal (- x) c)|))
 (129 129 (:REWRITE |(equal (- x) (- y))|))
 (126 126 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
 (126 126 (:TYPE-PRESCRIPTION ABS))
 (115 115 (:REWRITE |arith (* (- x) y)|))
 (80 14
     (:REWRITE |(< (/ x) y) with (< 0 x)|))
 (76 2
     (:REWRITE |(<= x (/ y)) with (< 0 y)|))
 (67 67 (:REWRITE DEFAULT-EXPT-2))
 (67 67 (:REWRITE DEFAULT-EXPT-1))
 (67 67 (:REWRITE |(expt (- x) n)|))
 (65 65 (:REWRITE REDUCE-INTEGERP-+))
 (65 65 (:META META-INTEGERP-CORRECT))
 (62 2 (:REWRITE BUBBLE-DOWN-*-BUBBLE-DOWN))
 (55 55 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (55 55 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (55 55 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (52 52 (:REWRITE |(* (- x) y)|))
 (43 43 (:REWRITE |(< (+ c/d x) y)|))
 (43 43 (:REWRITE |(< (+ (- c) x) y)|))
 (42 42 (:REWRITE |(< (* x y) 0)|))
 (36 36 (:REWRITE |(< 0 (* x y))|))
 (36 36 (:REWRITE |(* a (/ a) b)|))
 (36 18 (:REWRITE COLLECT-*-PROBLEM-FINDER))
 (30 30
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (30 30
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (30 30 (:REWRITE |(< (/ x) 0)|))
 (26 26 (:REWRITE |(< y (+ (- c) x))|))
 (26 26 (:REWRITE |(< x (+ c/d y))|))
 (24 24
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (24 24
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (24 24 (:REWRITE |(< 0 (/ x))|))
 (24 24
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (24 24
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (24 24
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (24 24
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (22 1 (:REWRITE |(not (equal x (/ y)))|))
 (22 1 (:REWRITE |(equal x (/ y))|))
 (18 18
     (:TYPE-PRESCRIPTION FMT-TO-COMMENT-WINDOW))
 (14 14
     (:REWRITE |(< (/ x) y) with (< x 0)|))
 (13 13
     (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (12 12
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (12 12
     (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (12 12
     (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (12 12 (:LINEAR EXPT-LINEAR-UPPER-<))
 (12 12 (:LINEAR EXPT-LINEAR-LOWER-<))
 (12 12 (:LINEAR EXPT->=-1-TWO))
 (12 12 (:LINEAR EXPT->-1-TWO))
 (12 12 (:LINEAR EXPT-<=-1-ONE))
 (12 12 (:LINEAR EXPT-<-1-ONE))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE BUBBLE-DOWN-*-MATCH-3))
 (2 2
    (:REWRITE |(<= x (/ y)) with (< y 0)|))
 (2 2 (:REWRITE |(* c (* d x))|)))
(RTL::QUOT%-BNDS-9
 (530 24
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (212 16 (:REWRITE CONSTANT-<-INTEGERP))
 (188 2 (:LINEAR EXPT-X->=-X))
 (188 2 (:LINEAR EXPT-X->-X))
 (106 2 (:LINEAR EXPT-<=-1-TWO))
 (104 2 (:LINEAR EXPT->-1-ONE))
 (88 8 (:REWRITE |(* y (* x z))|))
 (65
  65
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (65 65
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (65 65
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (65 65
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (65 65
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (56 24 (:REWRITE DEFAULT-TIMES-2))
 (24 24 (:REWRITE THE-FLOOR-BELOW))
 (24 24 (:REWRITE THE-FLOOR-ABOVE))
 (24 24 (:REWRITE DEFAULT-TIMES-1))
 (24 24 (:REWRITE DEFAULT-LESS-THAN-2))
 (24 24 (:REWRITE DEFAULT-LESS-THAN-1))
 (16 16
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
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
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (16 16
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (16 16
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (16 16
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (16 16 (:REWRITE |(< (/ x) (/ y))|))
 (16 16 (:REWRITE |(< (- x) c)|))
 (16 16 (:REWRITE |(< (- x) (- y))|))
 (13 13
     (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
 (12 12 (:REWRITE SIMPLIFY-SUMS-<))
 (12 12
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (12 12
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (12 12 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (12 12 (:REWRITE INTEGERP-<-CONSTANT))
 (10 10 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (9 9 (:REWRITE |arith (expt x c)|))
 (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (8 8 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
 (8 8 (:TYPE-PRESCRIPTION ABS))
 (8 8
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (8 8 (:REWRITE |(< 0 (* x y))|))
 (8 8 (:REWRITE |(* a (/ a) b)|))
 (7 7 (:REWRITE |arith (expt 1/c n)|))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (4 4 (:REWRITE |(< 0 (/ x))|))
 (4 4
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (4 4 (:REWRITE |(< (/ x) y) with (< x 0)|))
 (4 4 (:REWRITE |(< (/ x) y) with (< 0 x)|))
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
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-TWO))
 (2 2 (:LINEAR EXPT-<-1-ONE))
 (1 1 (:REWRITE |arith (- (* c x))|))
 (1 1 (:REWRITE |arith (* c (* d x))|))
 (1 1 (:REWRITE |arith (* (- x) y)|)))
(RTL::QUOT%-BNDS-10)
(RTL::QUOT%-BNDS-11
 (316
  316
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (316 316
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (316
     316
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (316 316
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (242 50 (:REWRITE DEFAULT-TIMES-1))
 (220 50 (:REWRITE DEFAULT-TIMES-2))
 (46 10 (:REWRITE DEFAULT-LESS-THAN-2))
 (44 8 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (42 5 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (32 10 (:REWRITE DEFAULT-LESS-THAN-1))
 (30 10
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (28 10 (:REWRITE DEFAULT-PLUS-2))
 (23 5 (:REWRITE SIMPLIFY-SUMS-<))
 (14 10 (:REWRITE DEFAULT-PLUS-1))
 (11 11 (:REWRITE DEFAULT-EXPT-2))
 (11 11 (:REWRITE DEFAULT-EXPT-1))
 (11 11 (:REWRITE |(expt 1/c n)|))
 (11 11 (:REWRITE |(expt (- x) n)|))
 (10 10 (:REWRITE THE-FLOOR-BELOW))
 (10 10 (:REWRITE THE-FLOOR-ABOVE))
 (10 10
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (10 10
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
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
 (10 10 (:REWRITE |(< (- x) c)|))
 (10 10 (:REWRITE |(< (- x) (- y))|))
 (7 7 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (5 5 (:REWRITE REDUCE-INTEGERP-+))
 (5 5 (:REWRITE INTEGERP-MINUS-X))
 (5 5 (:META META-INTEGERP-CORRECT))
 (5 2
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (4 4 (:REWRITE DEFAULT-MINUS))
 (4 4 (:REWRITE |(* (- x) y)|))
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
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
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
 (2 2 (:REWRITE |(< (+ c/d x) y)|))
 (2 2 (:REWRITE |(< (+ (- c) x) y)|))
 (1 1 (:REWRITE ZP-OPEN)))
(RTL::QUOT%-BNDS-12
 (343
  343
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (343 343
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (343
     343
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (343 343
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (87 87 (:REWRITE |arith (expt x c)|))
 (83 83 (:REWRITE |arith (expt 1/c n)|))
 (62 7 (:REWRITE DEFAULT-PLUS-2))
 (45 7 (:REWRITE DEFAULT-PLUS-1))
 (44 4
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (27 27 (:REWRITE |arith (* (- x) y)|))
 (26 5 (:REWRITE DEFAULT-LESS-THAN-2))
 (25 5 (:REWRITE DEFAULT-LESS-THAN-1))
 (22 3 (:REWRITE SIMPLIFY-SUMS-<))
 (16 16
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (16 16
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (16 16
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (16 16
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (15 5
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (14 5 (:REWRITE |(< (- x) (- y))|))
 (12 2 (:REWRITE DEFAULT-TIMES-2))
 (12 2 (:REWRITE DEFAULT-TIMES-1))
 (11 11 (:REWRITE |arith (* c (* d x))|))
 (11 2 (:REWRITE DEFAULT-MINUS))
 (10 1 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (8 8 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (8 8 (:LINEAR EXPT-LINEAR-UPPER-<))
 (8 8 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (8 8 (:LINEAR EXPT-LINEAR-LOWER-<))
 (8 8 (:LINEAR EXPT->=-1-TWO))
 (8 8 (:LINEAR EXPT->-1-TWO))
 (8 8 (:LINEAR EXPT-<=-1-ONE))
 (8 8 (:LINEAR EXPT-<-1-ONE))
 (5 5 (:REWRITE THE-FLOOR-BELOW))
 (5 5 (:REWRITE THE-FLOOR-ABOVE))
 (5 5
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (5 5
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
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
 (5 2
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (3 3
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (3 3 (:REWRITE DEFAULT-EXPT-2))
 (3 3 (:REWRITE DEFAULT-EXPT-1))
 (3 3 (:REWRITE |(expt 1/c n)|))
 (3 3 (:REWRITE |(expt (- x) n)|))
 (2 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (2 2
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (2 2 (:REWRITE REDUCE-INTEGERP-+))
 (2 2
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (2 2 (:REWRITE INTEGERP-MINUS-X))
 (2 2
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (2 2 (:REWRITE |(equal c (/ x))|))
 (2 2 (:REWRITE |(equal c (- x))|))
 (2 2 (:REWRITE |(equal (/ x) c)|))
 (2 2 (:REWRITE |(equal (/ x) (/ y))|))
 (2 2 (:REWRITE |(equal (- x) c)|))
 (2 2 (:REWRITE |(equal (- x) (- y))|))
 (2 2 (:REWRITE |(< (+ c/d x) y)|))
 (2 2 (:REWRITE |(< (+ (- c) x) y)|))
 (2 2 (:META META-INTEGERP-CORRECT))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (1 1 (:REWRITE |(< y (+ (- c) x))|))
 (1 1 (:REWRITE |(< x (+ c/d y))|)))
(RTL::QUOT%-BNDS-13
 (2245 181
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (1258
  1258
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1258
      1258
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1258
     1258
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1258 1258
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (835 291 (:REWRITE DEFAULT-PLUS-2))
 (733 145 (:REWRITE CONSTANT-<-INTEGERP))
 (678 291 (:REWRITE DEFAULT-PLUS-1))
 (640 320
      (:TYPE-PRESCRIPTION RTL::Q%-CONSTRAINT))
 (574 169 (:REWRITE DEFAULT-TIMES-2))
 (570 12 (:LINEAR EXPT-X->=-X))
 (570 12 (:LINEAR EXPT-X->-X))
 (420 129
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (420 36 (:REWRITE |(* y (* x z))|))
 (382 181 (:REWRITE DEFAULT-LESS-THAN-2))
 (342 12 (:LINEAR EXPT-<-1-TWO))
 (318 12 (:LINEAR EXPT->-1-ONE))
 (273 181 (:REWRITE DEFAULT-LESS-THAN-1))
 (254 127
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (217 145 (:REWRITE |(< c (- x))|))
 (195 119 (:REWRITE SIMPLIFY-SUMS-<))
 (181 181 (:REWRITE THE-FLOOR-BELOW))
 (181 181 (:REWRITE THE-FLOOR-ABOVE))
 (178 169 (:REWRITE DEFAULT-TIMES-1))
 (163 145 (:REWRITE |(< (- x) (- y))|))
 (156 156
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (152 62 (:REWRITE DEFAULT-MINUS))
 (145 145 (:REWRITE |arith (expt x c)|))
 (145 145
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (145 145
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (145 145
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (145 145
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (145 145
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (145 145
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (145 145
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (145 145
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (145 145
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (145 145 (:REWRITE |(< (/ x) (/ y))|))
 (145 145 (:REWRITE |(< (- x) c)|))
 (133 133
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (133 133 (:REWRITE INTEGERP-<-CONSTANT))
 (127 127 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (127 127
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (127 127
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (127 127
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (127 127 (:REWRITE |(equal c (/ x))|))
 (127 127 (:REWRITE |(equal c (- x))|))
 (127 127 (:REWRITE |(equal (/ x) c)|))
 (127 127 (:REWRITE |(equal (/ x) (/ y))|))
 (127 127 (:REWRITE |(equal (- x) c)|))
 (127 127 (:REWRITE |(equal (- x) (- y))|))
 (108 18 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (95 95 (:REWRITE |arith (expt 1/c n)|))
 (75 75 (:REWRITE |arith (* (- x) y)|))
 (61 61 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (61 61 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (61 61 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (52 52 (:REWRITE |(* (- x) y)|))
 (42 42 (:REWRITE |(< (* x y) 0)|))
 (36 36 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
 (36 36 (:TYPE-PRESCRIPTION ABS))
 (36 36 (:REWRITE |(< 0 (* x y))|))
 (36 36 (:REWRITE |(* a (/ a) b)|))
 (31 31 (:REWRITE DEFAULT-EXPT-2))
 (31 31 (:REWRITE DEFAULT-EXPT-1))
 (31 31 (:REWRITE |(expt 1/c n)|))
 (31 31 (:REWRITE |(expt (- x) n)|))
 (30 30
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (30 30
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (30 30 (:REWRITE REDUCE-INTEGERP-+))
 (30 30 (:REWRITE INTEGERP-MINUS-X))
 (30 30 (:REWRITE |(< (/ x) 0)|))
 (30 30 (:META META-INTEGERP-CORRECT))
 (24 24
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (24 24
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (24 24 (:REWRITE |(< 0 (/ x))|))
 (24 24
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (24 24
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (24 24
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (24 24
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (19 19 (:REWRITE |(< y (+ (- c) x))|))
 (19 19 (:REWRITE |(< x (+ c/d y))|))
 (12 12
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (12 12
     (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (12 12
     (:REWRITE |(< (/ x) y) with (< x 0)|))
 (12 12
     (:REWRITE |(< (/ x) y) with (< 0 x)|))
 (12 12
     (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (12 12 (:LINEAR EXPT-LINEAR-UPPER-<))
 (12 12 (:LINEAR EXPT-LINEAR-LOWER-<))
 (12 12 (:LINEAR EXPT->=-1-TWO))
 (12 12 (:LINEAR EXPT->-1-TWO))
 (12 12 (:LINEAR EXPT-<=-1-ONE))
 (12 12 (:LINEAR EXPT-<-1-ONE))
 (10 10 (:REWRITE |(< (+ c/d x) y)|))
 (10 10 (:REWRITE |(< (+ (- c) x) y)|))
 (2 2 (:REWRITE ZP-OPEN)))
(RTL::QUOT%-BNDS
     (387 9 (:REWRITE |(< x (/ y)) with (< 0 y)|))
     (362 9
          (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (203 43
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (93 43 (:REWRITE INTEGERP-<-CONSTANT))
     (92 14 (:REWRITE |(equal (/ x) c)|))
     (79 43
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (79 43
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (67 43 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (64 43 (:REWRITE DEFAULT-LESS-THAN-1))
     (52 40 (:REWRITE DEFAULT-PLUS-1))
     (46 43 (:REWRITE DEFAULT-LESS-THAN-2))
     (43 43 (:REWRITE THE-FLOOR-BELOW))
     (43 43 (:REWRITE THE-FLOOR-ABOVE))
     (43 43
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (43 43 (:REWRITE CONSTANT-<-INTEGERP))
     (43 43
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (43 43
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (43 43
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (43 43
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (43 43 (:REWRITE |(< c (- x))|))
     (43 43
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (43 43
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (43 43
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (43 43
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (43 43 (:REWRITE |(< (/ x) (/ y))|))
     (43 43 (:REWRITE |(< (- x) c)|))
     (43 43 (:REWRITE |(< (- x) (- y))|))
     (43 9 (:REWRITE |(* y x)|))
     (41 27 (:REWRITE DEFAULT-TIMES-2))
     (40 40 (:REWRITE DEFAULT-PLUS-2))
     (36 36 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
     (36 36 (:TYPE-PRESCRIPTION ABS))
     (34 34 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (34 27 (:REWRITE DEFAULT-TIMES-1))
     (18 18
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (16 9
         (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (16 9 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (14 14
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (14 14
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (14 14 (:REWRITE |(equal c (/ x))|))
     (14 14 (:REWRITE |(equal (/ x) (/ y))|))
     (14 14 (:REWRITE |(equal (- x) (- y))|))
     (12 12 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (11 8
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (10 10 (:REWRITE REDUCE-INTEGERP-+))
     (10 10 (:REWRITE INTEGERP-MINUS-X))
     (10 10 (:META META-INTEGERP-CORRECT))
     (8 8 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (8 8
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (8 8 (:REWRITE |(equal c (- x))|))
     (8 8 (:REWRITE |(equal (- x) c)|))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (6 6 (:REWRITE DEFAULT-DIVIDE))
     (6 6 (:REWRITE |(not (equal x (/ y)))|))
     (6 6 (:REWRITE |(equal x (/ y))|))
     (6 6 (:REWRITE |(/ (/ x))|))
     (4 4
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (1 1 (:REWRITE |(< (/ x) 0)|))
     (1 1 (:REWRITE |(< (* x y) 0)|)))
(RTL::SRT-SQRT-RAD-4)
(RTL::MS8-0)
(RTL::MS8-1 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
            (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
            (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
            (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B)))
(RTL::MS8-2)
(RTL::MS8*64)
(RTL::MS8 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
          (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
          (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
          (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B)))
(RTL::SELECT-DIGIT-S8)
(RTL::I8%)
(RTL::APPROX8%)
(RTL::RATP-APPROX8%)
(RTL::APPROX8%-0)
(RTL::APPROX8%-BOUNDS)
(RTL::APPROX8%-INV (14 7
                       (:TYPE-PRESCRIPTION RTL::Q%-CONSTRAINT)))
(RTL::S8-INV)
(RTL::S8-HYP)
(RTL::REM%-8-BNDS-1
     (138 54 (:REWRITE SIMPLIFY-SUMS-<))
     (138 54
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (138 54 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (100 56 (:REWRITE DEFAULT-LESS-THAN-2))
     (100 56 (:REWRITE DEFAULT-LESS-THAN-1))
     (88 36 (:REWRITE DEFAULT-TIMES-2))
     (87 32
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (60 32 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (56 56 (:REWRITE THE-FLOOR-BELOW))
     (56 56 (:REWRITE THE-FLOOR-ABOVE))
     (54 54 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (54 54
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (54 54
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
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
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (54 54
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (54 54
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (54 54
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (54 54 (:REWRITE |(< (/ x) (/ y))|))
     (54 54 (:REWRITE |(< (- x) c)|))
     (54 54 (:REWRITE |(< (- x) (- y))|))
     (36 36 (:REWRITE DEFAULT-TIMES-1))
     (32 32
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (32 32
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (32 32
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (32 32 (:REWRITE |(equal c (/ x))|))
     (32 32 (:REWRITE |(equal c (- x))|))
     (32 32 (:REWRITE |(equal (/ x) c)|))
     (32 32 (:REWRITE |(equal (/ x) (/ y))|))
     (32 32 (:REWRITE |(equal (- x) c)|))
     (32 32 (:REWRITE |(equal (- x) (- y))|))
     (28 28
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (20 20
         (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
     (9 9 (:REWRITE ZP-OPEN))
     (9 9
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (9 9
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (9 9 (:REWRITE REDUCE-INTEGERP-+))
     (9 9 (:REWRITE INTEGERP-MINUS-X))
     (9 9 (:REWRITE |(< (/ x) 0)|))
     (9 9 (:REWRITE |(< (* x y) 0)|))
     (9 9 (:META META-INTEGERP-CORRECT))
     (8 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (7 7
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (7 7 (:REWRITE NORMALIZE-ADDENDS))
     (7 7 (:REWRITE DEFAULT-PLUS-2))
     (7 7 (:REWRITE DEFAULT-PLUS-1))
     (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A)))
(RTL::REM%-8-BNDS-2
     (84 24 (:REWRITE INTEGERP-<-CONSTANT))
     (80 10
         (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (60 24 (:REWRITE CONSTANT-<-INTEGERP))
     (46 1 (:REWRITE |(< x (/ y)) with (< 0 y)|))
     (44 44 (:REWRITE DEFAULT-PLUS-2))
     (44 44 (:REWRITE DEFAULT-PLUS-1))
     (43 1
         (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (39 37 (:REWRITE DEFAULT-TIMES-2))
     (38 37 (:REWRITE DEFAULT-TIMES-1))
     (36 36
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (34 34
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (34 34 (:REWRITE NORMALIZE-ADDENDS))
     (32 28
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (32 28
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (31 28 (:REWRITE DEFAULT-LESS-THAN-1))
     (28 28 (:REWRITE THE-FLOOR-BELOW))
     (28 28 (:REWRITE THE-FLOOR-ABOVE))
     (28 28 (:REWRITE DEFAULT-LESS-THAN-2))
     (28 24
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (27 24
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (27 24 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (25 23 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (24 24 (:REWRITE SIMPLIFY-SUMS-<))
     (24 24
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
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
     (24 24 (:REWRITE |(< (/ x) (/ y))|))
     (24 24 (:REWRITE |(< (- x) c)|))
     (24 24 (:REWRITE |(< (- x) (- y))|))
     (16 16 (:REWRITE |(< (+ c/d x) y)|))
     (16 16 (:REWRITE |(< (+ (- c) x) y)|))
     (12 12 (:REWRITE REDUCE-INTEGERP-+))
     (12 12 (:REWRITE INTEGERP-MINUS-X))
     (12 12 (:META META-INTEGERP-CORRECT))
     (10 10 (:REWRITE |(+ 0 x)|))
     (9 9
        (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
     (9 9 (:REWRITE ARITH-NORMALIZE-ADDENDS))
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (8 8 (:REWRITE |(< y (+ (- c) x))|))
     (8 8 (:REWRITE |(< x (+ c/d y))|))
     (8 8 (:REWRITE |(< (/ x) 0)|))
     (8 8 (:REWRITE |(< (* x y) 0)|))
     (7 3
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (5 1 (:REWRITE |(* y x)|))
     (4 4 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
     (4 4 (:TYPE-PRESCRIPTION ABS))
     (4 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
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
     (2 1
        (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (2 1
        (:REWRITE |(< x (/ y)) with (< y 0)|)))
(RTL::REM%-8-BNDS-3 (133 133
                         (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
                    (133 133
                         (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                    (133 133
                         (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                    (133 133
                         (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                    (46 21
                        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                    (21 21 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                    (21 21
                        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                    (21 21
                        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
                    (21 21
                        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
                    (21 21 (:REWRITE |(equal c (/ x))|))
                    (21 21 (:REWRITE |(equal c (- x))|))
                    (21 21 (:REWRITE |(equal (/ x) c)|))
                    (21 21 (:REWRITE |(equal (/ x) (/ y))|))
                    (21 21 (:REWRITE |(equal (- x) c)|))
                    (21 21 (:REWRITE |(equal (- x) (- y))|))
                    (3 3
                       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RTL::REM%-8-BNDS-4
     (81 36 (:REWRITE DEFAULT-PLUS-2))
     (53 36 (:REWRITE DEFAULT-PLUS-1))
     (51 23
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (29 29 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (29 29 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (29 29 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (26 10 (:REWRITE DEFAULT-TIMES-2))
     (23 23 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (23 23
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (23 23
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (23 23
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (23 23 (:REWRITE |(equal c (/ x))|))
     (23 23 (:REWRITE |(equal c (- x))|))
     (23 23 (:REWRITE |(equal (/ x) c)|))
     (23 23 (:REWRITE |(equal (/ x) (/ y))|))
     (23 23 (:REWRITE |(equal (- x) c)|))
     (23 23 (:REWRITE |(equal (- x) (- y))|))
     (18 18
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (18 18 (:REWRITE NORMALIZE-ADDENDS))
     (13 3 (:REWRITE DEFAULT-LESS-THAN-2))
     (12 10 (:REWRITE DEFAULT-TIMES-1))
     (12 2
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (12 2 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (8 3 (:REWRITE DEFAULT-LESS-THAN-1))
     (7 7
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (6 1
        (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (3 3 (:REWRITE THE-FLOOR-BELOW))
     (3 3 (:REWRITE THE-FLOOR-ABOVE))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (3 3
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (3 3
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (2 2 (:REWRITE SIMPLIFY-SUMS-<))
     (2 2 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (2 2 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (2 2 (:REWRITE INTEGERP-<-CONSTANT))
     (2 2 (:REWRITE CONSTANT-<-INTEGERP))
     (2 2 (:REWRITE |(< y (+ (- c) x))|))
     (2 2 (:REWRITE |(< x (+ c/d y))|))
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
     (1 1 (:REWRITE |(< (+ c/d x) y)|))
     (1 1 (:REWRITE |(< (+ (- c) x) y)|)))
(RTL::REM%-8-BNDS-5 (27 27 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                    (27 27 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                    (27 27 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                    (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
                    (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
                    (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
                    (17 5 (:REWRITE DEFAULT-TIMES-2))
                    (14 5 (:REWRITE DEFAULT-PLUS-2))
                    (6 5 (:REWRITE DEFAULT-TIMES-1))
                    (6 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
                    (5 5 (:REWRITE DEFAULT-PLUS-1))
                    (5 2
                       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                    (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                    (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                    (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                    (3 3
                       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                    (3 3
                       (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                    (3 3 (:REWRITE NORMALIZE-ADDENDS))
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
                    (2 2 (:REWRITE |(equal (- x) (- y))|)))
(RTL::REM%-8-BNDS-6 (126 42 (:REWRITE DEFAULT-TIMES-2))
                    (108 42 (:REWRITE DEFAULT-PLUS-2))
                    (54 54 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                    (54 54 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                    (54 54 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                    (48 42 (:REWRITE DEFAULT-TIMES-1))
                    (45 45 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
                    (45 45 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
                    (45 45 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
                    (43 23
                        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                    (42 42 (:REWRITE DEFAULT-PLUS-1))
                    (36 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
                    (30 30
                        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                    (30 30
                        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                    (30 30 (:REWRITE NORMALIZE-ADDENDS))
                    (23 23 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                    (23 23
                        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                    (23 23
                        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
                    (23 23
                        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
                    (23 23 (:REWRITE |(equal c (/ x))|))
                    (23 23 (:REWRITE |(equal c (- x))|))
                    (23 23 (:REWRITE |(equal (/ x) c)|))
                    (23 23 (:REWRITE |(equal (/ x) (/ y))|))
                    (23 23 (:REWRITE |(equal (- x) c)|))
                    (23 23 (:REWRITE |(equal (- x) (- y))|))
                    (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                    (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                    (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                    (11 11 (:REWRITE |(equal (+ (- c) x) y)|))
                    (2 2
                       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RTL::Q%-8-VALS
     (39 39
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (39 39
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (39 39 (:REWRITE |(equal c (/ x))|))
     (39 39 (:REWRITE |(equal c (- x))|))
     (39 39 (:REWRITE |(equal (/ x) c)|))
     (39 39 (:REWRITE |(equal (/ x) (/ y))|))
     (39 39 (:REWRITE |(equal (- x) (- y))|))
     (32 32 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (32 32
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (32 32
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (24 24 (:TYPE-PRESCRIPTION ZP))
     (24 12
         (:TYPE-PRESCRIPTION RTL::Q%-CONSTRAINT))
     (21 21 (:REWRITE DEFAULT-MINUS))
     (14 12 (:REWRITE DEFAULT-LESS-THAN-2))
     (13 12 (:REWRITE DEFAULT-LESS-THAN-1))
     (12 12 (:REWRITE THE-FLOOR-BELOW))
     (12 12 (:REWRITE THE-FLOOR-ABOVE))
     (11 11
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (11 11
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (11 11
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (11 11
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (11 11
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (11 11
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (11 11
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (11 11
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (11 11
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (11 11
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (11 11 (:REWRITE |(< (/ x) (/ y))|))
     (11 11 (:REWRITE |(< (- x) (- y))|))
     (9 8
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (9 8 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (8 8 (:REWRITE SIMPLIFY-SUMS-<))
     (8 8 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (8 8 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (8 8 (:REWRITE INTEGERP-<-CONSTANT))
     (8 8 (:REWRITE CONSTANT-<-INTEGERP))
     (4 4 (:REWRITE |(< (/ x) 0)|))
     (4 4 (:REWRITE |(< (* x y) 0)|))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (1 1 (:REWRITE |(< 0 (/ x))|))
     (1 1 (:REWRITE |(< 0 (* x y))|)))
(RTL::REM%-8-BNDS-7
     (31683 19502 (:REWRITE DEFAULT-PLUS-2))
     (26103 19502 (:REWRITE DEFAULT-PLUS-1))
     (12537 6615 (:REWRITE DEFAULT-TIMES-2))
     (12130 12130
            (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (12130 12130 (:REWRITE NORMALIZE-ADDENDS))
     (11675 6103
            (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (10368 360 (:REWRITE |(< (+ c/d x) y)|))
     (7533 81
           (:REWRITE |(< x (/ y)) with (< 0 y)|))
     (7290 81
           (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (6696 6615 (:REWRITE DEFAULT-TIMES-1))
     (6246 6246
           (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (6103 6103 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (6103 6103
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (6103 6103
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (6103 6103
           (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (6103 6103 (:REWRITE |(equal c (/ x))|))
     (6103 6103 (:REWRITE |(equal c (- x))|))
     (6103 6103 (:REWRITE |(equal (/ x) c)|))
     (6103 6103 (:REWRITE |(equal (/ x) (/ y))|))
     (6103 6103 (:REWRITE |(equal (- x) c)|))
     (6103 6103 (:REWRITE |(equal (- x) (- y))|))
     (5427 5427 (:REWRITE |(equal (+ (- c) x) y)|))
     (2772 216 (:REWRITE |(< (+ (- c) x) y)|))
     (1872 144 (:REWRITE |(* y (* x z))|))
     (1134 324 (:REWRITE INTEGERP-<-CONSTANT))
     (1125 81 (:REWRITE |(* y x)|))
     (999 540 (:REWRITE DEFAULT-LESS-THAN-1))
     (720 144 (:REWRITE |(* c (* d x))|))
     (576 396
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (576 396
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (567 324
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (567 324
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (540 540 (:REWRITE THE-FLOOR-BELOW))
     (540 540 (:REWRITE THE-FLOOR-ABOVE))
     (540 540 (:REWRITE DEFAULT-LESS-THAN-2))
     (468 108
          (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (324 324 (:REWRITE SIMPLIFY-SUMS-<))
     (324 324
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (324 324 (:REWRITE CONSTANT-<-INTEGERP))
     (324 324
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (324 324
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (324 324
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (324 324
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (324 324 (:REWRITE |(< c (- x))|))
     (324 324
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (324 324
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (324 324
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (324 324
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (324 324 (:REWRITE |(< (/ x) (/ y))|))
     (324 324 (:REWRITE |(< (- x) c)|))
     (324 324 (:REWRITE |(< (- x) (- y))|))
     (281 281
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (243 243 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (180 180 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
     (180 180 (:TYPE-PRESCRIPTION ABS))
     (162 81
          (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (162 81
          (:REWRITE |(< x (/ y)) with (< y 0)|))
     (81 81 (:REWRITE REDUCE-INTEGERP-+))
     (81 81 (:REWRITE INTEGERP-MINUS-X))
     (81 81 (:META META-INTEGERP-CORRECT))
     (72 72 (:REWRITE |(< y (+ (- c) x))|))
     (72 72 (:REWRITE |(< x (+ c/d y))|)))
(RTL::REM%-8-BNDS-8
     (4310 180 (:REWRITE |(< (+ c/d x) y)|))
     (4204 172 (:REWRITE |(< x (+ c/d y))|))
     (3511 1583 (:REWRITE DEFAULT-TIMES-2))
     (2750 30
           (:REWRITE |(< x (/ y)) with (< 0 y)|))
     (2678 1263 (:REWRITE DEFAULT-PLUS-2))
     (2675 30
           (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (2664 30
           (:REWRITE |(< (/ x) y) with (< 0 x)|))
     (2138 162 (:REWRITE |(* y (* x z))|))
     (1895 120 (:REWRITE |(< (+ (- c) x) y)|))
     (1783 1263 (:REWRITE DEFAULT-PLUS-1))
     (1749 116 (:REWRITE |(< y (+ (- c) x))|))
     (1702 1583 (:REWRITE DEFAULT-TIMES-1))
     (1210 234 (:REWRITE INTEGERP-<-CONSTANT))
     (1180 234 (:REWRITE CONSTANT-<-INTEGERP))
     (1036 120 (:REWRITE INTEGERP-MINUS-X))
     (1017 1017
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (1017 1017
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (1017 1017
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (1001 1001
           (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (880 176
          (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (854 854
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (803 30
          (:REWRITE |(< x (/ y)) with (< y 0)|))
     (763 30
          (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (738 448 (:REWRITE DEFAULT-LESS-THAN-2))
     (700 30
          (:REWRITE |(<= x (/ y)) with (< y 0)|))
     (698 448 (:REWRITE DEFAULT-LESS-THAN-1))
     (670 30
          (:REWRITE |(< (/ x) y) with (< x 0)|))
     (550 550
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (550 550
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (550 550
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (524 332
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (524 332
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (524 234
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (448 448 (:REWRITE THE-FLOOR-BELOW))
     (448 448 (:REWRITE THE-FLOOR-ABOVE))
     (396 28 (:REWRITE |(- (+ x y))|))
     (383 196
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (234 234
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (234 234
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (234 234
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (234 234
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (234 234
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (234 234 (:REWRITE |(< c (- x))|))
     (234 234
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (234 234
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (234 234
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (234 234
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (234 234 (:REWRITE |(< (/ x) (/ y))|))
     (234 234 (:REWRITE |(< (- x) c)|))
     (234 234 (:REWRITE |(< (- x) (- y))|))
     (196 196 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (196 196
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (196 196
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (196 196
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (196 196 (:REWRITE |(equal c (/ x))|))
     (196 196 (:REWRITE |(equal c (- x))|))
     (196 196 (:REWRITE |(equal (/ x) c)|))
     (196 196 (:REWRITE |(equal (/ x) (/ y))|))
     (196 196 (:REWRITE |(equal (- x) c)|))
     (196 196 (:REWRITE |(equal (- x) (- y))|))
     (194 194 (:REWRITE SIMPLIFY-SUMS-<))
     (192 192 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
     (192 192 (:TYPE-PRESCRIPTION ABS))
     (176 176 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (152 152 (:REWRITE |(* (- x) y)|))
     (144 56 (:REWRITE DEFAULT-MINUS))
     (140 28 (:REWRITE |(- (* c x))|))
     (100 40 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (92 92 (:REWRITE REDUCE-INTEGERP-+))
     (92 92 (:META META-INTEGERP-CORRECT))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
     (12 12
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (11 11 (:REWRITE |(equal (+ (- c) x) y)|))
     (10 10 (:REWRITE |(* x (- y))|)))
(RTL::REM%-8-BNDS-9
     (27686 1164 (:REWRITE |(< x (+ c/d y))|))
     (27441 1166 (:REWRITE |(< (+ c/d x) y)|))
     (22473 10273 (:REWRITE DEFAULT-TIMES-2))
     (19277 194
            (:REWRITE |(<= x (/ y)) with (< 0 y)|))
     (18206 194
            (:REWRITE |(< (/ x) y) with (< 0 x)|))
     (17789 194
            (:REWRITE |(< x (/ y)) with (< 0 y)|))
     (17300 194
            (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (17142 8185 (:REWRITE DEFAULT-PLUS-2))
     (12918 978 (:REWRITE |(* y (* x z))|))
     (12357 784 (:REWRITE |(< y (+ (- c) x))|))
     (12357 784 (:REWRITE |(< (+ (- c) x) y)|))
     (11617 8185 (:REWRITE DEFAULT-PLUS-1))
     (11042 10273 (:REWRITE DEFAULT-TIMES-1))
     (9914 1568 (:REWRITE INTEGERP-<-CONSTANT))
     (9792 1568 (:REWRITE CONSTANT-<-INTEGERP))
     (9293 1046 (:REWRITE INTEGERP-MINUS-X))
     (8738 8738
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (8738 8738
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (8738 8738
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (7714 1550
           (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (6571 6571
           (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (5393 5393
           (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (4901 194
           (:REWRITE |(< x (/ y)) with (< y 0)|))
     (4864 2982 (:REWRITE DEFAULT-LESS-THAN-2))
     (4653 194
           (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (4606 2982 (:REWRITE DEFAULT-LESS-THAN-1))
     (4411 2202
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (4358 194
           (:REWRITE |(<= x (/ y)) with (< y 0)|))
     (4172 194
           (:REWRITE |(< (/ x) y) with (< x 0)|))
     (3602 258 (:REWRITE |(- (+ x y))|))
     (3532 1568
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (3524 2220
           (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (3524 2220
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (3299 3299
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (3299 3299
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (3299 3299
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (2982 2982 (:REWRITE THE-FLOOR-BELOW))
     (2982 2982 (:REWRITE THE-FLOOR-ABOVE))
     (2418 2274
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (2202 2202 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (2202 2202
           (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (2202 2202 (:REWRITE |(equal c (/ x))|))
     (2202 2202 (:REWRITE |(equal c (- x))|))
     (2202 2202 (:REWRITE |(equal (/ x) c)|))
     (2202 2202 (:REWRITE |(equal (/ x) (/ y))|))
     (2202 2202 (:REWRITE |(equal (- x) c)|))
     (2202 2202 (:REWRITE |(equal (- x) (- y))|))
     (1568 1568
           (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (1568 1568
           (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (1568 1568
           (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (1568 1568
           (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (1568 1568
           (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (1568 1568 (:REWRITE |(< c (- x))|))
     (1568 1568
           (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (1568 1568
           (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (1568 1568
           (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (1568 1568
           (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (1568 1568 (:REWRITE |(< (/ x) (/ y))|))
     (1568 1568 (:REWRITE |(< (- x) c)|))
     (1568 1568 (:REWRITE |(< (- x) (- y))|))
     (1376 1376 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
     (1376 1376 (:TYPE-PRESCRIPTION ABS))
     (1304 1304 (:REWRITE SIMPLIFY-SUMS-<))
     (1290 258 (:REWRITE |(- (* c x))|))
     (1280 516 (:REWRITE DEFAULT-MINUS))
     (1180 1180
           (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (980 980 (:REWRITE |(* (- x) y)|))
     (788 788 (:REWRITE REDUCE-INTEGERP-+))
     (788 788 (:META META-INTEGERP-CORRECT))
     (660 264 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (127 127
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (125 4 (:REWRITE EVEN-AND-ODD-ALTERNATE))
     (67 67 (:REWRITE |(equal (+ (- c) x) y)|))
     (62 62 (:REWRITE |(* x (- y))|))
     (9 9 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
     (9 9 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
     (9 9 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E)))
(RTL::REM%-8-BNDS-10
 (10101 1130 (:REWRITE DEFAULT-PLUS-2))
 (5784 699
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (5784 699
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (4232
  4232
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (4232
      4232
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (4232
     4232
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (4232 4232
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (4099 1130 (:REWRITE DEFAULT-PLUS-1))
 (3045 256 (:REWRITE DEFAULT-LESS-THAN-2))
 (2914 214
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (1853 256 (:REWRITE DEFAULT-LESS-THAN-1))
 (1652 313 (:REWRITE DEFAULT-MINUS))
 (1581 699
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (1581 699
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (1281 255 (:REWRITE DEFAULT-TIMES-2))
 (891 27 (:REWRITE ZP-OPEN))
 (556 137 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (499 499
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (339 255 (:REWRITE DEFAULT-TIMES-1))
 (312 231 (:REWRITE |(< (- x) (- y))|))
 (262 262 (:TYPE-PRESCRIPTION ZP))
 (262 131
      (:TYPE-PRESCRIPTION RTL::Q%-CONSTRAINT))
 (256 256 (:REWRITE THE-FLOOR-BELOW))
 (256 256 (:REWRITE THE-FLOOR-ABOVE))
 (239 231 (:REWRITE |(< c (- x))|))
 (231 231
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (231 231
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (231 231
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (231 231
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (231 231
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (231 231
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (231 231
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (231 231
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (231 231
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (231 231
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (231 231 (:REWRITE |(< (/ x) (/ y))|))
 (223 223
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (223 223 (:REWRITE INTEGERP-<-CONSTANT))
 (223 223 (:REWRITE CONSTANT-<-INTEGERP))
 (199 199
      (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
 (170 170 (:REWRITE |arith (expt x c)|))
 (141 141 (:REWRITE |(< (+ c/d x) y)|))
 (141 141 (:REWRITE |(< (+ (- c) x) y)|))
 (135 27 (:REWRITE |(* y x)|))
 (127 127 (:REWRITE |(< y (+ (- c) x))|))
 (127 127 (:REWRITE |(< x (+ c/d y))|))
 (109 109 (:REWRITE DEFAULT-EXPT-2))
 (109 109 (:REWRITE DEFAULT-EXPT-1))
 (109 109 (:REWRITE |(expt 1/c n)|))
 (109 109 (:REWRITE |(expt (- x) n)|))
 (102 102 (:REWRITE FOLD-CONSTS-IN-+))
 (85 85 (:REWRITE |arith (expt 1/c n)|))
 (85 85 (:REWRITE |arith (* (- x) y)|))
 (74 37
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (54 27 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (46 46 (:REWRITE |(* (- x) y)|))
 (37 37 (:REWRITE SIMPLIFY-SUMS-EQUAL))
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
 (36 36 (:REWRITE |(< (/ x) 0)|))
 (36 36 (:REWRITE |(< (* x y) 0)|))
 (36 9 (:REWRITE RATIONALP-X))
 (35 35 (:REWRITE |(< 0 (/ x))|))
 (35 35 (:REWRITE |(< 0 (* x y))|))
 (30 30 (:REWRITE |arith (+ c (+ d x))|))
 (27 27 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (27 27 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (27 27 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (27 27
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (27 27
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (18 18 (:REWRITE REDUCE-INTEGERP-+))
 (18 18 (:REWRITE INTEGERP-MINUS-X))
 (18 18 (:META META-INTEGERP-CORRECT))
 (9 9 (:REWRITE REDUCE-RATIONALP-+))
 (9 9 (:REWRITE REDUCE-RATIONALP-*))
 (9 9 (:REWRITE RATIONALP-MINUS-X))
 (9 9 (:META META-RATIONALP-CORRECT))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RTL::REM%-8-BNDS-11
 (252 27
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (252 27
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (229
  229
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (229 229
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (229
     229
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (229 229
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (221 28 (:REWRITE DEFAULT-TIMES-2))
 (168 22 (:REWRITE DEFAULT-PLUS-2))
 (110 11 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (88 22 (:REWRITE DEFAULT-PLUS-1))
 (74 12 (:REWRITE DEFAULT-MINUS))
 (60 60 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (60 60 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (60 60 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (57 28 (:REWRITE DEFAULT-TIMES-1))
 (27 27
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (27 27
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (16 16
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (16 16 (:REWRITE NORMALIZE-ADDENDS))
 (11 11 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (11 11 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (11 11 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (6 6 (:REWRITE DEFAULT-EXPT-2))
 (6 6 (:REWRITE DEFAULT-EXPT-1))
 (6 6 (:REWRITE |(expt 1/c n)|))
 (6 6 (:REWRITE |(expt (- x) n)|))
 (5 5 (:REWRITE |(* (- x) y)|))
 (5 2
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (3 3 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (2 2 (:REWRITE THE-FLOOR-BELOW))
 (2 2 (:REWRITE THE-FLOOR-ABOVE))
 (2 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (2 2 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (2 2
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (2 2
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (2 2
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (2 2
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (2 2 (:REWRITE INTEGERP-<-CONSTANT))
 (2 2
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (2 2 (:REWRITE DEFAULT-LESS-THAN-2))
 (2 2 (:REWRITE DEFAULT-LESS-THAN-1))
 (2 2 (:REWRITE CONSTANT-<-INTEGERP))
 (2 2 (:REWRITE |(equal c (/ x))|))
 (2 2 (:REWRITE |(equal c (- x))|))
 (2 2 (:REWRITE |(equal (/ x) c)|))
 (2 2 (:REWRITE |(equal (/ x) (/ y))|))
 (2 2 (:REWRITE |(equal (- x) c)|))
 (2 2 (:REWRITE |(equal (- x) (- y))|))
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
 (1 1 (:REWRITE SIMPLIFY-SUMS-<))
 (1 1
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (1 1 (:REWRITE REDUCE-INTEGERP-+))
 (1 1 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (1 1 (:REWRITE INTEGERP-MINUS-X))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (* x y) 0)|))
 (1 1 (:META META-INTEGERP-CORRECT)))
(RTL::REM%-8-BNDS-12
 (714 38
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (222 26 (:REWRITE CONSTANT-<-INTEGERP))
 (211 3 (:LINEAR EXPT-X->=-X))
 (211 3 (:LINEAR EXPT-X->-X))
 (134 3 (:LINEAR EXPT->=-1-ONE))
 (134 3 (:LINEAR EXPT-<=-1-TWO))
 (132 12 (:REWRITE |(* y (* x z))|))
 (131 3 (:LINEAR EXPT->-1-ONE))
 (131 3 (:LINEAR EXPT-<-1-TWO))
 (85 37 (:REWRITE DEFAULT-TIMES-2))
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
 (38 38 (:REWRITE THE-FLOOR-BELOW))
 (38 38 (:REWRITE THE-FLOOR-ABOVE))
 (38 38 (:REWRITE DEFAULT-LESS-THAN-2))
 (38 38 (:REWRITE DEFAULT-LESS-THAN-1))
 (37 37 (:REWRITE DEFAULT-TIMES-1))
 (26 26
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
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
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (26 26
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (26 26
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (26 26
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (26 26 (:REWRITE |(< (/ x) (/ y))|))
 (26 26 (:REWRITE |(< (- x) c)|))
 (26 26 (:REWRITE |(< (- x) (- y))|))
 (22 22 (:REWRITE SIMPLIFY-SUMS-<))
 (22 22
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (22 22
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (22 22 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (22 22 (:REWRITE INTEGERP-<-CONSTANT))
 (14 14 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (13 13
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (12 12 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (12 12 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (12 12 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (12 12 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (12 12 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
 (12 12 (:TYPE-PRESCRIPTION ABS))
 (12 12 (:REWRITE |(* a (/ a) b)|))
 (10 10 (:REWRITE |(< 0 (* x y))|))
 (10 10 (:REWRITE |(< (* x y) 0)|))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (6 6 (:REWRITE |(< 0 (/ x))|))
 (6 6 (:REWRITE |(< (/ x) 0)|))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (6 6
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (4 4 (:REWRITE |(< (/ x) y) with (< x 0)|))
 (4 4 (:REWRITE |(< (/ x) y) with (< 0 x)|))
 (4 4
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
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
 (1 1 (:REWRITE REDUCE-INTEGERP-+))
 (1 1 (:REWRITE INTEGERP-MINUS-X))
 (1 1 (:META META-INTEGERP-CORRECT)))
(RTL::REM%-8-BNDS-13
 (821 37 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (292 4 (:LINEAR EXPT->=-1-ONE))
 (288 4 (:LINEAR EXPT-X->=-X))
 (288 4 (:LINEAR EXPT-X->-X))
 (284 4 (:LINEAR EXPT->-1-ONE))
 (201 109 (:REWRITE DEFAULT-PLUS-1))
 (199
  199
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (199 199
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (199
     199
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (199 199
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (190 109 (:REWRITE DEFAULT-PLUS-2))
 (58 13 (:REWRITE DEFAULT-TIMES-2))
 (39 21 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (38 38 (:REWRITE THE-FLOOR-BELOW))
 (38 38 (:REWRITE THE-FLOOR-ABOVE))
 (38 38
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (38 38
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (38 38
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (38 38 (:REWRITE INTEGERP-<-CONSTANT))
 (38 38 (:REWRITE DEFAULT-LESS-THAN-2))
 (38 38 (:REWRITE DEFAULT-LESS-THAN-1))
 (38 38 (:REWRITE CONSTANT-<-INTEGERP))
 (38 38
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (38 38
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (38 38
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (38 38
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (38 38 (:REWRITE |(< c (- x))|))
 (38 38
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (38 38
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (38 38
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (38 38
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (38 38 (:REWRITE |(< (/ x) (/ y))|))
 (38 38 (:REWRITE |(< (- x) c)|))
 (38 38 (:REWRITE |(< (- x) (- y))|))
 (37 37
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (21 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (19 19 (:REWRITE SIMPLIFY-SUMS-<))
 (18 18
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (18 18 (:REWRITE |(+ x (- x))|))
 (18 9 (:REWRITE DEFAULT-MINUS))
 (14 14 (:REWRITE |(< (+ c/d x) y)|))
 (14 14 (:REWRITE |(< (+ (- c) x) y)|))
 (14 13 (:REWRITE DEFAULT-TIMES-1))
 (12 12 (:REWRITE DEFAULT-EXPT-2))
 (12 12 (:REWRITE DEFAULT-EXPT-1))
 (12 12 (:REWRITE |(expt 1/c n)|))
 (12 12 (:REWRITE |(expt (- x) n)|))
 (12 12 (:REWRITE |(< y (+ (- c) x))|))
 (12 12 (:REWRITE |(< x (+ c/d y))|))
 (8 8
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (8 8
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (8 8
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (8 8
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (7 7 (:REWRITE |(< (/ x) 0)|))
 (7 7 (:REWRITE |(< (* x y) 0)|))
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
 (4 4 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (4 4 (:LINEAR EXPT-LINEAR-UPPER-<))
 (4 4 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (4 4 (:LINEAR EXPT-LINEAR-LOWER-<))
 (4 4 (:LINEAR EXPT->=-1-TWO))
 (4 4 (:LINEAR EXPT->-1-TWO))
 (4 4 (:LINEAR EXPT-<=-1-ONE))
 (4 4 (:LINEAR EXPT-<-1-ONE))
 (3 3 (:REWRITE |(* (- x) y)|))
 (1 1 (:REWRITE REDUCE-INTEGERP-+))
 (1 1 (:REWRITE INTEGERP-MINUS-X))
 (1 1 (:REWRITE |(equal (expt 2 n) c)|))
 (1 1 (:REWRITE |(equal (+ (- c) x) y)|))
 (1 1 (:META META-INTEGERP-CORRECT)))
(RTL::REM%-8-BNDS-14)
(RTL::REM%-8-BNDS-15
 (95 95 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (95 95 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (95 95 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (95
  95
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (95 95
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (95 95
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (95 95
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (95 95
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE)))
(RTL::REM%-8-BNDS-16
 (1617 7 (:REWRITE |(< (/ x) y) with (< 0 x)|))
 (1547 7
       (:REWRITE |(<= x (/ y)) with (< 0 y)|))
 (882 91 (:REWRITE DEFAULT-TIMES-2))
 (691
  691
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (691 691
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (691
     691
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (691 691
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (691 691
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (624 96 (:REWRITE DEFAULT-PLUS-2))
 (611 96 (:REWRITE DEFAULT-PLUS-1))
 (449 37 (:REWRITE CONSTANT-<-INTEGERP))
 (436 33
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (366 37 (:REWRITE DEFAULT-LESS-THAN-2))
 (349 349
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (349 349
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (349 349
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (273 91 (:REWRITE DEFAULT-TIMES-1))
 (191 29 (:REWRITE DEFAULT-MINUS))
 (175 175
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (175 175
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (175 175
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (140 14 (:REWRITE |(* a (/ a) b)|))
 (128 37 (:REWRITE DEFAULT-LESS-THAN-1))
 (126 7
      (:REWRITE |(<= x (/ y)) with (< y 0)|))
 (126 7 (:REWRITE |(< (/ x) y) with (< x 0)|))
 (100 8 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (59 59
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (49 49
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (37 37 (:REWRITE THE-FLOOR-BELOW))
 (37 37 (:REWRITE THE-FLOOR-ABOVE))
 (37 37
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (37 37
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (37 37
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (37 37 (:REWRITE INTEGERP-<-CONSTANT))
 (37 37
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (37 37
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (37 37
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (37 37
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (37 37 (:REWRITE |(< c (- x))|))
 (37 37
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (37 37
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (37 37
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (37 37
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (37 37 (:REWRITE |(< (/ x) (/ y))|))
 (37 37 (:REWRITE |(< (- x) c)|))
 (37 37 (:REWRITE |(< (- x) (- y))|))
 (26 26 (:REWRITE SIMPLIFY-SUMS-<))
 (21 21 (:REWRITE |(< y (+ (- c) x))|))
 (21 21 (:REWRITE |(< x (+ c/d y))|))
 (15 6
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (14 14
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (14 14
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (14 14
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (14 14
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (10 10 (:REWRITE REDUCE-INTEGERP-+))
 (10 10 (:REWRITE INTEGERP-MINUS-X))
 (10 10 (:META META-INTEGERP-CORRECT))
 (9 9 (:REWRITE |(< (+ c/d x) y)|))
 (9 9 (:REWRITE |(< (+ (- c) x) y)|))
 (7 7 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (7 7 (:REWRITE DEFAULT-EXPT-2))
 (7 7 (:REWRITE DEFAULT-EXPT-1))
 (7 7 (:REWRITE |(expt 1/c n)|))
 (7 7 (:REWRITE |(expt (- x) n)|))
 (7 7 (:REWRITE |(* (- x) y)|))
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
 (7 7 (:LINEAR EXPT-<=-1-TWO))
 (7 7 (:LINEAR EXPT-<=-1-ONE))
 (7 7 (:LINEAR EXPT-<-1-TWO))
 (7 7 (:LINEAR EXPT-<-1-ONE))
 (6 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
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
 (3 3 (:REWRITE |(< (/ x) 0)|))
 (3 3 (:REWRITE |(< (* x y) 0)|)))
(RTL::REM%-8-BNDS-17
 (4665 2
       (:REWRITE |(<= x (/ y)) with (< 0 y)|))
 (4657 2 (:REWRITE |(< (/ x) y) with (< 0 x)|))
 (3856 400
       (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
 (800
  800
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (800 800
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (800
     800
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (800 800
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (800 800
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (707 124 (:REWRITE DEFAULT-PLUS-2))
 (672 96
      (:REWRITE ARITH-BUBBLE-DOWN-*-MATCH-1))
 (576 96
      (:REWRITE |arith (* (expt x m) (expt x n))|))
 (521 137 (:REWRITE ARITH-NORMALIZE-ADDENDS))
 (352 124 (:REWRITE DEFAULT-PLUS-1))
 (350 350 (:REWRITE |arith (expt x c)|))
 (337 67 (:REWRITE DEFAULT-TIMES-2))
 (333 2 (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (330 330 (:REWRITE |arith (expt 1/c n)|))
 (327 2
      (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (288 96
      (:REWRITE ARITH-BUBBLE-DOWN-+-MATCH-1))
 (284 32 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (284 32 (:LINEAR EXPT-<=-1-TWO))
 (280 32 (:LINEAR EXPT-X->-X))
 (280 32 (:LINEAR EXPT->-1-ONE))
 (280 32 (:LINEAR EXPT-<-1-TWO))
 (248 34
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (221 37 (:REWRITE CONSTANT-<-INTEGERP))
 (208 32 (:LINEAR EXPT-X->=-X))
 (208 32 (:LINEAR EXPT->=-1-ONE))
 (203 38 (:REWRITE DEFAULT-LESS-THAN-2))
 (192 96
      (:REWRITE |arith (+ (* c x) (* d x))|))
 (159 159
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (159 159
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (159 159
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (122 122 (:REWRITE |arith (* (- x) y)|))
 (110 67 (:REWRITE DEFAULT-TIMES-1))
 (110 38 (:REWRITE DEFAULT-LESS-THAN-1))
 (109 17 (:REWRITE SIMPLIFY-SUMS-<))
 (96 96 (:REWRITE |arith (* 0 x)|))
 (90 12 (:META META-INTEGERP-CORRECT))
 (64 64
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (64 64
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (64 64
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (64 64
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (61 20 (:REWRITE DEFAULT-MINUS))
 (59 37 (:REWRITE INTEGERP-<-CONSTANT))
 (58 17 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (42 37 (:REWRITE |(< (- x) c)|))
 (42 37 (:REWRITE |(< (- x) (- y))|))
 (40 4 (:REWRITE |(* a (/ a) b)|))
 (39 39
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (39 39
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (39 37 (:REWRITE |(< c (- x))|))
 (38 38 (:REWRITE THE-FLOOR-BELOW))
 (38 38 (:REWRITE THE-FLOOR-ABOVE))
 (37 37
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (37 37
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (37 37
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (37 37
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (37 37
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (37 37
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (37 37
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (37 37
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (37 37
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (37 37
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (37 37
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (37 37 (:REWRITE |(< (/ x) (/ y))|))
 (32 32 (:LINEAR EXPT-LINEAR-UPPER-<))
 (32 32 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (32 32 (:LINEAR EXPT-LINEAR-LOWER-<))
 (32 32 (:LINEAR EXPT->=-1-TWO))
 (32 32 (:LINEAR EXPT->-1-TWO))
 (32 32 (:LINEAR EXPT-<=-1-ONE))
 (32 32 (:LINEAR EXPT-<-1-ONE))
 (32 2
     (:REWRITE |(<= x (/ y)) with (< y 0)|))
 (32 2 (:REWRITE |(< (/ x) y) with (< x 0)|))
 (20 20 (:REWRITE |(< y (+ (- c) x))|))
 (20 20 (:REWRITE |(< x (+ c/d y))|))
 (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (18 18 (:REWRITE |(+ c (+ d x))|))
 (17 17 (:REWRITE |(< (+ c/d x) y)|))
 (17 17 (:REWRITE |(< (+ (- c) x) y)|))
 (16 12 (:REWRITE INTEGERP-MINUS-X))
 (14 2 (:REWRITE |(integerp (- x))|))
 (12 12 (:REWRITE REDUCE-INTEGERP-+))
 (10 4
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (9 9 (:REWRITE |(* (- x) y)|))
 (6 6 (:REWRITE FOLD-CONSTS-IN-+))
 (6 2
    (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (6 2 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (5 5 (:REWRITE |(< (/ x) 0)|))
 (5 5 (:REWRITE |(< (* x y) 0)|))
 (4 4 (:REWRITE |arith (+ c (+ d x))|))
 (4 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (4 4
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (4 4
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (4 4 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (4 4
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (4 4 (:REWRITE |(equal c (/ x))|))
 (4 4 (:REWRITE |(equal c (- x))|))
 (4 4 (:REWRITE |(equal (/ x) c)|))
 (4 4 (:REWRITE |(equal (/ x) (/ y))|))
 (4 4 (:REWRITE |(equal (- x) c)|))
 (4 4 (:REWRITE |(equal (- x) (- y))|))
 (1 1 (:REWRITE DEFAULT-EXPT-2))
 (1 1 (:REWRITE DEFAULT-EXPT-1))
 (1 1 (:REWRITE |(expt 1/c n)|))
 (1 1 (:REWRITE |(expt (- x) n)|)))
(RTL::QMIN8 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
            (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
            (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
            (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B)))
(RTL::QMAX8 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
            (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
            (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
            (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B)))
(RTL::REM%-8-BNDS-18
     (612 6 (:REWRITE |(< x (/ y)) with (< 0 y)|))
     (317 19 (:REWRITE |(< (+ c/d x) y)|))
     (282 12 (:REWRITE |(* x (+ y z))|))
     (253 253
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (253 253
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (253 253
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (193 78 (:REWRITE DEFAULT-TIMES-2))
     (162 162
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (162 162
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (162 162
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (147 65 (:REWRITE DEFAULT-PLUS-2))
     (140 52 (:REWRITE DEFAULT-LESS-THAN-1))
     (108 41 (:REWRITE INTEGERP-<-CONSTANT))
     (96 78 (:REWRITE DEFAULT-TIMES-1))
     (96 52 (:REWRITE DEFAULT-LESS-THAN-2))
     (87 65 (:REWRITE DEFAULT-PLUS-1))
     (84 36
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (52 52 (:REWRITE THE-FLOOR-BELOW))
     (52 52 (:REWRITE THE-FLOOR-ABOVE))
     (52 4 (:REWRITE |(* y (* x z))|))
     (51 43
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (51 43
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (47 47
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (46 4 (:REWRITE |(* x (- y))|))
     (43 41 (:REWRITE |(< (- x) c)|))
     (43 41 (:REWRITE |(< (- x) (- y))|))
     (43 29 (:REWRITE SIMPLIFY-SUMS-<))
     (41 41
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
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
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (41 41
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (41 41
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (41 41
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (41 41 (:REWRITE |(< (/ x) (/ y))|))
     (40 8 (:REWRITE |(* c (* d x))|))
     (29 29
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (22 4 (:REWRITE |(- (* c x))|))
     (21 8
         (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (19 6 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (18 4 (:REWRITE |(+ (* c x) (* d x))|))
     (17 5
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (15 15 (:REWRITE |(< (+ (- c) x) y)|))
     (11 8 (:REWRITE DEFAULT-MINUS))
     (11 7 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (11 5 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (10 10 (:REWRITE |(< y (+ (- c) x))|))
     (10 10 (:REWRITE |(< x (+ c/d y))|))
     (9 8 (:REWRITE INTEGERP-MINUS-X))
     (8 8 (:REWRITE REDUCE-INTEGERP-+))
     (8 8 (:META META-INTEGERP-CORRECT))
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
     (4 4 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (4 4 (:REWRITE |(+ c (+ d x))|))
     (4 4 (:REWRITE |(* 0 x)|))
     (4 4 (:REWRITE |(* (- x) y)|))
     (3 3 (:REWRITE |(< (/ x) 0)|))
     (3 3 (:REWRITE |(< (* x y) 0)|))
     (1 1 (:REWRITE |(equal (+ (- c) x) y)|)))
(RTL::REM%-8-BNDS-19
 (41861 91
        (:REWRITE |(<= x (/ y)) with (< 0 y)|))
 (41266 91
        (:REWRITE |(< (/ x) y) with (< 0 x)|))
 (40950 5526
        (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
 (20664 2952 (:DEFINITION FIX))
 (16399 2866 (:REWRITE DEFAULT-TIMES-2))
 (13647
  13647
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (13647
      13647
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (13647
     13647
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (13647 13647
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (12220 68
        (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (10446 10446
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (10446 10446
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (6888 984
       (:REWRITE ARITH-BUBBLE-DOWN-*-MATCH-1))
 (6247 857 (:REWRITE CONSTANT-<-INTEGERP))
 (5980 2044 (:REWRITE ARITH-NORMALIZE-ADDENDS))
 (5904 984
       (:REWRITE |arith (* (expt x m) (expt x n))|))
 (5292 5292 (:REWRITE |arith (expt x c)|))
 (5166 857 (:REWRITE INTEGERP-<-CONSTANT))
 (5069 741
       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (4935 4935
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3D))
 (4935 4935
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2D))
 (4935 4935
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1D))
 (4859 159 (:REWRITE |(* y x)|))
 (4818 891 (:REWRITE DEFAULT-PLUS-2))
 (4600 4600 (:REWRITE |arith (expt 1/c n)|))
 (4550 745
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (4550 745
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (4044 450 (:REWRITE ACL2-NUMBERP-X))
 (3591 2866 (:REWRITE DEFAULT-TIMES-1))
 (3192 874 (:REWRITE DEFAULT-LESS-THAN-2))
 (2952 984
       (:REWRITE ARITH-BUBBLE-DOWN-+-MATCH-1))
 (2582 874 (:REWRITE DEFAULT-LESS-THAN-1))
 (1968 984
       (:REWRITE |arith (+ (* c x) (* d x))|))
 (1794 450 (:REWRITE RATIONALP-X))
 (1785 1785
       (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (1486 1486 (:REWRITE |arith (* (- x) y)|))
 (1346 874
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (1346 874
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (1184 1184
       (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (1184 1184
       (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (1184 1184
       (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (1184 1184
       (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (1031 891 (:REWRITE DEFAULT-PLUS-1))
 (984 984 (:REWRITE |arith (* 0 x)|))
 (891 891
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (891 891 (:REWRITE NORMALIZE-ADDENDS))
 (874 874 (:REWRITE THE-FLOOR-BELOW))
 (874 874 (:REWRITE THE-FLOOR-ABOVE))
 (873 873 (:REWRITE REDUCE-INTEGERP-+))
 (873 873 (:REWRITE INTEGERP-MINUS-X))
 (873 873 (:META META-INTEGERP-CORRECT))
 (857 857
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (857 857
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (857 857
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (857 857
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (857 857
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (857 857 (:REWRITE |(< c (- x))|))
 (857 857
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (857 857
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (857 857
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (857 857
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (857 857 (:REWRITE |(< (/ x) (/ y))|))
 (857 857 (:REWRITE |(< (- x) c)|))
 (857 857 (:REWRITE |(< (- x) (- y))|))
 (745 745 (:REWRITE SIMPLIFY-SUMS-<))
 (741 741 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (741 741
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (741 741
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (741 741
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (741 741 (:REWRITE |(equal c (/ x))|))
 (741 741 (:REWRITE |(equal c (- x))|))
 (741 741 (:REWRITE |(equal (/ x) c)|))
 (741 741 (:REWRITE |(equal (/ x) (/ y))|))
 (741 741 (:REWRITE |(equal (- x) c)|))
 (741 741 (:REWRITE |(equal (- x) (- y))|))
 (652 91
      (:REWRITE |(<= x (/ y)) with (< y 0)|))
 (652 91
      (:REWRITE |(< (/ x) y) with (< x 0)|))
 (592 592 (:LINEAR EXPT-LINEAR-UPPER-<))
 (592 592 (:LINEAR EXPT-LINEAR-LOWER-<))
 (592 592 (:LINEAR EXPT->=-1-TWO))
 (592 592 (:LINEAR EXPT->-1-TWO))
 (592 592 (:LINEAR EXPT-<=-1-ONE))
 (592 592 (:LINEAR EXPT-<-1-ONE))
 (528 528 (:REWRITE DEFAULT-MINUS))
 (472 472 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
 (472 472 (:TYPE-PRESCRIPTION ABS))
 (470 85
      (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (450 450 (:REWRITE REDUCE-RATIONALP-+))
 (450 450 (:REWRITE REDUCE-RATIONALP-*))
 (450 450 (:REWRITE RATIONALP-MINUS-X))
 (450 450 (:META META-RATIONALP-CORRECT))
 (264 264 (:REWRITE DEFAULT-EXPT-2))
 (264 264 (:REWRITE DEFAULT-EXPT-1))
 (264 264 (:REWRITE |(expt 1/c n)|))
 (264 264 (:REWRITE |(expt (- x) n)|))
 (247 247
      (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (232 68
      (:REWRITE |(< x (/ y)) with (< y 0)|))
 (198 198 (:REWRITE |(< y (+ (- c) x))|))
 (198 198 (:REWRITE |(< x (+ c/d y))|))
 (148 148 (:REWRITE |(< (+ c/d x) y)|))
 (148 148 (:REWRITE |(< (+ (- c) x) y)|))
 (69 69 (:REWRITE |arith (+ c (+ d x))|))
 (60 60 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (60 60 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (60 60 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (56 56 (:REWRITE |(< (/ x) 0)|))
 (56 56 (:REWRITE |(< (* x y) 0)|))
 (14 2 (:REWRITE |arith (* 1 x)|))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RTL::REM%-8-BNDS-20
 (167880 126
         (:REWRITE |(<= x (/ y)) with (< y 0)|))
 (167530 126
         (:REWRITE |(< (/ x) y) with (< x 0)|))
 (135700 14740
         (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
 (32948
  32948
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (32948
      32948
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (32948
     32948
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (32948 32948
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (29554 1526 (:REWRITE |(< (- x) c)|))
 (26916 3770 (:REWRITE DEFAULT-PLUS-2))
 (23520 3360
        (:REWRITE ARITH-BUBBLE-DOWN-*-MATCH-1))
 (23112 4390 (:REWRITE DEFAULT-TIMES-2))
 (20160 3360
        (:REWRITE |arith (* (expt x m) (expt x n))|))
 (18556 5116 (:REWRITE ARITH-NORMALIZE-ADDENDS))
 (16572 16572
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (16572 16572
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (13898 1518 (:REWRITE CONSTANT-<-INTEGERP))
 (13832 13832 (:REWRITE |arith (expt x c)|))
 (12680 12680 (:REWRITE |arith (expt 1/c n)|))
 (11862 3770 (:REWRITE DEFAULT-PLUS-1))
 (11856 1400
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (10080 3360
        (:REWRITE ARITH-BUBBLE-DOWN-+-MATCH-1))
 (10066 1576 (:REWRITE DEFAULT-LESS-THAN-2))
 (9838 510 (:REWRITE |(< (+ (- c) x) y)|))
 (7014 296 (:REWRITE |(* y (* x z))|))
 (6720 3360
       (:REWRITE |arith (+ (* c x) (* d x))|))
 (5922 956 (:REWRITE SIMPLIFY-SUMS-<))
 (5771 835
       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (5568 4390 (:REWRITE DEFAULT-TIMES-1))
 (5468 82
       (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (5190 82
       (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (4620 514 (:REWRITE ACL2-NUMBERP-X))
 (4560 4560
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3D))
 (4560 4560
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2D))
 (4560 4560
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1D))
 (4364 4364 (:REWRITE |arith (* (- x) y)|))
 (4102 1576 (:REWRITE DEFAULT-LESS-THAN-1))
 (3372 546 (:REWRITE |(< (+ c/d x) y)|))
 (3372 126
       (:REWRITE |(<= x (/ y)) with (< 0 y)|))
 (3360 3360 (:REWRITE |arith (* 0 x)|))
 (3132 126
       (:REWRITE |(< (/ x) y) with (< 0 x)|))
 (2816 2816
       (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (2816 2816
       (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2816 2816
       (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2816 2816
       (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (2420 2420
       (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (2284 444 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (2240 1518 (:REWRITE INTEGERP-<-CONSTANT))
 (2194 2194 (:REWRITE |(* (- x) y)|))
 (2050 514 (:REWRITE RATIONALP-X))
 (2030 1534
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (2030 1534
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (1806 1062 (:META META-INTEGERP-CORRECT))
 (1714 1714
       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (1576 1576 (:REWRITE THE-FLOOR-BELOW))
 (1576 1576 (:REWRITE THE-FLOOR-ABOVE))
 (1526 1526
       (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (1526 1526
       (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (1526 1526
       (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (1526 1526
       (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (1526 1526 (:REWRITE |(< c (- x))|))
 (1526 1526
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (1526 1526
       (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (1526 1526
       (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (1526 1526
       (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (1526 1526 (:REWRITE |(< (/ x) (/ y))|))
 (1526 1526 (:REWRITE |(< (- x) (- y))|))
 (1518 1518
       (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (1408 1408 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1408 1408 (:LINEAR EXPT-LINEAR-LOWER-<))
 (1408 1408 (:LINEAR EXPT->=-1-TWO))
 (1408 1408 (:LINEAR EXPT->-1-TWO))
 (1408 1408 (:LINEAR EXPT-<=-1-ONE))
 (1408 1408 (:LINEAR EXPT-<-1-ONE))
 (1238 1078 (:REWRITE INTEGERP-MINUS-X))
 (1062 1062 (:REWRITE REDUCE-INTEGERP-+))
 (1048 648 (:REWRITE DEFAULT-MINUS))
 (835 835 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (835 835
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (835 835
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (835 835
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (835 835 (:REWRITE |(equal c (/ x))|))
 (835 835 (:REWRITE |(equal c (- x))|))
 (835 835 (:REWRITE |(equal (/ x) c)|))
 (835 835 (:REWRITE |(equal (/ x) (/ y))|))
 (835 835 (:REWRITE |(equal (- x) c)|))
 (835 835 (:REWRITE |(equal (- x) (- y))|))
 (633 633
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (633 633
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (633 633
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (514 514 (:REWRITE REDUCE-RATIONALP-+))
 (514 514 (:REWRITE REDUCE-RATIONALP-*))
 (514 514 (:REWRITE RATIONALP-MINUS-X))
 (514 514 (:META META-RATIONALP-CORRECT))
 (498 498 (:REWRITE |(< y (+ (- c) x))|))
 (498 498 (:REWRITE |(< x (+ c/d y))|))
 (496 496 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
 (496 496 (:TYPE-PRESCRIPTION ABS))
 (314 314
      (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (296 296 (:REWRITE DEFAULT-EXPT-2))
 (296 296 (:REWRITE DEFAULT-EXPT-1))
 (296 296 (:REWRITE |(expt 1/c n)|))
 (296 296 (:REWRITE |(expt (- x) n)|))
 (248 40 (:REWRITE |(- (* c x))|))
 (197 197
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (196 82
      (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (196 82
      (:REWRITE |(< x (/ y)) with (< y 0)|))
 (96 96 (:REWRITE |arith (+ c (+ d x))|))
 (82 82 (:REWRITE |(* x (- y))|))
 (58 58 (:REWRITE |(< (/ x) 0)|))
 (58 58 (:REWRITE |(< (* x y) 0)|))
 (40 40 (:REWRITE FOLD-CONSTS-IN-+))
 (14 2 (:REWRITE |arith (* 1 x)|))
 (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
 (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
 (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
 (6 6 (:REWRITE |(* a (/ a) b)|)))
(RTL::REM%-8-BNDS-21
 (13847 31 (:REWRITE |(< y (+ (- c) x))|))
 (9689 1049
       (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
 (7515 2
       (:REWRITE |(<= x (/ y)) with (< 0 y)|))
 (7502 2 (:REWRITE |(< (/ x) y) with (< 0 x)|))
 (4851 1 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (4798 1
       (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (2350 239 (:REWRITE DEFAULT-PLUS-2))
 (1952
  1952
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1952
      1952
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1952
     1952
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1952 1952
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1952 1952
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (1680 240
       (:REWRITE ARITH-BUBBLE-DOWN-*-MATCH-1))
 (1440 240
       (:REWRITE |arith (* (expt x m) (expt x n))|))
 (1312 352 (:REWRITE ARITH-NORMALIZE-ADDENDS))
 (1115 1115
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (1115 1115
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (1115 1115
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (1112 172 (:REWRITE DEFAULT-TIMES-2))
 (892 892 (:REWRITE |arith (expt x c)|))
 (844 844 (:REWRITE |arith (expt 1/c n)|))
 (777 239 (:REWRITE DEFAULT-PLUS-1))
 (720 240
      (:REWRITE ARITH-BUBBLE-DOWN-+-MATCH-1))
 (710 80 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (710 80 (:LINEAR EXPT-<=-1-TWO))
 (700 80 (:LINEAR EXPT-X->-X))
 (700 80 (:LINEAR EXPT->-1-ONE))
 (700 80 (:LINEAR EXPT-<-1-TWO))
 (520 80 (:LINEAR EXPT-X->=-X))
 (520 80 (:LINEAR EXPT->=-1-ONE))
 (489 41 (:REWRITE DEFAULT-LESS-THAN-2))
 (480 240
      (:REWRITE |arith (+ (* c x) (* d x))|))
 (453 31
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (392 6 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (318 34 (:REWRITE CONSTANT-<-INTEGERP))
 (316 316 (:REWRITE |arith (* (- x) y)|))
 (304 34 (:REWRITE INTEGERP-<-CONSTANT))
 (291 39 (:REWRITE DEFAULT-MINUS))
 (262 172 (:REWRITE DEFAULT-TIMES-1))
 (240 240 (:REWRITE |arith (* 0 x)|))
 (186 14 (:META META-INTEGERP-CORRECT))
 (166 41 (:REWRITE DEFAULT-LESS-THAN-1))
 (164 13 (:REWRITE SIMPLIFY-SUMS-<))
 (160 160
      (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (160 160
      (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (160 160
      (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (160 160
      (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (123 123
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (102 102
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (85 15 (:REWRITE INTEGERP-MINUS-X))
 (80 80 (:LINEAR EXPT-LINEAR-UPPER-<))
 (80 80 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (80 80 (:LINEAR EXPT-LINEAR-LOWER-<))
 (80 80 (:LINEAR EXPT->=-1-TWO))
 (80 80 (:LINEAR EXPT->-1-TWO))
 (80 80 (:LINEAR EXPT-<=-1-ONE))
 (80 80 (:LINEAR EXPT-<-1-ONE))
 (72 18 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (60 60 (:REWRITE FOLD-CONSTS-IN-+))
 (50 2
     (:REWRITE |(<= x (/ y)) with (< y 0)|))
 (50 2 (:REWRITE |(< (/ x) y) with (< x 0)|))
 (48 48 (:REWRITE |(* (- x) y)|))
 (46 46 (:REWRITE |arith (+ c (+ d x))|))
 (41 41 (:REWRITE THE-FLOOR-BELOW))
 (41 41 (:REWRITE THE-FLOOR-ABOVE))
 (40 40
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (40 40
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (37 36 (:REWRITE |(< (- x) (- y))|))
 (36 36
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (36 36
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (36 36
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (36 36
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (36 36
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (36 36
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (36 36
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (36 36
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (36 36 (:REWRITE |(< (/ x) (/ y))|))
 (34 34
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (31 31 (:REWRITE |(< x (+ c/d y))|))
 (25 1
     (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (25 1 (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (21 21 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (21 21 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (21 21 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (19 19 (:REWRITE |(< (+ c/d x) y)|))
 (19 19 (:REWRITE |(< (+ (- c) x) y)|))
 (16 6
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (14 14 (:REWRITE REDUCE-INTEGERP-+))
 (14 2 (:REWRITE |(integerp (- x))|))
 (6 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (6 6
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (6 6
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (6 6
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (6 6 (:REWRITE DEFAULT-EXPT-2))
 (6 6 (:REWRITE DEFAULT-EXPT-1))
 (6 6 (:REWRITE |(expt 1/c n)|))
 (6 6 (:REWRITE |(expt (- x) n)|))
 (6 6 (:REWRITE |(equal c (/ x))|))
 (6 6 (:REWRITE |(equal c (- x))|))
 (6 6 (:REWRITE |(equal (/ x) c)|))
 (6 6 (:REWRITE |(equal (/ x) (/ y))|))
 (6 6 (:REWRITE |(equal (- x) c)|))
 (6 6 (:REWRITE |(equal (- x) (- y))|))
 (6 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (3 3 (:REWRITE |(< (/ x) 0)|))
 (3 3 (:REWRITE |(< (* x y) 0)|))
 (2 2 (:REWRITE |(equal (+ (- c) x) y)|))
 (1 1 (:REWRITE |(< 0 (/ x))|))
 (1 1 (:REWRITE |(< 0 (* x y))|)))
(RTL::REM%-8-BNDS-22
 (66818 66818
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (66818 66818
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (66818 66818
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (51765 51765
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (51765 51765
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (51765 51765
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (32670 32670
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3D))
 (32670 32670
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2D))
 (32670 32670
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1D))
 (30060 4815 (:REWRITE RATIONALP-X))
 (24369 7615 (:REWRITE DEFAULT-TIMES-2))
 (15009 6948 (:REWRITE DEFAULT-PLUS-1))
 (14685 5057 (:REWRITE CONSTANT-<-INTEGERP))
 (12944 7724
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (11316 5057 (:REWRITE INTEGERP-<-CONSTANT))
 (11314 6239 (:REWRITE DEFAULT-LESS-THAN-1))
 (10331 4745
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (10331 4745
        (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (9208 4745 (:REWRITE SIMPLIFY-SUMS-<))
 (7970 1114 (:REWRITE ACL2-NUMBERP-X))
 (7876 7876 (:REWRITE REDUCE-INTEGERP-+))
 (7876 7876 (:REWRITE INTEGERP-MINUS-X))
 (7876 7876 (:META META-INTEGERP-CORRECT))
 (7838 7615 (:REWRITE DEFAULT-TIMES-1))
 (7724 7724 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (7724 7724
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (7724 7724
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (7724 7724
       (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (7724 7724 (:REWRITE |(equal c (/ x))|))
 (7724 7724 (:REWRITE |(equal c (- x))|))
 (7724 7724 (:REWRITE |(equal (/ x) c)|))
 (7724 7724 (:REWRITE |(equal (/ x) (/ y))|))
 (7724 7724 (:REWRITE |(equal (- x) c)|))
 (7724 7724 (:REWRITE |(equal (- x) (- y))|))
 (7711 539
       (:REWRITE |(<= x (/ y)) with (< y 0)|))
 (7711 539
       (:REWRITE |(<= x (/ y)) with (< 0 y)|))
 (7711 539
       (:REWRITE |(< (/ x) y) with (< x 0)|))
 (7711 539
       (:REWRITE |(< (/ x) y) with (< 0 x)|))
 (7578 6239 (:REWRITE DEFAULT-LESS-THAN-2))
 (6375 449
       (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (6375 449
       (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (6375 449
       (:REWRITE |(< x (/ y)) with (< y 0)|))
 (6375 449
       (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (6239 6239 (:REWRITE THE-FLOOR-BELOW))
 (6239 6239 (:REWRITE THE-FLOOR-ABOVE))
 (5404 5404
       (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (5404 5404
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE))
 (5404 5404
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (5404
   5404
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (5404
  5404
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (5404 5404
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (5404 5404
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (5404
      5404
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (5404
     5404
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (5404 5404
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (5404 5404
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (5404 5404
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (5097 5057
       (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (5073 5057
       (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (5057 5057
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (5057 5057
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (5057 5057
       (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (5057 5057
       (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (5057 5057
       (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (5057 5057 (:REWRITE |(< c (- x))|))
 (5057 5057
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (5057 5057
       (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (5057 5057
       (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (5057 5057
       (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (5057 5057 (:REWRITE |(< (/ x) (/ y))|))
 (5057 5057 (:REWRITE |(< (- x) c)|))
 (5057 5057 (:REWRITE |(< (- x) (- y))|))
 (4872 4872
       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (4815 4815 (:REWRITE REDUCE-RATIONALP-+))
 (4815 4815 (:REWRITE REDUCE-RATIONALP-*))
 (4815 4815 (:REWRITE RATIONALP-MINUS-X))
 (4815 4815 (:META META-RATIONALP-CORRECT))
 (2376 2376 (:REWRITE ARITH-NORMALIZE-ADDENDS))
 (1854 1854
       (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (1163 1163 (:REWRITE |(< y (+ (- c) x))|))
 (1163 1163 (:REWRITE |(< x (+ c/d y))|))
 (1068 1068
       (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
 (892 892 (:REWRITE FOLD-CONSTS-IN-+))
 (892 892 (:REWRITE |(* (- x) y)|))
 (665 665
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (446 446 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (446 446 (:REWRITE DEFAULT-EXPT-2))
 (446 446 (:REWRITE DEFAULT-EXPT-1))
 (446 446 (:REWRITE |(expt 1/c n)|))
 (446 446 (:REWRITE |(expt (- x) n)|))
 (441 441 (:REWRITE |(< (+ c/d x) y)|))
 (441 441 (:REWRITE |(< (+ (- c) x) y)|))
 (282 282 (:REWRITE |(< (/ x) 0)|))
 (282 282 (:REWRITE |(< (* x y) 0)|))
 (112 16 (:REWRITE |arith (* 1 x)|)))
(RTL::I8-J-2
 (600 8 (:DEFINITION RTL::QUOT%))
 (219 28 (:REWRITE DEFAULT-TIMES-2))
 (208 33 (:REWRITE DEFAULT-PLUS-2))
 (187 1 (:REWRITE |(* x (if a b c))|))
 (123 28 (:REWRITE DEFAULT-TIMES-1))
 (120 2 (:REWRITE ACL2-NUMBERP-X))
 (102 2 (:REWRITE RATIONALP-X))
 (95 2 (:REWRITE |(* y x)|))
 (84 2 (:REWRITE RTL::INTP-Q%))
 (80 2 (:REWRITE ZP-OPEN))
 (70 2 (:REWRITE |(< x (if a b c))|))
 (52 2 (:REWRITE |(< y (+ (- c) x))|))
 (50 2 (:REWRITE |(+ x (if a b c))|))
 (48
   22
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (43 33 (:REWRITE DEFAULT-PLUS-1))
 (41 30 (:TYPE-PRESCRIPTION RTL::INTP-Q%))
 (32 32 (:TYPE-PRESCRIPTION RTL::R%))
 (32 32 (:TYPE-PRESCRIPTION RTL::NATP-R%))
 (30 30
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (30 30 (:REWRITE NORMALIZE-ADDENDS))
 (30 10 (:REWRITE DEFAULT-EXPT-1))
 (28 7
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (25 25
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (24 24 (:TYPE-PRESCRIPTION ZP))
 (22 22
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (22
  22
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (22 22
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (22 22
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (22 22
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (22 22
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (22 22
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (22 22
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (22 11
     (:TYPE-PRESCRIPTION RTL::Q%-CONSTRAINT))
 (21 21 (:REWRITE THE-FLOOR-BELOW))
 (21 21 (:REWRITE THE-FLOOR-ABOVE))
 (21 21 (:REWRITE DEFAULT-LESS-THAN-2))
 (21 21 (:REWRITE DEFAULT-LESS-THAN-1))
 (19 19
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (19 19
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (17 17
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (17 17 (:REWRITE INTEGERP-<-CONSTANT))
 (17 17 (:REWRITE CONSTANT-<-INTEGERP))
 (17 17
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (17 17
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (17 17
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (17 17
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (17 17 (:REWRITE |(< c (- x))|))
 (17 17
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (17 17
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (17 17
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (17 17
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (17 17 (:REWRITE |(< (/ x) (/ y))|))
 (17 17 (:REWRITE |(< (- x) c)|))
 (17 17 (:REWRITE |(< (- x) (- y))|))
 (13 1 (:REWRITE |(expt x (if a b c))|))
 (11 11 (:REWRITE SIMPLIFY-SUMS-<))
 (11 11
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (11 11 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (10 10 (:REWRITE DEFAULT-EXPT-2))
 (9 9 (:REWRITE |(expt 1/c n)|))
 (9 9 (:REWRITE |(expt (- x) n)|))
 (8 2
    (:TYPE-PRESCRIPTION NOT-INTEGERP-4A-EXPT))
 (8 1 (:REWRITE |(- (if a b c))|))
 (7 7
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (7 7
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (7 7
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (7 7 (:REWRITE |(< (/ x) 0)|))
 (7 7 (:REWRITE |(< (* x y) 0)|))
 (6 1 (:REWRITE |(- (+ x y))|))
 (5 1 (:REWRITE |(+ c (+ d x))|))
 (3 3 (:REWRITE REDUCE-INTEGERP-+))
 (3 3 (:REWRITE INTEGERP-MINUS-X))
 (3 3 (:REWRITE DEFAULT-MINUS))
 (3 3 (:REWRITE |(< (+ c/d x) y)|))
 (3 3 (:REWRITE |(< (+ (- c) x) y)|))
 (3 3 (:META META-INTEGERP-CORRECT))
 (3 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (3 1
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (2 2
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (2 2
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (2 2
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (2 2 (:REWRITE |(< x (+ c/d y))|))
 (2 2 (:REWRITE |(< 0 (* x y))|))
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
 (1 1 (:REWRITE |(equal (+ (- c) x) y)|)))
(RTL::REM%-8-BNDS-35
     (5958 248 (:DEFINITION NTH))
     (4698 124 (:REWRITE ZP-OPEN))
     (3408 3336
           (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (3336 3336
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (3336 3336
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (3336 3336
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (2198 2198
           (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (2198 2198
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (2198 2198
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (2198 2198
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (1476 164 (:REWRITE ACL2-NUMBERP-X))
     (1115 517 (:REWRITE DEFAULT-LESS-THAN-2))
     (1115 517 (:REWRITE DEFAULT-LESS-THAN-1))
     (914 362
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (914 362
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (832 362 (:REWRITE SIMPLIFY-SUMS-<))
     (820 410
          (:TYPE-PRESCRIPTION RTL::Q%-CONSTRAINT))
     (656 164 (:REWRITE RATIONALP-X))
     (532 532 (:TYPE-PRESCRIPTION RTL::I8%))
     (517 517 (:REWRITE THE-FLOOR-BELOW))
     (517 517 (:REWRITE THE-FLOOR-ABOVE))
     (453 417
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (453 417
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (417 417
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
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
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (417 417
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (417 417
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (417 417
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (417 417 (:REWRITE |(< (/ x) (/ y))|))
     (417 417 (:REWRITE |(< (- x) c)|))
     (417 417 (:REWRITE |(< (- x) (- y))|))
     (372 354 (:REWRITE DEFAULT-TIMES-2))
     (320 320 (:REWRITE REDUCE-INTEGERP-+))
     (320 320 (:REWRITE INTEGERP-MINUS-X))
     (320 320 (:META META-INTEGERP-CORRECT))
     (303 250 (:REWRITE DEFAULT-PLUS-2))
     (303 250 (:REWRITE DEFAULT-PLUS-1))
     (207 101
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (197 197
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (197 197 (:REWRITE NORMALIZE-ADDENDS))
     (180 180
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (180 180
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (180 180 (:REWRITE |(< 0 (/ x))|))
     (180 180 (:REWRITE |(< 0 (* x y))|))
     (164 164 (:REWRITE REDUCE-RATIONALP-+))
     (164 164 (:REWRITE REDUCE-RATIONALP-*))
     (164 164 (:REWRITE RATIONALP-MINUS-X))
     (164 164 (:META META-RATIONALP-CORRECT))
     (112 112
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (110 110 (:REWRITE DEFAULT-CDR))
     (103 103 (:REWRITE |(< y (+ (- c) x))|))
     (103 103 (:REWRITE |(< x (+ c/d y))|))
     (101 101 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (101 101
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (101 101
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (101 101
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (101 101 (:REWRITE |(equal c (/ x))|))
     (101 101 (:REWRITE |(equal c (- x))|))
     (101 101 (:REWRITE |(equal (/ x) c)|))
     (101 101 (:REWRITE |(equal (/ x) (/ y))|))
     (101 101 (:REWRITE |(equal (- x) c)|))
     (101 101 (:REWRITE |(equal (- x) (- y))|))
     (88 88 (:REWRITE |(< (/ x) 0)|))
     (88 88 (:REWRITE |(< (* x y) 0)|))
     (56 56
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (56 56
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (36 36 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
     (36 36 (:TYPE-PRESCRIPTION ABS))
     (18 18
         (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (14 14 (:REWRITE DEFAULT-CAR))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RTL::HYP-INV-8
     (10 10 (:REWRITE THE-FLOOR-BELOW))
     (10 10 (:REWRITE THE-FLOOR-ABOVE))
     (10 10
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (10 10
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (10 10
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (10 10 (:REWRITE INTEGERP-<-CONSTANT))
     (10 10 (:REWRITE DEFAULT-LESS-THAN-2))
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
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (10 10
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (10 10
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (10 10
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (10 10 (:REWRITE |(< (/ x) (/ y))|))
     (10 10 (:REWRITE |(< (- x) c)|))
     (10 10 (:REWRITE |(< (- x) (- y))|))
     (7 7 (:REWRITE SIMPLIFY-SUMS-<))
     (7 7
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (7 7 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (6 6 (:REWRITE |(< (/ x) 0)|))
     (6 6 (:REWRITE |(< (* x y) 0)|))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (3 3 (:REWRITE REDUCE-INTEGERP-+))
     (3 3 (:REWRITE INTEGERP-MINUS-X))
     (3 3 (:META META-INTEGERP-CORRECT))
     (2 2 (:REWRITE ZP-OPEN))
     (2 2
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (2 2 (:REWRITE NORMALIZE-ADDENDS))
     (2 2 (:REWRITE DEFAULT-PLUS-2))
     (2 2 (:REWRITE DEFAULT-PLUS-1))
     (1 1 (:REWRITE |(< (+ c/d x) y)|))
     (1 1 (:REWRITE |(< (+ (- c) x) y)|)))
(RTL::REM%-8-BNDS-36)
(RTL::REM%-8-BNDS-37)
(RTL::REM%-8-BNDS-38)
(RTL::REM%-8-BNDS-39)
(RTL::REM%-8-BNDS-40
     (516 516
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (516 516
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (516 516
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (516 516
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (140 2 (:DEFINITION NTH))
     (108 2 (:REWRITE ZP-OPEN))
     (92 44 (:REWRITE INTEGERP-<-CONSTANT))
     (86 44
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (72 56 (:REWRITE DEFAULT-LESS-THAN-2))
     (56 56 (:REWRITE THE-FLOOR-BELOW))
     (56 56 (:REWRITE THE-FLOOR-ABOVE))
     (56 56 (:REWRITE DEFAULT-LESS-THAN-1))
     (44 44
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (44 44
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (44 44 (:REWRITE CONSTANT-<-INTEGERP))
     (44 44
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (44 44
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (44 44
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (44 44
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (44 44 (:REWRITE |(< c (- x))|))
     (44 44
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (44 44
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (44 44
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (44 44 (:REWRITE |(< (/ x) (/ y))|))
     (44 44 (:REWRITE |(< (- x) c)|))
     (44 44 (:REWRITE |(< (- x) (- y))|))
     (44 11 (:REWRITE RATIONALP-X))
     (41 41 (:REWRITE REDUCE-INTEGERP-+))
     (41 41 (:REWRITE INTEGERP-MINUS-X))
     (41 41 (:META META-INTEGERP-CORRECT))
     (37 16
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (36 4 (:REWRITE ACL2-NUMBERP-X))
     (32 24 (:REWRITE SIMPLIFY-SUMS-<))
     (32 24
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (32 24 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (25 25 (:REWRITE DEFAULT-PLUS-2))
     (25 25 (:REWRITE DEFAULT-PLUS-1))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (16 16 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (16 16
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (16 16
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (16 16
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (16 16 (:REWRITE |(equal c (/ x))|))
     (16 16 (:REWRITE |(equal c (- x))|))
     (16 16 (:REWRITE |(equal (/ x) c)|))
     (16 16 (:REWRITE |(equal (/ x) (/ y))|))
     (16 16 (:REWRITE |(equal (- x) c)|))
     (16 16 (:REWRITE |(equal (- x) (- y))|))
     (15 15 (:REWRITE |(< (/ x) 0)|))
     (15 15 (:REWRITE |(< (* x y) 0)|))
     (13 13 (:REWRITE RTL::I8-J-2))
     (11 11 (:REWRITE REDUCE-RATIONALP-+))
     (11 11 (:REWRITE REDUCE-RATIONALP-*))
     (11 11 (:REWRITE RATIONALP-MINUS-X))
     (11 11 (:META META-RATIONALP-CORRECT))
     (10 10 (:REWRITE DEFAULT-MINUS))
     (9 9
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (9 9
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (6 6 (:REWRITE DEFAULT-TIMES-2))
     (2 2
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS)))
(RTL::REM%-8-BNDS-41
     (4508 4508
           (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (4508 4508
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (4508 4508
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (4508 4508
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (2085 450 (:REWRITE |(< c (- x))|))
     (1195 400 (:REWRITE INTEGERP-<-CONSTANT))
     (950 10 (:DEFINITION NTH))
     (825 450
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (775 505
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (775 505
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (700 10 (:REWRITE ZP-OPEN))
     (675 595 (:REWRITE DEFAULT-LESS-THAN-2))
     (600 450
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (595 595 (:REWRITE THE-FLOOR-BELOW))
     (595 595 (:REWRITE THE-FLOOR-ABOVE))
     (595 595 (:REWRITE DEFAULT-LESS-THAN-1))
     (510 510 (:REWRITE REDUCE-INTEGERP-+))
     (510 510 (:REWRITE INTEGERP-MINUS-X))
     (510 510 (:META META-INTEGERP-CORRECT))
     (450 450
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (450 450
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (450 450
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (450 450
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (450 450
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (450 450
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (450 450 (:REWRITE |(< (/ x) (/ y))|))
     (450 450 (:REWRITE |(< (- x) (- y))|))
     (400 400 (:REWRITE CONSTANT-<-INTEGERP))
     (400 400 (:REWRITE |(< (- x) c)|))
     (363 166
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (280 70 (:REWRITE RATIONALP-X))
     (275 235 (:REWRITE SIMPLIFY-SUMS-<))
     (275 235
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (275 235
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (270 270 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
     (270 270 (:TYPE-PRESCRIPTION ABS))
     (255 255 (:REWRITE DEFAULT-TIMES-2))
     (200 200 (:REWRITE DEFAULT-PLUS-2))
     (200 200 (:REWRITE DEFAULT-PLUS-1))
     (200 50 (:REWRITE |(- (* c x))|))
     (180 180
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (180 20 (:REWRITE ACL2-NUMBERP-X))
     (166 166 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (166 166
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (166 166
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (166 166
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (166 166 (:REWRITE |(equal c (/ x))|))
     (166 166 (:REWRITE |(equal c (- x))|))
     (166 166 (:REWRITE |(equal (/ x) c)|))
     (166 166 (:REWRITE |(equal (/ x) (/ y))|))
     (166 166 (:REWRITE |(equal (- x) c)|))
     (166 166 (:REWRITE |(equal (- x) (- y))|))
     (146 146 (:REWRITE RTL::I8-J-2))
     (130 130 (:REWRITE DEFAULT-MINUS))
     (80 80 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (80 80 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (80 80 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (80 80 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (75 75 (:REWRITE |(* (- x) y)|))
     (70 70 (:REWRITE REDUCE-RATIONALP-+))
     (70 70 (:REWRITE REDUCE-RATIONALP-*))
     (70 70 (:REWRITE RATIONALP-MINUS-X))
     (70 70 (:META META-RATIONALP-CORRECT))
     (35 35 (:REWRITE |(* x (- y))|))
     (11 11
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (10 10
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (10 10
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (10 10 (:REWRITE |(< (/ x) 0)|))
     (10 10 (:REWRITE |(< (* x y) 0)|)))
(RTL::REM%-8-BNDS-42
     (30820 30820
            (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (30820 30820
            (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (30820 30820
            (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (30820 30820
            (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (13398 3261 (:REWRITE |(< c (- x))|))
     (8315 2951 (:REWRITE INTEGERP-<-CONSTANT))
     (6270 66 (:DEFINITION NTH))
     (5766 3261
           (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (5276 3602
           (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (5276 3602
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (4724 4196 (:REWRITE DEFAULT-LESS-THAN-2))
     (4620 66 (:REWRITE ZP-OPEN))
     (4275 3261
           (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (4196 4196 (:REWRITE THE-FLOOR-BELOW))
     (4196 4196 (:REWRITE THE-FLOOR-ABOVE))
     (4196 4196 (:REWRITE DEFAULT-LESS-THAN-1))
     (3811 3811 (:REWRITE REDUCE-INTEGERP-+))
     (3811 3811 (:REWRITE INTEGERP-MINUS-X))
     (3811 3811 (:META META-INTEGERP-CORRECT))
     (3261 3261
           (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (3261 3261
           (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (3261 3261
           (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (3261 3261
           (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (3261 3261
           (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (3261 3261
           (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (3261 3261 (:REWRITE |(< (/ x) (/ y))|))
     (3261 3261 (:REWRITE |(< (- x) (- y))|))
     (2951 2951 (:REWRITE CONSTANT-<-INTEGERP))
     (2951 2951 (:REWRITE |(< (- x) c)|))
     (2337 777
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (2112 528 (:REWRITE RATIONALP-X))
     (2103 1839 (:REWRITE SIMPLIFY-SUMS-<))
     (2103 1839
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (2103 1839
           (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (1782 198 (:REWRITE ACL2-NUMBERP-X))
     (1674 1674 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
     (1674 1674 (:TYPE-PRESCRIPTION ABS))
     (1593 1593 (:REWRITE DEFAULT-TIMES-2))
     (1320 1320 (:REWRITE DEFAULT-PLUS-2))
     (1320 1320 (:REWRITE DEFAULT-PLUS-1))
     (1240 310 (:REWRITE |(- (* c x))|))
     (1120 1120
           (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (838 838 (:REWRITE DEFAULT-MINUS))
     (777 777 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (777 777
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (777 777
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (777 777
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (777 777 (:REWRITE |(equal c (/ x))|))
     (777 777 (:REWRITE |(equal c (- x))|))
     (777 777 (:REWRITE |(equal (/ x) c)|))
     (777 777 (:REWRITE |(equal (/ x) (/ y))|))
     (777 777 (:REWRITE |(equal (- x) c)|))
     (777 777 (:REWRITE |(equal (- x) (- y))|))
     (528 528
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (528 528
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (528 528
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (528 528
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (528 528 (:REWRITE REDUCE-RATIONALP-+))
     (528 528 (:REWRITE REDUCE-RATIONALP-*))
     (528 528 (:REWRITE RATIONALP-MINUS-X))
     (528 528 (:META META-RATIONALP-CORRECT))
     (465 465 (:REWRITE |(* (- x) y)|))
     (217 217 (:REWRITE |(* x (- y))|))
     (67 67 (:REWRITE |(< (/ x) 0)|))
     (67 67 (:REWRITE |(< (* x y) 0)|))
     (66 66
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (66 66
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RTL::REM%-8-BNDS-43
     (25 10
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (10 10 (:REWRITE SIMPLIFY-SUMS-EQUAL))
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
     (4 4 (:REWRITE THE-FLOOR-BELOW))
     (4 4 (:REWRITE THE-FLOOR-ABOVE))
     (4 4 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (4 4
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (4 4
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
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
     (3 3 (:REWRITE SIMPLIFY-SUMS-<))
     (3 3
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (3 3 (:REWRITE REDUCE-INTEGERP-+))
     (3 3 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (3 3
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (3 3 (:REWRITE NORMALIZE-ADDENDS))
     (3 3 (:REWRITE INTEGERP-MINUS-X))
     (3 3 (:REWRITE DEFAULT-PLUS-2))
     (3 3 (:REWRITE DEFAULT-PLUS-1))
     (3 3 (:META META-INTEGERP-CORRECT))
     (1 1 (:REWRITE |(< (/ x) 0)|))
     (1 1 (:REWRITE |(< (* x y) 0)|)))
(RTL::REM%-8-BNDS-44
     (4996 2496
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (3377 2452 (:REWRITE RTL::I8-J-2))
     (2496 2496 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (2496 2496
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (2496 2496
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (2496 2496
           (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (2496 2496 (:REWRITE |(equal c (/ x))|))
     (2496 2496 (:REWRITE |(equal c (- x))|))
     (2496 2496 (:REWRITE |(equal (/ x) c)|))
     (2496 2496 (:REWRITE |(equal (/ x) (/ y))|))
     (2496 2496 (:REWRITE |(equal (- x) c)|))
     (2496 2496 (:REWRITE |(equal (- x) (- y))|))
     (302 222 (:REWRITE DEFAULT-LESS-THAN-2))
     (257 181 (:REWRITE SIMPLIFY-SUMS-<))
     (257 181
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (257 181
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (222 222 (:REWRITE THE-FLOOR-BELOW))
     (222 222 (:REWRITE THE-FLOOR-ABOVE))
     (222 222
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (222 222
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (222 222 (:REWRITE INTEGERP-<-CONSTANT))
     (222 222 (:REWRITE DEFAULT-LESS-THAN-1))
     (222 222 (:REWRITE CONSTANT-<-INTEGERP))
     (222 222
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (222 222
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (222 222
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (222 222
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (222 222 (:REWRITE |(< c (- x))|))
     (222 222
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (222 222
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (222 222
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (222 222
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (222 222 (:REWRITE |(< (/ x) (/ y))|))
     (222 222 (:REWRITE |(< (- x) c)|))
     (222 222 (:REWRITE |(< (- x) (- y))|))
     (152 38 (:REWRITE RATIONALP-X))
     (104 104
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (74 37 (:REWRITE DEFAULT-PLUS-2))
     (73 73 (:REWRITE REDUCE-INTEGERP-+))
     (73 73 (:REWRITE INTEGERP-MINUS-X))
     (73 73 (:META META-INTEGERP-CORRECT))
     (38 38 (:REWRITE REDUCE-RATIONALP-+))
     (38 38 (:REWRITE REDUCE-RATIONALP-*))
     (38 38 (:REWRITE RATIONALP-MINUS-X))
     (38 38 (:META META-RATIONALP-CORRECT))
     (37 37
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (37 37 (:REWRITE NORMALIZE-ADDENDS))
     (37 37 (:REWRITE DEFAULT-PLUS-1))
     (35 35 (:REWRITE |(< (/ x) 0)|))
     (35 35 (:REWRITE |(< (* x y) 0)|)))
(RTL::REM%-8-BNDS-45
     (29889 28805
            (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (28805 28805
            (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (28805 28805
            (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (28805 28805
            (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (16360 16360
            (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (16360 16360
            (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (16360 16360
            (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (16360 16360
            (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (14815 5170 (:REWRITE DEFAULT-LESS-THAN-2))
     (13065 1417 (:REWRITE ACL2-NUMBERP-X))
     (10689 6182 (:REWRITE DEFAULT-PLUS-2))
     (10363 4222 (:REWRITE |(< c (- x))|))
     (9723 923 (:REWRITE RTL::I8-J-2))
     (8657 6182 (:REWRITE DEFAULT-PLUS-1))
     (7266 3890
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (7024 1717 (:REWRITE RATIONALP-X))
     (6583 4048 (:REWRITE |(< (- x) c)|))
     (5823 5170 (:REWRITE DEFAULT-LESS-THAN-1))
     (5799 3395 (:REWRITE SIMPLIFY-SUMS-<))
     (5170 5170 (:REWRITE THE-FLOOR-BELOW))
     (5170 5170 (:REWRITE THE-FLOOR-ABOVE))
     (4764 4222
           (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (4764 4222
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (4287 4222 (:REWRITE |(< (- x) (- y))|))
     (4231 4222
           (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (4228 4222
           (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (4222 4222
           (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (4222 4222
           (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (4222 4222
           (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (4222 4222
           (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (4222 4222
           (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (4222 4222
           (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (4222 4222 (:REWRITE |(< (/ x) (/ y))|))
     (3989 3983 (:REWRITE INTEGERP-<-CONSTANT))
     (3983 3983 (:REWRITE CONSTANT-<-INTEGERP))
     (2982 2982 (:TYPE-PRESCRIPTION RTL::I8%))
     (2515 2515 (:REWRITE REDUCE-INTEGERP-+))
     (2515 2515 (:REWRITE INTEGERP-MINUS-X))
     (2515 2515 (:META META-INTEGERP-CORRECT))
     (2484 2484
           (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (2460 1255
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (2214 1239 (:REWRITE DEFAULT-MINUS))
     (1717 1717 (:REWRITE REDUCE-RATIONALP-+))
     (1717 1717 (:REWRITE REDUCE-RATIONALP-*))
     (1717 1717 (:REWRITE RATIONALP-MINUS-X))
     (1717 1717 (:META META-RATIONALP-CORRECT))
     (1350 1350 (:REWRITE |(< 0 (/ x))|))
     (1350 1350 (:REWRITE |(< 0 (* x y))|))
     (1318 1318 (:REWRITE |(< (/ x) 0)|))
     (1318 1318 (:REWRITE |(< (* x y) 0)|))
     (1255 1255 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (1255 1255
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (1255 1255
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (1255 1255
           (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (1255 1255 (:REWRITE |(equal c (/ x))|))
     (1255 1255 (:REWRITE |(equal c (- x))|))
     (1255 1255 (:REWRITE |(equal (/ x) c)|))
     (1255 1255 (:REWRITE |(equal (/ x) (/ y))|))
     (1255 1255 (:REWRITE |(equal (- x) c)|))
     (1255 1255 (:REWRITE |(equal (- x) (- y))|))
     (1164 1164
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (1164 1164
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (990 495 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (876 876
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (681 681
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (681 681
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (542 542 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
     (542 542 (:TYPE-PRESCRIPTION ABS))
     (528 528 (:REWRITE DEFAULT-CAR))
     (514 514 (:REWRITE DEFAULT-CDR))
     (495 495 (:REWRITE |(< y (+ (- c) x))|))
     (495 495 (:REWRITE |(< x (+ c/d y))|))
     (375 239 (:REWRITE |(- (- x))|))
     (271 271
          (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (184 184
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (1 1 (:REWRITE |(* x (if a b c))|)))
(RTL::REM%-8-BNDS-46
     (28 3 (:REWRITE RTL::I8-J-2))
     (8 4
        (:TYPE-PRESCRIPTION RTL::Q%-CONSTRAINT))
     (8 3
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (5 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (4 2 (:REWRITE DEFAULT-TIMES-2))
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
     (2 2 (:TYPE-PRESCRIPTION RTL::REM%))
     (2 2 (:REWRITE THE-FLOOR-BELOW))
     (2 2 (:REWRITE THE-FLOOR-ABOVE))
     (2 2 (:REWRITE SIMPLIFY-SUMS-<))
     (2 2
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (2 2 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (2 2 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (2 2
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (2 2
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (2 2 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (2 2
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (2 2 (:REWRITE INTEGERP-<-CONSTANT))
     (2 2 (:REWRITE DEFAULT-TIMES-1))
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
     (1 1 (:REWRITE ZP-OPEN))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (1 1 (:REWRITE REDUCE-INTEGERP-+))
     (1 1
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (1 1 (:REWRITE NORMALIZE-ADDENDS))
     (1 1 (:REWRITE INTEGERP-MINUS-X))
     (1 1 (:REWRITE DEFAULT-PLUS-2))
     (1 1 (:REWRITE DEFAULT-PLUS-1))
     (1 1 (:REWRITE |(< (/ x) 0)|))
     (1 1 (:REWRITE |(< (* x y) 0)|))
     (1 1 (:META META-INTEGERP-CORRECT)))
(RTL::REM%-8-BNDS-47
     (581 533
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (533 533
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (533 533
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (533 533
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (488 488
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (488 488
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (488 488
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (488 488
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (408 155 (:REWRITE |(< c (- x))|))
     (386 173 (:REWRITE DEFAULT-LESS-THAN-2))
     (385 35 (:REWRITE RTL::I8-J-2))
     (320 254 (:REWRITE DEFAULT-PLUS-2))
     (300 254 (:REWRITE DEFAULT-PLUS-1))
     (288 24 (:REWRITE ACL2-NUMBERP-X))
     (274 145
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (237 173 (:REWRITE DEFAULT-LESS-THAN-1))
     (224 147 (:REWRITE |(< (- x) c)|))
     (221 127 (:REWRITE SIMPLIFY-SUMS-<))
     (199 155
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (199 155
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (173 173 (:REWRITE THE-FLOOR-BELOW))
     (173 173 (:REWRITE THE-FLOOR-ABOVE))
     (156 155 (:REWRITE |(< (- x) (- y))|))
     (155 155
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (155 155
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (155 155
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (155 155
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (155 155
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (155 155
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (155 155
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (155 155
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (155 155 (:REWRITE |(< (/ x) (/ y))|))
     (151 145 (:REWRITE INTEGERP-<-CONSTANT))
     (147 145 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (145 145
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (145 145 (:REWRITE CONSTANT-<-INTEGERP))
     (139 67
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (133 109 (:REWRITE DEFAULT-TIMES-2))
     (132 24 (:REWRITE RATIONALP-X))
     (122 61
          (:TYPE-PRESCRIPTION RTL::Q%-CONSTRAINT))
     (120 120 (:TYPE-PRESCRIPTION RTL::I8%))
     (116 116
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (70 67 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (69 55 (:REWRITE DEFAULT-MINUS))
     (67 67
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (67 67
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (67 67
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (67 67 (:REWRITE |(equal c (/ x))|))
     (67 67 (:REWRITE |(equal c (- x))|))
     (67 67 (:REWRITE |(equal (/ x) c)|))
     (67 67 (:REWRITE |(equal (/ x) (/ y))|))
     (67 67 (:REWRITE |(equal (- x) c)|))
     (67 67 (:REWRITE |(equal (- x) (- y))|))
     (56 56 (:REWRITE REDUCE-INTEGERP-+))
     (56 56 (:REWRITE INTEGERP-MINUS-X))
     (56 56 (:META META-INTEGERP-CORRECT))
     (54 54 (:REWRITE |(< 0 (/ x))|))
     (54 54 (:REWRITE |(< 0 (* x y))|))
     (47 47
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (44 44 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
     (44 44 (:TYPE-PRESCRIPTION ABS))
     (43 43 (:REWRITE |(< (/ x) 0)|))
     (43 43 (:REWRITE |(< (* x y) 0)|))
     (41 41
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (41 41
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (28 28
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (28 28
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (25 18 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (24 24 (:REWRITE REDUCE-RATIONALP-+))
     (24 24 (:REWRITE REDUCE-RATIONALP-*))
     (24 24 (:REWRITE RATIONALP-MINUS-X))
     (24 24 (:META META-RATIONALP-CORRECT))
     (20 20 (:REWRITE DEFAULT-CDR))
     (20 20 (:REWRITE DEFAULT-CAR))
     (18 18 (:REWRITE |(< y (+ (- c) x))|))
     (18 18 (:REWRITE |(< x (+ c/d y))|))
     (12 12
         (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (12 10 (:REWRITE |(- (- x))|))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RTL::REM%-8-BNDS-48
     (3756 3532
           (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (3532 3532
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (3532 3532
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (3532 3532
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (1497 555 (:REWRITE |(< (- x) c)|))
     (1188 694 (:REWRITE DEFAULT-PLUS-2))
     (1158 532
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (1027 581 (:REWRITE DEFAULT-LESS-THAN-2))
     (999 124 (:REWRITE RTL::I8-J-2))
     (961 485 (:REWRITE SIMPLIFY-SUMS-<))
     (954 581 (:REWRITE DEFAULT-LESS-THAN-1))
     (940 10
          (:REWRITE |(<= x (/ y)) with (< y 0)|))
     (930 694 (:REWRITE DEFAULT-PLUS-1))
     (930 565 (:REWRITE |(< c (- x))|))
     (892 590 (:REWRITE DEFAULT-TIMES-2))
     (880 10
          (:REWRITE |(< (/ x) y) with (< x 0)|))
     (841 565
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (841 565
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (592 532 (:REWRITE CONSTANT-<-INTEGERP))
     (581 581 (:REWRITE THE-FLOOR-BELOW))
     (581 581 (:REWRITE THE-FLOOR-ABOVE))
     (568 565 (:REWRITE |(< (- x) (- y))|))
     (565 565
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (565 565
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (565 565
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (565 565
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (565 565
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (565 565
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (565 565
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (565 565
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (565 565 (:REWRITE |(< (/ x) (/ y))|))
     (560 560 (:TYPE-PRESCRIPTION RTL::I8%))
     (538 532 (:REWRITE INTEGERP-<-CONSTANT))
     (532 532
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (522 522 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (347 347
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (342 342
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (330 26 (:REWRITE ACL2-NUMBERP-X))
     (320 160
          (:TYPE-PRESCRIPTION RTL::Q%-CONSTRAINT))
     (276 276 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
     (276 276 (:TYPE-PRESCRIPTION ABS))
     (263 118
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (224 123 (:REWRITE DEFAULT-MINUS))
     (200 10 (:REWRITE |(* (* x y) z)|))
     (186 186
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (186 186
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (186 186
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (186 186
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (179 179 (:REWRITE |(< 0 (/ x))|))
     (179 179 (:REWRITE |(< 0 (* x y))|))
     (164 164 (:REWRITE REDUCE-INTEGERP-+))
     (164 164 (:REWRITE INTEGERP-MINUS-X))
     (164 164 (:META META-INTEGERP-CORRECT))
     (152 26 (:REWRITE RATIONALP-X))
     (150 10 (:REWRITE |(* y (* x z))|))
     (122 122
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (122 122
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (120 20 (:REWRITE |(* c (* d x))|))
     (118 118 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (118 118
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (118 118
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (118 118
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (118 118 (:REWRITE |(equal c (/ x))|))
     (118 118 (:REWRITE |(equal c (- x))|))
     (118 118 (:REWRITE |(equal (/ x) c)|))
     (118 118 (:REWRITE |(equal (/ x) (/ y))|))
     (118 118 (:REWRITE |(equal (- x) c)|))
     (118 118 (:REWRITE |(equal (- x) (- y))|))
     (100 20 (:REWRITE |(- (* c x))|))
     (94 47 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (84 84 (:REWRITE DEFAULT-CAR))
     (80 80 (:REWRITE |(< (/ x) 0)|))
     (80 80 (:REWRITE |(< (* x y) 0)|))
     (77 77
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (77 77
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (72 72 (:REWRITE DEFAULT-CDR))
     (57 57 (:REWRITE |(< y (+ (- c) x))|))
     (57 57 (:REWRITE |(< x (+ c/d y))|))
     (56 56
         (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (50 50 (:REWRITE |(* (- x) y)|))
     (26 26 (:REWRITE REDUCE-RATIONALP-+))
     (26 26 (:REWRITE REDUCE-RATIONALP-*))
     (26 26 (:REWRITE RATIONALP-MINUS-X))
     (26 26 (:META META-RATIONALP-CORRECT))
     (20 20 (:REWRITE |(* x (- y))|))
     (20 10
         (:REWRITE |(<= x (/ y)) with (< 0 y)|))
     (20 10
         (:REWRITE |(< (/ x) y) with (< 0 x)|))
     (19 13 (:REWRITE |(- (- x))|))
     (17 17
         (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (14 14 (:REWRITE |(< (+ c/d x) y)|))
     (14 14 (:REWRITE |(< (+ (- c) x) y)|))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RTL::REM%-8-BNDS-49
     (3706 256 (:REWRITE RTL::I8-J-2))
     (2686 1343
           (:TYPE-PRESCRIPTION RTL::Q%-CONSTRAINT))
     (1710 790
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (1034 790 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (790 790
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (790 790
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (790 790
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (790 790 (:REWRITE |(equal c (/ x))|))
     (790 790 (:REWRITE |(equal c (- x))|))
     (790 790 (:REWRITE |(equal (/ x) c)|))
     (790 790 (:REWRITE |(equal (/ x) (/ y))|))
     (790 790 (:REWRITE |(equal (- x) c)|))
     (790 790 (:REWRITE |(equal (- x) (- y))|))
     (764 436 (:REWRITE SIMPLIFY-SUMS-<))
     (764 436
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (764 436
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (600 436 (:REWRITE DEFAULT-LESS-THAN-2))
     (600 436 (:REWRITE DEFAULT-LESS-THAN-1))
     (564 282 (:REWRITE DEFAULT-TIMES-2))
     (444 443 (:REWRITE DEFAULT-PLUS-2))
     (443 443
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (443 443 (:REWRITE NORMALIZE-ADDENDS))
     (443 443 (:REWRITE DEFAULT-PLUS-1))
     (436 436 (:REWRITE THE-FLOOR-BELOW))
     (436 436 (:REWRITE THE-FLOOR-ABOVE))
     (436 436 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (436 436
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (436 436
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (436 436
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (436 436 (:REWRITE INTEGERP-<-CONSTANT))
     (436 436 (:REWRITE CONSTANT-<-INTEGERP))
     (436 436
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (436 436
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (436 436
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (436 436
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (436 436 (:REWRITE |(< c (- x))|))
     (436 436
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (436 436
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (436 436
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (436 436
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (436 436 (:REWRITE |(< (/ x) (/ y))|))
     (436 436 (:REWRITE |(< (- x) c)|))
     (436 436 (:REWRITE |(< (- x) (- y))|))
     (282 282
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (282 282 (:REWRITE DEFAULT-TIMES-1))
     (134 134
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (134 134
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (134 134 (:REWRITE REDUCE-INTEGERP-+))
     (134 134 (:REWRITE INTEGERP-MINUS-X))
     (134 134 (:REWRITE |(< (/ x) 0)|))
     (134 134 (:REWRITE |(< (* x y) 0)|))
     (134 134 (:META META-INTEGERP-CORRECT))
     (118 118 (:REWRITE ZP-OPEN))
     (45 45
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RTL::REM%-8-BNDS)
(RTL::QUOT8%-BNDS-1-1
     (48 48 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (48 48 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (48 48 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (48 48 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (24 15 (:REWRITE INTEGERP-<-CONSTANT))
     (20 20 (:REWRITE THE-FLOOR-BELOW))
     (20 20 (:REWRITE THE-FLOOR-ABOVE))
     (20 20 (:REWRITE DEFAULT-LESS-THAN-2))
     (20 20 (:REWRITE DEFAULT-LESS-THAN-1))
     (15 15 (:REWRITE SIMPLIFY-SUMS-<))
     (15 15
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (15 15 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (15 15
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (15 15
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (15 15
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (15 15 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
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
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (15 15
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (15 15
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (15 15
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (15 15 (:REWRITE |(< (/ x) (/ y))|))
     (15 15 (:REWRITE |(< (- x) c)|))
     (15 15 (:REWRITE |(< (- x) (- y))|))
     (9 9
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (9 9
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (9 9 (:REWRITE |(< (/ x) 0)|))
     (9 9 (:REWRITE |(< (* x y) 0)|))
     (5 2
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (4 4 (:REWRITE REDUCE-INTEGERP-+))
     (4 4 (:REWRITE INTEGERP-MINUS-X))
     (4 4 (:REWRITE RTL::I8-J-2))
     (4 4 (:META META-INTEGERP-CORRECT))
     (4 1 (:REWRITE RATIONALP-X))
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
     (1 1 (:REWRITE REDUCE-RATIONALP-+))
     (1 1 (:REWRITE REDUCE-RATIONALP-*))
     (1 1 (:REWRITE RATIONALP-MINUS-X))
     (1 1 (:META META-RATIONALP-CORRECT)))
(RTL::QUOT8%-BNDS-1-2
     (1140 165 (:REWRITE |(< c (- x))|))
     (960 30
          (:REWRITE |(< x (/ y)) with (< y 0)|))
     (915 30
          (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (540 30
          (:REWRITE |(< x (/ y)) with (< 0 y)|))
     (510 30
          (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (345 165
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (345 165
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (279 135 (:REWRITE INTEGERP-<-CONSTANT))
     (205 205 (:REWRITE THE-FLOOR-BELOW))
     (205 205 (:REWRITE THE-FLOOR-ABOVE))
     (205 205 (:REWRITE DEFAULT-LESS-THAN-2))
     (205 205 (:REWRITE DEFAULT-LESS-THAN-1))
     (180 180 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
     (180 180 (:TYPE-PRESCRIPTION ABS))
     (165 165
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (165 165
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (165 165
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (165 165
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (165 165
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (165 165
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (165 165
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (165 165
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (165 165 (:REWRITE |(< (/ x) (/ y))|))
     (165 165 (:REWRITE |(< (- x) (- y))|))
     (135 135 (:REWRITE SIMPLIFY-SUMS-<))
     (135 135
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (135 135
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (135 135
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (135 135 (:REWRITE CONSTANT-<-INTEGERP))
     (135 135 (:REWRITE |(< (- x) c)|))
     (135 30 (:REWRITE |(* y x)|))
     (120 120 (:REWRITE DEFAULT-TIMES-2))
     (120 120 (:REWRITE DEFAULT-TIMES-1))
     (120 30 (:REWRITE |(- (* c x))|))
     (105 105 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (90 90
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (53 53 (:REWRITE REDUCE-INTEGERP-+))
     (53 53 (:REWRITE INTEGERP-MINUS-X))
     (53 53 (:META META-INTEGERP-CORRECT))
     (38 21
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (30 30 (:REWRITE DEFAULT-MINUS))
     (30 30 (:REWRITE |(* (- x) y)|))
     (25 25 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (25 25 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (25 25 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (25 25 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (21 21 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (21 21
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (21 21
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (21 21
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (21 21 (:REWRITE |(equal c (/ x))|))
     (21 21 (:REWRITE |(equal c (- x))|))
     (21 21 (:REWRITE |(equal (/ x) c)|))
     (21 21 (:REWRITE |(equal (/ x) (/ y))|))
     (21 21 (:REWRITE |(equal (- x) c)|))
     (21 21 (:REWRITE |(equal (- x) (- y))|))
     (20 5 (:REWRITE RATIONALP-X))
     (15 15 (:REWRITE |(* x (- y))|))
     (11 11 (:REWRITE RTL::I8-J-2))
     (5 5 (:REWRITE REDUCE-RATIONALP-+))
     (5 5 (:REWRITE REDUCE-RATIONALP-*))
     (5 5 (:REWRITE RATIONALP-MINUS-X))
     (5 5 (:META META-RATIONALP-CORRECT))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RTL::QUOT8%-BNDS-1-3
     (7100 1055 (:REWRITE |(< c (- x))|))
     (5952 186
           (:REWRITE |(< x (/ y)) with (< y 0)|))
     (5673 186
           (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (3348 186
           (:REWRITE |(< x (/ y)) with (< 0 y)|))
     (3162 186
           (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (2171 1055
           (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (2171 1055
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (1835 869 (:REWRITE INTEGERP-<-CONSTANT))
     (1319 1319 (:REWRITE THE-FLOOR-BELOW))
     (1319 1319 (:REWRITE THE-FLOOR-ABOVE))
     (1319 1319 (:REWRITE DEFAULT-LESS-THAN-2))
     (1319 1319 (:REWRITE DEFAULT-LESS-THAN-1))
     (1116 1116 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
     (1116 1116 (:TYPE-PRESCRIPTION ABS))
     (1055 1055
           (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (1055 1055
           (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (1055 1055
           (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (1055 1055
           (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (1055 1055
           (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (1055 1055
           (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (1055 1055
           (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (1055 1055
           (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (1055 1055 (:REWRITE |(< (/ x) (/ y))|))
     (1055 1055 (:REWRITE |(< (- x) (- y))|))
     (869 869
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (869 869 (:REWRITE CONSTANT-<-INTEGERP))
     (869 869 (:REWRITE |(< (- x) c)|))
     (868 868 (:REWRITE SIMPLIFY-SUMS-<))
     (868 868
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (868 868
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (837 186 (:REWRITE |(* y x)|))
     (744 744 (:REWRITE DEFAULT-TIMES-2))
     (744 744 (:REWRITE DEFAULT-TIMES-1))
     (744 186 (:REWRITE |(- (* c x))|))
     (666 69
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (594 66 (:REWRITE ACL2-NUMBERP-X))
     (558 558
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (422 422 (:REWRITE REDUCE-INTEGERP-+))
     (422 422 (:REWRITE INTEGERP-MINUS-X))
     (422 422 (:META META-INTEGERP-CORRECT))
     (396 99 (:REWRITE RATIONALP-X))
     (380 380
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (380 380
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (380 380
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (380 380
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (186 186 (:REWRITE DEFAULT-MINUS))
     (186 186 (:REWRITE |(* (- x) y)|))
     (99 99 (:REWRITE REDUCE-RATIONALP-+))
     (99 99 (:REWRITE REDUCE-RATIONALP-*))
     (99 99 (:REWRITE RATIONALP-MINUS-X))
     (99 99 (:META META-RATIONALP-CORRECT))
     (93 93 (:REWRITE |(* x (- y))|))
     (69 69 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (69 69
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (69 69
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (69 69
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (69 69 (:REWRITE |(equal c (/ x))|))
     (69 69 (:REWRITE |(equal c (- x))|))
     (69 69 (:REWRITE |(equal (/ x) c)|))
     (69 69 (:REWRITE |(equal (/ x) (/ y))|))
     (69 69 (:REWRITE |(equal (- x) c)|))
     (69 69 (:REWRITE |(equal (- x) (- y))|))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (1 1 (:REWRITE |(< (/ x) 0)|))
     (1 1 (:REWRITE |(< (* x y) 0)|)))
(RTL::QUOT8%-BNDS-1-4
     (13904 13904
            (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (13904 13904
            (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (13904 13904
            (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (13904 13904
            (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (4359 880 (:REWRITE |(< c (- x))|))
     (2888 2888
           (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (2888 2888
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (2888 2888
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (2888 2888
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (2160 96 (:DEFINITION NTH))
     (1728 48 (:REWRITE ZP-OPEN))
     (1588 892
           (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (1588 892
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (1376 200 (:REWRITE RATIONALP-X))
     (1285 928 (:REWRITE DEFAULT-LESS-THAN-2))
     (1278 640
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (1094 773 (:REWRITE INTEGERP-<-CONSTANT))
     (1037 751
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (1037 751
           (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (1001 928 (:REWRITE DEFAULT-LESS-THAN-1))
     (953 773 (:REWRITE CONSTANT-<-INTEGERP))
     (943 880
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (928 928 (:REWRITE THE-FLOOR-BELOW))
     (928 928 (:REWRITE THE-FLOOR-ABOVE))
     (880 880
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (880 880
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (880 880
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (880 880
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (880 880
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (880 880
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (880 880
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (880 880 (:REWRITE |(< (/ x) (/ y))|))
     (880 880 (:REWRITE |(< (- x) (- y))|))
     (799 751 (:REWRITE SIMPLIFY-SUMS-<))
     (773 773 (:REWRITE |(< (- x) c)|))
     (696 696 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
     (696 696 (:TYPE-PRESCRIPTION ABS))
     (648 72 (:REWRITE ACL2-NUMBERP-X))
     (640 640 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (640 640
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (640 640
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (640 640
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (640 640 (:REWRITE |(equal c (/ x))|))
     (640 640 (:REWRITE |(equal c (- x))|))
     (640 640 (:REWRITE |(equal (/ x) c)|))
     (640 640 (:REWRITE |(equal (/ x) (/ y))|))
     (640 640 (:REWRITE |(equal (- x) c)|))
     (640 640 (:REWRITE |(equal (- x) (- y))|))
     (572 572 (:REWRITE DEFAULT-TIMES-2))
     (468 468 (:REWRITE REDUCE-INTEGERP-+))
     (468 468 (:REWRITE INTEGERP-MINUS-X))
     (468 468 (:META META-INTEGERP-CORRECT))
     (428 107 (:REWRITE |(- (* c x))|))
     (396 12
          (:REWRITE |(<= x (/ y)) with (< y 0)|))
     (396 12
          (:REWRITE |(<= x (/ y)) with (< 0 y)|))
     (396 12
          (:REWRITE |(< (/ x) y) with (< x 0)|))
     (396 12
          (:REWRITE |(< (/ x) y) with (< 0 x)|))
     (378 378
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (200 200 (:REWRITE REDUCE-RATIONALP-+))
     (200 200 (:REWRITE REDUCE-RATIONALP-*))
     (200 200 (:REWRITE RATIONALP-MINUS-X))
     (200 200 (:META META-RATIONALP-CORRECT))
     (133 133 (:REWRITE |(< 0 (/ x))|))
     (133 133 (:REWRITE |(< 0 (* x y))|))
     (129 129
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (129 129
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (110 110 (:REWRITE |(* (- x) y)|))
     (107 107 (:REWRITE DEFAULT-MINUS))
     (101 101 (:REWRITE |(< (/ x) 0)|))
     (101 101 (:REWRITE |(< (* x y) 0)|))
     (85 85
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (85 85
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (55 55 (:REWRITE |(* x (- y))|))
     (48 48
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (48 48 (:REWRITE NORMALIZE-ADDENDS))
     (48 48 (:REWRITE DEFAULT-PLUS-2))
     (48 48 (:REWRITE DEFAULT-PLUS-1))
     (48 48 (:REWRITE DEFAULT-CDR))
     (36 36
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (12 12
         (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (12 4 (:REWRITE RTL::REM%-8-BNDS-46)))
(RTL::QUOT8%-BNDS-1-5
     (88392 3712 (:DEFINITION NTH))
     (69832 1856 (:REWRITE ZP-OPEN))
     (34688 33760
            (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (33760 33760
            (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (33760 33760
            (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (33760 33760
            (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (23704 3382 (:REWRITE RATIONALP-X))
     (13924 13924
            (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (13924 13924
            (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (13924 13924
            (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (13924 13924
            (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (10310 1254 (:REWRITE ACL2-NUMBERP-X))
     (9264 464
           (:REWRITE |(<= x (/ y)) with (< y 0)|))
     (9264 464
           (:REWRITE |(<= x (/ y)) with (< 0 y)|))
     (9264 464
           (:REWRITE |(< (/ x) y) with (< x 0)|))
     (9264 464
           (:REWRITE |(< (/ x) y) with (< 0 x)|))
     (9049 5120 (:REWRITE DEFAULT-LESS-THAN-2))
     (8329 4393 (:REWRITE CONSTANT-<-INTEGERP))
     (7888 7888 (:TYPE-PRESCRIPTION RTL::I8%))
     (6381 4393
           (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (6381 4393
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (5880 5880 (:REWRITE REDUCE-INTEGERP-+))
     (5880 5880 (:REWRITE INTEGERP-MINUS-X))
     (5880 5880 (:META META-INTEGERP-CORRECT))
     (5755 4393
           (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (5694 4393
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (5185 5120 (:REWRITE DEFAULT-LESS-THAN-1))
     (5120 5120 (:REWRITE THE-FLOOR-BELOW))
     (5120 5120 (:REWRITE THE-FLOOR-ABOVE))
     (4937 4393 (:REWRITE SIMPLIFY-SUMS-<))
     (4803 4571 (:REWRITE DEFAULT-TIMES-2))
     (4393 4393
           (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (4393 4393
           (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (4393 4393 (:REWRITE INTEGERP-<-CONSTANT))
     (4393 4393
           (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (4393 4393
           (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (4393 4393
           (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (4393 4393
           (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (4393 4393 (:REWRITE |(< c (- x))|))
     (4393 4393
           (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (4393 4393
           (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (4393 4393
           (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (4393 4393
           (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (4393 4393 (:REWRITE |(< (/ x) (/ y))|))
     (4393 4393 (:REWRITE |(< (- x) c)|))
     (4393 4393 (:REWRITE |(< (- x) (- y))|))
     (3382 3382 (:REWRITE REDUCE-RATIONALP-+))
     (3382 3382 (:REWRITE REDUCE-RATIONALP-*))
     (3382 3382 (:REWRITE RATIONALP-MINUS-X))
     (3382 3382 (:META META-RATIONALP-CORRECT))
     (2319 2319
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (2319 2319
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (2319 2319 (:REWRITE |(< 0 (/ x))|))
     (2319 2319 (:REWRITE |(< 0 (* x y))|))
     (2073 891
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (1988 1988 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
     (1988 1988 (:TYPE-PRESCRIPTION ABS))
     (1856 1856
           (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (1856 1856 (:REWRITE NORMALIZE-ADDENDS))
     (1856 1856 (:REWRITE DEFAULT-PLUS-2))
     (1856 1856 (:REWRITE DEFAULT-PLUS-1))
     (1856 1856 (:REWRITE DEFAULT-CDR))
     (1756 1756
           (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (891 891 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (891 891
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (891 891
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (891 891
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (891 891 (:REWRITE |(equal c (/ x))|))
     (891 891 (:REWRITE |(equal c (- x))|))
     (891 891 (:REWRITE |(equal (/ x) c)|))
     (891 891 (:REWRITE |(equal (/ x) (/ y))|))
     (891 891 (:REWRITE |(equal (- x) c)|))
     (891 891 (:REWRITE |(equal (- x) (- y))|))
     (802 802
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (802 802
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (802 802 (:REWRITE |(< (/ x) 0)|))
     (802 802 (:REWRITE |(< (* x y) 0)|))
     (530 530
          (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RTL::QUOT8%-BNDS-1-6
     (6702 268 (:DEFINITION NTH))
     (5246 140 (:REWRITE ZP-OPEN))
     (2694 244 (:REWRITE RTL::I8-J-2))
     (2482 2354
           (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (2354 2354
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (2354 2354
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (2354 2354
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (1470 470
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (1360 173 (:REWRITE RATIONALP-X))
     (1014 1014
           (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (1014 1014
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (1014 1014
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (1014 1014
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (841 512 (:REWRITE DEFAULT-LESS-THAN-2))
     (722 82 (:REWRITE ACL2-NUMBERP-X))
     (628 512 (:REWRITE DEFAULT-LESS-THAN-1))
     (615 447
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (612 447
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (600 600 (:TYPE-PRESCRIPTION RTL::I8%))
     (575 447 (:REWRITE CONSTANT-<-INTEGERP))
     (512 512 (:REWRITE THE-FLOOR-BELOW))
     (512 512 (:REWRITE THE-FLOOR-ABOVE))
     (506 447 (:REWRITE SIMPLIFY-SUMS-<))
     (478 447 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (454 447
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (447 447 (:REWRITE INTEGERP-<-CONSTANT))
     (447 447
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (447 447
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (447 447
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (447 447
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (447 447 (:REWRITE |(< c (- x))|))
     (447 447
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (447 447
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (447 447
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (447 447
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (447 447 (:REWRITE |(< (/ x) (/ y))|))
     (447 447 (:REWRITE |(< (- x) c)|))
     (447 447 (:REWRITE |(< (- x) (- y))|))
     (440 195
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (372 186
          (:TYPE-PRESCRIPTION RTL::Q%-CONSTRAINT))
     (350 350 (:REWRITE REDUCE-INTEGERP-+))
     (350 350 (:REWRITE INTEGERP-MINUS-X))
     (350 350 (:META META-INTEGERP-CORRECT))
     (306 18
          (:REWRITE |(<= x (/ y)) with (< y 0)|))
     (306 18
          (:REWRITE |(<= x (/ y)) with (< 0 y)|))
     (306 18
          (:REWRITE |(< (/ x) y) with (< x 0)|))
     (306 18
          (:REWRITE |(< (/ x) y) with (< 0 x)|))
     (269 195 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (258 48
          (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (233 233
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (195 195
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (195 195
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (195 195
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (195 195 (:REWRITE |(equal c (/ x))|))
     (195 195 (:REWRITE |(equal c (- x))|))
     (195 195 (:REWRITE |(equal (/ x) c)|))
     (195 195 (:REWRITE |(equal (/ x) (/ y))|))
     (195 195 (:REWRITE |(equal (- x) c)|))
     (195 195 (:REWRITE |(equal (- x) (- y))|))
     (175 175
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (175 175 (:REWRITE NORMALIZE-ADDENDS))
     (175 175 (:REWRITE DEFAULT-PLUS-2))
     (175 175 (:REWRITE DEFAULT-PLUS-1))
     (173 173
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (173 173
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (173 173 (:REWRITE REDUCE-RATIONALP-+))
     (173 173 (:REWRITE REDUCE-RATIONALP-*))
     (173 173 (:REWRITE RATIONALP-MINUS-X))
     (173 173 (:REWRITE |(< 0 (/ x))|))
     (173 173 (:META META-RATIONALP-CORRECT))
     (134 134 (:REWRITE DEFAULT-CDR))
     (89 89
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (89 89
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (89 89 (:REWRITE |(< (/ x) 0)|))
     (89 89 (:REWRITE |(< (* x y) 0)|))
     (34 34
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (13 13
         (:REWRITE |(< (* x y) 0) rationalp (* x y)|)))
(RTL::QUOT8%-BNDS-1
 (1681 259 (:REWRITE DEFAULT-TIMES-2))
 (1019 216 (:REWRITE DEFAULT-PLUS-2))
 (916
  916
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (916 916
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (916
     916
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (916 916
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (916 78 (:REWRITE INTEGERP-<-CONSTANT))
 (786 94
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (761 5 (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (758 4 (:REWRITE EVEN-AND-ODD-ALTERNATE))
 (713 5
      (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (636 216 (:REWRITE DEFAULT-PLUS-1))
 (496 248
      (:TYPE-PRESCRIPTION RTL::Q%-CONSTRAINT))
 (427 259 (:REWRITE DEFAULT-TIMES-1))
 (422 22 (:REWRITE RTL::I8-J-2))
 (356 78
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (284 82 (:REWRITE CONSTANT-<-INTEGERP))
 (277 94 (:REWRITE DEFAULT-LESS-THAN-1))
 (190 4 (:LINEAR EXPT-X->=-X))
 (190 4 (:LINEAR EXPT-X->-X))
 (189 94 (:REWRITE DEFAULT-LESS-THAN-2))
 (188 72 (:REWRITE SIMPLIFY-SUMS-<))
 (186 6 (:REWRITE |(equal x (/ y))|))
 (154 46 (:REWRITE DEFAULT-MINUS))
 (140 140
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (140 12 (:REWRITE |(* y (* x z))|))
 (120 6 (:REWRITE |(not (equal x (/ y)))|))
 (118 82 (:REWRITE |(< (- x) (- y))|))
 (114 4 (:LINEAR EXPT-<-1-TWO))
 (108 54 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (106 4 (:LINEAR EXPT->-1-ONE))
 (104 104
      (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
 (97 42
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (96 96 (:TYPE-PRESCRIPTION COLLECT-*))
 (94 94 (:REWRITE THE-FLOOR-BELOW))
 (94 94 (:REWRITE THE-FLOOR-ABOVE))
 (86 82
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (86 82
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (82 82
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (82 82
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (82 82
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (82 82
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (82 82 (:REWRITE |(< c (- x))|))
 (82 82
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (82 82
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (82 82
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (82 82 (:REWRITE |(< (/ x) (/ y))|))
 (82 82 (:REWRITE |(< (- x) c)|))
 (78 78
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (71 69 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (64 64 (:REWRITE |arith (expt x c)|))
 (58 58 (:REWRITE ARITH-NORMALIZE-ADDENDS))
 (54 42 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (54 42
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (52 52 (:REWRITE DEFAULT-EXPT-2))
 (52 52 (:REWRITE DEFAULT-EXPT-1))
 (52 52 (:REWRITE |(expt 1/c n)|))
 (52 52 (:REWRITE |(expt (- x) n)|))
 (43 5
     (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (43 5 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (42 42
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (42 42
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (42 42 (:REWRITE |(equal c (/ x))|))
 (42 42 (:REWRITE |(equal c (- x))|))
 (42 42 (:REWRITE |(equal (/ x) c)|))
 (42 42 (:REWRITE |(equal (/ x) (/ y))|))
 (42 42 (:REWRITE |(equal (- x) c)|))
 (42 42 (:REWRITE |(equal (- x) (- y))|))
 (36 18
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (32 32 (:REWRITE |arith (expt 1/c n)|))
 (28 4 (:REWRITE RATIONALP-X))
 (27 27 (:REWRITE REDUCE-INTEGERP-+))
 (27 27 (:REWRITE INTEGERP-MINUS-X))
 (27 27 (:META META-INTEGERP-CORRECT))
 (22 22 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
 (22 22 (:TYPE-PRESCRIPTION ABS))
 (22 22 (:REWRITE |(* (- x) y)|))
 (20 20 (:REWRITE |arith (* c (* d x))|))
 (20 20 (:REWRITE |(< (+ c/d x) y)|))
 (20 20 (:REWRITE |(< (+ (- c) x) y)|))
 (20 4 (:REWRITE |(- (* c x))|))
 (19 19 (:REWRITE ZP-OPEN))
 (19 5 (:REWRITE |(< (/ x) y) with (< x 0)|))
 (19 5 (:REWRITE |(< (/ x) y) with (< 0 x)|))
 (18 18
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (18 18
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (18 18
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (18 18 (:REWRITE |arith (* (- x) y)|))
 (18 18 (:REWRITE BUBBLE-DOWN-*-MATCH-3))
 (18 18 (:REWRITE |(* c (* d x))|))
 (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (16 8 (:REWRITE COLLECT-*-PROBLEM-FINDER))
 (15 1
     (:REWRITE |(<= x (/ y)) with (< y 0)|))
 (15 1
     (:REWRITE |(<= x (/ y)) with (< 0 y)|))
 (14 14 (:REWRITE |(< 0 (* x y))|))
 (13 13 (:REWRITE |(< (* x y) 0)|))
 (12 12 (:REWRITE |(* a (/ a) b)|))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (10 10 (:REWRITE |(< 0 (/ x))|))
 (9 9
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (9 9
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (9 9 (:REWRITE |(< (/ x) 0)|))
 (8 8
    (:TYPE-PRESCRIPTION FMT-TO-COMMENT-WINDOW))
 (8 8
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (8 8
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (8 8
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (8 8
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (6 6 (:REWRITE |(< y (+ (- c) x))|))
 (6 6 (:REWRITE |(< x (+ c/d y))|))
 (4 4 (:REWRITE REDUCE-RATIONALP-+))
 (4 4 (:REWRITE REDUCE-RATIONALP-*))
 (4 4 (:REWRITE RATIONALP-MINUS-X))
 (4 4
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (4 4
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (4 4 (:META META-RATIONALP-CORRECT))
 (4 4 (:LINEAR EXPT-LINEAR-UPPER-<))
 (4 4 (:LINEAR EXPT-LINEAR-LOWER-<))
 (4 4 (:LINEAR EXPT->=-1-TWO))
 (4 4 (:LINEAR EXPT->-1-TWO))
 (4 4 (:LINEAR EXPT-<=-1-ONE))
 (4 4 (:LINEAR EXPT-<-1-ONE))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 (1 1 (:REWRITE |arith (+ c (+ d x))|)))
(RTL::QUOT8%-BNDS-2
 (14960 2190 (:REWRITE DEFAULT-TIMES-2))
 (12229 2367 (:REWRITE DEFAULT-PLUS-2))
 (10850
  10850
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (10850
      10850
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (10850
     10850
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (10850 10850
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (10788 1152
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (7007 2367 (:REWRITE DEFAULT-PLUS-1))
 (6576 3288
       (:TYPE-PRESCRIPTION RTL::Q%-CONSTRAINT))
 (5909 309 (:REWRITE RTL::I8-J-2))
 (4641 928
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (3812 984 (:REWRITE CONSTANT-<-INTEGERP))
 (3504 1152 (:REWRITE DEFAULT-LESS-THAN-2))
 (3465 2190 (:REWRITE DEFAULT-TIMES-1))
 (2660 56 (:LINEAR EXPT-X->=-X))
 (2660 56 (:LINEAR EXPT-X->-X))
 (2513 1152 (:REWRITE DEFAULT-LESS-THAN-1))
 (2468 844 (:REWRITE SIMPLIFY-SUMS-<))
 (2100 588 (:REWRITE DEFAULT-MINUS))
 (1960 168 (:REWRITE |(* y (* x z))|))
 (1642 1642
       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (1596 56 (:LINEAR EXPT-<-1-TWO))
 (1484 56 (:LINEAR EXPT->-1-ONE))
 (1236 984 (:REWRITE |(< (- x) (- y))|))
 (1152 1152 (:REWRITE THE-FLOOR-BELOW))
 (1152 1152 (:REWRITE THE-FLOOR-ABOVE))
 (1092 336 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (1014 428
       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (988 984
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (988 984
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (984 984
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (984 984
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (984 984
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (984 984
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (984 984 (:REWRITE |(< c (- x))|))
 (984 984
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (984 984
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (984 984
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (984 984 (:REWRITE |(< (/ x) (/ y))|))
 (984 984 (:REWRITE |(< (- x) c)|))
 (934 928 (:REWRITE INTEGERP-<-CONSTANT))
 (928 928
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (873 871 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (846 846
      (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
 (588 588 (:REWRITE DEFAULT-EXPT-2))
 (588 588 (:REWRITE DEFAULT-EXPT-1))
 (588 588 (:REWRITE |(expt 1/c n)|))
 (588 588 (:REWRITE |(expt (- x) n)|))
 (550 428 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (532 532 (:REWRITE |arith (expt x c)|))
 (504 252
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (482 482 (:REWRITE ARITH-NORMALIZE-ADDENDS))
 (428 428
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (428 428
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (428 428
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (428 428 (:REWRITE |(equal c (/ x))|))
 (428 428 (:REWRITE |(equal c (- x))|))
 (428 428 (:REWRITE |(equal (/ x) c)|))
 (428 428 (:REWRITE |(equal (/ x) (/ y))|))
 (428 428 (:REWRITE |(equal (- x) c)|))
 (428 428 (:REWRITE |(equal (- x) (- y))|))
 (392 56 (:REWRITE RATIONALP-X))
 (308 308 (:REWRITE |arith (expt 1/c n)|))
 (266 266 (:REWRITE ZP-OPEN))
 (266 70
      (:REWRITE |(< (/ x) y) with (< x 0)|))
 (266 70
      (:REWRITE |(< (/ x) y) with (< 0 x)|))
 (252 252
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (252 252
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (252 252
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (252 252 (:REWRITE |arith (* c (* d x))|))
 (252 252 (:REWRITE |(* (- x) y)|))
 (224 224
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (224 224
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (224 224
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (210 14
      (:REWRITE |(<= x (/ y)) with (< y 0)|))
 (210 14
      (:REWRITE |(<= x (/ y)) with (< 0 y)|))
 (196 196 (:REWRITE |(< 0 (* x y))|))
 (184 184 (:REWRITE REDUCE-INTEGERP-+))
 (184 184 (:REWRITE INTEGERP-MINUS-X))
 (184 184 (:META META-INTEGERP-CORRECT))
 (182 182 (:REWRITE |(< (* x y) 0)|))
 (172 172 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
 (172 172 (:TYPE-PRESCRIPTION ABS))
 (168 168 (:REWRITE |(* a (/ a) b)|))
 (140 140
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (140 140
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (140 140 (:REWRITE |(< y (+ (- c) x))|))
 (140 140 (:REWRITE |(< x (+ c/d y))|))
 (140 140 (:REWRITE |(< 0 (/ x))|))
 (140 140 (:REWRITE |(< (+ c/d x) y)|))
 (140 140 (:REWRITE |(< (+ (- c) x) y)|))
 (126 126 (:REWRITE |arith (* (- x) y)|))
 (126 126
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (126 126
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (126 126 (:REWRITE |(< (/ x) 0)|))
 (112 112
      (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (112 112
      (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (112 112
      (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (112 112
      (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (84 84 (:REWRITE BUBBLE-DOWN-*-MATCH-3))
 (84 84 (:REWRITE |(* c (* d x))|))
 (56 56 (:REWRITE REDUCE-RATIONALP-+))
 (56 56 (:REWRITE REDUCE-RATIONALP-*))
 (56 56 (:REWRITE RATIONALP-MINUS-X))
 (56 56 (:REWRITE FOLD-CONSTS-IN-+))
 (56 56
     (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (56 56
     (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (56 56 (:META META-RATIONALP-CORRECT))
 (56 56 (:LINEAR EXPT-LINEAR-UPPER-<))
 (56 56 (:LINEAR EXPT-LINEAR-LOWER-<))
 (56 56 (:LINEAR EXPT->=-1-TWO))
 (56 56 (:LINEAR EXPT->-1-TWO))
 (56 56 (:LINEAR EXPT-<=-1-ONE))
 (56 56 (:LINEAR EXPT-<-1-ONE))
 (46 1 (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (43 1
     (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (42 42 (:REWRITE |arith (+ c (+ d x))|))
 (21 21
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (2 1
    (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (2 1
    (:REWRITE |(< x (/ y)) with (< y 0)|)))
(RTL::QUOT8%-BNDS-3
 (530 24
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (212 16 (:REWRITE CONSTANT-<-INTEGERP))
 (188 2 (:LINEAR EXPT-X->=-X))
 (188 2 (:LINEAR EXPT-X->-X))
 (106 2 (:LINEAR EXPT-<=-1-TWO))
 (104 2 (:LINEAR EXPT->-1-ONE))
 (88 8 (:REWRITE |(* y (* x z))|))
 (74
  74
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (74 74
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (74 74
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (74 74
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (74 74
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (56 24 (:REWRITE DEFAULT-TIMES-2))
 (36 36 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (36 36 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (36 36 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (24 24 (:REWRITE THE-FLOOR-BELOW))
 (24 24 (:REWRITE THE-FLOOR-ABOVE))
 (24 24 (:REWRITE DEFAULT-TIMES-1))
 (24 24 (:REWRITE DEFAULT-LESS-THAN-2))
 (24 24 (:REWRITE DEFAULT-LESS-THAN-1))
 (16 16
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (16 16
     (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
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
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (16 16
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (16 16
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (16 16
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (16 16 (:REWRITE |(< (/ x) (/ y))|))
 (16 16 (:REWRITE |(< (- x) c)|))
 (16 16 (:REWRITE |(< (- x) (- y))|))
 (12 12 (:REWRITE SIMPLIFY-SUMS-<))
 (12 12
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (12 12
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (12 12 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (12 12 (:REWRITE INTEGERP-<-CONSTANT))
 (10 10 (:REWRITE |arith (expt x c)|))
 (10 10 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (8 8 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
 (8 8 (:TYPE-PRESCRIPTION ABS))
 (8 8 (:REWRITE |arith (expt 1/c n)|))
 (8 8
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (8 8 (:REWRITE |(< 0 (* x y))|))
 (8 8 (:REWRITE |(* a (/ a) b)|))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (4 4 (:REWRITE |(< 0 (/ x))|))
 (4 4
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (4 4 (:REWRITE |(< (/ x) y) with (< x 0)|))
 (4 4 (:REWRITE |(< (/ x) y) with (< 0 x)|))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (2 2 (:REWRITE |arith (* c (* d x))|))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-TWO))
 (2 2 (:LINEAR EXPT-<-1-ONE)))
(RTL::QUOT8%-BNDS-4
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
 (21 3 (:REWRITE DEFAULT-TIMES-2))
 (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (4 3 (:REWRITE DEFAULT-TIMES-1))
 (2 2 (:REWRITE DEFAULT-EXPT-2))
 (2 2 (:REWRITE DEFAULT-EXPT-1))
 (2 2 (:REWRITE |(expt 1/c n)|))
 (2 2 (:REWRITE |(expt (- x) n)|))
 (1 1 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (1 1 (:REWRITE NORMALIZE-ADDENDS))
 (1 1 (:REWRITE DEFAULT-PLUS-2))
 (1 1 (:REWRITE DEFAULT-PLUS-1)))
(RTL::QUOT8%-BNDS-5)
(RTL::QUOT8%-BNDS-6
 (394
  394
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (394 394
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (394
     394
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (394 394
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (326 72 (:REWRITE DEFAULT-TIMES-2))
 (245 72 (:REWRITE DEFAULT-TIMES-1))
 (108 108
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (108 108
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (108 108
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (53 14 (:REWRITE DEFAULT-LESS-THAN-2))
 (50 14 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (48 9 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (46 1
     (:REWRITE |(<= x (/ y)) with (< 0 y)|))
 (38 20 (:REWRITE DEFAULT-PLUS-2))
 (32 14 (:REWRITE DEFAULT-LESS-THAN-1))
 (27 9 (:REWRITE SIMPLIFY-SUMS-<))
 (25 1 (:LINEAR EXPT-X->=-X))
 (25 1 (:LINEAR EXPT-X->-X))
 (24 20 (:REWRITE DEFAULT-PLUS-1))
 (20 20 (:REWRITE DEFAULT-EXPT-2))
 (20 20 (:REWRITE DEFAULT-EXPT-1))
 (20 20 (:REWRITE |(expt 1/c n)|))
 (20 20 (:REWRITE |(expt (- x) n)|))
 (18 14
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (18 14
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (17 11 (:REWRITE CONSTANT-<-INTEGERP))
 (16 11
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (14 14 (:REWRITE THE-FLOOR-BELOW))
 (14 14 (:REWRITE THE-FLOOR-ABOVE))
 (13 11
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (11 11 (:REWRITE INTEGERP-<-CONSTANT))
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
 (8 8 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (8 8
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (5 4 (:REWRITE |(< (/ x) y) with (< x 0)|))
 (5 2
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (4 4 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
 (4 4 (:TYPE-PRESCRIPTION ABS))
 (4 4 (:REWRITE DEFAULT-MINUS))
 (4 4 (:REWRITE |(* (- x) y)|))
 (3 3 (:REWRITE REDUCE-INTEGERP-+))
 (3 3 (:REWRITE INTEGERP-MINUS-X))
 (3 3 (:META META-INTEGERP-CORRECT))
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
 (2 2 (:REWRITE |(< y (+ (- c) x))|))
 (2 2 (:REWRITE |(< x (+ c/d y))|))
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
    (:REWRITE |(<= x (/ y)) with (< y 0)|))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<))
 (1 1 (:LINEAR EXPT->=-1-TWO))
 (1 1 (:LINEAR EXPT->-1-TWO))
 (1 1 (:LINEAR EXPT-<=-1-TWO))
 (1 1 (:LINEAR EXPT-<=-1-ONE))
 (1 1 (:LINEAR EXPT-<-1-TWO))
 (1 1 (:LINEAR EXPT-<-1-ONE)))
(RTL::QUOT8%-BNDS-7
 (339
  339
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (339 339
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (339
     339
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (339 339
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (87 87 (:REWRITE |arith (expt x c)|))
 (83 83 (:REWRITE |arith (expt 1/c n)|))
 (72 16 (:REWRITE DEFAULT-TIMES-2))
 (47 1
     (:REWRITE |(<= x (/ y)) with (< 0 y)|))
 (42 6 (:REWRITE DEFAULT-PLUS-2))
 (37 7 (:REWRITE DEFAULT-LESS-THAN-2))
 (35 5
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (35 5 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (32 32 (:REWRITE |arith (* (- x) y)|))
 (32 5 (:REWRITE SIMPLIFY-SUMS-<))
 (28 16 (:REWRITE DEFAULT-TIMES-1))
 (19 19 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (19 19 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (19 19 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (16 16
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (16 16
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (16 16
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (16 16
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (16 7 (:REWRITE DEFAULT-LESS-THAN-1))
 (11 11 (:REWRITE |arith (* c (* d x))|))
 (11 5 (:REWRITE CONSTANT-<-INTEGERP))
 (10 6
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (10 6
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (10 5
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (8 8 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (8 8 (:LINEAR EXPT-LINEAR-UPPER-<))
 (8 8 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (8 8 (:LINEAR EXPT-LINEAR-LOWER-<))
 (8 8 (:LINEAR EXPT->=-1-TWO))
 (8 8 (:LINEAR EXPT->-1-TWO))
 (8 8 (:LINEAR EXPT-<=-1-ONE))
 (8 8 (:LINEAR EXPT-<-1-ONE))
 (7 7 (:REWRITE THE-FLOOR-BELOW))
 (7 7 (:REWRITE THE-FLOOR-ABOVE))
 (7 5 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (6 6
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (6 6 (:REWRITE NORMALIZE-ADDENDS))
 (6 6 (:REWRITE DEFAULT-PLUS-1))
 (5 5 (:REWRITE INTEGERP-<-CONSTANT))
 (5 5 (:REWRITE DEFAULT-EXPT-2))
 (5 5 (:REWRITE DEFAULT-EXPT-1))
 (5 5 (:REWRITE |(expt 1/c n)|))
 (5 5 (:REWRITE |(expt (- x) n)|))
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
 (5 2
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (4 4 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
 (4 4 (:TYPE-PRESCRIPTION ABS))
 (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (3 2 (:REWRITE |(< (/ x) y) with (< x 0)|))
 (2 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (2 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (2 2
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (2 2 (:REWRITE REDUCE-INTEGERP-+))
 (2 2
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (2 2 (:REWRITE INTEGERP-MINUS-X))
 (2 2
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (2 2 (:REWRITE DEFAULT-MINUS))
 (2 2 (:REWRITE |(equal c (/ x))|))
 (2 2 (:REWRITE |(equal c (- x))|))
 (2 2 (:REWRITE |(equal (/ x) c)|))
 (2 2 (:REWRITE |(equal (/ x) (/ y))|))
 (2 2 (:REWRITE |(equal (- x) c)|))
 (2 2 (:REWRITE |(equal (- x) (- y))|))
 (2 2 (:REWRITE |(< y (+ (- c) x))|))
 (2 2 (:META META-INTEGERP-CORRECT))
 (2 1
    (:REWRITE |(<= x (/ y)) with (< y 0)|))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE |(* (- x) y)|)))
(RTL::QUOT8%-BNDS-8
 (8931 57
       (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (4049 457
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (3641
  3641
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (3641
      3641
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (3641
     3641
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (3641 3641
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (3203 696 (:REWRITE DEFAULT-TIMES-2))
 (3065 951 (:REWRITE DEFAULT-PLUS-2))
 (2471 951 (:REWRITE DEFAULT-PLUS-1))
 (2126 61 (:REWRITE |(* y x)|))
 (1369 381 (:REWRITE CONSTANT-<-INTEGERP))
 (1288 361 (:REWRITE INTEGERP-<-CONSTANT))
 (1256 628
       (:TYPE-PRESCRIPTION RTL::Q%-CONSTRAINT))
 (1209 361
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (1009 457 (:REWRITE DEFAULT-LESS-THAN-1))
 (950 20 (:LINEAR EXPT-X->=-X))
 (950 20 (:LINEAR EXPT-X->-X))
 (949 696 (:REWRITE DEFAULT-TIMES-1))
 (843 457 (:REWRITE DEFAULT-LESS-THAN-2))
 (700 60 (:REWRITE |(* y (* x z))|))
 (699 313 (:REWRITE SIMPLIFY-SUMS-<))
 (641 381 (:REWRITE |(< (- x) c)|))
 (641 381 (:REWRITE |(< (- x) (- y))|))
 (570 20 (:LINEAR EXPT-<-1-TWO))
 (549 397
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (530 20 (:LINEAR EXPT->-1-ONE))
 (476 108 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (457 457 (:REWRITE THE-FLOOR-BELOW))
 (457 457 (:REWRITE THE-FLOOR-ABOVE))
 (447 225
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (423 423 (:REWRITE |arith (expt x c)|))
 (420 420
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (400 140 (:REWRITE DEFAULT-MINUS))
 (381 381
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (381 381
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (381 381
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (381 381
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (381 381 (:REWRITE |(< c (- x))|))
 (381 381
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (381 381
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (381 381
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (381 381
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (381 381 (:REWRITE |(< (/ x) (/ y))|))
 (361 361
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (353 73
      (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (336 336 (:TYPE-PRESCRIPTION COLLECT-*))
 (302 266 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (247 57
      (:REWRITE |(< x (/ y)) with (< y 0)|))
 (229 225
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (227 227 (:REWRITE |arith (expt 1/c n)|))
 (225 225 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (225 225
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (225 225
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (225 225 (:REWRITE |(equal c (/ x))|))
 (225 225 (:REWRITE |(equal c (- x))|))
 (225 225 (:REWRITE |(equal (/ x) c)|))
 (225 225 (:REWRITE |(equal (/ x) (/ y))|))
 (225 225 (:REWRITE |(equal (- x) c)|))
 (225 225 (:REWRITE |(equal (- x) (- y))|))
 (221 113 (:REWRITE INTEGERP-MINUS-X))
 (214 214 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
 (214 214 (:TYPE-PRESCRIPTION ABS))
 (211 211 (:REWRITE |arith (* (- x) y)|))
 (131 131
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (131 131
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (131 131
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (113 113 (:REWRITE REDUCE-INTEGERP-+))
 (113 113 (:META META-INTEGERP-CORRECT))
 (103 103 (:REWRITE DEFAULT-EXPT-2))
 (103 103 (:REWRITE DEFAULT-EXPT-1))
 (103 103 (:REWRITE |(expt (- x) n)|))
 (100 100 (:REWRITE |(* (- x) y)|))
 (88 22
     (:REWRITE |(< (/ x) y) with (< 0 x)|))
 (76 2
     (:REWRITE |(<= x (/ y)) with (< 0 y)|))
 (75 75 (:REWRITE |(< (+ c/d x) y)|))
 (75 75 (:REWRITE |(< (+ (- c) x) y)|))
 (74 74 (:REWRITE |(< (* x y) 0)|))
 (62 2 (:REWRITE BUBBLE-DOWN-*-BUBBLE-DOWN))
 (60 60 (:REWRITE |(< 0 (* x y))|))
 (60 60 (:REWRITE |(* a (/ a) b)|))
 (54 54
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (54 54
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (54 54 (:REWRITE |(< (/ x) 0)|))
 (50 50 (:REWRITE |(< y (+ (- c) x))|))
 (50 50 (:REWRITE |(< x (+ c/d y))|))
 (40 40
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (40 40
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (40 40 (:REWRITE |(< 0 (/ x))|))
 (40 40
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (40 40
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (40 40
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (40 40
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (36 18 (:REWRITE COLLECT-*-PROBLEM-FINDER))
 (22 22
     (:REWRITE |(< (/ x) y) with (< x 0)|))
 (22 1 (:REWRITE |(not (equal x (/ y)))|))
 (22 1 (:REWRITE |(equal x (/ y))|))
 (21 21
     (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (20 20
     (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (20 20
     (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (20 20 (:LINEAR EXPT-LINEAR-UPPER-<))
 (20 20 (:LINEAR EXPT-LINEAR-LOWER-<))
 (20 20 (:LINEAR EXPT->=-1-TWO))
 (20 20 (:LINEAR EXPT->-1-TWO))
 (20 20 (:LINEAR EXPT-<=-1-ONE))
 (20 20 (:LINEAR EXPT-<-1-ONE))
 (18 18
     (:TYPE-PRESCRIPTION FMT-TO-COMMENT-WINDOW))
 (12 12
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE BUBBLE-DOWN-*-MATCH-3))
 (2 2
    (:REWRITE |(<= x (/ y)) with (< y 0)|)))
(RTL::QUOT8%-BNDS-9
 (530 24
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (212 16 (:REWRITE CONSTANT-<-INTEGERP))
 (188 2 (:LINEAR EXPT-X->=-X))
 (188 2 (:LINEAR EXPT-X->-X))
 (106 2 (:LINEAR EXPT-<=-1-TWO))
 (104 2 (:LINEAR EXPT->-1-ONE))
 (88 8 (:REWRITE |(* y (* x z))|))
 (65
  65
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (65 65
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (65 65
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (65 65
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (65 65
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (56 24 (:REWRITE DEFAULT-TIMES-2))
 (24 24 (:REWRITE THE-FLOOR-BELOW))
 (24 24 (:REWRITE THE-FLOOR-ABOVE))
 (24 24 (:REWRITE DEFAULT-TIMES-1))
 (24 24 (:REWRITE DEFAULT-LESS-THAN-2))
 (24 24 (:REWRITE DEFAULT-LESS-THAN-1))
 (16 16
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
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
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (16 16
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (16 16
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (16 16
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (16 16 (:REWRITE |(< (/ x) (/ y))|))
 (16 16 (:REWRITE |(< (- x) c)|))
 (16 16 (:REWRITE |(< (- x) (- y))|))
 (13 13
     (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
 (12 12 (:REWRITE SIMPLIFY-SUMS-<))
 (12 12
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (12 12
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (12 12 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (12 12 (:REWRITE INTEGERP-<-CONSTANT))
 (10 10 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (9 9 (:REWRITE |arith (expt x c)|))
 (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (8 8 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
 (8 8 (:TYPE-PRESCRIPTION ABS))
 (8 8
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (8 8 (:REWRITE |(< 0 (* x y))|))
 (8 8 (:REWRITE |(* a (/ a) b)|))
 (7 7 (:REWRITE |arith (expt 1/c n)|))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (4 4 (:REWRITE |(< 0 (/ x))|))
 (4 4
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (4 4 (:REWRITE |(< (/ x) y) with (< x 0)|))
 (4 4 (:REWRITE |(< (/ x) y) with (< 0 x)|))
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
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-TWO))
 (2 2 (:LINEAR EXPT-<-1-ONE))
 (1 1 (:REWRITE |arith (- (* c x))|))
 (1 1 (:REWRITE |arith (* c (* d x))|))
 (1 1 (:REWRITE |arith (* (- x) y)|)))
(RTL::QUOT8%-BNDS-10)
(RTL::QUOT8%-BNDS-11
 (316
  316
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (316 316
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (316
     316
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (316 316
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (242 50 (:REWRITE DEFAULT-TIMES-1))
 (220 50 (:REWRITE DEFAULT-TIMES-2))
 (46 10 (:REWRITE DEFAULT-LESS-THAN-2))
 (44 8 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (42 5 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (32 10 (:REWRITE DEFAULT-LESS-THAN-1))
 (30 10
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (28 10 (:REWRITE DEFAULT-PLUS-2))
 (23 5 (:REWRITE SIMPLIFY-SUMS-<))
 (14 10 (:REWRITE DEFAULT-PLUS-1))
 (11 11 (:REWRITE DEFAULT-EXPT-2))
 (11 11 (:REWRITE DEFAULT-EXPT-1))
 (11 11 (:REWRITE |(expt 1/c n)|))
 (11 11 (:REWRITE |(expt (- x) n)|))
 (10 10 (:REWRITE THE-FLOOR-BELOW))
 (10 10 (:REWRITE THE-FLOOR-ABOVE))
 (10 10
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (10 10
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
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
 (10 10 (:REWRITE |(< (- x) c)|))
 (10 10 (:REWRITE |(< (- x) (- y))|))
 (7 7 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (5 5 (:REWRITE REDUCE-INTEGERP-+))
 (5 5 (:REWRITE INTEGERP-MINUS-X))
 (5 5 (:META META-INTEGERP-CORRECT))
 (5 2
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (4 4 (:REWRITE DEFAULT-MINUS))
 (4 4 (:REWRITE |(* (- x) y)|))
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
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
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
 (2 2 (:REWRITE |(< (+ c/d x) y)|))
 (2 2 (:REWRITE |(< (+ (- c) x) y)|))
 (1 1 (:REWRITE ZP-OPEN)))
(RTL::QUOT8%-BNDS-12
 (343
  343
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (343 343
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (343
     343
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (343 343
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (87 87 (:REWRITE |arith (expt x c)|))
 (83 83 (:REWRITE |arith (expt 1/c n)|))
 (62 7 (:REWRITE DEFAULT-PLUS-2))
 (45 7 (:REWRITE DEFAULT-PLUS-1))
 (44 4
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (27 27 (:REWRITE |arith (* (- x) y)|))
 (26 5 (:REWRITE DEFAULT-LESS-THAN-2))
 (25 5 (:REWRITE DEFAULT-LESS-THAN-1))
 (22 3 (:REWRITE SIMPLIFY-SUMS-<))
 (16 16
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (16 16
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (16 16
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (16 16
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (15 5
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (14 5 (:REWRITE |(< (- x) (- y))|))
 (12 2 (:REWRITE DEFAULT-TIMES-2))
 (12 2 (:REWRITE DEFAULT-TIMES-1))
 (11 11 (:REWRITE |arith (* c (* d x))|))
 (11 2 (:REWRITE DEFAULT-MINUS))
 (10 1 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (8 8 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (8 8 (:LINEAR EXPT-LINEAR-UPPER-<))
 (8 8 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (8 8 (:LINEAR EXPT-LINEAR-LOWER-<))
 (8 8 (:LINEAR EXPT->=-1-TWO))
 (8 8 (:LINEAR EXPT->-1-TWO))
 (8 8 (:LINEAR EXPT-<=-1-ONE))
 (8 8 (:LINEAR EXPT-<-1-ONE))
 (5 5 (:REWRITE THE-FLOOR-BELOW))
 (5 5 (:REWRITE THE-FLOOR-ABOVE))
 (5 5
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (5 5
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
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
 (5 2
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (3 3
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (3 3 (:REWRITE DEFAULT-EXPT-2))
 (3 3 (:REWRITE DEFAULT-EXPT-1))
 (3 3 (:REWRITE |(expt 1/c n)|))
 (3 3 (:REWRITE |(expt (- x) n)|))
 (2 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (2 2
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (2 2 (:REWRITE REDUCE-INTEGERP-+))
 (2 2
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (2 2 (:REWRITE INTEGERP-MINUS-X))
 (2 2
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (2 2 (:REWRITE |(equal c (/ x))|))
 (2 2 (:REWRITE |(equal c (- x))|))
 (2 2 (:REWRITE |(equal (/ x) c)|))
 (2 2 (:REWRITE |(equal (/ x) (/ y))|))
 (2 2 (:REWRITE |(equal (- x) c)|))
 (2 2 (:REWRITE |(equal (- x) (- y))|))
 (2 2 (:REWRITE |(< (+ c/d x) y)|))
 (2 2 (:REWRITE |(< (+ (- c) x) y)|))
 (2 2 (:META META-INTEGERP-CORRECT))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (1 1 (:REWRITE |(< y (+ (- c) x))|))
 (1 1 (:REWRITE |(< x (+ c/d y))|)))
(RTL::QUOT8%-BNDS-13
 (3749 309
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (2197
  2197
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (2197
      2197
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (2197
     2197
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (2197 2197
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1499 515 (:REWRITE DEFAULT-PLUS-2))
 (1229 249 (:REWRITE CONSTANT-<-INTEGERP))
 (1210 515 (:REWRITE DEFAULT-PLUS-1))
 (1140 570
       (:TYPE-PRESCRIPTION RTL::Q%-CONSTRAINT))
 (1054 301 (:REWRITE DEFAULT-TIMES-2))
 (950 20 (:LINEAR EXPT-X->=-X))
 (950 20 (:LINEAR EXPT-X->-X))
 (752 225
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (700 60 (:REWRITE |(* y (* x z))|))
 (674 309 (:REWRITE DEFAULT-LESS-THAN-2))
 (570 20 (:LINEAR EXPT-<-1-TWO))
 (530 20 (:LINEAR EXPT->-1-ONE))
 (473 309 (:REWRITE DEFAULT-LESS-THAN-1))
 (446 223
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (359 207 (:REWRITE SIMPLIFY-SUMS-<))
 (357 249 (:REWRITE |(< c (- x))|))
 (318 301 (:REWRITE DEFAULT-TIMES-1))
 (309 309 (:REWRITE THE-FLOOR-BELOW))
 (309 309 (:REWRITE THE-FLOOR-ABOVE))
 (276 276
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (267 249 (:REWRITE |(< (- x) (- y))|))
 (249 249 (:REWRITE |arith (expt x c)|))
 (249 249
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (249 249
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (249 249
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (249 249
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (249 249
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (249 249
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (249 249
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (249 249
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (249 249
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (249 249 (:REWRITE |(< (/ x) (/ y))|))
 (249 249 (:REWRITE |(< (- x) c)|))
 (232 106 (:REWRITE DEFAULT-MINUS))
 (229 229
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (229 229 (:REWRITE INTEGERP-<-CONSTANT))
 (223 223 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (223 223
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (223 223
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (223 223
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (223 223 (:REWRITE |(equal c (/ x))|))
 (223 223 (:REWRITE |(equal c (- x))|))
 (223 223 (:REWRITE |(equal (/ x) c)|))
 (223 223 (:REWRITE |(equal (/ x) (/ y))|))
 (223 223 (:REWRITE |(equal (- x) c)|))
 (223 223 (:REWRITE |(equal (- x) (- y))|))
 (196 34 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (160 160 (:REWRITE |arith (expt 1/c n)|))
 (124 124 (:REWRITE |arith (* (- x) y)|))
 (105 105
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (105 105
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (105 105
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (92 92 (:REWRITE |(* (- x) y)|))
 (74 74 (:REWRITE |(< (* x y) 0)|))
 (60 60 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
 (60 60 (:TYPE-PRESCRIPTION ABS))
 (60 60 (:REWRITE |(< 0 (* x y))|))
 (60 60 (:REWRITE |(* a (/ a) b)|))
 (55 55 (:REWRITE DEFAULT-EXPT-2))
 (55 55 (:REWRITE DEFAULT-EXPT-1))
 (55 55 (:REWRITE |(expt 1/c n)|))
 (55 55 (:REWRITE |(expt (- x) n)|))
 (54 54
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (54 54
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (54 54 (:REWRITE REDUCE-INTEGERP-+))
 (54 54 (:REWRITE INTEGERP-MINUS-X))
 (54 54 (:REWRITE |(< (/ x) 0)|))
 (54 54 (:META META-INTEGERP-CORRECT))
 (40 40
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (40 40
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (40 40 (:REWRITE |(< 0 (/ x))|))
 (40 40
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (40 40
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (40 40
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (40 40
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (35 35 (:REWRITE |(< y (+ (- c) x))|))
 (35 35 (:REWRITE |(< x (+ c/d y))|))
 (20 20
     (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (20 20
     (:REWRITE |(< (/ x) y) with (< x 0)|))
 (20 20
     (:REWRITE |(< (/ x) y) with (< 0 x)|))
 (20 20
     (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (20 20 (:LINEAR EXPT-LINEAR-UPPER-<))
 (20 20 (:LINEAR EXPT-LINEAR-LOWER-<))
 (20 20 (:LINEAR EXPT->=-1-TWO))
 (20 20 (:LINEAR EXPT->-1-TWO))
 (20 20 (:LINEAR EXPT-<=-1-ONE))
 (20 20 (:LINEAR EXPT-<-1-ONE))
 (18 18 (:REWRITE |(< (+ c/d x) y)|))
 (18 18 (:REWRITE |(< (+ (- c) x) y)|))
 (12 12
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (2 2 (:REWRITE ZP-OPEN)))
(RTL::QUOT8%-BNDS
     (387 9 (:REWRITE |(< x (/ y)) with (< 0 y)|))
     (362 9
          (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (203 43
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (93 43 (:REWRITE INTEGERP-<-CONSTANT))
     (92 14 (:REWRITE |(equal (/ x) c)|))
     (79 43
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (79 43
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (67 43 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (64 43 (:REWRITE DEFAULT-LESS-THAN-1))
     (52 40 (:REWRITE DEFAULT-PLUS-1))
     (46 43 (:REWRITE DEFAULT-LESS-THAN-2))
     (43 43 (:REWRITE THE-FLOOR-BELOW))
     (43 43 (:REWRITE THE-FLOOR-ABOVE))
     (43 43
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (43 43 (:REWRITE CONSTANT-<-INTEGERP))
     (43 43
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (43 43
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (43 43
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (43 43
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (43 43 (:REWRITE |(< c (- x))|))
     (43 43
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (43 43
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (43 43
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (43 43
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (43 43 (:REWRITE |(< (/ x) (/ y))|))
     (43 43 (:REWRITE |(< (- x) c)|))
     (43 43 (:REWRITE |(< (- x) (- y))|))
     (43 9 (:REWRITE |(* y x)|))
     (41 27 (:REWRITE DEFAULT-TIMES-2))
     (40 40 (:REWRITE DEFAULT-PLUS-2))
     (36 36 (:TYPE-PRESCRIPTION RTL::ABS-TYPE))
     (36 36 (:TYPE-PRESCRIPTION ABS))
     (34 34 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (34 27 (:REWRITE DEFAULT-TIMES-1))
     (18 18
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (16 9
         (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (16 9 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (14 14
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (14 14
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (14 14 (:REWRITE |(equal c (/ x))|))
     (14 14 (:REWRITE |(equal (/ x) (/ y))|))
     (14 14 (:REWRITE |(equal (- x) (- y))|))
     (12 12 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (11 8
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (10 10 (:REWRITE REDUCE-INTEGERP-+))
     (10 10 (:REWRITE INTEGERP-MINUS-X))
     (10 10 (:META META-INTEGERP-CORRECT))
     (8 8 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (8 8
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (8 8 (:REWRITE |(equal c (- x))|))
     (8 8 (:REWRITE |(equal (- x) c)|))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (6 6 (:REWRITE DEFAULT-DIVIDE))
     (6 6 (:REWRITE |(not (equal x (/ y)))|))
     (6 6 (:REWRITE |(equal x (/ y))|))
     (6 6 (:REWRITE |(/ (/ x))|))
     (4 4
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (1 1 (:REWRITE |(< (/ x) 0)|))
     (1 1 (:REWRITE |(< (* x y) 0)|)))
(RTL::SRT-SQRT-RAD-8)
