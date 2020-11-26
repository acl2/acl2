(RTL::ALL-BVECP
     (62 54 (:REWRITE DEFAULT-PLUS-1))
     (54 54 (:REWRITE DEFAULT-PLUS-2))
     (18 18 (:REWRITE THE-FLOOR-BELOW))
     (18 18 (:REWRITE THE-FLOOR-ABOVE))
     (18 18 (:REWRITE DEFAULT-LESS-THAN-2))
     (18 18 (:REWRITE DEFAULT-LESS-THAN-1))
     (15 15
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (15 15
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
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
     (15 15 (:REWRITE |(< (- x) (- y))|))
     (13 13
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (13 13 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (13 13
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (13 13 (:REWRITE INTEGERP-<-CONSTANT))
     (13 13 (:REWRITE CONSTANT-<-INTEGERP))
     (11 11
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (10 10 (:REWRITE DEFAULT-MINUS))
     (8 8 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (7 7 (:REWRITE |(+ c (+ d x))|))
     (6 6 (:REWRITE |(< y (+ (- c) x))|))
     (6 6 (:REWRITE |(< x (+ c/d y))|))
     (5 5 (:REWRITE |(< (/ x) 0)|))
     (5 5 (:REWRITE |(< (+ c/d x) y)|))
     (5 5 (:REWRITE |(< (+ (- c) x) y)|))
     (5 5 (:REWRITE |(< (* x y) 0)|))
     (4 2 (:REWRITE GL::NFIX-NATP))
     (3 3 (:REWRITE FOLD-CONSTS-IN-+))
     (3 3 (:REWRITE |(< 0 (/ x))|))
     (3 3 (:REWRITE |(< 0 (* x y))|))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (2 2 (:REWRITE REDUCE-INTEGERP-+))
     (2 2 (:REWRITE INTEGERP-MINUS-X))
     (2 2 (:META META-INTEGERP-CORRECT)))
(RTL::ALL-BVECP-INTEGERP
     (21 21 (:REWRITE THE-FLOOR-BELOW))
     (21 21 (:REWRITE THE-FLOOR-ABOVE))
     (21 21 (:REWRITE SIMPLIFY-SUMS-<))
     (21 21
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (21 21 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (21 21
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (21 21
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (21 21
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (21 21 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (21 21 (:REWRITE INTEGERP-<-CONSTANT))
     (21 21 (:REWRITE DEFAULT-LESS-THAN-2))
     (21 21 (:REWRITE DEFAULT-LESS-THAN-1))
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
     (12 12 (:REWRITE REDUCE-INTEGERP-+))
     (12 12 (:REWRITE INTEGERP-MINUS-X))
     (12 12 (:META META-INTEGERP-CORRECT))
     (10 10
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (10 10
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (10 10 (:REWRITE |(< (/ x) 0)|))
     (10 10 (:REWRITE |(< (* x y) 0)|))
     (2 2
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (2 2 (:REWRITE NORMALIZE-ADDENDS))
     (2 2 (:REWRITE DEFAULT-PLUS-2))
     (2 2 (:REWRITE DEFAULT-PLUS-1)))
(RTL::ALL-BVECP-BVECP
     (21 21 (:TYPE-PRESCRIPTION NATP))
     (21 21 (:REWRITE THE-FLOOR-BELOW))
     (21 21 (:REWRITE THE-FLOOR-ABOVE))
     (21 21 (:REWRITE SIMPLIFY-SUMS-<))
     (21 21
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (21 21 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (21 21
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (21 21
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (21 21
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (21 21 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (21 21 (:REWRITE INTEGERP-<-CONSTANT))
     (21 21 (:REWRITE DEFAULT-LESS-THAN-2))
     (21 21 (:REWRITE DEFAULT-LESS-THAN-1))
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
     (10 10
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (10 10
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (10 10 (:REWRITE REDUCE-INTEGERP-+))
     (10 10 (:REWRITE INTEGERP-MINUS-X))
     (10 10 (:REWRITE |(< (/ x) 0)|))
     (10 10 (:REWRITE |(< (* x y) 0)|))
     (10 10 (:META META-INTEGERP-CORRECT))
     (2 2
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (2 2 (:REWRITE NORMALIZE-ADDENDS))
     (2 2 (:REWRITE DEFAULT-PLUS-2))
     (2 2 (:REWRITE DEFAULT-PLUS-1)))
(RTL::ALL-BVECP-LEQ
     (168 119
          (:TYPE-PRESCRIPTION RTL::ALL-BVECP-INTEGERP))
     (135 122
          (:TYPE-PRESCRIPTION RTL::ALL-BVECP-BVECP))
     (133 49 (:REWRITE SIMPLIFY-SUMS-<))
     (62 62 (:TYPE-PRESCRIPTION NATP))
     (60 6 (:REWRITE |(+ y x)|))
     (49 49 (:REWRITE THE-FLOOR-BELOW))
     (49 49 (:REWRITE THE-FLOOR-ABOVE))
     (49 49
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (49 49
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (49 49
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (49 49
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (49 49 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (49 49 (:REWRITE INTEGERP-<-CONSTANT))
     (49 49 (:REWRITE DEFAULT-LESS-THAN-2))
     (49 49 (:REWRITE DEFAULT-LESS-THAN-1))
     (49 49 (:REWRITE CONSTANT-<-INTEGERP))
     (49 49
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (49 49
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (49 49
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (49 49
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (49 49 (:REWRITE |(< c (- x))|))
     (49 49
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (49 49
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (49 49
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (49 49
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (49 49 (:REWRITE |(< (/ x) (/ y))|))
     (49 49 (:REWRITE |(< (- x) c)|))
     (49 49 (:REWRITE |(< (- x) (- y))|))
     (47 47 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (46 10 (:REWRITE NORMALIZE-ADDENDS))
     (39 3 (:REWRITE |(+ y (+ x z))|))
     (31 25 (:REWRITE DEFAULT-PLUS-1))
     (25 25 (:REWRITE DEFAULT-PLUS-2))
     (19 19
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (19 19
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (19 19 (:REWRITE REDUCE-INTEGERP-+))
     (19 19 (:REWRITE INTEGERP-MINUS-X))
     (19 19 (:REWRITE |(< (/ x) 0)|))
     (19 19 (:REWRITE |(< (* x y) 0)|))
     (19 19 (:META META-INTEGERP-CORRECT))
     (12 6 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
     (9 9 (:DEFINITION FIX))
     (6 6 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (6 6 (:REWRITE |(+ x (- x))|))
     (4 4
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (3 3 (:REWRITE |(< y (+ (- c) x))|))
     (3 3 (:REWRITE |(< x (+ c/d y))|)))
(RTL::ALL-BVECP-SUBRANGE
     (89 89 (:REWRITE THE-FLOOR-BELOW))
     (89 89 (:REWRITE THE-FLOOR-ABOVE))
     (89 89 (:REWRITE DEFAULT-LESS-THAN-2))
     (89 89 (:REWRITE DEFAULT-LESS-THAN-1))
     (87 3
         (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (87 3 (:REWRITE |(< x (/ y)) with (< 0 y)|))
     (80 80
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (80 80
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (80 80
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
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
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (80 80
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (80 80
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (80 80
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (80 80 (:REWRITE |(< (/ x) (/ y))|))
     (80 80 (:REWRITE |(< (- x) c)|))
     (80 80 (:REWRITE |(< (- x) (- y))|))
     (77 77 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (71 71 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (69 69 (:TYPE-PRESCRIPTION NATP))
     (45 39 (:REWRITE DEFAULT-PLUS-1))
     (39 39 (:REWRITE DEFAULT-PLUS-2))
     (25 25 (:REWRITE REDUCE-INTEGERP-+))
     (25 25 (:REWRITE INTEGERP-MINUS-X))
     (25 25 (:META META-INTEGERP-CORRECT))
     (24 24
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (24 24
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (24 24 (:REWRITE |(< (/ x) 0)|))
     (24 24 (:REWRITE |(< (* x y) 0)|))
     (18 18 (:REWRITE DEFAULT-TIMES-2))
     (18 18 (:REWRITE DEFAULT-TIMES-1))
     (15 15
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (15 3 (:REWRITE |(+ c (+ d x))|))
     (13 13
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (13 13
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (13 13 (:REWRITE |(equal c (/ x))|))
     (13 13 (:REWRITE |(equal (/ x) (/ y))|))
     (13 13 (:REWRITE |(equal (- x) (- y))|))
     (12 12
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (12 12
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (12 12 (:REWRITE |(< 0 (/ x))|))
     (12 12 (:REWRITE |(< 0 (* x y))|))
     (10 10
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (10 10 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (10 10
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (10 10
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (10 10
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (10 10 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
     (10 10 (:REWRITE |(equal c (- x))|))
     (10 10 (:REWRITE |(equal (- x) c)|))
     (6 6 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (5 5 (:REWRITE |(< y (+ (- c) x))|))
     (5 5 (:REWRITE |(< x (+ c/d y))|))
     (4 4 (:REWRITE |(< (+ c/d x) y)|))
     (4 4 (:REWRITE |(< (+ (- c) x) y)|))
     (3 3 (:REWRITE DEFAULT-DIVIDE))
     (3 3 (:REWRITE |(not (equal x (/ y)))|))
     (3 3 (:REWRITE |(equal x (/ y))|))
     (3 3
        (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (3 3
        (:REWRITE |(< x (/ y)) with (< y 0)|)))
(RTL::SUM-SIMPLE)
(RTL::BVECP-SUM-SIMPLE (96 6 (:REWRITE ACL2-NUMBERP-X))
                       (48 6 (:REWRITE RATIONALP-X))
                       (39 3 (:REWRITE RTL::BITS-TAIL-GEN))
                       (17 11 (:REWRITE DEFAULT-PLUS-2))
                       (9 9 (:REWRITE REDUCE-INTEGERP-+))
                       (9 9 (:REWRITE INTEGERP-MINUS-X))
                       (9 9 (:META META-INTEGERP-CORRECT))
                       (9 3 (:REWRITE RTL::BITS-TAIL))
                       (8 8
                          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                       (8 8 (:REWRITE NORMALIZE-ADDENDS))
                       (6 6 (:REWRITE REDUCE-RATIONALP-+))
                       (6 6 (:REWRITE REDUCE-RATIONALP-*))
                       (6 6 (:REWRITE RATIONALP-MINUS-X))
                       (6 6 (:REWRITE RTL::ALL-BVECP-INTEGERP))
                       (6 6 (:META META-RATIONALP-CORRECT))
                       (4 4 (:REWRITE ZP-OPEN))
                       (3 3 (:REWRITE RTL::BITS-REVERSE-INDICES))
                       (3 3 (:REWRITE RTL::BITS-NEG-INDICES)))
(RTL::SUM-RANGE
     (20 16 (:REWRITE DEFAULT-PLUS-1))
     (18 2 (:REWRITE ACL2-NUMBERP-X))
     (16 16 (:REWRITE DEFAULT-PLUS-2))
     (9 9 (:REWRITE THE-FLOOR-BELOW))
     (9 9 (:REWRITE THE-FLOOR-ABOVE))
     (9 9 (:REWRITE DEFAULT-LESS-THAN-2))
     (8 8
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (8 8 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (8 8 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (8 8
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (8 8
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (8 8 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
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
     (8 2 (:REWRITE RATIONALP-X))
     (4 4 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (4 4 (:REWRITE |(< (/ x) 0)|))
     (4 4 (:REWRITE |(< (+ c/d x) y)|))
     (4 4 (:REWRITE |(< (+ (- c) x) y)|))
     (4 4 (:REWRITE |(< (* x y) 0)|))
     (2 2 (:REWRITE REDUCE-RATIONALP-+))
     (2 2 (:REWRITE REDUCE-RATIONALP-*))
     (2 2 (:REWRITE REDUCE-INTEGERP-+))
     (2 2 (:REWRITE RATIONALP-MINUS-X))
     (2 2
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (2 2 (:REWRITE INTEGERP-MINUS-X))
     (2 2 (:META META-RATIONALP-CORRECT))
     (2 2 (:META META-INTEGERP-CORRECT))
     (1 1 (:REWRITE ZP-OPEN))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (1 1 (:REWRITE |(< 0 (/ x))|))
     (1 1 (:REWRITE |(< 0 (* x y))|)))
(RTL::INTEGERP-SUM-RANGE
     (1306 25 (:REWRITE ACL2-NUMBERP-X))
     (1058 25 (:REWRITE RATIONALP-X))
     (835 25 (:REWRITE RTL::ALL-BVECP-INTEGERP))
     (708 26 (:REWRITE |(< (+ (- c) x) y)|))
     (268 12 (:REWRITE ZP-OPEN))
     (118 96 (:REWRITE DEFAULT-PLUS-2))
     (89 89 (:REWRITE THE-FLOOR-BELOW))
     (89 89 (:REWRITE THE-FLOOR-ABOVE))
     (89 89
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (89 89
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (89 89 (:REWRITE DEFAULT-LESS-THAN-2))
     (89 89 (:REWRITE DEFAULT-LESS-THAN-1))
     (85 17 (:REWRITE |(+ c (+ d x))|))
     (68 68
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (68 68 (:REWRITE NORMALIZE-ADDENDS))
     (64 64
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
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
     (61 61 (:REWRITE SIMPLIFY-SUMS-<))
     (61 61
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (61 61 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (50 11 (:REWRITE RTL::ALL-BVECP-LEQ))
     (34 34 (:REWRITE REDUCE-INTEGERP-+))
     (34 34 (:REWRITE INTEGERP-MINUS-X))
     (34 34 (:META META-INTEGERP-CORRECT))
     (29 5 (:REWRITE RTL::ALL-BVECP-BVECP))
     (27 27 (:REWRITE |(< y (+ (- c) x))|))
     (27 27 (:REWRITE |(< x (+ c/d y))|))
     (26 26 (:REWRITE |(< (+ c/d x) y)|))
     (25 25 (:REWRITE REDUCE-RATIONALP-+))
     (25 25 (:REWRITE REDUCE-RATIONALP-*))
     (25 25 (:REWRITE RATIONALP-MINUS-X))
     (25 25 (:META META-RATIONALP-CORRECT))
     (23 23 (:REWRITE |(< (* x y) 0)|))
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (8 8 (:REWRITE |(< 0 (/ x))|))
     (8 8 (:REWRITE |(< 0 (* x y))|))
     (7 7 (:REWRITE |(< (/ x) 0)|))
     (5 5 (:TYPE-PRESCRIPTION RTL::BVECP))
     (5 5
        (:TYPE-PRESCRIPTION RTL::ALL-BVECP-BVECP))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON)))
(RTL::SUM-RANGE-SUM-SIMPLE
 (454 10 (:REWRITE RTL::BITS-TAIL-GEN))
 (42 24 (:REWRITE DEFAULT-PLUS-2))
 (36 24 (:REWRITE DEFAULT-PLUS-1))
 (33 17 (:REWRITE DEFAULT-LESS-THAN-1))
 (32 16 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (30 10 (:REWRITE RTL::BITS-TAIL))
 (26 16
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (22 22
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (22 22 (:REWRITE NORMALIZE-ADDENDS))
 (17 17 (:REWRITE THE-FLOOR-BELOW))
 (17 17 (:REWRITE THE-FLOOR-ABOVE))
 (17 17
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (17 17
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (17 17
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (17 17 (:REWRITE INTEGERP-<-CONSTANT))
 (17 17 (:REWRITE DEFAULT-LESS-THAN-2))
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
 (16 16 (:REWRITE SIMPLIFY-SUMS-<))
 (12 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (12 4
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (12 4
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (10 10 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (10 10 (:REWRITE RTL::BITS-NEG-INDICES))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (8
   8
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (8
  8
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (8 4 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (7 7 (:REWRITE RTL::ALL-BVECP-LEQ))
 (6 6 (:REWRITE ZP-OPEN))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (6 6 (:REWRITE |(< 0 (/ x))|))
 (6 6 (:REWRITE |(< 0 (* x y))|))
 (4 4
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (4 4 (:REWRITE REDUCE-INTEGERP-+))
 (4 4
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (4 4 (:REWRITE INTEGERP-MINUS-X))
 (4 4
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (4 4 (:REWRITE |(equal c (/ x))|))
 (4 4 (:REWRITE |(equal c (- x))|))
 (4 4 (:REWRITE |(equal (/ x) c)|))
 (4 4 (:REWRITE |(equal (/ x) (/ y))|))
 (4 4 (:REWRITE |(equal (- x) c)|))
 (4 4 (:REWRITE |(equal (- x) (- y))|))
 (4 4 (:REWRITE |(< (+ c/d x) y)|))
 (4 4 (:REWRITE |(< (+ (- c) x) y)|))
 (4 4 (:META META-INTEGERP-CORRECT))
 (3 3
    (:TYPE-PRESCRIPTION RTL::ALL-BVECP-BVECP))
 (3 3 (:REWRITE RTL::ALL-BVECP-BVECP))
 (3 3 (:REWRITE |(< (/ x) 0)|))
 (3 3 (:REWRITE |(< (* x y) 0)|))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2 (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
 (2 2
    (:REWRITE INTEGERP-+-REDUCE-CONSTANT)))
(RTL::SUM-RANGES
     (5185 91 (:REWRITE ACL2-NUMBERP-X))
     (4277 91 (:REWRITE RATIONALP-X))
     (3460 91 (:REWRITE RTL::ALL-BVECP-INTEGERP))
     (898 479 (:REWRITE DEFAULT-PLUS-2))
     (372 372 (:REWRITE THE-FLOOR-BELOW))
     (372 372 (:REWRITE THE-FLOOR-ABOVE))
     (372 372
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (372 372
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (372 372 (:REWRITE DEFAULT-LESS-THAN-2))
     (372 372 (:REWRITE DEFAULT-LESS-THAN-1))
     (317 65 (:REWRITE |(+ c (+ d x))|))
     (285 285
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (258 258
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (258 258 (:REWRITE INTEGERP-<-CONSTANT))
     (258 258 (:REWRITE CONSTANT-<-INTEGERP))
     (258 258
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (258 258
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (258 258
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (258 258
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (258 258 (:REWRITE |(< c (- x))|))
     (258 258
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (258 258
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (258 258
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (258 258
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (258 258 (:REWRITE |(< (/ x) (/ y))|))
     (258 258 (:REWRITE |(< (- x) c)|))
     (258 258 (:REWRITE |(< (- x) (- y))|))
     (244 244
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (211 27 (:REWRITE RTL::ALL-BVECP-LEQ))
     (116 116 (:REWRITE |(< y (+ (- c) x))|))
     (116 116 (:REWRITE |(< x (+ c/d y))|))
     (109 109 (:REWRITE REDUCE-INTEGERP-+))
     (109 109 (:REWRITE INTEGERP-MINUS-X))
     (109 109 (:META META-INTEGERP-CORRECT))
     (106 106 (:REWRITE |(< (+ c/d x) y)|))
     (91 91 (:REWRITE REDUCE-RATIONALP-+))
     (91 91 (:REWRITE REDUCE-RATIONALP-*))
     (91 91 (:REWRITE RATIONALP-MINUS-X))
     (91 91 (:META META-RATIONALP-CORRECT))
     (82 82 (:REWRITE |(< (* x y) 0)|))
     (82 6
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (82 6
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (53 5 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
     (41 41 (:REWRITE |(< 0 (* x y))|))
     (36 36 (:REWRITE DEFAULT-TIMES-2))
     (36 36 (:REWRITE DEFAULT-TIMES-1))
     (36 12 (:REWRITE RTL::ALL-BVECP-BVECP))
     (32 32
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (32 32
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (32 32 (:REWRITE |(< 0 (/ x))|))
     (24 18 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (22 22 (:REWRITE |(< (/ x) 0)|))
     (18 18
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (18 18
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (10 10 (:TYPE-PRESCRIPTION RTL::BVECP))
     (10 10
         (:TYPE-PRESCRIPTION RTL::ALL-BVECP-BVECP))
     (9 9
        (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (9 9
        (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (9 9 (:REWRITE |(< x (/ y)) with (< y 0)|))
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
     (2 2 (:REWRITE FOLD-CONSTS-IN-+))
     (2 2 (:REWRITE |(equal (+ (- c) x) y)|))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RTL::SUM-RANGE-SPLIT
 (2586 9 (:DEFINITION RTL::SUM-RANGE))
 (992 189 (:REWRITE DEFAULT-PLUS-1))
 (704 704
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (704 704
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (704 704
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (607 189 (:REWRITE DEFAULT-PLUS-2))
 (509 5 (:REWRITE ACL2-NUMBERP-X))
 (414 5 (:REWRITE RATIONALP-X))
 (356 8 (:REWRITE RTL::BITS-TAIL-GEN))
 (323 5 (:REWRITE RTL::ALL-BVECP-INTEGERP))
 (282 2 (:REWRITE ZP-OPEN))
 (203 43
      (:TYPE-PRESCRIPTION RTL::ALL-BVECP-INTEGERP))
 (177 57
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (140 4 (:DEFINITION RTL::ALL-BVECP))
 (137 59 (:REWRITE DEFAULT-LESS-THAN-1))
 (123 59 (:REWRITE DEFAULT-LESS-THAN-2))
 (116 4
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (106 8 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (97 97 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (97 97 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (97 97 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (92 92 (:REWRITE DEFAULT-TIMES-2))
 (92 92 (:REWRITE DEFAULT-TIMES-1))
 (82 14 (:REWRITE |(< (+ (- c) x) y)|))
 (75 75
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (71 71
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (67 59
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (67 59
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (59 59 (:REWRITE THE-FLOOR-BELOW))
 (59 59 (:REWRITE THE-FLOOR-ABOVE))
 (57 57
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
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
 (56 32 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (51 51 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (29 29 (:REWRITE REDUCE-INTEGERP-+))
 (29 29 (:REWRITE INTEGERP-MINUS-X))
 (29 29 (:META META-INTEGERP-CORRECT))
 (25 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (25 1
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (25 1
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (23 1 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (20 8 (:REWRITE RTL::BITS-TAIL))
 (18 18 (:REWRITE |(+ c (+ d x))|))
 (16 16 (:TYPE-PRESCRIPTION ABS))
 (16 16 (:REWRITE |(< (* x y) 0)|))
 (14 14 (:REWRITE |(< (/ x) 0)|))
 (14 14 (:REWRITE |(< (+ c/d x) y)|))
 (12 12 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (12 12 (:REWRITE RTL::BITS-NEG-INDICES))
 (12 12 (:REWRITE |(< y (+ (- c) x))|))
 (12 12 (:REWRITE |(< x (+ c/d y))|))
 (9 9
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (8 8 (:REWRITE RTL::ALL-BVECP-LEQ))
 (8 8 (:REWRITE |(< 0 (/ x))|))
 (8 8 (:REWRITE |(< 0 (* x y))|))
 (8 8 (:REWRITE |(* (- x) y)|))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (6
   6
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (6
  6
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
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
 (6 6 (:REWRITE FOLD-CONSTS-IN-+))
 (4 4
    (:TYPE-PRESCRIPTION RTL::ALL-BVECP-BVECP))
 (4 4 (:REWRITE REDUCE-RATIONALP-+))
 (4 4 (:REWRITE REDUCE-RATIONALP-*))
 (4 4 (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
 (4 4 (:REWRITE RATIONALP-MINUS-X))
 (4 4 (:REWRITE RTL::ALL-BVECP-BVECP))
 (4 4 (:META META-RATIONALP-CORRECT))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
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
(RTL::ENCODE-LEMMA
     (9 9 (:REWRITE AND*-REM-FIRST))
     (4 4
        (:REWRITE GL::SHAPE-SPEC-OBJ-IN-RANGE-BACKCHAIN-INTEGER-2))
     (3 3
        (:REWRITE GL::SHAPE-SPEC-OBJ-IN-RANGE-BACKCHAIN-LIST-OF-G-BOOLEANS))
     (3 3
        (:REWRITE GL::SHAPE-SPEC-OBJ-IN-RANGE-BACKCHAIN-ATOM))
     (1 1
        (:REWRITE GL::SHAPE-SPEC-OBJ-IN-RANGE-OPEN-LIST-OF-G-BOOLEANS))
     (1 1
        (:REWRITE GL::SHAPE-SPEC-OBJ-IN-RANGE-OPEN-ATOM)))
(RTL::BOOTH-RECURSION-1
     (498 8 (:REWRITE RTL::BITS-REVERSE-INDICES))
     (461 461
          (:TYPE-PRESCRIPTION RTL::ALL-BVECP-INTEGERP))
     (308 30 (:REWRITE SIMPLIFY-SUMS-<))
     (183 39 (:REWRITE NORMALIZE-ADDENDS))
     (160 10 (:REWRITE |(+ y (+ x z))|))
     (120 104 (:REWRITE DEFAULT-PLUS-1))
     (104 104 (:REWRITE DEFAULT-PLUS-2))
     (80 16 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
     (80 4
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (72 12 (:REWRITE ACL2-NUMBERP-X))
     (64 16 (:REWRITE |(+ (* c x) (* d x))|))
     (60 4 (:REWRITE |(+ (+ x y) z)|))
     (36 36 (:REWRITE DEFAULT-TIMES-2))
     (36 36 (:REWRITE DEFAULT-TIMES-1))
     (32 4 (:REWRITE RATIONALP-X))
     (32 4 (:REWRITE |(* x (+ y z))|))
     (30 30 (:REWRITE THE-FLOOR-BELOW))
     (30 30 (:REWRITE THE-FLOOR-ABOVE))
     (30 30
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (30 30
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (30 30
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (30 30
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (30 30 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (30 30 (:REWRITE INTEGERP-<-CONSTANT))
     (30 30 (:REWRITE DEFAULT-LESS-THAN-2))
     (30 30 (:REWRITE DEFAULT-LESS-THAN-1))
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
     (24 24 (:DEFINITION FIX))
     (24 4 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
     (23 23
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (22 22 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (20 20
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (20 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (20 4
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (20 4 (:REWRITE |(+ c (+ d x))|))
     (16 16 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (16 16 (:REWRITE |(* 0 x)|))
     (13 13 (:REWRITE REDUCE-INTEGERP-+))
     (13 13 (:REWRITE INTEGERP-MINUS-X))
     (13 13 (:META META-INTEGERP-CORRECT))
     (10 10 (:REWRITE |(< (+ c/d x) y)|))
     (10 10 (:REWRITE |(< (+ (- c) x) y)|))
     (8 8 (:TYPE-PRESCRIPTION BOOLEANP))
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (8 8 (:REWRITE RTL::BITS-NEG-INDICES))
     (8 8 (:REWRITE |(< (/ x) 0)|))
     (8 8 (:REWRITE |(< (* x y) 0)|))
     (4 4 (:REWRITE REDUCE-RATIONALP-+))
     (4 4 (:REWRITE REDUCE-RATIONALP-*))
     (4 4
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (4 4
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (4 4 (:REWRITE RATIONALP-MINUS-X))
     (4 4
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (4 4 (:REWRITE RTL::ALL-BVECP-INTEGERP))
     (4 4 (:REWRITE |(equal c (/ x))|))
     (4 4 (:REWRITE |(equal c (- x))|))
     (4 4 (:REWRITE |(equal (/ x) c)|))
     (4 4 (:REWRITE |(equal (/ x) (/ y))|))
     (4 4 (:REWRITE |(equal (- x) c)|))
     (4 4 (:REWRITE |(equal (- x) (- y))|))
     (4 4 (:META META-RATIONALP-CORRECT))
     (2 2 (:REWRITE RTL::AS-DIFF-AS))
     (2 2 (:REWRITE |(< y (+ (- c) x))|))
     (2 2 (:REWRITE |(< x (+ c/d y))|)))
(RTL::BOOTH-RECURSION-2
     (1057 22 (:REWRITE RTL::BITS-REVERSE-INDICES))
     (354 354
          (:TYPE-PRESCRIPTION RTL::ALL-BVECP-INTEGERP))
     (243 207 (:REWRITE DEFAULT-PLUS-1))
     (207 207 (:REWRITE DEFAULT-PLUS-2))
     (136 34 (:REWRITE |(+ (* c x) (* d x))|))
     (103 8
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (90 15 (:REWRITE ACL2-NUMBERP-X))
     (90 6 (:REWRITE |(+ (+ x y) z)|))
     (82 82 (:REWRITE DEFAULT-TIMES-2))
     (82 82 (:REWRITE DEFAULT-TIMES-1))
     (64 64 (:REWRITE THE-FLOOR-BELOW))
     (64 64 (:REWRITE THE-FLOOR-ABOVE))
     (64 64 (:REWRITE DEFAULT-LESS-THAN-2))
     (64 64 (:REWRITE DEFAULT-LESS-THAN-1))
     (61 61
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (61 61
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (61 61
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
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
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (61 61
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (61 61
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (61 61
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (61 61 (:REWRITE |(< (/ x) (/ y))|))
     (61 61 (:REWRITE |(< (- x) c)|))
     (61 61 (:REWRITE |(< (- x) (- y))|))
     (60 60 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (48 6 (:REWRITE |(* x (+ y z))|))
     (42 42
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (42 42
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (40 5 (:REWRITE RATIONALP-X))
     (39 39 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (36 36 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (33 8 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
     (30 6 (:REWRITE |(+ c (+ d x))|))
     (29 1
         (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (29 1 (:REWRITE |(< x (/ y)) with (< 0 y)|))
     (28 8 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (28 8
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (23 23 (:REWRITE REDUCE-INTEGERP-+))
     (23 23 (:REWRITE INTEGERP-MINUS-X))
     (23 23 (:META META-INTEGERP-CORRECT))
     (22 22 (:REWRITE RTL::BITS-NEG-INDICES))
     (20 20 (:REWRITE |(< (+ c/d x) y)|))
     (20 20 (:REWRITE |(< (+ (- c) x) y)|))
     (15 15
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (15 15
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (15 15 (:REWRITE |(< (/ x) 0)|))
     (15 15 (:REWRITE |(< (* x y) 0)|))
     (10 10 (:TYPE-PRESCRIPTION BOOLEANP))
     (9 9
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (9 9
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (9 9 (:REWRITE |(equal c (/ x))|))
     (9 9 (:REWRITE |(equal (/ x) (/ y))|))
     (9 9 (:REWRITE |(equal (- x) (- y))|))
     (9 3 (:REWRITE RTL::BITS-TAIL-GEN))
     (8 8
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (8 8 (:REWRITE |(equal c (- x))|))
     (8 8 (:REWRITE |(equal (- x) c)|))
     (7 7 (:REWRITE |(< y (+ (- c) x))|))
     (7 7 (:REWRITE |(< x (+ c/d y))|))
     (7 3 (:REWRITE RTL::BITS-TAIL))
     (5 5 (:REWRITE REDUCE-RATIONALP-+))
     (5 5 (:REWRITE REDUCE-RATIONALP-*))
     (5 5 (:REWRITE RATIONALP-MINUS-X))
     (5 5 (:REWRITE RTL::ALL-BVECP-INTEGERP))
     (5 5 (:META META-RATIONALP-CORRECT))
     (4 4 (:REWRITE RTL::AS-DIFF-AS))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (3 3 (:REWRITE |(< 0 (/ x))|))
     (3 3 (:REWRITE |(< 0 (* x y))|))
     (2 2 (:REWRITE RTL::AG-DIFF-AS))
     (1 1 (:REWRITE DEFAULT-DIVIDE))
     (1 1 (:REWRITE |(not (equal x (/ y)))|))
     (1 1 (:REWRITE |(equal x (/ y))|))
     (1 1
        (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (1 1
        (:REWRITE |(< x (/ y)) with (< y 0)|)))
(RTL::BOOTH-LEMMA
 (1212 70
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (1197 17 (:REWRITE |(< (+ (- c) x) y)|))
 (892 12 (:REWRITE RTL::NEG-BITN-0))
 (576 12 (:REWRITE RTL::BITN-NEG))
 (505 53 (:REWRITE INTEGERP-<-CONSTANT))
 (264 8 (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (139 73 (:REWRITE DEFAULT-PLUS-2))
 (127 73 (:REWRITE DEFAULT-PLUS-1))
 (124 4
      (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (121 75 (:REWRITE DEFAULT-TIMES-2))
 (99 9 (:REWRITE |(* y (* x z))|))
 (90 70 (:REWRITE DEFAULT-LESS-THAN-1))
 (87 41 (:REWRITE SIMPLIFY-SUMS-<))
 (75 75 (:REWRITE DEFAULT-TIMES-1))
 (74 70 (:REWRITE DEFAULT-LESS-THAN-2))
 (74 61
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (70 70 (:REWRITE THE-FLOOR-BELOW))
 (70 70 (:REWRITE THE-FLOOR-ABOVE))
 (63 3 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (59 1 (:DEFINITION RTL::BOOTH-LOOP-0))
 (57 45
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
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
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (53 53
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (53 53
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (53 53
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (53 53 (:REWRITE |(< (/ x) (/ y))|))
 (53 53 (:REWRITE |(< (- x) c)|))
 (53 53 (:REWRITE |(< (- x) (- y))|))
 (45 45
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (42 42
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (36 12 (:REWRITE RTL::BVECP-BITN-0))
 (35 35 (:TYPE-PRESCRIPTION ABS))
 (30 30
     (:TYPE-PRESCRIPTION RTL::ALL-BVECP-INTEGERP))
 (29 29
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (27 27 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (26 10 (:REWRITE DEFAULT-MINUS))
 (20 20
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (20 20
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (20 20 (:REWRITE |(< 0 (/ x))|))
 (20 20 (:REWRITE |(< 0 (* x y))|))
 (17 17 (:REWRITE |(< (+ c/d x) y)|))
 (14 14 (:REWRITE |(< (* x y) 0)|))
 (12 12 (:REWRITE RTL::NEG-BITN-1))
 (11
   11
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
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
 (10 6 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (9 9 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (9 9 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (9 9 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (9 9 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (9 9 (:REWRITE |(* a (/ a) b)|))
 (8 8 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (6 6 (:REWRITE FOLD-CONSTS-IN-+))
 (6 6 (:REWRITE |(< (/ x) 0)|))
 (6 6 (:REWRITE |(+ c (+ d x))|))
 (4 4 (:TYPE-PRESCRIPTION NATP))
 (4 4
    (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (4 4 (:REWRITE |(* (- x) y)|))
 (3 3 (:REWRITE RTL::BITS-NEG-INDICES))
 (3 1 (:REWRITE RTL::BITS-TAIL))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1 (:REWRITE REDUCE-INTEGERP-+))
 (1 1 (:REWRITE INTEGERP-MINUS-X))
 (1 1
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (1 1 (:META META-INTEGERP-CORRECT)))
(RTL::PARTIALPRODUCTS-RECURSION-1
 (3517 89 (:REWRITE RTL::BITS-TAIL-GEN))
 (1708 56 (:REWRITE |(< (if a b c) x)|))
 (1313 1313
       (:TYPE-PRESCRIPTION RTL::ALL-BVECP-INTEGERP))
 (844 141
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (379 197 (:REWRITE DEFAULT-LESS-THAN-1))
 (354 354 (:TYPE-PRESCRIPTION LOGNOT))
 (280 60
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (265 34 (:REWRITE RTL::NEG-BITN-1))
 (265 34 (:REWRITE RTL::NEG-BITN-0))
 (259 89 (:REWRITE RTL::BITS-TAIL))
 (211 211 (:REWRITE REDUCE-INTEGERP-+))
 (211 211 (:REWRITE INTEGERP-MINUS-X))
 (211 211 (:META META-INTEGERP-CORRECT))
 (209 19 (:REWRITE |(* y (* x z))|))
 (197 197 (:REWRITE THE-FLOOR-BELOW))
 (197 197 (:REWRITE THE-FLOOR-ABOVE))
 (197 197 (:REWRITE DEFAULT-LESS-THAN-2))
 (180 104 (:REWRITE DEFAULT-TIMES-2))
 (165 11 (:REWRITE |(+ (+ x y) z)|))
 (162 27 (:REWRITE ACL2-NUMBERP-X))
 (156 60 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (148 122
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (146 60
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (144 122
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (122 122 (:REWRITE SIMPLIFY-SUMS-<))
 (122 122
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (122 122
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (122 122 (:REWRITE INTEGERP-<-CONSTANT))
 (122 122 (:REWRITE CONSTANT-<-INTEGERP))
 (122 122
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (122 122
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (122 122
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (122 122
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (122 122 (:REWRITE |(< c (- x))|))
 (122 122
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (122 122
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (122 122
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (122 122
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (122 122 (:REWRITE |(< (/ x) (/ y))|))
 (122 122 (:REWRITE |(< (- x) c)|))
 (122 122 (:REWRITE |(< (- x) (- y))|))
 (111 111 (:REWRITE RTL::ALL-BVECP-INTEGERP))
 (104 104 (:REWRITE DEFAULT-TIMES-1))
 (100 34 (:REWRITE RTL::BVECP-BITN-0))
 (98 98 (:REWRITE DEFAULT-PLUS-2))
 (98 98 (:REWRITE DEFAULT-PLUS-1))
 (96 60 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (89 89 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (89 89 (:REWRITE RTL::BITS-NEG-INDICES))
 (72 9 (:REWRITE RATIONALP-X))
 (71 71 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (60 60
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (60 60
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (60 60
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (60 60 (:REWRITE |(equal c (/ x))|))
 (60 60 (:REWRITE |(equal c (- x))|))
 (60 60 (:REWRITE |(equal (/ x) c)|))
 (60 60 (:REWRITE |(equal (/ x) (/ y))|))
 (60 60 (:REWRITE |(equal (- x) c)|))
 (60 60 (:REWRITE |(equal (- x) (- y))|))
 (55 11 (:REWRITE |(+ c (+ d x))|))
 (44 44
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (44 44 (:REWRITE NORMALIZE-ADDENDS))
 (38 38
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (37 37
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (37
   37
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (37
  37
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (37 37
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (37 37
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (37 37
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (37 37
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (37 37
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (37 37
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (34 34 (:REWRITE RTL::BITN-NEG))
 (24 24
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (24 24
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (24 24 (:REWRITE |(< (/ x) 0)|))
 (24 24 (:REWRITE |(< (* x y) 0)|))
 (22 22 (:REWRITE RTL::AS-DIFF-AS))
 (19 19 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (19 19 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (19 19 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (19 19 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (19 19 (:TYPE-PRESCRIPTION ABS))
 (19 19 (:REWRITE |(* a (/ a) b)|))
 (18 18 (:TYPE-PRESCRIPTION BOOLEANP))
 (16 16
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (11 11 (:REWRITE |(< (+ c/d x) y)|))
 (11 11 (:REWRITE |(< (+ (- c) x) y)|))
 (9 9 (:REWRITE REDUCE-RATIONALP-+))
 (9 9 (:REWRITE REDUCE-RATIONALP-*))
 (9 9 (:REWRITE RATIONALP-MINUS-X))
 (9 9 (:META META-RATIONALP-CORRECT)))
(RTL::PARTIALPRODUCTS-RECURSION-2
 (6208 6007
       (:TYPE-PRESCRIPTION RTL::ALL-BVECP-INTEGERP))
 (3808 811
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (2308 292 (:REWRITE RTL::NEG-BITN-1))
 (2308 292 (:REWRITE RTL::NEG-BITN-0))
 (1962 1089 (:REWRITE DEFAULT-LESS-THAN-1))
 (1915 555
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (1687 1687 (:TYPE-PRESCRIPTION LOGNOT))
 (1663 569 (:REWRITE RTL::BITS-TAIL))
 (1467 1467 (:REWRITE REDUCE-INTEGERP-+))
 (1467 1467 (:REWRITE INTEGERP-MINUS-X))
 (1467 1467 (:META META-INTEGERP-CORRECT))
 (1302 555
       (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (1249 555
       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (1155 77 (:REWRITE |(+ (+ x y) z)|))
 (1089 1089 (:REWRITE THE-FLOOR-BELOW))
 (1089 1089 (:REWRITE THE-FLOOR-ABOVE))
 (1089 1089 (:REWRITE DEFAULT-LESS-THAN-2))
 (942 730
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (894 894 (:REWRITE RTL::ALL-BVECP-INTEGERP))
 (891 81 (:REWRITE |(* y (* x z))|))
 (871 730
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (868 292 (:REWRITE RTL::BVECP-BITN-0))
 (793 115 (:REWRITE ACL2-NUMBERP-X))
 (750 426 (:REWRITE DEFAULT-TIMES-2))
 (730 730
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (730 730
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (730 730 (:REWRITE INTEGERP-<-CONSTANT))
 (730 730 (:REWRITE CONSTANT-<-INTEGERP))
 (730 730
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (730 730
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (730 730
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (730 730
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (730 730 (:REWRITE |(< c (- x))|))
 (730 730
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (730 730
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (730 730
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (730 730
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (730 730 (:REWRITE |(< (/ x) (/ y))|))
 (730 730 (:REWRITE |(< (- x) c)|))
 (730 730 (:REWRITE |(< (- x) (- y))|))
 (727 555 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (665 649 (:REWRITE DEFAULT-PLUS-1))
 (649 649 (:REWRITE DEFAULT-PLUS-2))
 (619 559 (:REWRITE |(equal (/ x) c)|))
 (586 586
      (:REWRITE RTL::BITS-REVERSE-INDICES))
 (586 586 (:REWRITE RTL::BITS-NEG-INDICES))
 (559 559
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (559 559
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (559 559 (:REWRITE |(equal c (/ x))|))
 (559 559 (:REWRITE |(equal (/ x) (/ y))|))
 (559 559 (:REWRITE |(equal (- x) (- y))|))
 (555 555
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (555 555 (:REWRITE |(equal c (- x))|))
 (555 555 (:REWRITE |(equal (- x) c)|))
 (426 426 (:REWRITE DEFAULT-TIMES-1))
 (394 394 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (385 77 (:REWRITE |(+ c (+ d x))|))
 (360 42 (:REWRITE RATIONALP-X))
 (292 292 (:REWRITE RTL::BITN-NEG))
 (274 274
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (218
   218
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
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
 (208 208
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (168 168
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (144 144 (:REWRITE RTL::AS-DIFF-AS))
 (99 99
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (99 99
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (99 99 (:REWRITE |(< (/ x) 0)|))
 (99 99 (:REWRITE |(< (* x y) 0)|))
 (84 84 (:TYPE-PRESCRIPTION BOOLEANP))
 (81 81 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (81 81 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (81 81 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (81 81 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (81 81 (:TYPE-PRESCRIPTION ABS))
 (81 81 (:REWRITE |(* a (/ a) b)|))
 (77 77 (:REWRITE |(< y (+ (- c) x))|))
 (77 77 (:REWRITE |(< x (+ c/d y))|))
 (77 77 (:REWRITE |(< (+ c/d x) y)|))
 (77 77 (:REWRITE |(< (+ (- c) x) y)|))
 (42 42 (:REWRITE REDUCE-RATIONALP-+))
 (42 42 (:REWRITE REDUCE-RATIONALP-*))
 (42 42 (:REWRITE RATIONALP-MINUS-X))
 (42 42 (:META META-RATIONALP-CORRECT))
 (16 16 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (4 4 (:REWRITE DEFAULT-DIVIDE))
 (4 4 (:REWRITE |(not (equal x (/ y)))|))
 (4 4 (:REWRITE |(equal x (/ y))|))
 (4 4 (:REWRITE |(/ (/ x))|)))
(RTL::PARTIALPRODUCTS-LEMMA
     (18 18 (:REWRITE AND*-REM-FIRST))
     (7 7
        (:REWRITE GL::SHAPE-SPEC-OBJ-IN-RANGE-BACKCHAIN-INTEGER-2))
     (6 6
        (:REWRITE GL::SHAPE-SPEC-OBJ-IN-RANGE-BACKCHAIN-LIST-OF-G-BOOLEANS))
     (6 6
        (:REWRITE GL::SHAPE-SPEC-OBJ-IN-RANGE-BACKCHAIN-ATOM))
     (2 2 (:TYPE-PRESCRIPTION RTL::BMUX4))
     (2 2
        (:TYPE-PRESCRIPTION RTL::ALL-BVECP-INTEGERP))
     (2 2
        (:REWRITE GL::SHAPE-SPEC-OBJ-IN-RANGE-OPEN-LIST-OF-G-BOOLEANS))
     (2 2
        (:REWRITE GL::SHAPE-SPEC-OBJ-IN-RANGE-OPEN-ATOM)))
(RTL::SIGN-BITS-RECURSION-1
     (597 597
          (:TYPE-PRESCRIPTION RTL::ALL-BVECP-INTEGERP))
     (100 5
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (90 15 (:REWRITE ACL2-NUMBERP-X))
     (80 17 (:REWRITE RTL::NEG-BITN-1))
     (80 17 (:REWRITE RTL::NEG-BITN-0))
     (60 4 (:REWRITE |(+ (+ x y) z)|))
     (44 44 (:REWRITE DEFAULT-PLUS-2))
     (44 44 (:REWRITE DEFAULT-PLUS-1))
     (40 5 (:REWRITE RATIONALP-X))
     (35 17 (:REWRITE RTL::BVECP-BITN-0))
     (34 34 (:REWRITE REDUCE-INTEGERP-+))
     (34 34 (:REWRITE INTEGERP-MINUS-X))
     (34 34 (:META META-INTEGERP-CORRECT))
     (30 5 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
     (26 26 (:REWRITE THE-FLOOR-BELOW))
     (26 26 (:REWRITE THE-FLOOR-ABOVE))
     (26 26 (:REWRITE SIMPLIFY-SUMS-<))
     (26 26
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (26 26 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (26 26
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (26 26
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (26 26
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (26 26 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (26 26 (:REWRITE INTEGERP-<-CONSTANT))
     (26 26 (:REWRITE DEFAULT-LESS-THAN-2))
     (26 26 (:REWRITE DEFAULT-LESS-THAN-1))
     (26 26 (:REWRITE CONSTANT-<-INTEGERP))
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
     (25 5 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (25 5
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (23 23 (:REWRITE RTL::ALL-BVECP-INTEGERP))
     (20 20
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (20 20 (:REWRITE NORMALIZE-ADDENDS))
     (20 4 (:REWRITE |(+ c (+ d x))|))
     (17 17 (:REWRITE RTL::BITN-NEG))
     (10 10 (:TYPE-PRESCRIPTION BOOLEANP))
     (10 10
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (10 10
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (10 10 (:REWRITE |(< (/ x) 0)|))
     (10 10 (:REWRITE |(< (* x y) 0)|))
     (5 5 (:REWRITE REDUCE-RATIONALP-+))
     (5 5 (:REWRITE REDUCE-RATIONALP-*))
     (5 5
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (5 5
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (5 5 (:REWRITE RATIONALP-MINUS-X))
     (5 5
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (5 5 (:REWRITE |(equal c (/ x))|))
     (5 5 (:REWRITE |(equal c (- x))|))
     (5 5 (:REWRITE |(equal (/ x) c)|))
     (5 5 (:REWRITE |(equal (/ x) (/ y))|))
     (5 5 (:REWRITE |(equal (- x) c)|))
     (5 5 (:REWRITE |(equal (- x) (- y))|))
     (5 5 (:META META-RATIONALP-CORRECT))
     (4 4 (:REWRITE RTL::AS-DIFF-AS))
     (2 2 (:REWRITE |(< (+ c/d x) y)|))
     (2 2 (:REWRITE |(< (+ (- c) x) y)|)))
(RTL::SIGN-BITS-RECURSION-2
     (597 597
          (:TYPE-PRESCRIPTION RTL::ALL-BVECP-INTEGERP))
     (100 5
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (90 15 (:REWRITE ACL2-NUMBERP-X))
     (80 17 (:REWRITE RTL::NEG-BITN-1))
     (80 17 (:REWRITE RTL::NEG-BITN-0))
     (60 4 (:REWRITE |(+ (+ x y) z)|))
     (46 46 (:REWRITE DEFAULT-PLUS-2))
     (46 46 (:REWRITE DEFAULT-PLUS-1))
     (40 5 (:REWRITE RATIONALP-X))
     (35 17 (:REWRITE RTL::BVECP-BITN-0))
     (34 34 (:REWRITE REDUCE-INTEGERP-+))
     (34 34 (:REWRITE INTEGERP-MINUS-X))
     (34 34 (:META META-INTEGERP-CORRECT))
     (30 5 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
     (26 26 (:REWRITE THE-FLOOR-BELOW))
     (26 26 (:REWRITE THE-FLOOR-ABOVE))
     (26 26 (:REWRITE SIMPLIFY-SUMS-<))
     (26 26
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (26 26 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (26 26
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (26 26
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (26 26
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (26 26 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (26 26 (:REWRITE INTEGERP-<-CONSTANT))
     (26 26 (:REWRITE DEFAULT-LESS-THAN-2))
     (26 26 (:REWRITE DEFAULT-LESS-THAN-1))
     (26 26 (:REWRITE CONSTANT-<-INTEGERP))
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
     (25 5 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (25 5
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (23 23 (:REWRITE RTL::ALL-BVECP-INTEGERP))
     (21 21
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (21 21 (:REWRITE NORMALIZE-ADDENDS))
     (20 4 (:REWRITE |(+ c (+ d x))|))
     (17 17 (:REWRITE RTL::BITN-NEG))
     (10 10 (:TYPE-PRESCRIPTION BOOLEANP))
     (10 10
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (10 10
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (10 10 (:REWRITE |(< (/ x) 0)|))
     (10 10 (:REWRITE |(< (* x y) 0)|))
     (5 5 (:REWRITE REDUCE-RATIONALP-+))
     (5 5 (:REWRITE REDUCE-RATIONALP-*))
     (5 5
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (5 5
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (5 5 (:REWRITE RATIONALP-MINUS-X))
     (5 5
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (5 5 (:REWRITE |(equal c (/ x))|))
     (5 5 (:REWRITE |(equal c (- x))|))
     (5 5 (:REWRITE |(equal (/ x) c)|))
     (5 5 (:REWRITE |(equal (/ x) (/ y))|))
     (5 5 (:REWRITE |(equal (- x) c)|))
     (5 5 (:REWRITE |(equal (- x) (- y))|))
     (5 5 (:META META-RATIONALP-CORRECT))
     (4 4 (:REWRITE RTL::AS-DIFF-AS))
     (2 2 (:REWRITE |(< (+ c/d x) y)|))
     (2 2 (:REWRITE |(< (+ (- c) x) y)|)))
(RTL::SIGN-BITS-RECURSION-3
     (311 59 (:REWRITE RTL::NEG-BITN-1))
     (311 59 (:REWRITE RTL::NEG-BITN-0))
     (264 17
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (234 39 (:REWRITE ACL2-NUMBERP-X))
     (180 12 (:REWRITE |(+ (+ x y) z)|))
     (132 130 (:REWRITE DEFAULT-PLUS-1))
     (131 59 (:REWRITE RTL::BVECP-BITN-0))
     (130 130 (:REWRITE DEFAULT-PLUS-2))
     (110 110 (:REWRITE REDUCE-INTEGERP-+))
     (110 110 (:REWRITE INTEGERP-MINUS-X))
     (110 110 (:META META-INTEGERP-CORRECT))
     (104 13 (:REWRITE RATIONALP-X))
     (85 85 (:REWRITE RTL::ALL-BVECP-INTEGERP))
     (82 17 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
     (78 78 (:REWRITE THE-FLOOR-BELOW))
     (78 78 (:REWRITE THE-FLOOR-ABOVE))
     (78 78 (:REWRITE DEFAULT-LESS-THAN-2))
     (78 78 (:REWRITE DEFAULT-LESS-THAN-1))
     (75 75
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (75 75
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (75 75
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (75 75 (:REWRITE INTEGERP-<-CONSTANT))
     (75 75 (:REWRITE CONSTANT-<-INTEGERP))
     (75 75
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (75 75
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (75 75
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (75 75
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (75 75 (:REWRITE |(< c (- x))|))
     (75 75
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (75 75
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (75 75
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (75 75
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (75 75 (:REWRITE |(< (/ x) (/ y))|))
     (75 75 (:REWRITE |(< (- x) c)|))
     (75 75 (:REWRITE |(< (- x) (- y))|))
     (74 74 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (69 69 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (69 17 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (69 17
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (61 61
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (60 12 (:REWRITE |(+ c (+ d x))|))
     (59 59 (:REWRITE RTL::BITN-NEG))
     (29 1
         (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (29 1 (:REWRITE |(< x (/ y)) with (< 0 y)|))
     (26 26 (:TYPE-PRESCRIPTION BOOLEANP))
     (24 24
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (24 24
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (24 24 (:REWRITE |(< (/ x) 0)|))
     (24 24 (:REWRITE |(< (* x y) 0)|))
     (18 18
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (18 18
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (18 18 (:REWRITE |(equal c (/ x))|))
     (18 18 (:REWRITE |(equal (/ x) (/ y))|))
     (18 18 (:REWRITE |(equal (- x) (- y))|))
     (17 17
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (17 17 (:REWRITE |(equal c (- x))|))
     (17 17 (:REWRITE |(equal (- x) c)|))
     (16 3 (:REWRITE RTL::AG-DIFF-AS))
     (14 14 (:REWRITE RTL::AS-DIFF-AS))
     (13 13 (:REWRITE REDUCE-RATIONALP-+))
     (13 13 (:REWRITE REDUCE-RATIONALP-*))
     (13 13 (:REWRITE RATIONALP-MINUS-X))
     (13 13 (:REWRITE |(< y (+ (- c) x))|))
     (13 13 (:REWRITE |(< x (+ c/d y))|))
     (13 13 (:META META-RATIONALP-CORRECT))
     (10 10 (:REWRITE |(< (+ c/d x) y)|))
     (10 10 (:REWRITE |(< (+ (- c) x) y)|))
     (6 6 (:REWRITE DEFAULT-TIMES-2))
     (6 6 (:REWRITE DEFAULT-TIMES-1))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (3 3 (:REWRITE |(< 0 (/ x))|))
     (3 3 (:REWRITE |(< 0 (* x y))|))
     (2 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (1 1 (:REWRITE DEFAULT-DIVIDE))
     (1 1 (:REWRITE |(not (equal x (/ y)))|))
     (1 1 (:REWRITE |(equal x (/ y))|))
     (1 1
        (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (1 1
        (:REWRITE |(< x (/ y)) with (< y 0)|)))
(RTL::SIGN-BITS-LEMMA
 (195 1 (:DEFINITION RTL::ALIGN-LOOP-1))
 (56 4 (:REWRITE RTL::NEG-BITN-0))
 (22 12
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (22 12 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (22 12 (:REWRITE DEFAULT-LESS-THAN-1))
 (20 4 (:REWRITE RTL::NEG-BITN-1))
 (12 12 (:REWRITE THE-FLOOR-BELOW))
 (12 12 (:REWRITE THE-FLOOR-ABOVE))
 (12 12 (:REWRITE SIMPLIFY-SUMS-<))
 (12 12 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (12 12
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (12 12
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (12 12
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (12 12 (:REWRITE INTEGERP-<-CONSTANT))
 (12 12 (:REWRITE DEFAULT-LESS-THAN-2))
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
 (11 11
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (11 11
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (11 11 (:REWRITE |(< (/ x) 0)|))
 (11 11 (:REWRITE |(< (* x y) 0)|))
 (10 4 (:REWRITE RTL::BVECP-BITN-0))
 (10 4 (:REWRITE RTL::BITN-BVECP-1))
 (8 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (8 2
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (5 2
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (4
   4
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (4
  4
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (4 4 (:REWRITE DEFAULT-MINUS))
 (4 4 (:REWRITE RTL::BITN-NEG))
 (4 2 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
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
 (1 1 (:REWRITE REDUCE-INTEGERP-+))
 (1 1
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (1 1 (:REWRITE NORMALIZE-ADDENDS))
 (1 1 (:REWRITE INTEGERP-MINUS-X))
 (1 1 (:REWRITE DEFAULT-PLUS-2))
 (1 1 (:REWRITE DEFAULT-PLUS-1))
 (1 1 (:META META-INTEGERP-CORRECT)))
(RTL::ALIGN-RECURSION-1
 (5517 72 (:REWRITE RTL::BITS-TAIL-GEN))
 (4149 400
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (3473 72 (:REWRITE RTL::BITS-TAIL))
 (3075 69 (:REWRITE |(< (+ (- c) x) y)|))
 (2970 56 (:REWRITE RTL::CAT-BVECP))
 (2713 120
       (:REWRITE RTL::BITS-REVERSE-INDICES))
 (2059 1891 (:REWRITE DEFAULT-PLUS-1))
 (1939 275 (:REWRITE INTEGERP-<-CONSTANT))
 (1891 1891 (:REWRITE DEFAULT-PLUS-2))
 (1164 1164
       (:TYPE-PRESCRIPTION RTL::ALL-BVECP-INTEGERP))
 (1011 120 (:REWRITE RTL::BITS-NEG-INDICES))
 (890 51 (:REWRITE |(< y (+ (- c) x))|))
 (882 654 (:REWRITE DEFAULT-TIMES-2))
 (705 705
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (697 400 (:REWRITE DEFAULT-LESS-THAN-2))
 (654 654 (:REWRITE DEFAULT-TIMES-1))
 (627 57 (:REWRITE |(* y (* x z))|))
 (579 234
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (574 234
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (564 234 (:REWRITE SIMPLIFY-SUMS-<))
 (561 286 (:REWRITE CONSTANT-<-INTEGERP))
 (448 400 (:REWRITE DEFAULT-LESS-THAN-1))
 (446 446
      (:TYPE-PRESCRIPTION RTL::CAT-NONNEGATIVE-INTEGER-TYPE))
 (400 400 (:REWRITE THE-FLOOR-BELOW))
 (400 400 (:REWRITE THE-FLOOR-ABOVE))
 (372 372
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (360 18
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (343 343
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (312 42 (:REWRITE ACL2-NUMBERP-X))
 (303 303 (:REWRITE DEFAULT-MINUS))
 (286 286
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (286 286
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (286 286
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (286 286
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (286 286 (:REWRITE |(< c (- x))|))
 (286 286
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (286 286
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (286 286
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (286 286
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (286 286 (:REWRITE |(< (/ x) (/ y))|))
 (286 286 (:REWRITE |(< (- x) c)|))
 (286 286 (:REWRITE |(< (- x) (- y))|))
 (256 256
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (256
   256
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (256
  256
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (256 256
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (256 256
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (256
     256
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (256 256
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (256 256
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (256 256
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (250 28 (:REWRITE RTL::NEG-BITN-0))
 (246 33 (:REWRITE ODD-EXPT-THM))
 (234 234
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (200 25 (:REWRITE |(* x (+ y z))|))
 (182 182 (:REWRITE |(* (- x) y)|))
 (168 168 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (160 28 (:REWRITE RTL::NEG-BITN-1))
 (144 18 (:REWRITE RATIONALP-X))
 (133 133 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (108 18 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (104 104 (:REWRITE RTL::BITS-CAT-CONSTANTS))
 (90 18
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (80 28 (:REWRITE RTL::BVECP-BITN-0))
 (80 28 (:REWRITE RTL::BITN-BVECP-1))
 (77 77 (:REWRITE REDUCE-INTEGERP-+))
 (77 77 (:REWRITE INTEGERP-MINUS-X))
 (77 77 (:META META-INTEGERP-CORRECT))
 (69 69 (:REWRITE |(< (+ c/d x) y)|))
 (66 66 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (64 64 (:REWRITE RTL::ALL-BVECP-INTEGERP))
 (57 57 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (57 57 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (57 57 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (57 57 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (57 57 (:TYPE-PRESCRIPTION ABS))
 (57 57 (:REWRITE |(* a (/ a) b)|))
 (51 51 (:REWRITE |(< x (+ c/d y))|))
 (42 18 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (39 39 (:REWRITE |(< (* x y) 0)|))
 (36 36 (:TYPE-PRESCRIPTION BOOLEANP))
 (33 33 (:REWRITE DEFAULT-EXPT-2))
 (33 33 (:REWRITE DEFAULT-EXPT-1))
 (33 33 (:REWRITE |(expt 1/c n)|))
 (33 33 (:REWRITE |(expt (- x) n)|))
 (28 28 (:REWRITE RTL::BITN-NEG))
 (18 18 (:REWRITE REDUCE-RATIONALP-+))
 (18 18 (:REWRITE REDUCE-RATIONALP-*))
 (18 18
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (18 18
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (18 18 (:REWRITE RATIONALP-MINUS-X))
 (18 18
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (18 18 (:REWRITE |(equal c (/ x))|))
 (18 18 (:REWRITE |(equal c (- x))|))
 (18 18 (:REWRITE |(equal (/ x) c)|))
 (18 18 (:REWRITE |(equal (/ x) (/ y))|))
 (18 18 (:REWRITE |(equal (- x) c)|))
 (18 18 (:REWRITE |(equal (- x) (- y))|))
 (18 18 (:META META-RATIONALP-CORRECT))
 (12 12
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (12 12
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (12 12
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (12 12 (:REWRITE |(< (/ x) 0)|))
 (10 10 (:REWRITE |(+ 0 x)|))
 (9 9 (:TYPE-PRESCRIPTION NATP))
 (8 8 (:TYPE-PRESCRIPTION RTL::SETBITS))
 (5 5 (:REWRITE RTL::AS-DIFF-AS))
 (5 5 (:REWRITE |(< 0 (* x y))|))
 (5 5 (:REWRITE |(< (/ x) y) with (< x 0)|))
 (5 5
    (:REWRITE |(< (/ x) y) with (< 0 x)|)))
(RTL::ALIGN-RECURSION-2
 (16108 391 (:REWRITE RTL::BITS-TAIL-GEN))
 (11457 1071
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (9551 391 (:REWRITE RTL::BITS-TAIL))
 (8589 181 (:REWRITE |(< (+ (- c) x) y)|))
 (8104 555
       (:REWRITE RTL::BITS-REVERSE-INDICES))
 (7732 156 (:REWRITE RTL::CAT-BVECP))
 (5349 4913 (:REWRITE DEFAULT-PLUS-1))
 (5259 736 (:REWRITE INTEGERP-<-CONSTANT))
 (4913 4913 (:REWRITE DEFAULT-PLUS-2))
 (4387 4387
       (:TYPE-PRESCRIPTION RTL::ALL-BVECP-INTEGERP))
 (3566 427 (:REWRITE RTL::NEG-BITN-0))
 (3040 545 (:REWRITE RTL::BITS-NEG-INDICES))
 (2604 148 (:REWRITE |(< y (+ (- c) x))|))
 (2448 1844 (:REWRITE DEFAULT-TIMES-2))
 (1889 1889
       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (1844 1844 (:REWRITE DEFAULT-TIMES-1))
 (1804 1075 (:REWRITE DEFAULT-LESS-THAN-2))
 (1784 427 (:REWRITE RTL::NEG-BITN-1))
 (1661 151 (:REWRITE |(* y (* x z))|))
 (1646 771 (:REWRITE CONSTANT-<-INTEGERP))
 (1499 628
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (1483 628
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (1438 628 (:REWRITE SIMPLIFY-SUMS-<))
 (1225 1075 (:REWRITE DEFAULT-LESS-THAN-1))
 (1208 143 (:REWRITE ACL2-NUMBERP-X))
 (1167 84
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (1154 427 (:REWRITE RTL::BVECP-BITN-0))
 (1104 1104
       (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (1075 1075 (:REWRITE THE-FLOOR-BELOW))
 (1075 1075 (:REWRITE THE-FLOOR-ABOVE))
 (924 920
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (822 822
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (822
   822
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (822
  822
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (822 822
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (822 822
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (822
     822
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (822 822
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (822 822
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (822 822
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (771 771
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (771 771
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (771 771
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (771 771
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (771 771 (:REWRITE |(< c (- x))|))
 (771 771
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (771 771
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (771 771
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (771 771
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (771 771 (:REWRITE |(< (/ x) (/ y))|))
 (771 771 (:REWRITE |(< (- x) c)|))
 (771 771 (:REWRITE |(< (- x) (- y))|))
 (762 762 (:REWRITE DEFAULT-MINUS))
 (692 286 (:REWRITE RTL::BITN-BVECP-1))
 (628 628
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (578 84
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (568 71 (:REWRITE RATIONALP-X))
 (558 558 (:REWRITE REDUCE-INTEGERP-+))
 (558 558 (:REWRITE INTEGERP-MINUS-X))
 (558 558 (:META META-INTEGERP-CORRECT))
 (548 548 (:REWRITE RTL::ALL-BVECP-INTEGERP))
 (504 504 (:REWRITE |(* (- x) y)|))
 (450 81 (:REWRITE ODD-EXPT-THM))
 (439 84 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (436 436 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (400 50 (:REWRITE |(* x (+ y z))|))
 (330 330 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (286 286 (:REWRITE RTL::BITN-NEG))
 (244 4 (:REWRITE |(< (if a b c) x)|))
 (181 181 (:REWRITE |(< (+ c/d x) y)|))
 (162 162
      (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (159 159 (:TYPE-PRESCRIPTION ABS))
 (151 151
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (151 151
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (151 151
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (151 151
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (151 151 (:REWRITE |(* a (/ a) b)|))
 (148 148 (:REWRITE |(< x (+ c/d y))|))
 (144 84 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (142 142 (:TYPE-PRESCRIPTION BOOLEANP))
 (107 107 (:REWRITE RTL::BITN-BVECP))
 (93 93 (:REWRITE |(< (* x y) 0)|))
 (84 84
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (84 84
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (84 84
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (84 84 (:REWRITE |(equal c (/ x))|))
 (84 84 (:REWRITE |(equal c (- x))|))
 (84 84 (:REWRITE |(equal (/ x) c)|))
 (84 84 (:REWRITE |(equal (/ x) (/ y))|))
 (84 84 (:REWRITE |(equal (- x) c)|))
 (84 84 (:REWRITE |(equal (- x) (- y))|))
 (81 81 (:REWRITE DEFAULT-EXPT-2))
 (81 81 (:REWRITE DEFAULT-EXPT-1))
 (81 81 (:REWRITE |(expt 1/c n)|))
 (81 81 (:REWRITE |(expt (- x) n)|))
 (71 71 (:REWRITE REDUCE-RATIONALP-+))
 (71 71 (:REWRITE REDUCE-RATIONALP-*))
 (71 71 (:REWRITE RATIONALP-MINUS-X))
 (71 71 (:META META-RATIONALP-CORRECT))
 (70 6 (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (68 68
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (62 2
     (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (46 46 (:TYPE-PRESCRIPTION RTL::SETBITS))
 (25 25 (:TYPE-PRESCRIPTION NATP))
 (22 22 (:REWRITE |(< 0 (* x y))|))
 (20 20 (:REWRITE RTL::CAT-ASSOCIATIVE))
 (20 20 (:REWRITE RTL::AS-DIFF-AS))
 (20 20 (:REWRITE |(+ 0 x)|))
 (18 18
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (18 18
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (18 18 (:REWRITE |(< (/ x) 0)|))
 (16 3 (:REWRITE RTL::AG-DIFF-AS))
 (14 14
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (14 14
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (14 14 (:REWRITE |(< 0 (/ x))|))
 (11 11 (:REWRITE ZP-OPEN))
 (8 8 (:REWRITE |(< (/ x) y) with (< x 0)|))
 (8 8 (:REWRITE |(< (/ x) y) with (< 0 x)|))
 (8 2 (:REWRITE |(* y x)|))
 (6 6 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (2 2
    (:REWRITE |(<= (/ x) y) with (< x 0)|)))
(RTL::ALIGN-LEMMA
     (18 18 (:REWRITE AND*-REM-FIRST))
     (7 7
        (:REWRITE GL::SHAPE-SPEC-OBJ-IN-RANGE-BACKCHAIN-INTEGER-2))
     (6 6
        (:REWRITE GL::SHAPE-SPEC-OBJ-IN-RANGE-BACKCHAIN-LIST-OF-G-BOOLEANS))
     (6 6
        (:REWRITE GL::SHAPE-SPEC-OBJ-IN-RANGE-BACKCHAIN-ATOM))
     (2 2
        (:TYPE-PRESCRIPTION RTL::ALL-BVECP-INTEGERP))
     (2 2
        (:REWRITE GL::SHAPE-SPEC-OBJ-IN-RANGE-OPEN-LIST-OF-G-BOOLEANS))
     (2 2
        (:REWRITE GL::SHAPE-SPEC-OBJ-IN-RANGE-OPEN-ATOM)))
(RTL::BVECP-ALIGN
 (975 5 (:DEFINITION RTL::ALIGN-LOOP-1))
 (720 10 (:REWRITE RTL::BOOTH-LEMMA))
 (709 24 (:REWRITE RTL::BITS-TAIL-GEN))
 (571 1 (:DEFINITION RTL::ALIGN-LOOP-0))
 (558 84
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (479 34 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (392 32 (:REWRITE RTL::NEG-BITN-0))
 (382 24 (:REWRITE RTL::BITS-TAIL))
 (360 10 (:DEFINITION ABS))
 (341 7 (:REWRITE |(< (+ (- c) x) y)|))
 (250 10 (:REWRITE RTL::BITN-CAT-CONSTANTS))
 (238 67 (:REWRITE INTEGERP-<-CONSTANT))
 (223 207 (:REWRITE DEFAULT-PLUS-1))
 (207 207 (:REWRITE DEFAULT-PLUS-2))
 (200 8 (:REWRITE |(< y (+ (- c) x))|))
 (150 6 (:REWRITE RTL::BITN-BITN-0))
 (149 32 (:REWRITE RTL::NEG-BITN-1))
 (145 70 (:REWRITE CONSTANT-<-INTEGERP))
 (137 109 (:REWRITE DEFAULT-TIMES-2))
 (133 34 (:REWRITE RTL::BITS-NEG-INDICES))
 (128 63
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (128 63 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (122 84 (:REWRITE DEFAULT-LESS-THAN-1))
 (111 84 (:REWRITE DEFAULT-LESS-THAN-2))
 (109 109 (:REWRITE DEFAULT-TIMES-1))
 (99 99
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (93 63 (:REWRITE SIMPLIFY-SUMS-<))
 (84 84 (:REWRITE THE-FLOOR-BELOW))
 (84 84 (:REWRITE THE-FLOOR-ABOVE))
 (79 79
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (77 77
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (77 7 (:REWRITE |(* y (* x z))|))
 (76 32 (:REWRITE RTL::BVECP-BITN-0))
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
 (67 63
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (58 26 (:REWRITE RTL::BITN-BVECP-1))
 (53 49 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (52 52
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (52
   52
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (52
  52
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (52 52
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (52 52
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (52 52
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (52 52
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (52 52
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (52 52
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (52 29
     (:TYPE-PRESCRIPTION RTL::ALL-BVECP-BVECP))
 (47 47
     (:TYPE-PRESCRIPTION RTL::CAT-NONNEGATIVE-INTEGER-TYPE))
 (42 42 (:TYPE-PRESCRIPTION RTL::BMUX4))
 (38 38 (:REWRITE DEFAULT-MINUS))
 (37 37 (:REWRITE |(< (* x y) 0)|))
 (34 34
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (34 34
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (34 34 (:REWRITE |(< (/ x) 0)|))
 (29 29 (:REWRITE |(* (- x) y)|))
 (26 26 (:REWRITE RTL::BITN-NEG))
 (23 23
     (:TYPE-PRESCRIPTION RTL::ALIGN-LOOP-1))
 (21 21 (:REWRITE REDUCE-INTEGERP-+))
 (21 21 (:REWRITE INTEGERP-MINUS-X))
 (21 21 (:META META-INTEGERP-CORRECT))
 (18 18
     (:TYPE-PRESCRIPTION RTL::ALL-BVECP-INTEGERP))
 (16 16 (:TYPE-PRESCRIPTION RTL::SETBITS))
 (16 16 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (9 3
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (9 3
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (9 3 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (8 8 (:REWRITE |(< x (+ c/d y))|))
 (7 7 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (7 7 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (7 7 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (7 7 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (7 7 (:TYPE-PRESCRIPTION ABS))
 (7 7 (:REWRITE |(< (+ c/d x) y)|))
 (7 7 (:REWRITE |(* a (/ a) b)|))
 (6 6 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (6 6 (:REWRITE RTL::ALL-BVECP-INTEGERP))
 (6 3 (:REWRITE ODD-EXPT-THM))
 (5 5 (:REWRITE RTL::SIGN-BITS-RECURSION-2))
 (4 4 (:REWRITE RTL::BITN-BVECP))
 (3 3 (:REWRITE ZP-OPEN))
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
 (1 1 (:TYPE-PRESCRIPTION NATP)))
(RTL::ALL-BVECP-ALIGN
 (6664 17 (:DEFINITION RTL::ALIGN-LOOP-0))
 (5466 234 (:REWRITE RTL::BITS-TAIL-GEN))
 (4706 632
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (3786 290 (:REWRITE RTL::NEG-BITN-0))
 (3740 66 (:REWRITE |(< (+ (- c) x) y)|))
 (3244 234 (:REWRITE RTL::BITS-TAIL))
 (2924 275
       (:REWRITE RTL::BITS-REVERSE-INDICES))
 (2386 505 (:REWRITE INTEGERP-<-CONSTANT))
 (2050 82 (:REWRITE RTL::BITN-BITN-0))
 (1583 1447 (:REWRITE DEFAULT-PLUS-1))
 (1447 1447 (:REWRITE DEFAULT-PLUS-2))
 (1362 273 (:REWRITE RTL::BITS-NEG-INDICES))
 (1311 290 (:REWRITE RTL::NEG-BITN-1))
 (871 39 (:REWRITE |(< y (+ (- c) x))|))
 (870 453
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (870 453
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (851 632 (:REWRITE DEFAULT-LESS-THAN-1))
 (843 518 (:REWRITE CONSTANT-<-INTEGERP))
 (830 632 (:REWRITE DEFAULT-LESS-THAN-2))
 (770 542 (:REWRITE DEFAULT-TIMES-2))
 (730 290 (:REWRITE RTL::BVECP-BITN-0))
 (729 453 (:REWRITE SIMPLIFY-SUMS-<))
 (632 632 (:REWRITE THE-FLOOR-BELOW))
 (632 632 (:REWRITE THE-FLOOR-ABOVE))
 (627 57 (:REWRITE |(* y (* x z))|))
 (575 575
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (542 542 (:REWRITE DEFAULT-TIMES-1))
 (531 531
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (518 518
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (518 518
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (518 518
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (518 518
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (518 518 (:REWRITE |(< c (- x))|))
 (518 518
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (518 518
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (518 518
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (518 518
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (518 518 (:REWRITE |(< (/ x) (/ y))|))
 (518 518 (:REWRITE |(< (- x) c)|))
 (518 518 (:REWRITE |(< (- x) (- y))|))
 (480 208 (:REWRITE RTL::BITN-BVECP-1))
 (477 477 (:TYPE-PRESCRIPTION RTL::BMUX4))
 (465 461
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (444 444
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (444
   444
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (444
  444
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (444 444
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (444 444
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (444
     444
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (444 444
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (444 444
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (444 444
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (319 319
      (:TYPE-PRESCRIPTION RTL::CAT-NONNEGATIVE-INTEGER-TYPE))
 (317 317 (:REWRITE DEFAULT-MINUS))
 (296 296
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (293 293 (:REWRITE |(< (* x y) 0)|))
 (260 260 (:REWRITE |(< (/ x) 0)|))
 (252 252
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (252 252
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (208 208 (:REWRITE RTL::BITN-NEG))
 (191 191 (:REWRITE REDUCE-INTEGERP-+))
 (191 191 (:REWRITE INTEGERP-MINUS-X))
 (191 191 (:META META-INTEGERP-CORRECT))
 (146 146 (:REWRITE |(* (- x) y)|))
 (136 136 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (134 120
      (:TYPE-PRESCRIPTION RTL::ALL-BVECP-INTEGERP))
 (122 23
      (:REWRITE RTL::SIGN-BITS-RECURSION-3))
 (66 66 (:REWRITE |(< (+ c/d x) y)|))
 (65 22
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (65 22
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (65 22 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (57 57 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (57 57 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (57 57 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (57 57 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (57 57 (:TYPE-PRESCRIPTION ABS))
 (57 57 (:REWRITE |(* a (/ a) b)|))
 (56 56 (:REWRITE RTL::BITN-BVECP))
 (50 48
     (:TYPE-PRESCRIPTION RTL::ALL-BVECP-BVECP))
 (44 44 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (44 22 (:REWRITE ODD-EXPT-THM))
 (39 39 (:REWRITE |(< x (+ c/d y))|))
 (32 32 (:TYPE-PRESCRIPTION RTL::SETBITS))
 (27 27 (:TYPE-PRESCRIPTION NATP))
 (26 26 (:REWRITE RTL::ALL-BVECP-INTEGERP))
 (23 23 (:REWRITE RTL::ALL-BVECP-LEQ))
 (22 22
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (22 22 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (22 22
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (22 22
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (22 22
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (22 22 (:REWRITE DEFAULT-EXPT-2))
 (22 22 (:REWRITE DEFAULT-EXPT-1))
 (22 22 (:REWRITE |(expt 1/c n)|))
 (22 22 (:REWRITE |(expt (- x) n)|))
 (22 22 (:REWRITE |(equal c (/ x))|))
 (22 22 (:REWRITE |(equal c (- x))|))
 (22 22 (:REWRITE |(equal (/ x) c)|))
 (22 22 (:REWRITE |(equal (/ x) (/ y))|))
 (22 22 (:REWRITE |(equal (- x) c)|))
 (22 22 (:REWRITE |(equal (- x) (- y))|))
 (16 16
     (:REWRITE RTL::SIGN-BITS-RECURSION-2))
 (7 7 (:REWRITE ZP-OPEN))
 (4 4 (:REWRITE RTL::CAT-ASSOCIATIVE))
 (4 4 (:REWRITE |(+ x (- x))|)))
(RTL::SUM-SIMPLE-PP4P-THETA
 (450 10 (:REWRITE RTL::BITS-TAIL-GEN))
 (126 2 (:REWRITE RTL::BITS-BITS-SUM))
 (34 22 (:REWRITE DEFAULT-PLUS-2))
 (34 22 (:REWRITE DEFAULT-PLUS-1))
 (30 16 (:REWRITE DEFAULT-LESS-THAN-1))
 (30 10 (:REWRITE RTL::BITS-TAIL))
 (29 15 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (23 15
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (20 20
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (20 20 (:REWRITE NORMALIZE-ADDENDS))
 (16 16 (:REWRITE THE-FLOOR-BELOW))
 (16 16 (:REWRITE THE-FLOOR-ABOVE))
 (16 16
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (16 16
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (16 16
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (16 16 (:REWRITE INTEGERP-<-CONSTANT))
 (16 16 (:REWRITE DEFAULT-LESS-THAN-2))
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
 (15 15 (:REWRITE SIMPLIFY-SUMS-<))
 (14 14 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (14 14 (:REWRITE RTL::BITS-NEG-INDICES))
 (10 10
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (10
   10
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (10
  10
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (10 10
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (10 10
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (10 10
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (10 10
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (10 10
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (10 10
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (9 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (9 3
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (9 3
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (6 3 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (5 5 (:REWRITE ZP-OPEN))
 (4 4 (:REWRITE |(< (+ c/d x) y)|))
 (4 4 (:REWRITE |(< (+ (- c) x) y)|))
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
 (3 3 (:REWRITE |(< (/ x) 0)|))
 (3 3 (:REWRITE |(< (* x y) 0)|))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2 (:REWRITE REDUCE-INTEGERP-+))
 (2 2 (:REWRITE INTEGERP-MINUS-X))
 (2 2 (:META META-INTEGERP-CORRECT)))
(RTL::SUM-SIMPLE-ALIGN-PROD
 (326 8 (:REWRITE RTL::BITS-TAIL-GEN))
 (52 52
     (:TYPE-PRESCRIPTION RTL::SUM-PP4P-THETA))
 (42 6 (:DEFINITION RTL::SUM-PP4P-THETA))
 (15 8 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (15 8 (:REWRITE DEFAULT-LESS-THAN-1))
 (13 8
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (12 6 (:REWRITE DEFAULT-PLUS-2))
 (12 6 (:REWRITE DEFAULT-PLUS-1))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (8
   8
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (8
  8
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (8 8 (:REWRITE THE-FLOOR-BELOW))
 (8 8 (:REWRITE THE-FLOOR-ABOVE))
 (8 8 (:REWRITE SIMPLIFY-SUMS-<))
 (8 8 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (8 8
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (8 8
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (8 8 (:REWRITE INTEGERP-<-CONSTANT))
 (8 8 (:REWRITE DEFAULT-LESS-THAN-2))
 (8 8 (:REWRITE CONSTANT-<-INTEGERP))
 (8 8 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (8 8 (:REWRITE RTL::BITS-NEG-INDICES))
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
 (7 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (7 3
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (7 3
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (6 6 (:TYPE-PRESCRIPTION RTL::PP4P-THETA))
 (6 6
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (6 6 (:REWRITE NORMALIZE-ADDENDS))
 (6 3 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (4 4
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (4 4 (:REWRITE DEFAULT-TIMES-2))
 (4 4 (:REWRITE DEFAULT-TIMES-1))
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
 (1 1 (:REWRITE RTL::BITS-BVECP-SIMPLE))
 (1 1 (:REWRITE RTL::BITS-BVECP)))
(RTL::COMPRESS32-LEMMA
     (27 27 (:REWRITE AND*-REM-FIRST))
     (9 9
        (:REWRITE GL::SHAPE-SPEC-OBJ-IN-RANGE-BACKCHAIN-LIST-OF-G-BOOLEANS))
     (9 9
        (:REWRITE GL::SHAPE-SPEC-OBJ-IN-RANGE-BACKCHAIN-INTEGER-2))
     (9 9
        (:REWRITE GL::SHAPE-SPEC-OBJ-IN-RANGE-BACKCHAIN-INTEGER-1))
     (9 9
        (:REWRITE GL::SHAPE-SPEC-OBJ-IN-RANGE-BACKCHAIN-ATOM))
     (3 3
        (:REWRITE GL::SHAPE-SPEC-OBJ-IN-RANGE-OPEN-LIST-OF-G-BOOLEANS))
     (3 3
        (:REWRITE GL::SHAPE-SPEC-OBJ-IN-RANGE-OPEN-ATOM)))
(RTL::COMPRESS42-LEMMA
     (36 36 (:REWRITE AND*-REM-FIRST))
     (12 12
         (:REWRITE GL::SHAPE-SPEC-OBJ-IN-RANGE-BACKCHAIN-LIST-OF-G-BOOLEANS))
     (12 12
         (:REWRITE GL::SHAPE-SPEC-OBJ-IN-RANGE-BACKCHAIN-INTEGER-2))
     (12 12
         (:REWRITE GL::SHAPE-SPEC-OBJ-IN-RANGE-BACKCHAIN-INTEGER-1))
     (12 12
         (:REWRITE GL::SHAPE-SPEC-OBJ-IN-RANGE-BACKCHAIN-ATOM))
     (4 4
        (:REWRITE GL::SHAPE-SPEC-OBJ-IN-RANGE-OPEN-LIST-OF-G-BOOLEANS))
     (4 4
        (:REWRITE GL::SHAPE-SPEC-OBJ-IN-RANGE-OPEN-ATOM)))
(RTL::LEVEL1)
(RTL::LEVEL2)
(RTL::LEVEL3 (12 12
                 (:TYPE-PRESCRIPTION RTL::ALL-BVECP-INTEGERP)))
(RTL::LEVEL4 (9 9
                (:TYPE-PRESCRIPTION RTL::ALL-BVECP-INTEGERP)))
(RTL::SUM-REWRITE (82 10 (:REWRITE ACL2-NUMBERP-X))
                  (50 25 (:DEFINITION RTL::SUM-LOOP-1))
                  (50 25 (:DEFINITION RTL::SUM-LOOP-0))
                  (36 9 (:REWRITE RATIONALP-X))
                  (10 10 (:REWRITE REDUCE-INTEGERP-+))
                  (10 10 (:REWRITE INTEGERP-MINUS-X))
                  (10 10 (:META META-INTEGERP-CORRECT))
                  (9 9 (:REWRITE REDUCE-RATIONALP-+))
                  (9 9 (:REWRITE REDUCE-RATIONALP-*))
                  (9 9 (:REWRITE RATIONALP-MINUS-X))
                  (9 9 (:META META-RATIONALP-CORRECT))
                  (5 2 (:REWRITE RTL::BITS-TAIL-GEN))
                  (4 2 (:REWRITE RTL::BITS-TAIL))
                  (2 2
                     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                  (2 2 (:REWRITE NORMALIZE-ADDENDS))
                  (2 2 (:REWRITE RTL::BITS-REVERSE-INDICES))
                  (2 2 (:REWRITE RTL::BITS-NEG-INDICES)))
(RTL::LEVEL1-ALL-BVECP (53 53 (:REWRITE RTL::ALL-BVECP-SUBRANGE))
                       (53 53 (:REWRITE RTL::ALL-BVECP-LEQ))
                       (32 32 (:REWRITE RTL::ALL-BVECP-BVECP)))
(RTL::LEVEL1-4-2
 (44982 44982
        (:TYPE-PRESCRIPTION RTL::ALL-BVECP-INTEGERP))
 (20133 20133
        (:TYPE-PRESCRIPTION RTL::ALL-BVECP-BVECP))
 (3604 264 (:REWRITE ACL2-NUMBERP-X))
 (1760 260 (:REWRITE RATIONALP-X))
 (688 40 (:REWRITE RTL::BITS-TAIL-GEN))
 (560 280
      (:TYPE-PRESCRIPTION RTL::INTEGERP-SUM-RANGE))
 (389 389 (:REWRITE RTL::ALL-BVECP-BVECP))
 (284 284 (:REWRITE REDUCE-INTEGERP-+))
 (284 284 (:REWRITE INTEGERP-MINUS-X))
 (284 284 (:META META-INTEGERP-CORRECT))
 (260 260 (:REWRITE REDUCE-RATIONALP-+))
 (260 260 (:REWRITE REDUCE-RATIONALP-*))
 (260 260 (:REWRITE RATIONALP-MINUS-X))
 (260 260 (:META META-RATIONALP-CORRECT))
 (236 236
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (236 236 (:REWRITE NORMALIZE-ADDENDS))
 (180 180 (:REWRITE RTL::ALL-BVECP-INTEGERP))
 (169 169 (:REWRITE RTL::ALL-BVECP-SUBRANGE))
 (165 165 (:REWRITE RTL::ALL-BVECP-LEQ))
 (112 8 (:REWRITE RTL::INTEGERP-SUM-RANGE))
 (64 12
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (60 60 (:REWRITE FOLD-CONSTS-IN-+))
 (60 60 (:REWRITE |(+ c (+ d x))|))
 (40 40 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (40 40 (:REWRITE RTL::BITS-NEG-INDICES))
 (32 12
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (28 12 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (28 12 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (16 4
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (16 4 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (16 4 (:REWRITE DEFAULT-LESS-THAN-1))
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
 (8 8 (:TYPE-PRESCRIPTION BOOLEANP))
 (5 5 (:REWRITE SUBSETP-MEMBER . 4))
 (5 5 (:REWRITE SUBSETP-MEMBER . 3))
 (5 5 (:REWRITE SUBSETP-MEMBER . 2))
 (5 5 (:REWRITE SUBSETP-MEMBER . 1))
 (5 5 (:REWRITE INTERSECTP-MEMBER . 3))
 (5 5 (:REWRITE INTERSECTP-MEMBER . 2))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (4
   4
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (4
  4
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (4 4 (:REWRITE THE-FLOOR-BELOW))
 (4 4 (:REWRITE THE-FLOOR-ABOVE))
 (4 4 (:REWRITE SIMPLIFY-SUMS-<))
 (4 4 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (4 4
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (4 4
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (4 4 (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
 (4 4 (:REWRITE INTEGERP-<-CONSTANT))
 (4 4 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
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
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RTL::LEVEL1-SUM
 (676 30 (:REWRITE RTL::BITS-TAIL-GEN))
 (420 210
      (:TYPE-PRESCRIPTION RTL::INTEGERP-SUM-RANGE))
 (82 10 (:REWRITE ACL2-NUMBERP-X))
 (68 68
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (68 68 (:REWRITE NORMALIZE-ADDENDS))
 (46 46 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (46 46 (:REWRITE RTL::BITS-NEG-INDICES))
 (44 4 (:REWRITE RTL::BITS-BITS-SUM))
 (36 10 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (36 10 (:REWRITE DEFAULT-LESS-THAN-1))
 (36 9 (:REWRITE RATIONALP-X))
 (18 18 (:REWRITE REDUCE-INTEGERP-+))
 (18 18 (:REWRITE INTEGERP-MINUS-X))
 (18 18 (:META META-INTEGERP-CORRECT))
 (13 2 (:DEFINITION RTL::ALL-BVECP))
 (11 10
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (10 10
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (10
   10
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (10
  10
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (10 10
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (10 10
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (10 10
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (10 10
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (10 10
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (10 10
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (10 10 (:REWRITE THE-FLOOR-BELOW))
 (10 10 (:REWRITE THE-FLOOR-ABOVE))
 (10 10 (:REWRITE SIMPLIFY-SUMS-<))
 (10 10
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (10 10
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (10 10
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (10 10 (:REWRITE INTEGERP-<-CONSTANT))
 (10 10 (:REWRITE DEFAULT-LESS-THAN-2))
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
 (9 9 (:REWRITE REDUCE-RATIONALP-+))
 (9 9 (:REWRITE REDUCE-RATIONALP-*))
 (9 9 (:REWRITE RATIONALP-MINUS-X))
 (9 9 (:META META-RATIONALP-CORRECT))
 (8 8 (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
 (8 8 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (4 4 (:REWRITE RTL::ALL-BVECP-LEQ))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE RTL::ALL-BVECP-BVECP))
 (2 2 (:REWRITE |(< (+ c/d x) y)|))
 (2 2 (:REWRITE |(< (+ (- c) x) y)|))
 (2 2 (:REWRITE |(+ c (+ d x))|)))
(RTL::LEVEL2-ALL-BVECP (38 38
                           (:TYPE-PRESCRIPTION RTL::ALL-BVECP-BVECP))
                       (30 30 (:REWRITE RTL::ALL-BVECP-SUBRANGE))
                       (30 30 (:REWRITE RTL::ALL-BVECP-LEQ))
                       (18 18 (:REWRITE RTL::ALL-BVECP-BVECP)))
(RTL::A2-4-2 (150 22 (:REWRITE ACL2-NUMBERP-X))
             (64 16 (:REWRITE RATIONALP-X))
             (20 2
                 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
             (18 18 (:REWRITE REDUCE-INTEGERP-+))
             (18 18 (:REWRITE INTEGERP-MINUS-X))
             (18 18 (:META META-INTEGERP-CORRECT))
             (16 16 (:REWRITE REDUCE-RATIONALP-+))
             (16 16 (:REWRITE REDUCE-RATIONALP-*))
             (16 16 (:REWRITE RATIONALP-MINUS-X))
             (16 16
                 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
             (16 16 (:REWRITE NORMALIZE-ADDENDS))
             (16 16 (:META META-RATIONALP-CORRECT))
             (10 4 (:REWRITE RTL::BITS-TAIL-GEN))
             (8 4 (:REWRITE RTL::BITS-TAIL))
             (6 6 (:REWRITE FOLD-CONSTS-IN-+))
             (6 6 (:REWRITE |(+ c (+ d x))|))
             (6 2 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
             (6 1 (:DEFINITION RTL::ALL-BVECP))
             (4 4 (:TYPE-PRESCRIPTION BOOLEANP))
             (4 4 (:REWRITE RTL::BITS-REVERSE-INDICES))
             (4 4 (:REWRITE RTL::BITS-NEG-INDICES))
             (4 2
                (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
             (3 3 (:REWRITE SUBSETP-MEMBER . 4))
             (3 3 (:REWRITE SUBSETP-MEMBER . 3))
             (3 3 (:REWRITE SUBSETP-MEMBER . 2))
             (3 3 (:REWRITE SUBSETP-MEMBER . 1))
             (3 3 (:REWRITE INTERSECTP-MEMBER . 3))
             (3 3 (:REWRITE INTERSECTP-MEMBER . 2))
             (2 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
             (2 2
                (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
             (2 2
                (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
             (2 2
                (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
             (2 2 (:REWRITE RTL::ALL-BVECP-SUBRANGE))
             (2 2 (:REWRITE RTL::ALL-BVECP-LEQ))
             (2 2 (:REWRITE |(equal c (/ x))|))
             (2 2 (:REWRITE |(equal c (- x))|))
             (2 2 (:REWRITE |(equal (/ x) c)|))
             (2 2 (:REWRITE |(equal (/ x) (/ y))|))
             (2 2 (:REWRITE |(equal (- x) c)|))
             (2 2 (:REWRITE |(equal (- x) (- y))|))
             (1 1
                (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
             (1 1 (:REWRITE RTL::ALL-BVECP-BVECP)))
(RTL::LEVEL2-SUM
 (323 14 (:REWRITE RTL::BITS-TAIL-GEN))
 (176 88
      (:TYPE-PRESCRIPTION RTL::INTEGERP-SUM-RANGE))
 (118 36 (:REWRITE DEFAULT-PLUS-2))
 (82 36 (:REWRITE DEFAULT-PLUS-1))
 (34 12 (:REWRITE RTL::LEVEL1-4-2))
 (28 28
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (28 28 (:REWRITE NORMALIZE-ADDENDS))
 (27 4 (:DEFINITION RTL::ALL-BVECP))
 (20 20 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (20 20 (:REWRITE RTL::BITS-NEG-INDICES))
 (19 2 (:REWRITE RTL::BITS-BITS-SUM))
 (17 5 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (17 5 (:REWRITE DEFAULT-LESS-THAN-1))
 (8 8 (:REWRITE RTL::ALL-BVECP-LEQ))
 (6 5
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (5 5
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (5
   5
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (5
  5
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (5 5
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (5 5
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (5 5
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (5 5
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (5 5
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (5 5
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (5 5 (:REWRITE THE-FLOOR-BELOW))
 (5 5 (:REWRITE THE-FLOOR-ABOVE))
 (5 5 (:REWRITE SIMPLIFY-SUMS-<))
 (5 5 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (5 5
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (5 5
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (5 5 (:REWRITE INTEGERP-<-CONSTANT))
 (5 5 (:REWRITE DEFAULT-LESS-THAN-2))
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
 (4 4 (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
 (4 4 (:REWRITE REDUCE-INTEGERP-+))
 (4 4 (:REWRITE INTEGERP-MINUS-X))
 (4 4 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (4 4 (:REWRITE RTL::ALL-BVECP-BVECP))
 (4 4 (:META META-INTEGERP-CORRECT))
 (1 1 (:REWRITE |(< (+ c/d x) y)|))
 (1 1 (:REWRITE |(< (+ (- c) x) y)|)))
(RTL::LEVEL3-ALL-BVECP (13 13
                           (:TYPE-PRESCRIPTION RTL::ALL-BVECP-BVECP))
                       (8 8 (:REWRITE RTL::ALL-BVECP-SUBRANGE))
                       (8 8 (:REWRITE RTL::ALL-BVECP-LEQ))
                       (5 5 (:REWRITE RTL::ALL-BVECP-BVECP)))
(RTL::LEVEL3-SUM (65 9 (:REWRITE ACL2-NUMBERP-X))
                 (28 7 (:REWRITE RATIONALP-X))
                 (8 8 (:REWRITE REDUCE-INTEGERP-+))
                 (8 8
                    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                 (8 8 (:REWRITE NORMALIZE-ADDENDS))
                 (8 8 (:REWRITE INTEGERP-MINUS-X))
                 (8 8 (:META META-INTEGERP-CORRECT))
                 (7 7 (:REWRITE REDUCE-RATIONALP-+))
                 (7 7 (:REWRITE REDUCE-RATIONALP-*))
                 (7 7 (:REWRITE RATIONALP-MINUS-X))
                 (7 7 (:META META-RATIONALP-CORRECT))
                 (6 1 (:DEFINITION RTL::ALL-BVECP))
                 (5 2 (:REWRITE RTL::BITS-TAIL-GEN))
                 (4 2 (:REWRITE RTL::BITS-TAIL))
                 (3 3 (:REWRITE FOLD-CONSTS-IN-+))
                 (3 3 (:REWRITE |(+ c (+ d x))|))
                 (2 2 (:REWRITE RTL::BITS-REVERSE-INDICES))
                 (2 2 (:REWRITE RTL::BITS-NEG-INDICES))
                 (2 2 (:REWRITE RTL::ALL-BVECP-SUBRANGE))
                 (2 2 (:REWRITE RTL::ALL-BVECP-LEQ))
                 (1 1 (:REWRITE RTL::ALL-BVECP-BVECP)))
(RTL::LEVEL4-SUM (883 883
                      (:TYPE-PRESCRIPTION RTL::ALL-BVECP-INTEGERP))
                 (438 438
                      (:TYPE-PRESCRIPTION RTL::ALL-BVECP-BVECP))
                 (181 17 (:REWRITE ACL2-NUMBERP-X))
                 (84 17 (:REWRITE RATIONALP-X))
                 (34 8 (:REWRITE RTL::BITS-TAIL-GEN))
                 (22 22 (:REWRITE REDUCE-INTEGERP-+))
                 (22 22 (:REWRITE INTEGERP-MINUS-X))
                 (22 22 (:META META-INTEGERP-CORRECT))
                 (18 18 (:REWRITE RTL::ALL-BVECP-BVECP))
                 (17 17 (:REWRITE REDUCE-RATIONALP-+))
                 (17 17 (:REWRITE REDUCE-RATIONALP-*))
                 (17 17 (:REWRITE RATIONALP-MINUS-X))
                 (17 17 (:META META-RATIONALP-CORRECT))
                 (16 16
                     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                 (16 16 (:REWRITE NORMALIZE-ADDENDS))
                 (8 8 (:REWRITE RTL::BITS-REVERSE-INDICES))
                 (8 8 (:REWRITE RTL::BITS-NEG-INDICES))
                 (5 5 (:REWRITE FOLD-CONSTS-IN-+))
                 (5 5 (:REWRITE RTL::ALL-BVECP-SUBRANGE))
                 (5 5 (:REWRITE RTL::ALL-BVECP-LEQ))
                 (5 5 (:REWRITE |(+ c (+ d x))|))
                 (4 4 (:REWRITE RTL::ALL-BVECP-INTEGERP))
                 (3 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                 (3 1
                    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                 (3 1
                    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                 (2 1 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
                 (1 1
                    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                 (1 1 (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
                 (1 1
                    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
                 (1 1 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
                 (1 1
                    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
                 (1 1 (:REWRITE |(equal c (/ x))|))
                 (1 1 (:REWRITE |(equal c (- x))|))
                 (1 1 (:REWRITE |(equal (/ x) c)|))
                 (1 1 (:REWRITE |(equal (/ x) (/ y))|))
                 (1 1 (:REWRITE |(equal (- x) c)|))
                 (1 1 (:REWRITE |(equal (- x) (- y))|)))
(RTL::SUM-SUM-RANGE
 (225 15 (:REWRITE ACL2-NUMBERP-X))
 (221 13 (:REWRITE RTL::BITS-TAIL-GEN))
 (112 14 (:REWRITE RATIONALP-X))
 (52 8 (:DEFINITION RTL::ALL-BVECP))
 (43 13 (:REWRITE RTL::BITS-TAIL))
 (31 31
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (31 31 (:REWRITE NORMALIZE-ADDENDS))
 (28 3 (:REWRITE RTL::A2-4-2))
 (24 24 (:REWRITE REDUCE-INTEGERP-+))
 (24 24 (:REWRITE INTEGERP-MINUS-X))
 (24 24 (:META META-INTEGERP-CORRECT))
 (24 2 (:REWRITE RTL::LEVEL1-4-2))
 (16 16 (:REWRITE RTL::ALL-BVECP-LEQ))
 (16 16 (:REWRITE RTL::ALL-BVECP-INTEGERP))
 (15 15 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (15 15 (:REWRITE RTL::BITS-NEG-INDICES))
 (14 14 (:REWRITE REDUCE-RATIONALP-+))
 (14 14 (:REWRITE REDUCE-RATIONALP-*))
 (14 14 (:REWRITE RATIONALP-MINUS-X))
 (14 14 (:META META-RATIONALP-CORRECT))
 (10 10 (:REWRITE RTL::ALL-BVECP-BVECP))
 (6 6 (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
 (6 6 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (5 2
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (5 2
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (4 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (4 2
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (4 2 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (4 2 (:REWRITE DEFAULT-LESS-THAN-1))
 (3 2 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (2
   2
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (2
  2
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (2 2 (:REWRITE THE-FLOOR-BELOW))
 (2 2 (:REWRITE THE-FLOOR-ABOVE))
 (2 2 (:REWRITE SIMPLIFY-SUMS-<))
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
 (1 1 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RTL::SUM-SUM-SIMPLE
 (126 2 (:DEFINITION RTL::SUM-SIMPLE))
 (102 2 (:REWRITE RTL::BITS-TAIL-GEN))
 (17 17
     (:TYPE-PRESCRIPTION RTL::ALL-BVECP-INTEGERP))
 (9 1 (:DEFINITION RTL::SUM-RANGE))
 (8 3 (:REWRITE DEFAULT-PLUS-2))
 (6 3 (:REWRITE DEFAULT-PLUS-1))
 (6 2
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (6 2 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (6 2 (:REWRITE DEFAULT-LESS-THAN-1))
 (6 2 (:REWRITE RTL::BITS-TAIL))
 (6 1 (:DEFINITION RTL::ALL-BVECP))
 (5 5 (:TYPE-PRESCRIPTION RTL::BVECP))
 (4 1 (:REWRITE RTL::A2-4-2))
 (3 3
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (3 3 (:REWRITE NORMALIZE-ADDENDS))
 (3 3 (:REWRITE RTL::ALL-BVECP-SUBRANGE))
 (2 2 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (2
   2
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (2
  2
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (2 2 (:REWRITE THE-FLOOR-BELOW))
 (2 2 (:REWRITE THE-FLOOR-ABOVE))
 (2 2 (:REWRITE SIMPLIFY-SUMS-<))
 (2 2 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (2 2
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (2 2
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (2 2 (:REWRITE INTEGERP-<-CONSTANT))
 (2 2 (:REWRITE DEFAULT-LESS-THAN-2))
 (2 2 (:REWRITE CONSTANT-<-INTEGERP))
 (2 2 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (2 2 (:REWRITE RTL::BITS-NEG-INDICES))
 (2 2 (:REWRITE RTL::ALL-BVECP-LEQ))
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
 (2 2 (:REWRITE |(< (+ c/d x) y)|))
 (2 2 (:REWRITE |(< (+ (- c) x) y)|))
 (2 1
    (:TYPE-PRESCRIPTION RTL::INTEGERP-SUM-RANGE))
 (2 1 (:REWRITE RTL::LEVEL1-4-2))
 (1 1 (:TYPE-PRESCRIPTION RTL::SUM-RANGE))
 (1 1
    (:TYPE-PRESCRIPTION RTL::ALL-BVECP-BVECP))
 (1 1 (:REWRITE RTL::ALL-BVECP-BVECP)))
(RTL::IMUL-THM (3 3 (:REWRITE DEFAULT-TIMES-2))
               (3 3 (:REWRITE DEFAULT-TIMES-1))
               (2 2
                  (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS)))
