(RP::MERGE-B+-TO-B+)
(RP::HIDE-X-IS-X-ALL)
(RP::LEN-OF-TAKE
     (36 4 (:DEFINITION LEN))
     (18 18 (:LINEAR LEN-WHEN-PREFIXP))
     (17 11 (:REWRITE DEFAULT-PLUS-2))
     (16 2 (:DEFINITION TAKE))
     (11 11
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (11 11 (:REWRITE NORMALIZE-ADDENDS))
     (11 11 (:REWRITE DEFAULT-PLUS-1))
     (8 8 (:TYPE-PRESCRIPTION TRUE-LISTP-TAKE))
     (8 8 (:REWRITE DEFAULT-CDR))
     (6 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (6 3
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (6 3
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (5 5 (:REWRITE ZP-OPEN))
     (5 5 (:REWRITE DEFAULT-CAR))
     (4 4
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (4 4
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (4 4 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (3 3 (:REWRITE THE-FLOOR-BELOW))
     (3 3 (:REWRITE THE-FLOOR-ABOVE))
     (3 3 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (3 3
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (3 3
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (3 3 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (3 3 (:REWRITE INTEGERP-<-CONSTANT))
     (3 3
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (3 3 (:REWRITE DEFAULT-LESS-THAN-2))
     (3 3 (:REWRITE DEFAULT-LESS-THAN-1))
     (3 3 (:REWRITE CONSTANT-<-INTEGERP))
     (3 3 (:REWRITE |(equal c (/ x))|))
     (3 3 (:REWRITE |(equal c (- x))|))
     (3 3 (:REWRITE |(equal (/ x) c)|))
     (3 3 (:REWRITE |(equal (/ x) (/ y))|))
     (3 3 (:REWRITE |(equal (- x) c)|))
     (3 3 (:REWRITE |(equal (- x) (- y))|))
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
     (3 3 (:REWRITE |(< (/ x) 0)|))
     (3 3 (:REWRITE |(< (/ x) (/ y))|))
     (3 3 (:REWRITE |(< (- x) c)|))
     (3 3 (:REWRITE |(< (- x) (- y))|))
     (3 3 (:REWRITE |(< (* x y) 0)|))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (2 2 (:REWRITE SIMPLIFY-SUMS-<))
     (2 2
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (2 2 (:REWRITE REDUCE-INTEGERP-+))
     (2 2 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (2 2 (:REWRITE INTEGERP-MINUS-X))
     (2 2
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (2 2 (:META META-INTEGERP-CORRECT)))
(RP::LEN-NTHCDR
     (108 61 (:REWRITE DEFAULT-PLUS-2))
     (68 61 (:REWRITE DEFAULT-PLUS-1))
     (60 60 (:LINEAR LEN-WHEN-PREFIXP))
     (43 43
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (29 29 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (29 3 (:REWRITE ACL2-NUMBERP-X))
     (27 9
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (26 16 (:REWRITE DEFAULT-LESS-THAN-1))
     (24 12
         (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
     (24 8 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (23 23 (:REWRITE DEFAULT-CDR))
     (22 13
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (22 13 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (20 13 (:REWRITE SIMPLIFY-SUMS-<))
     (17 17 (:REWRITE THE-FLOOR-BELOW))
     (17 17 (:REWRITE THE-FLOOR-ABOVE))
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
     (12 12 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (11 3 (:REWRITE RATIONALP-X))
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
     (8 8 (:REWRITE |(< (/ x) 0)|))
     (8 8 (:REWRITE |(< (* x y) 0)|))
     (7 7 (:REWRITE |(equal (+ (- c) x) y)|))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (6 6 (:REWRITE REDUCE-INTEGERP-+))
     (6 6 (:REWRITE INTEGERP-MINUS-X))
     (6 6
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (6 6 (:META META-INTEGERP-CORRECT))
     (5 5 (:REWRITE ZP-OPEN))
     (3 3 (:REWRITE REDUCE-RATIONALP-+))
     (3 3 (:REWRITE REDUCE-RATIONALP-*))
     (3 3 (:REWRITE RATIONALP-MINUS-X))
     (3 3
        (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (3 3 (:REWRITE DEFAULT-MINUS))
     (3 3
        (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (3 3 (:REWRITE |(< (if a b c) x)|))
     (3 3 (:META META-RATIONALP-CORRECT))
     (2 2 (:REWRITE |(+ c (+ d x))|))
     (1 1 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (1 1 (:REWRITE FOLD-CONSTS-IN-+))
     (1 1 (:REWRITE |(< y (+ (- c) x))|))
     (1 1 (:REWRITE |(< x (+ c/d y))|)))
(RP::LEN-OF-NTHCDR
     (61 39 (:REWRITE DEFAULT-PLUS-2))
     (44 39 (:REWRITE DEFAULT-PLUS-1))
     (28 19 (:REWRITE DEFAULT-LESS-THAN-1))
     (27 18
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (25 17 (:REWRITE SIMPLIFY-SUMS-<))
     (23 19
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (22 22 (:LINEAR LEN-WHEN-PREFIXP))
     (20 20
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (19 19 (:REWRITE THE-FLOOR-BELOW))
     (19 19 (:REWRITE THE-FLOOR-ABOVE))
     (19 19
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (19 19
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (19 19
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (19 19 (:REWRITE INTEGERP-<-CONSTANT))
     (19 19 (:REWRITE DEFAULT-LESS-THAN-2))
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
     (10 10 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (9 9 (:REWRITE |(< (/ x) 0)|))
     (9 9 (:REWRITE |(< (* x y) 0)|))
     (8 3
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (7 7
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (7 7
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (7 7 (:REWRITE REDUCE-INTEGERP-+))
     (7 7 (:REWRITE INTEGERP-MINUS-X))
     (7 7
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (7 7 (:META META-INTEGERP-CORRECT))
     (4 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (3 3 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
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
     (3 3 (:REWRITE |(+ c (+ d x))|))
     (2 2 (:REWRITE ZP-OPEN))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (2 2 (:REWRITE DEFAULT-MINUS))
     (2 2 (:REWRITE |(equal (+ (- c) x) y)|))
     (2 2 (:REWRITE |(< y (+ (- c) x))|))
     (2 2 (:REWRITE |(< x (+ c/d y))|))
     (2 2 (:REWRITE |(< 0 (/ x))|))
     (2 2 (:REWRITE |(< 0 (* x y))|))
     (2 2 (:REWRITE |(< (if a b c) x)|))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (1 1 (:REWRITE |(< (+ c/d x) y)|))
     (1 1 (:REWRITE |(< (+ (- c) x) y)|)))
(RP::TRUE-LIST-TAKE)
(RP::TRUE-LIST-NTHCDR)
(RP::TAKE-IS-[]-TAKE (16 2 (:DEFINITION TAKE))
                     (8 8 (:REWRITE ZP-OPEN))
                     (8 8 (:REWRITE DEFAULT-CAR))
                     (6 6
                        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                     (6 6 (:REWRITE NORMALIZE-ADDENDS))
                     (6 6 (:REWRITE DEFAULT-PLUS-2))
                     (6 6 (:REWRITE DEFAULT-PLUS-1))
                     (6 6 (:REWRITE DEFAULT-CDR))
                     (6 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                     (6 3
                        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                     (6 3
                        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                     (4 4 (:REWRITE TAKE-OPENER))
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
(RP::[]-CDR-IS-NTH-CDR
     (502 37
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (478 102 (:REWRITE ACL2-NUMBERP-X))
     (292 292 (:REWRITE DEFAULT-PLUS-2))
     (292 292 (:REWRITE DEFAULT-PLUS-1))
     (188 34 (:REWRITE RATIONALP-X))
     (159 159
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (159 159 (:REWRITE NORMALIZE-ADDENDS))
     (126 37 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (126 37
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (102 102
          (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (76 76 (:REWRITE THE-FLOOR-BELOW))
     (76 76 (:REWRITE THE-FLOOR-ABOVE))
     (76 76
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (76 76
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (76 76 (:REWRITE DEFAULT-LESS-THAN-2))
     (76 76 (:REWRITE DEFAULT-LESS-THAN-1))
     (73 73 (:REWRITE SIMPLIFY-SUMS-<))
     (73 73
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (73 73 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (73 73
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (73 73 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (73 73 (:REWRITE INTEGERP-<-CONSTANT))
     (73 73 (:REWRITE CONSTANT-<-INTEGERP))
     (73 73
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (73 73
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (73 73
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (73 73
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (73 73 (:REWRITE |(< c (- x))|))
     (73 73
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (73 73
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (73 73
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (73 73
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (73 73 (:REWRITE |(< (/ x) (/ y))|))
     (73 73 (:REWRITE |(< (- x) c)|))
     (73 73 (:REWRITE |(< (- x) (- y))|))
     (72 6 (:REWRITE |(+ y (+ x z))|))
     (57 57 (:REWRITE |(< x (+ c/d y))|))
     (57 57 (:REWRITE |(< 0 (* x y))|))
     (54 54
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (54 54
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (54 54 (:REWRITE |(< y (+ (- c) x))|))
     (54 54 (:REWRITE |(< 0 (/ x))|))
     (38 38 (:REWRITE REDUCE-INTEGERP-+))
     (38 38 (:REWRITE INTEGERP-MINUS-X))
     (38 38
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (38 38 (:META META-INTEGERP-CORRECT))
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
     (34 34 (:REWRITE REDUCE-RATIONALP-+))
     (34 34 (:REWRITE REDUCE-RATIONALP-*))
     (34 34 (:REWRITE RATIONALP-MINUS-X))
     (34 34
         (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (34 34 (:META META-RATIONALP-CORRECT)))
(RP::NTH-IS-CAR-NTHCDR
     (212 14 (:REWRITE ZP-OPEN))
     (163 7
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (139 21 (:REWRITE ACL2-NUMBERP-X))
     (59 7 (:REWRITE RATIONALP-X))
     (47 14 (:REWRITE DEFAULT-CAR))
     (45 7 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (45 7
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (36 36 (:REWRITE DEFAULT-PLUS-2))
     (36 36 (:REWRITE DEFAULT-PLUS-1))
     (30 6 (:REWRITE |(+ c (+ d x))|))
     (30 2 (:REWRITE |(+ (+ x y) z)|))
     (22 22
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (22 22 (:REWRITE NORMALIZE-ADDENDS))
     (21 21
         (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (11 11 (:REWRITE NTH-WHEN-PREFIXP))
     (7 7 (:REWRITE REDUCE-RATIONALP-+))
     (7 7 (:REWRITE REDUCE-RATIONALP-*))
     (7 7
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (7 7 (:REWRITE REDUCE-INTEGERP-+))
     (7 7
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (7 7 (:REWRITE RATIONALP-MINUS-X))
     (7 7
        (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (7 7 (:REWRITE INTEGERP-MINUS-X))
     (7 7
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (7 7
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (7 7 (:REWRITE |(equal c (/ x))|))
     (7 7 (:REWRITE |(equal c (- x))|))
     (7 7 (:REWRITE |(equal (/ x) c)|))
     (7 7 (:REWRITE |(equal (/ x) (/ y))|))
     (7 7 (:REWRITE |(equal (- x) c)|))
     (7 7 (:REWRITE |(equal (- x) (- y))|))
     (7 7 (:META META-RATIONALP-CORRECT))
     (7 7 (:META META-INTEGERP-CORRECT))
     (6 6 (:REWRITE THE-FLOOR-BELOW))
     (6 6 (:REWRITE THE-FLOOR-ABOVE))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (6 6 (:REWRITE SIMPLIFY-SUMS-<))
     (6 6
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (6 6 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (6 6 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (6 6
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (6 6
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (6 6 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (6 6 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (6 6 (:REWRITE INTEGERP-<-CONSTANT))
     (6 6 (:REWRITE DEFAULT-LESS-THAN-2))
     (6 6 (:REWRITE DEFAULT-LESS-THAN-1))
     (6 6 (:REWRITE CONSTANT-<-INTEGERP))
     (6 6 (:REWRITE |(< y (+ (- c) x))|))
     (6 6 (:REWRITE |(< x (+ c/d y))|))
     (6 6
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (6 6
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (6 6
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (6 6
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (6 6 (:REWRITE |(< c (- x))|))
     (6 6 (:REWRITE |(< 0 (/ x))|))
     (6 6 (:REWRITE |(< 0 (* x y))|))
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
     (2 2 (:REWRITE |(equal x (if a b c))|))
     (2 2 (:REWRITE |(equal (if a b c) x)|)))
(RP::[]-IS-NTH)
(RP::BITP-[]
     (286 22
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (264 44 (:REWRITE ACL2-NUMBERP-X))
     (110 22 (:REWRITE RATIONALP-X))
     (66 22
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (66 11 (:REWRITE O-INFP->NEQ-0))
     (44 44
         (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (33 33 (:TYPE-PRESCRIPTION O-FINP))
     (33 11 (:REWRITE O-FIRST-EXPT-O-INFP))
     (32 20 (:REWRITE DEFAULT-LESS-THAN-2))
     (31 18 (:REWRITE DEFAULT-PLUS-2))
     (24 24 (:REWRITE REDUCE-INTEGERP-+))
     (24 24 (:REWRITE INTEGERP-MINUS-X))
     (24 24
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (24 24 (:META META-INTEGERP-CORRECT))
     (24 13
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (24 13 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (23 19
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (22 22 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (22 22 (:REWRITE REDUCE-RATIONALP-+))
     (22 22 (:REWRITE REDUCE-RATIONALP-*))
     (22 22
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (22 22
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (22 22 (:REWRITE RATIONALP-MINUS-X))
     (22 22
         (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (22 22
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (22 22 (:REWRITE |(equal c (/ x))|))
     (22 22 (:REWRITE |(equal c (- x))|))
     (22 22 (:REWRITE |(equal (/ x) c)|))
     (22 22 (:REWRITE |(equal (/ x) (/ y))|))
     (22 22 (:REWRITE |(equal (- x) c)|))
     (22 22 (:REWRITE |(equal (- x) (- y))|))
     (22 22 (:META META-RATIONALP-CORRECT))
     (22 13 (:REWRITE SIMPLIFY-SUMS-<))
     (22 11 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
     (20 20 (:REWRITE THE-FLOOR-BELOW))
     (20 20 (:REWRITE THE-FLOOR-ABOVE))
     (20 20
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (20 20
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (20 20
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (20 20 (:REWRITE DEFAULT-LESS-THAN-1))
     (20 20 (:LINEAR LEN-WHEN-PREFIXP))
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
     (18 18
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (18 18 (:REWRITE NORMALIZE-ADDENDS))
     (18 18 (:REWRITE DEFAULT-PLUS-1))
     (15 15 (:REWRITE DEFAULT-CAR))
     (13 13 (:REWRITE NTH-WHEN-PREFIXP))
     (11 11
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (10 10 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (9 9 (:REWRITE |(< y (+ (- c) x))|))
     (9 9 (:REWRITE |(< x (+ c/d y))|))
     (8 8 (:REWRITE ZP-OPEN))
     (8 8 (:REWRITE DEFAULT-CDR))
     (8 8 (:REWRITE |(< (/ x) 0)|))
     (8 8 (:REWRITE |(< (* x y) 0)|))
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
     (1 1 (:REWRITE |(< (+ c/d x) y)|)))
(RP::BITP-CAR-LIST (1 1 (:REWRITE DEFAULT-CAR)))
(RP::CDR-[]-CDR (7 7 (:REWRITE DEFAULT-PLUS-2))
                (7 7 (:REWRITE DEFAULT-PLUS-1))
                (5 5 (:REWRITE DEFAULT-CDR))
                (4 4
                   (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                (4 4 (:REWRITE NORMALIZE-ADDENDS))
                (1 1 (:REWRITE ZP-OPEN)))
(RP::LEN-[]-CDR
     (1053 21 (:REWRITE RP::CDR-[]-CDR))
     (491 57
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (168 121 (:REWRITE DEFAULT-PLUS-2))
     (122 121 (:REWRITE DEFAULT-PLUS-1))
     (95 24 (:REWRITE |(+ c (+ d x))|))
     (73 73
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (66 57 (:REWRITE DEFAULT-LESS-THAN-1))
     (62 62 (:LINEAR LEN-WHEN-PREFIXP))
     (57 57 (:REWRITE THE-FLOOR-BELOW))
     (57 57 (:REWRITE THE-FLOOR-ABOVE))
     (57 57
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (57 57
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (57 57 (:REWRITE DEFAULT-LESS-THAN-2))
     (52 43
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (52 43 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (50 43 (:REWRITE SIMPLIFY-SUMS-<))
     (45 29 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (43 43
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (43 43 (:REWRITE INTEGERP-<-CONSTANT))
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
     (33 33 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (33 3 (:REWRITE |(+ y (+ x z))|))
     (21 11
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (20 20 (:REWRITE |(< x (+ c/d y))|))
     (20 20 (:REWRITE |(< 0 (* x y))|))
     (19 10 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (12 12
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (12 12
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (11 11
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (11 11 (:REWRITE |(equal c (/ x))|))
     (11 11 (:REWRITE |(equal c (- x))|))
     (11 11 (:REWRITE |(equal (/ x) c)|))
     (11 11 (:REWRITE |(equal (/ x) (/ y))|))
     (11 11 (:REWRITE |(equal (- x) c)|))
     (11 11 (:REWRITE |(equal (- x) (- y))|))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (6 6 (:REWRITE |(< y (+ (- c) x))|))
     (6 6 (:REWRITE |(< 0 (/ x))|))
     (1 1 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (1 1 (:REWRITE FOLD-CONSTS-IN-+))
     (1 1 (:REWRITE DEFAULT-MINUS))
     (1 1 (:REWRITE |(< (if a b c) x)|))
     (1 1 (:REWRITE |(+ x (if a b c))|)))
(RP::POS-LEN-IS-CONSP (2 2 (:LINEAR LEN-WHEN-PREFIXP))
                      (1 1 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS)))
(RP::BIT-LISTP-APPEND
     (2247 91 (:REWRITE RP::POS-LEN-IS-CONSP))
     (687 24
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (672 45 (:DEFINITION LEN))
     (562 62 (:REWRITE DEFAULT-CDR))
     (538 48 (:REWRITE ACL2-NUMBERP-X))
     (421 6 (:REWRITE LEN-OF-APPEND))
     (403 403 (:TYPE-PRESCRIPTION LEN))
     (347 6 (:REWRITE CONSP-OF-APPEND))
     (294 3 (:REWRITE CAR-OF-APPEND))
     (245 24 (:REWRITE RATIONALP-X))
     (200 6 (:REWRITE APPEND-WHEN-NOT-CONSP))
     (197 24
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (172 22 (:REWRITE DEFAULT-CAR))
     (172 12 (:REWRITE O-INFP->NEQ-0))
     (144 3 (:REWRITE CDR-OF-APPEND-WHEN-CONSP))
     (110 55 (:REWRITE DEFAULT-PLUS-2))
     (96 96 (:LINEAR LEN-WHEN-PREFIXP))
     (94 44 (:REWRITE DEFAULT-LESS-THAN-2))
     (88 44 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (63 55 (:REWRITE DEFAULT-PLUS-1))
     (61 44
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (61 12 (:REWRITE O-FIRST-EXPT-O-INFP))
     (53 53
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (53 53 (:REWRITE NORMALIZE-ADDENDS))
     (51 51 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (49 12 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
     (48 48
         (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (44 44 (:REWRITE THE-FLOOR-BELOW))
     (44 44 (:REWRITE THE-FLOOR-ABOVE))
     (44 44
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (44 44
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (44 44 (:REWRITE SIMPLIFY-SUMS-<))
     (44 44
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (44 44
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (44 44
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (44 44
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (44 44 (:REWRITE INTEGERP-<-CONSTANT))
     (44 44 (:REWRITE DEFAULT-LESS-THAN-1))
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
     (44 44 (:REWRITE |(< 0 (/ x))|))
     (44 44 (:REWRITE |(< 0 (* x y))|))
     (44 44
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (44 44
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (44 44
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (44 44
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (44 44 (:REWRITE |(< (/ x) (/ y))|))
     (44 44 (:REWRITE |(< (- x) c)|))
     (44 44 (:REWRITE |(< (- x) (- y))|))
     (36 36 (:TYPE-PRESCRIPTION O-FINP))
     (36 18
         (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
     (24 24 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (24 24 (:REWRITE REDUCE-RATIONALP-+))
     (24 24 (:REWRITE REDUCE-RATIONALP-*))
     (24 24
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (24 24 (:REWRITE REDUCE-INTEGERP-+))
     (24 24
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (24 24 (:REWRITE RATIONALP-MINUS-X))
     (24 24
         (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (24 24 (:REWRITE INTEGERP-MINUS-X))
     (24 24
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (24 24
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (24 24 (:REWRITE |(equal c (/ x))|))
     (24 24 (:REWRITE |(equal c (- x))|))
     (24 24 (:REWRITE |(equal (/ x) c)|))
     (24 24 (:REWRITE |(equal (/ x) (/ y))|))
     (24 24 (:REWRITE |(equal (- x) c)|))
     (24 24 (:REWRITE |(equal (- x) (- y))|))
     (24 24 (:META META-RATIONALP-CORRECT))
     (24 24 (:META META-INTEGERP-CORRECT))
     (18 18 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (18 18 (:TYPE-PRESCRIPTION BINARY-APPEND))
     (14 2 (:REWRITE |(+ y x)|))
     (12 12
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (6 6 (:REWRITE |(equal x (if a b c))|))
     (6 6 (:REWRITE |(equal (if a b c) x)|))
     (6 6 (:REWRITE |(< y (+ (- c) x))|))
     (6 6 (:REWRITE |(< x (+ c/d y))|))
     (2 2 (:REWRITE |(< x (if a b c))|)))
(RP::LEMMA2
     (265 1 (:DEFINITION RP::[]-CDR))
     (205 4 (:REWRITE ZP-OPEN))
     (195 5 (:REWRITE DEFAULT-CDR))
     (141 4 (:DEFINITION LEN))
     (140 2 (:REWRITE RP::CDR-[]-CDR))
     (105 12
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (17 13 (:REWRITE DEFAULT-PLUS-2))
     (15 12 (:REWRITE DEFAULT-LESS-THAN-2))
     (13 13 (:REWRITE DEFAULT-PLUS-1))
     (12 12 (:REWRITE THE-FLOOR-BELOW))
     (12 12 (:REWRITE THE-FLOOR-ABOVE))
     (12 12
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (12 12
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (12 12 (:REWRITE DEFAULT-LESS-THAN-1))
     (12 9
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (12 9 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (12 3 (:REWRITE |(+ c (+ d x))|))
     (11 9 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (10 9 (:REWRITE SIMPLIFY-SUMS-<))
     (9 9 (:REWRITE INTEGERP-<-CONSTANT))
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
     (6 6
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (6 6 (:REWRITE NORMALIZE-ADDENDS))
     (5 5 (:REWRITE |(< 0 (* x y))|))
     (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (4 4 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (4 4 (:LINEAR LEN-WHEN-PREFIXP))
     (3 3 (:REWRITE |(< x (+ c/d y))|))
     (3 3 (:REWRITE |(+ 0 x)|))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (2 2 (:REWRITE |(< 0 (/ x))|))
     (1 1 (:REWRITE DEFAULT-MINUS)))
(RP::ARRAY-CDR-1-IS-CDR
     (122 7 (:REWRITE DEFAULT-CDR))
     (118 6 (:REWRITE RP::POS-LEN-IS-CONSP))
     (38 3 (:DEFINITION LEN))
     (8 4 (:REWRITE DEFAULT-PLUS-2))
     (4 4
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (4 4 (:REWRITE NORMALIZE-ADDENDS))
     (4 4 (:REWRITE DEFAULT-PLUS-1))
     (4 2
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (4 2 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (4 2 (:REWRITE DEFAULT-LESS-THAN-2))
     (3 3 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (2 2 (:REWRITE THE-FLOOR-BELOW))
     (2 2 (:REWRITE THE-FLOOR-ABOVE))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (2 2 (:REWRITE SIMPLIFY-SUMS-<))
     (2 2 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (2 2
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (2 2
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (2 2 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (2 2 (:REWRITE RP::LEMMA2))
     (2 2 (:REWRITE INTEGERP-<-CONSTANT))
     (2 2 (:REWRITE DEFAULT-LESS-THAN-1))
     (2 2 (:REWRITE CONSTANT-<-INTEGERP))
     (2 2 (:REWRITE RP::CDR-[]-CDR))
     (2 2
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (2 2
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (2 2
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (2 2
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (2 2 (:REWRITE |(< c (- x))|))
     (2 2 (:REWRITE |(< 0 (/ x))|))
     (2 2 (:REWRITE |(< 0 (* x y))|))
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
     (2 2 (:LINEAR LEN-WHEN-PREFIXP))
     (1 1 (:REWRITE RP::LEN-[]-CDR))
     (1 1 (:REWRITE |(< x (if a b c))|)))
(RP::CONS-OF-CAR-AND-CDR-TO-[]
     (101 4 (:REWRITE RP::POS-LEN-IS-CONSP))
     (56 4 (:REWRITE DEFAULT-CDR))
     (20 2 (:DEFINITION LEN))
     (4 4 (:LINEAR LEN-WHEN-PREFIXP))
     (4 2
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (4 2 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (4 2 (:REWRITE DEFAULT-PLUS-2))
     (4 2 (:REWRITE DEFAULT-LESS-THAN-2))
     (2 2 (:REWRITE THE-FLOOR-BELOW))
     (2 2 (:REWRITE THE-FLOOR-ABOVE))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (2 2 (:REWRITE SIMPLIFY-SUMS-<))
     (2 2 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (2 2
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (2 2
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (2 2 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (2 2
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (2 2 (:REWRITE NORMALIZE-ADDENDS))
     (2 2 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (2 2 (:REWRITE RP::LEMMA2))
     (2 2 (:REWRITE INTEGERP-<-CONSTANT))
     (2 2 (:REWRITE DEFAULT-PLUS-1))
     (2 2 (:REWRITE DEFAULT-LESS-THAN-1))
     (2 2 (:REWRITE CONSTANT-<-INTEGERP))
     (2 2 (:REWRITE RP::CDR-[]-CDR))
     (2 2
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (2 2
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (2 2
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (2 2
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (2 2 (:REWRITE |(< c (- x))|))
     (2 2 (:REWRITE |(< 0 (/ x))|))
     (2 2 (:REWRITE |(< 0 (* x y))|))
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
     (1 1 (:REWRITE RP::LEN-[]-CDR))
     (1 1 (:REWRITE DEFAULT-CAR)))
(RP::CONS-OF-CAR-AND-CDR-TO-[]-2
     (3058 30 (:REWRITE RP::POS-LEN-IS-CONSP))
     (2898 10 (:REWRITE APPEND-WHEN-NOT-CONSP))
     (2738 9 (:DEFINITION LEN))
     (2646 12
           (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (2640 3 (:DEFINITION APPLY$-BADGEP))
     (1749 3 (:DEFINITION SUBSETP-EQUAL))
     (1698 42 (:DEFINITION MEMBER-EQUAL))
     (882 21
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (541 73
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (486 243
          (:TYPE-PRESCRIPTION RP::BITP-CAR-LIST))
     (396 36 (:REWRITE ACL2-NUMBERP-X))
     (341 289 (:REWRITE DEFAULT-CDR))
     (294 6 (:DEFINITION NATP))
     (243 243 (:TYPE-PRESCRIPTION RP::BIT-LISTP))
     (240 3 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (204 18 (:REWRITE RATIONALP-X))
     (181 73
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (126 63
          (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
     (93 93 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (80 80 (:REWRITE DEFAULT-CAR))
     (79 73 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (75 75 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (73 73
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (73 73
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (73 73
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (73 73 (:REWRITE |(equal c (/ x))|))
     (73 73 (:REWRITE |(equal c (- x))|))
     (73 73 (:REWRITE |(equal (/ x) c)|))
     (73 73 (:REWRITE |(equal (/ x) (/ y))|))
     (73 73 (:REWRITE |(equal (- x) c)|))
     (73 73 (:REWRITE |(equal (- x) (- y))|))
     (63 63 (:TYPE-PRESCRIPTION BINARY-APPEND))
     (63 63
         (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (57 57 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (42 42
         (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (36 36
         (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (36 18
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (36 3 (:DEFINITION ALL-NILS))
     (30 15
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (30 3 (:DEFINITION TRUE-LISTP))
     (26 26 (:LINEAR LEN-WHEN-PREFIXP))
     (24 24 (:REWRITE REDUCE-INTEGERP-+))
     (24 24 (:REWRITE INTEGERP-MINUS-X))
     (24 24
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (24 24 (:META META-INTEGERP-CORRECT))
     (22 14 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (22 14 (:REWRITE DEFAULT-LESS-THAN-2))
     (20 10 (:REWRITE DEFAULT-PLUS-2))
     (19 14
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (18 18 (:REWRITE REDUCE-RATIONALP-+))
     (18 18 (:REWRITE REDUCE-RATIONALP-*))
     (18 18 (:REWRITE RATIONALP-MINUS-X))
     (18 18
         (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (18 18 (:META META-RATIONALP-CORRECT))
     (18 9
         (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (15 15 (:TYPE-PRESCRIPTION ALL-NILS))
     (14 14 (:REWRITE THE-FLOOR-BELOW))
     (14 14 (:REWRITE THE-FLOOR-ABOVE))
     (14 14 (:REWRITE SIMPLIFY-SUMS-<))
     (14 14
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (14 14
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (14 14
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (14 14
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (14 14 (:REWRITE INTEGERP-<-CONSTANT))
     (14 14 (:REWRITE DEFAULT-LESS-THAN-1))
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
     (12 12 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (10 10
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (10 10 (:REWRITE NORMALIZE-ADDENDS))
     (10 10 (:REWRITE DEFAULT-PLUS-1))
     (9 9 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (8 8 (:REWRITE |(< 0 (/ x))|))
     (8 8 (:REWRITE |(< 0 (* x y))|))
     (6 6
        (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (6 6 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (6 6 (:REWRITE |(< (/ x) 0)|))
     (6 6 (:REWRITE |(< (* x y) 0)|))
     (6 3
        (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (2 2 (:REWRITE RP::LEMMA2))
     (2 2 (:REWRITE RP::CDR-[]-CDR))
     (1 1 (:REWRITE RP::LEN-[]-CDR))
     (1 1 (:REWRITE |(< x (if a b c))|)))
(RP::CONS-OF-[]-AND-CDR
     (57 4 (:REWRITE DEFAULT-CDR))
     (55 2 (:DEFINITION LEN))
     (6 3
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (6 3 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (6 3 (:REWRITE DEFAULT-LESS-THAN-2))
     (5 3 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (4 4 (:LINEAR LEN-WHEN-PREFIXP))
     (4 2 (:REWRITE DEFAULT-PLUS-2))
     (3 3 (:REWRITE THE-FLOOR-BELOW))
     (3 3 (:REWRITE THE-FLOOR-ABOVE))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (3 3 (:REWRITE SIMPLIFY-SUMS-<))
     (3 3
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (3 3
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (3 3 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (3 3 (:REWRITE INTEGERP-<-CONSTANT))
     (3 3 (:REWRITE DEFAULT-LESS-THAN-1))
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
     (3 3 (:REWRITE |(< 0 (/ x))|))
     (3 3 (:REWRITE |(< 0 (* x y))|))
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
     (2 2
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (2 2 (:REWRITE NORMALIZE-ADDENDS))
     (2 2 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (2 2 (:REWRITE RP::LEMMA2))
     (2 2 (:REWRITE DEFAULT-PLUS-1))
     (2 2 (:REWRITE RP::CDR-[]-CDR))
     (2 1 (:REWRITE DEFAULT-CAR))
     (1 1 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (1 1 (:REWRITE RP::LEN-[]-CDR)))
(RP::[]-CDR-TO-CONS-2-LEMMA
     (37 2 (:REWRITE RP::POS-LEN-IS-CONSP))
     (6 6 (:REWRITE DEFAULT-CDR))
     (4 1 (:DEFINITION LEN))
     (3 3
        (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
     (3 3 (:REWRITE DEFAULT-CAR))
     (1 1 (:REWRITE THE-FLOOR-BELOW))
     (1 1 (:REWRITE THE-FLOOR-ABOVE))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (1 1 (:REWRITE SIMPLIFY-SUMS-<))
     (1 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (1 1 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (1 1
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (1 1
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (1 1 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (1 1 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (1 1 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (1 1 (:REWRITE INTEGERP-<-CONSTANT))
     (1 1 (:REWRITE DEFAULT-LESS-THAN-2))
     (1 1 (:REWRITE DEFAULT-LESS-THAN-1))
     (1 1 (:REWRITE CONSTANT-<-INTEGERP))
     (1 1 (:REWRITE |(< x (if a b c))|))
     (1 1
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (1 1
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (1 1
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (1 1
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (1 1 (:REWRITE |(< c (- x))|))
     (1 1 (:REWRITE |(< 0 (/ x))|))
     (1 1 (:REWRITE |(< 0 (* x y))|))
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
(RP::[]-CDR-TO-CONS-2
     (1500 49 (:REWRITE RP::POS-LEN-IS-CONSP))
     (842 2
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (840 1 (:DEFINITION APPLY$-BADGEP))
     (583 1 (:DEFINITION SUBSETP-EQUAL))
     (566 14 (:DEFINITION MEMBER-EQUAL))
     (294 7
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (195 38
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (169 135 (:REWRITE DEFAULT-CDR))
     (162 81
          (:TYPE-PRESCRIPTION RP::BITP-CAR-LIST))
     (120 10 (:REWRITE ACL2-NUMBERP-X))
     (111 81 (:REWRITE DEFAULT-PLUS-2))
     (98 2 (:DEFINITION NATP))
     (85 38
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (81 81 (:TYPE-PRESCRIPTION RP::BIT-LISTP))
     (81 81 (:REWRITE DEFAULT-PLUS-1))
     (80 1 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (63 5 (:REWRITE RATIONALP-X))
     (54 54
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (54 54 (:REWRITE NORMALIZE-ADDENDS))
     (52 38 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (44 30 (:REWRITE DEFAULT-CAR))
     (40 40
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (38 38
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (38 38 (:REWRITE |(equal c (/ x))|))
     (38 38 (:REWRITE |(equal c (- x))|))
     (38 38 (:REWRITE |(equal (/ x) c)|))
     (38 38 (:REWRITE |(equal (/ x) (/ y))|))
     (38 38 (:REWRITE |(equal (- x) c)|))
     (38 38 (:REWRITE |(equal (- x) (- y))|))
     (35 23 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (35 23 (:REWRITE DEFAULT-LESS-THAN-2))
     (34 23
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (31 31 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (30 30 (:LINEAR LEN-WHEN-PREFIXP))
     (30 2 (:REWRITE |(+ (+ x y) z)|))
     (23 23 (:REWRITE THE-FLOOR-BELOW))
     (23 23 (:REWRITE THE-FLOOR-ABOVE))
     (23 23 (:REWRITE SIMPLIFY-SUMS-<))
     (23 23
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (23 23
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (23 23
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (23 23
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (23 23 (:REWRITE INTEGERP-<-CONSTANT))
     (23 23 (:REWRITE DEFAULT-LESS-THAN-1))
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
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (23 23
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (23 23
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (23 23
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (23 23 (:REWRITE |(< (/ x) (/ y))|))
     (23 23 (:REWRITE |(< (- x) c)|))
     (23 23 (:REWRITE |(< (- x) (- y))|))
     (21 21
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (21 21
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (21 21
         (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (21 21 (:REWRITE |(< 0 (/ x))|))
     (21 21 (:REWRITE |(< 0 (* x y))|))
     (17 17 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (17 17 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (14 14
         (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (12 12 (:REWRITE NTH-WHEN-PREFIXP))
     (12 6
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (12 1 (:DEFINITION ALL-NILS))
     (11 11
         (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
     (10 10
         (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (10 5
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (9 9 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (7 7 (:REWRITE REDUCE-INTEGERP-+))
     (7 7 (:REWRITE INTEGERP-MINUS-X))
     (7 7
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (7 7 (:REWRITE |(< y (+ (- c) x))|))
     (7 7 (:REWRITE |(< x (+ c/d y))|))
     (7 7 (:META META-INTEGERP-CORRECT))
     (6 3
        (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (5 5 (:TYPE-PRESCRIPTION ALL-NILS))
     (5 5 (:REWRITE REDUCE-RATIONALP-+))
     (5 5 (:REWRITE REDUCE-RATIONALP-*))
     (5 5 (:REWRITE RATIONALP-MINUS-X))
     (5 5
        (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (5 5 (:REWRITE |(equal (+ (- c) x) y)|))
     (5 5 (:REWRITE |(< x (if a b c))|))
     (5 5 (:META META-RATIONALP-CORRECT))
     (4 4 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (3 3 (:REWRITE |(equal x (if a b c))|))
     (3 3 (:REWRITE |(equal (if a b c) x)|))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (2 2 (:REWRITE |(< (/ x) 0)|))
     (2 2 (:REWRITE |(< (* x y) 0)|))
     (2 1
        (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (1 1 (:REWRITE FOLD-CONSTS-IN-+)))
(RP::[]-CDR-TO-CONS
     (613 10 (:REWRITE ZP-OPEN))
     (606 15 (:REWRITE DEFAULT-CDR))
     (409 19 (:REWRITE RP::POS-LEN-IS-CONSP))
     (311 32
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (276 8 (:REWRITE RP::[]-CDR-TO-CONS-2))
     (210 3 (:REWRITE RP::LEN-[]-CDR))
     (128 10 (:DEFINITION LEN))
     (50 40 (:REWRITE DEFAULT-PLUS-2))
     (40 40 (:REWRITE DEFAULT-PLUS-1))
     (37 32 (:REWRITE DEFAULT-LESS-THAN-2))
     (32 32 (:REWRITE THE-FLOOR-BELOW))
     (32 32 (:REWRITE THE-FLOOR-ABOVE))
     (32 32
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (32 32
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (32 32 (:REWRITE DEFAULT-LESS-THAN-1))
     (30 2 (:DEFINITION =))
     (28 23
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (28 23 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (25 23
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (24 23 (:REWRITE SIMPLIFY-SUMS-<))
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
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (23 23
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (23 23
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (23 23
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (23 23 (:REWRITE |(< (/ x) (/ y))|))
     (23 23 (:REWRITE |(< (- x) c)|))
     (23 23 (:REWRITE |(< (- x) (- y))|))
     (18 18
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (18 18 (:REWRITE NORMALIZE-ADDENDS))
     (13 13 (:REWRITE |(< 0 (* x y))|))
     (12 1 (:REWRITE DEFAULT-CAR))
     (10 10 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (10 10 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (9 9 (:REWRITE |(< x (+ c/d y))|))
     (8 8 (:LINEAR LEN-WHEN-PREFIXP))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (4 4 (:REWRITE |(< 0 (/ x))|))
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
     (2 2 (:REWRITE |(equal (+ (- c) x) y)|))
     (1 1 (:REWRITE |(< (+ c/d x) y)|))
     (1 1 (:REWRITE |(< (+ (- c) x) y)|)))
(RP::[]-TAKE-TO-LIST
     (374 22 (:REWRITE RP::POS-LEN-IS-CONSP))
     (152 4 (:REWRITE ZP-OPEN))
     (32 18 (:REWRITE DEFAULT-PLUS-2))
     (24 12
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (24 12 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (24 12 (:REWRITE DEFAULT-LESS-THAN-2))
     (20 16 (:REWRITE DEFAULT-CDR))
     (18 18 (:REWRITE DEFAULT-PLUS-1))
     (15 15
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (15 15 (:REWRITE NORMALIZE-ADDENDS))
     (12 12 (:REWRITE THE-FLOOR-BELOW))
     (12 12 (:REWRITE THE-FLOOR-ABOVE))
     (12 12
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (12 12
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (12 12 (:REWRITE SIMPLIFY-SUMS-<))
     (12 12
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (12 12
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (12 12
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (12 12
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (12 12 (:REWRITE INTEGERP-<-CONSTANT))
     (12 12 (:REWRITE DEFAULT-LESS-THAN-1))
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
     (12 12 (:REWRITE |(< 0 (/ x))|))
     (12 12 (:REWRITE |(< 0 (* x y))|))
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
     (12 12 (:LINEAR LEN-WHEN-PREFIXP))
     (9 9 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (9 5 (:REWRITE DEFAULT-CAR))
     (8 8
        (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
     (8 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (8 4
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (8 4
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
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
     (2 2 (:REWRITE |(< x (if a b c))|)))
(RP::BIT-LISTP-IS-TRUE-LISTP
     (311 14 (:REWRITE RP::POS-LEN-IS-CONSP))
     (168 84
          (:TYPE-PRESCRIPTION RP::BITP-CAR-LIST))
     (168 6
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (132 12 (:REWRITE ACL2-NUMBERP-X))
     (104 2 (:DEFINITION TRUE-LISTP))
     (72 7 (:DEFINITION LEN))
     (60 6 (:REWRITE RATIONALP-X))
     (58 58 (:TYPE-PRESCRIPTION LEN))
     (48 6
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (42 3 (:REWRITE O-INFP->NEQ-0))
     (16 8 (:REWRITE DEFAULT-PLUS-2))
     (15 3 (:REWRITE O-FIRST-EXPT-O-INFP))
     (12 12 (:REWRITE DEFAULT-CDR))
     (12 12
         (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (12 6
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (12 6 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (12 6 (:REWRITE DEFAULT-LESS-THAN-2))
     (12 3 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
     (10 10 (:LINEAR LEN-WHEN-PREFIXP))
     (9 9 (:TYPE-PRESCRIPTION O-FINP))
     (8 8
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (8 8 (:REWRITE NORMALIZE-ADDENDS))
     (8 8 (:REWRITE DEFAULT-PLUS-1))
     (7 7 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (6 6 (:REWRITE THE-FLOOR-BELOW))
     (6 6 (:REWRITE THE-FLOOR-ABOVE))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (6 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (6 6 (:REWRITE SIMPLIFY-SUMS-<))
     (6 6 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (6 6 (:REWRITE REDUCE-RATIONALP-+))
     (6 6 (:REWRITE REDUCE-RATIONALP-*))
     (6 6
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (6 6
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (6 6
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (6 6 (:REWRITE REDUCE-INTEGERP-+))
     (6 6
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (6 6 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (6 6 (:REWRITE RATIONALP-MINUS-X))
     (6 6
        (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (6 6 (:REWRITE INTEGERP-MINUS-X))
     (6 6 (:REWRITE INTEGERP-<-CONSTANT))
     (6 6
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (6 6
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (6 6 (:REWRITE DEFAULT-LESS-THAN-1))
     (6 6 (:REWRITE CONSTANT-<-INTEGERP))
     (6 6 (:REWRITE |(equal c (/ x))|))
     (6 6 (:REWRITE |(equal c (- x))|))
     (6 6 (:REWRITE |(equal (/ x) c)|))
     (6 6 (:REWRITE |(equal (/ x) (/ y))|))
     (6 6 (:REWRITE |(equal (- x) c)|))
     (6 6 (:REWRITE |(equal (- x) (- y))|))
     (6 6
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (6 6
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (6 6
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (6 6
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (6 6 (:REWRITE |(< c (- x))|))
     (6 6 (:REWRITE |(< 0 (/ x))|))
     (6 6 (:REWRITE |(< 0 (* x y))|))
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
     (6 6 (:META META-RATIONALP-CORRECT))
     (6 6 (:META META-INTEGERP-CORRECT))
     (4 4
        (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (3 3 (:REWRITE DEFAULT-CAR))
     (1 1 (:REWRITE |(< x (if a b c))|)))
(RP::APPEND-[]-TAKE
     (22367 57 (:REWRITE RP::[]-TAKE-TO-LIST))
     (21851 164 (:DEFINITION LEN))
     (18695 101
            (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (18667 14 (:DEFINITION APPLY$-BADGEP))
     (14899 458 (:REWRITE RP::POS-LEN-IS-CONSP))
     (8477 14 (:DEFINITION SUBSETP-EQUAL))
     (7924 196 (:DEFINITION MEMBER-EQUAL))
     (6373 5 (:REWRITE EQUAL-LEN-1))
     (4856 28
           (:REWRITE RP::BIT-LISTP-IS-TRUE-LISTP))
     (4772 28 (:DEFINITION RP::BIT-LISTP))
     (4428 445
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (4116 98
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (3978 1989
           (:TYPE-PRESCRIPTION RP::BITP-CAR-LIST))
     (3752 28 (:DEFINITION BITP))
     (3304 280 (:REWRITE ACL2-NUMBERP-X))
     (2910 14 (:DEFINITION TRUE-LISTP))
     (2272 46 (:REWRITE APPEND-WHEN-NOT-CONSP))
     (2129 2129 (:TYPE-PRESCRIPTION RP::BIT-LISTP))
     (1964 1964 (:TYPE-PRESCRIPTION LEN))
     (1736 140 (:REWRITE RATIONALP-X))
     (1639 14 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (1405 445
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (1372 28 (:DEFINITION NATP))
     (1265 23 (:DEFINITION BINARY-APPEND))
     (725 464
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (665 665 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (526 445 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (502 502 (:LINEAR LEN-WHEN-PREFIXP))
     (483 14 (:DEFINITION ALL-NILS))
     (479 277 (:REWRITE DEFAULT-PLUS-2))
     (464 464
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (445 445
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (445 445 (:REWRITE |(equal c (/ x))|))
     (445 445 (:REWRITE |(equal c (- x))|))
     (445 445 (:REWRITE |(equal (/ x) c)|))
     (445 445 (:REWRITE |(equal (/ x) (/ y))|))
     (445 445 (:REWRITE |(equal (- x) c)|))
     (445 445 (:REWRITE |(equal (- x) (- y))|))
     (434 434 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (409 232 (:REWRITE DEFAULT-LESS-THAN-2))
     (400 232
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (344 172
          (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (294 294
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (280 280
          (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (280 140
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (277 277 (:REWRITE DEFAULT-PLUS-1))
     (275 232
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (259 19 (:REWRITE |(equal (+ (- c) x) y)|))
     (252 126
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (252 126
          (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (239 239
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (239 239 (:REWRITE NORMALIZE-ADDENDS))
     (232 232 (:REWRITE THE-FLOOR-BELOW))
     (232 232 (:REWRITE THE-FLOOR-ABOVE))
     (232 232 (:REWRITE SIMPLIFY-SUMS-<))
     (232 232
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (232 232
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (232 232
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (232 232
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (232 232 (:REWRITE INTEGERP-<-CONSTANT))
     (232 232 (:REWRITE DEFAULT-LESS-THAN-1))
     (232 232 (:REWRITE CONSTANT-<-INTEGERP))
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
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (232 232
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (232 232
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (232 232
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (232 232 (:REWRITE |(< (/ x) (/ y))|))
     (232 232 (:REWRITE |(< (- x) c)|))
     (232 232 (:REWRITE |(< (- x) (- y))|))
     (204 204
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (204 204
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (204 204 (:REWRITE |(< 0 (/ x))|))
     (204 204 (:REWRITE |(< 0 (* x y))|))
     (196 196
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (170 170
          (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (168 168 (:REWRITE REDUCE-INTEGERP-+))
     (168 168 (:REWRITE INTEGERP-MINUS-X))
     (168 168
          (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (168 168 (:META META-INTEGERP-CORRECT))
     (140 140 (:REWRITE REDUCE-RATIONALP-+))
     (140 140 (:REWRITE REDUCE-RATIONALP-*))
     (140 140 (:REWRITE RATIONALP-MINUS-X))
     (140 140
          (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (140 140 (:META META-RATIONALP-CORRECT))
     (127 8 (:REWRITE EQUAL-LEN-0))
     (70 70 (:TYPE-PRESCRIPTION ALL-NILS))
     (56 56 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (53 1 (:REWRITE RP::LEN-CONS))
     (42 10 (:REWRITE CDR-OF-APPEND-WHEN-CONSP))
     (36 36
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (36 36 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (28 28
         (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
     (28 28
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (28 28
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (28 28 (:REWRITE |(< (/ x) 0)|))
     (28 28 (:REWRITE |(< (* x y) 0)|))
     (24 24 (:REWRITE |(< x (if a b c))|))
     (11 11 (:REWRITE NTH-WHEN-PREFIXP))
     (8 8 (:REWRITE |(< y (+ (- c) x))|))
     (8 8 (:REWRITE |(< x (+ c/d y))|))
     (6 6 (:REWRITE |(equal x (if a b c))|))
     (6 6 (:REWRITE |(equal (if a b c) x)|)))
(RP::APPEND-NIL)
(RP::[]-OF-TAKE
     (1415 58 (:REWRITE RP::POS-LEN-IS-CONSP))
     (915 11 (:REWRITE RP::[]-TAKE-TO-LIST))
     (827 32 (:DEFINITION LEN))
     (540 16 (:REWRITE DEFAULT-CAR))
     (364 364 (:TYPE-PRESCRIPTION LEN))
     (103 16
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (99 59 (:REWRITE DEFAULT-PLUS-2))
     (88 88 (:LINEAR LEN-WHEN-PREFIXP))
     (77 15 (:REWRITE ACL2-NUMBERP-X))
     (75 45 (:REWRITE DEFAULT-LESS-THAN-2))
     (74 44 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (74 8 (:REWRITE ZP-OPEN))
     (70 44
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (64 4 (:REWRITE |(equal (+ (- c) x) y)|))
     (59 59 (:REWRITE DEFAULT-PLUS-1))
     (54 20
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (53 53
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (53 53 (:REWRITE NORMALIZE-ADDENDS))
     (45 45 (:REWRITE THE-FLOOR-BELOW))
     (45 45 (:REWRITE THE-FLOOR-ABOVE))
     (45 45
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (45 45
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (45 45
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (45 45
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (45 45 (:REWRITE INTEGERP-<-CONSTANT))
     (45 45 (:REWRITE DEFAULT-LESS-THAN-1))
     (45 45 (:REWRITE CONSTANT-<-INTEGERP))
     (45 45
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (45 45
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (45 45
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (45 45
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (45 45 (:REWRITE |(< c (- x))|))
     (45 45
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (45 45
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (45 45
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (45 45
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (45 45 (:REWRITE |(< (/ x) (/ y))|))
     (45 45 (:REWRITE |(< (- x) c)|))
     (45 45 (:REWRITE |(< (- x) (- y))|))
     (44 44 (:REWRITE SIMPLIFY-SUMS-<))
     (41 16 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (41 16
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (36 18
         (:TYPE-PRESCRIPTION RP::BITP-CAR-LIST))
     (34 34 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (33 33
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (33 33
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (33 33 (:REWRITE |(< 0 (/ x))|))
     (33 33 (:REWRITE |(< 0 (* x y))|))
     (31 5 (:REWRITE RATIONALP-X))
     (20 20
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (18 18 (:TYPE-PRESCRIPTION RP::BIT-LISTP))
     (18 4 (:REWRITE |(+ c (+ d x))|))
     (16 16
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (16 16 (:REWRITE |(equal c (/ x))|))
     (16 16 (:REWRITE |(equal c (- x))|))
     (16 16 (:REWRITE |(equal (/ x) c)|))
     (16 16 (:REWRITE |(equal (/ x) (/ y))|))
     (16 16 (:REWRITE |(equal (- x) c)|))
     (16 16 (:REWRITE |(equal (- x) (- y))|))
     (15 15
         (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (12 12 (:REWRITE REDUCE-INTEGERP-+))
     (12 12 (:REWRITE INTEGERP-MINUS-X))
     (12 12
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (12 12 (:META META-INTEGERP-CORRECT))
     (11 11 (:REWRITE NTH-WHEN-PREFIXP))
     (8 8 (:REWRITE |(< (/ x) 0)|))
     (8 8 (:REWRITE |(< (* x y) 0)|))
     (7 7
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (7 7
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (5 5 (:REWRITE REDUCE-RATIONALP-+))
     (5 5 (:REWRITE REDUCE-RATIONALP-*))
     (5 5 (:REWRITE RATIONALP-MINUS-X))
     (5 5
        (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (5 5 (:META META-RATIONALP-CORRECT))
     (4 4 (:REWRITE |(equal x (if a b c))|))
     (4 4 (:REWRITE |(equal (if a b c) x)|))
     (4 4 (:REWRITE |(< x (if a b c))|))
     (2 2 (:REWRITE |(< y (+ (- c) x))|))
     (2 2 (:REWRITE |(< x (+ c/d y))|))
     (2 2 (:REWRITE |(+ 0 x)|)))
(RP::[]-OF-NTHCDR
     (2607 42 (:REWRITE RP::POS-LEN-IS-CONSP))
     (1110 7 (:REWRITE RP::LEN-OF-NTHCDR))
     (1060 73
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (793 11 (:REWRITE |(< x (if a b c))|))
     (754 52 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (739 7 (:DEFINITION NFIX))
     (478 478 (:TYPE-PRESCRIPTION LEN))
     (400 20 (:DEFINITION LEN))
     (280 188 (:REWRITE DEFAULT-PLUS-2))
     (218 98 (:REWRITE NORMALIZE-ADDENDS))
     (206 188 (:REWRITE DEFAULT-PLUS-1))
     (183 18 (:REWRITE ZP-OPEN))
     (137 11 (:REWRITE |(< (+ (- c) x) y)|))
     (132 80 (:REWRITE DEFAULT-LESS-THAN-2))
     (130 16 (:REWRITE |(< y (+ (- c) x))|))
     (109 57 (:REWRITE |(< c (- x))|))
     (109 55 (:REWRITE |(< (- x) c)|))
     (96 80 (:REWRITE DEFAULT-LESS-THAN-1))
     (93 38 (:REWRITE |(+ c (+ d x))|))
     (88 88
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (86 52
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (80 80 (:REWRITE THE-FLOOR-BELOW))
     (80 80 (:REWRITE THE-FLOOR-ABOVE))
     (73 73
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (73 73
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (70 10 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
     (57 57
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (57 57
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (57 57
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (57 57
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (57 57
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (57 57
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (57 57
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (57 57
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (57 57 (:REWRITE |(< (/ x) (/ y))|))
     (57 57 (:REWRITE |(< (- x) (- y))|))
     (56 56 (:LINEAR LEN-WHEN-PREFIXP))
     (53 53
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (53 53 (:REWRITE INTEGERP-<-CONSTANT))
     (53 53 (:REWRITE CONSTANT-<-INTEGERP))
     (52 42 (:REWRITE SIMPLIFY-SUMS-<))
     (52 12 (:REWRITE ACL2-NUMBERP-X))
     (52 4
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (39 5 (:REWRITE |(- (+ x y))|))
     (28 28 (:REWRITE |(< 0 (* x y))|))
     (23 23 (:REWRITE |(< 0 (/ x))|))
     (21 21
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (21 21
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (21 21 (:REWRITE |(< x (+ c/d y))|))
     (20 20 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (20 20 (:DEFINITION FIX))
     (20 4 (:REWRITE RATIONALP-X))
     (16 16 (:REWRITE DEFAULT-MINUS))
     (16 16 (:REWRITE |(< (+ c/d x) y)|))
     (15 15 (:REWRITE FOLD-CONSTS-IN-+))
     (15 15 (:REWRITE |(< (* x y) 0)|))
     (14 14 (:REWRITE NTH-WHEN-PREFIXP))
     (12 12 (:REWRITE DEFAULT-CAR))
     (12 12
         (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (12 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (12 4
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (11 11 (:REWRITE REDUCE-INTEGERP-+))
     (11 11 (:REWRITE INTEGERP-MINUS-X))
     (11 11
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (11 11 (:META META-INTEGERP-CORRECT))
     (10 10 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (10 10 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (10 10 (:REWRITE |(< (/ x) 0)|))
     (10 10 (:REWRITE |(+ x (- x))|))
     (7 7
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (7 7
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (4 4 (:REWRITE REDUCE-RATIONALP-+))
     (4 4 (:REWRITE REDUCE-RATIONALP-*))
     (4 4
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (4 4
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (4 4 (:REWRITE RATIONALP-MINUS-X))
     (4 4
        (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (4 4
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (4 4 (:REWRITE |(equal c (/ x))|))
     (4 4 (:REWRITE |(equal c (- x))|))
     (4 4 (:REWRITE |(equal (/ x) c)|))
     (4 4 (:REWRITE |(equal (/ x) (/ y))|))
     (4 4 (:REWRITE |(equal (- x) c)|))
     (4 4 (:REWRITE |(equal (- x) (- y))|))
     (4 4 (:REWRITE |(- (- x))|))
     (4 4 (:META META-RATIONALP-CORRECT))
     (1 1 (:REWRITE |(equal x (if a b c))|))
     (1 1 (:REWRITE |(equal (if a b c) x)|)))
(RP::TYPE-FIX-N2B (9 6 (:TYPE-PRESCRIPTION RP::TYPE-FIX))
                  (3 3 (:TYPE-PRESCRIPTION RP::N2B)))
(RP::HIDE-X-IS-X)
(RP::M2-OF-SINGLE-PP
     (104 8
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (102 102
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (102 102
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (102 102
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (100 20 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (100 20 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (100 20
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (100 20
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (96 16 (:REWRITE ACL2-NUMBERP-X))
     (67 5 (:REWRITE DEFAULT-MOD-RATIO))
     (57 2 (:REWRITE RP::BIT-FIX-OPENER))
     (56 2 (:LINEAR MOD-BOUNDS-3))
     (40 8 (:REWRITE RATIONALP-X))
     (34 7 (:REWRITE |(* y x)|))
     (29 19 (:REWRITE DEFAULT-TIMES-2))
     (27 27 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (27 27 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (27 27 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (25 19 (:REWRITE DEFAULT-TIMES-1))
     (24 8
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (24 4 (:LINEAR MOD-BOUNDS-2))
     (20 20 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (20 20
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (20 20 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (20 20
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (20 20 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (18 3 (:REWRITE O-INFP->NEQ-0))
     (16 16 (:REWRITE REDUCE-INTEGERP-+))
     (16 16 (:REWRITE INTEGERP-MINUS-X))
     (16 16
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (16 16
         (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (16 16 (:META META-INTEGERP-CORRECT))
     (12 12
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (9 9 (:TYPE-PRESCRIPTION O-FINP))
     (9 5 (:REWRITE DEFAULT-MOD-1))
     (9 3 (:REWRITE O-FIRST-EXPT-O-INFP))
     (8 8 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (8 8 (:REWRITE REDUCE-RATIONALP-+))
     (8 8 (:REWRITE REDUCE-RATIONALP-*))
     (8 8
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (8 8
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (8 8 (:REWRITE RATIONALP-MINUS-X))
     (8 8
        (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (8 8
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (8 8 (:REWRITE |(equal c (/ x))|))
     (8 8 (:REWRITE |(equal c (- x))|))
     (8 8 (:REWRITE |(equal (/ x) c)|))
     (8 8 (:REWRITE |(equal (/ x) (/ y))|))
     (8 8 (:REWRITE |(equal (- x) c)|))
     (8 8 (:REWRITE |(equal (- x) (- y))|))
     (8 8 (:META META-RATIONALP-CORRECT))
     (6 3 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
     (5 5 (:REWRITE DEFAULT-MOD-2))
     (5 5 (:REWRITE |(mod x 2)| . 2))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (1 1 (:TYPE-PRESCRIPTION BITP))
     (1 1 (:REWRITE DEFAULT-PLUS-2))
     (1 1 (:REWRITE DEFAULT-PLUS-1)))
(RP::LEMMA1 (465 93 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
            (465 93 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
            (433 93
                 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
            (433 93
                 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
            (426 426
                 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
            (426 426
                 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
            (426 426
                 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
            (192 7 (:REWRITE DEFAULT-MOD-RATIO))
            (178 2 (:LINEAR MOD-BOUNDS-3))
            (169 9 (:REWRITE |(* y x)|))
            (154 154
                 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
            (154 154
                 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
            (154 154
                 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
            (154 154
                 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
            (140 7 (:REWRITE SUM-IS-EVEN . 2))
            (93 93 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
            (93 93
                (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
            (93 93 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
            (93 93
                (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
            (93 93 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
            (71 71 (:REWRITE DEFAULT-TIMES-2))
            (71 71 (:REWRITE DEFAULT-TIMES-1))
            (62 62
                (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
            (61 13 (:REWRITE DEFAULT-PLUS-2))
            (61 13 (:REWRITE DEFAULT-PLUS-1))
            (34 2 (:REWRITE RP::STUPID-LEMMA1))
            (31 31 (:REWRITE REDUCE-INTEGERP-+))
            (31 31 (:REWRITE INTEGERP-MINUS-X))
            (31 31
                (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
            (31 31 (:META META-INTEGERP-CORRECT))
            (20 4 (:LINEAR MOD-BOUNDS-2))
            (13 13
                (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
            (13 13 (:REWRITE NORMALIZE-ADDENDS))
            (8 8 (:TYPE-PRESCRIPTION RATIONALP-MOD))
            (7 7 (:REWRITE DEFAULT-MOD-2))
            (7 7 (:REWRITE DEFAULT-MOD-1))
            (7 7 (:REWRITE |(mod x 2)| . 2))
            (2 2
               (:REWRITE INTEGERP-+-REDUCE-CONSTANT)))
(RP::B+-A-MINUS-A-BACKUP1-EXTRA
     (154 146 (:REWRITE DEFAULT-PLUS-1))
     (146 146 (:REWRITE DEFAULT-PLUS-2))
     (19 19
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (14 14 (:REWRITE |(+ c (+ d x))|))
     (8 8 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (8 8 (:REWRITE REDUCE-INTEGERP-+))
     (8 8 (:REWRITE INTEGERP-MINUS-X))
     (8 8
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (8 8 (:META META-INTEGERP-CORRECT))
     (7 7 (:REWRITE FOLD-CONSTS-IN-+))
     (2 2 (:REWRITE DEFAULT-MINUS)))
(RP::B+-A-MINUS-A-BACKUP1-EXTRA2
     (335 319 (:REWRITE DEFAULT-PLUS-1))
     (319 319 (:REWRITE DEFAULT-PLUS-2))
     (48 48
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (41 41 (:REWRITE |(+ c (+ d x))|))
     (26 26 (:REWRITE FOLD-CONSTS-IN-+))
     (16 16 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (10 10 (:REWRITE REDUCE-INTEGERP-+))
     (10 10 (:REWRITE INTEGERP-MINUS-X))
     (10 10
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (10 10 (:META META-INTEGERP-CORRECT))
     (2 2 (:REWRITE DEFAULT-MINUS)))
(RP::B+-A-MINUS-A-BACKUP1-EXTRA3
     (700 668 (:REWRITE DEFAULT-PLUS-1))
     (668 668 (:REWRITE DEFAULT-PLUS-2))
     (109 109
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (105 105 (:REWRITE |(+ c (+ d x))|))
     (74 74 (:REWRITE FOLD-CONSTS-IN-+))
     (32 32 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (12 12 (:REWRITE REDUCE-INTEGERP-+))
     (12 12 (:REWRITE INTEGERP-MINUS-X))
     (12 12
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (12 12 (:META META-INTEGERP-CORRECT))
     (2 2 (:REWRITE DEFAULT-MINUS)))
(RP::B+-A-MINUS-A-BACKUP2
     (72 68 (:REWRITE DEFAULT-PLUS-1))
     (68 68 (:REWRITE DEFAULT-PLUS-2))
     (9 9
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (6 6 (:REWRITE REDUCE-INTEGERP-+))
     (6 6 (:REWRITE INTEGERP-MINUS-X))
     (6 6
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (6 6 (:META META-INTEGERP-CORRECT))
     (5 5 (:REWRITE |(+ c (+ d x))|))
     (4 4 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (2 2 (:REWRITE FOLD-CONSTS-IN-+))
     (2 2 (:REWRITE DEFAULT-MINUS)))
(RP::B+-A-MINUS-A-BACKUP2-EXTRA
     (169 161 (:REWRITE DEFAULT-PLUS-1))
     (161 161 (:REWRITE DEFAULT-PLUS-2))
     (26 26
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (18 18 (:REWRITE |(+ c (+ d x))|))
     (11 11 (:REWRITE FOLD-CONSTS-IN-+))
     (8 8 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (8 8 (:REWRITE REDUCE-INTEGERP-+))
     (8 8 (:REWRITE INTEGERP-MINUS-X))
     (8 8
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (8 8 (:META META-INTEGERP-CORRECT))
     (2 2 (:REWRITE DEFAULT-MINUS)))
(RP::B+-A-MINUS-A-BACKUP2-EXTRA2
     (366 350 (:REWRITE DEFAULT-PLUS-1))
     (350 350 (:REWRITE DEFAULT-PLUS-2))
     (63 63
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (52 52 (:REWRITE |(+ c (+ d x))|))
     (37 37 (:REWRITE FOLD-CONSTS-IN-+))
     (16 16 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (10 10 (:REWRITE REDUCE-INTEGERP-+))
     (10 10 (:REWRITE INTEGERP-MINUS-X))
     (10 10
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (10 10 (:META META-INTEGERP-CORRECT))
     (2 2 (:REWRITE DEFAULT-MINUS)))
(RP::B+-A-MINUS-A-BACKUP2-EXTRA3
     (763 731 (:REWRITE DEFAULT-PLUS-1))
     (731 731 (:REWRITE DEFAULT-PLUS-2))
     (140 140
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (131 131 (:REWRITE |(+ c (+ d x))|))
     (100 100 (:REWRITE FOLD-CONSTS-IN-+))
     (32 32 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (12 12 (:REWRITE REDUCE-INTEGERP-+))
     (12 12 (:REWRITE INTEGERP-MINUS-X))
     (12 12
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (12 12 (:META META-INTEGERP-CORRECT))
     (2 2 (:REWRITE DEFAULT-MINUS)))
(RP::BA-COMM)
(RP::B+-COMM-1)
(RP::B+-COMM-1A (6 6 (:TYPE-PRESCRIPTION NUMERATOR-ZERO))
                (6 6
                   (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 2))
                (6 6
                   (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 1))
                (6 6
                   (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 2))
                (6 6
                   (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 1))
                (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B)))
(RP::B+-COMM-1B (30 30 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                (30 30 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                (30 30 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                (30 6 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
                (30 6 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
                (30 6 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
                (30 6 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
                (6 6 (:TYPE-PRESCRIPTION NUMERATOR-ZERO))
                (6 6
                   (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 2))
                (6 6
                   (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 1))
                (6 6
                   (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 2))
                (6 6
                   (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 1))
                (6 6 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
                (6 6 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
                (6 6 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
                (6 6 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
                (6 6 (:TYPE-PRESCRIPTION INTEGERP-MOD-2)))
(RP::B+-COMM-1C (30 30 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                (30 30 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                (30 30 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                (30 6 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
                (30 6 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
                (30 6 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
                (30 6 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
                (6 6 (:TYPE-PRESCRIPTION NUMERATOR-ZERO))
                (6 6
                   (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 2))
                (6 6
                   (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 1))
                (6 6
                   (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 2))
                (6 6
                   (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 1))
                (6 6 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
                (6 6 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
                (6 6 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
                (6 6 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
                (6 6 (:TYPE-PRESCRIPTION INTEGERP-MOD-2)))
(RP::B+-COMM-1D (60 12 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
                (60 12 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
                (60 12
                    (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
                (60 12
                    (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
                (54 54 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                (54 54 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                (54 54 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                (12 12 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
                (12 12
                    (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
                (12 12 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
                (12 12
                    (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
                (12 12 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
                (6 6 (:TYPE-PRESCRIPTION NUMERATOR-ZERO))
                (6 6
                   (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 2))
                (6 6
                   (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 1))
                (6 6
                   (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 2))
                (6 6
                   (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 1)))
(RP::B+-COMM-1E (30 6 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
                (30 6 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
                (30 6 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
                (30 6 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
                (24 24 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
                (24 24 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                (24 24 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                (24 24 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                (6 6 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
                (6 6 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
                (6 6 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
                (6 6 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
                (6 6 (:TYPE-PRESCRIPTION INTEGERP-MOD-2)))
(RP::B+-COMM-F)
(RP::B+-COMM-1G)
(RP::B+-COMM-2 (47 47 (:REWRITE DEFAULT-PLUS-2))
               (47 47 (:REWRITE DEFAULT-PLUS-1))
               (9 9
                  (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
               (9 9 (:REWRITE NORMALIZE-ADDENDS))
               (6 6 (:REWRITE REDUCE-INTEGERP-+))
               (6 6 (:REWRITE INTEGERP-MINUS-X))
               (6 6
                  (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
               (6 6 (:META META-INTEGERP-CORRECT))
               (2 2 (:REWRITE FOLD-CONSTS-IN-+))
               (2 2 (:REWRITE |(+ c (+ d x))|)))
(RP::B+-COMM-2-[] (54 54 (:REWRITE DEFAULT-PLUS-2))
                  (54 54 (:REWRITE DEFAULT-PLUS-1))
                  (10 10
                      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                  (10 10 (:REWRITE NORMALIZE-ADDENDS))
                  (6 6 (:REWRITE REDUCE-INTEGERP-+))
                  (6 6 (:REWRITE INTEGERP-MINUS-X))
                  (6 6
                     (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                  (6 6 (:META META-INTEGERP-CORRECT))
                  (2 2 (:REWRITE FOLD-CONSTS-IN-+))
                  (2 2 (:REWRITE |(+ c (+ d x))|)))
(RP::B+-REORDER-THM)
(RP::B+-REORDER-1A (108 108 (:REWRITE DEFAULT-PLUS-2))
                   (108 108 (:REWRITE DEFAULT-PLUS-1))
                   (26 26
                       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                   (26 26 (:REWRITE NORMALIZE-ADDENDS))
                   (11 11 (:REWRITE FOLD-CONSTS-IN-+))
                   (11 11 (:REWRITE |(+ c (+ d x))|))
                   (8 8 (:REWRITE REDUCE-INTEGERP-+))
                   (8 8 (:REWRITE INTEGERP-MINUS-X))
                   (8 8
                      (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                   (8 8 (:META META-INTEGERP-CORRECT)))
(RP::B+-REORDER-1B (127 127 (:REWRITE DEFAULT-PLUS-2))
                   (127 127 (:REWRITE DEFAULT-PLUS-1))
                   (33 33
                       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                   (33 33 (:REWRITE NORMALIZE-ADDENDS))
                   (12 12 (:REWRITE FOLD-CONSTS-IN-+))
                   (12 12 (:REWRITE |(+ c (+ d x))|))
                   (8 8 (:REWRITE REDUCE-INTEGERP-+))
                   (8 8 (:REWRITE INTEGERP-MINUS-X))
                   (8 8
                      (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                   (8 8 (:META META-INTEGERP-CORRECT)))
(RP::SUM-PP->PP-SUM-PP-1
     (78 6
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (72 12 (:REWRITE ACL2-NUMBERP-X))
     (57 2 (:REWRITE RP::BIT-FIX-OPENER))
     (30 6 (:REWRITE RATIONALP-X))
     (18 6
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (12 12
         (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (12 2 (:REWRITE O-INFP->NEQ-0))
     (11 11 (:REWRITE DEFAULT-PLUS-2))
     (11 11 (:REWRITE DEFAULT-PLUS-1))
     (10 10 (:REWRITE REDUCE-INTEGERP-+))
     (10 10 (:REWRITE INTEGERP-MINUS-X))
     (10 10
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (10 10 (:META META-INTEGERP-CORRECT))
     (6 6 (:TYPE-PRESCRIPTION O-FINP))
     (6 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (6 6 (:REWRITE REDUCE-RATIONALP-+))
     (6 6 (:REWRITE REDUCE-RATIONALP-*))
     (6 6
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (6 6
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (6 6 (:REWRITE RATIONALP-MINUS-X))
     (6 6
        (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (6 6
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (6 6 (:REWRITE |(equal c (/ x))|))
     (6 6 (:REWRITE |(equal c (- x))|))
     (6 6 (:REWRITE |(equal (/ x) c)|))
     (6 6 (:REWRITE |(equal (/ x) (/ y))|))
     (6 6 (:REWRITE |(equal (- x) c)|))
     (6 6 (:REWRITE |(equal (- x) (- y))|))
     (6 6 (:META META-RATIONALP-CORRECT))
     (6 2 (:REWRITE O-FIRST-EXPT-O-INFP))
     (4 2 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (2 2
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (2 2 (:REWRITE NORMALIZE-ADDENDS))
     (1 1 (:TYPE-PRESCRIPTION BITP)))
(RP::SUM-PP->PP-SUM-PP-2
     (78 6
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (72 12 (:REWRITE ACL2-NUMBERP-X))
     (57 2 (:REWRITE RP::BIT-FIX-OPENER))
     (30 6 (:REWRITE RATIONALP-X))
     (18 6
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (12 12
         (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (12 2 (:REWRITE O-INFP->NEQ-0))
     (10 10 (:REWRITE REDUCE-INTEGERP-+))
     (10 10 (:REWRITE INTEGERP-MINUS-X))
     (10 10
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (10 10 (:META META-INTEGERP-CORRECT))
     (7 7 (:REWRITE DEFAULT-PLUS-2))
     (7 7 (:REWRITE DEFAULT-PLUS-1))
     (6 6 (:TYPE-PRESCRIPTION O-FINP))
     (6 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (6 6 (:REWRITE REDUCE-RATIONALP-+))
     (6 6 (:REWRITE REDUCE-RATIONALP-*))
     (6 6
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (6 6
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (6 6 (:REWRITE RATIONALP-MINUS-X))
     (6 6
        (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (6 6
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (6 6 (:REWRITE |(equal c (/ x))|))
     (6 6 (:REWRITE |(equal c (- x))|))
     (6 6 (:REWRITE |(equal (/ x) c)|))
     (6 6 (:REWRITE |(equal (/ x) (/ y))|))
     (6 6 (:REWRITE |(equal (- x) c)|))
     (6 6 (:REWRITE |(equal (- x) (- y))|))
     (6 6 (:META META-RATIONALP-CORRECT))
     (6 2 (:REWRITE O-FIRST-EXPT-O-INFP))
     (4 2 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (2 2
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (2 2 (:REWRITE NORMALIZE-ADDENDS))
     (1 1 (:TYPE-PRESCRIPTION BITP)))
(RP::SUM-PP+_MERGE1)
(RP::SUM-PP+_MERGE2 (316 316 (:REWRITE DEFAULT-PLUS-2))
                    (316 316 (:REWRITE DEFAULT-PLUS-1))
                    (100 100
                         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                    (100 100 (:REWRITE NORMALIZE-ADDENDS))
                    (49 49 (:REWRITE FOLD-CONSTS-IN-+))
                    (49 49 (:REWRITE |(+ c (+ d x))|))
                    (10 10 (:REWRITE REDUCE-INTEGERP-+))
                    (10 10 (:REWRITE INTEGERP-MINUS-X))
                    (10 10
                        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                    (10 10 (:META META-INTEGERP-CORRECT)))
(RP::C-OF-SINGLE-PP-SUM (14 14 (:TYPE-PRESCRIPTION NUMERATOR-ZERO))
                        (14 14
                            (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 2))
                        (14 14
                            (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 1))
                        (14 14
                            (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 2))
                        (14 14
                            (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 1))
                        (14 14 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                        (14 14 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                        (14 14
                            (:TYPE-PRESCRIPTION NOT-INTEGERP-1B)))
(RP::S-OF-SINGLE-PP-SUM (75 15 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
                        (75 15 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
                        (75 15
                            (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
                        (75 15
                            (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
                        (72 72 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                        (72 72 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                        (72 72 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                        (15 15 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
                        (15 15
                            (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
                        (15 15 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
                        (15 15
                            (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
                        (15 15 (:TYPE-PRESCRIPTION INTEGERP-MOD-2)))
(RP::CONVERT-D2-TO-F2
     (4111 4111
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (4111 4111
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (4111 4111
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (1545 309 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (1545 309 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (1545 309
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (1545 309
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (309 309 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (309 309
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (309 309
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (309 309
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (309 309 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (279 31 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (279 31
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (279 31
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (279 31
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (279 31
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (155 31 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (155 31 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (155 31
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (155 31
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (155 31
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (155 31
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (155 31
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (155 31
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (155 31
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (155 31
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (151 8 (:REWRITE DEFAULT-MOD-RATIO))
     (135 9 (:REWRITE |(* (if a b c) x)|))
     (126 6 (:REWRITE DEFAULT-FLOOR-RATIO))
     (120 18 (:REWRITE |(* y x)|))
     (95 71 (:REWRITE DEFAULT-TIMES-1))
     (77 77 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (77 77 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (77 77 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (77 77 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (71 71 (:REWRITE DEFAULT-TIMES-2))
     (52 28 (:REWRITE DEFAULT-PLUS-1))
     (41 41
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (32 28 (:REWRITE DEFAULT-PLUS-2))
     (31 1 (:REWRITE |(floor (+ x r) i)|))
     (20 4 (:REWRITE DEFAULT-MINUS))
     (17 17
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (17 17 (:REWRITE NORMALIZE-ADDENDS))
     (16 8 (:REWRITE DEFAULT-MOD-1))
     (14 6 (:REWRITE DEFAULT-FLOOR-1))
     (11 11 (:REWRITE REDUCE-INTEGERP-+))
     (11 11 (:REWRITE INTEGERP-MINUS-X))
     (11 11
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (11 11 (:META META-INTEGERP-CORRECT))
     (8 8 (:REWRITE DEFAULT-MOD-2))
     (6 6 (:REWRITE DEFAULT-FLOOR-2))
     (4 4 (:REWRITE |(mod x 2)| . 2))
     (3 3 (:REWRITE |(floor x 2)| . 2))
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
     (1 1 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (1 1 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (1 1 (:REWRITE INTEGERP-<-CONSTANT))
     (1 1 (:REWRITE DEFAULT-LESS-THAN-2))
     (1 1 (:REWRITE DEFAULT-LESS-THAN-1))
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
     (1 1 (:REWRITE |(< (/ x) 0)|))
     (1 1 (:REWRITE |(< (/ x) (/ y))|))
     (1 1 (:REWRITE |(< (- x) c)|))
     (1 1 (:REWRITE |(< (- x) (- y))|))
     (1 1 (:REWRITE |(< (* x y) 0)|)))
(RP::C-MERGE-1
     (15541 15541
            (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (15541 15541
            (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (15541 15541
            (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (2990 598 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (2990 598 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (2990 598
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (2990 598
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (1470 50 (:REWRITE |(* (if a b c) x)|))
     (1204 84 (:REWRITE |(* y x)|))
     (1120 24 (:REWRITE DEFAULT-MOD-RATIO))
     (1070 20 (:REWRITE DEFAULT-FLOOR-RATIO))
     (771 467 (:REWRITE DEFAULT-TIMES-1))
     (598 598 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (598 598
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (598 598
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (598 598
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (598 598 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (548 548
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (548 548
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (548 548
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (548 548
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (498 246 (:REWRITE DEFAULT-PLUS-1))
     (467 467 (:REWRITE DEFAULT-TIMES-2))
     (405 45 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (405 45
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (405 45
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (405 45
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (405 45
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (313 313
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (286 246 (:REWRITE DEFAULT-PLUS-2))
     (225 45 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (225 45 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (225 45
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (225 45
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (225 45
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (225 45
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (225 45
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (225 45
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (225 45
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (225 45
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (192 6 (:REWRITE |(floor (+ x r) i)|))
     (167 167
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (167 167 (:REWRITE NORMALIZE-ADDENDS))
     (92 24 (:REWRITE DEFAULT-MOD-1))
     (88 20 (:REWRITE DEFAULT-FLOOR-1))
     (58 58 (:REWRITE FOLD-CONSTS-IN-+))
     (40 8 (:REWRITE DEFAULT-MINUS))
     (35 35 (:REWRITE REDUCE-INTEGERP-+))
     (35 35 (:REWRITE INTEGERP-MINUS-X))
     (35 35
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (35 35 (:META META-INTEGERP-CORRECT))
     (29 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (29 1
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (29 1
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (24 24 (:REWRITE DEFAULT-MOD-2))
     (20 20 (:REWRITE DEFAULT-FLOOR-2))
     (12 12 (:REWRITE |(mod x 2)| . 2))
     (10 10 (:REWRITE |(floor x 2)| . 2))
     (6 6 (:REWRITE THE-FLOOR-BELOW))
     (6 6 (:REWRITE THE-FLOOR-ABOVE))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (6 6 (:REWRITE SIMPLIFY-SUMS-<))
     (6 6
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (6 6 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (6 6 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (6 6
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (6 6
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (6 6 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (6 6 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (6 6 (:REWRITE INTEGERP-<-CONSTANT))
     (6 6 (:REWRITE DEFAULT-LESS-THAN-2))
     (6 6 (:REWRITE DEFAULT-LESS-THAN-1))
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
     (6 6 (:REWRITE |(< (/ x) 0)|))
     (6 6 (:REWRITE |(< (/ x) (/ y))|))
     (6 6 (:REWRITE |(< (- x) c)|))
     (6 6 (:REWRITE |(< (- x) (- y))|))
     (6 6 (:REWRITE |(< (* x y) 0)|))
     (3 3 (:REWRITE |(< (+ c/d x) y)|))
     (3 3 (:REWRITE |(< (+ (- c) x) y)|))
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
(RP::C-MERGE-1-TYPE-COND
     (1395 1395
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (1395 1395
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (1395 1395
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (230 230
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (230 230
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (230 230
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (230 230
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (189 65 (:REWRITE DEFAULT-PLUS-1))
     (141 73 (:REWRITE DEFAULT-TIMES-1))
     (110 22 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (110 22 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (110 22
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (110 22
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (73 73 (:REWRITE DEFAULT-TIMES-2))
     (73 65 (:REWRITE DEFAULT-PLUS-2))
     (50 4 (:REWRITE DEFAULT-MOD-RATIO))
     (45 45
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (29 29
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (29 29 (:REWRITE NORMALIZE-ADDENDS))
     (25 25 (:REWRITE REDUCE-INTEGERP-+))
     (25 25 (:REWRITE INTEGERP-MINUS-X))
     (25 25
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (25 25 (:META META-INTEGERP-CORRECT))
     (22 22 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (22 22
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (22 22 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (22 22
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (22 22 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (20 4 (:REWRITE DEFAULT-MINUS))
     (11 11 (:REWRITE FOLD-CONSTS-IN-+))
     (11 11 (:REWRITE |(+ c (+ d x))|))
     (4 4 (:REWRITE DEFAULT-MOD-2))
     (4 4 (:REWRITE DEFAULT-MOD-1))
     (2 2 (:REWRITE |(mod x 2)| . 2)))
(RP::C-MERGE-1-SHORTCUT
     (4992 4992
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (4992 4992
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (4992 4992
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (2000 400 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (2000 400 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (2000 400
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (2000 400
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (1000 32 (:REWRITE DEFAULT-FLOOR-RATIO))
     (875 875
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (875 875
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (875 875
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (875 875
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (864 96 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (864 96
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (864 96
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (864 96
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (864 96
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (504 36 (:REWRITE |(* (if a b c) x)|))
     (480 96 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (480 96 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (480 96
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (480 96
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (480 96
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (480 96
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (480 96
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (480 96
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (480 96
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (480 96
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (402 48 (:REWRITE |(* y x)|))
     (400 400 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (400 400
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (400 400
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (400 400
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (400 400 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (392 296 (:REWRITE DEFAULT-TIMES-1))
     (304 296 (:REWRITE DEFAULT-TIMES-2))
     (299 159 (:REWRITE DEFAULT-PLUS-2))
     (271 159 (:REWRITE DEFAULT-PLUS-1))
     (198 198
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (124 4 (:REWRITE |(floor (+ x r) i)|))
     (108 12 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (108 12
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (108 12
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (98 98
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (98 98 (:REWRITE NORMALIZE-ADDENDS))
     (84 84 (:REWRITE REDUCE-INTEGERP-+))
     (84 84 (:REWRITE INTEGERP-MINUS-X))
     (84 84
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (84 84 (:META META-INTEGERP-CORRECT))
     (80 32 (:REWRITE DEFAULT-FLOOR-1))
     (50 4 (:REWRITE DEFAULT-MOD-RATIO))
     (40 2 (:REWRITE SUM-IS-EVEN . 2))
     (32 32 (:REWRITE DEFAULT-FLOOR-2))
     (14 14 (:REWRITE FOLD-CONSTS-IN-+))
     (14 14 (:REWRITE |(floor x 2)| . 2))
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
     (12 12 (:REWRITE |(equal (+ (- c) x) y)|))
     (4 4 (:REWRITE THE-FLOOR-BELOW))
     (4 4 (:REWRITE THE-FLOOR-ABOVE))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (4 4 (:REWRITE SIMPLIFY-SUMS-<))
     (4 4
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (4 4 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (4 4
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (4 4
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (4 4 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (4 4 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (4 4 (:REWRITE INTEGERP-<-CONSTANT))
     (4 4 (:REWRITE DEFAULT-MOD-2))
     (4 4 (:REWRITE DEFAULT-MOD-1))
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
     (4 4 (:REWRITE |(< (/ x) 0)|))
     (4 4 (:REWRITE |(< (/ x) (/ y))|))
     (4 4 (:REWRITE |(< (- x) c)|))
     (4 4 (:REWRITE |(< (- x) (- y))|))
     (4 4 (:REWRITE |(< (* x y) 0)|))
     (2 2 (:REWRITE |(mod x 2)| . 2)))
(RP::C-MERGE-2
     (9295 9295
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (9295 9295
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (9295 9295
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (1655 331 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (1655 331 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (1655 331
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (1655 331
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (608 48 (:REWRITE |(* y x)|))
     (585 27 (:REWRITE |(* (if a b c) x)|))
     (512 16 (:REWRITE DEFAULT-MOD-RATIO))
     (487 14 (:REWRITE DEFAULT-FLOOR-RATIO))
     (459 51 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (459 51
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (459 51
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (459 51
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (459 51
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (449 449
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (449 449
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (449 449
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (449 449
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (331 331 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (331 331
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (331 331
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (331 331
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (331 331 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (303 279 (:REWRITE DEFAULT-TIMES-1))
     (299 155 (:REWRITE DEFAULT-PLUS-2))
     (295 279 (:REWRITE DEFAULT-TIMES-2))
     (283 155 (:REWRITE DEFAULT-PLUS-1))
     (255 51 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (255 51 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (255 51
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (255 51
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (255 51
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (255 51
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (255 51
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (255 51
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (255 51
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (255 51
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (190 190
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (103 103
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (103 103 (:REWRITE NORMALIZE-ADDENDS))
     (95 3 (:REWRITE |(floor (+ x r) i)|))
     (47 47 (:REWRITE REDUCE-INTEGERP-+))
     (47 47 (:REWRITE INTEGERP-MINUS-X))
     (47 47
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (47 47 (:META META-INTEGERP-CORRECT))
     (40 8 (:REWRITE DEFAULT-MINUS))
     (32 32 (:REWRITE FOLD-CONSTS-IN-+))
     (27 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (27 3
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (27 3
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (24 16 (:REWRITE DEFAULT-MOD-1))
     (22 14 (:REWRITE DEFAULT-FLOOR-1))
     (16 16 (:REWRITE DEFAULT-MOD-2))
     (14 14 (:REWRITE DEFAULT-FLOOR-2))
     (8 8 (:REWRITE |(mod x 2)| . 2))
     (7 7 (:REWRITE |(floor x 2)| . 2))
     (3 3 (:REWRITE THE-FLOOR-BELOW))
     (3 3 (:REWRITE THE-FLOOR-ABOVE))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (3 3 (:REWRITE SIMPLIFY-SUMS-<))
     (3 3
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (3 3 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (3 3 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (3 3
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (3 3
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (3 3
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (3 3
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (3 3 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (3 3 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (3 3 (:REWRITE INTEGERP-<-CONSTANT))
     (3 3
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (3 3 (:REWRITE DEFAULT-LESS-THAN-2))
     (3 3 (:REWRITE DEFAULT-LESS-THAN-1))
     (3 3 (:REWRITE CONSTANT-<-INTEGERP))
     (3 3 (:REWRITE |(equal c (/ x))|))
     (3 3 (:REWRITE |(equal c (- x))|))
     (3 3 (:REWRITE |(equal (/ x) c)|))
     (3 3 (:REWRITE |(equal (/ x) (/ y))|))
     (3 3 (:REWRITE |(equal (- x) c)|))
     (3 3 (:REWRITE |(equal (- x) (- y))|))
     (3 3 (:REWRITE |(equal (+ (- c) x) y)|))
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
     (3 3 (:REWRITE |(< (/ x) 0)|))
     (3 3 (:REWRITE |(< (/ x) (/ y))|))
     (3 3 (:REWRITE |(< (- x) c)|))
     (3 3 (:REWRITE |(< (- x) (- y))|))
     (3 3 (:REWRITE |(< (* x y) 0)|))
     (1 1 (:REWRITE |(< (+ c/d x) y)|))
     (1 1 (:REWRITE |(< (+ (- c) x) y)|)))
(RP::C-MERGE-2-SLOW
     (25186 25186
            (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (25186 25186
            (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (25186 25186
            (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (4190 838 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (4190 838 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (4190 838
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (4190 838
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (838 838 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (838 838
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (838 838
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (838 838
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (838 838 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (651 651
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (651 651
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (651 651
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (651 651
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (639 215 (:REWRITE DEFAULT-PLUS-2))
     (608 48 (:REWRITE |(* y x)|))
     (585 27 (:REWRITE |(* (if a b c) x)|))
     (512 16 (:REWRITE DEFAULT-MOD-RATIO))
     (487 14 (:REWRITE DEFAULT-FLOOR-RATIO))
     (486 54 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (486 54
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (486 54
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (486 54
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (486 54
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (349 215 (:REWRITE DEFAULT-PLUS-1))
     (303 279 (:REWRITE DEFAULT-TIMES-1))
     (295 279 (:REWRITE DEFAULT-TIMES-2))
     (270 54 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (270 54 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (270 54
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (270 54
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (270 54
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (270 54
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (270 54
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (270 54
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (270 54
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (270 54
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (190 190
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (119 119
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (108 12
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (108 12
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (95 3 (:REWRITE |(floor (+ x r) i)|))
     (49 49 (:REWRITE REDUCE-INTEGERP-+))
     (49 49 (:REWRITE INTEGERP-MINUS-X))
     (49 49
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (49 49 (:META META-INTEGERP-CORRECT))
     (41 41 (:REWRITE FOLD-CONSTS-IN-+))
     (40 8 (:REWRITE DEFAULT-MINUS))
     (24 16 (:REWRITE DEFAULT-MOD-1))
     (22 14 (:REWRITE DEFAULT-FLOOR-1))
     (16 16 (:REWRITE DEFAULT-MOD-2))
     (14 14 (:REWRITE DEFAULT-FLOOR-2))
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
     (12 12 (:REWRITE |(equal (+ (- c) x) y)|))
     (8 8 (:REWRITE |(mod x 2)| . 2))
     (7 7 (:REWRITE |(floor x 2)| . 2))
     (6 6 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (3 3 (:REWRITE THE-FLOOR-BELOW))
     (3 3 (:REWRITE THE-FLOOR-ABOVE))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (3 3 (:REWRITE SIMPLIFY-SUMS-<))
     (3 3
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (3 3 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (3 3 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (3 3
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (3 3
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (3 3 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (3 3 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (3 3 (:REWRITE INTEGERP-<-CONSTANT))
     (3 3 (:REWRITE DEFAULT-LESS-THAN-2))
     (3 3 (:REWRITE DEFAULT-LESS-THAN-1))
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
     (3 3 (:REWRITE |(< (/ x) 0)|))
     (3 3 (:REWRITE |(< (/ x) (/ y))|))
     (3 3 (:REWRITE |(< (- x) c)|))
     (3 3 (:REWRITE |(< (- x) (- y))|))
     (3 3 (:REWRITE |(< (* x y) 0)|))
     (1 1 (:REWRITE |(< (+ c/d x) y)|))
     (1 1 (:REWRITE |(< (+ (- c) x) y)|)))
(RP::C-MERGE-2-SIDE-COND
     (729 729
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (729 729
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (729 729
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (140 140
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (140 140
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (140 140
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (140 140
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (76 60 (:REWRITE DEFAULT-TIMES-1))
     (70 14 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (70 14 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (70 14
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (70 14
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (68 44 (:REWRITE DEFAULT-PLUS-1))
     (60 44 (:REWRITE DEFAULT-PLUS-2))
     (50 4 (:REWRITE DEFAULT-MOD-RATIO))
     (33 33
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (24 24 (:REWRITE REDUCE-INTEGERP-+))
     (24 24 (:REWRITE INTEGERP-MINUS-X))
     (24 24
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (24 24 (:META META-INTEGERP-CORRECT))
     (20 20
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (20 20 (:REWRITE NORMALIZE-ADDENDS))
     (20 4 (:REWRITE DEFAULT-MINUS))
     (14 14 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (14 14
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (14 14 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (14 14
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (14 14 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (14 2 (:REWRITE ACL2-NUMBERP-X))
     (4 4 (:REWRITE FOLD-CONSTS-IN-+))
     (4 4 (:REWRITE DEFAULT-MOD-2))
     (4 4 (:REWRITE DEFAULT-MOD-1))
     (4 4 (:REWRITE |(+ c (+ d x))|))
     (2 2 (:REWRITE REDUCE-RATIONALP-+))
     (2 2 (:REWRITE REDUCE-RATIONALP-*))
     (2 2 (:REWRITE RATIONALP-X))
     (2 2 (:REWRITE RATIONALP-MINUS-X))
     (2 2
        (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (2 2
        (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (2 2 (:REWRITE |(mod x 2)| . 2))
     (2 2 (:META META-RATIONALP-CORRECT)))
(RP::C-MERGE-2R
     (9295 9295
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (9295 9295
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (9295 9295
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (1655 331 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (1655 331 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (1655 331
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (1655 331
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (608 48 (:REWRITE |(* y x)|))
     (585 27 (:REWRITE |(* (if a b c) x)|))
     (512 16 (:REWRITE DEFAULT-MOD-RATIO))
     (487 14 (:REWRITE DEFAULT-FLOOR-RATIO))
     (459 51 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (459 51
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (459 51
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (459 51
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (459 51
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (439 439
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (439 439
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (439 439
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (439 439
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (367 159 (:REWRITE DEFAULT-PLUS-2))
     (331 331 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (331 331
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (331 331
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (331 331
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (331 331 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (297 273 (:REWRITE DEFAULT-TIMES-1))
     (289 273 (:REWRITE DEFAULT-TIMES-2))
     (255 51 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (255 51 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (255 51
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (255 51
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (255 51
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (255 51
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (255 51
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (255 51
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (255 51
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (255 51
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (223 159 (:REWRITE DEFAULT-PLUS-1))
     (184 184
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (103 103
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (103 103 (:REWRITE NORMALIZE-ADDENDS))
     (95 3 (:REWRITE |(floor (+ x r) i)|))
     (43 43 (:REWRITE REDUCE-INTEGERP-+))
     (43 43 (:REWRITE INTEGERP-MINUS-X))
     (43 43
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (43 43 (:META META-INTEGERP-CORRECT))
     (40 8 (:REWRITE DEFAULT-MINUS))
     (32 32 (:REWRITE FOLD-CONSTS-IN-+))
     (27 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (27 3
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (27 3
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (24 16 (:REWRITE DEFAULT-MOD-1))
     (22 14 (:REWRITE DEFAULT-FLOOR-1))
     (16 16 (:REWRITE DEFAULT-MOD-2))
     (14 14 (:REWRITE DEFAULT-FLOOR-2))
     (8 8 (:REWRITE |(mod x 2)| . 2))
     (7 7 (:REWRITE |(floor x 2)| . 2))
     (3 3 (:REWRITE THE-FLOOR-BELOW))
     (3 3 (:REWRITE THE-FLOOR-ABOVE))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (3 3 (:REWRITE SIMPLIFY-SUMS-<))
     (3 3
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (3 3 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (3 3 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (3 3
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (3 3
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (3 3
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (3 3
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (3 3 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (3 3 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (3 3 (:REWRITE INTEGERP-<-CONSTANT))
     (3 3
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (3 3 (:REWRITE DEFAULT-LESS-THAN-2))
     (3 3 (:REWRITE DEFAULT-LESS-THAN-1))
     (3 3 (:REWRITE CONSTANT-<-INTEGERP))
     (3 3 (:REWRITE |(equal c (/ x))|))
     (3 3 (:REWRITE |(equal c (- x))|))
     (3 3 (:REWRITE |(equal (/ x) c)|))
     (3 3 (:REWRITE |(equal (/ x) (/ y))|))
     (3 3 (:REWRITE |(equal (- x) c)|))
     (3 3 (:REWRITE |(equal (- x) (- y))|))
     (3 3 (:REWRITE |(equal (+ (- c) x) y)|))
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
     (3 3 (:REWRITE |(< (/ x) 0)|))
     (3 3 (:REWRITE |(< (/ x) (/ y))|))
     (3 3 (:REWRITE |(< (- x) c)|))
     (3 3 (:REWRITE |(< (- x) (- y))|))
     (3 3 (:REWRITE |(< (* x y) 0)|))
     (1 1 (:REWRITE |(< (+ c/d x) y)|))
     (1 1 (:REWRITE |(< (+ (- c) x) y)|)))
(RP::C-MERGE-2R-SLOW
     (25186 25186
            (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (25186 25186
            (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (25186 25186
            (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (4190 838 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (4190 838 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (4190 838
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (4190 838
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (838 838 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (838 838
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (838 838
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (838 838
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (838 838 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (707 219 (:REWRITE DEFAULT-PLUS-2))
     (641 641
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (641 641
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (641 641
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (641 641
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (608 48 (:REWRITE |(* y x)|))
     (585 27 (:REWRITE |(* (if a b c) x)|))
     (512 16 (:REWRITE DEFAULT-MOD-RATIO))
     (487 14 (:REWRITE DEFAULT-FLOOR-RATIO))
     (486 54 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (486 54
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (486 54
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (486 54
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (486 54
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (297 273 (:REWRITE DEFAULT-TIMES-1))
     (289 273 (:REWRITE DEFAULT-TIMES-2))
     (289 219 (:REWRITE DEFAULT-PLUS-1))
     (270 54 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (270 54 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (270 54
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (270 54
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (270 54
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (270 54
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (270 54
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (270 54
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (270 54
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (270 54
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (184 184
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (119 119
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (108 12
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (108 12
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (95 3 (:REWRITE |(floor (+ x r) i)|))
     (45 45 (:REWRITE REDUCE-INTEGERP-+))
     (45 45 (:REWRITE INTEGERP-MINUS-X))
     (45 45
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (45 45 (:META META-INTEGERP-CORRECT))
     (41 41 (:REWRITE FOLD-CONSTS-IN-+))
     (40 8 (:REWRITE DEFAULT-MINUS))
     (24 16 (:REWRITE DEFAULT-MOD-1))
     (22 14 (:REWRITE DEFAULT-FLOOR-1))
     (16 16 (:REWRITE DEFAULT-MOD-2))
     (14 14 (:REWRITE DEFAULT-FLOOR-2))
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
     (12 12 (:REWRITE |(equal (+ (- c) x) y)|))
     (8 8 (:REWRITE |(mod x 2)| . 2))
     (7 7 (:REWRITE |(floor x 2)| . 2))
     (6 6 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (3 3 (:REWRITE THE-FLOOR-BELOW))
     (3 3 (:REWRITE THE-FLOOR-ABOVE))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (3 3 (:REWRITE SIMPLIFY-SUMS-<))
     (3 3
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (3 3 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (3 3 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (3 3
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (3 3
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (3 3 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (3 3 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (3 3 (:REWRITE INTEGERP-<-CONSTANT))
     (3 3 (:REWRITE DEFAULT-LESS-THAN-2))
     (3 3 (:REWRITE DEFAULT-LESS-THAN-1))
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
     (3 3 (:REWRITE |(< (/ x) 0)|))
     (3 3 (:REWRITE |(< (/ x) (/ y))|))
     (3 3 (:REWRITE |(< (- x) c)|))
     (3 3 (:REWRITE |(< (- x) (- y))|))
     (3 3 (:REWRITE |(< (* x y) 0)|))
     (1 1 (:REWRITE |(< (+ c/d x) y)|))
     (1 1 (:REWRITE |(< (+ (- c) x) y)|)))
(RP::C-MERGE-2R-SIDE-COND
     (729 729
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (729 729
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (729 729
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (140 140
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (140 140
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (140 140
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (140 140
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (76 60 (:REWRITE DEFAULT-TIMES-1))
     (70 46 (:REWRITE DEFAULT-PLUS-1))
     (70 14 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (70 14 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (70 14
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (70 14
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (62 46 (:REWRITE DEFAULT-PLUS-2))
     (50 4 (:REWRITE DEFAULT-MOD-RATIO))
     (33 33
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (24 24 (:REWRITE REDUCE-INTEGERP-+))
     (24 24 (:REWRITE INTEGERP-MINUS-X))
     (24 24
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (24 24 (:META META-INTEGERP-CORRECT))
     (20 20
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (20 20 (:REWRITE NORMALIZE-ADDENDS))
     (20 4 (:REWRITE DEFAULT-MINUS))
     (14 14 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (14 14
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (14 14 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (14 14
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (14 14 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (14 2 (:REWRITE ACL2-NUMBERP-X))
     (4 4 (:REWRITE FOLD-CONSTS-IN-+))
     (4 4 (:REWRITE DEFAULT-MOD-2))
     (4 4 (:REWRITE DEFAULT-MOD-1))
     (4 4 (:REWRITE |(+ c (+ d x))|))
     (2 2 (:REWRITE REDUCE-RATIONALP-+))
     (2 2 (:REWRITE REDUCE-RATIONALP-*))
     (2 2 (:REWRITE RATIONALP-X))
     (2 2 (:REWRITE RATIONALP-MINUS-X))
     (2 2
        (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (2 2
        (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (2 2 (:REWRITE |(mod x 2)| . 2))
     (2 2 (:META META-RATIONALP-CORRECT)))
(RP::C-MERGE-3
     (1194 1194
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (1194 1194
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (1194 1194
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (403 75
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (403 75
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (340 68 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (340 68
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (340 68
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (239 75
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (239 75
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (239 75
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (239 75
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (239 75
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (239 75
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (210 18 (:REWRITE DEFAULT-MOD-RATIO))
     (210 18 (:REWRITE DEFAULT-FLOOR-RATIO))
     (204 68 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (204 68
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (204 68
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (204 68
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (204 68
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (160 160 (:REWRITE DEFAULT-TIMES-2))
     (160 160 (:REWRITE DEFAULT-TIMES-1))
     (90 90
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (75 75 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (75 75
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (75 75
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (63 63 (:REWRITE DEFAULT-PLUS-2))
     (63 63 (:REWRITE DEFAULT-PLUS-1))
     (34 34 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (34 34 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (31 1 (:REWRITE |(floor (+ x r) i)|))
     (22 22 (:REWRITE REDUCE-INTEGERP-+))
     (22 22 (:REWRITE INTEGERP-MINUS-X))
     (22 22
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (22 22 (:META META-INTEGERP-CORRECT))
     (18 18 (:REWRITE DEFAULT-MOD-2))
     (18 18 (:REWRITE DEFAULT-MOD-1))
     (18 18 (:REWRITE DEFAULT-FLOOR-2))
     (18 18 (:REWRITE DEFAULT-FLOOR-1))
     (13 13 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (13 13 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (13 13 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (13 13 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (12 12
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (12 12 (:REWRITE NORMALIZE-ADDENDS))
     (9 9 (:REWRITE |(mod x 2)| . 2))
     (9 9 (:REWRITE |(floor x 2)| . 2))
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
     (1 1 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (1 1 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
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
     (1 1 (:REWRITE |(< (* x y) 0)|)))
(RP::C-MERGE-3-SIDE-COND (45 45 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                         (45 45 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                         (45 45 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                         (26 26 (:REWRITE DEFAULT-TIMES-2))
                         (26 26 (:REWRITE DEFAULT-TIMES-1))
                         (13 13 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
                         (13 13 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                         (13 13 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                         (13 13 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                         (13 13 (:REWRITE DEFAULT-PLUS-2))
                         (13 13 (:REWRITE DEFAULT-PLUS-1))
                         (10 10 (:REWRITE REDUCE-INTEGERP-+))
                         (10 10
                             (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                         (10 10 (:REWRITE INTEGERP-MINUS-X))
                         (10 10
                             (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                         (10 10 (:META META-INTEGERP-CORRECT))
                         (2 2
                            (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                         (2 2 (:REWRITE NORMALIZE-ADDENDS)))
(RP::LESS-OR-EQ)
(RP::LESS-THAN)
(RP::NOT-NEGP)
(RP::MUL-LAST-BIT-SAVE-FROM-M2-1
     (648 10 (:REWRITE CANCEL-MOD-+))
     (469 293
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (350 294
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (310 17 (:REWRITE DEFAULT-MOD-RATIO))
     (299 15 (:REWRITE |(* (* x y) z)|))
     (294 294
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (294 294
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (293 293
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (293 293
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (256 184 (:REWRITE DEFAULT-TIMES-2))
     (246 184 (:REWRITE DEFAULT-TIMES-1))
     (196 20 (:REWRITE INTEGERP-MINUS-X))
     (174 31 (:REWRITE |(* y x)|))
     (138 24
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (138 24
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (133 23 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (128 8 (:REWRITE |(* y (* x z))|))
     (110 16 (:REWRITE MOD-X-Y-=-X . 4))
     (106 9
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (106 9
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (100 16 (:REWRITE MOD-ZERO . 4))
     (100 16 (:REWRITE MOD-ZERO . 3))
     (100 16 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (100 16 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (98 28 (:REWRITE |(* (- x) y)|))
     (97 97
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (90 16 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (90 16 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (88 48 (:REWRITE DEFAULT-PLUS-2))
     (84 48 (:REWRITE DEFAULT-PLUS-1))
     (70 10 (:REWRITE MOD-X-Y-=-X . 2))
     (70 10 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (70 10
         (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (60 8 (:REWRITE DEFAULT-MINUS))
     (59 5 (:REWRITE MOD-X-Y-=-X-Y . 1))
     (59 5 (:REWRITE MOD-X-Y-=-X+Y . 1))
     (54 8 (:REWRITE |(- (* c x))|))
     (44 4 (:REWRITE DEFAULT-FLOOR-RATIO))
     (41 23 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (30 4
         (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (30 4
         (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (27 17 (:REWRITE DEFAULT-MOD-1))
     (26 26
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (24 24 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (24 24
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (24 24
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (23 23 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (18 5
         (:REWRITE |(equal (mod (+ x y) z) x)|))
     (17 17 (:REWRITE DEFAULT-MOD-2))
     (16 16 (:REWRITE THE-FLOOR-BELOW))
     (16 16 (:REWRITE THE-FLOOR-ABOVE))
     (16 16 (:REWRITE DEFAULT-LESS-THAN-2))
     (14 14 (:REWRITE REDUCE-INTEGERP-+))
     (14 14
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (14 14 (:META META-INTEGERP-CORRECT))
     (14 2
         (:REWRITE |(not (equal (* (/ x) y) 1))|))
     (14 2 (:REWRITE |(equal (* (/ x) y) 1)|))
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
     (13 13 (:REWRITE |(< (- x) (- y))|))
     (11 11 (:REWRITE SIMPLIFY-SUMS-<))
     (11 11
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (11 11 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (11 11 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (11 11 (:REWRITE |(mod x 2)| . 2))
     (11 9
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
     (4 4 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (4 4
        (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (4 4 (:REWRITE DEFAULT-FLOOR-2))
     (4 4 (:REWRITE DEFAULT-FLOOR-1))
     (4 4 (:REWRITE ACL2-NUMBERP-X))
     (4 4
        (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (4 4 (:REWRITE |(mod x (- y))| . 3))
     (4 4 (:REWRITE |(mod x (- y))| . 2))
     (4 4 (:REWRITE |(mod x (- y))| . 1))
     (4 4
        (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (4 4
        (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (4 4 (:REWRITE |(mod (- x) y)| . 3))
     (4 4 (:REWRITE |(mod (- x) y)| . 2))
     (4 4 (:REWRITE |(mod (- x) y)| . 1))
     (4 4
        (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (4 4 (:REWRITE |(floor x 2)| . 2))
     (4 4 (:REWRITE |(equal (+ (- c) x) y)|))
     (4 4 (:REWRITE |(< (+ (- c) x) y)|))
     (2 2 (:TYPE-PRESCRIPTION ABS))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (2 2
        (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 3))
     (2 2
        (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 2))
     (2 2 (:REWRITE |(< (/ x) 0)|))
     (2 2 (:REWRITE |(< (* x y) 0)|))
     (2 2 (:DEFINITION MOD)))
(RP::MUL-LAST-BIT-SAVE-FROM-M2-1-SIDE-COND
     (139 139 (:TYPE-PRESCRIPTION NUMERATOR-ZERO))
     (139 139
          (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 2))
     (139 139
          (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 1))
     (122 1
          (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
     (100 100
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (100 100
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (92 12 (:REWRITE ACL2-NUMBERP-X))
     (71 7
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (40 8 (:REWRITE RATIONALP-X))
     (31 31 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (31 31 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (31 31 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (31 31 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (31 7
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (31 1 (:DEFINITION NFIX))
     (19 3 (:REWRITE INTEGERP==>NUMERATOR-=-X))
     (17 2 (:REWRITE O-INFP->NEQ-0))
     (17 1 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
     (14 14 (:REWRITE REDUCE-INTEGERP-+))
     (14 14 (:REWRITE INTEGERP-MINUS-X))
     (14 14
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (14 14 (:META META-INTEGERP-CORRECT))
     (12 12
         (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (10 6
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (10 5 (:REWRITE SIMPLIFY-SUMS-<))
     (10 5
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (10 5 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (10 1 (:REWRITE |(+ y x)|))
     (9 3 (:REWRITE DEFAULT-PLUS-2))
     (8 8 (:REWRITE THE-FLOOR-BELOW))
     (8 8 (:REWRITE THE-FLOOR-ABOVE))
     (8 8 (:REWRITE REDUCE-RATIONALP-+))
     (8 8 (:REWRITE REDUCE-RATIONALP-*))
     (8 8
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (8 8
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (8 8 (:REWRITE RATIONALP-MINUS-X))
     (8 8
        (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (8 8 (:REWRITE DEFAULT-LESS-THAN-2))
     (8 8 (:REWRITE |(equal c (/ x))|))
     (8 8 (:REWRITE |(equal c (- x))|))
     (8 8 (:REWRITE |(equal (/ x) c)|))
     (8 8 (:REWRITE |(equal (/ x) (/ y))|))
     (8 8 (:REWRITE |(equal (- x) c)|))
     (8 8 (:REWRITE |(equal (- x) (- y))|))
     (8 8 (:META META-RATIONALP-CORRECT))
     (8 3 (:REWRITE DEFAULT-PLUS-1))
     (8 1
        (:LINEAR NUMERATOR-GOES-DOWN-BY-INTEGER-DIVISION-LINEAR
                 . 1))
     (7 7 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (7 7
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (7 6
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (7 6
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (7 3 (:REWRITE DEFAULT-RATIONAL-NUMERATOR))
     (6 6 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (6 6 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (6 6 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (6 6 (:REWRITE INTEGERP-<-CONSTANT))
     (6 6 (:REWRITE DEFAULT-TIMES-2))
     (6 6 (:REWRITE DEFAULT-TIMES-1))
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
     (6 1 (:DEFINITION IFIX))
     (5 1
        (:REWRITE DEFAULT-RATIONAL-DENOMINATOR))
     (4 4 (:REWRITE |(< (/ x) 0)|))
     (4 4 (:REWRITE |(< (* x y) 0)|))
     (3 3 (:TYPE-PRESCRIPTION O-FINP))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (3 3
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (3 1 (:REWRITE O-FIRST-EXPT-O-INFP))
     (2 2 (:TYPE-PRESCRIPTION ABS))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (2 2
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (2 2 (:REWRITE NORMALIZE-ADDENDS))
     (2 1 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
     (1 1 (:REWRITE DEFAULT-MINUS))
     (1 1
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (1 1
        (:LINEAR NUMERATOR-GOES-DOWN-BY-INTEGER-DIVISION-LINEAR
                 . 3)))
(RP::MUL-LAST-BIT-SAVE-FROM-M2-2
     (352 8 (:REWRITE DEFAULT-MOD-RATIO))
     (332 332
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (332 332
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (332 332
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (245 36 (:REWRITE DEFAULT-TIMES-2))
     (234 3 (:LINEAR MOD-BOUNDS-3))
     (185 37 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (185 37 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (185 37
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (185 37
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (166 166 (:TYPE-PRESCRIPTION NUMERATOR-ZERO))
     (166 166
          (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 2))
     (166 166
          (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 1))
     (166 166
          (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 2))
     (166 166
          (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 1))
     (157 36 (:REWRITE DEFAULT-TIMES-1))
     (96 8 (:REWRITE DEFAULT-MOD-1))
     (96 6 (:LINEAR MOD-BOUNDS-2))
     (60 60 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (60 60 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (60 60 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (37 37 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (37 37
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (37 37 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (37 37
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (37 37 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (21 21
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (13 13 (:REWRITE REDUCE-INTEGERP-+))
     (13 13 (:REWRITE INTEGERP-MINUS-X))
     (13 13
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (13 13 (:META META-INTEGERP-CORRECT))
     (12 1 (:REWRITE DEFAULT-PLUS-2))
     (8 8 (:REWRITE DEFAULT-MOD-2))
     (8 8 (:REWRITE |(mod x 2)| . 2))
     (1 1 (:REWRITE DEFAULT-PLUS-1)))
(RP::MUL-LAST-BIT-SAVE-FROM-M2-OLD
     (648 10 (:REWRITE CANCEL-MOD-+))
     (481 305
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (352 296
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (310 17 (:REWRITE DEFAULT-MOD-RATIO))
     (305 305
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (305 305
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (299 15 (:REWRITE |(* (* x y) z)|))
     (296 296
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (296 296
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (256 184 (:REWRITE DEFAULT-TIMES-2))
     (246 184 (:REWRITE DEFAULT-TIMES-1))
     (196 20 (:REWRITE INTEGERP-MINUS-X))
     (174 31 (:REWRITE |(* y x)|))
     (155 27
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (155 27
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (150 26 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (128 8 (:REWRITE |(* y (* x z))|))
     (110 16 (:REWRITE MOD-X-Y-=-X . 4))
     (106 9
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (106 9
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (100 16 (:REWRITE MOD-ZERO . 4))
     (100 16 (:REWRITE MOD-ZERO . 3))
     (100 16 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (100 16 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (98 28 (:REWRITE |(* (- x) y)|))
     (97 97
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (90 16 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (90 16 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (88 48 (:REWRITE DEFAULT-PLUS-2))
     (84 48 (:REWRITE DEFAULT-PLUS-1))
     (70 10 (:REWRITE MOD-X-Y-=-X . 2))
     (70 10 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (70 10
         (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (60 8 (:REWRITE DEFAULT-MINUS))
     (59 5 (:REWRITE MOD-X-Y-=-X-Y . 1))
     (59 5 (:REWRITE MOD-X-Y-=-X+Y . 1))
     (54 8 (:REWRITE |(- (* c x))|))
     (46 26 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (44 4 (:REWRITE DEFAULT-FLOOR-RATIO))
     (30 4
         (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (30 4
         (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (27 27 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (27 27
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (27 27
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (27 17 (:REWRITE DEFAULT-MOD-1))
     (26 26 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (26 26
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (18 5
         (:REWRITE |(equal (mod (+ x y) z) x)|))
     (17 17 (:REWRITE DEFAULT-MOD-2))
     (16 16 (:REWRITE THE-FLOOR-BELOW))
     (16 16 (:REWRITE THE-FLOOR-ABOVE))
     (16 16 (:REWRITE DEFAULT-LESS-THAN-2))
     (14 14 (:REWRITE REDUCE-INTEGERP-+))
     (14 14
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (14 14 (:META META-INTEGERP-CORRECT))
     (14 2
         (:REWRITE |(not (equal (* (/ x) y) 1))|))
     (14 2 (:REWRITE |(equal (* (/ x) y) 1)|))
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
     (13 13 (:REWRITE |(< (- x) (- y))|))
     (11 11 (:REWRITE SIMPLIFY-SUMS-<))
     (11 11
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (11 11 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (11 11 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (11 11 (:REWRITE |(mod x 2)| . 2))
     (11 9
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
     (4 4 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (4 4
        (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (4 4 (:REWRITE DEFAULT-FLOOR-2))
     (4 4 (:REWRITE DEFAULT-FLOOR-1))
     (4 4 (:REWRITE ACL2-NUMBERP-X))
     (4 4
        (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (4 4 (:REWRITE |(mod x (- y))| . 3))
     (4 4 (:REWRITE |(mod x (- y))| . 2))
     (4 4 (:REWRITE |(mod x (- y))| . 1))
     (4 4
        (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (4 4
        (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (4 4 (:REWRITE |(mod (- x) y)| . 3))
     (4 4 (:REWRITE |(mod (- x) y)| . 2))
     (4 4 (:REWRITE |(mod (- x) y)| . 1))
     (4 4
        (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (4 4 (:REWRITE |(floor x 2)| . 2))
     (4 4 (:REWRITE |(equal (+ (- c) x) y)|))
     (4 4 (:REWRITE |(< (+ (- c) x) y)|))
     (2 2 (:TYPE-PRESCRIPTION ABS))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (2 2
        (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 3))
     (2 2
        (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 2))
     (2 2 (:REWRITE |(< (/ x) 0)|))
     (2 2 (:REWRITE |(< (* x y) 0)|))
     (2 2 (:DEFINITION MOD)))
(RP::MOD-MOD-2 (625 125 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
               (625 125 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
               (625 125
                    (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
               (625 125
                    (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
               (575 575
                    (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
               (575 575
                    (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
               (575 575
                    (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
               (491 12 (:REWRITE DEFAULT-MOD-RATIO))
               (349 3 (:LINEAR MOD-BOUNDS-3))
               (319 39 (:REWRITE DEFAULT-TIMES-2))
               (220 13 (:REWRITE |(* y x)|))
               (219 39 (:REWRITE DEFAULT-TIMES-1))
               (142 6 (:LINEAR MOD-BOUNDS-2))
               (132 12 (:REWRITE DEFAULT-MOD-1))
               (125 125 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
               (125 125
                    (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
               (125 125
                    (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
               (125 125
                    (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
               (125 125 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
               (52 52 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
               (52 52 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
               (52 52 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
               (31 5 (:REWRITE |(* (if a b c) x)|))
               (21 21
                   (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
               (13 13 (:REWRITE REDUCE-INTEGERP-+))
               (13 13 (:REWRITE INTEGERP-MINUS-X))
               (13 13
                   (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
               (13 13 (:META META-INTEGERP-CORRECT))
               (12 12 (:REWRITE DEFAULT-MOD-2))
               (8 8 (:REWRITE |(mod x 2)| . 2)))
(RP::TYPE-FIX-OF-M2 (201 201
                         (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                    (201 201
                         (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                    (201 201
                         (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                    (185 37 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
                    (185 37 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
                    (185 37
                         (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
                    (185 37
                         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
                    (72 6 (:REWRITE DEFAULT-MOD-RATIO))
                    (37 37 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
                    (37 37
                        (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
                    (37 37 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
                    (37 37
                        (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
                    (37 37 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
                    (28 7 (:REWRITE |(* y x)|))
                    (23 1 (:LINEAR MOD-BOUNDS-3))
                    (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                    (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                    (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                    (20 20 (:REWRITE DEFAULT-TIMES-2))
                    (20 20 (:REWRITE DEFAULT-TIMES-1))
                    (14 2 (:REWRITE |(* (if a b c) x)|))
                    (11 11
                        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                    (10 2 (:LINEAR MOD-BOUNDS-2))
                    (7 7 (:REWRITE REDUCE-INTEGERP-+))
                    (7 7 (:REWRITE INTEGERP-MINUS-X))
                    (7 7
                       (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                    (7 7 (:META META-INTEGERP-CORRECT))
                    (6 6 (:REWRITE DEFAULT-MOD-2))
                    (6 6 (:REWRITE DEFAULT-MOD-1))
                    (4 4 (:REWRITE |(mod x 2)| . 2)))
(RP::S-OF-S (116 106
                 (:REWRITE |(mod (+ x (mod a b)) y)|))
            (26 26 (:REWRITE NORMALIZE-ADDENDS)))
(RP::F2-OF-SINGLE-PP (64 5
                         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                     (56 1 (:REWRITE RP::BIT-FIX-OPENER))
                     (48 8 (:REWRITE ACL2-NUMBERP-X))
                     (24 5
                         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                     (20 4 (:REWRITE RATIONALP-X))
                     (18 2 (:REWRITE O-INFP->NEQ-0))
                     (15 15 (:TYPE-PRESCRIPTION NUMERATOR-ZERO))
                     (15 15
                         (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 2))
                     (15 15
                         (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 1))
                     (15 15
                         (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 2))
                     (15 15
                         (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 1))
                     (11 11 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                     (11 11 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                     (11 11 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                     (8 8
                        (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
                     (5 5 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                     (5 5
                        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                     (5 5 (:REWRITE REDUCE-INTEGERP-+))
                     (5 5
                        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
                     (5 5 (:REWRITE INTEGERP-MINUS-X))
                     (5 5
                        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                     (5 5
                        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
                     (5 5 (:REWRITE |(equal c (/ x))|))
                     (5 5 (:REWRITE |(equal c (- x))|))
                     (5 5 (:REWRITE |(equal (/ x) c)|))
                     (5 5 (:REWRITE |(equal (/ x) (/ y))|))
                     (5 5 (:REWRITE |(equal (- x) c)|))
                     (5 5 (:REWRITE |(equal (- x) (- y))|))
                     (5 5 (:META META-INTEGERP-CORRECT))
                     (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                     (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                     (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                     (4 4 (:REWRITE REDUCE-RATIONALP-+))
                     (4 4 (:REWRITE REDUCE-RATIONALP-*))
                     (4 4 (:REWRITE RATIONALP-MINUS-X))
                     (4 4
                        (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
                     (4 4 (:META META-RATIONALP-CORRECT))
                     (3 3 (:TYPE-PRESCRIPTION O-FINP))
                     (3 3
                        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
                     (3 1 (:REWRITE O-FIRST-EXPT-O-INFP))
                     (2 2 (:REWRITE DEFAULT-TIMES-2))
                     (2 2 (:REWRITE DEFAULT-TIMES-1))
                     (2 1 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
                     (1 1 (:TYPE-PRESCRIPTION BITP))
                     (1 1
                        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                     (1 1 (:REWRITE DEFAULT-PLUS-2))
                     (1 1 (:REWRITE DEFAULT-PLUS-1)))
(RP::F2-OF-SINGLE-BITP
     (26 2
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (24 4 (:REWRITE ACL2-NUMBERP-X))
     (14 14 (:TYPE-PRESCRIPTION NUMERATOR-ZERO))
     (14 14
         (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 2))
     (14 14
         (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 1))
     (14 14
         (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 2))
     (14 14
         (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 1))
     (14 14 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (14 14 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (10 2 (:REWRITE RATIONALP-X))
     (6 2
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (6 1 (:REWRITE O-INFP->NEQ-0))
     (4 4
        (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (3 3 (:TYPE-PRESCRIPTION O-FINP))
     (3 1 (:REWRITE O-FIRST-EXPT-O-INFP))
     (2 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (2 2 (:REWRITE REDUCE-RATIONALP-+))
     (2 2 (:REWRITE REDUCE-RATIONALP-*))
     (2 2
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (2 2 (:REWRITE REDUCE-INTEGERP-+))
     (2 2
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (2 2 (:REWRITE RATIONALP-MINUS-X))
     (2 2
        (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (2 2 (:REWRITE INTEGERP-MINUS-X))
     (2 2
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (2 2
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (2 2 (:REWRITE |(equal c (/ x))|))
     (2 2 (:REWRITE |(equal c (- x))|))
     (2 2 (:REWRITE |(equal (/ x) c)|))
     (2 2 (:REWRITE |(equal (/ x) (/ y))|))
     (2 2 (:REWRITE |(equal (- x) c)|))
     (2 2 (:REWRITE |(equal (- x) (- y))|))
     (2 2 (:META META-RATIONALP-CORRECT))
     (2 2 (:META META-INTEGERP-CORRECT))
     (2 1 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RP::B+-0 (20 20 (:REWRITE DEFAULT-PLUS-2))
          (20 20 (:REWRITE DEFAULT-PLUS-1))
          (4 4 (:REWRITE REDUCE-INTEGERP-+))
          (4 4 (:REWRITE INTEGERP-MINUS-X))
          (4 4
             (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
          (4 4 (:META META-INTEGERP-CORRECT))
          (2 2
             (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
          (2 2 (:REWRITE NORMALIZE-ADDENDS)))
(RP::B+-0-2 (16 16 (:REWRITE DEFAULT-PLUS-2))
            (16 16 (:REWRITE DEFAULT-PLUS-1))
            (4 4 (:REWRITE REDUCE-INTEGERP-+))
            (4 4 (:REWRITE INTEGERP-MINUS-X))
            (4 4
               (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
            (4 4 (:META META-INTEGERP-CORRECT))
            (2 2
               (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
            (2 2 (:REWRITE NORMALIZE-ADDENDS)))
(RP::B+-0-PP-SUM (20 20 (:REWRITE DEFAULT-PLUS-2))
                 (20 20 (:REWRITE DEFAULT-PLUS-1))
                 (4 4 (:REWRITE REDUCE-INTEGERP-+))
                 (4 4 (:REWRITE INTEGERP-MINUS-X))
                 (4 4
                    (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                 (4 4 (:META META-INTEGERP-CORRECT))
                 (2 2
                    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                 (2 2 (:REWRITE NORMALIZE-ADDENDS)))
(RP::B+-0-3 (3 3 (:TYPE-PRESCRIPTION RP::TYPE-FIX)))
(RP::B+-0-TYPE-FIX-1 (3 3 (:TYPE-PRESCRIPTION RP::TYPE-FIX)))
(RP::B+-NIL-2 (3 3 (:TYPE-PRESCRIPTION RP::TYPE-FIX)))
(RP::B+-NIL-3 (3 3 (:TYPE-PRESCRIPTION RP::TYPE-FIX)))
(RP::TYPE-FIX-SUM (14 14 (:REWRITE DEFAULT-PLUS-2))
                  (14 14 (:REWRITE DEFAULT-PLUS-1))
                  (4 4 (:REWRITE REDUCE-INTEGERP-+))
                  (4 4 (:REWRITE INTEGERP-MINUS-X))
                  (4 4
                     (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                  (4 4 (:META META-INTEGERP-CORRECT))
                  (2 2
                     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                  (2 2 (:REWRITE NORMALIZE-ADDENDS)))
(RP::TYPE-FIX-PP-SUM (14 14 (:REWRITE DEFAULT-PLUS-2))
                     (14 14 (:REWRITE DEFAULT-PLUS-1))
                     (4 4 (:REWRITE REDUCE-INTEGERP-+))
                     (4 4 (:REWRITE INTEGERP-MINUS-X))
                     (4 4
                        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                     (4 4 (:META META-INTEGERP-CORRECT))
                     (2 2
                        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                     (2 2 (:REWRITE NORMALIZE-ADDENDS)))
(RP::SUM-TYPE-FIX-1)
(RP::SUM-TYPE-FIX-2)
(RP::M2-TYPE-FIX (75 15 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
                 (75 15 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
                 (75 15
                     (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
                 (75 15
                     (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
                 (72 72 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                 (72 72 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                 (72 72 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                 (15 15 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
                 (15 15
                     (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
                 (15 15 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
                 (15 15
                     (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
                 (15 15 (:TYPE-PRESCRIPTION INTEGERP-MOD-2)))
(RP::F2-TYPE-FIX (14 14 (:TYPE-PRESCRIPTION NUMERATOR-ZERO))
                 (14 14
                     (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 2))
                 (14 14
                     (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 1))
                 (14 14
                     (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 2))
                 (14 14
                     (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 1))
                 (14 14 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                 (14 14 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                 (14 14
                     (:TYPE-PRESCRIPTION NOT-INTEGERP-1B)))
(RP::TYPE-FIX-OF-F2 (35 35 (:TYPE-PRESCRIPTION NUMERATOR-ZERO))
                    (35 35
                        (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 2))
                    (35 35
                        (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 1))
                    (35 35
                        (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 2))
                    (35 35
                        (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 1))
                    (34 34 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                    (34 34 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                    (34 34 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                    (6 6 (:REWRITE DEFAULT-TIMES-2))
                    (6 6 (:REWRITE DEFAULT-TIMES-1))
                    (2 2 (:REWRITE REDUCE-INTEGERP-+))
                    (2 2
                       (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                    (2 2 (:REWRITE INTEGERP-MINUS-X))
                    (2 2
                       (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                    (2 2 (:META META-INTEGERP-CORRECT))
                    (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
                    (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                    (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                    (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A)))
(RP::D2-TYPE-FIX (141 141
                      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                 (141 141
                      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                 (141 141
                      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                 (70 14 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
                 (70 14 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
                 (70 14
                     (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
                 (70 14
                     (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
                 (14 14 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
                 (14 14
                     (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
                 (14 14 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
                 (14 14
                     (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
                 (14 14 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
                 (13 13 (:TYPE-PRESCRIPTION NUMERATOR-ZERO))
                 (13 13
                     (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 2))
                 (13 13
                     (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 1))
                 (13 13
                     (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 2))
                 (13 13
                     (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 1)))
(RP::M2-OF-MINUS-M2-LEMMA1)
(RP::M2-OF-MINUS-M2 (2356 12
                          (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
                    (1730 24 (:REWRITE NIQ-TYPE . 3))
                    (921 921 (:TYPE-PRESCRIPTION MOD-TYPE . 3))
                    (921 921 (:TYPE-PRESCRIPTION MOD-TYPE . 2))
                    (921 921 (:TYPE-PRESCRIPTION MOD-TYPE . 1))
                    (632 24 (:REWRITE NIQ-TYPE . 2))
                    (466 124 (:REWRITE DEFAULT-*-1))
                    (438 13 (:REWRITE DISTRIBUTIVITY))
                    (426 124 (:REWRITE DEFAULT-*-2))
                    (314 79 (:REWRITE DEFAULT-+-2))
                    (310 110 (:REWRITE DEFAULT-<-2))
                    (290 110 (:REWRITE DEFAULT-<-1))
                    (250 79 (:REWRITE DEFAULT-+-1))
                    (206 13 (:REWRITE RP::STUPID-LEMMA1))
                    (184 24 (:REWRITE DEFAULT-UNARY-/))
                    (176 33 (:REWRITE DEFAULT-UNARY-MINUS))
                    (169 9 (:REWRITE MOD-=-0 . 2))
                    (156 12 (:DEFINITION NFIX))
                    (125 9
                         (:REWRITE MOD-X-Y-=-X-FOR-RATIONALS . 3))
                    (125 9
                         (:REWRITE MOD-X-Y-=-X-FOR-RATIONALS . 2))
                    (125 9
                         (:REWRITE MOD-X-Y-=-X+Y-FOR-RATIONALS . 3))
                    (125 9
                         (:REWRITE MOD-X-Y-=-X+Y-FOR-RATIONALS . 2))
                    (118 6 (:REWRITE FLOOR-TYPE-4 . 3))
                    (118 6 (:REWRITE FLOOR-TYPE-4 . 2))
                    (118 6 (:REWRITE FLOOR-TYPE-3 . 3))
                    (118 6 (:REWRITE FLOOR-TYPE-3 . 2))
                    (72 6 (:REWRITE INTEGERP==>NUMERATOR-=-X))
                    (72 6 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
                    (71 3 (:LINEAR MOD-TYPE . 2))
                    (66 66
                        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                    (52 12 (:REWRITE RATIONAL-IMPLIES2))
                    (26 6 (:REWRITE DEFAULT-NUMERATOR))
                    (26 6 (:REWRITE DEFAULT-DENOMINATOR))
                    (16 4 (:REWRITE CANCEL-MOD-+-BASIC))
                    (12 12 (:DEFINITION IFIX))
                    (3 3 (:LINEAR MOD-TYPE . 3))
                    (3 3 (:LINEAR MOD-TYPE . 1)))
(RP::MINUS-BA+ (15 15 (:REWRITE DEFAULT-PLUS-2))
               (15 15 (:REWRITE DEFAULT-PLUS-1))
               (12 12 (:REWRITE DEFAULT-MINUS))
               (4 4 (:REWRITE REDUCE-INTEGERP-+))
               (4 4 (:REWRITE INTEGERP-MINUS-X))
               (4 4
                  (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
               (4 4 (:META META-INTEGERP-CORRECT))
               (3 3
                  (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
               (3 3 (:REWRITE NORMALIZE-ADDENDS)))
(RP::MINUS-B+ (15 15 (:REWRITE DEFAULT-PLUS-2))
              (15 15 (:REWRITE DEFAULT-PLUS-1))
              (12 12 (:REWRITE DEFAULT-MINUS))
              (4 4 (:REWRITE REDUCE-INTEGERP-+))
              (4 4 (:REWRITE INTEGERP-MINUS-X))
              (4 4
                 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
              (4 4 (:META META-INTEGERP-CORRECT))
              (3 3
                 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
              (3 3 (:REWRITE NORMALIZE-ADDENDS)))
(RP::B+-A-MINUS-A-0 (22 20 (:REWRITE DEFAULT-PLUS-1))
                    (20 20 (:REWRITE DEFAULT-PLUS-2))
                    (4 4 (:REWRITE REDUCE-INTEGERP-+))
                    (4 4 (:REWRITE INTEGERP-MINUS-X))
                    (4 4
                       (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                    (4 4 (:META META-INTEGERP-CORRECT))
                    (3 3 (:TYPE-PRESCRIPTION RP::TYPE-FIX))
                    (2 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
                    (2 2 (:REWRITE DEFAULT-MINUS))
                    (1 1
                       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                    (1 1 (:REWRITE |(+ c (+ d x))|)))
(RP::B+-A-MINUS-A-1 (63 59 (:REWRITE DEFAULT-PLUS-1))
                    (59 59 (:REWRITE DEFAULT-PLUS-2))
                    (6 6 (:REWRITE REDUCE-INTEGERP-+))
                    (6 6
                       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                    (6 6 (:REWRITE INTEGERP-MINUS-X))
                    (6 6
                       (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                    (6 6 (:META META-INTEGERP-CORRECT))
                    (4 4 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
                    (4 4 (:REWRITE |(+ c (+ d x))|))
                    (2 2 (:REWRITE DEFAULT-MINUS))
                    (1 1 (:REWRITE FOLD-CONSTS-IN-+)))
(RP::B+-A-MINUS-A-2 (25 23 (:REWRITE DEFAULT-PLUS-1))
                    (23 23 (:REWRITE DEFAULT-PLUS-2))
                    (4 4 (:REWRITE REDUCE-INTEGERP-+))
                    (4 4 (:REWRITE INTEGERP-MINUS-X))
                    (4 4
                       (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                    (4 4 (:META META-INTEGERP-CORRECT))
                    (3 3 (:TYPE-PRESCRIPTION RP::TYPE-FIX))
                    (2 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
                    (2 2
                       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                    (2 2 (:REWRITE DEFAULT-MINUS))
                    (1 1 (:REWRITE |(+ c (+ d x))|)))
(RP::B+-A-MINUS-A-3 (70 66 (:REWRITE DEFAULT-PLUS-1))
                    (66 66 (:REWRITE DEFAULT-PLUS-2))
                    (9 9
                       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                    (6 6 (:REWRITE REDUCE-INTEGERP-+))
                    (6 6 (:REWRITE INTEGERP-MINUS-X))
                    (6 6
                       (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                    (6 6 (:META META-INTEGERP-CORRECT))
                    (5 5 (:REWRITE |(+ c (+ d x))|))
                    (4 4 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
                    (2 2 (:REWRITE FOLD-CONSTS-IN-+))
                    (2 2 (:REWRITE DEFAULT-MINUS)))
(RP::BA+-BA-0 (24 22 (:REWRITE DEFAULT-PLUS-1))
              (22 22 (:REWRITE DEFAULT-PLUS-2))
              (4 4 (:REWRITE REDUCE-INTEGERP-+))
              (4 4 (:REWRITE INTEGERP-MINUS-X))
              (4 4
                 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
              (4 4 (:META META-INTEGERP-CORRECT))
              (2 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
              (2 2 (:REWRITE DEFAULT-MINUS))
              (1 1
                 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
              (1 1 (:REWRITE |(+ c (+ d x))|)))
(RP::BA+-BA-1 (27 25 (:REWRITE DEFAULT-PLUS-1))
              (25 25 (:REWRITE DEFAULT-PLUS-2))
              (4 4 (:REWRITE REDUCE-INTEGERP-+))
              (4 4 (:REWRITE INTEGERP-MINUS-X))
              (4 4
                 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
              (4 4 (:META META-INTEGERP-CORRECT))
              (2 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
              (2 2
                 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
              (2 2 (:REWRITE DEFAULT-MINUS))
              (1 1 (:REWRITE |(+ c (+ d x))|)))
(RP::BA+-BA-2 (7 6 (:REWRITE DEFAULT-PLUS-1))
              (6 6 (:REWRITE DEFAULT-PLUS-2))
              (2 2 (:REWRITE REDUCE-INTEGERP-+))
              (2 2 (:REWRITE INTEGERP-MINUS-X))
              (2 2
                 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
              (2 2 (:REWRITE DEFAULT-MINUS))
              (2 2 (:META META-INTEGERP-CORRECT))
              (1 1 (:TYPE-PRESCRIPTION BUBBLE-DOWN)))
(RP::A+-A-END-1 (6 5 (:REWRITE DEFAULT-PLUS-1))
                (5 5 (:REWRITE DEFAULT-PLUS-2))
                (2 2 (:REWRITE REDUCE-INTEGERP-+))
                (2 2 (:REWRITE INTEGERP-MINUS-X))
                (2 2
                   (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                (2 2 (:REWRITE DEFAULT-MINUS))
                (2 2 (:META META-INTEGERP-CORRECT))
                (1 1 (:TYPE-PRESCRIPTION BUBBLE-DOWN)))
(RP::A+-A-END-2 (7 6 (:REWRITE DEFAULT-PLUS-1))
                (6 6 (:REWRITE DEFAULT-PLUS-2))
                (2 2 (:REWRITE REDUCE-INTEGERP-+))
                (2 2 (:REWRITE INTEGERP-MINUS-X))
                (2 2
                   (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                (2 2 (:REWRITE DEFAULT-MINUS))
                (2 2 (:META META-INTEGERP-CORRECT))
                (1 1 (:TYPE-PRESCRIPTION BUBBLE-DOWN)))
(RP::BINARYP-NATP)
(RP::F2-OF-TIMES2
     (250 8 (:REWRITE DEFAULT-FLOOR-RATIO))
     (140 11 (:REWRITE |(* y x)|))
     (139 91 (:REWRITE DEFAULT-TIMES-2))
     (136 6 (:REWRITE |(* (if a b c) x)|))
     (124 124
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (124 124
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (124 124
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (124 124
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (103 52 (:REWRITE DEFAULT-PLUS-2))
     (91 91 (:REWRITE DEFAULT-TIMES-1))
     (70 52 (:REWRITE DEFAULT-PLUS-1))
     (52 1 (:REWRITE |(floor (+ x r) i)|))
     (48 48
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (45 2
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (42 3 (:REWRITE |(* (* x y) z)|))
     (26 26 (:REWRITE INTEGERP-MINUS-X))
     (25 25
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (25 25 (:META META-INTEGERP-CORRECT))
     (23 23
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (18 6
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (18 6
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (16 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (8 8 (:REWRITE DEFAULT-FLOOR-2))
     (8 8 (:REWRITE DEFAULT-FLOOR-1))
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
     (4 4 (:REWRITE |(floor x 2)| . 2))
     (4 4 (:REWRITE |(+ c (+ d x))|))
     (3 3 (:REWRITE FOLD-CONSTS-IN-+))
     (3 3 (:REWRITE |(equal (+ (- c) x) y)|))
     (3 1 (:REWRITE O-INFP->NEQ-0))
     (2 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (2 2 (:REWRITE THE-FLOOR-BELOW))
     (2 2 (:REWRITE THE-FLOOR-ABOVE))
     (2 2 (:REWRITE DEFAULT-LESS-THAN-2))
     (2 2 (:REWRITE DEFAULT-LESS-THAN-1))
     (2 2 (:REWRITE |(< (* x y) 0)|))
     (1 1 (:TYPE-PRESCRIPTION ABS))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
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
     (1 1 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (1 1 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (1 1 (:REWRITE INTEGERP-<-CONSTANT))
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
     (1 1
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|)))
(RP::F2-OF-MINUS-LEMMA1 (42 38 (:REWRITE DEFAULT-PLUS-1))
                        (38 38 (:REWRITE DEFAULT-PLUS-2))
                        (9 9 (:REWRITE DEFAULT-MINUS))
                        (6 6 (:REWRITE REDUCE-INTEGERP-+))
                        (6 6 (:REWRITE INTEGERP-MINUS-X))
                        (6 6
                           (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                        (6 6 (:META META-INTEGERP-CORRECT))
                        (5 5 (:REWRITE DEFAULT-TIMES-2))
                        (5 5 (:REWRITE DEFAULT-TIMES-1))
                        (4 4 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
                        (4 4
                           (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                        (3 3 (:REWRITE |(* (- x) y)|))
                        (2 2
                           (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                        (1 1 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
                        (1 1 (:REWRITE |(+ c (+ d x))|)))
(RP::F2-OF-MINUS)
(RP::S-OF-TIMES2 (316 14 (:REWRITE DEFAULT-MOD-RATIO))
                 (187 187
                      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                 (187 187
                      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                 (187 187
                      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                 (185 37 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
                 (185 37 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
                 (185 37
                      (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
                 (185 37
                      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
                 (176 20 (:REWRITE |(* y x)|))
                 (136 6 (:REWRITE |(* (if a b c) x)|))
                 (113 81 (:REWRITE DEFAULT-TIMES-2))
                 (81 81 (:REWRITE DEFAULT-TIMES-1))
                 (71 71 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                 (71 71 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                 (71 71 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                 (69 3 (:LINEAR MOD-BOUNDS-3))
                 (62 26 (:REWRITE DEFAULT-PLUS-2))
                 (44 26 (:REWRITE DEFAULT-PLUS-1))
                 (42 3 (:REWRITE |(* (* x y) z)|))
                 (39 39
                     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                 (37 37 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
                 (37 37
                     (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
                 (37 37 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
                 (37 37
                     (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
                 (37 37 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
                 (30 6 (:LINEAR MOD-BOUNDS-2))
                 (17 17 (:REWRITE INTEGERP-MINUS-X))
                 (16 16
                     (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                 (16 16 (:META META-INTEGERP-CORRECT))
                 (14 14 (:REWRITE DEFAULT-MOD-2))
                 (14 14 (:REWRITE DEFAULT-MOD-1))
                 (10 10 (:REWRITE |(mod x 2)| . 2))
                 (6 6
                    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                 (2 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
                 (1 1 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
                 (1 1 (:REWRITE |(+ c (+ d x))|)))
(RP::S-OF-MINUS-LEMMA (42 38 (:REWRITE DEFAULT-PLUS-1))
                      (38 38 (:REWRITE DEFAULT-PLUS-2))
                      (9 9 (:REWRITE DEFAULT-MINUS))
                      (6 6 (:REWRITE REDUCE-INTEGERP-+))
                      (6 6 (:REWRITE INTEGERP-MINUS-X))
                      (6 6
                         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                      (6 6 (:META META-INTEGERP-CORRECT))
                      (5 5 (:REWRITE DEFAULT-TIMES-2))
                      (5 5 (:REWRITE DEFAULT-TIMES-1))
                      (4 4 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
                      (4 4
                         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                      (3 3 (:REWRITE |(* (- x) y)|))
                      (2 2
                         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                      (1 1 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
                      (1 1 (:REWRITE |(+ c (+ d x))|)))
(RP::S-OF-MINUS)
(RP::PP-RANGE)
(RP::AND$-RANGE)
(RP::B+-PP-SUM-RANGE-1
     (224 4 (:REWRITE RP::BIT-FIX-OPENER))
     (208 16
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (192 32 (:REWRITE ACL2-NUMBERP-X))
     (85 17 (:REWRITE RATIONALP-X))
     (48 16
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (32 32
         (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (28 28 (:REWRITE DEFAULT-PLUS-2))
     (28 28 (:REWRITE DEFAULT-PLUS-1))
     (24 4 (:REWRITE O-INFP->NEQ-0))
     (23 23 (:REWRITE REDUCE-INTEGERP-+))
     (23 23 (:REWRITE INTEGERP-MINUS-X))
     (23 23
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (23 23 (:META META-INTEGERP-CORRECT))
     (17 17 (:REWRITE REDUCE-RATIONALP-+))
     (17 17 (:REWRITE REDUCE-RATIONALP-*))
     (17 17 (:REWRITE RATIONALP-MINUS-X))
     (17 17
         (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (17 17 (:META META-RATIONALP-CORRECT))
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
     (12 12 (:TYPE-PRESCRIPTION O-FINP))
     (12 4 (:REWRITE O-FIRST-EXPT-O-INFP))
     (11 11 (:REWRITE THE-FLOOR-BELOW))
     (11 11 (:REWRITE THE-FLOOR-ABOVE))
     (11 11 (:REWRITE DEFAULT-LESS-THAN-2))
     (11 11 (:REWRITE DEFAULT-LESS-THAN-1))
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (8 8 (:REWRITE SIMPLIFY-SUMS-<))
     (8 8
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (8 8 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (8 8 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (8 8
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (8 8
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (8 8 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (8 8 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (8 8
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (8 8 (:REWRITE NORMALIZE-ADDENDS))
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
     (8 4 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
     (4 4 (:TYPE-PRESCRIPTION BITP))
     (4 4 (:REWRITE |(< y (+ (- c) x))|))
     (4 4 (:REWRITE |(< x (+ c/d y))|))
     (4 4 (:REWRITE |(< (+ c/d x) y)|))
     (4 4 (:REWRITE |(< (+ (- c) x) y)|))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (1 1 (:REWRITE FOLD-CONSTS-IN-+))
     (1 1 (:REWRITE |(< 0 (/ x))|))
     (1 1 (:REWRITE |(< 0 (* x y))|))
     (1 1 (:REWRITE |(+ c (+ d x))|)))
(RP::B+-PP-SUM-RANGE-1-AND$
     (41 31 (:REWRITE DEFAULT-PLUS-2))
     (41 31 (:REWRITE DEFAULT-PLUS-1))
     (15 11 (:REWRITE DEFAULT-LESS-THAN-1))
     (12 8 (:REWRITE SIMPLIFY-SUMS-<))
     (12 8
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (12 8 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (11 11 (:REWRITE THE-FLOOR-BELOW))
     (11 11 (:REWRITE THE-FLOOR-ABOVE))
     (11 11 (:REWRITE DEFAULT-LESS-THAN-2))
     (8 8 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (8 8 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (8 8
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (8 8
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (8 8 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (8 8
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (8 8 (:REWRITE NORMALIZE-ADDENDS))
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
     (5 1 (:REWRITE RATIONALP-X))
     (4 4 (:REWRITE |(< y (+ (- c) x))|))
     (4 4 (:REWRITE |(< x (+ c/d y))|))
     (4 4 (:REWRITE |(< (+ c/d x) y)|))
     (4 4 (:REWRITE |(< (+ (- c) x) y)|))
     (3 3 (:REWRITE REDUCE-INTEGERP-+))
     (3 3 (:REWRITE INTEGERP-MINUS-X))
     (3 3
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (3 3 (:META META-INTEGERP-CORRECT))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (1 1 (:REWRITE REDUCE-RATIONALP-+))
     (1 1 (:REWRITE REDUCE-RATIONALP-*))
     (1 1 (:REWRITE RATIONALP-MINUS-X))
     (1 1
        (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (1 1 (:REWRITE FOLD-CONSTS-IN-+))
     (1 1 (:REWRITE |(< 0 (/ x))|))
     (1 1 (:REWRITE |(< 0 (* x y))|))
     (1 1 (:REWRITE |(+ c (+ d x))|))
     (1 1 (:META META-RATIONALP-CORRECT)))
(RP::B+-PP-SUM-RANGE-2)
(RP::B+-PP-SUM-RANGE-2-AND$)
(RP::LESS-THAN-0)
(RP::PP-SUM-RANGE)
(RP::PP-SUM-RANGE-AND$)
(RP::PP-SUM-RANGE-AND$-2)
(RP::B+-FLOOR-RANGE
     (817 817
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (817 817
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (817 817
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (288 32
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (288 32
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (279 31 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (279 31
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (279 31
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (160 32
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (160 32
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (160 32
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (160 32
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (155 31 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (155 31
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (155 31
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (155 31
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (155 31
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (64 64 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (64 64 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (64 64 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (64 64 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (25 2 (:REWRITE DEFAULT-FLOOR-RATIO))
     (22 2 (:REWRITE ACL2-NUMBERP-X))
     (16 16 (:REWRITE DEFAULT-TIMES-2))
     (16 16 (:REWRITE DEFAULT-TIMES-1))
     (14 10 (:REWRITE SIMPLIFY-SUMS-<))
     (14 10
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (14 10 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (12 12 (:REWRITE REDUCE-INTEGERP-+))
     (12 12
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (12 12 (:REWRITE INTEGERP-MINUS-X))
     (12 12
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (12 12 (:META META-INTEGERP-CORRECT))
     (11 11 (:REWRITE THE-FLOOR-BELOW))
     (11 11 (:REWRITE THE-FLOOR-ABOVE))
     (11 11 (:REWRITE DEFAULT-LESS-THAN-2))
     (11 10
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (11 10
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (10 10 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (10 10
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (10 10
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
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
     (10 10 (:REWRITE |(< (- x) c)|))
     (10 10 (:REWRITE |(< (- x) (- y))|))
     (10 2 (:REWRITE RATIONALP-X))
     (8 2 (:REWRITE |(* y x)|))
     (7 1 (:REWRITE |(* (if a b c) x)|))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (4 4 (:REWRITE |(< 0 (/ x))|))
     (4 4 (:REWRITE |(< 0 (* x y))|))
     (3 3
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (3 3 (:REWRITE NORMALIZE-ADDENDS))
     (3 3 (:REWRITE DEFAULT-PLUS-2))
     (3 3 (:REWRITE DEFAULT-PLUS-1))
     (2 2 (:TYPE-PRESCRIPTION ABS))
     (2 2 (:REWRITE REDUCE-RATIONALP-+))
     (2 2 (:REWRITE REDUCE-RATIONALP-*))
     (2 2 (:REWRITE RATIONALP-MINUS-X))
     (2 2
        (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (2 2 (:REWRITE DEFAULT-FLOOR-2))
     (2 2 (:REWRITE DEFAULT-FLOOR-1))
     (2 2
        (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (2 2 (:META META-RATIONALP-CORRECT))
     (1 1 (:REWRITE |(floor x 2)| . 2))
     (1 1
        (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (1 1 (:REWRITE |(< (+ c/d x) y)|))
     (1 1 (:REWRITE |(< (+ (- c) x) y)|)))
(RP::F2-RANGE
     (718 718
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (718 718
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (718 718
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (288 32
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (288 32
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (279 31 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (279 31
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (279 31
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (160 32
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (160 32
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (160 32
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (160 32
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (155 31 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (155 31
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (155 31
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (155 31
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (155 31
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (47 4 (:REWRITE DEFAULT-FLOOR-RATIO))
     (30 30 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (30 30 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (30 30 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (27 27 (:REWRITE DEFAULT-TIMES-2))
     (27 27 (:REWRITE DEFAULT-TIMES-1))
     (27 1 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
     (23 1 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (22 2 (:REWRITE ACL2-NUMBERP-X))
     (18 18
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (10 2 (:REWRITE RATIONALP-X))
     (9 9 (:REWRITE THE-FLOOR-BELOW))
     (9 9 (:REWRITE THE-FLOOR-ABOVE))
     (9 9 (:REWRITE REDUCE-INTEGERP-+))
     (9 9 (:REWRITE INTEGERP-MINUS-X))
     (9 9
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (9 9 (:REWRITE DEFAULT-LESS-THAN-2))
     (9 9 (:META META-INTEGERP-CORRECT))
     (9 5 (:REWRITE DEFAULT-PLUS-2))
     (9 5 (:REWRITE DEFAULT-PLUS-1))
     (7 6
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (7 6
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (7 1 (:REWRITE |(* (if a b c) x)|))
     (6 6 (:REWRITE SIMPLIFY-SUMS-<))
     (6 6
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (6 6 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (6 6 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (6 6 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (6 6 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
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
     (4 4
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (4 4 (:REWRITE NORMALIZE-ADDENDS))
     (4 4 (:REWRITE DEFAULT-FLOOR-2))
     (4 4 (:REWRITE DEFAULT-FLOOR-1))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (3 3 (:REWRITE |(floor x 2)| . 2))
     (3 3 (:REWRITE |(< 0 (/ x))|))
     (3 3 (:REWRITE |(< 0 (* x y))|))
     (2 2 (:TYPE-PRESCRIPTION ABS))
     (2 2 (:REWRITE REDUCE-RATIONALP-+))
     (2 2 (:REWRITE REDUCE-RATIONALP-*))
     (2 2 (:REWRITE RATIONALP-MINUS-X))
     (2 2
        (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (2 2
        (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (2 2 (:META META-RATIONALP-CORRECT))
     (1 1
        (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (1 1 (:REWRITE |(< (+ c/d x) y)|))
     (1 1 (:REWRITE |(< (+ (- c) x) y)|)))
(RP::SUM-IS-NOT-NEG)
(RP::F2-IS-NOT-NEG (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
                   (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                   (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                   (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                   (13 1 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
                   (9 1
                      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
                   (9 1
                      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
                   (9 1
                      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
                   (5 1 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
                   (5 1 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
                   (5 1
                      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
                   (5 1
                      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
                   (5 1
                      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
                   (5 1
                      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
                   (5 1
                      (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
                   (5 1
                      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
                   (5 1
                      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2)))
(RP::PP-SUM-IS-NOT-NEG)
(RP::PP-IS-NOT-NEGP)
(RP::AND-IS-NOT-NEGP)
(RP::LIST-EQ1 (14 2
                  (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
              (13 3 (:REWRITE ACL2-NUMBERP-X))
              (5 1 (:REWRITE RATIONALP-X))
              (4 4 (:REWRITE DEFAULT-CDR))
              (4 4 (:REWRITE DEFAULT-CAR))
              (4 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
              (4 2
                 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
              (3 3
                 (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
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
              (1 1 (:REWRITE REDUCE-INTEGERP-+))
              (1 1 (:REWRITE RATIONALP-MINUS-X))
              (1 1
                 (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
              (1 1 (:REWRITE INTEGERP-MINUS-X))
              (1 1
                 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
              (1 1 (:META META-RATIONALP-CORRECT))
              (1 1 (:META META-INTEGERP-CORRECT)))
(RP::LIST-EQ2 (14 2
                  (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
              (13 3 (:REWRITE ACL2-NUMBERP-X))
              (5 1 (:REWRITE RATIONALP-X))
              (4 4 (:REWRITE DEFAULT-CAR))
              (4 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
              (4 2
                 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
              (3 3
                 (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
              (2 2
                 (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
              (2 2
                 (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
              (2 2
                 (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
              (2 2 (:REWRITE DEFAULT-CDR))
              (2 2 (:REWRITE |(equal c (/ x))|))
              (2 2 (:REWRITE |(equal c (- x))|))
              (2 2 (:REWRITE |(equal (/ x) c)|))
              (2 2 (:REWRITE |(equal (/ x) (/ y))|))
              (2 2 (:REWRITE |(equal (- x) c)|))
              (2 2 (:REWRITE |(equal (- x) (- y))|))
              (1 1 (:REWRITE REDUCE-RATIONALP-+))
              (1 1 (:REWRITE REDUCE-RATIONALP-*))
              (1 1 (:REWRITE REDUCE-INTEGERP-+))
              (1 1 (:REWRITE RATIONALP-MINUS-X))
              (1 1
                 (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
              (1 1 (:REWRITE INTEGERP-MINUS-X))
              (1 1
                 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
              (1 1 (:META META-RATIONALP-CORRECT))
              (1 1 (:META META-INTEGERP-CORRECT)))
(RP::LEN-NIL)
(RP::BOOLEAN-LISTP-NIL)
(RP::TAKE-CONS
     (68 2 (:REWRITE ZP-OPEN))
     (10 2 (:REWRITE |(+ c (+ d x))|))
     (7 7 (:REWRITE DEFAULT-PLUS-2))
     (7 7 (:REWRITE DEFAULT-PLUS-1))
     (5 5
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (5 5 (:REWRITE NORMALIZE-ADDENDS))
     (4 4 (:REWRITE THE-FLOOR-BELOW))
     (4 4 (:REWRITE THE-FLOOR-ABOVE))
     (4 4 (:REWRITE SIMPLIFY-SUMS-<))
     (4 4
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
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
     (3 3 (:REWRITE TAKE-OPENER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (3 3 (:REWRITE DEFAULT-CDR))
     (3 3 (:REWRITE DEFAULT-CAR))
     (3 3 (:REWRITE |(< 0 (/ x))|))
     (3 3 (:REWRITE |(< 0 (* x y))|))
     (2 2 (:REWRITE |(< y (+ (- c) x))|))
     (2 2 (:REWRITE |(< x (+ c/d y))|))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (1 1 (:REWRITE REDUCE-INTEGERP-+))
     (1 1 (:REWRITE INTEGERP-MINUS-X))
     (1 1
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (1 1 (:REWRITE |(< (/ x) 0)|))
     (1 1 (:REWRITE |(< (* x y) 0)|))
     (1 1 (:META META-INTEGERP-CORRECT)))
(RP::TAKE-0)
(RP::NTHCDR-CONS$
     (68 2 (:REWRITE ZP-OPEN))
     (30 2 (:REWRITE |(+ (+ x y) z)|))
     (14 14 (:REWRITE DEFAULT-PLUS-2))
     (14 14 (:REWRITE DEFAULT-PLUS-1))
     (10 2 (:REWRITE |(+ c (+ d x))|))
     (7 7
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (7 7 (:REWRITE NORMALIZE-ADDENDS))
     (4 4 (:REWRITE THE-FLOOR-BELOW))
     (4 4 (:REWRITE THE-FLOOR-ABOVE))
     (4 4 (:REWRITE SIMPLIFY-SUMS-<))
     (4 4
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
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
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (3 3 (:REWRITE DEFAULT-CDR))
     (3 3 (:REWRITE |(< 0 (/ x))|))
     (3 3 (:REWRITE |(< 0 (* x y))|))
     (2 2 (:REWRITE |(< y (+ (- c) x))|))
     (2 2 (:REWRITE |(< x (+ c/d y))|))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (1 1 (:REWRITE REDUCE-INTEGERP-+))
     (1 1 (:REWRITE INTEGERP-MINUS-X))
     (1 1
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (1 1 (:REWRITE |(< (/ x) 0)|))
     (1 1 (:REWRITE |(< (* x y) 0)|))
     (1 1 (:META META-INTEGERP-CORRECT)))
(RP::NTHCDR-0$ (22 11
                   (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
               (11 11 (:TYPE-PRESCRIPTION TRUE-LISTP)))
(RP::REPEAT-0)
(RP::CDR-REPEAT
     (68 2 (:REWRITE ZP-OPEN))
     (10 2 (:REWRITE |(+ c (+ d x))|))
     (7 7 (:REWRITE DEFAULT-PLUS-2))
     (7 7 (:REWRITE DEFAULT-PLUS-1))
     (5 5
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (5 5 (:REWRITE NORMALIZE-ADDENDS))
     (3 3 (:REWRITE THE-FLOOR-BELOW))
     (3 3 (:REWRITE THE-FLOOR-ABOVE))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (3 3 (:REWRITE SIMPLIFY-SUMS-<))
     (3 3
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (3 3 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (3 3 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (3 3
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (3 3
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (3 3 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (3 3 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (3 3 (:REWRITE INTEGERP-<-CONSTANT))
     (3 3 (:REWRITE DEFAULT-LESS-THAN-2))
     (3 3 (:REWRITE DEFAULT-LESS-THAN-1))
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
     (3 3 (:REWRITE |(< 0 (/ x))|))
     (3 3 (:REWRITE |(< 0 (* x y))|))
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
     (2 2 (:REWRITE |(< y (+ (- c) x))|))
     (2 2 (:REWRITE |(< x (+ c/d y))|))
     (2 1 (:REWRITE DEFAULT-CDR))
     (1 1 (:REWRITE REDUCE-INTEGERP-+))
     (1 1 (:REWRITE INTEGERP-MINUS-X))
     (1 1
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (1 1 (:META META-INTEGERP-CORRECT)))
(RP::CAR-REPEAT
     (34 1 (:REWRITE ZP-OPEN))
     (5 1 (:REWRITE |(+ c (+ d x))|))
     (4 4 (:REWRITE DEFAULT-PLUS-2))
     (4 4 (:REWRITE DEFAULT-PLUS-1))
     (3 3
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (3 3 (:REWRITE NORMALIZE-ADDENDS))
     (2 2 (:REWRITE THE-FLOOR-BELOW))
     (2 2 (:REWRITE THE-FLOOR-ABOVE))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (2 2 (:REWRITE SIMPLIFY-SUMS-<))
     (2 2
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (2 2 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (2 2 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (2 2
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (2 2
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (2 2 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (2 2 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
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
     (2 2 (:REWRITE |(< 0 (/ x))|))
     (2 2 (:REWRITE |(< 0 (* x y))|))
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
     (2 1 (:REWRITE DEFAULT-CAR))
     (1 1 (:REWRITE REDUCE-INTEGERP-+))
     (1 1 (:REWRITE INTEGERP-MINUS-X))
     (1 1
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (1 1 (:REWRITE |(< y (+ (- c) x))|))
     (1 1 (:REWRITE |(< x (+ c/d y))|))
     (1 1 (:META META-INTEGERP-CORRECT)))
(RP::BIT-LISTP-CONS (130 10
                         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                    (120 20 (:REWRITE ACL2-NUMBERP-X))
                    (50 10 (:REWRITE RATIONALP-X))
                    (30 10
                        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                    (30 5 (:REWRITE O-INFP->NEQ-0))
                    (20 20
                        (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
                    (15 15 (:TYPE-PRESCRIPTION O-FINP))
                    (15 5 (:REWRITE O-FIRST-EXPT-O-INFP))
                    (10 10 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                    (10 10 (:REWRITE REDUCE-RATIONALP-+))
                    (10 10 (:REWRITE REDUCE-RATIONALP-*))
                    (10 10
                        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                    (10 10 (:REWRITE REDUCE-INTEGERP-+))
                    (10 10
                        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
                    (10 10 (:REWRITE RATIONALP-MINUS-X))
                    (10 10
                        (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
                    (10 10 (:REWRITE INTEGERP-MINUS-X))
                    (10 10
                        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                    (10 10
                        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
                    (10 10 (:REWRITE |(equal c (/ x))|))
                    (10 10 (:REWRITE |(equal c (- x))|))
                    (10 10 (:REWRITE |(equal (/ x) c)|))
                    (10 10 (:REWRITE |(equal (/ x) (/ y))|))
                    (10 10 (:REWRITE |(equal (- x) c)|))
                    (10 10 (:REWRITE |(equal (- x) (- y))|))
                    (10 10 (:META META-RATIONALP-CORRECT))
                    (10 10 (:META META-INTEGERP-CORRECT))
                    (10 5 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
                    (5 5
                       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
                    (3 3 (:REWRITE DEFAULT-CDR))
                    (3 3 (:REWRITE DEFAULT-CAR)))
(RP::TRUE-LISTP-CONS
     (6109 16
           (:REWRITE RP::BIT-LISTP-IS-TRUE-LISTP))
     (6054 7 (:DEFINITION BITP))
     (6036 6 (:DEFINITION RP::BIT-LISTP))
     (5652 12 (:DEFINITION APPLY$-BADGEP))
     (4328 26
           (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (3530 10 (:DEFINITION SUBSETP-EQUAL))
     (3400 100 (:DEFINITION MEMBER-EQUAL))
     (2252 186
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (2092 104 (:REWRITE ACL2-NUMBERP-X))
     (1748 70
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (1728 52 (:REWRITE RATIONALP-X))
     (1456 54
           (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (786 22 (:DEFINITION NATP))
     (723 723 (:REWRITE DEFAULT-CDR))
     (304 12 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (300 186
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (238 238 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (210 210
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (202 202 (:REWRITE DEFAULT-CAR))
     (196 186 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (186 186
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (186 186
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (186 186
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (186 186 (:REWRITE |(equal c (/ x))|))
     (186 186 (:REWRITE |(equal c (- x))|))
     (186 186 (:REWRITE |(equal (/ x) c)|))
     (186 186 (:REWRITE |(equal (/ x) (/ y))|))
     (186 186 (:REWRITE |(equal (- x) c)|))
     (186 186 (:REWRITE |(equal (- x) (- y))|))
     (154 154 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (140 140
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (116 1 (:REWRITE RP::BIT-LISTP-CONS))
     (104 104
          (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (100 100 (:TYPE-PRESCRIPTION LEN))
     (90 10 (:DEFINITION LEN))
     (78 78 (:REWRITE REDUCE-INTEGERP-+))
     (78 78 (:REWRITE INTEGERP-MINUS-X))
     (78 78
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (78 78 (:META META-INTEGERP-CORRECT))
     (68 34
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (60 30
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (60 10 (:DEFINITION ALL-NILS))
     (58 22 (:REWRITE RP::BINARYP-NATP))
     (52 52 (:REWRITE REDUCE-RATIONALP-+))
     (52 52 (:REWRITE REDUCE-RATIONALP-*))
     (52 52 (:REWRITE RATIONALP-MINUS-X))
     (52 52
         (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (52 52 (:META META-RATIONALP-CORRECT))
     (50 50 (:TYPE-PRESCRIPTION ALL-NILS))
     (40 40 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (40 40 (:TYPE-PRESCRIPTION RP::BIT-LISTP))
     (36 36 (:TYPE-PRESCRIPTION RP::BINARYP))
     (36 36 (:LINEAR LEN-WHEN-PREFIXP))
     (20 10 (:REWRITE DEFAULT-PLUS-2))
     (20 10
         (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (18 18 (:REWRITE THE-FLOOR-BELOW))
     (18 18 (:REWRITE THE-FLOOR-ABOVE))
     (18 18
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (18 18
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (18 18 (:REWRITE SIMPLIFY-SUMS-<))
     (18 18
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (18 18 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (18 18
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (18 18
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (18 18
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (18 18
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (18 18 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (18 18 (:REWRITE INTEGERP-<-CONSTANT))
     (18 18 (:REWRITE DEFAULT-LESS-THAN-2))
     (18 18 (:REWRITE DEFAULT-LESS-THAN-1))
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
     (18 18 (:REWRITE |(< (/ x) 0)|))
     (18 18 (:REWRITE |(< (/ x) (/ y))|))
     (18 18 (:REWRITE |(< (- x) c)|))
     (18 18 (:REWRITE |(< (- x) (- y))|))
     (18 18 (:REWRITE |(< (* x y) 0)|))
     (16 16
         (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
     (10 10
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (10 10 (:REWRITE NORMALIZE-ADDENDS))
     (10 10 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (10 10 (:REWRITE DEFAULT-PLUS-1))
     (7 7
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RP::~-OF-PP (140 20 (:REWRITE ACL2-NUMBERP-X))
             (85 11
                 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
             (60 12 (:REWRITE RATIONALP-X))
             (20 20
                 (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
             (20 19 (:REWRITE DEFAULT-PLUS-1))
             (19 19 (:REWRITE DEFAULT-PLUS-2))
             (18 3 (:REWRITE O-INFP->NEQ-0))
             (15 15
                 (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
             (13 13 (:REWRITE |(equal c (/ x))|))
             (13 13 (:REWRITE |(equal c (- x))|))
             (13 13 (:REWRITE |(equal (/ x) c)|))
             (13 13 (:REWRITE |(equal (/ x) (/ y))|))
             (13 13 (:REWRITE |(equal (- x) (- y))|))
             (12 12 (:REWRITE REDUCE-RATIONALP-+))
             (12 12 (:REWRITE REDUCE-RATIONALP-*))
             (12 12 (:REWRITE REDUCE-INTEGERP-+))
             (12 12 (:REWRITE RATIONALP-MINUS-X))
             (12 12
                 (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
             (12 12 (:REWRITE INTEGERP-MINUS-X))
             (12 12
                 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
             (12 12 (:META META-RATIONALP-CORRECT))
             (12 12 (:META META-INTEGERP-CORRECT))
             (11 11
                 (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
             (10 10 (:REWRITE SIMPLIFY-SUMS-EQUAL))
             (9 9 (:TYPE-PRESCRIPTION O-FINP))
             (9 3 (:REWRITE O-FIRST-EXPT-O-INFP))
             (6 3 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
             (5 5
                (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
             (5 5
                (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
             (2 2 (:REWRITE |(equal (+ (- c) x) y)|))
             (1 1 (:TYPE-PRESCRIPTION BUBBLE-DOWN)))
(RP::MINUS-OF-MINUS-IS-TERM (4 4 (:REWRITE DEFAULT-MINUS))
                            (3 3 (:TYPE-PRESCRIPTION RP::TYPE-FIX))
                            (2 2 (:REWRITE REDUCE-INTEGERP-+))
                            (2 2 (:REWRITE INTEGERP-MINUS-X))
                            (2 2
                               (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                            (2 2 (:META META-INTEGERP-CORRECT)))
(RP::TYPE-FIX-WHEN-NATP)
(RP::BITP-M2 (120 24 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
             (120 24 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
             (120 24
                  (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
             (120 24
                  (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
             (113 113
                  (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
             (113 113
                  (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
             (113 113
                  (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
             (54 5 (:REWRITE DEFAULT-MOD-RATIO))
             (24 24 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
             (24 24
                 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
             (24 24 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
             (24 24
                 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
             (24 24 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
             (24 6 (:REWRITE |(* y x)|))
             (23 1 (:LINEAR MOD-BOUNDS-3))
             (21 21 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
             (21 21 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
             (21 21 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
             (17 17 (:REWRITE DEFAULT-TIMES-2))
             (17 17 (:REWRITE DEFAULT-TIMES-1))
             (10 10
                 (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
             (10 2 (:LINEAR MOD-BOUNDS-2))
             (7 1 (:REWRITE |(* (if a b c) x)|))
             (6 6 (:REWRITE REDUCE-INTEGERP-+))
             (6 6 (:REWRITE INTEGERP-MINUS-X))
             (6 6
                (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
             (6 6 (:META META-INTEGERP-CORRECT))
             (5 5 (:REWRITE DEFAULT-MOD-2))
             (5 5 (:REWRITE DEFAULT-MOD-1))
             (4 4 (:REWRITE |(mod x 2)| . 2)))
(RP::F2-OF-AND$ (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
                (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                (9 1
                   (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
                (9 1
                   (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
                (5 1
                   (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
                (5 1
                   (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
                (5 1
                   (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
                (5 1
                   (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2)))
(RP::M2-OF-AND$ (222 18
                     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                (204 34 (:REWRITE ACL2-NUMBERP-X))
                (169 4 (:REWRITE RP::BIT-FIX-OPENER))
                (100 20 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
                (100 20 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
                (100 20
                     (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
                (100 20
                     (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
                (98 98 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                (98 98 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                (98 98 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                (94 5 (:REWRITE DEFAULT-MOD-RATIO))
                (85 17 (:REWRITE RATIONALP-X))
                (76 2 (:LINEAR MOD-BOUNDS-3))
                (52 18
                    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                (51 19 (:REWRITE DEFAULT-TIMES-2))
                (47 7 (:REWRITE |(* y x)|))
                (38 19 (:REWRITE DEFAULT-TIMES-1))
                (34 34
                    (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
                (32 4 (:LINEAR MOD-BOUNDS-2))
                (27 27 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                (27 27 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                (27 27 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                (24 24 (:REWRITE REDUCE-INTEGERP-+))
                (24 24 (:REWRITE INTEGERP-MINUS-X))
                (24 24
                    (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                (24 24 (:META META-INTEGERP-CORRECT))
                (24 4 (:REWRITE O-INFP->NEQ-0))
                (20 20 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
                (20 20
                    (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
                (20 20 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
                (20 20
                    (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
                (20 20 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
                (18 18 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                (18 18
                    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                (18 18
                    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
                (18 18
                    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
                (18 18 (:REWRITE |(equal c (/ x))|))
                (18 18 (:REWRITE |(equal c (- x))|))
                (18 18 (:REWRITE |(equal (/ x) c)|))
                (18 18 (:REWRITE |(equal (/ x) (/ y))|))
                (18 18 (:REWRITE |(equal (- x) c)|))
                (18 18 (:REWRITE |(equal (- x) (- y))|))
                (18 5 (:REWRITE DEFAULT-MOD-1))
                (17 17 (:REWRITE REDUCE-RATIONALP-+))
                (17 17 (:REWRITE REDUCE-RATIONALP-*))
                (17 17 (:REWRITE RATIONALP-MINUS-X))
                (17 17
                    (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
                (17 17 (:META META-RATIONALP-CORRECT))
                (12 12 (:TYPE-PRESCRIPTION O-FINP))
                (12 12
                    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                (12 4 (:REWRITE O-FIRST-EXPT-O-INFP))
                (8 4 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
                (7 7
                   (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
                (5 5 (:REWRITE DEFAULT-MOD-2))
                (5 5 (:REWRITE |(mod x 2)| . 2))
                (3 3 (:TYPE-PRESCRIPTION BITP)))
(RP::M2-OF-PP-SUM-OF-AND$
     (228 21
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (204 34 (:REWRITE ACL2-NUMBERP-X))
     (169 4 (:REWRITE RP::BIT-FIX-OPENER))
     (85 17 (:REWRITE RATIONALP-X))
     (58 21
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (34 34
         (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (28 6 (:REWRITE O-INFP->NEQ-0))
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
     (17 17 (:REWRITE REDUCE-RATIONALP-+))
     (17 17 (:REWRITE REDUCE-RATIONALP-*))
     (17 17 (:REWRITE REDUCE-INTEGERP-+))
     (17 17 (:REWRITE RATIONALP-MINUS-X))
     (17 17
         (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (17 17 (:REWRITE INTEGERP-MINUS-X))
     (17 17
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (17 17 (:META META-RATIONALP-CORRECT))
     (17 17 (:META META-INTEGERP-CORRECT))
     (12 12 (:TYPE-PRESCRIPTION O-FINP))
     (12 4 (:REWRITE O-FIRST-EXPT-O-INFP))
     (9 9
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (8 4 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
     (3 3 (:TYPE-PRESCRIPTION BITP))
     (2 1 (:REWRITE DEFAULT-PLUS-2))
     (1 1 (:REWRITE DEFAULT-PLUS-1)))
(RP::F2-OF-PP-SUM-OF-AND$ (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
                          (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                          (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                          (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                          (9 1
                             (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
                          (9 1
                             (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
                          (5 1
                             (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
                          (5 1
                             (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
                          (5 1
                             (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
                          (5 1
                             (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2)))
(RP::M2-OF-F2 (3 2
                 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
              (3 2
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
              (2 1 (:REWRITE O-INFP->NEQ-0))
              (1 1
                 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RP::EQUAL-OF-M2-OF-F2
     (3 2
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (3 2
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
     (2 1 (:REWRITE O-INFP->NEQ-0))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RP::BINARY-NOT-OF-M2 (118 8 (:REWRITE DEFAULT-MOD-RATIO))
                      (114 114
                           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                      (114 114
                           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                      (114 114
                           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                      (100 20 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
                      (100 20 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
                      (100 20
                           (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
                      (100 20
                           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
                      (64 10 (:REWRITE |(* y x)|))
                      (46 2 (:LINEAR MOD-BOUNDS-3))
                      (44 44 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                      (44 44 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                      (44 44 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                      (36 32 (:REWRITE DEFAULT-TIMES-2))
                      (32 32 (:REWRITE DEFAULT-TIMES-1))
                      (27 7 (:REWRITE DEFAULT-PLUS-2))
                      (26 2 (:REWRITE |(* (if a b c) x)|))
                      (20 20 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
                      (20 20
                          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
                      (20 20 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
                      (20 20
                          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
                      (20 20 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
                      (20 4 (:LINEAR MOD-BOUNDS-2))
                      (19 19
                          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                      (10 10 (:REWRITE REDUCE-INTEGERP-+))
                      (10 10 (:REWRITE INTEGERP-MINUS-X))
                      (10 10
                          (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                      (10 10 (:META META-INTEGERP-CORRECT))
                      (10 2 (:REWRITE DEFAULT-MINUS))
                      (8 8 (:REWRITE DEFAULT-MOD-2))
                      (8 8 (:REWRITE DEFAULT-MOD-1))
                      (7 7 (:REWRITE DEFAULT-PLUS-1))
                      (6 6 (:REWRITE |(mod x 2)| . 2))
                      (4 4
                         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                      (4 4 (:REWRITE NORMALIZE-ADDENDS)))
(RP::INTEGERP-M2 (5 1 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
                 (5 1 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
                 (5 1 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
                 (5 1 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
                 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
                 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                 (1 1 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
                 (1 1 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
                 (1 1 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
                 (1 1 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
                 (1 1 (:TYPE-PRESCRIPTION INTEGERP-MOD-2)))
(RP::INTEGERP-F2)
(RP::PP-SUM-OF-0 (53 53 (:REWRITE DEFAULT-PLUS-2))
                 (53 53 (:REWRITE DEFAULT-PLUS-1))
                 (12 12 (:REWRITE REDUCE-INTEGERP-+))
                 (12 12 (:REWRITE INTEGERP-MINUS-X))
                 (12 12
                     (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                 (12 12 (:META META-INTEGERP-CORRECT))
                 (6 6
                    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                 (6 6 (:REWRITE NORMALIZE-ADDENDS)))
(RP::PP-SUM-OF-NIL)
(RP::PP-SUM-OF-0-FIXORDER)
(RP::PP-SUM-OF-0-0)
(RP::BIT-OF-BIT-OF-WHEN-NOT-O
 (1981 16 (:REWRITE DEFAULT-FLOOR-RATIO))
 (1497 6 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (1229 161 (:REWRITE DEFAULT-TIMES-2))
 (1218 10 (:REWRITE |(* (* x y) z)|))
 (1176 161 (:REWRITE DEFAULT-TIMES-1))
 (984 5 (:REWRITE FLOOR-ZERO . 3))
 (844 5 (:REWRITE CANCEL-FLOOR-+))
 (670 6 (:REWRITE FLOOR-=-X/Y . 3))
 (636 10 (:REWRITE BUBBLE-DOWN-*-BUBBLE-DOWN))
 (613 6 (:REWRITE FLOOR-=-X/Y . 2))
 (604 604
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (604 604
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (604 604
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (604 604
      (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (603 30
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (523
  523
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (523 523
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (523
     523
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (523 523
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (523 523
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (370 37 (:REWRITE DEFAULT-DIVIDE))
 (367 16 (:REWRITE DEFAULT-FLOOR-1))
 (357 6 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (337 37 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (337 37
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (337 37
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (337 37
      (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (337 37
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (308 6 (:REWRITE FLOOR-ZERO . 5))
 (264 34 (:REWRITE |(/ (expt x n))|))
 (224 8 (:REWRITE |(* (/ c) (expt d n))|))
 (187 37 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (187 37 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (187 37
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (187 37
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (187 37
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (187 37
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (187 37
      (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (187 37
      (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
 (187 37
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (187 37
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (179 27 (:REWRITE DEFAULT-PLUS-2))
 (172 5 (:REWRITE |(integerp (- x))|))
 (158 6 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (158 6 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (155 28 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (133 5 (:REWRITE FLOOR-ZERO . 2))
 (126 59 (:REWRITE DEFAULT-MINUS))
 (124 16 (:REWRITE DEFAULT-FLOOR-2))
 (122 122
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (122 122
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (122 122
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (113 3 (:REWRITE |(* x (if a b c))|))
 (112 8 (:LINEAR EXPT->=-1-ONE))
 (110 30 (:REWRITE DEFAULT-LESS-THAN-2))
 (109 8 (:LINEAR EXPT->-1-ONE))
 (103 30 (:REWRITE DEFAULT-LESS-THAN-1))
 (88 10 (:REWRITE |(* x (- y))|))
 (88 5 (:REWRITE FLOOR-CANCEL-*-CONST))
 (88 2 (:REWRITE |(* (- (/ c)) (expt d n))|))
 (78 5 (:REWRITE |(* (- x) y)|))
 (73 28 (:REWRITE SIMPLIFY-SUMS-<))
 (71 71 (:REWRITE DEFAULT-EXPT-2))
 (71 71 (:REWRITE DEFAULT-EXPT-1))
 (69 69 (:REWRITE |(expt 1/c n)|))
 (69 69 (:REWRITE |(expt (- x) n)|))
 (60 10 (:REWRITE |(- (+ x y))|))
 (55 16
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (48 3
     (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (48 3
     (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (45 3 (:REWRITE |(/ (if a b c))|))
 (40 40
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (40 40
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (40 40
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (40 40
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (36 30
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (36 30
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (30 30 (:REWRITE THE-FLOOR-BELOW))
 (30 30 (:REWRITE THE-FLOOR-ABOVE))
 (30 30
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (30 30
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
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
 (29 16
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (27 27 (:REWRITE DEFAULT-PLUS-1))
 (25 25 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (25 25
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (25 25 (:REWRITE NORMALIZE-ADDENDS))
 (24 24 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (24 2 (:REWRITE |(* x (expt x n))|))
 (19 19 (:REWRITE REDUCE-INTEGERP-+))
 (19 19 (:REWRITE INTEGERP-MINUS-X))
 (19 19
     (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
 (19 19 (:META META-INTEGERP-CORRECT))
 (18 2 (:REWRITE |(* (/ x) (expt x n))|))
 (17 17
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (17 17
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (17 17 (:REWRITE |(< (/ x) 0)|))
 (17 17 (:REWRITE |(< (* x y) 0)|))
 (16 16
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (16 16
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (16 8 (:REWRITE ODD-EXPT-THM))
 (12 12 (:TYPE-PRESCRIPTION ABS))
 (10 10 (:REWRITE BUBBLE-DOWN-*-MATCH-3))
 (10 10 (:REWRITE |(* c (* d x))|))
 (10 2 (:REWRITE |(+ y x)|))
 (9 9
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (8 8 (:LINEAR EXPT-X->=-X))
 (8 8 (:LINEAR EXPT-X->-X))
 (8 8 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (8 8 (:LINEAR EXPT-LINEAR-UPPER-<))
 (8 8 (:LINEAR EXPT-LINEAR-LOWER-<))
 (8 8 (:LINEAR EXPT->=-1-TWO))
 (8 8 (:LINEAR EXPT->-1-TWO))
 (8 8 (:LINEAR EXPT-<=-1-TWO))
 (8 8 (:LINEAR EXPT-<=-1-ONE))
 (8 8 (:LINEAR EXPT-<-1-TWO))
 (8 8 (:LINEAR EXPT-<-1-ONE))
 (6 6 (:REWRITE |(* 0 x)|))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (5 5 (:REWRITE |(< 0 (/ x))|))
 (5 5 (:REWRITE |(< 0 (* x y))|))
 (5 5 (:REWRITE |(- (* c x))|))
 (3 3
    (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (3 3 (:REWRITE |(floor x (- y))| . 2))
 (3 3 (:REWRITE |(floor x (- y))| . 1))
 (3 3
    (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (3 3 (:REWRITE |(floor (- x) y)| . 2))
 (3 3 (:REWRITE |(floor (- x) y)| . 1))
 (3 3
    (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (2 2
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (1 1 (:REWRITE |(* 1/2 (floor x y))| . 3))
 (1 1 (:REWRITE |(* 1/2 (floor x y))| . 2)))
(RP::BIT-OF-BIT-OF-WHEN-0
 (2643 27 (:REWRITE DEFAULT-FLOOR-RATIO))
 (2616 10 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (2436 20 (:REWRITE |(* (* x y) z)|))
 (2340 310 (:REWRITE DEFAULT-TIMES-1))
 (2320 310 (:REWRITE DEFAULT-TIMES-2))
 (1968 10 (:REWRITE FLOOR-ZERO . 3))
 (1688 10 (:REWRITE CANCEL-FLOOR-+))
 (1530 1530
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (1530 1530
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (1530 1530
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (1530 1530
       (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (1272 20 (:REWRITE BUBBLE-DOWN-*-BUBBLE-DOWN))
 (1216 10 (:REWRITE FLOOR-=-X/Y . 3))
 (1184 56
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (1132 10 (:REWRITE FLOOR-=-X/Y . 2))
 (972
  972
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (972 972
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (972
     972
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (972 972
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (972 972
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (890 98 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (890 98
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (890 98
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (890 98
      (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (890 98
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (664 10 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (640 64 (:REWRITE DEFAULT-DIVIDE))
 (584 10 (:REWRITE FLOOR-ZERO . 5))
 (584 10 (:REWRITE FLOOR-ZERO . 4))
 (494 98 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (494 98 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (494 98
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (494 98
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (494 98
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (494 98
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (494 98
      (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (494 98
      (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
 (494 98
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (494 98
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (468 58 (:REWRITE |(/ (expt x n))|))
 (448 16 (:REWRITE |(* (/ c) (expt d n))|))
 (386 27 (:REWRITE DEFAULT-FLOOR-1))
 (358 54 (:REWRITE DEFAULT-PLUS-2))
 (344 10 (:REWRITE |(integerp (- x))|))
 (288 52 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (268 268
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (268 268
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (268 268
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (266 10 (:REWRITE FLOOR-ZERO . 2))
 (266 10 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (266 10 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (242 108 (:REWRITE DEFAULT-MINUS))
 (226 6 (:REWRITE |(* x (if a b c))|))
 (202 56 (:REWRITE DEFAULT-LESS-THAN-1))
 (198 56 (:REWRITE DEFAULT-LESS-THAN-2))
 (196 14 (:LINEAR EXPT->=-1-ONE))
 (190 14 (:LINEAR EXPT->-1-ONE))
 (189 27 (:REWRITE DEFAULT-FLOOR-2))
 (176 20 (:REWRITE |(* x (- y))|))
 (176 10 (:REWRITE FLOOR-CANCEL-*-CONST))
 (176 4 (:REWRITE |(* (- (/ c)) (expt d n))|))
 (156 10 (:REWRITE |(* (- x) y)|))
 (142 52 (:REWRITE SIMPLIFY-SUMS-<))
 (120 120 (:REWRITE DEFAULT-EXPT-2))
 (120 120 (:REWRITE DEFAULT-EXPT-1))
 (120 20 (:REWRITE |(- (+ x y))|))
 (116 116 (:REWRITE |(expt 1/c n)|))
 (116 116 (:REWRITE |(expt (- x) n)|))
 (106 28
      (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (96 6
     (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (96 6
     (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (90 6 (:REWRITE |(/ (if a b c))|))
 (80 80
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (80 80
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (80 80
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (80 80
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (68 56
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (68 56
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (56 56 (:REWRITE THE-FLOOR-BELOW))
 (56 56 (:REWRITE THE-FLOOR-ABOVE))
 (56 56
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (56 56
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (56 56 (:REWRITE INTEGERP-<-CONSTANT))
 (56 56 (:REWRITE CONSTANT-<-INTEGERP))
 (56 56
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (56 56
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (56 56
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (56 56
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (56 56 (:REWRITE |(< c (- x))|))
 (56 56
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (56 56
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (56 56
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (56 56
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (56 56 (:REWRITE |(< (/ x) (/ y))|))
 (56 56 (:REWRITE |(< (- x) c)|))
 (56 56 (:REWRITE |(< (- x) (- y))|))
 (54 54 (:REWRITE DEFAULT-PLUS-1))
 (50 50
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (50 50 (:REWRITE NORMALIZE-ADDENDS))
 (48 48 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (48 4 (:REWRITE |(* x (expt x n))|))
 (46 46 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (40 40 (:REWRITE REDUCE-INTEGERP-+))
 (40 40 (:REWRITE INTEGERP-MINUS-X))
 (40 40
     (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
 (40 40 (:META META-INTEGERP-CORRECT))
 (36 4 (:REWRITE |(* (/ x) (expt x n))|))
 (32 32
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (32 32
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (32 32 (:REWRITE |(< (/ x) 0)|))
 (32 32 (:REWRITE |(< (* x y) 0)|))
 (30 14 (:REWRITE ODD-EXPT-THM))
 (28 28
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (28 28
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (28 28
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (24 24 (:TYPE-PRESCRIPTION ABS))
 (20 20 (:REWRITE BUBBLE-DOWN-*-MATCH-3))
 (20 20 (:REWRITE |(* c (* d x))|))
 (20 4 (:REWRITE |(+ y x)|))
 (18 18
     (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (14 14 (:LINEAR EXPT-X->=-X))
 (14 14 (:LINEAR EXPT-X->-X))
 (14 14 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (14 14 (:LINEAR EXPT-LINEAR-UPPER-<))
 (14 14 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (14 14 (:LINEAR EXPT-LINEAR-LOWER-<))
 (14 14 (:LINEAR EXPT->=-1-TWO))
 (14 14 (:LINEAR EXPT->-1-TWO))
 (14 14 (:LINEAR EXPT-<=-1-TWO))
 (14 14 (:LINEAR EXPT-<=-1-ONE))
 (14 14 (:LINEAR EXPT-<-1-TWO))
 (14 14 (:LINEAR EXPT-<-1-ONE))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (10 10 (:REWRITE |(< 0 (/ x))|))
 (10 10 (:REWRITE |(< 0 (* x y))|))
 (10 10 (:REWRITE |(- (* c x))|))
 (8 8 (:REWRITE |(* 0 x)|))
 (6 6
    (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (6 6 (:REWRITE |(floor x (- y))| . 2))
 (6 6 (:REWRITE |(floor x (- y))| . 1))
 (6 6
    (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (6 6 (:REWRITE |(floor (- x) y)| . 2))
 (6 6 (:REWRITE |(floor (- x) y)| . 1))
 (6 6
    (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (4 4
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (2 2 (:REWRITE |(* 1/2 (floor x y))| . 3))
 (2 2 (:REWRITE |(* 1/2 (floor x y))| . 2)))
(RP::BINARY-XOR-OF-0
     (184 16
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (168 28 (:REWRITE ACL2-NUMBERP-X))
     (114 4 (:REWRITE RP::BIT-FIX-OPENER))
     (70 14 (:REWRITE RATIONALP-X))
     (44 16
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (38 8 (:REWRITE O-INFP->NEQ-0))
     (28 28
         (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (18 18 (:TYPE-PRESCRIPTION O-FINP))
     (18 6 (:REWRITE O-FIRST-EXPT-O-INFP))
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
     (14 14 (:REWRITE REDUCE-RATIONALP-+))
     (14 14 (:REWRITE REDUCE-RATIONALP-*))
     (14 14 (:REWRITE REDUCE-INTEGERP-+))
     (14 14 (:REWRITE RATIONALP-MINUS-X))
     (14 14
         (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (14 14 (:REWRITE INTEGERP-MINUS-X))
     (14 14
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (14 14 (:META META-RATIONALP-CORRECT))
     (14 14 (:META META-INTEGERP-CORRECT))
     (12 6 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
     (10 10
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (2 2 (:TYPE-PRESCRIPTION BITP)))
(RP::BINARY-XOR-OF-1
     (232 32 (:REWRITE ACL2-NUMBERP-X))
     (164 20
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (114 4 (:REWRITE RP::BIT-FIX-OPENER))
     (100 20 (:REWRITE RATIONALP-X))
     (32 32
         (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (26 6 (:REWRITE O-INFP->NEQ-0))
     (20 20 (:REWRITE REDUCE-RATIONALP-+))
     (20 20 (:REWRITE REDUCE-RATIONALP-*))
     (20 20
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (20 20 (:REWRITE REDUCE-INTEGERP-+))
     (20 20
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (20 20 (:REWRITE RATIONALP-MINUS-X))
     (20 20
         (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (20 20 (:REWRITE INTEGERP-MINUS-X))
     (20 20
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (20 20
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (20 20 (:REWRITE |(equal c (/ x))|))
     (20 20 (:REWRITE |(equal c (- x))|))
     (20 20 (:REWRITE |(equal (/ x) c)|))
     (20 20 (:REWRITE |(equal (/ x) (/ y))|))
     (20 20 (:REWRITE |(equal (- x) c)|))
     (20 20 (:REWRITE |(equal (- x) (- y))|))
     (20 20 (:META META-RATIONALP-CORRECT))
     (20 20 (:META META-INTEGERP-CORRECT))
     (20 18 (:REWRITE DEFAULT-PLUS-1))
     (18 18 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (18 18 (:REWRITE DEFAULT-PLUS-2))
     (12 12 (:TYPE-PRESCRIPTION O-FINP))
     (12 4 (:REWRITE O-FIRST-EXPT-O-INFP))
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (8 4 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
     (6 6 (:REWRITE |(equal (+ (- c) x) y)|))
     (4 4
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (2 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (2 2 (:TYPE-PRESCRIPTION BITP)))
(RP::NOT$-OF-NOT$ (107 17 (:REWRITE ACL2-NUMBERP-X))
                  (70 8
                      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                  (45 9 (:REWRITE RATIONALP-X))
                  (20 8
                      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                  (18 18 (:REWRITE DEFAULT-PLUS-2))
                  (18 18 (:REWRITE DEFAULT-PLUS-1))
                  (17 17
                      (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
                  (12 12
                      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                  (12 2 (:REWRITE O-INFP->NEQ-0))
                  (10 10 (:REWRITE |(equal c (/ x))|))
                  (10 10 (:REWRITE |(equal c (- x))|))
                  (10 10 (:REWRITE |(equal (/ x) c)|))
                  (10 10 (:REWRITE |(equal (/ x) (/ y))|))
                  (10 10 (:REWRITE |(equal (- x) (- y))|))
                  (9 9 (:REWRITE REDUCE-RATIONALP-+))
                  (9 9 (:REWRITE REDUCE-RATIONALP-*))
                  (9 9 (:REWRITE REDUCE-INTEGERP-+))
                  (9 9 (:REWRITE RATIONALP-MINUS-X))
                  (9 9
                     (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
                  (9 9 (:REWRITE INTEGERP-MINUS-X))
                  (9 9
                     (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                  (9 9 (:META META-RATIONALP-CORRECT))
                  (9 9 (:META META-INTEGERP-CORRECT))
                  (8 8 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                  (8 8
                     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
                  (6 6 (:TYPE-PRESCRIPTION O-FINP))
                  (6 2 (:REWRITE O-FIRST-EXPT-O-INFP))
                  (4 4
                     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
                  (4 4
                     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                  (4 4 (:REWRITE NORMALIZE-ADDENDS))
                  (4 2 (:REWRITE O-FIRST-EXPT-DEF-O-FINP)))
(RP::BINARY-?-OF-CONSTANTS
     (800 68
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (776 126 (:REWRITE ACL2-NUMBERP-X))
     (325 65 (:REWRITE RATIONALP-X))
     (126 126
          (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (120 20 (:REWRITE O-INFP->NEQ-0))
     (72 72
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (70 70 (:REWRITE |(equal c (/ x))|))
     (70 70 (:REWRITE |(equal c (- x))|))
     (70 70 (:REWRITE |(equal (/ x) c)|))
     (70 70 (:REWRITE |(equal (/ x) (/ y))|))
     (70 70 (:REWRITE |(equal (- x) (- y))|))
     (68 68
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (67 67 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (65 65 (:REWRITE REDUCE-RATIONALP-+))
     (65 65 (:REWRITE REDUCE-RATIONALP-*))
     (65 65 (:REWRITE REDUCE-INTEGERP-+))
     (65 65 (:REWRITE RATIONALP-MINUS-X))
     (65 65
         (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (65 65 (:REWRITE INTEGERP-MINUS-X))
     (65 65
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (65 65 (:META META-RATIONALP-CORRECT))
     (65 65 (:META META-INTEGERP-CORRECT))
     (60 60 (:TYPE-PRESCRIPTION O-FINP))
     (60 20 (:REWRITE O-FIRST-EXPT-O-INFP))
     (40 20 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
     (31 31
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (18 17 (:REWRITE DEFAULT-PLUS-1))
     (17 17 (:REWRITE DEFAULT-PLUS-2))
     (4 4
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (2 2 (:REWRITE |(equal (+ (- c) x) y)|))
     (1 1 (:TYPE-PRESCRIPTION BUBBLE-DOWN)))
(RP::AND$-OF-0 (65 5
                   (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
               (60 10 (:REWRITE ACL2-NUMBERP-X))
               (56 1 (:REWRITE RP::BIT-FIX-OPENER))
               (25 5 (:REWRITE RATIONALP-X))
               (15 5
                   (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
               (10 10
                   (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
               (6 1 (:REWRITE O-INFP->NEQ-0))
               (5 5 (:REWRITE SIMPLIFY-SUMS-EQUAL))
               (5 5 (:REWRITE REDUCE-RATIONALP-+))
               (5 5 (:REWRITE REDUCE-RATIONALP-*))
               (5 5
                  (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
               (5 5 (:REWRITE REDUCE-INTEGERP-+))
               (5 5
                  (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
               (5 5 (:REWRITE RATIONALP-MINUS-X))
               (5 5
                  (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
               (5 5 (:REWRITE INTEGERP-MINUS-X))
               (5 5
                  (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
               (5 5
                  (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
               (5 5 (:REWRITE |(equal c (/ x))|))
               (5 5 (:REWRITE |(equal c (- x))|))
               (5 5 (:REWRITE |(equal (/ x) c)|))
               (5 5 (:REWRITE |(equal (/ x) (/ y))|))
               (5 5 (:REWRITE |(equal (- x) c)|))
               (5 5 (:REWRITE |(equal (- x) (- y))|))
               (5 5 (:META META-RATIONALP-CORRECT))
               (5 5 (:META META-INTEGERP-CORRECT))
               (3 3 (:TYPE-PRESCRIPTION O-FINP))
               (3 1 (:REWRITE O-FIRST-EXPT-O-INFP))
               (2 2
                  (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
               (2 1 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
               (1 1 (:TYPE-PRESCRIPTION BITP)))
(RP::AND$-OF-1 (184 16
                    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
               (168 28 (:REWRITE ACL2-NUMBERP-X))
               (114 4 (:REWRITE RP::BIT-FIX-OPENER))
               (70 14 (:REWRITE RATIONALP-X))
               (44 16
                   (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
               (36 6 (:REWRITE O-INFP->NEQ-0))
               (28 28
                   (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
               (18 18 (:TYPE-PRESCRIPTION O-FINP))
               (18 6 (:REWRITE O-FIRST-EXPT-O-INFP))
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
               (14 14 (:REWRITE REDUCE-RATIONALP-+))
               (14 14 (:REWRITE REDUCE-RATIONALP-*))
               (14 14 (:REWRITE REDUCE-INTEGERP-+))
               (14 14 (:REWRITE RATIONALP-MINUS-X))
               (14 14
                   (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
               (14 14 (:REWRITE INTEGERP-MINUS-X))
               (14 14
                   (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
               (14 14 (:META META-RATIONALP-CORRECT))
               (14 14 (:META META-INTEGERP-CORRECT))
               (12 6 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
               (8 8
                  (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
               (2 2 (:TYPE-PRESCRIPTION BITP)))
(RP::OR$-OF-0 (184 16
                   (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
              (168 28 (:REWRITE ACL2-NUMBERP-X))
              (114 4 (:REWRITE RP::BIT-FIX-OPENER))
              (70 14 (:REWRITE RATIONALP-X))
              (44 16
                  (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
              (38 8 (:REWRITE O-INFP->NEQ-0))
              (28 28
                  (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
              (18 18 (:TYPE-PRESCRIPTION O-FINP))
              (18 6 (:REWRITE O-FIRST-EXPT-O-INFP))
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
              (14 14 (:REWRITE REDUCE-RATIONALP-+))
              (14 14 (:REWRITE REDUCE-RATIONALP-*))
              (14 14 (:REWRITE REDUCE-INTEGERP-+))
              (14 14 (:REWRITE RATIONALP-MINUS-X))
              (14 14
                  (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
              (14 14 (:REWRITE INTEGERP-MINUS-X))
              (14 14
                  (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
              (14 14 (:META META-RATIONALP-CORRECT))
              (14 14 (:META META-INTEGERP-CORRECT))
              (12 6 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
              (10 10
                  (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
              (2 2 (:TYPE-PRESCRIPTION BITP)))
(RP::OR$-OF-1 (65 5
                  (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
              (60 10 (:REWRITE ACL2-NUMBERP-X))
              (56 1 (:REWRITE RP::BIT-FIX-OPENER))
              (25 5 (:REWRITE RATIONALP-X))
              (15 5
                  (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
              (12 2 (:REWRITE O-INFP->NEQ-0))
              (10 10
                  (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
              (6 6 (:TYPE-PRESCRIPTION O-FINP))
              (6 2 (:REWRITE O-FIRST-EXPT-O-INFP))
              (5 5 (:REWRITE SIMPLIFY-SUMS-EQUAL))
              (5 5 (:REWRITE REDUCE-RATIONALP-+))
              (5 5 (:REWRITE REDUCE-RATIONALP-*))
              (5 5
                 (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
              (5 5 (:REWRITE REDUCE-INTEGERP-+))
              (5 5
                 (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
              (5 5 (:REWRITE RATIONALP-MINUS-X))
              (5 5
                 (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
              (5 5 (:REWRITE INTEGERP-MINUS-X))
              (5 5
                 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
              (5 5
                 (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
              (5 5 (:REWRITE |(equal c (/ x))|))
              (5 5 (:REWRITE |(equal c (- x))|))
              (5 5 (:REWRITE |(equal (/ x) c)|))
              (5 5 (:REWRITE |(equal (/ x) (/ y))|))
              (5 5 (:REWRITE |(equal (- x) c)|))
              (5 5 (:REWRITE |(equal (- x) (- y))|))
              (5 5 (:META META-RATIONALP-CORRECT))
              (5 5 (:META META-INTEGERP-CORRECT))
              (4 2 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
              (3 3
                 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
              (1 1 (:TYPE-PRESCRIPTION BITP)))
(RP::ASSOC-EQUAL-OPENER
     (65 15 (:REWRITE ACL2-NUMBERP-X))
     (65 5
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (25 5 (:REWRITE RATIONALP-X))
     (17 9 (:REWRITE DEFAULT-CAR))
     (15 15
         (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (15 5 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (15 5
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (8 2 (:REWRITE O-P-O-INFP-CAR))
     (5 5 (:REWRITE REDUCE-RATIONALP-+))
     (5 5 (:REWRITE REDUCE-RATIONALP-*))
     (5 5
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (5 5 (:REWRITE REDUCE-INTEGERP-+))
     (5 5
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (5 5 (:REWRITE RATIONALP-MINUS-X))
     (5 5
        (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (5 5 (:REWRITE INTEGERP-MINUS-X))
     (5 5
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (5 5
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (5 5 (:REWRITE |(equal c (/ x))|))
     (5 5 (:REWRITE |(equal c (- x))|))
     (5 5 (:REWRITE |(equal (/ x) c)|))
     (5 5 (:REWRITE |(equal (/ x) (/ y))|))
     (5 5 (:REWRITE |(equal (- x) c)|))
     (5 5 (:REWRITE |(equal (- x) (- y))|))
     (5 5 (:META META-RATIONALP-CORRECT))
     (5 5 (:META META-INTEGERP-CORRECT))
     (4 4 (:TYPE-PRESCRIPTION O-P))
     (3 3 (:REWRITE DEFAULT-CDR))
     (2 2 (:REWRITE O-P-DEF-O-FINP-1)))
(RP::F2-OF-M2 (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
              (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
              (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
              (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
              (9 1
                 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
              (9 1
                 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
              (5 1 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
              (5 1
                 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
              (5 1
                 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
              (5 1
                 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
              (5 1
                 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2)))
(RP::TYPE-FIX-OF-BINARY-FNCS
     (1068 95
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (1046 176 (:REWRITE ACL2-NUMBERP-X))
     (790 20 (:REWRITE RP::BIT-FIX-OPENER))
     (435 87 (:REWRITE RATIONALP-X))
     (176 176
          (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (153 28 (:REWRITE O-INFP->NEQ-0))
     (102 94 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (95 95
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (95 95
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (95 95
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (95 95 (:REWRITE |(equal c (/ x))|))
     (95 95 (:REWRITE |(equal c (- x))|))
     (95 95 (:REWRITE |(equal (/ x) c)|))
     (95 95 (:REWRITE |(equal (/ x) (/ y))|))
     (95 95 (:REWRITE |(equal (- x) c)|))
     (95 95 (:REWRITE |(equal (- x) (- y))|))
     (87 87 (:REWRITE REDUCE-RATIONALP-+))
     (87 87 (:REWRITE REDUCE-RATIONALP-*))
     (87 87 (:REWRITE REDUCE-INTEGERP-+))
     (87 87 (:REWRITE RATIONALP-MINUS-X))
     (87 87
         (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (87 87 (:REWRITE INTEGERP-MINUS-X))
     (87 87
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (87 87 (:META META-RATIONALP-CORRECT))
     (87 87 (:META META-INTEGERP-CORRECT))
     (75 75 (:TYPE-PRESCRIPTION O-FINP))
     (75 25 (:REWRITE O-FIRST-EXPT-O-INFP))
     (50 25 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
     (42 42
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (14 14 (:TYPE-PRESCRIPTION BITP))
     (13 12 (:REWRITE DEFAULT-PLUS-2))
     (13 12 (:REWRITE DEFAULT-PLUS-1))
     (3 3
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (2 2 (:REWRITE |(equal (+ (- c) x) y)|))
     (1 1 (:TYPE-PRESCRIPTION BUBBLE-DOWN)))
