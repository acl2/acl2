(LL2::OCCURLIST)
(LL2::OCCURLIST-APPEND--THM
     (176 48 (:REWRITE ACL2-NUMBERP-X))
     (172 19
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (86 43 (:REWRITE DEFAULT-PLUS-2))
     (64 16 (:REWRITE RATIONALP-X))
     (54 43 (:REWRITE DEFAULT-PLUS-1))
     (44 19 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (44 19
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (40 36 (:REWRITE DEFAULT-CDR))
     (22 22
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (22 22 (:REWRITE NORMALIZE-ADDENDS))
     (21 19 (:REWRITE DEFAULT-CAR))
     (20 20 (:REWRITE REDUCE-INTEGERP-+))
     (20 20 (:REWRITE INTEGERP-MINUS-X))
     (20 20 (:META META-INTEGERP-CORRECT))
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
     (16 16 (:REWRITE REDUCE-RATIONALP-+))
     (16 16 (:REWRITE REDUCE-RATIONALP-*))
     (16 16 (:REWRITE RATIONALP-MINUS-X))
     (16 16 (:META META-RATIONALP-CORRECT))
     (3 3 (:REWRITE |(equal (+ (- c) x) y)|)))
(LL2::TAKE-N-MINUS-1-NTH-MINUS-1--THM
     (2545 20 (:REWRITE NTH-WITH-LARGE-INDEX))
     (1097 12 (:REWRITE |(< (if a b c) x)|))
     (756 18 (:DEFINITION NFIX))
     (671 22 (:REWRITE |(< (+ (- c) x) y)|))
     (250 188 (:REWRITE DEFAULT-PLUS-2))
     (208 149 (:REWRITE DEFAULT-LESS-THAN-2))
     (188 188 (:REWRITE DEFAULT-PLUS-1))
     (161 149 (:REWRITE DEFAULT-LESS-THAN-1))
     (149 149 (:REWRITE THE-FLOOR-BELOW))
     (149 149 (:REWRITE THE-FLOOR-ABOVE))
     (137 137
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (137 137
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (136 96 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (126 96
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (119 96 (:REWRITE SIMPLIFY-SUMS-<))
     (108 108
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (108 108 (:REWRITE NORMALIZE-ADDENDS))
     (105 96 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (102 95 (:REWRITE DEFAULT-CDR))
     (96 96
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
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
     (57 50 (:REWRITE DEFAULT-CAR))
     (46 46 (:REWRITE |(< x (+ c/d y))|))
     (44 44 (:REWRITE |(< 0 (* x y))|))
     (44 44 (:LINEAR LEQ-POSITION-EQUAL-LEN))
     (43 43 (:REWRITE |(< (+ c/d x) y)|))
     (41 41
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (41 41
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (41 41 (:REWRITE |(< 0 (/ x))|))
     (26 26 (:REWRITE |(< (* x y) 0)|))
     (16 9 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (16 9
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (16 9
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
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
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (8 8 (:REWRITE |(< (/ x) 0)|))
     (6 6 (:REWRITE REDUCE-INTEGERP-+))
     (6 6 (:REWRITE INTEGERP-MINUS-X))
     (6 6 (:META META-INTEGERP-CORRECT)))
(LL2::XFIRSTN-N-MINUS-1-NTH-MINUS-1--THM
     (2545 20 (:REWRITE NTH-WITH-LARGE-INDEX))
     (1097 12 (:REWRITE |(< (if a b c) x)|))
     (756 18 (:DEFINITION NFIX))
     (671 22 (:REWRITE |(< (+ (- c) x) y)|))
     (250 188 (:REWRITE DEFAULT-PLUS-2))
     (208 149 (:REWRITE DEFAULT-LESS-THAN-2))
     (188 188 (:REWRITE DEFAULT-PLUS-1))
     (161 149 (:REWRITE DEFAULT-LESS-THAN-1))
     (149 149 (:REWRITE THE-FLOOR-BELOW))
     (149 149 (:REWRITE THE-FLOOR-ABOVE))
     (137 137
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (137 137
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (136 96 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (126 96
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (119 96 (:REWRITE SIMPLIFY-SUMS-<))
     (108 108
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (108 108 (:REWRITE NORMALIZE-ADDENDS))
     (105 96 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (102 95 (:REWRITE DEFAULT-CDR))
     (96 96
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
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
     (57 50 (:REWRITE DEFAULT-CAR))
     (46 46 (:REWRITE |(< x (+ c/d y))|))
     (44 44 (:REWRITE |(< 0 (* x y))|))
     (44 44 (:LINEAR LEQ-POSITION-EQUAL-LEN))
     (43 43 (:REWRITE |(< (+ c/d x) y)|))
     (41 41
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (41 41
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (41 41 (:REWRITE |(< 0 (/ x))|))
     (26 26 (:REWRITE |(< (* x y) 0)|))
     (16 9 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (16 9
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (16 9
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
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
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (8 8 (:REWRITE |(< (/ x) 0)|))
     (6 6 (:REWRITE REDUCE-INTEGERP-+))
     (6 6 (:REWRITE INTEGERP-MINUS-X))
     (6 6 (:META META-INTEGERP-CORRECT)))
(LL2::XFIRSTN-LEN--THM
     (114 3 (:REWRITE ZP-OPEN))
     (17 10 (:REWRITE DEFAULT-PLUS-2))
     (10 10 (:REWRITE DEFAULT-PLUS-1))
     (10 10 (:REWRITE DEFAULT-CDR))
     (7 7
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (7 7 (:REWRITE NORMALIZE-ADDENDS))
     (6 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (6 3
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (6 3
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (6 3
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (6 3 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (6 3 (:REWRITE DEFAULT-LESS-THAN-2))
     (4 4 (:REWRITE DEFAULT-CAR))
     (3 3 (:REWRITE THE-FLOOR-BELOW))
     (3 3 (:REWRITE THE-FLOOR-ABOVE))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (3 3 (:REWRITE SIMPLIFY-SUMS-<))
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
     (3 3 (:REWRITE INTEGERP-<-CONSTANT))
     (3 3
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
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
     (3 3 (:REWRITE |(< (- x) (- y))|)))
(LL2::TAKE-LEN--THM
     (114 3 (:REWRITE ZP-OPEN))
     (17 10 (:REWRITE DEFAULT-PLUS-2))
     (10 10 (:REWRITE DEFAULT-PLUS-1))
     (10 10 (:REWRITE DEFAULT-CDR))
     (7 7
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (7 7 (:REWRITE NORMALIZE-ADDENDS))
     (6 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (6 3
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (6 3
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (6 3
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (6 3 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (6 3 (:REWRITE DEFAULT-LESS-THAN-2))
     (4 4 (:REWRITE DEFAULT-CAR))
     (3 3 (:REWRITE THE-FLOOR-BELOW))
     (3 3 (:REWRITE THE-FLOOR-ABOVE))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (3 3 (:REWRITE SIMPLIFY-SUMS-<))
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
     (3 3 (:REWRITE INTEGERP-<-CONSTANT))
     (3 3
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
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
     (3 3 (:REWRITE |(< (- x) (- y))|)))
(LL2::OCCUR-ARR-STEP$INLINE)
(LL2::OCCUR-ARR-TAILREC
     (1225 8 (:REWRITE NATP-WHEN-INTEGERP))
     (782 5 (:REWRITE NFIX-WHEN-NOT-NATP))
     (516 40
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (248 110 (:REWRITE DEFAULT-PLUS-2))
     (189 110 (:REWRITE DEFAULT-PLUS-1))
     (116 1 (:REWRITE ZP-WHEN-GT-0))
     (110 36
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (94 40 (:REWRITE DEFAULT-LESS-THAN-1))
     (68 40 (:REWRITE DEFAULT-LESS-THAN-2))
     (53 7 (:DEFINITION LEN))
     (49 36 (:REWRITE |(< (- x) (- y))|))
     (49 21 (:REWRITE |(+ c (+ d x))|))
     (47 36 (:REWRITE |(< (- x) c)|))
     (40 40 (:REWRITE THE-FLOOR-BELOW))
     (40 40 (:REWRITE THE-FLOOR-ABOVE))
     (40 40
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (40 40
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (40 36
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (38 36 (:REWRITE |(< c (- x))|))
     (36 36 (:REWRITE INTEGERP-<-CONSTANT))
     (36 36 (:REWRITE CONSTANT-<-INTEGERP))
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
     (34 17 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (32 12 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
     (31 31 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (22 22
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (17 17 (:REWRITE |(< (+ c/d x) y)|))
     (16 16 (:LINEAR LEQ-POSITION-EQUAL-LEN))
     (14 7 (:REWRITE DEFAULT-MINUS))
     (13 13 (:REWRITE |(< (+ (- c) x) y)|))
     (11 11 (:REWRITE |(< (* x y) 0)|))
     (10 10 (:REWRITE REDUCE-INTEGERP-+))
     (10 10 (:REWRITE INTEGERP-MINUS-X))
     (10 10 (:META META-INTEGERP-CORRECT))
     (9 9 (:REWRITE |(< y (+ (- c) x))|))
     (9 9 (:REWRITE |(< x (+ c/d y))|))
     (7 7 (:REWRITE DEFAULT-CDR))
     (7 7 (:REWRITE |(< (/ x) 0)|))
     (4 4
        (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
     (2 2 (:REWRITE FOLD-CONSTS-IN-+))
     (2 2 (:REWRITE |(< 0 (/ x))|))
     (2 2 (:REWRITE |(< 0 (* x y))|))
     (1 1 (:REWRITE INEQUALITY-WITH-NFIX-HYP-2))
     (1 1
        (:REWRITE INEQUALITY-WITH-NFIX-HYP-1)))
(LL2::OCCUR-ARR-ITER
     (38 2 (:REWRITE NATP-WHEN-GTE-0))
     (35 5 (:REWRITE DEFAULT-LESS-THAN-2))
     (35 4 (:REWRITE DEFAULT-LESS-THAN-1))
     (35 1 (:REWRITE ZP-WHEN-GT-0))
     (10 8 (:REWRITE DEFAULT-PLUS-1))
     (8 8 (:REWRITE DEFAULT-PLUS-2))
     (7 3 (:REWRITE NFIX-WHEN-NOT-NATP))
     (5 5 (:REWRITE THE-FLOOR-BELOW))
     (5 5 (:REWRITE THE-FLOOR-ABOVE))
     (5 2 (:REWRITE NATP-WHEN-INTEGERP))
     (4 4 (:TYPE-PRESCRIPTION NATP))
     (4 4 (:REWRITE ACL2-NUMBERP-X))
     (4 1 (:REWRITE ZP-WHEN-INTEGERP))
     (3 3
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (3 3 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (3 3
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (3 3
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (3 3 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (3 3 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
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
     (2 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (2 2 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (2 2 (:REWRITE REDUCE-INTEGERP-+))
     (2 2 (:REWRITE INTEGERP-MINUS-X))
     (2 2 (:META META-INTEGERP-CORRECT))
     (1 1 (:REWRITE ZP-OPEN))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (1 1
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (1 1 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
     (1 1 (:REWRITE |(< 0 (/ x))|))
     (1 1 (:REWRITE |(< 0 (* x y))|))
     (1 1 (:REWRITE |(< (/ x) 0)|))
     (1 1 (:REWRITE |(< (+ c/d x) y)|))
     (1 1 (:REWRITE |(< (+ (- c) x) y)|))
     (1 1 (:REWRITE |(< (* x y) 0)|)))
(LL2::OCCUR-ARR-ITER-OF-IFIX-IX
     (4838 24 (:REWRITE NTH-WITH-LARGE-INDEX))
     (3990 12 (:DEFINITION NTH))
     (2594 36 (:REWRITE NATP-WHEN-INTEGERP))
     (2498 228
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (2164 24 (:REWRITE NFIX-WHEN-NATP))
     (1364 24 (:REWRITE NFIX-WHEN-NOT-NATP))
     (922 30 (:REWRITE ZP-WHEN-GT-0))
     (898 102 (:REWRITE ACL2-NUMBERP-X))
     (834 36 (:REWRITE NATP-WHEN-GTE-0))
     (741 741
          (:TYPE-PRESCRIPTION LL2::OCCUR-ARR-ITER))
     (674 30 (:REWRITE ZP-WHEN-INTEGERP))
     (450 234 (:REWRITE DEFAULT-LESS-THAN-2))
     (398 62 (:REWRITE RATIONALP-X))
     (390 86 (:REWRITE |(+ c (+ d x))|))
     (278 228 (:REWRITE DEFAULT-LESS-THAN-1))
     (258 6 (:REWRITE |(< (+ (- c) x) y)|))
     (246 246 (:TYPE-PRESCRIPTION LEN))
     (236 236 (:REWRITE DEFAULT-PLUS-1))
     (234 234 (:REWRITE THE-FLOOR-BELOW))
     (234 234 (:REWRITE THE-FLOOR-ABOVE))
     (228 228
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (228 228
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (214 152
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (214 152
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (198 43 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
     (194 152 (:REWRITE SIMPLIFY-SUMS-<))
     (168 24 (:DEFINITION LEN))
     (158 14
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (152 152
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (152 152 (:REWRITE INTEGERP-<-CONSTANT))
     (152 152 (:REWRITE CONSTANT-<-INTEGERP))
     (152 152
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (152 152
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (152 152
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (152 152
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (152 152 (:REWRITE |(< c (- x))|))
     (152 152
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (152 152
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (152 152
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (152 152
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (152 152 (:REWRITE |(< (/ x) (/ y))|))
     (152 152 (:REWRITE |(< (- x) c)|))
     (152 152 (:REWRITE |(< (- x) (- y))|))
     (134 134 (:TYPE-PRESCRIPTION NFIX))
     (122 122 (:REWRITE REDUCE-INTEGERP-+))
     (122 122 (:REWRITE INTEGERP-MINUS-X))
     (122 122 (:META META-INTEGERP-CORRECT))
     (112 112 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (102 4 (:REWRITE IFIX-POSITIVE-TO-NON-ZP))
     (68 68
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (68 68 (:REWRITE NORMALIZE-ADDENDS))
     (62 62 (:REWRITE REDUCE-RATIONALP-+))
     (62 62 (:REWRITE REDUCE-RATIONALP-*))
     (62 62 (:REWRITE RATIONALP-MINUS-X))
     (62 62 (:META META-RATIONALP-CORRECT))
     (60 60 (:REWRITE |(< (+ c/d x) y)|))
     (54 54 (:REWRITE |(< (* x y) 0)|))
     (38 38 (:REWRITE |(< x (+ c/d y))|))
     (38 38 (:REWRITE |(< 0 (* x y))|))
     (36 36 (:TYPE-PRESCRIPTION NATP))
     (36 36 (:REWRITE DEFAULT-CDR))
     (34 14 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (34 14
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (30 30 (:LINEAR LEQ-POSITION-EQUAL-LEN))
     (22 22
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (22 22
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (22 22 (:REWRITE |(< y (+ (- c) x))|))
     (22 22 (:REWRITE |(< 0 (/ x))|))
     (18 18
         (:REWRITE INEQUALITY-WITH-NFIX-HYP-2))
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
     (12 12 (:REWRITE ZP-OPEN))
     (12 12 (:REWRITE DEFAULT-CAR)))
(LL2::OCCUR-ARR-ITER-INT-EQUIV-CONGRUENCE-ON-IX)
(LL2::OCCUR-ARR-TAILREC-IS-OCCUR-ARR-ITER)
(LL2::OCCUR-ARR$INLINE)
(LL2::HYPS)
(LL2::INTEGER-LISTP-NTH
     (337 6 (:REWRITE NTH-WITH-LARGE-INDEX))
     (126 33 (:REWRITE DEFAULT-LESS-THAN-1))
     (81 30
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (47 33 (:REWRITE DEFAULT-LESS-THAN-2))
     (43 23 (:REWRITE DEFAULT-PLUS-2))
     (36 26
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (36 26 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (34 26 (:REWRITE SIMPLIFY-SUMS-<))
     (33 33 (:REWRITE THE-FLOOR-BELOW))
     (33 33 (:REWRITE THE-FLOOR-ABOVE))
     (30 30
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (30 30
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (30 26
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (26 26 (:REWRITE INTEGERP-<-CONSTANT))
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
     (23 23 (:REWRITE DEFAULT-PLUS-1))
     (21 21 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (20 20
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (20 20 (:REWRITE NORMALIZE-ADDENDS))
     (16 4 (:REWRITE NATP-WHEN-INTEGERP))
     (15 15 (:REWRITE REDUCE-INTEGERP-+))
     (15 15 (:REWRITE INTEGERP-MINUS-X))
     (15 15 (:META META-INTEGERP-CORRECT))
     (15 15 (:LINEAR LEQ-POSITION-EQUAL-LEN))
     (15 1 (:REWRITE |(+ y (+ x z))|))
     (12 12 (:REWRITE |(< 0 (* x y))|))
     (11 11
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (11 11
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (11 11 (:REWRITE |(< 0 (/ x))|))
     (10 10 (:REWRITE DEFAULT-CDR))
     (10 10 (:REWRITE DEFAULT-CAR))
     (8 8 (:REWRITE |(< x (+ c/d y))|))
     (7 7 (:REWRITE |(< y (+ (- c) x))|))
     (6 6 (:REWRITE ACL2-NUMBERP-X))
     (6 1 (:REWRITE |(+ c (+ d x))|))
     (5 5 (:REWRITE NFIX-WHEN-NOT-NATP))
     (5 5 (:REWRITE NFIX-WHEN-NATP))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (4 4 (:REWRITE |(< (/ x) 0)|))
     (4 4 (:REWRITE |(< (* x y) 0)|))
     (3 3 (:REWRITE |(< (+ c/d x) y)|))
     (2 1 (:REWRITE |(+ 0 x)|)))
(LL2::INTEGER-LISTP-UPDATE-NTH
     (3491 29 (:REWRITE LL2::UPDATE-NTH-REDUNDANT))
     (2857 43 (:REWRITE NTH-WITH-LARGE-INDEX))
     (1168 36 (:REWRITE ZP-WHEN-GT-0))
     (892 23 (:REWRITE |(< (+ (- c) x) y)|))
     (632 258 (:REWRITE DEFAULT-LESS-THAN-1))
     (409 250 (:REWRITE DEFAULT-PLUS-2))
     (354 258 (:REWRITE DEFAULT-LESS-THAN-2))
     (315 35 (:REWRITE NFIX-WHEN-NOT-NATP))
     (263 35 (:REWRITE NFIX-WHEN-NATP))
     (259 190
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (259 190
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (258 258 (:REWRITE THE-FLOOR-BELOW))
     (258 258 (:REWRITE THE-FLOOR-ABOVE))
     (250 250 (:REWRITE DEFAULT-PLUS-1))
     (246 246
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (246 246
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (245 190 (:REWRITE SIMPLIFY-SUMS-<))
     (204 190
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (202 163 (:REWRITE DEFAULT-CDR))
     (190 190 (:REWRITE INTEGERP-<-CONSTANT))
     (190 190 (:REWRITE CONSTANT-<-INTEGERP))
     (190 190
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (190 190
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (190 190
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (190 190
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (190 190 (:REWRITE |(< c (- x))|))
     (190 190
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (190 190
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (190 190
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (190 190
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (190 190 (:REWRITE |(< (/ x) (/ y))|))
     (190 190 (:REWRITE |(< (- x) c)|))
     (190 190 (:REWRITE |(< (- x) (- y))|))
     (152 152
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (152 152 (:REWRITE NORMALIZE-ADDENDS))
     (149 107 (:REWRITE DEFAULT-CAR))
     (136 136 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (112 48 (:REWRITE ACL2-NUMBERP-X))
     (105 24
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (94 94 (:REWRITE REDUCE-INTEGERP-+))
     (94 94 (:REWRITE INTEGERP-MINUS-X))
     (94 94 (:META META-INTEGERP-CORRECT))
     (88 88 (:REWRITE |(< 0 (* x y))|))
     (87 8 (:REWRITE LL2::INTEGER-LISTP-NTH))
     (74 74 (:LINEAR LEQ-POSITION-EQUAL-LEN))
     (70 70
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (70 70
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (70 70 (:REWRITE |(< 0 (/ x))|))
     (69 69 (:REWRITE |(< x (+ c/d y))|))
     (51 51 (:REWRITE |(< y (+ (- c) x))|))
     (41 24 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (41 24
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (40 40 (:REWRITE |(< (+ c/d x) y)|))
     (32 8 (:REWRITE RATIONALP-X))
     (31 31 (:REWRITE |(< (* x y) 0)|))
     (24 24
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (24 24
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (24 24
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (24 24 (:REWRITE |(equal c (/ x))|))
     (24 24 (:REWRITE |(equal c (- x))|))
     (24 24 (:REWRITE |(equal (/ x) c)|))
     (24 24 (:REWRITE |(equal (/ x) (/ y))|))
     (24 24 (:REWRITE |(equal (- x) c)|))
     (24 24 (:REWRITE |(equal (- x) (- y))|))
     (14 14
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (14 14
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (14 14 (:REWRITE |(< (/ x) 0)|))
     (8 8 (:REWRITE REDUCE-RATIONALP-+))
     (8 8 (:REWRITE REDUCE-RATIONALP-*))
     (8 8 (:REWRITE RATIONALP-MINUS-X))
     (8 8 (:META META-RATIONALP-CORRECT))
     (6 6
        (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
     (2 2
        (:REWRITE INEQUALITY-WITH-NFIX-HYP-2)))
(LL2::OCCURRENCES-PROGRAMP)
(LL2::OCCURRENCES-PROGRAMP-PRESERVED
     (21 3
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (20 4 (:REWRITE ACL2-NUMBERP-X))
     (8 2 (:REWRITE RATIONALP-X))
     (5 3
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
     (3 1 (:REWRITE LL2::WR-REDUNDANT))
     (2 2 (:TYPE-PRESCRIPTION LL2::SP))
     (2 2 (:REWRITE REDUCE-RATIONALP-+))
     (2 2 (:REWRITE REDUCE-RATIONALP-*))
     (2 2 (:REWRITE REDUCE-INTEGERP-+))
     (2 2 (:REWRITE RATIONALP-MINUS-X))
     (2 2 (:REWRITE INTEGERP-MINUS-X))
     (2 2 (:META META-RATIONALP-CORRECT))
     (2 2 (:META META-INTEGERP-CORRECT)))
(LL2::LEN-OCCURRENCES-PROGRAMP)
(LL2::RESOLVE-NEXT-INST1 (39 26
                             (:TYPE-PRESCRIPTION LL2::INTEGER-LISTP-NTH))
                         (13 13 (:TYPE-PRESCRIPTION INTEGER-LISTP)))
(LL2::LOOP-PC-P)
(LL2::LOOP-INV (16 8
                   (:TYPE-PRESCRIPTION LL2::INTEGER-LISTP-NTH))
               (8 8 (:TYPE-PRESCRIPTION INTEGER-LISTP)))
(LL2::PROGRAM-INV (38 19
                      (:TYPE-PRESCRIPTION LL2::INTEGER-LISTP-NTH))
                  (19 19 (:TYPE-PRESCRIPTION INTEGER-LISTP)))
(LL2::CLK-8-MEASURE (18 9
                        (:TYPE-PRESCRIPTION LL2::INTEGER-LISTP-NTH))
                    (9 9 (:TYPE-PRESCRIPTION INTEGER-LISTP)))
(CODEWALKER-WRAPPER
     (1148 17 (:REWRITE NATP-WHEN-INTEGERP))
     (655 12 (:REWRITE NFIX-WHEN-NOT-NATP))
     (334 4 (:REWRITE O<=-O-FINP-DEF))
     (298 44 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (282 2
          (:REWRITE |a < b  <=>  c+a < c+b :l1|))
     (222 84 (:REWRITE DEFAULT-LESS-THAN-1))
     (158 129 (:REWRITE DEFAULT-PLUS-2))
     (137 129 (:REWRITE DEFAULT-PLUS-1))
     (97 49 (:REWRITE NORMALIZE-ADDENDS))
     (89 84 (:REWRITE DEFAULT-LESS-THAN-2))
     (84 84 (:REWRITE THE-FLOOR-BELOW))
     (84 84 (:REWRITE THE-FLOOR-ABOVE))
     (80 80
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (80 80
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (73 73 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (68 63
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (66 63
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (66 63 (:REWRITE |(< (- x) (- y))|))
     (63 63
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (63 63
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (63 63
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (63 63 (:REWRITE |(< c (- x))|))
     (63 63
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (63 63
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (63 63
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (63 63 (:REWRITE |(< (/ x) (/ y))|))
     (56 44
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (52 20 (:REWRITE ACL2-NUMBERP-X))
     (44 44
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (44 44 (:REWRITE INTEGERP-<-CONSTANT))
     (44 44 (:REWRITE CONSTANT-<-INTEGERP))
     (41 41
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (40 4
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (38 38 (:REWRITE SIMPLIFY-SUMS-<))
     (37 37 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (34 30 (:REWRITE DEFAULT-MINUS))
     (23 23 (:REWRITE |(< (* x y) 0)|))
     (21 21 (:REWRITE |(< (+ c/d x) y)|))
     (16 8 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
     (16 4 (:REWRITE RATIONALP-X))
     (14 14 (:DEFINITION FIX))
     (10 2 (:REWRITE O-FIRST-EXPT-<))
     (8 8 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (8 8 (:REWRITE REDUCE-INTEGERP-+))
     (8 8 (:REWRITE INTEGERP-MINUS-X))
     (8 8 (:REWRITE |(< x (+ c/d y))|))
     (8 8 (:REWRITE |(< (/ x) 0)|))
     (8 8 (:REWRITE |(+ x (- x))|))
     (8 8 (:META META-INTEGERP-CORRECT))
     (8 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (8 4
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (6 6 (:TYPE-PRESCRIPTION LL2::STEP))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (6 6 (:REWRITE |(< y (+ (- c) x))|))
     (6 6 (:REWRITE |(< 0 (/ x))|))
     (6 6 (:REWRITE |(< 0 (* x y))|))
     (6 4 (:REWRITE O-INFP-O-FINP-O<=))
     (6 4 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
     (6 4 (:REWRITE AC-<))
     (5 5 (:REWRITE INEQUALITY-WITH-NFIX-HYP-1))
     (4 4 (:REWRITE |a < b & b < c  =>  a < c|))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (4 4 (:REWRITE REDUCE-RATIONALP-+))
     (4 4 (:REWRITE REDUCE-RATIONALP-*))
     (4 4
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (4 4
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (4 4 (:REWRITE RATIONALP-MINUS-X))
     (4 4 (:REWRITE INEQUALITY-WITH-NFIX-HYP-2))
     (4 4
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (4 4 (:REWRITE DEFAULT-CDR))
     (4 4 (:REWRITE DEFAULT-CAR))
     (4 4 (:REWRITE |(equal c (/ x))|))
     (4 4 (:REWRITE |(equal c (- x))|))
     (4 4 (:REWRITE |(equal (/ x) c)|))
     (4 4 (:REWRITE |(equal (/ x) (/ y))|))
     (4 4 (:REWRITE |(equal (- x) c)|))
     (4 4 (:REWRITE |(equal (- x) (- y))|))
     (4 4 (:REWRITE |(< (+ (- c) x) y)|))
     (4 4 (:META META-RATIONALP-CORRECT))
     (2 2
        (:TYPE-PRESCRIPTION CONSP-REVAPPEND . 2))
     (2 2 (:REWRITE O-FIRST-COEFF-<)))
(CODEWALKER-WRAPPER-RULE-1
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
     (1 1 (:REWRITE SIMPLIFY-SUMS-<))
     (1 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (1 1 (:REWRITE REDUCE-INTEGERP-+))
     (1 1 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (1 1 (:REWRITE INTEGERP-MINUS-X))
     (1 1 (:META META-INTEGERP-CORRECT)))
(CODEWALKER-WRAPPER-RULE-2
     (57 17 (:REWRITE ACL2-NUMBERP-X))
     (50 5
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (44 22
         (:TYPE-PRESCRIPTION TRUE-LISTP-MEMBER-EQUAL))
     (37 1 (:REWRITE NATP-WHEN-GTE-0))
     (36 5 (:REWRITE DEFAULT-LESS-THAN-1))
     (22 22 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (20 5 (:REWRITE RATIONALP-X))
     (15 15 (:REWRITE DEFAULT-CDR))
     (15 15 (:REWRITE DEFAULT-CAR))
     (10 5 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (10 5
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (6 6 (:REWRITE REDUCE-INTEGERP-+))
     (6 6 (:REWRITE INTEGERP-MINUS-X))
     (6 6 (:META META-INTEGERP-CORRECT))
     (5 5 (:REWRITE THE-FLOOR-BELOW))
     (5 5 (:REWRITE THE-FLOOR-ABOVE))
     (5 5 (:REWRITE REDUCE-RATIONALP-+))
     (5 5 (:REWRITE REDUCE-RATIONALP-*))
     (5 5
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (5 5
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (5 5 (:REWRITE RATIONALP-MINUS-X))
     (5 5
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (5 5 (:REWRITE DEFAULT-LESS-THAN-2))
     (5 5 (:REWRITE |(equal c (/ x))|))
     (5 5 (:REWRITE |(equal c (- x))|))
     (5 5 (:REWRITE |(equal (/ x) c)|))
     (5 5 (:REWRITE |(equal (/ x) (/ y))|))
     (5 5 (:REWRITE |(equal (- x) c)|))
     (5 5 (:REWRITE |(equal (- x) (- y))|))
     (5 5 (:META META-RATIONALP-CORRECT))
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
     (4 1 (:REWRITE NATP-WHEN-INTEGERP))
     (2 2 (:REWRITE CODEWALKER-WRAPPER-RULE-1))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (1 1 (:REWRITE |(< (/ x) 0)|))
     (1 1 (:REWRITE |(< (* x y) 0)|)))
(CODEWALKER-WRAPPER-IGNORES-SPLITTERS
     (6222 74 (:REWRITE LL2::STEP-OPENER))
     (5916 58 (:DEFINITION LL2::NEXT-INST))
     (5568 58 (:REWRITE NTH-WITH-LARGE-INDEX))
     (2552 58 (:REWRITE NFIX-WHEN-NATP))
     (2376 334 (:REWRITE DEFAULT-LESS-THAN-1))
     (2370 270
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (1431 52 (:REWRITE CODEWALKER-WRAPPER-RULE-2))
     (1381 52 (:REWRITE CODEWALKER-WRAPPER-RULE-1))
     (1054 342 (:REWRITE ACL2-NUMBERP-X))
     (620 62
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (616 56 (:REWRITE |(+ y (+ x z))|))
     (464 464 (:TYPE-PRESCRIPTION LEN))
     (406 406 (:TYPE-PRESCRIPTION NFIX))
     (392 334 (:REWRITE DEFAULT-LESS-THAN-2))
     (356 89 (:REWRITE RATIONALP-X))
     (334 334 (:REWRITE THE-FLOOR-BELOW))
     (334 334 (:REWRITE THE-FLOOR-ABOVE))
     (330 214 (:REWRITE SIMPLIFY-SUMS-<))
     (330 214
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (330 214
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (320 128 (:REWRITE NATP-WHEN-INTEGERP))
     (302 302 (:REWRITE DEFAULT-PLUS-1))
     (290 58 (:REWRITE NFIX-WHEN-NOT-NATP))
     (270 270
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (270 270
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (232 232
          (:TYPE-PRESCRIPTION LL2::OCCURRENCES-PROGRAMP))
     (232 116
          (:TYPE-PRESCRIPTION LL2::INTEGER-LISTP-NTH))
     (214 214
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (214 214 (:REWRITE INTEGERP-<-CONSTANT))
     (214 214 (:REWRITE CONSTANT-<-INTEGERP))
     (214 214
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (214 214
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (214 214
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (214 214
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (214 214 (:REWRITE |(< c (- x))|))
     (214 214
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (214 214
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (214 214
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (214 214
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (214 214 (:REWRITE |(< (/ x) (/ y))|))
     (214 214 (:REWRITE |(< (- x) c)|))
     (214 214 (:REWRITE |(< (- x) (- y))|))
     (186 186 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (174 58 (:REWRITE LL2::RESOLVE-NEXT-INST1))
     (174 58
          (:REWRITE LL2::LEN-OCCURRENCES-PROGRAMP))
     (157 157 (:REWRITE REDUCE-INTEGERP-+))
     (157 157 (:REWRITE INTEGERP-MINUS-X))
     (157 157 (:META META-INTEGERP-CORRECT))
     (124 62 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (124 62
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (116 116 (:TYPE-PRESCRIPTION INTEGER-LISTP))
     (115 115 (:REWRITE DEFAULT-CDR))
     (115 115 (:REWRITE DEFAULT-CAR))
     (114 114
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (114 114 (:REWRITE NORMALIZE-ADDENDS))
     (89 89 (:REWRITE REDUCE-RATIONALP-+))
     (89 89 (:REWRITE REDUCE-RATIONALP-*))
     (89 89 (:REWRITE RATIONALP-MINUS-X))
     (89 89 (:META META-RATIONALP-CORRECT))
     (77 77 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (66 66 (:REWRITE |(< (+ c/d x) y)|))
     (64 64
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (64 64
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (64 64 (:REWRITE |(< (/ x) 0)|))
     (64 64 (:REWRITE |(< (* x y) 0)|))
     (62 62
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (62 62
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (62 62
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (62 62 (:REWRITE |(equal c (/ x))|))
     (62 62 (:REWRITE |(equal c (- x))|))
     (62 62 (:REWRITE |(equal (/ x) c)|))
     (62 62 (:REWRITE |(equal (/ x) (/ y))|))
     (62 62 (:REWRITE |(equal (- x) c)|))
     (62 62 (:REWRITE |(equal (- x) (- y))|))
     (58 58
         (:REWRITE INEQUALITY-WITH-NFIX-HYP-2))
     (58 58 (:LINEAR LEQ-POSITION-EQUAL-LEN))
     (58 58 (:DEFINITION LL2::PROGRAM))
     (58 58 (:DEFINITION LL2::PC))
     (56 56 (:REWRITE |(+ 0 x)|))
     (32 4 (:REWRITE |(+ x (if a b c))|))
     (10 10 (:REWRITE |(< (+ (- c) x) y)|)))
(CODEWALKER-WRAPPER-RULE-3
     (10403 121 (:REWRITE LL2::STEP-OPENER))
     (9894 97 (:DEFINITION LL2::NEXT-INST))
     (9312 97 (:REWRITE NTH-WITH-LARGE-INDEX))
     (4268 97 (:REWRITE NFIX-WHEN-NATP))
     (3982 202 (:REWRITE NATP-WHEN-GTE-0))
     (3872 520 (:REWRITE DEFAULT-LESS-THAN-1))
     (3715 415
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (2734 90 (:DEFINITION REVAPPEND))
     (2124 56 (:REWRITE CODEWALKER-WRAPPER-RULE-1))
     (2080 56 (:REWRITE CODEWALKER-WRAPPER-RULE-2))
     (1428 500 (:REWRITE ACL2-NUMBERP-X))
     (968 88 (:REWRITE |(+ y (+ x z))|))
     (860 86
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (776 776 (:TYPE-PRESCRIPTION LEN))
     (679 679 (:TYPE-PRESCRIPTION NFIX))
     (617 520 (:REWRITE DEFAULT-LESS-THAN-2))
     (521 327 (:REWRITE SIMPLIFY-SUMS-<))
     (521 327
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (521 327
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (520 520 (:REWRITE THE-FLOOR-BELOW))
     (520 520 (:REWRITE THE-FLOOR-ABOVE))
     (517 202 (:REWRITE NATP-WHEN-INTEGERP))
     (485 97 (:REWRITE NFIX-WHEN-NOT-NATP))
     (482 114 (:REWRITE |(+ c (+ d x))|))
     (466 466 (:REWRITE DEFAULT-PLUS-1))
     (464 116 (:REWRITE RATIONALP-X))
     (415 415
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (415 415
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (388 388
          (:TYPE-PRESCRIPTION LL2::OCCURRENCES-PROGRAMP))
     (388 194
          (:TYPE-PRESCRIPTION LL2::INTEGER-LISTP-NTH))
     (327 327
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (327 327 (:REWRITE INTEGERP-<-CONSTANT))
     (327 327 (:REWRITE CONSTANT-<-INTEGERP))
     (327 327
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (327 327
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (327 327
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (327 327
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (327 327 (:REWRITE |(< c (- x))|))
     (327 327
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (327 327
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (327 327
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (327 327
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (327 327 (:REWRITE |(< (/ x) (/ y))|))
     (327 327 (:REWRITE |(< (- x) c)|))
     (327 327 (:REWRITE |(< (- x) (- y))|))
     (291 97 (:REWRITE LL2::RESOLVE-NEXT-INST1))
     (291 97
          (:REWRITE LL2::LEN-OCCURRENCES-PROGRAMP))
     (283 283 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (221 221 (:REWRITE REDUCE-INTEGERP-+))
     (221 221 (:REWRITE INTEGERP-MINUS-X))
     (221 221 (:META META-INTEGERP-CORRECT))
     (194 194 (:TYPE-PRESCRIPTION INTEGER-LISTP))
     (172 86 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (172 86
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (169 169
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (169 169 (:REWRITE NORMALIZE-ADDENDS))
     (138 138 (:REWRITE DEFAULT-CAR))
     (137 137 (:REWRITE DEFAULT-CDR))
     (116 116 (:REWRITE REDUCE-RATIONALP-+))
     (116 116 (:REWRITE REDUCE-RATIONALP-*))
     (116 116 (:REWRITE RATIONALP-MINUS-X))
     (116 116 (:META META-RATIONALP-CORRECT))
     (111 111 (:TYPE-PRESCRIPTION LL2::STEP))
     (105 105
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (105 105
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (105 105 (:REWRITE |(< (/ x) 0)|))
     (105 105 (:REWRITE |(< (* x y) 0)|))
     (104 104 (:REWRITE |(< (+ c/d x) y)|))
     (97 97
         (:REWRITE INEQUALITY-WITH-NFIX-HYP-2))
     (97 97 (:LINEAR LEQ-POSITION-EQUAL-LEN))
     (97 97 (:DEFINITION LL2::PROGRAM))
     (97 97 (:DEFINITION LL2::PC))
     (88 88 (:REWRITE |(+ 0 x)|))
     (86 86
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (86 86
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (86 86
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (86 86 (:REWRITE |(equal c (/ x))|))
     (86 86 (:REWRITE |(equal c (- x))|))
     (86 86 (:REWRITE |(equal (/ x) c)|))
     (86 86 (:REWRITE |(equal (/ x) (/ y))|))
     (86 86 (:REWRITE |(equal (- x) c)|))
     (86 86 (:REWRITE |(equal (- x) (- y))|))
     (75 75 (:REWRITE CDR-CONS))
     (56 7 (:REWRITE |(+ x (if a b c))|))
     (16 16 (:REWRITE |(< (+ (- c) x) y)|)))
(LL2::CLK-PREAMBLE-0 (8 4
                        (:TYPE-PRESCRIPTION LL2::INTEGER-LISTP-NTH))
                     (4 4 (:TYPE-PRESCRIPTION INTEGER-LISTP)))
(LL2::SEM-PREAMBLE-0 (26 26 (:TYPE-PRESCRIPTION LL2::WR))
                     (12 6
                         (:TYPE-PRESCRIPTION LL2::INTEGER-LISTP-NTH))
                     (6 6 (:TYPE-PRESCRIPTION INTEGER-LISTP)))
(LL2::SEM-PREAMBLE-0-CORRECT
     (6019 39 (:REWRITE LL2::UPDATE-NTH-REDUNDANT))
     (5796 92 (:REWRITE NTH-WITH-LARGE-INDEX))
     (4860 180 (:REWRITE LEN-UPDATE-NTH1))
     (1096 690
           (:TYPE-PRESCRIPTION TRUE-LISTP-UPDATE-NTH))
     (690 690 (:TYPE-PRESCRIPTION UPDATE-NTH))
     (634 395 (:TYPE-PRESCRIPTION LL2::STEP))
     (456 456 (:TYPE-PRESCRIPTION LL2::WR))
     (289 276
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (289 276
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (288 278 (:REWRITE DEFAULT-LESS-THAN-1))
     (284 276 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (281 278 (:REWRITE DEFAULT-LESS-THAN-2))
     (281 278
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (278 278 (:REWRITE THE-FLOOR-BELOW))
     (278 278 (:REWRITE THE-FLOOR-ABOVE))
     (278 278
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (278 278
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (278 278
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (278 278 (:REWRITE INTEGERP-<-CONSTANT))
     (278 278 (:REWRITE CONSTANT-<-INTEGERP))
     (278 278
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (278 278
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (278 278
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (278 278 (:REWRITE |(< c (- x))|))
     (278 278
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (278 278
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (278 278
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (278 278
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (278 278 (:REWRITE |(< (/ x) (/ y))|))
     (278 278 (:REWRITE |(< (- x) c)|))
     (278 278 (:REWRITE |(< (- x) (- y))|))
     (276 276 (:REWRITE SIMPLIFY-SUMS-<))
     (229 83
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (176 83
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (155 83 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (144 24 (:REWRITE DEFAULT-CDR))
     (144 24 (:REWRITE DEFAULT-CAR))
     (114 3 (:REWRITE NATP-WHEN-GTE-0))
     (96 96 (:TYPE-PRESCRIPTION LL2::PUSH))
     (83 83
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (83 83
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (83 83
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (83 83 (:REWRITE |(equal c (/ x))|))
     (83 83 (:REWRITE |(equal c (- x))|))
     (83 83 (:REWRITE |(equal (/ x) c)|))
     (83 83 (:REWRITE |(equal (/ x) (/ y))|))
     (83 83 (:REWRITE |(equal (- x) c)|))
     (83 83 (:REWRITE |(equal (- x) (- y))|))
     (76 12 (:REWRITE ACL2-NUMBERP-X))
     (54 26 (:REWRITE UPDATE-NTH-UPDATE-NTH . 1))
     (49 49 (:TYPE-PRESCRIPTION LL2::LL2))
     (40 40
         (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
     (40 40
         (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
     (33 33
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (32 5 (:REWRITE RATIONALP-X))
     (23 7 (:REWRITE O-INFP->NEQ-0))
     (11 11
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (11 11
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (11 11 (:REWRITE |(< (/ x) 0)|))
     (11 11 (:REWRITE |(< (* x y) 0)|))
     (9 9 (:TYPE-PRESCRIPTION O-FINP))
     (9 3 (:REWRITE O-FIRST-EXPT-O-INFP))
     (6 3 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (5 5 (:REWRITE REDUCE-RATIONALP-+))
     (5 5 (:REWRITE REDUCE-RATIONALP-*))
     (5 5 (:REWRITE REDUCE-INTEGERP-+))
     (5 5 (:REWRITE RATIONALP-MINUS-X))
     (5 5 (:REWRITE INTEGERP-MINUS-X))
     (5 5 (:REWRITE |(< 0 (/ x))|))
     (5 5 (:REWRITE |(< 0 (* x y))|))
     (5 5 (:META META-RATIONALP-CORRECT))
     (5 5 (:META META-INTEGERP-CORRECT))
     (4 4 (:LINEAR LEQ-POSITION-EQUAL-LEN))
     (3 3 (:TYPE-PRESCRIPTION LL2::!PC)))
(LL2::SEM-PREAMBLE-0-PRESERVES-HYPS
     (4514 16 (:REWRITE LL2::UPDATE-NTH-REDUNDANT))
     (3381 73 (:REWRITE NTH-WITH-LARGE-INDEX))
     (534 273 (:REWRITE DEFAULT-LESS-THAN-1))
     (408 11 (:REWRITE NATP-WHEN-GTE-0))
     (287 273 (:REWRITE DEFAULT-LESS-THAN-2))
     (285 258
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (281 258
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (273 273 (:REWRITE THE-FLOOR-BELOW))
     (273 273 (:REWRITE THE-FLOOR-ABOVE))
     (272 265
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (266 258 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (265 265
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (265 265
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (265 265
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (265 265 (:REWRITE INTEGERP-<-CONSTANT))
     (265 265 (:REWRITE CONSTANT-<-INTEGERP))
     (265 265
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (265 265
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (265 265
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (265 265 (:REWRITE |(< c (- x))|))
     (265 265
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (265 265
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (265 265
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (265 265
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (265 265 (:REWRITE |(< (/ x) (/ y))|))
     (265 265 (:REWRITE |(< (- x) c)|))
     (265 265 (:REWRITE |(< (- x) (- y))|))
     (264 258 (:REWRITE SIMPLIFY-SUMS-<))
     (244 8 (:REWRITE LL2::WR-REDUNDANT))
     (40 27
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (36 12 (:REWRITE UPDATE-NTH-UPDATE-NTH . 1))
     (32 27
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (31 31
         (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
     (31 31
         (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
     (27 27 (:REWRITE SIMPLIFY-SUMS-EQUAL))
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
     (22 22
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (22 22
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (22 22 (:REWRITE |(< (/ x) 0)|))
     (22 22 (:REWRITE |(< (* x y) 0)|))
     (17 17
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (16 16 (:REWRITE ACL2-NUMBERP-X))
     (14 14 (:LINEAR LEQ-POSITION-EQUAL-LEN))
     (8 8 (:REWRITE REDUCE-INTEGERP-+))
     (8 8 (:REWRITE INTEGERP-MINUS-X))
     (8 8 (:META META-INTEGERP-CORRECT))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (4 4 (:REWRITE |(< 0 (/ x))|))
     (4 4 (:REWRITE |(< 0 (* x y))|))
     (4 3 (:REWRITE O-INFP->NEQ-0)))
(LL2::SEM-PREAMBLE-0-PRESERVES-PROGRAM-INV
     (12835 166 (:REWRITE NTH-WITH-LARGE-INDEX))
     (8478 314 (:REWRITE LEN-UPDATE-NTH1))
     (4738 16 (:REWRITE LL2::UPDATE-NTH-REDUNDANT))
     (2012 39 (:REWRITE NATP-WHEN-GTE-0))
     (658 574 (:REWRITE DEFAULT-LESS-THAN-2))
     (630 539
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (630 539
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (574 574 (:REWRITE THE-FLOOR-BELOW))
     (574 574 (:REWRITE THE-FLOOR-ABOVE))
     (543 539
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (541 539 (:REWRITE SIMPLIFY-SUMS-<))
     (541 539
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (539 539
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (539 539
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (539 539
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (539 539 (:REWRITE INTEGERP-<-CONSTANT))
     (539 539 (:REWRITE CONSTANT-<-INTEGERP))
     (539 539
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (539 539
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (539 539
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (539 539 (:REWRITE |(< c (- x))|))
     (539 539
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (539 539
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (539 539
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (539 539
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (539 539 (:REWRITE |(< (/ x) (/ y))|))
     (539 539 (:REWRITE |(< (- x) c)|))
     (539 539 (:REWRITE |(< (- x) (- y))|))
     (537 533 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (496 8 (:REWRITE LL2::WR-REDUNDANT))
     (420 164
          (:TYPE-PRESCRIPTION TRUE-LISTP-UPDATE-NTH))
     (222 76 (:REWRITE ACL2-NUMBERP-X))
     (164 164 (:TYPE-PRESCRIPTION UPDATE-NTH))
     (120 120 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (114 114
          (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
     (114 114
          (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
     (105 105 (:LINEAR LEQ-POSITION-EQUAL-LEN))
     (85 40 (:REWRITE LL2::INTEGER-LISTP-NTH))
     (50 27
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (48 48 (:REWRITE REDUCE-INTEGERP-+))
     (48 48 (:REWRITE INTEGERP-MINUS-X))
     (48 48 (:META META-INTEGERP-CORRECT))
     (44 44
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (44 44
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (44 44 (:REWRITE |(< (/ x) 0)|))
     (44 44 (:REWRITE |(< (* x y) 0)|))
     (42 27
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (36 12 (:REWRITE UPDATE-NTH-UPDATE-NTH . 1))
     (33 33
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (33 33
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (33 33 (:REWRITE |(< 0 (/ x))|))
     (33 33 (:REWRITE |(< 0 (* x y))|))
     (29 27 (:REWRITE SIMPLIFY-SUMS-EQUAL))
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
     (17 17
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (16 4 (:REWRITE RATIONALP-X))
     (4 4 (:REWRITE LL2::SP-WR))
     (4 4 (:REWRITE REDUCE-RATIONALP-+))
     (4 4 (:REWRITE REDUCE-RATIONALP-*))
     (4 4 (:REWRITE RATIONALP-MINUS-X))
     (4 4 (:META META-RATIONALP-CORRECT))
     (4 3 (:REWRITE O-INFP->NEQ-0)))
(LL2::SEM-PREAMBLE-0-PRESERVES-OCCURRENCES-PROGRAMP
     (4738 16 (:REWRITE LL2::UPDATE-NTH-REDUNDANT))
     (3297 52 (:REWRITE NTH-WITH-LARGE-INDEX))
     (2916 108 (:REWRITE LEN-UPDATE-NTH1))
     (1284 24 (:REWRITE NTH-UPDATE-NTH))
     (496 8 (:REWRITE LL2::WR-REDUNDANT))
     (420 164
          (:TYPE-PRESCRIPTION TRUE-LISTP-UPDATE-NTH))
     (292 189 (:REWRITE DEFAULT-LESS-THAN-1))
     (223 6 (:REWRITE NATP-WHEN-GTE-0))
     (199 186
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (195 186
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (192 189 (:REWRITE DEFAULT-LESS-THAN-2))
     (190 186
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (189 189 (:REWRITE THE-FLOOR-BELOW))
     (189 189 (:REWRITE THE-FLOOR-ABOVE))
     (188 186
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (188 180 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (186 186 (:REWRITE SIMPLIFY-SUMS-<))
     (186 186
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (186 186
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (186 186
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (186 186 (:REWRITE INTEGERP-<-CONSTANT))
     (186 186 (:REWRITE CONSTANT-<-INTEGERP))
     (186 186
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (186 186
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (186 186
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (186 186 (:REWRITE |(< c (- x))|))
     (186 186
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (186 186
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (186 186
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (186 186
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (186 186 (:REWRITE |(< (/ x) (/ y))|))
     (186 186 (:REWRITE |(< (- x) c)|))
     (186 186 (:REWRITE |(< (- x) (- y))|))
     (164 164 (:TYPE-PRESCRIPTION UPDATE-NTH))
     (120 120 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (50 27
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (42 27
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (36 12 (:REWRITE UPDATE-NTH-UPDATE-NTH . 1))
     (33 33 (:LINEAR LEQ-POSITION-EQUAL-LEN))
     (29 27 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (28 28
         (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
     (28 28
         (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
     (28 12 (:REWRITE ACL2-NUMBERP-X))
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
     (17 17
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (14 14
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (14 14
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (14 14 (:REWRITE |(< (/ x) 0)|))
     (14 14 (:REWRITE |(< (* x y) 0)|))
     (8 2 (:REWRITE RATIONALP-X))
     (5 5 (:REWRITE REDUCE-INTEGERP-+))
     (5 5 (:REWRITE INTEGERP-MINUS-X))
     (5 5 (:META META-INTEGERP-CORRECT))
     (4 4 (:REWRITE LL2::SP-WR))
     (4 4 (:REWRITE LL2::RD-WR))
     (4 3 (:REWRITE O-INFP->NEQ-0))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (3 3 (:REWRITE |(< 0 (/ x))|))
     (3 3 (:REWRITE |(< 0 (* x y))|))
     (2 2 (:REWRITE REDUCE-RATIONALP-+))
     (2 2 (:REWRITE REDUCE-RATIONALP-*))
     (2 2 (:REWRITE RATIONALP-MINUS-X))
     (2 2 (:META META-RATIONALP-CORRECT)))
(LL2::SEM-PREAMBLE-0-N-GE-1-PC
     (1129 4 (:REWRITE LL2::UPDATE-NTH-REDUNDANT))
     (1026 20 (:REWRITE NTH-WITH-LARGE-INDEX))
     (729 27 (:REWRITE LEN-UPDATE-NTH1))
     (318 6 (:REWRITE NTH-UPDATE-NTH))
     (113 3 (:REWRITE NATP-WHEN-GTE-0))
     (94 58 (:REWRITE DEFAULT-LESS-THAN-1))
     (62 56
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (62 56 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (61 2 (:REWRITE LL2::WR-REDUNDANT))
     (59 58 (:REWRITE DEFAULT-LESS-THAN-2))
     (58 58 (:REWRITE THE-FLOOR-BELOW))
     (58 58 (:REWRITE THE-FLOOR-ABOVE))
     (58 57
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (58 56 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (57 57
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (57 57
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (57 57
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (57 57 (:REWRITE INTEGERP-<-CONSTANT))
     (57 57 (:REWRITE CONSTANT-<-INTEGERP))
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
     (56 56 (:REWRITE SIMPLIFY-SUMS-<))
     (37 22
         (:TYPE-PRESCRIPTION TRUE-LISTP-UPDATE-NTH))
     (22 22 (:TYPE-PRESCRIPTION UPDATE-NTH))
     (14 14
         (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
     (14 14
         (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
     (9 6
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (9 3 (:REWRITE UPDATE-NTH-UPDATE-NTH . 1))
     (7 6
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
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
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (5 5 (:REWRITE |(< (/ x) 0)|))
     (5 5 (:REWRITE |(< (* x y) 0)|))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (2 2 (:REWRITE ACL2-NUMBERP-X))
     (2 2 (:REWRITE |(< 0 (/ x))|))
     (2 2 (:REWRITE |(< 0 (* x y))|))
     (2 2 (:LINEAR LEQ-POSITION-EQUAL-LEN))
     (1 1 (:REWRITE LL2::SP-WR))
     (1 1 (:REWRITE REDUCE-INTEGERP-+))
     (1 1 (:REWRITE INTEGERP-MINUS-X))
     (1 1 (:META META-INTEGERP-CORRECT)))
(LL2::PREAMBLE-INDEX-=-0
     (4958 63 (:REWRITE NTH-WITH-LARGE-INDEX))
     (4514 16 (:REWRITE LL2::UPDATE-NTH-REDUNDANT))
     (4266 158 (:REWRITE LEN-UPDATE-NTH1))
     (249 235
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (249 235
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (246 236 (:REWRITE DEFAULT-LESS-THAN-1))
     (243 235 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (240 236 (:REWRITE DEFAULT-LESS-THAN-2))
     (239 236
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (236 236 (:REWRITE THE-FLOOR-BELOW))
     (236 236 (:REWRITE THE-FLOOR-ABOVE))
     (236 236
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (236 236
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (236 236
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (236 236 (:REWRITE INTEGERP-<-CONSTANT))
     (236 236 (:REWRITE CONSTANT-<-INTEGERP))
     (236 236
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (236 236
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (236 236
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (236 236 (:REWRITE |(< c (- x))|))
     (236 236
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (236 236
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (236 236
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (236 236
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (236 236 (:REWRITE |(< (/ x) (/ y))|))
     (236 236 (:REWRITE |(< (- x) c)|))
     (236 236 (:REWRITE |(< (- x) (- y))|))
     (235 235 (:REWRITE SIMPLIFY-SUMS-<))
     (196 8 (:REWRITE LL2::WR-REDUNDANT))
     (148 88
          (:TYPE-PRESCRIPTION TRUE-LISTP-UPDATE-NTH))
     (114 3 (:REWRITE NATP-WHEN-GTE-0))
     (89 27
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (88 88 (:TYPE-PRESCRIPTION UPDATE-NTH))
     (55 8 (:REWRITE ACL2-NUMBERP-X))
     (50 27
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (36 12 (:REWRITE UPDATE-NTH-UPDATE-NTH . 1))
     (36 7 (:REWRITE O-INFP->NEQ-0))
     (35 35
         (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
     (35 35
         (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
     (27 27 (:REWRITE SIMPLIFY-SUMS-EQUAL))
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
     (25 4 (:REWRITE RATIONALP-X))
     (21 21
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (14 4 (:REWRITE O-FIRST-EXPT-O-INFP))
     (12 12 (:TYPE-PRESCRIPTION O-FINP))
     (11 11
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (11 11
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (11 11 (:REWRITE |(< (/ x) 0)|))
     (11 11 (:REWRITE |(< (* x y) 0)|))
     (10 4 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
     (5 5 (:LINEAR LEQ-POSITION-EQUAL-LEN))
     (4 4 (:REWRITE LL2::SP-WR))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (4 4 (:REWRITE REDUCE-RATIONALP-+))
     (4 4 (:REWRITE REDUCE-RATIONALP-*))
     (4 4 (:REWRITE REDUCE-INTEGERP-+))
     (4 4 (:REWRITE RATIONALP-MINUS-X))
     (4 4 (:REWRITE INTEGERP-MINUS-X))
     (4 4 (:REWRITE |(< 0 (/ x))|))
     (4 4 (:REWRITE |(< 0 (* x y))|))
     (4 4 (:META META-RATIONALP-CORRECT))
     (4 4 (:META META-INTEGERP-CORRECT))
     (3 1 (:REWRITE LL2::INTEGER-LISTP-NTH)))
(LL2::PREAMBLE-NUM-OCCUR-=-0
     (5072 65 (:REWRITE NTH-WITH-LARGE-INDEX))
     (4514 16 (:REWRITE LL2::UPDATE-NTH-REDUNDANT))
     (4320 160 (:REWRITE LEN-UPDATE-NTH1))
     (253 239
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (253 239
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (250 240 (:REWRITE DEFAULT-LESS-THAN-1))
     (247 239 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (244 240 (:REWRITE DEFAULT-LESS-THAN-2))
     (243 240
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (240 240 (:REWRITE THE-FLOOR-BELOW))
     (240 240 (:REWRITE THE-FLOOR-ABOVE))
     (240 240
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (240 240
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (240 240
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (240 240 (:REWRITE INTEGERP-<-CONSTANT))
     (240 240 (:REWRITE CONSTANT-<-INTEGERP))
     (240 240
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (240 240
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (240 240
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (240 240 (:REWRITE |(< c (- x))|))
     (240 240
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (240 240
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (240 240
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (240 240
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (240 240 (:REWRITE |(< (/ x) (/ y))|))
     (240 240 (:REWRITE |(< (- x) c)|))
     (240 240 (:REWRITE |(< (- x) (- y))|))
     (239 239 (:REWRITE SIMPLIFY-SUMS-<))
     (196 8 (:REWRITE LL2::WR-REDUNDANT))
     (148 88
          (:TYPE-PRESCRIPTION TRUE-LISTP-UPDATE-NTH))
     (114 3 (:REWRITE NATP-WHEN-GTE-0))
     (89 27
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (88 88 (:TYPE-PRESCRIPTION UPDATE-NTH))
     (55 8 (:REWRITE ACL2-NUMBERP-X))
     (50 27
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (36 12 (:REWRITE UPDATE-NTH-UPDATE-NTH . 1))
     (36 7 (:REWRITE O-INFP->NEQ-0))
     (35 35
         (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
     (35 35
         (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
     (27 27 (:REWRITE SIMPLIFY-SUMS-EQUAL))
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
     (25 4 (:REWRITE RATIONALP-X))
     (21 21
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (14 4 (:REWRITE O-FIRST-EXPT-O-INFP))
     (12 12 (:TYPE-PRESCRIPTION O-FINP))
     (11 11
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (11 11
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (11 11 (:REWRITE |(< (/ x) 0)|))
     (11 11 (:REWRITE |(< (* x y) 0)|))
     (10 4 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
     (5 5 (:LINEAR LEQ-POSITION-EQUAL-LEN))
     (4 4 (:REWRITE LL2::SP-WR))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (4 4 (:REWRITE REDUCE-RATIONALP-+))
     (4 4 (:REWRITE REDUCE-RATIONALP-*))
     (4 4 (:REWRITE REDUCE-INTEGERP-+))
     (4 4 (:REWRITE RATIONALP-MINUS-X))
     (4 4 (:REWRITE INTEGERP-MINUS-X))
     (4 4 (:REWRITE |(< 0 (/ x))|))
     (4 4 (:REWRITE |(< 0 (* x y))|))
     (4 4 (:META META-RATIONALP-CORRECT))
     (4 4 (:META META-INTEGERP-CORRECT))
     (3 1 (:REWRITE LL2::INTEGER-LISTP-NTH)))
(LL2::PREAMBLE-N-UNCHANGED
     (5160 69 (:REWRITE NTH-WITH-LARGE-INDEX))
     (4514 16 (:REWRITE LL2::UPDATE-NTH-REDUNDANT))
     (4320 160 (:REWRITE LEN-UPDATE-NTH1))
     (256 242
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (256 242
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (253 243 (:REWRITE DEFAULT-LESS-THAN-1))
     (250 242 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (247 243 (:REWRITE DEFAULT-LESS-THAN-2))
     (246 243
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (243 243 (:REWRITE THE-FLOOR-BELOW))
     (243 243 (:REWRITE THE-FLOOR-ABOVE))
     (243 243
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (243 243
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (243 243
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (243 243 (:REWRITE INTEGERP-<-CONSTANT))
     (243 243 (:REWRITE CONSTANT-<-INTEGERP))
     (243 243
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (243 243
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (243 243
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (243 243 (:REWRITE |(< c (- x))|))
     (243 243
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (243 243
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (243 243
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (243 243
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (243 243 (:REWRITE |(< (/ x) (/ y))|))
     (243 243 (:REWRITE |(< (- x) c)|))
     (243 243 (:REWRITE |(< (- x) (- y))|))
     (242 242 (:REWRITE SIMPLIFY-SUMS-<))
     (196 8 (:REWRITE LL2::WR-REDUNDANT))
     (148 88
          (:TYPE-PRESCRIPTION TRUE-LISTP-UPDATE-NTH))
     (114 3 (:REWRITE NATP-WHEN-GTE-0))
     (89 27
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (88 88 (:TYPE-PRESCRIPTION UPDATE-NTH))
     (56 9 (:REWRITE ACL2-NUMBERP-X))
     (50 27
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (37 37
         (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
     (37 37
         (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
     (36 12 (:REWRITE UPDATE-NTH-UPDATE-NTH . 1))
     (34 27 (:REWRITE SIMPLIFY-SUMS-EQUAL))
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
     (25 4 (:REWRITE RATIONALP-X))
     (22 6 (:REWRITE O-INFP->NEQ-0))
     (20 20
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (11 11
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (11 11
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (11 11 (:REWRITE |(< (/ x) 0)|))
     (11 11 (:REWRITE |(< (* x y) 0)|))
     (9 9 (:TYPE-PRESCRIPTION O-FINP))
     (9 3 (:REWRITE O-FIRST-EXPT-O-INFP))
     (6 3 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
     (5 5 (:LINEAR LEQ-POSITION-EQUAL-LEN))
     (4 4 (:REWRITE LL2::SP-WR))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (4 4 (:REWRITE REDUCE-RATIONALP-+))
     (4 4 (:REWRITE REDUCE-RATIONALP-*))
     (4 4 (:REWRITE REDUCE-INTEGERP-+))
     (4 4 (:REWRITE RATIONALP-MINUS-X))
     (4 4 (:REWRITE INTEGERP-MINUS-X))
     (4 4 (:REWRITE |(< 0 (/ x))|))
     (4 4 (:REWRITE |(< 0 (* x y))|))
     (4 4 (:META META-RATIONALP-CORRECT))
     (4 4 (:META META-INTEGERP-CORRECT))
     (3 1 (:REWRITE LL2::INTEGER-LISTP-NTH)))
(LL2::PREAMBLE-BASE-ADDR-UNCHANGED
     (5209 70 (:REWRITE NTH-WITH-LARGE-INDEX))
     (4514 16 (:REWRITE LL2::UPDATE-NTH-REDUNDANT))
     (4320 160 (:REWRITE LEN-UPDATE-NTH1))
     (256 242
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (256 242
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (253 243 (:REWRITE DEFAULT-LESS-THAN-1))
     (250 242 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (247 243 (:REWRITE DEFAULT-LESS-THAN-2))
     (246 243
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (243 243 (:REWRITE THE-FLOOR-BELOW))
     (243 243 (:REWRITE THE-FLOOR-ABOVE))
     (243 243
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (243 243
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (243 243
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (243 243 (:REWRITE INTEGERP-<-CONSTANT))
     (243 243 (:REWRITE CONSTANT-<-INTEGERP))
     (243 243
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (243 243
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (243 243
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (243 243 (:REWRITE |(< c (- x))|))
     (243 243
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (243 243
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (243 243
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (243 243
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (243 243 (:REWRITE |(< (/ x) (/ y))|))
     (243 243 (:REWRITE |(< (- x) c)|))
     (243 243 (:REWRITE |(< (- x) (- y))|))
     (242 242 (:REWRITE SIMPLIFY-SUMS-<))
     (196 8 (:REWRITE LL2::WR-REDUNDANT))
     (148 88
          (:TYPE-PRESCRIPTION TRUE-LISTP-UPDATE-NTH))
     (114 3 (:REWRITE NATP-WHEN-GTE-0))
     (89 27
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (88 88 (:TYPE-PRESCRIPTION UPDATE-NTH))
     (56 9 (:REWRITE ACL2-NUMBERP-X))
     (50 27
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (38 38
         (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
     (38 38
         (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
     (36 12 (:REWRITE UPDATE-NTH-UPDATE-NTH . 1))
     (34 27 (:REWRITE SIMPLIFY-SUMS-EQUAL))
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
     (25 4 (:REWRITE RATIONALP-X))
     (22 6 (:REWRITE O-INFP->NEQ-0))
     (20 20
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (16 16
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (16 16
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (16 16 (:REWRITE |(< 0 (/ x))|))
     (16 16 (:REWRITE |(< 0 (* x y))|))
     (11 11
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (11 11
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (11 11 (:REWRITE |(< (/ x) 0)|))
     (11 11 (:REWRITE |(< (* x y) 0)|))
     (9 9 (:TYPE-PRESCRIPTION O-FINP))
     (9 3 (:REWRITE O-FIRST-EXPT-O-INFP))
     (6 3 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
     (5 5 (:LINEAR LEQ-POSITION-EQUAL-LEN))
     (4 4 (:REWRITE LL2::SP-WR))
     (4 4 (:REWRITE REDUCE-RATIONALP-+))
     (4 4 (:REWRITE REDUCE-RATIONALP-*))
     (4 4 (:REWRITE REDUCE-INTEGERP-+))
     (4 4 (:REWRITE RATIONALP-MINUS-X))
     (4 4 (:REWRITE INTEGERP-MINUS-X))
     (4 4 (:META META-RATIONALP-CORRECT))
     (4 4 (:META META-INTEGERP-CORRECT))
     (3 1 (:REWRITE LL2::INTEGER-LISTP-NTH)))
(CODEWALKER-WRAPPER
     (1148 17 (:REWRITE NATP-WHEN-INTEGERP))
     (655 12 (:REWRITE NFIX-WHEN-NOT-NATP))
     (334 4 (:REWRITE O<=-O-FINP-DEF))
     (298 44 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (282 2
          (:REWRITE |a < b  <=>  c+a < c+b :l1|))
     (222 84 (:REWRITE DEFAULT-LESS-THAN-1))
     (158 129 (:REWRITE DEFAULT-PLUS-2))
     (137 129 (:REWRITE DEFAULT-PLUS-1))
     (97 49 (:REWRITE NORMALIZE-ADDENDS))
     (89 84 (:REWRITE DEFAULT-LESS-THAN-2))
     (84 84 (:REWRITE THE-FLOOR-BELOW))
     (84 84 (:REWRITE THE-FLOOR-ABOVE))
     (80 80
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (80 80
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (73 73 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (68 63
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (66 63
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (66 63 (:REWRITE |(< (- x) (- y))|))
     (63 63
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (63 63
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (63 63
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (63 63 (:REWRITE |(< c (- x))|))
     (63 63
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (63 63
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (63 63
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (63 63 (:REWRITE |(< (/ x) (/ y))|))
     (56 44
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (52 20 (:REWRITE ACL2-NUMBERP-X))
     (44 44
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (44 44 (:REWRITE INTEGERP-<-CONSTANT))
     (44 44 (:REWRITE CONSTANT-<-INTEGERP))
     (41 41
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (40 4
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (38 38 (:REWRITE SIMPLIFY-SUMS-<))
     (37 37 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (34 30 (:REWRITE DEFAULT-MINUS))
     (23 23 (:REWRITE |(< (* x y) 0)|))
     (21 21 (:REWRITE |(< (+ c/d x) y)|))
     (16 8 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
     (16 4 (:REWRITE RATIONALP-X))
     (14 14 (:DEFINITION FIX))
     (10 2 (:REWRITE O-FIRST-EXPT-<))
     (8 8 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (8 8 (:REWRITE REDUCE-INTEGERP-+))
     (8 8 (:REWRITE INTEGERP-MINUS-X))
     (8 8 (:REWRITE |(< x (+ c/d y))|))
     (8 8 (:REWRITE |(< (/ x) 0)|))
     (8 8 (:REWRITE |(+ x (- x))|))
     (8 8 (:META META-INTEGERP-CORRECT))
     (8 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (8 4
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (6 6 (:TYPE-PRESCRIPTION LL2::STEP))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (6 6 (:REWRITE |(< y (+ (- c) x))|))
     (6 6 (:REWRITE |(< 0 (/ x))|))
     (6 6 (:REWRITE |(< 0 (* x y))|))
     (6 4 (:REWRITE O-INFP-O-FINP-O<=))
     (6 4 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
     (6 4 (:REWRITE AC-<))
     (5 5 (:REWRITE INEQUALITY-WITH-NFIX-HYP-1))
     (4 4 (:REWRITE |a < b & b < c  =>  a < c|))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (4 4 (:REWRITE REDUCE-RATIONALP-+))
     (4 4 (:REWRITE REDUCE-RATIONALP-*))
     (4 4
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (4 4
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (4 4 (:REWRITE RATIONALP-MINUS-X))
     (4 4 (:REWRITE INEQUALITY-WITH-NFIX-HYP-2))
     (4 4
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (4 4 (:REWRITE DEFAULT-CDR))
     (4 4 (:REWRITE DEFAULT-CAR))
     (4 4 (:REWRITE |(equal c (/ x))|))
     (4 4 (:REWRITE |(equal c (- x))|))
     (4 4 (:REWRITE |(equal (/ x) c)|))
     (4 4 (:REWRITE |(equal (/ x) (/ y))|))
     (4 4 (:REWRITE |(equal (- x) c)|))
     (4 4 (:REWRITE |(equal (- x) (- y))|))
     (4 4 (:REWRITE |(< (+ (- c) x) y)|))
     (4 4 (:META META-RATIONALP-CORRECT))
     (2 2
        (:TYPE-PRESCRIPTION CONSP-REVAPPEND . 2))
     (2 2 (:REWRITE O-FIRST-COEFF-<)))
(CODEWALKER-WRAPPER-RULE-1
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
     (1 1 (:REWRITE SIMPLIFY-SUMS-<))
     (1 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (1 1 (:REWRITE REDUCE-INTEGERP-+))
     (1 1 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (1 1 (:REWRITE INTEGERP-MINUS-X))
     (1 1 (:META META-INTEGERP-CORRECT)))
(CODEWALKER-WRAPPER-RULE-2
     (57 17 (:REWRITE ACL2-NUMBERP-X))
     (50 5
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (44 22
         (:TYPE-PRESCRIPTION TRUE-LISTP-MEMBER-EQUAL))
     (37 1 (:REWRITE NATP-WHEN-GTE-0))
     (36 5 (:REWRITE DEFAULT-LESS-THAN-1))
     (22 22 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (20 5 (:REWRITE RATIONALP-X))
     (15 15 (:REWRITE DEFAULT-CDR))
     (15 15 (:REWRITE DEFAULT-CAR))
     (10 5 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (10 5
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (6 6 (:REWRITE REDUCE-INTEGERP-+))
     (6 6 (:REWRITE INTEGERP-MINUS-X))
     (6 6 (:META META-INTEGERP-CORRECT))
     (5 5 (:REWRITE THE-FLOOR-BELOW))
     (5 5 (:REWRITE THE-FLOOR-ABOVE))
     (5 5 (:REWRITE REDUCE-RATIONALP-+))
     (5 5 (:REWRITE REDUCE-RATIONALP-*))
     (5 5
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (5 5
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (5 5 (:REWRITE RATIONALP-MINUS-X))
     (5 5
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (5 5 (:REWRITE DEFAULT-LESS-THAN-2))
     (5 5 (:REWRITE |(equal c (/ x))|))
     (5 5 (:REWRITE |(equal c (- x))|))
     (5 5 (:REWRITE |(equal (/ x) c)|))
     (5 5 (:REWRITE |(equal (/ x) (/ y))|))
     (5 5 (:REWRITE |(equal (- x) c)|))
     (5 5 (:REWRITE |(equal (- x) (- y))|))
     (5 5 (:META META-RATIONALP-CORRECT))
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
     (4 1 (:REWRITE NATP-WHEN-INTEGERP))
     (2 2 (:REWRITE CODEWALKER-WRAPPER-RULE-1))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (1 1 (:REWRITE |(< (/ x) 0)|))
     (1 1 (:REWRITE |(< (* x y) 0)|)))
(CODEWALKER-WRAPPER-IGNORES-SPLITTERS
     (6222 74 (:REWRITE LL2::STEP-OPENER))
     (5916 58 (:DEFINITION LL2::NEXT-INST))
     (5568 58 (:REWRITE NTH-WITH-LARGE-INDEX))
     (2552 58 (:REWRITE NFIX-WHEN-NATP))
     (2376 334 (:REWRITE DEFAULT-LESS-THAN-1))
     (2370 270
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (1431 52 (:REWRITE CODEWALKER-WRAPPER-RULE-2))
     (1381 52 (:REWRITE CODEWALKER-WRAPPER-RULE-1))
     (1054 342 (:REWRITE ACL2-NUMBERP-X))
     (620 62
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (616 56 (:REWRITE |(+ y (+ x z))|))
     (464 464 (:TYPE-PRESCRIPTION LEN))
     (406 406 (:TYPE-PRESCRIPTION NFIX))
     (392 334 (:REWRITE DEFAULT-LESS-THAN-2))
     (356 89 (:REWRITE RATIONALP-X))
     (334 334 (:REWRITE THE-FLOOR-BELOW))
     (334 334 (:REWRITE THE-FLOOR-ABOVE))
     (330 214 (:REWRITE SIMPLIFY-SUMS-<))
     (330 214
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (330 214
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (320 128 (:REWRITE NATP-WHEN-INTEGERP))
     (302 302 (:REWRITE DEFAULT-PLUS-1))
     (290 58 (:REWRITE NFIX-WHEN-NOT-NATP))
     (270 270
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (270 270
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (232 232
          (:TYPE-PRESCRIPTION LL2::OCCURRENCES-PROGRAMP))
     (232 116
          (:TYPE-PRESCRIPTION LL2::INTEGER-LISTP-NTH))
     (214 214
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (214 214 (:REWRITE INTEGERP-<-CONSTANT))
     (214 214 (:REWRITE CONSTANT-<-INTEGERP))
     (214 214
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (214 214
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (214 214
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (214 214
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (214 214 (:REWRITE |(< c (- x))|))
     (214 214
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (214 214
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (214 214
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (214 214
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (214 214 (:REWRITE |(< (/ x) (/ y))|))
     (214 214 (:REWRITE |(< (- x) c)|))
     (214 214 (:REWRITE |(< (- x) (- y))|))
     (186 186 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (174 58 (:REWRITE LL2::RESOLVE-NEXT-INST1))
     (174 58
          (:REWRITE LL2::LEN-OCCURRENCES-PROGRAMP))
     (157 157 (:REWRITE REDUCE-INTEGERP-+))
     (157 157 (:REWRITE INTEGERP-MINUS-X))
     (157 157 (:META META-INTEGERP-CORRECT))
     (124 62 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (124 62
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (116 116 (:TYPE-PRESCRIPTION INTEGER-LISTP))
     (115 115 (:REWRITE DEFAULT-CDR))
     (115 115 (:REWRITE DEFAULT-CAR))
     (114 114
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (114 114 (:REWRITE NORMALIZE-ADDENDS))
     (89 89 (:REWRITE REDUCE-RATIONALP-+))
     (89 89 (:REWRITE REDUCE-RATIONALP-*))
     (89 89 (:REWRITE RATIONALP-MINUS-X))
     (89 89 (:META META-RATIONALP-CORRECT))
     (77 77 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (66 66 (:REWRITE |(< (+ c/d x) y)|))
     (64 64
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (64 64
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (64 64 (:REWRITE |(< (/ x) 0)|))
     (64 64 (:REWRITE |(< (* x y) 0)|))
     (62 62
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (62 62
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (62 62
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (62 62 (:REWRITE |(equal c (/ x))|))
     (62 62 (:REWRITE |(equal c (- x))|))
     (62 62 (:REWRITE |(equal (/ x) c)|))
     (62 62 (:REWRITE |(equal (/ x) (/ y))|))
     (62 62 (:REWRITE |(equal (- x) c)|))
     (62 62 (:REWRITE |(equal (- x) (- y))|))
     (58 58
         (:REWRITE INEQUALITY-WITH-NFIX-HYP-2))
     (58 58 (:LINEAR LEQ-POSITION-EQUAL-LEN))
     (58 58 (:DEFINITION LL2::PROGRAM))
     (58 58 (:DEFINITION LL2::PC))
     (56 56 (:REWRITE |(+ 0 x)|))
     (32 4 (:REWRITE |(+ x (if a b c))|))
     (10 10 (:REWRITE |(< (+ (- c) x) y)|)))
(CODEWALKER-WRAPPER-RULE-3
     (10403 121 (:REWRITE LL2::STEP-OPENER))
     (9894 97 (:DEFINITION LL2::NEXT-INST))
     (9312 97 (:REWRITE NTH-WITH-LARGE-INDEX))
     (4268 97 (:REWRITE NFIX-WHEN-NATP))
     (3982 202 (:REWRITE NATP-WHEN-GTE-0))
     (3872 520 (:REWRITE DEFAULT-LESS-THAN-1))
     (3715 415
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (2734 90 (:DEFINITION REVAPPEND))
     (2124 56 (:REWRITE CODEWALKER-WRAPPER-RULE-1))
     (2080 56 (:REWRITE CODEWALKER-WRAPPER-RULE-2))
     (1428 500 (:REWRITE ACL2-NUMBERP-X))
     (968 88 (:REWRITE |(+ y (+ x z))|))
     (860 86
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (776 776 (:TYPE-PRESCRIPTION LEN))
     (679 679 (:TYPE-PRESCRIPTION NFIX))
     (617 520 (:REWRITE DEFAULT-LESS-THAN-2))
     (521 327 (:REWRITE SIMPLIFY-SUMS-<))
     (521 327
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (521 327
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (520 520 (:REWRITE THE-FLOOR-BELOW))
     (520 520 (:REWRITE THE-FLOOR-ABOVE))
     (517 202 (:REWRITE NATP-WHEN-INTEGERP))
     (485 97 (:REWRITE NFIX-WHEN-NOT-NATP))
     (482 114 (:REWRITE |(+ c (+ d x))|))
     (466 466 (:REWRITE DEFAULT-PLUS-1))
     (464 116 (:REWRITE RATIONALP-X))
     (415 415
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (415 415
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (388 388
          (:TYPE-PRESCRIPTION LL2::OCCURRENCES-PROGRAMP))
     (388 194
          (:TYPE-PRESCRIPTION LL2::INTEGER-LISTP-NTH))
     (327 327
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (327 327 (:REWRITE INTEGERP-<-CONSTANT))
     (327 327 (:REWRITE CONSTANT-<-INTEGERP))
     (327 327
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (327 327
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (327 327
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (327 327
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (327 327 (:REWRITE |(< c (- x))|))
     (327 327
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (327 327
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (327 327
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (327 327
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (327 327 (:REWRITE |(< (/ x) (/ y))|))
     (327 327 (:REWRITE |(< (- x) c)|))
     (327 327 (:REWRITE |(< (- x) (- y))|))
     (291 97 (:REWRITE LL2::RESOLVE-NEXT-INST1))
     (291 97
          (:REWRITE LL2::LEN-OCCURRENCES-PROGRAMP))
     (283 283 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (221 221 (:REWRITE REDUCE-INTEGERP-+))
     (221 221 (:REWRITE INTEGERP-MINUS-X))
     (221 221 (:META META-INTEGERP-CORRECT))
     (194 194 (:TYPE-PRESCRIPTION INTEGER-LISTP))
     (172 86 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (172 86
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (169 169
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (169 169 (:REWRITE NORMALIZE-ADDENDS))
     (138 138 (:REWRITE DEFAULT-CAR))
     (137 137 (:REWRITE DEFAULT-CDR))
     (116 116 (:REWRITE REDUCE-RATIONALP-+))
     (116 116 (:REWRITE REDUCE-RATIONALP-*))
     (116 116 (:REWRITE RATIONALP-MINUS-X))
     (116 116 (:META META-RATIONALP-CORRECT))
     (111 111 (:TYPE-PRESCRIPTION LL2::STEP))
     (105 105
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (105 105
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (105 105 (:REWRITE |(< (/ x) 0)|))
     (105 105 (:REWRITE |(< (* x y) 0)|))
     (104 104 (:REWRITE |(< (+ c/d x) y)|))
     (97 97
         (:REWRITE INEQUALITY-WITH-NFIX-HYP-2))
     (97 97 (:LINEAR LEQ-POSITION-EQUAL-LEN))
     (97 97 (:DEFINITION LL2::PROGRAM))
     (97 97 (:DEFINITION LL2::PC))
     (88 88 (:REWRITE |(+ 0 x)|))
     (86 86
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (86 86
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (86 86
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (86 86 (:REWRITE |(equal c (/ x))|))
     (86 86 (:REWRITE |(equal c (- x))|))
     (86 86 (:REWRITE |(equal (/ x) c)|))
     (86 86 (:REWRITE |(equal (/ x) (/ y))|))
     (86 86 (:REWRITE |(equal (- x) c)|))
     (86 86 (:REWRITE |(equal (- x) (- y))|))
     (75 75 (:REWRITE CDR-CONS))
     (56 7 (:REWRITE |(+ x (if a b c))|))
     (16 16 (:REWRITE |(< (+ (- c) x) y)|)))
(LL2::CLK-LOOP-8
     (120528 4464 (:REWRITE LEN-UPDATE-NTH1))
     (106221 171 (:REWRITE NTH-WITH-LARGE-INDEX))
     (62341 17 (:REWRITE LL2::UPDATE-NTH-REDUNDANT))
     (6456 4726
           (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (5737 4737
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (5047 4744 (:REWRITE DEFAULT-LESS-THAN-1))
     (4896 4726
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (4887 4707 (:REWRITE SIMPLIFY-SUMS-<))
     (4805 4744 (:REWRITE DEFAULT-LESS-THAN-2))
     (4776 4727 (:REWRITE |(< (- x) c)|))
     (4745 4727 (:REWRITE |(< (- x) (- y))|))
     (4744 4744 (:REWRITE THE-FLOOR-BELOW))
     (4744 4744 (:REWRITE THE-FLOOR-ABOVE))
     (4740 4726
           (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (4737 4737
           (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (4737 4737
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (4731 4727
           (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (4731 4715
           (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (4729 4727
           (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (4727 4727
           (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (4727 4727
           (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (4727 4727 (:REWRITE |(< c (- x))|))
     (4727 4727
           (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (4727 4727
           (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (4727 4727
           (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (4727 4727
           (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (4727 4727 (:REWRITE |(< (/ x) (/ y))|))
     (4726 4726 (:REWRITE INTEGERP-<-CONSTANT))
     (4726 4726 (:REWRITE CONSTANT-<-INTEGERP))
     (3257 33 (:REWRITE NATP-WHEN-INTEGERP))
     (1816 14 (:REWRITE NFIX-WHEN-NOT-NATP))
     (809 29
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (779 27 (:REWRITE ACL2-NUMBERP-X))
     (612 9 (:REWRITE RATIONALP-X))
     (574 4 (:REWRITE O<=-O-FINP-DEF))
     (478 56 (:REWRITE |(< (+ (- c) x) y)|))
     (476 238 (:REWRITE DEFAULT-PLUS-2))
     (472 9 (:REWRITE LL2::INTEGER-LISTP-NTH))
     (355 79 (:REWRITE NORMALIZE-ADDENDS))
     (280 29 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (264 4 (:REWRITE LL2::WR-REDUNDANT))
     (200 3 (:REWRITE |(< (if a b c) x)|))
     (151 29
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (108 55 (:DEFINITION FIX))
     (85 85
         (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
     (85 85
         (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
     (70 14 (:REWRITE |(+ c (+ d x))|))
     (64 64 (:REWRITE |(< (+ c/d x) y)|))
     (62 31 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
     (61 31 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (58 58 (:REWRITE |(< (* x y) 0)|))
     (50 50 (:REWRITE |(< (/ x) 0)|))
     (48 48
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (45 15 (:REWRITE UPDATE-NTH-UPDATE-NTH . 1))
     (40 40
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (40 40
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (31 31 (:REWRITE |(+ x (- x))|))
     (29 29
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (29 29
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (29 29
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (29 29 (:REWRITE |(equal c (/ x))|))
     (29 29 (:REWRITE |(equal c (- x))|))
     (29 29 (:REWRITE |(equal (/ x) c)|))
     (29 29 (:REWRITE |(equal (/ x) (/ y))|))
     (29 29 (:REWRITE |(equal (- x) c)|))
     (29 29 (:REWRITE |(equal (- x) (- y))|))
     (22 22 (:REWRITE |(< y (+ (- c) x))|))
     (22 22 (:REWRITE |(< x (+ c/d y))|))
     (16 4 (:REWRITE AC-<))
     (15 15 (:LINEAR LEQ-POSITION-EQUAL-LEN))
     (14 14 (:REWRITE REDUCE-INTEGERP-+))
     (14 14 (:REWRITE INTEGERP-MINUS-X))
     (14 14 (:META META-INTEGERP-CORRECT))
     (12 12 (:REWRITE |(equal (+ (- c) x) y)|))
     (12 2 (:REWRITE O-FIRST-EXPT-<))
     (11 11
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (11 11
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (11 11 (:REWRITE |(< 0 (/ x))|))
     (11 11 (:REWRITE |(< 0 (* x y))|))
     (10 4 (:REWRITE O-INFP-O-FINP-O<=))
     (9 9 (:REWRITE REDUCE-RATIONALP-+))
     (9 9 (:REWRITE REDUCE-RATIONALP-*))
     (9 9 (:REWRITE RATIONALP-MINUS-X))
     (9 9 (:REWRITE INEQUALITY-WITH-NFIX-HYP-2))
     (9 9 (:META META-RATIONALP-CORRECT))
     (8 4 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
     (6 6 (:TYPE-PRESCRIPTION LL2::WR))
     (6 6 (:REWRITE FOLD-CONSTS-IN-+))
     (4 4 (:REWRITE |a < b & b < c  =>  a < c|))
     (4 4 (:REWRITE INEQUALITY-WITH-NFIX-HYP-1))
     (4 2 (:REWRITE O-FIRST-COEFF-<))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (2 2 (:REWRITE LL2::SP-WR))
     (1 1 (:REWRITE |(- (- x))|)))
(LL2::SEM-LOOP-8
     (120528 4464 (:REWRITE LEN-UPDATE-NTH1))
     (106221 171 (:REWRITE NTH-WITH-LARGE-INDEX))
     (62341 17 (:REWRITE LL2::UPDATE-NTH-REDUNDANT))
     (6456 4726
           (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (5737 4737
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (5047 4744 (:REWRITE DEFAULT-LESS-THAN-1))
     (4896 4726
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (4887 4707 (:REWRITE SIMPLIFY-SUMS-<))
     (4805 4744 (:REWRITE DEFAULT-LESS-THAN-2))
     (4776 4727 (:REWRITE |(< (- x) c)|))
     (4745 4727 (:REWRITE |(< (- x) (- y))|))
     (4744 4744 (:REWRITE THE-FLOOR-BELOW))
     (4744 4744 (:REWRITE THE-FLOOR-ABOVE))
     (4740 4726
           (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (4737 4737
           (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (4737 4737
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (4731 4727
           (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (4731 4715
           (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (4729 4727
           (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (4727 4727
           (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (4727 4727
           (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (4727 4727 (:REWRITE |(< c (- x))|))
     (4727 4727
           (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (4727 4727
           (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (4727 4727
           (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (4727 4727
           (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (4727 4727 (:REWRITE |(< (/ x) (/ y))|))
     (4726 4726 (:REWRITE INTEGERP-<-CONSTANT))
     (4726 4726 (:REWRITE CONSTANT-<-INTEGERP))
     (3257 33 (:REWRITE NATP-WHEN-INTEGERP))
     (1816 14 (:REWRITE NFIX-WHEN-NOT-NATP))
     (809 29
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (779 27 (:REWRITE ACL2-NUMBERP-X))
     (612 9 (:REWRITE RATIONALP-X))
     (574 4 (:REWRITE O<=-O-FINP-DEF))
     (478 56 (:REWRITE |(< (+ (- c) x) y)|))
     (476 238 (:REWRITE DEFAULT-PLUS-2))
     (472 9 (:REWRITE LL2::INTEGER-LISTP-NTH))
     (355 79 (:REWRITE NORMALIZE-ADDENDS))
     (280 29 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (264 4 (:REWRITE LL2::WR-REDUNDANT))
     (200 3 (:REWRITE |(< (if a b c) x)|))
     (151 29
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (108 55 (:DEFINITION FIX))
     (85 85
         (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
     (85 85
         (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
     (70 14 (:REWRITE |(+ c (+ d x))|))
     (64 64 (:REWRITE |(< (+ c/d x) y)|))
     (62 31 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
     (61 31 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (58 58 (:TYPE-PRESCRIPTION LL2::WR))
     (58 58 (:REWRITE |(< (* x y) 0)|))
     (50 50 (:REWRITE |(< (/ x) 0)|))
     (48 48
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (45 15 (:REWRITE UPDATE-NTH-UPDATE-NTH . 1))
     (40 40
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (40 40
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (31 31 (:REWRITE |(+ x (- x))|))
     (29 29
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (29 29
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (29 29
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (29 29 (:REWRITE |(equal c (/ x))|))
     (29 29 (:REWRITE |(equal c (- x))|))
     (29 29 (:REWRITE |(equal (/ x) c)|))
     (29 29 (:REWRITE |(equal (/ x) (/ y))|))
     (29 29 (:REWRITE |(equal (- x) c)|))
     (29 29 (:REWRITE |(equal (- x) (- y))|))
     (22 22 (:REWRITE |(< y (+ (- c) x))|))
     (22 22 (:REWRITE |(< x (+ c/d y))|))
     (16 4 (:REWRITE AC-<))
     (15 15 (:LINEAR LEQ-POSITION-EQUAL-LEN))
     (14 14 (:REWRITE REDUCE-INTEGERP-+))
     (14 14 (:REWRITE INTEGERP-MINUS-X))
     (14 14 (:META META-INTEGERP-CORRECT))
     (12 12 (:REWRITE |(equal (+ (- c) x) y)|))
     (12 2 (:REWRITE O-FIRST-EXPT-<))
     (11 11
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (11 11
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (11 11 (:REWRITE |(< 0 (/ x))|))
     (11 11 (:REWRITE |(< 0 (* x y))|))
     (10 4 (:REWRITE O-INFP-O-FINP-O<=))
     (9 9 (:REWRITE REDUCE-RATIONALP-+))
     (9 9 (:REWRITE REDUCE-RATIONALP-*))
     (9 9 (:REWRITE RATIONALP-MINUS-X))
     (9 9 (:REWRITE INEQUALITY-WITH-NFIX-HYP-2))
     (9 9 (:META META-RATIONALP-CORRECT))
     (8 4 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
     (6 6 (:REWRITE FOLD-CONSTS-IN-+))
     (4 4 (:REWRITE |a < b & b < c  =>  a < c|))
     (4 4 (:REWRITE INEQUALITY-WITH-NFIX-HYP-1))
     (4 2 (:REWRITE O-FIRST-COEFF-<))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (2 2 (:REWRITE LL2::SP-WR))
     (1 1 (:REWRITE |(- (- x))|)))
(LL2::SEM-LOOP-8-CORRECT
     (1440264 3381 (:REWRITE NTH-WITH-LARGE-INDEX))
     (74302 73160
            (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (74220 73209 (:REWRITE DEFAULT-LESS-THAN-1))
     (73928 73160
            (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (73440 73160 (:REWRITE SIMPLIFY-SUMS-<))
     (73431 73209 (:REWRITE DEFAULT-LESS-THAN-2))
     (73233 73209
            (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (73209 73209 (:REWRITE THE-FLOOR-BELOW))
     (73209 73209 (:REWRITE THE-FLOOR-ABOVE))
     (73209 73209
            (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (73209 73209
            (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (73209 73209
            (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (73209 73209 (:REWRITE INTEGERP-<-CONSTANT))
     (73209 73209 (:REWRITE CONSTANT-<-INTEGERP))
     (73209 73209
            (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (73209 73209
            (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (73209 73209
            (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (73209 73209 (:REWRITE |(< c (- x))|))
     (73209 73209
            (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (73209 73209
            (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (73209 73209
            (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (73209 73209
            (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (73209 73209 (:REWRITE |(< (/ x) (/ y))|))
     (73209 73209 (:REWRITE |(< (- x) c)|))
     (73209 73209 (:REWRITE |(< (- x) (- y))|))
     (16039 183 (:REWRITE NATP-WHEN-INTEGERP))
     (11447 777
            (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (8598 62 (:REWRITE NFIX-WHEN-NATP))
     (7974 207 (:REWRITE ACL2-NUMBERP-X))
     (6540 72 (:REWRITE RATIONALP-X))
     (6172 777 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (6149 62 (:REWRITE NFIX-WHEN-NOT-NATP))
     (5498 60 (:REWRITE LL2::INTEGER-LISTP-NTH))
     (3733 777
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (3107 183 (:REWRITE NATP-WHEN-GTE-0))
     (2390 148 (:REWRITE DEFAULT-CDR))
     (2390 148 (:REWRITE DEFAULT-CAR))
     (1829 1446 (:TYPE-PRESCRIPTION LL2::LL2))
     (1496 753 (:REWRITE DEFAULT-PLUS-2))
     (1494 450 (:REWRITE NORMALIZE-ADDENDS))
     (1443 753 (:REWRITE DEFAULT-PLUS-1))
     (1295 471
           (:REWRITE UPDATE-NTH-UPDATE-NTH . 1))
     (1160 58 (:REWRITE |(+ y (+ x z))|))
     (1120 1120
           (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
     (1120 1120
           (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
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
     (430 430 (:REWRITE |(< (+ c/d x) y)|))
     (430 430 (:REWRITE |(< (+ (- c) x) y)|))
     (428 428
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (428 428
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (428 428 (:REWRITE |(< (/ x) 0)|))
     (428 428 (:REWRITE |(< (* x y) 0)|))
     (383 383 (:TYPE-PRESCRIPTION LL2::WR))
     (348 348 (:TYPE-PRESCRIPTION LL2::PUSH))
     (348 174 (:DEFINITION FIX))
     (334 334
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (232 116 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (232 116 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
     (229 229 (:REWRITE |(equal (+ (- c) x) y)|))
     (167 167 (:LINEAR LEQ-POSITION-EQUAL-LEN))
     (116 116 (:REWRITE |(+ x (- x))|))
     (104 104
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (104 104
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (104 104 (:REWRITE |(< 0 (/ x))|))
     (104 104 (:REWRITE |(< 0 (* x y))|))
     (75 75 (:REWRITE REDUCE-INTEGERP-+))
     (75 75 (:REWRITE INTEGERP-MINUS-X))
     (75 75 (:META META-INTEGERP-CORRECT))
     (72 72 (:REWRITE REDUCE-RATIONALP-+))
     (72 72 (:REWRITE REDUCE-RATIONALP-*))
     (72 72 (:REWRITE RATIONALP-MINUS-X))
     (72 72 (:META META-RATIONALP-CORRECT))
     (69 69
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (62 62
         (:REWRITE INEQUALITY-WITH-NFIX-HYP-2))
     (43 43 (:REWRITE |(< y (+ (- c) x))|))
     (43 43 (:REWRITE |(< x (+ c/d y))|)))
(LL2::COMPOSITION)
(LL2::OCCUR-ARR-TAILREC-INSENSITIVE-TO-LOCALS-UPDATE
     (6430 33 (:REWRITE NTH-WITH-LARGE-INDEX))
     (3903 58 (:REWRITE NATP-WHEN-INTEGERP))
     (3139 29 (:REWRITE NFIX-WHEN-NATP))
     (2880 328
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (2024 29 (:REWRITE NFIX-WHEN-NOT-NATP))
     (1144 58 (:REWRITE NATP-WHEN-GTE-0))
     (929 671 (:REWRITE DEFAULT-PLUS-2))
     (817 671 (:REWRITE DEFAULT-PLUS-1))
     (714 36
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (604 87 (:REWRITE ACL2-NUMBERP-X))
     (463 328 (:REWRITE DEFAULT-LESS-THAN-2))
     (416 268
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (369 328 (:REWRITE DEFAULT-LESS-THAN-1))
     (328 328 (:REWRITE THE-FLOOR-BELOW))
     (328 328 (:REWRITE THE-FLOOR-ABOVE))
     (328 328
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (328 328
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (328 222 (:REWRITE SIMPLIFY-SUMS-<))
     (292 280 (:REWRITE |(< (- x) (- y))|))
     (287 29 (:REWRITE RATIONALP-X))
     (280 280
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (280 280
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (280 280
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (280 280
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (280 280
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (280 280
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (280 280
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (280 280
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (280 280 (:REWRITE |(< (/ x) (/ y))|))
     (280 268 (:REWRITE |(< (- x) c)|))
     (272 268
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (268 268 (:REWRITE INTEGERP-<-CONSTANT))
     (268 268 (:REWRITE CONSTANT-<-INTEGERP))
     (242 12 (:REWRITE LL2::WR-REDUNDANT))
     (198 198
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (197 36 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (197 36
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (187 187 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (164 128 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
     (133 133 (:REWRITE |(< (* x y) 0)|))
     (124 88 (:REWRITE DEFAULT-MINUS))
     (97 97 (:REWRITE |(< (/ x) 0)|))
     (85 85
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (85 85
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (72 72 (:REWRITE |(< (+ c/d x) y)|))
     (60 20 (:REWRITE LL2::INTEGER-LISTP-NTH))
     (58 58 (:TYPE-PRESCRIPTION NATP))
     (58 58 (:REWRITE |(< x (+ c/d y))|))
     (58 58 (:LINEAR LEQ-POSITION-EQUAL-LEN))
     (58 46 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (50 50 (:REWRITE REDUCE-INTEGERP-+))
     (50 50 (:REWRITE INTEGERP-MINUS-X))
     (50 50 (:META META-INTEGERP-CORRECT))
     (46 46 (:REWRITE |(< y (+ (- c) x))|))
     (46 46 (:REWRITE |(< 0 (* x y))|))
     (46 4 (:REWRITE |(+ x (if a b c))|))
     (36 36
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (36 36
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (36 36
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (36 36 (:REWRITE |(equal c (/ x))|))
     (36 36 (:REWRITE |(equal c (- x))|))
     (36 36 (:REWRITE |(equal (/ x) c)|))
     (36 36 (:REWRITE |(equal (/ x) (/ y))|))
     (36 36 (:REWRITE |(equal (- x) c)|))
     (36 36 (:REWRITE |(equal (- x) (- y))|))
     (36 36 (:REWRITE |(< (+ (- c) x) y)|))
     (34 34 (:REWRITE |(< 0 (/ x))|))
     (29 29 (:REWRITE REDUCE-RATIONALP-+))
     (29 29 (:REWRITE REDUCE-RATIONALP-*))
     (29 29 (:REWRITE RATIONALP-MINUS-X))
     (29 29
         (:REWRITE INEQUALITY-WITH-NFIX-HYP-2))
     (29 29 (:META META-RATIONALP-CORRECT))
     (24 24 (:REWRITE FOLD-CONSTS-IN-+)))
(LL2::OCCUR-ARR-TAILREC-INSENSITIVE-TO-PC-UPDATE
     (6430 33 (:REWRITE NTH-WITH-LARGE-INDEX))
     (3903 58 (:REWRITE NATP-WHEN-INTEGERP))
     (3139 29 (:REWRITE NFIX-WHEN-NATP))
     (2880 328
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (2024 29 (:REWRITE NFIX-WHEN-NOT-NATP))
     (1144 58 (:REWRITE NATP-WHEN-GTE-0))
     (929 671 (:REWRITE DEFAULT-PLUS-2))
     (817 671 (:REWRITE DEFAULT-PLUS-1))
     (714 36
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (604 87 (:REWRITE ACL2-NUMBERP-X))
     (463 328 (:REWRITE DEFAULT-LESS-THAN-2))
     (416 268
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (369 328 (:REWRITE DEFAULT-LESS-THAN-1))
     (328 328 (:REWRITE THE-FLOOR-BELOW))
     (328 328 (:REWRITE THE-FLOOR-ABOVE))
     (328 328
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (328 328
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (328 222 (:REWRITE SIMPLIFY-SUMS-<))
     (292 280 (:REWRITE |(< (- x) (- y))|))
     (287 29 (:REWRITE RATIONALP-X))
     (280 280
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (280 280
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (280 280
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (280 280
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (280 280
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (280 280
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (280 280
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (280 280
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (280 280 (:REWRITE |(< (/ x) (/ y))|))
     (280 268 (:REWRITE |(< (- x) c)|))
     (272 268
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (268 268 (:REWRITE INTEGERP-<-CONSTANT))
     (268 268 (:REWRITE CONSTANT-<-INTEGERP))
     (242 12 (:REWRITE LL2::WR-REDUNDANT))
     (198 198
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (197 36 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (197 36
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (187 187 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (164 128 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
     (133 133 (:REWRITE |(< (* x y) 0)|))
     (124 88 (:REWRITE DEFAULT-MINUS))
     (97 97 (:REWRITE |(< (/ x) 0)|))
     (85 85
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (85 85
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (72 72 (:REWRITE |(< (+ c/d x) y)|))
     (60 20 (:REWRITE LL2::INTEGER-LISTP-NTH))
     (58 58 (:TYPE-PRESCRIPTION NATP))
     (58 58 (:REWRITE |(< x (+ c/d y))|))
     (58 58 (:LINEAR LEQ-POSITION-EQUAL-LEN))
     (58 46 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (50 50 (:REWRITE REDUCE-INTEGERP-+))
     (50 50 (:REWRITE INTEGERP-MINUS-X))
     (50 50 (:META META-INTEGERP-CORRECT))
     (46 46 (:REWRITE |(< y (+ (- c) x))|))
     (46 46 (:REWRITE |(< 0 (* x y))|))
     (46 4 (:REWRITE |(+ x (if a b c))|))
     (36 36
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (36 36
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (36 36
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (36 36 (:REWRITE |(equal c (/ x))|))
     (36 36 (:REWRITE |(equal c (- x))|))
     (36 36 (:REWRITE |(equal (/ x) c)|))
     (36 36 (:REWRITE |(equal (/ x) (/ y))|))
     (36 36 (:REWRITE |(equal (- x) c)|))
     (36 36 (:REWRITE |(equal (- x) (- y))|))
     (36 36 (:REWRITE |(< (+ (- c) x) y)|))
     (34 34 (:REWRITE |(< 0 (/ x))|))
     (29 29 (:REWRITE REDUCE-RATIONALP-+))
     (29 29 (:REWRITE REDUCE-RATIONALP-*))
     (29 29 (:REWRITE RATIONALP-MINUS-X))
     (29 29
         (:REWRITE INEQUALITY-WITH-NFIX-HYP-2))
     (29 29 (:META META-RATIONALP-CORRECT))
     (24 24 (:REWRITE FOLD-CONSTS-IN-+)))
(LL2::OCCUR-ARR-TAILREC-INSENSITIVE-TO-SEM-PREAMBLE-0
     (4738 16 (:REWRITE LL2::UPDATE-NTH-REDUNDANT))
     (4515 58 (:REWRITE NTH-WITH-LARGE-INDEX))
     (3176 6 (:DEFINITION LL2::OCCUR-ARR-TAILREC))
     (2916 108 (:REWRITE LEN-UPDATE-NTH1))
     (1898 6
           (:DEFINITION LL2::OCCUR-ARR-STEP$INLINE))
     (1284 24 (:REWRITE NTH-UPDATE-NTH))
     (946 254
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (570 6 (:REWRITE NFIX-WHEN-NATP))
     (558 6 (:REWRITE ZP-WHEN-GT-0))
     (552 6 (:REWRITE ZP-WHEN-INTEGERP))
     (496 8 (:REWRITE LL2::WR-REDUNDANT))
     (487 34
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (432 30 (:REWRITE ACL2-NUMBERP-X))
     (420 164
          (:TYPE-PRESCRIPTION TRUE-LISTP-UPDATE-NTH))
     (419 22 (:REWRITE NATP-WHEN-GTE-0))
     (384 6 (:REWRITE NFIX-WHEN-NOT-NATP))
     (366 257 (:REWRITE DEFAULT-LESS-THAN-1))
     (334 8 (:REWRITE RATIONALP-X))
     (300 254
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (291 257 (:REWRITE DEFAULT-LESS-THAN-2))
     (267 242 (:REWRITE SIMPLIFY-SUMS-<))
     (266 6 (:REWRITE LL2::INTEGER-LISTP-NTH))
     (258 254
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (257 257 (:REWRITE THE-FLOOR-BELOW))
     (257 257 (:REWRITE THE-FLOOR-ABOVE))
     (256 254
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (254 254
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (254 254
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (254 254
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (254 254 (:REWRITE INTEGERP-<-CONSTANT))
     (254 254 (:REWRITE CONSTANT-<-INTEGERP))
     (254 254
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (254 254
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (254 254
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (254 254 (:REWRITE |(< c (- x))|))
     (254 254
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (254 254
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (254 254
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (254 254
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (254 254 (:REWRITE |(< (/ x) (/ y))|))
     (254 254 (:REWRITE |(< (- x) c)|))
     (254 254 (:REWRITE |(< (- x) (- y))|))
     (238 230 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (174 30 (:REWRITE NORMALIZE-ADDENDS))
     (164 164 (:TYPE-PRESCRIPTION UPDATE-NTH))
     (132 90 (:REWRITE DEFAULT-PLUS-2))
     (120 120 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (108 90 (:REWRITE DEFAULT-PLUS-1))
     (93 34
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (84 18 (:REWRITE |(+ y x)|))
     (84 12 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
     (80 34 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (53 53 (:LINEAR LEQ-POSITION-EQUAL-LEN))
     (52 52
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (52 52
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (52 52 (:REWRITE |(< (/ x) 0)|))
     (52 52 (:REWRITE |(< (* x y) 0)|))
     (42 30 (:REWRITE |(+ 0 x)|))
     (36 30 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
     (36 30 (:REWRITE IFIX-WHEN-INTEGERP))
     (36 12 (:REWRITE UPDATE-NTH-UPDATE-NTH . 1))
     (34 34
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (34 34
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (34 34
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (34 34 (:REWRITE |(equal c (/ x))|))
     (34 34 (:REWRITE |(equal c (- x))|))
     (34 34 (:REWRITE |(equal (/ x) c)|))
     (34 34 (:REWRITE |(equal (/ x) (/ y))|))
     (34 34 (:REWRITE |(equal (- x) c)|))
     (34 34 (:REWRITE |(equal (- x) (- y))|))
     (28 28
         (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
     (28 28
         (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
     (24 24 (:DEFINITION FIX))
     (20 20 (:REWRITE REDUCE-INTEGERP-+))
     (20 20 (:REWRITE INTEGERP-MINUS-X))
     (20 20 (:META META-INTEGERP-CORRECT))
     (18 18
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (18 6 (:DEFINITION LIFIX$INLINE))
     (17 17
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (15 15 (:REWRITE |(< 0 (/ x))|))
     (15 15 (:REWRITE |(< 0 (* x y))|))
     (12 12 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (12 12 (:REWRITE |(< y (+ (- c) x))|))
     (12 12 (:REWRITE |(< x (+ c/d y))|))
     (12 12 (:REWRITE |(+ x (- x))|))
     (12 12 (:REWRITE |(+ c (+ d x))|))
     (8 8 (:REWRITE REDUCE-RATIONALP-+))
     (8 8 (:REWRITE REDUCE-RATIONALP-*))
     (8 8 (:REWRITE RATIONALP-MINUS-X))
     (8 8 (:META META-RATIONALP-CORRECT))
     (6 6 (:REWRITE INEQUALITY-WITH-NFIX-HYP-2))
     (6 6 (:REWRITE DEFAULT-MINUS))
     (4 4 (:REWRITE LL2::RD-WR))
     (4 3 (:REWRITE O-INFP->NEQ-0))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON)))
(LL2::SEM-LOOP-8-=-OCCUR-ARR-TAILREC
     (4320088 1431
              (:REWRITE LL2::UPDATE-NTH-REDUNDANT))
     (3851649 8301 (:REWRITE NTH-WITH-LARGE-INDEX))
     (2813586 768
              (:REWRITE UPDATE-NTH-UPDATE-NTH . 2))
     (237735 1551
             (:REWRITE UPDATE-NTH-UPDATE-NTH . 1))
     (212157 211661 (:REWRITE |(< c (- x))|))
     (212088 211680
             (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (211959 211683 (:REWRITE DEFAULT-LESS-THAN-2))
     (211728 211683 (:REWRITE DEFAULT-LESS-THAN-1))
     (211695 211661
             (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (211683 211683 (:REWRITE THE-FLOOR-BELOW))
     (211683 211683 (:REWRITE THE-FLOOR-ABOVE))
     (211680 211680
             (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (211680 211680
             (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (211676 211572 (:REWRITE SIMPLIFY-SUMS-<))
     (211665 211661 (:REWRITE |(< (- x) (- y))|))
     (211661 211661
             (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (211661 211661
             (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (211661 211661
             (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (211661 211661
             (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (211661 211661
             (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (211661 211661
             (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (211661 211661
             (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (211661 211661 (:REWRITE |(< (/ x) (/ y))|))
     (211661 211657 (:REWRITE |(< (- x) c)|))
     (211657 211657 (:REWRITE INTEGERP-<-CONSTANT))
     (211657 211657 (:REWRITE CONSTANT-<-INTEGERP))
     (211578 211557
             (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (11055 1295 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (3619 2478 (:REWRITE DEFAULT-PLUS-1))
     (3340 1295
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (3289 2478 (:REWRITE DEFAULT-PLUS-2))
     (2789 1295
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (2304 24 (:REWRITE LL2::WR-WR-SAME))
     (1653 1653
           (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
     (1653 1653
           (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
     (1346 1321 (:REWRITE |(equal (/ x) (/ y))|))
     (1321 1321
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (1321 1321
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (1321 1321 (:REWRITE |(equal c (/ x))|))
     (1321 1321 (:REWRITE |(equal (- x) (- y))|))
     (1295 1295
           (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (1295 1295 (:REWRITE |(equal c (- x))|))
     (1295 1295 (:REWRITE |(equal (- x) c)|))
     (1002 48 (:REWRITE DEFAULT-CDR))
     (1002 48 (:REWRITE DEFAULT-CAR))
     (994 41
          (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (676 508 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (442 442 (:REWRITE |(equal (+ (- c) x) y)|))
     (400 58 (:REWRITE ACL2-NUMBERP-X))
     (374 83 (:REWRITE |(+ c (+ d x))|))
     (345 345
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (316 216 (:REWRITE DEFAULT-TIMES-2))
     (266 216 (:REWRITE DEFAULT-TIMES-1))
     (237 121 (:REWRITE O-INFP->NEQ-0))
     (221 196 (:REWRITE |(< 0 (/ x))|))
     (215 215 (:REWRITE |(< 0 (* x y))|))
     (186 24 (:REWRITE RATIONALP-X))
     (178 178
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (178 178
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (132 88 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
     (128 16 (:REWRITE |(- (+ x y))|))
     (124 124
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (114 114 (:LINEAR LEQ-POSITION-EQUAL-LEN))
     (114 3 (:REWRITE NATP-WHEN-GTE-0))
     (91 41
         (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (91 41
         (:REWRITE |(< x (/ y)) with (< y 0)|))
     (88 88 (:TYPE-PRESCRIPTION LL2::PUSH))
     (76 26 (:REWRITE |(equal x (/ y))|))
     (71 71 (:REWRITE NFIX-WHEN-NOT-NATP))
     (71 71 (:REWRITE NFIX-WHEN-NATP))
     (58 46 (:REWRITE DEFAULT-MINUS))
     (51 26 (:REWRITE DEFAULT-DIVIDE))
     (51 26 (:REWRITE |(not (equal x (/ y)))|))
     (34 34 (:REWRITE |(< (+ c/d x) y)|))
     (34 34 (:REWRITE |(< (+ (- c) x) y)|))
     (30 10 (:REWRITE LL2::INTEGER-LISTP-NTH))
     (26 26 (:REWRITE |(< x (+ c/d y))|))
     (25 25 (:REWRITE |(< (/ x) 0)|))
     (25 25 (:REWRITE |(< (* x y) 0)|))
     (24 24 (:TYPE-PRESCRIPTION LL2::KEYP))
     (24 24 (:REWRITE REDUCE-RATIONALP-+))
     (24 24 (:REWRITE REDUCE-RATIONALP-*))
     (24 24 (:REWRITE REDUCE-INTEGERP-+))
     (24 24 (:REWRITE RATIONALP-MINUS-X))
     (24 24 (:REWRITE INTEGERP-MINUS-X))
     (24 24 (:META META-RATIONALP-CORRECT))
     (24 24 (:META META-INTEGERP-CORRECT))
     (22 22 (:REWRITE |(< y (+ (- c) x))|))
     (21 21
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (21 21
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (20 4 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
     (12 12 (:REWRITE FOLD-CONSTS-IN-+))
     (4 4 (:REWRITE |(equal x (if a b c))|))
     (4 4 (:REWRITE |(equal (if a b c) x)|))
     (4 4 (:REWRITE |(- (- x))|))
     (4 4 (:REWRITE |(* x (if a b c))|))
     (2 2 (:REWRITE |(* (if a b c) x)|)))
(LL2::SEM-LOOP-8-=-OCCUR-ARR-TAILREC-0-0
     (249506 2 (:DEFINITION LL2::SEM-LOOP-8))
     (247240 68 (:REWRITE LL2::UPDATE-NTH-REDUNDANT))
     (235764 8732 (:REWRITE LEN-UPDATE-NTH1))
     (165693 445 (:REWRITE NTH-WITH-LARGE-INDEX))
     (81520 256 (:REWRITE NTH-UPDATE-NTH))
     (9226 9099
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (9109 9104 (:REWRITE DEFAULT-LESS-THAN-2))
     (9106 9104 (:REWRITE DEFAULT-LESS-THAN-1))
     (9104 9104 (:REWRITE THE-FLOOR-BELOW))
     (9104 9104 (:REWRITE THE-FLOOR-ABOVE))
     (9104 9104
           (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (9104 9104
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (9104 9104
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (9104 9097
           (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (9103 9102
           (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (9102 9102 (:REWRITE INTEGERP-<-CONSTANT))
     (9102 9102 (:REWRITE CONSTANT-<-INTEGERP))
     (9102 9102
           (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (9102 9102
           (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (9102 9102
           (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (9102 9102 (:REWRITE |(< c (- x))|))
     (9102 9102
           (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (9102 9102
           (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (9102 9102
           (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (9102 9102
           (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (9102 9102 (:REWRITE |(< (/ x) (/ y))|))
     (9102 9102 (:REWRITE |(< (- x) c)|))
     (9102 9102 (:REWRITE |(< (- x) (- y))|))
     (9099 9099
           (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (1016 528
           (:TYPE-PRESCRIPTION TRUE-LISTP-UPDATE-NTH))
     (804 20 (:REWRITE LL2::WR-REDUNDANT))
     (528 528 (:TYPE-PRESCRIPTION UPDATE-NTH))
     (185 185
          (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
     (185 185
          (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
     (180 60 (:REWRITE UPDATE-NTH-UPDATE-NTH . 1))
     (164 2 (:DEFINITION LL2::LOOP-INV))
     (153 79
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (129 79
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (107 81 (:REWRITE |(equal (/ x) c)|))
     (101 79 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (83 81 (:REWRITE |(equal (/ x) (/ y))|))
     (81 81
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (81 81
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (81 81 (:REWRITE |(equal c (/ x))|))
     (81 81 (:REWRITE |(equal (- x) (- y))|))
     (79 79
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (79 79 (:REWRITE |(equal c (- x))|))
     (79 79 (:REWRITE |(equal (- x) c)|))
     (34 18 (:REWRITE DEFAULT-PLUS-2))
     (34 18 (:REWRITE DEFAULT-PLUS-1))
     (23 23
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (20 16 (:REWRITE LL2::SP-WR))
     (16 16 (:TYPE-PRESCRIPTION LL2::PUSH))
     (16 16 (:REWRITE LL2::RD-WR))
     (16 4 (:REWRITE |(* y x)|))
     (14 14 (:REWRITE |(< 0 (* x y))|))
     (14 7 (:REWRITE O-INFP->NEQ-0))
     (12 12
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (12 12
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (12 12 (:REWRITE |(< 0 (/ x))|))
     (10 2 (:REWRITE ACL2-NUMBERP-X))
     (8 8 (:REWRITE DEFAULT-TIMES-2))
     (8 8 (:REWRITE DEFAULT-TIMES-1))
     (8 4 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (6 6 (:LINEAR LEQ-POSITION-EQUAL-LEN))
     (6 2 (:REWRITE |(equal x (/ y))|))
     (4 4 (:REWRITE |(* a (/ a))|))
     (4 2 (:REWRITE LL2::EQUAL-LEN-0))
     (4 2 (:REWRITE DEFAULT-DIVIDE))
     (4 2 (:REWRITE |(not (equal x (/ y)))|))
     (4 2 (:REWRITE |(/ (/ x))|))
     (4 1 (:REWRITE RATIONALP-X))
     (2 2
        (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (2 2
        (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (2 2 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (2 2 (:REWRITE |(< x (/ y)) with (< 0 y)|))
     (1 1 (:REWRITE REDUCE-RATIONALP-+))
     (1 1 (:REWRITE REDUCE-RATIONALP-*))
     (1 1 (:REWRITE REDUCE-INTEGERP-+))
     (1 1 (:REWRITE RATIONALP-MINUS-X))
     (1 1 (:REWRITE INTEGERP-MINUS-X))
     (1 1 (:META META-RATIONALP-CORRECT))
     (1 1 (:META META-INTEGERP-CORRECT)))
(LL2::OCCUR-ARR-TAILREC-LN-NUM-=-NUM
     (20 20
         (:TYPE-PRESCRIPTION LL2::OCCUR-ARR-TAILREC))
     (5 2 (:REWRITE DEFAULT-PLUS-1))
     (4 2 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
     (4 2 (:REWRITE DEFAULT-PLUS-2))
     (2 1 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (2 1 (:REWRITE DEFAULT-MINUS))
     (1 1
        (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
     (1 1
        (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV)))
(LL2::OCCUR-ARR-TAILREC-0-0-VAL-=-0)
(LL2::COMPOSITION-=-OCCUR-ARR-TAILREC
     (1841916 168
              (:REWRITE LL2::UPDATE-NTH-REDUNDANT))
     (1840326 126
              (:REWRITE UPDATE-NTH-UPDATE-NTH . 2))
     (1137968 1334 (:REWRITE NTH-WITH-LARGE-INDEX))
     (68840 68774 (:REWRITE DEFAULT-LESS-THAN-1))
     (68777 68774 (:REWRITE DEFAULT-LESS-THAN-2))
     (68774 68774 (:REWRITE THE-FLOOR-BELOW))
     (68774 68774 (:REWRITE THE-FLOOR-ABOVE))
     (68772 68772
            (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (68772 68772
            (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (68772 68772
            (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (68772 68770
            (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (68770 68770 (:REWRITE INTEGERP-<-CONSTANT))
     (68770 68770 (:REWRITE CONSTANT-<-INTEGERP))
     (68770 68770
            (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (68770 68770
            (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (68770 68770
            (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (68770 68770 (:REWRITE |(< c (- x))|))
     (68770 68770
            (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (68770 68770
            (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (68770 68770
            (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (68770 68770
            (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (68770 68770 (:REWRITE |(< (/ x) (/ y))|))
     (68770 68770 (:REWRITE |(< (- x) c)|))
     (68770 68770 (:REWRITE |(< (- x) (- y))|))
     (68770 68763
            (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (68765 68765
            (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (68763 68763 (:REWRITE SIMPLIFY-SUMS-<))
     (35014 168
            (:REWRITE UPDATE-NTH-UPDATE-NTH . 1))
     (3080 32 (:REWRITE LL2::WR-REDUNDANT))
     (1724 6 (:REWRITE LL2::WR-WR-DIFF))
     (470 6 (:REWRITE LL2::WR-WR-SAME))
     (325 203
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (292 203
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (278 203 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (264 16 (:REWRITE DEFAULT-CDR))
     (264 16 (:REWRITE DEFAULT-CAR))
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
     (150 4 (:REWRITE NATP-WHEN-GTE-0))
     (146 146
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (119 119
          (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
     (119 119
          (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
     (24 24 (:REWRITE |(< 0 (* x y))|))
     (22 22 (:REWRITE |(< 0 (/ x))|))
     (21 21
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (21 21
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (18 18 (:TYPE-PRESCRIPTION LL2::KEYP))
     (17 4
         (:REWRITE LL2::OCCUR-ARR-TAILREC-LN-NUM-=-NUM))
     (16 16 (:TYPE-PRESCRIPTION LL2::PUSH))
     (12 12 (:LINEAR LEQ-POSITION-EQUAL-LEN))
     (8 8 (:REWRITE DEFAULT-TIMES-2))
     (8 8 (:REWRITE DEFAULT-TIMES-1))
     (8 4 (:REWRITE O-INFP->NEQ-0))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (6 6 (:REWRITE |(< (/ x) 0)|))
     (6 6 (:REWRITE |(< (* x y) 0)|))
     (4 4 (:REWRITE ACL2-NUMBERP-X))
     (3 3 (:REWRITE DEFAULT-PLUS-2))
     (3 3 (:REWRITE DEFAULT-PLUS-1))
     (2 2 (:REWRITE REDUCE-INTEGERP-+))
     (2 2 (:REWRITE INTEGERP-MINUS-X))
     (2 2
        (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (2 2
        (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (2 2 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (2 2 (:META META-INTEGERP-CORRECT)))
(LL2::OCCUR-ARR-ITER-=-OCCURLIST-TAKE--THM
     (695 8 (:REWRITE NTH-WITH-LARGE-INDEX))
     (504 76
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (424 9 (:REWRITE NATP-WHEN-INTEGERP))
     (404 12 (:REWRITE ZP-WHEN-GT-0))
     (271 15
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (240 24 (:REWRITE ACL2-NUMBERP-X))
     (231 7 (:REWRITE NFIX-WHEN-NATP))
     (186 5 (:REWRITE |(< (+ (- c) x) y)|))
     (180 6 (:REWRITE RATIONALP-X))
     (178 79 (:REWRITE DEFAULT-LESS-THAN-1))
     (147 7 (:REWRITE NFIX-WHEN-NOT-NATP))
     (144 2 (:REWRITE LL2::INTEGER-LISTP-NTH))
     (102 81 (:REWRITE DEFAULT-PLUS-2))
     (83 79 (:REWRITE DEFAULT-LESS-THAN-2))
     (81 81 (:REWRITE DEFAULT-PLUS-1))
     (79 79 (:REWRITE THE-FLOOR-BELOW))
     (79 79 (:REWRITE THE-FLOOR-ABOVE))
     (76 76
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (76 76
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (76 18 (:REWRITE |(+ c (+ d x))|))
     (65 57
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (65 57 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (64 57 (:REWRITE SIMPLIFY-SUMS-<))
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
     (55 15 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (55 15
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (45 39 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (34 34
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (34 34 (:REWRITE NORMALIZE-ADDENDS))
     (30 22 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
     (28 28 (:REWRITE |(< 0 (* x y))|))
     (22 22
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (22 22
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (22 22 (:REWRITE |(< 0 (/ x))|))
     (19 19 (:TYPE-PRESCRIPTION NFIX))
     (16 16 (:REWRITE |(< x (+ c/d y))|))
     (15 15
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (15 15
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (15 15
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (15 15 (:REWRITE DEFAULT-CDR))
     (15 15 (:REWRITE |(equal c (/ x))|))
     (15 15 (:REWRITE |(equal c (- x))|))
     (15 15 (:REWRITE |(equal (/ x) c)|))
     (15 15 (:REWRITE |(equal (/ x) (/ y))|))
     (15 15 (:REWRITE |(equal (- x) c)|))
     (15 15 (:REWRITE |(equal (- x) (- y))|))
     (14 14 (:REWRITE REDUCE-INTEGERP-+))
     (14 14 (:REWRITE INTEGERP-MINUS-X))
     (14 14 (:META META-INTEGERP-CORRECT))
     (13 13 (:REWRITE |(< (+ c/d x) y)|))
     (12 12 (:REWRITE |(< (* x y) 0)|))
     (10 10 (:REWRITE DEFAULT-CAR))
     (10 10 (:REWRITE |(< y (+ (- c) x))|))
     (6 6 (:REWRITE REDUCE-RATIONALP-+))
     (6 6 (:REWRITE REDUCE-RATIONALP-*))
     (6 6 (:REWRITE RATIONALP-MINUS-X))
     (6 6 (:META META-RATIONALP-CORRECT))
     (6 6 (:LINEAR LEQ-POSITION-EQUAL-LEN))
     (5 1 (:DEFINITION BINARY-APPEND))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (4 4 (:REWRITE |(< (/ x) 0)|))
     (2 2
        (:REWRITE INEQUALITY-WITH-NFIX-HYP-2)))
(LL2::OCCUR-ARR-ITER-=-OCCURLIST
     (74 2 (:DEFINITION LL2::OCCURLIST))
     (22 6 (:REWRITE ACL2-NUMBERP-X))
     (20 2
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (8 4 (:REWRITE DEFAULT-PLUS-2))
     (8 2 (:REWRITE RATIONALP-X))
     (4 4 (:REWRITE DEFAULT-PLUS-1))
     (4 4 (:REWRITE DEFAULT-CDR))
     (4 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (4 2
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (4 2 (:REWRITE |(+ 0 x)|))
     (3 3 (:REWRITE REDUCE-INTEGERP-+))
     (3 3 (:REWRITE INTEGERP-MINUS-X))
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
     (2 2 (:REWRITE DEFAULT-CAR))
     (2 2 (:REWRITE |(equal c (/ x))|))
     (2 2 (:REWRITE |(equal c (- x))|))
     (2 2 (:REWRITE |(equal (/ x) c)|))
     (2 2 (:REWRITE |(equal (/ x) (/ y))|))
     (2 2 (:REWRITE |(equal (- x) c)|))
     (2 2 (:REWRITE |(equal (- x) (- y))|))
     (2 2 (:META META-RATIONALP-CORRECT)))
(LL2::OCCUR-ARR-TAILREC-=-OCCURLIST
     (74 2 (:DEFINITION LL2::OCCURLIST))
     (22 6 (:REWRITE ACL2-NUMBERP-X))
     (20 2
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (10 10 (:TYPE-PRESCRIPTION LEN))
     (10 1
         (:REWRITE LL2::OCCUR-ARR-TAILREC-LN-NUM-=-NUM))
     (10 1
         (:REWRITE LL2::OCCUR-ARR-TAILREC-0-0-VAL-=-0))
     (8 4 (:REWRITE DEFAULT-PLUS-2))
     (8 2 (:REWRITE RATIONALP-X))
     (4 4 (:REWRITE DEFAULT-PLUS-1))
     (4 4 (:REWRITE DEFAULT-CDR))
     (4 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (4 2
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (4 2 (:REWRITE LL2::EQUAL-LEN-0))
     (4 2 (:REWRITE |(+ 0 x)|))
     (3 3 (:REWRITE REDUCE-INTEGERP-+))
     (3 3 (:REWRITE INTEGERP-MINUS-X))
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
     (2 2 (:REWRITE DEFAULT-CAR))
     (2 2 (:REWRITE |(equal c (/ x))|))
     (2 2 (:REWRITE |(equal c (- x))|))
     (2 2 (:REWRITE |(equal (/ x) c)|))
     (2 2 (:REWRITE |(equal (/ x) (/ y))|))
     (2 2 (:REWRITE |(equal (- x) c)|))
     (2 2 (:REWRITE |(equal (- x) (- y))|))
     (2 2 (:META META-RATIONALP-CORRECT))
     (2 2 (:LINEAR LEQ-POSITION-EQUAL-LEN)))
(LL2::COMPOSITION-=-OCCURLIST
     (1975068 214
              (:REWRITE LL2::UPDATE-NTH-REDUNDANT))
     (1839838 126
              (:REWRITE UPDATE-NTH-UPDATE-NTH . 2))
     (1225439 1610 (:REWRITE NTH-WITH-LARGE-INDEX))
     (73874 73602 (:REWRITE DEFAULT-LESS-THAN-1))
     (73655 73582
            (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (73626 73602 (:REWRITE DEFAULT-LESS-THAN-2))
     (73602 73602 (:REWRITE THE-FLOOR-BELOW))
     (73602 73602 (:REWRITE THE-FLOOR-ABOVE))
     (73596 73582 (:REWRITE SIMPLIFY-SUMS-<))
     (73595 73591
            (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (73592 73592
            (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (73592 73592
            (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (73592 73592
            (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (73591 73591 (:REWRITE INTEGERP-<-CONSTANT))
     (73591 73591 (:REWRITE CONSTANT-<-INTEGERP))
     (73591 73591
            (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (73591 73591
            (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (73591 73591
            (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (73591 73591 (:REWRITE |(< c (- x))|))
     (73591 73591
            (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (73591 73591
            (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (73591 73591
            (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (73591 73591
            (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (73591 73591 (:REWRITE |(< (/ x) (/ y))|))
     (73591 73591 (:REWRITE |(< (- x) c)|))
     (73591 73591 (:REWRITE |(< (- x) (- y))|))
     (73546 73544
            (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (35107 207
            (:REWRITE UPDATE-NTH-UPDATE-NTH . 1))
     (18445 48 (:REWRITE LL2::WR-REDUNDANT))
     (6128 6128 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (1724 6 (:REWRITE LL2::WR-WR-DIFF))
     (994 280
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (658 280 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (544 53 (:REWRITE ACL2-NUMBERP-X))
     (537 280
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (519 19 (:REWRITE NATP-WHEN-GTE-0))
     (470 6 (:REWRITE LL2::WR-WR-SAME))
     (409 3 (:REWRITE NFIX-WHEN-NATP))
     (385 13 (:REWRITE RATIONALP-X))
     (283 282 (:REWRITE |(equal (/ x) (/ y))|))
     (283 3 (:REWRITE NFIX-WHEN-NOT-NATP))
     (282 282
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (282 282
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (282 282 (:REWRITE |(equal c (/ x))|))
     (282 282 (:REWRITE |(equal (- x) (- y))|))
     (280 280
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (280 280 (:REWRITE |(equal c (- x))|))
     (280 280 (:REWRITE |(equal (- x) c)|))
     (279 4 (:REWRITE LL2::INTEGER-LISTP-NTH))
     (270 22 (:REWRITE DEFAULT-CDR))
     (267 19 (:REWRITE DEFAULT-CAR))
     (228 228
          (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
     (228 228
          (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
     (220 220 (:LINEAR LEQ-POSITION-EQUAL-LEN))
     (167 167
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (128 1
          (:REWRITE LL2::SEM-LOOP-8-=-OCCUR-ARR-TAILREC))
     (120 8 (:REWRITE |(+ y x)|))
     (115 58 (:REWRITE DEFAULT-PLUS-2))
     (102 58 (:REWRITE DEFAULT-PLUS-1))
     (102 30 (:REWRITE NORMALIZE-ADDENDS))
     (80 4 (:REWRITE |(+ y (+ x z))|))
     (70 3
         (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (70 3 (:REWRITE |(< x (/ y)) with (< 0 y)|))
     (35 35
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (35 35
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (35 35 (:REWRITE |(< (/ x) 0)|))
     (35 35 (:REWRITE |(< (* x y) 0)|))
     (34 34 (:REWRITE |(< 0 (* x y))|))
     (34 33 (:REWRITE |(< 0 (/ x))|))
     (33 33
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (33 33
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (27 16 (:REWRITE O-INFP->NEQ-0))
     (24 24 (:TYPE-PRESCRIPTION LL2::PUSH))
     (22 22
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (21 21 (:REWRITE |(< (+ c/d x) y)|))
     (21 21 (:REWRITE |(< (+ (- c) x) y)|))
     (20 20 (:REWRITE REDUCE-INTEGERP-+))
     (20 20 (:REWRITE INTEGERP-MINUS-X))
     (20 20 (:META META-INTEGERP-CORRECT))
     (20 16 (:REWRITE DEFAULT-TIMES-2))
     (18 18 (:TYPE-PRESCRIPTION LL2::KEYP))
     (18 16 (:REWRITE DEFAULT-TIMES-1))
     (16 8 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (16 8 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
     (14 14 (:REWRITE |(equal (+ (- c) x) y)|))
     (13 13 (:REWRITE REDUCE-RATIONALP-+))
     (13 13 (:REWRITE REDUCE-RATIONALP-*))
     (13 13 (:REWRITE RATIONALP-MINUS-X))
     (13 13 (:META META-RATIONALP-CORRECT))
     (8 8 (:REWRITE |(+ x (- x))|))
     (5 3
        (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (5 3 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (4 4 (:REWRITE |(equal x (if a b c))|))
     (4 4 (:REWRITE |(equal (if a b c) x)|))
     (4 4 (:REWRITE |(* x (if a b c))|))
     (4 2 (:REWRITE |(equal x (/ y))|))
     (3 3 (:REWRITE INEQUALITY-WITH-NFIX-HYP-2))
     (3 2 (:REWRITE DEFAULT-DIVIDE))
     (3 2 (:REWRITE |(not (equal x (/ y)))|))
     (2 2 (:REWRITE |(* (if a b c) x)|))
     (1 1 (:REWRITE |(< y (+ (- c) x))|))
     (1 1 (:REWRITE |(< x (+ c/d y))|)))
(LL2::LL2-RUNNING-OCCURRENCES-CODE-=-OCCURLIST
     (2764004 256
              (:REWRITE LL2::UPDATE-NTH-REDUNDANT))
     (2760490 189
              (:REWRITE UPDATE-NTH-UPDATE-NTH . 2))
     (1851066 1 (:DEFINITION LL2::SEM-LOOP-8))
     (1704075 2045 (:REWRITE NTH-WITH-LARGE-INDEX))
     (103094 103090 (:REWRITE DEFAULT-LESS-THAN-1))
     (103093 103090 (:REWRITE DEFAULT-LESS-THAN-2))
     (103090 103090 (:REWRITE THE-FLOOR-BELOW))
     (103090 103090 (:REWRITE THE-FLOOR-ABOVE))
     (103090 103090
             (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (103090 103090
             (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (103090 103090
             (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (103089 103087
             (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (103087 103087 (:REWRITE INTEGERP-<-CONSTANT))
     (103087 103087 (:REWRITE CONSTANT-<-INTEGERP))
     (103087 103087
             (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (103087 103087
             (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (103087 103087
             (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (103087 103087 (:REWRITE |(< c (- x))|))
     (103087 103087
             (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (103087 103087
             (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (103087 103087
             (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (103087 103087
             (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (103087 103087 (:REWRITE |(< (/ x) (/ y))|))
     (103087 103087 (:REWRITE |(< (- x) c)|))
     (103087 103087 (:REWRITE |(< (- x) (- y))|))
     (103082 103075
             (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (103078 103078
             (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (103075 103075 (:REWRITE SIMPLIFY-SUMS-<))
     (52530 255
            (:REWRITE UPDATE-NTH-UPDATE-NTH . 1))
     (4430 46 (:REWRITE LL2::WR-REDUNDANT))
     (2448 8 (:REWRITE LL2::WR-WR-DIFF))
     (660 8 (:REWRITE LL2::WR-WR-SAME))
     (487 296
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (468 296
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (413 296 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (400 28 (:REWRITE DEFAULT-CDR))
     (398 26 (:REWRITE DEFAULT-CAR))
     (296 296
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (296 296
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (296 296
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (296 296 (:REWRITE |(equal c (/ x))|))
     (296 296 (:REWRITE |(equal c (- x))|))
     (296 296 (:REWRITE |(equal (/ x) c)|))
     (296 296 (:REWRITE |(equal (/ x) (/ y))|))
     (296 296 (:REWRITE |(equal (- x) c)|))
     (296 296 (:REWRITE |(equal (- x) (- y))|))
     (224 224
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (199 199
          (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
     (199 199
          (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
     (76 2 (:REWRITE NATP-WHEN-GTE-0))
     (50 50 (:TYPE-PRESCRIPTION LL2::LL2))
     (42 10 (:REWRITE ACL2-NUMBERP-X))
     (28 28 (:REWRITE |(< 0 (* x y))|))
     (25 25 (:REWRITE |(< 0 (/ x))|))
     (24 24 (:TYPE-PRESCRIPTION LL2::KEYP))
     (23 23
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (23 23
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (20 6 (:REWRITE O-INFP->NEQ-0))
     (16 16 (:TYPE-PRESCRIPTION LL2::PUSH))
     (16 4 (:REWRITE RATIONALP-X))
     (13 9 (:REWRITE DEFAULT-PLUS-2))
     (12 12 (:REWRITE DEFAULT-TIMES-2))
     (12 12 (:REWRITE DEFAULT-TIMES-1))
     (12 12 (:LINEAR LEQ-POSITION-EQUAL-LEN))
     (9 9 (:REWRITE DEFAULT-PLUS-1))
     (6 6 (:TYPE-PRESCRIPTION O-FINP))
     (6 2 (:REWRITE O-FIRST-EXPT-O-INFP))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (4 4 (:REWRITE REDUCE-RATIONALP-+))
     (4 4 (:REWRITE REDUCE-RATIONALP-*))
     (4 4 (:REWRITE REDUCE-INTEGERP-+))
     (4 4 (:REWRITE RATIONALP-MINUS-X))
     (4 4 (:REWRITE INTEGERP-MINUS-X))
     (4 4 (:REWRITE |(< (/ x) 0)|))
     (4 4 (:REWRITE |(< (* x y) 0)|))
     (4 4 (:META META-RATIONALP-CORRECT))
     (4 4 (:META META-INTEGERP-CORRECT))
     (4 2 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
     (3 3
        (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (3 3
        (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (3 3 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (2 2
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (2 2 (:REWRITE NORMALIZE-ADDENDS)))
