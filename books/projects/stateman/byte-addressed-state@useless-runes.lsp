(SMAN::NATP-NTH-MP
     (59 47
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (58 48 (:REWRITE DEFAULT-LESS-THAN-2))
     (55 45
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (55 45 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (54 45 (:REWRITE SIMPLIFY-SUMS-<))
     (48 48 (:REWRITE THE-FLOOR-BELOW))
     (48 48 (:REWRITE THE-FLOOR-ABOVE))
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
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (47 47
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (47 47
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (47 47
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (47 47 (:REWRITE |(< (/ x) (/ y))|))
     (47 47 (:REWRITE |(< (- x) c)|))
     (47 47 (:REWRITE |(< (- x) (- y))|))
     (31 21 (:REWRITE DEFAULT-PLUS-2))
     (26 26 (:REWRITE |(< (/ x) 0)|))
     (26 26 (:REWRITE |(< (* x y) 0)|))
     (24 24
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (24 24
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (24 24 (:REWRITE REDUCE-INTEGERP-+))
     (24 24 (:REWRITE INTEGERP-MINUS-X))
     (24 24 (:META META-INTEGERP-CORRECT))
     (21 21
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (21 21 (:REWRITE NORMALIZE-ADDENDS))
     (21 21 (:REWRITE DEFAULT-PLUS-1))
     (20 20 (:REWRITE DEFAULT-CDR))
     (20 20 (:REWRITE DEFAULT-CAR))
     (18 2 (:REWRITE ACL2-NUMBERP-X))
     (9 9 (:REWRITE ZP-OPEN))
     (8 2 (:REWRITE RATIONALP-X))
     (3 3 (:REWRITE |(< y (+ (- c) x))|))
     (3 3 (:REWRITE |(< x (+ c/d y))|))
     (2 2 (:REWRITE REDUCE-RATIONALP-+))
     (2 2 (:REWRITE REDUCE-RATIONALP-*))
     (2 2 (:REWRITE RATIONALP-MINUS-X))
     (2 2 (:REWRITE |(< (+ c/d x) y)|))
     (2 2 (:REWRITE |(< (+ (- c) x) y)|))
     (2 2 (:META META-RATIONALP-CORRECT))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (1 1 (:REWRITE |(< 0 (/ x))|))
     (1 1 (:REWRITE |(< 0 (* x y))|)))
(SMAN::BYTEP-NTH-MP
     (84 4 (:REWRITE ACL2-NUMBERP-X))
     (45 37 (:REWRITE DEFAULT-LESS-THAN-2))
     (43 33
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (40 4 (:REWRITE RATIONALP-X))
     (39 30
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (39 30 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (37 37 (:REWRITE THE-FLOOR-BELOW))
     (37 37 (:REWRITE THE-FLOOR-ABOVE))
     (37 33
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (36 30 (:REWRITE SIMPLIFY-SUMS-<))
     (34 34
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (34 34
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (34 34
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
     (33 33 (:REWRITE |(< c (- x))|))
     (33 33
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (33 33
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (33 33
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (33 33 (:REWRITE |(< (/ x) (/ y))|))
     (33 33 (:REWRITE |(< (- x) c)|))
     (33 33 (:REWRITE |(< (- x) (- y))|))
     (19 11 (:REWRITE DEFAULT-PLUS-2))
     (16 16 (:REWRITE REDUCE-INTEGERP-+))
     (16 16 (:REWRITE INTEGERP-MINUS-X))
     (16 16 (:META META-INTEGERP-CORRECT))
     (13 13 (:REWRITE |(< (/ x) 0)|))
     (13 13 (:REWRITE |(< (* x y) 0)|))
     (11 11
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (11 11 (:REWRITE NORMALIZE-ADDENDS))
     (11 11 (:REWRITE DEFAULT-PLUS-1))
     (11 11 (:REWRITE DEFAULT-CAR))
     (10 10
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (10 10
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (6 6 (:REWRITE DEFAULT-CDR))
     (5 5 (:REWRITE ZP-OPEN))
     (5 5 (:REWRITE |(< y (+ (- c) x))|))
     (5 5 (:REWRITE |(< x (+ c/d y))|))
     (4 4 (:REWRITE REDUCE-RATIONALP-+))
     (4 4 (:REWRITE REDUCE-RATIONALP-*))
     (4 4 (:REWRITE RATIONALP-MINUS-X))
     (4 4 (:META META-RATIONALP-CORRECT))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (1 1 (:REWRITE |(< 0 (/ x))|))
     (1 1 (:REWRITE |(< 0 (* x y))|))
     (1 1 (:REWRITE |(< (+ c/d x) y)|)))
(SMAN::MP-!NTH
     (72 62 (:REWRITE DEFAULT-LESS-THAN-2))
     (65 59
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (64 56
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (64 56 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (63 56 (:REWRITE SIMPLIFY-SUMS-<))
     (63 7 (:REWRITE ACL2-NUMBERP-X))
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
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (59 59
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (59 59
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (59 59
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (59 59 (:REWRITE |(< (/ x) (/ y))|))
     (59 59 (:REWRITE |(< (- x) c)|))
     (59 59 (:REWRITE |(< (- x) (- y))|))
     (40 25 (:REWRITE DEFAULT-CDR))
     (37 22 (:REWRITE DEFAULT-CAR))
     (28 28 (:REWRITE REDUCE-INTEGERP-+))
     (28 28 (:REWRITE INTEGERP-MINUS-X))
     (28 28 (:META META-INTEGERP-CORRECT))
     (28 7 (:REWRITE RATIONALP-X))
     (26 26 (:REWRITE |(< (/ x) 0)|))
     (26 26 (:REWRITE |(< (* x y) 0)|))
     (23 23
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (23 23
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (20 12 (:REWRITE DEFAULT-PLUS-2))
     (12 12
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (12 12 (:REWRITE NORMALIZE-ADDENDS))
     (12 12 (:REWRITE DEFAULT-PLUS-1))
     (7 7 (:REWRITE ZP-OPEN))
     (7 7 (:REWRITE REDUCE-RATIONALP-+))
     (7 7 (:REWRITE REDUCE-RATIONALP-*))
     (7 7 (:REWRITE RATIONALP-MINUS-X))
     (7 7 (:META META-RATIONALP-CORRECT))
     (4 4 (:REWRITE |(< y (+ (- c) x))|))
     (4 4 (:REWRITE |(< x (+ c/d y))|))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (1 1 (:REWRITE |(< 0 (/ x))|))
     (1 1 (:REWRITE |(< 0 (* x y))|))
     (1 1 (:REWRITE |(< (+ c/d x) y)|)))
(SMAN::!NTH-NTH
     (24 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (24 4
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (24 4
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (23 15 (:REWRITE DEFAULT-PLUS-2))
     (23 15 (:REWRITE DEFAULT-LESS-THAN-2))
     (20 14
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (18 11
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (18 11 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (17 11 (:REWRITE SIMPLIFY-SUMS-<))
     (15 15 (:REWRITE THE-FLOOR-BELOW))
     (15 15 (:REWRITE THE-FLOOR-ABOVE))
     (15 15
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (15 15
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (15 15
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (15 15
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (15 15 (:REWRITE NORMALIZE-ADDENDS))
     (15 15 (:REWRITE DEFAULT-PLUS-1))
     (15 15 (:REWRITE DEFAULT-LESS-THAN-1))
     (14 14 (:REWRITE INTEGERP-<-CONSTANT))
     (14 14 (:REWRITE DEFAULT-CDR))
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
     (8 8 (:REWRITE ZP-OPEN))
     (8 8 (:REWRITE DEFAULT-CAR))
     (7 7 (:REWRITE |(< (/ x) 0)|))
     (7 7 (:REWRITE |(< (* x y) 0)|))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
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
     (4 4 (:REWRITE |(< y (+ (- c) x))|))
     (4 4 (:REWRITE |(< x (+ c/d y))|))
     (4 4 (:META META-INTEGERP-CORRECT))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (1 1 (:REWRITE |(< 0 (/ x))|))
     (1 1 (:REWRITE |(< 0 (* x y))|))
     (1 1 (:REWRITE |(< (+ c/d x) y)|)))
(SMAN::!NTH-!NTH-SAME
     (770 19 (:REWRITE SMAN::!NTH-NTH))
     (279 7 (:REWRITE |(< (+ (- c) x) y)|))
     (202 11 (:DEFINITION LEN))
     (180 2 (:REWRITE LEN-UPDATE-NTH))
     (146 146 (:TYPE-PRESCRIPTION LEN))
     (88 34 (:REWRITE DEFAULT-CDR))
     (84 22
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (84 2 (:DEFINITION NFIX))
     (78 3 (:REWRITE |(< x (if a b c))|))
     (68 2 (:DEFINITION MAX))
     (60 15 (:REWRITE DEFAULT-CAR))
     (58 37 (:REWRITE DEFAULT-PLUS-2))
     (43 24 (:REWRITE DEFAULT-LESS-THAN-2))
     (37 37 (:REWRITE DEFAULT-PLUS-1))
     (30 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (30 3
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (30 3
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (28 28
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (28 28 (:REWRITE NORMALIZE-ADDENDS))
     (26 24 (:REWRITE DEFAULT-LESS-THAN-1))
     (24 24 (:REWRITE THE-FLOOR-BELOW))
     (24 24 (:REWRITE THE-FLOOR-ABOVE))
     (22 22
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (22 22
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (22 13 (:REWRITE SIMPLIFY-SUMS-<))
     (22 13
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (22 13 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (16 4 (:REWRITE |(+ c (+ d x))|))
     (13 13
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
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
     (12 1 (:REWRITE |(+ x (if a b c))|))
     (9 9 (:REWRITE |(< (+ c/d x) y)|))
     (8 8 (:REWRITE ZP-OPEN))
     (8 8 (:REWRITE |(< y (+ (- c) x))|))
     (8 8 (:REWRITE |(< x (+ c/d y))|))
     (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (4 4 (:REWRITE |(+ 0 x)|))
     (3 3
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (3 3 (:REWRITE REDUCE-INTEGERP-+))
     (3 3
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (3 3 (:REWRITE INTEGERP-MINUS-X))
     (3 3
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (3 3 (:REWRITE |(equal c (/ x))|))
     (3 3 (:REWRITE |(equal c (- x))|))
     (3 3 (:REWRITE |(equal (/ x) c)|))
     (3 3 (:REWRITE |(equal (/ x) (/ y))|))
     (3 3 (:REWRITE |(equal (- x) c)|))
     (3 3 (:REWRITE |(equal (- x) (- y))|))
     (3 3 (:META META-INTEGERP-CORRECT))
     (2 2 (:REWRITE |(< (* x y) 0)|)))
(SMAN::!NTH-!NTH-DIFF
     (6210 90 (:REWRITE SMAN::!NTH-NTH))
     (1579 72 (:DEFINITION LEN))
     (1415 37 (:REWRITE |(< (+ (- c) x) y)|))
     (1396 16 (:REWRITE LEN-UPDATE-NTH))
     (1359 225
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (887 887 (:TYPE-PRESCRIPTION LEN))
     (858 14 (:REWRITE |(< x (if a b c))|))
     (823 37 (:REWRITE ZP-OPEN))
     (628 16 (:DEFINITION NFIX))
     (552 16 (:DEFINITION MAX))
     (447 322 (:REWRITE DEFAULT-PLUS-2))
     (422 200 (:REWRITE DEFAULT-CDR))
     (341 237 (:REWRITE DEFAULT-LESS-THAN-2))
     (322 322 (:REWRITE DEFAULT-PLUS-1))
     (313 72 (:REWRITE |(+ c (+ d x))|))
     (253 237 (:REWRITE DEFAULT-LESS-THAN-1))
     (237 237 (:REWRITE THE-FLOOR-BELOW))
     (237 237 (:REWRITE THE-FLOOR-ABOVE))
     (225 225
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (225 225
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (222 66 (:REWRITE DEFAULT-CAR))
     (209 151
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (207 151 (:REWRITE SIMPLIFY-SUMS-<))
     (207 151
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (196 196
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (196 196 (:REWRITE NORMALIZE-ADDENDS))
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
     (116 20
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (84 20 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (84 20
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (79 79 (:REWRITE |(< x (+ c/d y))|))
     (75 75 (:REWRITE |(< y (+ (- c) x))|))
     (72 6 (:REWRITE |(+ x (if a b c))|))
     (70 70 (:REWRITE |(< (+ c/d x) y)|))
     (48 48 (:REWRITE |(+ 0 x)|))
     (47 47 (:REWRITE |(< (* x y) 0)|))
     (44 12 (:REWRITE ACL2-NUMBERP-X))
     (25 25 (:REWRITE |(< 0 (* x y))|))
     (22 22
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (22 22
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (22 22 (:REWRITE |(< 0 (/ x))|))
     (20 20
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (20 20
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (20 20
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (20 20 (:REWRITE |(equal c (/ x))|))
     (20 20 (:REWRITE |(equal c (- x))|))
     (20 20 (:REWRITE |(equal (/ x) c)|))
     (20 20 (:REWRITE |(equal (/ x) (/ y))|))
     (20 20 (:REWRITE |(equal (- x) c)|))
     (20 20 (:REWRITE |(equal (- x) (- y))|))
     (20 4
         (:TYPE-PRESCRIPTION SMAN::NATP-NTH-MP))
     (16 4 (:REWRITE RATIONALP-X))
     (15 15 (:REWRITE |(< (/ x) 0)|))
     (14 14
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (14 14
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (13 13 (:REWRITE REDUCE-INTEGERP-+))
     (13 13 (:REWRITE INTEGERP-MINUS-X))
     (13 13 (:META META-INTEGERP-CORRECT))
     (4 4 (:TYPE-PRESCRIPTION SMAN::MP))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (4 4 (:REWRITE REDUCE-RATIONALP-+))
     (4 4 (:REWRITE REDUCE-RATIONALP-*))
     (4 4 (:REWRITE RATIONALP-MINUS-X))
     (4 4 (:REWRITE NTH-0-CONS))
     (4 4 (:META META-RATIONALP-CORRECT))
     (1 1 (:REWRITE |(equal x (if a b c))|))
     (1 1 (:REWRITE |(equal (if a b c) x)|)))
(SMAN::NTH-0-1-2 (90 45
                     (:TYPE-PRESCRIPTION SMAN::NATP-NTH-MP))
                 (45 45 (:TYPE-PRESCRIPTION SMAN::MP))
                 (33 9 (:REWRITE ACL2-NUMBERP-X))
                 (30 3
                     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                 (12 3 (:REWRITE RATIONALP-X))
                 (10 10 (:REWRITE DEFAULT-CDR))
                 (6 6 (:REWRITE DEFAULT-CAR))
                 (6 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                 (6 3
                    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                 (3 3 (:REWRITE REDUCE-RATIONALP-+))
                 (3 3 (:REWRITE REDUCE-RATIONALP-*))
                 (3 3
                    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                 (3 3 (:REWRITE REDUCE-INTEGERP-+))
                 (3 3
                    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
                 (3 3 (:REWRITE RATIONALP-MINUS-X))
                 (3 3 (:REWRITE INTEGERP-MINUS-X))
                 (3 3
                    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
                 (3 3 (:REWRITE |(equal x (if a b c))|))
                 (3 3 (:REWRITE |(equal c (/ x))|))
                 (3 3 (:REWRITE |(equal c (- x))|))
                 (3 3 (:REWRITE |(equal (if a b c) x)|))
                 (3 3 (:REWRITE |(equal (/ x) c)|))
                 (3 3 (:REWRITE |(equal (/ x) (/ y))|))
                 (3 3 (:REWRITE |(equal (- x) c)|))
                 (3 3 (:REWRITE |(equal (- x) (- y))|))
                 (3 3 (:META META-RATIONALP-CORRECT))
                 (3 3 (:META META-INTEGERP-CORRECT)))
(SMAN::UPDATE-NTH-0-1-2
     (674 10 (:REWRITE SMAN::!NTH-NTH))
     (306 25 (:DEFINITION LEN))
     (114 114 (:TYPE-PRESCRIPTION LEN))
     (93 93 (:REWRITE DEFAULT-CDR))
     (90 45
         (:TYPE-PRESCRIPTION TRUE-LISTP-UPDATE-NTH))
     (80 40 (:REWRITE DEFAULT-PLUS-2))
     (45 45 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (40 40
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (40 40 (:REWRITE NORMALIZE-ADDENDS))
     (40 40 (:REWRITE DEFAULT-PLUS-1))
     (20 10
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (20 10 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (20 10 (:REWRITE DEFAULT-LESS-THAN-2))
     (14 10
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (10 10 (:REWRITE THE-FLOOR-BELOW))
     (10 10 (:REWRITE THE-FLOOR-ABOVE))
     (10 10 (:REWRITE SIMPLIFY-SUMS-<))
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
     (10 10 (:REWRITE DEFAULT-CAR))
     (10 10 (:REWRITE CONSTANT-<-INTEGERP))
     (10 10 (:REWRITE |(< x (if a b c))|))
     (10 10
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
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
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (6 6 (:REWRITE |(< 0 (/ x))|))
     (6 6 (:REWRITE |(< 0 (* x y))|))
     (5 5 (:REWRITE |(+ x (if a b c))|)))
(SMAN::NATP-I)
(SMAN::NATP-MI (2 2
                  (:TYPE-PRESCRIPTION SMAN::NATP-NTH-MP)))
(SMAN::BYTEP-MI (4 4
                   (:TYPE-PRESCRIPTION SMAN::NATP-NTH-MP)))
(SMAN::STP-!I
     (37 37 (:REWRITE DEFAULT-CDR))
     (28 14 (:REWRITE DEFAULT-PLUS-2))
     (14 14 (:REWRITE DEFAULT-PLUS-1))
     (12 12
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (12 12 (:REWRITE NORMALIZE-ADDENDS))
     (9 9 (:REWRITE DEFAULT-CAR))
     (7 7 (:REWRITE THE-FLOOR-BELOW))
     (7 7 (:REWRITE THE-FLOOR-ABOVE))
     (7 7 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (7 7
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (7 7
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (7 7 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (7 7 (:REWRITE INTEGERP-<-CONSTANT))
     (7 7 (:REWRITE DEFAULT-LESS-THAN-2))
     (7 7 (:REWRITE DEFAULT-LESS-THAN-1))
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
     (6 6 (:REWRITE SIMPLIFY-SUMS-<))
     (6 6
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (6 6 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (5 5 (:REWRITE |(< (/ x) 0)|))
     (5 5 (:REWRITE |(< (* x y) 0)|))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (4 4 (:REWRITE REDUCE-INTEGERP-+))
     (4 4 (:REWRITE INTEGERP-MINUS-X))
     (4 4 (:META META-INTEGERP-CORRECT))
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
     (1 1 (:REWRITE |(equal (+ (- c) x) y)|)))
(SMAN::STP-!S
     (36 36 (:REWRITE DEFAULT-CDR))
     (28 14 (:REWRITE DEFAULT-PLUS-2))
     (14 14 (:REWRITE DEFAULT-PLUS-1))
     (12 12
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (12 12 (:REWRITE NORMALIZE-ADDENDS))
     (10 10 (:REWRITE DEFAULT-CAR))
     (6 6 (:REWRITE THE-FLOOR-BELOW))
     (6 6 (:REWRITE THE-FLOOR-ABOVE))
     (6 6 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (6 6
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (6 6
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (6 6 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
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
     (6 6 (:REWRITE |(< (/ x) (/ y))|))
     (6 6 (:REWRITE |(< (- x) c)|))
     (6 6 (:REWRITE |(< (- x) (- y))|))
     (5 5 (:REWRITE SIMPLIFY-SUMS-<))
     (5 5
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (5 5 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (4 4 (:REWRITE |(< (/ x) 0)|))
     (4 4 (:REWRITE |(< (* x y) 0)|))
     (4 2
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (4 2
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (3 3 (:REWRITE REDUCE-INTEGERP-+))
     (3 3 (:REWRITE INTEGERP-MINUS-X))
     (3 3 (:META META-INTEGERP-CORRECT))
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
     (1 1 (:REWRITE |(equal (+ (- c) x) y)|)))
(SMAN::STP-!MI
     (122 122 (:REWRITE DEFAULT-CDR))
     (87 45 (:REWRITE DEFAULT-PLUS-2))
     (64 1 (:DEFINITION SMAN::MP))
     (61 1 (:DEFINITION UNSIGNED-BYTE-P))
     (60 1 (:DEFINITION INTEGER-RANGE-P))
     (45 45 (:REWRITE DEFAULT-PLUS-1))
     (36 4 (:REWRITE ACL2-NUMBERP-X))
     (34 34
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (34 34 (:REWRITE NORMALIZE-ADDENDS))
     (23 23 (:REWRITE DEFAULT-CAR))
     (17 17 (:REWRITE THE-FLOOR-BELOW))
     (17 17 (:REWRITE THE-FLOOR-ABOVE))
     (17 17 (:REWRITE DEFAULT-LESS-THAN-2))
     (16 13
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (16 4 (:REWRITE RATIONALP-X))
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
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (13 13
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (13 13
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (13 13 (:REWRITE |(< (/ x) (/ y))|))
     (13 13 (:REWRITE |(< (- x) c)|))
     (13 13 (:REWRITE |(< (- x) (- y))|))
     (12 12 (:REWRITE REDUCE-INTEGERP-+))
     (12 12 (:REWRITE INTEGERP-MINUS-X))
     (12 12 (:META META-INTEGERP-CORRECT))
     (12 6 (:REWRITE SMAN::!NTH-NTH))
     (11 11 (:REWRITE SIMPLIFY-SUMS-<))
     (11 11
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (11 11 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (11 6
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (10 6
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (7 7 (:REWRITE |(< (/ x) 0)|))
     (7 7 (:REWRITE |(< (* x y) 0)|))
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
     (5 5 (:REWRITE |(equal (+ (- c) x) y)|))
     (4 4 (:REWRITE REDUCE-RATIONALP-+))
     (4 4 (:REWRITE REDUCE-RATIONALP-*))
     (4 4 (:REWRITE RATIONALP-MINUS-X))
     (4 4 (:META META-RATIONALP-CORRECT))
     (1 1 (:REWRITE |(< y (+ (- c) x))|))
     (1 1 (:REWRITE |(< x (+ c/d y))|)))
(SMAN::ST-PROPERTIES
     (33 33 (:REWRITE DEFAULT-CDR))
     (26 13 (:REWRITE DEFAULT-PLUS-2))
     (13 13 (:REWRITE DEFAULT-PLUS-1))
     (11 11
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (11 11 (:REWRITE NORMALIZE-ADDENDS))
     (9 9 (:REWRITE DEFAULT-CAR))
     (6 6 (:REWRITE THE-FLOOR-BELOW))
     (6 6 (:REWRITE THE-FLOOR-ABOVE))
     (6 6 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (6 6
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (6 6
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (6 6 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
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
     (6 6 (:REWRITE |(< (/ x) (/ y))|))
     (6 6 (:REWRITE |(< (- x) c)|))
     (6 6 (:REWRITE |(< (- x) (- y))|))
     (5 5 (:REWRITE SIMPLIFY-SUMS-<))
     (5 5
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (5 5 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (4 4 (:REWRITE |(< (/ x) 0)|))
     (4 4 (:REWRITE |(< (* x y) 0)|))
     (4 2
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (4 2
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (3 3 (:REWRITE REDUCE-INTEGERP-+))
     (3 3 (:REWRITE INTEGERP-MINUS-X))
     (3 3 (:META META-INTEGERP-CORRECT))
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
     (2 1
        (:TYPE-PRESCRIPTION SMAN::NATP-NTH-MP))
     (1 1 (:REWRITE |(equal (+ (- c) x) y)|)))
(SMAN::I-!I)
(SMAN::I-!S (28 14
                (:TYPE-PRESCRIPTION TRUE-LISTP-UPDATE-NTH))
            (14 14 (:TYPE-PRESCRIPTION TRUE-LISTP))
            (3 3 (:REWRITE DEFAULT-CAR))
            (2 2 (:REWRITE DEFAULT-CDR)))
(SMAN::I-!MI (6 6 (:REWRITE DEFAULT-CDR))
             (5 5 (:REWRITE DEFAULT-CAR))
             (4 1 (:REWRITE SMAN::!NTH-NTH))
             (1 1 (:REWRITE REDUCE-INTEGERP-+))
             (1 1 (:REWRITE INTEGERP-MINUS-X))
             (1 1 (:META META-INTEGERP-CORRECT)))
(SMAN::S-!I)
(SMAN::S-!S (28 14
                (:TYPE-PRESCRIPTION TRUE-LISTP-UPDATE-NTH))
            (14 14 (:TYPE-PRESCRIPTION TRUE-LISTP))
            (3 3 (:REWRITE DEFAULT-CDR))
            (2 2 (:REWRITE DEFAULT-CAR)))
(SMAN::S-!MI (8 8 (:REWRITE DEFAULT-CDR))
             (5 5 (:REWRITE DEFAULT-CAR))
             (4 1 (:REWRITE SMAN::!NTH-NTH))
             (1 1 (:REWRITE REDUCE-INTEGERP-+))
             (1 1 (:REWRITE INTEGERP-MINUS-X))
             (1 1 (:META META-INTEGERP-CORRECT)))
(SMAN::MI-!I)
(SMAN::MI-!S (98 28
                 (:TYPE-PRESCRIPTION SMAN::NATP-NTH-MP))
             (28 28 (:TYPE-PRESCRIPTION SMAN::MP))
             (28 14
                 (:TYPE-PRESCRIPTION TRUE-LISTP-UPDATE-NTH))
             (14 14 (:TYPE-PRESCRIPTION UPDATE-NTH))
             (14 14 (:TYPE-PRESCRIPTION TRUE-LISTP))
             (6 6 (:REWRITE DEFAULT-CDR))
             (3 3 (:REWRITE DEFAULT-CAR)))
(SMAN::MI-!MI
     (110 44
          (:TYPE-PRESCRIPTION SMAN::NATP-NTH-MP))
     (44 44 (:TYPE-PRESCRIPTION SMAN::MP))
     (41 1 (:REWRITE SMAN::!NTH-NTH))
     (22 22
         (:TYPE-PRESCRIPTION UPDATE-NTH-ARRAY))
     (11 11 (:REWRITE DEFAULT-CDR))
     (9 9 (:TYPE-PRESCRIPTION LEN))
     (7 1 (:DEFINITION LEN))
     (6 5 (:REWRITE DEFAULT-LESS-THAN-2))
     (5 5 (:REWRITE THE-FLOOR-BELOW))
     (5 5 (:REWRITE THE-FLOOR-ABOVE))
     (5 5 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (5 5
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (5 5
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (5 5 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (5 5 (:REWRITE INTEGERP-<-CONSTANT))
     (5 5 (:REWRITE DEFAULT-LESS-THAN-1))
     (5 5 (:REWRITE DEFAULT-CAR))
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
     (4 4 (:REWRITE |(< (/ x) 0)|))
     (4 4 (:REWRITE |(< (* x y) 0)|))
     (4 3 (:REWRITE SIMPLIFY-SUMS-<))
     (4 3
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (4 3 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (2 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (2 2
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (2 2
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (2 2 (:REWRITE REDUCE-INTEGERP-+))
     (2 2
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (2 2
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (2 2 (:REWRITE INTEGERP-MINUS-X))
     (2 2
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (2 2 (:REWRITE |(equal c (/ x))|))
     (2 2 (:REWRITE |(equal c (- x))|))
     (2 2 (:REWRITE |(equal (/ x) c)|))
     (2 2 (:REWRITE |(equal (/ x) (/ y))|))
     (2 2 (:REWRITE |(equal (- x) c)|))
     (2 2 (:REWRITE |(equal (- x) (- y))|))
     (2 2 (:META META-INTEGERP-CORRECT))
     (2 1 (:REWRITE DEFAULT-PLUS-2))
     (1 1
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (1 1 (:REWRITE NORMALIZE-ADDENDS))
     (1 1 (:REWRITE DEFAULT-PLUS-1)))
(SMAN::!I-!I)
(SMAN::!S-!I (6 6 (:REWRITE DEFAULT-CDR))
             (2 2 (:REWRITE DEFAULT-CAR)))
(SMAN::!S-!S)
(SMAN::!MI-!I (14 14 (:REWRITE DEFAULT-CDR))
              (8 2 (:REWRITE SMAN::!NTH-NTH))
              (6 6 (:REWRITE DEFAULT-CAR))
              (2 2 (:REWRITE REDUCE-INTEGERP-+))
              (2 2 (:REWRITE INTEGERP-MINUS-X))
              (2 2 (:META META-INTEGERP-CORRECT)))
(SMAN::!MI-!S (16 16 (:REWRITE DEFAULT-CDR))
              (8 8 (:REWRITE DEFAULT-CAR))
              (8 2 (:REWRITE SMAN::!NTH-NTH))
              (2 2 (:REWRITE REDUCE-INTEGERP-+))
              (2 2 (:REWRITE INTEGERP-MINUS-X))
              (2 2 (:META META-INTEGERP-CORRECT)))
(SMAN::!MI-!MI-SAME
     (123 3 (:REWRITE SMAN::!NTH-NTH))
     (27 27 (:TYPE-PRESCRIPTION LEN))
     (21 21 (:REWRITE DEFAULT-CDR))
     (21 3 (:DEFINITION LEN))
     (9 9 (:REWRITE DEFAULT-CAR))
     (7 4 (:REWRITE SIMPLIFY-SUMS-<))
     (7 4
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (7 4 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (7 4 (:REWRITE DEFAULT-LESS-THAN-2))
     (6 3 (:REWRITE DEFAULT-PLUS-2))
     (4 4 (:REWRITE THE-FLOOR-BELOW))
     (4 4 (:REWRITE THE-FLOOR-ABOVE))
     (4 4 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (4 4
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (4 4
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (4 4 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (4 4 (:REWRITE INTEGERP-<-CONSTANT))
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
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (3 3 (:REWRITE NORMALIZE-ADDENDS))
     (3 3 (:REWRITE DEFAULT-PLUS-1))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (1 1 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (1 1 (:REWRITE REDUCE-INTEGERP-+))
     (1 1 (:REWRITE INTEGERP-MINUS-X))
     (1 1 (:REWRITE |(< (/ x) 0)|))
     (1 1 (:REWRITE |(< (* x y) 0)|))
     (1 1 (:META META-INTEGERP-CORRECT)))
(SMAN::!MI-!MI-DIFF
     (425 5 (:REWRITE SMAN::!NTH-NTH))
     (158 2 (:REWRITE LEN-UPDATE-NTH))
     (114 2 (:REWRITE |(< x (if a b c))|))
     (72 2 (:DEFINITION MAX))
     (71 71 (:TYPE-PRESCRIPTION LEN))
     (62 2 (:DEFINITION NFIX))
     (35 5 (:DEFINITION LEN))
     (29 29 (:REWRITE DEFAULT-CDR))
     (24 15 (:REWRITE DEFAULT-LESS-THAN-2))
     (18 13 (:REWRITE SIMPLIFY-SUMS-<))
     (18 13
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (18 13 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (17 15 (:REWRITE DEFAULT-LESS-THAN-1))
     (15 15 (:REWRITE THE-FLOOR-BELOW))
     (15 15 (:REWRITE THE-FLOOR-ABOVE))
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
     (13 13 (:REWRITE |(< (- x) (- y))|))
     (12 12 (:REWRITE DEFAULT-CAR))
     (12 7 (:REWRITE DEFAULT-PLUS-2))
     (7 7
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (7 7 (:REWRITE NORMALIZE-ADDENDS))
     (7 7 (:REWRITE DEFAULT-PLUS-1))
     (6 6 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (4 4 (:REWRITE |(< y (+ (- c) x))|))
     (4 4 (:REWRITE |(< x (+ c/d y))|))
     (4 4 (:REWRITE |(< (/ x) 0)|))
     (4 4 (:REWRITE |(< (* x y) 0)|))
     (2 2 (:REWRITE REDUCE-INTEGERP-+))
     (2 2 (:REWRITE INTEGERP-MINUS-X))
     (2 2 (:META META-INTEGERP-CORRECT))
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
(SMAN::!I-I
     (64 1 (:DEFINITION SMAN::MP))
     (61 1 (:DEFINITION UNSIGNED-BYTE-P))
     (60 1 (:DEFINITION INTEGER-RANGE-P))
     (22 22 (:REWRITE DEFAULT-CDR))
     (14 7 (:REWRITE DEFAULT-PLUS-2))
     (12 6
         (:TYPE-PRESCRIPTION SMAN::NATP-NTH-MP))
     (7 7 (:REWRITE DEFAULT-PLUS-1))
     (6 6
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (6 6 (:REWRITE NORMALIZE-ADDENDS))
     (6 6 (:REWRITE DEFAULT-CAR))
     (4 2
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (4 2
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (3 3 (:REWRITE THE-FLOOR-BELOW))
     (3 3 (:REWRITE THE-FLOOR-ABOVE))
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
     (3 3 (:REWRITE |(< (/ x) (/ y))|))
     (3 3 (:REWRITE |(< (- x) c)|))
     (3 3 (:REWRITE |(< (- x) (- y))|))
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
     (2 2 (:REWRITE |(< (/ x) 0)|))
     (2 2 (:REWRITE |(< (* x y) 0)|))
     (2 2 (:META META-INTEGERP-CORRECT))
     (1 1 (:REWRITE |(equal (+ (- c) x) y)|)))
(SMAN::!S-S
     (64 1 (:DEFINITION SMAN::MP))
     (61 1 (:DEFINITION UNSIGNED-BYTE-P))
     (60 1 (:DEFINITION INTEGER-RANGE-P))
     (24 24 (:REWRITE DEFAULT-CDR))
     (14 7 (:REWRITE DEFAULT-PLUS-2))
     (12 6
         (:TYPE-PRESCRIPTION SMAN::NATP-NTH-MP))
     (7 7 (:REWRITE DEFAULT-PLUS-1))
     (7 7 (:REWRITE DEFAULT-CAR))
     (6 6
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (6 6 (:REWRITE NORMALIZE-ADDENDS))
     (4 2
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (4 2
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (3 3 (:REWRITE THE-FLOOR-BELOW))
     (3 3 (:REWRITE THE-FLOOR-ABOVE))
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
     (3 3 (:REWRITE |(< (/ x) (/ y))|))
     (3 3 (:REWRITE |(< (- x) c)|))
     (3 3 (:REWRITE |(< (- x) (- y))|))
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
     (2 2 (:REWRITE |(< (/ x) 0)|))
     (2 2 (:REWRITE |(< (* x y) 0)|))
     (2 2 (:META META-INTEGERP-CORRECT))
     (1 1 (:REWRITE |(equal (+ (- c) x) y)|)))
(SMAN::!MI-MI
     (128 2 (:DEFINITION SMAN::MP))
     (122 2 (:DEFINITION UNSIGNED-BYTE-P))
     (120 2 (:DEFINITION INTEGER-RANGE-P))
     (57 57 (:REWRITE DEFAULT-CDR))
     (30 15 (:REWRITE DEFAULT-PLUS-2))
     (27 21
         (:TYPE-PRESCRIPTION SMAN::NATP-NTH-MP))
     (20 20 (:REWRITE DEFAULT-CAR))
     (15 15 (:REWRITE DEFAULT-PLUS-1))
     (11 11
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (11 11 (:REWRITE NORMALIZE-ADDENDS))
     (10 10 (:REWRITE THE-FLOOR-BELOW))
     (10 10 (:REWRITE THE-FLOOR-ABOVE))
     (10 10 (:REWRITE SIMPLIFY-SUMS-<))
     (10 10
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (10 10 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (10 10
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (10 10
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (10 10
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (10 10
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (10 10 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
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
     (9 5
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (9 5
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (6 6
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (6 6 (:REWRITE REDUCE-INTEGERP-+))
     (6 6 (:REWRITE INTEGERP-MINUS-X))
     (6 6 (:REWRITE |(< (/ x) 0)|))
     (6 6 (:REWRITE |(< (* x y) 0)|))
     (6 6 (:META META-INTEGERP-CORRECT))
     (5 5 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (5 5
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (5 5 (:REWRITE |(equal c (/ x))|))
     (5 5 (:REWRITE |(equal c (- x))|))
     (5 5 (:REWRITE |(equal (/ x) c)|))
     (5 5 (:REWRITE |(equal (/ x) (/ y))|))
     (5 5 (:REWRITE |(equal (- x) c)|))
     (5 5 (:REWRITE |(equal (- x) (- y))|))
     (1 1 (:REWRITE |(equal (+ (- c) x) y)|)))
(SMAN::R
 (833 9 (:REWRITE MOD-X-Y-=-X . 3))
 (821 9 (:REWRITE CANCEL-MOD-+))
 (573 9 (:REWRITE MOD-X-Y-=-X . 4))
 (544 9 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (521 9 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (500 184
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (500 184
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (500 184
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (500 184
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (487 325 (:REWRITE DEFAULT-TIMES-2))
 (479 325 (:REWRITE DEFAULT-TIMES-1))
 (429 9 (:REWRITE MOD-ZERO . 4))
 (345 34 (:REWRITE INTEGERP-MINUS-X))
 (302 9 (:REWRITE MOD-ZERO . 3))
 (268 134
      (:TYPE-PRESCRIPTION SMAN::NATP-NTH-MP))
 (237 9 (:REWRITE MOD-X-Y-=-X . 2))
 (237 9 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (237 9
      (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (221 205
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (221 205
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (221 205
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (221 9 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (221 9 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (221 9
      (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (221 9 (:REWRITE MOD-CANCEL-*-CONST))
 (221 9
      (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (206 16 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (206 16 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (185 18 (:REWRITE |(* (- x) y)|))
 (167 167
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (146 44
      (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 3))
 (123 9 (:REWRITE DEFAULT-MOD-RATIO))
 (108 4 (:LINEAR MOD-BOUNDS-2))
 (106 18 (:REWRITE DEFAULT-MINUS))
 (102 60
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (102 60 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (98 44
     (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 2))
 (97 18 (:REWRITE |(- (* c x))|))
 (95 60 (:REWRITE DEFAULT-LESS-THAN-1))
 (70 2 (:LINEAR MOD-BOUNDS-3))
 (68 60 (:REWRITE DEFAULT-LESS-THAN-2))
 (67 11 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (62 60
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (60 60 (:REWRITE THE-FLOOR-BELOW))
 (60 60 (:REWRITE THE-FLOOR-ABOVE))
 (60 60 (:REWRITE SIMPLIFY-SUMS-<))
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
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (60 60
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (60 60
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (60 60
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (60 60 (:REWRITE |(< (/ x) (/ y))|))
 (60 60 (:REWRITE |(< (- x) c)|))
 (60 60 (:REWRITE |(< (- x) (- y))|))
 (60 1 (:REWRITE MOD-X-Y-=-X-Y . 1))
 (53 1 (:REWRITE MOD-X-Y-=-X+Y . 1))
 (50 6 (:REWRITE |(+ y x)|))
 (48 44
     (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (47 3 (:REWRITE |(equal (+ (- c) x) y)|))
 (44 16 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
 (44 16 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (43 43 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (38 16
     (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (38 16
     (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (34 10 (:REWRITE NORMALIZE-ADDENDS))
 (30 16 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (30 16
     (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (30 16 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (30 16
     (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (28 28
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (28 28
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (28 28 (:REWRITE |(< (/ x) 0)|))
 (28 28 (:REWRITE |(< (* x y) 0)|))
 (28 14 (:TYPE-PRESCRIPTION RATIONALP-MOD))
 (26 22 (:REWRITE DEFAULT-PLUS-1))
 (26 2 (:REWRITE |(+ y (+ x z))|))
 (25 25 (:REWRITE REDUCE-INTEGERP-+))
 (25 25 (:META META-INTEGERP-CORRECT))
 (22 22 (:REWRITE DEFAULT-PLUS-2))
 (19 11
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (19 11
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (17 9 (:REWRITE DEFAULT-MOD-1))
 (15 5 (:LINEAR SMAN::BYTEP-NTH-MP))
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
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (10 10 (:REWRITE |(< 0 (/ x))|))
 (10 10 (:REWRITE |(< 0 (* x y))|))
 (9 9
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (9 9
    (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (9 9 (:REWRITE DEFAULT-MOD-2))
 (9 9 (:REWRITE |(mod x (- y))| . 3))
 (9 9 (:REWRITE |(mod x (- y))| . 2))
 (9 9 (:REWRITE |(mod x (- y))| . 1))
 (9 9
    (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (9 9
    (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (9 9 (:REWRITE |(mod (- x) y)| . 3))
 (9 9 (:REWRITE |(mod (- x) y)| . 2))
 (9 9 (:REWRITE |(mod (- x) y)| . 1))
 (9 9
    (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (8 4 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
 (6 6
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (6 6 (:DEFINITION FIX))
 (6 2 (:LINEAR LOGAND-BOUNDS-NEG . 2))
 (6 2 (:LINEAR LOGAND-BOUNDS-NEG . 1))
 (5
   5
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
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
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (5 5 (:REWRITE DEFAULT-LOGAND-1))
 (4 4 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (4 4 (:REWRITE |(+ x (- x))|))
 (3 3 (:REWRITE ZP-OPEN))
 (3 3 (:REWRITE |(< y (+ (- c) x))|))
 (3 3 (:REWRITE |(< x (+ c/d y))|)))
(SMAN::!R
 (321 321
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (321 321
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (321 321
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (321 321
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (306 16 (:REWRITE DEFAULT-PLUS-1))
 (305 16 (:REWRITE DEFAULT-PLUS-2))
 (132 66
      (:TYPE-PRESCRIPTION SMAN::NATP-NTH-MP))
 (117 9 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (106 2 (:REWRITE CANCEL-MOD-+))
 (105 21 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (105 21 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (105 21
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (105 21
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (96 1 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (86 22 (:REWRITE DEFAULT-LESS-THAN-1))
 (84 20
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (84 20 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (82 13 (:REWRITE INTEGERP-MINUS-X))
 (81 9
     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (81 9
     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (81 9
     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (70 2 (:REWRITE MOD-X-Y-=-X . 4))
 (68 1 (:REWRITE FLOOR-ZERO . 3))
 (62 2 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (60 2 (:REWRITE MOD-X-Y-=-X . 3))
 (53 1 (:REWRITE CANCEL-FLOOR-+))
 (51 6 (:REWRITE |(* (- x) y)|))
 (47 47
     (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (45 9 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
 (45 9 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (45 9 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (45 9
     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (45 9
     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (45 9
     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (45 9
     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (45 9
     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (45 9
     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (45 9
     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (44 44 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (44 44 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (44 44 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (44 44 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (44 2 (:REWRITE MOD-ZERO . 3))
 (36 2 (:REWRITE MOD-ZERO . 4))
 (35 35 (:REWRITE DEFAULT-TIMES-2))
 (35 35 (:REWRITE DEFAULT-TIMES-1))
 (35 1 (:REWRITE FLOOR-ZERO . 5))
 (31 1 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (30 6 (:REWRITE DEFAULT-MINUS))
 (30 1 (:REWRITE FLOOR-ZERO . 4))
 (27 6 (:REWRITE |(- (* c x))|))
 (24 24 (:REWRITE THE-FLOOR-BELOW))
 (24 22
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (24 22
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (22 22
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (22 22
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (22 22 (:REWRITE INTEGERP-<-CONSTANT))
 (22 22 (:REWRITE DEFAULT-LESS-THAN-2))
 (22 22 (:REWRITE CONSTANT-<-INTEGERP))
 (22 22
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (22 22
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (22 22
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (22 22
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (22 22 (:REWRITE |(< c (- x))|))
 (22 22
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (22 22
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (22 22
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (22 22
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (22 22 (:REWRITE |(< (/ x) (/ y))|))
 (22 22 (:REWRITE |(< (- x) c)|))
 (22 22 (:REWRITE |(< (- x) (- y))|))
 (22 2 (:REWRITE DEFAULT-MOD-RATIO))
 (22 1 (:REWRITE FLOOR-=-X/Y . 3))
 (22 1 (:REWRITE FLOOR-=-X/Y . 2))
 (22 1 (:LINEAR MOD-BOUNDS-3))
 (21 21 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
 (21 21 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (21 21
     (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (21 21 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (21 21
     (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (21 21 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (20 20 (:REWRITE SIMPLIFY-SUMS-<))
 (19 19
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (11 1 (:REWRITE DEFAULT-FLOOR-RATIO))
 (10 10 (:REWRITE REDUCE-INTEGERP-+))
 (10 10 (:META META-INTEGERP-CORRECT))
 (10 2 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (10 2 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (10 2 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (10 2 (:REWRITE MOD-X-Y-=-X . 2))
 (10 2
     (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (10 2 (:REWRITE MOD-CANCEL-*-CONST))
 (10 2 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (10 2
     (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (10 2
     (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (10 2 (:LINEAR MOD-BOUNDS-2))
 (8 8
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (7 7 (:REWRITE |(< (/ x) 0)|))
 (7 7 (:REWRITE |(< (* x y) 0)|))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (6 2 (:LINEAR SMAN::BYTEP-NTH-MP))
 (5 1 (:REWRITE FLOOR-ZERO . 2))
 (5 1 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (5 1 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (5 1 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (5 1
    (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (5 1 (:REWRITE FLOOR-CANCEL-*-CONST))
 (5 1
    (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (4 4 (:TYPE-PRESCRIPTION ABS))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (3 3 (:REWRITE |(< 0 (/ x))|))
 (3 3 (:REWRITE |(< 0 (* x y))|))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
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
    (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (2 2
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (2 2 (:REWRITE DEFAULT-MOD-2))
 (2 2 (:REWRITE DEFAULT-MOD-1))
 (2 2 (:REWRITE DEFAULT-LOGAND-2))
 (2 2 (:REWRITE DEFAULT-LOGAND-1))
 (2 2 (:REWRITE |(mod x (- y))| . 3))
 (2 2 (:REWRITE |(mod x (- y))| . 2))
 (2 2 (:REWRITE |(mod x (- y))| . 1))
 (2 2
    (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (2 2
    (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (2 2 (:REWRITE |(mod (- x) y)| . 3))
 (2 2 (:REWRITE |(mod (- x) y)| . 2))
 (2 2 (:REWRITE |(mod (- x) y)| . 1))
 (2 2
    (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (2 2 (:REWRITE |(equal c (/ x))|))
 (2 2 (:REWRITE |(equal c (- x))|))
 (2 2 (:REWRITE |(equal (/ x) c)|))
 (2 2 (:REWRITE |(equal (/ x) (/ y))|))
 (2 2 (:REWRITE |(equal (- x) c)|))
 (2 2 (:REWRITE |(equal (- x) (- y))|))
 (2 2 (:REWRITE |(< y (+ (- c) x))|))
 (2 2 (:REWRITE |(< x (+ c/d y))|))
 (2 2 (:REWRITE |(< (+ c/d x) y)|))
 (2 2 (:REWRITE |(< (+ (- c) x) y)|))
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
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE MOD-NEGATIVE . 3))
 (1 1 (:REWRITE MOD-NEGATIVE . 2))
 (1 1 (:REWRITE FOLD-CONSTS-IN-+))
 (1 1
    (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (1 1 (:REWRITE DEFAULT-FLOOR-2))
 (1 1 (:REWRITE DEFAULT-FLOOR-1))
 (1 1 (:REWRITE |(floor x (- y))| . 2))
 (1 1 (:REWRITE |(floor x (- y))| . 1))
 (1 1
    (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (1 1
    (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (1 1 (:REWRITE |(floor (- x) y)| . 2))
 (1 1 (:REWRITE |(floor (- x) y)| . 1))
 (1 1
    (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (1 1
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (1 1
    (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
 (1 1
    (:REWRITE |(< (* (/ x) y) 1) with (< 0 x)|)))
(SMAN::R-BOUND
 (528 64 (:REWRITE DEFAULT-PLUS-1))
 (450 9 (:REWRITE CANCEL-MOD-+))
 (351 9 (:REWRITE MOD-X-Y-=-X . 4))
 (351 9 (:REWRITE MOD-X-Y-=-X . 3))
 (342 9 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (315 73
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (315 9 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (297 297
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (297 297
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (297 297
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (297 297
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (263
  263
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (263 263
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (263
     263
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (263 263
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (263 263
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (259 61 (:REWRITE INTEGERP-MINUS-X))
 (238 128 (:REWRITE DEFAULT-TIMES-2))
 (219 77 (:REWRITE DEFAULT-LESS-THAN-2))
 (217 64 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (216 9 (:REWRITE MOD-ZERO . 4))
 (214 70 (:REWRITE DEFAULT-PLUS-2))
 (206 103 (:TYPE-PRESCRIPTION SMAN::NATP-MI))
 (202 77 (:REWRITE DEFAULT-LESS-THAN-1))
 (190 38 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (190 38 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (190 38
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (190 38
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (189 9 (:REWRITE MOD-ZERO . 3))
 (172 64 (:REWRITE SIMPLIFY-SUMS-<))
 (157 157 (:TYPE-PRESCRIPTION SMAN::STP))
 (140 128 (:REWRITE DEFAULT-TIMES-1))
 (135 18 (:REWRITE |(* (- x) y)|))
 (108 54 (:LINEAR SMAN::BYTEP-MI))
 (108 12 (:REWRITE ACL2-NUMBERP-X))
 (95 95 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (95 95 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (95 95 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (90 18 (:REWRITE DEFAULT-MINUS))
 (90 9 (:REWRITE DEFAULT-MOD-RATIO))
 (84 2 (:LINEAR EXPT-<=-1-TWO))
 (83 65
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (82 2 (:LINEAR EXPT->-1-ONE))
 (80 2 (:LINEAR EXPT-X->=-X))
 (80 2 (:LINEAR EXPT-X->-X))
 (77 77 (:REWRITE THE-FLOOR-BELOW))
 (77 77 (:REWRITE THE-FLOOR-ABOVE))
 (75 73
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (75 73
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (66 8 (:REWRITE DEFAULT-FLOOR-RATIO))
 (65 65 (:REWRITE INTEGERP-<-CONSTANT))
 (65 65 (:REWRITE CONSTANT-<-INTEGERP))
 (65 65
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (65 65
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (65 65
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (65 65
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (65 65 (:REWRITE |(< c (- x))|))
 (65 65
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (65 65
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (65 65
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (65 65
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (65 65 (:REWRITE |(< (/ x) (/ y))|))
 (65 65 (:REWRITE |(< (- x) c)|))
 (65 65 (:REWRITE |(< (- x) (- y))|))
 (63 18 (:REWRITE |(- (* c x))|))
 (52 52 (:REWRITE REDUCE-INTEGERP-+))
 (52 52 (:META META-INTEGERP-CORRECT))
 (52 50 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (48 12 (:REWRITE RATIONALP-X))
 (45 9 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (45 9 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (45 9 (:REWRITE MOD-X-Y-=-X . 2))
 (45 9
     (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (45 9 (:REWRITE MOD-CANCEL-*-CONST))
 (45 9 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (45 9
     (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (45 9
     (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (38 38 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
 (38 38 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (38 38
     (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (38 38 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (38 38
     (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (38 38 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (32 8 (:REWRITE |(+ c (+ d x))|))
 (28 28
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (28 28 (:REWRITE NORMALIZE-ADDENDS))
 (28 2 (:LINEAR EXPT->=-1-ONE))
 (23 23
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (23 23
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (23 23 (:REWRITE |(< (/ x) 0)|))
 (23 23 (:REWRITE |(< (* x y) 0)|))
 (21 1 (:LINEAR MOD-BOUNDS-3))
 (20 20 (:REWRITE |(< 0 (* x y))|))
 (16 16
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (16 16
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (16 16 (:REWRITE |(< 0 (/ x))|))
 (14 8 (:REWRITE DEFAULT-FLOOR-1))
 (13 13 (:REWRITE DEFAULT-EXPT-1))
 (13 13 (:REWRITE |(expt 1/c n)|))
 (13 13 (:REWRITE |(expt (- x) n)|))
 (12 12 (:REWRITE REDUCE-RATIONALP-+))
 (12 12 (:REWRITE REDUCE-RATIONALP-*))
 (12 12 (:REWRITE RATIONALP-MINUS-X))
 (12 12 (:META META-RATIONALP-CORRECT))
 (10 2 (:LINEAR MOD-BOUNDS-2))
 (9 9
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
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
    (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (9 9
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (9 9 (:REWRITE DEFAULT-MOD-2))
 (9 9 (:REWRITE DEFAULT-MOD-1))
 (9 9 (:REWRITE |(mod x (- y))| . 3))
 (9 9 (:REWRITE |(mod x (- y))| . 2))
 (9 9 (:REWRITE |(mod x (- y))| . 1))
 (9 9
    (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (9 9
    (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (9 9 (:REWRITE |(mod (- x) y)| . 3))
 (9 9 (:REWRITE |(mod (- x) y)| . 2))
 (9 9 (:REWRITE |(mod (- x) y)| . 1))
 (9 9
    (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (9 9 (:REWRITE |(equal c (/ x))|))
 (9 9 (:REWRITE |(equal c (- x))|))
 (9 9 (:REWRITE |(equal (/ x) c)|))
 (9 9 (:REWRITE |(equal (/ x) (/ y))|))
 (9 9 (:REWRITE |(equal (- x) c)|))
 (9 9 (:REWRITE |(equal (- x) (- y))|))
 (8 8 (:REWRITE DEFAULT-LOGAND-1))
 (8 8 (:REWRITE DEFAULT-FLOOR-2))
 (8 8 (:REWRITE |(< x (+ c/d y))|))
 (5 5 (:REWRITE ZP-OPEN))
 (5 5 (:REWRITE ZIP-OPEN))
 (4 4 (:TYPE-PRESCRIPTION ABS))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (2 2 (:REWRITE |(< (+ c/d x) y)|))
 (2 2 (:REWRITE |(< (+ (- c) x) y)|))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-TWO))
 (2 2 (:LINEAR EXPT-<-1-ONE))
 (1 1
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|)))
(SMAN::STP-!R
 (16434 44 (:LINEAR LINEAR-FLOOR-BOUNDS-1))
 (15701 1 (:REWRITE |(logand (if a b c) x)|))
 (15638 11318
        (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (13525 1 (:REWRITE |(floor (if a b c) x)|))
 (11318 11318
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (11318 11318
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (11318 11318
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (10956 180 (:REWRITE THE-FLOOR-ABOVE))
 (6282 929
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (5775 16 (:REWRITE SMAN::!MI-MI))
 (5415 57 (:REWRITE CANCEL-FLOOR-+))
 (5262 21 (:REWRITE MOD-ZERO . 4))
 (5013 21 (:REWRITE MOD-X-Y-=-X . 3))
 (4889 57 (:REWRITE FLOOR-ZERO . 3))
 (4790 21 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (4725 21 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (4647 57 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (4629 57 (:REWRITE FLOOR-ZERO . 4))
 (4619 57 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (4363 21 (:REWRITE MOD-X-Y-=-X . 4))
 (4158 462 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (4158 462
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (4158 462
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (4158 462
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (4158 462
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (4145 159 (:REWRITE DEFAULT-PLUS-1))
 (4133 159 (:REWRITE DEFAULT-PLUS-2))
 (4022 228 (:REWRITE INTEGERP-MINUS-X))
 (3979 57 (:REWRITE FLOOR-ZERO . 5))
 (3872 887 (:REWRITE DEFAULT-TIMES-2))
 (3771 63 (:REWRITE NORMALIZE-ADDENDS))
 (3739 21 (:REWRITE CANCEL-MOD-+))
 (3109 887 (:REWRITE DEFAULT-TIMES-1))
 (3009 323 (:REWRITE |(* y x)|))
 (2936 158 (:REWRITE |(* (- x) y)|))
 (2898 3 (:REWRITE |(equal (if a b c) x)|))
 (2792 2 (:REWRITE |(mod (floor x y) z)| . 1))
 (2310 462 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
 (2310 462 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (2310 462 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (2310 462
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (2310 462
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (2310 462
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (2310 462
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (2310 462
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (2310 462
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
 (2310 462
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (2310 462
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (1784 158 (:REWRITE DEFAULT-MINUS))
 (1729 57 (:REWRITE FLOOR-=-X/Y . 2))
 (1722 158 (:REWRITE |(- (* c x))|))
 (1643 58 (:REWRITE DEFAULT-FLOOR-RATIO))
 (1473 57 (:REWRITE FLOOR-=-X/Y . 3))
 (1472 21 (:REWRITE MOD-ZERO . 3))
 (1224 12 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (1224 12 (:DEFINITION FIX))
 (1004 180 (:REWRITE THE-FLOOR-BELOW))
 (929 929
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (929 929
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (929 929
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (853 159
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (837 21 (:REWRITE DEFAULT-MOD-RATIO))
 (572 168 (:REWRITE DEFAULT-LESS-THAN-2))
 (514 168 (:REWRITE DEFAULT-LESS-THAN-1))
 (509 21 (:REWRITE MOD-X-Y-=-X . 2))
 (509 21 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (509 21
      (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (487 57 (:REWRITE FLOOR-ZERO . 2))
 (487 57 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (487 57 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (485 485
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (479 57 (:REWRITE FLOOR-CANCEL-*-CONST))
 (462 462 (:TYPE-PRESCRIPTION FLOOR))
 (460 2
      (:REWRITE |(floor (floor x y) z)| . 1))
 (449 159
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (410 82 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (410 82 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (410 82
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (410 82
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (388 166
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (361 58 (:REWRITE DEFAULT-FLOOR-1))
 (359 29
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (359 29
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (311 57
      (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (307 21 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (307 21 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (307 21 (:REWRITE MOD-CANCEL-*-CONST))
 (263 21
      (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (233 57
      (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (231 55
      (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (225 23 (:REWRITE DEFAULT-LOGAND-2))
 (223 21 (:REWRITE DEFAULT-MOD-1))
 (209 1 (:REWRITE |(* (if a b c) x)|))
 (198 22 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (190 166
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (190 166
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (165 19 (:LINEAR SMAN::BYTEP-MI))
 (160 160
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (160 160 (:REWRITE INTEGERP-<-CONSTANT))
 (160 160 (:REWRITE CONSTANT-<-INTEGERP))
 (160 160
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (160 160
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (160 160
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (160 160
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (160 160 (:REWRITE |(< c (- x))|))
 (160 160
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (160 160
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (160 160
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (160 160
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (160 160 (:REWRITE |(< (/ x) (/ y))|))
 (160 160 (:REWRITE |(< (- x) c)|))
 (160 160 (:REWRITE |(< (- x) (- y))|))
 (159 159 (:REWRITE SIMPLIFY-SUMS-<))
 (156 3 (:REWRITE SMAN::!MI-!MI-DIFF))
 (154 7 (:LINEAR MOD-BOUNDS-3))
 (150 150 (:REWRITE REDUCE-INTEGERP-+))
 (150 150 (:META META-INTEGERP-CORRECT))
 (149 29 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (139 139 (:TYPE-PRESCRIPTION SMAN::NATP-MI))
 (110 22 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (108 9 (:REWRITE ZP-OPEN))
 (99 55
     (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (82 82 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
 (82 82 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (82 82
     (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (82 82 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (82 82
     (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (82 82 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (81 81 (:REWRITE |(< (/ x) 0)|))
 (81 81 (:REWRITE |(< (* x y) 0)|))
 (80 80
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (80 80
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (70 14 (:LINEAR MOD-BOUNDS-2))
 (66 6 (:REWRITE |(+ y (+ x z))|))
 (65 21
     (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (63 19
     (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (58 58 (:REWRITE DEFAULT-FLOOR-2))
 (55 55 (:REWRITE |(floor x (- y))| . 2))
 (55 55 (:REWRITE |(floor x (- y))| . 1))
 (55 55
     (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (55 55
     (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (55 55 (:REWRITE |(floor (- x) y)| . 2))
 (55 55 (:REWRITE |(floor (- x) y)| . 1))
 (54 12 (:REWRITE |(+ c (+ d x))|))
 (51 51
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (51 19
     (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (48 48 (:TYPE-PRESCRIPTION ABS))
 (36 4 (:REWRITE FLOOR-POSITIVE . 2))
 (36 4 (:REWRITE FLOOR-NONPOSITIVE . 1))
 (34 34
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (34 34
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (34 34 (:REWRITE |(< 0 (/ x))|))
 (34 34 (:REWRITE |(< 0 (* x y))|))
 (33 11 (:LINEAR SMAN::BYTEP-NTH-MP))
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
 (25 25
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (24 12 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
 (21 21 (:REWRITE DEFAULT-MOD-2))
 (20 20
     (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (20 4 (:REWRITE FLOOR-POSITIVE . 4))
 (20 4 (:REWRITE FLOOR-POSITIVE . 3))
 (20 4 (:REWRITE FLOOR-NONPOSITIVE . 3))
 (20 4 (:REWRITE FLOOR-NONPOSITIVE . 2))
 (19 19 (:REWRITE |(mod x (- y))| . 3))
 (19 19 (:REWRITE |(mod x (- y))| . 2))
 (19 19 (:REWRITE |(mod x (- y))| . 1))
 (19 19
     (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (19 19
     (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (19 19 (:REWRITE |(mod (- x) y)| . 3))
 (19 19 (:REWRITE |(mod (- x) y)| . 2))
 (19 19 (:REWRITE |(mod (- x) y)| . 1))
 (12 12 (:REWRITE |(+ x (- x))|))
 (10 2 (:REWRITE FLOOR-=-X/Y . 4))
 (10 2
     (:REWRITE |(equal (floor (+ x y) z) x)|))
 (8
   8
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (8
  8
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (6 6 (:REWRITE |(< y (+ (- c) x))|))
 (6 6 (:REWRITE |(< x (+ c/d y))|))
 (6 6 (:REWRITE |(< (+ c/d x) y)|))
 (4 4 (:REWRITE MOD-X-Y-=-X-Y . 1))
 (4 4 (:REWRITE MOD-X-Y-=-X+Y . 1))
 (4 4 (:REWRITE FLOOR-POSITIVE . 1))
 (4 4
    (:REWRITE |(equal (mod (+ x y) z) x)|))
 (2 2 (:REWRITE FLOOR-ZERO . 1))
 (2 2 (:REWRITE |(mod (floor x y) z)| . 5))
 (2 2 (:REWRITE |(mod (floor x y) z)| . 4))
 (2 2 (:REWRITE |(mod (floor x y) z)| . 3))
 (2 2 (:REWRITE |(mod (floor x y) z)| . 2))
 (2 2
    (:REWRITE |(floor (floor x y) z)| . 5))
 (2 2
    (:REWRITE |(floor (floor x y) z)| . 4))
 (2 2
    (:REWRITE |(floor (floor x y) z)| . 3))
 (2 2
    (:REWRITE |(floor (floor x y) z)| . 2)))
(SMAN::I-!R
 (24651 66 (:LINEAR LINEAR-FLOOR-BOUNDS-1))
 (22612 16132
        (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (16306 142 (:REWRITE THE-FLOOR-ABOVE))
 (16132 16132
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (16132 16132
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (16132 16132
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (15701 1 (:REWRITE |(logand (if a b c) x)|))
 (13525 1 (:REWRITE |(floor (if a b c) x)|))
 (9783 69 (:REWRITE |(+ y x)|))
 (9145 1166
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (8043 84 (:REWRITE CANCEL-FLOOR-+))
 (7542 12 (:REWRITE MOD-ZERO . 4))
 (7198 84 (:REWRITE FLOOR-ZERO . 3))
 (6909 84 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (6874 84 (:REWRITE FLOOR-ZERO . 4))
 (6861 84 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (6837 12 (:REWRITE MOD-X-Y-=-X . 3))
 (6522 12 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (6483 12 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (6210 690 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (6210 690
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (6210 690
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (6210 690
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (6210 690
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (6171 192 (:REWRITE DEFAULT-PLUS-1))
 (5899 84 (:REWRITE FLOOR-ZERO . 5))
 (5862 12 (:REWRITE MOD-X-Y-=-X . 4))
 (5638 76 (:REWRITE NORMALIZE-ADDENDS))
 (5537 1110 (:REWRITE DEFAULT-TIMES-2))
 (5469 261 (:REWRITE INTEGERP-MINUS-X))
 (4575 12 (:REWRITE CANCEL-MOD-+))
 (4342 1110 (:REWRITE DEFAULT-TIMES-1))
 (4186 3 (:REWRITE |(mod (floor x y) z)| . 1))
 (4149 406 (:REWRITE |(* y x)|))
 (4047 195 (:REWRITE |(* (- x) y)|))
 (3450 690 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
 (3450 690 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (3450 690 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (3450 690
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (3450 690
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (3450 690
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (3450 690
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (3450 690
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (3450 690
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
 (3450 690
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (3450 690
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (2550 84 (:REWRITE FLOOR-=-X/Y . 2))
 (2466 195 (:REWRITE DEFAULT-MINUS))
 (2394 195 (:REWRITE |(- (* c x))|))
 (2239 85 (:REWRITE DEFAULT-FLOOR-RATIO))
 (2166 84 (:REWRITE FLOOR-=-X/Y . 3))
 (1836 18 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (1836 18 (:DEFINITION FIX))
 (1779 12 (:REWRITE MOD-ZERO . 3))
 (1378 142 (:REWRITE THE-FLOOR-BELOW))
 (1166 1166
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (1166 1166
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (1166 1166
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (1157 124
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (1041 12 (:REWRITE DEFAULT-MOD-RATIO))
 (730 124 (:REWRITE DEFAULT-LESS-THAN-2))
 (723 84 (:REWRITE FLOOR-ZERO . 2))
 (723 84 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (723 84 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (707 84 (:REWRITE FLOOR-CANCEL-*-CONST))
 (690 690 (:TYPE-PRESCRIPTION FLOOR))
 (666 12 (:REWRITE MOD-X-Y-=-X . 2))
 (666 12 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (666 12
      (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (607 607
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (568 3
      (:REWRITE |(floor (floor x y) z)| . 1))
 (551 124
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (551 124 (:REWRITE DEFAULT-LESS-THAN-1))
 (489 85 (:REWRITE DEFAULT-FLOOR-1))
 (481 16
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (459 84
      (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (365 16
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (363 12 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (363 12 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (363 12
      (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (363 12 (:REWRITE MOD-CANCEL-*-CONST))
 (348 84
      (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (345 81
      (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (328 25 (:REWRITE DEFAULT-LOGAND-2))
 (315 12 (:REWRITE DEFAULT-MOD-1))
 (297 33 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (209 1 (:REWRITE |(* (if a b c) x)|))
 (200 20 (:REWRITE ACL2-NUMBERP-X))
 (178 13 (:REWRITE ZP-OPEN))
 (165 165 (:REWRITE REDUCE-INTEGERP-+))
 (165 165 (:META META-INTEGERP-CORRECT))
 (165 33 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (158 124
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (158 124
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (141 81
      (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (124 124 (:REWRITE SIMPLIFY-SUMS-<))
 (124 124
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (124 124
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (124 124 (:REWRITE INTEGERP-<-CONSTANT))
 (124 124 (:REWRITE CONSTANT-<-INTEGERP))
 (124 124
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (124 124
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (124 124
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (124 124
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (124 124 (:REWRITE |(< c (- x))|))
 (124 124
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (124 124
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (124 124
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (124 124
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (124 124 (:REWRITE |(< (/ x) (/ y))|))
 (124 124 (:REWRITE |(< (- x) c)|))
 (124 124 (:REWRITE |(< (- x) (- y))|))
 (99 99 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (92 20 (:REWRITE |(+ 0 x)|))
 (90 12 (:REWRITE RATIONALP-X))
 (85 85 (:REWRITE DEFAULT-FLOOR-2))
 (81 81 (:REWRITE |(floor x (- y))| . 2))
 (81 81 (:REWRITE |(floor x (- y))| . 1))
 (81 81
     (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (81 81
     (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (81 81 (:REWRITE |(floor (- x) y)| . 2))
 (81 81 (:REWRITE |(floor (- x) y)| . 1))
 (68 68 (:TYPE-PRESCRIPTION ABS))
 (66 66
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (66 66
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (66 66 (:REWRITE |(< (/ x) 0)|))
 (66 66 (:REWRITE |(< (* x y) 0)|))
 (62 16 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (58 58
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (54 13 (:REWRITE SMAN::!MI-MI))
 (54 6 (:REWRITE FLOOR-POSITIVE . 2))
 (54 6 (:REWRITE FLOOR-NONPOSITIVE . 1))
 (45 9
     (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (40 8 (:REWRITE |(+ c (+ d x))|))
 (36 18 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
 (30 30
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (30 30
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (30 30 (:REWRITE |(< 0 (/ x))|))
 (30 30 (:REWRITE |(< 0 (* x y))|))
 (30 6 (:REWRITE FLOOR-POSITIVE . 4))
 (30 6 (:REWRITE FLOOR-POSITIVE . 3))
 (30 6 (:REWRITE FLOOR-NONPOSITIVE . 3))
 (30 6 (:REWRITE FLOOR-NONPOSITIVE . 2))
 (28 28
     (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (20 3 (:REWRITE SMAN::!MI-!MI-DIFF))
 (18 18 (:REWRITE |(+ x (- x))|))
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
 (15 5 (:REWRITE SMAN::STP-!MI))
 (15 3 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (15 3 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (15 3 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (15 3 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (15 3 (:REWRITE FLOOR-=-X/Y . 4))
 (15 3
     (:REWRITE |(equal (floor (+ x y) z) x)|))
 (14 2 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (12 12
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (12 12 (:REWRITE REDUCE-RATIONALP-+))
 (12 12 (:REWRITE REDUCE-RATIONALP-*))
 (12 12 (:REWRITE RATIONALP-MINUS-X))
 (12 12
     (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (12 12 (:REWRITE DEFAULT-MOD-2))
 (12 12 (:META META-RATIONALP-CORRECT))
 (9
   9
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (9
  9
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (9 9
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (9 9
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (9 9
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (9 9
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (9 9 (:REWRITE |(mod x (- y))| . 3))
 (9 9 (:REWRITE |(mod x (- y))| . 2))
 (9 9 (:REWRITE |(mod x (- y))| . 1))
 (9 9
    (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (9 9
    (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (9 9 (:REWRITE |(mod (- x) y)| . 3))
 (9 9 (:REWRITE |(mod (- x) y)| . 2))
 (9 9 (:REWRITE |(mod (- x) y)| . 1))
 (9 9
    (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (8 1 (:REWRITE |(+ x (if a b c))|))
 (6 6 (:REWRITE FLOOR-POSITIVE . 1))
 (5 5 (:REWRITE |(< y (+ (- c) x))|))
 (5 5 (:REWRITE |(< x (+ c/d y))|))
 (3 3 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
 (3 3 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (3 3 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (3 3 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (3 3 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
 (3 3 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (3 3 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (3 3 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
 (3 3 (:REWRITE FLOOR-ZERO . 1))
 (3 3 (:REWRITE |(mod (floor x y) z)| . 5))
 (3 3 (:REWRITE |(mod (floor x y) z)| . 4))
 (3 3 (:REWRITE |(mod (floor x y) z)| . 3))
 (3 3 (:REWRITE |(mod (floor x y) z)| . 2))
 (3 3
    (:REWRITE |(floor (floor x y) z)| . 5))
 (3 3
    (:REWRITE |(floor (floor x y) z)| . 4))
 (3 3
    (:REWRITE |(floor (floor x y) z)| . 3))
 (3 3
    (:REWRITE |(floor (floor x y) z)| . 2)))
(SMAN::S-!R
 (24651 66 (:LINEAR LINEAR-FLOOR-BOUNDS-1))
 (22548 16068
        (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (16306 142 (:REWRITE THE-FLOOR-ABOVE))
 (16068 16068
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (16068 16068
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (16068 16068
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (15701 1 (:REWRITE |(logand (if a b c) x)|))
 (13525 1 (:REWRITE |(floor (if a b c) x)|))
 (9783 69 (:REWRITE |(+ y x)|))
 (9145 1166
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (8043 84 (:REWRITE CANCEL-FLOOR-+))
 (7542 12 (:REWRITE MOD-ZERO . 4))
 (7198 84 (:REWRITE FLOOR-ZERO . 3))
 (6909 84 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (6874 84 (:REWRITE FLOOR-ZERO . 4))
 (6861 84 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (6837 12 (:REWRITE MOD-X-Y-=-X . 3))
 (6522 12 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (6483 12 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (6210 690 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (6210 690
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (6210 690
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (6210 690
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (6210 690
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (6171 192 (:REWRITE DEFAULT-PLUS-1))
 (5899 84 (:REWRITE FLOOR-ZERO . 5))
 (5862 12 (:REWRITE MOD-X-Y-=-X . 4))
 (5638 76 (:REWRITE NORMALIZE-ADDENDS))
 (5537 1110 (:REWRITE DEFAULT-TIMES-2))
 (5469 261 (:REWRITE INTEGERP-MINUS-X))
 (4575 12 (:REWRITE CANCEL-MOD-+))
 (4342 1110 (:REWRITE DEFAULT-TIMES-1))
 (4186 3 (:REWRITE |(mod (floor x y) z)| . 1))
 (4149 406 (:REWRITE |(* y x)|))
 (4047 195 (:REWRITE |(* (- x) y)|))
 (3450 690 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
 (3450 690 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (3450 690 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (3450 690
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (3450 690
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (3450 690
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (3450 690
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (3450 690
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (3450 690
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
 (3450 690
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (3450 690
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (2550 84 (:REWRITE FLOOR-=-X/Y . 2))
 (2466 195 (:REWRITE DEFAULT-MINUS))
 (2394 195 (:REWRITE |(- (* c x))|))
 (2239 85 (:REWRITE DEFAULT-FLOOR-RATIO))
 (2166 84 (:REWRITE FLOOR-=-X/Y . 3))
 (1836 18 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (1836 18 (:DEFINITION FIX))
 (1779 12 (:REWRITE MOD-ZERO . 3))
 (1378 142 (:REWRITE THE-FLOOR-BELOW))
 (1166 1166
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (1166 1166
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (1166 1166
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (1157 124
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (1041 12 (:REWRITE DEFAULT-MOD-RATIO))
 (730 124 (:REWRITE DEFAULT-LESS-THAN-2))
 (723 84 (:REWRITE FLOOR-ZERO . 2))
 (723 84 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (723 84 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (707 84 (:REWRITE FLOOR-CANCEL-*-CONST))
 (690 690 (:TYPE-PRESCRIPTION FLOOR))
 (666 12 (:REWRITE MOD-X-Y-=-X . 2))
 (666 12 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (666 12
      (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (607 607
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (568 3
      (:REWRITE |(floor (floor x y) z)| . 1))
 (551 124
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (551 124 (:REWRITE DEFAULT-LESS-THAN-1))
 (489 85 (:REWRITE DEFAULT-FLOOR-1))
 (459 84
      (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (363 12 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (363 12 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (363 12
      (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (363 12 (:REWRITE MOD-CANCEL-*-CONST))
 (355 16
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (348 84
      (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (345 81
      (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (328 25 (:REWRITE DEFAULT-LOGAND-2))
 (323 16
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (315 12 (:REWRITE DEFAULT-MOD-1))
 (297 33 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (209 1 (:REWRITE |(* (if a b c) x)|))
 (178 13 (:REWRITE ZP-OPEN))
 (165 165 (:REWRITE REDUCE-INTEGERP-+))
 (165 165 (:META META-INTEGERP-CORRECT))
 (165 33 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (158 124
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (158 124
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (141 81
      (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (124 124 (:REWRITE SIMPLIFY-SUMS-<))
 (124 124
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (124 124
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (124 124 (:REWRITE INTEGERP-<-CONSTANT))
 (124 124 (:REWRITE CONSTANT-<-INTEGERP))
 (124 124
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (124 124
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (124 124
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (124 124
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (124 124 (:REWRITE |(< c (- x))|))
 (124 124
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (124 124
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (124 124
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (124 124
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (124 124 (:REWRITE |(< (/ x) (/ y))|))
 (124 124 (:REWRITE |(< (- x) c)|))
 (124 124 (:REWRITE |(< (- x) (- y))|))
 (116 20 (:REWRITE ACL2-NUMBERP-X))
 (99 99 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (92 20 (:REWRITE |(+ 0 x)|))
 (85 85 (:REWRITE DEFAULT-FLOOR-2))
 (81 81 (:REWRITE |(floor x (- y))| . 2))
 (81 81 (:REWRITE |(floor x (- y))| . 1))
 (81 81
     (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (81 81
     (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (81 81 (:REWRITE |(floor (- x) y)| . 2))
 (81 81 (:REWRITE |(floor (- x) y)| . 1))
 (68 68 (:TYPE-PRESCRIPTION ABS))
 (66 66
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (66 66
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (66 66 (:REWRITE |(< (/ x) 0)|))
 (66 66 (:REWRITE |(< (* x y) 0)|))
 (58 58
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (54 13 (:REWRITE SMAN::!MI-MI))
 (54 6 (:REWRITE FLOOR-POSITIVE . 2))
 (54 6 (:REWRITE FLOOR-NONPOSITIVE . 1))
 (48 12 (:REWRITE RATIONALP-X))
 (45 9
     (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (40 8 (:REWRITE |(+ c (+ d x))|))
 (36 36 (:TYPE-PRESCRIPTION SMAN::STP))
 (36 18 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
 (30 30
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (30 30
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (30 30 (:REWRITE |(< 0 (/ x))|))
 (30 30 (:REWRITE |(< 0 (* x y))|))
 (30 6 (:REWRITE FLOOR-POSITIVE . 4))
 (30 6 (:REWRITE FLOOR-POSITIVE . 3))
 (30 6 (:REWRITE FLOOR-NONPOSITIVE . 3))
 (30 6 (:REWRITE FLOOR-NONPOSITIVE . 2))
 (28 28
     (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (20 16 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (20 3 (:REWRITE SMAN::!MI-!MI-DIFF))
 (18 18 (:REWRITE |(+ x (- x))|))
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
 (15 5 (:REWRITE SMAN::STP-!MI))
 (15 3 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (15 3 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (15 3 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (15 3 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (15 3 (:REWRITE FLOOR-=-X/Y . 4))
 (15 3
     (:REWRITE |(equal (floor (+ x y) z) x)|))
 (14 2 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (12 12
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (12 12 (:REWRITE REDUCE-RATIONALP-+))
 (12 12 (:REWRITE REDUCE-RATIONALP-*))
 (12 12 (:REWRITE RATIONALP-MINUS-X))
 (12 12
     (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (12 12 (:REWRITE DEFAULT-MOD-2))
 (12 12 (:META META-RATIONALP-CORRECT))
 (9
   9
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (9
  9
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (9 9
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (9 9
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (9 9
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (9 9
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (9 9 (:REWRITE |(mod x (- y))| . 3))
 (9 9 (:REWRITE |(mod x (- y))| . 2))
 (9 9 (:REWRITE |(mod x (- y))| . 1))
 (9 9
    (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (9 9
    (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (9 9 (:REWRITE |(mod (- x) y)| . 3))
 (9 9 (:REWRITE |(mod (- x) y)| . 2))
 (9 9 (:REWRITE |(mod (- x) y)| . 1))
 (9 9
    (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (8 1 (:REWRITE |(+ x (if a b c))|))
 (6 6 (:REWRITE FLOOR-POSITIVE . 1))
 (5 5 (:REWRITE |(< y (+ (- c) x))|))
 (5 5 (:REWRITE |(< x (+ c/d y))|))
 (3 3 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
 (3 3 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (3 3 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (3 3 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (3 3 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
 (3 3 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (3 3 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (3 3 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
 (3 3 (:REWRITE FLOOR-ZERO . 1))
 (3 3 (:REWRITE |(mod (floor x y) z)| . 5))
 (3 3 (:REWRITE |(mod (floor x y) z)| . 4))
 (3 3 (:REWRITE |(mod (floor x y) z)| . 3))
 (3 3 (:REWRITE |(mod (floor x y) z)| . 2))
 (3 3
    (:REWRITE |(floor (floor x y) z)| . 5))
 (3 3
    (:REWRITE |(floor (floor x y) z)| . 4))
 (3 3
    (:REWRITE |(floor (floor x y) z)| . 3))
 (3 3
    (:REWRITE |(floor (floor x y) z)| . 2)))
(SMAN::R-!I
 (1634 126 (:REWRITE DEFAULT-PLUS-1))
 (1378 26 (:REWRITE CANCEL-MOD-+))
 (1014 26 (:REWRITE MOD-X-Y-=-X . 4))
 (1014 26 (:REWRITE MOD-X-Y-=-X . 3))
 (988 26 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (910 26 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (814 216 (:REWRITE INTEGERP-MINUS-X))
 (644 146 (:REWRITE DEFAULT-PLUS-2))
 (630 630
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (630 630
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (630 630
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (630 630
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (624 26 (:REWRITE MOD-ZERO . 4))
 (588 294 (:TYPE-PRESCRIPTION SMAN::NATP-MI))
 (576 64 (:REWRITE ACL2-NUMBERP-X))
 (572 26 (:REWRITE MOD-ZERO . 3))
 (494 140 (:REWRITE DEFAULT-LESS-THAN-2))
 (458 458 (:TYPE-PRESCRIPTION SMAN::STP))
 (442 52 (:REWRITE |(* (- x) y)|))
 (390 338 (:REWRITE DEFAULT-TIMES-2))
 (390 338 (:REWRITE DEFAULT-TIMES-1))
 (318 132 (:REWRITE DEFAULT-LESS-THAN-1))
 (312 156 (:LINEAR SMAN::BYTEP-MI))
 (300 60 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (300 60 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (300 60
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (300 60
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (286 26 (:REWRITE DEFAULT-MOD-RATIO))
 (260 52 (:REWRITE DEFAULT-MINUS))
 (260 26 (:REWRITE DEFAULT-FLOOR-RATIO))
 (256 64 (:REWRITE RATIONALP-X))
 (249 128
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (234 234
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (234 234
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (234 234
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (234 234
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (234 52 (:REWRITE |(- (* c x))|))
 (190 190 (:REWRITE REDUCE-INTEGERP-+))
 (190 190 (:META META-INTEGERP-CORRECT))
 (186 5 (:LINEAR EXPT-X->=-X))
 (186 5 (:LINEAR EXPT-X->-X))
 (182 182
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (148 5 (:LINEAR EXPT->=-1-ONE))
 (148 5 (:LINEAR EXPT-<=-1-TWO))
 (140 140 (:REWRITE THE-FLOOR-BELOW))
 (140 140 (:REWRITE THE-FLOOR-ABOVE))
 (130 26 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (130 26 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (130 26 (:REWRITE MOD-X-Y-=-X . 2))
 (130 26
      (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (130 26 (:REWRITE MOD-CANCEL-*-CONST))
 (130 26 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (130 26
      (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (130 26
      (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (128 128
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (128 128
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (124 124 (:REWRITE SIMPLIFY-SUMS-<))
 (124 124
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (124 124
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (124 124
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (124 124 (:REWRITE INTEGERP-<-CONSTANT))
 (124 124 (:REWRITE CONSTANT-<-INTEGERP))
 (124 124
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (124 124
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (124 124
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (124 124
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (124 124 (:REWRITE |(< c (- x))|))
 (124 124
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (124 124
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (124 124
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (124 124
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (124 124 (:REWRITE |(< (/ x) (/ y))|))
 (124 124 (:REWRITE |(< (- x) c)|))
 (124 124 (:REWRITE |(< (- x) (- y))|))
 (107 5 (:LINEAR EXPT-<-1-TWO))
 (83 83 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (69
  69
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (69 69
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (69 69
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (69 69
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (69 69
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (66 66
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (66 66 (:REWRITE NORMALIZE-ADDENDS))
 (64 64 (:REWRITE REDUCE-RATIONALP-+))
 (64 64 (:REWRITE REDUCE-RATIONALP-*))
 (64 64 (:REWRITE RATIONALP-MINUS-X))
 (64 64 (:META META-RATIONALP-CORRECT))
 (60 60 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
 (60 60 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (60 60
     (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (60 60 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (60 60
     (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (60 60 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (56 56
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (56 56
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (56 56 (:REWRITE |(< (/ x) 0)|))
 (56 56 (:REWRITE |(< (* x y) 0)|))
 (52 26 (:REWRITE DEFAULT-FLOOR-1))
 (35 29 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (35 29
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (35 29
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (32 32 (:REWRITE |(< 0 (* x y))|))
 (30 30
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (30 30
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (30 30 (:REWRITE |(< 0 (/ x))|))
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
 (26 26
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (26 26
     (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (26 26 (:REWRITE DEFAULT-MOD-2))
 (26 26 (:REWRITE DEFAULT-MOD-1))
 (26 26 (:REWRITE DEFAULT-LOGAND-1))
 (26 26 (:REWRITE DEFAULT-FLOOR-2))
 (26 26 (:REWRITE |(mod x (- y))| . 3))
 (26 26 (:REWRITE |(mod x (- y))| . 2))
 (26 26 (:REWRITE |(mod x (- y))| . 1))
 (26 26
     (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (26 26
     (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (26 26 (:REWRITE |(mod (- x) y)| . 3))
 (26 26 (:REWRITE |(mod (- x) y)| . 2))
 (26 26 (:REWRITE |(mod (- x) y)| . 1))
 (26 26
     (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (22 22 (:REWRITE ZP-OPEN))
 (20 20 (:REWRITE DEFAULT-EXPT-1))
 (20 20 (:REWRITE |(expt 1/c n)|))
 (20 20 (:REWRITE |(expt (- x) n)|))
 (16 4 (:REWRITE |(+ c (+ d x))|))
 (12 4 (:REWRITE SMAN::!I-I))
 (10 10
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (10 10
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (10 10
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (10 10
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (5 5 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (5 5 (:LINEAR EXPT-LINEAR-UPPER-<))
 (5 5 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (5 5 (:LINEAR EXPT-LINEAR-LOWER-<))
 (5 5 (:LINEAR EXPT->=-1-TWO))
 (5 5 (:LINEAR EXPT->-1-TWO))
 (5 5 (:LINEAR EXPT-<=-1-ONE))
 (5 5 (:LINEAR EXPT-<-1-ONE))
 (4 4 (:REWRITE |(< x (+ c/d y))|)))
(SMAN::R-!S
 (1634 126 (:REWRITE DEFAULT-PLUS-1))
 (1378 26 (:REWRITE CANCEL-MOD-+))
 (1014 26 (:REWRITE MOD-X-Y-=-X . 4))
 (1014 26 (:REWRITE MOD-X-Y-=-X . 3))
 (988 26 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (910 26 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (814 216 (:REWRITE INTEGERP-MINUS-X))
 (644 146 (:REWRITE DEFAULT-PLUS-2))
 (630 630
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (630 630
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (630 630
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (630 630
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (624 26 (:REWRITE MOD-ZERO . 4))
 (588 294 (:TYPE-PRESCRIPTION SMAN::NATP-MI))
 (576 64 (:REWRITE ACL2-NUMBERP-X))
 (572 26 (:REWRITE MOD-ZERO . 3))
 (494 140 (:REWRITE DEFAULT-LESS-THAN-2))
 (458 458 (:TYPE-PRESCRIPTION SMAN::STP))
 (442 52 (:REWRITE |(* (- x) y)|))
 (390 338 (:REWRITE DEFAULT-TIMES-2))
 (390 338 (:REWRITE DEFAULT-TIMES-1))
 (318 132 (:REWRITE DEFAULT-LESS-THAN-1))
 (312 156 (:LINEAR SMAN::BYTEP-MI))
 (300 60 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (300 60 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (300 60
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (300 60
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (286 26 (:REWRITE DEFAULT-MOD-RATIO))
 (260 52 (:REWRITE DEFAULT-MINUS))
 (260 26 (:REWRITE DEFAULT-FLOOR-RATIO))
 (256 64 (:REWRITE RATIONALP-X))
 (249 128
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (234 234
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (234 234
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (234 234
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (234 234
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (234 52 (:REWRITE |(- (* c x))|))
 (190 190 (:REWRITE REDUCE-INTEGERP-+))
 (190 190 (:META META-INTEGERP-CORRECT))
 (186 5 (:LINEAR EXPT-X->=-X))
 (186 5 (:LINEAR EXPT-X->-X))
 (182 182
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (148 5 (:LINEAR EXPT->=-1-ONE))
 (148 5 (:LINEAR EXPT-<=-1-TWO))
 (140 140 (:REWRITE THE-FLOOR-BELOW))
 (140 140 (:REWRITE THE-FLOOR-ABOVE))
 (130 26 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (130 26 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (130 26 (:REWRITE MOD-X-Y-=-X . 2))
 (130 26
      (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (130 26 (:REWRITE MOD-CANCEL-*-CONST))
 (130 26 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (130 26
      (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (130 26
      (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (128 128
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (128 128
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (124 124 (:REWRITE SIMPLIFY-SUMS-<))
 (124 124
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (124 124
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (124 124
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (124 124 (:REWRITE INTEGERP-<-CONSTANT))
 (124 124 (:REWRITE CONSTANT-<-INTEGERP))
 (124 124
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (124 124
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (124 124
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (124 124
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (124 124 (:REWRITE |(< c (- x))|))
 (124 124
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (124 124
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (124 124
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (124 124
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (124 124 (:REWRITE |(< (/ x) (/ y))|))
 (124 124 (:REWRITE |(< (- x) c)|))
 (124 124 (:REWRITE |(< (- x) (- y))|))
 (107 5 (:LINEAR EXPT-<-1-TWO))
 (83 83 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (69
  69
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (69 69
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (69 69
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (69 69
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (69 69
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (66 66
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (66 66 (:REWRITE NORMALIZE-ADDENDS))
 (64 64 (:REWRITE REDUCE-RATIONALP-+))
 (64 64 (:REWRITE REDUCE-RATIONALP-*))
 (64 64 (:REWRITE RATIONALP-MINUS-X))
 (64 64 (:META META-RATIONALP-CORRECT))
 (60 60 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
 (60 60 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (60 60
     (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (60 60 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (60 60
     (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (60 60 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (56 56
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (56 56
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (56 56 (:REWRITE |(< (/ x) 0)|))
 (56 56 (:REWRITE |(< (* x y) 0)|))
 (52 26 (:REWRITE DEFAULT-FLOOR-1))
 (35 29 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (35 29
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (35 29
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (32 32 (:REWRITE |(< 0 (* x y))|))
 (30 30
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (30 30
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (30 30 (:REWRITE |(< 0 (/ x))|))
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
 (26 26
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (26 26
     (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (26 26 (:REWRITE DEFAULT-MOD-2))
 (26 26 (:REWRITE DEFAULT-MOD-1))
 (26 26 (:REWRITE DEFAULT-LOGAND-1))
 (26 26 (:REWRITE DEFAULT-FLOOR-2))
 (26 26 (:REWRITE |(mod x (- y))| . 3))
 (26 26 (:REWRITE |(mod x (- y))| . 2))
 (26 26 (:REWRITE |(mod x (- y))| . 1))
 (26 26
     (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (26 26
     (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (26 26 (:REWRITE |(mod (- x) y)| . 3))
 (26 26 (:REWRITE |(mod (- x) y)| . 2))
 (26 26 (:REWRITE |(mod (- x) y)| . 1))
 (26 26
     (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (22 22 (:REWRITE ZP-OPEN))
 (20 20 (:REWRITE DEFAULT-EXPT-1))
 (20 20 (:REWRITE |(expt 1/c n)|))
 (20 20 (:REWRITE |(expt (- x) n)|))
 (16 4 (:REWRITE |(+ c (+ d x))|))
 (12 4 (:REWRITE SMAN::!S-S))
 (10 10
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (10 10
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (10 10
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (10 10
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (5 5 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (5 5 (:LINEAR EXPT-LINEAR-UPPER-<))
 (5 5 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (5 5 (:LINEAR EXPT-LINEAR-LOWER-<))
 (5 5 (:LINEAR EXPT->=-1-TWO))
 (5 5 (:LINEAR EXPT->-1-TWO))
 (5 5 (:LINEAR EXPT-<=-1-ONE))
 (5 5 (:LINEAR EXPT-<-1-ONE))
 (4 4 (:REWRITE |(< x (+ c/d y))|)))
(SMAN::UNNECESSARY-MOD
     (190 190
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (190 190
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (190 190
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (190 190
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (175 5 (:REWRITE MOD-X-Y-=-X . 4))
     (165 33 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (165 33 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (149 33
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (149 33
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (91 5 (:REWRITE MOD-ZERO . 3))
     (90 5 (:REWRITE MOD-ZERO . 4))
     (50 5 (:REWRITE DEFAULT-MOD-RATIO))
     (35 2 (:LINEAR MOD-BOUNDS-3))
     (33 33 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (33 33 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (33 33
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (33 33 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (33 33
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (33 33 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (25 5 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (25 5 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (25 5 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (25 5 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (20 4 (:LINEAR MOD-BOUNDS-2))
     (12 12
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (12 12
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (12 12 (:REWRITE DEFAULT-TIMES-2))
     (12 12 (:REWRITE DEFAULT-TIMES-1))
     (12 12 (:REWRITE DEFAULT-DIVIDE))
     (8 8 (:REWRITE THE-FLOOR-BELOW))
     (8 8 (:REWRITE THE-FLOOR-ABOVE))
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
     (8 8 (:REWRITE INTEGERP-<-CONSTANT))
     (8 8 (:REWRITE DEFAULT-LESS-THAN-2))
     (8 8 (:REWRITE DEFAULT-LESS-THAN-1))
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
     (6 6 (:REWRITE REDUCE-INTEGERP-+))
     (6 6 (:REWRITE INTEGERP-MINUS-X))
     (6 6 (:META META-INTEGERP-CORRECT))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
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
     (5 5 (:REWRITE DEFAULT-MOD-2))
     (5 5 (:REWRITE DEFAULT-MOD-1))
     (5 5 (:REWRITE |(equal c (/ x))|))
     (5 5 (:REWRITE |(equal c (- x))|))
     (5 5 (:REWRITE |(equal (/ x) c)|))
     (5 5 (:REWRITE |(equal (/ x) (/ y))|))
     (5 5 (:REWRITE |(equal (- x) c)|))
     (5 5 (:REWRITE |(equal (- x) (- y))|))
     (5 5 (:REWRITE |(< 0 (/ x))|))
     (5 5 (:REWRITE |(< 0 (* x y))|))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (2 2 (:REWRITE |(< (/ x) 0)|))
     (2 2 (:REWRITE |(< (* x y) 0)|)))
(SMAN::UNNECESSARY-FLOOR (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
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
(SMAN::MI-!R+
 (45006 108 (:LINEAR LINEAR-FLOOR-BOUNDS-1))
 (36658 2 (:REWRITE |(logand (if a b c) x)|))
 (34084 25444
        (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (32028 2 (:REWRITE |(floor (if a b c) x)|))
 (30930 412 (:REWRITE THE-FLOOR-ABOVE))
 (25444 25444
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (25444 25444
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (25444 25444
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (18414 124 (:REWRITE |(+ y x)|))
 (16782 134 (:REWRITE SMAN::UNNECESSARY-FLOOR))
 (12318 2016
        (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (11784 132 (:REWRITE CANCEL-FLOOR-+))
 (11422 330 (:REWRITE DEFAULT-PLUS-1))
 (11388 330 (:REWRITE DEFAULT-PLUS-2))
 (10694 18 (:REWRITE SMAN::UNNECESSARY-MOD))
 (10632 126 (:REWRITE NORMALIZE-ADDENDS))
 (10454 132 (:REWRITE FLOOR-ZERO . 3))
 (10108 18 (:REWRITE MOD-ZERO . 4))
 (9880 132 (:REWRITE FLOOR-ZERO . 4))
 (9860 132 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (9842 132 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (9774 1086
       (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (9774 1086
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (9774 1086
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (9774 1086
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (9774 1086
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (9178 18 (:REWRITE MOD-X-Y-=-X . 3))
 (8756 18 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (8714 18 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (8596 132 (:REWRITE FLOOR-ZERO . 5))
 (7909 459 (:REWRITE INTEGERP-MINUS-X))
 (7896 1886 (:REWRITE DEFAULT-TIMES-2))
 (7894 18 (:REWRITE MOD-X-Y-=-X . 4))
 (6330 1886 (:REWRITE DEFAULT-TIMES-1))
 (6206 18 (:REWRITE CANCEL-MOD-+))
 (5820 4 (:REWRITE |(mod (floor x y) z)| . 1))
 (5770 304 (:REWRITE |(* (- x) y)|))
 (5430 1086
       (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
 (5430 1086
       (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (5430 1086
       (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (5430 1086
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (5430 1086
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (5430 1086
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (5430 1086
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (5430 1086
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (5430 1086
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
 (5430 1086
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (5430 1086
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (3854 132 (:REWRITE FLOOR-=-X/Y . 2))
 (3508 304 (:REWRITE DEFAULT-MINUS))
 (3484 134 (:REWRITE DEFAULT-FLOOR-RATIO))
 (3468 34 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (3390 304 (:REWRITE |(- (* c x))|))
 (3342 132 (:REWRITE FLOOR-=-X/Y . 3))
 (2416 18 (:REWRITE MOD-ZERO . 3))
 (2060 412 (:REWRITE THE-FLOOR-BELOW))
 (2016 2016
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (2016 2016
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (2016 2016
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (1816 356
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (1410 18 (:REWRITE DEFAULT-MOD-RATIO))
 (1272 378 (:REWRITE DEFAULT-LESS-THAN-1))
 (1186 378 (:REWRITE DEFAULT-LESS-THAN-2))
 (1086 1086 (:TYPE-PRESCRIPTION FLOOR))
 (1064 132 (:REWRITE FLOOR-ZERO . 2))
 (1064 132 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (1064 132 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (1048 132 (:REWRITE FLOOR-CANCEL-*-CONST))
 (1012 1012
       (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (976 4
      (:REWRITE |(floor (floor x y) z)| . 1))
 (898 18 (:REWRITE MOD-X-Y-=-X . 2))
 (898 18 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (898 18
      (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (846 370
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (740 134 (:REWRITE DEFAULT-FLOOR-1))
 (735 39
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (656 54 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (632 132
      (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (564 132
      (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (560 128
      (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (535 39
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (494 18 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (494 18 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (494 18
      (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (494 18 (:REWRITE MOD-CANCEL-*-CONST))
 (444 40 (:REWRITE DEFAULT-LOGAND-2))
 (440 54 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (426 360
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (422 18 (:REWRITE DEFAULT-MOD-1))
 (418 2 (:REWRITE |(* (if a b c) x)|))
 (360 360
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (360 360
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (360 360 (:REWRITE INTEGERP-<-CONSTANT))
 (360 360 (:REWRITE CONSTANT-<-INTEGERP))
 (360 360
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (360 360
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (360 360
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (360 360
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (360 360 (:REWRITE |(< c (- x))|))
 (360 360
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (360 360
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (360 360
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (360 360
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (360 360 (:REWRITE |(< (/ x) (/ y))|))
 (360 360 (:REWRITE |(< (- x) c)|))
 (360 360 (:REWRITE |(< (- x) (- y))|))
 (356 356 (:REWRITE SIMPLIFY-SUMS-<))
 (309 309 (:REWRITE REDUCE-INTEGERP-+))
 (309 309 (:META META-INTEGERP-CORRECT))
 (256 24 (:REWRITE ACL2-NUMBERP-X))
 (235 235 (:REWRITE |(< (* x y) 0)|))
 (225 225 (:REWRITE |(< (/ x) 0)|))
 (223 223
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (223 223
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (213 15 (:REWRITE ZP-OPEN))
 (208 128
      (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (170 34 (:REWRITE |(+ 0 x)|))
 (142 142 (:TYPE-PRESCRIPTION ABS))
 (137 1 (:REWRITE MOD-X-Y-=-X-Y . 1))
 (135 27 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (135 27 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (135 27
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (135 27
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (134 134 (:REWRITE DEFAULT-FLOOR-2))
 (128 128 (:REWRITE |(floor x (- y))| . 2))
 (128 128 (:REWRITE |(floor x (- y))| . 1))
 (128 128
      (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (128 128
      (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (128 128 (:REWRITE |(floor (- x) y)| . 2))
 (128 128 (:REWRITE |(floor (- x) y)| . 1))
 (118 39 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (116 8 (:REWRITE RATIONALP-X))
 (114 30 (:REWRITE SMAN::!MI-MI))
 (92 92
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (72 8 (:REWRITE FLOOR-POSITIVE . 2))
 (72 8 (:REWRITE FLOOR-NONPOSITIVE . 1))
 (70 14
     (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (69 69
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (69 69
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (69 69 (:REWRITE |(< 0 (/ x))|))
 (69 69 (:REWRITE |(< 0 (* x y))|))
 (68 68
     (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (68 34 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
 (60 12 (:REWRITE |(+ c (+ d x))|))
 (60 2
     (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (60 2 (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (54 6 (:LINEAR SMAN::BYTEP-MI))
 (53 1 (:REWRITE MOD-X-Y-=-X+Y . 1))
 (48 6 (:REWRITE SMAN::!MI-!MI-DIFF))
 (47 2 (:REWRITE |(equal (+ (- c) x) y)|))
 (42 18 (:REWRITE SMAN::STP-!MI))
 (41 41
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (41 41
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (41 41 (:REWRITE |(equal c (/ x))|))
 (41 41 (:REWRITE |(equal (/ x) (/ y))|))
 (41 41 (:REWRITE |(equal (- x) (- y))|))
 (40 8 (:REWRITE FLOOR-POSITIVE . 4))
 (40 8 (:REWRITE FLOOR-POSITIVE . 3))
 (40 8 (:REWRITE FLOOR-NONPOSITIVE . 3))
 (40 8 (:REWRITE FLOOR-NONPOSITIVE . 2))
 (39 39
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (39 39 (:REWRITE |(equal c (- x))|))
 (39 39 (:REWRITE |(equal (- x) c)|))
 (36 6 (:REWRITE SMAN::STP-!R))
 (34 34 (:REWRITE |(+ x (- x))|))
 (27 27 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
 (27 27 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (27 27
     (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (27 27 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (27 27
     (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (27 27 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (27 27
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (20 4 (:REWRITE FLOOR-=-X/Y . 4))
 (20 4
     (:REWRITE |(equal (floor (+ x y) z) x)|))
 (18 18
     (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (18 18 (:REWRITE DEFAULT-MOD-2))
 (14
   14
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (14
  14
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (14 14
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (14 14
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (14 14
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (14 14
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (14 14 (:REWRITE |(mod x (- y))| . 3))
 (14 14 (:REWRITE |(mod x (- y))| . 2))
 (14 14 (:REWRITE |(mod x (- y))| . 1))
 (14 14
     (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (14 14
     (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (14 14 (:REWRITE |(mod (- x) y)| . 3))
 (14 14 (:REWRITE |(mod (- x) y)| . 2))
 (14 14 (:REWRITE |(mod (- x) y)| . 1))
 (14 14
     (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (10 10 (:REWRITE |(* a (/ a) b)|))
 (8 8 (:REWRITE REDUCE-RATIONALP-+))
 (8 8 (:REWRITE REDUCE-RATIONALP-*))
 (8 8 (:REWRITE RATIONALP-MINUS-X))
 (8 8 (:REWRITE FLOOR-POSITIVE . 1))
 (8 8 (:META META-RATIONALP-CORRECT))
 (6 6 (:REWRITE |(< y (+ (- c) x))|))
 (6 6 (:REWRITE |(< x (+ c/d y))|))
 (4 4 (:REWRITE FLOOR-ZERO . 1))
 (4 4 (:REWRITE |(mod (floor x y) z)| . 5))
 (4 4 (:REWRITE |(mod (floor x y) z)| . 4))
 (4 4 (:REWRITE |(mod (floor x y) z)| . 3))
 (4 4 (:REWRITE |(mod (floor x y) z)| . 2))
 (4 4
    (:REWRITE |(floor (floor x y) z)| . 5))
 (4 4
    (:REWRITE |(floor (floor x y) z)| . 4))
 (4 4
    (:REWRITE |(floor (floor x y) z)| . 3))
 (4 4
    (:REWRITE |(floor (floor x y) z)| . 2))
 (2 2 (:REWRITE DEFAULT-DIVIDE))
 (2 2 (:REWRITE |(not (equal x (/ y)))|))
 (2 2 (:REWRITE |(equal x (/ y))|))
 (2 2
    (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (2 2 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (1 1
    (:REWRITE |(equal (mod (+ x y) z) x)|)))
(SMAN::MI-!R-
 (22503 54 (:LINEAR LINEAR-FLOOR-BOUNDS-1))
 (18329 1 (:REWRITE |(logand (if a b c) x)|))
 (17163 12843
        (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (16014 1 (:REWRITE |(floor (if a b c) x)|))
 (15503 244 (:REWRITE THE-FLOOR-ABOVE))
 (12843 12843
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (12843 12843
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (12843 12843
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (8453 69 (:REWRITE SMAN::UNNECESSARY-FLOOR))
 (6209 1058
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (5998 68 (:REWRITE CANCEL-FLOOR-+))
 (5744 194 (:REWRITE DEFAULT-PLUS-1))
 (5409 11 (:REWRITE SMAN::UNNECESSARY-MOD))
 (5355 68 (:REWRITE FLOOR-ZERO . 3))
 (5090 11 (:REWRITE MOD-ZERO . 4))
 (5010 68 (:REWRITE FLOOR-ZERO . 4))
 (4992 68 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (4989 68 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (4887 543 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (4887 543
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (4887 543
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (4887 543
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (4887 543
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (4659 11 (:REWRITE MOD-X-Y-=-X . 3))
 (4446 11 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (4419 11 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (4368 68 (:REWRITE FLOOR-ZERO . 5))
 (4084 267 (:REWRITE INTEGERP-MINUS-X))
 (4017 11 (:REWRITE MOD-X-Y-=-X . 4))
 (3986 981 (:REWRITE DEFAULT-TIMES-2))
 (3209 11 (:REWRITE CANCEL-MOD-+))
 (3203 981 (:REWRITE DEFAULT-TIMES-1))
 (3181 366 (:REWRITE |(* y x)|))
 (2953 160 (:REWRITE |(* (- x) y)|))
 (2910 2 (:REWRITE |(mod (floor x y) z)| . 1))
 (2715 543 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
 (2715 543 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (2715 543 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (2715 543
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (2715 543
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (2715 543
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (2715 543
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (2715 543
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (2715 543
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
 (2715 543
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (2715 543
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (2363 1 (:REWRITE |(< (if a b c) x)|))
 (1971 68 (:REWRITE FLOOR-=-X/Y . 2))
 (1794 160 (:REWRITE DEFAULT-MINUS))
 (1764 69 (:REWRITE DEFAULT-FLOOR-RATIO))
 (1738 21 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (1731 160 (:REWRITE |(- (* c x))|))
 (1715 68 (:REWRITE FLOOR-=-X/Y . 3))
 (1252 11 (:REWRITE MOD-ZERO . 3))
 (1068 244 (:REWRITE THE-FLOOR-BELOW))
 (1058 1058
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (1058 1058
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (1058 1058
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (956 218
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (727 11 (:REWRITE DEFAULT-MOD-RATIO))
 (682 227 (:REWRITE DEFAULT-LESS-THAN-1))
 (631 227 (:REWRITE DEFAULT-LESS-THAN-2))
 (543 543 (:TYPE-PRESCRIPTION FLOOR))
 (542 68 (:REWRITE FLOOR-ZERO . 2))
 (542 68 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (542 68 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (534 68 (:REWRITE FLOOR-CANCEL-*-CONST))
 (530 530
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (488 2
      (:REWRITE |(floor (floor x y) z)| . 1))
 (465 225
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (463 23
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (459 11 (:REWRITE MOD-X-Y-=-X . 2))
 (459 11 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (459 11
      (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (372 69 (:REWRITE DEFAULT-FLOOR-1))
 (328 27 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (326 68
      (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (301 23
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (284 68
      (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (282 66
      (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (260 26 (:REWRITE ACL2-NUMBERP-X))
 (257 11 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (257 11 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (257 11
      (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (257 11 (:REWRITE MOD-CANCEL-*-CONST))
 (255 220
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (234 218
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (228 26 (:REWRITE DEFAULT-LOGAND-2))
 (220 220
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (220 220
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (220 220 (:REWRITE INTEGERP-<-CONSTANT))
 (220 220 (:REWRITE CONSTANT-<-INTEGERP))
 (220 220
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (220 220
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (220 220
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (220 220
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (220 220 (:REWRITE |(< c (- x))|))
 (220 220
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (220 220
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (220 220
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (220 220
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (220 220 (:REWRITE |(< (/ x) (/ y))|))
 (220 220 (:REWRITE |(< (- x) c)|))
 (220 220 (:REWRITE |(< (- x) (- y))|))
 (220 27 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (213 11 (:REWRITE DEFAULT-MOD-1))
 (209 1 (:REWRITE |(* (if a b c) x)|))
 (190 7 (:REWRITE SMAN::MI-!R+))
 (188 188 (:REWRITE REDUCE-INTEGERP-+))
 (188 188 (:META META-INTEGERP-CORRECT))
 (145 29 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (145 29 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (145 29
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (145 29
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (139 139 (:REWRITE |(< (* x y) 0)|))
 (137 1 (:REWRITE MOD-X-Y-=-X-Y . 1))
 (134 134 (:REWRITE |(< (/ x) 0)|))
 (132 132
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (132 132
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (117 12 (:REWRITE RATIONALP-X))
 (114 66
      (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (109 10 (:REWRITE ZP-OPEN))
 (86 23 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (75 75 (:TYPE-PRESCRIPTION ABS))
 (69 69 (:REWRITE DEFAULT-FLOOR-2))
 (66 66 (:REWRITE |(floor x (- y))| . 2))
 (66 66 (:REWRITE |(floor x (- y))| . 1))
 (66 66
     (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (66 66
     (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (66 66 (:REWRITE |(floor (- x) y)| . 2))
 (66 66 (:REWRITE |(floor (- x) y)| . 1))
 (63 17 (:REWRITE SMAN::!MI-MI))
 (60 60
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (53 1 (:REWRITE MOD-X-Y-=-X+Y . 1))
 (47 2 (:REWRITE |(equal (+ (- c) x) y)|))
 (45 9
     (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (37 37
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (37 37
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (37 37 (:REWRITE |(< 0 (/ x))|))
 (37 37 (:REWRITE |(< 0 (* x y))|))
 (36 36
     (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (36 4 (:REWRITE FLOOR-POSITIVE . 2))
 (36 4 (:REWRITE FLOOR-NONPOSITIVE . 1))
 (32 8 (:REWRITE |(+ c (+ d x))|))
 (29 29 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
 (29 29 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (29 29
     (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (29 29 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (29 29
     (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (29 29 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (27 3 (:LINEAR SMAN::BYTEP-MI))
 (24 3 (:REWRITE SMAN::!MI-!MI-DIFF))
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
 (21 9 (:REWRITE SMAN::STP-!MI))
 (20 4 (:REWRITE FLOOR-POSITIVE . 4))
 (20 4 (:REWRITE FLOOR-POSITIVE . 3))
 (20 4 (:REWRITE FLOOR-NONPOSITIVE . 3))
 (20 4 (:REWRITE FLOOR-NONPOSITIVE . 2))
 (18 3 (:REWRITE SMAN::STP-!R))
 (14 14 (:REWRITE |(< y (+ (- c) x))|))
 (14 14 (:REWRITE |(< x (+ c/d y))|))
 (12 12
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (12 12 (:REWRITE REDUCE-RATIONALP-+))
 (12 12 (:REWRITE REDUCE-RATIONALP-*))
 (12 12 (:REWRITE RATIONALP-MINUS-X))
 (12 12 (:META META-RATIONALP-CORRECT))
 (11 11
     (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (11 11 (:REWRITE DEFAULT-MOD-2))
 (10 2 (:REWRITE FLOOR-=-X/Y . 4))
 (10 2
     (:REWRITE |(equal (floor (+ x y) z) x)|))
 (9
   9
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (9
  9
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (9 9
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (9 9
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (9 9
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (9 9
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (9 9 (:REWRITE |(mod x (- y))| . 3))
 (9 9 (:REWRITE |(mod x (- y))| . 2))
 (9 9 (:REWRITE |(mod x (- y))| . 1))
 (9 9
    (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (9 9
    (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (9 9 (:REWRITE |(mod (- x) y)| . 3))
 (9 9 (:REWRITE |(mod (- x) y)| . 2))
 (9 9 (:REWRITE |(mod (- x) y)| . 1))
 (9 9
    (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (5 5 (:REWRITE |(* a (/ a) b)|))
 (4 4 (:REWRITE FLOOR-POSITIVE . 1))
 (2 2 (:REWRITE FLOOR-ZERO . 1))
 (2 2 (:REWRITE |(mod (floor x y) z)| . 5))
 (2 2 (:REWRITE |(mod (floor x y) z)| . 4))
 (2 2 (:REWRITE |(mod (floor x y) z)| . 3))
 (2 2 (:REWRITE |(mod (floor x y) z)| . 2))
 (2 2
    (:REWRITE |(floor (floor x y) z)| . 5))
 (2 2
    (:REWRITE |(floor (floor x y) z)| . 4))
 (2 2
    (:REWRITE |(floor (floor x y) z)| . 3))
 (2 2
    (:REWRITE |(floor (floor x y) z)| . 2))
 (1 1
    (:REWRITE |(equal (mod (+ x y) z) x)|)))
(SMAN::R-1-!MI
 (130401 348 (:LINEAR MOD-BOUNDS-1))
 (118688 116 (:REWRITE MOD-X-Y-=-X-Y . 1))
 (63648 116 (:REWRITE MOD-X-Y-=-X+Y . 1))
 (57473 117 (:REWRITE |(equal (+ (- c) x) y)|))
 (19080 360 (:REWRITE CANCEL-MOD-+))
 (15186 15186
        (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (15186 15186
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (15186 15186
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (15186 15186
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (12910 360 (:REWRITE MOD-X-Y-=-X . 4))
 (12570 360 (:REWRITE MOD-X-Y-=-X . 3))
 (12567 360 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (11910 360 (:REWRITE SMAN::UNNECESSARY-MOD))
 (11470 360 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (11130 2226 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (11130 2226 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (11130 2226
        (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (11130 2226
        (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (9570 1290 (:REWRITE INTEGERP-MINUS-X))
 (7563 360 (:REWRITE MOD-ZERO . 3))
 (7443 360 (:REWRITE MOD-ZERO . 4))
 (6125 725 (:REWRITE |(* (- x) y)|))
 (5088 1270 (:REWRITE |(* y x)|))
 (4059 4059 (:TYPE-PRESCRIPTION SMAN::MP))
 (3990 1995
       (:TYPE-PRESCRIPTION SMAN::NATP-NTH-MP))
 (3960 360 (:REWRITE DEFAULT-MOD-RATIO))
 (3828 174 (:LINEAR MOD-BOUNDS-3))
 (3642 1578 (:LINEAR SMAN::BYTEP-NTH-MP))
 (3633 3625 (:REWRITE DEFAULT-TIMES-2))
 (3633 3625 (:REWRITE DEFAULT-TIMES-1))
 (3625 3625
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (3625 3625
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (3625 3625
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (3625 3625
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (3625 725 (:REWRITE DEFAULT-MINUS))
 (3397 513
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (3397 513
       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (3265 725 (:REWRITE |(- (* c x))|))
 (2977 513 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (2226 2226 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
 (2226 2226 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (2226 2226
       (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (2226 2226
       (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (2226 2226
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (2226 2226
       (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (2168 616
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (1995 1995
       (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (1803 437 (:REWRITE DEFAULT-PLUS-2))
 (1800 360 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (1800 360 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (1800 360 (:REWRITE MOD-X-Y-=-X . 2))
 (1800 360
       (:REWRITE |(mod (+ x (mod a b)) y)|))
 (1800 360
       (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (1752 360
       (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (1752 360
       (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (1740 348 (:LINEAR MOD-BOUNDS-2))
 (1739 1739 (:REWRITE THE-FLOOR-BELOW))
 (1739 1739 (:REWRITE THE-FLOOR-ABOVE))
 (1739 1739
       (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (1739 1739
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (1739 1739
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (1739 1739
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (1739 1739 (:REWRITE INTEGERP-<-CONSTANT))
 (1739 1739 (:REWRITE DEFAULT-LESS-THAN-2))
 (1739 1739 (:REWRITE DEFAULT-LESS-THAN-1))
 (1739 1739 (:REWRITE CONSTANT-<-INTEGERP))
 (1739 1739
       (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (1739 1739
       (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (1739 1739
       (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (1739 1739
       (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (1739 1739 (:REWRITE |(< c (- x))|))
 (1739 1739
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (1739 1739
       (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (1739 1739
       (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (1739 1739
       (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (1739 1739 (:REWRITE |(< (/ x) (/ y))|))
 (1739 1739 (:REWRITE |(< (- x) c)|))
 (1739 1739 (:REWRITE |(< (- x) (- y))|))
 (1737 1737 (:REWRITE SIMPLIFY-SUMS-<))
 (1737 1737
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (1737 1737
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (1732 360 (:REWRITE MOD-CANCEL-*-CONST))
 (1284 437 (:REWRITE DEFAULT-PLUS-1))
 (930 930 (:REWRITE REDUCE-INTEGERP-+))
 (930 930 (:META META-INTEGERP-CORRECT))
 (916 916 (:REWRITE |(< (/ x) 0)|))
 (916 916 (:REWRITE |(< (* x y) 0)|))
 (914 914
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (914 914
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (616 616
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (513 513
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (513 513 (:REWRITE |(equal c (/ x))|))
 (513 513 (:REWRITE |(equal c (- x))|))
 (513 513 (:REWRITE |(equal (/ x) c)|))
 (513 513 (:REWRITE |(equal (/ x) (/ y))|))
 (513 513 (:REWRITE |(equal (- x) c)|))
 (513 513 (:REWRITE |(equal (- x) (- y))|))
 (408 360
      (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (408 360
      (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (390 15 (:REWRITE MOD-ZERO . 1))
 (363 363
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (360 360 (:REWRITE DEFAULT-MOD-2))
 (360 360 (:REWRITE DEFAULT-MOD-1))
 (360 360 (:REWRITE |(mod x (- y))| . 3))
 (360 360 (:REWRITE |(mod x (- y))| . 2))
 (360 360 (:REWRITE |(mod x (- y))| . 1))
 (360 360
      (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (360 360
      (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (360 360 (:REWRITE |(mod (- x) y)| . 3))
 (360 360 (:REWRITE |(mod (- x) y)| . 2))
 (360 360 (:REWRITE |(mod (- x) y)| . 1))
 (352 32 (:REWRITE |(+ y (+ x z))|))
 (348 5
      (:REWRITE |(equal (mod a n) (mod b n))|))
 (343 343
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (343 343
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (343 343 (:REWRITE |(< 0 (/ x))|))
 (343 343 (:REWRITE |(< 0 (* x y))|))
 (256 64 (:REWRITE |(+ c (+ d x))|))
 (165 165
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (165 165 (:REWRITE NORMALIZE-ADDENDS))
 (136 4 (:REWRITE ASH-TO-FLOOR))
 (116 116
      (:REWRITE |(equal (mod (+ x y) z) x)|))
 (75 15 (:REWRITE MOD-ZERO . 2))
 (54 54
     (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 3))
 (54 54
     (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 2))
 (54 54
     (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (40 4 (:REWRITE FLOOR-=-X/Y . 3))
 (40 4 (:REWRITE DEFAULT-FLOOR-RATIO))
 (36 4 (:REWRITE SMAN::UNNECESSARY-FLOOR))
 (22 22 (:REWRITE DEFAULT-CDR))
 (16 8 (:LINEAR SMAN::R-BOUND))
 (14 14 (:REWRITE DEFAULT-LOGAND-1))
 (12
   12
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (12
  12
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (12 12
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (12 12
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (12 12
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (12 12
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (11 11 (:REWRITE DEFAULT-CAR))
 (8 4 (:REWRITE DEFAULT-FLOOR-1))
 (5 5 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (4 4 (:REWRITE DEFAULT-FLOOR-2))
 (4 1 (:REWRITE SMAN::!NTH-NTH)))
(SMAN::R-!R-SAME-LEMMA
 (2115 180 (:REWRITE DEFAULT-PLUS-2))
 (1035 146 (:REWRITE DEFAULT-TIMES-2))
 (996 8
      (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
 (572
  572
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (572 572
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (572
     572
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (572 572
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (509 62 (:REWRITE DEFAULT-MINUS))
 (455 455
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (455 455
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (455 455
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (395 180 (:REWRITE DEFAULT-PLUS-1))
 (367 146 (:REWRITE DEFAULT-TIMES-1))
 (248 8 (:DEFINITION NFIX))
 (240 40 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (240 40 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (235 235
      (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (235 235
      (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (220 40
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (220 40
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (211 2 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (211 2 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (206 206 (:TYPE-PRESCRIPTION NUMERATOR-ZERO))
 (206 206
      (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 2))
 (206 206
      (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 1))
 (206 206
      (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 2))
 (206 206
      (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 1))
 (194 2 (:REWRITE FLOOR-ZERO . 3))
 (183 2 (:REWRITE CANCEL-MOD-+))
 (165 2 (:REWRITE CANCEL-FLOOR-+))
 (115 42 (:REWRITE DEFAULT-LESS-THAN-1))
 (100 10 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (100 10
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (100 10
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (100 10
      (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (100 10
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (96 38 (:REWRITE SIMPLIFY-SUMS-<))
 (96 38
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (96 38 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (93 2 (:REWRITE MOD-ZERO . 3))
 (90 9 (:REWRITE DEFAULT-DIVIDE))
 (89 13 (:REWRITE |(* (- x) y)|))
 (88 2 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (86 2 (:REWRITE |(integerp (- x))|))
 (84 84
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (84 84
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (84 84
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (84 84
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (84 2 (:REWRITE FLOOR-=-X/Y . 3))
 (83 83
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (81 2 (:REWRITE FLOOR-ZERO . 5))
 (81 2 (:REWRITE FLOOR-ZERO . 4))
 (78 2 (:REWRITE FLOOR-=-X/Y . 2))
 (76 40 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (62 42 (:REWRITE |(< (- x) (- y))|))
 (62 2 (:REWRITE SMAN::UNNECESSARY-FLOOR))
 (60 42 (:REWRITE DEFAULT-LESS-THAN-2))
 (60 10 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (60 10 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (60 10
     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (60 10
     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (60 10
     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (60 10
     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (60 10
     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (60 10
     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
 (60 10
     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (60 10
     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (49 2 (:REWRITE DEFAULT-MOD-RATIO))
 (49 2 (:REWRITE DEFAULT-FLOOR-RATIO))
 (48 8 (:DEFINITION IFIX))
 (46 4 (:REWRITE INTEGERP==>NUMERATOR-=-X))
 (46 4 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
 (46 2 (:LINEAR EXPT->-1-ONE))
 (45 42
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (45 42
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (42 42 (:REWRITE THE-FLOOR-BELOW))
 (42 42 (:REWRITE THE-FLOOR-ABOVE))
 (42 42
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (42 42
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
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
 (41 15 (:REWRITE INTEGERP-MINUS-X))
 (40 40 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (40 40
     (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (40 40 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (40 40
     (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (39 39 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (39 2 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (39 2
     (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (36 2 (:REWRITE MOD-X-Y-=-X . 4))
 (36 2 (:REWRITE MOD-X-Y-=-X . 3))
 (35 2 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (32 32 (:REWRITE DEFAULT-EXPT-2))
 (32 32 (:REWRITE DEFAULT-EXPT-1))
 (32 32 (:REWRITE |(expt 1/c n)|))
 (32 32 (:REWRITE |(expt (- x) n)|))
 (32 2 (:REWRITE SMAN::UNNECESSARY-MOD))
 (30 4 (:REWRITE DEFAULT-RATIONAL-NUMERATOR))
 (30 4
     (:REWRITE DEFAULT-RATIONAL-DENOMINATOR))
 (30 2 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (30 2 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (30 2 (:REWRITE MOD-X-Y-=-X . 2))
 (30 2 (:REWRITE FLOOR-ZERO . 2))
 (30 2 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (30 2 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (28 28 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (28 28 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (28 28 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (28 28 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (28 2 (:LINEAR EXPT->=-1-ONE))
 (27 27 (:REWRITE |(< (/ x) 0)|))
 (27 27 (:REWRITE |(< (* x y) 0)|))
 (23 23
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (23 23
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (21 2
     (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (21 2 (:REWRITE MOD-CANCEL-*-CONST))
 (21 2
     (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (21 2 (:REWRITE FLOOR-CANCEL-*-CONST))
 (21 2
     (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (21 2
     (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (20 14 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (19 19 (:REWRITE FOLD-CONSTS-IN-+))
 (19 2 (:REWRITE MOD-ZERO . 4))
 (17 2
     (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (17 2
     (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (13 13 (:REWRITE REDUCE-INTEGERP-+))
 (13 13 (:META META-INTEGERP-CORRECT))
 (11 2 (:REWRITE DEFAULT-MOD-2))
 (11 2 (:REWRITE DEFAULT-FLOOR-2))
 (6 6 (:TYPE-PRESCRIPTION ABS))
 (6 6
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (6 6 (:REWRITE |(* c (* d x))|))
 (4 4 (:TYPE-PRESCRIPTION RATIONALP-MOD))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (3 3
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (3 3
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (3 3 (:REWRITE |(equal c (/ x))|))
 (3 3 (:REWRITE |(equal c (- x))|))
 (3 3 (:REWRITE |(equal (/ x) c)|))
 (3 3 (:REWRITE |(equal (/ x) (/ y))|))
 (3 3 (:REWRITE |(equal (- x) c)|))
 (3 3 (:REWRITE |(equal (- x) (- y))|))
 (3 3 (:REWRITE |(< 0 (/ x))|))
 (3 3 (:REWRITE |(< 0 (* x y))|))
 (2 2
    (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (2 2
    (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (2 2 (:REWRITE DEFAULT-MOD-1))
 (2 2 (:REWRITE DEFAULT-FLOOR-1))
 (2 2 (:REWRITE |(mod x (- y))| . 3))
 (2 2 (:REWRITE |(mod x (- y))| . 2))
 (2 2 (:REWRITE |(mod x (- y))| . 1))
 (2 2
    (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (2 2 (:REWRITE |(mod (- x) y)| . 3))
 (2 2 (:REWRITE |(mod (- x) y)| . 2))
 (2 2 (:REWRITE |(mod (- x) y)| . 1))
 (2 2
    (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (2 2 (:REWRITE |(floor x (- y))| . 2))
 (2 2 (:REWRITE |(floor x (- y))| . 1))
 (2 2
    (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (2 2 (:REWRITE |(floor (- x) y)| . 2))
 (2 2 (:REWRITE |(floor (- x) y)| . 1))
 (2 2
    (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (2 2 (:LINEAR EXPT-X->=-X))
 (2 2 (:LINEAR EXPT-X->-X))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-TWO))
 (2 2 (:LINEAR EXPT-<-1-ONE))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (1 1
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (1 1
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (1 1
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE)))
(SMAN::R-!R-SAME
 (225251 558 (:LINEAR LINEAR-FLOOR-BOUNDS-1))
 (219948 12 (:REWRITE |(logand (if a b c) x)|))
 (192168 12 (:REWRITE |(floor (if a b c) x)|))
 (162051 4512 (:REWRITE THE-FLOOR-ABOVE))
 (142426 142426
         (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (142426 142426
         (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (142426 142426
         (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (96905 851 (:REWRITE SMAN::UNNECESSARY-FLOOR))
 (74429 5438 (:REWRITE DEFAULT-PLUS-1))
 (67221 5438 (:REWRITE DEFAULT-PLUS-2))
 (62496 741 (:REWRITE CANCEL-FLOOR-+))
 (59096 312 (:REWRITE MOD-ZERO . 4))
 (58714 741 (:REWRITE FLOOR-ZERO . 3))
 (57240 309 (:REWRITE MOD-X-Y-=-X . 3))
 (56183 14977 (:REWRITE DEFAULT-TIMES-2))
 (56120 312 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (54516 312 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (52900 5842
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (52852 5842
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (52852 5842
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (52852 5842
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (52751 741 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (52744 5830
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (52415 741 (:REWRITE FLOOR-ZERO . 4))
 (51966 741 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (50984 309 (:REWRITE MOD-X-Y-=-X . 4))
 (49795 309 (:REWRITE CANCEL-MOD-+))
 (46326 741 (:REWRITE FLOOR-ZERO . 5))
 (44415 14977 (:REWRITE DEFAULT-TIMES-1))
 (42541 2928 (:REWRITE INTEGERP-MINUS-X))
 (37945 2087 (:REWRITE |(* (- x) y)|))
 (34207 4
        (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 1))
 (30085 4
        (:REWRITE |(floor (+ x y) z) where (< 0 z)| . 1))
 (30065 5 (:REWRITE MOD-X-Y-=-X-Y . 1))
 (29362 5842
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (29362 5842
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (29362 5842
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (29362 5842
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (29362 5842
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (29362 5842
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (29362 5842
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (29362 5842
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
 (29362 5842
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (29362 5842
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (22537 4080
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (21814 741 (:REWRITE FLOOR-=-X/Y . 2))
 (21589 851 (:REWRITE DEFAULT-FLOOR-RATIO))
 (20414 302
        (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (20201 2198 (:REWRITE DEFAULT-MINUS))
 (19262 802 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (17374 168 (:REWRITE SMAN::MI-!R-))
 (14908 5 (:REWRITE MOD-X-Y-=-X+Y . 1))
 (14107 3975
        (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (14008 314 (:REWRITE DEFAULT-MOD-RATIO))
 (13839 734
        (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (12958 4512 (:REWRITE THE-FLOOR-BELOW))
 (11731 4335 (:REWRITE DEFAULT-LESS-THAN-1))
 (11717 279 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (10582
  10582
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (10582
      10582
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (10582
     10582
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (10582 10582
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (10582 10582
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (10009 10009
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (10009 10009
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (10009 10009
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (9290 4335 (:REWRITE DEFAULT-LESS-THAN-2))
 (8476 741 (:REWRITE FLOOR-CANCEL-*-CONST))
 (7297 4316
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (7107 309
       (:REWRITE |(mod (+ x (mod a b)) y)|))
 (7107 309
       (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (6891 309 (:REWRITE MOD-X-Y-=-X . 2))
 (6329 309 (:REWRITE MOD-CANCEL-*-CONST))
 (5947 741 (:REWRITE FLOOR-ZERO . 2))
 (5947 741 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (5947 741 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (5420 20
       (:REWRITE |(floor (floor x y) z)| . 1))
 (5370 925
       (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (5370 925
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (4863 925 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (4681 4248
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (4439 312 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (4439 312 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (4430 1206 (:REWRITE |(< 0 (/ x))|))
 (4389 439
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (4375 851 (:REWRITE DEFAULT-FLOOR-1))
 (4240 150 (:REWRITE |(* (/ c) (expt d n))|))
 (4232 4188
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (4225 4083
       (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (4188 4188
       (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (4188 4188
       (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (4188 4188
       (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (4188 4188
       (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (4188 4188
       (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (4188 4188
       (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (4188 4188
       (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (4188 4188 (:REWRITE |(< (/ x) (/ y))|))
 (4188 4188 (:REWRITE |(< (- x) (- y))|))
 (4111 4084 (:REWRITE |(< c (- x))|))
 (4083 4083 (:REWRITE INTEGERP-<-CONSTANT))
 (4083 4083 (:REWRITE CONSTANT-<-INTEGERP))
 (4083 4083 (:REWRITE |(< (- x) c)|))
 (3324 87 (:REWRITE |(integerp (- x))|))
 (3121 105
       (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (3040 725
       (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (3020 705
       (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (2882 314 (:REWRITE DEFAULT-MOD-1))
 (2756 50 (:REWRITE BUBBLE-DOWN-*-BUBBLE-DOWN))
 (2659 14 (:REWRITE |(* (if a b c) x)|))
 (2250 826 (:LINEAR SMAN::BYTEP-MI))
 (2224 558 (:REWRITE |(equal (/ x) c)|))
 (2137 279 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (1996 907 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (1969 1969 (:REWRITE |(< (* x y) 0)|))
 (1956 1956 (:META META-INTEGERP-CORRECT))
 (1900 1900 (:REWRITE |(< (/ x) 0)|))
 (1897 1897
       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1897 1897
       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1773 1773
       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (1450 264
       (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (1406 432 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (1382 65 (:LINEAR EXPT-X->=-X))
 (1382 65 (:LINEAR EXPT-X->-X))
 (1324 705
       (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (1238 788
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (1217 1217 (:REWRITE |(< 0 (* x y))|))
 (1184 320 (:REWRITE DEFAULT-DIVIDE))
 (1102 1102
       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (1102 1102
       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (1058 65 (:LINEAR EXPT-<=-1-TWO))
 (941 941 (:TYPE-PRESCRIPTION ABS))
 (925 925 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (925 925
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (925 925
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (925 558 (:REWRITE |(equal (- x) (- y))|))
 (907 907
      (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (890 31 (:LINEAR MOD-BOUNDS-3))
 (878 851 (:REWRITE DEFAULT-FLOOR-2))
 (788 788
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (775 23 (:REWRITE FLOOR-=-X/Y . 4))
 (735 705
      (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (720 705
      (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (705 705 (:REWRITE |(floor x (- y))| . 2))
 (705 705 (:REWRITE |(floor x (- y))| . 1))
 (705 705 (:REWRITE |(floor (- x) y)| . 2))
 (705 705 (:REWRITE |(floor (- x) y)| . 1))
 (673 673 (:REWRITE DEFAULT-EXPT-2))
 (673 673 (:REWRITE DEFAULT-EXPT-1))
 (673 673 (:REWRITE |(expt 1/c n)|))
 (673 673 (:REWRITE |(expt (- x) n)|))
 (613 264
      (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (594 62 (:LINEAR MOD-BOUNDS-2))
 (579 159 (:REWRITE SMAN::!MI-MI))
 (565 558
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (561 561
      (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (558 558
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (558 558 (:REWRITE |(equal c (/ x))|))
 (558 558 (:REWRITE |(equal (/ x) (/ y))|))
 (548 314 (:REWRITE DEFAULT-MOD-2))
 (533 285
      (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (512 264
      (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (480 118 (:REWRITE SMAN::STP-!R))
 (439 439
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (439 439 (:REWRITE |(equal c (- x))|))
 (439 439 (:REWRITE |(equal (- x) c)|))
 (409 409
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (407 17 (:REWRITE |(mod x 1)|))
 (369 41 (:REWRITE FLOOR-POSITIVE . 2))
 (369 41 (:REWRITE FLOOR-NONPOSITIVE . 1))
 (344 4 (:REWRITE |(floor (+ x r) i)|))
 (303 303 (:REWRITE |(< x (+ c/d y))|))
 (288 106 (:REWRITE |(* c (* d x))|))
 (279 9 (:REWRITE |(floor x 1)|))
 (272 34 (:REWRITE SMAN::!MI-!MI-DIFF))
 (264 264 (:REWRITE |(mod x (- y))| . 3))
 (264 264 (:REWRITE |(mod x (- y))| . 2))
 (264 264 (:REWRITE |(mod x (- y))| . 1))
 (264 264
      (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (264 264 (:REWRITE |(mod (- x) y)| . 3))
 (264 264 (:REWRITE |(mod (- x) y)| . 2))
 (264 264 (:REWRITE |(mod (- x) y)| . 1))
 (262 110 (:REWRITE SMAN::STP-!MI))
 (245 245 (:REWRITE |(< y (+ (- c) x))|))
 (223 223 (:REWRITE |(/ (/ x))|))
 (208 208 (:REWRITE |(* a (/ a))|))
 (205 41 (:REWRITE FLOOR-POSITIVE . 4))
 (205 41 (:REWRITE FLOOR-POSITIVE . 3))
 (205 41 (:REWRITE FLOOR-NONPOSITIVE . 3))
 (205 41 (:REWRITE FLOOR-NONPOSITIVE . 2))
 (196 196 (:TYPE-PRESCRIPTION ASH))
 (136 136 (:REWRITE |(< (+ c/d x) y)|))
 (130 130
      (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (130 130
      (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (130 130
      (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (119 119 (:REWRITE |(not (equal x (/ y)))|))
 (119 119 (:REWRITE |(equal x (/ y))|))
 (117 13 (:REWRITE |(* (/ x) (expt x n))|))
 (115 23
      (:REWRITE |(equal (floor (+ x y) z) x)|))
 (105 105
      (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (105 105
      (:REWRITE |(< x (/ y)) with (< y 0)|))
 (97 97 (:REWRITE FOLD-CONSTS-IN-+))
 (93 93 (:REWRITE |(< (+ (- c) x) y)|))
 (66 66 (:LINEAR EXPT-LINEAR-LOWER-<))
 (65 65 (:LINEAR EXPT-LINEAR-UPPER-<))
 (65 65 (:LINEAR EXPT->=-1-TWO))
 (65 65 (:LINEAR EXPT->-1-TWO))
 (65 65 (:LINEAR EXPT-<=-1-ONE))
 (65 65 (:LINEAR EXPT-<-1-TWO))
 (65 65 (:LINEAR EXPT-<-1-ONE))
 (50 50 (:REWRITE BUBBLE-DOWN-*-MATCH-3))
 (50 5
     (:REWRITE |(equal (mod (+ x y) z) x)|))
 (41 41 (:REWRITE FLOOR-POSITIVE . 1))
 (33 33 (:REWRITE |(equal (* x y) 0)|))
 (28 1 (:REWRITE |(* x (expt x n))|))
 (24 4 (:REWRITE |(- (+ x y))|))
 (23 23 (:REWRITE |(equal (+ (- c) x) y)|))
 (21 21 (:REWRITE FLOOR-ZERO . 1))
 (21 21 (:REWRITE |(mod (floor x y) z)| . 5))
 (21 21 (:REWRITE |(mod (floor x y) z)| . 4))
 (21 21 (:REWRITE |(mod (floor x y) z)| . 3))
 (21 21 (:REWRITE |(mod (floor x y) z)| . 2))
 (20 20
     (:REWRITE |(floor (floor x y) z)| . 5))
 (20 20
     (:REWRITE |(floor (floor x y) z)| . 4))
 (20 20
     (:REWRITE |(floor (floor x y) z)| . 3))
 (20 20
     (:REWRITE |(floor (floor x y) z)| . 2))
 (13 13
     (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (10 10 (:TYPE-PRESCRIPTION RATIONALP-MOD))
 (8 8
    (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
 (8 8
    (:REWRITE |(< (* (/ x) y) 1) with (< 0 x)|))
 (4 4
    (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 3))
 (4 4
    (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 2))
 (4 4
    (:REWRITE |(floor (+ x y) z) where (< 0 z)| . 3))
 (4 4
    (:REWRITE |(floor (+ x y) z) where (< 0 z)| . 2))
 (1 1
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (1 1 (:REWRITE |(- (- x))|)))
(SMAN::R-!R-DIFF-BELOW
 (4464 6 (:DEFINITION SMAN::!R))
 (2302 213 (:REWRITE DEFAULT-PLUS-1))
 (2226 42 (:REWRITE CANCEL-MOD-+))
 (2106 54 (:REWRITE DEFAULT-LOGAND-1))
 (2010 6 (:REWRITE |(logand y x)|))
 (1660 20 (:REWRITE SMAN::MI-!R-))
 (1615 42 (:REWRITE MOD-X-Y-=-X . 4))
 (1615 42 (:REWRITE MOD-X-Y-=-X . 3))
 (1573 42 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (1486 42 (:REWRITE SMAN::UNNECESSARY-MOD))
 (1447 42 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (1437 333 (:REWRITE INTEGERP-MINUS-X))
 (1034 1034
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (1034 1034
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (1034 1034
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (1034 1034
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (973 42 (:REWRITE MOD-ZERO . 4))
 (924 42 (:REWRITE MOD-ZERO . 3))
 (900 42 (:REWRITE SMAN::UNNECESSARY-FLOOR))
 (892 440 (:TYPE-PRESCRIPTION SMAN::NATP-MI))
 (816 96 (:REWRITE |(* (- x) y)|))
 (742 742 (:TYPE-PRESCRIPTION SMAN::STP))
 (672 600 (:REWRITE DEFAULT-TIMES-2))
 (672 600 (:REWRITE DEFAULT-TIMES-1))
 (543 252 (:LINEAR SMAN::BYTEP-MI))
 (480 96 (:REWRITE DEFAULT-MINUS))
 (474 474
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (474 474
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (474 474
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (474 474
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (462 42 (:REWRITE DEFAULT-MOD-RATIO))
 (450 329
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (432 96 (:REWRITE |(- (* c x))|))
 (426 42 (:REWRITE DEFAULT-FLOOR-RATIO))
 (405 45 (:REWRITE ACL2-NUMBERP-X))
 (400 80 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (400 80 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (400 80
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (400 80
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (384 6 (:REWRITE FLOOR-ZERO . 3))
 (374 350 (:REWRITE DEFAULT-LESS-THAN-1))
 (350 350 (:REWRITE THE-FLOOR-BELOW))
 (350 350 (:REWRITE THE-FLOOR-ABOVE))
 (350 350 (:REWRITE DEFAULT-LESS-THAN-2))
 (349 325
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (335 329
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (335 329
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (325 325 (:REWRITE SIMPLIFY-SUMS-<))
 (325 325
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (325 325
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (325 325 (:REWRITE INTEGERP-<-CONSTANT))
 (325 325 (:REWRITE CONSTANT-<-INTEGERP))
 (325 325
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (325 325
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (325 325
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (325 325
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (325 325 (:REWRITE |(< c (- x))|))
 (325 325
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (325 325
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (325 325
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (325 325
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (325 325 (:REWRITE |(< (/ x) (/ y))|))
 (325 325 (:REWRITE |(< (- x) c)|))
 (325 325 (:REWRITE |(< (- x) (- y))|))
 (324 324
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (318 6 (:REWRITE CANCEL-FLOOR-+))
 (285 285 (:REWRITE REDUCE-INTEGERP-+))
 (285 285 (:META META-INTEGERP-CORRECT))
 (261 261 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (210 42 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (210 42 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (210 42 (:REWRITE MOD-X-Y-=-X . 2))
 (210 42
      (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (210 42 (:REWRITE MOD-CANCEL-*-CONST))
 (210 42 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (210 42
      (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (210 42
      (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (210 6 (:REWRITE FLOOR-ZERO . 5))
 (210 6 (:REWRITE FLOOR-ZERO . 4))
 (204 6 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (186 6 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (180 45 (:REWRITE RATIONALP-X))
 (166 166
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (166 166
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (166 166 (:REWRITE |(< (/ x) 0)|))
 (166 166 (:REWRITE |(< (* x y) 0)|))
 (144 5 (:LINEAR EXPT-X->=-X))
 (144 5 (:LINEAR EXPT-X->-X))
 (133 133
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (133 133 (:REWRITE NORMALIZE-ADDENDS))
 (132 6 (:REWRITE FLOOR-=-X/Y . 2))
 (123
  123
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (123 123
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (123
     123
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (123 123
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (123 123
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (106 5 (:LINEAR EXPT-<=-1-TWO))
 (80 80 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
 (80 80 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (80 80
     (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (80 80 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (80 80
     (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (80 80 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (78 42 (:REWRITE DEFAULT-FLOOR-1))
 (63 5 (:LINEAR EXPT-<-1-TWO))
 (54 54 (:REWRITE DEFAULT-EXPT-1))
 (54 54 (:REWRITE |(expt 1/c n)|))
 (54 54 (:REWRITE |(expt (- x) n)|))
 (54 54 (:REWRITE |(< 0 (* x y))|))
 (54 46 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (54 46
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (54 46
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (52 52
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (52 52
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (52 52 (:REWRITE |(< 0 (/ x))|))
 (46 46
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (46 46
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (46 46
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (46 46 (:REWRITE |(equal c (/ x))|))
 (46 46 (:REWRITE |(equal c (- x))|))
 (46 46 (:REWRITE |(equal (/ x) c)|))
 (46 46 (:REWRITE |(equal (/ x) (/ y))|))
 (46 46 (:REWRITE |(equal (- x) c)|))
 (46 46 (:REWRITE |(equal (- x) (- y))|))
 (45 45 (:REWRITE REDUCE-RATIONALP-+))
 (45 45 (:REWRITE REDUCE-RATIONALP-*))
 (45 45 (:REWRITE RATIONALP-MINUS-X))
 (45 45 (:META META-RATIONALP-CORRECT))
 (42 42
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (42 42
     (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (42 42 (:REWRITE DEFAULT-MOD-2))
 (42 42 (:REWRITE DEFAULT-MOD-1))
 (42 42 (:REWRITE DEFAULT-FLOOR-2))
 (42 42 (:REWRITE |(mod x (- y))| . 3))
 (42 42 (:REWRITE |(mod x (- y))| . 2))
 (42 42 (:REWRITE |(mod x (- y))| . 1))
 (42 42
     (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (42 42
     (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (42 42 (:REWRITE |(mod (- x) y)| . 3))
 (42 42 (:REWRITE |(mod (- x) y)| . 2))
 (42 42 (:REWRITE |(mod (- x) y)| . 1))
 (42 42
     (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (38 38 (:REWRITE ZP-OPEN))
 (30 6 (:REWRITE FLOOR-ZERO . 2))
 (30 6 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (30 6 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (30 6
     (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (30 6 (:REWRITE FLOOR-CANCEL-*-CONST))
 (30 6
     (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (29 29 (:REWRITE |(< x (+ c/d y))|))
 (25 25 (:REWRITE |(< y (+ (- c) x))|))
 (18 6 (:REWRITE SMAN::!MI-MI))
 (16 4 (:REWRITE |(+ c (+ d x))|))
 (12 12 (:TYPE-PRESCRIPTION ABS))
 (12 12 (:TYPE-PRESCRIPTION SMAN::!R))
 (10 10
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (10 10
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (10 10
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (10 10
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (6 6
    (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (6 6 (:REWRITE |(floor x (- y))| . 2))
 (6 6 (:REWRITE |(floor x (- y))| . 1))
 (6 6
    (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (6 6
    (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (6 6 (:REWRITE |(floor (- x) y)| . 2))
 (6 6 (:REWRITE |(floor (- x) y)| . 1))
 (6 6
    (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (6 6
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (5 5 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (5 5 (:LINEAR EXPT-LINEAR-UPPER-<))
 (5 5 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (5 5 (:LINEAR EXPT-LINEAR-LOWER-<))
 (5 5 (:LINEAR EXPT->=-1-TWO))
 (5 5 (:LINEAR EXPT->-1-TWO))
 (5 5 (:LINEAR EXPT-<=-1-ONE))
 (5 5 (:LINEAR EXPT-<-1-ONE))
 (3 1 (:REWRITE SMAN::STP-!R)))
(SMAN::R-!R-DIFF-ABOVE
 (2430 226 (:REWRITE DEFAULT-PLUS-1))
 (2279 43 (:REWRITE CANCEL-MOD-+))
 (1825 25 (:REWRITE SMAN::R-!R-DIFF-BELOW))
 (1763 53 (:REWRITE DEFAULT-LOGAND-1))
 (1675 5 (:REWRITE |(logand y x)|))
 (1657 43 (:REWRITE MOD-X-Y-=-X . 4))
 (1657 43 (:REWRITE MOD-X-Y-=-X . 3))
 (1614 43 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (1523 43 (:REWRITE SMAN::UNNECESSARY-MOD))
 (1485 43 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (1461 357 (:REWRITE INTEGERP-MINUS-X))
 (1051 1051
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (1051 1051
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (1051 1051
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (1051 1051
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (1002 43 (:REWRITE MOD-ZERO . 4))
 (946 43 (:REWRITE MOD-ZERO . 3))
 (928 464 (:TYPE-PRESCRIPTION SMAN::NATP-MI))
 (915 43 (:REWRITE SMAN::UNNECESSARY-FLOOR))
 (816 96 (:REWRITE |(* (- x) y)|))
 (778 778 (:TYPE-PRESCRIPTION SMAN::STP))
 (719 365 (:REWRITE DEFAULT-LESS-THAN-2))
 (680 604 (:REWRITE DEFAULT-TIMES-2))
 (680 604 (:REWRITE DEFAULT-TIMES-1))
 (630 70 (:REWRITE ACL2-NUMBERP-X))
 (570 266 (:LINEAR SMAN::BYTEP-MI))
 (563 357 (:REWRITE DEFAULT-LESS-THAN-1))
 (480 96 (:REWRITE DEFAULT-MINUS))
 (473 43 (:REWRITE DEFAULT-MOD-RATIO))
 (467 467
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (467 467
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (467 467
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (467 467
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (453 332
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (435 43 (:REWRITE DEFAULT-FLOOR-RATIO))
 (432 96 (:REWRITE |(- (* c x))|))
 (420 84 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (420 84 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (420 84
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (420 84
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (365 365 (:REWRITE THE-FLOOR-BELOW))
 (365 365 (:REWRITE THE-FLOOR-ABOVE))
 (348 328
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (337 332
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (337 332
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (328 328 (:REWRITE SIMPLIFY-SUMS-<))
 (328 328
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (328 328
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (328 328 (:REWRITE INTEGERP-<-CONSTANT))
 (328 328 (:REWRITE CONSTANT-<-INTEGERP))
 (328 328
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (328 328
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (328 328
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (328 328
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (328 328 (:REWRITE |(< c (- x))|))
 (328 328
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (328 328
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (328 328
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (328 328
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (328 328 (:REWRITE |(< (/ x) (/ y))|))
 (328 328 (:REWRITE |(< (- x) c)|))
 (328 328 (:REWRITE |(< (- x) (- y))|))
 (326 326
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (320 5 (:REWRITE FLOOR-ZERO . 3))
 (309 309 (:REWRITE REDUCE-INTEGERP-+))
 (309 309 (:META META-INTEGERP-CORRECT))
 (280 70 (:REWRITE RATIONALP-X))
 (265 265 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (265 5 (:REWRITE CANCEL-FLOOR-+))
 (215 43 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (215 43 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (215 43 (:REWRITE MOD-X-Y-=-X . 2))
 (215 43
      (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (215 43 (:REWRITE MOD-CANCEL-*-CONST))
 (215 43 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (215 43
      (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (215 43
      (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (186 5 (:LINEAR EXPT-X->=-X))
 (186 5 (:LINEAR EXPT-X->-X))
 (175 5 (:REWRITE FLOOR-ZERO . 5))
 (175 5 (:REWRITE FLOOR-ZERO . 4))
 (170 5 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (165 165
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (165 165
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (165 165 (:REWRITE |(< (/ x) 0)|))
 (165 165 (:REWRITE |(< (* x y) 0)|))
 (155 5 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (148 5 (:LINEAR EXPT-<=-1-TWO))
 (142 142
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (142 142 (:REWRITE NORMALIZE-ADDENDS))
 (126
  126
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (126 126
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (126
     126
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (126 126
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (126 126
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (110 5 (:REWRITE FLOOR-=-X/Y . 2))
 (107 5 (:LINEAR EXPT-<-1-TWO))
 (84 84 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
 (84 84 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (84 84
     (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (84 84 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (84 84
     (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (84 84 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (81 43 (:REWRITE DEFAULT-FLOOR-1))
 (70 70 (:REWRITE REDUCE-RATIONALP-+))
 (70 70 (:REWRITE REDUCE-RATIONALP-*))
 (70 70 (:REWRITE RATIONALP-MINUS-X))
 (70 70 (:META META-RATIONALP-CORRECT))
 (56 56 (:REWRITE DEFAULT-EXPT-1))
 (56 56 (:REWRITE |(expt 1/c n)|))
 (56 56 (:REWRITE |(expt (- x) n)|))
 (55 47 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (55 47
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (55 47
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (54 54 (:REWRITE |(< 0 (* x y))|))
 (52 52
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (52 52
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (52 52 (:REWRITE |(< 0 (/ x))|))
 (47 47
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (47 47
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (47 47
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (47 47 (:REWRITE |(equal c (/ x))|))
 (47 47 (:REWRITE |(equal c (- x))|))
 (47 47 (:REWRITE |(equal (/ x) c)|))
 (47 47 (:REWRITE |(equal (/ x) (/ y))|))
 (47 47 (:REWRITE |(equal (- x) c)|))
 (47 47 (:REWRITE |(equal (- x) (- y))|))
 (43 43
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (43 43
     (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (43 43 (:REWRITE DEFAULT-MOD-2))
 (43 43 (:REWRITE DEFAULT-MOD-1))
 (43 43 (:REWRITE DEFAULT-FLOOR-2))
 (43 43 (:REWRITE |(mod x (- y))| . 3))
 (43 43 (:REWRITE |(mod x (- y))| . 2))
 (43 43 (:REWRITE |(mod x (- y))| . 1))
 (43 43
     (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (43 43
     (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (43 43 (:REWRITE |(mod (- x) y)| . 3))
 (43 43 (:REWRITE |(mod (- x) y)| . 2))
 (43 43 (:REWRITE |(mod (- x) y)| . 1))
 (43 43
     (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (39 39 (:REWRITE ZP-OPEN))
 (34 34 (:REWRITE |(< x (+ c/d y))|))
 (30 30 (:REWRITE |(< y (+ (- c) x))|))
 (25 5 (:REWRITE FLOOR-ZERO . 2))
 (25 5 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (25 5 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (25 5
     (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (25 5 (:REWRITE FLOOR-CANCEL-*-CONST))
 (25 5
     (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (16 4 (:REWRITE |(+ c (+ d x))|))
 (15 5 (:REWRITE SMAN::!MI-MI))
 (10 10 (:TYPE-PRESCRIPTION ABS))
 (10 10
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (10 10
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (10 10
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (10 10
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (5 5
    (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (5 5 (:REWRITE |(floor x (- y))| . 2))
 (5 5 (:REWRITE |(floor x (- y))| . 1))
 (5 5
    (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (5 5
    (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (5 5 (:REWRITE |(floor (- x) y)| . 2))
 (5 5 (:REWRITE |(floor (- x) y)| . 1))
 (5 5
    (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (5 5
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (5 5 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (5 5 (:LINEAR EXPT-LINEAR-UPPER-<))
 (5 5 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (5 5 (:LINEAR EXPT-LINEAR-LOWER-<))
 (5 5 (:LINEAR EXPT->=-1-TWO))
 (5 5 (:LINEAR EXPT->-1-TWO))
 (5 5 (:LINEAR EXPT-<=-1-ONE))
 (5 5 (:LINEAR EXPT-<-1-ONE)))
(SMAN::!R-!I
 (66304 160 (:LINEAR LINEAR-FLOOR-BOUNDS-1))
 (50374 37414
        (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (45386 512 (:REWRITE THE-FLOOR-ABOVE))
 (37414 37414
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (37414 37414
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (37414 37414
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (36658 2 (:REWRITE |(logand (if a b c) x)|))
 (32028 2 (:REWRITE |(floor (if a b c) x)|))
 (27070 180 (:REWRITE |(+ y x)|))
 (22210 198 (:REWRITE SMAN::UNNECESSARY-FLOOR))
 (18270 2918
        (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (17570 196 (:REWRITE CANCEL-FLOOR-+))
 (16808 482 (:REWRITE DEFAULT-PLUS-1))
 (15888 24 (:REWRITE SMAN::UNNECESSARY-MOD))
 (15630 180 (:REWRITE NORMALIZE-ADDENDS))
 (15364 196 (:REWRITE FLOOR-ZERO . 3))
 (15074 24 (:REWRITE MOD-ZERO . 4))
 (14648 196 (:REWRITE FLOOR-ZERO . 4))
 (14638 196 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (14596 196 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (14436 1604
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (14436 1604
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (14436 1604
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (14436 1604
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (14436 1604
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (13594 24 (:REWRITE MOD-X-Y-=-X . 3))
 (12966 24 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (12918 24 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (12722 196 (:REWRITE FLOOR-ZERO . 5))
 (11715 655 (:REWRITE INTEGERP-MINUS-X))
 (11668 24 (:REWRITE MOD-X-Y-=-X . 4))
 (11632 2722 (:REWRITE DEFAULT-TIMES-2))
 (9186 2722 (:REWRITE DEFAULT-TIMES-1))
 (9150 24 (:REWRITE CANCEL-MOD-+))
 (9106 1014 (:REWRITE |(* y x)|))
 (8726 6 (:REWRITE |(mod (floor x y) z)| . 1))
 (8570 446 (:REWRITE |(* (- x) y)|))
 (8020 1604
       (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
 (8020 1604
       (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (8020 1604
       (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (8020 1604
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (8020 1604
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (8020 1604
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (8020 1604
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (8020 1604
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (8020 1604
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
 (8020 1604
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (8020 1604
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (5674 196 (:REWRITE FLOOR-=-X/Y . 2))
 (5212 446 (:REWRITE DEFAULT-MINUS))
 (5100 50 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (5100 50 (:DEFINITION FIX))
 (5040 446 (:REWRITE |(- (* c x))|))
 (4906 196 (:REWRITE FLOOR-=-X/Y . 3))
 (4786 198 (:REWRITE DEFAULT-FLOOR-RATIO))
 (4726 2 (:REWRITE |(< (if a b c) x)|))
 (3516 24 (:REWRITE MOD-ZERO . 3))
 (2984 512 (:REWRITE THE-FLOOR-BELOW))
 (2918 2918
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (2918 2918
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (2918 2918
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (2616 446
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (2082 24 (:REWRITE DEFAULT-MOD-RATIO))
 (1678 462 (:REWRITE DEFAULT-LESS-THAN-1))
 (1674 462 (:REWRITE DEFAULT-LESS-THAN-2))
 (1604 1604 (:TYPE-PRESCRIPTION FLOOR))
 (1586 196 (:REWRITE FLOOR-ZERO . 2))
 (1586 196 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (1586 196 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (1546 196 (:REWRITE FLOOR-CANCEL-*-CONST))
 (1472 1472
       (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (1332 24 (:REWRITE MOD-X-Y-=-X . 2))
 (1332 24 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (1332 24
       (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (1194 6
       (:REWRITE |(floor (floor x y) z)| . 1))
 (1128 460
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (1006 198 (:REWRITE DEFAULT-FLOOR-1))
 (958 80 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (946 196
      (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (836 196
      (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (830 190
      (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (726 24 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (726 24 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (726 24
      (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (718 24 (:REWRITE MOD-CANCEL-*-CONST))
 (656 50 (:REWRITE DEFAULT-LOGAND-2))
 (640 26
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (640 26
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (638 80 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (630 24 (:REWRITE DEFAULT-MOD-1))
 (540 446
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (494 446
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (446 446 (:REWRITE SIMPLIFY-SUMS-<))
 (446 446
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (446 446
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (446 446 (:REWRITE INTEGERP-<-CONSTANT))
 (446 446 (:REWRITE CONSTANT-<-INTEGERP))
 (446 446
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (446 446
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (446 446
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (446 446
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (446 446 (:REWRITE |(< c (- x))|))
 (446 446
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (446 446
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (446 446
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (446 446
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (446 446 (:REWRITE |(< (/ x) (/ y))|))
 (446 446 (:REWRITE |(< (- x) c)|))
 (446 446 (:REWRITE |(< (- x) (- y))|))
 (435 435 (:REWRITE REDUCE-INTEGERP-+))
 (435 435 (:META META-INTEGERP-CORRECT))
 (418 2 (:REWRITE |(* (if a b c) x)|))
 (372 372 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (350 20 (:REWRITE ZP-OPEN))
 (310 190
      (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (296 296 (:REWRITE |(< (* x y) 0)|))
 (282 282
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (282 282
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (282 282 (:REWRITE |(< (/ x) 0)|))
 (254 54 (:REWRITE |(+ 0 x)|))
 (202 202 (:TYPE-PRESCRIPTION ABS))
 (198 198 (:REWRITE DEFAULT-FLOOR-2))
 (190 190 (:REWRITE |(floor x (- y))| . 2))
 (190 190 (:REWRITE |(floor x (- y))| . 1))
 (190 190
      (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (190 190
      (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (190 190 (:REWRITE |(floor (- x) y)| . 2))
 (190 190 (:REWRITE |(floor (- x) y)| . 1))
 (172 172 (:TYPE-PRESCRIPTION SMAN::STP))
 (159 35 (:REWRITE SMAN::!MI-MI))
 (152 26 (:REWRITE SMAN::!I-I))
 (130 130
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (128 16 (:REWRITE ACL2-NUMBERP-X))
 (108 12 (:REWRITE FLOOR-POSITIVE . 2))
 (108 12 (:REWRITE FLOOR-NONPOSITIVE . 1))
 (100 50 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
 (96 96
     (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (90 18
     (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (84 84
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (84 84
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (84 84 (:REWRITE |(< 0 (/ x))|))
 (84 84 (:REWRITE |(< 0 (* x y))|))
 (82 34 (:REWRITE SMAN::STP-!MI))
 (80 16 (:REWRITE |(+ c (+ d x))|))
 (60 12 (:REWRITE FLOOR-POSITIVE . 4))
 (60 12 (:REWRITE FLOOR-POSITIVE . 3))
 (60 12 (:REWRITE FLOOR-NONPOSITIVE . 3))
 (60 12 (:REWRITE FLOOR-NONPOSITIVE . 2))
 (56 14 (:REWRITE RATIONALP-X))
 (50 50 (:REWRITE |(+ x (- x))|))
 (40 6 (:REWRITE SMAN::!MI-!MI-DIFF))
 (36 9 (:REWRITE SMAN::STP-!I))
 (34 26 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (32 8 (:REWRITE SMAN::STP-!R))
 (30 6 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (30 6 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (30 6 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (30 6 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (30 6 (:REWRITE FLOOR-=-X/Y . 4))
 (30 6
     (:REWRITE |(equal (floor (+ x y) z) x)|))
 (28 4 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
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
 (24 24
     (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (24 24 (:REWRITE DEFAULT-MOD-2))
 (22 22
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (20 8 (:REWRITE DEFAULT-CDR))
 (20 8 (:REWRITE DEFAULT-CAR))
 (18
   18
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (18
  18
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (18 18
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (18 18
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (18 18
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (18 18
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (18 18 (:REWRITE |(mod x (- y))| . 3))
 (18 18 (:REWRITE |(mod x (- y))| . 2))
 (18 18 (:REWRITE |(mod x (- y))| . 1))
 (18 18
     (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (18 18
     (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (18 18 (:REWRITE |(mod (- x) y)| . 3))
 (18 18 (:REWRITE |(mod (- x) y)| . 2))
 (18 18 (:REWRITE |(mod (- x) y)| . 1))
 (18 18
     (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (16 2 (:REWRITE |(+ x (if a b c))|))
 (14 14 (:REWRITE REDUCE-RATIONALP-+))
 (14 14 (:REWRITE REDUCE-RATIONALP-*))
 (14 14 (:REWRITE RATIONALP-MINUS-X))
 (14 14 (:REWRITE |(* a (/ a) b)|))
 (14 14 (:META META-RATIONALP-CORRECT))
 (12 12 (:REWRITE FLOOR-POSITIVE . 1))
 (10 10 (:REWRITE |(< y (+ (- c) x))|))
 (10 10 (:REWRITE |(< x (+ c/d y))|))
 (6 6 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
 (6 6 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (6 6 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (6 6 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (6 6 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
 (6 6 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (6 6 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (6 6 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
 (6 6 (:REWRITE FLOOR-ZERO . 1))
 (6 6 (:REWRITE |(mod (floor x y) z)| . 5))
 (6 6 (:REWRITE |(mod (floor x y) z)| . 4))
 (6 6 (:REWRITE |(mod (floor x y) z)| . 3))
 (6 6 (:REWRITE |(mod (floor x y) z)| . 2))
 (6 6
    (:REWRITE |(floor (floor x y) z)| . 5))
 (6 6
    (:REWRITE |(floor (floor x y) z)| . 4))
 (6 6
    (:REWRITE |(floor (floor x y) z)| . 3))
 (6 6
    (:REWRITE |(floor (floor x y) z)| . 2)))
(SMAN::!R-!S
 (66304 160 (:LINEAR LINEAR-FLOOR-BOUNDS-1))
 (50374 37414
        (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (45386 512 (:REWRITE THE-FLOOR-ABOVE))
 (37414 37414
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (37414 37414
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (37414 37414
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (36658 2 (:REWRITE |(logand (if a b c) x)|))
 (32028 2 (:REWRITE |(floor (if a b c) x)|))
 (27070 180 (:REWRITE |(+ y x)|))
 (22210 198 (:REWRITE SMAN::UNNECESSARY-FLOOR))
 (18270 2918
        (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (17570 196 (:REWRITE CANCEL-FLOOR-+))
 (16808 482 (:REWRITE DEFAULT-PLUS-1))
 (15888 24 (:REWRITE SMAN::UNNECESSARY-MOD))
 (15630 180 (:REWRITE NORMALIZE-ADDENDS))
 (15364 196 (:REWRITE FLOOR-ZERO . 3))
 (15074 24 (:REWRITE MOD-ZERO . 4))
 (14648 196 (:REWRITE FLOOR-ZERO . 4))
 (14638 196 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (14596 196 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (14436 1604
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (14436 1604
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (14436 1604
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (14436 1604
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (14436 1604
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (13594 24 (:REWRITE MOD-X-Y-=-X . 3))
 (12966 24 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (12918 24 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (12722 196 (:REWRITE FLOOR-ZERO . 5))
 (11706 646 (:REWRITE INTEGERP-MINUS-X))
 (11668 24 (:REWRITE MOD-X-Y-=-X . 4))
 (11632 2722 (:REWRITE DEFAULT-TIMES-2))
 (9186 2722 (:REWRITE DEFAULT-TIMES-1))
 (9150 24 (:REWRITE CANCEL-MOD-+))
 (9106 1014 (:REWRITE |(* y x)|))
 (8726 6 (:REWRITE |(mod (floor x y) z)| . 1))
 (8570 446 (:REWRITE |(* (- x) y)|))
 (8020 1604
       (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
 (8020 1604
       (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (8020 1604
       (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (8020 1604
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (8020 1604
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (8020 1604
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (8020 1604
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (8020 1604
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (8020 1604
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
 (8020 1604
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (8020 1604
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (5674 196 (:REWRITE FLOOR-=-X/Y . 2))
 (5212 446 (:REWRITE DEFAULT-MINUS))
 (5100 50 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (5100 50 (:DEFINITION FIX))
 (5040 446 (:REWRITE |(- (* c x))|))
 (4906 196 (:REWRITE FLOOR-=-X/Y . 3))
 (4786 198 (:REWRITE DEFAULT-FLOOR-RATIO))
 (4726 2 (:REWRITE |(< (if a b c) x)|))
 (3516 24 (:REWRITE MOD-ZERO . 3))
 (2984 512 (:REWRITE THE-FLOOR-BELOW))
 (2918 2918
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (2918 2918
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (2918 2918
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (2616 446
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (2082 24 (:REWRITE DEFAULT-MOD-RATIO))
 (1678 462 (:REWRITE DEFAULT-LESS-THAN-1))
 (1674 462 (:REWRITE DEFAULT-LESS-THAN-2))
 (1604 1604 (:TYPE-PRESCRIPTION FLOOR))
 (1586 196 (:REWRITE FLOOR-ZERO . 2))
 (1586 196 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (1586 196 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (1546 196 (:REWRITE FLOOR-CANCEL-*-CONST))
 (1472 1472
       (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (1332 24 (:REWRITE MOD-X-Y-=-X . 2))
 (1332 24 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (1332 24
       (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (1194 6
       (:REWRITE |(floor (floor x y) z)| . 1))
 (1128 460
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (1006 198 (:REWRITE DEFAULT-FLOOR-1))
 (958 80 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (946 196
      (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (836 196
      (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (830 190
      (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (726 24 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (726 24 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (726 24
      (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (718 24 (:REWRITE MOD-CANCEL-*-CONST))
 (656 50 (:REWRITE DEFAULT-LOGAND-2))
 (640 26
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (640 26
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (638 80 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (630 24 (:REWRITE DEFAULT-MOD-1))
 (540 446
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (494 446
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (446 446 (:REWRITE SIMPLIFY-SUMS-<))
 (446 446
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (446 446
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (446 446 (:REWRITE INTEGERP-<-CONSTANT))
 (446 446 (:REWRITE CONSTANT-<-INTEGERP))
 (446 446
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (446 446
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (446 446
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (446 446
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (446 446 (:REWRITE |(< c (- x))|))
 (446 446
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (446 446
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (446 446
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (446 446
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (446 446 (:REWRITE |(< (/ x) (/ y))|))
 (446 446 (:REWRITE |(< (- x) c)|))
 (446 446 (:REWRITE |(< (- x) (- y))|))
 (426 426 (:REWRITE REDUCE-INTEGERP-+))
 (426 426 (:META META-INTEGERP-CORRECT))
 (418 2 (:REWRITE |(* (if a b c) x)|))
 (372 372 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (350 20 (:REWRITE ZP-OPEN))
 (310 190
      (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (296 296 (:REWRITE |(< (* x y) 0)|))
 (282 282
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (282 282
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (282 282 (:REWRITE |(< (/ x) 0)|))
 (254 54 (:REWRITE |(+ 0 x)|))
 (202 202 (:TYPE-PRESCRIPTION ABS))
 (198 198 (:REWRITE DEFAULT-FLOOR-2))
 (190 190 (:TYPE-PRESCRIPTION SMAN::STP))
 (190 190 (:REWRITE |(floor x (- y))| . 2))
 (190 190 (:REWRITE |(floor x (- y))| . 1))
 (190 190
      (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (190 190
      (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (190 190 (:REWRITE |(floor (- x) y)| . 2))
 (190 190 (:REWRITE |(floor (- x) y)| . 1))
 (155 35 (:REWRITE SMAN::!MI-MI))
 (152 26 (:REWRITE SMAN::!S-S))
 (130 130
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (128 16 (:REWRITE ACL2-NUMBERP-X))
 (108 12 (:REWRITE FLOOR-POSITIVE . 2))
 (108 12 (:REWRITE FLOOR-NONPOSITIVE . 1))
 (100 50 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
 (96 96
     (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (90 18
     (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (87 39 (:REWRITE SMAN::STP-!MI))
 (84 84
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (84 84
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (84 84 (:REWRITE |(< 0 (/ x))|))
 (84 84 (:REWRITE |(< 0 (* x y))|))
 (80 16 (:REWRITE |(+ c (+ d x))|))
 (60 12 (:REWRITE FLOOR-POSITIVE . 4))
 (60 12 (:REWRITE FLOOR-POSITIVE . 3))
 (60 12 (:REWRITE FLOOR-NONPOSITIVE . 3))
 (60 12 (:REWRITE FLOOR-NONPOSITIVE . 2))
 (56 14 (:REWRITE RATIONALP-X))
 (50 50 (:REWRITE |(+ x (- x))|))
 (42 9 (:REWRITE SMAN::STP-!S))
 (40 6 (:REWRITE SMAN::!MI-!MI-DIFF))
 (34 26 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (32 8 (:REWRITE SMAN::STP-!R))
 (30 6 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (30 6 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (30 6 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (30 6 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (30 6 (:REWRITE FLOOR-=-X/Y . 4))
 (30 6
     (:REWRITE |(equal (floor (+ x y) z) x)|))
 (28 4 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
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
 (24 24
     (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (24 24 (:REWRITE DEFAULT-MOD-2))
 (22 22
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (20 8 (:REWRITE DEFAULT-CDR))
 (20 8 (:REWRITE DEFAULT-CAR))
 (18
   18
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (18
  18
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (18 18
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (18 18
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (18 18
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (18 18
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (18 18 (:REWRITE |(mod x (- y))| . 3))
 (18 18 (:REWRITE |(mod x (- y))| . 2))
 (18 18 (:REWRITE |(mod x (- y))| . 1))
 (18 18
     (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (18 18
     (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (18 18 (:REWRITE |(mod (- x) y)| . 3))
 (18 18 (:REWRITE |(mod (- x) y)| . 2))
 (18 18 (:REWRITE |(mod (- x) y)| . 1))
 (18 18
     (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (16 2 (:REWRITE |(+ x (if a b c))|))
 (14 14 (:REWRITE REDUCE-RATIONALP-+))
 (14 14 (:REWRITE REDUCE-RATIONALP-*))
 (14 14 (:REWRITE RATIONALP-MINUS-X))
 (14 14 (:REWRITE |(* a (/ a) b)|))
 (14 14 (:META META-RATIONALP-CORRECT))
 (12 12 (:REWRITE FLOOR-POSITIVE . 1))
 (10 10 (:REWRITE |(< y (+ (- c) x))|))
 (10 10 (:REWRITE |(< x (+ c/d y))|))
 (6 6 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
 (6 6 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (6 6 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (6 6 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (6 6 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
 (6 6 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (6 6 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (6 6 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
 (6 6 (:REWRITE FLOOR-ZERO . 1))
 (6 6 (:REWRITE |(mod (floor x y) z)| . 5))
 (6 6 (:REWRITE |(mod (floor x y) z)| . 4))
 (6 6 (:REWRITE |(mod (floor x y) z)| . 3))
 (6 6 (:REWRITE |(mod (floor x y) z)| . 2))
 (6 6
    (:REWRITE |(floor (floor x y) z)| . 5))
 (6 6
    (:REWRITE |(floor (floor x y) z)| . 4))
 (6 6
    (:REWRITE |(floor (floor x y) z)| . 3))
 (6 6
    (:REWRITE |(floor (floor x y) z)| . 2)))
(SMAN::!R-!R-SAME-HINT (6 6
                          (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 3))
                       (6 6
                          (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 2))
                       (6 6
                          (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1)))
(SMAN::!R-!MI-BELOW
 (45006 108 (:LINEAR LINEAR-FLOOR-BOUNDS-1))
 (36658 2 (:REWRITE |(logand (if a b c) x)|))
 (34003 25363
        (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (32028 2 (:REWRITE |(floor (if a b c) x)|))
 (30914 396 (:REWRITE THE-FLOOR-ABOVE))
 (25363 25363
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (25363 25363
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (25363 25363
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (18404 122 (:REWRITE |(+ y x)|))
 (16814 136 (:REWRITE SMAN::UNNECESSARY-FLOOR))
 (12339 2037
        (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (11890 134 (:REWRITE CANCEL-FLOOR-+))
 (11422 330 (:REWRITE DEFAULT-PLUS-1))
 (11388 330 (:REWRITE DEFAULT-PLUS-2))
 (10664 18 (:REWRITE SMAN::UNNECESSARY-MOD))
 (10634 128 (:REWRITE NORMALIZE-ADDENDS))
 (10519 134 (:REWRITE FLOOR-ZERO . 3))
 (10091 18 (:REWRITE MOD-ZERO . 4))
 (9916 134 (:REWRITE FLOOR-ZERO . 4))
 (9892 134 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (9877 134 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (9774 1086
       (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (9774 1086
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (9774 1086
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (9774 1086
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (9774 1086
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (9144 18 (:REWRITE MOD-X-Y-=-X . 3))
 (8723 18 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (8684 18 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (8632 134 (:REWRITE FLOOR-ZERO . 5))
 (7957 461 (:REWRITE INTEGERP-MINUS-X))
 (7902 1892 (:REWRITE DEFAULT-TIMES-2))
 (7860 18 (:REWRITE MOD-X-Y-=-X . 4))
 (6336 1892 (:REWRITE DEFAULT-TIMES-1))
 (6258 706 (:REWRITE |(* y x)|))
 (6206 18 (:REWRITE CANCEL-MOD-+))
 (5820 4 (:REWRITE |(mod (floor x y) z)| . 1))
 (5804 308 (:REWRITE |(* (- x) y)|))
 (5430 1086
       (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
 (5430 1086
       (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (5430 1086
       (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (5430 1086
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (5430 1086
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (5430 1086
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (5430 1086
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (5430 1086
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (5430 1086
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
 (5430 1086
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (5430 1086
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (4726 2 (:REWRITE |(< (if a b c) x)|))
 (3877 134 (:REWRITE FLOOR-=-X/Y . 2))
 (3528 308 (:REWRITE DEFAULT-MINUS))
 (3506 136 (:REWRITE DEFAULT-FLOOR-RATIO))
 (3468 34 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (3468 34 (:DEFINITION FIX))
 (3408 308 (:REWRITE |(- (* c x))|))
 (3365 134 (:REWRITE FLOOR-=-X/Y . 3))
 (2395 18 (:REWRITE MOD-ZERO . 3))
 (2044 396 (:REWRITE THE-FLOOR-BELOW))
 (2037 2037
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (2037 2037
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (2037 2037
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (1813 349
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (1410 18 (:REWRITE DEFAULT-MOD-RATIO))
 (1260 362 (:REWRITE DEFAULT-LESS-THAN-1))
 (1170 362 (:REWRITE DEFAULT-LESS-THAN-2))
 (1086 1086 (:TYPE-PRESCRIPTION FLOOR))
 (1074 134 (:REWRITE FLOOR-ZERO . 2))
 (1074 134 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (1074 134 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (1054 134 (:REWRITE FLOOR-CANCEL-*-CONST))
 (1022 1022
       (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (976 4
      (:REWRITE |(floor (floor x y) z)| . 1))
 (898 18 (:REWRITE MOD-X-Y-=-X . 2))
 (898 18 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (898 18
      (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (837 360
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (742 136 (:REWRITE DEFAULT-FLOOR-1))
 (656 54 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (642 134
      (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (566 134
      (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (562 130
      (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (494 18 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (494 18 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (494 18
      (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (490 18 (:REWRITE MOD-CANCEL-*-CONST))
 (444 40 (:REWRITE DEFAULT-LOGAND-2))
 (440 54 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (433 21
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (433 21
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (422 18 (:REWRITE DEFAULT-MOD-1))
 (418 2 (:REWRITE |(* (if a b c) x)|))
 (417 350
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (381 349
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (350 350
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (350 350
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (350 350 (:REWRITE INTEGERP-<-CONSTANT))
 (350 350 (:REWRITE CONSTANT-<-INTEGERP))
 (350 350
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (350 350
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (350 350
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (350 350
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (350 350 (:REWRITE |(< c (- x))|))
 (350 350
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (350 350
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (350 350
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (350 350
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (350 350 (:REWRITE |(< (/ x) (/ y))|))
 (350 350 (:REWRITE |(< (- x) c)|))
 (350 350 (:REWRITE |(< (- x) (- y))|))
 (349 349 (:REWRITE SIMPLIFY-SUMS-<))
 (309 309 (:REWRITE REDUCE-INTEGERP-+))
 (309 309 (:META META-INTEGERP-CORRECT))
 (237 53 (:REWRITE SMAN::!MI-MI))
 (234 234 (:REWRITE |(< (* x y) 0)|))
 (224 224 (:REWRITE |(< (/ x) 0)|))
 (223 223
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (223 223
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (218 130
      (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (211 13 (:REWRITE ZP-OPEN))
 (170 34 (:REWRITE |(+ 0 x)|))
 (144 144 (:TYPE-PRESCRIPTION ABS))
 (142 142 (:TYPE-PRESCRIPTION SMAN::STP))
 (136 136 (:REWRITE DEFAULT-FLOOR-2))
 (130 130 (:REWRITE |(floor x (- y))| . 2))
 (130 130 (:REWRITE |(floor x (- y))| . 1))
 (130 130
      (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (130 130
      (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (130 130 (:REWRITE |(floor (- x) y)| . 2))
 (130 130 (:REWRITE |(floor (- x) y)| . 1))
 (94 94
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (74 36 (:REWRITE SMAN::STP-!MI))
 (72 8 (:REWRITE FLOOR-POSITIVE . 2))
 (72 8 (:REWRITE FLOOR-NONPOSITIVE . 1))
 (70 14
     (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (69 69
     (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (68 34 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
 (62 62
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (62 62
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (62 62 (:REWRITE |(< 0 (/ x))|))
 (62 62 (:REWRITE |(< 0 (* x y))|))
 (60 12 (:REWRITE |(+ c (+ d x))|))
 (40 8 (:REWRITE FLOOR-POSITIVE . 4))
 (40 8 (:REWRITE FLOOR-POSITIVE . 3))
 (40 8 (:REWRITE FLOOR-NONPOSITIVE . 3))
 (40 8 (:REWRITE FLOOR-NONPOSITIVE . 2))
 (34 34 (:REWRITE |(+ x (- x))|))
 (29 21 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (24 6 (:REWRITE SMAN::STP-!R))
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
 (20 8 (:REWRITE DEFAULT-CDR))
 (20 8 (:REWRITE DEFAULT-CAR))
 (20 4 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (20 4 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (20 4 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (20 4 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (20 4 (:REWRITE FLOOR-=-X/Y . 4))
 (20 4
     (:REWRITE |(equal (floor (+ x y) z) x)|))
 (18 18
     (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (18 18 (:REWRITE DEFAULT-MOD-2))
 (17 17
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (14
   14
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (14
  14
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (14 14
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (14 14
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (14 14
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (14 14
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (14 14 (:REWRITE |(mod x (- y))| . 3))
 (14 14 (:REWRITE |(mod x (- y))| . 2))
 (14 14 (:REWRITE |(mod x (- y))| . 1))
 (14 14
     (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (14 14
     (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (14 14 (:REWRITE |(mod (- x) y)| . 3))
 (14 14 (:REWRITE |(mod (- x) y)| . 2))
 (14 14 (:REWRITE |(mod (- x) y)| . 1))
 (14 14
     (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (10 10 (:REWRITE |(* a (/ a) b)|))
 (8 8 (:REWRITE FLOOR-POSITIVE . 1))
 (6 6 (:REWRITE |(< y (+ (- c) x))|))
 (6 6 (:REWRITE |(< x (+ c/d y))|))
 (4 4 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
 (4 4 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (4 4 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (4 4 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (4 4 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
 (4 4 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (4 4 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (4 4 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
 (4 4 (:REWRITE FLOOR-ZERO . 1))
 (4 4 (:REWRITE |(mod (floor x y) z)| . 5))
 (4 4 (:REWRITE |(mod (floor x y) z)| . 4))
 (4 4 (:REWRITE |(mod (floor x y) z)| . 3))
 (4 4 (:REWRITE |(mod (floor x y) z)| . 2))
 (4 4
    (:REWRITE |(floor (floor x y) z)| . 5))
 (4 4
    (:REWRITE |(floor (floor x y) z)| . 4))
 (4 4
    (:REWRITE |(floor (floor x y) z)| . 3))
 (4 4
    (:REWRITE |(floor (floor x y) z)| . 2)))
(SMAN::!R-!R-SAME
 (269840 656 (:LINEAR LINEAR-FLOOR-BOUNDS-1))
 (206024 152024
         (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (184109 1950 (:REWRITE THE-FLOOR-ABOVE))
 (152024 152024
         (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (152024 152024
         (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (152024 152024
         (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (109933 734 (:REWRITE |(+ y x)|))
 (76788 798 (:REWRITE SMAN::UNNECESSARY-FLOOR))
 (74988 11560
        (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (72060 795 (:REWRITE CANCEL-FLOOR-+))
 (68373 2012 (:REWRITE DEFAULT-PLUS-1))
 (68170 2012 (:REWRITE DEFAULT-PLUS-2))
 (65774 84 (:REWRITE SMAN::UNNECESSARY-MOD))
 (63513 786 (:REWRITE NORMALIZE-ADDENDS))
 (62441 795 (:REWRITE FLOOR-ZERO . 3))
 (61954 84 (:REWRITE MOD-ZERO . 4))
 (60230 795 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (60173 795 (:REWRITE FLOOR-ZERO . 4))
 (59981 795 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (58896 6544
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (58896 6544
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (58896 6544
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (58896 6544
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (58896 6544
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (56161 84 (:REWRITE MOD-X-Y-=-X . 3))
 (54987 3 (:REWRITE |(logand (if a b c) x)|))
 (53558 84 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (53399 84 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (52148 795 (:REWRITE FLOOR-ZERO . 5))
 (48136 84 (:REWRITE MOD-X-Y-=-X . 4))
 (48042 3 (:REWRITE |(floor (if a b c) x)|))
 (47583 2366 (:REWRITE INTEGERP-MINUS-X))
 (47449 10884 (:REWRITE DEFAULT-TIMES-2))
 (37277 84 (:REWRITE CANCEL-MOD-+))
 (36740 10884 (:REWRITE DEFAULT-TIMES-1))
 (36735 4058 (:REWRITE |(* y x)|))
 (36337 25 (:REWRITE |(mod (floor x y) z)| . 1))
 (35068 1783 (:REWRITE |(* (- x) y)|))
 (32720 6544
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
 (32720 6544
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (32720 6544
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (32720 6544
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (32720 6544
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (32720 6544
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (32720 6544
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (32720 6544
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (32720 6544
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
 (32720 6544
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (32720 6544
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (23102 795 (:REWRITE FLOOR-=-X/Y . 2))
 (21340 1783 (:REWRITE DEFAULT-MINUS))
 (20713 210 (:DEFINITION FIX))
 (20706 203 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (20661 1783 (:REWRITE |(- (* c x))|))
 (19902 795 (:REWRITE FLOOR-=-X/Y . 3))
 (17474 798 (:REWRITE DEFAULT-FLOOR-RATIO))
 (14347 84 (:REWRITE MOD-ZERO . 3))
 (12250 1950 (:REWRITE THE-FLOOR-BELOW))
 (11560 11560
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (11560 11560
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (11560 11560
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (10616 1673
        (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (8499 84 (:REWRITE DEFAULT-MOD-RATIO))
 (7089 3 (:REWRITE |(< (if a b c) x)|))
 (6797 1747 (:REWRITE DEFAULT-LESS-THAN-2))
 (6544 6544 (:TYPE-PRESCRIPTION FLOOR))
 (6500 795 (:REWRITE FLOOR-ZERO . 2))
 (6500 795 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (6500 795 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (6300 795 (:REWRITE FLOOR-CANCEL-*-CONST))
 (6155 1747 (:REWRITE DEFAULT-LESS-THAN-1))
 (5863 5863
       (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (5470 84 (:REWRITE MOD-X-Y-=-X . 2))
 (5470 84 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (5470 84
       (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (4284 1744
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (3876 795
       (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (3853 328 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (3626 798 (:REWRITE DEFAULT-FLOOR-1))
 (3535 25
       (:REWRITE |(floor (floor x y) z)| . 1))
 (3419 795
       (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (3394 770
       (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (2986 1680
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (2945 84 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (2945 84 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (2945 84
       (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (2921 84 (:REWRITE MOD-CANCEL-*-CONST))
 (2667 100
       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (2642 117 (:REWRITE DEFAULT-LOGAND-2))
 (2609 84 (:REWRITE DEFAULT-MOD-1))
 (2541 328 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (2141 100
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (2058 1691
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (1691 1691
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (1691 1691
       (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (1691 1691
       (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (1691 1691
       (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (1691 1691
       (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (1691 1691
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (1691 1691
       (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (1691 1691
       (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (1691 1691
       (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (1691 1691 (:REWRITE |(< (/ x) (/ y))|))
 (1691 1691 (:REWRITE |(< (- x) (- y))|))
 (1684 1684
       (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (1684 1684 (:REWRITE INTEGERP-<-CONSTANT))
 (1684 1684 (:REWRITE CONSTANT-<-INTEGERP))
 (1684 1684 (:REWRITE |(< c (- x))|))
 (1684 1684 (:REWRITE |(< (- x) c)|))
 (1673 1673 (:REWRITE SIMPLIFY-SUMS-<))
 (1487 1487 (:REWRITE REDUCE-INTEGERP-+))
 (1487 1487 (:META META-INTEGERP-CORRECT))
 (1470 51 (:REWRITE ZP-OPEN))
 (1226 770
       (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (1101 1101 (:REWRITE |(< (* x y) 0)|))
 (1048 1048 (:REWRITE |(< (/ x) 0)|))
 (1044 1044
       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1044 1044
       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1015 203 (:REWRITE |(+ 0 x)|))
 (798 798 (:REWRITE DEFAULT-FLOOR-2))
 (787 787 (:TYPE-PRESCRIPTION ABS))
 (770 770 (:REWRITE |(floor x (- y))| . 2))
 (770 770 (:REWRITE |(floor x (- y))| . 1))
 (770 770
      (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (770 770
      (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (770 770 (:REWRITE |(floor (- x) y)| . 2))
 (770 770 (:REWRITE |(floor (- x) y)| . 1))
 (627 3 (:REWRITE |(* (if a b c) x)|))
 (583 583
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (558 341 (:REWRITE |(< 0 (/ x))|))
 (533 129 (:REWRITE SMAN::!MI-MI))
 (450 50 (:REWRITE FLOOR-POSITIVE . 2))
 (450 50 (:REWRITE FLOOR-NONPOSITIVE . 1))
 (430 86 (:REWRITE |(+ c (+ d x))|))
 (406 203 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
 (370 370
      (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (341 341 (:REWRITE |(< 0 (* x y))|))
 (334 334
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (334 334
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (322 322 (:TYPE-PRESCRIPTION SMAN::STP))
 (295 59
      (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (250 50 (:REWRITE FLOOR-POSITIVE . 4))
 (250 50 (:REWRITE FLOOR-POSITIVE . 3))
 (250 50 (:REWRITE FLOOR-NONPOSITIVE . 3))
 (250 50 (:REWRITE FLOOR-NONPOSITIVE . 2))
 (210 7
      (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (210 7 (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (205 107 (:REWRITE |(equal (/ x) c)|))
 (203 203 (:REWRITE |(+ x (- x))|))
 (158 72 (:REWRITE SMAN::STP-!R))
 (142 100 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (125 25 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (125 25 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (125 25
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (125 25
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (125 25 (:REWRITE FLOOR-=-X/Y . 4))
 (125 25
      (:REWRITE |(equal (floor (+ x y) z) x)|))
 (107 107
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (107 107
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (107 107 (:REWRITE |(equal c (/ x))|))
 (107 107 (:REWRITE |(equal (/ x) (/ y))|))
 (107 107 (:REWRITE |(equal (- x) (- y))|))
 (100 100
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (100 100 (:REWRITE |(equal c (- x))|))
 (100 100 (:REWRITE |(equal (- x) c)|))
 (92 12 (:REWRITE ACL2-NUMBERP-X))
 (85 85
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (84 84
     (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (84 84 (:REWRITE DEFAULT-MOD-2))
 (59 59 (:REWRITE |(mod x (- y))| . 3))
 (59 59 (:REWRITE |(mod x (- y))| . 2))
 (59 59 (:REWRITE |(mod x (- y))| . 1))
 (59 59
     (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (59 59
     (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (59 59 (:REWRITE |(mod (- x) y)| . 3))
 (59 59 (:REWRITE |(mod (- x) y)| . 2))
 (59 59 (:REWRITE |(mod (- x) y)| . 1))
 (59 59
     (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (53 53 (:REWRITE |(* a (/ a) b)|))
 (50 50 (:REWRITE FLOOR-POSITIVE . 1))
 (47
   47
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
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
 (47 22 (:REWRITE DEFAULT-CDR))
 (47 22 (:REWRITE DEFAULT-CAR))
 (43 43 (:REWRITE |(< y (+ (- c) x))|))
 (43 43 (:REWRITE |(< x (+ c/d y))|))
 (40 10 (:REWRITE SMAN::STP-!MI))
 (40 4 (:REWRITE RATIONALP-X))
 (25 25 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
 (25 25 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (25 25
     (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (25 25 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (25 25 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
 (25 25
     (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (25 25 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (25 25 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
 (25 25 (:REWRITE FLOOR-ZERO . 1))
 (25 25 (:REWRITE |(mod (floor x y) z)| . 5))
 (25 25 (:REWRITE |(mod (floor x y) z)| . 4))
 (25 25 (:REWRITE |(mod (floor x y) z)| . 3))
 (25 25 (:REWRITE |(mod (floor x y) z)| . 2))
 (25 25
     (:REWRITE |(floor (floor x y) z)| . 5))
 (25 25
     (:REWRITE |(floor (floor x y) z)| . 4))
 (25 25
     (:REWRITE |(floor (floor x y) z)| . 3))
 (25 25
     (:REWRITE |(floor (floor x y) z)| . 2))
 (14 14 (:REWRITE DEFAULT-DIVIDE))
 (14 14 (:REWRITE |(/ (/ x))|))
 (14 14 (:REWRITE |(* a (/ a))|))
 (14 14 (:REWRITE |(* 0 x)|))
 (7 7 (:REWRITE |(not (equal x (/ y)))|))
 (7 7 (:REWRITE |(equal x (/ y))|))
 (7 7
    (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (7 7 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (4 4 (:REWRITE REDUCE-RATIONALP-+))
 (4 4 (:REWRITE REDUCE-RATIONALP-*))
 (4 4 (:REWRITE RATIONALP-MINUS-X))
 (4 4 (:META META-RATIONALP-CORRECT))
 (2 2 (:REWRITE |(< (+ c/d x) y)|))
 (2 2 (:REWRITE |(< (+ (- c) x) y)|)))
(SMAN::!R-!R-DIFF-BELOW
 (45006 108 (:LINEAR LINEAR-FLOOR-BOUNDS-1))
 (36658 2 (:REWRITE |(logand (if a b c) x)|))
 (34409 25769
        (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (32028 2 (:REWRITE |(floor (if a b c) x)|))
 (31072 554 (:REWRITE THE-FLOOR-ABOVE))
 (25769 25769
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (25769 25769
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (25769 25769
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (17248 150 (:REWRITE SMAN::UNNECESSARY-FLOOR))
 (12689 2387
        (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (12632 148 (:REWRITE CANCEL-FLOOR-+))
 (11455 363 (:REWRITE DEFAULT-PLUS-1))
 (11421 363 (:REWRITE DEFAULT-PLUS-2))
 (11415 148 (:REWRITE FLOOR-ZERO . 3))
 (11098 32 (:REWRITE SMAN::UNNECESSARY-MOD))
 (10665 159 (:REWRITE NORMALIZE-ADDENDS))
 (10406 148 (:REWRITE FLOOR-ZERO . 4))
 (10353 148 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (10343 32 (:REWRITE MOD-ZERO . 4))
 (10326 148 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (9774 1086
       (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (9774 1086
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (9774 1086
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (9774 1086
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (9774 1086
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (9634 32 (:REWRITE MOD-X-Y-=-X . 3))
 (9199 32 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (9122 148 (:REWRITE FLOOR-ZERO . 5))
 (9118 32 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (8761 621 (:REWRITE INTEGERP-MINUS-X))
 (8350 32 (:REWRITE MOD-X-Y-=-X . 4))
 (8210 2200 (:REWRITE DEFAULT-TIMES-2))
 (6948 32 (:REWRITE CANCEL-MOD-+))
 (6706 818 (:REWRITE |(* y x)|))
 (6644 2200 (:REWRITE DEFAULT-TIMES-1))
 (6280 364 (:REWRITE |(* (- x) y)|))
 (5820 4 (:REWRITE |(mod (floor x y) z)| . 1))
 (5430 1086
       (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
 (5430 1086
       (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (5430 1086
       (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (5430 1086
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (5430 1086
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (5430 1086
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (5430 1086
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (5430 1086
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (5430 1086
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
 (5430 1086
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (5430 1086
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (4726 2 (:REWRITE |(< (if a b c) x)|))
 (4185 148 (:REWRITE FLOOR-=-X/Y . 2))
 (3808 364 (:REWRITE DEFAULT-MINUS))
 (3673 148 (:REWRITE FLOOR-=-X/Y . 3))
 (3660 364 (:REWRITE |(- (* c x))|))
 (3660 150 (:REWRITE DEFAULT-FLOOR-RATIO))
 (3468 34 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (3468 34 (:DEFINITION FIX))
 (2703 32 (:REWRITE MOD-ZERO . 3))
 (2387 2387
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (2387 2387
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (2387 2387
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (2202 554 (:REWRITE THE-FLOOR-BELOW))
 (2027 507
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (1564 32 (:REWRITE DEFAULT-MOD-RATIO))
 (1474 520 (:REWRITE DEFAULT-LESS-THAN-1))
 (1328 520 (:REWRITE DEFAULT-LESS-THAN-2))
 (1190 1190
       (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (1144 148 (:REWRITE FLOOR-ZERO . 2))
 (1144 148 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (1144 148 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (1124 148 (:REWRITE FLOOR-CANCEL-*-CONST))
 (1086 1086 (:TYPE-PRESCRIPTION FLOOR))
 (1009 518
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (976 4
      (:REWRITE |(floor (floor x y) z)| . 1))
 (968 32 (:REWRITE MOD-X-Y-=-X . 2))
 (968 32 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (968 32
      (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (756 150 (:REWRITE DEFAULT-FLOOR-1))
 (712 148
      (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (656 54 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (589 508
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (580 148
      (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (576 144
      (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (564 32 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (564 32 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (564 32
      (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (560 32 (:REWRITE MOD-CANCEL-*-CONST))
 (539 507
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (508 508
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (508 508
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (508 508 (:REWRITE INTEGERP-<-CONSTANT))
 (508 508 (:REWRITE CONSTANT-<-INTEGERP))
 (508 508
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (508 508
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (508 508
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (508 508
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (508 508 (:REWRITE |(< c (- x))|))
 (508 508
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (508 508
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (508 508
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (508 508
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (508 508 (:REWRITE |(< (/ x) (/ y))|))
 (508 508 (:REWRITE |(< (- x) c)|))
 (508 508 (:REWRITE |(< (- x) (- y))|))
 (507 507 (:REWRITE SIMPLIFY-SUMS-<))
 (497 35
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (486 82 (:REWRITE DEFAULT-LOGAND-2))
 (457 35
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (441 441 (:REWRITE REDUCE-INTEGERP-+))
 (441 441 (:META META-INTEGERP-CORRECT))
 (440 54 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (436 32 (:REWRITE DEFAULT-MOD-1))
 (418 2 (:REWRITE |(* (if a b c) x)|))
 (336 336 (:REWRITE |(< (* x y) 0)|))
 (326 326 (:REWRITE |(< (/ x) 0)|))
 (325 325
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (325 325
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (288 144
      (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (225 27 (:REWRITE ZP-OPEN))
 (198 43 (:REWRITE SMAN::!MI-MI))
 (172 172 (:TYPE-PRESCRIPTION ABS))
 (150 150 (:REWRITE DEFAULT-FLOOR-2))
 (144 144 (:REWRITE |(floor x (- y))| . 2))
 (144 144 (:REWRITE |(floor x (- y))| . 1))
 (144 144
      (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (144 144
      (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (144 144 (:REWRITE |(floor (- x) y)| . 2))
 (144 144 (:REWRITE |(floor (- x) y)| . 1))
 (140 28
      (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (125 125
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (124 124 (:TYPE-PRESCRIPTION SMAN::STP))
 (90 90
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (90 90
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (90 90 (:REWRITE |(< 0 (/ x))|))
 (90 90 (:REWRITE |(< 0 (* x y))|))
 (83 83
     (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (73 30 (:REWRITE SMAN::STP-!R))
 (72 8 (:REWRITE FLOOR-POSITIVE . 2))
 (72 8 (:REWRITE FLOOR-NONPOSITIVE . 1))
 (68 34 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
 (60 12 (:REWRITE |(+ c (+ d x))|))
 (53 35 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (46 6 (:REWRITE ACL2-NUMBERP-X))
 (40 8 (:REWRITE FLOOR-POSITIVE . 4))
 (40 8 (:REWRITE FLOOR-POSITIVE . 3))
 (40 8 (:REWRITE FLOOR-NONPOSITIVE . 3))
 (40 8 (:REWRITE FLOOR-NONPOSITIVE . 2))
 (35 35
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (35 35
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (35 35
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (35 35 (:REWRITE |(equal c (/ x))|))
 (35 35 (:REWRITE |(equal c (- x))|))
 (35 35 (:REWRITE |(equal (/ x) c)|))
 (35 35 (:REWRITE |(equal (/ x) (/ y))|))
 (35 35 (:REWRITE |(equal (- x) c)|))
 (35 35 (:REWRITE |(equal (- x) (- y))|))
 (34 34 (:REWRITE |(+ x (- x))|))
 (32 32
     (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (32 32 (:REWRITE DEFAULT-MOD-2))
 (31 31
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (28
   28
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (28
  28
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (28 28
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (28 28
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (28 28
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (28 28
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (28 28 (:REWRITE |(mod x (- y))| . 3))
 (28 28 (:REWRITE |(mod x (- y))| . 2))
 (28 28 (:REWRITE |(mod x (- y))| . 1))
 (28 28
     (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (28 28
     (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (28 28 (:REWRITE |(mod (- x) y)| . 3))
 (28 28 (:REWRITE |(mod (- x) y)| . 2))
 (28 28 (:REWRITE |(mod (- x) y)| . 1))
 (28 28
     (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (20 4 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (20 4 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (20 4 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (20 4 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (20 4 (:REWRITE FLOOR-=-X/Y . 4))
 (20 4
     (:REWRITE |(equal (floor (+ x y) z) x)|))
 (20 2 (:REWRITE RATIONALP-X))
 (12 4 (:REWRITE DEFAULT-CDR))
 (12 4 (:REWRITE DEFAULT-CAR))
 (10 10 (:REWRITE |(* a (/ a) b)|))
 (9 9 (:REWRITE |(< y (+ (- c) x))|))
 (9 9 (:REWRITE |(< x (+ c/d y))|))
 (8 8 (:REWRITE FLOOR-POSITIVE . 1))
 (4 4 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
 (4 4 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (4 4 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (4 4 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (4 4 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
 (4 4 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (4 4 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (4 4 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
 (4 4 (:REWRITE FLOOR-ZERO . 1))
 (4 4 (:REWRITE |(mod (floor x y) z)| . 5))
 (4 4 (:REWRITE |(mod (floor x y) z)| . 4))
 (4 4 (:REWRITE |(mod (floor x y) z)| . 3))
 (4 4 (:REWRITE |(mod (floor x y) z)| . 2))
 (4 4
    (:REWRITE |(floor (floor x y) z)| . 5))
 (4 4
    (:REWRITE |(floor (floor x y) z)| . 4))
 (4 4
    (:REWRITE |(floor (floor x y) z)| . 3))
 (4 4
    (:REWRITE |(floor (floor x y) z)| . 2))
 (3 1 (:REWRITE SMAN::STP-!MI))
 (2 2 (:REWRITE REDUCE-RATIONALP-+))
 (2 2 (:REWRITE REDUCE-RATIONALP-*))
 (2 2 (:REWRITE RATIONALP-MINUS-X))
 (2 2 (:META META-RATIONALP-CORRECT)))
(SMAN::!R-!R-DIFF-ABOVE
 (3726 5 (:DEFINITION SMAN::!R))
 (1925 5 (:REWRITE ASH-TO-FLOOR))
 (1725 15 (:REWRITE DEFAULT-LOGAND-1))
 (1675 5 (:REWRITE |(logand y x)|))
 (1665 10 (:REWRITE LOGAND-CONSTANT-MASK))
 (320 5 (:REWRITE FLOOR-ZERO . 3))
 (289 59 (:REWRITE INTEGERP-MINUS-X))
 (265 5 (:REWRITE CANCEL-MOD-+))
 (265 5 (:REWRITE CANCEL-FLOOR-+))
 (175 5 (:REWRITE MOD-X-Y-=-X . 4))
 (175 5 (:REWRITE MOD-X-Y-=-X . 3))
 (175 5 (:REWRITE FLOOR-ZERO . 5))
 (175 5 (:REWRITE FLOOR-ZERO . 4))
 (170 20 (:REWRITE |(* (- x) y)|))
 (170 5 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (170 5 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (160 40 (:REWRITE |(* y x)|))
 (155 5 (:REWRITE SMAN::UNNECESSARY-MOD))
 (155 5 (:REWRITE SMAN::UNNECESSARY-FLOOR))
 (155 5 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (155 5 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (145 145
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (145 145
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (145 145
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (145 145
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (140 140 (:TYPE-PRESCRIPTION SMAN::!R))
 (125 125
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (125 125
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (125 125
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (125 125
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (110 110 (:REWRITE DEFAULT-TIMES-2))
 (110 110 (:REWRITE DEFAULT-TIMES-1))
 (110 5 (:REWRITE MOD-ZERO . 3))
 (110 5 (:REWRITE FLOOR-=-X/Y . 3))
 (110 5 (:REWRITE FLOOR-=-X/Y . 2))
 (100 20 (:REWRITE DEFAULT-MINUS))
 (90 20 (:REWRITE |(- (* c x))|))
 (90 5 (:REWRITE MOD-ZERO . 4))
 (80 60 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (80 60 (:REWRITE DEFAULT-LESS-THAN-1))
 (65 60
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (65 60
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (60 60 (:REWRITE THE-FLOOR-BELOW))
 (60 60 (:REWRITE THE-FLOOR-ABOVE))
 (60 60 (:REWRITE SIMPLIFY-SUMS-<))
 (60 60
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (60 60
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (60 60
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (60 60
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (60 60 (:REWRITE INTEGERP-<-CONSTANT))
 (60 60 (:REWRITE DEFAULT-LESS-THAN-2))
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
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (60 60
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (60 60
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (60 60
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (60 60 (:REWRITE |(< (/ x) (/ y))|))
 (60 60 (:REWRITE |(< (- x) c)|))
 (60 60 (:REWRITE |(< (- x) (- y))|))
 (55 5 (:REWRITE DEFAULT-MOD-RATIO))
 (55 5 (:REWRITE DEFAULT-FLOOR-RATIO))
 (50 50 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (49 49 (:REWRITE REDUCE-INTEGERP-+))
 (49 49 (:META META-INTEGERP-CORRECT))
 (39 39
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (39 39
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (39 39 (:REWRITE |(< (/ x) 0)|))
 (39 39 (:REWRITE |(< (* x y) 0)|))
 (25 5 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (25 5 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (25 5 (:REWRITE MOD-X-Y-=-X . 2))
 (25 5
     (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (25 5 (:REWRITE MOD-CANCEL-*-CONST))
 (25 5 (:REWRITE FLOOR-ZERO . 2))
 (25 5 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (25 5 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (25 5
     (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (25 5 (:REWRITE FLOOR-CANCEL-*-CONST))
 (25 5 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (25 5
     (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (25 5
     (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (25 5
     (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (21 5 (:REWRITE SMAN::!MI-MI))
 (15 15 (:REWRITE DEFAULT-LOGAND-2))
 (14 14 (:TYPE-PRESCRIPTION SMAN::STP))
 (11 11
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (11 11 (:REWRITE NORMALIZE-ADDENDS))
 (11 11 (:REWRITE DEFAULT-PLUS-2))
 (11 11 (:REWRITE DEFAULT-PLUS-1))
 (10 10 (:TYPE-PRESCRIPTION ABS))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (10 10 (:REWRITE |(< 0 (/ x))|))
 (10 10 (:REWRITE |(< 0 (* x y))|))
 (6 2 (:REWRITE SMAN::STP-!R))
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
 (5 5 (:REWRITE ZP-OPEN))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
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
    (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (5 5
    (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (5 5
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (5 5 (:REWRITE DEFAULT-MOD-2))
 (5 5 (:REWRITE DEFAULT-MOD-1))
 (5 5 (:REWRITE DEFAULT-FLOOR-2))
 (5 5 (:REWRITE DEFAULT-FLOOR-1))
 (5 5 (:REWRITE |(mod x (- y))| . 3))
 (5 5 (:REWRITE |(mod x (- y))| . 2))
 (5 5 (:REWRITE |(mod x (- y))| . 1))
 (5 5
    (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (5 5
    (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (5 5 (:REWRITE |(mod (- x) y)| . 3))
 (5 5 (:REWRITE |(mod (- x) y)| . 2))
 (5 5 (:REWRITE |(mod (- x) y)| . 1))
 (5 5
    (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (5 5 (:REWRITE |(floor x (- y))| . 2))
 (5 5 (:REWRITE |(floor x (- y))| . 1))
 (5 5
    (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (5 5
    (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (5 5 (:REWRITE |(floor (- x) y)| . 2))
 (5 5 (:REWRITE |(floor (- x) y)| . 1))
 (5 5
    (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (5 5 (:REWRITE |(equal c (/ x))|))
 (5 5 (:REWRITE |(equal c (- x))|))
 (5 5 (:REWRITE |(equal (/ x) c)|))
 (5 5 (:REWRITE |(equal (/ x) (/ y))|))
 (5 5 (:REWRITE |(equal (- x) c)|))
 (5 5 (:REWRITE |(equal (- x) (- y))|))
 (5 5
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (1 1 (:REWRITE |(< y (+ (- c) x))|))
 (1 1 (:REWRITE |(< x (+ c/d y))|)))
(SMAN::!R-R
 (17923 188 (:LINEAR SMAN::R-BOUND))
 (12291 233 (:REWRITE DEFAULT-LOGAND-2))
 (2771 668 (:REWRITE DEFAULT-PLUS-1))
 (2443 32 (:REWRITE MOD-X-Y-=-X . 3))
 (2256 111 (:REWRITE |(+ (if a b c) x)|))
 (2070 32 (:REWRITE MOD-X-Y-=-X . 4))
 (2067 32 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (2007 32 (:REWRITE MOD-ZERO . 4))
 (1969 32 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (1749 5 (:REWRITE FLOOR-ZERO . 3))
 (1438 5 (:REWRITE FLOOR-ZERO . 4))
 (1095 5 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (1078 5 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (1066 304
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (1063 5 (:REWRITE FLOOR-ZERO . 5))
 (1041 668 (:REWRITE DEFAULT-PLUS-2))
 (1033 65 (:LINEAR EXPT->-1-ONE))
 (953 305
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (919 1 (:REWRITE |(floor (+ x r) i)|))
 (912 548 (:REWRITE DEFAULT-TIMES-2))
 (910 65 (:LINEAR EXPT->=-1-ONE))
 (769 32 (:REWRITE MOD-ZERO . 3))
 (764 764
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (764 764
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (764 764
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (706 130
      (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (665 548 (:REWRITE DEFAULT-TIMES-1))
 (641 65 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (565 279 (:REWRITE INTEGERP-<-CONSTANT))
 (513
   513
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (513
  513
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (513 513
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (513
     513
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (513 513
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (513 513
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (488 65 (:LINEAR EXPT-X->=-X))
 (488 65 (:LINEAR EXPT-X->-X))
 (463 453
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (463 453
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (463 453
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (432 432 (:TYPE-PRESCRIPTION ASH))
 (402 32 (:REWRITE DEFAULT-MOD-RATIO))
 (400 79 (:REWRITE DEFAULT-MINUS))
 (385 305 (:REWRITE DEFAULT-LESS-THAN-1))
 (384 192
      (:TYPE-PRESCRIPTION SMAN::NATP-NTH-MP))
 (377 377
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (357 277
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (327 277
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (319 305 (:REWRITE DEFAULT-LESS-THAN-2))
 (309 309 (:REWRITE REDUCE-INTEGERP-+))
 (309 309 (:META META-INTEGERP-CORRECT))
 (309 304
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (305 305 (:REWRITE THE-FLOOR-BELOW))
 (305 305 (:REWRITE THE-FLOOR-ABOVE))
 (291 291 (:REWRITE DEFAULT-EXPT-2))
 (291 291 (:REWRITE DEFAULT-EXPT-1))
 (291 291 (:REWRITE |(expt 1/c n)|))
 (291 291 (:REWRITE |(expt (- x) n)|))
 (286 130
      (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (285 285
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (279 279 (:REWRITE CONSTANT-<-INTEGERP))
 (279 279
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (279 279
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (279 279
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (279 279
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (279 279 (:REWRITE |(< c (- x))|))
 (279 279
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (279 279
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (279 279
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (279 279
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (279 279 (:REWRITE |(< (/ x) (/ y))|))
 (279 279 (:REWRITE |(< (- x) c)|))
 (279 279 (:REWRITE |(< (- x) (- y))|))
 (278 278
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (277 277 (:REWRITE SIMPLIFY-SUMS-<))
 (270 65 (:LINEAR EXPT-<=-1-TWO))
 (270 54 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (270 54 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (270 54
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (270 54
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (222 32 (:REWRITE MOD-X-Y-=-X . 2))
 (222 32 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (222 32
      (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (216 32 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (216 32 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (181 5 (:REWRITE FLOOR-=-X/Y . 2))
 (168 168
      (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 3))
 (168 168
      (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (159 31 (:REWRITE MOD-CANCEL-*-CONST))
 (145 9 (:REWRITE DEFAULT-FLOOR-RATIO))
 (130 130
      (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (130 130
      (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (128 122 (:REWRITE DEFAULT-LOGAND-1))
 (127 31
      (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (127 31
      (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (110 27 (:REWRITE |(+ c (+ d x))|))
 (108 108 (:REWRITE |(< (/ x) 0)|))
 (108 108 (:REWRITE |(< (* x y) 0)|))
 (107 107
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (107 107
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (106 1 (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (81 5 (:REWRITE FLOOR-ZERO . 2))
 (81 5 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (81 5 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (65 65 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (65 65 (:LINEAR EXPT-LINEAR-UPPER-<))
 (65 65 (:LINEAR EXPT-LINEAR-LOWER-<))
 (65 65 (:LINEAR EXPT->=-1-TWO))
 (65 65 (:LINEAR EXPT->-1-TWO))
 (65 65 (:LINEAR EXPT-<=-1-ONE))
 (65 65 (:LINEAR EXPT-<-1-TWO))
 (65 65 (:LINEAR EXPT-<-1-ONE))
 (63 31
     (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (63 31
     (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (54 54 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
 (54 54 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (54 54
     (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (54 54 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (54 54 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
 (54 54
     (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (54 54 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (54 54 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
 (50 50 (:REWRITE |(< 0 (* x y))|))
 (46 36
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (46 36
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (41 8 (:REWRITE ZP-OPEN))
 (40 40
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (40 40
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (40 40 (:REWRITE |(< 0 (/ x))|))
 (40 36 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (38 32 (:REWRITE DEFAULT-MOD-1))
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
 (32 32
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (32 32 (:REWRITE DEFAULT-MOD-2))
 (31 31 (:REWRITE |(mod x (- y))| . 3))
 (31 31 (:REWRITE |(mod x (- y))| . 2))
 (31 31 (:REWRITE |(mod x (- y))| . 1))
 (31 31
     (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (31 31
     (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (31 31 (:REWRITE |(mod (- x) y)| . 3))
 (31 31 (:REWRITE |(mod (- x) y)| . 2))
 (31 31 (:REWRITE |(mod (- x) y)| . 1))
 (31 31 (:REWRITE |(< x (+ c/d y))|))
 (24 4
     (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (24 4 (:REWRITE FLOOR-CANCEL-*-CONST))
 (24 4
     (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (19 9 (:REWRITE DEFAULT-FLOOR-1))
 (18 6 (:LINEAR SMAN::BYTEP-NTH-MP))
 (12 8 (:REWRITE DEFAULT-CDR))
 (12 8 (:REWRITE DEFAULT-CAR))
 (12 4
     (:REWRITE |(< (* (/ x) y) 1) with (< 0 x)|))
 (11 11 (:TYPE-PRESCRIPTION ABS))
 (10 10 (:REWRITE |(< (+ c/d x) y)|))
 (9 9 (:REWRITE DEFAULT-FLOOR-2))
 (9 9 (:REWRITE |(< (+ (- c) x) y)|))
 (8 4
    (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
 (7 7 (:REWRITE |(< y (+ (- c) x))|))
 (4 4
    (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (4 4 (:REWRITE |(floor x (- y))| . 2))
 (4 4 (:REWRITE |(floor x (- y))| . 1))
 (4 4
    (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (4 4
    (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (4 4 (:REWRITE |(floor (- x) y)| . 2))
 (4 4 (:REWRITE |(floor (- x) y)| . 1))
 (4 4
    (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (4 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (3 3 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (2 1 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (1 1 (:REWRITE |(equal (+ (- c) x) y)|)))
(SMAN::NTHCDR-IS-LAST
     (167 128 (:REWRITE DEFAULT-PLUS-2))
     (128 128 (:REWRITE DEFAULT-PLUS-1))
     (91 91 (:REWRITE DEFAULT-CDR))
     (80 80
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (80 80 (:REWRITE NORMALIZE-ADDENDS))
     (60 4 (:REWRITE |(+ (+ x y) z)|))
     (53 30
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (53 30
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (46 30 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (32 32
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (30 30
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (30 30 (:REWRITE |(equal c (/ x))|))
     (30 30 (:REWRITE |(equal c (- x))|))
     (30 30 (:REWRITE |(equal (/ x) c)|))
     (30 30 (:REWRITE |(equal (/ x) (/ y))|))
     (30 30 (:REWRITE |(equal (- x) c)|))
     (30 30 (:REWRITE |(equal (- x) (- y))|))
     (27 27 (:REWRITE DEFAULT-CAR))
     (22 19 (:REWRITE DEFAULT-LESS-THAN-2))
     (20 17
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (20 17 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (19 19 (:REWRITE THE-FLOOR-BELOW))
     (19 19 (:REWRITE THE-FLOOR-ABOVE))
     (19 19
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (19 19
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (19 19
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (19 19
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (19 19 (:REWRITE INTEGERP-<-CONSTANT))
     (19 19 (:REWRITE DEFAULT-LESS-THAN-1))
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
     (17 17 (:REWRITE SIMPLIFY-SUMS-<))
     (11 11
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (11 11
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (11 11 (:REWRITE |(< 0 (/ x))|))
     (11 11 (:REWRITE |(< 0 (* x y))|))
     (10 10 (:REWRITE |(< y (+ (- c) x))|))
     (10 10 (:REWRITE |(< x (+ c/d y))|))
     (8 8 (:REWRITE |(< (/ x) 0)|))
     (8 8 (:REWRITE |(< (* x y) 0)|))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (5 5 (:REWRITE REDUCE-INTEGERP-+))
     (5 5 (:REWRITE INTEGERP-MINUS-X))
     (5 5 (:REWRITE |(equal (+ (- c) x) y)|))
     (5 5 (:META META-INTEGERP-CORRECT))
     (4 2
        (:TYPE-PRESCRIPTION SMAN::NATP-NTH-MP))
     (3 3 (:REWRITE |(equal x (if a b c))|))
     (3 3 (:REWRITE |(equal (if a b c) x)|))
     (2 2 (:TYPE-PRESCRIPTION SMAN::MP))
     (1 1 (:REWRITE |(< (+ c/d x) y)|))
     (1 1 (:REWRITE |(< (+ (- c) x) y)|)))
(SMAN::NTHCDR-UPDATE-NTH
     (3917 63 (:REWRITE SMAN::NTHCDR-IS-LAST))
     (1252 21 (:REWRITE SMAN::!NTH-NTH))
     (1069 85
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (1018 40 (:REWRITE ZP-OPEN))
     (738 559 (:REWRITE DEFAULT-PLUS-2))
     (718 60 (:REWRITE ACL2-NUMBERP-X))
     (676 8 (:REWRITE LEN-UPDATE-NTH))
     (645 118
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (634 113
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (559 559 (:REWRITE DEFAULT-PLUS-1))
     (549 121 (:REWRITE |(+ c (+ d x))|))
     (488 46 (:REWRITE |(equal (+ (- c) x) y)|))
     (411 85 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (396 85
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (329 20 (:REWRITE RATIONALP-X))
     (314 8 (:DEFINITION NFIX))
     (287 287
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (287 287 (:REWRITE NORMALIZE-ADDENDS))
     (263 21 (:REWRITE |(+ y (+ x z))|))
     (255 17 (:REWRITE |(+ (+ x y) z)|))
     (254 8 (:DEFINITION MAX))
     (242 206 (:REWRITE DEFAULT-CDR))
     (228 114
          (:TYPE-PRESCRIPTION SMAN::NATP-NTH-MP))
     (228 6 (:DEFINITION NTH))
     (206 6 (:REWRITE |(< (+ (- c) x) y)|))
     (142 118 (:REWRITE DEFAULT-LESS-THAN-2))
     (124 118 (:REWRITE DEFAULT-LESS-THAN-1))
     (121 96 (:REWRITE SIMPLIFY-SUMS-<))
     (121 96
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (121 96 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (118 118 (:REWRITE THE-FLOOR-BELOW))
     (118 118 (:REWRITE THE-FLOOR-ABOVE))
     (118 118
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (118 118
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (116 4 (:REWRITE |(equal (if a b c) x)|))
     (114 114 (:TYPE-PRESCRIPTION SMAN::MP))
     (113 113
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (110 96
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
     (89 89 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (85 85
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (85 85 (:REWRITE |(equal c (/ x))|))
     (85 85 (:REWRITE |(equal c (- x))|))
     (85 85 (:REWRITE |(equal (/ x) c)|))
     (85 85 (:REWRITE |(equal (/ x) (/ y))|))
     (85 85 (:REWRITE |(equal (- x) c)|))
     (85 85 (:REWRITE |(equal (- x) (- y))|))
     (82 74 (:REWRITE |(+ 0 x)|))
     (43 43 (:REWRITE |(< x (+ c/d y))|))
     (37 37 (:REWRITE |(< y (+ (- c) x))|))
     (35 35 (:REWRITE REDUCE-INTEGERP-+))
     (35 35 (:REWRITE INTEGERP-MINUS-X))
     (35 35 (:META META-INTEGERP-CORRECT))
     (33 33 (:REWRITE |(< 0 (* x y))|))
     (30 30 (:REWRITE |(< (* x y) 0)|))
     (27 27
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (27 27
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (27 27 (:REWRITE |(< 0 (/ x))|))
     (21 21 (:REWRITE DEFAULT-CAR))
     (20 20 (:REWRITE REDUCE-RATIONALP-+))
     (20 20 (:REWRITE REDUCE-RATIONALP-*))
     (20 20 (:REWRITE RATIONALP-MINUS-X))
     (20 20 (:META META-RATIONALP-CORRECT))
     (19 19
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (19 19
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (19 19 (:REWRITE |(< (/ x) 0)|))
     (17 17 (:REWRITE |(< (+ c/d x) y)|))
     (13 2 (:REWRITE |(+ x (if a b c))|))
     (3 3 (:REWRITE |(< x (if a b c))|))
     (2 2 (:REWRITE |(equal x (if a b c))|)))
(SMAN::NTHCDR-TO-END
     (374 14 (:REWRITE SMAN::NTHCDR-IS-LAST))
     (100 11
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (94 77 (:REWRITE DEFAULT-PLUS-2))
     (77 77 (:REWRITE DEFAULT-PLUS-1))
     (48 4 (:REWRITE |(+ y (+ x z))|))
     (38 38
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (38 38 (:REWRITE NORMALIZE-ADDENDS))
     (17 9
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (17 9
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (16 9 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (15 15 (:REWRITE DEFAULT-CDR))
     (14 9 (:REWRITE DEFAULT-LESS-THAN-2))
     (13 8 (:REWRITE SIMPLIFY-SUMS-<))
     (13 8
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (13 8 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (11 11
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (11 10 (:REWRITE |(+ 0 x)|))
     (9 9 (:REWRITE THE-FLOOR-BELOW))
     (9 9 (:REWRITE THE-FLOOR-ABOVE))
     (9 9 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (9 9
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (9 9
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (9 9 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (9 9 (:REWRITE INTEGERP-<-CONSTANT))
     (9 9
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (9 9 (:REWRITE DEFAULT-LESS-THAN-1))
     (9 9 (:REWRITE CONSTANT-<-INTEGERP))
     (9 9 (:REWRITE |(equal c (/ x))|))
     (9 9 (:REWRITE |(equal c (- x))|))
     (9 9 (:REWRITE |(equal (/ x) c)|))
     (9 9 (:REWRITE |(equal (/ x) (/ y))|))
     (9 9 (:REWRITE |(equal (- x) c)|))
     (9 9 (:REWRITE |(equal (- x) (- y))|))
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
     (3 3 (:REWRITE REDUCE-INTEGERP-+))
     (3 3 (:REWRITE INTEGERP-MINUS-X))
     (3 3 (:REWRITE |(equal (+ (- c) x) y)|))
     (3 3 (:META META-INTEGERP-CORRECT))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (2 2 (:REWRITE |(< y (+ (- c) x))|))
     (2 2 (:REWRITE |(< x (if a b c))|))
     (2 2 (:REWRITE |(< x (+ c/d y))|))
     (2 2 (:REWRITE |(< 0 (/ x))|))
     (2 2 (:REWRITE |(< 0 (* x y))|))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (1 1 (:REWRITE |(equal x (if a b c))|))
     (1 1 (:REWRITE |(equal (if a b c) x)|))
     (1 1 (:REWRITE |(< (/ x) 0)|))
     (1 1 (:REWRITE |(< (+ c/d x) y)|))
     (1 1 (:REWRITE |(< (+ (- c) x) y)|))
     (1 1 (:REWRITE |(< (* x y) 0)|)))
(SMAN::NTH-AND-NTHCDR-MAKE-CONS
     (5546 123 (:REWRITE SMAN::NTHCDR-IS-LAST))
     (1850 46 (:REWRITE |(< (+ (- c) x) y)|))
     (1807 212
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (1746 1084 (:REWRITE DEFAULT-PLUS-2))
     (1240 168 (:REWRITE ACL2-NUMBERP-X))
     (1084 1084 (:REWRITE DEFAULT-PLUS-1))
     (728 212 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (700 212
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (684 684
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (684 684 (:REWRITE NORMALIZE-ADDENDS))
     (536 56 (:REWRITE RATIONALP-X))
     (420 223 (:REWRITE DEFAULT-LESS-THAN-2))
     (303 167
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (297 99 (:REWRITE ZP-OPEN))
     (296 167 (:REWRITE SIMPLIFY-SUMS-<))
     (295 167
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (253 253
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (223 223 (:REWRITE THE-FLOOR-BELOW))
     (223 223 (:REWRITE THE-FLOOR-ABOVE))
     (223 223
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (223 223
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (223 223 (:REWRITE DEFAULT-LESS-THAN-1))
     (212 212
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (212 212 (:REWRITE |(equal c (/ x))|))
     (212 212 (:REWRITE |(equal c (- x))|))
     (212 212 (:REWRITE |(equal (/ x) c)|))
     (212 212 (:REWRITE |(equal (/ x) (/ y))|))
     (212 212 (:REWRITE |(equal (- x) c)|))
     (212 212 (:REWRITE |(equal (- x) (- y))|))
     (183 167
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (167 167 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (167 167 (:REWRITE INTEGERP-<-CONSTANT))
     (167 167 (:REWRITE CONSTANT-<-INTEGERP))
     (167 167
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (167 167
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (167 167
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (167 167
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (167 167 (:REWRITE |(< c (- x))|))
     (167 167
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (167 167
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (167 167
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (167 167
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (167 167 (:REWRITE |(< (/ x) (/ y))|))
     (167 167 (:REWRITE |(< (- x) c)|))
     (167 167 (:REWRITE |(< (- x) (- y))|))
     (103 103 (:REWRITE |(< x (+ c/d y))|))
     (91 91 (:REWRITE |(< y (+ (- c) x))|))
     (74 74 (:REWRITE REDUCE-INTEGERP-+))
     (74 74 (:REWRITE INTEGERP-MINUS-X))
     (74 74 (:META META-INTEGERP-CORRECT))
     (61 61 (:REWRITE DEFAULT-CAR))
     (56 56 (:REWRITE REDUCE-RATIONALP-+))
     (56 56 (:REWRITE REDUCE-RATIONALP-*))
     (56 56 (:REWRITE RATIONALP-MINUS-X))
     (56 56 (:META META-RATIONALP-CORRECT))
     (54 18 (:LINEAR SMAN::BYTEP-NTH-MP))
     (48 48 (:REWRITE CDR-CONS))
     (46 46 (:REWRITE |(< (+ c/d x) y)|))
     (45 45 (:REWRITE |(equal (+ (- c) x) y)|))
     (20 20
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (20 20
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (20 20 (:REWRITE |(< (/ x) 0)|))
     (20 20 (:REWRITE |(< (* x y) 0)|))
     (18 18 (:REWRITE |(< 0 (* x y))|))
     (12 12
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (12 12 (:REWRITE CAR-CONS))
     (8 8 (:REWRITE |(< x (if a b c))|))
     (7 7 (:REWRITE |(equal x (if a b c))|))
     (7 7 (:REWRITE |(equal (if a b c) x)|))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (6 6 (:REWRITE |(< 0 (/ x))|))
     (1 1 (:REWRITE |(+ x (if a b c))|)))
(SMAN::MP-IMPLIES-TRUE-LISTP
     (6 6 (:REWRITE THE-FLOOR-BELOW))
     (6 6 (:REWRITE THE-FLOOR-ABOVE))
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
     (6 6 (:REWRITE |(< (/ x) (/ y))|))
     (6 6 (:REWRITE |(< (- x) c)|))
     (6 6 (:REWRITE |(< (- x) (- y))|))
     (4 4 (:REWRITE DEFAULT-CDR))
     (4 2 (:DEFINITION TRUE-LISTP))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (3 3 (:REWRITE REDUCE-INTEGERP-+))
     (3 3 (:REWRITE INTEGERP-MINUS-X))
     (3 3 (:REWRITE DEFAULT-CAR))
     (3 3 (:REWRITE |(< (/ x) 0)|))
     (3 3 (:REWRITE |(< (* x y) 0)|))
     (3 3 (:META META-INTEGERP-CORRECT)))
(SMAN::EQUAL-LEN-0 (9 5 (:REWRITE DEFAULT-PLUS-2))
                   (8 4
                      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                   (8 4
                      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                   (5 5
                      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                   (5 5 (:REWRITE NORMALIZE-ADDENDS))
                   (5 5 (:REWRITE DEFAULT-PLUS-1))
                   (4 4
                      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
                   (4 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                   (4 4
                      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                   (4 4
                      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
                   (4 4
                      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
                   (4 4 (:REWRITE DEFAULT-CDR))
                   (4 4 (:REWRITE |(equal c (/ x))|))
                   (4 4 (:REWRITE |(equal c (- x))|))
                   (4 4 (:REWRITE |(equal (/ x) c)|))
                   (4 4 (:REWRITE |(equal (/ x) (/ y))|))
                   (4 4 (:REWRITE |(equal (- x) c)|))
                   (4 4 (:REWRITE |(equal (- x) (- y))|)))
(SMAN::WEAK-ML (6 3
                  (:TYPE-PRESCRIPTION SMAN::NATP-NTH-MP))
               (3 3 (:TYPE-PRESCRIPTION SMAN::MP)))
(SMAN::WEAK-STP (12 6
                    (:TYPE-PRESCRIPTION SMAN::NATP-NTH-MP))
                (6 6 (:TYPE-PRESCRIPTION SMAN::MP)))
(SMAN::DIVERGENT-ADDR
     (330 165 (:TYPE-PRESCRIPTION SMAN::NATP-MI))
     (272 72 (:REWRITE DEFAULT-LESS-THAN-1))
     (225 159 (:REWRITE DEFAULT-PLUS-1))
     (189 159 (:REWRITE DEFAULT-PLUS-2))
     (167 167 (:TYPE-PRESCRIPTION SMAN::STP))
     (84 72 (:REWRITE DEFAULT-LESS-THAN-2))
     (84 12 (:DEFINITION LEN))
     (72 72 (:REWRITE THE-FLOOR-BELOW))
     (72 72 (:REWRITE THE-FLOOR-ABOVE))
     (72 48
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (56 2
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (54 54
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (54 54
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (54 54
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
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
     (54 54 (:REWRITE |(< (- x) (- y))|))
     (50 50
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (50 50 (:REWRITE INTEGERP-<-CONSTANT))
     (50 50 (:REWRITE CONSTANT-<-INTEGERP))
     (46 6 (:REWRITE ACL2-NUMBERP-X))
     (38 38
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (36 36 (:REWRITE DEFAULT-CDR))
     (25 25 (:REWRITE DEFAULT-MINUS))
     (24 24 (:REWRITE |(< (/ x) 0)|))
     (24 24 (:REWRITE |(< (* x y) 0)|))
     (20 20 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (20 2 (:REWRITE RATIONALP-X))
     (18 18 (:REWRITE |(+ c (+ d x))|))
     (16 16 (:REWRITE |(< (+ c/d x) y)|))
     (16 16 (:REWRITE |(< (+ (- c) x) y)|))
     (16 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (16 2
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (12 12
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (12 12
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (12 12 (:REWRITE DEFAULT-CAR))
     (12 12 (:REWRITE |(< y (+ (- c) x))|))
     (12 12 (:REWRITE |(< x (+ c/d y))|))
     (6 6 (:REWRITE FOLD-CONSTS-IN-+))
     (6 6 (:REWRITE |(< 0 (/ x))|))
     (6 6 (:REWRITE |(< 0 (* x y))|))
     (4 4 (:REWRITE REDUCE-INTEGERP-+))
     (4 4 (:REWRITE INTEGERP-MINUS-X))
     (4 4 (:META META-INTEGERP-CORRECT))
     (3 1 (:LINEAR SMAN::BYTEP-MI))
     (2 2 (:REWRITE REDUCE-RATIONALP-+))
     (2 2 (:REWRITE REDUCE-RATIONALP-*))
     (2 2
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (2 2
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (2 2 (:REWRITE RATIONALP-MINUS-X))
     (2 2
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (2 2 (:REWRITE |(equal c (/ x))|))
     (2 2 (:REWRITE |(equal c (- x))|))
     (2 2 (:REWRITE |(equal (/ x) c)|))
     (2 2 (:REWRITE |(equal (/ x) (/ y))|))
     (2 2 (:REWRITE |(equal (- x) c)|))
     (2 2 (:REWRITE |(equal (- x) (- y))|))
     (2 2 (:META META-RATIONALP-CORRECT)))
(SMAN::DIVERGENT-ADDR-LEGAL
     (2262 1131 (:TYPE-PRESCRIPTION SMAN::NATP-MI))
     (1171 1171 (:REWRITE DEFAULT-CDR))
     (1133 1133 (:TYPE-PRESCRIPTION SMAN::STP))
     (834 424 (:REWRITE DEFAULT-PLUS-2))
     (600 68
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (424 424 (:REWRITE DEFAULT-PLUS-1))
     (414 54 (:REWRITE ACL2-NUMBERP-X))
     (384 384
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (384 384 (:REWRITE NORMALIZE-ADDENDS))
     (240 68
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (235 184
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (235 184
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (229 201 (:REWRITE DEFAULT-LESS-THAN-2))
     (225 201 (:REWRITE DEFAULT-LESS-THAN-1))
     (207 184 (:REWRITE SIMPLIFY-SUMS-<))
     (201 201 (:REWRITE THE-FLOOR-BELOW))
     (201 201 (:REWRITE THE-FLOOR-ABOVE))
     (194 194
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (194 194
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (194 194
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
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
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (194 194
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (194 194
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (194 194
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (194 194 (:REWRITE |(< (/ x) (/ y))|))
     (194 194 (:REWRITE |(< (- x) c)|))
     (194 194 (:REWRITE |(< (- x) (- y))|))
     (194 68 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (191 191 (:REWRITE DEFAULT-CAR))
     (184 184 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (180 18 (:REWRITE RATIONALP-X))
     (72 72
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (68 68
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (68 68 (:REWRITE |(equal c (/ x))|))
     (68 68 (:REWRITE |(equal c (- x))|))
     (68 68 (:REWRITE |(equal (/ x) c)|))
     (68 68 (:REWRITE |(equal (/ x) (/ y))|))
     (68 68 (:REWRITE |(equal (- x) c)|))
     (68 68 (:REWRITE |(equal (- x) (- y))|))
     (65 65 (:REWRITE |(< 0 (/ x))|))
     (65 65 (:REWRITE |(< 0 (* x y))|))
     (55 55
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (55 55
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (36 36 (:REWRITE REDUCE-INTEGERP-+))
     (36 36 (:REWRITE INTEGERP-MINUS-X))
     (36 36 (:META META-INTEGERP-CORRECT))
     (30 30 (:REWRITE |(equal (+ (- c) x) y)|))
     (18 18
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (18 18
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (18 18 (:REWRITE REDUCE-RATIONALP-+))
     (18 18 (:REWRITE REDUCE-RATIONALP-*))
     (18 18 (:REWRITE RATIONALP-MINUS-X))
     (18 18 (:REWRITE |(< (/ x) 0)|))
     (18 18 (:REWRITE |(< (* x y) 0)|))
     (18 18 (:META META-RATIONALP-CORRECT))
     (15 15 (:REWRITE CAR-CONS))
     (8 8 (:REWRITE |(equal x (if a b c))|))
     (8 8 (:REWRITE |(equal (if a b c) x)|))
     (4 4 (:REWRITE |(+ x (if a b c))|))
     (3 1 (:LINEAR SMAN::BYTEP-MI)))
(SMAN::NO-DIVERGENCE-IMPLIES-M1=M2
     (2988 96 (:REWRITE SMAN::NTHCDR-IS-LAST))
     (2098 231
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (1934 48 (:REWRITE |(< (+ (- c) x) y)|))
     (1812 184 (:REWRITE ZP-OPEN))
     (1605 1605 (:REWRITE DEFAULT-CDR))
     (1569 995 (:REWRITE DEFAULT-PLUS-2))
     (1448 174 (:REWRITE ACL2-NUMBERP-X))
     (995 995 (:REWRITE DEFAULT-PLUS-1))
     (824 231
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (820 820
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (820 820 (:REWRITE NORMALIZE-ADDENDS))
     (793 231 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (637 58 (:REWRITE RATIONALP-X))
     (586 409 (:REWRITE DEFAULT-LESS-THAN-2))
     (460 460 (:REWRITE DEFAULT-CAR))
     (409 409 (:REWRITE THE-FLOOR-BELOW))
     (409 409 (:REWRITE THE-FLOOR-ABOVE))
     (409 409 (:REWRITE DEFAULT-LESS-THAN-1))
     (407 407
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (407 407
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (407 407
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (381 260
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (322 260 (:REWRITE SIMPLIFY-SUMS-<))
     (314 314 (:REWRITE INTEGERP-<-CONSTANT))
     (314 314 (:REWRITE CONSTANT-<-INTEGERP))
     (314 314
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (314 314
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (314 314
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (314 314
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (314 314 (:REWRITE |(< c (- x))|))
     (314 314
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (314 314
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (314 314
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (314 314
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (314 314 (:REWRITE |(< (/ x) (/ y))|))
     (314 314 (:REWRITE |(< (- x) c)|))
     (314 314 (:REWRITE |(< (- x) (- y))|))
     (287 287 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (235 235
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (231 231
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (231 231 (:REWRITE |(equal c (/ x))|))
     (231 231 (:REWRITE |(equal c (- x))|))
     (231 231 (:REWRITE |(equal (/ x) c)|))
     (231 231 (:REWRITE |(equal (/ x) (/ y))|))
     (231 231 (:REWRITE |(equal (- x) c)|))
     (231 231 (:REWRITE |(equal (- x) (- y))|))
     (188 188 (:REWRITE DEFAULT-TIMES-2))
     (188 188 (:REWRITE DEFAULT-TIMES-1))
     (125 125 (:REWRITE |(< 0 (* x y))|))
     (120 2 (:REWRITE |(< x (if a b c))|))
     (84 84 (:REWRITE CAR-CONS))
     (80 80 (:REWRITE REDUCE-INTEGERP-+))
     (80 80 (:REWRITE INTEGERP-MINUS-X))
     (80 80 (:META META-INTEGERP-CORRECT))
     (78 78 (:REWRITE |(< 0 (/ x))|))
     (71 71
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (71 71
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (69 23 (:LINEAR SMAN::BYTEP-NTH-MP))
     (67 67 (:REWRITE |(equal (+ (- c) x) y)|))
     (58 58 (:REWRITE REDUCE-RATIONALP-+))
     (58 58 (:REWRITE REDUCE-RATIONALP-*))
     (58 58 (:REWRITE RATIONALP-MINUS-X))
     (58 58 (:META META-RATIONALP-CORRECT))
     (48 48 (:REWRITE |(< (+ c/d x) y)|))
     (47 47
         (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (47 47
         (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (47 47
         (:REWRITE |(< x (/ y)) with (< y 0)|))
     (46 46 (:REWRITE |(< y (+ (- c) x))|))
     (46 46 (:REWRITE |(< x (+ c/d y))|))
     (22 22
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (22 22
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (22 22 (:REWRITE |(< (/ x) 0)|))
     (22 22 (:REWRITE |(< (* x y) 0)|))
     (4 4 (:REWRITE |(equal x (if a b c))|))
     (4 4 (:REWRITE |(equal (if a b c) x)|))
     (2 2 (:REWRITE |(+ x (if a b c))|)))
(SMAN::NO-DIVERGENCE-IMPLIES-ST1=ST2
     (638 72
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (511 511 (:REWRITE DEFAULT-CDR))
     (480 72 (:REWRITE ACL2-NUMBERP-X))
     (240 120 (:REWRITE DEFAULT-PLUS-2))
     (230 72
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (208 208 (:REWRITE DEFAULT-CAR))
     (206 72 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (204 24 (:REWRITE RATIONALP-X))
     (120 120 (:REWRITE DEFAULT-PLUS-1))
     (101 101
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (101 101 (:REWRITE NORMALIZE-ADDENDS))
     (76 76
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (72 72
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (72 72 (:REWRITE |(equal c (/ x))|))
     (72 72 (:REWRITE |(equal c (- x))|))
     (72 72 (:REWRITE |(equal (/ x) c)|))
     (72 72 (:REWRITE |(equal (/ x) (/ y))|))
     (72 72 (:REWRITE |(equal (- x) c)|))
     (72 72 (:REWRITE |(equal (- x) (- y))|))
     (45 15 (:LINEAR SMAN::BYTEP-MI))
     (42 2 (:REWRITE SMAN::NTHCDR-IS-LAST))
     (27 18 (:REWRITE DEFAULT-LESS-THAN-2))
     (24 24 (:REWRITE REDUCE-RATIONALP-+))
     (24 24 (:REWRITE REDUCE-RATIONALP-*))
     (24 24 (:REWRITE REDUCE-INTEGERP-+))
     (24 24 (:REWRITE RATIONALP-MINUS-X))
     (24 24 (:REWRITE INTEGERP-MINUS-X))
     (24 24 (:META META-RATIONALP-CORRECT))
     (24 24 (:META META-INTEGERP-CORRECT))
     (24 15
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (24 15 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (20 10 (:TYPE-PRESCRIPTION SMAN::NATP-I))
     (18 18 (:REWRITE THE-FLOOR-BELOW))
     (18 18 (:REWRITE THE-FLOOR-ABOVE))
     (18 18
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (18 18
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (18 18
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (18 18 (:REWRITE INTEGERP-<-CONSTANT))
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
     (18 18 (:REWRITE |(< 0 (/ x))|))
     (18 18 (:REWRITE |(< 0 (* x y))|))
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
     (15 15
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (15 15
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (15 15 (:REWRITE SIMPLIFY-SUMS-<))
     (15 15 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (9 9 (:REWRITE |(equal (+ (- c) x) y)|))
     (8 4
        (:TYPE-PRESCRIPTION SMAN::NATP-NTH-MP))
     (5 5 (:REWRITE |(equal x (if a b c))|))
     (5 5 (:REWRITE |(equal (if a b c) x)|))
     (4 4 (:TYPE-PRESCRIPTION SMAN::MP))
     (2 2 (:REWRITE SMAN::NTHCDR-TO-END))
     (2 2 (:REWRITE |(+ x (if a b c))|)))
(SMAN::MI-!R-OVERLAP
 (319685 92 (:REWRITE SMAN::UNNECESSARY-MOD))
 (298328 298328
         (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (298328 298328
         (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (298328 298328
         (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (297426 13 (:REWRITE MOD-X-Y-=-X+Y . 1))
 (283866 3993 (:REWRITE THE-FLOOR-ABOVE))
 (276850 40 (:REWRITE FLOOR-=-X/Y . 4))
 (252709 13 (:REWRITE MOD-X-Y-=-X-Y . 1))
 (206542 90 (:REWRITE MOD-ZERO . 4))
 (194894 192 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (150967 87 (:REWRITE MOD-X-Y-=-X . 3))
 (150798 90 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (148346 1112 (:REWRITE SMAN::UNNECESSARY-FLOOR))
 (146582 90 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (143751 76 (:REWRITE |(equal (+ (- c) x) y)|))
 (140932 87 (:REWRITE MOD-X-Y-=-X . 4))
 (134779 13247
         (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (133063 13247
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (133063 13247
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (133063 13247
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (132280 15542 (:REWRITE DEFAULT-PLUS-2))
 (129202 12818
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (120465 15542 (:REWRITE DEFAULT-PLUS-1))
 (119463 26115 (:REWRITE DEFAULT-TIMES-1))
 (106348 237
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (103435 26115 (:REWRITE DEFAULT-TIMES-2))
 (95121 882 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (93647 253
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (92817 882 (:REWRITE FLOOR-ZERO . 3))
 (79812 882 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (78887 882 (:REWRITE FLOOR-ZERO . 4))
 (76232 1112 (:REWRITE DEFAULT-FLOOR-RATIO))
 (73185 13247
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (73185 13247
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (73185 13247
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (73185 13247
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (73185 13247
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (73185 13247
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (73185 13247
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (73185 13247
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
 (73185 13247
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (73185 13247
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (73049 882 (:REWRITE FLOOR-ZERO . 5))
 (71332 930 (:REWRITE FLOOR-=-X/Y . 2))
 (68422 12728
        (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (56786 484 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (42882 14789 (:REWRITE DEFAULT-MINUS))
 (39656 484 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (36425 210 (:REWRITE |(equal c (- x))|))
 (34815 3486 (:REWRITE DEFAULT-DIVIDE))
 (33016
  33016
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (33016
      33016
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (33016
     33016
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (33016 33016
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (30671 3476 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (28761 3562
        (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (26459 140 (:REWRITE |(integerp (- x))|))
 (20946 882 (:REWRITE FLOOR-ZERO . 2))
 (20946 882 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (20946 882 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (20492 3801
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (18329 1 (:REWRITE |(logand (if a b c) x)|))
 (17437 3993 (:REWRITE THE-FLOOR-BELOW))
 (16683 877 (:REWRITE FLOOR-CANCEL-*-CONST))
 (16026 92 (:REWRITE DEFAULT-MOD-RATIO))
 (15918 1112 (:REWRITE DEFAULT-FLOOR-1))
 (15627 3810 (:REWRITE DEFAULT-LESS-THAN-1))
 (15348 877
        (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (15337 866
        (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (13681 866
        (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (13064 3810 (:REWRITE DEFAULT-LESS-THAN-2))
 (12728 12728
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (12728 12728
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (12728 12728
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (8643 87 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (8643 87
       (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (8571 87 (:REWRITE MOD-X-Y-=-X . 2))
 (7068 1274 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (6968 1274
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (6791 1112 (:REWRITE DEFAULT-FLOOR-2))
 (5820 13 (:LINEAR MOD-BOUNDS-3))
 (5592 1274 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (4687 90 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (4687 90 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (4324 81 (:REWRITE MOD-CANCEL-*-CONST))
 (4235 3745
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (4229 92 (:REWRITE DEFAULT-MOD-1))
 (3570 3570 (:REWRITE INTEGERP-<-CONSTANT))
 (3570 3570 (:REWRITE CONSTANT-<-INTEGERP))
 (3570 3570
       (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (3570 3570
       (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (3570 3570
       (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (3570 3570
       (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (3570 3570 (:REWRITE |(< c (- x))|))
 (3570 3570
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (3570 3570
       (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (3570 3570
       (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (3570 3570
       (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (3570 3570 (:REWRITE |(< (/ x) (/ y))|))
 (3570 3570 (:REWRITE |(< (- x) c)|))
 (3570 3570 (:REWRITE |(< (- x) (- y))|))
 (3211 307 (:LINEAR EXPT-<=-1-TWO))
 (3163 307 (:LINEAR EXPT-<-1-TWO))
 (2762 2762
       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (2697 67
       (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (2656 877
       (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (2500 44 (:REWRITE FLOOR-POSITIVE . 2))
 (2500 44 (:REWRITE FLOOR-NONPOSITIVE . 1))
 (2419 2419 (:META META-INTEGERP-CORRECT))
 (2415 44 (:REWRITE FLOOR-POSITIVE . 3))
 (2298 44 (:REWRITE FLOOR-NONPOSITIVE . 2))
 (2287 64 (:REWRITE DEFAULT-LOGAND-2))
 (2254 2254 (:REWRITE |(< (* x y) 0)|))
 (2193 17 (:REWRITE |(integerp (expt x n))|))
 (2184 26 (:LINEAR MOD-BOUNDS-2))
 (2158 2158 (:REWRITE |(< (/ x) 0)|))
 (2155 2155
       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2155 2155
       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2092 82
       (:REWRITE |(floor (floor x y) z)| . 5))
 (1904 176 (:REWRITE |(< (+ (- c) x) y)|))
 (1580 35 (:REWRITE |(* c (* d x))|))
 (1474 866
       (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (1450 40
       (:REWRITE |(equal (floor (+ x y) z) x)|))
 (1389 44 (:REWRITE FLOOR-POSITIVE . 4))
 (1389 44 (:REWRITE FLOOR-NONPOSITIVE . 3))
 (1282 866
       (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (1274 1274
       (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (1274 1274
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (1238 761 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (1235 1235 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (1235 1235
       (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (1065 1065 (:REWRITE DEFAULT-EXPT-2))
 (1065 1065 (:REWRITE DEFAULT-EXPT-1))
 (1065 1065 (:REWRITE |(expt 1/c n)|))
 (1065 1065 (:REWRITE |(expt (- x) n)|))
 (1053 1053 (:TYPE-PRESCRIPTION ABS))
 (980 236 (:REWRITE |(< y (+ (- c) x))|))
 (866 866 (:REWRITE |(floor x (- y))| . 2))
 (866 866 (:REWRITE |(floor x (- y))| . 1))
 (866 866 (:REWRITE |(floor (- x) y)| . 2))
 (866 866 (:REWRITE |(floor (- x) y)| . 1))
 (770 5 (:REWRITE |(* -1 x)|))
 (733 733 (:REWRITE FOLD-CONSTS-IN-+))
 (683 65 (:REWRITE ACL2-NUMBERP-X))
 (622 82
      (:REWRITE |(floor (floor x y) z)| . 4))
 (622 82
      (:REWRITE |(floor (floor x y) z)| . 3))
 (622 82
      (:REWRITE |(floor (floor x y) z)| . 2))
 (621 21 (:REWRITE SMAN::MI-!R-))
 (614 614
      (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (614 614
      (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (614 614
      (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (614 614
      (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (610 610
      (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (590 590 (:REWRITE |(< 0 (* x y))|))
 (570 5 (:REWRITE |(floor (+ x r) i)|))
 (535 535 (:REWRITE |(< 0 (/ x))|))
 (534 534
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (534 534
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (427 31 (:REWRITE ZP-OPEN))
 (335 2 (:REWRITE |(* (if a b c) x)|))
 (309 24 (:REWRITE RATIONALP-X))
 (307 307 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (307 307 (:LINEAR EXPT-LINEAR-UPPER-<))
 (307 307 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (307 307 (:LINEAR EXPT-LINEAR-LOWER-<))
 (307 307 (:LINEAR EXPT->=-1-TWO))
 (307 307 (:LINEAR EXPT->-1-TWO))
 (307 307 (:LINEAR EXPT-<=-1-ONE))
 (307 307 (:LINEAR EXPT-<-1-ONE))
 (292 12
      (:REWRITE |(equal (mod (+ x y) z) x)|))
 (290 290 (:REWRITE |(< x (+ c/d y))|))
 (252 55 (:REWRITE SMAN::!R-R))
 (218 218 (:REWRITE |(< (+ c/d x) y)|))
 (214 214 (:REWRITE |(equal c (/ x))|))
 (214 214 (:REWRITE |(equal (/ x) (/ y))|))
 (214 214 (:REWRITE |(equal (- x) (- y))|))
 (205 205
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (205 205 (:REWRITE |(equal (- x) c)|))
 (199 9
      (:REWRITE |(< (* (/ x) y) 1) with (< 0 x)|))
 (195 30 (:LINEAR SMAN::BYTEP-MI))
 (187 67
      (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (164 92 (:REWRITE DEFAULT-MOD-2))
 (135 38 (:REWRITE SMAN::!MI-MI))
 (126 37 (:REWRITE SMAN::STP-!R))
 (120 120
      (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (112 80
      (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (108 36 (:REWRITE SMAN::STP-!MI))
 (104 104
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (104 9
      (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
 (99 67
     (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (67 67 (:REWRITE |(mod x (- y))| . 3))
 (67 67 (:REWRITE |(mod x (- y))| . 2))
 (67 67 (:REWRITE |(mod x (- y))| . 1))
 (67 67
     (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (67 67 (:REWRITE |(mod (- x) y)| . 3))
 (67 67 (:REWRITE |(mod (- x) y)| . 2))
 (67 67 (:REWRITE |(mod (- x) y)| . 1))
 (61 3
     (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (44 44 (:REWRITE FLOOR-POSITIVE . 1))
 (35 35 (:TYPE-PRESCRIPTION COLLECT-*))
 (28 28 (:TYPE-PRESCRIPTION RATIONALP-MOD))
 (26 1 (:REWRITE MOD-ZERO . 1))
 (25 25
     (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (24 24 (:REWRITE REDUCE-RATIONALP-+))
 (24 24 (:REWRITE REDUCE-RATIONALP-*))
 (24 24 (:REWRITE RATIONALP-MINUS-X))
 (24 24 (:META META-RATIONALP-CORRECT))
 (22 22 (:REWRITE FLOOR-ZERO . 1))
 (22 22 (:REWRITE |(mod (floor x y) z)| . 5))
 (22 22 (:REWRITE |(mod (floor x y) z)| . 4))
 (22 22 (:REWRITE |(mod (floor x y) z)| . 3))
 (22 22 (:REWRITE |(mod (floor x y) z)| . 2))
 (15 15 (:REWRITE |(equal (* x y) 0)|))
 (10 5 (:REWRITE COLLECT-*-PROBLEM-FINDER))
 (5 5
    (:TYPE-PRESCRIPTION FMT-TO-COMMENT-WINDOW))
 (5 5 (:REWRITE FLOOR-X-Y-=--1 . 1))
 (5 1 (:REWRITE MOD-ZERO . 2))
 (4 4 (:REWRITE |(not (equal x (/ y)))|))
 (4 4 (:REWRITE |(equal x (/ y))|))
 (3 3 (:REWRITE FLOOR-X-Y-=-1 . 1))
 (3 3
    (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (3 3 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (1 1
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX)))
(SMAN::ONE-BYTE-READ
 (26349 28 (:LINEAR LINEAR-FLOOR-BOUNDS-1))
 (11410 20 (:REWRITE MOD-ZERO . 4))
 (11161 241 (:REWRITE THE-FLOOR-ABOVE))
 (11060 21 (:REWRITE SMAN::UNNECESSARY-MOD))
 (9938 1728 (:REWRITE DEFAULT-TIMES-2))
 (9485 20 (:REWRITE MOD-X-Y-=-X . 3))
 (9454 20 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (9065 20 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (9006 20 (:REWRITE MOD-X-Y-=-X . 4))
 (8986 8986
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (8986 8986
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (8986 8986
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (8946 8946
       (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (6763 1573 (:REWRITE DEFAULT-PLUS-2))
 (6517
  6517
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (6517
      6517
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (6517
     6517
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (6517 6517
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (6361 1728 (:REWRITE DEFAULT-TIMES-1))
 (6129 1573 (:REWRITE DEFAULT-PLUS-1))
 (4552 352 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (4552 352
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (4552 352
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (4552 352
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (4552 352
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (4189 20 (:REWRITE MOD-ZERO . 3))
 (3773 4 (:REWRITE MOD-X-Y-=-X-Y . 1))
 (3755 37 (:REWRITE CANCEL-FLOOR-+))
 (3198 21 (:REWRITE DEFAULT-MOD-RATIO))
 (2823 21 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (2544 387 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (2508 387
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (2464 352 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (2464 352 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (2464 352
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (2464 352
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (2464 352
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (2464 352
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (2464 352
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (2464 352
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
 (2464 352
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (2464 352
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (2438 156 (:REWRITE INTEGERP-MINUS-X))
 (2432 11 (:REWRITE |(equal (+ (- c) x) y)|))
 (2407 4 (:REWRITE MOD-X-Y-=-X+Y . 1))
 (2279 37 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (2123 37 (:REWRITE FLOOR-ZERO . 3))
 (2080 738 (:REWRITE DEFAULT-MINUS))
 (2010 38 (:REWRITE DEFAULT-FLOOR-RATIO))
 (2003 37 (:REWRITE FLOOR-=-X/Y . 2))
 (1891 190 (:REWRITE DEFAULT-DIVIDE))
 (1811 35
       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (1806 14 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (1800 206 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (1563 387 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (1426 35 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (1094 226
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (1037 37 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (970 20 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (970 20
      (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (934 20 (:REWRITE MOD-X-Y-=-X . 2))
 (930 30 (:REWRITE |(integerp (- x))|))
 (925 37 (:REWRITE FLOOR-ZERO . 2))
 (925 37 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (925 37 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (904 347 (:TYPE-PRESCRIPTION SMAN::NATP-MI))
 (904 4 (:LINEAR MOD-BOUNDS-3))
 (879 241 (:REWRITE THE-FLOOR-BELOW))
 (816 233 (:REWRITE DEFAULT-LESS-THAN-2))
 (757 37 (:REWRITE FLOOR-ZERO . 5))
 (757 37 (:REWRITE FLOOR-ZERO . 4))
 (647 233 (:REWRITE DEFAULT-LESS-THAN-1))
 (601 601
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (559 232
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (547 37 (:REWRITE FLOOR-CANCEL-*-CONST))
 (531 20 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (531 20 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (494 19 (:REWRITE MOD-CANCEL-*-CONST))
 (476 197 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (476 197 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
 (472 37
      (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (472 37
      (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (472 37
      (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (460 4 (:REWRITE DEFAULT-LOGAND-2))
 (424 21 (:REWRITE DEFAULT-MOD-1))
 (402 14 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (387 387
      (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (387 387
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (386 386 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (386 386
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (383 20 (:REWRITE ODD-EXPT-THM))
 (380 38 (:REWRITE DEFAULT-FLOOR-2))
 (379 379 (:TYPE-PRESCRIPTION SMAN::STP))
 (308 38 (:REWRITE SMAN::UNNECESSARY-FLOOR))
 (288 288 (:REWRITE DEFAULT-EXPT-2))
 (288 288 (:REWRITE DEFAULT-EXPT-1))
 (288 288 (:REWRITE |(expt 1/c n)|))
 (288 288 (:REWRITE |(expt (- x) n)|))
 (232 232
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (226 226
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (226 226 (:REWRITE INTEGERP-<-CONSTANT))
 (226 226 (:REWRITE CONSTANT-<-INTEGERP))
 (226 226
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (226 226
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (226 226
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (226 226
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (226 226 (:REWRITE |(< c (- x))|))
 (226 226
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (226 226
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (226 226
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (226 226
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (226 226 (:REWRITE |(< (/ x) (/ y))|))
 (226 226 (:REWRITE |(< (- x) c)|))
 (226 226 (:REWRITE |(< (- x) (- y))|))
 (210 210 (:TYPE-PRESCRIPTION SMAN::!R))
 (197 197 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (180 171 (:REWRITE |(+ c (+ d x))|))
 (157 37
      (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (157 37
      (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (157 37
      (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (144 144 (:META META-INTEGERP-CORRECT))
 (139 16
      (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (132 14 (:REWRITE ACL2-NUMBERP-X))
 (123 123 (:REWRITE |(< (/ x) 0)|))
 (123 123 (:REWRITE |(< (* x y) 0)|))
 (122 122
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (122 122
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (116 116 (:REWRITE FOLD-CONSTS-IN-+))
 (108 12 (:REWRITE |(< (+ (- c) x) y)|))
 (80 8 (:LINEAR MOD-BOUNDS-2))
 (76 16
     (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (68 2 (:REWRITE FLOOR-POSITIVE . 3))
 (62 2 (:REWRITE FLOOR-POSITIVE . 2))
 (62 2 (:REWRITE FLOOR-NONPOSITIVE . 1))
 (59 5 (:REWRITE RATIONALP-X))
 (57 21 (:REWRITE DEFAULT-MOD-2))
 (51 37 (:REWRITE |(equal (/ x) c)|))
 (50 2 (:REWRITE FLOOR-POSITIVE . 4))
 (50 2 (:REWRITE FLOOR-NONPOSITIVE . 3))
 (50 2 (:REWRITE FLOOR-NONPOSITIVE . 2))
 (44 8 (:REWRITE |(- (- x))|))
 (43 43
     (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (40 40
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (40 40
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (38 38 (:REWRITE DEFAULT-FLOOR-1))
 (38 38 (:REWRITE |(< 0 (* x y))|))
 (37 37 (:REWRITE |(floor x (- y))| . 2))
 (37 37 (:REWRITE |(floor x (- y))| . 1))
 (37 37 (:REWRITE |(floor (- x) y)| . 2))
 (37 37 (:REWRITE |(floor (- x) y)| . 1))
 (37 37 (:REWRITE |(equal c (/ x))|))
 (37 37 (:REWRITE |(equal (/ x) (/ y))|))
 (37 37 (:REWRITE |(equal (- x) (- y))|))
 (36 36
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (36 36 (:REWRITE |(equal c (- x))|))
 (36 36 (:REWRITE |(equal (- x) c)|))
 (35 35
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (35 35
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (35 35 (:REWRITE |(< 0 (/ x))|))
 (32 2 (:REWRITE FLOOR-=-X/Y . 4))
 (32 2
     (:REWRITE |(equal (floor (+ x y) z) x)|))
 (30 5 (:LINEAR SMAN::BYTEP-MI))
 (30 3
     (:REWRITE |(equal (mod (+ x y) z) x)|))
 (29 29
     (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (28 28
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (28 28
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (28 28
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (28 28
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (22 22 (:REWRITE |(< x (+ c/d y))|))
 (21 21 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (21 21 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (21 21 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (21 21
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (19 19 (:REWRITE |(< y (+ (- c) x))|))
 (18 18
     (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (18 6 (:REWRITE SMAN::!R-R))
 (16 16
     (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (16 16 (:REWRITE |(mod x (- y))| . 3))
 (16 16 (:REWRITE |(mod x (- y))| . 2))
 (16 16 (:REWRITE |(mod x (- y))| . 1))
 (16 16
     (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (16 16 (:REWRITE |(mod (- x) y)| . 3))
 (16 16 (:REWRITE |(mod (- x) y)| . 2))
 (16 16 (:REWRITE |(mod (- x) y)| . 1))
 (16 16
     (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (15 5 (:REWRITE SMAN::STP-!R))
 (14 14
     (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (14 14 (:LINEAR EXPT-X->=-X))
 (14 14 (:LINEAR EXPT-X->-X))
 (14 14 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (14 14 (:LINEAR EXPT-LINEAR-UPPER-<))
 (14 14 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (14 14 (:LINEAR EXPT-LINEAR-LOWER-<))
 (14 14 (:LINEAR EXPT->=-1-TWO))
 (14 14 (:LINEAR EXPT->=-1-ONE))
 (14 14 (:LINEAR EXPT->-1-TWO))
 (14 14 (:LINEAR EXPT->-1-ONE))
 (14 14 (:LINEAR EXPT-<=-1-TWO))
 (14 14 (:LINEAR EXPT-<=-1-ONE))
 (14 14 (:LINEAR EXPT-<-1-TWO))
 (14 14 (:LINEAR EXPT-<-1-ONE))
 (12 12 (:REWRITE |(equal (* x y) 0)|))
 (12 12 (:REWRITE |(< (+ c/d x) y)|))
 (10 10 (:TYPE-PRESCRIPTION RATIONALP-MOD))
 (5 5 (:REWRITE REDUCE-RATIONALP-+))
 (5 5 (:REWRITE REDUCE-RATIONALP-*))
 (5 5 (:REWRITE RATIONALP-MINUS-X))
 (5 5 (:META META-RATIONALP-CORRECT))
 (4 4 (:REWRITE DEFAULT-LOGAND-1))
 (2 2 (:REWRITE FLOOR-ZERO . 1))
 (2 2 (:REWRITE FLOOR-POSITIVE . 1))
 (2 2 (:REWRITE |(mod (floor x y) z)| . 5))
 (2 2 (:REWRITE |(mod (floor x y) z)| . 4))
 (2 2 (:REWRITE |(mod (floor x y) z)| . 3))
 (2 2 (:REWRITE |(mod (floor x y) z)| . 2))
 (2 2 (:REWRITE |(* c (* d x))|))
 (1 1 (:REWRITE |(not (equal x (/ y)))|))
 (1 1 (:REWRITE |(equal x (/ y))|))
 (1 1 (:REWRITE |(/ (/ x))|)))
(SMAN::DEMO-THM--NO-DIVERGENCE
 (84108 84 (:LINEAR LINEAR-FLOOR-BOUNDS-1))
 (47454 19278
        (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (33868 352 (:REWRITE THE-FLOOR-ABOVE))
 (31980 12 (:REWRITE MOD-ZERO . 4))
 (30078 12 (:REWRITE SMAN::UNNECESSARY-MOD))
 (24864 12 (:REWRITE MOD-X-Y-=-X . 3))
 (24630 12 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (23994 12 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (23286 12 (:REWRITE MOD-X-Y-=-X . 4))
 (19278 19278
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (19278 19278
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (19278 19278
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (19194 19194
        (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (14490 1854 (:REWRITE DEFAULT-TIMES-2))
 (13905 1419 (:REWRITE DEFAULT-PLUS-1))
 (13869 1419 (:REWRITE DEFAULT-PLUS-2))
 (13086 12 (:REWRITE CANCEL-MOD-+))
 (12606 102 (:REWRITE CANCEL-FLOOR-+))
 (10686 822 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (10686 822
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (10686 822
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (10686 822
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (10686 822
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (8274 66 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (6840 672 (:REWRITE |(* (- x) y)|))
 (6828 102 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (6684 102 (:REWRITE FLOOR-ZERO . 3))
 (6680
  6680
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (6680
      6680
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (6680
     6680
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (6680 6680
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (6680 6680
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (6312 102 (:REWRITE FLOOR-=-X/Y . 2))
 (5808 102 (:REWRITE DEFAULT-FLOOR-RATIO))
 (5754 822 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (5754 822 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (5754 822
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (5754 822
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (5754 822
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (5754 822
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (5754 822
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (5754 822
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
 (5754 822
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (5754 822
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (5676 1854 (:REWRITE DEFAULT-TIMES-1))
 (5454 1752 (:REWRITE DEFAULT-MINUS))
 (5352 12 (:REWRITE MOD-ZERO . 3))
 (5160 516 (:REWRITE DEFAULT-DIVIDE))
 (4909 211 (:REWRITE INTEGERP-MINUS-X))
 (4512 102 (:REWRITE FLOOR-=-X/Y . 3))
 (3696 48 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (3192 12 (:REWRITE DEFAULT-MOD-RATIO))
 (3162 102 (:REWRITE |(integerp (- x))|))
 (3102 102 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (3072 5 (:REWRITE SMAN::!R-R))
 (2550 102 (:REWRITE FLOOR-ZERO . 2))
 (2550 102 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (2550 102 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (2266 352 (:REWRITE THE-FLOOR-BELOW))
 (2262 102 (:REWRITE FLOOR-ZERO . 5))
 (2262 102 (:REWRITE FLOOR-ZERO . 4))
 (2088 42 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (2058 12 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (2058 12
       (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (2004 12 (:REWRITE MOD-X-Y-=-X . 2))
 (1836 12 (:REWRITE DEFAULT-LOGAND-2))
 (1666 322
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (1632 102 (:REWRITE FLOOR-CANCEL-*-CONST))
 (1564 328 (:REWRITE DEFAULT-LESS-THAN-2))
 (1458 42 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (1362 102
       (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (1362 102
       (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (1362 102
       (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (1092 12 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (1092 12 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (1072 20 (:LINEAR SMAN::R-BOUND))
 (1038 12
       (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (1038 12 (:REWRITE MOD-CANCEL-*-CONST))
 (1020 102 (:REWRITE DEFAULT-FLOOR-2))
 (956 17
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (932 17
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (924 12 (:REWRITE DEFAULT-MOD-1))
 (822 102 (:REWRITE SMAN::UNNECESSARY-FLOOR))
 (760 328 (:REWRITE DEFAULT-LESS-THAN-1))
 (687 687
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (640 316 (:REWRITE SIMPLIFY-SUMS-<))
 (574 574 (:REWRITE DEFAULT-EXPT-2))
 (574 574 (:REWRITE DEFAULT-EXPT-1))
 (574 574 (:REWRITE |(expt 1/c n)|))
 (574 574 (:REWRITE |(expt (- x) n)|))
 (463 15 (:REWRITE SMAN::R-!R-DIFF-BELOW))
 (463 15 (:REWRITE SMAN::R-!R-DIFF-ABOVE))
 (372 102
      (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (372 102
      (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (372 102
      (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (346 46 (:LINEAR EXPT-<=-1-TWO))
 (336 46 (:LINEAR EXPT->-1-ONE))
 (322 322
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (322 322
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (322 322
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (322 322 (:REWRITE INTEGERP-<-CONSTANT))
 (322 322 (:REWRITE CONSTANT-<-INTEGERP))
 (322 322
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (322 322
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (322 322
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (322 322
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (322 322 (:REWRITE |(< c (- x))|))
 (322 322
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (322 322
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (322 322
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (322 322
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (322 322 (:REWRITE |(< (/ x) (/ y))|))
 (322 322 (:REWRITE |(< (- x) c)|))
 (322 322 (:REWRITE |(< (- x) (- y))|))
 (296 46 (:LINEAR EXPT-X->=-X))
 (296 46 (:LINEAR EXPT-X->-X))
 (256 256 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (222 92
      (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (205 205 (:REWRITE REDUCE-INTEGERP-+))
 (205 205 (:META META-INTEGERP-CORRECT))
 (204 102
      (:TYPE-PRESCRIPTION SMAN::NATP-NTH-MP))
 (204 6 (:REWRITE FLOOR-POSITIVE . 3))
 (186 6 (:REWRITE FLOOR-POSITIVE . 2))
 (186 6 (:REWRITE FLOOR-NONPOSITIVE . 1))
 (176 46 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (176 46 (:LINEAR EXPT->=-1-ONE))
 (150 6 (:REWRITE FLOOR-POSITIVE . 4))
 (150 6 (:REWRITE FLOOR-NONPOSITIVE . 3))
 (150 6 (:REWRITE FLOOR-NONPOSITIVE . 2))
 (148 148 (:REWRITE |(< (/ x) 0)|))
 (148 148 (:REWRITE |(< (* x y) 0)|))
 (142 142
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (142 142
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (102 102 (:REWRITE DEFAULT-FLOOR-1))
 (102 102 (:REWRITE |(floor x (- y))| . 2))
 (102 102 (:REWRITE |(floor x (- y))| . 1))
 (102 102 (:REWRITE |(floor (- x) y)| . 2))
 (102 102 (:REWRITE |(floor (- x) y)| . 1))
 (96 6 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (96 6 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (96 6 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (96 6 (:REWRITE FLOOR-=-X/Y . 4))
 (96 6
     (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (96 6
     (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (96 6
     (:REWRITE |(equal (floor (+ x y) z) x)|))
 (92 92
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (92 92
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (92 92
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (70 70 (:TYPE-PRESCRIPTION SMAN::R))
 (66 66 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (66 66 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (66 66 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (66 66 (:REWRITE |(+ c (+ d x))|))
 (66 12 (:REWRITE DEFAULT-MOD-2))
 (60 60 (:REWRITE FOLD-CONSTS-IN-+))
 (60 6 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
 (56 56
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (56 56
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (56 56 (:REWRITE |(< 0 (/ x))|))
 (56 56 (:REWRITE |(< 0 (* x y))|))
 (48 48
     (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (46 46 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (46 46 (:LINEAR EXPT-LINEAR-UPPER-<))
 (46 46 (:LINEAR EXPT-LINEAR-LOWER-<))
 (46 46 (:LINEAR EXPT->=-1-TWO))
 (46 46 (:LINEAR EXPT->-1-TWO))
 (46 46 (:LINEAR EXPT-<=-1-ONE))
 (46 46 (:LINEAR EXPT-<-1-TWO))
 (46 46 (:LINEAR EXPT-<-1-ONE))
 (42 6 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (40 40 (:REWRITE |(< y (+ (- c) x))|))
 (40 40 (:REWRITE |(< x (+ c/d y))|))
 (36 36 (:REWRITE ODD-EXPT-THM))
 (33 9 (:REWRITE ACL2-NUMBERP-X))
 (33 1 (:REWRITE SMAN::!R-!R-DIFF-BELOW))
 (33 1 (:REWRITE SMAN::!R-!R-DIFF-ABOVE))
 (24 24 (:REWRITE |(+ x (- x))|))
 (20 17 (:REWRITE SIMPLIFY-SUMS-EQUAL))
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
 (12 12
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (12 12
     (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (12 12 (:REWRITE DEFAULT-LOGAND-1))
 (12 3 (:REWRITE RATIONALP-X))
 (6 6 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (6 6 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (6 6 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (6 6 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
 (6 6 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (6 6 (:TYPE-PRESCRIPTION INTEGERP-MOD-3))
 (6 6 (:REWRITE FLOOR-ZERO . 1))
 (6 6 (:REWRITE FLOOR-POSITIVE . 1))
 (6 6 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
 (6 6 (:REWRITE |(mod x (- y))| . 3))
 (6 6 (:REWRITE |(mod x (- y))| . 2))
 (6 6 (:REWRITE |(mod x (- y))| . 1))
 (6 6
    (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (6 6 (:REWRITE |(mod (floor x y) z)| . 5))
 (6 6 (:REWRITE |(mod (floor x y) z)| . 4))
 (6 6 (:REWRITE |(mod (floor x y) z)| . 3))
 (6 6 (:REWRITE |(mod (floor x y) z)| . 2))
 (6 6 (:REWRITE |(mod (- x) y)| . 3))
 (6 6 (:REWRITE |(mod (- x) y)| . 2))
 (6 6 (:REWRITE |(mod (- x) y)| . 1))
 (6 6
    (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (6 6 (:REWRITE |(< (+ c/d x) y)|))
 (6 6 (:REWRITE |(< (+ (- c) x) y)|))
 (5 4 (:REWRITE SMAN::STP-!R))
 (3 3 (:REWRITE REDUCE-RATIONALP-+))
 (3 3 (:REWRITE REDUCE-RATIONALP-*))
 (3 3 (:REWRITE RATIONALP-MINUS-X))
 (3 3 (:META META-RATIONALP-CORRECT))
 (3 1 (:LINEAR SMAN::BYTEP-NTH-MP)))
(SMAN::STP-IMPLIES-WEAK-STP
     (34 34 (:REWRITE DEFAULT-CDR))
     (28 14 (:REWRITE DEFAULT-PLUS-2))
     (24 12
         (:TYPE-PRESCRIPTION SMAN::NATP-NTH-MP))
     (14 14 (:REWRITE DEFAULT-PLUS-1))
     (12 12
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (12 12 (:REWRITE NORMALIZE-ADDENDS))
     (6 6 (:REWRITE DEFAULT-CAR))
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
     (1 1 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (1 1 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (1 1 (:REWRITE INTEGERP-MINUS-X))
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
     (1 1 (:REWRITE |(< (* x y) 0)|))
     (1 1 (:META META-INTEGERP-CORRECT)))
(SMAN::WEAK-ML-!MI
     (102 2 (:REWRITE SMAN::!NTH-NTH))
     (70 1 (:DEFINITION UPDATE-NTH))
     (41 1 (:REWRITE |(< (+ (- c) x) y)|))
     (28 4 (:DEFINITION LEN))
     (16 16 (:REWRITE DEFAULT-CDR))
     (13 8 (:REWRITE DEFAULT-PLUS-2))
     (10 7 (:REWRITE DEFAULT-LESS-THAN-2))
     (9 7 (:REWRITE DEFAULT-LESS-THAN-1))
     (9 5 (:REWRITE SIMPLIFY-SUMS-<))
     (9 5
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (9 5 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (8 8
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (8 8 (:REWRITE NORMALIZE-ADDENDS))
     (8 8 (:REWRITE DEFAULT-PLUS-1))
     (7 7 (:REWRITE THE-FLOOR-BELOW))
     (7 7 (:REWRITE THE-FLOOR-ABOVE))
     (7 7
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (7 7
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (7 7 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (6 6 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (6 6 (:REWRITE INTEGERP-<-CONSTANT))
     (6 6 (:REWRITE DEFAULT-CAR))
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
     (3 3 (:REWRITE |(< y (+ (- c) x))|))
     (3 3 (:REWRITE |(< x (+ c/d y))|))
     (2 2 (:REWRITE |(< (/ x) 0)|))
     (2 2 (:REWRITE |(< (* x y) 0)|))
     (1 1 (:REWRITE ZP-OPEN))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (1 1 (:REWRITE REDUCE-INTEGERP-+))
     (1 1 (:REWRITE INTEGERP-MINUS-X))
     (1 1 (:REWRITE |(< (+ c/d x) y)|))
     (1 1 (:META META-INTEGERP-CORRECT)))
(SMAN::WEAK-ML-!R
 (43801 106 (:LINEAR LINEAR-FLOOR-BOUNDS-1))
 (35444 26804
        (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (30426 811 (:REWRITE THE-FLOOR-ABOVE))
 (26804 26804
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (26804 26804
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (26804 26804
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (19295 7 (:REWRITE SMAN::!NTH-!NTH-DIFF))
 (18329 1 (:REWRITE |(logand (if a b c) x)|))
 (16014 1 (:REWRITE |(floor (if a b c) x)|))
 (14383 155 (:REWRITE SMAN::UNNECESSARY-FLOOR))
 (13877 112 (:REWRITE SMAN::!NTH-NTH))
 (13208 2447
        (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (12830 154 (:REWRITE CANCEL-FLOOR-+))
 (12589 56 (:DEFINITION UPDATE-NTH))
 (12513 746 (:REWRITE DEFAULT-PLUS-2))
 (12340 746 (:REWRITE DEFAULT-PLUS-1))
 (11703 154 (:REWRITE FLOOR-ZERO . 3))
 (11190 34 (:REWRITE SMAN::UNNECESSARY-MOD))
 (10512 154 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (10396 34 (:REWRITE MOD-ZERO . 4))
 (10344 154 (:REWRITE FLOOR-ZERO . 4))
 (10293 154 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (10161 1129
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (10161 1129
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (10161 1129
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (10161 1129
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (10161 1129
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (9738 34 (:REWRITE MOD-X-Y-=-X . 3))
 (9300 34 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (9262 154 (:REWRITE FLOOR-ZERO . 5))
 (9245 2308 (:REWRITE DEFAULT-TIMES-2))
 (9210 34 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (8821 577 (:REWRITE INTEGERP-MINUS-X))
 (8656 34 (:REWRITE MOD-X-Y-=-X . 4))
 (7054 34 (:REWRITE CANCEL-MOD-+))
 (6729 849 (:REWRITE |(* y x)|))
 (6550 2308 (:REWRITE DEFAULT-TIMES-1))
 (6392 388 (:REWRITE |(* (- x) y)|))
 (5816 4 (:REWRITE |(mod (floor x y) z)| . 1))
 (5645 1129
       (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
 (5645 1129
       (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (5645 1129
       (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (5645 1129
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (5645 1129
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (5645 1129
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (5645 1129
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (5645 1129
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (5645 1129
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
 (5645 1129
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (5645 1129
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (4830 35
       (:TYPE-PRESCRIPTION TRUE-LISTP-UPDATE-NTH))
 (4197 154 (:REWRITE FLOOR-=-X/Y . 2))
 (3856 380 (:REWRITE DEFAULT-MINUS))
 (3732 380 (:REWRITE |(- (* c x))|))
 (3717 154 (:REWRITE FLOOR-=-X/Y . 3))
 (3372 39 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (3276 155 (:REWRITE DEFAULT-FLOOR-RATIO))
 (2768 34 (:REWRITE MOD-ZERO . 3))
 (2459 811 (:REWRITE THE-FLOOR-BELOW))
 (2447 2447
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (2447 2447
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (2447 2447
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (2363 1 (:REWRITE |(< (if a b c) x)|))
 (2326 687
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (1896 72 (:REWRITE |(< (+ (- c) x) y)|))
 (1778 778 (:REWRITE DEFAULT-LESS-THAN-2))
 (1639 778 (:REWRITE DEFAULT-LESS-THAN-1))
 (1586 34 (:REWRITE DEFAULT-MOD-RATIO))
 (1261 1261
       (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (1250 687
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (1228 219 (:REWRITE DEFAULT-CAR))
 (1218 762
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (1174 154 (:REWRITE FLOOR-ZERO . 2))
 (1174 154 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (1174 154 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (1129 1129 (:TYPE-PRESCRIPTION FLOOR))
 (1126 154 (:REWRITE FLOOR-CANCEL-*-CONST))
 (978 34 (:REWRITE MOD-X-Y-=-X . 2))
 (978 34 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (978 34
      (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (840 753
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (813 753
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (718 154
      (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (706 4
      (:REWRITE |(floor (floor x y) z)| . 1))
 (704 704
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (704 704 (:REWRITE INTEGERP-<-CONSTANT))
 (704 704 (:REWRITE CONSTANT-<-INTEGERP))
 (704 704
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (704 704
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (704 704
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (704 704
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (704 704 (:REWRITE |(< c (- x))|))
 (704 704
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (704 704
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (704 704
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (704 704
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (704 704 (:REWRITE |(< (/ x) (/ y))|))
 (704 704 (:REWRITE |(< (- x) c)|))
 (704 704 (:REWRITE |(< (- x) (- y))|))
 (660 155 (:REWRITE DEFAULT-FLOOR-1))
 (630 53 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (610 154
      (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (606 150
      (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (574 34 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (574 34 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (574 34 (:REWRITE MOD-CANCEL-*-CONST))
 (558 34
      (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (472 53
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (472 53
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (467 63 (:REWRITE DEFAULT-LOGAND-2))
 (447 447
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (438 34 (:REWRITE DEFAULT-MOD-1))
 (418 53 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (389 389 (:REWRITE REDUCE-INTEGERP-+))
 (389 389 (:META META-INTEGERP-CORRECT))
 (383 383 (:REWRITE |(< (* x y) 0)|))
 (372 372 (:REWRITE |(< (/ x) 0)|))
 (355 355
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (355 355
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (294 150
      (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (209 1 (:REWRITE |(* (if a b c) x)|))
 (183 183 (:TYPE-PRESCRIPTION ABS))
 (164 164 (:TYPE-PRESCRIPTION SMAN::STP))
 (160 32 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (160 32 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (160 32
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (160 32
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (155 155 (:REWRITE DEFAULT-FLOOR-2))
 (150 150 (:REWRITE |(floor x (- y))| . 2))
 (150 150 (:REWRITE |(floor x (- y))| . 1))
 (150 150
      (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (150 150
      (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (150 150 (:REWRITE |(floor (- x) y)| . 2))
 (150 150 (:REWRITE |(floor (- x) y)| . 1))
 (150 50 (:REWRITE SMAN::!R-R))
 (134 30
      (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (105 7 (:REWRITE |(+ x (if a b c))|))
 (96 32 (:REWRITE SMAN::!MI-MI))
 (89 89
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (89 89
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (89 89 (:REWRITE |(< 0 (/ x))|))
 (89 89 (:REWRITE |(< 0 (* x y))|))
 (88 88
     (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (79 79 (:REWRITE |(< y (+ (- c) x))|))
 (79 79 (:REWRITE |(< x (+ c/d y))|))
 (74 74 (:REWRITE |(< (+ c/d x) y)|))
 (72 8 (:REWRITE FLOOR-POSITIVE . 2))
 (72 8 (:REWRITE FLOOR-NONPOSITIVE . 1))
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
 (50 34
     (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (46 30
     (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (40 8 (:REWRITE FLOOR-POSITIVE . 4))
 (40 8 (:REWRITE FLOOR-POSITIVE . 3))
 (40 8 (:REWRITE FLOOR-NONPOSITIVE . 3))
 (40 8 (:REWRITE FLOOR-NONPOSITIVE . 2))
 (35 35 (:TYPE-PRESCRIPTION UPDATE-NTH))
 (35 35 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (34 34
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (34 34 (:REWRITE DEFAULT-MOD-2))
 (32 32 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
 (32 32 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (32 32
     (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (32 32 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (32 32 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
 (32 32
     (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (32 32 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (32 32 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
 (30 30 (:REWRITE |(mod x (- y))| . 3))
 (30 30 (:REWRITE |(mod x (- y))| . 2))
 (30 30 (:REWRITE |(mod x (- y))| . 1))
 (30 30
     (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (30 30
     (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (30 30 (:REWRITE |(mod (- x) y)| . 3))
 (30 30 (:REWRITE |(mod (- x) y)| . 2))
 (30 30 (:REWRITE |(mod (- x) y)| . 1))
 (22
   22
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (22
  22
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (22 22
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (22 22
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (22 22
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (22 22
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (20 4 (:REWRITE FLOOR-=-X/Y . 4))
 (20 4
     (:REWRITE |(equal (floor (+ x y) z) x)|))
 (14 14 (:REWRITE |(equal (+ (- c) x) y)|))
 (9 9 (:REWRITE |(* a (/ a) b)|))
 (8 8 (:REWRITE FLOOR-POSITIVE . 1))
 (4 4 (:REWRITE FLOOR-ZERO . 1))
 (4 4 (:REWRITE |(mod (floor x y) z)| . 5))
 (4 4 (:REWRITE |(mod (floor x y) z)| . 4))
 (4 4 (:REWRITE |(mod (floor x y) z)| . 3))
 (4 4 (:REWRITE |(mod (floor x y) z)| . 2))
 (4 4
    (:REWRITE |(floor (floor x y) z)| . 5))
 (4 4
    (:REWRITE |(floor (floor x y) z)| . 4))
 (4 4
    (:REWRITE |(floor (floor x y) z)| . 3))
 (4 4
    (:REWRITE |(floor (floor x y) z)| . 2))
 (1 1 (:REWRITE FOLD-CONSTS-IN-+))
 (1 1 (:REWRITE |(equal x (if a b c))|)))
(SMAN::DEMO-THM
     (2160 2 (:LINEAR SMAN::DIVERGENT-ADDR-LEGAL))
     (1182 42 (:REWRITE SMAN::!R-R))
     (1124 2 (:REWRITE SMAN::MI-!R-))
     (1117 2 (:REWRITE SMAN::MI-!R+))
     (456 228
          (:TYPE-PRESCRIPTION SMAN::NATP-NTH-MP))
     (338 2 (:DEFINITION MIN))
     (268 12 (:REWRITE SMAN::R-!R-DIFF-BELOW))
     (268 12 (:REWRITE SMAN::R-!R-DIFF-ABOVE))
     (228 204 (:REWRITE DEFAULT-PLUS-1))
     (204 204 (:REWRITE DEFAULT-PLUS-2))
     (178 110 (:REWRITE DEFAULT-LESS-THAN-2))
     (178 24
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (138 110 (:REWRITE DEFAULT-LESS-THAN-1))
     (138 87 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (136 8 (:REWRITE SMAN::!R-!R-DIFF-BELOW))
     (136 8 (:REWRITE SMAN::!R-!R-DIFF-ABOVE))
     (132 36 (:REWRITE ACL2-NUMBERP-X))
     (110 110 (:REWRITE THE-FLOOR-BELOW))
     (110 110 (:REWRITE THE-FLOOR-ABOVE))
     (98 98
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (98 98
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (98 98
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (95 95
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (95 95 (:REWRITE INTEGERP-<-CONSTANT))
     (95 95 (:REWRITE CONSTANT-<-INTEGERP))
     (95 95
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (95 95
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (95 95
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (95 95
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (95 95 (:REWRITE |(< c (- x))|))
     (95 95
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (95 95
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (95 95
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (95 95
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (95 95 (:REWRITE |(< (/ x) (/ y))|))
     (95 95 (:REWRITE |(< (- x) c)|))
     (95 95 (:REWRITE |(< (- x) (- y))|))
     (84 4 (:TYPE-PRESCRIPTION MIN))
     (82 24 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (80 80 (:TYPE-PRESCRIPTION SMAN::R))
     (72 72
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (62 24
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (48 12 (:REWRITE RATIONALP-X))
     (41 41 (:REWRITE |(< y (+ (- c) x))|))
     (41 41 (:REWRITE |(< x (+ c/d y))|))
     (30 30 (:REWRITE |(< (+ c/d x) y)|))
     (30 30 (:REWRITE |(< (+ (- c) x) y)|))
     (24 24 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
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
     (21 21 (:REWRITE |(< (/ x) 0)|))
     (21 21 (:REWRITE |(< (* x y) 0)|))
     (16 16
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (16 16
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (16 16 (:REWRITE REDUCE-INTEGERP-+))
     (16 16 (:REWRITE INTEGERP-MINUS-X))
     (16 16 (:META META-INTEGERP-CORRECT))
     (14 4 (:REWRITE DEFAULT-CDR))
     (14 4 (:REWRITE DEFAULT-CAR))
     (12 12 (:REWRITE REDUCE-RATIONALP-+))
     (12 12 (:REWRITE REDUCE-RATIONALP-*))
     (12 12 (:REWRITE RATIONALP-MINUS-X))
     (12 12 (:REWRITE DEFAULT-TIMES-2))
     (12 12 (:REWRITE DEFAULT-TIMES-1))
     (12 12 (:META META-RATIONALP-CORRECT))
     (9 2 (:TYPE-PRESCRIPTION SMAN::NATP-I))
     (6 6 (:REWRITE ZP-OPEN))
     (6 6 (:REWRITE |(+ c (+ d x))|))
     (3 3
        (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (3 3
        (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (3 3 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (3 3 (:REWRITE |(< 0 (* x y))|))
     (3 1 (:LINEAR SMAN::BYTEP-NTH-MP))
     (2 2 (:REWRITE |(equal x (if a b c))|))
     (2 2 (:REWRITE |(equal (if a b c) x)|))
     (2 2 (:REWRITE |(< (if a b c) x)|)))
(SMAN::!MI-DEFAULT-1
     (28 28 (:REWRITE DEFAULT-CDR))
     (12 12 (:REWRITE DEFAULT-CAR))
     (5 2 (:REWRITE SMAN::!NTH-NTH))
     (2 2 (:REWRITE REDUCE-INTEGERP-+))
     (2 2 (:REWRITE INTEGERP-MINUS-X))
     (2 2 (:META META-INTEGERP-CORRECT))
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
(SMAN::!R-DEFAULT-1-NON-NUMBER
 (36658 2 (:REWRITE |(logand (if a b c) x)|))
 (32028 2 (:REWRITE |(floor (if a b c) x)|))
 (23708 56 (:LINEAR LINEAR-FLOOR-BOUNDS-1))
 (17516 13196
        (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (16369 207 (:REWRITE THE-FLOOR-ABOVE))
 (13196 13196
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (13196 13196
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (13196 13196
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (11294 70 (:REWRITE SMAN::UNNECESSARY-FLOOR))
 (9738 64 (:REWRITE |(+ y x)|))
 (6308 1056
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (6014 156 (:REWRITE DEFAULT-PLUS-1))
 (5998 68 (:REWRITE CANCEL-FLOOR-+))
 (5616 54 (:REWRITE NORMALIZE-ADDENDS))
 (5418 68 (:REWRITE FLOOR-ZERO . 3))
 (5316 8 (:REWRITE SMAN::UNNECESSARY-MOD))
 (5112 568 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (5112 568
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (5112 568
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (5112 568
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (5112 568
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (5044 68 (:REWRITE FLOOR-ZERO . 4))
 (5036 8 (:REWRITE MOD-ZERO . 4))
 (5022 68 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (5022 68 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (4726 2 (:REWRITE |(< (if a b c) x)|))
 (4554 8 (:REWRITE MOD-X-Y-=-X . 3))
 (4402 68 (:REWRITE FLOOR-ZERO . 5))
 (4344 8 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (4326 8 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (4084 974 (:REWRITE DEFAULT-TIMES-2))
 (3982 234 (:REWRITE INTEGERP-MINUS-X))
 (3912 8 (:REWRITE MOD-X-Y-=-X . 4))
 (3398 974 (:REWRITE DEFAULT-TIMES-1))
 (3282 366 (:REWRITE |(* y x)|))
 (3050 8 (:REWRITE CANCEL-MOD-+))
 (2914 2 (:REWRITE |(mod (floor x y) z)| . 1))
 (2902 154 (:REWRITE |(* (- x) y)|))
 (2840 568 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
 (2840 568 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (2840 568 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (2840 568
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (2840 568
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (2840 568
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (2840 568
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (2840 568
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (2840 568
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
 (2840 568
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (2840 568
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (2182 70 (:REWRITE DEFAULT-FLOOR-RATIO))
 (1992 68 (:REWRITE FLOOR-=-X/Y . 2))
 (1836 18 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (1836 18 (:DEFINITION FIX))
 (1764 154 (:REWRITE DEFAULT-MINUS))
 (1736 68 (:REWRITE FLOOR-=-X/Y . 3))
 (1704 154 (:REWRITE |(- (* c x))|))
 (1186 8 (:REWRITE MOD-ZERO . 3))
 (1056 1056
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (1056 1056
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (1056 1056
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (1031 207 (:REWRITE THE-FLOOR-BELOW))
 (922 180
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (758 2
      (:REWRITE |(floor (floor x y) z)| . 1))
 (753 189 (:REWRITE DEFAULT-LESS-THAN-1))
 (694 8 (:REWRITE DEFAULT-MOD-RATIO))
 (593 189 (:REWRITE DEFAULT-LESS-THAN-2))
 (568 568 (:TYPE-PRESCRIPTION FLOOR))
 (542 68 (:REWRITE FLOOR-ZERO . 2))
 (542 68 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (542 68 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (542 68 (:REWRITE FLOOR-CANCEL-*-CONST))
 (524 524
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (474 70 (:REWRITE DEFAULT-FLOOR-1))
 (469 187
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (444 8 (:REWRITE MOD-X-Y-=-X . 2))
 (444 8 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (444 8
      (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (418 2 (:REWRITE |(* (if a b c) x)|))
 (354 28 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (318 68
      (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (292 68
      (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (290 66
      (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (242 28 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (242 8 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (242 8 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (242 8
      (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (242 8 (:REWRITE MOD-CANCEL-*-CONST))
 (220 18 (:REWRITE DEFAULT-LOGAND-2))
 (217 181
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (210 8
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (210 8
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (210 8 (:REWRITE DEFAULT-MOD-1))
 (196 180
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (181 181
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (181 181
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (181 181 (:REWRITE INTEGERP-<-CONSTANT))
 (181 181 (:REWRITE CONSTANT-<-INTEGERP))
 (181 181
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (181 181
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (181 181
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (181 181
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (181 181 (:REWRITE |(< c (- x))|))
 (181 181
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (181 181
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (181 181
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (181 181
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (181 181 (:REWRITE |(< (/ x) (/ y))|))
 (181 181 (:REWRITE |(< (- x) c)|))
 (181 181 (:REWRITE |(< (- x) (- y))|))
 (180 180 (:REWRITE SIMPLIFY-SUMS-<))
 (158 158 (:REWRITE REDUCE-INTEGERP-+))
 (158 158 (:META META-INTEGERP-CORRECT))
 (123 123 (:REWRITE |(< (* x y) 0)|))
 (117 117 (:REWRITE |(< (/ x) 0)|))
 (116 116
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (116 116
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (109 109 (:TYPE-PRESCRIPTION SMAN::!R))
 (106 66
      (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (90 18 (:REWRITE |(+ 0 x)|))
 (78 78 (:TYPE-PRESCRIPTION ABS))
 (70 70 (:REWRITE DEFAULT-FLOOR-2))
 (69 3 (:REWRITE ZP-OPEN))
 (66 66 (:REWRITE |(floor x (- y))| . 2))
 (66 66 (:REWRITE |(floor x (- y))| . 1))
 (66 66
     (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (66 66
     (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (66 66 (:REWRITE |(floor (- x) y)| . 2))
 (66 66 (:REWRITE |(floor (- x) y)| . 1))
 (38 38
     (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (36 36
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (36 18 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
 (36 12 (:REWRITE SMAN::!R-R))
 (36 4 (:REWRITE FLOOR-POSITIVE . 2))
 (36 4 (:REWRITE FLOOR-NONPOSITIVE . 1))
 (32 32 (:TYPE-PRESCRIPTION SMAN::STP))
 (32 32
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (32 32
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (32 32 (:REWRITE |(< 0 (/ x))|))
 (32 32 (:REWRITE |(< 0 (* x y))|))
 (30 6
     (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (21 8 (:REWRITE SMAN::!MI-MI))
 (20 4 (:REWRITE FLOOR-POSITIVE . 4))
 (20 4 (:REWRITE FLOOR-POSITIVE . 3))
 (20 4 (:REWRITE FLOOR-NONPOSITIVE . 3))
 (20 4 (:REWRITE FLOOR-NONPOSITIVE . 2))
 (18 18 (:REWRITE |(+ x (- x))|))
 (18 2 (:REWRITE ACL2-NUMBERP-X))
 (12 4 (:REWRITE SMAN::STP-!MI))
 (10 2 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (10 2 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (10 2 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (10 2 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (10 2 (:REWRITE FLOOR-=-X/Y . 4))
 (10 2
     (:REWRITE |(equal (floor (+ x y) z) x)|))
 (10 2 (:REWRITE |(+ c (+ d x))|))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (8 8 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (8 8
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (8 8
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (8 8
    (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (8 8
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (8 8 (:REWRITE DEFAULT-MOD-2))
 (8 8 (:REWRITE |(equal c (/ x))|))
 (8 8 (:REWRITE |(equal c (- x))|))
 (8 8 (:REWRITE |(equal (/ x) c)|))
 (8 8 (:REWRITE |(equal (/ x) (/ y))|))
 (8 8 (:REWRITE |(equal (- x) c)|))
 (8 8 (:REWRITE |(equal (- x) (- y))|))
 (8 2 (:REWRITE RATIONALP-X))
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
 (6 6 (:REWRITE |(mod x (- y))| . 3))
 (6 6 (:REWRITE |(mod x (- y))| . 2))
 (6 6 (:REWRITE |(mod x (- y))| . 1))
 (6 6
    (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (6 6
    (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (6 6 (:REWRITE |(mod (- x) y)| . 3))
 (6 6 (:REWRITE |(mod (- x) y)| . 2))
 (6 6 (:REWRITE |(mod (- x) y)| . 1))
 (6 6
    (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (6 6 (:REWRITE |(* a (/ a) b)|))
 (4 4 (:REWRITE FLOOR-POSITIVE . 1))
 (3 1 (:REWRITE SMAN::STP-!R))
 (2 2 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
 (2 2 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (2 2 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (2 2 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (2 2 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
 (2 2 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (2 2 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (2 2 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
 (2 2 (:REWRITE REDUCE-RATIONALP-+))
 (2 2 (:REWRITE REDUCE-RATIONALP-*))
 (2 2 (:REWRITE RATIONALP-MINUS-X))
 (2 2 (:REWRITE FLOOR-ZERO . 1))
 (2 2 (:REWRITE |(mod (floor x y) z)| . 5))
 (2 2 (:REWRITE |(mod (floor x y) z)| . 4))
 (2 2 (:REWRITE |(mod (floor x y) z)| . 3))
 (2 2 (:REWRITE |(mod (floor x y) z)| . 2))
 (2 2
    (:REWRITE |(floor (floor x y) z)| . 5))
 (2 2
    (:REWRITE |(floor (floor x y) z)| . 4))
 (2 2
    (:REWRITE |(floor (floor x y) z)| . 3))
 (2 2
    (:REWRITE |(floor (floor x y) z)| . 2))
 (2 2 (:REWRITE |(< y (+ (- c) x))|))
 (2 2 (:REWRITE |(< x (+ c/d y))|))
 (2 2 (:META META-RATIONALP-CORRECT)))
(SMAN::!R-DEFAULT-1-NUMBER-NOT-INTEGER
 (151056 146 (:LINEAR LINEAR-FLOOR-BOUNDS-1))
 (55212 470 (:REWRITE THE-FLOOR-ABOVE))
 (53720 22 (:REWRITE SMAN::UNNECESSARY-MOD))
 (53400 53400
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (53400 53400
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (53400 53400
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (40648 22 (:REWRITE MOD-ZERO . 4))
 (29500 22 (:REWRITE MOD-X-Y-=-X . 3))
 (29224 177 (:REWRITE CANCEL-FLOOR-+))
 (29182 22 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (28625 22 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (27889 22 (:REWRITE MOD-X-Y-=-X . 4))
 (23050 2374
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (23050 2374
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (23050 2374
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (23050 2374
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (23050 2374
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (21613 181 (:REWRITE SMAN::UNNECESSARY-FLOOR))
 (20341 744 (:REWRITE DEFAULT-PLUS-1))
 (20294 744 (:REWRITE DEFAULT-PLUS-2))
 (18704 177 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (17999 2433 (:REWRITE DEFAULT-TIMES-1))
 (17903 177 (:REWRITE FLOOR-ZERO . 3))
 (17563 177 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (17182 177 (:REWRITE FLOOR-ZERO . 4))
 (15761 177 (:REWRITE FLOOR-ZERO . 5))
 (14500 1912
        (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (13608 2433 (:REWRITE DEFAULT-TIMES-2))
 (12789 22 (:REWRITE CANCEL-MOD-+))
 (12712 2374
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (12712 2374
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (12712 2374
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (12712 2374
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (12712 2374
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (12712 2374
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (12712 2374
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (12712 2374
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
 (12712 2374
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (12712 2374
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (12117 600 (:REWRITE |(* (- x) y)|))
 (10233 177 (:REWRITE FLOOR-=-X/Y . 2))
 (9915 9915
       (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (9545 471 (:REWRITE INTEGERP-MINUS-X))
 (8541 181 (:REWRITE DEFAULT-FLOOR-RATIO))
 (7012 864 (:REWRITE DEFAULT-MINUS))
 (6401 38 (:REWRITE |(integerp (- x))|))
 (5730 59 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (5088 22 (:REWRITE MOD-ZERO . 3))
 (4374 73 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (3958 392
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (3945 177 (:REWRITE FLOOR-ZERO . 2))
 (3945 177 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (3945 177 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (3584 470 (:REWRITE THE-FLOOR-BELOW))
 (3439
  3439
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (3439
      3439
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (3439
     3439
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (3439 3439
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (3415 177 (:REWRITE FLOOR-CANCEL-*-CONST))
 (3062 22 (:REWRITE DEFAULT-MOD-RATIO))
 (2737 424 (:REWRITE DEFAULT-LESS-THAN-1))
 (2652 177
       (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (2647 172
       (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (2620 262 (:REWRITE DEFAULT-DIVIDE))
 (2441 392
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (2363 1 (:REWRITE |(< (if a b c) x)|))
 (2302 181 (:REWRITE DEFAULT-FLOOR-1))
 (2231 172
       (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (2056 424 (:REWRITE DEFAULT-LESS-THAN-2))
 (1998 73 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (1912 1912
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (1912 1912
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (1912 1912
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (1910 22 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (1910 22
       (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (1892 22 (:REWRITE MOD-X-Y-=-X . 2))
 (1050 392 (:REWRITE SIMPLIFY-SUMS-<))
 (1019 22 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (1019 22 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (1002 177
       (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (997 22 (:REWRITE MOD-CANCEL-*-CONST))
 (903 24
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (903 24
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (895 22 (:REWRITE DEFAULT-MOD-1))
 (742 34 (:REWRITE DEFAULT-LOGAND-2))
 (676 181 (:REWRITE DEFAULT-FLOOR-2))
 (518 13 (:REWRITE ODD-EXPT-THM))
 (466 406
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (465 6 (:REWRITE |(* (* x y) z)|))
 (450 172
      (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (395 395
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (395 395 (:REWRITE INTEGERP-<-CONSTANT))
 (395 395 (:REWRITE CONSTANT-<-INTEGERP))
 (395 395
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (395 395
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (395 395
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (395 395
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (395 395 (:REWRITE |(< c (- x))|))
 (395 395
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (395 395
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (395 395
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (395 395
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (395 395 (:REWRITE |(< (/ x) (/ y))|))
 (395 395 (:REWRITE |(< (- x) c)|))
 (395 395 (:REWRITE |(< (- x) (- y))|))
 (378 172
      (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (376 376
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (376 12 (:REWRITE FLOOR-POSITIVE . 2))
 (376 12 (:REWRITE FLOOR-NONPOSITIVE . 1))
 (349 12 (:REWRITE FLOOR-POSITIVE . 3))
 (340 20
      (:REWRITE |(floor (floor x y) z)| . 5))
 (328 328 (:REWRITE REDUCE-INTEGERP-+))
 (328 328 (:META META-INTEGERP-CORRECT))
 (322 12 (:REWRITE FLOOR-NONPOSITIVE . 2))
 (305 305 (:REWRITE DEFAULT-EXPT-2))
 (305 305 (:REWRITE DEFAULT-EXPT-1))
 (305 305 (:REWRITE |(expt (- x) n)|))
 (259 259 (:REWRITE |(< (* x y) 0)|))
 (242 242 (:REWRITE |(< (/ x) 0)|))
 (239 239
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (239 239
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (221 12 (:REWRITE FLOOR-POSITIVE . 4))
 (221 12 (:REWRITE FLOOR-NONPOSITIVE . 3))
 (172 172 (:REWRITE |(floor x (- y))| . 2))
 (172 172 (:REWRITE |(floor x (- y))| . 1))
 (172 172 (:REWRITE |(floor (- x) y)| . 2))
 (172 172 (:REWRITE |(floor (- x) y)| . 1))
 (164 6 (:REWRITE FLOOR-=-X/Y . 4))
 (164 6
      (:REWRITE |(equal (floor (+ x y) z) x)|))
 (131 131
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (131 131
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (131 131
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (131 131
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (128 20
      (:REWRITE |(floor (floor x y) z)| . 4))
 (128 20
      (:REWRITE |(floor (floor x y) z)| . 3))
 (128 20
      (:REWRITE |(floor (floor x y) z)| . 2))
 (126 1 (:REWRITE |(* (if a b c) x)|))
 (105 17 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (98 98 (:TYPE-PRESCRIPTION SMAN::STP))
 (96 2
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4A-EXPT))
 (93 93
     (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (86 18 (:REWRITE SMAN::!R-R))
 (79 29 (:REWRITE SMAN::!MI-MI))
 (78 34
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (69 69 (:REWRITE |(< 0 (* x y))|))
 (69 17 (:LINEAR EXPT->=-1-ONE))
 (69 17 (:LINEAR EXPT->-1-ONE))
 (65 65
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (65 65
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (65 65 (:REWRITE |(< 0 (/ x))|))
 (53 8 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
 (50 8 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (50 8 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (50 8 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (50 8 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (46 46 (:REWRITE |(+ x (- x))|))
 (46 16
     (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (44 20 (:REWRITE SMAN::STP-!MI))
 (43 17 (:LINEAR EXPT-X->=-X))
 (43 17 (:LINEAR EXPT-X->-X))
 (43 1 (:REWRITE |(mod x 1)|))
 (40 22 (:REWRITE DEFAULT-MOD-2))
 (34 34
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (34 34
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (34 34
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (30 24 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (26 10 (:REWRITE DEFAULT-CDR))
 (26 10 (:REWRITE DEFAULT-CAR))
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
 (24 4 (:REWRITE ACL2-NUMBERP-X))
 (21 21
     (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (20 20
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (18 8 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (17 17 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (17 17 (:LINEAR EXPT-LINEAR-UPPER-<))
 (17 17 (:LINEAR EXPT-LINEAR-LOWER-<))
 (17 17 (:LINEAR EXPT->=-1-TWO))
 (17 17 (:LINEAR EXPT->-1-TWO))
 (17 17 (:LINEAR EXPT-<=-1-TWO))
 (17 17 (:LINEAR EXPT-<=-1-ONE))
 (17 17 (:LINEAR EXPT-<-1-TWO))
 (17 17 (:LINEAR EXPT-<-1-ONE))
 (16 16 (:REWRITE |(mod x (- y))| . 3))
 (16 16 (:REWRITE |(mod x (- y))| . 2))
 (16 16 (:REWRITE |(mod x (- y))| . 1))
 (16 16
     (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (16 16 (:REWRITE |(mod (- x) y)| . 3))
 (16 16 (:REWRITE |(mod (- x) y)| . 2))
 (16 16 (:REWRITE |(mod (- x) y)| . 1))
 (15 15
     (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (12 12 (:REWRITE FLOOR-POSITIVE . 1))
 (8 8 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (8 8 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (8 8 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (8 8 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
 (8 8 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (8 8 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
 (7 7 (:REWRITE |(< x (+ c/d y))|))
 (7 7 (:REWRITE |(< (+ c/d x) y)|))
 (6 6 (:REWRITE FLOOR-ZERO . 1))
 (6 6 (:REWRITE |(mod (floor x y) z)| . 5))
 (6 6 (:REWRITE |(mod (floor x y) z)| . 4))
 (6 6 (:REWRITE |(mod (floor x y) z)| . 3))
 (6 6 (:REWRITE |(mod (floor x y) z)| . 2))
 (6 6 (:REWRITE SMAN::!R-!MI-BELOW))
 (4 4 (:REWRITE REDUCE-RATIONALP-+))
 (4 4 (:REWRITE REDUCE-RATIONALP-*))
 (4 4 (:REWRITE RATIONALP-X))
 (4 4 (:REWRITE RATIONALP-MINUS-X))
 (4 4 (:META META-RATIONALP-CORRECT))
 (3 3 (:REWRITE |(< y (+ (- c) x))|))
 (2 2
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (2 2
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (2 2
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (2 2 (:REWRITE |(equal (* x y) 0)|))
 (2 2
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (2 2 (:REWRITE |(* c (* d x))|)))
(SMAN::!R-DEFAULT-1-NEGATIVE-INTEGER-CASE-1
 (176322 188 (:LINEAR LINEAR-FLOOR-BOUNDS-1))
 (68937 670 (:REWRITE THE-FLOOR-ABOVE))
 (63420 63420
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (63420 63420
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (63420 63420
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (61157 30 (:REWRITE SMAN::UNNECESSARY-MOD))
 (48315 30 (:REWRITE MOD-ZERO . 4))
 (35849 30 (:REWRITE MOD-X-Y-=-X . 3))
 (35421 30 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (34723 30 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (34242 229 (:REWRITE CANCEL-FLOOR-+))
 (33662 30 (:REWRITE MOD-X-Y-=-X . 4))
 (27428 234 (:REWRITE SMAN::UNNECESSARY-FLOOR))
 (27417 2797
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (27417 2797
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (27417 2797
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (27417 2797
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (27417 2797
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (25778 1021 (:REWRITE DEFAULT-PLUS-1))
 (25718 1021 (:REWRITE DEFAULT-PLUS-2))
 (22431 229 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (21751 229 (:REWRITE FLOOR-ZERO . 3))
 (20625 229 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (20571 3156 (:REWRITE DEFAULT-TIMES-1))
 (20116 229 (:REWRITE FLOOR-ZERO . 4))
 (19063 2481
        (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (18374 229 (:REWRITE FLOOR-ZERO . 5))
 (17988 3156 (:REWRITE DEFAULT-TIMES-2))
 (16594 30 (:REWRITE CANCEL-MOD-+))
 (15107 2797
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (15107 2797
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (15107 2797
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (15107 2797
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (15107 2797
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (15107 2797
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (15107 2797
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (15107 2797
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
 (15107 2797
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (15107 2797
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (14756 784 (:REWRITE |(* (- x) y)|))
 (12433 633 (:REWRITE INTEGERP-MINUS-X))
 (12160 229 (:REWRITE FLOOR-=-X/Y . 2))
 (10460 234 (:REWRITE DEFAULT-FLOOR-RATIO))
 (8736 1134 (:REWRITE DEFAULT-MINUS))
 (7262 74 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (6952 55 (:REWRITE |(integerp (- x))|))
 (6568 30 (:REWRITE MOD-ZERO . 3))
 (4828 94 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (4762 557
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (4726 2 (:REWRITE |(< (if a b c) x)|))
 (4646 229 (:REWRITE FLOOR-ZERO . 2))
 (4646 229 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (4646 229 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (4605
  4605
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (4605
      4605
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (4605
     4605
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (4605 4605
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (4515 670 (:REWRITE THE-FLOOR-BELOW))
 (3963 229 (:REWRITE FLOOR-CANCEL-*-CONST))
 (3940 30 (:REWRITE DEFAULT-MOD-RATIO))
 (3480 348 (:REWRITE DEFAULT-DIVIDE))
 (3286 611 (:REWRITE DEFAULT-LESS-THAN-1))
 (3026 229
       (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (3020 223
       (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (2728 557
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (2651 611 (:REWRITE DEFAULT-LESS-THAN-2))
 (2557 234 (:REWRITE DEFAULT-FLOOR-1))
 (2492 223
       (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (2485 30 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (2485 30
       (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (2481 2481
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (2481 2481
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (2481 2481
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (2458 30 (:REWRITE MOD-X-Y-=-X . 2))
 (2291 94 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (1332 30 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (1332 30 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (1297 30 (:REWRITE MOD-CANCEL-*-CONST))
 (1269 557 (:REWRITE SIMPLIFY-SUMS-<))
 (1228 229
       (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (1166 32
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (1166 32
       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (1156 30 (:REWRITE DEFAULT-MOD-1))
 (1007 46 (:REWRITE DEFAULT-LOGAND-2))
 (882 234 (:REWRITE DEFAULT-FLOOR-2))
 (668 589
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (570 223
      (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (562 562
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (562 562 (:REWRITE INTEGERP-<-CONSTANT))
 (562 562 (:REWRITE CONSTANT-<-INTEGERP))
 (562 562
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (562 562
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (562 562
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (562 562
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (562 562 (:REWRITE |(< c (- x))|))
 (562 562
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (562 562
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (562 562
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (562 562
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (562 562 (:REWRITE |(< (/ x) (/ y))|))
 (562 562 (:REWRITE |(< (- x) c)|))
 (562 562 (:REWRITE |(< (- x) (- y))|))
 (522 17 (:REWRITE ODD-EXPT-THM))
 (508 508
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (474 223
      (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (465 6 (:REWRITE |(* (* x y) z)|))
 (448 448 (:REWRITE REDUCE-INTEGERP-+))
 (448 448 (:META META-INTEGERP-CORRECT))
 (425 15 (:REWRITE FLOOR-POSITIVE . 2))
 (425 15 (:REWRITE FLOOR-NONPOSITIVE . 1))
 (402 402 (:REWRITE DEFAULT-EXPT-2))
 (402 402 (:REWRITE DEFAULT-EXPT-1))
 (402 402 (:REWRITE |(expt (- x) n)|))
 (393 15 (:REWRITE FLOOR-POSITIVE . 3))
 (374 374 (:REWRITE |(< (* x y) 0)|))
 (357 15 (:REWRITE FLOOR-NONPOSITIVE . 2))
 (341 21
      (:REWRITE |(floor (floor x y) z)| . 5))
 (338 338 (:REWRITE |(< (/ x) 0)|))
 (335 2 (:REWRITE |(* (if a b c) x)|))
 (334 334
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (334 334
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (297 9 (:REWRITE SMAN::!R-!MI-BELOW))
 (256 15 (:REWRITE FLOOR-POSITIVE . 4))
 (256 15 (:REWRITE FLOOR-NONPOSITIVE . 3))
 (245 5 (:REWRITE SMAN::!MI-!MI-DIFF))
 (223 223 (:REWRITE |(floor x (- y))| . 2))
 (223 223 (:REWRITE |(floor x (- y))| . 1))
 (223 223 (:REWRITE |(floor (- x) y)| . 2))
 (223 223 (:REWRITE |(floor (- x) y)| . 1))
 (185 8 (:REWRITE FLOOR-=-X/Y . 4))
 (185 8
      (:REWRITE |(equal (floor (+ x y) z) x)|))
 (155 155
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (155 155
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (155 155
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (155 155
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (155 23 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (138 138 (:TYPE-PRESCRIPTION SMAN::STP))
 (132 24 (:REWRITE SMAN::!R-R))
 (129 21
      (:REWRITE |(floor (floor x y) z)| . 4))
 (129 21
      (:REWRITE |(floor (floor x y) z)| . 3))
 (129 21
      (:REWRITE |(floor (floor x y) z)| . 2))
 (121 121
      (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (101 23 (:LINEAR EXPT->=-1-ONE))
 (101 23 (:LINEAR EXPT->-1-ONE))
 (99 99 (:REWRITE |(< 0 (* x y))|))
 (96 2
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4A-EXPT))
 (95 95 (:REWRITE |(< 0 (/ x))|))
 (94 94
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (94 94
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (94 33 (:REWRITE SMAN::!MI-MI))
 (90 46
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (75 31 (:REWRITE SMAN::STP-!MI))
 (72 12 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (72 12 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (72 12
     (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (72 12
     (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (67 22
     (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (66 12 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
 (59 59 (:REWRITE |(+ x (- x))|))
 (57 30 (:REWRITE DEFAULT-MOD-2))
 (49 23 (:LINEAR EXPT-X->=-X))
 (49 23 (:LINEAR EXPT-X->-X))
 (46 46
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (46 46
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (46 46
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (43 1 (:REWRITE |(mod x 1)|))
 (40 32 (:REWRITE SIMPLIFY-SUMS-EQUAL))
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
 (31 12 (:REWRITE DEFAULT-CDR))
 (31 12 (:REWRITE DEFAULT-CAR))
 (29 29
     (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (27 27
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (25 25 (:REWRITE |(< (+ c/d x) y)|))
 (24 12 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (23 23 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (23 23 (:LINEAR EXPT-LINEAR-UPPER-<))
 (23 23 (:LINEAR EXPT-LINEAR-LOWER-<))
 (23 23 (:LINEAR EXPT->=-1-TWO))
 (23 23 (:LINEAR EXPT->-1-TWO))
 (23 23 (:LINEAR EXPT-<=-1-TWO))
 (23 23 (:LINEAR EXPT-<=-1-ONE))
 (23 23 (:LINEAR EXPT-<-1-TWO))
 (23 23 (:LINEAR EXPT-<-1-ONE))
 (22 22 (:REWRITE |(mod x (- y))| . 3))
 (22 22 (:REWRITE |(mod x (- y))| . 2))
 (22 22 (:REWRITE |(mod x (- y))| . 1))
 (22 22
     (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (22 22 (:REWRITE |(mod (- x) y)| . 3))
 (22 22 (:REWRITE |(mod (- x) y)| . 2))
 (22 22 (:REWRITE |(mod (- x) y)| . 1))
 (21 21
     (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (15 15 (:REWRITE FLOOR-POSITIVE . 1))
 (13 13 (:REWRITE |(< x (+ c/d y))|))
 (12 12 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (12 12
     (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (12 12 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (12 12
     (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (9 9 (:REWRITE |(< y (+ (- c) x))|))
 (8 8 (:REWRITE FLOOR-ZERO . 1))
 (8 8 (:REWRITE |(mod (floor x y) z)| . 5))
 (8 8 (:REWRITE |(mod (floor x y) z)| . 4))
 (8 8 (:REWRITE |(mod (floor x y) z)| . 3))
 (8 8 (:REWRITE |(mod (floor x y) z)| . 2))
 (5 5 (:TYPE-PRESCRIPTION NATP))
 (2 2
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (2 2
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (2 2
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (2 2 (:REWRITE |(equal (* x y) 0)|))
 (2 2
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (2 2 (:REWRITE |(< (+ (- c) x) y)|))
 (2 2 (:REWRITE |(* c (* d x))|))
 (1 1 (:REWRITE FOLD-CONSTS-IN-+)))
(SMAN::ASH-0
     (31 1 (:REWRITE SMAN::UNNECESSARY-FLOOR))
     (7 1 (:REWRITE DEFAULT-FLOOR-RATIO))
     (4 1 (:REWRITE |(* y x)|))
     (3 3 (:REWRITE REDUCE-INTEGERP-+))
     (3 3 (:REWRITE INTEGERP-MINUS-X))
     (3 3 (:META META-INTEGERP-CORRECT))
     (2 2 (:REWRITE DEFAULT-TIMES-2))
     (2 2 (:REWRITE DEFAULT-TIMES-1))
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
     (1 1 (:REWRITE DEFAULT-FLOOR-2))
     (1 1 (:REWRITE DEFAULT-FLOOR-1))
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
     (1 1 (:REWRITE |(* 1 x)|)))
(SMAN::ASH-ASH-LEMMA1
 (4657 10 (:LINEAR LINEAR-FLOOR-BOUNDS-1))
 (3775 68 (:REWRITE THE-FLOOR-ABOVE))
 (2921 2921
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (2921 2921
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (2921 2921
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (2576 16 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (2559 16 (:REWRITE FLOOR-ZERO . 4))
 (2363 1 (:REWRITE |(< (if a b c) x)|))
 (2357 16 (:REWRITE FLOOR-ZERO . 5))
 (2153 13 (:REWRITE |(+ y x)|))
 (1984 16 (:REWRITE CANCEL-FLOOR-+))
 (1934 16 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (1903 16 (:REWRITE FLOOR-ZERO . 3))
 (1314 251 (:REWRITE DEFAULT-TIMES-1))
 (1298 44 (:REWRITE DEFAULT-PLUS-1))
 (1292 44 (:REWRITE DEFAULT-PLUS-2))
 (1152 128 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (1152 128
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (1152 128
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (1152 128
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (1152 128
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (958 17 (:REWRITE DEFAULT-FLOOR-RATIO))
 (945 16 (:REWRITE FLOOR-=-X/Y . 2))
 (936 16 (:REWRITE FLOOR-=-X/Y . 3))
 (700 251 (:REWRITE DEFAULT-TIMES-2))
 (640 128 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
 (640 128 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (640 128 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (640 128
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (640 128
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (640 128
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (640 128
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (640 128
      (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (640 128
      (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
 (640 128
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (640 128
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (603 31 (:REWRITE |(* (- x) y)|))
 (545 61 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (511 64 (:REWRITE DEFAULT-LESS-THAN-1))
 (460 10 (:REWRITE |(* (* x y) z)|))
 (458 5 (:REWRITE |(integerp (- x))|))
 (431 9 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (396
  396
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (396 396
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (396
     396
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (396 396
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (326 61
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (313 60 (:REWRITE INTEGERP-MINUS-X))
 (290 56 (:REWRITE DEFAULT-MINUS))
 (274 68 (:REWRITE THE-FLOOR-BELOW))
 (251 16 (:REWRITE FLOOR-ZERO . 2))
 (251 16 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (251 16 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (237 17 (:REWRITE DEFAULT-FLOOR-1))
 (224 16 (:REWRITE FLOOR-CANCEL-*-CONST))
 (210 64 (:REWRITE DEFAULT-LESS-THAN-2))
 (189 61 (:REWRITE SIMPLIFY-SUMS-<))
 (184 184
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (184 184
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (184 184
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (184 184
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (184 16
      (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (166 16 (:REWRITE |(/ (expt x n))|))
 (160 16 (:REWRITE DEFAULT-DIVIDE))
 (152 63
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (126 1 (:REWRITE |(* (if a b c) x)|))
 (102 1 (:REWRITE ODD-EXPT-THM))
 (79 5 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (68 61
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (62 2 (:REWRITE |(floor x 1)|))
 (61 61
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
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
 (59 5 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (56 16
     (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (53 17 (:REWRITE DEFAULT-FLOOR-2))
 (53 13
     (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (51 51 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (49 49 (:REWRITE REDUCE-INTEGERP-+))
 (49 49 (:META META-INTEGERP-CORRECT))
 (47 3 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (43 43 (:REWRITE |(< (* x y) 0)|))
 (41 41
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (41 41
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (41 41
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (41 41 (:REWRITE |(< (/ x) 0)|))
 (35 13
     (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (29 29 (:REWRITE DEFAULT-EXPT-2))
 (29 29 (:REWRITE DEFAULT-EXPT-1))
 (29 29 (:REWRITE |(expt (- x) n)|))
 (29 3 (:LINEAR EXPT->=-1-ONE))
 (29 3 (:LINEAR EXPT->-1-ONE))
 (18 18
     (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (16 16 (:TYPE-PRESCRIPTION ABS))
 (15 15 (:REWRITE |(floor x (- y))| . 2))
 (15 15 (:REWRITE |(floor x (- y))| . 1))
 (15 15 (:REWRITE |(floor (- x) y)| . 2))
 (15 15 (:REWRITE |(floor (- x) y)| . 1))
 (13 13
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (13 13
     (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (10 10 (:REWRITE |(< 0 (/ x))|))
 (10 10 (:REWRITE |(< 0 (* x y))|))
 (10 10 (:REWRITE |(- (- x))|))
 (9 1 (:REWRITE FLOOR-POSITIVE . 2))
 (9 1 (:REWRITE FLOOR-NONPOSITIVE . 1))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (6 6
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (5 1 (:REWRITE FLOOR-POSITIVE . 4))
 (5 1 (:REWRITE FLOOR-POSITIVE . 3))
 (5 1 (:REWRITE FLOOR-NONPOSITIVE . 3))
 (5 1 (:REWRITE FLOOR-NONPOSITIVE . 2))
 (4 4 (:REWRITE |(+ x (- x))|))
 (3 3 (:LINEAR EXPT-X->=-X))
 (3 3 (:LINEAR EXPT-X->-X))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<))
 (3 3 (:LINEAR EXPT->=-1-TWO))
 (3 3 (:LINEAR EXPT->-1-TWO))
 (3 3 (:LINEAR EXPT-<=-1-TWO))
 (3 3 (:LINEAR EXPT-<=-1-ONE))
 (3 3 (:LINEAR EXPT-<-1-TWO))
 (3 3 (:LINEAR EXPT-<-1-ONE))
 (2 2
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (2 2 (:REWRITE |(* a (/ a) b)|))
 (1 1 (:REWRITE FLOOR-POSITIVE . 1))
 (1 1
    (:REWRITE |(floor (floor x y) z)| . 5))
 (1 1
    (:REWRITE |(floor (floor x y) z)| . 4))
 (1 1
    (:REWRITE |(floor (floor x y) z)| . 3))
 (1 1
    (:REWRITE |(floor (floor x y) z)| . 2)))
(SMAN::ASH-ASH-LEMMA2
 (10862 12 (:LINEAR LINEAR-FLOOR-BOUNDS-1))
 (7589 61 (:REWRITE THE-FLOOR-ABOVE))
 (7232 2991
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (5522 16 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (4342 1 (:REWRITE |(< (if a b c) x)|))
 (4108 16 (:REWRITE |(+ y x)|))
 (4099 16 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (3981 16 (:REWRITE FLOOR-ZERO . 4))
 (3709 16 (:REWRITE FLOOR-ZERO . 5))
 (3406 16 (:REWRITE CANCEL-FLOOR-+))
 (3014 16 (:REWRITE FLOOR-ZERO . 3))
 (2991 2991
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (2991 2991
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (2991 2991
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (2991 2991
       (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (2991 2991
       (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (2601 17
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4A-EXPT))
 (2483 54 (:REWRITE DEFAULT-PLUS-1))
 (2477 54 (:REWRITE DEFAULT-PLUS-2))
 (2343 27 (:REWRITE NORMALIZE-ADDENDS))
 (2093 151 (:REWRITE DEFAULT-TIMES-2))
 (1852 17 (:REWRITE DEFAULT-FLOOR-RATIO))
 (1686 16 (:REWRITE FLOOR-=-X/Y . 2))
 (1677 129 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (1677 129
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (1677 129
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (1677 129
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (1677 129
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (1505 151 (:REWRITE DEFAULT-TIMES-1))
 (1502 16 (:REWRITE FLOOR-=-X/Y . 3))
 (1137 8 (:REWRITE |(* y x)|))
 (1120 16 (:REWRITE |(integerp (- x))|))
 (1115
   1115
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (1115
  1115
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1115
      1115
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1115
     1115
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1115 1115
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1115 1115
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (933 41 (:REWRITE |(* (- x) y)|))
 (903 129 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (903 129 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (903 129
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (903 129
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (903 129
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (903 129
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (903 129
      (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (903 129
      (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
 (903 129
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (903 129
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (870 87 (:REWRITE DEFAULT-DIVIDE))
 (796 9 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (776 54
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (693 87 (:REWRITE |(/ (expt x n))|))
 (569 53 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (552 16 (:REWRITE FLOOR-ZERO . 2))
 (552 16 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (552 16 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (539 56 (:REWRITE DEFAULT-LESS-THAN-1))
 (480 128 (:REWRITE DEFAULT-MINUS))
 (408 16 (:REWRITE FLOOR-CANCEL-*-CONST))
 (380 61 (:REWRITE THE-FLOOR-BELOW))
 (341 1 (:REWRITE |(* (if a b c) x)|))
 (321 17 (:REWRITE DEFAULT-FLOOR-1))
 (300 6 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (298 56 (:REWRITE DEFAULT-LESS-THAN-2))
 (228 16
      (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (220 220
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (220 220
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (220 220
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (220 220
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (210 6 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (196 16
      (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (195 15
      (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (195 15
      (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (170 17 (:REWRITE DEFAULT-FLOOR-2))
 (116 53 (:REWRITE SIMPLIFY-SUMS-<))
 (111 111 (:REWRITE DEFAULT-EXPT-2))
 (111 111 (:REWRITE DEFAULT-EXPT-1))
 (111 111 (:REWRITE |(expt 1/c n)|))
 (111 111 (:REWRITE |(expt (- x) n)|))
 (106 1 (:REWRITE |(* y (* x z))|))
 (98 7 (:LINEAR EXPT->=-1-ONE))
 (92 10 (:REWRITE |(< 0 (/ x))|))
 (79 14
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (72 7 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (70 5 (:REWRITE |(+ 0 x)|))
 (60 15
     (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (60 15
     (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (55 55
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (55 55
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (55 55
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (55 55
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (55 55
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (55 55
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (55 55
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (55 55
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (55 55
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (55 55
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (55 55
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (55 55 (:REWRITE |(< (/ x) (/ y))|))
 (55 55 (:REWRITE |(< (- x) (- y))|))
 (54 54
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (54 54 (:REWRITE INTEGERP-<-CONSTANT))
 (54 54 (:REWRITE CONSTANT-<-INTEGERP))
 (54 54 (:REWRITE |(< c (- x))|))
 (54 54 (:REWRITE |(< (- x) c)|))
 (46 46 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (42 42 (:REWRITE REDUCE-INTEGERP-+))
 (42 42 (:REWRITE INTEGERP-MINUS-X))
 (42 42 (:META META-INTEGERP-CORRECT))
 (36 36
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (36 36
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (36 36 (:REWRITE |(< (/ x) 0)|))
 (36 36 (:REWRITE |(< (* x y) 0)|))
 (34 1 (:REWRITE FLOOR-POSITIVE . 3))
 (31 1 (:REWRITE FLOOR-POSITIVE . 2))
 (31 1 (:REWRITE FLOOR-NONPOSITIVE . 1))
 (25 1 (:REWRITE FLOOR-POSITIVE . 4))
 (25 1 (:REWRITE FLOOR-NONPOSITIVE . 3))
 (25 1 (:REWRITE FLOOR-NONPOSITIVE . 2))
 (21 21
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (19 2
     (:REWRITE |(* (expt x m) (expt x n))|))
 (17 17
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (17 17
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (17 17
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (15 15 (:REWRITE |(floor x (- y))| . 2))
 (15 15 (:REWRITE |(floor x (- y))| . 1))
 (15 15 (:REWRITE |(floor (- x) y)| . 2))
 (15 15 (:REWRITE |(floor (- x) y)| . 1))
 (14 14
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (14 14
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (14 14
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (12 12
     (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (12 6 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
 (10 10 (:REWRITE |(< 0 (* x y))|))
 (9 9
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (9 9
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (7 7 (:LINEAR EXPT-X->=-X))
 (7 7 (:LINEAR EXPT-X->-X))
 (7 7 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (7 7 (:LINEAR EXPT-LINEAR-UPPER-<))
 (7 7 (:LINEAR EXPT-LINEAR-LOWER-<))
 (7 7 (:LINEAR EXPT->=-1-TWO))
 (7 7 (:LINEAR EXPT->-1-TWO))
 (7 7 (:LINEAR EXPT->-1-ONE))
 (7 7 (:LINEAR EXPT-<=-1-TWO))
 (7 7 (:LINEAR EXPT-<=-1-ONE))
 (7 7 (:LINEAR EXPT-<-1-TWO))
 (7 7 (:LINEAR EXPT-<-1-ONE))
 (6 6 (:REWRITE |(+ x (- x))|))
 (2 2 (:REWRITE ODD-EXPT-THM))
 (1 1 (:REWRITE FLOOR-POSITIVE . 1))
 (1 1
    (:REWRITE |(floor (floor x y) z)| . 5))
 (1 1
    (:REWRITE |(floor (floor x y) z)| . 4))
 (1 1
    (:REWRITE |(floor (floor x y) z)| . 3))
 (1 1
    (:REWRITE |(floor (floor x y) z)| . 2))
 (1 1 (:REWRITE |(- (- x))|))
 (1 1 (:REWRITE |(* 0 x)|)))
(SMAN::LOGAND-COMMUTES1 (149 149
                             (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 2))
                        (149 149
                             (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
                        (36 36 (:REWRITE REDUCE-INTEGERP-+))
                        (36 36 (:REWRITE INTEGERP-MINUS-X))
                        (36 36 (:META META-INTEGERP-CORRECT))
                        (17 17 (:REWRITE LOGAND-CONSTANT-MASK))
                        (16 4 (:LINEAR LOGAND-BOUNDS-POS . 2))
                        (16 4 (:LINEAR LOGAND-BOUNDS-POS . 1))
                        (16 4 (:LINEAR LOGAND-BOUNDS-NEG . 2))
                        (16 4 (:LINEAR LOGAND-BOUNDS-NEG . 1))
                        (3 3 (:REWRITE |(logand c d x)|)))
(SMAN::LOGAND-ABSORBTION
     (180742 1950
             (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (180668 2218 (:REWRITE THE-FLOOR-ABOVE))
     (112051 112051
             (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (112051 112051
             (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (112051 112051
             (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (112051 112051
             (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (108750 747 (:REWRITE SMAN::UNNECESSARY-FLOOR))
     (108673 1738
             (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (92268 149 (:LINEAR LOGAND-BOUNDS-NEG . 2))
     (92268 149 (:LINEAR LOGAND-BOUNDS-NEG . 1))
     (90776 404 (:LINEAR LINEAR-FLOOR-BOUNDS-1))
     (69873 1977 (:REWRITE DEFAULT-PLUS-2))
     (66409 1977 (:REWRITE DEFAULT-PLUS-1))
     (63215 797 (:REWRITE NORMALIZE-ADDENDS))
     (46275 5175
            (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (46275 5175
            (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (46275 5175
            (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (46275 5175
            (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (46275 5175
            (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (45440 66 (:REWRITE |(< (logand x y) 0)|))
     (27085 1729 (:REWRITE INTEGERP-<-CONSTANT))
     (25875 5175
            (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
     (25875 5175
            (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (25875 5175
            (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (25875 5175
            (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (25875 5175
            (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (25875 5175
            (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (25875 5175
            (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (25875 5175
            (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (25875 5175
            (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (25875 5175
            (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (25875 5175
            (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (24562 7156 (:REWRITE DEFAULT-TIMES-2))
     (20604 202 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (20604 202 (:DEFINITION FIX))
     (19108 1735 (:REWRITE |(< c (- x))|))
     (17987 1 (:REWRITE |(floor (+ x r) i)|))
     (16749 3 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (16122 3
            (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (11322 18 (:REWRITE |(* y (* x z))|))
     (9563 747 (:REWRITE DEFAULT-FLOOR-RATIO))
     (8432 7156 (:REWRITE DEFAULT-TIMES-1))
     (8216 202 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
     (6784 128 (:REWRITE CANCEL-FLOOR-+))
     (6501 202 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (6428 128 (:REWRITE FLOOR-ZERO . 3))
     (5284 1950 (:REWRITE DEFAULT-LESS-THAN-1))
     (5033 293 (:REWRITE FLOOR-=-X/Y . 3))
     (4422 1950 (:REWRITE DEFAULT-LESS-THAN-2))
     (4290 747 (:REWRITE |(floor x 2)| . 2))
     (4045 4045
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (4045 4045
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (4045 4045
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (3989 3989
           (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (3980 1726
           (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (3715 771 (:REWRITE INTEGERP-MINUS-X))
     (3580 1726
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (3528 128 (:REWRITE FLOOR-ZERO . 5))
     (3528 128 (:REWRITE FLOOR-ZERO . 4))
     (3428 128 (:REWRITE FLOOR-X-Y-=--1 . 2))
     (3340 4 (:REWRITE |(+ y (+ x z))|))
     (3128 128 (:REWRITE FLOOR-X-Y-=-1 . 2))
     (2522 262 (:REWRITE DEFAULT-MINUS))
     (2514 3 (:REWRITE |(* (* x y) z)|))
     (2476 2432
           (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
     (2412 262 (:REWRITE |(- (* c x))|))
     (2386 57
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (2386 57
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (2228 128 (:REWRITE FLOOR-=-X/Y . 2))
     (2218 2218 (:REWRITE THE-FLOOR-BELOW))
     (2182 262 (:REWRITE |(* (- x) y)|))
     (1850 1738
           (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (1736 57 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (1735 1735
           (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (1735 1735
           (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (1735 1735
           (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (1735 1735
           (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (1735 1735
           (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (1735 1735
           (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (1735 1735
           (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (1735 1735
           (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (1735 1735 (:REWRITE |(< (/ x) (/ y))|))
     (1735 1735 (:REWRITE |(< (- x) (- y))|))
     (1729 1729 (:REWRITE CONSTANT-<-INTEGERP))
     (1729 1729 (:REWRITE |(< (- x) c)|))
     (1726 1726 (:REWRITE SIMPLIFY-SUMS-<))
     (1726 1726
           (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (1698 1698 (:REWRITE |(< (* x y) 0)|))
     (1486 1486
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (1486 1486
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (1486 1486 (:REWRITE |(< (/ x) 0)|))
     (1326 1326
           (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (787 747 (:REWRITE DEFAULT-FLOOR-1))
     (747 747 (:REWRITE DEFAULT-FLOOR-2))
     (643 643 (:REWRITE REDUCE-INTEGERP-+))
     (643 643 (:META META-INTEGERP-CORRECT))
     (640 128 (:REWRITE FLOOR-ZERO . 2))
     (640 128 (:REWRITE FLOOR-X-Y-=-1 . 3))
     (640 128 (:REWRITE FLOOR-X-Y-=--1 . 3))
     (640 128
          (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (640 128
          (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
     (621 3
          (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (621 3 (:REWRITE |(< x (/ y)) with (< 0 y)|))
     (595 595
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (528 128 (:REWRITE FLOOR-CANCEL-*-CONST))
     (442 442 (:TYPE-PRESCRIPTION ABS))
     (404 202 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
     (309 309
          (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (202 202 (:REWRITE |(+ x (- x))|))
     (170 170 (:REWRITE LOGAND-CONSTANT-MASK))
     (128 128
          (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
     (128 128 (:REWRITE |(floor x (- y))| . 2))
     (128 128 (:REWRITE |(floor x (- y))| . 1))
     (128 128
          (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
     (128 128
          (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
     (128 128 (:REWRITE |(floor (- x) y)| . 2))
     (128 128 (:REWRITE |(floor (- x) y)| . 1))
     (128 128
          (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
     (100 100
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (100 100
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (100 100 (:REWRITE |(< 0 (/ x))|))
     (100 100 (:REWRITE |(< 0 (* x y))|))
     (63 57
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (57 57
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (57 57
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (57 57 (:REWRITE |(equal c (/ x))|))
     (57 57 (:REWRITE |(equal c (- x))|))
     (57 57 (:REWRITE |(equal (/ x) c)|))
     (57 57 (:REWRITE |(equal (/ x) (/ y))|))
     (57 57 (:REWRITE |(equal (- x) c)|))
     (57 57 (:REWRITE |(equal (- x) (- y))|))
     (13 13 (:REWRITE |(logand c d x)|))
     (7 7
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (3 3 (:REWRITE |(equal (+ (- c) x) y)|))
     (3 3 (:REWRITE |(< (+ c/d x) y)|))
     (3 3 (:REWRITE |(* x (- y))|))
     (1 1 (:REWRITE |(equal x (if a b c))|)))
(SMAN::!R-DEFAULT-1-NEGATIVE-INTEGER-CASE-2
 (14901 237 (:REWRITE CANCEL-MOD-+))
 (9641 237 (:REWRITE MOD-X-Y-=-X . 4))
 (9317 237 (:REWRITE MOD-X-Y-=-X . 3))
 (8907 237 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (8577 237 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (8470 237 (:REWRITE SMAN::UNNECESSARY-MOD))
 (7237 886 (:REWRITE INTEGERP-MINUS-X))
 (5967 237 (:REWRITE MOD-ZERO . 3))
 (5767 237 (:REWRITE MOD-ZERO . 4))
 (4765 490 (:REWRITE |(* (- x) y)|))
 (4104 4104
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (4104 4104
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (4104 4104
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (3893 2273
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (3384 2396 (:REWRITE DEFAULT-TIMES-2))
 (3147 237 (:REWRITE DEFAULT-MOD-RATIO))
 (3116 2396 (:REWRITE DEFAULT-TIMES-1))
 (2857 272
       (:REWRITE SMAN::!R-DEFAULT-1-NEGATIVE-INTEGER-CASE-1))
 (2742 486 (:REWRITE DEFAULT-MINUS))
 (2359 1627 (:REWRITE DEFAULT-LESS-THAN-1))
 (2273 2273
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (2273 2273
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (2021 1477
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (1902 1477
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (1811 1627 (:REWRITE DEFAULT-LESS-THAN-2))
 (1628 1625
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (1627 1627 (:REWRITE THE-FLOOR-BELOW))
 (1627 1627 (:REWRITE THE-FLOOR-ABOVE))
 (1545 237 (:REWRITE MOD-X-Y-=-X . 2))
 (1545 237
       (:REWRITE |(mod (+ x (mod a b)) y)|))
 (1545 237
       (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (1482 1482 (:REWRITE INTEGERP-<-CONSTANT))
 (1482 1482 (:REWRITE CONSTANT-<-INTEGERP))
 (1482 1482
       (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (1482 1482
       (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (1482 1482
       (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (1482 1482
       (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (1482 1482 (:REWRITE |(< c (- x))|))
 (1482 1482
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (1482 1482
       (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (1482 1482
       (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (1482 1482
       (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (1482 1482 (:REWRITE |(< (/ x) (/ y))|))
 (1482 1482 (:REWRITE |(< (- x) c)|))
 (1482 1482 (:REWRITE |(< (- x) (- y))|))
 (1385 1385
       (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (1381 71 (:REWRITE ZP-OPEN))
 (1365 237 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (1365 237 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (1365 237
       (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (1365 237
       (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (1337 237 (:REWRITE MOD-CANCEL-*-CONST))
 (1323 27 (:REWRITE SMAN::!MI-!MI-DIFF))
 (1259 272 (:REWRITE SMAN::!R-R))
 (1187 1171 (:REWRITE DEFAULT-PLUS-1))
 (1170 1170 (:TYPE-PRESCRIPTION SMAN::STP))
 (959 370 (:REWRITE SMAN::!MI-MI))
 (895 895 (:REWRITE |(< (* x y) 0)|))
 (758 758 (:REWRITE |(< (/ x) 0)|))
 (754 754
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (754 754
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (649 403 (:REWRITE SMAN::STP-!MI))
 (647 647 (:META META-INTEGERP-CORRECT))
 (589 589
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (578 288
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (578 288
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (417 237 (:REWRITE DEFAULT-MOD-1))
 (398 288 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (331 331 (:REWRITE |(< 0 (* x y))|))
 (330 110 (:REWRITE DEFAULT-CDR))
 (330 110 (:REWRITE DEFAULT-CAR))
 (325 325
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (325 325
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (325 325 (:REWRITE |(< 0 (/ x))|))
 (303 289 (:REWRITE |(equal (/ x) c)|))
 (289 289
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (289 289
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (289 289 (:REWRITE |(equal c (/ x))|))
 (289 289 (:REWRITE |(equal (/ x) (/ y))|))
 (289 289 (:REWRITE |(equal (- x) (- y))|))
 (288 288
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (288 288 (:REWRITE |(equal c (- x))|))
 (288 288 (:REWRITE |(equal (- x) c)|))
 (237 237
      (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (237 237 (:REWRITE DEFAULT-MOD-2))
 (237 237 (:REWRITE |(mod x (- y))| . 3))
 (237 237 (:REWRITE |(mod x (- y))| . 2))
 (237 237 (:REWRITE |(mod x (- y))| . 1))
 (237 237
      (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (237 237
      (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (237 237 (:REWRITE |(mod (- x) y)| . 3))
 (237 237 (:REWRITE |(mod (- x) y)| . 2))
 (237 237 (:REWRITE |(mod (- x) y)| . 1))
 (237 237
      (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (233 233
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (144 144 (:REWRITE |(< (+ c/d x) y)|))
 (140
   140
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
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
 (140 140 (:REWRITE DEFAULT-LOGAND-1))
 (111 15 (:REWRITE ACL2-NUMBERP-X))
 (60 60 (:REWRITE |(< x (+ c/d y))|))
 (54 54 (:REWRITE |(< y (+ (- c) x))|))
 (48 12 (:REWRITE RATIONALP-X))
 (38 38 (:REWRITE FOLD-CONSTS-IN-+))
 (38 38 (:REWRITE SMAN::ASH-ASH-LEMMA2))
 (27 27 (:TYPE-PRESCRIPTION NATP))
 (27 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (27 3
     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (27 3
     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (27 3
     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (27 3
     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (27 1
     (:REWRITE |(<= 1 (* (/ x) y)) with (< 0 x)|))
 (26 1
     (:REWRITE |(< (* (/ x) y) 1) with (< 0 x)|))
 (15 3 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (15 3 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (15 3 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (15 3 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (15 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
 (15 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (15 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (15 3
     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (15 3
     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (15 3
     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (15 3
     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (15 3
     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (15 3
     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
 (15 3
     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (15 3
     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (12 12 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (12 12 (:REWRITE REDUCE-RATIONALP-+))
 (12 12 (:REWRITE REDUCE-RATIONALP-*))
 (12 12 (:REWRITE RATIONALP-MINUS-X))
 (12 12 (:META META-RATIONALP-CORRECT))
 (9 3 (:REWRITE SMAN::STP-!R))
 (7 7 (:REWRITE |(< (+ (- c) x) y)|))
 (3 3 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
 (3 3 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (3 3 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (3 3 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (3 3 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (3 3 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (2 2 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (1 1 (:REWRITE DEFAULT-DIVIDE))
 (1 1 (:REWRITE |(not (equal x (/ y)))|))
 (1 1 (:REWRITE |(equal x (/ y))|))
 (1 1
    (:REWRITE |(<= 1 (* (/ x) y)) with (< x 0)|))
 (1 1
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (1 1
    (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
 (1 1 (:REWRITE |(/ (/ x))|)))
(SMAN::!R-DEFAULT-1-NEGATIVE-INTEGER
 (50658 56 (:LINEAR LINEAR-FLOOR-BOUNDS-1))
 (21946 242 (:REWRITE THE-FLOOR-ABOVE))
 (20712 14 (:REWRITE SMAN::UNNECESSARY-MOD))
 (20269 14 (:REWRITE MOD-ZERO . 4))
 (16131 14 (:REWRITE MOD-X-Y-=-X . 3))
 (15972 14 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (15507 14 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (14930 14 (:REWRITE MOD-X-Y-=-X . 4))
 (12991 12991
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (12991 12991
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (12991 12991
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (12914 12914
        (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (11117 1223 (:REWRITE DEFAULT-TIMES-2))
 (9624 14 (:REWRITE CANCEL-MOD-+))
 (9322 588 (:REWRITE DEFAULT-PLUS-1))
 (8920 588 (:REWRITE DEFAULT-PLUS-2))
 (8089 84 (:REWRITE CANCEL-FLOOR-+))
 (7108 556 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (7108 556
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (7108 556
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (7108 556
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (7108 556
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (5558 84 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (5510 38 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (5449
  5449
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (5449
      5449
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (5449
     5449
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (5449 5449
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (5401 320 (:REWRITE |(* (- x) y)|))
 (4946 84 (:REWRITE FLOOR-ZERO . 3))
 (4893 1223 (:REWRITE DEFAULT-TIMES-1))
 (3926 14 (:REWRITE MOD-ZERO . 3))
 (3892 86 (:REWRITE DEFAULT-FLOOR-RATIO))
 (3832 556 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (3832 556 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (3832 556
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (3832 556
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (3832 556
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (3832 556
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (3832 556
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (3832 556
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
 (3832 556
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (3832 556
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (3822 84 (:REWRITE FLOOR-=-X/Y . 2))
 (3770 377 (:REWRITE DEFAULT-DIVIDE))
 (3476 28 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (3289 157 (:REWRITE INTEGERP-MINUS-X))
 (3003 863 (:REWRITE DEFAULT-MINUS))
 (2580 84 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (2553 49 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (2550 14 (:REWRITE DEFAULT-MOD-RATIO))
 (2433 45 (:REWRITE |(* (* x y) z)|))
 (2008 84 (:REWRITE FLOOR-ZERO . 5))
 (2008 84 (:REWRITE FLOOR-ZERO . 4))
 (1980 84 (:REWRITE FLOOR-ZERO . 2))
 (1980 84 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (1980 84 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (1832 56 (:REWRITE |(integerp (- x))|))
 (1518 242 (:REWRITE THE-FLOOR-BELOW))
 (1511 222
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (1466 14 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (1466 14
       (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (1430 14 (:REWRITE MOD-X-Y-=-X . 2))
 (1170 84 (:REWRITE FLOOR-CANCEL-*-CONST))
 (1126 226 (:REWRITE DEFAULT-LESS-THAN-2))
 (966 222
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (954 84
      (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (949 79
      (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (949 79
      (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (920 8 (:REWRITE DEFAULT-LOGAND-2))
 (788 86 (:REWRITE DEFAULT-FLOOR-2))
 (782 14 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (782 14 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (776 86 (:REWRITE SMAN::UNNECESSARY-FLOOR))
 (770 28 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (722 14 (:REWRITE MOD-CANCEL-*-CONST))
 (673 14
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (662 14 (:REWRITE DEFAULT-MOD-1))
 (659 14
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (651 226 (:REWRITE DEFAULT-LESS-THAN-1))
 (472 472 (:REWRITE DEFAULT-EXPT-2))
 (472 472 (:REWRITE DEFAULT-EXPT-1))
 (472 472 (:REWRITE |(expt (- x) n)|))
 (447 222 (:REWRITE SIMPLIFY-SUMS-<))
 (426 84
      (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (418 418
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (346 79
      (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (224 224
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (222 222
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (222 222 (:REWRITE INTEGERP-<-CONSTANT))
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
 (187 187 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (187 25 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (178 25 (:LINEAR EXPT->-1-ONE))
 (158 86 (:REWRITE DEFAULT-FLOOR-1))
 (153 153 (:REWRITE REDUCE-INTEGERP-+))
 (153 153 (:META META-INTEGERP-CORRECT))
 (143 143
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (143 143
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (143 143
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (143 143
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (142 25 (:LINEAR EXPT->=-1-ONE))
 (140 14 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
 (139 139 (:REWRITE |(< (* x y) 0)|))
 (137 137
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (137 137
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (137 137 (:REWRITE |(< (/ x) 0)|))
 (136 4 (:REWRITE FLOOR-POSITIVE . 3))
 (128 8 (:REWRITE |(floor x 1)|))
 (124 4 (:REWRITE FLOOR-POSITIVE . 2))
 (124 4 (:REWRITE FLOOR-NONPOSITIVE . 1))
 (118 3
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4A-EXPT))
 (106 4 (:REWRITE |(mod x 1)|))
 (102 50
      (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (100 4 (:REWRITE FLOOR-POSITIVE . 4))
 (100 4 (:REWRITE FLOOR-NONPOSITIVE . 3))
 (100 4 (:REWRITE FLOOR-NONPOSITIVE . 2))
 (84 84 (:REWRITE |(floor x (- y))| . 2))
 (84 84 (:REWRITE |(floor x (- y))| . 1))
 (84 84 (:REWRITE |(floor (- x) y)| . 2))
 (84 84 (:REWRITE |(floor (- x) y)| . 1))
 (68 14 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (68 14
     (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (68 14
     (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (64 4 (:REWRITE FLOOR-=-X/Y . 4))
 (64 4
     (:REWRITE |(equal (floor (+ x y) z) x)|))
 (58 58
     (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (50 50
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (50 50
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (50 50
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (50 14 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (50 14 (:REWRITE DEFAULT-MOD-2))
 (45 45
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (45 45
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (45 45 (:REWRITE |(< 0 (/ x))|))
 (45 45 (:REWRITE |(< 0 (* x y))|))
 (44 14 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (38 38 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (38 38 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (38 38 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (34 34 (:TYPE-PRESCRIPTION SMAN::STP))
 (32 14 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
 (30 14 (:REWRITE SMAN::!MI-MI))
 (30 8 (:REWRITE SMAN::!R-R))
 (25 25 (:REWRITE |(- (- x))|))
 (25 25 (:LINEAR EXPT-X->=-X))
 (25 25 (:LINEAR EXPT-X->-X))
 (25 25 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (25 25 (:LINEAR EXPT-LINEAR-UPPER-<))
 (25 25 (:LINEAR EXPT-LINEAR-LOWER-<))
 (25 25 (:LINEAR EXPT->=-1-TWO))
 (25 25 (:LINEAR EXPT->-1-TWO))
 (25 25 (:LINEAR EXPT-<=-1-TWO))
 (25 25 (:LINEAR EXPT-<=-1-ONE))
 (25 25 (:LINEAR EXPT-<-1-TWO))
 (25 25 (:LINEAR EXPT-<-1-ONE))
 (20 14 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (17 3 (:REWRITE ACL2-NUMBERP-X))
 (16 16 (:REWRITE ODD-EXPT-THM))
 (16 16 (:REWRITE |(+ x (- x))|))
 (14 14 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (14 14
     (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (14 14 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (14 14 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
 (14 14
     (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
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
 (14 14 (:REWRITE SMAN::!MI-DEFAULT-1))
 (12 12
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (12 12
     (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (12 4 (:REWRITE SMAN::STP-!MI))
 (10 10 (:REWRITE |(< y (+ (- c) x))|))
 (10 10 (:REWRITE |(< x (+ c/d y))|))
 (9 9
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (8 8 (:REWRITE DEFAULT-LOGAND-1))
 (8 8 (:REWRITE |(mod x (- y))| . 3))
 (8 8 (:REWRITE |(mod x (- y))| . 2))
 (8 8 (:REWRITE |(mod x (- y))| . 1))
 (8 8 (:REWRITE |(mod (- x) y)| . 3))
 (8 8 (:REWRITE |(mod (- x) y)| . 2))
 (8 8 (:REWRITE |(mod (- x) y)| . 1))
 (7 7
    (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (7 7 (:REWRITE SMAN::!R-!MI-BELOW))
 (7 1 (:REWRITE RATIONALP-X))
 (6 6
    (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (5 5 (:REWRITE |(equal (* x y) 0)|))
 (4 4 (:REWRITE ZP-OPEN))
 (4 4 (:REWRITE FLOOR-ZERO . 1))
 (4 4 (:REWRITE FLOOR-POSITIVE . 1))
 (4 4 (:REWRITE |(mod (floor x y) z)| . 5))
 (4 4 (:REWRITE |(mod (floor x y) z)| . 4))
 (4 4 (:REWRITE |(mod (floor x y) z)| . 3))
 (4 4 (:REWRITE |(mod (floor x y) z)| . 2))
 (4 4 (:REWRITE |(* c (* d x))|))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (2 2 (:REWRITE |(< (+ c/d x) y)|))
 (1 1 (:REWRITE REDUCE-RATIONALP-+))
 (1 1 (:REWRITE REDUCE-RATIONALP-*))
 (1 1 (:REWRITE RATIONALP-MINUS-X))
 (1 1 (:REWRITE |(equal x (if a b c))|))
 (1 1 (:META META-RATIONALP-CORRECT)))
(SMAN::!R-DEFAULT-1
 (613948 700 (:LINEAR LINEAR-FLOOR-BOUNDS-1))
 (271501 3009 (:REWRITE THE-FLOOR-ABOVE))
 (265800 194 (:REWRITE SMAN::UNNECESSARY-MOD))
 (250154 194 (:REWRITE MOD-ZERO . 4))
 (200714 190 (:REWRITE MOD-X-Y-=-X . 3))
 (199368 194 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (193074 194 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (186711 190 (:REWRITE MOD-X-Y-=-X . 4))
 (161829 161829
         (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (161829 161829
         (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (161829 161829
         (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (160455 160455
         (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (133986 14450 (:REWRITE DEFAULT-TIMES-2))
 (122278 190 (:REWRITE CANCEL-MOD-+))
 (111178 7336 (:REWRITE DEFAULT-PLUS-2))
 (88929 6885
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (88929 6885
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (88929 6885
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (88929 6885
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (88929 6885
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (79798 934 (:REWRITE CANCEL-FLOOR-+))
 (69064 664
        (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (64038 934 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (62294 4602 (:REWRITE |(* (- x) y)|))
 (58090
  58090
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (58090
      58090
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (58090
     58090
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (58090 58090
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (55730 14450 (:REWRITE DEFAULT-TIMES-1))
 (55594 934 (:REWRITE FLOOR-ZERO . 3))
 (54262 350 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (47907 6885
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (47907 6885
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (47907 6885
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (47907 6885
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (47907 6885
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (47907 6885
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (47907 6885
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (47907 6885
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
 (47907 6885
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (47907 6885
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (46380 4638 (:REWRITE DEFAULT-DIVIDE))
 (42976 1002 (:REWRITE DEFAULT-FLOOR-RATIO))
 (42580 934 (:REWRITE FLOOR-=-X/Y . 2))
 (33154 194 (:REWRITE DEFAULT-MOD-RATIO))
 (31618 606 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (29034 934 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (22840 934 (:REWRITE FLOOR-ZERO . 2))
 (22840 934 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (22840 934 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (22016 934 (:REWRITE FLOOR-ZERO . 5))
 (21998 934 (:REWRITE FLOOR-ZERO . 4))
 (18959 3009 (:REWRITE THE-FLOOR-BELOW))
 (18254 190
        (:REWRITE |(mod (+ x (mod a b)) y)|))
 (18254 190
        (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (17858 190 (:REWRITE MOD-X-Y-=-X . 2))
 (17693 2711
        (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (14962 430 (:REWRITE |(integerp (- x))|))
 (13960 934 (:REWRITE FLOOR-CANCEL-*-CONST))
 (13913 2809 (:REWRITE DEFAULT-LESS-THAN-2))
 (11974 934
        (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (11948 908
        (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (11948 908
        (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (11124 2711
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (10002 1002 (:REWRITE SMAN::UNNECESSARY-FLOOR))
 (9798 194 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (9798 194 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (9580 120 (:REWRITE DEFAULT-LOGAND-2))
 (9570 1002 (:REWRITE DEFAULT-FLOOR-2))
 (9364 190 (:REWRITE MOD-CANCEL-*-CONST))
 (8695 241
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (8453 241
       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (8310 194 (:REWRITE DEFAULT-MOD-1))
 (8080 350 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (6957 2809 (:REWRITE DEFAULT-LESS-THAN-1))
 (5646 5646 (:REWRITE DEFAULT-EXPT-1))
 (5642 5642 (:REWRITE |(expt (- x) n)|))
 (5465 2711 (:REWRITE SIMPLIFY-SUMS-<))
 (5112 5112
       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (3700 934
       (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (3391 3391
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (3391 3391
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (3391 3391
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (3391 3391
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (3284 908
       (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (3012 66
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4A-EXPT))
 (2761 2757
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (2711 2711
       (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (2711 2711 (:REWRITE INTEGERP-<-CONSTANT))
 (2711 2711 (:REWRITE CONSTANT-<-INTEGERP))
 (2711 2711
       (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (2711 2711
       (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (2711 2711
       (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (2711 2711
       (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (2711 2711 (:REWRITE |(< c (- x))|))
 (2711 2711
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (2711 2711
       (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (2711 2711
       (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (2711 2711
       (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (2711 2711 (:REWRITE |(< (/ x) (/ y))|))
 (2711 2711 (:REWRITE |(< (- x) c)|))
 (2711 2711 (:REWRITE |(< (- x) (- y))|))
 (2442 306 (:LINEAR EXPT->-1-ONE))
 (2281 2281
       (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (1750 1750 (:REWRITE |(< (* x y) 0)|))
 (1702 1702
       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1702 1702
       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1702 1702 (:REWRITE |(< (/ x) 0)|))
 (1700 170 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
 (1700 50 (:REWRITE FLOOR-POSITIVE . 3))
 (1662 42 (:REWRITE |(mod x 1)|))
 (1632 306 (:LINEAR EXPT->=-1-ONE))
 (1550 50 (:REWRITE FLOOR-POSITIVE . 2))
 (1550 50 (:REWRITE FLOOR-NONPOSITIVE . 1))
 (1454 306 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (1364 1364 (:REWRITE REDUCE-INTEGERP-+))
 (1364 1364 (:META META-INTEGERP-CORRECT))
 (1308 1002 (:REWRITE DEFAULT-FLOOR-1))
 (1250 50 (:REWRITE FLOOR-POSITIVE . 4))
 (1250 50 (:REWRITE FLOOR-NONPOSITIVE . 3))
 (1250 50 (:REWRITE FLOOR-NONPOSITIVE . 2))
 (974 170 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (974 170
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (974 170
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (938 170 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (934 934 (:REWRITE |(floor x (- y))| . 2))
 (934 934 (:REWRITE |(floor x (- y))| . 1))
 (934 934 (:REWRITE |(floor (- x) y)| . 2))
 (934 934 (:REWRITE |(floor (- x) y)| . 1))
 (800 50 (:REWRITE FLOOR-=-X/Y . 4))
 (800 50
      (:REWRITE |(equal (floor (+ x y) z) x)|))
 (716 612
      (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (696 696
      (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (664 664
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (664 664
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (664 664
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (660 660 (:TYPE-PRESCRIPTION SMAN::STP))
 (633 191 (:REWRITE SMAN::!R-R))
 (612 612
      (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (612 612
      (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (612 612
      (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (590 194 (:REWRITE DEFAULT-MOD-2))
 (533 90 (:REWRITE ACL2-NUMBERP-X))
 (475 475
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (475 475
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (475 475 (:REWRITE |(< 0 (/ x))|))
 (475 475 (:REWRITE |(< 0 (* x y))|))
 (462 170 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (444 24 (:REWRITE |(/ (if a b c))|))
 (391 135 (:REWRITE SMAN::!MI-MI))
 (337 241 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (306 306 (:LINEAR EXPT-X->=-X))
 (306 306 (:LINEAR EXPT-X->-X))
 (306 306 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (306 306 (:LINEAR EXPT-LINEAR-UPPER-<))
 (306 306 (:LINEAR EXPT-LINEAR-LOWER-<))
 (306 306 (:LINEAR EXPT->=-1-TWO))
 (306 306 (:LINEAR EXPT->-1-TWO))
 (306 306 (:LINEAR EXPT-<=-1-TWO))
 (306 306 (:LINEAR EXPT-<=-1-ONE))
 (306 306 (:LINEAR EXPT-<-1-TWO))
 (306 306 (:LINEAR EXPT-<-1-ONE))
 (243 241
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (242 50 (:REWRITE RATIONALP-X))
 (241 241
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (241 241
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (241 241 (:REWRITE |(equal c (/ x))|))
 (241 241 (:REWRITE |(equal c (- x))|))
 (241 241 (:REWRITE |(equal (/ x) c)|))
 (241 241 (:REWRITE |(equal (/ x) (/ y))|))
 (241 241 (:REWRITE |(equal (- x) c)|))
 (241 241 (:REWRITE |(equal (- x) (- y))|))
 (206 170 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
 (204 204 (:REWRITE ODD-EXPT-THM))
 (200 200 (:REWRITE |(+ x (- x))|))
 (194 194
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (170 170 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (170 170
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (170 170
      (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (170 170
      (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
 (170 170
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (154 154
      (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (135 135 (:REWRITE SMAN::!MI-DEFAULT-1))
 (126 64 (:REWRITE DEFAULT-CDR))
 (126 64 (:REWRITE DEFAULT-CAR))
 (122 122 (:REWRITE |(- (- x))|))
 (120 120 (:REWRITE DEFAULT-LOGAND-1))
 (114 38 (:REWRITE SMAN::STP-!MI))
 (108 108 (:REWRITE |(mod x (- y))| . 3))
 (108 108 (:REWRITE |(mod x (- y))| . 2))
 (108 108 (:REWRITE |(mod x (- y))| . 1))
 (108 108 (:REWRITE |(mod (- x) y)| . 3))
 (108 108 (:REWRITE |(mod (- x) y)| . 2))
 (108 108 (:REWRITE |(mod (- x) y)| . 1))
 (106 106
      (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (102 102
      (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (82 82 (:REWRITE |(equal (* x y) 0)|))
 (72 72
     (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (72 72 (:REWRITE |(* c (* d x))|))
 (66 66
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (66 66
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (66 66
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (59 38 (:REWRITE SMAN::!R-!MI-BELOW))
 (50 50 (:REWRITE FLOOR-ZERO . 1))
 (50 50 (:REWRITE FLOOR-POSITIVE . 1))
 (50 50 (:REWRITE |(mod (floor x y) z)| . 5))
 (50 50 (:REWRITE |(mod (floor x y) z)| . 4))
 (50 50 (:REWRITE |(mod (floor x y) z)| . 3))
 (50 50 (:REWRITE |(mod (floor x y) z)| . 2))
 (46 46 (:REWRITE REDUCE-RATIONALP-+))
 (46 46 (:REWRITE REDUCE-RATIONALP-*))
 (46 46 (:REWRITE RATIONALP-MINUS-X))
 (46 46 (:REWRITE |(< (+ c/d x) y)|))
 (46 46 (:META META-RATIONALP-CORRECT))
 (40 40 (:REWRITE |(< y (+ (- c) x))|))
 (40 40 (:REWRITE |(< x (+ c/d y))|))
 (12 12 (:REWRITE ZP-OPEN))
 (4 4 (:REWRITE |(equal x (if a b c))|)))
(SMAN::ONE-BYTE-READ-STRONGER
     (575 575 (:TYPE-PRESCRIPTION SMAN::!R))
     (525 18
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (458 49 (:REWRITE ACL2-NUMBERP-X))
     (411 411
          (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
     (191 23 (:REWRITE RATIONALP-X))
     (169 18 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (169 18
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (120 20 (:LINEAR SMAN::BYTEP-MI))
     (96 96 (:REWRITE THE-FLOOR-BELOW))
     (96 96 (:REWRITE THE-FLOOR-ABOVE))
     (96 96
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (96 96
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (96 96
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (96 96
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (96 96 (:REWRITE INTEGERP-<-CONSTANT))
     (96 96 (:REWRITE DEFAULT-LESS-THAN-2))
     (96 96 (:REWRITE DEFAULT-LESS-THAN-1))
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
     (87 87 (:REWRITE SIMPLIFY-SUMS-<))
     (87 87
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (87 87 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (74 74 (:REWRITE DEFAULT-PLUS-2))
     (74 74 (:REWRITE DEFAULT-PLUS-1))
     (64 64 (:REWRITE REDUCE-INTEGERP-+))
     (64 64 (:REWRITE INTEGERP-MINUS-X))
     (64 64 (:META META-INTEGERP-CORRECT))
     (60 20 (:REWRITE SMAN::STP-!R))
     (58 58
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (58 58 (:REWRITE NORMALIZE-ADDENDS))
     (51 51 (:REWRITE |(< (/ x) 0)|))
     (51 51 (:REWRITE |(< (* x y) 0)|))
     (51 14 (:REWRITE SMAN::!R-R))
     (49 49
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (49 49
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (47 47
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (47 47 (:REWRITE DEFAULT-TIMES-2))
     (47 47 (:REWRITE DEFAULT-TIMES-1))
     (47 47 (:REWRITE |(* (- x) y)|))
     (29 29 (:REWRITE DEFAULT-LOGAND-1))
     (27 27
         (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 2))
     (27 9 (:REWRITE SMAN::!MI-MI))
     (26 26 (:REWRITE |(< y (+ (- c) x))|))
     (26 26 (:REWRITE |(< x (+ c/d y))|))
     (23 23 (:REWRITE REDUCE-RATIONALP-+))
     (23 23 (:REWRITE REDUCE-RATIONALP-*))
     (23 23 (:REWRITE RATIONALP-MINUS-X))
     (23 23 (:META META-RATIONALP-CORRECT))
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
     (18 18 (:REWRITE |(< 0 (/ x))|))
     (18 18 (:REWRITE |(< 0 (* x y))|))
     (16 16
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (16 16
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (14 14 (:REWRITE ZP-OPEN))
     (13 13 (:REWRITE DEFAULT-MINUS))
     (9 9 (:REWRITE SMAN::!MI-DEFAULT-1))
     (9 3 (:REWRITE SMAN::STP-!MI))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (4 1 (:REWRITE SMAN::MI-!R-))
     (4 1 (:REWRITE SMAN::MI-!R+))
     (3 3 (:REWRITE |(equal x (if a b c))|))
     (3 3 (:REWRITE SMAN::!R-!MI-BELOW))
     (2 2 (:TYPE-PRESCRIPTION NATP)))
(SMAN::WEAK-STP-IMPLIES-WEAK-ML-NON-ZERO)
(SMAN::WEAK-ML-!R-STRONGER
 (67570 70 (:LINEAR LINEAR-FLOOR-BOUNDS-1))
 (28184 422 (:REWRITE THE-FLOOR-ABOVE))
 (26353 16 (:REWRITE MOD-ZERO . 4))
 (24621 16 (:REWRITE SMAN::UNNECESSARY-MOD))
 (21336 16 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (20801 16 (:REWRITE MOD-X-Y-=-X . 3))
 (20070 16 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (19385 16 (:REWRITE MOD-X-Y-=-X . 4))
 (16384 16384
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (16384 16384
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (16384 16384
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (16320 16320
        (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (14346 1413 (:REWRITE DEFAULT-TIMES-2))
 (12181 714 (:REWRITE DEFAULT-PLUS-1))
 (11775 714 (:REWRITE DEFAULT-PLUS-2))
 (11684 16 (:REWRITE CANCEL-MOD-+))
 (11542 101 (:REWRITE CANCEL-FLOOR-+))
 (9006 702 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (9006 702
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (9006 702
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (9006 702
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (9006 702
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (8147 101 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (7462
  7462
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (7462
      7462
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (7462
     7462
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (7462 7462
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (7436 101 (:REWRITE FLOOR-ZERO . 3))
 (6889 49 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (6529 421 (:REWRITE |(* (- x) y)|))
 (5695 1413 (:REWRITE DEFAULT-TIMES-1))
 (5512 101 (:REWRITE FLOOR-=-X/Y . 2))
 (4879 101 (:REWRITE DEFAULT-FLOOR-RATIO))
 (4860 486 (:REWRITE DEFAULT-DIVIDE))
 (4854 702 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (4854 702 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (4854 702
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (4854 702
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (4854 702
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (4854 702
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (4854 702
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (4854 702
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
 (4854 702
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (4854 702
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (4816 16 (:REWRITE MOD-ZERO . 3))
 (4573 101 (:REWRITE FLOOR-=-X/Y . 3))
 (4212 297 (:REWRITE INTEGERP-MINUS-X))
 (4100 1057 (:REWRITE DEFAULT-MINUS))
 (3495 101 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (3337 103 (:REWRITE |(integerp (- x))|))
 (3158 46 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (2866 16 (:REWRITE DEFAULT-MOD-RATIO))
 (2771 101 (:REWRITE FLOOR-ZERO . 5))
 (2753 101 (:REWRITE FLOOR-ZERO . 4))
 (2420 101 (:REWRITE FLOOR-ZERO . 2))
 (2420 101 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (2420 101 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (2259 378
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (2017 422 (:REWRITE THE-FLOOR-BELOW))
 (1886 41 (:REWRITE |(* (* x y) z)|))
 (1874 16 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (1874 16
       (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (1802 16 (:REWRITE MOD-X-Y-=-X . 2))
 (1698 35 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (1687 378
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (1627 402 (:REWRITE DEFAULT-LESS-THAN-2))
 (1565 101 (:REWRITE FLOOR-CANCEL-*-CONST))
 (1530 10 (:REWRITE DEFAULT-LOGAND-2))
 (1173 35 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (1151 402 (:REWRITE DEFAULT-LESS-THAN-1))
 (1151 101
       (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (1147 97
       (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (1147 97
       (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (1061 101 (:REWRITE SMAN::UNNECESSARY-FLOOR))
 (1015 16 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (1015 16 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (947 101 (:REWRITE DEFAULT-FLOOR-2))
 (943 16
      (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (943 16 (:REWRITE MOD-CANCEL-*-CONST))
 (846 33
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (846 33
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (803 16 (:REWRITE DEFAULT-MOD-1))
 (765 378 (:REWRITE SIMPLIFY-SUMS-<))
 (612 612 (:REWRITE DEFAULT-EXPT-2))
 (612 612 (:REWRITE DEFAULT-EXPT-1))
 (612 612 (:REWRITE |(expt (- x) n)|))
 (524 101
      (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (522 522
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (460 97
      (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (397 397
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (393 393 (:REWRITE INTEGERP-<-CONSTANT))
 (393 393 (:REWRITE CONSTANT-<-INTEGERP))
 (393 393
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (393 393
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (393 393
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (393 393
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (393 393 (:REWRITE |(< c (- x))|))
 (393 393
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (393 393
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (393 393
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (393 393
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (393 393 (:REWRITE |(< (/ x) (/ y))|))
 (393 393 (:REWRITE |(< (- x) c)|))
 (393 393 (:REWRITE |(< (- x) (- y))|))
 (384 42 (:LINEAR EXPT->-1-ONE))
 (375 71
      (:REWRITE SMAN::STP-IMPLIES-WEAK-STP))
 (316 316 (:TYPE-PRESCRIPTION SMAN::STP))
 (292 292 (:REWRITE REDUCE-INTEGERP-+))
 (292 292 (:META META-INTEGERP-CORRECT))
 (276 42 (:LINEAR EXPT->=-1-ONE))
 (264 42 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (240 84
      (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (221 221 (:REWRITE |(< (* x y) 0)|))
 (217 217 (:REWRITE |(< (/ x) 0)|))
 (215 215
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (215 215
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (190 19 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
 (187 7 (:REWRITE |(floor x 1)|))
 (172 19 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (172 19
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (172 19
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (170 5 (:REWRITE FLOOR-POSITIVE . 3))
 (164 101 (:REWRITE DEFAULT-FLOOR-1))
 (155 5 (:REWRITE FLOOR-POSITIVE . 2))
 (155 5 (:REWRITE FLOOR-NONPOSITIVE . 1))
 (148 19 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (144 144
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (144 144
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (144 144
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (144 144
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (136 19 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
 (134 2
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4A-EXPT))
 (126 9
      (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (125 5 (:REWRITE FLOOR-POSITIVE . 4))
 (125 5 (:REWRITE FLOOR-NONPOSITIVE . 3))
 (125 5 (:REWRITE FLOOR-NONPOSITIVE . 2))
 (108 42 (:LINEAR EXPT-LINEAR-LOWER-<))
 (108 30 (:REWRITE SMAN::STP-!R))
 (101 101 (:REWRITE |(floor x (- y))| . 2))
 (101 101 (:REWRITE |(floor x (- y))| . 1))
 (101 101 (:REWRITE |(floor (- x) y)| . 2))
 (101 101 (:REWRITE |(floor (- x) y)| . 1))
 (93 3 (:REWRITE |(mod x 1)|))
 (88 16 (:REWRITE DEFAULT-MOD-2))
 (87 29 (:REWRITE SMAN::STP-!MI))
 (84 84
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (84 84
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (84 84
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (80 5 (:REWRITE FLOOR-=-X/Y . 4))
 (80 5
     (:REWRITE |(equal (floor (+ x y) z) x)|))
 (73 73
     (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (66 9 (:REWRITE ACL2-NUMBERP-X))
 (64 64 (:REWRITE |(< 0 (/ x))|))
 (64 64 (:REWRITE |(< 0 (* x y))|))
 (62 62
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (62 62
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (58 33 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (55 19 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (51 17 (:REWRITE SMAN::!MI-MI))
 (49 49 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (49 49 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (49 49 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (48 11 (:REWRITE SMAN::!R-R))
 (42 42 (:LINEAR EXPT-X->=-X))
 (42 42 (:LINEAR EXPT-X->-X))
 (42 42 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (42 42 (:LINEAR EXPT-LINEAR-UPPER-<))
 (42 42 (:LINEAR EXPT->=-1-TWO))
 (42 42 (:LINEAR EXPT->-1-TWO))
 (42 42 (:LINEAR EXPT-<=-1-TWO))
 (42 42 (:LINEAR EXPT-<=-1-ONE))
 (42 42 (:LINEAR EXPT-<-1-TWO))
 (42 42 (:LINEAR EXPT-<-1-ONE))
 (33 33
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (33 33
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (33 33
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (33 33 (:REWRITE |(equal c (/ x))|))
 (33 33 (:REWRITE |(equal c (- x))|))
 (33 33 (:REWRITE |(equal (/ x) c)|))
 (33 33 (:REWRITE |(equal (/ x) (/ y))|))
 (33 33 (:REWRITE |(equal (- x) c)|))
 (33 33 (:REWRITE |(equal (- x) (- y))|))
 (27 27 (:REWRITE |(< y (+ (- c) x))|))
 (27 27 (:REWRITE |(< x (+ c/d y))|))
 (26 26 (:REWRITE |(- (- x))|))
 (24 24 (:REWRITE ODD-EXPT-THM))
 (21 9 (:REWRITE RATIONALP-X))
 (20 20 (:REWRITE |(+ x (- x))|))
 (19 19 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (19 19
     (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (19 19 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (19 19 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
 (19 19
     (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (18 18 (:REWRITE ZP-OPEN))
 (17 17 (:REWRITE SMAN::!MI-DEFAULT-1))
 (16 16
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (16 16
     (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (13 13 (:REWRITE |(< (+ c/d x) y)|))
 (11 11 (:REWRITE |(mod x (- y))| . 3))
 (11 11 (:REWRITE |(mod x (- y))| . 2))
 (11 11 (:REWRITE |(mod x (- y))| . 1))
 (11 11 (:REWRITE |(mod (- x) y)| . 3))
 (11 11 (:REWRITE |(mod (- x) y)| . 2))
 (11 11 (:REWRITE |(mod (- x) y)| . 1))
 (10 10 (:REWRITE DEFAULT-LOGAND-1))
 (9 9 (:REWRITE REDUCE-RATIONALP-+))
 (9 9 (:REWRITE REDUCE-RATIONALP-*))
 (9 9 (:REWRITE RATIONALP-MINUS-X))
 (9 9
    (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (9 9
    (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (9 9
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (9 9 (:REWRITE |(< (+ (- c) x) y)|))
 (9 9 (:META META-RATIONALP-CORRECT))
 (5 5 (:REWRITE FLOOR-ZERO . 1))
 (5 5 (:REWRITE FLOOR-POSITIVE . 1))
 (5 5 (:REWRITE |(mod (floor x y) z)| . 5))
 (5 5 (:REWRITE |(mod (floor x y) z)| . 4))
 (5 5 (:REWRITE |(mod (floor x y) z)| . 3))
 (5 5 (:REWRITE |(mod (floor x y) z)| . 2))
 (5 5 (:REWRITE |(equal (+ (- c) x) y)|))
 (5 5 (:REWRITE SMAN::!R-!MI-BELOW))
 (3 3 (:TYPE-PRESCRIPTION NATP))
 (3 3 (:REWRITE |(equal x (if a b c))|))
 (3 3 (:REWRITE |(equal (* x y) 0)|))
 (2 2
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (2 2
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (2 2
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (2 2 (:REWRITE |(* c (* d x))|)))
(SMAN::STRONGER-DEMO-THM--NO-DIVERGENCE)
(SMAN::WEAK-STP-!MI
     (210 3 (:DEFINITION UPDATE-NTH))
     (192 6 (:REWRITE SMAN::!NTH-NTH))
     (123 3 (:REWRITE |(< (+ (- c) x) y)|))
     (80 80 (:REWRITE DEFAULT-CDR))
     (66 36 (:REWRITE DEFAULT-PLUS-2))
     (36 36 (:REWRITE DEFAULT-PLUS-1))
     (29 29
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (29 29 (:REWRITE NORMALIZE-ADDENDS))
     (27 20 (:REWRITE DEFAULT-LESS-THAN-2))
     (20 20 (:REWRITE THE-FLOOR-BELOW))
     (20 20 (:REWRITE THE-FLOOR-ABOVE))
     (20 20 (:REWRITE DEFAULT-LESS-THAN-1))
     (15 15
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (15 15
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (15 15
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (15 11
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (15 11 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (14 11 (:REWRITE SIMPLIFY-SUMS-<))
     (13 13 (:REWRITE DEFAULT-CAR))
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
     (8 8 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (6 3
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (5 5 (:REWRITE |(< y (+ (- c) x))|))
     (5 5 (:REWRITE |(< x (+ c/d y))|))
     (5 3
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (4 4 (:REWRITE REDUCE-INTEGERP-+))
     (4 4 (:REWRITE INTEGERP-MINUS-X))
     (4 4 (:META META-INTEGERP-CORRECT))
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
     (3 3 (:REWRITE |(equal (+ (- c) x) y)|))
     (3 3 (:REWRITE |(< 0 (/ x))|))
     (3 3 (:REWRITE |(< 0 (* x y))|))
     (3 3 (:REWRITE |(< (+ c/d x) y)|))
     (3 1 (:REWRITE SMAN::STP-IMPLIES-WEAK-STP))
     (2 2 (:TYPE-PRESCRIPTION SMAN::STP))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (2 2 (:REWRITE |(< (/ x) 0)|))
     (2 2 (:REWRITE |(< (* x y) 0)|)))
(SMAN::WEAK-STP-!R
 (6540483 4542 (:LINEAR LINEAR-FLOOR-BOUNDS-1))
 (2054993 457 (:REWRITE SMAN::UNNECESSARY-MOD))
 (1631826 13503 (:REWRITE THE-FLOOR-ABOVE))
 (1556535 1556535
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (1556535 1556535
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (1556535 1556535
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (1435982 457 (:REWRITE MOD-ZERO . 4))
 (1238816 5416 (:REWRITE CANCEL-FLOOR-+))
 (951569 457 (:REWRITE MOD-X-Y-=-X . 3))
 (942457 457 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (931226 457 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (916496 457 (:REWRITE MOD-X-Y-=-X . 4))
 (869125 89185 (:REWRITE DEFAULT-TIMES-1))
 (824927 5416 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (816836 5416 (:REWRITE FLOOR-ZERO . 4))
 (762559 5416 (:REWRITE FLOOR-ZERO . 5))
 (731340 5416 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (714235 5416 (:REWRITE FLOOR-ZERO . 3))
 (690935 86591
         (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (690935 86591
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (690935 86591
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (690935 86591
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (690935 86591
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (560079 22185 (:REWRITE DEFAULT-PLUS-1))
 (490295 10892 (:REWRITE |(* (- x) y)|))
 (489416 89185 (:REWRITE DEFAULT-TIMES-2))
 (460596 9408 (:REWRITE |(* (* x y) z)|))
 (458207 5416 (:REWRITE FLOOR-=-X/Y . 2))
 (399662 5455 (:REWRITE DEFAULT-FLOOR-RATIO))
 (388763 86591
         (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (388763 86591
         (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (388763 86591
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (388763 86591
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (388763 86591
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (388763 86591
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (388763 86591
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (388763 86591
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
 (388763 86591
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (388763 86591
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (347816 2990 (:REWRITE |(integerp (- x))|))
 (294291 36652
         (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (288171 457 (:REWRITE CANCEL-MOD-+))
 (226293
  226293
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (226293
      226293
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (226293
     226293
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (226293 226293
         (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (213934 213934
         (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (205944 20070 (:REWRITE DEFAULT-MINUS))
 (193786 13675 (:REWRITE INTEGERP-MINUS-X))
 (165444 2271 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (151602 2669 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (149378 5416 (:REWRITE FLOOR-ZERO . 2))
 (149378 5416 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (149378 5416 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (142341 11089
         (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (136696 5416 (:REWRITE FLOOR-CANCEL-*-CONST))
 (118692 457 (:REWRITE MOD-ZERO . 3))
 (117428 5296
         (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (117250 5118
         (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (115600 5416
         (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (111910 5455 (:REWRITE DEFAULT-FLOOR-1))
 (111139 12034 (:REWRITE DEFAULT-LESS-THAN-1))
 (104835 13503 (:REWRITE THE-FLOOR-BELOW))
 (95884 2271 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (94962 5118
        (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (86077 11089
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (74073 457 (:REWRITE DEFAULT-MOD-RATIO))
 (60662 12034 (:REWRITE DEFAULT-LESS-THAN-2))
 (56160 5616 (:REWRITE DEFAULT-DIVIDE))
 (41917 457
        (:REWRITE |(mod (+ x (mod a b)) y)|))
 (41917 457
        (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (41881 457 (:REWRITE MOD-X-Y-=-X . 2))
 (36652 36652
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (36652 36652
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (36652 36652
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (34799 11089 (:REWRITE SIMPLIFY-SUMS-<))
 (24624 1824 (:REWRITE |(floor x 1)|))
 (21955 457 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (21955 457 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (21887 457 (:REWRITE MOD-CANCEL-*-CONST))
 (21084 278 (:REWRITE ODD-EXPT-THM))
 (20639 589
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (20639 589
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (20383 457 (:REWRITE DEFAULT-MOD-1))
 (18302 926
        (:REWRITE |(floor (floor x y) z)| . 5))
 (18224 1 (:REWRITE |(logand y (if a b c))|))
 (17338 410 (:REWRITE FLOOR-POSITIVE . 2))
 (17338 410 (:REWRITE FLOOR-NONPOSITIVE . 1))
 (16668 410 (:REWRITE FLOOR-POSITIVE . 3))
 (16255 5455 (:REWRITE DEFAULT-FLOOR-2))
 (16038 410 (:REWRITE FLOOR-NONPOSITIVE . 2))
 (16014 1 (:REWRITE |(floor (if a b c) x)|))
 (14624 5118
        (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (12669 11498
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (12253 275
        (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (11110 11110 (:REWRITE INTEGERP-<-CONSTANT))
 (11110 11110 (:REWRITE CONSTANT-<-INTEGERP))
 (11110 11110
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (11110 11110
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (11110 11110
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (11110 11110
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (11110 11110 (:REWRITE |(< c (- x))|))
 (11110 11110
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (11110 11110
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (11110 11110
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (11110 11110
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (11110 11110 (:REWRITE |(< (/ x) (/ y))|))
 (11110 11110 (:REWRITE |(< (- x) c)|))
 (11110 11110 (:REWRITE |(< (- x) (- y))|))
 (11068 11068 (:REWRITE REDUCE-INTEGERP-+))
 (11068 11068 (:META META-INTEGERP-CORRECT))
 (10630 154
        (:REWRITE |(mod (floor x y) z)| . 3))
 (10328 10328
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (9504 410 (:REWRITE FLOOR-POSITIVE . 4))
 (9504 410 (:REWRITE FLOOR-NONPOSITIVE . 3))
 (9352 154
       (:REWRITE |(mod (floor x y) z)| . 5))
 (8118 24 (:LINEAR MOD-BOUNDS-3))
 (7026 7026 (:REWRITE |(< (* x y) 0)|))
 (6916 6916 (:REWRITE DEFAULT-EXPT-2))
 (6916 6916 (:REWRITE DEFAULT-EXPT-1))
 (6916 6916 (:REWRITE |(expt (- x) n)|))
 (6650 926
       (:REWRITE |(floor (floor x y) z)| . 4))
 (6650 926
       (:REWRITE |(floor (floor x y) z)| . 3))
 (6650 926
       (:REWRITE |(floor (floor x y) z)| . 2))
 (6622 154 (:REWRITE FLOOR-=-X/Y . 4))
 (6622 154
       (:REWRITE |(equal (floor (+ x y) z) x)|))
 (6439 6439
       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (6439 6439
       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (6439 6439 (:REWRITE |(< (/ x) 0)|))
 (5162 5162 (:REWRITE |(floor x (- y))| . 2))
 (5162 5162 (:REWRITE |(floor x (- y))| . 1))
 (5162 5162 (:REWRITE |(floor (- x) y)| . 2))
 (5162 5162 (:REWRITE |(floor (- x) y)| . 1))
 (3948 3948
       (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (3335 385
       (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (3276 48 (:LINEAR MOD-BOUNDS-2))
 (2930 362 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (2930 362
       (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (2930 362
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (2658 2658 (:TYPE-PRESCRIPTION SMAN::STP))
 (2604 84 (:REWRITE |(mod x 1)|))
 (2378 362 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (2099 1809 (:REWRITE DEFAULT-CDR))
 (2035 2035 (:REWRITE |(< 0 (* x y))|))
 (2013 2013 (:REWRITE |(< 0 (/ x))|))
 (1996 1996
       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (1996 1996
       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (1971 616 (:REWRITE SMAN::!MI-MI))
 (1965 275
       (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (1696 355 (:REWRITE SMAN::!R-R))
 (1469 1469 (:REWRITE |(+ x (- x))|))
 (1283 623 (:REWRITE SMAN::STP-!MI))
 (914 362 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (850 322 (:LINEAR EXPT->-1-ONE))
 (830 194
      (:REWRITE SMAN::STP-IMPLIES-WEAK-STP))
 (644 644
      (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (644 644
      (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (644 644
      (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (644 644
      (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (638 638
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (634 322 (:LINEAR EXPT->=-1-ONE))
 (589 589 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (589 589
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (589 589 (:REWRITE |(equal c (/ x))|))
 (589 589 (:REWRITE |(equal c (- x))|))
 (589 589 (:REWRITE |(equal (/ x) c)|))
 (589 589 (:REWRITE |(equal (/ x) (/ y))|))
 (589 589 (:REWRITE |(equal (- x) c)|))
 (589 589 (:REWRITE |(equal (- x) (- y))|))
 (580 580
      (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (540 60 (:REWRITE |(* (/ x) (expt x n))|))
 (534 63 (:REWRITE ACL2-NUMBERP-X))
 (493 457 (:REWRITE DEFAULT-MOD-2))
 (453 453
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (410 410 (:REWRITE FLOOR-POSITIVE . 1))
 (406 154
      (:REWRITE |(mod (floor x y) z)| . 4))
 (386 386 (:REWRITE |(< (+ c/d x) y)|))
 (370 223 (:REWRITE DEFAULT-CAR))
 (364 47 (:REWRITE SMAN::!MI-!MI-DIFF))
 (362 362 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (362 362
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (362 362
      (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (362 362
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (326 326 (:TYPE-PRESCRIPTION ASH))
 (322 322 (:LINEAR EXPT-X->=-X))
 (322 322 (:LINEAR EXPT-X->-X))
 (322 322 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (322 322 (:LINEAR EXPT-LINEAR-UPPER-<))
 (322 322 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (322 322 (:LINEAR EXPT-LINEAR-LOWER-<))
 (322 322 (:LINEAR EXPT->=-1-TWO))
 (322 322 (:LINEAR EXPT->-1-TWO))
 (322 322 (:LINEAR EXPT-<=-1-TWO))
 (322 322 (:LINEAR EXPT-<=-1-ONE))
 (322 322 (:LINEAR EXPT-<-1-TWO))
 (322 322 (:LINEAR EXPT-<-1-ONE))
 (279 279 (:REWRITE |(mod x (- y))| . 3))
 (279 279 (:REWRITE |(mod x (- y))| . 2))
 (279 279 (:REWRITE |(mod x (- y))| . 1))
 (279 279 (:REWRITE |(mod (- x) y)| . 3))
 (279 279 (:REWRITE |(mod (- x) y)| . 2))
 (279 279 (:REWRITE |(mod (- x) y)| . 1))
 (275 275
      (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (268 4
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4A-EXPT))
 (220 220 (:REWRITE |(- (- x))|))
 (219 63 (:REWRITE RATIONALP-X))
 (209 1 (:REWRITE |(* (if a b c) x)|))
 (196 196 (:REWRITE |(* c (* d x))|))
 (187 51 (:REWRITE SMAN::STP-!R))
 (176 176 (:REWRITE |(< x (+ c/d y))|))
 (174 174 (:REWRITE FOLD-CONSTS-IN-+))
 (166 166 (:REWRITE DEFAULT-LOGAND-1))
 (156 156 (:REWRITE |(equal (* x y) 0)|))
 (154 154 (:REWRITE FLOOR-ZERO . 1))
 (154 154 (:REWRITE |(< y (+ (- c) x))|))
 (142 142
      (:REWRITE |(mod (floor x y) z)| . 2))
 (63 63 (:REWRITE REDUCE-RATIONALP-+))
 (63 63 (:REWRITE REDUCE-RATIONALP-*))
 (63 63 (:REWRITE RATIONALP-MINUS-X))
 (63 63 (:META META-RATIONALP-CORRECT))
 (59 32 (:REWRITE |(+ x (if a b c))|))
 (28 2 (:DEFINITION NFIX))
 (20 20 (:REWRITE |(< (+ (- c) x) y)|))
 (16 16 (:REWRITE |(equal x (if a b c))|))
 (8 4 (:REWRITE SMAN::ASH-ASH-LEMMA2))
 (6 6 (:REWRITE |(equal (+ (- c) x) y)|))
 (4 4
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (4 4
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (4 4
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT)))
(SMAN::STRONGER-DEMO-THM
 (1344966 1434 (:LINEAR LINEAR-FLOOR-BOUNDS-1))
 (449720 6414 (:REWRITE THE-FLOOR-ABOVE))
 (410958 211 (:REWRITE MOD-ZERO . 4))
 (403467 211 (:REWRITE SMAN::UNNECESSARY-MOD))
 (368012 76 (:REWRITE SMAN::!R-R))
 (328007 211 (:REWRITE MOD-X-Y-=-X . 3))
 (325469 211 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (315876 211 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (297551 211 (:REWRITE MOD-X-Y-=-X . 4))
 (274174 274174
         (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (274174 274174
         (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (274174 274174
         (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (254476 367
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (221510 1766 (:REWRITE FLOOR-ZERO . 3))
 (220018 26272 (:REWRITE DEFAULT-TIMES-2))
 (203367 1766 (:REWRITE CANCEL-FLOOR-+))
 (190133 12343 (:REWRITE DEFAULT-PLUS-2))
 (185546 12343 (:REWRITE DEFAULT-PLUS-1))
 (177662 211 (:REWRITE CANCEL-MOD-+))
 (152879 12683
         (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (152879 12683
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (152879 12683
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (152879 12683
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (152879 12683
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (143725 13 (:REWRITE SMAN::!MI-MI))
 (140802 1766 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (116252
  116252
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (116252
      116252
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (116252
     116252
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (116252 116252
         (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (110464 7683 (:REWRITE |(* (- x) y)|))
 (108940 952
         (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (106732 717 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (96871 26272 (:REWRITE DEFAULT-TIMES-1))
 (96244 1766 (:REWRITE FLOOR-=-X/Y . 2))
 (88317 1772 (:REWRITE DEFAULT-FLOOR-RATIO))
 (82847 8234 (:REWRITE DEFAULT-DIVIDE))
 (82781 12683
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (82781 12683
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (82781 12683
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (82781 12683
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (82781 12683
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (82781 12683
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (82781 12683
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (82781 12683
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
 (82781 12683
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (82781 12683
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (72655 211 (:REWRITE MOD-ZERO . 3))
 (69290 19941 (:REWRITE DEFAULT-MINUS))
 (65707 3532 (:REWRITE INTEGERP-MINUS-X))
 (60731 1766 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (54101 1613 (:REWRITE |(integerp (- x))|))
 (51389 945 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (47407 1766 (:REWRITE FLOOR-ZERO . 5))
 (47407 1766 (:REWRITE FLOOR-ZERO . 4))
 (44195 211 (:REWRITE DEFAULT-MOD-RATIO))
 (41762 1766 (:REWRITE FLOOR-ZERO . 2))
 (41762 1766 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (41762 1766 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (31619 6414 (:REWRITE THE-FLOOR-BELOW))
 (27524 211
        (:REWRITE |(mod (+ x (mod a b)) y)|))
 (27524 211
        (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (27332 1766 (:REWRITE FLOOR-CANCEL-*-CONST))
 (26987 211 (:REWRITE MOD-X-Y-=-X . 2))
 (26692 14 (:LINEAR SMAN::DIVERGENT-ADDR-LEGAL))
 (25750 6082 (:REWRITE DEFAULT-LESS-THAN-2))
 (23714 1760
        (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (23682 1728
        (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (22566 1728
        (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (20995 20 (:LINEAR MOD-BOUNDS-1))
 (19850 1772 (:REWRITE SMAN::UNNECESSARY-FLOOR))
 (19069 717 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (18106 367
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (17351 6082 (:REWRITE DEFAULT-LESS-THAN-1))
 (16256 1772 (:REWRITE DEFAULT-FLOOR-2))
 (14530 211 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (14530 211 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (13993 211 (:REWRITE MOD-CANCEL-*-CONST))
 (12668 211 (:REWRITE DEFAULT-MOD-1))
 (10191 9657 (:REWRITE DEFAULT-EXPT-2))
 (9657 9657 (:REWRITE DEFAULT-EXPT-1))
 (9657 9657 (:REWRITE |(expt (- x) n)|))
 (8106 8106
       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (6176 100 (:REWRITE FLOOR-=-X/Y . 4))
 (6082 14 (:DEFINITION MIN))
 (5700 5700
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (5624 5624
       (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (5624 5624 (:REWRITE INTEGERP-<-CONSTANT))
 (5624 5624 (:REWRITE CONSTANT-<-INTEGERP))
 (5624 5624
       (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (5624 5624
       (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (5624 5624
       (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (5624 5624
       (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (5624 5624 (:REWRITE |(< c (- x))|))
 (5624 5624
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (5624 5624
       (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (5624 5624
       (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (5624 5624
       (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (5624 5624 (:REWRITE |(< (/ x) (/ y))|))
 (5624 5624 (:REWRITE |(< (- x) c)|))
 (5624 5624 (:REWRITE |(< (- x) (- y))|))
 (5214 1398
       (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (5121 699 (:LINEAR EXPT->-1-ONE))
 (4840 4840
       (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (4836 1728
       (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (4452 6 (:DEFINITION IFIX))
 (3996 3996
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (3996 3996
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (3996 3996
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (3996 3996
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (3938 1398
       (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (3910 121
       (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (3582 699 (:LINEAR EXPT->=-1-ONE))
 (3437 3437 (:REWRITE REDUCE-INTEGERP-+))
 (3437 3437 (:META META-INTEGERP-CORRECT))
 (3230 1772 (:REWRITE DEFAULT-FLOOR-1))
 (3179 20 (:REWRITE SMAN::STP-!MI))
 (3122 3122 (:REWRITE |(< (* x y) 0)|))
 (3089 3089 (:REWRITE |(< (/ x) 0)|))
 (3057 3057
       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (3057 3057
       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2756 83 (:REWRITE FLOOR-POSITIVE . 3))
 (2676 168 (:REWRITE |(floor x 1)|))
 (2550 1275
       (:TYPE-PRESCRIPTION SMAN::NATP-NTH-MP))
 (2525 83 (:REWRITE FLOOR-POSITIVE . 2))
 (2525 83 (:REWRITE FLOOR-NONPOSITIVE . 1))
 (2072 494 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (2072 494 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (2072 494
       (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (2072 494
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (2057 83 (:REWRITE FLOOR-NONPOSITIVE . 2))
 (2003 83 (:REWRITE FLOOR-POSITIVE . 4))
 (2003 83 (:REWRITE FLOOR-NONPOSITIVE . 3))
 (1843 699 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (1760 1760 (:REWRITE |(floor x (- y))| . 2))
 (1760 1760 (:REWRITE |(floor x (- y))| . 1))
 (1760 1760 (:REWRITE |(floor (- x) y)| . 2))
 (1760 1760 (:REWRITE |(floor (- x) y)| . 1))
 (1576 100
       (:REWRITE |(equal (floor (+ x y) z) x)|))
 (1398 1398
       (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (1398 1398
       (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (1395 45 (:REWRITE |(mod x 1)|))
 (1263 699 (:LINEAR EXPT-X->-X))
 (1121 1121
       (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (1047 699 (:LINEAR EXPT-X->=-X))
 (998 200 (:TYPE-PRESCRIPTION MAX))
 (952 952
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (952 952
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (952 952
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (940 468 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (924 924 (:REWRITE |(< 0 (* x y))|))
 (881 881
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (881 881
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (881 881 (:REWRITE |(< 0 (/ x))|))
 (880 10 (:LINEAR MOD-BOUNDS-3))
 (748 211 (:REWRITE DEFAULT-MOD-2))
 (735 699 (:LINEAR EXPT-<=-1-TWO))
 (735 699 (:LINEAR EXPT-<-1-TWO))
 (699 699 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (699 699 (:LINEAR EXPT-LINEAR-UPPER-<))
 (699 699 (:LINEAR EXPT-LINEAR-LOWER-<))
 (699 699 (:LINEAR EXPT->=-1-TWO))
 (699 699 (:LINEAR EXPT->-1-TWO))
 (699 699 (:LINEAR EXPT-<=-1-ONE))
 (699 699 (:LINEAR EXPT-<-1-ONE))
 (570 498 (:REWRITE ODD-EXPT-THM))
 (540 16 (:TYPE-PRESCRIPTION MIN))
 (494 494 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (494 494
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (494 494
      (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (494 494
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (492 492 (:TYPE-PRESCRIPTION SMAN::R))
 (468 468 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
 (406 46 (:REWRITE ACL2-NUMBERP-X))
 (382 368 (:REWRITE |(equal (/ x) c)|))
 (379 199
      (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (368 368
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (368 368
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (368 368 (:REWRITE |(equal c (/ x))|))
 (368 368 (:REWRITE |(equal (/ x) (/ y))|))
 (368 368 (:REWRITE |(equal (- x) (- y))|))
 (367 367
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (367 367 (:REWRITE |(equal c (- x))|))
 (367 367 (:REWRITE |(equal (- x) c)|))
 (359 359 (:REWRITE |(< (+ c/d x) y)|))
 (326 326 (:REWRITE |(< (+ (- c) x) y)|))
 (319 319 (:REWRITE |(< y (+ (- c) x))|))
 (319 319 (:REWRITE |(< x (+ c/d y))|))
 (301 121
      (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (296 34 (:REWRITE SMAN::STP-!R))
 (286 13
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4A-EXPT))
 (249 249
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (200 20 (:LINEAR MOD-BOUNDS-2))
 (190 190 (:REWRITE DEFAULT-LOGAND-1))
 (180 45 (:REWRITE RATIONALP-X))
 (168 72 (:LINEAR SMAN::R-BOUND))
 (140 140 (:REWRITE FOLD-CONSTS-IN-+))
 (140 10 (:REWRITE SMAN::!R-!R-DIFF-BELOW))
 (134 134 (:REWRITE |(mod x (- y))| . 3))
 (134 134 (:REWRITE |(mod x (- y))| . 2))
 (134 134 (:REWRITE |(mod x (- y))| . 1))
 (134 134 (:REWRITE |(mod (- x) y)| . 3))
 (134 134 (:REWRITE |(mod (- x) y)| . 2))
 (134 134 (:REWRITE |(mod (- x) y)| . 1))
 (121 121
      (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (113 113
      (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (87 29 (:LINEAR SMAN::BYTEP-NTH-MP))
 (83 83 (:REWRITE FLOOR-ZERO . 1))
 (83 83 (:REWRITE FLOOR-POSITIVE . 1))
 (83 83 (:REWRITE |(mod (floor x y) z)| . 5))
 (83 83 (:REWRITE |(mod (floor x y) z)| . 4))
 (83 83 (:REWRITE |(mod (floor x y) z)| . 3))
 (83 83 (:REWRITE |(mod (floor x y) z)| . 2))
 (80 10 (:REWRITE SMAN::!R-!R-DIFF-ABOVE))
 (61 61 (:REWRITE |(equal (+ (- c) x) y)|))
 (57 57 (:REWRITE |(equal (* x y) 0)|))
 (54 6 (:REWRITE |(* (/ x) (expt x n))|))
 (45 45 (:REWRITE REDUCE-RATIONALP-+))
 (45 45 (:REWRITE REDUCE-RATIONALP-*))
 (45 45 (:REWRITE RATIONALP-MINUS-X))
 (45 45 (:META META-RATIONALP-CORRECT))
 (45 15 (:LINEAR SMAN::BYTEP-MI))
 (43 43
     (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (43 43
     (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (43 43
     (:REWRITE |(< x (/ y)) with (< y 0)|))
 (39 12 (:REWRITE DEFAULT-CDR))
 (39 12 (:REWRITE DEFAULT-CAR))
 (31 31 (:REWRITE |(* c (* d x))|))
 (26 26 (:TYPE-PRESCRIPTION INTEGERP-MOD-3))
 (19 19 (:TYPE-PRESCRIPTION SMAN::ML))
 (13 13
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (13 13
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (13 13
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (13 13 (:REWRITE SMAN::!R-!MI-BELOW))
 (13 13 (:REWRITE SMAN::!MI-DEFAULT-1))
 (9 2 (:TYPE-PRESCRIPTION SMAN::NATP-I))
 (7 7 (:DEFINITION SMAN::ML))
 (4 4 (:TYPE-PRESCRIPTION NATP))
 (1 1 (:REWRITE |(not (equal x (/ y)))|))
 (1 1 (:REWRITE |(equal x (/ y))|))
 (1 1 (:REWRITE |(/ (/ x))|)))
(SMAN::!R-SIMPLE-ABSORBTION-LEMMA1)
(SMAN::!R-SIMPLE-ABSORBTION-LEMMA2
     (210 3 (:DEFINITION UPDATE-NTH))
     (195 6 (:REWRITE SMAN::!NTH-NTH))
     (123 3 (:REWRITE |(< (+ (- c) x) y)|))
     (42 42 (:TYPE-PRESCRIPTION LEN))
     (27 27 (:REWRITE DEFAULT-CDR))
     (21 3 (:DEFINITION LEN))
     (15 9 (:REWRITE DEFAULT-PLUS-2))
     (12 12 (:REWRITE DEFAULT-CAR))
     (12 6 (:REWRITE DEFAULT-LESS-THAN-2))
     (9 9
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (9 9 (:REWRITE NORMALIZE-ADDENDS))
     (9 9 (:REWRITE DEFAULT-PLUS-1))
     (6 6 (:REWRITE THE-FLOOR-BELOW))
     (6 6 (:REWRITE THE-FLOOR-ABOVE))
     (6 6
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (6 6
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (6 6 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (6 6 (:REWRITE DEFAULT-LESS-THAN-1))
     (6 3 (:REWRITE SIMPLIFY-SUMS-<))
     (6 3
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (6 3 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (3 3 (:REWRITE ZP-OPEN))
     (3 3 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (3 3 (:REWRITE REDUCE-INTEGERP-+))
     (3 3 (:REWRITE INTEGERP-MINUS-X))
     (3 3 (:REWRITE INTEGERP-<-CONSTANT))
     (3 3 (:REWRITE CONSTANT-<-INTEGERP))
     (3 3 (:REWRITE |(< y (+ (- c) x))|))
     (3 3 (:REWRITE |(< x (+ c/d y))|))
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
     (3 3 (:REWRITE |(< (+ c/d x) y)|))
     (3 3 (:META META-INTEGERP-CORRECT)))
(SMAN::!R-SIMPLE-ABSORBTION-LEMMA3
 (36448 2 (:REWRITE |(logand y (if a b c))|))
 (32028 2 (:REWRITE |(floor (if a b c) x)|))
 (23708 56 (:LINEAR LINEAR-FLOOR-BOUNDS-1))
 (17706 13386
        (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (16477 315 (:REWRITE THE-FLOOR-ABOVE))
 (13386 13386
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (13386 13386
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (13386 13386
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (11542 78 (:REWRITE SMAN::UNNECESSARY-FLOOR))
 (9738 64 (:REWRITE |(+ y x)|))
 (6508 1256
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (6422 76 (:REWRITE CANCEL-FLOOR-+))
 (6057 199 (:REWRITE DEFAULT-PLUS-1))
 (5930 76 (:REWRITE FLOOR-ZERO . 3))
 (5643 81 (:REWRITE NORMALIZE-ADDENDS))
 (5564 16 (:REWRITE SMAN::UNNECESSARY-MOD))
 (5324 76 (:REWRITE FLOOR-ZERO . 4))
 (5294 76 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (5270 76 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (5180 16 (:REWRITE MOD-ZERO . 4))
 (5094 566 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (5094 566
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (5094 566
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (5094 566
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (5094 566
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (4918 6 (:REWRITE |(< (if a b c) x)|))
 (4834 16 (:REWRITE MOD-X-Y-=-X . 3))
 (4682 76 (:REWRITE FLOOR-ZERO . 5))
 (4616 16 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (4574 16 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (4476 360 (:REWRITE INTEGERP-MINUS-X))
 (4260 1150 (:REWRITE DEFAULT-TIMES-2))
 (4192 16 (:REWRITE MOD-X-Y-=-X . 4))
 (3574 1150 (:REWRITE DEFAULT-TIMES-1))
 (3538 430 (:REWRITE |(* y x)|))
 (3474 16 (:REWRITE CANCEL-MOD-+))
 (3174 186 (:REWRITE |(* (- x) y)|))
 (2914 2 (:REWRITE |(mod (floor x y) z)| . 1))
 (2830 566 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
 (2830 566 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (2830 566 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (2830 566
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (2830 566
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (2830 566
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (2830 566
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (2830 566
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (2830 566
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
 (2830 566
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (2830 566
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (2270 78 (:REWRITE DEFAULT-FLOOR-RATIO))
 (2168 76 (:REWRITE FLOOR-=-X/Y . 2))
 (1924 186 (:REWRITE DEFAULT-MINUS))
 (1912 76 (:REWRITE FLOOR-=-X/Y . 3))
 (1848 186 (:REWRITE |(- (* c x))|))
 (1836 18 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (1836 18 (:DEFINITION FIX))
 (1362 16 (:REWRITE MOD-ZERO . 3))
 (1256 1256
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (1256 1256
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (1256 1256
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (1139 315 (:REWRITE THE-FLOOR-BELOW))
 (1055 281
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (893 297 (:REWRITE DEFAULT-LESS-THAN-1))
 (782 16 (:REWRITE DEFAULT-MOD-RATIO))
 (758 2
      (:REWRITE |(floor (floor x y) z)| . 1))
 (701 297 (:REWRITE DEFAULT-LESS-THAN-2))
 (620 620
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (582 76 (:REWRITE FLOOR-ZERO . 2))
 (582 76 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (582 76 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (582 76 (:REWRITE FLOOR-CANCEL-*-CONST))
 (581 291
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (566 566 (:TYPE-PRESCRIPTION FLOOR))
 (488 12 (:DEFINITION NATP))
 (484 16 (:REWRITE MOD-X-Y-=-X . 2))
 (484 16 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (484 16
      (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (482 78 (:REWRITE DEFAULT-FLOOR-1))
 (433 285
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (418 2 (:REWRITE |(* (if a b c) x)|))
 (358 76
      (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (354 28 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (329 285
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (300 76
      (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (298 74
      (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (297 281
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (282 16 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (282 16 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (282 16
      (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (282 16 (:REWRITE MOD-CANCEL-*-CONST))
 (281 281 (:REWRITE SIMPLIFY-SUMS-<))
 (281 281
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (281 281 (:REWRITE INTEGERP-<-CONSTANT))
 (281 281 (:REWRITE CONSTANT-<-INTEGERP))
 (281 281
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (281 281
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (281 281
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (281 281
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (281 281 (:REWRITE |(< c (- x))|))
 (281 281
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (281 281
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (281 281
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (281 281
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (281 281 (:REWRITE |(< (/ x) (/ y))|))
 (281 281 (:REWRITE |(< (- x) c)|))
 (281 281 (:REWRITE |(< (- x) (- y))|))
 (268 268 (:REWRITE REDUCE-INTEGERP-+))
 (268 268 (:META META-INTEGERP-CORRECT))
 (268 18 (:REWRITE SMAN::!MI-DEFAULT-1))
 (262 12 (:REWRITE SMAN::!R-DEFAULT-1))
 (242 28 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (227 19
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (227 19
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (223 223 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (218 16 (:REWRITE DEFAULT-MOD-1))
 (190 190 (:REWRITE |(< (* x y) 0)|))
 (184 24 (:REWRITE ACL2-NUMBERP-X))
 (180 180
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (180 180
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (180 180 (:REWRITE |(< (/ x) 0)|))
 (146 74
      (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (94 94 (:TYPE-PRESCRIPTION ABS))
 (94 22 (:REWRITE |(+ 0 x)|))
 (86 22 (:REWRITE SMAN::!R-R))
 (80 20 (:REWRITE RATIONALP-X))
 (78 78 (:REWRITE DEFAULT-FLOOR-2))
 (74 74 (:REWRITE |(floor x (- y))| . 2))
 (74 74 (:REWRITE |(floor x (- y))| . 1))
 (74 74
     (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (74 74
     (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (74 74 (:REWRITE |(floor (- x) y)| . 2))
 (74 74 (:REWRITE |(floor (- x) y)| . 1))
 (70 14
     (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (64 64 (:TYPE-PRESCRIPTION SMAN::STP))
 (63 63
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (49 49
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (49 49
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (49 49 (:REWRITE |(< 0 (/ x))|))
 (49 49 (:REWRITE |(< 0 (* x y))|))
 (46 46
     (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (44 4 (:REWRITE |(+ y (+ x z))|))
 (36 18 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
 (36 18 (:REWRITE SMAN::!MI-MI))
 (36 8 (:REWRITE |(+ c (+ d x))|))
 (36 4 (:REWRITE FLOOR-POSITIVE . 2))
 (36 4 (:REWRITE FLOOR-NONPOSITIVE . 1))
 (34 18 (:REWRITE SMAN::STP-!MI))
 (26 8 (:REWRITE SMAN::!R-!MI-BELOW))
 (25 19 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (20 20 (:REWRITE REDUCE-RATIONALP-+))
 (20 20 (:REWRITE REDUCE-RATIONALP-*))
 (20 20 (:REWRITE RATIONALP-MINUS-X))
 (20 20 (:META META-RATIONALP-CORRECT))
 (20 4 (:REWRITE FLOOR-POSITIVE . 4))
 (20 4 (:REWRITE FLOOR-POSITIVE . 3))
 (20 4 (:REWRITE FLOOR-NONPOSITIVE . 3))
 (20 4 (:REWRITE FLOOR-NONPOSITIVE . 2))
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
 (18 18 (:REWRITE |(+ x (- x))|))
 (16 16
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (16 16
     (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (16 16 (:REWRITE DEFAULT-MOD-2))
 (16 16 (:REWRITE DEFAULT-LOGAND-1))
 (16 2 (:REWRITE |(+ x (if a b c))|))
 (14
   14
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (14
  14
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (14 14
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (14 14
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (14 14
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (14 14
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (14 14 (:REWRITE |(mod x (- y))| . 3))
 (14 14 (:REWRITE |(mod x (- y))| . 2))
 (14 14 (:REWRITE |(mod x (- y))| . 1))
 (14 14
     (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (14 14
     (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (14 14 (:REWRITE |(mod (- x) y)| . 3))
 (14 14 (:REWRITE |(mod (- x) y)| . 2))
 (14 14 (:REWRITE |(mod (- x) y)| . 1))
 (14 14
     (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (12 12 (:TYPE-PRESCRIPTION NATP))
 (10 2 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (10 2 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (10 2 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (10 2 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (10 2 (:REWRITE FLOOR-=-X/Y . 4))
 (10 2
     (:REWRITE |(equal (floor (+ x y) z) x)|))
 (8 2 (:REWRITE SMAN::!MI-!MI-DIFF))
 (6 6 (:REWRITE |(* a (/ a) b)|))
 (6 2 (:REWRITE DEFAULT-CDR))
 (6 2 (:REWRITE DEFAULT-CAR))
 (4 4 (:REWRITE FLOOR-POSITIVE . 1))
 (4 4 (:REWRITE |(< (+ c/d x) y)|))
 (3 3 (:REWRITE |(< y (+ (- c) x))|))
 (3 3 (:REWRITE |(< x (+ c/d y))|))
 (2 2 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
 (2 2 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (2 2 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (2 2 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (2 2 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
 (2 2 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (2 2 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (2 2 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
 (2 2 (:REWRITE FLOOR-ZERO . 1))
 (2 2 (:REWRITE |(mod (floor x y) z)| . 5))
 (2 2 (:REWRITE |(mod (floor x y) z)| . 4))
 (2 2 (:REWRITE |(mod (floor x y) z)| . 3))
 (2 2 (:REWRITE |(mod (floor x y) z)| . 2))
 (2 2
    (:REWRITE |(floor (floor x y) z)| . 5))
 (2 2
    (:REWRITE |(floor (floor x y) z)| . 4))
 (2 2
    (:REWRITE |(floor (floor x y) z)| . 3))
 (2 2
    (:REWRITE |(floor (floor x y) z)| . 2)))
(SMAN::!R-SIMPLE-ABSORBTION
 (162276 168 (:LINEAR LINEAR-FLOOR-BOUNDS-1))
 (67253 617 (:REWRITE THE-FLOOR-ABOVE))
 (62664 27 (:REWRITE MOD-ZERO . 4))
 (58764 27 (:REWRITE SMAN::UNNECESSARY-MOD))
 (49308 27 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (49149 27 (:REWRITE MOD-X-Y-=-X . 3))
 (47379 27 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (45180 27 (:REWRITE MOD-X-Y-=-X . 4))
 (38580 38580
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (38580 38580
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (38580 38580
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (38421 38421
        (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (29817 2904 (:REWRITE DEFAULT-TIMES-2))
 (27853 1525 (:REWRITE DEFAULT-PLUS-1))
 (27415 1525 (:REWRITE DEFAULT-PLUS-2))
 (26448 27 (:REWRITE CANCEL-MOD-+))
 (25371 219 (:REWRITE CANCEL-FLOOR-+))
 (21384 1656
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (21384 1656
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (21384 1656
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (21384 1656
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (21384 1656
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (16536 120
        (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (15830 219 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (14939
  14939
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (14939
      14939
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (14939
     14939
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (14939 14939
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (14797 219 (:REWRITE FLOOR-ZERO . 3))
 (14529 1032 (:REWRITE |(* (- x) y)|))
 (12180 2904 (:REWRITE DEFAULT-TIMES-1))
 (11889 219 (:REWRITE FLOOR-=-X/Y . 2))
 (11520 1656
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (11520 1656
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (11520 1656
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (11520 1656
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (11520 1656
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (11520 1656
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (11520 1656
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (11520 1656
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
 (11520 1656
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (11520 1656
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (10668 219 (:REWRITE DEFAULT-FLOOR-RATIO))
 (10611 27 (:REWRITE MOD-ZERO . 3))
 (10500 1050 (:REWRITE DEFAULT-DIVIDE))
 (9913 517 (:REWRITE INTEGERP-MINUS-X))
 (9576 2316 (:REWRITE DEFAULT-MINUS))
 (9351 219 (:REWRITE FLOOR-=-X/Y . 3))
 (7500 96 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (7344 219 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (7098 222 (:REWRITE |(integerp (- x))|))
 (6300 27 (:REWRITE DEFAULT-MOD-RATIO))
 (5650 219 (:REWRITE FLOOR-ZERO . 5))
 (5650 219 (:REWRITE FLOOR-ZERO . 4))
 (5295 219 (:REWRITE FLOOR-ZERO . 2))
 (5295 219 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (5295 219 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (4445 617 (:REWRITE THE-FLOOR-BELOW))
 (4313 545
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (4173 27 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (4173 27
       (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (4077 84 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (4065 27 (:REWRITE MOD-X-Y-=-X . 2))
 (3672 24 (:REWRITE DEFAULT-LOGAND-2))
 (3414 219 (:REWRITE FLOOR-CANCEL-*-CONST))
 (3185 569 (:REWRITE DEFAULT-LESS-THAN-2))
 (2898 63 (:REWRITE |(* (* x y) z)|))
 (2817 84 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (2739 219
       (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (2733 213
       (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (2733 213
       (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (2609 545
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (2214 27 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (2214 27 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (2106 27
       (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (2106 27 (:REWRITE MOD-CANCEL-*-CONST))
 (2082 219 (:REWRITE DEFAULT-FLOOR-2))
 (2049 219 (:REWRITE SMAN::UNNECESSARY-FLOOR))
 (1973 32
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (1937 569 (:REWRITE DEFAULT-LESS-THAN-1))
 (1903 32
       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (1878 27 (:REWRITE DEFAULT-MOD-1))
 (1221 1221 (:REWRITE DEFAULT-EXPT-2))
 (1221 1221 (:REWRITE DEFAULT-EXPT-1))
 (1221 1221 (:REWRITE |(expt (- x) n)|))
 (1220 545 (:REWRITE SIMPLIFY-SUMS-<))
 (1090 1090
       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (912 219
      (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (816 213
      (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (669 75 (:LINEAR EXPT->-1-ONE))
 (557 557
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (545 545
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (545 545 (:REWRITE INTEGERP-<-CONSTANT))
 (545 545 (:REWRITE CONSTANT-<-INTEGERP))
 (545 545
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (545 545
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (545 545
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (545 545
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (545 545 (:REWRITE |(< c (- x))|))
 (545 545
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (545 545
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (545 545
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (545 545
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (545 545 (:REWRITE |(< (/ x) (/ y))|))
 (545 545 (:REWRITE |(< (- x) c)|))
 (545 545 (:REWRITE |(< (- x) (- y))|))
 (505 505 (:REWRITE REDUCE-INTEGERP-+))
 (505 505 (:META META-INTEGERP-CORRECT))
 (480 480 (:TYPE-PRESCRIPTION SMAN::!R))
 (457 457 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (426 75 (:LINEAR EXPT->=-1-ONE))
 (408 12 (:REWRITE FLOOR-POSITIVE . 3))
 (384 150
      (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (372 12 (:REWRITE FLOOR-POSITIVE . 2))
 (372 12 (:REWRITE FLOOR-NONPOSITIVE . 1))
 (350 350 (:REWRITE |(< (* x y) 0)|))
 (338 338
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (338 338
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (338 338 (:REWRITE |(< (/ x) 0)|))
 (327 219 (:REWRITE DEFAULT-FLOOR-1))
 (312 12 (:REWRITE |(floor x 1)|))
 (309 75 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (300 12 (:REWRITE FLOOR-POSITIVE . 4))
 (300 12 (:REWRITE FLOOR-NONPOSITIVE . 3))
 (300 12 (:REWRITE FLOOR-NONPOSITIVE . 2))
 (270 27 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
 (243 27 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (243 27
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (243 27
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (219 219 (:REWRITE |(floor x (- y))| . 2))
 (219 219 (:REWRITE |(floor x (- y))| . 1))
 (219 219 (:REWRITE |(floor (- x) y)| . 2))
 (219 219 (:REWRITE |(floor (- x) y)| . 1))
 (216 216
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (216 216
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (216 216
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (216 216
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (207 27 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (201 3
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4A-EXPT))
 (192 12 (:REWRITE FLOOR-=-X/Y . 4))
 (192 12
      (:REWRITE |(equal (floor (+ x y) z) x)|))
 (189 27 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
 (174 12
      (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (150 150
      (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (150 150
      (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (150 150
      (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (135 135
      (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (135 27 (:REWRITE DEFAULT-MOD-2))
 (120 120
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (120 120
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (120 120
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (99 19 (:REWRITE ACL2-NUMBERP-X))
 (95 95
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (95 95
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (95 95 (:REWRITE |(< 0 (/ x))|))
 (95 95 (:REWRITE |(< 0 (* x y))|))
 (93 3 (:REWRITE |(mod x 1)|))
 (84 30 (:REWRITE SMAN::!R-R))
 (81 27 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (75 75 (:LINEAR EXPT-X->=-X))
 (75 75 (:LINEAR EXPT-X->-X))
 (75 75 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (75 75 (:LINEAR EXPT-LINEAR-UPPER-<))
 (75 75 (:LINEAR EXPT-LINEAR-LOWER-<))
 (75 75 (:LINEAR EXPT->=-1-TWO))
 (75 75 (:LINEAR EXPT->-1-TWO))
 (75 75 (:LINEAR EXPT-<=-1-TWO))
 (75 75 (:LINEAR EXPT-<=-1-ONE))
 (75 75 (:LINEAR EXPT-<-1-TWO))
 (75 75 (:LINEAR EXPT-<-1-ONE))
 (72 72 (:TYPE-PRESCRIPTION SMAN::STP))
 (52 32 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (48 48 (:REWRITE ODD-EXPT-THM))
 (48 48 (:REWRITE |(+ x (- x))|))
 (39 39 (:REWRITE |(- (- x))|))
 (37 7 (:REWRITE RATIONALP-X))
 (36 12 (:REWRITE SMAN::!MI-MI))
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
 (27 27 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (27 27
     (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (27 27 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (27 27 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
 (27 27
     (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (27 27
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (27 27
     (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (24 24 (:REWRITE DEFAULT-LOGAND-1))
 (18 6 (:REWRITE SMAN::STP-!R))
 (15 15 (:REWRITE |(mod x (- y))| . 3))
 (15 15 (:REWRITE |(mod x (- y))| . 2))
 (15 15 (:REWRITE |(mod x (- y))| . 1))
 (15 15 (:REWRITE |(mod (- x) y)| . 3))
 (15 15 (:REWRITE |(mod (- x) y)| . 2))
 (15 15 (:REWRITE |(mod (- x) y)| . 1))
 (13 13
     (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (12 12 (:REWRITE FLOOR-ZERO . 1))
 (12 12 (:REWRITE FLOOR-POSITIVE . 1))
 (12 12
     (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (12 12 (:REWRITE |(mod (floor x y) z)| . 5))
 (12 12 (:REWRITE |(mod (floor x y) z)| . 4))
 (12 12 (:REWRITE |(mod (floor x y) z)| . 3))
 (12 12 (:REWRITE |(mod (floor x y) z)| . 2))
 (12 12
     (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (12 12 (:REWRITE |(< (+ c/d x) y)|))
 (12 12 (:REWRITE SMAN::!MI-DEFAULT-1))
 (9 9 (:REWRITE ZP-OPEN))
 (7 7 (:REWRITE REDUCE-RATIONALP-+))
 (7 7 (:REWRITE REDUCE-RATIONALP-*))
 (7 7 (:REWRITE RATIONALP-MINUS-X))
 (7 7 (:REWRITE |(< y (+ (- c) x))|))
 (7 7 (:REWRITE |(< x (+ c/d y))|))
 (7 7 (:META META-RATIONALP-CORRECT))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (3 3
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (3 3 (:REWRITE |(equal (* x y) 0)|))
 (3 3 (:REWRITE |(* c (* d x))|)))
(SMAN::LEMMA1
 (324290 788 (:LINEAR LINEAR-FLOOR-BOUNDS-1))
 (247083 182283
         (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (221270 2318 (:REWRITE THE-FLOOR-ABOVE))
 (182283 182283
         (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (182283 182283
         (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (182283 182283
         (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (132134 882 (:REWRITE |(+ y x)|))
 (93172 962 (:REWRITE SMAN::UNNECESSARY-FLOOR))
 (90097 13943
        (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (86684 958 (:REWRITE CANCEL-FLOOR-+))
 (82180 2422 (:REWRITE DEFAULT-PLUS-1))
 (81936 2422 (:REWRITE DEFAULT-PLUS-2))
 (78980 110 (:REWRITE SMAN::UNNECESSARY-MOD))
 (76336 940 (:REWRITE NORMALIZE-ADDENDS))
 (75105 110 (:REWRITE MOD-ZERO . 4))
 (74719 958 (:REWRITE FLOOR-ZERO . 3))
 (72896 4 (:REWRITE |(logand y (if a b c))|))
 (72178 958 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (72096 958 (:REWRITE FLOOR-ZERO . 4))
 (71869 958 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (70560 7840
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (70560 7840
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (70560 7840
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (70560 7840
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (70560 7840
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (67450 110 (:REWRITE MOD-X-Y-=-X . 3))
 (64325 110 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (64130 110 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (64056 4 (:REWRITE |(floor (if a b c) x)|))
 (62466 958 (:REWRITE FLOOR-ZERO . 5))
 (57820 110 (:REWRITE MOD-X-Y-=-X . 4))
 (57492 2928 (:REWRITE INTEGERP-MINUS-X))
 (56994 13074 (:REWRITE DEFAULT-TIMES-2))
 (45220 110 (:REWRITE CANCEL-MOD-+))
 (44182 13074 (:REWRITE DEFAULT-TIMES-1))
 (44068 4856 (:REWRITE |(* y x)|))
 (43606 30 (:REWRITE |(mod (floor x y) z)| . 1))
 (42306 2166 (:REWRITE |(* (- x) y)|))
 (39200 7840
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
 (39200 7840
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (39200 7840
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (39200 7840
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (39200 7840
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (39200 7840
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (39200 7840
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (39200 7840
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (39200 7840
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
 (39200 7840
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (39200 7840
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (27655 958 (:REWRITE FLOOR-=-X/Y . 2))
 (25740 2166 (:REWRITE DEFAULT-MINUS))
 (24912 2166 (:REWRITE |(- (* c x))|))
 (24888 244 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (24888 244 (:DEFINITION FIX))
 (23815 958 (:REWRITE FLOOR-=-X/Y . 3))
 (21180 962 (:REWRITE DEFAULT-FLOOR-RATIO))
 (17255 110 (:REWRITE MOD-ZERO . 3))
 (14678 2318 (:REWRITE THE-FLOOR-BELOW))
 (13943 13943
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (13943 13943
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (13943 13943
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (12722 2004
        (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (10300 110 (:REWRITE DEFAULT-MOD-RATIO))
 (9452 4 (:REWRITE |(< (if a b c) x)|))
 (8134 2074 (:REWRITE DEFAULT-LESS-THAN-2))
 (7840 7840 (:TYPE-PRESCRIPTION FLOOR))
 (7820 958 (:REWRITE FLOOR-ZERO . 2))
 (7820 958 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (7820 958 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (7552 958 (:REWRITE FLOOR-CANCEL-*-CONST))
 (7392 2074 (:REWRITE DEFAULT-LESS-THAN-1))
 (7082 7082
       (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (6610 110 (:REWRITE MOD-X-Y-=-X . 2))
 (6610 110
       (:REWRITE |(mod (+ x (mod a b)) y)|))
 (6610 110
       (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (5131 2070
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (4668 958
       (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (4634 394 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (4396 962 (:REWRITE DEFAULT-FLOOR-1))
 (4350 30
       (:REWRITE |(floor (floor x y) z)| . 1))
 (4110 958
       (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (4080 928
       (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (3580 110 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (3580 110 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (3580 110
       (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (3520 110 (:REWRITE MOD-CANCEL-*-CONST))
 (3274 147
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (3224 147
       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (3140 110 (:REWRITE DEFAULT-MOD-1))
 (3058 394 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (2443 2006
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (2244 2004
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (2006 2006
       (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (2006 2006
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (2006 2006 (:REWRITE INTEGERP-<-CONSTANT))
 (2006 2006 (:REWRITE CONSTANT-<-INTEGERP))
 (2006 2006
       (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (2006 2006
       (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (2006 2006
       (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (2006 2006
       (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (2006 2006 (:REWRITE |(< c (- x))|))
 (2006 2006
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (2006 2006
       (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (2006 2006
       (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (2006 2006
       (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (2006 2006 (:REWRITE |(< (/ x) (/ y))|))
 (2006 2006 (:REWRITE |(< (- x) c)|))
 (2006 2006 (:REWRITE |(< (- x) (- y))|))
 (2004 2004 (:REWRITE SIMPLIFY-SUMS-<))
 (1928 80 (:REWRITE ZP-OPEN))
 (1860 1860 (:REWRITE REDUCE-INTEGERP-+))
 (1860 1860 (:META META-INTEGERP-CORRECT))
 (1488 928
       (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (1318 1318 (:TYPE-PRESCRIPTION SMAN::STP))
 (1318 1318 (:REWRITE |(< (* x y) 0)|))
 (1254 1254 (:REWRITE |(< (/ x) 0)|))
 (1252 1252
       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1252 1252
       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1220 244 (:REWRITE |(+ 0 x)|))
 (1068 244 (:REWRITE SMAN::!MI-MI))
 (1057 204 (:REWRITE SMAN::!R-R))
 (962 962 (:REWRITE DEFAULT-FLOOR-2))
 (938 938 (:TYPE-PRESCRIPTION ABS))
 (928 928 (:REWRITE |(floor x (- y))| . 2))
 (928 928 (:REWRITE |(floor x (- y))| . 1))
 (928 928
      (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (928 928
      (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (928 928 (:REWRITE |(floor (- x) y)| . 2))
 (928 928 (:REWRITE |(floor (- x) y)| . 1))
 (836 4 (:REWRITE |(* (if a b c) x)|))
 (696 696
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (689 297 (:REWRITE SMAN::STP-!MI))
 (560 112 (:REWRITE |(+ c (+ d x))|))
 (540 60 (:REWRITE FLOOR-POSITIVE . 2))
 (540 60 (:REWRITE FLOOR-NONPOSITIVE . 1))
 (488 244 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
 (441 441
      (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (400 80
      (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (378 378
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (378 378
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (378 378 (:REWRITE |(< 0 (/ x))|))
 (378 378 (:REWRITE |(< 0 (* x y))|))
 (300 60 (:REWRITE FLOOR-POSITIVE . 4))
 (300 60 (:REWRITE FLOOR-POSITIVE . 3))
 (300 60 (:REWRITE FLOOR-NONPOSITIVE . 3))
 (300 60 (:REWRITE FLOOR-NONPOSITIVE . 2))
 (244 244 (:REWRITE |(+ x (- x))|))
 (244 244 (:REWRITE SMAN::!MI-DEFAULT-1))
 (194 147 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (182 62 (:REWRITE SMAN::STP-!R))
 (150 30 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (150 30 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (150 30
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (150 30
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (150 30 (:REWRITE FLOOR-=-X/Y . 4))
 (150 30
      (:REWRITE |(equal (floor (+ x y) z) x)|))
 (147 147
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (147 147
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (147 147
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (147 147 (:REWRITE |(equal c (/ x))|))
 (147 147 (:REWRITE |(equal c (- x))|))
 (147 147 (:REWRITE |(equal (/ x) c)|))
 (147 147 (:REWRITE |(equal (/ x) (/ y))|))
 (147 147 (:REWRITE |(equal (- x) c)|))
 (147 147 (:REWRITE |(equal (- x) (- y))|))
 (124 124 (:REWRITE SMAN::!R-DEFAULT-1))
 (114 50 (:REWRITE DEFAULT-CDR))
 (114 50 (:REWRITE DEFAULT-CAR))
 (110 110
      (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (110 110 (:REWRITE DEFAULT-MOD-2))
 (95 95
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (80 80 (:REWRITE |(mod x (- y))| . 3))
 (80 80 (:REWRITE |(mod x (- y))| . 2))
 (80 80 (:REWRITE |(mod x (- y))| . 1))
 (80 80
     (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (80 80
     (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (80 80 (:REWRITE |(mod (- x) y)| . 3))
 (80 80 (:REWRITE |(mod (- x) y)| . 2))
 (80 80 (:REWRITE |(mod (- x) y)| . 1))
 (80 80
     (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (66 66 (:REWRITE DEFAULT-LOGAND-1))
 (66 66 (:REWRITE |(< y (+ (- c) x))|))
 (66 66 (:REWRITE |(< x (+ c/d y))|))
 (64 64 (:REWRITE |(* a (/ a) b)|))
 (62
   62
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (62
  62
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (62 62
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (62 62
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (62 62
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (62 62
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (62 12 (:REWRITE ACL2-NUMBERP-X))
 (60 60 (:REWRITE FLOOR-POSITIVE . 1))
 (30 30 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
 (30 30 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (30 30
     (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (30 30 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (30 30 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
 (30 30
     (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (30 30 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (30 30 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
 (30 30 (:REWRITE FLOOR-ZERO . 1))
 (30 30 (:REWRITE |(mod (floor x y) z)| . 5))
 (30 30 (:REWRITE |(mod (floor x y) z)| . 4))
 (30 30 (:REWRITE |(mod (floor x y) z)| . 3))
 (30 30 (:REWRITE |(mod (floor x y) z)| . 2))
 (30 30
     (:REWRITE |(floor (floor x y) z)| . 5))
 (30 30
     (:REWRITE |(floor (floor x y) z)| . 4))
 (30 30
     (:REWRITE |(floor (floor x y) z)| . 3))
 (30 30
     (:REWRITE |(floor (floor x y) z)| . 2))
 (25 4 (:REWRITE RATIONALP-X))
 (20 20 (:REWRITE |(equal (+ (- c) x) y)|))
 (4 4 (:REWRITE REDUCE-RATIONALP-+))
 (4 4 (:REWRITE REDUCE-RATIONALP-*))
 (4 4 (:REWRITE RATIONALP-MINUS-X))
 (4 4 (:META META-RATIONALP-CORRECT)))
(SMAN::!R-INNER-ABSORBTION-NATP-CASE
 (45006 108 (:LINEAR LINEAR-FLOOR-BOUNDS-1))
 (36448 2 (:REWRITE |(logand y (if a b c))|))
 (34327 25687
        (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (32028 2 (:REWRITE |(floor (if a b c) x)|))
 (31062 544 (:REWRITE THE-FLOOR-ABOVE))
 (25687 25687
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (25687 25687
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (25687 25687
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (18404 122 (:REWRITE |(+ y x)|))
 (17186 148 (:REWRITE SMAN::UNNECESSARY-FLOOR))
 (12675 2373
        (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (12526 146 (:REWRITE CANCEL-FLOOR-+))
 (11452 360 (:REWRITE DEFAULT-PLUS-1))
 (11418 360 (:REWRITE DEFAULT-PLUS-2))
 (11287 146 (:REWRITE FLOOR-ZERO . 3))
 (11160 34 (:REWRITE SMAN::UNNECESSARY-MOD))
 (10664 158 (:REWRITE NORMALIZE-ADDENDS))
 (10379 34 (:REWRITE MOD-ZERO . 4))
 (10336 146 (:REWRITE FLOOR-ZERO . 4))
 (10285 146 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (10264 146 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (9738 1082
       (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (9738 1082
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (9738 1082
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (9738 1082
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (9738 1082
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (9704 34 (:REWRITE MOD-X-Y-=-X . 3))
 (9267 34 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (9180 34 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (9052 146 (:REWRITE FLOOR-ZERO . 5))
 (8752 612 (:REWRITE INTEGERP-MINUS-X))
 (8420 34 (:REWRITE MOD-X-Y-=-X . 4))
 (8202 2192 (:REWRITE DEFAULT-TIMES-2))
 (7054 34 (:REWRITE CANCEL-MOD-+))
 (6690 814 (:REWRITE |(* y x)|))
 (6636 2192 (:REWRITE DEFAULT-TIMES-1))
 (6280 364 (:REWRITE |(* (- x) y)|))
 (5820 4 (:REWRITE |(mod (floor x y) z)| . 1))
 (5410 1082
       (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
 (5410 1082
       (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (5410 1082
       (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (5410 1082
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (5410 1082
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (5410 1082
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (5410 1082
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (5410 1082
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (5410 1082
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
 (5410 1082
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (5410 1082
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (4726 2 (:REWRITE |(< (if a b c) x)|))
 (4141 146 (:REWRITE FLOOR-=-X/Y . 2))
 (3808 364 (:REWRITE DEFAULT-MINUS))
 (3660 364 (:REWRITE |(- (* c x))|))
 (3638 148 (:REWRITE DEFAULT-FLOOR-RATIO))
 (3629 146 (:REWRITE FLOOR-=-X/Y . 3))
 (3468 34 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (3468 34 (:DEFINITION FIX))
 (2747 34 (:REWRITE MOD-ZERO . 3))
 (2373 2373
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (2373 2373
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (2373 2373
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (2192 544 (:REWRITE THE-FLOOR-BELOW))
 (2009 497
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (1586 34 (:REWRITE DEFAULT-MOD-RATIO))
 (1456 510 (:REWRITE DEFAULT-LESS-THAN-1))
 (1318 510 (:REWRITE DEFAULT-LESS-THAN-2))
 (1186 1186
       (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (1134 146 (:REWRITE FLOOR-ZERO . 2))
 (1134 146 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (1134 146 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (1114 146 (:REWRITE FLOOR-CANCEL-*-CONST))
 (1082 1082 (:TYPE-PRESCRIPTION FLOOR))
 (997 508
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (978 34 (:REWRITE MOD-X-Y-=-X . 2))
 (978 34 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (978 34
      (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (976 4
      (:REWRITE |(floor (floor x y) z)| . 1))
 (754 148 (:REWRITE DEFAULT-FLOOR-1))
 (702 146
      (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (656 54 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (578 146
      (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (577 498
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (574 142
      (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (574 34 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (574 34 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (570 34 (:REWRITE MOD-CANCEL-*-CONST))
 (566 34
      (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (529 497
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (517 40
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (498 498
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (498 498
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (498 498 (:REWRITE INTEGERP-<-CONSTANT))
 (498 498 (:REWRITE CONSTANT-<-INTEGERP))
 (498 498
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (498 498
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (498 498
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (498 498
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (498 498 (:REWRITE |(< c (- x))|))
 (498 498
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (498 498
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (498 498
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (498 498
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (498 498 (:REWRITE |(< (/ x) (/ y))|))
 (498 498 (:REWRITE |(< (- x) c)|))
 (498 498 (:REWRITE |(< (- x) (- y))|))
 (497 497 (:REWRITE SIMPLIFY-SUMS-<))
 (469 40
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (440 54 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (438 34 (:REWRITE DEFAULT-MOD-1))
 (432 432 (:REWRITE REDUCE-INTEGERP-+))
 (432 432 (:META META-INTEGERP-CORRECT))
 (418 2 (:REWRITE |(* (if a b c) x)|))
 (328 328 (:TYPE-PRESCRIPTION SMAN::STP))
 (326 326 (:REWRITE |(< (* x y) 0)|))
 (320 60 (:REWRITE SMAN::!R-R))
 (316 316 (:REWRITE |(< (/ x) 0)|))
 (315 315
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (315 315
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (278 142
      (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (225 27 (:REWRITE ZP-OPEN))
 (198 40 (:REWRITE SMAN::!MI-MI))
 (188 60 (:REWRITE SMAN::STP-!MI))
 (170 34 (:REWRITE |(+ 0 x)|))
 (168 168 (:TYPE-PRESCRIPTION ABS))
 (148 148 (:REWRITE DEFAULT-FLOOR-2))
 (142 142 (:REWRITE |(floor x (- y))| . 2))
 (142 142 (:REWRITE |(floor x (- y))| . 1))
 (142 142
      (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (142 142
      (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (142 142 (:REWRITE |(floor (- x) y)| . 2))
 (142 142 (:REWRITE |(floor (- x) y)| . 1))
 (142 30
      (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (124 124
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (90 90
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (90 90
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (90 90 (:REWRITE |(< 0 (/ x))|))
 (90 90 (:REWRITE |(< 0 (* x y))|))
 (81 81
     (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (74 30 (:REWRITE SMAN::STP-!R))
 (72 8 (:REWRITE FLOOR-POSITIVE . 2))
 (72 8 (:REWRITE FLOOR-NONPOSITIVE . 1))
 (68 34 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
 (65 40 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (60 12 (:REWRITE |(+ c (+ d x))|))
 (57 9 (:REWRITE ACL2-NUMBERP-X))
 (42 34
     (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (40 40
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (40 40
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (40 40
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (40 40 (:REWRITE |(equal c (/ x))|))
 (40 40 (:REWRITE |(equal c (- x))|))
 (40 40 (:REWRITE |(equal (/ x) c)|))
 (40 40 (:REWRITE |(equal (/ x) (/ y))|))
 (40 40 (:REWRITE |(equal (- x) c)|))
 (40 40 (:REWRITE |(equal (- x) (- y))|))
 (40 40 (:REWRITE SMAN::!MI-DEFAULT-1))
 (40 8 (:REWRITE FLOOR-POSITIVE . 4))
 (40 8 (:REWRITE FLOOR-POSITIVE . 3))
 (40 8 (:REWRITE FLOOR-NONPOSITIVE . 3))
 (40 8 (:REWRITE FLOOR-NONPOSITIVE . 2))
 (38 30
     (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (34 34 (:REWRITE DEFAULT-MOD-2))
 (34 34 (:REWRITE |(+ x (- x))|))
 (34 34 (:REWRITE SMAN::!R-DEFAULT-1))
 (33 33
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (32 32 (:REWRITE DEFAULT-LOGAND-1))
 (30
   30
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (30
  30
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (30 30
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (30 30
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (30 30
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (30 30
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (30 30 (:REWRITE |(mod x (- y))| . 3))
 (30 30 (:REWRITE |(mod x (- y))| . 2))
 (30 30 (:REWRITE |(mod x (- y))| . 1))
 (30 30
     (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (30 30
     (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (30 30 (:REWRITE |(mod (- x) y)| . 3))
 (30 30 (:REWRITE |(mod (- x) y)| . 2))
 (30 30 (:REWRITE |(mod (- x) y)| . 1))
 (24 3 (:REWRITE RATIONALP-X))
 (20 6 (:REWRITE DEFAULT-CDR))
 (20 6 (:REWRITE DEFAULT-CAR))
 (20 4 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (20 4 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (20 4 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (20 4 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (20 4 (:REWRITE FLOOR-=-X/Y . 4))
 (20 4
     (:REWRITE |(equal (floor (+ x y) z) x)|))
 (10 10 (:REWRITE |(* a (/ a) b)|))
 (8 8 (:REWRITE FLOOR-POSITIVE . 1))
 (6 6 (:REWRITE |(< y (+ (- c) x))|))
 (6 6 (:REWRITE |(< x (+ c/d y))|))
 (4 4 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
 (4 4 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (4 4 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (4 4 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (4 4 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
 (4 4 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (4 4 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (4 4 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
 (4 4 (:REWRITE FLOOR-ZERO . 1))
 (4 4 (:REWRITE |(mod (floor x y) z)| . 5))
 (4 4 (:REWRITE |(mod (floor x y) z)| . 4))
 (4 4 (:REWRITE |(mod (floor x y) z)| . 3))
 (4 4 (:REWRITE |(mod (floor x y) z)| . 2))
 (4 4
    (:REWRITE |(floor (floor x y) z)| . 5))
 (4 4
    (:REWRITE |(floor (floor x y) z)| . 4))
 (4 4
    (:REWRITE |(floor (floor x y) z)| . 3))
 (4 4
    (:REWRITE |(floor (floor x y) z)| . 2))
 (3 3 (:REWRITE REDUCE-RATIONALP-+))
 (3 3 (:REWRITE REDUCE-RATIONALP-*))
 (3 3 (:REWRITE RATIONALP-MINUS-X))
 (3 3 (:META META-RATIONALP-CORRECT)))
(SMAN::!M-SIMPLE-ABSORBTION-LEMMA
     (1176 40 (:REWRITE SMAN::!NTH-NTH))
     (410 46
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (366 18
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (328 8 (:REWRITE |(< (+ (- c) x) y)|))
     (298 42 (:REWRITE ACL2-NUMBERP-X))
     (153 21 (:REWRITE ZP-OPEN))
     (146 146 (:TYPE-PRESCRIPTION LEN))
     (128 14 (:REWRITE RATIONALP-X))
     (128 14 (:DEFINITION LEN))
     (110 18 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (110 18
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (102 76 (:REWRITE DEFAULT-PLUS-2))
     (76 76 (:REWRITE DEFAULT-PLUS-1))
     (68 16 (:REWRITE |(+ c (+ d x))|))
     (64 46 (:REWRITE DEFAULT-LESS-THAN-2))
     (48 48
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (48 48 (:REWRITE NORMALIZE-ADDENDS))
     (46 46 (:REWRITE THE-FLOOR-BELOW))
     (46 46 (:REWRITE THE-FLOOR-ABOVE))
     (46 46
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (46 46
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (46 46 (:REWRITE DEFAULT-LESS-THAN-1))
     (36 26 (:REWRITE SIMPLIFY-SUMS-<))
     (36 26
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (36 26 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (28 22 (:REWRITE DEFAULT-CAR))
     (26 26
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
     (22 22 (:REWRITE REDUCE-INTEGERP-+))
     (22 22 (:REWRITE INTEGERP-MINUS-X))
     (22 22 (:META META-INTEGERP-CORRECT))
     (20 20 (:REWRITE |(< (+ c/d x) y)|))
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
     (14 14 (:REWRITE REDUCE-RATIONALP-+))
     (14 14 (:REWRITE REDUCE-RATIONALP-*))
     (14 14 (:REWRITE RATIONALP-MINUS-X))
     (14 14 (:META META-RATIONALP-CORRECT))
     (12 12 (:REWRITE |(< y (+ (- c) x))|))
     (12 12 (:REWRITE |(< x (+ c/d y))|))
     (12 12 (:REWRITE |(< (* x y) 0)|))
     (12 12 (:REWRITE |(+ 0 x)|))
     (8 8 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (4 4 (:REWRITE |(< 0 (/ x))|))
     (4 4 (:REWRITE |(< 0 (* x y))|))
     (2 2 (:REWRITE |(< x (if a b c))|))
     (2 2 (:REWRITE |(+ x (if a b c))|)))
(SMAN::!M-SIMPLE-ABSORBTION
     (140 2 (:DEFINITION UPDATE-NTH))
     (130 4 (:REWRITE SMAN::!NTH-NTH))
     (116 86 (:REWRITE DEFAULT-CDR))
     (84 60 (:REWRITE DEFAULT-CAR))
     (82 2 (:REWRITE |(< (+ (- c) x) y)|))
     (78 39
         (:TYPE-PRESCRIPTION TRUE-LISTP-UPDATE-NTH))
     (51 12
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (44 12 (:REWRITE ACL2-NUMBERP-X))
     (39 39 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (28 28 (:TYPE-PRESCRIPTION LEN))
     (19 12 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (19 12
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (16 4 (:REWRITE RATIONALP-X))
     (14 2 (:DEFINITION LEN))
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
     (10 6 (:REWRITE DEFAULT-PLUS-2))
     (8 4 (:REWRITE DEFAULT-LESS-THAN-2))
     (6 6 (:REWRITE REDUCE-INTEGERP-+))
     (6 6
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (6 6 (:REWRITE NORMALIZE-ADDENDS))
     (6 6 (:REWRITE INTEGERP-MINUS-X))
     (6 6 (:REWRITE DEFAULT-PLUS-1))
     (6 6 (:META META-INTEGERP-CORRECT))
     (4 4 (:REWRITE THE-FLOOR-BELOW))
     (4 4 (:REWRITE THE-FLOOR-ABOVE))
     (4 4 (:REWRITE REDUCE-RATIONALP-+))
     (4 4 (:REWRITE REDUCE-RATIONALP-*))
     (4 4
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (4 4
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (4 4 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (4 4 (:REWRITE RATIONALP-MINUS-X))
     (4 4 (:REWRITE DEFAULT-LESS-THAN-1))
     (4 4 (:META META-RATIONALP-CORRECT))
     (4 2 (:REWRITE SIMPLIFY-SUMS-<))
     (4 2
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (4 2 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (2 2 (:REWRITE ZP-OPEN))
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
     (2 2 (:REWRITE |(< (+ c/d x) y)|)))
(SMAN::!M-INNER-ABSORBTION
 (87602 212 (:LINEAR LINEAR-FLOOR-BOUNDS-1))
 (66601 49321
        (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (59942 712 (:REWRITE THE-FLOOR-ABOVE))
 (49321 49321
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (49321 49321
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (49321 49321
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (36448 2 (:REWRITE |(logand y (if a b c))|))
 (35736 238 (:REWRITE |(+ y x)|))
 (32028 2 (:REWRITE |(floor (if a b c) x)|))
 (27668 262 (:REWRITE SMAN::UNNECESSARY-FLOOR))
 (24269 3867
        (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (23356 260 (:REWRITE CANCEL-FLOOR-+))
 (22236 676 (:REWRITE DEFAULT-PLUS-1))
 (21236 34 (:REWRITE SMAN::UNNECESSARY-MOD))
 (20639 245 (:REWRITE NORMALIZE-ADDENDS))
 (20337 260 (:REWRITE FLOOR-ZERO . 3))
 (20129 34 (:REWRITE MOD-ZERO . 4))
 (19450 260 (:REWRITE FLOOR-ZERO . 4))
 (19446 260 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (19383 260 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (19026 2114
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (19026 2114
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (19026 2114
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (19026 2114
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (19026 2114
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (18184 34 (:REWRITE MOD-X-Y-=-X . 3))
 (17345 34 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (17276 34 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (16882 260 (:REWRITE FLOOR-ZERO . 5))
 (15651 889 (:REWRITE INTEGERP-MINUS-X))
 (15616 34 (:REWRITE MOD-X-Y-=-X . 4))
 (15424 3614 (:REWRITE DEFAULT-TIMES-2))
 (12306 34 (:REWRITE CANCEL-MOD-+))
 (12098 3614 (:REWRITE DEFAULT-TIMES-1))
 (12042 1344 (:REWRITE |(* y x)|))
 (11632 8 (:REWRITE |(mod (floor x y) z)| . 1))
 (11438 596 (:REWRITE |(* (- x) y)|))
 (10570 2114
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
 (10570 2114
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (10570 2114
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (10570 2114
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (10570 2114
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (10570 2114
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (10570 2114
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (10570 2114
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (10570 2114
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
 (10570 2114
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (10570 2114
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (7515 260 (:REWRITE FLOOR-=-X/Y . 2))
 (6956 596 (:REWRITE DEFAULT-MINUS))
 (6732 66 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (6732 66 (:DEFINITION FIX))
 (6726 596 (:REWRITE |(- (* c x))|))
 (6491 260 (:REWRITE FLOOR-=-X/Y . 3))
 (6088 262 (:REWRITE DEFAULT-FLOOR-RATIO))
 (4870 5 (:REWRITE |(< (if a b c) x)|))
 (4725 34 (:REWRITE MOD-ZERO . 3))
 (4008 712 (:REWRITE THE-FLOOR-BELOW))
 (3867 3867
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (3867 3867
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (3867 3867
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (3498 614
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (2798 34 (:REWRITE DEFAULT-MOD-RATIO))
 (2262 646 (:REWRITE DEFAULT-LESS-THAN-2))
 (2188 646 (:REWRITE DEFAULT-LESS-THAN-1))
 (2114 2114 (:TYPE-PRESCRIPTION FLOOR))
 (2108 260 (:REWRITE FLOOR-ZERO . 2))
 (2108 260 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (2108 260 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (2048 260 (:REWRITE FLOOR-CANCEL-*-CONST))
 (1956 1956
       (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (1786 34 (:REWRITE MOD-X-Y-=-X . 2))
 (1786 34 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (1786 34
       (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (1502 641
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (1412 8
       (:REWRITE |(floor (floor x y) z)| . 1))
 (1272 262 (:REWRITE DEFAULT-FLOOR-1))
 (1260 260
       (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (1260 106 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (1108 260
       (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (1100 252
       (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (1026 25 (:DEFINITION NATP))
 (978 34 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (978 34 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (978 34
      (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (966 34 (:REWRITE MOD-CANCEL-*-CONST))
 (956 623
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (869 46
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (869 46
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (842 34 (:REWRITE DEFAULT-MOD-1))
 (836 106 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (746 623
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (678 614
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (614 614 (:REWRITE SIMPLIFY-SUMS-<))
 (614 614
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (614 614 (:REWRITE INTEGERP-<-CONSTANT))
 (614 614 (:REWRITE CONSTANT-<-INTEGERP))
 (614 614
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (614 614
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (614 614
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (614 614
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (614 614 (:REWRITE |(< c (- x))|))
 (614 614
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (614 614
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (614 614
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (614 614
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (614 614 (:REWRITE |(< (/ x) (/ y))|))
 (614 614 (:REWRITE |(< (- x) c)|))
 (614 614 (:REWRITE |(< (- x) (- y))|))
 (595 595 (:REWRITE REDUCE-INTEGERP-+))
 (595 595 (:META META-INTEGERP-CORRECT))
 (491 491 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (489 27 (:REWRITE ZP-OPEN))
 (432 432 (:TYPE-PRESCRIPTION SMAN::STP))
 (418 2 (:REWRITE |(* (if a b c) x)|))
 (414 414 (:REWRITE |(< (* x y) 0)|))
 (412 252
      (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (400 94 (:REWRITE SMAN::!MI-MI))
 (387 387
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (387 387
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (387 387 (:REWRITE |(< (/ x) 0)|))
 (371 32 (:REWRITE SMAN::!R-DEFAULT-1))
 (351 87 (:REWRITE |(+ 0 x)|))
 (276 54 (:REWRITE SMAN::!R-R))
 (264 264 (:TYPE-PRESCRIPTION ABS))
 (262 262 (:REWRITE DEFAULT-FLOOR-2))
 (252 252 (:REWRITE |(floor x (- y))| . 2))
 (252 252 (:REWRITE |(floor x (- y))| . 1))
 (252 252
      (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (252 252
      (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (252 252 (:REWRITE |(floor (- x) y)| . 2))
 (252 252 (:REWRITE |(floor (- x) y)| . 1))
 (182 66 (:REWRITE SMAN::STP-!MI))
 (182 22 (:REWRITE ACL2-NUMBERP-X))
 (179 179
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (144 16 (:REWRITE FLOOR-POSITIVE . 2))
 (144 16 (:REWRITE FLOOR-NONPOSITIVE . 1))
 (136 29 (:REWRITE |(+ c (+ d x))|))
 (132 66 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
 (130 26
      (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (125 125
      (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (112 112
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (112 112
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (112 112 (:REWRITE |(< 0 (/ x))|))
 (112 112 (:REWRITE |(< 0 (* x y))|))
 (99 9 (:REWRITE |(+ y (+ x z))|))
 (86 30 (:REWRITE SMAN::STP-!R))
 (84 12
     (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (80 20 (:REWRITE RATIONALP-X))
 (80 16 (:REWRITE FLOOR-POSITIVE . 4))
 (80 16 (:REWRITE FLOOR-POSITIVE . 3))
 (80 16 (:REWRITE FLOOR-NONPOSITIVE . 3))
 (80 16 (:REWRITE FLOOR-NONPOSITIVE . 2))
 (66 66 (:REWRITE |(+ x (- x))|))
 (61 46 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (60 30 (:REWRITE DEFAULT-CDR))
 (60 30 (:REWRITE DEFAULT-CAR))
 (46 46
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (46 46
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (46 46
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (46 46 (:REWRITE |(equal c (/ x))|))
 (46 46 (:REWRITE |(equal c (- x))|))
 (46 46 (:REWRITE |(equal (/ x) c)|))
 (46 46 (:REWRITE |(equal (/ x) (/ y))|))
 (46 46 (:REWRITE |(equal (- x) c)|))
 (46 46 (:REWRITE |(equal (- x) (- y))|))
 (40 8 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (40 8 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (40 8 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (40 8 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (40 8 (:REWRITE FLOOR-=-X/Y . 4))
 (40 8
     (:REWRITE |(equal (floor (+ x y) z) x)|))
 (40 6 (:REWRITE SMAN::!MI-!MI-DIFF))
 (34 34
     (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (34 34 (:REWRITE DEFAULT-MOD-2))
 (31 31
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (26 26 (:REWRITE DEFAULT-LOGAND-1))
 (26 26 (:REWRITE |(mod x (- y))| . 3))
 (26 26 (:REWRITE |(mod x (- y))| . 2))
 (26 26 (:REWRITE |(mod x (- y))| . 1))
 (26 26
     (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (26 26
     (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (26 26 (:REWRITE |(mod (- x) y)| . 3))
 (26 26 (:REWRITE |(mod (- x) y)| . 2))
 (26 26 (:REWRITE |(mod (- x) y)| . 1))
 (26 26
     (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (25 25 (:TYPE-PRESCRIPTION NATP))
 (24
   24
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
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
 (20 20 (:REWRITE REDUCE-RATIONALP-+))
 (20 20 (:REWRITE REDUCE-RATIONALP-*))
 (20 20 (:REWRITE RATIONALP-MINUS-X))
 (20 20 (:META META-RATIONALP-CORRECT))
 (18 18 (:REWRITE |(* a (/ a) b)|))
 (16 16 (:REWRITE FLOOR-POSITIVE . 1))
 (16 2 (:REWRITE |(+ x (if a b c))|))
 (14 14 (:REWRITE |(< y (+ (- c) x))|))
 (14 14 (:REWRITE |(< x (+ c/d y))|))
 (9 9 (:REWRITE |(< (+ c/d x) y)|))
 (8 8 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
 (8 8 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (8 8 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (8 8 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (8 8 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
 (8 8 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (8 8 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (8 8 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
 (8 8 (:REWRITE FLOOR-ZERO . 1))
 (8 8 (:REWRITE |(mod (floor x y) z)| . 5))
 (8 8 (:REWRITE |(mod (floor x y) z)| . 4))
 (8 8 (:REWRITE |(mod (floor x y) z)| . 3))
 (8 8 (:REWRITE |(mod (floor x y) z)| . 2))
 (8 8
    (:REWRITE |(floor (floor x y) z)| . 5))
 (8 8
    (:REWRITE |(floor (floor x y) z)| . 4))
 (8 8
    (:REWRITE |(floor (floor x y) z)| . 3))
 (8 8
    (:REWRITE |(floor (floor x y) z)| . 2)))
(SMAN::!R-0-!M-0
 (36448 2 (:REWRITE |(logand y (if a b c))|))
 (32028 2 (:REWRITE |(floor (if a b c) x)|))
 (23708 56 (:LINEAR LINEAR-FLOOR-BOUNDS-1))
 (17822 13502
        (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (16507 345 (:REWRITE THE-FLOOR-ABOVE))
 (13502 13502
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (13502 13502
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (13502 13502
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (11666 82 (:REWRITE SMAN::UNNECESSARY-FLOOR))
 (9738 64 (:REWRITE |(+ y x)|))
 (6634 80 (:REWRITE CANCEL-FLOOR-+))
 (6608 1356
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (6186 80 (:REWRITE FLOOR-ZERO . 3))
 (6027 169 (:REWRITE DEFAULT-PLUS-1))
 (6009 169 (:REWRITE DEFAULT-PLUS-2))
 (5688 20 (:REWRITE SMAN::UNNECESSARY-MOD))
 (5629 67 (:REWRITE NORMALIZE-ADDENDS))
 (5464 80 (:REWRITE FLOOR-ZERO . 4))
 (5430 80 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (5394 80 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (5252 20 (:REWRITE MOD-ZERO . 4))
 (5094 566 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (5094 566
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (5094 566
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (5094 566
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (5094 566
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (4974 20 (:REWRITE MOD-X-Y-=-X . 3))
 (4822 80 (:REWRITE FLOOR-ZERO . 5))
 (4752 20 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (4726 2 (:REWRITE |(< (if a b c) x)|))
 (4698 20 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (4665 365 (:REWRITE INTEGERP-MINUS-X))
 (4348 1238 (:REWRITE DEFAULT-TIMES-2))
 (4332 20 (:REWRITE MOD-X-Y-=-X . 4))
 (3686 20 (:REWRITE CANCEL-MOD-+))
 (3666 462 (:REWRITE |(* y x)|))
 (3662 1238 (:REWRITE DEFAULT-TIMES-1))
 (3310 202 (:REWRITE |(* (- x) y)|))
 (2914 2 (:REWRITE |(mod (floor x y) z)| . 1))
 (2830 566 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
 (2830 566 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (2830 566 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (2830 566
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (2830 566
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (2830 566
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (2830 566
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (2830 566
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (2830 566
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
 (2830 566
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (2830 566
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (2314 82 (:REWRITE DEFAULT-FLOOR-RATIO))
 (2256 80 (:REWRITE FLOOR-=-X/Y . 2))
 (2004 202 (:REWRITE DEFAULT-MINUS))
 (2000 80 (:REWRITE FLOOR-=-X/Y . 3))
 (1920 202 (:REWRITE |(- (* c x))|))
 (1836 18 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (1836 18 (:DEFINITION FIX))
 (1450 20 (:REWRITE MOD-ZERO . 3))
 (1356 1356
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (1356 1356
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (1356 1356
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (1169 345 (:REWRITE THE-FLOOR-BELOW))
 (1107 317
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (939 327 (:REWRITE DEFAULT-LESS-THAN-1))
 (826 20 (:REWRITE DEFAULT-MOD-RATIO))
 (758 2
      (:REWRITE |(floor (floor x y) z)| . 1))
 (731 327 (:REWRITE DEFAULT-LESS-THAN-2))
 (668 668
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (619 325
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (602 80 (:REWRITE FLOOR-ZERO . 2))
 (602 80 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (602 80 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (602 80 (:REWRITE FLOOR-CANCEL-*-CONST))
 (566 566 (:TYPE-PRESCRIPTION FLOOR))
 (504 20 (:REWRITE MOD-X-Y-=-X . 2))
 (504 20 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (504 20
      (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (486 82 (:REWRITE DEFAULT-FLOOR-1))
 (418 2 (:REWRITE |(* (if a b c) x)|))
 (378 80
      (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (367 319
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (354 28 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (333 317
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (319 319
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (319 319
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (319 319 (:REWRITE INTEGERP-<-CONSTANT))
 (319 319 (:REWRITE CONSTANT-<-INTEGERP))
 (319 319
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (319 319
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (319 319
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (319 319
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (319 319 (:REWRITE |(< c (- x))|))
 (319 319
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (319 319
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (319 319
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (319 319
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (319 319 (:REWRITE |(< (/ x) (/ y))|))
 (319 319 (:REWRITE |(< (- x) c)|))
 (319 319 (:REWRITE |(< (- x) (- y))|))
 (317 317 (:REWRITE SIMPLIFY-SUMS-<))
 (304 80
      (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (302 78
      (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (302 20 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (302 20 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (302 20
      (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (302 20 (:REWRITE MOD-CANCEL-*-CONST))
 (265 265 (:REWRITE REDUCE-INTEGERP-+))
 (265 265 (:META META-INTEGERP-CORRECT))
 (242 28 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (237 25
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (237 25
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (222 20 (:REWRITE DEFAULT-MOD-1))
 (212 212 (:REWRITE |(< (* x y) 0)|))
 (206 206 (:REWRITE |(< (/ x) 0)|))
 (204 204
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (204 204
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (166 78
      (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (130 35 (:REWRITE SMAN::!R-R))
 (120 120 (:TYPE-PRESCRIPTION SMAN::STP))
 (102 102 (:TYPE-PRESCRIPTION ABS))
 (94 39 (:REWRITE SMAN::!MI-MI))
 (90 18
     (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (90 18 (:REWRITE |(+ 0 x)|))
 (82 82 (:REWRITE DEFAULT-FLOOR-2))
 (78 78 (:REWRITE |(floor x (- y))| . 2))
 (78 78 (:REWRITE |(floor x (- y))| . 1))
 (78 78
     (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (78 78
     (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (78 78 (:REWRITE |(floor (- x) y)| . 2))
 (78 78 (:REWRITE |(floor (- x) y)| . 1))
 (57 57
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (57 57
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (57 57 (:REWRITE |(< 0 (/ x))|))
 (57 57 (:REWRITE |(< 0 (* x y))|))
 (51 29 (:REWRITE SMAN::STP-!MI))
 (50 50
     (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (49 49
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (39 39 (:REWRITE SMAN::!MI-DEFAULT-1))
 (36 18 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
 (36 4 (:REWRITE FLOOR-POSITIVE . 2))
 (36 4 (:REWRITE FLOOR-NONPOSITIVE . 1))
 (35 25 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (25 25
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (25 25
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (25 25
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (25 25 (:REWRITE |(equal c (/ x))|))
 (25 25 (:REWRITE |(equal c (- x))|))
 (25 25 (:REWRITE |(equal (/ x) c)|))
 (25 25 (:REWRITE |(equal (/ x) (/ y))|))
 (25 25 (:REWRITE |(equal (- x) c)|))
 (25 25 (:REWRITE |(equal (- x) (- y))|))
 (21 21 (:REWRITE SMAN::!R-DEFAULT-1))
 (20 20
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (20 20
     (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (20 20 (:REWRITE DEFAULT-MOD-2))
 (20 20 (:REWRITE DEFAULT-LOGAND-1))
 (20 4 (:REWRITE FLOOR-POSITIVE . 4))
 (20 4 (:REWRITE FLOOR-POSITIVE . 3))
 (20 4 (:REWRITE FLOOR-NONPOSITIVE . 3))
 (20 4 (:REWRITE FLOOR-NONPOSITIVE . 2))
 (18
   18
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (18
  18
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (18 18
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (18 18
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (18 18
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (18 18
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (18 18 (:REWRITE |(mod x (- y))| . 3))
 (18 18 (:REWRITE |(mod x (- y))| . 2))
 (18 18 (:REWRITE |(mod x (- y))| . 1))
 (18 18
     (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (18 18
     (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (18 18 (:REWRITE |(mod (- x) y)| . 3))
 (18 18 (:REWRITE |(mod (- x) y)| . 2))
 (18 18 (:REWRITE |(mod (- x) y)| . 1))
 (18 18
     (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (18 18 (:REWRITE |(+ x (- x))|))
 (10 2 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (10 2 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (10 2 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (10 2 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (10 2 (:REWRITE FLOOR-=-X/Y . 4))
 (10 2
     (:REWRITE |(equal (floor (+ x y) z) x)|))
 (10 2 (:REWRITE |(+ c (+ d x))|))
 (6 6 (:REWRITE |(* a (/ a) b)|))
 (6 2 (:REWRITE DEFAULT-CDR))
 (6 2 (:REWRITE DEFAULT-CAR))
 (4 4 (:REWRITE FLOOR-POSITIVE . 1))
 (3 3 (:REWRITE |(< y (+ (- c) x))|))
 (3 3 (:REWRITE |(< x (+ c/d y))|))
 (3 1 (:REWRITE SMAN::STP-!R))
 (2 2 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
 (2 2 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (2 2 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (2 2 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (2 2 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
 (2 2 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (2 2 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (2 2 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
 (2 2 (:REWRITE FLOOR-ZERO . 1))
 (2 2 (:REWRITE |(mod (floor x y) z)| . 5))
 (2 2 (:REWRITE |(mod (floor x y) z)| . 4))
 (2 2 (:REWRITE |(mod (floor x y) z)| . 3))
 (2 2 (:REWRITE |(mod (floor x y) z)| . 2))
 (2 2
    (:REWRITE |(floor (floor x y) z)| . 5))
 (2 2
    (:REWRITE |(floor (floor x y) z)| . 4))
 (2 2
    (:REWRITE |(floor (floor x y) z)| . 3))
 (2 2
    (:REWRITE |(floor (floor x y) z)| . 2))
 (1 1 (:REWRITE |(equal x (if a b c))|))
 (1 1 (:REWRITE |(equal (if a b c) x)|)))
(SMAN::!R-BASE-CASE
     (35 1 (:REWRITE SMAN::!R-DEFAULT-1))
     (33 1 (:DEFINITION NATP))
     (11 11 (:TYPE-PRESCRIPTION SMAN::!R))
     (3 1 (:REWRITE SMAN::!R-R))
     (2 2 (:TYPE-PRESCRIPTION SMAN::STP))
     (1 1 (:TYPE-PRESCRIPTION NATP))
     (1 1 (:REWRITE THE-FLOOR-BELOW))
     (1 1 (:REWRITE THE-FLOOR-ABOVE))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (1 1 (:REWRITE SIMPLIFY-SUMS-<))
     (1 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (1 1 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (1 1
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (1 1
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (1 1 (:REWRITE REDUCE-INTEGERP-+))
     (1 1 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
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
(SMAN::!R-INNER-ABSORBTION
 (2230408 2338 (:LINEAR LINEAR-FLOOR-BOUNDS-1))
 (933562 10763 (:REWRITE THE-FLOOR-ABOVE))
 (872052 666 (:REWRITE MOD-ZERO . 4))
 (832847 666 (:REWRITE SMAN::UNNECESSARY-MOD))
 (708583 666 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (688534 666 (:REWRITE MOD-X-Y-=-X . 3))
 (664549 666 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (634188 666 (:REWRITE MOD-X-Y-=-X . 4))
 (566912 566912
         (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (566912 566912
         (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (566912 566912
         (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (564647 564647
         (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (512007 47133 (:REWRITE DEFAULT-TIMES-2))
 (428904 666 (:REWRITE CANCEL-MOD-+))
 (425229 23842 (:REWRITE DEFAULT-PLUS-1))
 (419077 23842 (:REWRITE DEFAULT-PLUS-2))
 (386418 3532 (:REWRITE CANCEL-FLOOR-+))
 (310348 24028
         (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (310348 24028
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (310348 24028
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (310348 24028
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (310348 24028
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (258444 3532 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (239774 1742
         (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (239493
  239493
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (239493
      239493
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (239493
     239493
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (239493 239493
         (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (230924 3532 (:REWRITE FLOOR-ZERO . 3))
 (228744 17228 (:REWRITE |(* (- x) y)|))
 (184463 47133 (:REWRITE DEFAULT-TIMES-1))
 (178483 3532 (:REWRITE FLOOR-=-X/Y . 2))
 (171120 17112 (:REWRITE DEFAULT-DIVIDE))
 (167188 24028
         (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (167188 24028
         (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (167188 24028
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (167188 24028
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (167188 24028
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (167188 24028
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (167188 24028
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (167188 24028
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
 (167188 24028
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (167188 24028
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (166650 3556 (:REWRITE DEFAULT-FLOOR-RATIO))
 (161741 666 (:REWRITE MOD-ZERO . 3))
 (146225 36845 (:REWRITE DEFAULT-MINUS))
 (145996 8188 (:REWRITE INTEGERP-MINUS-X))
 (112336 3328 (:REWRITE |(integerp (- x))|))
 (106480 666 (:REWRITE DEFAULT-MOD-RATIO))
 (106288 3532 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (104782 1518 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (85930 3532 (:REWRITE FLOOR-ZERO . 2))
 (85930 3532 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (85930 3532 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (81890 3532 (:REWRITE FLOOR-ZERO . 5))
 (81818 3532 (:REWRITE FLOOR-ZERO . 4))
 (76991 1169 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (69550 666
        (:REWRITE |(mod (+ x (mod a b)) y)|))
 (69550 666
        (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (65950 666 (:REWRITE MOD-X-Y-=-X . 2))
 (65783 9613
        (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (64036 10763 (:REWRITE THE-FLOOR-BELOW))
 (50980 3532 (:REWRITE FLOOR-CANCEL-*-CONST))
 (49627 10095 (:REWRITE DEFAULT-LESS-THAN-2))
 (49290 346 (:REWRITE DEFAULT-LOGAND-2))
 (46846 928 (:REWRITE |(* (* x y) z)|))
 (40146 9613
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (38872 3532
        (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (38828 1169 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (38788 3448
        (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (38788 3448
        (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (38508 666 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (38508 666 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (34138 3556 (:REWRITE DEFAULT-FLOOR-2))
 (32206 3556 (:REWRITE SMAN::UNNECESSARY-FLOOR))
 (31632 666 (:REWRITE MOD-CANCEL-*-CONST))
 (28682 766
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (28108 666 (:REWRITE DEFAULT-MOD-1))
 (27332 766
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (22087 9613 (:REWRITE SIMPLIFY-SUMS-<))
 (21760 21760 (:REWRITE DEFAULT-EXPT-2))
 (21760 21760 (:REWRITE DEFAULT-EXPT-1))
 (21760 21760 (:REWRITE |(expt (- x) n)|))
 (20224 3532
        (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (18880 3448
        (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (17450 17450
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (14364 1386 (:LINEAR EXPT->-1-ONE))
 (9789 9789
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (9613 9613
       (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (9613 9613 (:REWRITE INTEGERP-<-CONSTANT))
 (9613 9613 (:REWRITE CONSTANT-<-INTEGERP))
 (9613 9613
       (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (9613 9613
       (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (9613 9613
       (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (9613 9613
       (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (9613 9613 (:REWRITE |(< c (- x))|))
 (9613 9613
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (9613 9613
       (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (9613 9613
       (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (9613 9613
       (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (9613 9613 (:REWRITE |(< (/ x) (/ y))|))
 (9613 9613 (:REWRITE |(< (- x) c)|))
 (9613 9613 (:REWRITE |(< (- x) (- y))|))
 (9225 1386 (:LINEAR EXPT->=-1-ONE))
 (9012 2772
       (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (8832 8832
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (8832 8832
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (8832 8832
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (8832 8832
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (8140 8140
       (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (8012 8012 (:REWRITE REDUCE-INTEGERP-+))
 (8012 8012 (:META META-INTEGERP-CORRECT))
 (7914 1386 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (6820 682 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
 (6194 6194 (:REWRITE |(< (* x y) 0)|))
 (6018 6018
       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (6018 6018
       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (6018 6018 (:REWRITE |(< (/ x) 0)|))
 (5678 167 (:REWRITE FLOOR-POSITIVE . 3))
 (5530 682 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (5530 682
       (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (5530 682
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (5177 167 (:REWRITE FLOOR-POSITIVE . 2))
 (5177 167 (:REWRITE FLOOR-NONPOSITIVE . 1))
 (5118 90
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4A-EXPT))
 (4978 3556 (:REWRITE DEFAULT-FLOOR-1))
 (4321 654 (:REWRITE ACL2-NUMBERP-X))
 (4266 666 (:REWRITE DEFAULT-MOD-2))
 (4175 167 (:REWRITE FLOOR-POSITIVE . 4))
 (4175 167 (:REWRITE FLOOR-NONPOSITIVE . 3))
 (4175 167 (:REWRITE FLOOR-NONPOSITIVE . 2))
 (3810 682 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (3698 158 (:REWRITE |(floor x 1)|))
 (3627 1100 (:REWRITE SMAN::!MI-MI))
 (3532 3532 (:REWRITE |(floor x (- y))| . 2))
 (3532 3532 (:REWRITE |(floor x (- y))| . 1))
 (3532 3532 (:REWRITE |(floor (- x) y)| . 2))
 (3532 3532 (:REWRITE |(floor (- x) y)| . 1))
 (3262 682 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (3194 3194 (:TYPE-PRESCRIPTION SMAN::STP))
 (2950 682 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
 (2772 2772
       (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2772 2772
       (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2772 2772
       (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (2672 167 (:REWRITE FLOOR-=-X/Y . 4))
 (2672 167
       (:REWRITE |(equal (floor (+ x y) z) x)|))
 (2133 2133
       (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (2082 66 (:REWRITE |(mod x 1)|))
 (1742 1742
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (1742 1742
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (1742 1742
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (1667 1667
       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (1667 1667
       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (1667 1667 (:REWRITE |(< 0 (/ x))|))
 (1667 1667 (:REWRITE |(< 0 (* x y))|))
 (1460 467 (:REWRITE RATIONALP-X))
 (1386 1386 (:LINEAR EXPT-X->=-X))
 (1386 1386 (:LINEAR EXPT-X->-X))
 (1386 1386 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (1386 1386 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1386 1386 (:LINEAR EXPT-LINEAR-LOWER-<))
 (1386 1386 (:LINEAR EXPT->=-1-TWO))
 (1386 1386 (:LINEAR EXPT->-1-TWO))
 (1386 1386 (:LINEAR EXPT-<=-1-TWO))
 (1386 1386 (:LINEAR EXPT-<=-1-ONE))
 (1386 1386 (:LINEAR EXPT-<-1-TWO))
 (1386 1386 (:LINEAR EXPT-<-1-ONE))
 (1360 408 (:REWRITE SMAN::!R-R))
 (1336 766 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (1100 1100 (:REWRITE SMAN::!MI-DEFAULT-1))
 (783 783 (:REWRITE ODD-EXPT-THM))
 (766 766
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (766 766
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (766 766
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (766 766 (:REWRITE |(equal c (/ x))|))
 (766 766 (:REWRITE |(equal c (- x))|))
 (766 766 (:REWRITE |(equal (/ x) c)|))
 (766 766 (:REWRITE |(equal (/ x) (/ y))|))
 (766 766 (:REWRITE |(equal (- x) c)|))
 (766 766 (:REWRITE |(equal (- x) (- y))|))
 (714 348 (:REWRITE DEFAULT-CDR))
 (714 348 (:REWRITE DEFAULT-CAR))
 (682 682 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (682 682
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (682 682
      (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (682 682
      (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
 (682 682
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (668 668 (:REWRITE |(+ x (- x))|))
 (642 642
      (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (537 537 (:REWRITE |(- (- x))|))
 (527 527
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (513 171 (:REWRITE SMAN::STP-!MI))
 (467 467 (:REWRITE REDUCE-RATIONALP-+))
 (467 467 (:REWRITE REDUCE-RATIONALP-*))
 (467 467 (:REWRITE RATIONALP-MINUS-X))
 (467 467 (:META META-RATIONALP-CORRECT))
 (466 466 (:REWRITE |(mod x (- y))| . 3))
 (466 466 (:REWRITE |(mod x (- y))| . 2))
 (466 466 (:REWRITE |(mod x (- y))| . 1))
 (466 466 (:REWRITE |(mod (- x) y)| . 3))
 (466 466 (:REWRITE |(mod (- x) y)| . 2))
 (466 466 (:REWRITE |(mod (- x) y)| . 1))
 (424 424
      (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (400 400
      (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (356 356 (:REWRITE ZP-OPEN))
 (346 346 (:REWRITE DEFAULT-LOGAND-1))
 (334 114 (:REWRITE SMAN::STP-!R))
 (279 18 (:REWRITE SMAN::!R-!MI-BELOW))
 (196 196 (:REWRITE |(< y (+ (- c) x))|))
 (196 196 (:REWRITE |(< x (+ c/d y))|))
 (196 196
      (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (176 176
      (:REWRITE |(mod (floor x y) z)| . 5))
 (176 176
      (:REWRITE |(mod (floor x y) z)| . 4))
 (176 176
      (:REWRITE |(mod (floor x y) z)| . 3))
 (176 176
      (:REWRITE |(mod (floor x y) z)| . 2))
 (176 176 (:REWRITE |(< (+ c/d x) y)|))
 (167 167 (:REWRITE FLOOR-ZERO . 1))
 (167 167 (:REWRITE FLOOR-POSITIVE . 1))
 (114 6 (:REWRITE SMAN::!R-!R-DIFF-ABOVE))
 (97 6 (:REWRITE SMAN::!R-!R-DIFF-BELOW))
 (90 90
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (90 90
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (90 90
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (90 90 (:REWRITE |(* c (* d x))|))
 (78 78 (:REWRITE |(equal (* x y) 0)|)))
(SMAN::INTEGERP-PRODUCT-BY-EXPT
 (213 213
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (213
  213
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (213 213
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (213 213
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (213
     213
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (213 213
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (213 213
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (153 13 (:REWRITE DEFAULT-TIMES-2))
 (33 13 (:REWRITE DEFAULT-TIMES-1))
 (26 1 (:REWRITE |(integerp (expt x n))|))
 (22 20 (:REWRITE DEFAULT-PLUS-1))
 (21 21 (:REWRITE REDUCE-INTEGERP-+))
 (21 21 (:REWRITE INTEGERP-MINUS-X))
 (20 20
     (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (20 20 (:REWRITE DEFAULT-PLUS-2))
 (19 1
     (:REWRITE |(expt x (+ m n)) non-zero (+ m n)|))
 (14 1
     (:REWRITE |(expt x (+ m n)) non-zero x|))
 (12 12 (:REWRITE DEFAULT-EXPT-2))
 (12 12 (:REWRITE DEFAULT-EXPT-1))
 (11 11 (:REWRITE |(expt 1/c n)|))
 (11 11 (:REWRITE |(expt (- x) n)|))
 (10 10
     (:REWRITE NORMALIZE-FACTORS-SCATTER-EXPONENTS))
 (9 9 (:REWRITE THE-FLOOR-BELOW))
 (9 9 (:REWRITE THE-FLOOR-ABOVE))
 (9 9 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (9 9
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (9 9
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (9 9 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (9 9 (:REWRITE INTEGERP-<-CONSTANT))
 (9 9 (:REWRITE DEFAULT-LESS-THAN-2))
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
 (8 8
    (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-<))
 (7 7 (:REWRITE SIMPLIFY-SUMS-<))
 (7 7
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (7 7 (:REWRITE |(< (/ x) 0)|))
 (7 7 (:REWRITE |(< (* x y) 0)|))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (5 5 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (5 5
    (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-EQUAL))
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
 (4 4 (:REWRITE |(equal (+ (- c) x) y)|))
 (3 3 (:TYPE-PRESCRIPTION FIX))
 (2 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (2 2 (:REWRITE DEFAULT-MINUS))
 (2 2 (:REWRITE |(* c (* d x))|))
 (1 1 (:REWRITE |(< (+ c/d x) y)|))
 (1 1 (:REWRITE |(< (+ (- c) x) y)|)))
(SMAN::EXPT-2-8*SUM-PN
 (1234 36 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (456 44
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (313 3 (:LINEAR EXPT->=-1-ONE))
 (313 3 (:LINEAR EXPT-<=-1-TWO))
 (307 3 (:LINEAR EXPT->-1-ONE))
 (307 3 (:LINEAR EXPT-<-1-TWO))
 (246 3 (:LINEAR EXPT-X->=-X))
 (246 3 (:LINEAR EXPT-X->-X))
 (196 87 (:REWRITE DEFAULT-TIMES-2))
 (176 16 (:REWRITE |(* y (* x z))|))
 (175 152 (:REWRITE DEFAULT-PLUS-1))
 (152 152 (:REWRITE DEFAULT-PLUS-2))
 (134 87 (:REWRITE DEFAULT-TIMES-1))
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
 (44 44 (:REWRITE THE-FLOOR-BELOW))
 (44 44 (:REWRITE THE-FLOOR-ABOVE))
 (44 44 (:REWRITE DEFAULT-LESS-THAN-2))
 (44 44 (:REWRITE DEFAULT-LESS-THAN-1))
 (43 25 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (36 36
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (36 36
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (36 36
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (36 36
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
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
 (18 18 (:REWRITE SIMPLIFY-SUMS-<))
 (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (16 16 (:REWRITE |(* a (/ a) b)|))
 (13 13
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (12 12 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (12 12 (:REWRITE |(< y (+ (- c) x))|))
 (12 12 (:REWRITE |(< x (+ c/d y))|))
 (12 12 (:REWRITE |(< (+ c/d x) y)|))
 (12 12 (:REWRITE |(< (+ (- c) x) y)|))
 (8 8 (:TYPE-PRESCRIPTION ABS))
 (6 6 (:REWRITE |(< 0 (/ x))|))
 (6 6 (:REWRITE |(< 0 (* x y))|))
 (6 6 (:REWRITE |(< (/ x) 0)|))
 (6 6 (:REWRITE |(< (* x y) 0)|))
 (6 6 (:REWRITE |(+ x (- x))|))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (6 6
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (4 4 (:REWRITE DEFAULT-MINUS))
 (4 4 (:REWRITE |(* (- x) y)|))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<))
 (3 3 (:LINEAR EXPT->=-1-TWO))
 (3 3 (:LINEAR EXPT->-1-TWO))
 (3 3 (:LINEAR EXPT-<=-1-ONE))
 (3 3 (:LINEAR EXPT-<-1-ONE))
 (2 2 (:REWRITE REDUCE-INTEGERP-+))
 (2 2 (:REWRITE INTEGERP-MINUS-X))
 (2 2 (:REWRITE DEFAULT-EXPT-2))
 (2 2 (:REWRITE DEFAULT-EXPT-1))
 (2 2 (:REWRITE |(expt 1/c n)|))
 (2 2 (:REWRITE |(expt (- x) n)|))
 (2 2 (:REWRITE |(+ c (+ d x))|))
 (2 2 (:META META-INTEGERP-CORRECT))
 (1 1
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (1 1
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (1 1
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (1 1 (:REWRITE |(equal c (/ x))|))
 (1 1 (:REWRITE |(equal c (- x))|))
 (1 1 (:REWRITE |(equal (expt 2 n) c)|))
 (1 1 (:REWRITE |(equal (/ x) c)|))
 (1 1 (:REWRITE |(equal (/ x) (/ y))|))
 (1 1 (:REWRITE |(equal (- x) c)|))
 (1 1 (:REWRITE |(equal (- x) (- y))|)))
(SMAN::EXPT-2-*-SUM-N8P
 (1002 44
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (700 56
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (254 3 (:LINEAR EXPT-X->=-X))
 (254 3 (:LINEAR EXPT-X->-X))
 (230 26 (:REWRITE CONSTANT-<-INTEGERP))
 (164 3 (:LINEAR EXPT->=-1-ONE))
 (164 3 (:LINEAR EXPT-<=-1-TWO))
 (161 3 (:LINEAR EXPT->-1-ONE))
 (161 3 (:LINEAR EXPT-<-1-TWO))
 (158 56 (:REWRITE DEFAULT-TIMES-2))
 (132 12 (:REWRITE |(* y (* x z))|))
 (112 56 (:REWRITE DEFAULT-TIMES-1))
 (72
  72
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (72 72
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (72 72
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (72 72
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (72 72
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (72 18 (:REWRITE |(+ c (+ d x))|))
 (56 56 (:REWRITE THE-FLOOR-BELOW))
 (56 56 (:REWRITE THE-FLOOR-ABOVE))
 (56 56 (:REWRITE DEFAULT-LESS-THAN-2))
 (56 56 (:REWRITE DEFAULT-LESS-THAN-1))
 (51 49 (:REWRITE DEFAULT-PLUS-1))
 (49 49 (:REWRITE DEFAULT-PLUS-2))
 (44 44
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
 (22 4 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (18 18 (:REWRITE |(+ 0 x)|))
 (14 14 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (12 12 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (12 12 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (12 12 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (12 12 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (12 12 (:TYPE-PRESCRIPTION ABS))
 (12 12 (:REWRITE |(< x (+ c/d y))|))
 (12 12 (:REWRITE |(* a (/ a) b)|))
 (6 6 (:REWRITE |(< 0 (* x y))|))
 (6 6 (:REWRITE |(< (+ c/d x) y)|))
 (6 6 (:REWRITE |(< (* x y) 0)|))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (6 6
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (5 5
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<))
 (3 3 (:LINEAR EXPT->=-1-TWO))
 (3 3 (:LINEAR EXPT->-1-TWO))
 (3 3 (:LINEAR EXPT-<=-1-ONE))
 (3 3 (:LINEAR EXPT-<-1-ONE))
 (2 2 (:REWRITE DEFAULT-MINUS))
 (2 2 (:REWRITE DEFAULT-EXPT-2))
 (2 2 (:REWRITE DEFAULT-EXPT-1))
 (2 2 (:REWRITE |(expt 1/c n)|))
 (2 2 (:REWRITE |(expt (- x) n)|))
 (2 2 (:REWRITE |(* (- x) y)|))
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
 (1 1 (:REWRITE |(equal (expt 2 n) c)|))
 (1 1 (:REWRITE |(equal (/ x) c)|))
 (1 1 (:REWRITE |(equal (/ x) (/ y))|))
 (1 1 (:REWRITE |(equal (- x) c)|))
 (1 1 (:REWRITE |(equal (- x) (- y))|))
 (1 1 (:META META-INTEGERP-CORRECT)))
(SMAN::EXPT-2-*-SUM-PPN
 (1140 36 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (276 3 (:LINEAR EXPT->=-1-ONE))
 (276 3 (:LINEAR EXPT-<=-1-TWO))
 (273 3 (:LINEAR EXPT-X->=-X))
 (273 3 (:LINEAR EXPT-X->-X))
 (270 3 (:LINEAR EXPT->-1-ONE))
 (270 3 (:LINEAR EXPT-<-1-TWO))
 (242 215 (:REWRITE DEFAULT-PLUS-1))
 (215 215 (:REWRITE DEFAULT-PLUS-2))
 (99 52 (:REWRITE DEFAULT-TIMES-1))
 (97 52 (:REWRITE DEFAULT-TIMES-2))
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
 (47 29 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (42 42
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (36 36 (:REWRITE THE-FLOOR-BELOW))
 (36 36 (:REWRITE THE-FLOOR-ABOVE))
 (36 36
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (36 36
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (36 36
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (36 36
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (36 36
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
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
 (24 24 (:REWRITE |(< y (+ (- c) x))|))
 (24 24 (:REWRITE |(< x (+ c/d y))|))
 (18 18 (:REWRITE SIMPLIFY-SUMS-<))
 (18 18 (:REWRITE |(< (+ c/d x) y)|))
 (18 18 (:REWRITE |(< (+ (- c) x) y)|))
 (12 12 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (10 10 (:REWRITE |(+ c (+ d x))|))
 (6 6 (:REWRITE FOLD-CONSTS-IN-+))
 (6 6 (:REWRITE DEFAULT-MINUS))
 (6 6 (:REWRITE |(< 0 (/ x))|))
 (6 6 (:REWRITE |(< 0 (* x y))|))
 (6 6 (:REWRITE |(< (/ x) 0)|))
 (6 6 (:REWRITE |(< (* x y) 0)|))
 (6 6 (:REWRITE |(+ x (- x))|))
 (6 6 (:REWRITE |(* (- x) y)|))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (6 6
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (3 3 (:REWRITE REDUCE-INTEGERP-+))
 (3 3 (:REWRITE INTEGERP-MINUS-X))
 (3 3 (:META META-INTEGERP-CORRECT))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<))
 (3 3 (:LINEAR EXPT->=-1-TWO))
 (3 3 (:LINEAR EXPT->-1-TWO))
 (3 3 (:LINEAR EXPT-<=-1-ONE))
 (3 3 (:LINEAR EXPT-<-1-ONE))
 (2 2 (:REWRITE DEFAULT-EXPT-2))
 (2 2 (:REWRITE DEFAULT-EXPT-1))
 (2 2 (:REWRITE |(expt 1/c n)|))
 (2 2 (:REWRITE |(expt (- x) n)|))
 (1 1
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (1 1
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (1 1
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (1 1 (:REWRITE |(equal c (/ x))|))
 (1 1 (:REWRITE |(equal c (- x))|))
 (1 1 (:REWRITE |(equal (expt 2 n) c)|))
 (1 1 (:REWRITE |(equal (/ x) c)|))
 (1 1 (:REWRITE |(equal (/ x) (/ y))|))
 (1 1 (:REWRITE |(equal (- x) c)|))
 (1 1 (:REWRITE |(equal (- x) (- y))|)))
(SMAN::EXPT-2-*-SUM-PNN
 (1598 54 (:REWRITE |(< c (- x))|))
 (1236 36 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (772 42 (:REWRITE |(< (- x) c)|))
 (516 102 (:REWRITE NORMALIZE-ADDENDS))
 (476 3 (:LINEAR EXPT-X->=-X))
 (476 3 (:LINEAR EXPT-X->-X))
 (446 3 (:LINEAR EXPT->=-1-ONE))
 (443 3 (:LINEAR EXPT-<=-1-TWO))
 (440 3 (:LINEAR EXPT-<-1-TWO))
 (437 3 (:LINEAR EXPT->-1-ONE))
 (300 24 (:REWRITE BUBBLE-DOWN-+-BUBBLE-DOWN))
 (274 232 (:REWRITE DEFAULT-PLUS-1))
 (232 232 (:REWRITE DEFAULT-PLUS-2))
 (228 30 (:REWRITE |(< y (+ (- c) x))|))
 (103 103 (:REWRITE DEFAULT-MINUS))
 (84 84
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (84 36 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
 (62
  62
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (62 62
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (62 62
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (62 62
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (62 62
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (62 62
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (60 60 (:REWRITE THE-FLOOR-BELOW))
 (60 60 (:REWRITE THE-FLOOR-ABOVE))
 (60 60
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (60 60
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (60 60
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (60 60 (:REWRITE DEFAULT-LESS-THAN-2))
 (60 60 (:REWRITE DEFAULT-LESS-THAN-1))
 (54 54 (:REWRITE DEFAULT-TIMES-2))
 (54 54 (:REWRITE DEFAULT-TIMES-1))
 (54 54
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (54 54
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (54 54
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (54 54
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (54 54
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (54 54
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (54 54
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (54 54
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (54 54 (:REWRITE |(< (/ x) (/ y))|))
 (54 54 (:REWRITE |(< (- x) (- y))|))
 (54 30 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
 (48 12 (:REWRITE |(+ (* c x) (* d x))|))
 (47 47 (:REWRITE |(+ c (+ d x))|))
 (42 42 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (42 42
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (36 36
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (36 36
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (36 36 (:REWRITE INTEGERP-<-CONSTANT))
 (36 36 (:REWRITE CONSTANT-<-INTEGERP))
 (36 36 (:REWRITE |(< (+ c/d x) y)|))
 (36 36 (:DEFINITION FIX))
 (30 30 (:REWRITE |(< x (+ c/d y))|))
 (30 30 (:REWRITE |(< (+ (- c) x) y)|))
 (30 30 (:REWRITE |(+ 0 x)|))
 (29 29 (:REWRITE FOLD-CONSTS-IN-+))
 (20 2 (:REWRITE DEFAULT-DIVIDE))
 (18 18 (:REWRITE SIMPLIFY-SUMS-<))
 (15 15 (:REWRITE |(* (- x) y)|))
 (12 12 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (12 12 (:REWRITE |(< 0 (/ x))|))
 (12 12 (:REWRITE |(< 0 (* x y))|))
 (12 12 (:REWRITE |(< (/ x) 0)|))
 (12 12 (:REWRITE |(< (* x y) 0)|))
 (12 12 (:REWRITE |(* 0 x)|))
 (6 6 (:REWRITE |(+ x (- x))|))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (6 6
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (4 4 (:REWRITE DEFAULT-EXPT-2))
 (4 4 (:REWRITE DEFAULT-EXPT-1))
 (4 4 (:REWRITE |(expt 1/c n)|))
 (4 4 (:REWRITE |(expt (- x) n)|))
 (3 3 (:REWRITE REDUCE-INTEGERP-+))
 (3 3 (:REWRITE INTEGERP-MINUS-X))
 (3 3 (:META META-INTEGERP-CORRECT))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<))
 (3 3 (:LINEAR EXPT->=-1-TWO))
 (3 3 (:LINEAR EXPT->-1-TWO))
 (3 3 (:LINEAR EXPT-<=-1-ONE))
 (3 3 (:LINEAR EXPT-<-1-ONE))
 (1 1
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (1 1
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL)))
(SMAN::EXPT-2-*-SUM-P8PNN
 (2966 76
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (1518 54 (:REWRITE |(< c (- x))|))
 (1182 36 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (778 42 (:REWRITE |(< (- x) c)|))
 (576 36 (:REWRITE |(- (+ x y))|))
 (540 3 (:LINEAR EXPT-X->=-X))
 (540 3 (:LINEAR EXPT-X->-X))
 (515 3 (:LINEAR EXPT->=-1-ONE))
 (512 3 (:LINEAR EXPT-<=-1-TWO))
 (509 3 (:LINEAR EXPT-<-1-TWO))
 (506 3 (:LINEAR EXPT->-1-ONE))
 (401 351 (:REWRITE DEFAULT-PLUS-1))
 (351 351 (:REWRITE DEFAULT-PLUS-2))
 (172 98 (:REWRITE |(+ c (+ d x))|))
 (126 88 (:REWRITE DEFAULT-TIMES-1))
 (124 88 (:REWRITE DEFAULT-TIMES-2))
 (121 121
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (96 96 (:REWRITE DEFAULT-MINUS))
 (76
  76
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (76 76
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (76 76
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (76 76
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (76 76
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (76 76 (:REWRITE THE-FLOOR-BELOW))
 (76 76 (:REWRITE THE-FLOOR-ABOVE))
 (76 76
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (76 76
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (76 76 (:REWRITE DEFAULT-LESS-THAN-2))
 (76 76 (:REWRITE DEFAULT-LESS-THAN-1))
 (70 52 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (54 54 (:REWRITE FOLD-CONSTS-IN-+))
 (54 54
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (54 54
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (54 54
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (54 54
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (54 54
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (54 54
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (54 54
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (54 54
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (54 54 (:REWRITE |(< (/ x) (/ y))|))
 (54 54 (:REWRITE |(< (- x) (- y))|))
 (50 50 (:REWRITE |(< x (+ c/d y))|))
 (42 42 (:REWRITE |(< (+ c/d x) y)|))
 (36 36
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (36 36
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (36 36 (:REWRITE INTEGERP-<-CONSTANT))
 (36 36 (:REWRITE CONSTANT-<-INTEGERP))
 (36 36 (:REWRITE |(< (+ (- c) x) y)|))
 (34 34 (:REWRITE |(< y (+ (- c) x))|))
 (18 18 (:REWRITE SIMPLIFY-SUMS-<))
 (18 18 (:REWRITE |(* (- x) y)|))
 (12 12 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (12 12 (:REWRITE |(< 0 (* x y))|))
 (12 12 (:REWRITE |(- (- x))|))
 (8 8 (:REWRITE |(< (* x y) 0)|))
 (6 6 (:REWRITE |(+ x (- x))|))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (6 6
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (3 3 (:REWRITE REDUCE-INTEGERP-+))
 (3 3 (:REWRITE INTEGERP-MINUS-X))
 (3 3 (:META META-INTEGERP-CORRECT))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<))
 (3 3 (:LINEAR EXPT->=-1-TWO))
 (3 3 (:LINEAR EXPT->-1-TWO))
 (3 3 (:LINEAR EXPT-<=-1-ONE))
 (3 3 (:LINEAR EXPT-<-1-ONE))
 (2 2 (:REWRITE DEFAULT-EXPT-2))
 (2 2 (:REWRITE DEFAULT-EXPT-1))
 (2 2 (:REWRITE |(expt 1/c n)|))
 (2 2 (:REWRITE |(expt (- x) n)|))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:REWRITE |(< (/ x) 0)|))
 (1 1
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (1 1
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (1 1
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (1 1 (:REWRITE |(equal c (/ x))|))
 (1 1 (:REWRITE |(equal c (- x))|))
 (1 1 (:REWRITE |(equal (expt 2 n) c)|))
 (1 1 (:REWRITE |(equal (/ x) c)|))
 (1 1 (:REWRITE |(equal (/ x) (/ y))|))
 (1 1 (:REWRITE |(equal (- x) c)|))
 (1 1 (:REWRITE |(equal (- x) (- y))|)))
(SMAN::EXPT-2-*-SUM-N8PPN
 (1758 54
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (1176 36 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (324 3 (:LINEAR EXPT->=-1-ONE))
 (324 3 (:LINEAR EXPT-<=-1-TWO))
 (318 3 (:LINEAR EXPT->-1-ONE))
 (318 3 (:LINEAR EXPT-<-1-TWO))
 (315 3 (:LINEAR EXPT-X->=-X))
 (315 3 (:LINEAR EXPT-X->-X))
 (295 268 (:REWRITE DEFAULT-PLUS-1))
 (268 268 (:REWRITE DEFAULT-PLUS-2))
 (102 55 (:REWRITE DEFAULT-TIMES-1))
 (100 55 (:REWRITE DEFAULT-TIMES-2))
 (89 35 (:REWRITE |(+ c (+ d x))|))
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
 (63 63
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (54 54 (:REWRITE THE-FLOOR-BELOW))
 (54 54 (:REWRITE THE-FLOOR-ABOVE))
 (54 54
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (54 54
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (54 54 (:REWRITE DEFAULT-LESS-THAN-2))
 (54 54 (:REWRITE DEFAULT-LESS-THAN-1))
 (47 29 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (42 42 (:REWRITE |(< x (+ c/d y))|))
 (36 36
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (36 36
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
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
 (30 30 (:REWRITE |(< y (+ (- c) x))|))
 (30 30 (:REWRITE |(< (+ c/d x) y)|))
 (24 24 (:REWRITE |(< (+ (- c) x) y)|))
 (18 18 (:REWRITE SIMPLIFY-SUMS-<))
 (13 13 (:REWRITE FOLD-CONSTS-IN-+))
 (12 12 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (6 6 (:REWRITE DEFAULT-MINUS))
 (6 6 (:REWRITE |(< 0 (* x y))|))
 (6 6 (:REWRITE |(< (* x y) 0)|))
 (6 6 (:REWRITE |(+ x (- x))|))
 (6 6 (:REWRITE |(* (- x) y)|))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (6 6
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (3 3 (:REWRITE REDUCE-INTEGERP-+))
 (3 3 (:REWRITE INTEGERP-MINUS-X))
 (3 3 (:META META-INTEGERP-CORRECT))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<))
 (3 3 (:LINEAR EXPT->=-1-TWO))
 (3 3 (:LINEAR EXPT->-1-TWO))
 (3 3 (:LINEAR EXPT-<=-1-ONE))
 (3 3 (:LINEAR EXPT-<-1-ONE))
 (2 2 (:REWRITE DEFAULT-EXPT-2))
 (2 2 (:REWRITE DEFAULT-EXPT-1))
 (2 2 (:REWRITE |(expt 1/c n)|))
 (2 2 (:REWRITE |(expt (- x) n)|))
 (1 1
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (1 1
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (1 1
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (1 1 (:REWRITE |(equal c (/ x))|))
 (1 1 (:REWRITE |(equal c (- x))|))
 (1 1 (:REWRITE |(equal (expt 2 n) c)|))
 (1 1 (:REWRITE |(equal (/ x) c)|))
 (1 1 (:REWRITE |(equal (/ x) (/ y))|))
 (1 1 (:REWRITE |(equal (- x) c)|))
 (1 1 (:REWRITE |(equal (- x) (- y))|)))
(SMAN::|MX-ROVER-CORRECT-SUBGOAL-*1/8.1'''|
 (21220 1689 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (21182 1723
        (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (15576 1689
        (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (13113 22 (:REWRITE MOD-X-Y-=-X . 3))
 (12294 12294
        (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (12293 22 (:REWRITE CANCEL-MOD-+))
 (11885
  11885
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (11885
      11885
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (11885
     11885
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (11885 11885
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (11197 22 (:REWRITE MOD-X-Y-=-X . 4))
 (10942 22 (:REWRITE MOD-ZERO . 4))
 (10850 10850
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (10850 10850
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (10850 10850
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (10565 22 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (10058 1098 (:REWRITE DEFAULT-TIMES-2))
 (9590 344
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (9405 15 (:REWRITE SMAN::UNNECESSARY-FLOOR))
 (8705 473
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (8378 1098 (:REWRITE DEFAULT-TIMES-1))
 (7288 22 (:REWRITE MOD-ZERO . 3))
 (6544 22 (:REWRITE SMAN::UNNECESSARY-MOD))
 (5193 94 (:REWRITE |(* (- x) y)|))
 (5059 22 (:REWRITE DEFAULT-MOD-RATIO))
 (4943 344
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (4775 28
       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (3799 2152 (:REWRITE DEFAULT-PLUS-2))
 (2844 22 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (2844 22
       (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (2833 2152 (:REWRITE DEFAULT-PLUS-1))
 (2818 154 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (2812 15 (:REWRITE |(integerp (- x))|))
 (2809 16 (:REWRITE |(mod x 1)|))
 (2790 22 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (2790 22 (:REWRITE MOD-X-Y-=-X . 2))
 (2541 63 (:LINEAR EXPT-<=-1-TWO))
 (2520 6 (:LINEAR MOD-BOUNDS-3))
 (2499 63 (:LINEAR EXPT-<-1-TWO))
 (2184 63 (:LINEAR EXPT-X->=-X))
 (2184 63 (:LINEAR EXPT-X->-X))
 (2040 15 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (1966 154
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (1966 154
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (1966 154
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (1963 473 (:REWRITE DEFAULT-LESS-THAN-1))
 (1890 15 (:REWRITE FLOOR-ZERO . 4))
 (1860 15 (:REWRITE FLOOR-ZERO . 3))
 (1812 473 (:REWRITE DEFAULT-LESS-THAN-2))
 (1723 1723
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (1704 1704 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (1704 1704
       (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (1689 1689
       (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (1478 22 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (1478 22 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (1424 22
       (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (1424 22 (:REWRITE MOD-CANCEL-*-CONST))
 (1415 697 (:REWRITE DEFAULT-MINUS))
 (1388 22
       (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (1131 114 (:REWRITE DEFAULT-DIVIDE))
 (1119 75 (:REWRITE |(< (+ (- c) x) y)|))
 (1110 15 (:REWRITE CANCEL-FLOOR-+))
 (1078 154 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (1078 154 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (1078 154
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (1078 154
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (1078 154
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (1078 154
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (1078 154
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (1078 154
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (1078 154
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (1035 15 (:REWRITE FLOOR-=-X/Y . 3))
 (976 12 (:LINEAR MOD-BOUNDS-2))
 (820 820
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (766 115 (:REWRITE |(< y (+ (- c) x))|))
 (740 22 (:REWRITE DEFAULT-MOD-1))
 (724 472 (:REWRITE |(+ c (+ d x))|))
 (675 15 (:REWRITE FLOOR-=-X/Y . 2))
 (675 15 (:REWRITE DEFAULT-FLOOR-RATIO))
 (525 63 (:LINEAR EXPT->=-1-ONE))
 (525 63 (:LINEAR EXPT->-1-ONE))
 (486 225 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (473 473 (:REWRITE THE-FLOOR-BELOW))
 (473 473 (:REWRITE THE-FLOOR-ABOVE))
 (473 473
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (473 473
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (427 19
      (:REWRITE SMAN::INTEGERP-PRODUCT-BY-EXPT))
 (375 15 (:REWRITE FLOOR-ZERO . 2))
 (375 15 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (375 15 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (375 15 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (347 347 (:REWRITE FOLD-CONSTS-IN-+))
 (344 344
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (344 344 (:REWRITE INTEGERP-<-CONSTANT))
 (344 344 (:REWRITE CONSTANT-<-INTEGERP))
 (344 344
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (344 344
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (344 344
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (344 344
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (344 344 (:REWRITE |(< c (- x))|))
 (344 344
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (344 344
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (344 344
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (344 344
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (344 344 (:REWRITE |(< (/ x) (/ y))|))
 (344 344 (:REWRITE |(< (- x) c)|))
 (344 344 (:REWRITE |(< (- x) (- y))|))
 (276 4 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (258 258 (:REWRITE DEFAULT-EXPT-2))
 (258 258 (:REWRITE DEFAULT-EXPT-1))
 (258 258 (:REWRITE |(expt 1/c n)|))
 (258 258 (:REWRITE |(expt (- x) n)|))
 (240 15 (:REWRITE FLOOR-ZERO . 5))
 (240 15
      (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (240 15 (:REWRITE FLOOR-CANCEL-*-CONST))
 (240 15
      (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (240 15
      (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (178 178 (:REWRITE |(< x (+ c/d y))|))
 (150 15 (:REWRITE DEFAULT-FLOOR-2))
 (145 145 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (126 126
      (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (126 126
      (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (126 126
      (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (126 126
      (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (120 12
      (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (112 22
      (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (96 96 (:REWRITE INTEGERP-MINUS-X))
 (96 96 (:REWRITE |(< (+ c/d x) y)|))
 (93 93 (:META META-INTEGERP-CORRECT))
 (86 86 (:REWRITE |(< 0 (* x y))|))
 (76 22 (:REWRITE DEFAULT-MOD-2))
 (65 65 (:REWRITE |(< 0 (/ x))|))
 (63 63 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (63 63 (:LINEAR EXPT-LINEAR-UPPER-<))
 (63 63 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (63 63 (:LINEAR EXPT-LINEAR-LOWER-<))
 (63 63 (:LINEAR EXPT->=-1-TWO))
 (63 63 (:LINEAR EXPT->-1-TWO))
 (63 63 (:LINEAR EXPT-<=-1-ONE))
 (63 63 (:LINEAR EXPT-<-1-ONE))
 (49 1 (:REWRITE MOD-X-Y-=-X+Y . 1))
 (46 46 (:REWRITE |(< (* x y) 0)|))
 (44 30 (:REWRITE |(equal (/ x) c)|))
 (30 30
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (30 30
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (30 30 (:REWRITE |(equal c (/ x))|))
 (30 30 (:REWRITE |(equal (/ x) (/ y))|))
 (30 30 (:REWRITE |(equal (- x) (- y))|))
 (29 29
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (29 29 (:REWRITE |(equal c (- x))|))
 (29 29 (:REWRITE |(equal (- x) c)|))
 (25 25
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (25 25
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (25 25 (:REWRITE |(< (/ x) 0)|))
 (23 23
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (23 23
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (22 22
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (22 22
     (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (22 22 (:REWRITE |(mod x (- y))| . 3))
 (22 22 (:REWRITE |(mod x (- y))| . 2))
 (22 22 (:REWRITE |(mod x (- y))| . 1))
 (22 22
     (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (22 22 (:REWRITE |(mod (- x) y)| . 3))
 (22 22 (:REWRITE |(mod (- x) y)| . 2))
 (22 22 (:REWRITE |(mod (- x) y)| . 1))
 (22 22
     (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (20 20 (:TYPE-PRESCRIPTION RATIONALP-MOD))
 (17 17
     (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (16 16 (:REWRITE |(equal (* x y) 0)|))
 (15 15
     (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (15 15 (:REWRITE DEFAULT-FLOOR-1))
 (15 15 (:REWRITE |(floor x (- y))| . 2))
 (15 15 (:REWRITE |(floor x (- y))| . 1))
 (15 15
     (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (15 15 (:REWRITE |(floor (- x) y)| . 2))
 (15 15 (:REWRITE |(floor (- x) y)| . 1))
 (15 15
     (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (10 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (8 1 (:REWRITE MOD-X-Y-=-X-Y . 1))
 (7 7 (:REWRITE |(equal (+ (- c) x) y)|))
 (4 1 (:REWRITE RATIONALP-X))
 (3 3 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (3 3
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (1 1 (:REWRITE REDUCE-RATIONALP-+))
 (1 1 (:REWRITE REDUCE-RATIONALP-*))
 (1 1 (:REWRITE RATIONALP-MINUS-X))
 (1 1 (:REWRITE BUBBLE-DOWN-*-MATCH-3))
 (1 1 (:REWRITE |(not (equal x (/ y)))|))
 (1 1 (:REWRITE |(equal x (/ y))|))
 (1 1 (:REWRITE |(/ (/ x))|))
 (1 1 (:REWRITE |(* c (* d x))|))
 (1 1 (:META META-RATIONALP-CORRECT)))
(SMAN::|MX-ROVER-CORRECT-SUBGOAL-*1/7.1'''|
 (1924
  1924
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1924
      1924
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1924
     1924
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1924 1924
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1725 413 (:REWRITE DEFAULT-TIMES-2))
 (1544 413 (:REWRITE DEFAULT-TIMES-1))
 (1254 2 (:REWRITE SMAN::UNNECESSARY-MOD))
 (930 624 (:REWRITE DEFAULT-PLUS-2))
 (854 70
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (755 56 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (747 624 (:REWRITE DEFAULT-PLUS-1))
 (569 569
      (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (540 72 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (504 72 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (504 72
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (504 72
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (500 500
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (500 500
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (500 500
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (327 15 (:REWRITE |(< (+ (- c) x) y)|))
 (279 7
      (:REWRITE SMAN::INTEGERP-PRODUCT-BY-EXPT))
 (272 2 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (260 260
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (252 2 (:REWRITE MOD-X-Y-=-X . 3))
 (242 6 (:LINEAR EXPT-<=-1-TWO))
 (240 72 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (238 6 (:LINEAR EXPT-<-1-TWO))
 (228 84 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (208 6 (:LINEAR EXPT-X->=-X))
 (208 6 (:LINEAR EXPT-X->-X))
 (184 2 (:REWRITE CANCEL-MOD-+))
 (160 70 (:REWRITE DEFAULT-LESS-THAN-2))
 (156 2 (:REWRITE MOD-ZERO . 3))
 (155 56
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (147 123 (:REWRITE |(+ c (+ d x))|))
 (133 133 (:REWRITE DEFAULT-MINUS))
 (97 70 (:REWRITE DEFAULT-LESS-THAN-1))
 (91 91 (:REWRITE FOLD-CONSTS-IN-+))
 (90 2 (:REWRITE DEFAULT-MOD-RATIO))
 (79 17 (:REWRITE |(< y (+ (- c) x))|))
 (72 72 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (72 72
     (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (72 72 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (72 72
     (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (70 70 (:REWRITE THE-FLOOR-BELOW))
 (70 70 (:REWRITE THE-FLOOR-ABOVE))
 (70 70
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (70 70
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (68 2 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (68 2
     (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (61 61 (:REWRITE DEFAULT-EXPT-2))
 (61 61 (:REWRITE DEFAULT-EXPT-1))
 (61 61 (:REWRITE |(expt 1/c n)|))
 (61 61 (:REWRITE |(expt (- x) n)|))
 (60 32 (:REWRITE |(* (- x) y)|))
 (60 6 (:REWRITE DEFAULT-DIVIDE))
 (57 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (56 56
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
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
 (50 6 (:LINEAR EXPT->=-1-ONE))
 (50 6 (:LINEAR EXPT->-1-ONE))
 (50 2 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (50 2 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (50 2 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (50 2 (:REWRITE MOD-X-Y-=-X . 2))
 (40 40 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (39 3
     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (39 3
     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (39 3
     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (32 2 (:REWRITE MOD-ZERO . 4))
 (32 2 (:REWRITE MOD-X-Y-=-X . 4))
 (32 2
     (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (32 2 (:REWRITE MOD-CANCEL-*-CONST))
 (32 2
     (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (32 2
     (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (24 24 (:REWRITE INTEGERP-MINUS-X))
 (23 23 (:REWRITE |(< x (+ c/d y))|))
 (21 21 (:META META-INTEGERP-CORRECT))
 (21 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (21 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (21 3
     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (21 3
     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (21 3
     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (21 3
     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (21 3
     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (21 3
     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (21 3
     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (20 20 (:REWRITE |(< (* x y) 0)|))
 (20 2 (:REWRITE DEFAULT-MOD-2))
 (18 18
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (18 18
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (18 18 (:REWRITE |(< (/ x) 0)|))
 (17 17 (:REWRITE |(< (+ c/d x) y)|))
 (13 4
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (13 4
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (12 12
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (12 12
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (12 12
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (12 12
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (11 11 (:REWRITE |(< 0 (* x y))|))
 (9 9 (:REWRITE |(< 0 (/ x))|))
 (6 6 (:TYPE-PRESCRIPTION RATIONALP-MOD))
 (6 6 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (6 6 (:LINEAR EXPT-LINEAR-UPPER-<))
 (6 6 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (6 6 (:LINEAR EXPT-LINEAR-LOWER-<))
 (6 6 (:LINEAR EXPT->=-1-TWO))
 (6 6 (:LINEAR EXPT->-1-TWO))
 (6 6 (:LINEAR EXPT-<=-1-ONE))
 (6 6 (:LINEAR EXPT-<-1-ONE))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (4 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
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
 (4 1 (:REWRITE RATIONALP-X))
 (3 3 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (2 2
    (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (2 2 (:REWRITE DEFAULT-MOD-1))
 (2 2 (:REWRITE |(mod x (- y))| . 3))
 (2 2 (:REWRITE |(mod x (- y))| . 2))
 (2 2 (:REWRITE |(mod x (- y))| . 1))
 (2 2
    (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (2 2 (:REWRITE |(mod (- x) y)| . 3))
 (2 2 (:REWRITE |(mod (- x) y)| . 2))
 (2 2 (:REWRITE |(mod (- x) y)| . 1))
 (2 2
    (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (1 1 (:REWRITE REDUCE-RATIONALP-+))
 (1 1 (:REWRITE REDUCE-RATIONALP-*))
 (1 1 (:REWRITE RATIONALP-MINUS-X))
 (1 1 (:REWRITE |(equal (+ (- c) x) y)|))
 (1 1
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (1 1
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (1 1 (:META META-RATIONALP-CORRECT)))
(SMAN::MX-ROVER-CORRECT-LEMMA1
 (3002449 2950 (:REWRITE MOD-ZERO . 4))
 (2930158 173276 (:REWRITE DEFAULT-PLUS-1))
 (2884671 173276 (:REWRITE DEFAULT-PLUS-2))
 (2859554 2950 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (2661563 2949 (:REWRITE MOD-X-Y-=-X . 4))
 (2414516 2414516
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (2414516 2414516
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (2414516 2414516
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (2019194 2950 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (1865797 107155
          (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (1650097 99946 (:REWRITE DEFAULT-TIMES-2))
 (1392601 107155
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (1392601 107155
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (1392601 107155
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (750085 107155
         (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (750085 107155
         (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (750085 107155
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (750085 107155
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (750085 107155
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (750085 107155
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (750085 107155
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (750085 107155
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (750085 107155
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (744505
  744505
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (744505
      744505
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (744505
     744505
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (744505 744505
         (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (723972 2953 (:REWRITE DEFAULT-MOD-RATIO))
 (641524 8282 (:REWRITE FLOOR-ZERO . 3))
 (623493 99946 (:REWRITE DEFAULT-TIMES-1))
 (496537 8282 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (444331 8282 (:REWRITE FLOOR-=-X/Y . 2))
 (439922 173831 (:REWRITE DEFAULT-MINUS))
 (425378 8388 (:REWRITE DEFAULT-FLOOR-RATIO))
 (420964 8388 (:REWRITE SMAN::UNNECESSARY-FLOOR))
 (396697 39676 (:REWRITE DEFAULT-DIVIDE))
 (388819 1633
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (383610 23454
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (372451 12979 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (367343 28289
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (347511 8282 (:REWRITE FLOOR-ZERO . 4))
 (256755 28478 (:REWRITE DEFAULT-LESS-THAN-2))
 (256597 29993 (:REWRITE THE-FLOOR-BELOW))
 (220864 8282 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (212007 2841
         (:REWRITE |(mod (+ x (mod a b)) y)|))
 (212007 2841
         (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (211431 2841 (:REWRITE MOD-X-Y-=-X . 2))
 (207194 8282 (:REWRITE FLOOR-ZERO . 2))
 (207194 8282 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (207194 8282 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (192338 45215
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (182449 28478 (:REWRITE DEFAULT-LESS-THAN-1))
 (179253 8282 (:REWRITE FLOOR-ZERO . 5))
 (158935 45215 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (145021 6101 (:REWRITE |(< (+ (- c) x) y)|))
 (123120 8250 (:REWRITE FLOOR-CANCEL-*-CONST))
 (122550 8250
         (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (122550 8250
         (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (122550 8250
         (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (122452 3707 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (112288 2950 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (112288 2950 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (106843 2953 (:REWRITE DEFAULT-MOD-1))
 (104721 104721
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (86617 4173 (:LINEAR EXPT-<=-1-TWO))
 (86240 45197
        (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (84493 4173 (:LINEAR EXPT-<-1-TWO))
 (83160 8388 (:REWRITE DEFAULT-FLOOR-2))
 (60629 16077 (:META META-INTEGERP-CORRECT))
 (54065 2723 (:REWRITE MOD-CANCEL-*-CONST))
 (47782 47782 (:REWRITE FOLD-CONSTS-IN-+))
 (47390 4173 (:LINEAR EXPT-X->=-X))
 (47390 4173 (:LINEAR EXPT-X->-X))
 (45215 45215
        (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (45197 45197
        (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (45195 45195 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (45195 45195
        (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (43853 43853 (:REWRITE DEFAULT-EXPT-2))
 (43853 43853 (:REWRITE DEFAULT-EXPT-1))
 (43853 43853 (:REWRITE |(expt 1/c n)|))
 (43853 43853 (:REWRITE |(expt (- x) n)|))
 (34854 1032 (:LINEAR MOD-BOUNDS-3))
 (33553 7270 (:REWRITE |(< y (+ (- c) x))|))
 (28681 28465
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (28681 28465
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (23497 23461
        (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (23463 23463
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (23463 23463
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (23463 23463
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (23463 23463
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (23463 23463
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (23463 23463
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (23463 23463
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (23463 23463
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (23463 23463 (:REWRITE |(< (/ x) (/ y))|))
 (23463 23463 (:REWRITE |(< (- x) (- y))|))
 (23461 23461 (:REWRITE INTEGERP-<-CONSTANT))
 (23461 23461 (:REWRITE CONSTANT-<-INTEGERP))
 (23461 23461 (:REWRITE |(< c (- x))|))
 (23461 23461 (:REWRITE |(< (- x) c)|))
 (21564 2064 (:LINEAR MOD-BOUNDS-2))
 (18710 2567
        (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (18444 2301
        (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (18159 2301
        (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (17700 8250
        (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (17700 8250
        (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (17700 8250
        (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (15726 317 (:REWRITE FLOOR-=-X/Y . 4))
 (14400 298 (:REWRITE INTEGERP-MOD-2))
 (13184 298 (:REWRITE INTEGERP-MOD-1))
 (9087 9087 (:REWRITE |(< x (+ c/d y))|))
 (9044 266 (:REWRITE FLOOR-POSITIVE . 3))
 (8683 8388 (:REWRITE DEFAULT-FLOOR-1))
 (8346 8346
       (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (8346 8346
       (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (8346 8346
       (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (8346 8346
       (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (8250 8250 (:REWRITE |(floor x (- y))| . 2))
 (8250 8250 (:REWRITE |(floor x (- y))| . 1))
 (8250 8250 (:REWRITE |(floor (- x) y)| . 2))
 (8250 8250 (:REWRITE |(floor (- x) y)| . 1))
 (8246 266 (:REWRITE FLOOR-POSITIVE . 2))
 (8246 266 (:REWRITE FLOOR-NONPOSITIVE . 1))
 (7366 7366
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (7366 7366
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (7366 7366
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (7292 7292 (:REWRITE |(< (+ c/d x) y)|))
 (6650 266 (:REWRITE FLOOR-POSITIVE . 4))
 (6650 266 (:REWRITE FLOOR-NONPOSITIVE . 3))
 (6650 266 (:REWRITE FLOOR-NONPOSITIVE . 2))
 (5129 5129 (:REWRITE |(< (* x y) 0)|))
 (5072 317
       (:REWRITE |(equal (floor (+ x y) z) x)|))
 (4812 4092
       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4812 4092
       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4624 4624 (:REWRITE |(< 0 (* x y))|))
 (4328 4328 (:REWRITE |(< (/ x) 0)|))
 (4174 4174 (:LINEAR EXPT-LINEAR-LOWER-<))
 (4173 4173 (:LINEAR EXPT-LINEAR-UPPER-<))
 (4173 4173 (:LINEAR EXPT->=-1-TWO))
 (4173 4173 (:LINEAR EXPT->-1-TWO))
 (4173 4173 (:LINEAR EXPT-<=-1-ONE))
 (4173 4173 (:LINEAR EXPT-<-1-ONE))
 (4137 85 (:REWRITE SMAN::R-!R-DIFF-BELOW))
 (4023 3859 (:REWRITE |(< 0 (/ x))|))
 (3538 2953 (:REWRITE DEFAULT-MOD-2))
 (3428 3092
       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (3428 3092
       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (3156 2301
       (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (2953 85 (:REWRITE SMAN::R-!R-DIFF-ABOVE))
 (2563 1597 (:REWRITE |(equal (- x) (- y))|))
 (2325 1085 (:LINEAR SMAN::BYTEP-MI))
 (2316 2301
       (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (2301 2301 (:REWRITE |(mod x (- y))| . 3))
 (2301 2301 (:REWRITE |(mod x (- y))| . 2))
 (2301 2301 (:REWRITE |(mod x (- y))| . 1))
 (2301 2301 (:REWRITE |(mod (- x) y)| . 3))
 (2301 2301 (:REWRITE |(mod (- x) y)| . 2))
 (2301 2301 (:REWRITE |(mod (- x) y)| . 1))
 (1928 36 (:REWRITE |(floor (+ x r) i)|))
 (1750 1750
       (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (1741 1633
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (1667 1597 (:REWRITE |(equal (/ x) c)|))
 (1649 1313
       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (1597 1597 (:REWRITE |(equal c (/ x))|))
 (1597 1597 (:REWRITE |(equal (/ x) (/ y))|))
 (1592 1592
       (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (1592 1592 (:REWRITE |(equal c (- x))|))
 (1592 1592 (:REWRITE |(equal (- x) c)|))
 (1224 8
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4A-EXPT))
 (997 22
      (:REWRITE |(* (expt x m) (expt x n))|))
 (894 66 (:REWRITE |(* (/ x) (expt x n))|))
 (729 729 (:REWRITE |(equal (* x y) 0)|))
 (579 579 (:REWRITE DEFAULT-LOGAND-1))
 (540 540 (:TYPE-PRESCRIPTION ABS))
 (341 1 (:REWRITE |(* (if a b c) x)|))
 (307 307 (:REWRITE |(equal (+ (- c) x) y)|))
 (266 266 (:REWRITE FLOOR-ZERO . 1))
 (266 266 (:REWRITE FLOOR-POSITIVE . 1))
 (266 266
      (:REWRITE |(mod (floor x y) z)| . 5))
 (266 266
      (:REWRITE |(mod (floor x y) z)| . 4))
 (266 266
      (:REWRITE |(mod (floor x y) z)| . 3))
 (266 266
      (:REWRITE |(mod (floor x y) z)| . 2))
 (123 41 (:REWRITE SMAN::!R-R))
 (98 98
     (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 3))
 (98 98
     (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 2))
 (98 2 (:REWRITE MOD-X-Y-=-X+Y . 1))
 (52 52 (:TYPE-PRESCRIPTION RATIONALP-MOD))
 (41 41 (:REWRITE SMAN::!R-DEFAULT-1))
 (20 5 (:REWRITE RATIONALP-X))
 (16 2 (:REWRITE MOD-X-Y-=-X-Y . 1))
 (8 8
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (8 8
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (8 8
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (5 5 (:REWRITE REDUCE-RATIONALP-+))
 (5 5 (:REWRITE REDUCE-RATIONALP-*))
 (5 5 (:REWRITE RATIONALP-MINUS-X))
 (5 5 (:REWRITE |(not (equal x (/ y)))|))
 (5 5 (:REWRITE |(equal x (/ y))|))
 (5 5 (:REWRITE |(/ (/ x))|))
 (5 5 (:META META-RATIONALP-CORRECT))
 (2 2
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (2 2
    (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (2 2
    (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (2 2
    (:REWRITE |(< x (/ y)) with (< y 0)|)))
(SMAN::MX-ROVER-CORRECT-LEMMA2
 (5712506 57
          (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 1))
 (5672109 34635 (:REWRITE THE-FLOOR-ABOVE))
 (2436497 3580 (:REWRITE MOD-ZERO . 4))
 (2354450 3579 (:REWRITE MOD-X-Y-=-X . 3))
 (2230478 3580 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (2114856 3579 (:REWRITE MOD-X-Y-=-X . 4))
 (1951052 163250 (:REWRITE DEFAULT-PLUS-1))
 (1798219 163250 (:REWRITE DEFAULT-PLUS-2))
 (1711131 1711131
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (1711131 1711131
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (1711131 1711131
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (1705727 1705727
          (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (1620925 3580 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (1376485 77257
          (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (1252469 89935 (:REWRITE DEFAULT-TIMES-2))
 (1003771 77257
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (1003771 77257
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (1003771 77257
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (837006 6944 (:REWRITE SMAN::UNNECESSARY-FLOOR))
 (702757
  702757
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (702757
      702757
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (702757
     702757
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (702757 702757
         (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (599770 3582 (:REWRITE DEFAULT-MOD-RATIO))
 (540799 77257
         (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (540799 77257
         (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (540799 77257
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (540799 77257
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (540799 77257
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (540799 77257
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (540799 77257
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (540799 77257
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (540799 77257
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (537045 3044 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (518231 89935 (:REWRITE DEFAULT-TIMES-1))
 (506331 6850 (:REWRITE FLOOR-ZERO . 3))
 (410827 6850 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (392433 1462
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (358482 6850 (:REWRITE FLOOR-=-X/Y . 2))
 (349718 143290 (:REWRITE DEFAULT-MINUS))
 (345099 6944 (:REWRITE DEFAULT-FLOOR-RATIO))
 (326406 32646 (:REWRITE DEFAULT-DIVIDE))
 (307085 6850 (:REWRITE FLOOR-ZERO . 4))
 (278865 11356 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (273434 25277
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (272629 416
         (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (207765 33532 (:REWRITE DEFAULT-LESS-THAN-2))
 (197237 34635 (:REWRITE THE-FLOOR-BELOW))
 (196224 15138
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (179544 6850 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (178081 3579
         (:REWRITE |(mod (+ x (mod a b)) y)|))
 (178081 3579
         (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (177595 3579 (:REWRITE MOD-X-Y-=-X . 2))
 (171457 6850 (:REWRITE FLOOR-ZERO . 2))
 (171457 6850 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (171457 6850 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (168551 4531 (:LINEAR EXPT-<=-1-TWO))
 (165771 4531 (:LINEAR EXPT-<-1-TWO))
 (161138 7286 (:REWRITE |(< (+ (- c) x) y)|))
 (154400 33532 (:REWRITE DEFAULT-LESS-THAN-1))
 (129391 6850 (:REWRITE FLOOR-ZERO . 5))
 (124704 17275 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (124278 17275
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (124278 17275
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (111161 3044 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (109566 17275
         (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (101653 6823
         (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (101653 6823
         (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (101653 6823
         (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (101617 4531 (:LINEAR EXPT-X->=-X))
 (101617 4531 (:LINEAR EXPT-X->-X))
 (99118 6823 (:REWRITE FLOOR-CANCEL-*-CONST))
 (92285 3580 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (92285 3580 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (90022 90022
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (88868 3582 (:REWRITE DEFAULT-MOD-1))
 (68657 6944 (:REWRITE DEFAULT-FLOOR-2))
 (53405 9493 (:REWRITE |(< y (+ (- c) x))|))
 (52754 12870 (:META META-INTEGERP-CORRECT))
 (52171 3503 (:REWRITE MOD-CANCEL-*-CONST))
 (47770 354 (:REWRITE |(* c (* d x))|))
 (47579 3007 (:REWRITE |(mod x 1)|))
 (45762 1529 (:LINEAR MOD-BOUNDS-3))
 (42137 42137 (:REWRITE FOLD-CONSTS-IN-+))
 (39463 17275 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (38091 38079 (:REWRITE |(expt 1/c n)|))
 (38079 38079 (:REWRITE DEFAULT-EXPT-2))
 (38079 38079 (:REWRITE DEFAULT-EXPT-1))
 (38079 38079 (:REWRITE |(expt (- x) n)|))
 (33527 33527
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (33527 33527
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (30640 3058 (:LINEAR MOD-BOUNDS-2))
 (29958 3443
        (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (29752 3237
        (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (25424 25292
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (25387 25292 (:REWRITE |(< (- x) c)|))
 (25292 25292
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (25292 25292
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (25292 25292
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (25292 25292
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (25292 25292 (:REWRITE |(< c (- x))|))
 (25292 25292
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (25292 25292
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (25292 25292
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (25292 25292 (:REWRITE |(< (/ x) (/ y))|))
 (25292 25292 (:REWRITE |(< (- x) (- y))|))
 (25291 25291 (:REWRITE INTEGERP-<-CONSTANT))
 (25291 25291 (:REWRITE CONSTANT-<-INTEGERP))
 (23616 184 (:REWRITE |(* -1 x)|))
 (17275 17275 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (17275 17275
        (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (17275 17275
        (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (17275 17275
        (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (14338 6823
        (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (14338 6823
        (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (14338 6823
        (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (12584 12584 (:REWRITE |(< x (+ c/d y))|))
 (11710 3237
        (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (11630 184 (:LINEAR SMAN::R-BOUND))
 (9062 9062
       (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (9062 9062
       (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (9062 9062
       (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (9062 9062
       (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (8791 2 (:REWRITE |(< (if a b c) x)|))
 (8766 140
       (:REWRITE SMAN::MX-ROVER-CORRECT-LEMMA1))
 (8756 8756 (:REWRITE |(< (+ c/d x) y)|))
 (7243 6944 (:REWRITE DEFAULT-FLOOR-1))
 (7004 206 (:REWRITE FLOOR-POSITIVE . 3))
 (6823 6823 (:REWRITE |(floor x (- y))| . 2))
 (6823 6823 (:REWRITE |(floor x (- y))| . 1))
 (6823 6823 (:REWRITE |(floor (- x) y)| . 2))
 (6823 6823 (:REWRITE |(floor (- x) y)| . 1))
 (6386 206 (:REWRITE FLOOR-POSITIVE . 2))
 (6386 206 (:REWRITE FLOOR-NONPOSITIVE . 1))
 (5984 222 (:REWRITE FLOOR-=-X/Y . 4))
 (5970 4 (:REWRITE MOD-X-Y-=-X-Y . 1))
 (5292 5292
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (5292 5292
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (5292 5292
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (5204 5204 (:REWRITE |(< (* x y) 0)|))
 (5150 5150 (:REWRITE |(< 0 (* x y))|))
 (5150 206 (:REWRITE FLOOR-POSITIVE . 4))
 (5150 206 (:REWRITE FLOOR-NONPOSITIVE . 3))
 (5150 206 (:REWRITE FLOOR-NONPOSITIVE . 2))
 (4531 4531 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (4531 4531 (:LINEAR EXPT-LINEAR-UPPER-<))
 (4531 4531 (:LINEAR EXPT-LINEAR-LOWER-<))
 (4531 4531 (:LINEAR EXPT->=-1-TWO))
 (4531 4531 (:LINEAR EXPT->-1-TWO))
 (4531 4531 (:LINEAR EXPT-<=-1-ONE))
 (4531 4531 (:LINEAR EXPT-<-1-ONE))
 (4391 2222
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (4344 2172 (:TYPE-PRESCRIPTION SMAN::NATP-MI))
 (4086 3582 (:REWRITE DEFAULT-MOD-2))
 (3927 3237
       (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (3753 3753 (:REWRITE |(< (/ x) 0)|))
 (3734 3734 (:REWRITE |(< 0 (/ x))|))
 (3685 4 (:REWRITE MOD-X-Y-=-X+Y . 1))
 (3584 3584
       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (3584 3584
       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (3552 222
       (:REWRITE |(equal (floor (+ x y) z) x)|))
 (3262 3262 (:TYPE-PRESCRIPTION SMAN::STP))
 (3252 3237
       (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (3237 3237 (:REWRITE |(mod x (- y))| . 3))
 (3237 3237 (:REWRITE |(mod x (- y))| . 2))
 (3237 3237 (:REWRITE |(mod x (- y))| . 1))
 (3237 3237 (:REWRITE |(mod (- x) y)| . 3))
 (3237 3237 (:REWRITE |(mod (- x) y)| . 2))
 (3237 3237 (:REWRITE |(mod (- x) y)| . 1))
 (3040 95 (:REWRITE INTEGERP-MOD-2))
 (3040 95 (:REWRITE INTEGERP-MOD-1))
 (2529 27 (:REWRITE |(floor (+ x r) i)|))
 (2435 1442 (:REWRITE |(equal (- x) (- y))|))
 (2423 249 (:REWRITE |(equal (+ (- c) x) y)|))
 (2222 2222
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (2025 2025
       (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (1923 1923
       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (1923 1923
       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (1890 882 (:LINEAR SMAN::BYTEP-MI))
 (1815 37 (:REWRITE SMAN::R-!R-DIFF-BELOW))
 (1484 1442 (:REWRITE |(equal (/ x) c)|))
 (1466 1439 (:REWRITE |(equal (- x) c)|))
 (1462 1462
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (1442 1442 (:REWRITE |(equal c (/ x))|))
 (1442 1442 (:REWRITE |(equal (/ x) (/ y))|))
 (1439 1439
       (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (1439 1439 (:REWRITE |(equal c (- x))|))
 (1209 1209
       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (892 29
      (:REWRITE |(* (expt x m) (expt x n))|))
 (753 3 (:REWRITE MOD-ZERO . 1))
 (436 32 (:REWRITE |(* (/ x) (expt x n))|))
 (354 2 (:REWRITE |(* (if a b c) x)|))
 (307 307 (:REWRITE DEFAULT-LOGAND-1))
 (206 206 (:REWRITE FLOOR-ZERO . 1))
 (206 206 (:REWRITE FLOOR-POSITIVE . 1))
 (206 206
      (:REWRITE |(mod (floor x y) z)| . 5))
 (206 206
      (:REWRITE |(mod (floor x y) z)| . 4))
 (206 206
      (:REWRITE |(mod (floor x y) z)| . 3))
 (206 206
      (:REWRITE |(mod (floor x y) z)| . 2))
 (174 1 (:REWRITE |(integerp (expt x n))|))
 (123 41 (:REWRITE SMAN::!R-R))
 (99 99 (:TYPE-PRESCRIPTION NATP))
 (86 86 (:TYPE-PRESCRIPTION RATIONALP-MOD))
 (75 3 (:REWRITE MOD-ZERO . 2))
 (57 57
     (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 3))
 (57 57
     (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 2))
 (41 41 (:REWRITE SMAN::!R-DEFAULT-1))
 (30 3
     (:REWRITE |(equal (mod (+ x y) z) x)|))
 (8 2 (:REWRITE RATIONALP-X))
 (3 3
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (3 3 (:REWRITE |(not (equal x (/ y)))|))
 (3 3 (:REWRITE |(equal x (/ y))|))
 (3 3
    (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (3 3
    (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (3 3 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (3 3 (:REWRITE |(/ (/ x))|))
 (2 2 (:REWRITE REDUCE-RATIONALP-+))
 (2 2 (:REWRITE REDUCE-RATIONALP-*))
 (2 2 (:REWRITE RATIONALP-MINUS-X))
 (2 2 (:META META-RATIONALP-CORRECT)))
(SMAN::MX-ROVER-CORRECT-LEMMA3
 (73472 160 (:LINEAR LINEAR-FLOOR-BOUNDS-1))
 (58269 5617 (:REWRITE DEFAULT-PLUS-1))
 (45229 45181
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (45229 45181
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (45229 45181
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (31461 2749 (:REWRITE THE-FLOOR-ABOVE))
 (27380 220 (:REWRITE MOD-X-Y-=-X . 3))
 (26666 220 (:REWRITE MOD-ZERO . 4))
 (26508 220 (:REWRITE CANCEL-MOD-+))
 (26034 220 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (25704 220 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (24920 220 (:REWRITE MOD-X-Y-=-X . 4))
 (22643 305 (:REWRITE SMAN::UNNECESSARY-FLOOR))
 (18472 5617 (:REWRITE DEFAULT-PLUS-2))
 (17326 4678
        (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (16544 6210 (:REWRITE DEFAULT-TIMES-2))
 (16088 220
        (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (14832 1648
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (14832 1648
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (14832 1648
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (14832 1648
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (14832 1648
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (14562 266
        (:REWRITE SMAN::MX-ROVER-CORRECT-LEMMA1))
 (14132 1660 (:REWRITE INTEGERP-MINUS-X))
 (13372 940 (:REWRITE |(* (- x) y)|))
 (12486 220 (:REWRITE MOD-ZERO . 3))
 (12420 6210 (:REWRITE DEFAULT-TIMES-1))
 (11624 8 (:REWRITE |(mod (floor x y) z)| . 1))
 (10000 200 (:REWRITE CANCEL-FLOOR-+))
 (9581 1513 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (9461 1513
       (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (9461 1513
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (9012 120 (:REWRITE |(* (* x y) z)|))
 (8240 1648
       (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
 (8240 1648
       (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (8240 1648
       (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (8240 1648
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (8240 1648
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (8240 1648
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (8240 1648
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (8240 1648
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (8240 1648
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
 (8240 1648
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (8240 1648
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (8144 88 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (8024 220 (:REWRITE DEFAULT-MOD-RATIO))
 (7222
  7222
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (7222
      7222
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (7222
     7222
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (7222 7222
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (7222 7222
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (7040 200 (:REWRITE FLOOR-ZERO . 3))
 (7018 1358 (:REWRITE DEFAULT-MINUS))
 (5801 1513 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (5749 1513 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
 (5317 1513
       (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (4678 4678
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (4678 4678
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (4678 4678
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (4397 2749 (:REWRITE THE-FLOOR-BELOW))
 (4294 2526 (:REWRITE |(< c (- x))|))
 (4181 2717 (:REWRITE DEFAULT-LESS-THAN-1))
 (4044 60 (:REWRITE BUBBLE-DOWN-*-MATCH-1))
 (3984 48 (:REWRITE |(* (/ c) (expt d n))|))
 (3849 2717 (:REWRITE DEFAULT-LESS-THAN-2))
 (3848 200 (:REWRITE FLOOR-ZERO . 5))
 (3848 200 (:REWRITE FLOOR-ZERO . 4))
 (3826 71 (:REWRITE SMAN::R-!R-DIFF-ABOVE))
 (3779 305 (:REWRITE DEFAULT-FLOOR-RATIO))
 (3752 200 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (3750 462 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (3704 200 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (3678 71
       (:REWRITE SMAN::MX-ROVER-CORRECT-LEMMA2))
 (3372 1686 (:TYPE-PRESCRIPTION SMAN::NATP-MI))
 (3268 220 (:REWRITE MOD-X-Y-=-X . 2))
 (3268 220
       (:REWRITE |(mod (+ x (mod a b)) y)|))
 (3268 220
       (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (3155 2699
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (3147 71 (:REWRITE SMAN::R-!R-DIFF-BELOW))
 (2819 2691
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (2744 200 (:REWRITE FLOOR-=-X/Y . 2))
 (2526 2526
       (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (2526 2526
       (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (2526 2526
       (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (2526 2526
       (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (2526 2526
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (2526 2526
       (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (2526 2526
       (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (2526 2526
       (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (2526 2526 (:REWRITE |(< (/ x) (/ y))|))
 (2526 2526 (:REWRITE |(< (- x) (- y))|))
 (2509 2509
       (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (2509 2509 (:REWRITE INTEGERP-<-CONSTANT))
 (2509 2509 (:REWRITE CONSTANT-<-INTEGERP))
 (2509 2509 (:REWRITE |(< (- x) c)|))
 (2272 2272 (:TYPE-PRESCRIPTION SMAN::STP))
 (2146 61 (:LINEAR MOD-BOUNDS-3))
 (2136 220 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (2136 220 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (2112 220 (:REWRITE MOD-CANCEL-*-CONST))
 (2033 2033
       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (1710 250
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (1710 250
       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (1648 1648 (:TYPE-PRESCRIPTION FLOOR))
 (1525 1513 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (1525 1513
       (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (1525 1513
       (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (1525 1513
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (1352 220 (:REWRITE DEFAULT-MOD-1))
 (1308 12 (:REWRITE BUBBLE-DOWN-*-BUBBLE-DOWN))
 (1276 1276 (:REWRITE REDUCE-INTEGERP-+))
 (1276 1276 (:META META-INTEGERP-CORRECT))
 (1152 36 (:REWRITE |(integerp (- x))|))
 (1122 1122 (:REWRITE |(< (* x y) 0)|))
 (1063 1063 (:REWRITE |(< (/ x) 0)|))
 (1044 1044
       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1044 1044
       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1000 200 (:REWRITE FLOOR-ZERO . 2))
 (1000 200 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (1000 200 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (977 441 (:REWRITE |(< y (+ (- c) x))|))
 (968 200 (:REWRITE FLOOR-CANCEL-*-CONST))
 (960 448 (:LINEAR SMAN::BYTEP-MI))
 (904 200
      (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (904 200
      (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (856 80 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (840 84 (:REWRITE |(* 1 x)|))
 (792 200
      (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (768 24 (:REWRITE |(mod x 1)|))
 (730 122 (:LINEAR MOD-BOUNDS-2))
 (536 208
      (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (528 200
      (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (513 513 (:REWRITE |(< x (+ c/d y))|))
 (513 513 (:REWRITE |(< 0 (* x y))|))
 (480 480 (:REWRITE FOLD-CONSTS-IN-+))
 (480 480 (:REWRITE |(< 0 (/ x))|))
 (456 51 (:REWRITE DEFAULT-DIVIDE))
 (440 305 (:REWRITE DEFAULT-FLOOR-2))
 (434 434
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (434 434
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (431 431 (:REWRITE |(< (+ c/d x) y)|))
 (398 305 (:REWRITE DEFAULT-FLOOR-1))
 (356 356 (:REWRITE |(< (+ (- c) x) y)|))
 (348 348 (:REWRITE DEFAULT-LOGAND-1))
 (296 200
      (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (296 200
      (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (273 273 (:TYPE-PRESCRIPTION NATP))
 (264 264 (:TYPE-PRESCRIPTION ABS))
 (256 256
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (256 256
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (256 256 (:REWRITE |(equal c (/ x))|))
 (256 256 (:REWRITE |(equal (/ x) (/ y))|))
 (256 256 (:REWRITE |(equal (- x) (- y))|))
 (250 250
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (250 250 (:REWRITE |(equal c (- x))|))
 (250 250 (:REWRITE |(equal (- x) c)|))
 (232 232
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (227 227 (:REWRITE DEFAULT-EXPT-2))
 (227 227 (:REWRITE DEFAULT-EXPT-1))
 (227 227 (:REWRITE |(expt 1/c n)|))
 (227 227 (:REWRITE |(expt (- x) n)|))
 (220 220 (:REWRITE DEFAULT-MOD-2))
 (212 212
      (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (205 31
      (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (205 31
      (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (200 200 (:REWRITE |(mod x (- y))| . 3))
 (200 200 (:REWRITE |(mod x (- y))| . 2))
 (200 200 (:REWRITE |(mod x (- y))| . 1))
 (200 200
      (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (200 200
      (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (200 200 (:REWRITE |(mod (- x) y)| . 3))
 (200 200 (:REWRITE |(mod (- x) y)| . 2))
 (200 200 (:REWRITE |(mod (- x) y)| . 1))
 (200 200 (:REWRITE |(floor x (- y))| . 2))
 (200 200 (:REWRITE |(floor x (- y))| . 1))
 (200 200
      (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (200 200
      (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (200 200 (:REWRITE |(floor (- x) y)| . 2))
 (200 200 (:REWRITE |(floor (- x) y)| . 1))
 (148 1 (:REWRITE |(integerp (expt x n))|))
 (132 132
      (:REWRITE SMAN::INTEGERP-PRODUCT-BY-EXPT))
 (132 4 (:LINEAR EXPT-<=-1-TWO))
 (131 57 (:REWRITE SMAN::!R-R))
 (112 4 (:LINEAR EXPT-X->=-X))
 (112 4 (:LINEAR EXPT-X->-X))
 (72 8 (:REWRITE FLOOR-POSITIVE . 2))
 (72 8 (:REWRITE FLOOR-NONPOSITIVE . 1))
 (57 57 (:REWRITE SMAN::!R-DEFAULT-1))
 (40 8 (:REWRITE FLOOR-POSITIVE . 4))
 (40 8 (:REWRITE FLOOR-POSITIVE . 3))
 (40 8 (:REWRITE FLOOR-NONPOSITIVE . 3))
 (40 8 (:REWRITE FLOOR-NONPOSITIVE . 2))
 (40 8 (:REWRITE FLOOR-=-X/Y . 4))
 (40 8
     (:REWRITE |(equal (floor (+ x y) z) x)|))
 (36 36 (:REWRITE |(equal (* x y) 0)|))
 (36 36
     (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (31 31
     (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (31 31
     (:REWRITE |(< x (/ y)) with (< y 0)|))
 (18 18 (:REWRITE |(equal (+ (- c) x) y)|))
 (18 6 (:TYPE-PRESCRIPTION RATIONALP-MOD))
 (15 15
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (14 14 (:REWRITE |(* c (* d x))|))
 (8 8 (:REWRITE FLOOR-ZERO . 1))
 (8 8 (:REWRITE FLOOR-POSITIVE . 1))
 (8 8 (:REWRITE |(mod (floor x y) z)| . 5))
 (8 8 (:REWRITE |(mod (floor x y) z)| . 4))
 (8 8 (:REWRITE |(mod (floor x y) z)| . 3))
 (8 8 (:REWRITE |(mod (floor x y) z)| . 2))
 (8 8 (:REWRITE |(* a (/ a) b)|))
 (8 8
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (8 8
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (8 8
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (8 8
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (6 6 (:REWRITE |(not (equal x (/ y)))|))
 (6 6 (:REWRITE |(equal x (/ y))|))
 (4 4 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (4 4 (:LINEAR EXPT-LINEAR-UPPER-<))
 (4 4 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (4 4 (:LINEAR EXPT-LINEAR-LOWER-<))
 (4 4 (:LINEAR EXPT->=-1-TWO))
 (4 4 (:LINEAR EXPT->-1-TWO))
 (4 4 (:LINEAR EXPT-<=-1-ONE))
 (4 4 (:LINEAR EXPT-<-1-TWO))
 (4 4 (:LINEAR EXPT-<-1-ONE)))
