(RTL::DISTINCT-SYMBOLS-ATOM
     (176 88
          (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-X))
     (176 88
          (:TYPE-PRESCRIPTION RTL::INT-CAR-TRIPP))
     (94 94 (:TYPE-PRESCRIPTION RTL::TRIPP))
     (94 94 (:TYPE-PRESCRIPTION RTL::ECP))
     (15 15 (:REWRITE DEFAULT-CAR))
     (12 12 (:REWRITE RTL::PERM-MEMBER))
     (12 6
         (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-Y))
     (12 6
         (:TYPE-PRESCRIPTION RTL::INT-CADR-TRIPP))
     (10 10 (:REWRITE DEFAULT-CDR))
     (7 7 (:REWRITE SIMPLIFY-SUMS-EQUAL))
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
     (7 7 (:REWRITE |(equal (- x) (- y))|)))
(RTL::ALL-INTEGERS-INTEGER
     (48 24
         (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-X))
     (48 24
         (:TYPE-PRESCRIPTION RTL::INT-CAR-TRIPP))
     (36 36 (:TYPE-PRESCRIPTION RTL::TRIPP))
     (36 36 (:TYPE-PRESCRIPTION RTL::ECP))
     (18 11 (:REWRITE DEFAULT-LESS-THAN-2))
     (18 6 (:REWRITE RTL::INTEGERP-EC-X))
     (18 6 (:REWRITE RTL::INT-CAR-TRIPP))
     (17 10 (:REWRITE DEFAULT-PLUS-2))
     (14 10
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (14 8 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (13 8 (:REWRITE SIMPLIFY-SUMS-<))
     (11 11 (:REWRITE THE-FLOOR-BELOW))
     (11 11 (:REWRITE THE-FLOOR-ABOVE))
     (11 11
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (11 11
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (11 11 (:REWRITE REDUCE-INTEGERP-+))
     (11 11 (:REWRITE INTEGERP-MINUS-X))
     (11 11 (:REWRITE DEFAULT-LESS-THAN-1))
     (11 11 (:META META-INTEGERP-CORRECT))
     (10 10
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (10 10 (:REWRITE NORMALIZE-ADDENDS))
     (10 10 (:REWRITE INTEGERP-<-CONSTANT))
     (10 10 (:REWRITE DEFAULT-PLUS-1))
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
     (9 9 (:REWRITE DEFAULT-CAR))
     (6 6 (:REWRITE DEFAULT-CDR))
     (5 5 (:REWRITE ZP-OPEN))
     (4 4 (:REWRITE |(< y (+ (- c) x))|))
     (4 4 (:REWRITE |(< x (+ c/d y))|))
     (4 4 (:REWRITE |(< (/ x) 0)|))
     (4 4 (:REWRITE |(< (* x y) 0)|))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (2 1
        (:TYPE-PRESCRIPTION RTL::ALL-INTEGERS-INTEGER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (1 1 (:REWRITE |(< 0 (/ x))|))
     (1 1 (:REWRITE |(< 0 (* x y))|))
     (1 1 (:REWRITE |(< (+ c/d x) y)|)))
(RTL::ALL-INTEGERS-NTHCDR
     (70 8 (:REWRITE ZP-OPEN))
     (45 45 (:TYPE-PRESCRIPTION RTL::ECP))
     (37 37 (:TYPE-PRESCRIPTION RTL::TRIPP))
     (33 11 (:REWRITE RTL::INTEGERP-EC-X))
     (33 11 (:REWRITE RTL::INT-CAR-TRIPP))
     (30 15
         (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-X))
     (30 15
         (:TYPE-PRESCRIPTION RTL::INT-CAR-TRIPP))
     (30 2 (:REWRITE |(+ (+ x y) z)|))
     (20 20 (:REWRITE DEFAULT-PLUS-2))
     (20 20 (:REWRITE DEFAULT-PLUS-1))
     (16 8
         (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-Y))
     (12 12 (:REWRITE DEFAULT-CAR))
     (11 11 (:REWRITE REDUCE-INTEGERP-+))
     (11 11 (:REWRITE INTEGERP-MINUS-X))
     (11 11 (:META META-INTEGERP-CORRECT))
     (10 10 (:REWRITE DEFAULT-CDR))
     (10 2 (:REWRITE |(+ c (+ d x))|))
     (9 9
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (9 9 (:REWRITE NORMALIZE-ADDENDS))
     (2 2 (:REWRITE THE-FLOOR-BELOW))
     (2 2 (:REWRITE THE-FLOOR-ABOVE))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (2 2 (:REWRITE SIMPLIFY-SUMS-<))
     (2 2 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (2 2 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (2 2
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (2 2
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (2 2 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (2 2 (:REWRITE INTEGERP-<-CONSTANT))
     (2 2 (:REWRITE DEFAULT-LESS-THAN-2))
     (2 2 (:REWRITE DEFAULT-LESS-THAN-1))
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
     (2 2 (:REWRITE |(< (- x) (- y))|)))
(RTL::NTHCDR+
     (566 283
          (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-Y))
     (283 283 (:TYPE-PRESCRIPTION RTL::ECP))
     (264 3
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (186 6 (:REWRITE ACL2-NUMBERP-X))
     (106 13 (:REWRITE ZP-OPEN))
     (90 3 (:REWRITE RATIONALP-X))
     (86 14 (:REWRITE DEFAULT-CDR))
     (84 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (55 55 (:REWRITE DEFAULT-PLUS-2))
     (55 55 (:REWRITE DEFAULT-PLUS-1))
     (28 28
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (28 28 (:REWRITE NORMALIZE-ADDENDS))
     (12 7 (:REWRITE |(+ c (+ d x))|))
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
     (9 9 (:REWRITE SIMPLIFY-SUMS-<))
     (9 9 (:REWRITE REDUCE-INTEGERP-+))
     (9 9 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (9 9 (:REWRITE INTEGERP-MINUS-X))
     (9 9 (:META META-INTEGERP-CORRECT))
     (7 7 (:REWRITE |(< (/ x) 0)|))
     (7 7 (:REWRITE |(< (* x y) 0)|))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (6 6 (:REWRITE FOLD-CONSTS-IN-+))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (3 3 (:REWRITE REDUCE-RATIONALP-+))
     (3 3 (:REWRITE REDUCE-RATIONALP-*))
     (3 3
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (3 3
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (3 3 (:REWRITE RATIONALP-MINUS-X))
     (3 3
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (3 3 (:REWRITE |(equal c (/ x))|))
     (3 3 (:REWRITE |(equal c (- x))|))
     (3 3 (:REWRITE |(equal (/ x) c)|))
     (3 3 (:REWRITE |(equal (/ x) (/ y))|))
     (3 3 (:REWRITE |(equal (- x) c)|))
     (3 3 (:REWRITE |(equal (- x) (- y))|))
     (3 3 (:REWRITE |(< y (+ (- c) x))|))
     (3 3 (:REWRITE |(< x (+ c/d y))|))
     (3 3 (:REWRITE |(< 0 (/ x))|))
     (3 3 (:REWRITE |(< 0 (* x y))|))
     (3 3 (:META META-RATIONALP-CORRECT)))
(RTL::CAR-NTHCDR
     (852 426
          (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-Y))
     (710 7
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (620 620 (:TYPE-PRESCRIPTION RTL::ECP))
     (530 14 (:REWRITE ACL2-NUMBERP-X))
     (364 182
          (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-X))
     (308 7 (:REWRITE RATIONALP-X))
     (200 14 (:REWRITE ZP-OPEN))
     (194 7 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (85 16 (:REWRITE DEFAULT-CAR))
     (70 2 (:REWRITE RTL::ALL-INTEGERS-INTEGER))
     (64 2 (:DEFINITION RTL::ALL-INTEGERS))
     (36 36 (:REWRITE DEFAULT-PLUS-2))
     (36 36 (:REWRITE DEFAULT-PLUS-1))
     (30 6 (:REWRITE |(+ c (+ d x))|))
     (30 2 (:REWRITE |(+ (+ x y) z)|))
     (22 22
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (22 22 (:REWRITE NORMALIZE-ADDENDS))
     (19 7 (:REWRITE RTL::INTEGERP-EC-X))
     (19 7 (:REWRITE RTL::INT-CAR-TRIPP))
     (9 9 (:REWRITE REDUCE-INTEGERP-+))
     (9 9 (:REWRITE INTEGERP-MINUS-X))
     (9 9 (:META META-INTEGERP-CORRECT))
     (8 4
        (:TYPE-PRESCRIPTION RTL::INT-CADR-TRIPP))
     (7 7 (:REWRITE REDUCE-RATIONALP-+))
     (7 7 (:REWRITE REDUCE-RATIONALP-*))
     (7 7
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (7 7
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (7 7 (:REWRITE RATIONALP-MINUS-X))
     (7 7
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (7 7 (:REWRITE |(equal c (/ x))|))
     (7 7 (:REWRITE |(equal c (- x))|))
     (7 7 (:REWRITE |(equal (/ x) c)|))
     (7 7 (:REWRITE |(equal (/ x) (/ y))|))
     (7 7 (:REWRITE |(equal (- x) c)|))
     (7 7 (:REWRITE |(equal (- x) (- y))|))
     (7 7 (:META META-RATIONALP-CORRECT))
     (6 6 (:REWRITE THE-FLOOR-BELOW))
     (6 6 (:REWRITE THE-FLOOR-ABOVE))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (6 6 (:REWRITE SIMPLIFY-SUMS-<))
     (6 6 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (6 6 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (6 6
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (6 6
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
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
     (4 2 (:REWRITE RTL::INT-CADR-TRIPP)))
(RTL::CONSP-NTHCDR
     (96 48
         (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-Y))
     (48 48 (:TYPE-PRESCRIPTION RTL::ECP))
     (18 12 (:REWRITE DEFAULT-PLUS-2))
     (16 10 (:REWRITE DEFAULT-LESS-THAN-2))
     (14 10
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (14 8 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (13 8 (:REWRITE SIMPLIFY-SUMS-<))
     (12 12 (:REWRITE DEFAULT-PLUS-1))
     (10 10 (:REWRITE THE-FLOOR-BELOW))
     (10 10 (:REWRITE THE-FLOOR-ABOVE))
     (10 10
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (10 10
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
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
     (9 9
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (9 9 (:REWRITE NORMALIZE-ADDENDS))
     (4 4 (:REWRITE ZP-OPEN))
     (4 4 (:REWRITE DEFAULT-CDR))
     (4 4 (:REWRITE |(< (/ x) 0)|))
     (4 4 (:REWRITE |(< (* x y) 0)|))
     (3 3 (:REWRITE |(< x (if a b c))|))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (2 2 (:REWRITE REDUCE-INTEGERP-+))
     (2 2 (:REWRITE INTEGERP-MINUS-X))
     (2 2 (:META META-INTEGERP-CORRECT))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (1 1 (:REWRITE |(< 0 (/ x))|))
     (1 1 (:REWRITE |(< 0 (* x y))|))
     (1 1 (:REWRITE |(< (+ c/d x) y)|))
     (1 1 (:REWRITE |(< (+ (- c) x) y)|)))
(RTL::MEMBER-LEN-POS (144 72
                          (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-X))
                     (144 72
                          (:TYPE-PRESCRIPTION RTL::INT-CAR-TRIPP))
                     (72 72 (:TYPE-PRESCRIPTION RTL::TRIPP))
                     (72 72 (:TYPE-PRESCRIPTION RTL::ECP))
                     (46 7
                         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                     (40 8 (:REWRITE ACL2-NUMBERP-X))
                     (16 4 (:REWRITE RATIONALP-X))
                     (11 7 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                     (11 6 (:REWRITE DEFAULT-PLUS-2))
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
                        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                     (6 6 (:REWRITE NORMALIZE-ADDENDS))
                     (6 6 (:REWRITE DEFAULT-PLUS-1))
                     (5 5 (:REWRITE RTL::PERM-MEMBER))
                     (4 4 (:REWRITE REDUCE-RATIONALP-+))
                     (4 4 (:REWRITE REDUCE-RATIONALP-*))
                     (4 4 (:REWRITE REDUCE-INTEGERP-+))
                     (4 4 (:REWRITE RATIONALP-MINUS-X))
                     (4 4 (:REWRITE INTEGERP-MINUS-X))
                     (4 4 (:REWRITE DEFAULT-CDR))
                     (4 4 (:REWRITE DEFAULT-CAR))
                     (4 4 (:META META-RATIONALP-CORRECT))
                     (4 4 (:META META-INTEGERP-CORRECT))
                     (3 3
                        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RTL::VARS)
(RTL::VALS)
(RTL::VLIST)
(RTL::ALL-INTEGERS-VALS (6 6 (:REWRITE DEFAULT-CDR))
                        (6 6 (:REWRITE DEFAULT-CAR)))
(RTL::LEN-VALS (10 5 (:REWRITE DEFAULT-PLUS-2))
               (6 6 (:REWRITE DEFAULT-CDR))
               (5 5
                  (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
               (5 5 (:REWRITE NORMALIZE-ADDENDS))
               (5 5 (:REWRITE DEFAULT-PLUS-1)))
(RTL::EVALP$)
(RTL::EVALH$)
(RTL::THETA)
(RTL::SHNFP-THETA)
(RTL::EVALH-THETA-0
 (244 30 (:REWRITE DEFAULT-PLUS-2))
 (224 30 (:REWRITE DEFAULT-PLUS-1))
 (100 100
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (100
     100
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (100 100
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (100 100
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (95 18 (:REWRITE DEFAULT-TIMES-2))
 (74 74
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (54 2
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (53 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (34 18 (:REWRITE DEFAULT-TIMES-1))
 (15 8 (:REWRITE DEFAULT-EXPT-1))
 (12 12
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (12 12 (:REWRITE NORMALIZE-ADDENDS))
 (8 8 (:REWRITE DEFAULT-EXPT-2))
 (8 8 (:REWRITE |(expt 1/c n)|))
 (8 8 (:REWRITE |(expt (- x) n)|))
 (6 6 (:REWRITE DEFAULT-CDR))
 (6 3 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (4 4 (:REWRITE FOLD-CONSTS-IN-+))
 (4 4 (:REWRITE |(+ c (+ d x))|))
 (3 3 (:REWRITE DEFAULT-CAR))
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
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (1 1 (:REWRITE |(equal (+ (- c) x) y)|))
 (1 1 (:REWRITE |(* c (expt d n))|)))
(RTL::EVALH-THETA-1
 (244 30 (:REWRITE DEFAULT-PLUS-2))
 (224 30 (:REWRITE DEFAULT-PLUS-1))
 (100 100
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (100
     100
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (100 100
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (100 100
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (95 18 (:REWRITE DEFAULT-TIMES-2))
 (74 74
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (54 2
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (53 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (34 18 (:REWRITE DEFAULT-TIMES-1))
 (15 8 (:REWRITE DEFAULT-EXPT-1))
 (12 12
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (12 12 (:REWRITE NORMALIZE-ADDENDS))
 (8 8 (:REWRITE DEFAULT-EXPT-2))
 (8 8 (:REWRITE |(expt 1/c n)|))
 (8 8 (:REWRITE |(expt (- x) n)|))
 (6 6 (:REWRITE DEFAULT-CDR))
 (6 3 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (4 4 (:REWRITE FOLD-CONSTS-IN-+))
 (4 4 (:REWRITE |(+ c (+ d x))|))
 (3 3 (:REWRITE DEFAULT-CAR))
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
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (1 1 (:REWRITE |(equal (+ (- c) x) y)|))
 (1 1 (:REWRITE |(* c (expt d n))|)))
(RTL::EVALH-THETA-2
 (244 30 (:REWRITE DEFAULT-PLUS-2))
 (224 30 (:REWRITE DEFAULT-PLUS-1))
 (100 100
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (100
     100
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (100 100
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (100 100
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (95 18 (:REWRITE DEFAULT-TIMES-2))
 (74 74
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (54 2
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (53 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (34 18 (:REWRITE DEFAULT-TIMES-1))
 (15 8 (:REWRITE DEFAULT-EXPT-1))
 (12 12
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (12 12 (:REWRITE NORMALIZE-ADDENDS))
 (8 8 (:REWRITE DEFAULT-EXPT-2))
 (8 8 (:REWRITE |(expt 1/c n)|))
 (8 8 (:REWRITE |(expt (- x) n)|))
 (6 6 (:REWRITE DEFAULT-CDR))
 (6 3 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (4 4 (:REWRITE FOLD-CONSTS-IN-+))
 (4 4 (:REWRITE |(+ c (+ d x))|))
 (3 3 (:REWRITE DEFAULT-CAR))
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
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (1 1 (:REWRITE |(equal (+ (- c) x) y)|))
 (1 1 (:REWRITE |(* c (expt d n))|)))
(RTL::ECP-MOD
 (42410 21205
        (:TYPE-PRESCRIPTION RTL::INT-CAR-TRIPP))
 (42319 3 (:REWRITE MOD-X-Y-=-X-Y . 1))
 (39509 15 (:LINEAR MOD-BOUNDS-1))
 (38605 537 (:REWRITE DEFAULT-PLUS-2))
 (24406 537 (:REWRITE DEFAULT-PLUS-1))
 (22095 162
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (21648 21205
        (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-X))
 (21483 21483 (:TYPE-PRESCRIPTION RTL::TRIPP))
 (16341 7 (:LINEAR RTL::MOD-BND-2))
 (16163
   8515
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (15603 31 (:REWRITE RTL::MOD-DOES-NOTHING))
 (14777 31 (:REWRITE MOD-ZERO . 3))
 (13734 3 (:REWRITE MOD-X-Y-=-X+Y . 1))
 (13232 16 (:LINEAR MOD-BOUNDS-2))
 (12875 4299
        (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (12875 4299
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE))
 (12539 31 (:REWRITE MOD-X-Y-=-X . 3))
 (12339 8515
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (12339
  8515
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (12339 8515
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (12339
      8515
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (12339
     8515
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (12154 894
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3D))
 (12154 894
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2D))
 (12154 894
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1D))
 (12112 31 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (11602 171 (:REWRITE RATIONALP-X))
 (11598 31 (:REWRITE MOD-X-Y-=-X . 4))
 (11009 31 (:REWRITE MOD-ZERO . 4))
 (8515 8515
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (8515 8515
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (7740 8 (:LINEAR MOD-BOUNDS-3))
 (6993 31 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (6289 161 (:REWRITE ACL2-NUMBERP-X))
 (6155 791 (:REWRITE DEFAULT-TIMES-1))
 (6013 31 (:REWRITE MOD-X-Y-=-X . 2))
 (5251 31 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (5251 31 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (5068 528 (:REWRITE DEFAULT-LESS-THAN-1))
 (4793 31
       (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (4709 31
       (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (4709 31
       (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (4277 552 (:REWRITE DEFAULT-LESS-THAN-2))
 (3777 512
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (3137 335 (:META META-INTEGERP-CORRECT))
 (2163 2163
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (2163 2163
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (2163 2163
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (2103 512 (:REWRITE SIMPLIFY-SUMS-<))
 (1806 170 (:LINEAR EXPT->=-1-TWO))
 (1806 170 (:LINEAR EXPT->-1-TWO))
 (1806 170 (:LINEAR EXPT-<-1-ONE))
 (1712 170 (:LINEAR EXPT-<=-1-ONE))
 (1696 170 (:LINEAR EXPT-X->=-X))
 (1696 170 (:LINEAR EXPT->=-1-ONE))
 (1696 170 (:LINEAR EXPT-<=-1-TWO))
 (1654 170 (:LINEAR EXPT-X->-X))
 (1654 170 (:LINEAR EXPT->-1-ONE))
 (1654 170 (:LINEAR EXPT-<-1-TWO))
 (1636 157 (:REWRITE RTL::INTEGERP-EC-X))
 (1415 1
       (:REWRITE |(equal (mod a n) (mod b n))|))
 (1312 26
       (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 1))
 (1294 121 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (1294 121 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (1110 121
       (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (1110 121
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (1043 336 (:REWRITE INTEGERP-MINUS-X))
 (943 33 (:REWRITE DEFAULT-MOD-1))
 (911 911
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (911 911
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (911 911
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (810 121 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (810 121
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (810 121
      (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (810 121
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (810 121 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (781 46 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
 (735 46
      (:TYPE-PRESCRIPTION RTL::RATIONALP-MOD))
 (735 46 (:TYPE-PRESCRIPTION RATIONALP-MOD))
 (735 46 (:TYPE-PRESCRIPTION RTL::NATP-MOD-2))
 (735 46
      (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
 (614 26
      (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 3))
 (614 26
      (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 2))
 (604 500
      (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-Y))
 (586 586
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (552 552 (:REWRITE THE-FLOOR-BELOW))
 (552 552 (:REWRITE THE-FLOOR-ABOVE))
 (535 31
      (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (535 31
      (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (535 31
      (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (513 512
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (513 512
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (512 512
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (512 512 (:REWRITE INTEGERP-<-CONSTANT))
 (512 512 (:REWRITE CONSTANT-<-INTEGERP))
 (512 512
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (512 512
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (512 512
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (512 512
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (512 512 (:REWRITE |(< c (- x))|))
 (512 512
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (512 512
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (512 512
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (512 512
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (512 512 (:REWRITE |(< (/ x) (/ y))|))
 (512 512 (:REWRITE |(< (- x) c)|))
 (512 512 (:REWRITE |(< (- x) (- y))|))
 (495 5 (:REWRITE |(- (+ x y))|))
 (435 157 (:REWRITE RTL::INT-CAR-TRIPP))
 (363 161 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (340 340
      (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (340 340
      (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (340 340
      (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (340 340
      (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (335 335 (:REWRITE REDUCE-INTEGERP-+))
 (326 287 (:REWRITE NORMALIZE-ADDENDS))
 (295 13 (:REWRITE DEFAULT-MINUS))
 (286 286
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (222 222 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (171 171 (:REWRITE REDUCE-RATIONALP-+))
 (171 171 (:REWRITE REDUCE-RATIONALP-*))
 (171 171 (:REWRITE RATIONALP-MINUS-X))
 (171 171 (:META META-RATIONALP-CORRECT))
 (170 170 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (170 170 (:LINEAR EXPT-LINEAR-UPPER-<))
 (170 170 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (170 170 (:LINEAR EXPT-LINEAR-LOWER-<))
 (167 166
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (166 166
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (166 166 (:REWRITE |(equal c (/ x))|))
 (166 166 (:REWRITE |(equal c (- x))|))
 (166 166 (:REWRITE |(equal (/ x) c)|))
 (166 166 (:REWRITE |(equal (/ x) (/ y))|))
 (166 166 (:REWRITE |(equal (- x) c)|))
 (166 166 (:REWRITE |(equal (- x) (- y))|))
 (162 162
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (150 108 (:REWRITE DEFAULT-DIVIDE))
 (145 145
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (145 145
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (145 145 (:REWRITE |(< 0 (/ x))|))
 (145 145 (:REWRITE |(< 0 (* x y))|))
 (124 4 (:REWRITE |(equal (expt x n) 0)|))
 (108 108
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (101 101 (:REWRITE |(+ c (+ d x))|))
 (100 100 (:REWRITE FOLD-CONSTS-IN-+))
 (99 99 (:REWRITE |(* c (* d x))|))
 (90 2 (:REWRITE |(* (* x y) z)|))
 (82 82 (:REWRITE |(< (+ c/d x) y)|))
 (82 82 (:REWRITE |(< (+ (- c) x) y)|))
 (53 3
     (:REWRITE |(equal (mod (+ x y) z) x)|))
 (46 46 (:TYPE-PRESCRIPTION NATP))
 (46 1 (:REWRITE |(integerp (- x))|))
 (42 5 (:REWRITE |(- (* c x))|))
 (37 37
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (37 33 (:REWRITE DEFAULT-MOD-2))
 (32 32
     (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (31 31 (:REWRITE INTEGERP-/))
 (31 31 (:REWRITE |(mod x (- y))| . 3))
 (31 31 (:REWRITE |(mod x (- y))| . 2))
 (31 31 (:REWRITE |(mod x (- y))| . 1))
 (29 29 (:REWRITE |(equal (+ (- c) x) y)|))
 (26 26 (:REWRITE |(< y (+ (- c) x))|))
 (26 26 (:REWRITE |(< x (+ c/d y))|))
 (25 1 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
 (20 2 (:REWRITE |(- (- x))|))
 (12 12
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (12 12
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (12 12 (:REWRITE |(< (/ x) 0)|))
 (12 12 (:REWRITE |(< (* x y) 0)|))
 (7 7 (:REWRITE DEFAULT-CAR))
 (7 7 (:LINEAR RTL::MOD-BND-3))
 (6 6 (:REWRITE DEFAULT-EXPT-2))
 (6 6 (:REWRITE DEFAULT-EXPT-1))
 (6 6 (:REWRITE |(expt 1/c n)|))
 (6 6 (:REWRITE |(expt (- x) n)|))
 (4 1 (:REWRITE RTL::INTEGERP-EC-Y))
 (3 3 (:TYPE-PRESCRIPTION ABS))
 (3 3 (:REWRITE DEFAULT-CDR))
 (2 2 (:DEFINITION FIX))
 (1 1 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (1 1 (:REWRITE |(equal (* x y) 0)|))
 (1 1
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (1 1 (:REWRITE |(+ x (- x))|))
 (1 1 (:REWRITE |(* (- x) y)|)))
(RTL::THETA-0-MOD
 (28418 4 (:REWRITE MOD-X-Y-=-X-Y . 1))
 (21001 15 (:LINEAR MOD-BOUNDS-1))
 (15474 48
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (11373 4 (:REWRITE MOD-X-Y-=-X+Y . 1))
 (6154 435 (:REWRITE DEFAULT-TIMES-2))
 (5469 28 (:REWRITE RTL::MOD-DOES-NOTHING))
 (5429 7 (:LINEAR RTL::MOD-BND-2))
 (4642 28 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (4158 28 (:REWRITE MOD-ZERO . 3))
 (4000 435 (:REWRITE DEFAULT-TIMES-1))
 (3214 8 (:LINEAR MOD-BOUNDS-3))
 (3150 134 (:REWRITE DEFAULT-PLUS-2))
 (2824 28 (:REWRITE MOD-X-Y-=-X . 3))
 (2669
      2669
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (2669
     2669
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (2669 2669
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (2669 2669
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (2495 2495
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (2347 183
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4D))
 (2233 28 (:REWRITE MOD-X-Y-=-X . 4))
 (2223 28 (:REWRITE MOD-ZERO . 4))
 (1847 188 (:META META-INTEGERP-CORRECT))
 (1820 291
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (1636 295 (:REWRITE DEFAULT-LESS-THAN-1))
 (1619 1
       (:REWRITE |(equal (mod a n) (mod b n))|))
 (1569 28 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (1333 134 (:REWRITE DEFAULT-PLUS-1))
 (1238 291 (:REWRITE SIMPLIFY-SUMS-<))
 (1232 16 (:LINEAR MOD-BOUNDS-2))
 (1208 1208
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (1208 1208
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (1208 1208
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (1198 238 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (1198 238 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (1018 238
       (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (1018 238
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (999 189 (:REWRITE INTEGERP-MINUS-X))
 (989 84 (:LINEAR EXPT-<=-1-ONE))
 (972 36 (:REWRITE REDUCE-RATIONALP-*))
 (930 31 (:REWRITE DEFAULT-MOD-1))
 (894 84 (:LINEAR EXPT-X->=-X))
 (888 84 (:LINEAR EXPT->=-1-TWO))
 (863 84 (:LINEAR EXPT->-1-TWO))
 (863 84 (:LINEAR EXPT-<-1-ONE))
 (861 28 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (861 28 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (849 84 (:LINEAR EXPT->=-1-ONE))
 (799 84 (:LINEAR EXPT-X->-X))
 (799 84 (:LINEAR EXPT->-1-ONE))
 (799 84 (:LINEAR EXPT-<-1-TWO))
 (797 84 (:LINEAR EXPT-<=-1-TWO))
 (695 295 (:REWRITE DEFAULT-LESS-THAN-2))
 (634 634
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (634 634
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (634 634
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (623 28 (:REWRITE MOD-X-Y-=-X . 2))
 (616 28
      (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (616 28
      (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (616 28
      (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (601 46 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (559 5 (:REWRITE |(- (+ x y))|))
 (477 28
      (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (477 28
      (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (477 28
      (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (443 23
      (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 3))
 (414 414 (:REWRITE DEFAULT-CDR))
 (411 411 (:REWRITE DEFAULT-CAR))
 (340 14 (:REWRITE DEFAULT-MINUS))
 (316 8 (:DEFINITION RFIX))
 (295 295 (:REWRITE THE-FLOOR-BELOW))
 (295 295 (:REWRITE THE-FLOOR-ABOVE))
 (292 291
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (292 291
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (291 291
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (291 291 (:REWRITE INTEGERP-<-CONSTANT))
 (291 291 (:REWRITE CONSTANT-<-INTEGERP))
 (291 291
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (291 291
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (291 291
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (291 291
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (291 291 (:REWRITE |(< c (- x))|))
 (291 291
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (291 291
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (291 291
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (291 291
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (291 291 (:REWRITE |(< (/ x) (/ y))|))
 (291 291 (:REWRITE |(< (- x) c)|))
 (291 291 (:REWRITE |(< (- x) (- y))|))
 (267 1 (:REWRITE |(* (if a b c) x)|))
 (246 238
      (:TYPE-PRESCRIPTION RTL::NATP-MOD-2))
 (246 238 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (246 238
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (246 238
      (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (246 238
      (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
 (246 238
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (246 238 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (196 106 (:REWRITE NORMALIZE-ADDENDS))
 (188 188 (:REWRITE REDUCE-INTEGERP-+))
 (183 183
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3D))
 (183 183
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2D))
 (183 183
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1D))
 (168 168
      (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (168 168
      (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (168 168
      (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (168 168
      (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (160 80 (:REWRITE DEFAULT-DIVIDE))
 (158 23
      (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 1))
 (135 3 (:REWRITE |(* (* x y) z)|))
 (130 130 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (104 104
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (86 86
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (86 86
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (86 86 (:REWRITE |(< 0 (/ x))|))
 (86 86 (:REWRITE |(< 0 (* x y))|))
 (84 84 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (84 84 (:LINEAR EXPT-LINEAR-UPPER-<))
 (84 84 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (84 84 (:LINEAR EXPT-LINEAR-LOWER-<))
 (80 80
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (78 2 (:REWRITE |(equal (expt x n) 0)|))
 (76 4
     (:REWRITE |(equal (mod (+ x y) z) x)|))
 (62 31 (:REWRITE DEFAULT-MOD-2))
 (58 50 (:REWRITE |(equal (/ x) c)|))
 (58 50 (:REWRITE |(equal (/ x) (/ y))|))
 (54 2 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
 (53 45
     (:TYPE-PRESCRIPTION RTL::RATIONALP-MOD))
 (53 45
     (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
 (52 50 (:REWRITE |(equal (- x) (- y))|))
 (52 1 (:REWRITE |(integerp (- x))|))
 (51 50
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (50 50
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (50 50 (:REWRITE |(equal c (/ x))|))
 (50 50 (:REWRITE |(equal c (- x))|))
 (50 50 (:REWRITE |(equal (- x) c)|))
 (50 50 (:REWRITE |(+ c (+ d x))|))
 (48 48 (:REWRITE FOLD-CONSTS-IN-+))
 (48 48
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (46 5 (:REWRITE |(- (* c x))|))
 (45 45 (:TYPE-PRESCRIPTION NATP))
 (44 44 (:REWRITE |(* c (* d x))|))
 (40 40
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (36 36 (:REWRITE REDUCE-RATIONALP-+))
 (36 36 (:REWRITE RATIONALP-MINUS-X))
 (36 36 (:META META-RATIONALP-CORRECT))
 (29 29 (:REWRITE |(< (+ c/d x) y)|))
 (29 29 (:REWRITE |(< (+ (- c) x) y)|))
 (28 28 (:REWRITE |(mod x (- y))| . 3))
 (28 28 (:REWRITE |(mod x (- y))| . 2))
 (28 28 (:REWRITE |(mod x (- y))| . 1))
 (27 18 (:REWRITE DEFAULT-EXPT-1))
 (24 8 (:REWRITE |(equal x (/ y))|))
 (24 2 (:REWRITE |(- (- x))|))
 (23 23
     (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 2))
 (18 18 (:REWRITE DEFAULT-EXPT-2))
 (18 18 (:REWRITE |(expt 1/c n)|))
 (18 18 (:REWRITE |(expt (- x) n)|))
 (16 16 (:REWRITE INTEGERP-/))
 (16 16
     (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (16 8 (:REWRITE |(not (equal x (/ y)))|))
 (15 15
     (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (15 15
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE))
 (12 12 (:REWRITE |(equal (+ (- c) x) y)|))
 (10 5 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (7 7 (:REWRITE |(< y (+ (- c) x))|))
 (7 7 (:REWRITE |(< x (+ c/d y))|))
 (7 7 (:LINEAR RTL::MOD-BND-3))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4 (:REWRITE |(< (/ x) 0)|))
 (4 4 (:REWRITE |(< (* x y) 0)|))
 (3 3 (:TYPE-PRESCRIPTION ABS))
 (2 2 (:REWRITE |(+ x (- x))|))
 (1 1 (:REWRITE |(equal (* x y) 0)|))
 (1 1
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (1 1 (:REWRITE |(* c (expt d n))|))
 (1 1 (:REWRITE |(* (- x) y)|)))
(RTL::THETA-1-MOD
 (28418 4 (:REWRITE MOD-X-Y-=-X-Y . 1))
 (20905 15 (:LINEAR MOD-BOUNDS-1))
 (15426 48
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (11373 4 (:REWRITE MOD-X-Y-=-X+Y . 1))
 (5890 435 (:REWRITE DEFAULT-TIMES-2))
 (5397 28 (:REWRITE RTL::MOD-DOES-NOTHING))
 (5381 7 (:LINEAR RTL::MOD-BND-2))
 (4642 28 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (4158 28 (:REWRITE MOD-ZERO . 3))
 (3736 435 (:REWRITE DEFAULT-TIMES-1))
 (3166 8 (:LINEAR MOD-BOUNDS-3))
 (3150 134 (:REWRITE DEFAULT-PLUS-2))
 (2824 28 (:REWRITE MOD-X-Y-=-X . 3))
 (2669
      2669
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (2669
     2669
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (2669 2669
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (2669 2669
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (2495 2495
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (2347 183
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4D))
 (2233 28 (:REWRITE MOD-X-Y-=-X . 4))
 (2223 28 (:REWRITE MOD-ZERO . 4))
 (1847 188 (:META META-INTEGERP-CORRECT))
 (1772 291
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (1619 1
       (:REWRITE |(equal (mod a n) (mod b n))|))
 (1588 295 (:REWRITE DEFAULT-LESS-THAN-1))
 (1569 28 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (1333 134 (:REWRITE DEFAULT-PLUS-1))
 (1214 291 (:REWRITE SIMPLIFY-SUMS-<))
 (1208 1208
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (1208 1208
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (1208 1208
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (1198 238 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (1198 238 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (1136 16 (:LINEAR MOD-BOUNDS-2))
 (1018 238
       (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (1018 238
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (999 189 (:REWRITE INTEGERP-MINUS-X))
 (989 84 (:LINEAR EXPT-<=-1-ONE))
 (894 84 (:LINEAR EXPT-X->=-X))
 (888 84 (:LINEAR EXPT->=-1-TWO))
 (882 31 (:REWRITE DEFAULT-MOD-1))
 (876 36 (:REWRITE REDUCE-RATIONALP-*))
 (863 84 (:LINEAR EXPT->-1-TWO))
 (863 84 (:LINEAR EXPT-<-1-ONE))
 (861 28 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (861 28 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (849 84 (:LINEAR EXPT->=-1-ONE))
 (799 84 (:LINEAR EXPT-X->-X))
 (799 84 (:LINEAR EXPT->-1-ONE))
 (799 84 (:LINEAR EXPT-<-1-TWO))
 (797 84 (:LINEAR EXPT-<=-1-TWO))
 (695 295 (:REWRITE DEFAULT-LESS-THAN-2))
 (634 634
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (634 634
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (634 634
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (623 28 (:REWRITE MOD-X-Y-=-X . 2))
 (616 28
      (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (616 28
      (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (616 28
      (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (601 46 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (559 5 (:REWRITE |(- (+ x y))|))
 (443 23
      (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 3))
 (429 28
      (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (429 28
      (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (429 28
      (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (346 346 (:REWRITE DEFAULT-CDR))
 (343 343 (:REWRITE DEFAULT-CAR))
 (340 14 (:REWRITE DEFAULT-MINUS))
 (295 295 (:REWRITE THE-FLOOR-BELOW))
 (295 295 (:REWRITE THE-FLOOR-ABOVE))
 (292 291
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (292 291
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (291 291
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (291 291 (:REWRITE INTEGERP-<-CONSTANT))
 (291 291 (:REWRITE CONSTANT-<-INTEGERP))
 (291 291
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (291 291
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (291 291
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (291 291
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (291 291 (:REWRITE |(< c (- x))|))
 (291 291
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (291 291
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (291 291
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (291 291
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (291 291 (:REWRITE |(< (/ x) (/ y))|))
 (291 291 (:REWRITE |(< (- x) c)|))
 (291 291 (:REWRITE |(< (- x) (- y))|))
 (268 8 (:DEFINITION RFIX))
 (267 1 (:REWRITE |(* (if a b c) x)|))
 (246 238
      (:TYPE-PRESCRIPTION RTL::NATP-MOD-2))
 (246 238 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (246 238
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (246 238
      (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (246 238
      (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
 (246 238
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (246 238 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (196 106 (:REWRITE NORMALIZE-ADDENDS))
 (188 188 (:REWRITE REDUCE-INTEGERP-+))
 (183 183
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3D))
 (183 183
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2D))
 (183 183
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1D))
 (168 168
      (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (168 168
      (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (168 168
      (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (168 168
      (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (160 80 (:REWRITE DEFAULT-DIVIDE))
 (158 23
      (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 1))
 (135 3 (:REWRITE |(* (* x y) z)|))
 (130 130 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (104 104
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (86 86
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (86 86
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (86 86 (:REWRITE |(< 0 (/ x))|))
 (86 86 (:REWRITE |(< 0 (* x y))|))
 (84 84 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (84 84 (:LINEAR EXPT-LINEAR-UPPER-<))
 (84 84 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (84 84 (:LINEAR EXPT-LINEAR-LOWER-<))
 (80 80
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (78 2 (:REWRITE |(equal (expt x n) 0)|))
 (76 4
     (:REWRITE |(equal (mod (+ x y) z) x)|))
 (62 31 (:REWRITE DEFAULT-MOD-2))
 (58 50 (:REWRITE |(equal (/ x) c)|))
 (58 50 (:REWRITE |(equal (/ x) (/ y))|))
 (54 2 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
 (53 45
     (:TYPE-PRESCRIPTION RTL::RATIONALP-MOD))
 (53 45
     (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
 (52 50 (:REWRITE |(equal (- x) (- y))|))
 (52 1 (:REWRITE |(integerp (- x))|))
 (51 50
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (50 50
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (50 50 (:REWRITE |(equal c (/ x))|))
 (50 50 (:REWRITE |(equal c (- x))|))
 (50 50 (:REWRITE |(equal (- x) c)|))
 (50 50 (:REWRITE |(+ c (+ d x))|))
 (48 48 (:REWRITE FOLD-CONSTS-IN-+))
 (48 48
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (46 5 (:REWRITE |(- (* c x))|))
 (45 45 (:TYPE-PRESCRIPTION NATP))
 (44 44 (:REWRITE |(* c (* d x))|))
 (40 40
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (36 36 (:REWRITE REDUCE-RATIONALP-+))
 (36 36 (:REWRITE RATIONALP-MINUS-X))
 (36 36 (:META META-RATIONALP-CORRECT))
 (29 29 (:REWRITE |(< (+ c/d x) y)|))
 (29 29 (:REWRITE |(< (+ (- c) x) y)|))
 (28 28 (:REWRITE |(mod x (- y))| . 3))
 (28 28 (:REWRITE |(mod x (- y))| . 2))
 (28 28 (:REWRITE |(mod x (- y))| . 1))
 (27 18 (:REWRITE DEFAULT-EXPT-1))
 (24 8 (:REWRITE |(equal x (/ y))|))
 (24 2 (:REWRITE |(- (- x))|))
 (23 23
     (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 2))
 (18 18 (:REWRITE DEFAULT-EXPT-2))
 (18 18 (:REWRITE |(expt 1/c n)|))
 (18 18 (:REWRITE |(expt (- x) n)|))
 (16 16 (:REWRITE INTEGERP-/))
 (16 16
     (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (16 8 (:REWRITE |(not (equal x (/ y)))|))
 (15 15
     (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (15 15
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE))
 (12 12 (:REWRITE |(equal (+ (- c) x) y)|))
 (10 5 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (7 7 (:REWRITE |(< y (+ (- c) x))|))
 (7 7 (:REWRITE |(< x (+ c/d y))|))
 (7 7 (:LINEAR RTL::MOD-BND-3))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4 (:REWRITE |(< (/ x) 0)|))
 (4 4 (:REWRITE |(< (* x y) 0)|))
 (3 3 (:TYPE-PRESCRIPTION ABS))
 (2 2 (:REWRITE |(+ x (- x))|))
 (1 1 (:REWRITE |(equal (* x y) 0)|))
 (1 1
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (1 1 (:REWRITE |(* c (expt d n))|))
 (1 1 (:REWRITE |(* (- x) y)|)))
(RTL::THETA-2-MOD
 (28418 4 (:REWRITE MOD-X-Y-=-X-Y . 1))
 (20809 15 (:LINEAR MOD-BOUNDS-1))
 (15378 48
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (11373 4 (:REWRITE MOD-X-Y-=-X+Y . 1))
 (5626 435 (:REWRITE DEFAULT-TIMES-2))
 (5333 7 (:LINEAR RTL::MOD-BND-2))
 (5325 28 (:REWRITE RTL::MOD-DOES-NOTHING))
 (4642 28 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (4158 28 (:REWRITE MOD-ZERO . 3))
 (3472 435 (:REWRITE DEFAULT-TIMES-1))
 (3150 134 (:REWRITE DEFAULT-PLUS-2))
 (3118 8 (:LINEAR MOD-BOUNDS-3))
 (2824 28 (:REWRITE MOD-X-Y-=-X . 3))
 (2669
      2669
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (2669
     2669
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (2669 2669
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (2669 2669
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (2495 2495
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (2347 183
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4D))
 (2233 28 (:REWRITE MOD-X-Y-=-X . 4))
 (2223 28 (:REWRITE MOD-ZERO . 4))
 (1847 188 (:META META-INTEGERP-CORRECT))
 (1724 291
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (1619 1
       (:REWRITE |(equal (mod a n) (mod b n))|))
 (1569 28 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (1540 295 (:REWRITE DEFAULT-LESS-THAN-1))
 (1333 134 (:REWRITE DEFAULT-PLUS-1))
 (1208 1208
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (1208 1208
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (1208 1208
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (1198 238 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (1198 238 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (1190 291 (:REWRITE SIMPLIFY-SUMS-<))
 (1040 16 (:LINEAR MOD-BOUNDS-2))
 (1018 238
       (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (1018 238
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (999 189 (:REWRITE INTEGERP-MINUS-X))
 (989 84 (:LINEAR EXPT-<=-1-ONE))
 (894 84 (:LINEAR EXPT-X->=-X))
 (888 84 (:LINEAR EXPT->=-1-TWO))
 (863 84 (:LINEAR EXPT->-1-TWO))
 (863 84 (:LINEAR EXPT-<-1-ONE))
 (861 28 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (861 28 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (849 84 (:LINEAR EXPT->=-1-ONE))
 (834 31 (:REWRITE DEFAULT-MOD-1))
 (799 84 (:LINEAR EXPT-X->-X))
 (799 84 (:LINEAR EXPT->-1-ONE))
 (799 84 (:LINEAR EXPT-<-1-TWO))
 (797 84 (:LINEAR EXPT-<=-1-TWO))
 (780 36 (:REWRITE REDUCE-RATIONALP-*))
 (695 295 (:REWRITE DEFAULT-LESS-THAN-2))
 (634 634
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (634 634
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (634 634
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (623 28 (:REWRITE MOD-X-Y-=-X . 2))
 (616 28
      (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (616 28
      (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (616 28
      (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (601 46 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (559 5 (:REWRITE |(- (+ x y))|))
 (443 23
      (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 3))
 (381 28
      (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (381 28
      (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (381 28
      (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (340 14 (:REWRITE DEFAULT-MINUS))
 (295 295 (:REWRITE THE-FLOOR-BELOW))
 (295 295 (:REWRITE THE-FLOOR-ABOVE))
 (292 291
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (292 291
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (291 291
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (291 291 (:REWRITE INTEGERP-<-CONSTANT))
 (291 291 (:REWRITE CONSTANT-<-INTEGERP))
 (291 291
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (291 291
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (291 291
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (291 291
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (291 291 (:REWRITE |(< c (- x))|))
 (291 291
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (291 291
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (291 291
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (291 291
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (291 291 (:REWRITE |(< (/ x) (/ y))|))
 (291 291 (:REWRITE |(< (- x) c)|))
 (291 291 (:REWRITE |(< (- x) (- y))|))
 (278 278 (:REWRITE DEFAULT-CDR))
 (275 275 (:REWRITE DEFAULT-CAR))
 (267 1 (:REWRITE |(* (if a b c) x)|))
 (246 238
      (:TYPE-PRESCRIPTION RTL::NATP-MOD-2))
 (246 238 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (246 238
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (246 238
      (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (246 238
      (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
 (246 238
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (246 238 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (220 8 (:DEFINITION RFIX))
 (196 106 (:REWRITE NORMALIZE-ADDENDS))
 (188 188 (:REWRITE REDUCE-INTEGERP-+))
 (183 183
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3D))
 (183 183
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2D))
 (183 183
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1D))
 (168 168
      (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (168 168
      (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (168 168
      (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (168 168
      (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (160 80 (:REWRITE DEFAULT-DIVIDE))
 (158 23
      (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 1))
 (135 3 (:REWRITE |(* (* x y) z)|))
 (130 130 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (104 104
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (86 86
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (86 86
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (86 86 (:REWRITE |(< 0 (/ x))|))
 (86 86 (:REWRITE |(< 0 (* x y))|))
 (84 84 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (84 84 (:LINEAR EXPT-LINEAR-UPPER-<))
 (84 84 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (84 84 (:LINEAR EXPT-LINEAR-LOWER-<))
 (80 80
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (78 2 (:REWRITE |(equal (expt x n) 0)|))
 (76 4
     (:REWRITE |(equal (mod (+ x y) z) x)|))
 (62 31 (:REWRITE DEFAULT-MOD-2))
 (58 50 (:REWRITE |(equal (/ x) c)|))
 (58 50 (:REWRITE |(equal (/ x) (/ y))|))
 (54 2 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
 (53 45
     (:TYPE-PRESCRIPTION RTL::RATIONALP-MOD))
 (53 45
     (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
 (52 50 (:REWRITE |(equal (- x) (- y))|))
 (52 1 (:REWRITE |(integerp (- x))|))
 (51 50
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (50 50
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (50 50 (:REWRITE |(equal c (/ x))|))
 (50 50 (:REWRITE |(equal c (- x))|))
 (50 50 (:REWRITE |(equal (- x) c)|))
 (50 50 (:REWRITE |(+ c (+ d x))|))
 (48 48 (:REWRITE FOLD-CONSTS-IN-+))
 (48 48
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (46 5 (:REWRITE |(- (* c x))|))
 (45 45 (:TYPE-PRESCRIPTION NATP))
 (44 44 (:REWRITE |(* c (* d x))|))
 (40 40
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (36 36 (:REWRITE REDUCE-RATIONALP-+))
 (36 36 (:REWRITE RATIONALP-MINUS-X))
 (36 36 (:META META-RATIONALP-CORRECT))
 (29 29 (:REWRITE |(< (+ c/d x) y)|))
 (29 29 (:REWRITE |(< (+ (- c) x) y)|))
 (28 28 (:REWRITE |(mod x (- y))| . 3))
 (28 28 (:REWRITE |(mod x (- y))| . 2))
 (28 28 (:REWRITE |(mod x (- y))| . 1))
 (27 18 (:REWRITE DEFAULT-EXPT-1))
 (24 8 (:REWRITE |(equal x (/ y))|))
 (24 2 (:REWRITE |(- (- x))|))
 (23 23
     (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 2))
 (18 18 (:REWRITE DEFAULT-EXPT-2))
 (18 18 (:REWRITE |(expt 1/c n)|))
 (18 18 (:REWRITE |(expt (- x) n)|))
 (16 16 (:REWRITE INTEGERP-/))
 (16 16
     (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (16 8 (:REWRITE |(not (equal x (/ y)))|))
 (15 15
     (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (15 15
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE))
 (12 12 (:REWRITE |(equal (+ (- c) x) y)|))
 (10 5 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (7 7 (:REWRITE |(< y (+ (- c) x))|))
 (7 7 (:REWRITE |(< x (+ c/d y))|))
 (7 7 (:LINEAR RTL::MOD-BND-3))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4 (:REWRITE |(< (/ x) 0)|))
 (4 4 (:REWRITE |(< (* x y) 0)|))
 (3 3 (:TYPE-PRESCRIPTION ABS))
 (2 2 (:REWRITE |(+ x (- x))|))
 (1 1 (:REWRITE |(equal (* x y) 0)|))
 (1 1
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (1 1 (:REWRITE |(* c (expt d n))|))
 (1 1 (:REWRITE |(* (- x) y)|)))
(RTL::SPLIT$
     (14678 7339
            (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-Y))
     (11600 232 (:DEFINITION INTEGER-ABS))
     (9119 9119 (:TYPE-PRESCRIPTION RTL::ECP))
     (7724 1352 (:REWRITE DEFAULT-PLUS-2))
     (6000 1352 (:REWRITE DEFAULT-PLUS-1))
     (4060 116 (:REWRITE |(+ (if a b c) x)|))
     (3782 135 (:REWRITE RATIONALP-X))
     (3364 348 (:REWRITE |(+ y x)|))
     (3364 116 (:REWRITE NUMERATOR-NEGATIVE))
     (2918 2918 (:TYPE-PRESCRIPTION RTL::TRIPP))
     (2652 1296
           (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-X))
     (2652 1296
           (:TYPE-PRESCRIPTION RTL::INT-CAR-TRIPP))
     (1546 479
           (:TYPE-PRESCRIPTION RTL::INT-CADDR-TRIPP))
     (1358 669
           (:TYPE-PRESCRIPTION RTL::INT-CADR-TRIPP))
     (1352 32
           (:LINEAR ACL2-COUNT-OF-CONSP-POSITIVE))
     (1160 116 (:DEFINITION LENGTH))
     (1069 349 (:REWRITE DEFAULT-CDR))
     (1044 1044
           (:TYPE-PRESCRIPTION NUMERATOR-ZERO))
     (1044 1044
           (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 2))
     (1044 1044
           (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 1))
     (1044 1044
           (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 2))
     (1044 1044
           (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 1))
     (1034 194 (:REWRITE DEFAULT-CAR))
     (888 888
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (888 888 (:REWRITE NORMALIZE-ADDENDS))
     (812 232 (:REWRITE DEFAULT-MINUS))
     (812 116 (:DEFINITION LEN))
     (681 2 (:REWRITE RTL::SHFP-POP-POW-ATOM))
     (667 2 (:DEFINITION RTL::SHFP))
     (641 249 (:REWRITE SIMPLIFY-SUMS-<))
     (641 249
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (408 136 (:REWRITE RTL::INTEGERP-EC-Y))
     (381 19 (:REWRITE ACL2-NUMBERP-X))
     (371 371 (:REWRITE THE-FLOOR-BELOW))
     (371 371 (:REWRITE THE-FLOOR-ABOVE))
     (365 365 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (365 365
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (365 365
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (365 365
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (365 365 (:REWRITE INTEGERP-<-CONSTANT))
     (365 365 (:REWRITE CONSTANT-<-INTEGERP))
     (365 365
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (365 365
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (365 365
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (365 365
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (365 365 (:REWRITE |(< c (- x))|))
     (365 365
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (365 365
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (365 365
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (365 365
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (365 365 (:REWRITE |(< (/ x) (/ y))|))
     (365 365 (:REWRITE |(< (- x) c)|))
     (365 365 (:REWRITE |(< (- x) (- y))|))
     (364 7
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (353 353 (:REWRITE |(< (/ x) 0)|))
     (353 353 (:REWRITE |(< (* x y) 0)|))
     (318 106 (:REWRITE RTL::INTEGERP-EC-X))
     (318 106 (:REWRITE RTL::INT-CAR-TRIPP))
     (256 256 (:REWRITE REDUCE-INTEGERP-+))
     (256 256 (:REWRITE INTEGERP-MINUS-X))
     (256 256 (:META META-INTEGERP-CORRECT))
     (252 252 (:REWRITE FOLD-CONSTS-IN-+))
     (252 252 (:REWRITE |(+ c (+ d x))|))
     (237 237
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (237 237
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (225 75 (:REWRITE RTL::INT-CADR-TRIPP))
     (201 3 (:DEFINITION NATP))
     (168 56 (:REWRITE RTL::INT-CADDR-TRIPP))
     (135 135 (:REWRITE REDUCE-RATIONALP-+))
     (135 135 (:REWRITE REDUCE-RATIONALP-*))
     (135 135 (:REWRITE RATIONALP-MINUS-X))
     (135 135 (:META META-RATIONALP-CORRECT))
     (116 116 (:TYPE-PRESCRIPTION LEN))
     (116 116 (:REWRITE INTEGERP==>NUMERATOR-=-X))
     (116 116
          (:REWRITE INTEGERP==>DENOMINATOR-=-1))
     (116 116 (:REWRITE DEFAULT-REALPART))
     (116 116
          (:REWRITE DEFAULT-RATIONAL-NUMERATOR))
     (116 116
          (:REWRITE DEFAULT-RATIONAL-DENOMINATOR))
     (116 116 (:REWRITE DEFAULT-IMAGPART))
     (116 116 (:REWRITE DEFAULT-COERCE-2))
     (116 116 (:REWRITE DEFAULT-COERCE-1))
     (82 7 (:REWRITE RTL::SHNFP-SHFP))
     (47 7 (:REWRITE RTL::SHNFP-INT))
     (21 21 (:TYPE-PRESCRIPTION RTL::SHNFP))
     (21 21 (:TYPE-PRESCRIPTION RTL::SHFP))
     (10 5 (:REWRITE RTL::SHNFP-POW-P))
     (7 7 (:REWRITE SIMPLIFY-SUMS-EQUAL))
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
     (6 6 (:TYPE-PRESCRIPTION RTL::NORM-POP))
     (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (4 4 (:REWRITE |(< y (+ (- c) x))|))
     (4 4 (:REWRITE |(< x (+ c/d y))|))
     (4 2 (:REWRITE RTL::SHNFP-POW-Q))
     (2 2 (:TYPE-PRESCRIPTION RTL::NORM-POW))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (2 2 (:REWRITE RTL::DISTINCT-SYMBOLS-ATOM))
     (2 2 (:REWRITE |(< 0 (/ x))|))
     (2 2 (:REWRITE |(< 0 (* x y))|)))
(RTL::SPLIT$-CASE-5-1
     (1570 1003
           (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-Y))
     (815 815 (:TYPE-PRESCRIPTION RTL::ECP))
     (631 391
          (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-X))
     (631 391
          (:TYPE-PRESCRIPTION RTL::INT-CAR-TRIPP))
     (472 472 (:TYPE-PRESCRIPTION RTL::TRIPP))
     (398 242
          (:TYPE-PRESCRIPTION RTL::INT-CADR-TRIPP))
     (248 94
          (:TYPE-PRESCRIPTION RTL::INT-CADDR-TRIPP))
     (177 3
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (132 3 (:REWRITE ACL2-NUMBERP-X))
     (75 3 (:REWRITE RATIONALP-X))
     (34 34 (:REWRITE DEFAULT-CDR))
     (20 4 (:REWRITE RTL::SHNFP-INT))
     (12 4 (:REWRITE RTL::INTEGERP-EC-X))
     (12 4 (:REWRITE RTL::INT-CAR-TRIPP))
     (10 10 (:REWRITE DEFAULT-CAR))
     (6 6 (:REWRITE REDUCE-INTEGERP-+))
     (6 6 (:REWRITE INTEGERP-MINUS-X))
     (6 6 (:META META-INTEGERP-CORRECT))
     (6 2 (:REWRITE RTL::INT-CADR-TRIPP))
     (4 4 (:REWRITE THE-FLOOR-BELOW))
     (4 4 (:REWRITE THE-FLOOR-ABOVE))
     (4 4 (:REWRITE SIMPLIFY-SUMS-<))
     (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (4 4 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (4 4
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (4 4
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
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
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (3 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (3 3 (:REWRITE REDUCE-RATIONALP-+))
     (3 3 (:REWRITE REDUCE-RATIONALP-*))
     (3 3
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (3 3
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (3 3 (:REWRITE RATIONALP-MINUS-X))
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
     (3 3 (:META META-RATIONALP-CORRECT))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (1 1 (:REWRITE |(< 0 (/ x))|))
     (1 1 (:REWRITE |(< 0 (* x y))|)))
(RTL::SPLIT$-CASE-5-2 (1146 791
                            (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-Y))
                      (460 460 (:TYPE-PRESCRIPTION RTL::ECP))
                      (361 256
                           (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-X))
                      (361 256
                           (:TYPE-PRESCRIPTION RTL::INT-CAR-TRIPP))
                      (252 169
                           (:TYPE-PRESCRIPTION RTL::INT-CADR-TRIPP))
                      (248 248 (:TYPE-PRESCRIPTION RTL::TRIPP))
                      (240 90
                           (:TYPE-PRESCRIPTION RTL::INT-CADDR-TRIPP))
                      (2 2 (:REWRITE DEFAULT-CDR))
                      (2 1
                         (:TYPE-PRESCRIPTION RTL::SPLIT$-CASE-5-2))
                      (1 1 (:REWRITE DEFAULT-CAR)))
(RTL::SPLIT$-CASE-5-3
     (3151 1891
           (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-Y))
     (1698 1698 (:TYPE-PRESCRIPTION RTL::ECP))
     (1028 610
           (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-X))
     (1028 610
           (:TYPE-PRESCRIPTION RTL::INT-CAR-TRIPP))
     (1012 1012 (:TYPE-PRESCRIPTION RTL::TRIPP))
     (686 396
          (:TYPE-PRESCRIPTION RTL::INT-CADR-TRIPP))
     (554 7
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (552 296
          (:TYPE-PRESCRIPTION RTL::INT-CADDR-TRIPP))
     (398 6 (:REWRITE ACL2-NUMBERP-X))
     (220 6 (:REWRITE RATIONALP-X))
     (195 15 (:REWRITE RTL::SHNFP-INT))
     (64 40 (:REWRITE DEFAULT-CDR))
     (59 17 (:REWRITE DEFAULT-CAR))
     (30 10 (:REWRITE RTL::INTEGERP-EC-X))
     (30 10 (:REWRITE RTL::INT-CAR-TRIPP))
     (18 6 (:REWRITE RTL::INT-CADR-TRIPP))
     (18 6 (:REWRITE RTL::INT-CADDR-TRIPP))
     (13 13 (:REWRITE REDUCE-INTEGERP-+))
     (13 13 (:REWRITE INTEGERP-MINUS-X))
     (13 13 (:META META-INTEGERP-CORRECT))
     (7 7 (:REWRITE SIMPLIFY-SUMS-EQUAL))
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
     (6 6 (:REWRITE REDUCE-RATIONALP-+))
     (6 6 (:REWRITE REDUCE-RATIONALP-*))
     (6 6 (:REWRITE RATIONALP-MINUS-X))
     (6 6 (:META META-RATIONALP-CORRECT))
     (6 2 (:REWRITE RTL::CADDR-0-TRIPP-2))
     (3 3 (:REWRITE THE-FLOOR-BELOW))
     (3 3 (:REWRITE THE-FLOOR-ABOVE))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (3 3 (:REWRITE SIMPLIFY-SUMS-<))
     (3 3 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (3 3 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (3 3
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (3 3
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
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
     (3 3 (:REWRITE |(< (* x y) 0)|)))
(RTL::NTHCDR-CDR
     (1472 632
           (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-Y))
     (633 633 (:TYPE-PRESCRIPTION RTL::ECP))
     (290 6 (:REWRITE RTL::CONSP-NTHCDR))
     (268 5
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (186 6 (:REWRITE ACL2-NUMBERP-X))
     (128 4 (:DEFINITION NATP))
     (90 3 (:REWRITE RATIONALP-X))
     (88 5 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (68 4 (:DEFINITION LEN))
     (40 8 (:REWRITE |(+ y x)|))
     (28 22 (:REWRITE DEFAULT-PLUS-2))
     (22 22 (:REWRITE DEFAULT-PLUS-1))
     (14 14
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (14 14 (:REWRITE NORMALIZE-ADDENDS))
     (12 6 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (12 6 (:REWRITE DEFAULT-LESS-THAN-2))
     (10 10 (:REWRITE ZP-OPEN))
     (7 7 (:REWRITE REDUCE-INTEGERP-+))
     (7 7 (:REWRITE INTEGERP-MINUS-X))
     (7 7 (:META META-INTEGERP-CORRECT))
     (6 6 (:REWRITE THE-FLOOR-BELOW))
     (6 6 (:REWRITE THE-FLOOR-ABOVE))
     (6 6 (:REWRITE SIMPLIFY-SUMS-<))
     (6 6 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (6 6
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (6 6
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (6 6 (:REWRITE INTEGERP-<-CONSTANT))
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
     (4 4 (:TYPE-PRESCRIPTION NATP))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (4 4 (:REWRITE |(< (/ x) 0)|))
     (4 4 (:REWRITE |(< (* x y) 0)|))
     (3 3 (:REWRITE REDUCE-RATIONALP-+))
     (3 3 (:REWRITE REDUCE-RATIONALP-*))
     (3 3 (:REWRITE RATIONALP-MINUS-X))
     (3 3 (:META META-RATIONALP-CORRECT))
     (2 2 (:REWRITE |(< x (if a b c))|))
     (2 2 (:REWRITE |(< (+ c/d x) y)|))
     (2 2 (:REWRITE |(< (+ (- c) x) y)|))
     (2 1
        (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-X))
     (2 1
        (:TYPE-PRESCRIPTION RTL::INT-CAR-TRIPP))
     (1 1 (:TYPE-PRESCRIPTION RTL::TRIPP)))
(RTL::CDR-NTHCDR
     (84 21
         (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-Y))
     (50 7 (:REWRITE DEFAULT-CDR))
     (38 1 (:REWRITE RTL::CONSP-NTHCDR))
     (21 21 (:TYPE-PRESCRIPTION RTL::ECP))
     (12 11 (:REWRITE DEFAULT-PLUS-2))
     (11 11 (:REWRITE DEFAULT-PLUS-1))
     (7 1 (:DEFINITION LEN))
     (5 5
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (5 5 (:REWRITE NORMALIZE-ADDENDS))
     (3 2 (:REWRITE SIMPLIFY-SUMS-<))
     (3 2 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (3 2 (:REWRITE DEFAULT-LESS-THAN-2))
     (2 2 (:REWRITE ZP-OPEN))
     (2 2 (:REWRITE THE-FLOOR-BELOW))
     (2 2 (:REWRITE THE-FLOOR-ABOVE))
     (2 2 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (2 2
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (2 2
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (2 2 (:REWRITE INTEGERP-<-CONSTANT))
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
     (1 1 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (1 1 (:REWRITE REDUCE-INTEGERP-+))
     (1 1 (:REWRITE INTEGERP-MINUS-X))
     (1 1 (:REWRITE |(< (/ x) 0)|))
     (1 1 (:REWRITE |(< (* x y) 0)|))
     (1 1 (:META META-INTEGERP-CORRECT)))
(RTL::CAR0 (10 5
               (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-X))
           (10 5
               (:TYPE-PRESCRIPTION RTL::INT-CAR-TRIPP))
           (5 5 (:TYPE-PRESCRIPTION RTL::TRIPP))
           (5 5 (:TYPE-PRESCRIPTION RTL::ECP)))
(RTL::EVALH-POW-REWRITE
 (412529 1127 (:REWRITE ACL2-NUMBERP-X))
 (399824 1103 (:REWRITE RATIONALP-X))
 (385963 710 (:REWRITE RTL::INTEGERP-EVALH))
 (382425 724 (:DEFINITION RTL::SHFP))
 (170250 1456 (:DEFINITION NATP))
 (148726 74363
         (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-Y))
 (107403 107403 (:TYPE-PRESCRIPTION RTL::ECP))
 (63518 18870
        (:TYPE-PRESCRIPTION RTL::SPLIT$-CASE-5-2))
 (62145 62145 (:TYPE-PRESCRIPTION RTL::TRIPP))
 (58324 29162
        (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-X))
 (58324 29162
        (:TYPE-PRESCRIPTION RTL::INT-CAR-TRIPP))
 (37740 18870
        (:TYPE-PRESCRIPTION RTL::INT-CADR-TRIPP))
 (28477 1870
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (24141 24141 (:TYPE-PRESCRIPTION RTL::SHNFP))
 (24098 5522 (:REWRITE DEFAULT-CAR))
 (12694 6347
        (:TYPE-PRESCRIPTION RTL::INT-CADDR-TRIPP))
 (11472 1673 (:REWRITE DEFAULT-PLUS-1))
 (9724 107 (:DEFINITION NTHCDR))
 (8890 25 (:REWRITE RTL::NTHCDR-CDR))
 (8598 8598 (:TYPE-PRESCRIPTION RTL::SHFP))
 (7351 977 (:REWRITE DEFAULT-TIMES-1))
 (6816 2988 (:REWRITE RTL::INTEGERP-EC-X))
 (6816 2988 (:REWRITE RTL::INT-CAR-TRIPP))
 (6634 107 (:REWRITE ZP-OPEN))
 (5913 2687 (:REWRITE RTL::INT-CADR-TRIPP))
 (5748 2874 (:REWRITE RTL::SHNFP-SHFP))
 (5665 25 (:REWRITE RTL::CONSP-NTHCDR))
 (5202 1456 (:REWRITE RTL::SPLIT$-CASE-5-2))
 (4012 712
       (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (4012 712
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE))
 (3803 3803 (:REWRITE REDUCE-INTEGERP-+))
 (3803 3803 (:REWRITE INTEGERP-MINUS-X))
 (3803 3803 (:META META-INTEGERP-CORRECT))
 (2040 50 (:REWRITE RTL::SPLIT$-CASE-5-3))
 (2034 1870 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (1870 1870
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (1870 1870
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (1870 1870
       (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (1870 1870 (:REWRITE |(equal c (/ x))|))
 (1870 1870 (:REWRITE |(equal c (- x))|))
 (1870 1870 (:REWRITE |(equal (/ x) c)|))
 (1870 1870 (:REWRITE |(equal (/ x) (/ y))|))
 (1870 1870 (:REWRITE |(equal (- x) c)|))
 (1870 1870 (:REWRITE |(equal (- x) (- y))|))
 (1570 1570 (:REWRITE THE-FLOOR-BELOW))
 (1570 1570 (:REWRITE THE-FLOOR-ABOVE))
 (1570 1570 (:REWRITE SIMPLIFY-SUMS-<))
 (1570 1570
       (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (1570 1570
       (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (1570 1570
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (1570 1570
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (1570 1570
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (1570 1570 (:REWRITE INTEGERP-<-CONSTANT))
 (1570 1570 (:REWRITE DEFAULT-LESS-THAN-2))
 (1570 1570 (:REWRITE DEFAULT-LESS-THAN-1))
 (1570 1570 (:REWRITE CONSTANT-<-INTEGERP))
 (1570 1570
       (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (1570 1570
       (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (1570 1570
       (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (1570 1570
       (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (1570 1570 (:REWRITE |(< c (- x))|))
 (1570 1570
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (1570 1570
       (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (1570 1570
       (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (1570 1570
       (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (1570 1570 (:REWRITE |(< (/ x) (/ y))|))
 (1570 1570 (:REWRITE |(< (- x) c)|))
 (1570 1570 (:REWRITE |(< (- x) (- y))|))
 (1463 1463
       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1463 1463
       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1463 1463 (:REWRITE |(< (/ x) 0)|))
 (1463 1463 (:REWRITE |(< (* x y) 0)|))
 (1424 712 (:REWRITE RTL::INT-CADDR-TRIPP))
 (1258
   752
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (1103 1103 (:REWRITE REDUCE-RATIONALP-+))
 (1103 1103 (:REWRITE REDUCE-RATIONALP-*))
 (1103 1103 (:REWRITE RATIONALP-MINUS-X))
 (1103 1103 (:META META-RATIONALP-CORRECT))
 (1042 752
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1042 752
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (1042 752
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (952
  752
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (900 75
      (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
 (849 483 (:REWRITE RTL::SHNFP-INT))
 (768 752
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (768 752
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (768 752
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (768
     752
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (502 502
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (502 502 (:REWRITE NORMALIZE-ADDENDS))
 (179 179
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (174 174 (:REWRITE |(expt 1/c n)|))
 (174 174 (:REWRITE |(expt (- x) n)|))
 (107 107
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (107 107
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (107 107 (:REWRITE |(< 0 (/ x))|))
 (107 107 (:REWRITE |(< 0 (* x y))|))
 (100 25 (:REWRITE RTL::SHNFP-POW-Q))
 (100 25 (:REWRITE RTL::SHNFP-POW-P))
 (80 80 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (80 80 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (80 80 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (80 80 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (75 75 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (75 25 (:REWRITE RTL::INTEGERP-EC-Y))
 (68 68
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (50 50 (:REWRITE RTL::P-NAT))
 (50 50 (:REWRITE RTL::NATP-Y2))
 (50 50 (:REWRITE RTL::NATP-Y1))
 (50 50 (:REWRITE RTL::NATP-Y0))
 (50 50 (:REWRITE RTL::NATP-X2))
 (50 50 (:REWRITE RTL::NATP-X1))
 (50 50 (:REWRITE RTL::NATP-X0))
 (50 50 (:REWRITE RTL::NATP-P-1/2))
 (25 25 (:TYPE-PRESCRIPTION NATP))
 (8 8 (:REWRITE |(equal (+ (- c) x) y)|))
 (1 1 (:REWRITE |(expt (if a b c) x)|)))
(RTL::SPLIT$-CASE-5-4
 (14400 45 (:REWRITE ACL2-NUMBERP-X))
 (13902 42 (:REWRITE RATIONALP-X))
 (13327 25 (:REWRITE RTL::INTEGERP-EVALH))
 (13205 31 (:DEFINITION RTL::SHFP))
 (6524 3262
       (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-Y))
 (4957 4957 (:TYPE-PRESCRIPTION RTL::ECP))
 (3964 76
       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (3142 1571
       (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-X))
 (3142 1571
       (:TYPE-PRESCRIPTION RTL::INT-CAR-TRIPP))
 (2995 2995 (:TYPE-PRESCRIPTION RTL::TRIPP))
 (2472 996
       (:TYPE-PRESCRIPTION RTL::SPLIT$-CASE-5-2))
 (2096 288 (:REWRITE DEFAULT-CAR))
 (2042 1117 (:REWRITE DEFAULT-CDR))
 (1992 996
       (:TYPE-PRESCRIPTION RTL::INT-CADR-TRIPP))
 (1496
   406
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (1176 1176 (:TYPE-PRESCRIPTION RTL::SHNFP))
 (976
  406
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (896 406
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (896 406
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (896 406
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (563 414 (:REWRITE DEFAULT-PLUS-1))
 (444 270
      (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (444 270
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE))
 (436 406
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (436 406
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (436 406
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (436
     406
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (357 357 (:TYPE-PRESCRIPTION RTL::SHFP))
 (348 174
      (:TYPE-PRESCRIPTION RTL::INT-CADDR-TRIPP))
 (260 260
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (260 260
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (260 260
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (260 260
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (260 10 (:REWRITE RTL::CONSP-NTHCDR))
 (242 121 (:REWRITE RTL::SHNFP-SHFP))
 (229 105 (:REWRITE RTL::INTEGERP-EC-X))
 (229 105 (:REWRITE RTL::INT-CAR-TRIPP))
 (199 34 (:REWRITE DEFAULT-TIMES-1))
 (196 94 (:REWRITE RTL::INT-CADR-TRIPP))
 (186 186
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (186 186 (:REWRITE NORMALIZE-ADDENDS))
 (154 14 (:DEFINITION NTH))
 (147 147 (:REWRITE REDUCE-INTEGERP-+))
 (147 147 (:REWRITE INTEGERP-MINUS-X))
 (147 147 (:META META-INTEGERP-CORRECT))
 (126 76 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (118 59 (:REWRITE RTL::SPLIT$-CASE-5-2))
 (105 105 (:REWRITE ZP-OPEN))
 (85 85 (:REWRITE THE-FLOOR-BELOW))
 (85 85 (:REWRITE THE-FLOOR-ABOVE))
 (85 85 (:REWRITE SIMPLIFY-SUMS-<))
 (85 85
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (85 85
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (85 85
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (85 85 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (85 85 (:REWRITE INTEGERP-<-CONSTANT))
 (85 85 (:REWRITE DEFAULT-LESS-THAN-2))
 (85 85 (:REWRITE DEFAULT-LESS-THAN-1))
 (85 85 (:REWRITE CONSTANT-<-INTEGERP))
 (85 85
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (85 85
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (85 85
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (85 85
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (85 85 (:REWRITE |(< c (- x))|))
 (85 85
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (85 85
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (85 85
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (85 85
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (85 85 (:REWRITE |(< (/ x) (/ y))|))
 (85 85 (:REWRITE |(< (- x) c)|))
 (85 85 (:REWRITE |(< (- x) (- y))|))
 (76 76
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (76 76
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (76 76
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (76 76 (:REWRITE |(equal c (/ x))|))
 (76 76 (:REWRITE |(equal c (- x))|))
 (76 76 (:REWRITE |(equal (/ x) c)|))
 (76 76 (:REWRITE |(equal (/ x) (/ y))|))
 (76 76 (:REWRITE |(equal (- x) c)|))
 (76 76 (:REWRITE |(equal (- x) (- y))|))
 (73 73
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (73 73
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (73 73 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (73 73 (:REWRITE |(< (/ x) 0)|))
 (73 73 (:REWRITE |(< (* x y) 0)|))
 (56 28 (:REWRITE RTL::INT-CADDR-TRIPP))
 (56 2 (:REWRITE RTL::ALL-INTEGERS-INTEGER))
 (42 42 (:REWRITE REDUCE-RATIONALP-+))
 (42 42 (:REWRITE REDUCE-RATIONALP-*))
 (42 42 (:REWRITE RATIONALP-MINUS-X))
 (42 42 (:META META-RATIONALP-CORRECT))
 (12 12 (:REWRITE RTL::LEN-VALS))
 (10 10 (:REWRITE |(expt 1/c n)|))
 (10 10 (:REWRITE |(expt (- x) n)|))
 (5 5
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (2 2 (:REWRITE RTL::ALL-INTEGERS-VALS))
 (2 2 (:REWRITE |(expt (if a b c) x)|))
 (1 1 (:REWRITE |(equal (+ (- c) x) y)|)))
(RTL::SPLIT$-CASE-5-5
     (72 36
         (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-X))
     (72 36
         (:TYPE-PRESCRIPTION RTL::INT-CAR-TRIPP))
     (52 1
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (39 1 (:REWRITE ACL2-NUMBERP-X))
     (38 38 (:TYPE-PRESCRIPTION RTL::TRIPP))
     (38 38 (:TYPE-PRESCRIPTION RTL::ECP))
     (22 1 (:REWRITE RATIONALP-X))
     (11 1 (:DEFINITION NTHCDR))
     (11 1 (:DEFINITION NTH))
     (5 1 (:REWRITE |(+ y x)|))
     (4 2 (:REWRITE DEFAULT-CDR))
     (3 3 (:REWRITE DEFAULT-PLUS-2))
     (3 3 (:REWRITE DEFAULT-PLUS-1))
     (3 2 (:REWRITE DEFAULT-CAR))
     (3 1 (:REWRITE RTL::INTEGERP-EC-X))
     (3 1 (:REWRITE RTL::INT-CAR-TRIPP))
     (2 2 (:REWRITE ZP-OPEN))
     (2 2 (:REWRITE THE-FLOOR-BELOW))
     (2 2 (:REWRITE THE-FLOOR-ABOVE))
     (2 2 (:REWRITE SIMPLIFY-SUMS-<))
     (2 2 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (2 2 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (2 2
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (2 2
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (2 2 (:REWRITE REDUCE-INTEGERP-+))
     (2 2 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (2 2
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (2 2 (:REWRITE NORMALIZE-ADDENDS))
     (2 2 (:REWRITE INTEGERP-MINUS-X))
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
     (2 2 (:META META-INTEGERP-CORRECT))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (1 1 (:REWRITE RTL::SHNFP-INT))
     (1 1 (:REWRITE REDUCE-RATIONALP-+))
     (1 1 (:REWRITE REDUCE-RATIONALP-*))
     (1 1
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (1 1
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (1 1 (:REWRITE RATIONALP-MINUS-X))
     (1 1
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (1 1 (:REWRITE |(equal c (/ x))|))
     (1 1 (:REWRITE |(equal c (- x))|))
     (1 1 (:REWRITE |(equal (/ x) c)|))
     (1 1 (:REWRITE |(equal (/ x) (/ y))|))
     (1 1 (:REWRITE |(equal (- x) c)|))
     (1 1 (:REWRITE |(equal (- x) (- y))|))
     (1 1 (:REWRITE |(< (/ x) 0)|))
     (1 1 (:REWRITE |(< (* x y) 0)|))
     (1 1 (:META META-RATIONALP-CORRECT)))
(RTL::SPLIT$-CASE-5-6
 (60 20
     (:TYPE-PRESCRIPTION RTL::ALL-INTEGERS-INTEGER))
 (56 28
     (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-X))
 (56 28
     (:TYPE-PRESCRIPTION RTL::INT-CAR-TRIPP))
 (52 52 (:TYPE-PRESCRIPTION RTL::ECP))
 (48 24
     (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-Y))
 (38 18
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (38 18
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (36 36 (:TYPE-PRESCRIPTION RTL::TRIPP))
 (24 18
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (24
  18
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (24 18
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (24 18
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (24 18
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (24 18
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (23 17
     (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (23 17
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE))
 (20 20
     (:TYPE-PRESCRIPTION RTL::ALL-INTEGERS))
 (16 8
     (:TYPE-PRESCRIPTION RTL::INT-CADR-TRIPP))
 (11 1 (:DEFINITION NTHCDR))
 (11 1 (:DEFINITION NTH))
 (5 1 (:REWRITE |(+ y x)|))
 (4 2 (:REWRITE DEFAULT-CDR))
 (3 3 (:REWRITE DEFAULT-PLUS-2))
 (3 3 (:REWRITE DEFAULT-PLUS-1))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (2 2 (:REWRITE NORMALIZE-ADDENDS))
 (2 1
    (:TYPE-PRESCRIPTION RTL::SPLIT$-CASE-5-6))
 (2 1 (:REWRITE DEFAULT-CAR))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 (1 1 (:REWRITE THE-FLOOR-BELOW))
 (1 1 (:REWRITE THE-FLOOR-ABOVE))
 (1 1 (:REWRITE SIMPLIFY-SUMS-<))
 (1 1 (:REWRITE RTL::SHNFP-INT))
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
 (1 1 (:REWRITE |(< (/ x) (/ y))|))
 (1 1 (:REWRITE |(< (- x) c)|))
 (1 1 (:REWRITE |(< (- x) (- y))|))
 (1 1 (:META META-INTEGERP-CORRECT)))
(RTL::SPLIT$-CASE-5-7
 (5792 1 (:DEFINITION RTL::EVALH))
 (4842 14 (:REWRITE ACL2-NUMBERP-X))
 (4574 14 (:REWRITE RATIONALP-X))
 (4200 8 (:DEFINITION RTL::SHFP))
 (2616 24 (:REWRITE DEFAULT-PLUS-2))
 (2191 14 (:REWRITE DEFAULT-TIMES-2))
 (1742 871
       (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-Y))
 (1281 1281 (:TYPE-PRESCRIPTION RTL::ECP))
 (940 366
      (:TYPE-PRESCRIPTION RTL::INT-CAR-TRIPP))
 (794 794 (:TYPE-PRESCRIPTION RTL::TRIPP))
 (776 233
      (:TYPE-PRESCRIPTION RTL::SPLIT$-CASE-5-2))
 (732 366
      (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-X))
 (614 22
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (603 1 (:REWRITE RTL::EVALH-POW-REWRITE))
 (466 233
      (:TYPE-PRESCRIPTION RTL::INT-CADR-TRIPP))
 (315 221 (:REWRITE DEFAULT-CDR))
 (290 61 (:REWRITE DEFAULT-CAR))
 (289 5 (:REWRITE DEFAULT-EXPT-2))
 (214 107
      (:TYPE-PRESCRIPTION RTL::INT-CADDR-TRIPP))
 (183 7 (:REWRITE |(+ (if a b c) x)|))
 (153 22 (:REWRITE DEFAULT-PLUS-1))
 (141 3 (:REWRITE DEFAULT-EXPT-1))
 (134 2 (:DEFINITION NTHCDR))
 (126 42
      (:TYPE-PRESCRIPTION RTL::ALL-INTEGERS-INTEGER))
 (124 1 (:REWRITE RTL::NTHCDR+))
 (98 12 (:REWRITE DEFAULT-TIMES-1))
 (98 5 (:REWRITE |(* (if a b c) x)|))
 (78 34 (:REWRITE RTL::INTEGERP-EC-X))
 (78 34 (:REWRITE RTL::INT-CAR-TRIPP))
 (66 30 (:REWRITE RTL::INT-CADR-TRIPP))
 (64 3 (:REWRITE ZP-OPEN))
 (56 2 (:REWRITE RTL::ALL-INTEGERS-INTEGER))
 (52 2 (:REWRITE RTL::CONSP-NTHCDR))
 (46 46 (:REWRITE REDUCE-INTEGERP-+))
 (46 46 (:REWRITE INTEGERP-MINUS-X))
 (46 46 (:META META-INTEGERP-CORRECT))
 (36 9
     (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (36 9
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE))
 (35 17 (:REWRITE RTL::SPLIT$-CASE-5-2))
 (35 3 (:REWRITE |(+ y x)|))
 (26 2 (:REWRITE ZIP-OPEN))
 (23 23 (:REWRITE THE-FLOOR-BELOW))
 (23 23 (:REWRITE THE-FLOOR-ABOVE))
 (23 23 (:REWRITE SIMPLIFY-SUMS-<))
 (23 23
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (23 23
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (23 23
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (23 23 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (23 23 (:REWRITE INTEGERP-<-CONSTANT))
 (23 23 (:REWRITE DEFAULT-LESS-THAN-2))
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
 (22 22 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (22 22
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (22 22
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (22 22
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (22 22 (:REWRITE |(equal c (/ x))|))
 (22 22 (:REWRITE |(equal c (- x))|))
 (22 22 (:REWRITE |(equal (/ x) c)|))
 (22 22 (:REWRITE |(equal (/ x) (/ y))|))
 (22 22 (:REWRITE |(equal (- x) c)|))
 (22 22 (:REWRITE |(equal (- x) (- y))|))
 (19 19 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (18 18
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (18 18
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (18 18 (:REWRITE |(< (/ x) 0)|))
 (18 18 (:REWRITE |(< (* x y) 0)|))
 (16 8 (:REWRITE RTL::INT-CADDR-TRIPP))
 (14 14 (:REWRITE REDUCE-RATIONALP-+))
 (14 14 (:REWRITE REDUCE-RATIONALP-*))
 (14 14 (:REWRITE RATIONALP-MINUS-X))
 (14 14 (:META META-RATIONALP-CORRECT))
 (14 1 (:REWRITE |(expt 0 n)|))
 (12 1 (:REWRITE RTL::CAR-NTHCDR))
 (11 1 (:DEFINITION NTH))
 (9 9
    (:TYPE-PRESCRIPTION RTL::SPLIT$-CASE-5-6))
 (9 9
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (9
   9
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (9
  9
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (9 9
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (9 9
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (9 9
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (9 9
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (9 9
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (9 9
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (9 9
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (9 9 (:TYPE-PRESCRIPTION EXPT))
 (8 8
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (8 8 (:REWRITE NORMALIZE-ADDENDS))
 (4 4 (:REWRITE RTL::LEN-VALS))
 (4 4 (:REWRITE |(+ 0 x)|))
 (4 4 (:REWRITE |(* 1 x)|))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (2 2 (:REWRITE |(expt 1/c n)|))
 (2 2 (:REWRITE |(expt (- x) n)|))
 (2 2 (:REWRITE |(* 0 x)|))
 (2 1
    (:TYPE-PRESCRIPTION RTL::SPLIT$-CASE-5-7))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (1 1 (:REWRITE RTL::SHNFP-INT))
 (1 1
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (1 1 (:REWRITE |(< 0 (/ x))|))
 (1 1 (:REWRITE |(< 0 (* x y))|)))
(RTL::SPLIT$-CASE-5-8
 (6639 1 (:DEFINITION RTL::EVALH))
 (5514 30 (:REWRITE ACL2-NUMBERP-X))
 (4538 30 (:REWRITE RATIONALP-X))
 (4192 25 (:REWRITE DEFAULT-PLUS-2))
 (3438 6 (:DEFINITION RTL::SHFP))
 (2294 1147
       (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-Y))
 (1516 1516 (:TYPE-PRESCRIPTION RTL::ECP))
 (1342 23 (:REWRITE DEFAULT-PLUS-1))
 (1277 13 (:REWRITE DEFAULT-TIMES-2))
 (1022 329
       (:TYPE-PRESCRIPTION RTL::INT-CAR-TRIPP))
 (951 1 (:REWRITE RTL::EVALH-POW-REWRITE))
 (910 212
      (:TYPE-PRESCRIPTION RTL::SPLIT$-CASE-5-2))
 (810 18
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (704 704 (:TYPE-PRESCRIPTION RTL::TRIPP))
 (688 6 (:REWRITE |(+ (if a b c) x)|))
 (658 329
      (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-X))
 (452 203
      (:TYPE-PRESCRIPTION RTL::SPLIT$-CASE-5-7))
 (424 212
      (:TYPE-PRESCRIPTION RTL::INT-CADR-TRIPP))
 (378 126
      (:TYPE-PRESCRIPTION RTL::ALL-INTEGERS-INTEGER))
 (338 49 (:REWRITE DEFAULT-CAR))
 (289 5 (:REWRITE DEFAULT-EXPT-2))
 (284 172 (:REWRITE DEFAULT-CDR))
 (264 5 (:REWRITE |(* (if a b c) x)|))
 (178 89
      (:TYPE-PRESCRIPTION RTL::INT-CADDR-TRIPP))
 (144 45
      (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (144 45
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE))
 (141 3 (:REWRITE DEFAULT-EXPT-1))
 (136 1 (:REWRITE RTL::NTHCDR+))
 (134 2 (:DEFINITION NTHCDR))
 (98 12 (:REWRITE DEFAULT-TIMES-1))
 (66 28 (:REWRITE RTL::INTEGERP-EC-X))
 (66 28 (:REWRITE RTL::INT-CAR-TRIPP))
 (64 3 (:REWRITE ZP-OPEN))
 (56 2 (:REWRITE RTL::ALL-INTEGERS-INTEGER))
 (54 24 (:REWRITE RTL::INT-CADR-TRIPP))
 (52 2 (:REWRITE RTL::CONSP-NTHCDR))
 (50 4 (:REWRITE |(* 1 x)|))
 (49 12 (:REWRITE RTL::SPLIT$-CASE-5-7))
 (46 46 (:REWRITE REDUCE-INTEGERP-+))
 (46 46 (:REWRITE INTEGERP-MINUS-X))
 (46 46 (:META META-INTEGERP-CORRECT))
 (45 45
     (:TYPE-PRESCRIPTION RTL::SPLIT$-CASE-5-6))
 (45 45
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (45
   45
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (45
  45
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (45 45
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (45 45
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (45 45
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (45 45
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (45 45
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (45 45
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (45 45
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (45 45 (:TYPE-PRESCRIPTION EXPT))
 (38 3 (:REWRITE |(+ y x)|))
 (27 13 (:REWRITE RTL::SPLIT$-CASE-5-2))
 (26 2 (:REWRITE ZIP-OPEN))
 (19 19 (:REWRITE THE-FLOOR-BELOW))
 (19 19 (:REWRITE THE-FLOOR-ABOVE))
 (19 19 (:REWRITE SIMPLIFY-SUMS-<))
 (19 19
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (19 19 (:REWRITE REDUCE-RATIONALP-+))
 (19 19 (:REWRITE REDUCE-RATIONALP-*))
 (19 19
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (19 19
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (19 19 (:REWRITE RATIONALP-MINUS-X))
 (19 19 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (19 19 (:REWRITE INTEGERP-<-CONSTANT))
 (19 19 (:REWRITE DEFAULT-LESS-THAN-2))
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
 (19 19 (:META META-RATIONALP-CORRECT))
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
 (15 15 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (14 14
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (14 14
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (14 14 (:REWRITE |(< (/ x) 0)|))
 (14 14 (:REWRITE |(< (* x y) 0)|))
 (14 2 (:REWRITE RTL::SHNFP-INT))
 (14 1 (:REWRITE |(expt 0 n)|))
 (12 6 (:REWRITE RTL::INT-CADDR-TRIPP))
 (12 1 (:REWRITE RTL::CAR-NTHCDR))
 (11 1 (:DEFINITION NTH))
 (8 8 (:TYPE-PRESCRIPTION NATP))
 (8 8
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (8 8 (:REWRITE NORMALIZE-ADDENDS))
 (4 4 (:REWRITE RTL::LEN-VALS))
 (3 3 (:REWRITE |(+ 0 x)|))
 (3 1 (:REWRITE RTL::INTEGERP-EC-Y))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (2 2 (:REWRITE |(expt 1/c n)|))
 (2 2 (:REWRITE |(expt (- x) n)|))
 (2 2 (:REWRITE |(* 0 x)|))
 (2 1
    (:TYPE-PRESCRIPTION RTL::SPLIT$-CASE-5-8))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (1 1
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (1 1 (:REWRITE |(< 0 (/ x))|))
 (1 1 (:REWRITE |(< 0 (* x y))|)))
(RTL::SPLIT$-CASE-9
 (3652 1 (:DEFINITION RTL::EVALH))
 (2808 14 (:REWRITE DEFAULT-PLUS-2))
 (2782 16 (:REWRITE ACL2-NUMBERP-X))
 (1977 16 (:REWRITE RATIONALP-X))
 (1143 13 (:REWRITE DEFAULT-PLUS-1))
 (1132 2 (:REWRITE RTL::INTEGERP-EVALH))
 (1122 2 (:DEFINITION RTL::SHFP))
 (998 499
      (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-Y))
 (912 304
      (:TYPE-PRESCRIPTION RTL::ALL-INTEGERS-INTEGER))
 (768 768 (:TYPE-PRESCRIPTION RTL::ECP))
 (702 247
      (:TYPE-PRESCRIPTION RTL::INT-CAR-TRIPP))
 (603 1 (:REWRITE RTL::EVALH-POW-REWRITE))
 (552 8
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (494 247
      (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-X))
 (488 488 (:TYPE-PRESCRIPTION RTL::TRIPP))
 (306 306
      (:TYPE-PRESCRIPTION RTL::ALL-INTEGERS))
 (300 150
      (:TYPE-PRESCRIPTION RTL::INT-CADR-TRIPP))
 (194 24 (:REWRITE DEFAULT-CAR))
 (154 58
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (154 58
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (148 58
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (148
  58
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (148 58
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (148 58
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (148 58
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (148
     58
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (147 4 (:REWRITE DEFAULT-TIMES-1))
 (140 56
      (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (140 56
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE))
 (140 56
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (138 1 (:REWRITE |(+ (if a b c) x)|))
 (125 1 (:REWRITE |(* (if a b c) x)|))
 (124 1 (:REWRITE RTL::NTHCDR+))
 (122 68 (:REWRITE DEFAULT-CDR))
 (120 3 (:DEFINITION NTHCDR))
 (106 53
      (:TYPE-PRESCRIPTION RTL::INT-CADDR-TRIPP))
 (95 3 (:REWRITE DEFAULT-EXPT-2))
 (68 4 (:REWRITE |(+ y x)|))
 (66 5 (:REWRITE ZP-OPEN))
 (65 4 (:REWRITE DEFAULT-TIMES-2))
 (46 2 (:REWRITE DEFAULT-EXPT-1))
 (36 14 (:REWRITE RTL::INTEGERP-EC-X))
 (36 14 (:REWRITE RTL::INT-CAR-TRIPP))
 (24 24 (:TYPE-PRESCRIPTION RTL::SHFP))
 (24 10 (:REWRITE RTL::INT-CADR-TRIPP))
 (24 1 (:REWRITE |(* 1 x)|))
 (22 2 (:DEFINITION NTH))
 (20 20 (:REWRITE REDUCE-INTEGERP-+))
 (20 20 (:REWRITE INTEGERP-MINUS-X))
 (20 20 (:META META-INTEGERP-CORRECT))
 (16 8 (:REWRITE RTL::SHNFP-SHFP))
 (15 5 (:REWRITE RTL::SPLIT$-CASE-5-7))
 (11 5 (:REWRITE RTL::SPLIT$-CASE-5-2))
 (10 2 (:REWRITE RTL::ALL-INTEGERS-INTEGER))
 (9 9 (:REWRITE REDUCE-RATIONALP-+))
 (9 9 (:REWRITE REDUCE-RATIONALP-*))
 (9 9 (:REWRITE RATIONALP-MINUS-X))
 (9 9 (:META META-RATIONALP-CORRECT))
 (8 8 (:TYPE-PRESCRIPTION NATP))
 (8 8 (:REWRITE THE-FLOOR-BELOW))
 (8 8 (:REWRITE THE-FLOOR-ABOVE))
 (8 8 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (8 8 (:REWRITE SIMPLIFY-SUMS-<))
 (8 8 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (8 8 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (8 8
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (8 8
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (8 8
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (8 8
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (8 8 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (8 8 (:REWRITE INTEGERP-<-CONSTANT))
 (8 8
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (8 8 (:REWRITE DEFAULT-LESS-THAN-2))
 (8 8 (:REWRITE DEFAULT-LESS-THAN-1))
 (8 8 (:REWRITE CONSTANT-<-INTEGERP))
 (8 8 (:REWRITE |(equal c (/ x))|))
 (8 8 (:REWRITE |(equal c (- x))|))
 (8 8 (:REWRITE |(equal (/ x) c)|))
 (8 8 (:REWRITE |(equal (/ x) (/ y))|))
 (8 8 (:REWRITE |(equal (- x) c)|))
 (8 8 (:REWRITE |(equal (- x) (- y))|))
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
 (7 7
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (7 7 (:REWRITE NORMALIZE-ADDENDS))
 (6 6 (:REWRITE RTL::SPLIT$-CASE-5-3))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (6 6 (:REWRITE |(< (/ x) 0)|))
 (6 6 (:REWRITE |(< (* x y) 0)|))
 (4 2 (:REWRITE RTL::INT-CADDR-TRIPP))
 (2 2
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (2 2 (:REWRITE RTL::ALL-INTEGERS-VALS))
 (2 2 (:REWRITE |(expt 1/c n)|))
 (2 2 (:REWRITE |(expt (- x) n)|))
 (2 1
    (:TYPE-PRESCRIPTION RTL::SPLIT$-CASE-9))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (1 1 (:REWRITE RTL::SHNFP-INT))
 (1 1 (:REWRITE |(< 0 (/ x))|))
 (1 1 (:REWRITE |(< 0 (* x y))|)))
(RTL::SPLIT$-CASE-5-10
 (15380 4 (:DEFINITION RTL::EVALH))
 (10795 117 (:REWRITE ACL2-NUMBERP-X))
 (7882 117 (:REWRITE RATIONALP-X))
 (6198 3041
       (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-Y))
 (6174 141 (:REWRITE DEFAULT-PLUS-1))
 (5035 1609
       (:TYPE-PRESCRIPTION RTL::ALL-INTEGERS-INTEGER))
 (4528 8 (:REWRITE RTL::INTEGERP-EVALH))
 (4488 8 (:DEFINITION RTL::SHFP))
 (4096 143 (:REWRITE DEFAULT-PLUS-2))
 (3825 3825 (:TYPE-PRESCRIPTION RTL::ECP))
 (3140 67 (:REWRITE DEFAULT-TIMES-2))
 (2438 14 (:REWRITE |(+ (if a b c) x)|))
 (1960 694
       (:TYPE-PRESCRIPTION RTL::INT-CAR-TRIPP))
 (1637 1637
       (:TYPE-PRESCRIPTION RTL::ALL-INTEGERS))
 (1617 36
       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (1542 1542 (:TYPE-PRESCRIPTION RTL::TRIPP))
 (1388 694
       (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-X))
 (1239 309
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1239 309
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (950 65 (:REWRITE DEFAULT-TIMES-1))
 (944 472
      (:TYPE-PRESCRIPTION RTL::INT-CADR-TRIPP))
 (894 309
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (894
  309
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (894 309
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (894 309
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (894 309
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (894
     309
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (894 5 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (892 16 (:REWRITE DEFAULT-EXPT-2))
 (867 5 (:REWRITE MOD-X-Y-=-X . 4))
 (867 5 (:REWRITE MOD-X-Y-=-X . 3))
 (865 99 (:REWRITE DEFAULT-CAR))
 (865 5 (:REWRITE MOD-ZERO . 3))
 (841 5 (:REWRITE DEFAULT-MOD-RATIO))
 (801 5 (:REWRITE MOD-ZERO . 4))
 (792 5 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (759 5 (:REWRITE RTL::MOD-DOES-NOTHING))
 (758 12 (:REWRITE |(* (if a b c) x)|))
 (535 295 (:REWRITE DEFAULT-CDR))
 (528 9 (:REWRITE |(* y x)|))
 (520 4 (:REWRITE RTL::NTHCDR+))
 (513 49 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (505 25 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (498 10 (:REWRITE DEFAULT-EXPT-1))
 (420 210
      (:TYPE-PRESCRIPTION RTL::INT-CADDR-TRIPP))
 (413 49 (:REWRITE DEFAULT-LESS-THAN-1))
 (342 3 (:REWRITE |(* x (+ y z))|))
 (318 2 (:REWRITE |(* (* x y) z)|))
 (295 171 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (295 171 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (274 154
      (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (274 154
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE))
 (271 171
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (271 171
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (260 16 (:REWRITE ZP-OPEN))
 (239 49 (:REWRITE SIMPLIFY-SUMS-<))
 (202 202
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (202 202
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (202 202
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (202 171 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
 (194 2 (:REWRITE |(* y (* x z))|))
 (192 8 (:REWRITE RTL::ALL-INTEGERS-INTEGER))
 (171 171
      (:TYPE-PRESCRIPTION RTL::NATP-MOD-2))
 (171 171 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (171 171
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (171 171
      (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (171 171
      (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
 (171 171
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (171 171 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (171 5 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (171 5 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (166 5
      (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (166 5
      (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (166 5
      (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (160 4 (:DEFINITION RTL::ALL-INTEGERS))
 (154 154
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (149 59 (:REWRITE RTL::INTEGERP-EC-X))
 (149 59 (:REWRITE RTL::INT-CAR-TRIPP))
 (149 49 (:REWRITE DEFAULT-LESS-THAN-2))
 (148 10 (:REWRITE |(* 1 x)|))
 (146 146
      (:TYPE-PRESCRIPTION RTL::RATIONALP-MOD))
 (146 146
      (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
 (142 93 (:META META-INTEGERP-CORRECT))
 (141 5 (:REWRITE DEFAULT-MOD-1))
 (126 42 (:REWRITE RTL::SPLIT$-CASE-5-8))
 (122 5 (:REWRITE MOD-X-Y-=-X . 2))
 (116 48 (:REWRITE RTL::INT-CADR-TRIPP))
 (110 8 (:DEFINITION NTH))
 (96 96 (:TYPE-PRESCRIPTION RTL::SHFP))
 (96 32 (:REWRITE RTL::SPLIT$-CASE-5-7))
 (94 2
     (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 1))
 (93 93 (:REWRITE REDUCE-INTEGERP-+))
 (93 93 (:REWRITE INTEGERP-MINUS-X))
 (64 32 (:REWRITE RTL::SHNFP-SHFP))
 (63 63
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (63 63 (:REWRITE NORMALIZE-ADDENDS))
 (52 4 (:REWRITE ZIP-OPEN))
 (49 49 (:REWRITE THE-FLOOR-BELOW))
 (49 49 (:REWRITE THE-FLOOR-ABOVE))
 (49 49
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (49 49
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (49 49
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (49 49 (:REWRITE INTEGERP-<-CONSTANT))
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
 (46 4 (:REWRITE |(+ y (+ x z))|))
 (44 20 (:REWRITE RTL::SPLIT$-CASE-5-2))
 (39 39 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (39 39 (:REWRITE REDUCE-RATIONALP-+))
 (39 39 (:REWRITE REDUCE-RATIONALP-*))
 (39 39 (:REWRITE RATIONALP-MINUS-X))
 (39 39 (:META META-RATIONALP-CORRECT))
 (36 36 (:REWRITE SIMPLIFY-SUMS-EQUAL))
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
 (35 35 (:TYPE-PRESCRIPTION NATP))
 (29 29
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (29 29
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (29 29 (:REWRITE |(< (/ x) 0)|))
 (29 29 (:REWRITE |(< (* x y) 0)|))
 (28 2 (:REWRITE |(expt 0 n)|))
 (26 26
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (25 25 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (25 25 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (25 25 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (22 10 (:LINEAR RTL::P-IS-BIG))
 (18 9 (:REWRITE DEFAULT-DIVIDE))
 (16 8 (:REWRITE RTL::INT-CADDR-TRIPP))
 (10 5 (:REWRITE DEFAULT-MOD-2))
 (9 9
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (9 9
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (9 9
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (9 9
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (9 9 (:REWRITE |(< 0 (/ x))|))
 (9 9 (:REWRITE |(< 0 (* x y))|))
 (8 8 (:REWRITE |(expt 1/c n)|))
 (8 8 (:REWRITE |(expt (- x) n)|))
 (6 6 (:REWRITE |(< (+ c/d x) y)|))
 (6 6 (:REWRITE |(< (+ (- c) x) y)|))
 (5 5
    (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (5 5 (:REWRITE |(mod x (- y))| . 3))
 (5 5 (:REWRITE |(mod x (- y))| . 2))
 (5 5 (:REWRITE |(mod x (- y))| . 1))
 (5 5
    (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (5 5
    (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (5 5 (:REWRITE |(* c (* d x))|))
 (4 4 (:REWRITE RTL::ALL-INTEGERS-VALS))
 (4 4 (:REWRITE |(* 0 x)|))
 (2 2 (:REWRITE RTL::SHNFP-INT))
 (2 2
    (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 3))
 (2 2
    (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 2))
 (2 2
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (1 1 (:REWRITE INTEGERP-/))
 (1 1 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (1 1 (:REWRITE |(equal (+ (- c) x) y)|))
 (1 1 (:REWRITE |(equal (* x y) 0)|))
 (1 1 (:REWRITE |(< y (+ (- c) x))|))
 (1 1 (:REWRITE |(< x (+ c/d y))|))
 (1 1
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|)))
(RTL::SPLIT$-CASE-5-11 (4 4 (:DEFINITION MV-NTH)))
(RTL::SPLIT$-CASE-5-12 (140 70
                            (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-Y))
                       (85 85 (:TYPE-PRESCRIPTION RTL::ECP))
                       (60 10
                           (:TYPE-PRESCRIPTION RTL::SPLIT$-CASE-5-2))
                       (35 35 (:TYPE-PRESCRIPTION RTL::TRIPP))
                       (30 15
                           (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-X))
                       (30 15
                           (:TYPE-PRESCRIPTION RTL::INT-CAR-TRIPP))
                       (20 10
                           (:TYPE-PRESCRIPTION RTL::INT-CADR-TRIPP))
                       (20 10
                           (:TYPE-PRESCRIPTION RTL::INT-CADDR-TRIPP)))
(RTL::SPLIT$-CASE-5-13
     (11 1 (:DEFINITION NTH))
     (2 2 (:REWRITE THE-FLOOR-BELOW))
     (2 2 (:REWRITE THE-FLOOR-ABOVE))
     (2 2 (:REWRITE SIMPLIFY-SUMS-<))
     (2 2 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (2 2 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (2 2
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (2 2
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
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
     (2 1 (:REWRITE DEFAULT-CDR))
     (2 1 (:REWRITE DEFAULT-CAR))
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
(RTL::SPLIT$-CASE-5-14
 (273606 12 (:DEFINITION RTL::SPLIT$))
 (248832 48 (:DEFINITION RTL::NORM-ADD))
 (158113 2331 (:REWRITE ACL2-NUMBERP-X))
 (87322 2211 (:REWRITE RATIONALP-X))
 (65351 743 (:REWRITE DEFAULT-LESS-THAN-2))
 (62128 31060
        (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-Y))
 (56950 56950 (:TYPE-PRESCRIPTION RTL::ECP))
 (49827 1513 (:REWRITE DEFAULT-PLUS-1))
 (47692 47692 (:TYPE-PRESCRIPTION RTL::TRIPP))
 (45671 647 (:REWRITE DEFAULT-LESS-THAN-1))
 (42966 21470
        (:TYPE-PRESCRIPTION RTL::INT-CAR-TRIPP))
 (42940 21470
        (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-X))
 (38016 384 (:REWRITE DEFAULT-MINUS))
 (37750 535
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (36836 17826
        (:TYPE-PRESCRIPTION RTL::SPLIT$-CASE-5-2))
 (35500 17750
        (:TYPE-PRESCRIPTION RTL::INT-CADR-TRIPP))
 (30119 1641 (:REWRITE DEFAULT-PLUS-2))
 (18185 1266 (:REWRITE DEFAULT-CAR))
 (8482 1979 (:REWRITE DEFAULT-CDR))
 (7376 6 (:DEFINITION RTL::EVALH))
 (7181 279 (:REWRITE DEFAULT-TIMES-1))
 (6960 48 (:DEFINITION RTL::NORM-EXPT))
 (6634 2214 (:REWRITE RTL::INTEGERP-EC-X))
 (6634 2214 (:REWRITE RTL::INT-CAR-TRIPP))
 (5634 1878 (:REWRITE RTL::INT-CADR-TRIPP))
 (5185 71 (:REWRITE ZP-OPEN))
 (4896 240 (:REWRITE |(+ x (if a b c))|))
 (3511 535 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (3000 48 (:REWRITE |(< x (if a b c))|))
 (2664 12 (:DEFINITION EVENP))
 (2323 2323 (:REWRITE REDUCE-INTEGERP-+))
 (2323 2323 (:REWRITE INTEGERP-MINUS-X))
 (2323 2323 (:META META-INTEGERP-CORRECT))
 (2211 2211 (:REWRITE REDUCE-RATIONALP-+))
 (2211 2211 (:REWRITE REDUCE-RATIONALP-*))
 (2211 2211 (:REWRITE RATIONALP-MINUS-X))
 (2211 2211 (:META META-RATIONALP-CORRECT))
 (1162 20 (:REWRITE DEFAULT-EXPT-2))
 (1152 44 (:REWRITE |(* (if a b c) x)|))
 (1051 285 (:REWRITE DEFAULT-TIMES-2))
 (1042 14 (:REWRITE DEFAULT-EXPT-1))
 (786 162
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (748 26 (:REWRITE |(+ (if a b c) x)|))
 (743 743 (:REWRITE THE-FLOOR-BELOW))
 (743 743 (:REWRITE THE-FLOOR-ABOVE))
 (624 6 (:REWRITE RTL::NTHCDR+))
 (592 296
      (:TYPE-PRESCRIPTION RTL::INT-CADDR-TRIPP))
 (586 394
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (562 62 (:REWRITE |(* y x)|))
 (535 535
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (535 535
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (535 535
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (535 535 (:REWRITE |(equal c (/ x))|))
 (535 535 (:REWRITE |(equal c (- x))|))
 (535 535 (:REWRITE |(equal (/ x) c)|))
 (535 535 (:REWRITE |(equal (/ x) (/ y))|))
 (535 535 (:REWRITE |(equal (- x) c)|))
 (535 535 (:REWRITE |(equal (- x) (- y))|))
 (486 6 (:REWRITE RTL::EVALH-POW-REWRITE))
 (478 478
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (478 478 (:REWRITE NORMALIZE-ADDENDS))
 (456 456
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (456 456
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (456 456
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (456 456
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (432 36 (:REWRITE |(* x (+ y z))|))
 (431 407
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (431 407
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (407 407
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (407 407 (:REWRITE INTEGERP-<-CONSTANT))
 (407 407 (:REWRITE CONSTANT-<-INTEGERP))
 (407 407
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (407 407
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (407 407
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (407 407
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (407 407 (:REWRITE |(< c (- x))|))
 (407 407
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (407 407
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (407 407
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (407 407
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (407 407 (:REWRITE |(< (/ x) (/ y))|))
 (407 407 (:REWRITE |(< (- x) c)|))
 (407 407 (:REWRITE |(< (- x) (- y))|))
 (400 13 (:REWRITE RTL::ALL-INTEGERS-INTEGER))
 (394 394 (:REWRITE SIMPLIFY-SUMS-<))
 (361 13 (:DEFINITION RTL::ALL-INTEGERS))
 (253 17 (:REWRITE RTL::CONSP-NTHCDR))
 (162 162 (:REWRITE |(< 0 (/ x))|))
 (162 162 (:REWRITE |(< 0 (* x y))|))
 (150 150
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (122 50
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (122 50
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (122 8 (:REWRITE ZIP-OPEN))
 (115 115
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (114 114
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (114 114
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (114 114 (:REWRITE |(< (/ x) 0)|))
 (114 114 (:REWRITE |(< (* x y) 0)|))
 (110 10 (:DEFINITION NTH))
 (104 66
      (:TYPE-PRESCRIPTION RTL::SPLIT$-CASE-5-7))
 (96 96 (:TYPE-PRESCRIPTION RTL::NORM-POP))
 (96 96 (:TYPE-PRESCRIPTION RTL::NORM-MUL))
 (86 32 (:REWRITE RTL::SHNFP-INT))
 (84 6 (:REWRITE |(+ y (+ x z))|))
 (50 50
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (50
   50
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (50
  50
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (50 50
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (50 50
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (50 50
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (50 50
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (48 48 (:TYPE-PRESCRIPTION ABS))
 (48 30
     (:TYPE-PRESCRIPTION RTL::SPLIT$-CASE-5-6))
 (48 4 (:REWRITE RTL::CAR-NTHCDR))
 (42 42 (:REWRITE |(< y (+ (- c) x))|))
 (42 42 (:REWRITE |(< x (+ c/d y))|))
 (38 38
     (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (38 38
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE))
 (38 38
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (38 38 (:TYPE-PRESCRIPTION EXPT))
 (28 2 (:REWRITE |(expt 0 n)|))
 (24 24
     (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (20 8 (:REWRITE RTL::SPLIT$-CASE-5-2))
 (16 14 (:REWRITE |(* 1 x)|))
 (16 4 (:REWRITE RTL::SPLIT$-CASE-5-7))
 (15 15 (:REWRITE RTL::LEN-VALS))
 (8 8 (:TYPE-PRESCRIPTION NATP))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (8 8 (:REWRITE |(expt 1/c n)|))
 (8 8 (:REWRITE |(expt (- x) n)|))
 (8 8 (:REWRITE |(* 0 x)|))
 (6 6 (:REWRITE FOLD-CONSTS-IN-+))
 (6 6 (:REWRITE |(equal (+ (- c) x) y)|)))
(RTL::SPLIT$-CASE-5-15
 (152 76
      (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-X))
 (152 76
      (:TYPE-PRESCRIPTION RTL::INT-CAR-TRIPP))
 (138 138 (:TYPE-PRESCRIPTION RTL::ECP))
 (120 60
      (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-Y))
 (119 29
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (119 29
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (112 28
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (110 110 (:TYPE-PRESCRIPTION RTL::TRIPP))
 (64 32
     (:TYPE-PRESCRIPTION RTL::INT-CADR-TRIPP))
 (58 2 (:REWRITE ACL2-NUMBERP-X))
 (52 1
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (36 12
     (:TYPE-PRESCRIPTION RTL::ALL-INTEGERS-INTEGER))
 (34 2 (:REWRITE RATIONALP-X))
 (32 29
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (32
  29
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (32 29
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (32 29
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (32 29
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (32 29
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (28 28
     (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (28 28
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE))
 (23 1 (:REWRITE DEFAULT-EXPT-1))
 (13 13
     (:TYPE-PRESCRIPTION RTL::ALL-INTEGERS))
 (11 1 (:DEFINITION NTHCDR))
 (11 1 (:DEFINITION NTH))
 (10 3 (:REWRITE DEFAULT-CAR))
 (5 3 (:REWRITE DEFAULT-CDR))
 (5 1 (:REWRITE RTL::ALL-INTEGERS-INTEGER))
 (5 1 (:REWRITE |(+ y x)|))
 (4 1 (:REWRITE DEFAULT-EXPT-2))
 (3 3 (:REWRITE DEFAULT-PLUS-2))
 (3 3 (:REWRITE DEFAULT-PLUS-1))
 (3 1 (:REWRITE RTL::INTEGERP-EC-X))
 (3 1 (:REWRITE RTL::INT-CAR-TRIPP))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE THE-FLOOR-BELOW))
 (2 2 (:REWRITE THE-FLOOR-ABOVE))
 (2 2 (:REWRITE SIMPLIFY-SUMS-<))
 (2 2 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (2 2 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (2 2
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (2 2
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (2 2 (:REWRITE REDUCE-INTEGERP-+))
 (2 2 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (2 2
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (2 2 (:REWRITE NORMALIZE-ADDENDS))
 (2 2 (:REWRITE INTEGERP-MINUS-X))
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
 (2 2 (:META META-INTEGERP-CORRECT))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (1 1 (:REWRITE RTL::SHNFP-INT))
 (1 1 (:REWRITE REDUCE-RATIONALP-+))
 (1 1 (:REWRITE REDUCE-RATIONALP-*))
 (1 1
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (1 1
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (1 1 (:REWRITE RATIONALP-MINUS-X))
 (1 1
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (1 1 (:REWRITE RTL::ALL-INTEGERS-VALS))
 (1 1 (:REWRITE |(expt 1/c n)|))
 (1 1 (:REWRITE |(expt (- x) n)|))
 (1 1 (:REWRITE |(equal c (/ x))|))
 (1 1 (:REWRITE |(equal c (- x))|))
 (1 1 (:REWRITE |(equal (/ x) c)|))
 (1 1 (:REWRITE |(equal (/ x) (/ y))|))
 (1 1 (:REWRITE |(equal (- x) c)|))
 (1 1 (:REWRITE |(equal (- x) (- y))|))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (* x y) 0)|))
 (1 1 (:META META-RATIONALP-CORRECT)))
(RTL::SPLIT$-CASE-5-16)
(RTL::SPLIT$-CASE-5-17
 (64 64 (:DEFINITION MV-NTH))
 (22
   2
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (22 2
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (22 2
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (22 2
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (16 16 (:TYPE-PRESCRIPTION RTL::TRIPP))
 (16 16 (:TYPE-PRESCRIPTION RTL::ECP))
 (16 8
     (:TYPE-PRESCRIPTION RTL::SPLIT$-CASE-5-2))
 (16 8
     (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-Y))
 (16 8
     (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-X))
 (16 8
     (:TYPE-PRESCRIPTION RTL::INT-CAR-TRIPP))
 (16 8
     (:TYPE-PRESCRIPTION RTL::INT-CADR-TRIPP))
 (8 8 (:TYPE-PRESCRIPTION RTL::SHNFP))
 (2 2
    (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (2
  2
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT)))
(RTL::SPLIT$-CASE-5-18
 (273606 12 (:DEFINITION RTL::SPLIT$))
 (248832 48 (:DEFINITION RTL::NORM-ADD))
 (158377 2343 (:REWRITE ACL2-NUMBERP-X))
 (87406 2223 (:REWRITE RATIONALP-X))
 (65353 745 (:REWRITE DEFAULT-LESS-THAN-2))
 (62348 31166
        (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-Y))
 (57118 57118 (:TYPE-PRESCRIPTION RTL::ECP))
 (49923 1555 (:REWRITE DEFAULT-PLUS-1))
 (47828 47828 (:TYPE-PRESCRIPTION RTL::TRIPP))
 (45673 649 (:REWRITE DEFAULT-LESS-THAN-1))
 (43066 21524
        (:TYPE-PRESCRIPTION RTL::INT-CAR-TRIPP))
 (43048 21524
        (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-X))
 (38016 384 (:REWRITE DEFAULT-MINUS))
 (37758 537
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (37024 17882
        (:TYPE-PRESCRIPTION RTL::SPLIT$-CASE-5-2))
 (35624 17812
        (:TYPE-PRESCRIPTION RTL::INT-CADR-TRIPP))
 (30333 1685 (:REWRITE DEFAULT-PLUS-2))
 (18313 1268 (:REWRITE DEFAULT-CAR))
 (8846 2002 (:REWRITE DEFAULT-CDR))
 (8414 6 (:DEFINITION RTL::EVALH))
 (7185 287 (:REWRITE DEFAULT-TIMES-1))
 (6960 48 (:DEFINITION RTL::NORM-EXPT))
 (6644 2216 (:REWRITE RTL::INTEGERP-EC-X))
 (6644 2216 (:REWRITE RTL::INT-CAR-TRIPP))
 (5652 1884 (:REWRITE RTL::INT-CADR-TRIPP))
 (5183 69 (:REWRITE ZP-OPEN))
 (4896 240 (:REWRITE |(+ x (if a b c))|))
 (3513 537 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (3000 48 (:REWRITE |(< x (if a b c))|))
 (2664 12 (:DEFINITION EVENP))
 (2333 2333 (:REWRITE REDUCE-INTEGERP-+))
 (2333 2333 (:REWRITE INTEGERP-MINUS-X))
 (2333 2333 (:META META-INTEGERP-CORRECT))
 (2223 2223 (:REWRITE REDUCE-RATIONALP-+))
 (2223 2223 (:REWRITE REDUCE-RATIONALP-*))
 (2223 2223 (:REWRITE RATIONALP-MINUS-X))
 (2223 2223 (:META META-RATIONALP-CORRECT))
 (1391 297 (:REWRITE DEFAULT-TIMES-2))
 (1202 46 (:REWRITE |(* (if a b c) x)|))
 (1184 16 (:REWRITE DEFAULT-EXPT-1))
 (1170 22 (:REWRITE DEFAULT-EXPT-2))
 (844 32 (:REWRITE |(+ (if a b c) x)|))
 (786 162
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (745 745 (:REWRITE THE-FLOOR-BELOW))
 (745 745 (:REWRITE THE-FLOOR-ABOVE))
 (624 6 (:REWRITE RTL::NTHCDR+))
 (602 64 (:REWRITE |(* y x)|))
 (592 296
      (:TYPE-PRESCRIPTION RTL::INT-CADDR-TRIPP))
 (588 396
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (537 537
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (537 537
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (537 537
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (537 537 (:REWRITE |(equal c (/ x))|))
 (537 537 (:REWRITE |(equal c (- x))|))
 (537 537 (:REWRITE |(equal (/ x) c)|))
 (537 537 (:REWRITE |(equal (/ x) (/ y))|))
 (537 537 (:REWRITE |(equal (- x) c)|))
 (537 537 (:REWRITE |(equal (- x) (- y))|))
 (488 488
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (488 488 (:REWRITE NORMALIZE-ADDENDS))
 (486 6 (:REWRITE RTL::EVALH-POW-REWRITE))
 (456 456
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (456 456
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (456 456
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (456 456
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (452 20 (:REWRITE RTL::CONSP-NTHCDR))
 (433 409
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (433 409
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (432 36 (:REWRITE |(* x (+ y z))|))
 (409 409
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (409 409 (:REWRITE INTEGERP-<-CONSTANT))
 (409 409 (:REWRITE CONSTANT-<-INTEGERP))
 (409 409
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (409 409
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (409 409
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (409 409
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (409 409 (:REWRITE |(< c (- x))|))
 (409 409
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (409 409
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (409 409
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (409 409
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (409 409 (:REWRITE |(< (/ x) (/ y))|))
 (409 409 (:REWRITE |(< (- x) c)|))
 (409 409 (:REWRITE |(< (- x) (- y))|))
 (396 396 (:REWRITE SIMPLIFY-SUMS-<))
 (280 9 (:REWRITE RTL::ALL-INTEGERS-INTEGER))
 (253 9 (:DEFINITION RTL::ALL-INTEGERS))
 (166 10 (:REWRITE ZIP-OPEN))
 (162 162 (:REWRITE |(< 0 (/ x))|))
 (162 162 (:REWRITE |(< 0 (* x y))|))
 (150 150
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (116 116
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (116 116
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (116 116 (:REWRITE |(< (/ x) 0)|))
 (116 116 (:REWRITE |(< (* x y) 0)|))
 (115 115
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (102
   54
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (96 96 (:TYPE-PRESCRIPTION RTL::NORM-POP))
 (96 96 (:TYPE-PRESCRIPTION RTL::NORM-MUL))
 (88 8 (:DEFINITION NTH))
 (86 32 (:REWRITE RTL::SHNFP-INT))
 (86 4 (:REWRITE |(expt 0 n)|))
 (84 6 (:REWRITE |(+ y (+ x z))|))
 (76 38
     (:TYPE-PRESCRIPTION RTL::SPLIT$-CASE-5-7))
 (54 54
     (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (54 54
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE))
 (54 54
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (54
  54
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (54 54
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (54 54
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (54 54
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (54 54
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (54 54
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (54 54
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (54 54
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (54 54 (:TYPE-PRESCRIPTION EXPT))
 (48 48 (:TYPE-PRESCRIPTION ABS))
 (42 42 (:REWRITE |(< y (+ (- c) x))|))
 (42 42 (:REWRITE |(< x (+ c/d y))|))
 (36 18
     (:TYPE-PRESCRIPTION RTL::SPLIT$-CASE-5-6))
 (24 24
     (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (24 2 (:REWRITE RTL::CAR-NTHCDR))
 (22 10 (:REWRITE RTL::SPLIT$-CASE-5-2))
 (16 16 (:REWRITE RTL::LEN-VALS))
 (16 16 (:REWRITE |(* 1 x)|))
 (16 4 (:REWRITE RTL::SPLIT$-CASE-5-7))
 (10 10 (:TYPE-PRESCRIPTION NATP))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (10 10 (:REWRITE |(expt 1/c n)|))
 (10 10 (:REWRITE |(expt (- x) n)|))
 (10 10 (:REWRITE |(* 0 x)|))
 (6 6 (:REWRITE FOLD-CONSTS-IN-+))
 (6 6 (:REWRITE |(equal (+ (- c) x) y)|)))
(RTL::SPLIT$-CASE-5-19
     (3928 12 (:LINEAR MOD-BOUNDS-3))
     (3260 520 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
     (2980 596 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (2980 596 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (2952 2952
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (2952 2952
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (2952 2952
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (2900 596
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (2900 596
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (2389 93 (:REWRITE |(* y x)|))
     (2218 43 (:REWRITE MOD-ZERO . 3))
     (2030 58 (:REWRITE |(* (* x y) z)|))
     (1961 503 (:REWRITE DEFAULT-TIMES-2))
     (1950 313
           (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (1695 43 (:REWRITE DEFAULT-MOD-RATIO))
     (1548 31 (:REWRITE |(* x (+ y z))|))
     (1495 43 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (1426 71 (:REWRITE DEFAULT-PLUS-2))
     (1406 43 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (1344 43 (:REWRITE MOD-X-Y-=-X . 4))
     (1344 43 (:REWRITE MOD-X-Y-=-X . 3))
     (1211 71 (:REWRITE DEFAULT-PLUS-1))
     (1208 503 (:REWRITE DEFAULT-TIMES-1))
     (1167 43 (:REWRITE RTL::MOD-DOES-NOTHING))
     (936 24 (:LINEAR MOD-BOUNDS-2))
     (754 58 (:REWRITE |(* y (* x z))|))
     (725 43 (:REWRITE MOD-ZERO . 4))
     (692 213
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (596 596 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (596 596
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (596 596
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (596 596
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (596 596 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (574 43 (:REWRITE MOD-X-Y-=-X . 2))
     (520 520
          (:TYPE-PRESCRIPTION RTL::NATP-MOD-2))
     (520 520 (:TYPE-PRESCRIPTION NATP))
     (509 16
          (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 1))
     (501 213 (:REWRITE DEFAULT-LESS-THAN-1))
     (367 86 (:META META-INTEGERP-CORRECT))
     (313 313
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (313 313
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (313 313
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (301 43 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (301 43 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (300 213 (:REWRITE DEFAULT-LESS-THAN-2))
     (294 294
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (289 213 (:REWRITE SIMPLIFY-SUMS-<))
     (213 213 (:REWRITE THE-FLOOR-BELOW))
     (213 213 (:REWRITE THE-FLOOR-ABOVE))
     (213 213
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (213 213
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (213 213
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (213 213 (:REWRITE INTEGERP-<-CONSTANT))
     (213 213 (:REWRITE CONSTANT-<-INTEGERP))
     (213 213
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (213 213
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (213 213
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (213 213
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (213 213 (:REWRITE |(< c (- x))|))
     (213 213
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (213 213
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (213 213
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (213 213
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (213 213 (:REWRITE |(< (/ x) (/ y))|))
     (213 213 (:REWRITE |(< (- x) c)|))
     (213 213 (:REWRITE |(< (- x) (- y))|))
     (198 43
          (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (198 43
          (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (198 43
          (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (186 93 (:REWRITE DEFAULT-DIVIDE))
     (137 137 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (103 43
          (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (103 43
          (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (103 43
          (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (93 93
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (88 88
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (88 88
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (88 88 (:REWRITE |(< (/ x) 0)|))
     (88 88 (:REWRITE |(< (* x y) 0)|))
     (87 87 (:REWRITE |(* c (* d x))|))
     (86 86 (:REWRITE REDUCE-INTEGERP-+))
     (86 86 (:REWRITE INTEGERP-MINUS-X))
     (86 43 (:REWRITE DEFAULT-MOD-2))
     (84 61
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (61 61
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (61 61 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (61 61
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (61 61
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (61 61
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (61 61 (:REWRITE |(equal c (/ x))|))
     (61 61 (:REWRITE |(equal c (- x))|))
     (61 61 (:REWRITE |(equal (/ x) c)|))
     (61 61 (:REWRITE |(equal (/ x) (/ y))|))
     (61 61 (:REWRITE |(equal (- x) c)|))
     (61 61 (:REWRITE |(equal (- x) (- y))|))
     (59 59
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (59 59 (:REWRITE NORMALIZE-ADDENDS))
     (58 58
         (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (49 49
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (49 49
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (49 49 (:REWRITE |(< 0 (/ x))|))
     (49 49 (:REWRITE |(< 0 (* x y))|))
     (48 48 (:REWRITE |(< (+ c/d x) y)|))
     (48 48 (:REWRITE |(< (+ (- c) x) y)|))
     (43 43 (:REWRITE DEFAULT-MOD-1))
     (43 43 (:REWRITE |(mod x (- y))| . 3))
     (43 43 (:REWRITE |(mod x (- y))| . 2))
     (43 43 (:REWRITE |(mod x (- y))| . 1))
     (33 33 (:REWRITE INTEGERP-/))
     (25 25 (:REWRITE |(equal (* x y) 0)|))
     (25 25
         (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (20 20
         (:TYPE-PRESCRIPTION RTL::RATIONALP-MOD))
     (20 20
         (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
     (16 16
         (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 3))
     (16 16
         (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 2))
     (15 15
         (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (12 12 (:LINEAR RTL::MOD-BND-3))
     (11 11 (:REWRITE |(equal (+ (- c) x) y)|))
     (11 11 (:REWRITE |(< y (+ (- c) x))|))
     (11 11 (:REWRITE |(< x (+ c/d y))|)))
(RTL::SPLIT$-CASE-5-20 (236 236 (:DEFINITION MV-NTH)))
(RTL::SPLIT$-CASE-5-21 (108 108 (:DEFINITION MV-NTH)))
(RTL::SPLIT$-CASE-5-22 (21 21 (:REWRITE DEFAULT-TIMES-2))
                       (21 21 (:REWRITE DEFAULT-TIMES-1))
                       (18 18 (:REWRITE DEFAULT-PLUS-2))
                       (18 18 (:REWRITE DEFAULT-PLUS-1))
                       (12 12
                           (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                       (12 12
                           (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                       (12 12 (:REWRITE NORMALIZE-ADDENDS))
                       (6 6 (:REWRITE REDUCE-INTEGERP-+))
                       (6 6 (:REWRITE INTEGERP-MINUS-X))
                       (6 6 (:REWRITE FOLD-CONSTS-IN-+))
                       (6 6 (:REWRITE |(+ c (+ d x))|))
                       (6 6 (:META META-INTEGERP-CORRECT))
                       (2 2 (:REWRITE |(* c (* d x))|)))
(RTL::SPLIT$-CASE-5-23 (264 264 (:DEFINITION MV-NTH)))
(RTL::SPLIT$-CASE-5-24
 (62208 12 (:DEFINITION RTL::NORM-ADD))
 (61931 671 (:REWRITE ACL2-NUMBERP-X))
 (43036 637 (:REWRITE RATIONALP-X))
 (28020 8 (:DEFINITION RTL::EVALH))
 (23318 11639
        (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-Y))
 (19878 19878 (:TYPE-PRESCRIPTION RTL::ECP))
 (19874 52 (:REWRITE RTL::INTEGERP-EVALH))
 (19128 40 (:DEFINITION RTL::SHFP))
 (16442 284 (:REWRITE DEFAULT-LESS-THAN-2))
 (13838 6919
        (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-X))
 (13834 511 (:REWRITE DEFAULT-PLUS-1))
 (11516 260 (:REWRITE DEFAULT-LESS-THAN-1))
 (10956 241
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (10850 5425
        (:TYPE-PRESCRIPTION RTL::INT-CADR-TRIPP))
 (9504 96 (:REWRITE DEFAULT-MINUS))
 (5975 664 (:REWRITE DEFAULT-CAR))
 (4235 1682 (:REWRITE DEFAULT-CDR))
 (2230 101 (:REWRITE DEFAULT-TIMES-1))
 (2043 723 (:REWRITE RTL::INTEGERP-EC-X))
 (2043 723 (:REWRITE RTL::INT-CAR-TRIPP))
 (1740 622 (:REWRITE RTL::INT-CADR-TRIPP))
 (1740 12 (:DEFINITION RTL::NORM-EXPT))
 (1224 60 (:REWRITE |(+ x (if a b c))|))
 (1116 20 (:REWRITE DEFAULT-EXPT-1))
 (985 241 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (912 304
      (:TYPE-PRESCRIPTION RTL::ALL-INTEGERS-INTEGER))
 (796 796 (:REWRITE REDUCE-INTEGERP-+))
 (796 796 (:REWRITE INTEGERP-MINUS-X))
 (796 796 (:META META-INTEGERP-CORRECT))
 (784 8 (:REWRITE RTL::NTHCDR+))
 (750 12 (:REWRITE |(< x (if a b c))|))
 (676 338
      (:TYPE-PRESCRIPTION RTL::INT-CADDR-TRIPP))
 (666 3 (:DEFINITION EVENP))
 (629 629 (:REWRITE REDUCE-RATIONALP-+))
 (629 629 (:REWRITE REDUCE-RATIONALP-*))
 (629 629 (:REWRITE RATIONALP-MINUS-X))
 (629 629 (:META META-RATIONALP-CORRECT))
 (548 10 (:REWRITE RTL::EVALH-POW-REWRITE))
 (492 492 (:TYPE-PRESCRIPTION RTL::SHFP))
 (474 12 (:DEFINITION RTL::ALL-INTEGERS))
 (470 18 (:REWRITE |(* (if a b c) x)|))
 (358
   154
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (332 172 (:REWRITE RTL::SHNFP-SHFP))
 (284 284 (:REWRITE THE-FLOOR-BELOW))
 (284 284 (:REWRITE THE-FLOOR-ABOVE))
 (262 154
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (262
  154
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (262 154
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (262 154
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (262 154
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (262
     154
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (251 200
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (250 154
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (250 154
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (241 241
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
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
 (212 19 (:REWRITE |(* y x)|))
 (206 200
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (206 200
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (205 49
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (200 200 (:REWRITE SIMPLIFY-SUMS-<))
 (200 200 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (200 200
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (200 200 (:REWRITE INTEGERP-<-CONSTANT))
 (200 200 (:REWRITE CONSTANT-<-INTEGERP))
 (200 200
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (200 200
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (200 200
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (200 200
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (200 200 (:REWRITE |(< c (- x))|))
 (200 200
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (200 200
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (200 200
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (200 200
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (200 200 (:REWRITE |(< (/ x) (/ y))|))
 (200 200 (:REWRITE |(< (- x) c)|))
 (200 200 (:REWRITE |(< (- x) (- y))|))
 (176 8 (:REWRITE ZIP-OPEN))
 (174 174
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (174 174 (:REWRITE NORMALIZE-ADDENDS))
 (172 92 (:REWRITE RTL::SPLIT$-CASE-5-2))
 (143 13 (:DEFINITION NTH))
 (118 118
      (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (118 118
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE))
 (118 118
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (118 118
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (118 118
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (118 118 (:REWRITE |(< (/ x) 0)|))
 (118 118 (:REWRITE |(< (* x y) 0)|))
 (116 4 (:REWRITE |(expt 0 n)|))
 (114 114
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (114 114
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (114 114
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (114 114
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (108 9 (:REWRITE |(* x (+ y z))|))
 (80 40 (:REWRITE RTL::INT-CADDR-TRIPP))
 (68 20 (:REWRITE DEFAULT-EXPT-2))
 (64 64 (:TYPE-PRESCRIPTION RTL::NORM-POW))
 (52 14 (:REWRITE RTL::ALL-INTEGERS-INTEGER))
 (49 49 (:REWRITE |(< 0 (/ x))|))
 (49 49 (:REWRITE |(< 0 (* x y))|))
 (46 46
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (42 3 (:REWRITE |(+ y (+ x z))|))
 (39 39
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (24 24 (:TYPE-PRESCRIPTION RTL::NORM-POP))
 (24 24 (:TYPE-PRESCRIPTION RTL::NORM-MUL))
 (18 6 (:REWRITE RTL::SHNFP-INT))
 (16 16
     (:TYPE-PRESCRIPTION RTL::SPLIT$-CASE-5-7))
 (16 16 (:REWRITE |(expt 1/c n)|))
 (16 16 (:REWRITE |(expt (- x) n)|))
 (12 12 (:TYPE-PRESCRIPTION NATP))
 (12 12 (:TYPE-PRESCRIPTION ABS))
 (12 12 (:REWRITE |(< y (+ (- c) x))|))
 (12 12 (:REWRITE |(< x (+ c/d y))|))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (8 8 (:REWRITE |(* 1 x)|))
 (8 8 (:REWRITE |(* 0 x)|))
 (6 6
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (3 3 (:REWRITE FOLD-CONSTS-IN-+))
 (3 3 (:REWRITE |(equal (+ (- c) x) y)|)))
(RTL::SPLIT$-CASE-5-25
     (988033 14395 (:REWRITE ACL2-NUMBERP-X))
     (545262 13647 (:REWRITE RATIONALP-X))
     (413631 4543 (:REWRITE DEFAULT-LESS-THAN-2))
     (370152 185076
             (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-Y))
     (345517 345517 (:TYPE-PRESCRIPTION RTL::ECP))
     (313143 9406 (:REWRITE DEFAULT-PLUS-1))
     (295094 295094 (:TYPE-PRESCRIPTION RTL::TRIPP))
     (289087 3935 (:REWRITE DEFAULT-LESS-THAN-1))
     (265954 133005
             (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-X))
     (265954 133005
             (:TYPE-PRESCRIPTION RTL::INT-CAR-TRIPP))
     (240768 2432 (:REWRITE DEFAULT-MINUS))
     (235481 3224
             (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (221086 110543
             (:TYPE-PRESCRIPTION RTL::INT-CADR-TRIPP))
     (179616 10154 (:REWRITE DEFAULT-PLUS-2))
     (114826 7968 (:REWRITE DEFAULT-CAR))
     (50900 13224 (:REWRITE DEFAULT-CDR))
     (41238 13746 (:REWRITE RTL::INTEGERP-EC-X))
     (41238 13746 (:REWRITE RTL::INT-CAR-TRIPP))
     (39466 1456 (:REWRITE DEFAULT-TIMES-1))
     (35301 11767 (:REWRITE RTL::INT-CADR-TRIPP))
     (30720 1496 (:REWRITE |(+ x (if a b c))|))
     (22072 3224 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (17500 280 (:REWRITE |(< x (if a b c))|))
     (14031 14031 (:REWRITE REDUCE-INTEGERP-+))
     (14031 14031 (:REWRITE INTEGERP-MINUS-X))
     (14031 14031 (:META META-INTEGERP-CORRECT))
     (13647 13647 (:REWRITE REDUCE-RATIONALP-+))
     (13647 13647 (:REWRITE REDUCE-RATIONALP-*))
     (13647 13647 (:REWRITE RATIONALP-MINUS-X))
     (13647 13647 (:META META-RATIONALP-CORRECT))
     (10180 57 (:REWRITE RTL::SPLIT$-CASE-5-2))
     (4543 4543 (:REWRITE THE-FLOOR-BELOW))
     (4543 4543 (:REWRITE THE-FLOOR-ABOVE))
     (4060 140 (:REWRITE |(* (if a b c) x)|))
     (3547 2427
           (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (3224 3224
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (3224 3224
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (3224 3224
           (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (3224 3224 (:REWRITE |(equal c (/ x))|))
     (3224 3224 (:REWRITE |(equal c (- x))|))
     (3224 3224 (:REWRITE |(equal (/ x) c)|))
     (3224 3224 (:REWRITE |(equal (/ x) (/ y))|))
     (3224 3224 (:REWRITE |(equal (- x) c)|))
     (3224 3224 (:REWRITE |(equal (- x) (- y))|))
     (3055 3055
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (3055 3055
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (3055 3055
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (2786 2786
           (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (2579 2439
           (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (2579 2439
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (2498 1218 (:REWRITE RTL::SHNFP-INT))
     (2439 2439
           (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (2439 2439 (:REWRITE INTEGERP-<-CONSTANT))
     (2439 2439 (:REWRITE CONSTANT-<-INTEGERP))
     (2439 2439
           (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (2439 2439
           (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (2439 2439
           (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (2439 2439
           (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (2439 2439 (:REWRITE |(< c (- x))|))
     (2439 2439
           (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (2439 2439
           (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (2439 2439
           (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (2439 2439
           (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (2439 2439 (:REWRITE |(< (/ x) (/ y))|))
     (2439 2439 (:REWRITE |(< (- x) c)|))
     (2439 2439 (:REWRITE |(< (- x) (- y))|))
     (1456 1456 (:REWRITE DEFAULT-TIMES-2))
     (1216 1216 (:REWRITE |(+ 0 x)|))
     (1040 520
           (:TYPE-PRESCRIPTION RTL::INT-CADDR-TRIPP))
     (1006 1006 (:REWRITE |(< 0 (/ x))|))
     (1006 1006 (:REWRITE |(< 0 (* x y))|))
     (927 927
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (848 608 (:TYPE-PRESCRIPTION RTL::NORM-POP))
     (720 172 (:REWRITE RTL::SHNFP-POW-P))
     (715 715
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (688 688
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (688 688
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (688 688 (:REWRITE |(< (/ x) 0)|))
     (688 688 (:REWRITE |(< (* x y) 0)|))
     (464 72 (:REWRITE RTL::SHNFP-POW-Q))
     (286 286 (:REWRITE |(< y (+ (- c) x))|))
     (286 286 (:REWRITE |(< x (+ c/d y))|))
     (280 280 (:TYPE-PRESCRIPTION ABS))
     (244 244 (:REWRITE RTL::P-NAT))
     (244 244 (:REWRITE RTL::NATP-Y2))
     (244 244 (:REWRITE RTL::NATP-Y1))
     (244 244 (:REWRITE RTL::NATP-Y0))
     (244 244 (:REWRITE RTL::NATP-X2))
     (244 244 (:REWRITE RTL::NATP-X1))
     (244 244 (:REWRITE RTL::NATP-X0))
     (244 244 (:REWRITE RTL::NATP-P-1/2))
     (160 160 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (153 17
          (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (140 140
          (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (84 28 (:REWRITE RTL::INT-CADDR-TRIPP))
     (17 17 (:REWRITE FOLD-CONSTS-IN-+))
     (17 17 (:REWRITE |(equal (+ (- c) x) y)|)))
(RTL::SPLIT$-CASE-5 (624 624 (:DEFINITION MV-NTH)))
(RTL::SPLIT$-CASE-4-1
     (22 2 (:DEFINITION NTH))
     (11 1 (:DEFINITION NTHCDR))
     (6 3 (:REWRITE DEFAULT-CDR))
     (5 1 (:REWRITE |(+ y x)|))
     (4 4 (:REWRITE DEFAULT-PLUS-2))
     (4 4 (:REWRITE DEFAULT-PLUS-1))
     (4 2 (:REWRITE DEFAULT-CAR))
     (4 1 (:REWRITE RTL::SHNFP-INT))
     (3 3 (:REWRITE ZP-OPEN))
     (3 3
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (3 3 (:REWRITE NORMALIZE-ADDENDS))
     (2 2 (:REWRITE THE-FLOOR-BELOW))
     (2 2 (:REWRITE THE-FLOOR-ABOVE))
     (2 2 (:REWRITE SIMPLIFY-SUMS-<))
     (2 2 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (2 2 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (2 2
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (2 2
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (2 2 (:REWRITE REDUCE-INTEGERP-+))
     (2 2 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (2 2 (:REWRITE INTEGERP-MINUS-X))
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
     (2 2 (:META META-INTEGERP-CORRECT))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (1 1 (:REWRITE |(< (/ x) 0)|))
     (1 1 (:REWRITE |(< (* x y) 0)|)))
(RTL::SPLIT$-CASE-4-2
 (404
  272
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (388 63 (:REWRITE DEFAULT-PLUS-2))
 (272 272
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (272 272
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (272
     272
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (272 272
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (272 272
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (230 63 (:REWRITE DEFAULT-PLUS-1))
 (203 38 (:REWRITE DEFAULT-TIMES-2))
 (107 107
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (107 107
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (107 107
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (81 38 (:REWRITE DEFAULT-TIMES-1))
 (72 5
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (26 26
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (15 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (15 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (15 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (15 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (13 13 (:REWRITE REDUCE-INTEGERP-+))
 (13 13 (:REWRITE INTEGERP-MINUS-X))
 (13 13 (:META META-INTEGERP-CORRECT))
 (8 8
    (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (8 8 (:REWRITE FOLD-CONSTS-IN-+))
 (8 8 (:REWRITE DEFAULT-EXPT-2))
 (8 8 (:REWRITE DEFAULT-EXPT-1))
 (8 8 (:REWRITE |(expt 1/c n)|))
 (8 8 (:REWRITE |(expt (- x) n)|))
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
 (4 4 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (2 2 (:REWRITE THE-FLOOR-BELOW))
 (2 2 (:REWRITE THE-FLOOR-ABOVE))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2 (:REWRITE SIMPLIFY-SUMS-<))
 (2 2 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (2 2 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (2 2
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (2 2
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
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
 (2 2
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (2 2
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (2 2
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (2 2
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (2 2 (:REWRITE |(< (/ x) 0)|))
 (2 2 (:REWRITE |(< (/ x) (/ y))|))
 (2 2 (:REWRITE |(< (- x) c)|))
 (2 2 (:REWRITE |(< (- x) (- y))|))
 (2 2 (:REWRITE |(< (* x y) 0)|))
 (2 2 (:REWRITE |(* c (expt d n))|))
 (1 1 (:REWRITE ZIP-OPEN))
 (1 1 (:REWRITE |(equal (+ (- c) x) y)|))
 (1 1 (:REWRITE |(equal (* x y) 0)|)))
(RTL::SPLIT$-CASE-4-3 (672 672 (:DEFINITION MV-NTH)))
(RTL::SPLIT$-CASE-4-4
     (272479 18 (:REWRITE MOD-X-Y-=-X-Y . 1))
     (143284 319
             (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (137069 18 (:REWRITE MOD-X-Y-=-X+Y . 1))
     (96265 225 (:REWRITE MOD-ZERO . 3))
     (89407 17951 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (89407 17951 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (88219 17951
            (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (88219 17951
            (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (75092 75092
            (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (75092 75092
            (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (75092 75092
            (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (67260 228 (:REWRITE DEFAULT-MOD-RATIO))
     (50065 3714 (:REWRITE DEFAULT-TIMES-2))
     (47579 225 (:REWRITE MOD-X-Y-=-X . 4))
     (47579 225 (:REWRITE MOD-X-Y-=-X . 3))
     (47559 225 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (42203 225 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (40637 225 (:REWRITE RTL::MOD-DOES-NOTHING))
     (40378 225 (:REWRITE MOD-ZERO . 4))
     (38967 1928 (:REWRITE DEFAULT-PLUS-2))
     (38495 1868 (:META META-INTEGERP-CORRECT))
     (37298 64 (:LINEAR MOD-BOUNDS-3))
     (34188 11034
            (:TYPE-PRESCRIPTION RTL::NATP-MOD))
     (31562 1189
            (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (25433 1193 (:REWRITE DEFAULT-LESS-THAN-1))
     (20128 3714 (:REWRITE DEFAULT-TIMES-1))
     (19323 1928 (:REWRITE DEFAULT-PLUS-1))
     (17951 17951 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (17951 17951
            (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (17951 17951
            (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (17951 17951
            (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (13726 64 (:LINEAR RTL::MOD-BND-2))
     (13187 225 (:REWRITE MOD-X-Y-=-X . 2))
     (11034 11034
            (:TYPE-PRESCRIPTION RTL::NATP-MOD-2))
     (11034 11034 (:TYPE-PRESCRIPTION NATP))
     (8351 225 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (8351 225 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (7901 7901
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (7901 7901
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (7164 228 (:REWRITE DEFAULT-MOD-1))
     (7008 1193 (:REWRITE DEFAULT-LESS-THAN-2))
     (6154 214
           (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 3))
     (5679 225
           (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (5679 225
           (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (5679 225
           (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (5208 128 (:LINEAR MOD-BOUNDS-2))
     (3950 214
           (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 1))
     (2840 2840
           (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (2778 225
           (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (2778 225
           (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (2778 225
           (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (2457 313 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (2270 1870 (:REWRITE INTEGERP-MINUS-X))
     (2158 214
           (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 2))
     (1652 11 (:REWRITE |(integerp (- x))|))
     (1514 1514 (:REWRITE |(* c (* d x))|))
     (1512 54 (:REWRITE DEFAULT-MINUS))
     (1381 1381
           (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (1193 1193 (:REWRITE THE-FLOOR-BELOW))
     (1193 1193 (:REWRITE THE-FLOOR-ABOVE))
     (1192 1192
           (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (1192 1192
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (1191 1190
           (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (1190 1190 (:REWRITE INTEGERP-<-CONSTANT))
     (1190 1190 (:REWRITE CONSTANT-<-INTEGERP))
     (1190 1190
           (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (1190 1190
           (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (1190 1190
           (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (1190 1190
           (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (1190 1190 (:REWRITE |(< c (- x))|))
     (1190 1190
           (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (1190 1190
           (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (1190 1190
           (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (1190 1190
           (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (1190 1190 (:REWRITE |(< (/ x) (/ y))|))
     (1190 1190 (:REWRITE |(< (- x) c)|))
     (1190 1190 (:REWRITE |(< (- x) (- y))|))
     (834 567 (:REWRITE DEFAULT-DIVIDE))
     (823 823 (:REWRITE |(< (+ c/d x) y)|))
     (750 750 (:REWRITE INTEGERP-/))
     (704 704 (:REWRITE |(+ c (+ d x))|))
     (677 677 (:REWRITE FOLD-CONSTS-IN-+))
     (591 18
          (:REWRITE |(equal (mod (+ x y) z) x)|))
     (566 566
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (485 485 (:REWRITE |(< (* x y) 0)|))
     (484 484 (:REWRITE |(< (/ x) 0)|))
     (483 483
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (483 483
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (347 228 (:REWRITE DEFAULT-MOD-2))
     (322 319 (:REWRITE |(equal (- x) (- y))|))
     (319 319
          (:TYPE-PRESCRIPTION RTL::RATIONALP-MOD))
     (319 319
          (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
     (319 319
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (319 319
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (319 319
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (319 319 (:REWRITE |(equal c (/ x))|))
     (319 319 (:REWRITE |(equal c (- x))|))
     (319 319 (:REWRITE |(equal (/ x) c)|))
     (319 319 (:REWRITE |(equal (/ x) (/ y))|))
     (319 319 (:REWRITE |(equal (- x) c)|))
     (293 293
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (293 293
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (293 293
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (293 293 (:REWRITE |(< 0 (/ x))|))
     (293 293 (:REWRITE |(< 0 (* x y))|))
     (260 260
          (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (225 225 (:REWRITE |(mod x (- y))| . 3))
     (225 225 (:REWRITE |(mod x (- y))| . 2))
     (225 225 (:REWRITE |(mod x (- y))| . 1))
     (205 205 (:REWRITE |(equal (+ (- c) x) y)|))
     (189 189 (:REWRITE |(< y (+ (- c) x))|))
     (189 189 (:REWRITE |(< x (+ c/d y))|))
     (126 46 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (64 64 (:LINEAR RTL::MOD-BND-3))
     (54 6 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (54 6
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (54 6
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (54 6
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (54 6
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (30 6 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (30 6 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (30 6
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (30 6
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (30 6
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (30 6
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (30 6
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (30 6
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (30 6
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (30 6
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (29 29 (:REWRITE |(- (* c x))|))
     (2 2
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (1 1
        (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|)))
(RTL::SPLIT$-CASE-4-5
 (10168 26 (:REWRITE |(* y x)|))
 (8788 464
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (8742 52 (:REWRITE |(* x (+ y z))|))
 (7926 12 (:REWRITE MOD-ZERO . 3))
 (6328 12 (:REWRITE DEFAULT-MOD-RATIO))
 (4670 934 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (4670 934 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (4670 934
       (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (4670 934
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (4124 104 (:REWRITE DEFAULT-PLUS-2))
 (4015 4015
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (4015 4015
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (4015 4015
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (3834 12 (:REWRITE MOD-X-Y-=-X . 4))
 (3834 12 (:REWRITE MOD-X-Y-=-X . 3))
 (3528 26 (:REWRITE |(+ y (+ x z))|))
 (3512 4 (:LINEAR MOD-BOUNDS-3))
 (3432 12 (:REWRITE MOD-ZERO . 4))
 (3422 156 (:REWRITE DEFAULT-TIMES-2))
 (3412 12 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (3392 12 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (2864 12 (:REWRITE RTL::MOD-DOES-NOTHING))
 (2756 84 (:META META-INTEGERP-CORRECT))
 (2626 64 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (2116 64 (:REWRITE DEFAULT-LESS-THAN-1))
 (1954 1954
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (1954
  1954
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1954 1954
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (1954 1954
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (1954
      1954
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1954
     1954
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1954 1954
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1954 1954
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (1920 104 (:REWRITE DEFAULT-PLUS-1))
 (1780 890 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
 (1582 156 (:REWRITE DEFAULT-TIMES-1))
 (1258 4 (:LINEAR RTL::MOD-BND-2))
 (1172 12 (:REWRITE MOD-X-Y-=-X . 2))
 (934 934 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (934 934
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (934 934
      (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (934 934
      (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
 (934 934
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (934 934 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (914 12
      (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 1))
 (890 890
      (:TYPE-PRESCRIPTION RTL::NATP-MOD-2))
 (890 890 (:TYPE-PRESCRIPTION NATP))
 (708 12 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (708 12 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (696 12
      (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (696 12
      (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (696 12
      (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (632 12 (:REWRITE DEFAULT-MOD-1))
 (558 64 (:REWRITE DEFAULT-LESS-THAN-2))
 (494 20
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (472 8 (:LINEAR MOD-BOUNDS-2))
 (464 464
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (464 464
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (464 464
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (130 130
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (84 84 (:REWRITE REDUCE-INTEGERP-+))
 (84 84 (:REWRITE INTEGERP-MINUS-X))
 (78 78
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (78 78 (:REWRITE NORMALIZE-ADDENDS))
 (64 64 (:REWRITE THE-FLOOR-BELOW))
 (64 64 (:REWRITE THE-FLOOR-ABOVE))
 (64 64 (:REWRITE SIMPLIFY-SUMS-<))
 (64 64
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (64 64
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (64 64
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
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
 (52 52 (:REWRITE |(* c (* d x))|))
 (52 26 (:REWRITE DEFAULT-DIVIDE))
 (44 44 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (44 44 (:REWRITE |(< (+ c/d x) y)|))
 (44 44 (:REWRITE |(< (+ (- c) x) y)|))
 (28 28 (:REWRITE INTEGERP-/))
 (26 26
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (26 26 (:REWRITE FOLD-CONSTS-IN-+))
 (26 26 (:REWRITE |(+ c (+ d x))|))
 (24 24
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (24 24
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (24 24 (:REWRITE |(< (/ x) 0)|))
 (24 24 (:REWRITE |(< (* x y) 0)|))
 (24 12 (:REWRITE DEFAULT-MOD-2))
 (20 20
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (20 20
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (20 20
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (20 20 (:REWRITE SIMPLIFY-SUMS-EQUAL))
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
 (20 20 (:REWRITE |(< 0 (/ x))|))
 (20 20 (:REWRITE |(< 0 (* x y))|))
 (14 14
     (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (12 12
     (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (12 12 (:REWRITE |(mod x (- y))| . 3))
 (12 12 (:REWRITE |(mod x (- y))| . 2))
 (12 12 (:REWRITE |(mod x (- y))| . 1))
 (12 12
     (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (12 12
     (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 3))
 (12 12
     (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 2))
 (12 12
     (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (10 10 (:REWRITE |(equal (+ (- c) x) y)|))
 (10 10 (:REWRITE |(< y (+ (- c) x))|))
 (10 10 (:REWRITE |(< x (+ c/d y))|))
 (9 9
    (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
 (4 4 (:LINEAR RTL::MOD-BND-3)))
(RTL::SPLIT$-CASE-4-6 (312 312 (:DEFINITION MV-NTH)))
(RTL::SPLIT$-CASE-4-7
     (37 37 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (37 37 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (37 37 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (23 23 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (23 23 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (23 23 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (16 16 (:REWRITE DEFAULT-TIMES-2))
     (16 16 (:REWRITE DEFAULT-TIMES-1))
     (10 10
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (9 9
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (9 9 (:REWRITE NORMALIZE-ADDENDS))
     (9 9 (:REWRITE DEFAULT-PLUS-2))
     (9 9 (:REWRITE DEFAULT-PLUS-1))
     (7 7 (:REWRITE THE-FLOOR-BELOW))
     (7 7 (:REWRITE THE-FLOOR-ABOVE))
     (7 7 (:REWRITE DEFAULT-LESS-THAN-2))
     (7 7 (:REWRITE DEFAULT-LESS-THAN-1))
     (7 7 (:REWRITE |(< (* x y) 0)|))
     (6 6 (:REWRITE SIMPLIFY-SUMS-<))
     (6 6 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (6 6 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (6 6
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (6 6
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
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
     (6 6 (:REWRITE |(< (/ x) 0)|))
     (6 6 (:REWRITE |(< (/ x) (/ y))|))
     (6 6 (:REWRITE |(< (- x) c)|))
     (6 6 (:REWRITE |(< (- x) (- y))|))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (4 4 (:REWRITE REDUCE-INTEGERP-+))
     (4 4 (:REWRITE INTEGERP-MINUS-X))
     (4 4 (:REWRITE |(< (+ (- c) x) y)|))
     (4 4 (:META META-INTEGERP-CORRECT)))
(RTL::SPLIT$-CASE-4-8
 (1244 22 (:LINEAR EXPT-<=-1-ONE))
 (1224 22 (:LINEAR EXPT->=-1-TWO))
 (1224 22 (:LINEAR EXPT->-1-TWO))
 (1224 22 (:LINEAR EXPT-<-1-ONE))
 (1164 22 (:LINEAR EXPT-X->=-X))
 (1164 22 (:LINEAR EXPT->=-1-ONE))
 (1164 22 (:LINEAR EXPT-<=-1-TWO))
 (1144 22 (:LINEAR EXPT-X->-X))
 (1144 22 (:LINEAR EXPT->-1-ONE))
 (1144 22 (:LINEAR EXPT-<-1-TWO))
 (421 221
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (341 221 (:REWRITE DEFAULT-LESS-THAN-2))
 (301 221 (:REWRITE DEFAULT-LESS-THAN-1))
 (224 208
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (224 208
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (221 221 (:REWRITE THE-FLOOR-BELOW))
 (221 221 (:REWRITE THE-FLOOR-ABOVE))
 (221 221 (:REWRITE SIMPLIFY-SUMS-<))
 (221 221
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (221 221
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (221 221
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (221 221 (:REWRITE INTEGERP-<-CONSTANT))
 (221 221 (:REWRITE CONSTANT-<-INTEGERP))
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
 (221 221 (:REWRITE |(< (- x) c)|))
 (221 221 (:REWRITE |(< (- x) (- y))|))
 (208 208
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (208
  208
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (208 208
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (208 208
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (208 208
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (208
     208
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (89 89 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (66 66
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (66 66
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (66 66 (:REWRITE |(< 0 (/ x))|))
 (66 66 (:REWRITE |(< 0 (* x y))|))
 (54 54 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (54 54 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (54 54 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (44 44
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (44 44
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (44 44
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (44 44
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (23 23
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (23 23
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (23 23 (:REWRITE |(< (/ x) 0)|))
 (23 23 (:REWRITE |(< (* x y) 0)|))
 (22 22 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (22 22 (:LINEAR EXPT-LINEAR-UPPER-<))
 (22 22 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (22 22 (:LINEAR EXPT-LINEAR-LOWER-<))
 (14 4 (:REWRITE DEFAULT-EXPT-1))
 (9 9 (:REWRITE DEFAULT-TIMES-2))
 (9 9 (:REWRITE DEFAULT-TIMES-1))
 (8 4 (:REWRITE DEFAULT-EXPT-2))
 (6 6
    (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (4 4
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (4 4
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (4 4 (:REWRITE NORMALIZE-ADDENDS))
 (4 4 (:REWRITE DEFAULT-PLUS-2))
 (4 4 (:REWRITE DEFAULT-PLUS-1))
 (3 3 (:REWRITE REDUCE-INTEGERP-+))
 (3 3 (:REWRITE INTEGERP-MINUS-X))
 (3 3 (:REWRITE |(expt 1/c n)|))
 (3 3 (:REWRITE |(expt (- x) n)|))
 (3 3 (:META META-INTEGERP-CORRECT)))
(RTL::SPLIT$-CASE-4-9
 (219093 273 (:REWRITE RTL::MOD-DOES-NOTHING))
 (61236 1626 (:LINEAR EXPT-<=-1-ONE))
 (46954 1626 (:LINEAR EXPT->=-1-TWO))
 (46954 1626 (:LINEAR EXPT->-1-TWO))
 (46954 1626 (:LINEAR EXPT-<-1-ONE))
 (45186 1626 (:LINEAR EXPT-X->=-X))
 (45186 1626 (:LINEAR EXPT->=-1-ONE))
 (45186 1626 (:LINEAR EXPT-<=-1-TWO))
 (44908 1626 (:LINEAR EXPT-X->-X))
 (44908 1626 (:LINEAR EXPT->-1-ONE))
 (44908 1626 (:LINEAR EXPT-<-1-TWO))
 (37773 273 (:REWRITE MOD-ZERO . 4))
 (35247 273 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (34097 273 (:REWRITE MOD-X-Y-=-X . 4))
 (34097 273 (:REWRITE MOD-X-Y-=-X . 3))
 (32127 273 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (22203 4253
        (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (19508 18204
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (19508 18204
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (19097 273 (:REWRITE MOD-ZERO . 3))
 (18204 18204
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (18204
  18204
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (18204 18204
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (18204
      18204
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (18204
     18204
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (17826 1540 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
 (16139 4253 (:REWRITE DEFAULT-LESS-THAN-1))
 (14223 273 (:REWRITE DEFAULT-MOD-RATIO))
 (12481 950
        (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (11084 11084
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (11084 11084
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (11084 11084
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (9729 4253 (:REWRITE DEFAULT-LESS-THAN-2))
 (9613 4253 (:REWRITE SIMPLIFY-SUMS-<))
 (8782 1229 (:REWRITE DEFAULT-TIMES-2))
 (8782 1229 (:REWRITE DEFAULT-TIMES-1))
 (8200 1640 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (8200 1640 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (8176 1640
       (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (8176 1640
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (8064 92 (:LINEAR MOD-BOUNDS-3))
 (7912 273 (:REWRITE MOD-X-Y-=-X . 2))
 (5420 220 (:REWRITE |(equal (expt x n) 0)|))
 (5153 273 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (5153 273 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (4253 4253 (:REWRITE THE-FLOOR-BELOW))
 (4253 4253 (:REWRITE THE-FLOOR-ABOVE))
 (4253 4253
       (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (4253 4253
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (4253 4253
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (4253 4253 (:REWRITE INTEGERP-<-CONSTANT))
 (4253 4253 (:REWRITE CONSTANT-<-INTEGERP))
 (4253 4253
       (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (4253 4253
       (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (4253 4253
       (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (4253 4253
       (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (4253 4253 (:REWRITE |(< c (- x))|))
 (4253 4253
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (4253 4253
       (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (4253 4253
       (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (4253 4253
       (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (4253 4253 (:REWRITE |(< (/ x) (/ y))|))
 (4253 4253 (:REWRITE |(< (- x) c)|))
 (4253 4253 (:REWRITE |(< (- x) (- y))|))
 (4113 273
       (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (4113 273
       (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (4113 273
       (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (3467 273 (:REWRITE DEFAULT-MOD-1))
 (3384 184 (:LINEAR MOD-BOUNDS-2))
 (3252 3252
       (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (3252 3252
       (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (3252 3252
       (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (3252 3252
       (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (2280 24 (:REWRITE MOD-POSITIVE . 3))
 (1977 1977
       (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (1640 1640 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (1640 1640
       (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (1640 1640
       (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (1640 1640
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (1640 1640
       (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (1626 1626 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (1626 1626 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1626 1626 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (1626 1626 (:LINEAR EXPT-LINEAR-LOWER-<))
 (1540 1540
       (:TYPE-PRESCRIPTION RTL::NATP-MOD-2))
 (1218 609 (:REWRITE DEFAULT-DIVIDE))
 (1146 1146
       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (1146 1146
       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (1146 1146 (:REWRITE |(< 0 (/ x))|))
 (1146 1146 (:REWRITE |(< 0 (* x y))|))
 (1102 619
       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (1040 273
       (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (1040 273
       (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (1040 273
       (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (950 950
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (950 950
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (950 950
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (835 835
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (835 835
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (835 835 (:REWRITE |(equal c (/ x))|))
 (835 835 (:REWRITE |(equal c (- x))|))
 (835 835 (:REWRITE |(equal (/ x) c)|))
 (835 835 (:REWRITE |(equal (/ x) (/ y))|))
 (835 835 (:REWRITE |(equal (- x) c)|))
 (835 835 (:REWRITE |(equal (- x) (- y))|))
 (823 823
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (823 823
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (823 823 (:REWRITE |(< (/ x) 0)|))
 (823 823 (:REWRITE |(< (* x y) 0)|))
 (619 619
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (619 619 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (619 619
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (613 613
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (609 609
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (546 273 (:REWRITE DEFAULT-MOD-2))
 (498 24 (:REWRITE MOD-POSITIVE . 2))
 (368 8 (:REWRITE ZP-OPEN))
 (359 359 (:REWRITE REDUCE-INTEGERP-+))
 (359 359 (:REWRITE INTEGERP-MINUS-X))
 (359 359 (:META META-INTEGERP-CORRECT))
 (273 273 (:REWRITE |(mod x (- y))| . 3))
 (273 273 (:REWRITE |(mod x (- y))| . 2))
 (273 273 (:REWRITE |(mod x (- y))| . 1))
 (268 8 (:REWRITE RTL::MOD-EXPT-REWRITE-2))
 (268 8 (:REWRITE RTL::MOD-EXPT-REWRITE-1))
 (108 8 (:REWRITE MOD-THEOREM-TWO))
 (84 84 (:LINEAR RTL::MOD-BND-3))
 (68 5 (:REWRITE DEFAULT-EXPT-1))
 (24 24 (:REWRITE MOD-POSITIVE . 1))
 (13 13
     (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
 (13 5 (:REWRITE DEFAULT-EXPT-2))
 (8 8 (:TYPE-PRESCRIPTION ZP))
 (8 8
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (8 8
    (:REWRITE |(< 0 (* x (/ y))) rationalp (* x (/ y))|))
 (6 6
    (:TYPE-PRESCRIPTION RTL::RATIONALP-MOD))
 (6 6
    (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (4 4
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (4 4 (:REWRITE NORMALIZE-ADDENDS))
 (4 4 (:REWRITE DEFAULT-PLUS-2))
 (4 4 (:REWRITE DEFAULT-PLUS-1))
 (4 4 (:REWRITE |(expt 1/c n)|))
 (4 4 (:REWRITE |(expt (- x) n)|)))
(RTL::SPLIT$-CASE-4-10
 (1244 22 (:LINEAR EXPT-<=-1-ONE))
 (1224 22 (:LINEAR EXPT->=-1-TWO))
 (1224 22 (:LINEAR EXPT->-1-TWO))
 (1224 22 (:LINEAR EXPT-<-1-ONE))
 (1164 22 (:LINEAR EXPT-X->=-X))
 (1164 22 (:LINEAR EXPT->=-1-ONE))
 (1164 22 (:LINEAR EXPT-<=-1-TWO))
 (1144 22 (:LINEAR EXPT-X->-X))
 (1144 22 (:LINEAR EXPT->-1-ONE))
 (1144 22 (:LINEAR EXPT-<-1-TWO))
 (421 221
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (341 221 (:REWRITE DEFAULT-LESS-THAN-2))
 (301 221 (:REWRITE DEFAULT-LESS-THAN-1))
 (224 208
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (224 208
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (221 221 (:REWRITE THE-FLOOR-BELOW))
 (221 221 (:REWRITE THE-FLOOR-ABOVE))
 (221 221 (:REWRITE SIMPLIFY-SUMS-<))
 (221 221
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (221 221
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (221 221
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (221 221 (:REWRITE INTEGERP-<-CONSTANT))
 (221 221 (:REWRITE CONSTANT-<-INTEGERP))
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
 (221 221 (:REWRITE |(< (- x) c)|))
 (221 221 (:REWRITE |(< (- x) (- y))|))
 (208 208
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (208
  208
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (208 208
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (208 208
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (208 208
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (208
     208
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (89 89 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (66 66
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (66 66
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (66 66 (:REWRITE |(< 0 (/ x))|))
 (66 66 (:REWRITE |(< 0 (* x y))|))
 (54 54 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (54 54 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (54 54 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (44 44
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (44 44
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (44 44
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (44 44
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (23 23
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (23 23
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (23 23 (:REWRITE |(< (/ x) 0)|))
 (23 23 (:REWRITE |(< (* x y) 0)|))
 (22 22 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (22 22 (:LINEAR EXPT-LINEAR-UPPER-<))
 (22 22 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (22 22 (:LINEAR EXPT-LINEAR-LOWER-<))
 (14 4 (:REWRITE DEFAULT-EXPT-1))
 (13 4 (:REWRITE DEFAULT-EXPT-2))
 (9 9 (:REWRITE DEFAULT-TIMES-2))
 (9 9 (:REWRITE DEFAULT-TIMES-1))
 (6 6
    (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (6 6
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (6 6 (:REWRITE NORMALIZE-ADDENDS))
 (6 6 (:REWRITE DEFAULT-PLUS-2))
 (6 6 (:REWRITE DEFAULT-PLUS-1))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (4 4
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (3 3 (:REWRITE REDUCE-INTEGERP-+))
 (3 3 (:REWRITE INTEGERP-MINUS-X))
 (3 3 (:REWRITE |(expt 1/c n)|))
 (3 3 (:REWRITE |(expt (- x) n)|))
 (3 3 (:META META-INTEGERP-CORRECT)))
(RTL::SPLIT$-CASE-4-11)
(RTL::SPLIT$-CASE-4-12
 (38 38 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (38 38 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (38 38 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (26 26 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (26 26 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (26 26 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (26 26 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (13 13
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (13
   13
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (13
  13
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (13 13
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (13 13
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (13 13
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (13 13
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (13 13
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (13 13
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (10 10 (:REWRITE DEFAULT-TIMES-2))
 (10 10 (:REWRITE DEFAULT-TIMES-1))
 (6 6 (:REWRITE REDUCE-INTEGERP-+))
 (6 6
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (6 6
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (6 6 (:REWRITE NORMALIZE-ADDENDS))
 (6 6 (:REWRITE INTEGERP-MINUS-X))
 (6 6 (:REWRITE DEFAULT-PLUS-2))
 (6 6 (:REWRITE DEFAULT-PLUS-1))
 (6 6 (:META META-INTEGERP-CORRECT))
 (5 5 (:REWRITE THE-FLOOR-BELOW))
 (5 5 (:REWRITE THE-FLOOR-ABOVE))
 (5 5 (:REWRITE DEFAULT-LESS-THAN-2))
 (5 5 (:REWRITE DEFAULT-LESS-THAN-1))
 (5 5 (:REWRITE |(< (* x y) 0)|))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4 (:REWRITE SIMPLIFY-SUMS-<))
 (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (4 4 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (4 4
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (4 4
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
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
 (4 4 (:REWRITE |(< (/ x) 0)|))
 (4 4 (:REWRITE |(< (/ x) (/ y))|))
 (4 4 (:REWRITE |(< (- x) c)|))
 (4 4 (:REWRITE |(< (- x) (- y))|))
 (3 3
    (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE))
 (2 2 (:REWRITE |(< (+ (- c) x) y)|))
 (1 1 (:REWRITE DEFAULT-EXPT-2))
 (1 1 (:REWRITE DEFAULT-EXPT-1))
 (1 1 (:REWRITE |(expt 1/c n)|))
 (1 1 (:REWRITE |(expt (- x) n)|)))
(RTL::SPLIT$-CASE-4-13)
(RTL::SPLIT$-CASE-4-14
 (206919 726 (:REWRITE RATIONALP-X))
 (198381 504 (:REWRITE RTL::INTEGERP-EVALH))
 (195861 504 (:DEFINITION RTL::SHFP))
 (182703 522 (:REWRITE ACL2-NUMBERP-X))
 (111285 45 (:DEFINITION RTL::EVALH))
 (63738 2034 (:REWRITE DEFAULT-TIMES-1))
 (53379 723 (:REWRITE DEFAULT-PLUS-2))
 (47688 2079 (:REWRITE DEFAULT-TIMES-2))
 (37926 16281
        (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-Y))
 (32838 726 (:REWRITE REDUCE-RATIONALP-*))
 (30858 30858 (:TYPE-PRESCRIPTION RTL::ECP))
 (30675 1761
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (29619 12939
        (:TYPE-PRESCRIPTION RTL::INT-CAR-TRIPP))
 (27144 144 (:DEFINITION RFIX))
 (25878 12939
        (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-X))
 (25053 25053 (:TYPE-PRESCRIPTION RTL::TRIPP))
 (24984 48 (:LINEAR MOD-BOUNDS-2))
 (24354 7758
        (:TYPE-PRESCRIPTION RTL::SPLIT$-CASE-5-2))
 (22827 21 (:REWRITE MOD-X-Y-=-X-Y . 1))
 (20076 20076 (:TYPE-PRESCRIPTION RTL::THETA))
 (18987 13119 (:REWRITE DEFAULT-CDR))
 (16203 1914 (:REWRITE DEFAULT-LESS-THAN-1))
 (16110 129 (:REWRITE RTL::MOD-DOES-NOTHING))
 (15516 7758
        (:TYPE-PRESCRIPTION RTL::INT-CADR-TRIPP))
 (13662 6765
        (:TYPE-PRESCRIPTION RTL::ALL-INTEGERS-INTEGER))
 (13398 129 (:REWRITE MOD-X-Y-=-X . 3))
 (12774 24 (:LINEAR MOD-BOUNDS-3))
 (12681 129 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (11742 129 (:REWRITE MOD-X-Y-=-X . 4))
 (11391 1971 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (11391 1971 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (11004 21 (:REWRITE MOD-X-Y-=-X+Y . 1))
 (10782 10782 (:TYPE-PRESCRIPTION RTL::SHNFP))
 (10197 129 (:REWRITE MOD-ZERO . 4))
 (8163 3384 (:REWRITE DEFAULT-CAR))
 (7833 6591
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (7833
  6591
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (7833 6591
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (7833
      6591
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (7833
     6591
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (7545 129 (:REWRITE MOD-ZERO . 3))
 (7329 7329
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (7329 7329
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (7329 7329
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (6765 6765
       (:TYPE-PRESCRIPTION RTL::ALL-INTEGERS))
 (6699 1971
       (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (6699 1971
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (6591 6591
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (6591 6591
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (6402 1740 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (6048 6048 (:TYPE-PRESCRIPTION RTL::SHFP))
 (5679 1899
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (4743 129 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (4623 1899 (:REWRITE SIMPLIFY-SUMS-<))
 (4320 45 (:REWRITE RTL::EVALH-POW-REWRITE))
 (4032 2016 (:REWRITE RTL::SHNFP-SHFP))
 (3960 45 (:DEFINITION EQL))
 (3870 678 (:REWRITE DEFAULT-PLUS-1))
 (3507 1971 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (3507 1971
       (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (3507 1971
       (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (3507 1971
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (3507 1971
       (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (3465 90 (:REWRITE |(+ (if a b c) x)|))
 (3375 135 (:REWRITE DEFAULT-EXPT-2))
 (3348 1812
       (:TYPE-PRESCRIPTION RTL::NATP-MOD-2))
 (3231 1914 (:REWRITE DEFAULT-LESS-THAN-2))
 (3051 1413 (:REWRITE RTL::INTEGERP-EC-X))
 (3051 1413 (:REWRITE RTL::INT-CAR-TRIPP))
 (2880 45 (:REWRITE ZP-OPEN))
 (2808 72 (:REWRITE |(equal (expt x n) 0)|))
 (2781 1323 (:REWRITE RTL::INT-CADR-TRIPP))
 (2709 1173
       (:TYPE-PRESCRIPTION RTL::RATIONALP-MOD))
 (2709 1173
       (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
 (2625 42 (:REWRITE |(+ x (if a b c))|))
 (2370 129 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (2370 129 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (2250 129 (:REWRITE MOD-X-Y-=-X . 2))
 (2241 129
       (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (2241 129
       (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (2241 129
       (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (2193 2193 (:REWRITE REDUCE-INTEGERP-+))
 (2193 2193 (:REWRITE INTEGERP-MINUS-X))
 (2193 2193 (:META META-INTEGERP-CORRECT))
 (2160 1080
       (:TYPE-PRESCRIPTION RTL::INT-CADDR-TRIPP))
 (2016 1008 (:REWRITE RTL::SPLIT$-CASE-5-2))
 (2010 198 (:REWRITE |(+ y x)|))
 (1977 1833 (:REWRITE |(equal (/ x) c)|))
 (1977 1833 (:REWRITE |(equal (/ x) (/ y))|))
 (1914 1914 (:REWRITE THE-FLOOR-BELOW))
 (1914 1914 (:REWRITE THE-FLOOR-ABOVE))
 (1899 1899
       (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (1899 1899
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (1899 1899
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (1899 1899 (:REWRITE INTEGERP-<-CONSTANT))
 (1899 1899 (:REWRITE CONSTANT-<-INTEGERP))
 (1899 1899
       (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (1899 1899
       (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (1899 1899
       (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (1899 1899
       (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (1899 1899 (:REWRITE |(< c (- x))|))
 (1899 1899
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (1899 1899
       (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (1899 1899
       (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (1899 1899
       (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (1899 1899 (:REWRITE |(< (/ x) (/ y))|))
 (1899 1899 (:REWRITE |(< (- x) c)|))
 (1899 1899 (:REWRITE |(< (- x) (- y))|))
 (1857 615
       (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (1857 615
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE))
 (1854 1833 (:REWRITE |(equal (- x) (- y))|))
 (1833 1833
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (1833 1833
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (1833 1833 (:REWRITE |(equal c (/ x))|))
 (1833 1833 (:REWRITE |(equal c (- x))|))
 (1833 1833 (:REWRITE |(equal (- x) c)|))
 (1824 912 (:REWRITE DEFAULT-DIVIDE))
 (1761 1761
       (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (1737 1737
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (1737 1737
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (1737 1737
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (1479 1479
       (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (1305 45 (:REWRITE |(* (if a b c) x)|))
 (1221 117 (:LINEAR EXPT-<=-1-ONE))
 (1194 117 (:LINEAR EXPT->=-1-TWO))
 (1194 117 (:LINEAR EXPT->-1-TWO))
 (1194 117 (:LINEAR EXPT-<-1-ONE))
 (1185 240 (:REWRITE NORMALIZE-ADDENDS))
 (1173 1173 (:TYPE-PRESCRIPTION NATP))
 (1119 1119
       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1119 1119
       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1119 1119 (:REWRITE |(< (/ x) 0)|))
 (1119 1119 (:REWRITE |(< (* x y) 0)|))
 (1104 117 (:LINEAR EXPT-X->=-X))
 (1104 117 (:LINEAR EXPT->=-1-ONE))
 (1104 117 (:LINEAR EXPT-<=-1-TWO))
 (1074 117 (:LINEAR EXPT-X->-X))
 (1074 117 (:LINEAR EXPT->-1-ONE))
 (1074 117 (:LINEAR EXPT-<-1-TWO))
 (957 957
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (912 912
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (726 726 (:REWRITE REDUCE-RATIONALP-+))
 (726 726 (:REWRITE RATIONALP-MINUS-X))
 (726 726 (:META META-RATIONALP-CORRECT))
 (567 21 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
 (534 534
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (432 144 (:REWRITE |(equal x (/ y))|))
 (426 213 (:REWRITE DEFAULT-MOD-2))
 (360 180 (:REWRITE RTL::INT-CADDR-TRIPP))
 (339 87 (:REWRITE |(+ 0 x)|))
 (288 144 (:REWRITE |(not (equal x (/ y)))|))
 (273 21
      (:REWRITE |(equal (mod (+ x y) z) x)|))
 (255 255
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (255 255
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (255 255 (:REWRITE |(< 0 (/ x))|))
 (255 255 (:REWRITE |(< 0 (* x y))|))
 (234 234
      (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (234 234
      (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (234 234
      (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (234 234
      (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (219 219
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (180 90 (:REWRITE DEFAULT-EXPT-1))
 (132 132 (:TYPE-PRESCRIPTION RTL::VALS))
 (129 129
      (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (129 129 (:REWRITE |(mod x (- y))| . 3))
 (129 129 (:REWRITE |(mod x (- y))| . 2))
 (129 129 (:REWRITE |(mod x (- y))| . 1))
 (129 129
      (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (129 129
      (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (117 117 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (117 117 (:LINEAR EXPT-LINEAR-UPPER-<))
 (117 117 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (117 117 (:LINEAR EXPT-LINEAR-LOWER-<))
 (90 90 (:REWRITE |(expt 1/c n)|))
 (90 90 (:REWRITE |(expt (- x) n)|))
 (84 42 (:DEFINITION FIX))
 (45 45 (:REWRITE CAR-CONS))
 (45 45 (:REWRITE |(* 1 x)|))
 (42 42 (:REWRITE |(equal (+ (- c) x) y)|))
 (42 21 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (42 21 (:REWRITE DEFAULT-MINUS))
 (24 24 (:LINEAR RTL::MOD-BND-3))
 (21 21 (:REWRITE |(+ x (- x))|))
 (21 21 (:REWRITE |(+ c (+ d x))|)))
(RTL::SPLIT$-CASE-4-15)
(RTL::SPLIT$-CASE-4-16)
(RTL::SPLIT$-CASE-4-17
     (37 37 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (37 37 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (37 37 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (8 8 (:REWRITE DEFAULT-TIMES-2))
     (8 8 (:REWRITE DEFAULT-TIMES-1))
     (5 5
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (3 3 (:REWRITE THE-FLOOR-BELOW))
     (3 3 (:REWRITE THE-FLOOR-ABOVE))
     (3 3 (:REWRITE SIMPLIFY-SUMS-<))
     (3 3 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (3 3 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (3 3
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (3 3
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (3 3 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (3 3
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (3 3 (:REWRITE NORMALIZE-ADDENDS))
     (3 3 (:REWRITE INTEGERP-<-CONSTANT))
     (3 3 (:REWRITE DEFAULT-PLUS-2))
     (3 3 (:REWRITE DEFAULT-PLUS-1))
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
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (2 2 (:REWRITE REDUCE-INTEGERP-+))
     (2 2 (:REWRITE INTEGERP-MINUS-X))
     (2 2 (:REWRITE |(< (+ c/d x) y)|))
     (2 2 (:REWRITE |(< (+ (- c) x) y)|))
     (2 2 (:META META-INTEGERP-CORRECT)))
(RTL::SPLIT$-CASE-4-18)
(RTL::SPLIT$-CASE-4-19)
(RTL::SPLIT$-CASE-4-20)
(RTL::SPLIT$-CASE-4-21 (92 92 (:DEFINITION MV-NTH)))
(RTL::SPLIT$-CASE-4-22 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
                       (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                       (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                       (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B)))
(RTL::SPLIT$-CASE-4-23 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
                       (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                       (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                       (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B)))
(RTL::SPLIT$-CASE-4-24 (2128 2128 (:DEFINITION MV-NTH)))
(RTL::SPLIT$-CASE-4-25
 (39182 228 (:REWRITE ACL2-NUMBERP-X))
 (34782 217 (:REWRITE RATIONALP-X))
 (29506 76 (:REWRITE RTL::INTEGERP-EVALH))
 (28640 64 (:DEFINITION RTL::SHFP))
 (11488 5724
        (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-Y))
 (10368 2 (:DEFINITION RTL::NORM-ADD))
 (9372 9372 (:TYPE-PRESCRIPTION RTL::ECP))
 (6526 6526 (:TYPE-PRESCRIPTION RTL::TRIPP))
 (6364 3130
       (:TYPE-PRESCRIPTION RTL::INT-CAR-TRIPP))
 (6260 3130
       (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-X))
 (5764 2272
       (:TYPE-PRESCRIPTION RTL::SPLIT$-CASE-5-2))
 (4148 192
       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (4128 2064
       (:TYPE-PRESCRIPTION RTL::INT-CADR-TRIPP))
 (3316 268 (:REWRITE DEFAULT-PLUS-1))
 (3292 1890 (:REWRITE DEFAULT-CDR))
 (2899 199 (:REWRITE DEFAULT-LESS-THAN-2))
 (2452 558 (:REWRITE DEFAULT-CAR))
 (2079 195 (:REWRITE DEFAULT-LESS-THAN-1))
 (1584 16 (:REWRITE DEFAULT-MINUS))
 (1332 444
       (:TYPE-PRESCRIPTION RTL::ALL-INTEGERS-INTEGER))
 (1170 20 (:REWRITE RTL::EVALH-POW-REWRITE))
 (1116 20 (:REWRITE DEFAULT-EXPT-1))
 (1098 42 (:REWRITE ZP-OPEN))
 (1044 12 (:DEFINITION EQL))
 (872 354 (:REWRITE RTL::INTEGERP-EC-X))
 (872 354 (:REWRITE RTL::INT-CAR-TRIPP))
 (780 780 (:TYPE-PRESCRIPTION RTL::SHFP))
 (728 306 (:REWRITE RTL::INT-CADR-TRIPP))
 (706 706 (:TYPE-PRESCRIPTION RTL::VALS))
 (672 336
      (:TYPE-PRESCRIPTION RTL::INT-CADDR-TRIPP))
 (524 268 (:REWRITE RTL::SHNFP-SHFP))
 (520 212
      (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
 (500 42 (:REWRITE RTL::CONSP-NTHCDR))
 (474 12 (:DEFINITION RTL::ALL-INTEGERS))
 (460 460 (:REWRITE REDUCE-INTEGERP-+))
 (460 460 (:REWRITE INTEGERP-MINUS-X))
 (460 460 (:META META-INTEGERP-CORRECT))
 (460 4 (:DEFINITION RTL::NORM-EXPT))
 (428 24 (:REWRITE DEFAULT-EXPT-2))
 (388
   76
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (316 192 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (288 144 (:REWRITE RTL::SPLIT$-CASE-5-2))
 (260 4 (:REWRITE |(< x (if a b c))|))
 (236 12 (:REWRITE |(+ x (if a b c))|))
 (213 4 (:REWRITE RTL::EVALH-NORM-EXPT))
 (209 209 (:REWRITE REDUCE-RATIONALP-+))
 (209 209 (:REWRITE REDUCE-RATIONALP-*))
 (209 209 (:REWRITE RATIONALP-MINUS-X))
 (209 209 (:META META-RATIONALP-CORRECT))
 (208 76
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (208
  76
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (208 76
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (208 76
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (208 76
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (208
     76
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (199 199 (:REWRITE THE-FLOOR-BELOW))
 (199 199 (:REWRITE THE-FLOOR-ABOVE))
 (194 178
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (192 192
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (192 192
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (192 192
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (192 192 (:REWRITE |(equal c (/ x))|))
 (192 192 (:REWRITE |(equal c (- x))|))
 (192 192 (:REWRITE |(equal (/ x) c)|))
 (192 192 (:REWRITE |(equal (/ x) (/ y))|))
 (192 192 (:REWRITE |(equal (- x) c)|))
 (192 192 (:REWRITE |(equal (- x) (- y))|))
 (179 179
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (179 179
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (178 178 (:REWRITE SIMPLIFY-SUMS-<))
 (178 178 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (178 178
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (178 178 (:REWRITE INTEGERP-<-CONSTANT))
 (178 178 (:REWRITE CONSTANT-<-INTEGERP))
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
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (178 178
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (178 178
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (178 178
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (178 178 (:REWRITE |(< (/ x) (/ y))|))
 (178 178 (:REWRITE |(< (- x) c)|))
 (178 178 (:REWRITE |(< (- x) (- y))|))
 (176 8 (:REWRITE ZIP-OPEN))
 (172 76
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (172 76
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (168 92
      (:TYPE-PRESCRIPTION RTL::SPLIT$-CASE-5-7))
 (168 14 (:REWRITE RTL::CAR-NTHCDR))
 (154 14 (:DEFINITION NTH))
 (153 153 (:REWRITE |(< (* x y) 0)|))
 (150 150
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (150 150
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (150 150 (:REWRITE |(< (/ x) 0)|))
 (148 148 (:TYPE-PRESCRIPTION RTL::NORM-EXPT))
 (147 2 (:REWRITE |(< (if a b c) x)|))
 (144 60
      (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (144 60
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE))
 (126 22
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (119 4 (:REWRITE |(< (+ c/d x) y)|))
 (116 4 (:REWRITE |(expt 0 n)|))
 (112 56 (:REWRITE RTL::INT-CADDR-TRIPP))
 (104 104
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (104 104 (:REWRITE NORMALIZE-ADDENDS))
 (72 44
     (:TYPE-PRESCRIPTION RTL::SPLIT$-CASE-5-6))
 (68 68 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (68 68 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (68 68 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (68 68 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (62 62 (:TYPE-PRESCRIPTION RTL::NORM-POP))
 (60 60
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (60 60 (:TYPE-PRESCRIPTION EXPT))
 (52 14 (:REWRITE RTL::ALL-INTEGERS-INTEGER))
 (48 8 (:REWRITE RTL::SPLIT$-CASE-5-7))
 (44 44 (:TYPE-PRESCRIPTION RTL::NORM-MUL))
 (40 40 (:TYPE-PRESCRIPTION RTL::NORM-ADD))
 (40 40 (:REWRITE RTL::LEN-VALS))
 (30 30
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (26 2 (:REWRITE |(< (+ (- c) x) y)|))
 (24 12 (:REWRITE RTL::SHNFP-INT))
 (22 22 (:REWRITE |(< 0 (/ x))|))
 (22 22 (:REWRITE |(< 0 (* x y))|))
 (20 20
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (18 18 (:TYPE-PRESCRIPTION NATP))
 (16 16 (:REWRITE |(expt 1/c n)|))
 (16 16 (:REWRITE |(expt (- x) n)|))
 (12 12 (:REWRITE |(* 1 x)|))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (8 8 (:REWRITE |(* 0 x)|))
 (6 6 (:REWRITE |(< y (+ (- c) x))|))
 (6 6 (:REWRITE |(< x (+ c/d y))|))
 (2 2 (:REWRITE |(* a (/ a) b)|)))
(RTL::SPLIT$-CASE-4-26 (162 162 (:DEFINITION MV-NTH)))
(RTL::SPLIT$-CASE-4 (236 236 (:DEFINITION MV-NTH)))
(RTL::SPLIT$-CASE-3-1
 (20336 52 (:REWRITE |(* y x)|))
 (17576 928
        (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (17484 104 (:REWRITE |(* x (+ y z))|))
 (15852 24 (:REWRITE MOD-ZERO . 3))
 (12656 24 (:REWRITE DEFAULT-MOD-RATIO))
 (9180 1836 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (9180 1836 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (9180 1836
       (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (9180 1836
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (8248 208 (:REWRITE DEFAULT-PLUS-2))
 (7884 7884
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (7884 7884
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (7884 7884
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (7668 24 (:REWRITE MOD-X-Y-=-X . 4))
 (7668 24 (:REWRITE MOD-X-Y-=-X . 3))
 (7056 52 (:REWRITE |(+ y (+ x z))|))
 (7024 8 (:LINEAR MOD-BOUNDS-3))
 (6864 24 (:REWRITE MOD-ZERO . 4))
 (6844 312 (:REWRITE DEFAULT-TIMES-2))
 (6824 24 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (6784 24 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (5728 24 (:REWRITE RTL::MOD-DOES-NOTHING))
 (5512 168 (:META META-INTEGERP-CORRECT))
 (5252 128
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (4232 128 (:REWRITE DEFAULT-LESS-THAN-1))
 (3856 3856
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (3856
   3856
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (3856
  3856
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (3856 3856
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (3856 3856
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (3856
      3856
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (3856
     3856
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (3856 3856
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (3856 3856
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (3840 208 (:REWRITE DEFAULT-PLUS-1))
 (3164 312 (:REWRITE DEFAULT-TIMES-1))
 (2516 8 (:LINEAR RTL::MOD-BND-2))
 (2344 24 (:REWRITE MOD-X-Y-=-X . 2))
 (1836 1836 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (1836 1836
       (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (1836 1836
       (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (1836 1836
       (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
 (1836 1836
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (1836 1836
       (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (1828 24
       (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 1))
 (1748 1748
       (:TYPE-PRESCRIPTION RTL::NATP-MOD-2))
 (1740 1740 (:TYPE-PRESCRIPTION NATP))
 (1416 24 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (1416 24 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (1392 24
       (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (1392 24
       (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (1392 24
       (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (1264 24 (:REWRITE DEFAULT-MOD-1))
 (1116 128 (:REWRITE DEFAULT-LESS-THAN-2))
 (988 40
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (944 16 (:LINEAR MOD-BOUNDS-2))
 (928 928
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (928 928
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (928 928
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (260 260
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (168 168 (:REWRITE REDUCE-INTEGERP-+))
 (168 168 (:REWRITE INTEGERP-MINUS-X))
 (156 156
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (156 156 (:REWRITE NORMALIZE-ADDENDS))
 (128 128 (:REWRITE THE-FLOOR-BELOW))
 (128 128 (:REWRITE THE-FLOOR-ABOVE))
 (128 128 (:REWRITE SIMPLIFY-SUMS-<))
 (128 128
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (128 128
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (128 128
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
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
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (128 128
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (128 128
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (128 128
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (128 128 (:REWRITE |(< (/ x) (/ y))|))
 (128 128 (:REWRITE |(< (- x) c)|))
 (128 128 (:REWRITE |(< (- x) (- y))|))
 (104 104 (:REWRITE |(* c (* d x))|))
 (104 52 (:REWRITE DEFAULT-DIVIDE))
 (88 88 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (88 88 (:REWRITE |(< (+ c/d x) y)|))
 (88 88 (:REWRITE |(< (+ (- c) x) y)|))
 (56 56 (:REWRITE INTEGERP-/))
 (52 52
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (52 52 (:REWRITE FOLD-CONSTS-IN-+))
 (52 52 (:REWRITE |(+ c (+ d x))|))
 (48 48
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (48 48
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (48 48 (:REWRITE |(< (/ x) 0)|))
 (48 48 (:REWRITE |(< (* x y) 0)|))
 (48 24 (:REWRITE DEFAULT-MOD-2))
 (40 40
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (40 40
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (40 40
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (40 40 (:REWRITE SIMPLIFY-SUMS-EQUAL))
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
 (40 40 (:REWRITE |(< 0 (/ x))|))
 (40 40 (:REWRITE |(< 0 (* x y))|))
 (28 28
     (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (24 24
     (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (24 24 (:REWRITE |(mod x (- y))| . 3))
 (24 24 (:REWRITE |(mod x (- y))| . 2))
 (24 24 (:REWRITE |(mod x (- y))| . 1))
 (24 24
     (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (24 24
     (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 3))
 (24 24
     (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 2))
 (24 24
     (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (20 20 (:REWRITE |(equal (+ (- c) x) y)|))
 (20 20 (:REWRITE |(< y (+ (- c) x))|))
 (20 20 (:REWRITE |(< x (+ c/d y))|))
 (8 8 (:LINEAR RTL::MOD-BND-3)))
(RTL::SPLIT$-CASE-3-2 (264 264 (:DEFINITION MV-NTH)))
(RTL::SPLIT$-CASE-3-3 (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
                      (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                      (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                      (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B)))
(RTL::SPLIT$-CASE-3-4
 (1244 22 (:LINEAR EXPT-<=-1-ONE))
 (1224 22 (:LINEAR EXPT->=-1-TWO))
 (1224 22 (:LINEAR EXPT->-1-TWO))
 (1224 22 (:LINEAR EXPT-<-1-ONE))
 (1164 22 (:LINEAR EXPT-X->=-X))
 (1164 22 (:LINEAR EXPT->=-1-ONE))
 (1164 22 (:LINEAR EXPT-<=-1-TWO))
 (1144 22 (:LINEAR EXPT-X->-X))
 (1144 22 (:LINEAR EXPT->-1-ONE))
 (1144 22 (:LINEAR EXPT-<-1-TWO))
 (421 221
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (341 221 (:REWRITE DEFAULT-LESS-THAN-2))
 (301 221 (:REWRITE DEFAULT-LESS-THAN-1))
 (221 221 (:REWRITE THE-FLOOR-BELOW))
 (221 221 (:REWRITE THE-FLOOR-ABOVE))
 (221 221 (:REWRITE SIMPLIFY-SUMS-<))
 (221 221
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (221 221
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (221 221
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (221 221 (:REWRITE INTEGERP-<-CONSTANT))
 (221 221 (:REWRITE CONSTANT-<-INTEGERP))
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
 (221 221 (:REWRITE |(< (- x) c)|))
 (221 221 (:REWRITE |(< (- x) (- y))|))
 (212 208
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (212 208
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (208 208
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (208
  208
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (208 208
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (208 208
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (208 208
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (208
     208
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (89 89 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (66 66
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (66 66
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (66 66 (:REWRITE |(< 0 (/ x))|))
 (66 66 (:REWRITE |(< 0 (* x y))|))
 (44 44
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (44 44
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (44 44
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (44 44
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (25 25 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (25 25 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (25 25 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (25 25 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (23 23
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (23 23
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (23 23 (:REWRITE |(< (/ x) 0)|))
 (23 23 (:REWRITE |(< (* x y) 0)|))
 (22 22 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (22 22 (:LINEAR EXPT-LINEAR-UPPER-<))
 (22 22 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (22 22 (:LINEAR EXPT-LINEAR-LOWER-<))
 (14 4 (:REWRITE DEFAULT-EXPT-1))
 (6 6
    (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (5 5 (:REWRITE DEFAULT-TIMES-2))
 (5 5 (:REWRITE DEFAULT-TIMES-1))
 (4 4 (:REWRITE DEFAULT-EXPT-2))
 (3 3 (:REWRITE REDUCE-INTEGERP-+))
 (3 3 (:REWRITE INTEGERP-MINUS-X))
 (3 3 (:REWRITE |(expt 1/c n)|))
 (3 3 (:REWRITE |(expt (- x) n)|))
 (3 3 (:META META-INTEGERP-CORRECT))
 (2 2
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS)))
(RTL::SPLIT$-CASE-3-5
 (50932 145 (:REWRITE RTL::MOD-DOES-NOTHING))
 (32996 998 (:LINEAR EXPT-<=-1-ONE))
 (25846 998 (:LINEAR EXPT->=-1-TWO))
 (25846 998 (:LINEAR EXPT->-1-TWO))
 (25846 998 (:LINEAR EXPT-<-1-ONE))
 (24890 998 (:LINEAR EXPT-X->=-X))
 (24890 998 (:LINEAR EXPT->=-1-ONE))
 (24890 998 (:LINEAR EXPT-<=-1-TWO))
 (24724 998 (:LINEAR EXPT-X->-X))
 (24724 998 (:LINEAR EXPT->-1-ONE))
 (24724 998 (:LINEAR EXPT-<-1-TWO))
 (20180 145 (:REWRITE MOD-ZERO . 4))
 (19387 145 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (18825 145 (:REWRITE MOD-X-Y-=-X . 4))
 (18825 145 (:REWRITE MOD-X-Y-=-X . 3))
 (17579 145 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (12493 2547
        (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (11225 145 (:REWRITE MOD-ZERO . 3))
 (10068 10060
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (10068 10060
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (10060 10060
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (10060
  10060
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (10060 10060
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (10060
      10060
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (10060
     10060
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (9141 2547 (:REWRITE DEFAULT-LESS-THAN-1))
 (6983 145 (:REWRITE DEFAULT-MOD-RATIO))
 (6793 542
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (5798 538 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
 (5619 2547 (:REWRITE SIMPLIFY-SUMS-<))
 (5311 2547 (:REWRITE DEFAULT-LESS-THAN-2))
 (4656 695 (:REWRITE DEFAULT-TIMES-2))
 (4656 695 (:REWRITE DEFAULT-TIMES-1))
 (4436 48 (:LINEAR MOD-BOUNDS-3))
 (4430 4430
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (4430 4430
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (4430 4430
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (3883 136 (:REWRITE |(equal (expt x n) 0)|))
 (3400 145 (:REWRITE MOD-X-Y-=-X . 2))
 (3110 622 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (3110 622 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (3086 622
       (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (3086 622
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (2547 2547 (:REWRITE THE-FLOOR-BELOW))
 (2547 2547 (:REWRITE THE-FLOOR-ABOVE))
 (2547 2547
       (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (2547 2547
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (2547 2547
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (2547 2547 (:REWRITE INTEGERP-<-CONSTANT))
 (2547 2547 (:REWRITE CONSTANT-<-INTEGERP))
 (2547 2547
       (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (2547 2547
       (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (2547 2547
       (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (2547 2547
       (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (2547 2547 (:REWRITE |(< c (- x))|))
 (2547 2547
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (2547 2547
       (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (2547 2547
       (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (2547 2547
       (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (2547 2547 (:REWRITE |(< (/ x) (/ y))|))
 (2547 2547 (:REWRITE |(< (- x) c)|))
 (2547 2547 (:REWRITE |(< (- x) (- y))|))
 (2521 145 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (2521 145 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (2065 145
       (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (2065 145
       (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (2065 145
       (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (2023 1996
       (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2020 1996
       (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (1996 1996
       (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (1996 1996
       (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (1856 96 (:LINEAR MOD-BOUNDS-2))
 (1651 145 (:REWRITE DEFAULT-MOD-1))
 (1182 1182
       (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (1140 12 (:REWRITE MOD-POSITIVE . 3))
 (998 998 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (998 998 (:LINEAR EXPT-LINEAR-UPPER-<))
 (998 998 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (998 998 (:LINEAR EXPT-LINEAR-LOWER-<))
 (786 786
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4E))
 (786 786
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
 (786 786
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
 (786 786
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
 (683 683
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (683 683
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (683 683 (:REWRITE |(< 0 (/ x))|))
 (683 683 (:REWRITE |(< 0 (* x y))|))
 (682 341 (:REWRITE DEFAULT-DIVIDE))
 (622 622 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (622 622
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (622 622
      (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (622 622
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (622 622 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (542 542
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (542 542
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (542 542
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (538 538
      (:TYPE-PRESCRIPTION RTL::NATP-MOD-2))
 (538 538 (:TYPE-PRESCRIPTION NATP))
 (537 370
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (506 506
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (506 506
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (506 506 (:REWRITE |(equal c (/ x))|))
 (506 506 (:REWRITE |(equal c (- x))|))
 (506 506 (:REWRITE |(equal (/ x) c)|))
 (506 506 (:REWRITE |(equal (/ x) (/ y))|))
 (506 506 (:REWRITE |(equal (- x) c)|))
 (506 506 (:REWRITE |(equal (- x) (- y))|))
 (495 495
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (495 495
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (495 495 (:REWRITE |(< (/ x) 0)|))
 (495 495 (:REWRITE |(< (* x y) 0)|))
 (456 145
      (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (456 145
      (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (456 145
      (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (370 370
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (370 370 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (370 370
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (351 351
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (341 341
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (290 145 (:REWRITE DEFAULT-MOD-2))
 (222 12 (:REWRITE MOD-POSITIVE . 2))
 (199 199 (:REWRITE REDUCE-INTEGERP-+))
 (199 199 (:REWRITE INTEGERP-MINUS-X))
 (199 199 (:META META-INTEGERP-CORRECT))
 (164 21 (:REWRITE DEFAULT-EXPT-1))
 (145 145 (:REWRITE |(mod x (- y))| . 3))
 (145 145 (:REWRITE |(mod x (- y))| . 2))
 (145 145 (:REWRITE |(mod x (- y))| . 1))
 (53 21 (:REWRITE DEFAULT-EXPT-2))
 (44 44 (:LINEAR RTL::MOD-BND-3))
 (20 20 (:REWRITE |(equal (* x y) 0)|))
 (12 12 (:REWRITE MOD-POSITIVE . 1))
 (12 12 (:REWRITE |(expt 1/c n)|))
 (12 12 (:REWRITE |(expt (- x) n)|))
 (10 10
     (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
 (9 9 (:REWRITE |(expt c (* d n))|))
 (8 8 (:REWRITE |(* c (* d x))|))
 (6 6
    (:TYPE-PRESCRIPTION RTL::RATIONALP-MOD))
 (6 6
    (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION)))
(RTL::SPLIT$-CASE-3-6)
(RTL::SPLIT$-CASE-3-7)
(RTL::SPLIT$-CASE-3-8)
(RTL::SPLIT$-CASE-3-9)
(RTL::SPLIT$-CASE-3-10 (60 60 (:DEFINITION MV-NTH)))
(RTL::SPLIT$-CASE-3-11 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
                       (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                       (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                       (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B)))
(RTL::SPLIT$-CASE-3-12 (1396 1396 (:DEFINITION MV-NTH)))
(RTL::SPLIT$-CASE-3-13
 (39135 227 (:REWRITE ACL2-NUMBERP-X))
 (34772 217 (:REWRITE RATIONALP-X))
 (29506 76 (:REWRITE RTL::INTEGERP-EVALH))
 (28640 64 (:DEFINITION RTL::SHFP))
 (11488 5724
        (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-Y))
 (10368 2 (:DEFINITION RTL::NORM-ADD))
 (9357 9357 (:TYPE-PRESCRIPTION RTL::ECP))
 (6511 6511 (:TYPE-PRESCRIPTION RTL::TRIPP))
 (6325 3117
       (:TYPE-PRESCRIPTION RTL::INT-CAR-TRIPP))
 (6234 3117
       (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-X))
 (5764 2272
       (:TYPE-PRESCRIPTION RTL::SPLIT$-CASE-5-2))
 (4128 2064
       (:TYPE-PRESCRIPTION RTL::INT-CADR-TRIPP))
 (4084 191
       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (3298 250 (:REWRITE DEFAULT-PLUS-1))
 (3292 1890 (:REWRITE DEFAULT-CDR))
 (2893 193 (:REWRITE DEFAULT-LESS-THAN-2))
 (2448 557 (:REWRITE DEFAULT-CAR))
 (2069 189 (:REWRITE DEFAULT-LESS-THAN-1))
 (1584 16 (:REWRITE DEFAULT-MINUS))
 (1332 444
       (:TYPE-PRESCRIPTION RTL::ALL-INTEGERS-INTEGER))
 (1116 20 (:REWRITE DEFAULT-EXPT-1))
 (1070 20 (:REWRITE RTL::EVALH-POW-REWRITE))
 (1014 42 (:REWRITE ZP-OPEN))
 (953 11 (:DEFINITION EQL))
 (869 353 (:REWRITE RTL::INTEGERP-EC-X))
 (869 353 (:REWRITE RTL::INT-CAR-TRIPP))
 (780 780 (:TYPE-PRESCRIPTION RTL::SHFP))
 (728 306 (:REWRITE RTL::INT-CADR-TRIPP))
 (706 706 (:TYPE-PRESCRIPTION RTL::VALS))
 (672 336
      (:TYPE-PRESCRIPTION RTL::INT-CADDR-TRIPP))
 (544 16 (:REWRITE |(* (if a b c) x)|))
 (524 268 (:REWRITE RTL::SHNFP-SHFP))
 (520 212
      (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
 (500 42 (:REWRITE RTL::CONSP-NTHCDR))
 (474 12 (:DEFINITION RTL::ALL-INTEGERS))
 (459 459 (:REWRITE REDUCE-INTEGERP-+))
 (459 459 (:REWRITE INTEGERP-MINUS-X))
 (459 459 (:META META-INTEGERP-CORRECT))
 (428 24 (:REWRITE DEFAULT-EXPT-2))
 (388
   76
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (356 4 (:DEFINITION RTL::NORM-EXPT))
 (315 191 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (288 144 (:REWRITE RTL::SPLIT$-CASE-5-2))
 (219 176
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (213 176
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (209 209 (:REWRITE REDUCE-RATIONALP-+))
 (209 209 (:REWRITE REDUCE-RATIONALP-*))
 (209 209 (:REWRITE RATIONALP-MINUS-X))
 (209 209 (:META META-RATIONALP-CORRECT))
 (208 76
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (208
  76
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (208 76
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (208 76
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (208 76
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (208
     76
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (200 12 (:REWRITE |(+ x (if a b c))|))
 (193 193 (:REWRITE THE-FLOOR-BELOW))
 (193 193 (:REWRITE THE-FLOOR-ABOVE))
 (191 191
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (191 191
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (191 191
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (191 191 (:REWRITE |(equal c (/ x))|))
 (191 191 (:REWRITE |(equal c (- x))|))
 (191 191 (:REWRITE |(equal (/ x) c)|))
 (191 191 (:REWRITE |(equal (/ x) (/ y))|))
 (191 191 (:REWRITE |(equal (- x) c)|))
 (191 191 (:REWRITE |(equal (- x) (- y))|))
 (191 175
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (176 8 (:REWRITE ZIP-OPEN))
 (175 175 (:REWRITE SIMPLIFY-SUMS-<))
 (175 175 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (175 175
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (175 175 (:REWRITE INTEGERP-<-CONSTANT))
 (175 175 (:REWRITE CONSTANT-<-INTEGERP))
 (175 175
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (175 175
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (175 175
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (175 175
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (175 175 (:REWRITE |(< c (- x))|))
 (175 175
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (175 175
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (175 175
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (175 175
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (175 175 (:REWRITE |(< (/ x) (/ y))|))
 (175 175 (:REWRITE |(< (- x) c)|))
 (175 175 (:REWRITE |(< (- x) (- y))|))
 (172 76
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (172 76
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (168 92
      (:TYPE-PRESCRIPTION RTL::SPLIT$-CASE-5-7))
 (168 14 (:REWRITE RTL::CAR-NTHCDR))
 (160 4 (:REWRITE |(< x (if a b c))|))
 (154 14 (:DEFINITION NTH))
 (151 151 (:REWRITE |(< (* x y) 0)|))
 (150 150
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (150 150
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (150 150 (:REWRITE |(< (/ x) 0)|))
 (144 60
      (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (144 60
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE))
 (128 128 (:TYPE-PRESCRIPTION RTL::NORM-EXPT))
 (125 4 (:REWRITE RTL::EVALH-NORM-EXPT))
 (116 4 (:REWRITE |(expt 0 n)|))
 (112 56 (:REWRITE RTL::INT-CADDR-TRIPP))
 (90 90
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (90 90 (:REWRITE NORMALIZE-ADDENDS))
 (90 1 (:REWRITE |(< (if a b c) x)|))
 (72 44
     (:TYPE-PRESCRIPTION RTL::SPLIT$-CASE-5-6))
 (62 62 (:TYPE-PRESCRIPTION RTL::NORM-POP))
 (60 60
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (60 60 (:TYPE-PRESCRIPTION EXPT))
 (55 55 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (55 55 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (55 55 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (55 55 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (52 14 (:REWRITE RTL::ALL-INTEGERS-INTEGER))
 (48 8 (:REWRITE RTL::SPLIT$-CASE-5-7))
 (44 44 (:TYPE-PRESCRIPTION RTL::NORM-MUL))
 (40 40 (:TYPE-PRESCRIPTION RTL::NORM-ADD))
 (40 40 (:REWRITE RTL::LEN-VALS))
 (24 12 (:REWRITE RTL::SHNFP-INT))
 (20 20
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (20 20
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (20 20
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (20 20 (:REWRITE |(< 0 (/ x))|))
 (20 20 (:REWRITE |(< 0 (* x y))|))
 (17 17 (:TYPE-PRESCRIPTION NATP))
 (16 16 (:REWRITE |(expt 1/c n)|))
 (16 16 (:REWRITE |(expt (- x) n)|))
 (12 12 (:REWRITE |(* 1 x)|))
 (10 10 (:TYPE-PRESCRIPTION ABS))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (8 8 (:REWRITE |(* 0 x)|))
 (4 4
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (1 1
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (1 1 (:REWRITE |(* a (/ a) b)|)))
(RTL::SPLIT$-CASE-3-14 (162 162 (:DEFINITION MV-NTH)))
(RTL::SPLIT$-CASE-3 (100 100 (:DEFINITION MV-NTH)))
(RTL::SPLIT$-CASE-2-1
     (1706 1101
           (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-Y))
     (857 857 (:TYPE-PRESCRIPTION RTL::ECP))
     (682 242
          (:TYPE-PRESCRIPTION RTL::SPLIT$-CASE-5-2))
     (639 395
          (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-X))
     (639 395
          (:TYPE-PRESCRIPTION RTL::INT-CAR-TRIPP))
     (476 476 (:TYPE-PRESCRIPTION RTL::TRIPP))
     (398 242
          (:TYPE-PRESCRIPTION RTL::INT-CADR-TRIPP))
     (186 3
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (158 94
          (:TYPE-PRESCRIPTION RTL::INT-CADDR-TRIPP))
     (138 3 (:REWRITE ACL2-NUMBERP-X))
     (86 2 (:REWRITE RTL::SPLIT$-CASE-5))
     (78 3 (:REWRITE RATIONALP-X))
     (25 25 (:REWRITE DEFAULT-CDR))
     (24 4 (:REWRITE RTL::SHNFP-INT))
     (18 2 (:REWRITE RTL::SPLIT$-CASE-5-3))
     (12 4 (:REWRITE RTL::INTEGERP-EC-X))
     (12 4 (:REWRITE RTL::INT-CAR-TRIPP))
     (9 9 (:REWRITE DEFAULT-CAR))
     (8 8 (:TYPE-PRESCRIPTION RTL::P-NAT))
     (8 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (6 6 (:REWRITE REDUCE-INTEGERP-+))
     (6 6 (:REWRITE RTL::P-NAT))
     (6 6 (:REWRITE RTL::NATP-Y2))
     (6 6 (:REWRITE RTL::NATP-Y1))
     (6 6 (:REWRITE RTL::NATP-Y0))
     (6 6 (:REWRITE RTL::NATP-X2))
     (6 6 (:REWRITE RTL::NATP-X1))
     (6 6 (:REWRITE RTL::NATP-X0))
     (6 6 (:REWRITE RTL::NATP-P-1/2))
     (6 6 (:REWRITE INTEGERP-MINUS-X))
     (6 6 (:META META-INTEGERP-CORRECT))
     (6 2 (:REWRITE RTL::INT-CADR-TRIPP))
     (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (4 4 (:TYPE-PRESCRIPTION RTL::NATP-Y2))
     (4 4 (:TYPE-PRESCRIPTION RTL::NATP-Y1))
     (4 4 (:TYPE-PRESCRIPTION RTL::NATP-Y0))
     (4 4 (:TYPE-PRESCRIPTION RTL::NATP-X2))
     (4 4 (:TYPE-PRESCRIPTION RTL::NATP-X1))
     (4 4 (:TYPE-PRESCRIPTION RTL::NATP-X0))
     (4 4 (:TYPE-PRESCRIPTION RTL::NATP-P-1/2))
     (4 4 (:REWRITE THE-FLOOR-BELOW))
     (4 4 (:REWRITE THE-FLOOR-ABOVE))
     (4 4 (:REWRITE SIMPLIFY-SUMS-<))
     (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (4 4 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (4 4
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (4 4
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
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
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (3 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (3 3 (:REWRITE REDUCE-RATIONALP-+))
     (3 3 (:REWRITE REDUCE-RATIONALP-*))
     (3 3
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (3 3
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (3 3 (:REWRITE RATIONALP-MINUS-X))
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
     (3 3 (:META META-RATIONALP-CORRECT))
     (2 2 (:REWRITE RTL::SHNFP-POW-P))
     (1 1 (:REWRITE RTL::SPLIT$-CASE-5-2))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (1 1 (:REWRITE |(< 0 (/ x))|))
     (1 1 (:REWRITE |(< 0 (* x y))|)))
(RTL::SPLIT$-CASE-2-2 (1386 941
                            (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-Y))
                      (567 169
                           (:TYPE-PRESCRIPTION RTL::SPLIT$-CASE-5-2))
                      (550 550 (:TYPE-PRESCRIPTION RTL::ECP))
                      (361 256
                           (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-X))
                      (361 256
                           (:TYPE-PRESCRIPTION RTL::INT-CAR-TRIPP))
                      (252 169
                           (:TYPE-PRESCRIPTION RTL::INT-CADR-TRIPP))
                      (248 248 (:TYPE-PRESCRIPTION RTL::TRIPP))
                      (150 90
                           (:TYPE-PRESCRIPTION RTL::INT-CADDR-TRIPP))
                      (2 2 (:REWRITE DEFAULT-CDR))
                      (2 1
                         (:TYPE-PRESCRIPTION RTL::SPLIT$-CASE-2-2))
                      (1 1 (:REWRITE DEFAULT-CAR)))
(RTL::SPLIT$-CASE-2-3
     (2167 1399
           (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-Y))
     (1151 1151 (:TYPE-PRESCRIPTION RTL::ECP))
     (972 567
          (:TYPE-PRESCRIPTION RTL::INT-CAR-TRIPP))
     (942 567
          (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-X))
     (760 2 (:REWRITE RTL::SPLIT$-CASE-5))
     (718 718 (:TYPE-PRESCRIPTION RTL::TRIPP))
     (480 291
          (:TYPE-PRESCRIPTION RTL::SPLIT$-CASE-5-2))
     (476 291
          (:TYPE-PRESCRIPTION RTL::INT-CADR-TRIPP))
     (340 190
          (:TYPE-PRESCRIPTION RTL::INT-CADDR-TRIPP))
     (212 6
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (162 4 (:REWRITE |(< x (+ c/d y))|))
     (156 4 (:REWRITE ACL2-NUMBERP-X))
     (88 4 (:REWRITE RATIONALP-X))
     (68 2 (:REWRITE |(< y (+ (- c) x))|))
     (64 64 (:TYPE-PRESCRIPTION RTL::P-NAT))
     (56 26 (:REWRITE DEFAULT-LESS-THAN-2))
     (38 22 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (34 34 (:REWRITE DEFAULT-CDR))
     (30 2 (:REWRITE |(* x (+ y z))|))
     (26 26 (:REWRITE THE-FLOOR-BELOW))
     (26 26 (:REWRITE THE-FLOOR-ABOVE))
     (26 26 (:REWRITE DEFAULT-LESS-THAN-1))
     (26 4 (:REWRITE DEFAULT-TIMES-2))
     (24 24
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (24 24
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (24 12 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (24 8 (:LINEAR RTL::P-IS-BIG))
     (22 22 (:REWRITE SIMPLIFY-SUMS-<))
     (22 22 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (22 22
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (22 22 (:REWRITE INTEGERP-<-CONSTANT))
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
     (18 2 (:REWRITE RTL::SPLIT$-CASE-5-3))
     (16 4 (:REWRITE DEFAULT-PLUS-2))
     (15 15 (:REWRITE DEFAULT-CAR))
     (12 12 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (12 12 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (12 12 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (12 12 (:TYPE-PRESCRIPTION RTL::NATP-Y2))
     (12 12 (:TYPE-PRESCRIPTION RTL::NATP-Y1))
     (12 12 (:TYPE-PRESCRIPTION RTL::NATP-Y0))
     (12 12 (:TYPE-PRESCRIPTION RTL::NATP-X2))
     (12 12 (:TYPE-PRESCRIPTION RTL::NATP-X1))
     (12 12 (:TYPE-PRESCRIPTION RTL::NATP-X0))
     (12 4 (:REWRITE RTL::INTEGERP-EC-X))
     (12 4 (:REWRITE RTL::INT-CAR-TRIPP))
     (8 8 (:TYPE-PRESCRIPTION RTL::NATP-P-1/2))
     (6 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (6 6
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (6 6 (:REWRITE REDUCE-INTEGERP-+))
     (6 6
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (6 6 (:REWRITE INTEGERP-MINUS-X))
     (6 6
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (6 6 (:REWRITE |(equal c (/ x))|))
     (6 6 (:REWRITE |(equal c (- x))|))
     (6 6 (:REWRITE |(equal (/ x) c)|))
     (6 6 (:REWRITE |(equal (/ x) (/ y))|))
     (6 6 (:REWRITE |(equal (- x) c)|))
     (6 6 (:REWRITE |(equal (- x) (- y))|))
     (6 6 (:META META-INTEGERP-CORRECT))
     (5 5 (:REWRITE RTL::SHNFP-INT))
     (4 4 (:REWRITE REDUCE-RATIONALP-+))
     (4 4 (:REWRITE REDUCE-RATIONALP-*))
     (4 4 (:REWRITE RATIONALP-MINUS-X))
     (4 4 (:REWRITE RTL::P-NAT))
     (4 4
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (4 4 (:REWRITE NORMALIZE-ADDENDS))
     (4 4 (:REWRITE RTL::NATP-Y2))
     (4 4 (:REWRITE RTL::NATP-Y1))
     (4 4 (:REWRITE RTL::NATP-Y0))
     (4 4 (:REWRITE RTL::NATP-X2))
     (4 4 (:REWRITE RTL::NATP-X1))
     (4 4 (:REWRITE RTL::NATP-X0))
     (4 4 (:REWRITE RTL::NATP-P-1/2))
     (4 4 (:REWRITE DEFAULT-TIMES-1))
     (4 4 (:REWRITE DEFAULT-PLUS-1))
     (4 4 (:META META-RATIONALP-CORRECT))
     (4 2 (:REWRITE |(* a (/ a) b)|))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (2 2 (:REWRITE RTL::SHNFP-POW-P))
     (2 2
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (2 2 (:REWRITE |(< (/ x) 0)|))
     (2 2 (:REWRITE |(< (* x y) 0)|)))
(RTL::SPLIT$-CASE-2-4
 (10406 86 (:REWRITE ACL2-NUMBERP-X))
 (7784 86 (:REWRITE RATIONALP-X))
 (5868 144 (:REWRITE DEFAULT-PLUS-1))
 (4608 8 (:REWRITE RTL::INTEGERP-EVALH))
 (4568 8 (:DEFINITION RTL::SHFP))
 (4146 2121
       (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-Y))
 (3994 146 (:REWRITE DEFAULT-PLUS-2))
 (3376 14 (:REWRITE |(+ (if a b c) x)|))
 (2854 26 (:REWRITE DEFAULT-TIMES-2))
 (2569 2569 (:TYPE-PRESCRIPTION RTL::ECP))
 (1854 462
       (:TYPE-PRESCRIPTION RTL::SPLIT$-CASE-5-7))
 (1355 10 (:DEFINITION NTHCDR))
 (1226 508
       (:TYPE-PRESCRIPTION RTL::INT-CAR-TRIPP))
 (1030 1030 (:TYPE-PRESCRIPTION RTL::TRIPP))
 (992 508
      (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-X))
 (948 212
      (:TYPE-PRESCRIPTION RTL::ALL-INTEGERS-INTEGER))
 (860 10 (:REWRITE |(* (if a b c) x)|))
 (798 10 (:REWRITE DEFAULT-EXPT-2))
 (760 152
      (:TYPE-PRESCRIPTION RTL::SPLIT$-CASE-5-8))
 (756 26
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (678 349
      (:TYPE-PRESCRIPTION RTL::SPLIT$-CASE-5-2))
 (674 349
      (:TYPE-PRESCRIPTION RTL::INT-CADR-TRIPP))
 (663 3 (:REWRITE RTL::EVALH-POW-REWRITE))
 (638 10 (:REWRITE ZP-OPEN))
 (490 80 (:REWRITE DEFAULT-CAR))
 (471 15 (:REWRITE |(+ (+ x y) z)|))
 (470 6 (:REWRITE DEFAULT-EXPT-1))
 (412 4 (:REWRITE RTL::CDR-NTHCDR))
 (383 255 (:REWRITE DEFAULT-CDR))
 (296 74
      (:TYPE-PRESCRIPTION RTL::SPLIT$-CASE-5-6))
 (256 15 (:REWRITE |(+ y (+ x z))|))
 (236 74
      (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (236 74
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE))
 (234 129
      (:TYPE-PRESCRIPTION RTL::INT-CADDR-TRIPP))
 (234 24 (:REWRITE DEFAULT-TIMES-1))
 (216 216
      (:TYPE-PRESCRIPTION RTL::ALL-INTEGERS))
 (216 2 (:REWRITE RTL::NTHCDR-CDR))
 (204 4 (:REWRITE RTL::ALL-INTEGERS-INTEGER))
 (184 8 (:REWRITE |(* 1 x)|))
 (180 30 (:REWRITE RTL::SPLIT$-CASE-5-8))
 (170 2 (:REWRITE |(< x (if a b c))|))
 (138 2 (:REWRITE RTL::CAR-NTHCDR))
 (136 2 (:DEFINITION NTH))
 (132 22 (:REWRITE RTL::SPLIT$-CASE-5-7))
 (126 8 (:REWRITE |(+ 0 x)|))
 (102 42 (:REWRITE RTL::INTEGERP-EC-X))
 (102 42 (:REWRITE RTL::INT-CAR-TRIPP))
 (98 2 (:REWRITE RTL::CONSP-NTHCDR))
 (96 96 (:TYPE-PRESCRIPTION RTL::SHFP))
 (85 34 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (84 36 (:REWRITE RTL::INT-CADR-TRIPP))
 (74 74
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (74
   74
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (74
  74
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (74 74
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (74 74
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (74 74
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (74 74
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (74 74
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (74 74
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (74 74
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (74 74 (:TYPE-PRESCRIPTION EXPT))
 (69 69 (:REWRITE REDUCE-INTEGERP-+))
 (69 69 (:REWRITE INTEGERP-MINUS-X))
 (69 69 (:META META-INTEGERP-CORRECT))
 (69 36 (:REWRITE DEFAULT-LESS-THAN-2))
 (64 32 (:REWRITE RTL::SHNFP-SHFP))
 (63 63
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (63 63 (:REWRITE NORMALIZE-ADDENDS))
 (54 54 (:REWRITE RTL::SPLIT$-CASE-2-3))
 (54 36 (:REWRITE DEFAULT-LESS-THAN-1))
 (52 4 (:REWRITE ZIP-OPEN))
 (43 25 (:REWRITE |(+ c (+ d x))|))
 (38 18 (:REWRITE RTL::SPLIT$-CASE-2-2))
 (36 36 (:REWRITE THE-FLOOR-BELOW))
 (36 36 (:REWRITE THE-FLOOR-ABOVE))
 (34 34 (:REWRITE SIMPLIFY-SUMS-<))
 (34 34
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (34 34 (:REWRITE REDUCE-RATIONALP-+))
 (34 34 (:REWRITE REDUCE-RATIONALP-*))
 (34 34
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (34 34
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (34 34 (:REWRITE RATIONALP-MINUS-X))
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
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (34 34
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (34 34
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (34 34
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (34 34 (:REWRITE |(< (/ x) (/ y))|))
 (34 34 (:REWRITE |(< (- x) c)|))
 (34 34 (:REWRITE |(< (- x) (- y))|))
 (34 34 (:META META-RATIONALP-CORRECT))
 (32 16 (:REWRITE RTL::SPLIT$-CASE-5-2))
 (28 28 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (28 2 (:REWRITE |(expt 0 n)|))
 (26 26 (:REWRITE SIMPLIFY-SUMS-EQUAL))
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
 (23 23 (:REWRITE FOLD-CONSTS-IN-+))
 (17 17
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (17 17
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (17 17 (:REWRITE |(< (/ x) 0)|))
 (17 17 (:REWRITE |(< (* x y) 0)|))
 (16 8 (:REWRITE RTL::INT-CADDR-TRIPP))
 (11 11
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (11 11
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (11 11 (:REWRITE |(< y (+ (- c) x))|))
 (11 11 (:REWRITE |(< x (+ c/d y))|))
 (11 11 (:REWRITE |(< 0 (/ x))|))
 (11 11 (:REWRITE |(< 0 (* x y))|))
 (6 6 (:REWRITE RTL::LEN-VALS))
 (6 6 (:REWRITE |(< (+ c/d x) y)|))
 (6 6 (:REWRITE |(< (+ (- c) x) y)|))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (4 4 (:REWRITE RTL::ALL-INTEGERS-VALS))
 (4 4 (:REWRITE |(expt 1/c n)|))
 (4 4 (:REWRITE |(expt (- x) n)|))
 (4 4 (:REWRITE |(* 0 x)|))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 (2 2
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (1 1 (:REWRITE RTL::SHNFP-INT)))
(RTL::SPLIT$-CASE-2-5
 (46862 402 (:REWRITE ACL2-NUMBERP-X))
 (43618 474 (:REWRITE RATIONALP-X))
 (34398 6 (:DEFINITION RTL::EVALH))
 (28248 84 (:REWRITE RTL::INTEGERP-EVALH))
 (25729 1 (:DEFINITION RTL::SPLIT$))
 (23392 4 (:DEFINITION RTL::NORM-ADD))
 (23375 541 (:REWRITE DEFAULT-PLUS-2))
 (23348 44 (:DEFINITION RTL::SHFP))
 (17362 8749
        (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-Y))
 (12529 12529 (:TYPE-PRESCRIPTION RTL::ECP))
 (7273 7273 (:TYPE-PRESCRIPTION RTL::TRIPP))
 (7230 3398
       (:TYPE-PRESCRIPTION RTL::INT-CAR-TRIPP))
 (7000 397 (:REWRITE DEFAULT-LESS-THAN-2))
 (6762 3398
       (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-X))
 (6470 378 (:REWRITE REDUCE-RATIONALP-*))
 (6118 274
       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (5124 2641
       (:TYPE-PRESCRIPTION RTL::SPLIT$-CASE-5-2))
 (5094 10 (:REWRITE RTL::SPLIT$-CASE-5))
 (5034 727 (:REWRITE DEFAULT-TIMES-1))
 (4992 2513
       (:TYPE-PRESCRIPTION RTL::INT-CADR-TRIPP))
 (4755 389 (:REWRITE DEFAULT-LESS-THAN-1))
 (4400 40 (:DEFINITION RTL::ALL-INTEGERS))
 (4192 48 (:DEFINITION RFIX))
 (3750 378 (:REWRITE REDUCE-RATIONALP-+))
 (3680 32 (:REWRITE DEFAULT-MINUS))
 (3239 61 (:REWRITE ZP-OPEN))
 (3174 46 (:REWRITE RTL::CAR-NTHCDR))
 (3150 48 (:DEFINITION NTH))
 (2949 475 (:REWRITE DEFAULT-CAR))
 (2504 30 (:REWRITE |(+ (if a b c) x)|))
 (2323 1452 (:REWRITE DEFAULT-CDR))
 (2120 6 (:REWRITE RTL::NTHCDR+))
 (1647 591 (:META META-INTEGERP-CORRECT))
 (1646 6 (:REWRITE RTL::EVALH-POW-REWRITE))
 (1539 9 (:DEFINITION NTHCDR))
 (1514 378 (:META META-RATIONALP-CORRECT))
 (1506 18 (:REWRITE DEFAULT-EXPT-1))
 (1356 347 (:REWRITE SIMPLIFY-SUMS-<))
 (1174 170
       (:REWRITE RTL::ALL-INTEGERS-INTEGER))
 (894 342 (:REWRITE RTL::INTEGERP-EC-X))
 (894 342 (:REWRITE RTL::INT-CAR-TRIPP))
 (884 102 (:REWRITE |(< x (+ c/d y))|))
 (858 22 (:REWRITE DEFAULT-EXPT-2))
 (829 33 (:REWRITE |(+ y (+ x z))|))
 (812 8 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (810 274 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (778 8 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (774 404
      (:TYPE-PRESCRIPTION RTL::INT-CADDR-TRIPP))
 (762 298 (:REWRITE RTL::INT-CADR-TRIPP))
 (758 347
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (758 8 (:REWRITE MOD-X-Y-=-X . 4))
 (758 8 (:REWRITE MOD-X-Y-=-X . 3))
 (628 8 (:REWRITE MOD-ZERO . 4))
 (622 4 (:DEFINITION RTL::NORM-EXPT))
 (614 46 (:REWRITE RTL::CONSP-NTHCDR))
 (614 8 (:REWRITE MOD-X-Y-=-X . 2))
 (612 612
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (612 612
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (612 612
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (591 591 (:REWRITE REDUCE-INTEGERP-+))
 (591 591 (:REWRITE INTEGERP-MINUS-X))
 (582 16 (:REWRITE |(+ (+ x y) z)|))
 (568 568 (:TYPE-PRESCRIPTION RTL::SHFP))
 (534 8 (:REWRITE MOD-ZERO . 3))
 (499 259 (:REWRITE NORMALIZE-ADDENDS))
 (456 114
      (:TYPE-PRESCRIPTION RTL::SPLIT$-CASE-5-6))
 (434 8 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (434 8 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (428 6 (:REWRITE |(< x (if a b c))|))
 (414 92 (:REWRITE |(< y (+ (- c) x))|))
 (397 397 (:REWRITE THE-FLOOR-BELOW))
 (397 397 (:REWRITE THE-FLOOR-ABOVE))
 (392 216 (:REWRITE RTL::SHNFP-SHFP))
 (378 378 (:REWRITE RATIONALP-MINUS-X))
 (360 8
      (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (360 8
      (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (360 8
      (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (359 357
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (359 357
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (353 353
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (347 347
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (347 347 (:REWRITE INTEGERP-<-CONSTANT))
 (347 347 (:REWRITE CONSTANT-<-INTEGERP))
 (347 347
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (347 347
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (347 347
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (347 347
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (347 347 (:REWRITE |(< c (- x))|))
 (347 347
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (347 347
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (347 347
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (347 347
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (347 347 (:REWRITE |(< (/ x) (/ y))|))
 (347 347 (:REWRITE |(< (- x) c)|))
 (347 347 (:REWRITE |(< (- x) (- y))|))
 (346 8 (:REWRITE RTL::MOD-DOES-NOTHING))
 (314 274 (:REWRITE |(equal (/ x) c)|))
 (314 274 (:REWRITE |(equal (/ x) (/ y))|))
 (313 313 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (284 142 (:REWRITE DEFAULT-DIVIDE))
 (274 274
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (274 274
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (274 274
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (274 274 (:REWRITE |(equal c (/ x))|))
 (274 274 (:REWRITE |(equal c (- x))|))
 (274 274 (:REWRITE |(equal (- x) c)|))
 (274 274 (:REWRITE |(equal (- x) (- y))|))
 (256 1 (:DEFINITION EVENP))
 (252 12 (:REWRITE ZIP-OPEN))
 (239 239
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (216 152 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (216 152 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (210
   114
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (208 16 (:REWRITE |(* 1 x)|))
 (182 90 (:REWRITE RTL::SPLIT$-CASE-2-2))
 (176 88 (:REWRITE RTL::SPLIT$-CASE-5-2))
 (176 64 (:LINEAR RTL::P-IS-BIG))
 (170 170
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (170 170
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (170 170
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (168 152 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
 (164 30 (:REWRITE RTL::SPLIT$-CASE-5-7))
 (164 6 (:REWRITE |(expt 0 n)|))
 (152 152
      (:TYPE-PRESCRIPTION RTL::RATIONALP-MOD))
 (152 152 (:TYPE-PRESCRIPTION RATIONALP-MOD))
 (152 152
      (:TYPE-PRESCRIPTION RTL::NATP-MOD-2))
 (152 152 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (152 152
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (152 152
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (152 152
      (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (152 152
      (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
 (152 152
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (152 152
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (152 152 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (152 152 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
 (152 152
      (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
 (142 142
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (139 87
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (124 124
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (120 40 (:REWRITE |(equal x (/ y))|))
 (114 114
      (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (114 114
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE))
 (114 114
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (114
  114
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (114 114
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (114 114
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (114 114
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (114
     114
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (114 114
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (114 114
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (114 114
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (114 114 (:TYPE-PRESCRIPTION EXPT))
 (114 114
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (114 114
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (114 114 (:REWRITE |(< (/ x) 0)|))
 (114 114 (:REWRITE |(< (* x y) 0)|))
 (110 10 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
 (104 88 (:REWRITE |(+ c (+ d x))|))
 (104 2
      (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 1))
 (100 100 (:REWRITE RTL::LEN-VALS))
 (94 94 (:REWRITE RTL::ALL-INTEGERS-VALS))
 (88 44 (:REWRITE RTL::INT-CADDR-TRIPP))
 (87 87 (:REWRITE |(< 0 (/ x))|))
 (87 87 (:REWRITE |(< 0 (* x y))|))
 (86 86
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (84 84 (:REWRITE |(* c (* d x))|))
 (80 40 (:REWRITE RTL::ALL-INTEGERS-NTHCDR))
 (80 40 (:REWRITE |(not (equal x (/ y)))|))
 (76 76 (:REWRITE FOLD-CONSTS-IN-+))
 (64 32 (:REWRITE DEFAULT-MOD-2))
 (52 52 (:TYPE-PRESCRIPTION RTL::NATP-Y2))
 (52 52 (:TYPE-PRESCRIPTION RTL::NATP-Y1))
 (52 52 (:TYPE-PRESCRIPTION RTL::NATP-Y0))
 (52 52 (:TYPE-PRESCRIPTION RTL::NATP-X2))
 (52 52 (:TYPE-PRESCRIPTION RTL::NATP-X1))
 (52 52 (:TYPE-PRESCRIPTION RTL::NATP-X0))
 (40 40 (:TYPE-PRESCRIPTION RTL::NATP-P-1/2))
 (32 32 (:REWRITE RTL::SPLIT$-CASE-2-3))
 (30 30 (:DEFINITION FIX))
 (26 26 (:REWRITE |(< (+ c/d x) y)|))
 (26 26 (:REWRITE |(< (+ (- c) x) y)|))
 (20 20 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (20 20 (:REWRITE |(+ x (- x))|))
 (20 10 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
 (20 10 (:REWRITE |(* a (/ a) b)|))
 (12 12 (:REWRITE |(expt 1/c n)|))
 (12 12 (:REWRITE |(expt (- x) n)|))
 (10 10 (:REWRITE RTL::P-NAT))
 (10 10 (:REWRITE RTL::NATP-Y2))
 (10 10 (:REWRITE RTL::NATP-Y1))
 (10 10 (:REWRITE RTL::NATP-Y0))
 (10 10 (:REWRITE RTL::NATP-X2))
 (10 10 (:REWRITE RTL::NATP-X1))
 (10 10 (:REWRITE RTL::NATP-X0))
 (10 10 (:REWRITE RTL::NATP-P-1/2))
 (9 3 (:REWRITE RTL::SHNFP-INT))
 (8 8 (:TYPE-PRESCRIPTION RTL::NORM-POP))
 (8 8 (:TYPE-PRESCRIPTION RTL::NORM-MUL))
 (8 8
    (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (8 8 (:REWRITE INTEGERP-/))
 (8 8 (:REWRITE |(mod x (- y))| . 3))
 (8 8 (:REWRITE |(mod x (- y))| . 2))
 (8 8 (:REWRITE |(mod x (- y))| . 1))
 (8 8
    (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (8 8
    (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (6 6 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (4 4 (:TYPE-PRESCRIPTION ABS))
 (4 4
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (4 4
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (3 3 (:REWRITE |(equal (+ (- c) x) y)|))
 (2 2
    (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 3))
 (2 2
    (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 2))
 (2 2 (:REWRITE |(equal (* x y) 0)|)))
(RTL::SPLIT$-CASE-2-6
 (7185 23 (:REWRITE ACL2-NUMBERP-X))
 (6872 23 (:REWRITE RATIONALP-X))
 (6336 12 (:REWRITE RTL::INTEGERP-EVALH))
 (6276 12 (:DEFINITION RTL::SHFP))
 (5213 81 (:REWRITE DEFAULT-PLUS-2))
 (2768 1384
       (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-Y))
 (2074 18 (:REWRITE DEFAULT-TIMES-2))
 (1873 1873 (:TYPE-PRESCRIPTION RTL::ECP))
 (891 439
      (:TYPE-PRESCRIPTION RTL::INT-CAR-TRIPP))
 (878 439
      (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-X))
 (831 831 (:TYPE-PRESCRIPTION RTL::TRIPP))
 (625 6 (:DEFINITION NTHCDR))
 (522 35
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (518 6 (:REWRITE DEFAULT-EXPT-1))
 (512 286
      (:TYPE-PRESCRIPTION RTL::SPLIT$-CASE-5-2))
 (461 345 (:REWRITE DEFAULT-CDR))
 (444 222
      (:TYPE-PRESCRIPTION RTL::INT-CADR-TRIPP))
 (424 101 (:REWRITE DEFAULT-CAR))
 (360 78
      (:TYPE-PRESCRIPTION RTL::ALL-INTEGERS-INTEGER))
 (360 8 (:REWRITE ZP-OPEN))
 (346 77 (:REWRITE DEFAULT-PLUS-1))
 (262 8 (:REWRITE |(+ (if a b c) x)|))
 (261 7 (:REWRITE |(+ (+ x y) z)|))
 (204 4 (:REWRITE RTL::ALL-INTEGERS-INTEGER))
 (199 4 (:REWRITE RTL::EVALH-POW-REWRITE))
 (190 9 (:REWRITE |(+ y (+ x z))|))
 (176 6 (:REWRITE |(* (if a b c) x)|))
 (172 16 (:REWRITE DEFAULT-TIMES-1))
 (144 144 (:TYPE-PRESCRIPTION RTL::SHFP))
 (144 72
      (:TYPE-PRESCRIPTION RTL::INT-CADDR-TRIPP))
 (138 2 (:REWRITE RTL::CAR-NTHCDR))
 (136 2 (:DEFINITION NTH))
 (112 28
      (:TYPE-PRESCRIPTION RTL::SPLIT$-CASE-5-7))
 (100 4 (:REWRITE ZIP-OPEN))
 (98 2 (:REWRITE RTL::CONSP-NTHCDR))
 (96 48 (:REWRITE RTL::SHNFP-SHFP))
 (93 43 (:REWRITE RTL::INTEGERP-EC-X))
 (93 43 (:REWRITE RTL::INT-CAR-TRIPP))
 (87 42 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (82 82
     (:TYPE-PRESCRIPTION RTL::ALL-INTEGERS))
 (72 36 (:REWRITE RTL::INT-CADR-TRIPP))
 (69 42 (:REWRITE DEFAULT-LESS-THAN-2))
 (68 2 (:REWRITE |(expt 0 n)|))
 (62 62 (:REWRITE REDUCE-INTEGERP-+))
 (62 62 (:REWRITE INTEGERP-MINUS-X))
 (62 62 (:META META-INTEGERP-CORRECT))
 (60 42 (:REWRITE DEFAULT-LESS-THAN-1))
 (60
   12
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (48 24 (:REWRITE RTL::SPLIT$-CASE-5-2))
 (48 24 (:REWRITE RTL::SPLIT$-CASE-2-2))
 (48 12
     (:TYPE-PRESCRIPTION RTL::SPLIT$-CASE-5-6))
 (48 12
     (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (48 12
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE))
 (48 12
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (42 42 (:REWRITE THE-FLOOR-BELOW))
 (42 42 (:REWRITE THE-FLOOR-ABOVE))
 (42 42 (:REWRITE SIMPLIFY-SUMS-<))
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
 (36 36 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (35 35 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (35 35
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (35 35
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (35 35
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (35 35 (:REWRITE NORMALIZE-ADDENDS))
 (35 35
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (35 35 (:REWRITE |(equal c (/ x))|))
 (35 35 (:REWRITE |(equal c (- x))|))
 (35 35 (:REWRITE |(equal (/ x) c)|))
 (35 35 (:REWRITE |(equal (/ x) (/ y))|))
 (35 35 (:REWRITE |(equal (- x) c)|))
 (35 35 (:REWRITE |(equal (- x) (- y))|))
 (30 6 (:REWRITE DEFAULT-EXPT-2))
 (29 29 (:TYPE-PRESCRIPTION RTL::NORM-POP))
 (26 26
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (26 26
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (26 26 (:REWRITE |(< (/ x) 0)|))
 (26 26 (:REWRITE |(< (* x y) 0)|))
 (24 12 (:REWRITE RTL::INT-CADDR-TRIPP))
 (23 23 (:REWRITE REDUCE-RATIONALP-+))
 (23 23 (:REWRITE REDUCE-RATIONALP-*))
 (23 23 (:REWRITE RATIONALP-MINUS-X))
 (23 23 (:META META-RATIONALP-CORRECT))
 (13 13 (:REWRITE FOLD-CONSTS-IN-+))
 (13 13 (:REWRITE |(+ c (+ d x))|))
 (12 12
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (12
  12
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (12 12
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (12 12
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (12 12
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (12 12
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (12 12
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (12 12
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (12 12 (:TYPE-PRESCRIPTION EXPT))
 (12 4 (:REWRITE |(* 1 x)|))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (7 7 (:REWRITE |(< y (+ (- c) x))|))
 (7 7 (:REWRITE |(< x (+ c/d y))|))
 (7 7 (:REWRITE |(< 0 (/ x))|))
 (7 7 (:REWRITE |(< 0 (* x y))|))
 (6 6 (:REWRITE RTL::LEN-VALS))
 (6 6 (:REWRITE |(< (+ c/d x) y)|))
 (6 6 (:REWRITE |(< (+ (- c) x) y)|))
 (6 6 (:REWRITE |(+ 0 x)|))
 (5 2 (:REWRITE RTL::SHNFP-INT))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (4 4 (:REWRITE RTL::ALL-INTEGERS-VALS))
 (4 4 (:REWRITE |(expt 1/c n)|))
 (4 4 (:REWRITE |(expt (- x) n)|))
 (4 4 (:REWRITE |(* 0 x)|))
 (2 2
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS)))
(RTL::SPLIT$-CASE-2-7 (45 45 (:DEFINITION MV-NTH))
                      (4 4 (:TYPE-PRESCRIPTION RTL::TRIPP))
                      (4 4 (:TYPE-PRESCRIPTION RTL::SHNFP))
                      (4 4 (:TYPE-PRESCRIPTION RTL::ECP))
                      (4 2
                         (:TYPE-PRESCRIPTION RTL::SPLIT$-CASE-5-2))
                      (4 2
                         (:TYPE-PRESCRIPTION RTL::SPLIT$-CASE-2-2))
                      (4 2
                         (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-Y))
                      (4 2
                         (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-X))
                      (4 2
                         (:TYPE-PRESCRIPTION RTL::INT-CAR-TRIPP))
                      (4 2
                         (:TYPE-PRESCRIPTION RTL::INT-CADR-TRIPP)))
(RTL::SPLIT$-CASE-2-8
     (46784 8 (:DEFINITION RTL::NORM-ADD))
     (29729 379 (:REWRITE ACL2-NUMBERP-X))
     (16214 359 (:REWRITE RATIONALP-X))
     (12434 124 (:REWRITE DEFAULT-LESS-THAN-2))
     (9880 4940
           (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-Y))
     (9488 240 (:REWRITE DEFAULT-PLUS-1))
     (9213 9213 (:TYPE-PRESCRIPTION RTL::ECP))
     (8636 108 (:REWRITE DEFAULT-LESS-THAN-1))
     (7879 7879 (:TYPE-PRESCRIPTION RTL::TRIPP))
     (7360 64 (:REWRITE DEFAULT-MINUS))
     (7110 3555
           (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-X))
     (7110 3555
           (:TYPE-PRESCRIPTION RTL::INT-CAR-TRIPP))
     (6718 85
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (5897 2946
           (:TYPE-PRESCRIPTION RTL::SPLIT$-CASE-5-2))
     (5892 2946
           (:TYPE-PRESCRIPTION RTL::INT-CADR-TRIPP))
     (5518 260 (:REWRITE DEFAULT-PLUS-2))
     (2880 206 (:REWRITE DEFAULT-CAR))
     (1300 38 (:REWRITE DEFAULT-TIMES-1))
     (1278 316 (:REWRITE DEFAULT-CDR))
     (1244 8 (:DEFINITION RTL::NORM-EXPT))
     (1077 359 (:REWRITE RTL::INTEGERP-EC-X))
     (1077 359 (:REWRITE RTL::INT-CAR-TRIPP))
     (924 308 (:REWRITE RTL::INT-CADR-TRIPP))
     (884 40 (:REWRITE |(+ x (if a b c))|))
     (677 85 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (516 8 (:REWRITE |(< x (if a b c))|))
     (512 2 (:DEFINITION EVENP))
     (369 369 (:REWRITE REDUCE-INTEGERP-+))
     (369 369 (:REWRITE INTEGERP-MINUS-X))
     (369 369 (:META META-INTEGERP-CORRECT))
     (359 359 (:REWRITE REDUCE-RATIONALP-+))
     (359 359 (:REWRITE REDUCE-RATIONALP-*))
     (359 359 (:REWRITE RATIONALP-MINUS-X))
     (359 359 (:META META-RATIONALP-CORRECT))
     (132 28
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (124 124 (:REWRITE THE-FLOOR-BELOW))
     (124 124 (:REWRITE THE-FLOOR-ABOVE))
     (124 4 (:REWRITE |(* (if a b c) x)|))
     (101 66 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (96 96 (:TYPE-PRESCRIPTION RTL::NORM-POP))
     (88 44
         (:TYPE-PRESCRIPTION RTL::INT-CADDR-TRIPP))
     (88 10 (:REWRITE |(* y x)|))
     (85 85
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (85 85
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (85 85
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (85 85 (:REWRITE |(equal c (/ x))|))
     (85 85 (:REWRITE |(equal c (- x))|))
     (85 85 (:REWRITE |(equal (/ x) c)|))
     (85 85 (:REWRITE |(equal (/ x) (/ y))|))
     (85 85 (:REWRITE |(equal (- x) c)|))
     (85 85 (:REWRITE |(equal (- x) (- y))|))
     (76 76 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (76 76 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (76 76 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (76 76 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (75 75
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (75 75 (:REWRITE NORMALIZE-ADDENDS))
     (72 68
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (72 68
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (72 6 (:REWRITE |(* x (+ y z))|))
     (68 68
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
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
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (68 68
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (68 68
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (68 68
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (68 68 (:REWRITE |(< (/ x) (/ y))|))
     (68 68 (:REWRITE |(< (- x) c)|))
     (68 68 (:REWRITE |(< (- x) (- y))|))
     (66 66 (:REWRITE SIMPLIFY-SUMS-<))
     (40 8 (:REWRITE |(+ c (+ d x))|))
     (38 38 (:REWRITE DEFAULT-TIMES-2))
     (32 32 (:REWRITE |(+ 0 x)|))
     (28 28 (:REWRITE |(< 0 (/ x))|))
     (28 28 (:REWRITE |(< 0 (* x y))|))
     (28 2 (:REWRITE |(+ y (+ x z))|))
     (26 26
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (18 18
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (18 18
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (18 18
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (18 18 (:REWRITE |(< (/ x) 0)|))
     (18 18 (:REWRITE |(< (* x y) 0)|))
     (16 16 (:TYPE-PRESCRIPTION RTL::NORM-MUL))
     (10 4 (:REWRITE RTL::SHNFP-INT))
     (8 8 (:TYPE-PRESCRIPTION ABS))
     (8 8 (:REWRITE |(< y (+ (- c) x))|))
     (8 8 (:REWRITE |(< x (+ c/d y))|))
     (4 4 (:REWRITE FOLD-CONSTS-IN-+))
     (4 4
        (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (2 2 (:REWRITE |(equal (+ (- c) x) y)|)))
(RTL::SPLIT$-CASE-2 (52 52 (:DEFINITION MV-NTH))
                    (4 4 (:TYPE-PRESCRIPTION RTL::TRIPP))
                    (4 4 (:TYPE-PRESCRIPTION RTL::ECP))
                    (4 2
                       (:TYPE-PRESCRIPTION RTL::SPLIT$-CASE-5-2))
                    (4 2
                       (:TYPE-PRESCRIPTION RTL::SPLIT$-CASE-2-2))
                    (4 2
                       (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-Y))
                    (4 2
                       (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-X))
                    (4 2
                       (:TYPE-PRESCRIPTION RTL::INT-CAR-TRIPP))
                    (4 2
                       (:TYPE-PRESCRIPTION RTL::INT-CADR-TRIPP)))
(RTL::SPLIT$-LEMMA
 (117344 20 (:DEFINITION RTL::NORM-ADD))
 (92921 1055 (:REWRITE ACL2-NUMBERP-X))
 (60307 1064 (:REWRITE RATIONALP-X))
 (31495 548 (:REWRITE DEFAULT-LESS-THAN-2))
 (29174 14587
        (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-Y))
 (26678 834 (:REWRITE DEFAULT-PLUS-2))
 (26400 26400 (:TYPE-PRESCRIPTION RTL::ECP))
 (21852 508 (:REWRITE DEFAULT-LESS-THAN-1))
 (21288 21288 (:TYPE-PRESCRIPTION RTL::TRIPP))
 (19848 9925
        (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-X))
 (19848 9925
        (:TYPE-PRESCRIPTION RTL::INT-CAR-TRIPP))
 (18405 394
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (18400 160 (:REWRITE DEFAULT-MINUS))
 (17142 61 (:REWRITE RTL::INTEGERP-EVALH))
 (16895 7815
        (:TYPE-PRESCRIPTION RTL::SPLIT$-CASE-5-2))
 (15920 7900
        (:TYPE-PRESCRIPTION RTL::SPLIT$-CASE-2-2))
 (15690 30 (:DEFINITION RTL::SHFP))
 (15310 7655
        (:TYPE-PRESCRIPTION RTL::INT-CADR-TRIPP))
 (8508 759 (:REWRITE DEFAULT-CAR))
 (6215 621 (:REWRITE DEFAULT-TIMES-1))
 (4456 1679 (:REWRITE DEFAULT-CDR))
 (3586 10 (:REWRITE RTL::SPLIT$-CASE-5))
 (3389 1023 (:REWRITE REDUCE-RATIONALP-*))
 (3320 20 (:DEFINITION RTL::NORM-EXPT))
 (2880 990 (:REWRITE RTL::INTEGERP-EC-X))
 (2880 990 (:REWRITE RTL::INT-CAR-TRIPP))
 (2523 73 (:REWRITE ZP-OPEN))
 (2460 850 (:REWRITE RTL::INT-CADR-TRIPP))
 (2253 394 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (2109 1023 (:REWRITE REDUCE-RATIONALP-+))
 (1450 5 (:DEFINITION EVENP))
 (1432 1204 (:META META-INTEGERP-CORRECT))
 (1330 20 (:REWRITE |(< x (if a b c))|))
 (1291 1023 (:META META-RATIONALP-CORRECT))
 (1204 1204 (:REWRITE REDUCE-INTEGERP-+))
 (1204 1204 (:REWRITE INTEGERP-MINUS-X))
 (1085 31 (:DEFINITION RTL::ALL-INTEGERS))
 (1023 1023 (:REWRITE RATIONALP-MINUS-X))
 (864 40 (:DEFINITION RFIX))
 (825 15 (:REWRITE DEFAULT-EXPT-1))
 (823 41 (:REWRITE |(< x (+ c/d y))|))
 (612 8 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (603 104
      (:REWRITE RTL::ALL-INTEGERS-INTEGER))
 (602 602
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (602 602
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (602 602
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (583 8 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (569 14 (:DEFINITION NTHCDR))
 (557 8 (:REWRITE MOD-X-Y-=-X . 4))
 (557 8 (:REWRITE MOD-X-Y-=-X . 3))
 (555 5 (:REWRITE RTL::NTHCDR+))
 (548 548 (:REWRITE THE-FLOOR-BELOW))
 (548 548 (:REWRITE THE-FLOOR-ABOVE))
 (545 388
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (463 8 (:REWRITE MOD-X-Y-=-X . 2))
 (460 20 (:REWRITE |(+ (if a b c) x)|))
 (432 36 (:REWRITE RTL::CAR-NTHCDR))
 (430 394 (:REWRITE |(equal (/ x) c)|))
 (430 394 (:REWRITE |(equal (/ x) (/ y))|))
 (429 39 (:DEFINITION NTH))
 (428 8 (:REWRITE MOD-ZERO . 4))
 (416 388 (:REWRITE SIMPLIFY-SUMS-<))
 (408 398
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (408 398
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (394 394
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (394 394
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (394 394
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (394 394 (:REWRITE |(equal c (/ x))|))
 (394 394 (:REWRITE |(equal c (- x))|))
 (394 394 (:REWRITE |(equal (- x) c)|))
 (394 394 (:REWRITE |(equal (- x) (- y))|))
 (392 392 (:TYPE-PRESCRIPTION RTL::SHFP))
 (388 388
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (388 388 (:REWRITE INTEGERP-<-CONSTANT))
 (388 388 (:REWRITE CONSTANT-<-INTEGERP))
 (388 388
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (388 388
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (388 388
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (388 388
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (388 388 (:REWRITE |(< c (- x))|))
 (388 388
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (388 388
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (388 388
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (388 388
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (388 388 (:REWRITE |(< (/ x) (/ y))|))
 (388 388 (:REWRITE |(< (- x) c)|))
 (388 388 (:REWRITE |(< (- x) (- y))|))
 (369 8 (:REWRITE MOD-ZERO . 3))
 (360 180
      (:TYPE-PRESCRIPTION RTL::INT-CADDR-TRIPP))
 (357 357 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (353 31 (:REWRITE |(< y (+ (- c) x))|))
 (341 9 (:REWRITE RTL::EVALH-POW-REWRITE))
 (338 78
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (300 300
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (300 300 (:REWRITE NORMALIZE-ADDENDS))
 (291 8 (:REWRITE RTL::MOD-DOES-NOTHING))
 (290 290
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (289 8 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (289 8 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (278 139 (:REWRITE DEFAULT-DIVIDE))
 (272 152 (:REWRITE RTL::SHNFP-SHFP))
 (260 164 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (260 164 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (250 10 (:REWRITE ZIP-OPEN))
 (248 8
      (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (248 8
      (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (248 8
      (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (192 36 (:REWRITE RTL::CONSP-NTHCDR))
 (188 164 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
 (177 177
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (177 177
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (177 177
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (176 64 (:LINEAR RTL::P-IS-BIG))
 (170 5 (:REWRITE |(expt 0 n)|))
 (165 5 (:REWRITE |(+ (+ x y) z)|))
 (164 164
      (:TYPE-PRESCRIPTION RTL::RATIONALP-MOD))
 (164 164 (:TYPE-PRESCRIPTION RATIONALP-MOD))
 (164 164
      (:TYPE-PRESCRIPTION RTL::NATP-MOD-2))
 (164 164 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (164 164
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (164 164
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (164 164
      (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (164 164
      (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
 (164 164
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (164 164
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (164 164 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (164 164 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
 (164 164
      (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
 (150
   30
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (144 72
      (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
 (139 139
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (130 130
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (130 130
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (130 130 (:REWRITE |(< (/ x) 0)|))
 (130 130 (:REWRITE |(< (* x y) 0)|))
 (120 60 (:REWRITE RTL::SPLIT$-CASE-5-2))
 (120 60 (:REWRITE RTL::SPLIT$-CASE-2-2))
 (112 112 (:DEFINITION MV-NTH))
 (108 36 (:REWRITE |(equal x (/ y))|))
 (106 106
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (95 15 (:REWRITE |(+ c (+ d x))|))
 (87 1 (:REWRITE RTL::SHFP-POP-POW-ATOM))
 (78 78 (:REWRITE |(< 0 (/ x))|))
 (78 78 (:REWRITE |(< 0 (* x y))|))
 (75 15 (:REWRITE DEFAULT-EXPT-2))
 (73 73
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (72 36 (:REWRITE |(not (equal x (/ y)))|))
 (70 70
     (:TYPE-PRESCRIPTION RTL::SPLIT$-CASE-5-7))
 (70 5 (:REWRITE |(+ y (+ x z))|))
 (64 32 (:REWRITE DEFAULT-MOD-2))
 (62 31 (:REWRITE RTL::ALL-INTEGERS-NTHCDR))
 (60 60 (:REWRITE RTL::LEN-VALS))
 (60 30 (:REWRITE RTL::INT-CADDR-TRIPP))
 (60 15 (:REWRITE RTL::SHNFP-INT))
 (55 55 (:REWRITE RTL::ALL-INTEGERS-VALS))
 (52 52 (:TYPE-PRESCRIPTION RTL::NATP-Y2))
 (52 52 (:TYPE-PRESCRIPTION RTL::NATP-Y1))
 (52 52 (:TYPE-PRESCRIPTION RTL::NATP-Y0))
 (52 52 (:TYPE-PRESCRIPTION RTL::NATP-X2))
 (52 52 (:TYPE-PRESCRIPTION RTL::NATP-X1))
 (52 52 (:TYPE-PRESCRIPTION RTL::NATP-X0))
 (52 1
     (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 1))
 (42 42 (:REWRITE |(* c (* d x))|))
 (40 40 (:TYPE-PRESCRIPTION RTL::NORM-POP))
 (40 40 (:TYPE-PRESCRIPTION RTL::NORM-MUL))
 (40 40 (:TYPE-PRESCRIPTION RTL::NATP-P-1/2))
 (30 30
     (:TYPE-PRESCRIPTION RTL::SPLIT$-CASE-5-6))
 (30 30
     (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (30 30
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE))
 (30 30
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (30
  30
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (30 30
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (30 30
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (30 30
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (30 30
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (30 30
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (30 30
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (30 30
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (30 30 (:TYPE-PRESCRIPTION EXPT))
 (24 24 (:TYPE-PRESCRIPTION NATP))
 (20 20 (:TYPE-PRESCRIPTION ABS))
 (20 10 (:REWRITE |(* a (/ a) b)|))
 (15 10 (:REWRITE |(* 1 x)|))
 (11 11
     (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (10 10 (:REWRITE RTL::P-NAT))
 (10 10 (:REWRITE RTL::NATP-Y2))
 (10 10 (:REWRITE RTL::NATP-Y1))
 (10 10 (:REWRITE RTL::NATP-Y0))
 (10 10 (:REWRITE RTL::NATP-X2))
 (10 10 (:REWRITE RTL::NATP-X1))
 (10 10 (:REWRITE RTL::NATP-X0))
 (10 10 (:REWRITE RTL::NATP-P-1/2))
 (10 10 (:REWRITE |(expt 1/c n)|))
 (10 10 (:REWRITE |(expt (- x) n)|))
 (8 8
    (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (8 8 (:REWRITE |(mod x (- y))| . 3))
 (8 8 (:REWRITE |(mod x (- y))| . 2))
 (8 8 (:REWRITE |(mod x (- y))| . 1))
 (8 8
    (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (8 8
    (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (5 5 (:REWRITE FOLD-CONSTS-IN-+))
 (4 4 (:REWRITE INTEGERP-/))
 (4 4 (:REWRITE |(< (+ c/d x) y)|))
 (4 4 (:REWRITE |(< (+ (- c) x) y)|))
 (3 3 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (2 2
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (1 1 (:REWRITE RTL::DISTINCT-SYMBOLS-ATOM))
 (1 1
    (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 3))
 (1 1
    (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 2))
 (1 1 (:REWRITE |(equal (+ (- c) x) y)|))
 (1 1 (:REWRITE |(equal (* x y) 0)|)))
(RTL::REWRITE$)
(RTL::EVALH$-NORM-VAR (9 6 (:REWRITE DEFAULT-TIMES-2))
                      (9 6 (:REWRITE DEFAULT-TIMES-1))
                      (9 6 (:REWRITE DEFAULT-PLUS-2))
                      (9 6 (:REWRITE DEFAULT-PLUS-1))
                      (6 6 (:REWRITE DEFAULT-CDR))
                      (6 3 (:REWRITE DEFAULT-EXPT-1))
                      (3 3 (:REWRITE DEFAULT-EXPT-2))
                      (3 3 (:REWRITE DEFAULT-CAR))
                      (3 3 (:REWRITE |(expt 1/c n)|))
                      (3 3 (:REWRITE |(expt (- x) n)|))
                      (2 2
                         (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-X))
                      (2 2
                         (:TYPE-PRESCRIPTION RTL::INT-CAR-TRIPP)))
(RTL::REWRITE$-LEMMA
 (289856 56 (:DEFINITION RTL::NORM-ADD))
 (257800 20 (:DEFINITION RTL::SPLIT$))
 (122640 240 (:DEFINITION RTL::SHFP))
 (100642 50321
         (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-Y))
 (87005 87005 (:TYPE-PRESCRIPTION RTL::ECP))
 (63964 1525 (:REWRITE DEFAULT-LESS-THAN-2))
 (62483 1517
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (62254 31146
        (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-X))
 (58708 2226 (:REWRITE DEFAULT-PLUS-1))
 (57827 1445 (:REWRITE DEFAULT-LESS-THAN-1))
 (49313 23441
        (:TYPE-PRESCRIPTION RTL::SPLIT$-CASE-2-2))
 (44320 424 (:REWRITE DEFAULT-MINUS))
 (42124 21062
        (:TYPE-PRESCRIPTION RTL::INT-CADR-TRIPP))
 (28769 2300 (:REWRITE DEFAULT-TIMES-1))
 (27988 3372 (:REWRITE DEFAULT-CAR))
 (23813 3285 (:REWRITE REDUCE-RATIONALP-*))
 (17814 8909 (:REWRITE DEFAULT-CDR))
 (8724 3148 (:REWRITE RTL::INTEGERP-EC-X))
 (8724 3148 (:REWRITE RTL::INT-CAR-TRIPP))
 (7412 92 (:DEFINITION EQL))
 (7180 100 (:REWRITE ZP-OPEN))
 (6816 2512 (:REWRITE RTL::INT-CADR-TRIPP))
 (6640 40 (:DEFINITION RTL::NORM-EXPT))
 (6358 1509 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (6172 60 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (5959 3285 (:REWRITE REDUCE-RATIONALP-+))
 (5727 60 (:REWRITE MOD-ZERO . 4))
 (5624 232 (:REWRITE |(+ x (if a b c))|))
 (5292 5156 (:META META-INTEGERP-CORRECT))
 (5156 5156 (:REWRITE REDUCE-INTEGERP-+))
 (5156 5156 (:REWRITE INTEGERP-MINUS-X))
 (4975 60 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (4975 60 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (4813 60 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (4120 60 (:REWRITE MOD-ZERO . 3))
 (3605 3285 (:META META-RATIONALP-CORRECT))
 (3575 923 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (3575 923 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (3498 60 (:REWRITE MOD-X-Y-=-X . 4))
 (3290 10 (:REWRITE RTL::SPLIT$-CASE-4-1))
 (3285 3285 (:REWRITE RATIONALP-MINUS-X))
 (3005 1131
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (2900 10 (:DEFINITION EVENP))
 (2880 1440
       (:TYPE-PRESCRIPTION RTL::INT-CADDR-TRIPP))
 (2779 60
       (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (2779 60
       (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (2779 60
       (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (2660 40 (:REWRITE |(< x (if a b c))|))
 (2154 2154
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (2154 2154
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (2154 2154
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (1966 1131 (:REWRITE SIMPLIFY-SUMS-<))
 (1904 80 (:LINEAR MOD-BOUNDS-2))
 (1820 20 (:REWRITE MOD-X-Y-=-X-Y . 1))
 (1650
   330
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (1624 60 (:REWRITE MOD-X-Y-=-X . 3))
 (1586 923 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
 (1577 1517 (:REWRITE |(equal (/ x) c)|))
 (1577 1517 (:REWRITE |(equal (/ x) (/ y))|))
 (1525 1525 (:REWRITE THE-FLOOR-BELOW))
 (1525 1525 (:REWRITE THE-FLOOR-ABOVE))
 (1525 1517 (:REWRITE |(equal (- x) c)|))
 (1525 1517 (:REWRITE |(equal (- x) (- y))|))
 (1517 1517
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (1517 1517
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (1517 1517
       (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (1517 1517 (:REWRITE |(equal c (/ x))|))
 (1517 1517 (:REWRITE |(equal c (- x))|))
 (1498 1498
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (1498 1498
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (1498 1498
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (1376 688 (:REWRITE DEFAULT-DIVIDE))
 (1174 84 (:REWRITE DEFAULT-MOD-1))
 (1161 1141
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (1161 1141
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (1136 40 (:LINEAR MOD-BOUNDS-3))
 (1131 1131
       (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (1131 1131 (:REWRITE INTEGERP-<-CONSTANT))
 (1131 1131 (:REWRITE CONSTANT-<-INTEGERP))
 (1131 1131
       (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (1131 1131
       (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (1131 1131
       (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (1131 1131
       (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (1131 1131 (:REWRITE |(< c (- x))|))
 (1131 1131
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (1131 1131
       (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (1131 1131
       (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (1131 1131
       (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (1131 1131 (:REWRITE |(< (/ x) (/ y))|))
 (1131 1131 (:REWRITE |(< (- x) c)|))
 (1131 1131 (:REWRITE |(< (- x) (- y))|))
 (1074 722 (:REWRITE NORMALIZE-ADDENDS))
 (1056 1056
       (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (1022 1022
       (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (960 480 (:REWRITE RTL::SPLIT$-CASE-5-2))
 (960 480 (:REWRITE RTL::SPLIT$-CASE-2-2))
 (923 923
      (:TYPE-PRESCRIPTION RTL::RATIONALP-MOD))
 (923 923 (:TYPE-PRESCRIPTION RATIONALP-MOD))
 (923 923
      (:TYPE-PRESCRIPTION RTL::NATP-MOD-2))
 (923 923 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (923 923
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (923 923
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (923 923
      (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (923 923
      (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
 (923 923
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (923 923
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (923 923 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (923 923 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
 (923 923
      (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
 (916 20 (:REWRITE MOD-X-Y-=-X+Y . 1))
 (840 50 (:REWRITE |(< x (+ c/d y))|))
 (802 66 (:DEFINITION RFIX))
 (792 9
      (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 1))
 (777 257
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (714 714
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (688 688
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (672 60 (:REWRITE MOD-X-Y-=-X . 2))
 (663 663 (:TYPE-PRESCRIPTION NATP))
 (624 60
      (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (624 60
      (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (624 60
      (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (607 607
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (607 607
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (607 607 (:REWRITE |(< (/ x) 0)|))
 (607 607 (:REWRITE |(< (* x y) 0)|))
 (560 32 (:LINEAR RTL::MOD-BND-2))
 (480 240 (:REWRITE RTL::INT-CADDR-TRIPP))
 (466 106 (:REWRITE DEFAULT-EXPT-2))
 (432 432 (:TYPE-PRESCRIPTION RTL::NORM-MUL))
 (370 40 (:REWRITE |(< y (+ (- c) x))|))
 (330 330
      (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (330 330
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE))
 (330 330
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (330
  330
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (330 330
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (330 330
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (330 330
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (330
     330
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (330 330
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (330 330
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (330 330
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (330 330 (:TYPE-PRESCRIPTION EXPT))
 (320 320 (:TYPE-PRESCRIPTION RTL::NORM-ADD))
 (288 8 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
 (257 257 (:REWRITE |(< 0 (/ x))|))
 (257 257 (:REWRITE |(< 0 (* x y))|))
 (247 247
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (224 224
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (188 28 (:REWRITE |(+ c (+ d x))|))
 (180 60 (:REWRITE |(equal x (/ y))|))
 (168 84 (:REWRITE DEFAULT-MOD-2))
 (136 20
      (:REWRITE |(equal (mod (+ x y) z) x)|))
 (120 60 (:REWRITE |(not (equal x (/ y)))|))
 (112 28 (:REWRITE RTL::SHNFP-INT))
 (96 32 (:LINEAR RTL::MOD-BND-1))
 (87 87 (:REWRITE |(* c (* d x))|))
 (80 80 (:TYPE-PRESCRIPTION RTL::NORM-POP))
 (75 75 (:REWRITE |(expt 1/c n)|))
 (75 75 (:REWRITE |(expt (- x) n)|))
 (64 20 (:REWRITE MOD-ZERO . 2))
 (60 60 (:TYPE-PRESCRIPTION RTL::NATP-Y2))
 (60 60 (:TYPE-PRESCRIPTION RTL::NATP-Y1))
 (60 60 (:TYPE-PRESCRIPTION RTL::NATP-Y0))
 (60 60 (:TYPE-PRESCRIPTION RTL::NATP-X2))
 (60 60 (:TYPE-PRESCRIPTION RTL::NATP-X1))
 (60 60 (:TYPE-PRESCRIPTION RTL::NATP-X0))
 (60 60 (:REWRITE |(mod x (- y))| . 3))
 (60 60 (:REWRITE |(mod x (- y))| . 2))
 (60 60 (:REWRITE |(mod x (- y))| . 1))
 (60 4 (:REWRITE INTP-3))
 (56 8 (:REWRITE MOD-NEGATIVE . 3))
 (40 40 (:TYPE-PRESCRIPTION RTL::NATP-P-1/2))
 (40 40 (:TYPE-PRESCRIPTION ABS))
 (36 36 (:TYPE-PRESCRIPTION FIX))
 (32 32 (:LINEAR RTL::MOD-BND-3))
 (32 16 (:DEFINITION FIX))
 (28 4 (:REWRITE MOD-POSITIVE . 3))
 (28 4 (:REWRITE MOD-NONPOSITIVE))
 (28 4 (:REWRITE MOD-NONNEGATIVE))
 (28 4 (:REWRITE INTP-1))
 (24 20 (:REWRITE MOD-ZERO . 1))
 (20 20 (:TYPE-PRESCRIPTION INTP-*))
 (20 20
     (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (20 10 (:REWRITE |(* a (/ a) b)|))
 (16 16 (:REWRITE |(equal (+ (- c) x) y)|))
 (16 8 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (16 8 (:REWRITE MOD-NEGATIVE . 2))
 (10 10 (:REWRITE RTL::P-NAT))
 (10 10 (:REWRITE RTL::NATP-Y2))
 (10 10 (:REWRITE RTL::NATP-Y1))
 (10 10 (:REWRITE RTL::NATP-Y0))
 (10 10 (:REWRITE RTL::NATP-X2))
 (10 10 (:REWRITE RTL::NATP-X1))
 (10 10 (:REWRITE RTL::NATP-X0))
 (10 10 (:REWRITE RTL::NATP-P-1/2))
 (9 9
    (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 3))
 (9 9
    (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 2))
 (9 9 (:REWRITE |(< (+ c/d x) y)|))
 (9 9 (:REWRITE |(< (+ (- c) x) y)|))
 (8 8 (:REWRITE MOD-NEGATIVE . 1))
 (8 8 (:REWRITE |(+ x (- x))|))
 (8 4 (:REWRITE MOD-POSITIVE . 2))
 (6 6 (:REWRITE INTEGERP-/))
 (6 6 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (4 4 (:REWRITE MOD-POSITIVE . 1))
 (4 4 (:REWRITE META-INTEGERP-UNHIDE-HIDE)))
(RTL::REDUCE$)
(RTL::POLYP$)
(RTL::EVALH$-EVALP$
     (12628 1 (:DEFINITION RTL::NORM))
     (11672 2 (:DEFINITION RTL::NORM-ADD))
     (8388 183 (:REWRITE ACL2-NUMBERP-X))
     (8244 3626
           (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-Y))
     (6422 2 (:DEFINITION RTL::EVALP))
     (4931 4931 (:TYPE-PRESCRIPTION RTL::ECP))
     (4738 14 (:DEFINITION ASSOC-EQUAL))
     (4476 179 (:REWRITE RATIONALP-X))
     (4140 175 (:REWRITE DEFAULT-CAR))
     (3843 349 (:REWRITE DEFAULT-CDR))
     (3094 26 (:REWRITE DEFAULT-LESS-THAN-2))
     (3051 82
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (2352 64 (:REWRITE DEFAULT-PLUS-1))
     (2203 1091
           (:TYPE-PRESCRIPTION RTL::INT-CAR-TRIPP))
     (2195 2195 (:TYPE-PRESCRIPTION RTL::TRIPP))
     (2182 1091
           (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-X))
     (2154 22 (:REWRITE DEFAULT-LESS-THAN-1))
     (1978 28 (:REWRITE DEFAULT-MINUS))
     (1620 707
           (:TYPE-PRESCRIPTION RTL::SPLIT$-CASE-2-2))
     (1418 1418 (:TYPE-PRESCRIPTION RTL::SHNFP))
     (1414 707
           (:TYPE-PRESCRIPTION RTL::SPLIT$-CASE-5-2))
     (1414 707
           (:TYPE-PRESCRIPTION RTL::INT-CADR-TRIPP))
     (1285 70 (:REWRITE DEFAULT-PLUS-2))
     (1078 1078 (:TYPE-PRESCRIPTION RTL::VALS))
     (783 1 (:DEFINITION RTL::POLYP))
     (578 2 (:DEFINITION RTL::NORM-NEG))
     (321 107 (:REWRITE RTL::INTEGERP-EC-X))
     (321 107 (:REWRITE RTL::INT-CAR-TRIPP))
     (236 6 (:DEFINITION MEMBER-EQUAL))
     (230 82 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (219 73 (:REWRITE RTL::INT-CADR-TRIPP))
     (218 10 (:REWRITE |(+ x (if a b c))|))
     (179 179 (:REWRITE REDUCE-RATIONALP-+))
     (179 179 (:REWRITE REDUCE-RATIONALP-*))
     (179 179 (:REWRITE RATIONALP-MINUS-X))
     (179 179 (:META META-RATIONALP-CORRECT))
     (154 154 (:REWRITE REDUCE-INTEGERP-+))
     (154 154 (:REWRITE INTEGERP-MINUS-X))
     (154 154 (:META META-INTEGERP-CORRECT))
     (104 1 (:REWRITE RTL::EVALH-POW-REWRITE))
     (94 1 (:DEFINITION EQL))
     (88 6 (:REWRITE DEFAULT-EXPT-2))
     (84 6 (:REWRITE DEFAULT-TIMES-2))
     (82 82
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (82 82
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (82 82
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (82 82 (:REWRITE |(equal c (/ x))|))
     (82 82 (:REWRITE |(equal c (- x))|))
     (82 82 (:REWRITE |(equal (/ x) c)|))
     (82 82 (:REWRITE |(equal (/ x) (/ y))|))
     (82 82 (:REWRITE |(equal (- x) c)|))
     (82 82 (:REWRITE |(equal (- x) (- y))|))
     (76 1 (:DEFINITION NATP))
     (72 4 (:REWRITE DEFAULT-EXPT-1))
     (70 35
         (:TYPE-PRESCRIPTION RTL::INT-CADDR-TRIPP))
     (60 14 (:REWRITE |(+ y x)|))
     (55 55 (:TYPE-PRESCRIPTION RTL::NORM))
     (44 4 (:REWRITE DEFAULT-TIMES-1))
     (42 1 (:DEFINITION RTL::NORM-EXPT))
     (36 36 (:REWRITE CAR-CONS))
     (35 1 (:REWRITE ZP-OPEN))
     (26 26 (:REWRITE THE-FLOOR-BELOW))
     (26 26 (:REWRITE THE-FLOOR-ABOVE))
     (26 2 (:REWRITE ZIP-OPEN))
     (24 12 (:REWRITE RTL::MEMBER-LEN-POS))
     (18 18
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (18 18 (:REWRITE NORMALIZE-ADDENDS))
     (14 14 (:REWRITE SIMPLIFY-SUMS-<))
     (14 14 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (14 14
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (14 14
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (14 14
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (14 14 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
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
     (12 12 (:REWRITE CDR-CONS))
     (11 11 (:REWRITE RTL::PERM-MEMBER))
     (10 10 (:REWRITE |(+ 0 x)|))
     (7 1 (:DEFINITION LEN))
     (6 2 (:REWRITE RTL::SHNFP-INT))
     (6 1 (:REWRITE RTL::SPLIT$-CASE-5-2))
     (6 1 (:REWRITE RTL::SPLIT$-CASE-2-2))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (5 5 (:REWRITE |(< 0 (/ x))|))
     (5 5 (:REWRITE |(< 0 (* x y))|))
     (5 5 (:REWRITE |(< (/ x) 0)|))
     (5 5 (:REWRITE |(< (* x y) 0)|))
     (4 1 (:DEFINITION TRUE-LISTP))
     (3 1 (:REWRITE RTL::INT-CADDR-TRIPP))
     (2 2 (:TYPE-PRESCRIPTION RTL::NORM-NEG))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (2 2
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (2 2 (:REWRITE |(expt 1/c n)|))
     (2 2 (:REWRITE |(expt (- x) n)|)))
(RTL::SHNFP-NORM-POLYP)
(RTL::REDUCE$-CORRECT
     (25000 2 (:DEFINITION RTL::NORM))
     (23152 4 (:DEFINITION RTL::NORM-ADD))
     (15680 264 (:REWRITE ACL2-NUMBERP-X))
     (8616 259 (:REWRITE RATIONALP-X))
     (6202 62 (:REWRITE DEFAULT-LESS-THAN-2))
     (5116 106
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (4783 4783 (:TYPE-PRESCRIPTION RTL::ECP))
     (4752 2375
           (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-Y))
     (4596 116 (:REWRITE DEFAULT-PLUS-1))
     (4318 54 (:REWRITE DEFAULT-LESS-THAN-1))
     (4048 4048 (:TYPE-PRESCRIPTION RTL::TRIPP))
     (4012 2000
           (:TYPE-PRESCRIPTION RTL::INT-CAR-TRIPP))
     (4000 2000
           (:TYPE-PRESCRIPTION RTL::INTEGERP-EC-X))
     (3860 48 (:REWRITE DEFAULT-MINUS))
     (2672 1336
           (:TYPE-PRESCRIPTION RTL::SPLIT$-CASE-5-2))
     (2672 1336
           (:TYPE-PRESCRIPTION RTL::INT-CADR-TRIPP))
     (2460 126 (:REWRITE DEFAULT-PLUS-2))
     (1600 146 (:REWRITE DEFAULT-CAR))
     (1218 2 (:DEFINITION RTL::EVALP))
     (1092 4 (:DEFINITION RTL::NORM-NEG))
     (803 220 (:REWRITE DEFAULT-CDR))
     (612 204 (:REWRITE RTL::INTEGERP-EC-X))
     (612 204 (:REWRITE RTL::INT-CAR-TRIPP))
     (579 259 (:REWRITE REDUCE-RATIONALP-*))
     (438 146 (:REWRITE RTL::INT-CADR-TRIPP))
     (414 18 (:REWRITE |(+ x (if a b c))|))
     (406 106 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (271 271 (:REWRITE REDUCE-INTEGERP-+))
     (271 271 (:REWRITE INTEGERP-MINUS-X))
     (271 271 (:META META-INTEGERP-CORRECT))
     (259 259 (:REWRITE REDUCE-RATIONALP-+))
     (259 259 (:REWRITE RATIONALP-MINUS-X))
     (259 259 (:META META-RATIONALP-CORRECT))
     (174 66 (:REWRITE DEFAULT-TIMES-2))
     (134 64 (:REWRITE DEFAULT-TIMES-1))
     (122 2 (:DEFINITION ASSOC-EQUAL))
     (114 106 (:REWRITE |(equal (/ x) c)|))
     (114 106 (:REWRITE |(equal (/ x) (/ y))|))
     (112 26 (:REWRITE |(+ y x)|))
     (108 2 (:DEFINITION MEMBER-EQUAL))
     (106 106
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (106 106
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (106 106
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (106 106 (:REWRITE |(equal c (/ x))|))
     (106 106 (:REWRITE |(equal c (- x))|))
     (106 106 (:REWRITE |(equal (- x) c)|))
     (106 106 (:REWRITE |(equal (- x) (- y))|))
     (104 2 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (98 2 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (90 2 (:REWRITE MOD-X-Y-=-X . 4))
     (90 2 (:REWRITE MOD-X-Y-=-X . 3))
     (88 6 (:REWRITE DEFAULT-EXPT-2))
     (84 2 (:DEFINITION RTL::NORM-EXPT))
     (78 2 (:REWRITE MOD-X-Y-=-X . 2))
     (72 4 (:REWRITE DEFAULT-EXPT-1))
     (70 14 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (70 14 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (70 2 (:REWRITE ZP-OPEN))
     (64 64 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (64 64 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (64 64 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (64 2 (:REWRITE RTL::MEMBER-LEN-POS))
     (62 62 (:REWRITE THE-FLOOR-BELOW))
     (62 62 (:REWRITE THE-FLOOR-ABOVE))
     (60 30 (:REWRITE DEFAULT-DIVIDE))
     (60 2 (:REWRITE RTL::MOD-DOES-NOTHING))
     (58 2 (:REWRITE MOD-ZERO . 4))
     (52 2 (:REWRITE MOD-ZERO . 3))
     (48 48 (:TYPE-PRESCRIPTION RTL::NORM))
     (44 8 (:DEFINITION RFIX))
     (42 38 (:REWRITE SIMPLIFY-SUMS-<))
     (42 38 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (38 38
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (38 38
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (38 38
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (38 38 (:REWRITE INTEGERP-<-CONSTANT))
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
     (38 2 (:DEFINITION =))
     (36 4 (:DEFINITION LEN))
     (36 2 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (36 2 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (34 34 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (34 34
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (34 34 (:REWRITE NORMALIZE-ADDENDS))
     (34 2
         (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (34 2
         (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (34 2
         (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (32 32
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (30 30
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (28 14 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
     (26 2 (:REWRITE ZIP-OPEN))
     (24 24
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (24 8 (:REWRITE |(equal x (/ y))|))
     (22 22 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (22 22 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (22 22 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (18 18 (:REWRITE |(+ 0 x)|))
     (16 8
         (:TYPE-PRESCRIPTION RTL::INT-CADDR-TRIPP))
     (16 8 (:REWRITE |(not (equal x (/ y)))|))
     (15 15 (:TYPE-PRESCRIPTION RTL::VARS))
     (15 2 (:DEFINITION TRUE-LISTP))
     (14 14
         (:TYPE-PRESCRIPTION RTL::RATIONALP-MOD))
     (14 14 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (14 14 (:TYPE-PRESCRIPTION RTL::NATP-MOD-2))
     (14 14 (:TYPE-PRESCRIPTION NATP))
     (14 14 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (14 14
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (14 14
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (14 14 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (14 14 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
     (14 14
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (14 14
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (14 14 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (14 14 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (14 14
         (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
     (14 14
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (14 14
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (14 14 (:REWRITE |(< (/ x) 0)|))
     (14 14 (:REWRITE |(< (* x y) 0)|))
     (14 6 (:LINEAR RTL::P-IS-BIG))
     (12 12
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (12 12
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (12 12 (:REWRITE |(< 0 (/ x))|))
     (12 12 (:REWRITE |(< 0 (* x y))|))
     (12 6 (:REWRITE DEFAULT-MOD-2))
     (12 4 (:REWRITE RTL::SHNFP-INT))
     (12 2 (:REWRITE RTL::SPLIT$-CASE-5-2))
     (12 2 (:REWRITE RTL::SPLIT$-CASE-2-2))
     (6 2 (:REWRITE RTL::INT-CADDR-TRIPP))
     (4 4 (:TYPE-PRESCRIPTION RTL::VLIST))
     (4 4 (:TYPE-PRESCRIPTION RTL::NORM-NEG))
     (4 4 (:REWRITE RTL::PERM-MEMBER))
     (2 2
        (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (2 2 (:REWRITE |(mod x (- y))| . 3))
     (2 2 (:REWRITE |(mod x (- y))| . 2))
     (2 2 (:REWRITE |(mod x (- y))| . 1))
     (2 2
        (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (2 2
        (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (2 2 (:REWRITE |(expt 1/c n)|))
     (2 2 (:REWRITE |(expt (- x) n)|)))
