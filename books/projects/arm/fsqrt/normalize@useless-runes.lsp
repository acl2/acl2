(RTL::SIGA-1)
(RTL::BS*)
(RTL::SIGA* (2 2 (:TYPE-PRESCRIPTION RTL::SI))
            (2 2 (:TYPE-PRESCRIPTION RTL::INT-SI)))
(RTL::EXPSHFT* (2 2 (:TYPE-PRESCRIPTION RTL::SI))
               (2 2 (:TYPE-PRESCRIPTION RTL::INT-SI)))
(RTL::EXPQ* (2 2 (:TYPE-PRESCRIPTION RTL::SI))
            (2 2 (:TYPE-PRESCRIPTION RTL::INT-SI)))
(RTL::NORMALIZE-LEMMA)
(RTL::INTEGERP-SIGA)
(A)
(P)
(E)
(RTL::BS)
(RTL::BS*-REWRITE
 (135 15 (:REWRITE ACL2-NUMBERP-X))
 (82 2 (:LINEAR EXPT->=-1-ONE))
 (82 2 (:LINEAR EXPT-<=-1-TWO))
 (80 8 (:REWRITE |(< y (+ (- c) x))|))
 (80 2 (:LINEAR EXPT->-1-ONE))
 (80 2 (:LINEAR EXPT-<-1-TWO))
 (72 2 (:LINEAR EXPT-X->=-X))
 (72 2 (:LINEAR EXPT-X->-X))
 (60 15 (:REWRITE RATIONALP-X))
 (40 4 (:REWRITE |(< (+ (- c) x) y)|))
 (30 3
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
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
 (15 15 (:REWRITE REDUCE-RATIONALP-+))
 (15 15 (:REWRITE REDUCE-RATIONALP-*))
 (15 15 (:REWRITE REDUCE-INTEGERP-+))
 (15 15 (:REWRITE RATIONALP-MINUS-X))
 (15 15 (:REWRITE INTEGERP-MINUS-X))
 (15 15 (:META META-RATIONALP-CORRECT))
 (15 15 (:META META-INTEGERP-CORRECT))
 (12 12 (:REWRITE THE-FLOOR-BELOW))
 (12 12 (:REWRITE THE-FLOOR-ABOVE))
 (12 12 (:REWRITE SIMPLIFY-SUMS-<))
 (12 12
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (12 12
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (12 12
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (12 12
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (12 12 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (12 12 (:REWRITE INTEGERP-<-CONSTANT))
 (12 12 (:REWRITE DEFAULT-LESS-THAN-2))
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
 (9 3 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (8 8 (:REWRITE |(< x (+ c/d y))|))
 (6 6 (:TYPE-PRESCRIPTION BOOLEANP))
 (4 4 (:REWRITE SUBSETP-MEMBER . 4))
 (4 4 (:REWRITE SUBSETP-MEMBER . 3))
 (4 4 (:REWRITE SUBSETP-MEMBER . 2))
 (4 4 (:REWRITE SUBSETP-MEMBER . 1))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (4 4 (:REWRITE |(< 0 (/ x))|))
 (4 4 (:REWRITE |(< 0 (* x y))|))
 (4 4 (:REWRITE |(< (/ x) 0)|))
 (4 4 (:REWRITE |(< (+ c/d x) y)|))
 (4 4 (:REWRITE |(< (* x y) 0)|))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
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
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-ONE))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RTL::OPZ-OPW (50 5
                  (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
              (45 5 (:REWRITE ACL2-NUMBERP-X))
              (20 5 (:REWRITE RATIONALP-X))
              (15 5 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
              (10 10 (:TYPE-PRESCRIPTION BOOLEANP))
              (5 5 (:REWRITE SUBSETP-MEMBER . 4))
              (5 5 (:REWRITE SUBSETP-MEMBER . 3))
              (5 5 (:REWRITE SUBSETP-MEMBER . 2))
              (5 5 (:REWRITE SUBSETP-MEMBER . 1))
              (5 5 (:REWRITE SIMPLIFY-SUMS-EQUAL))
              (5 5 (:REWRITE REDUCE-RATIONALP-+))
              (5 5 (:REWRITE REDUCE-RATIONALP-*))
              (5 5
                 (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
              (5 5 (:REWRITE REDUCE-INTEGERP-+))
              (5 5
                 (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
              (5 5 (:REWRITE RATIONALP-MINUS-X))
              (5 5 (:REWRITE INTEGERP-MINUS-X))
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
              (1 1
                 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RTL::SPEC-FIELDS (32 3
                      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                  (29 5 (:REWRITE ACL2-NUMBERP-X))
                  (12 3 (:REWRITE RATIONALP-X))
                  (7 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                  (7 3 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
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
                  (3 3 (:REWRITE |(equal c (/ x))|))
                  (3 3 (:REWRITE |(equal c (- x))|))
                  (3 3 (:REWRITE |(equal (/ x) c)|))
                  (3 3 (:REWRITE |(equal (/ x) (/ y))|))
                  (3 3 (:REWRITE |(equal (- x) c)|))
                  (3 3 (:REWRITE |(equal (- x) (- y))|))
                  (3 3 (:META META-RATIONALP-CORRECT))
                  (3 3 (:META META-INTEGERP-CORRECT))
                  (2 2 (:TYPE-PRESCRIPTION BOOLEANP))
                  (1 1
                     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RTL::SPEC-CLASS (60 6
                     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                 (54 6 (:REWRITE ACL2-NUMBERP-X))
                 (24 6 (:REWRITE RATIONALP-X))
                 (18 6 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
                 (12 12 (:TYPE-PRESCRIPTION BOOLEANP))
                 (7 7 (:REWRITE SUBSETP-MEMBER . 4))
                 (7 7 (:REWRITE SUBSETP-MEMBER . 3))
                 (7 7 (:REWRITE SUBSETP-MEMBER . 2))
                 (7 7 (:REWRITE SUBSETP-MEMBER . 1))
                 (6 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                 (6 6 (:REWRITE REDUCE-RATIONALP-+))
                 (6 6 (:REWRITE REDUCE-RATIONALP-*))
                 (6 6
                    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                 (6 6 (:REWRITE REDUCE-INTEGERP-+))
                 (6 6
                    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
                 (6 6 (:REWRITE RATIONALP-MINUS-X))
                 (6 6 (:REWRITE INTEGERP-MINUS-X))
                 (6 6
                    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
                 (6 6 (:REWRITE |(equal c (/ x))|))
                 (6 6 (:REWRITE |(equal c (- x))|))
                 (6 6 (:REWRITE |(equal (/ x) c)|))
                 (6 6 (:REWRITE |(equal (/ x) (/ y))|))
                 (6 6 (:REWRITE |(equal (- x) c)|))
                 (6 6 (:REWRITE |(equal (- x) (- y))|))
                 (6 6 (:META META-RATIONALP-CORRECT))
                 (6 6 (:META META-INTEGERP-CORRECT))
                 (1 1
                    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RTL::A-NORMP (69 2 (:REWRITE |(< (if a b c) x)|))
              (51 2 (:REWRITE |(< (+ (- c) x) y)|))
              (46 1 (:REWRITE RTL::NEG-BITN-0))
              (43 1 (:DEFINITION NATP))
              (39 1 (:REWRITE RTL::BITN-NEG))
              (18 2 (:REWRITE ACL2-NUMBERP-X))
              (8 2 (:REWRITE RATIONALP-X))
              (6 6 (:REWRITE THE-FLOOR-BELOW))
              (6 6 (:REWRITE THE-FLOOR-ABOVE))
              (6 6 (:REWRITE DEFAULT-LESS-THAN-2))
              (6 6 (:REWRITE DEFAULT-LESS-THAN-1))
              (6 3
                 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
              (6 3 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
              (5 1 (:REWRITE RTL::NEG-BITN-1))
              (4 4
                 (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
              (4 4
                 (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
              (4 4 (:REWRITE REDUCE-INTEGERP-+))
              (4 4 (:REWRITE INTEGERP-MINUS-X))
              (4 4 (:META META-INTEGERP-CORRECT))
              (3 3
                 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
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
              (3 1 (:REWRITE RTL::BVECP-BITN-0))
              (2 2 (:TYPE-PRESCRIPTION RTL::OPAW))
              (2 2 (:TYPE-PRESCRIPTION RTL::BVECP))
              (2 2 (:REWRITE SIMPLIFY-SUMS-<))
              (2 2
                 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
              (2 2 (:REWRITE REMOVE-STRICT-INEQUALITIES))
              (2 2 (:REWRITE REDUCE-RATIONALP-+))
              (2 2 (:REWRITE REDUCE-RATIONALP-*))
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
              (2 2 (:REWRITE |(< (+ c/d x) y)|))
              (2 2 (:REWRITE |(< (* x y) 0)|))
              (2 2 (:META META-RATIONALP-CORRECT))
              (1 1 (:TYPE-PRESCRIPTION NATP))
              (1 1 (:REWRITE REMOVE-WEAK-INEQUALITIES))
              (1 1
                 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
              (1 1 (:REWRITE NORMALIZE-ADDENDS))
              (1 1 (:REWRITE DEFAULT-PLUS-1)))
(RTL::A-DENORMP
 (69 2 (:REWRITE |(< (if a b c) x)|))
 (51 2 (:REWRITE |(< (+ (- c) x) y)|))
 (46 1 (:REWRITE RTL::NEG-BITN-0))
 (43 1 (:DEFINITION NATP))
 (39 1 (:REWRITE RTL::BITN-NEG))
 (29 10 (:REWRITE DEFAULT-LESS-THAN-2))
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
 (28 28
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (18 2 (:REWRITE ACL2-NUMBERP-X))
 (15 5
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (15 5 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (14 5 (:REWRITE SIMPLIFY-SUMS-<))
 (10 10 (:REWRITE THE-FLOOR-BELOW))
 (10 10 (:REWRITE THE-FLOOR-ABOVE))
 (10 10 (:REWRITE DEFAULT-LESS-THAN-1))
 (8 2 (:REWRITE RATIONALP-X))
 (7 7
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (7 7
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (6 6 (:REWRITE REDUCE-INTEGERP-+))
 (6 6 (:REWRITE INTEGERP-MINUS-X))
 (6 6 (:META META-INTEGERP-CORRECT))
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
 (5 1 (:REWRITE RTL::NEG-BITN-1))
 (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (3 3 (:REWRITE DEFAULT-PLUS-1))
 (3 3 (:REWRITE |(< (* x y) 0)|))
 (3 1 (:REWRITE RTL::BVECP-BITN-0))
 (2 2 (:TYPE-PRESCRIPTION RTL::OPAW))
 (2 2 (:TYPE-PRESCRIPTION RTL::BVECP))
 (2 2 (:REWRITE REDUCE-RATIONALP-+))
 (2 2 (:REWRITE REDUCE-RATIONALP-*))
 (2 2 (:REWRITE RATIONALP-MINUS-X))
 (2 2
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (2 2 (:REWRITE NORMALIZE-ADDENDS))
 (2 2 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (2 2 (:REWRITE |(< (+ c/d x) y)|))
 (2 2 (:META META-RATIONALP-CORRECT))
 (2 1
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (2 1 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (1 1
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (1 1
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (1 1
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (1 1 (:REWRITE DEFAULT-EXPT-1))
 (1 1 (:REWRITE RTL::A-NORMP))
 (1 1 (:REWRITE |(expt 1/c n)|))
 (1 1 (:REWRITE |(expt (- x) n)|))
 (1 1 (:REWRITE |(equal c (/ x))|))
 (1 1 (:REWRITE |(equal c (- x))|))
 (1 1 (:REWRITE |(equal (/ x) c)|))
 (1 1 (:REWRITE |(equal (/ x) (/ y))|))
 (1 1 (:REWRITE |(equal (- x) c)|))
 (1 1 (:REWRITE |(equal (- x) (- y))|))
 (1 1 (:REWRITE |(< y (+ (- c) x))|))
 (1 1 (:REWRITE |(< x (+ c/d y))|))
 (1 1 (:REWRITE |(< 0 (/ x))|))
 (1 1 (:REWRITE |(< 0 (* x y))|))
 (1 1 (:REWRITE |(< (/ x) 0)|)))
(RTL::BVECP-MANA
 (477 45
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (450 74 (:REWRITE ACL2-NUMBERP-X))
 (424 10 (:REWRITE RTL::BITS-TAIL-GEN))
 (188 47 (:REWRITE RATIONALP-X))
 (108 45 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (103 3 (:REWRITE |(< (if a b c) x)|))
 (99 45 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (76 3 (:REWRITE |(< (+ (- c) x) y)|))
 (73 73 (:TYPE-PRESCRIPTION RTL::OPAW))
 (48 48 (:REWRITE REDUCE-INTEGERP-+))
 (48 48 (:REWRITE INTEGERP-MINUS-X))
 (48 48 (:META META-INTEGERP-CORRECT))
 (48 10 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (48 10 (:REWRITE RTL::BITS-NEG-INDICES))
 (47 47 (:REWRITE REDUCE-RATIONALP-+))
 (47 47 (:REWRITE REDUCE-RATIONALP-*))
 (47 47 (:REWRITE RATIONALP-MINUS-X))
 (47 47 (:META META-RATIONALP-CORRECT))
 (45 45
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (45 45
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (45 45
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (45 45 (:REWRITE |(equal c (/ x))|))
 (45 45 (:REWRITE |(equal c (- x))|))
 (45 45 (:REWRITE |(equal (/ x) c)|))
 (45 45 (:REWRITE |(equal (/ x) (/ y))|))
 (45 45 (:REWRITE |(equal (- x) c)|))
 (45 45 (:REWRITE |(equal (- x) (- y))|))
 (43 1 (:DEFINITION NATP))
 (40 10 (:REWRITE RTL::BITS-TAIL))
 (36 36 (:TYPE-PRESCRIPTION BOOLEANP))
 (27 18 (:REWRITE DEFAULT-LESS-THAN-1))
 (21 12
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (21 12 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (18 18 (:REWRITE THE-FLOOR-BELOW))
 (18 18 (:REWRITE THE-FLOOR-ABOVE))
 (18 18 (:REWRITE DEFAULT-LESS-THAN-2))
 (15 15
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (15 15
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (12 12 (:REWRITE SIMPLIFY-SUMS-<))
 (12 12
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
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
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (9 9
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (9 9
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (9 9
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (9 9
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (8 8 (:REWRITE SUBSETP-MEMBER . 4))
 (8 8 (:REWRITE SUBSETP-MEMBER . 3))
 (8 8 (:REWRITE SUBSETP-MEMBER . 2))
 (8 8 (:REWRITE SUBSETP-MEMBER . 1))
 (8 1 (:REWRITE |(+ x (if a b c))|))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (5 1 (:REWRITE |(+ c (+ d x))|))
 (4 4 (:REWRITE DEFAULT-PLUS-1))
 (3 3 (:REWRITE |(< (+ c/d x) y)|))
 (3 3 (:REWRITE |(< (* x y) 0)|))
 (2 2
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (2 2 (:REWRITE NORMALIZE-ADDENDS))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 (1 1 (:REWRITE REMOVE-WEAK-INEQUALITIES)))
(RTL::BVECP-EXPA (606 57
                      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                 (549 93 (:REWRITE ACL2-NUMBERP-X))
                 (228 57 (:REWRITE RATIONALP-X))
                 (135 57 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
                 (129 57 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                 (57 57 (:REWRITE REDUCE-RATIONALP-+))
                 (57 57 (:REWRITE REDUCE-RATIONALP-*))
                 (57 57
                     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                 (57 57 (:REWRITE REDUCE-INTEGERP-+))
                 (57 57
                     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
                 (57 57 (:REWRITE RATIONALP-MINUS-X))
                 (57 57 (:REWRITE INTEGERP-MINUS-X))
                 (57 57
                     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
                 (57 57 (:REWRITE |(equal c (/ x))|))
                 (57 57 (:REWRITE |(equal c (- x))|))
                 (57 57 (:REWRITE |(equal (/ x) c)|))
                 (57 57 (:REWRITE |(equal (/ x) (/ y))|))
                 (57 57 (:REWRITE |(equal (- x) c)|))
                 (57 57 (:REWRITE |(equal (- x) (- y))|))
                 (57 57 (:META META-RATIONALP-CORRECT))
                 (57 57 (:META META-INTEGERP-CORRECT))
                 (42 42 (:TYPE-PRESCRIPTION BOOLEANP))
                 (12 12 (:REWRITE RTL::BITS-REVERSE-INDICES))
                 (12 12 (:REWRITE RTL::BITS-NEG-INDICES))
                 (7 7
                    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
                 (4 4 (:REWRITE SUBSETP-MEMBER . 4))
                 (4 4 (:REWRITE SUBSETP-MEMBER . 3))
                 (4 4 (:REWRITE SUBSETP-MEMBER . 2))
                 (4 4 (:REWRITE SUBSETP-MEMBER . 1)))
(RTL::SIGA-1-REWRITE
 (292 10 (:REWRITE RTL::BITS-TAIL-GEN))
 (246 26
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (119 15 (:REWRITE ACL2-NUMBERP-X))
 (117 1 (:REWRITE |(< x (if a b c))|))
 (56 8
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (52 13 (:REWRITE RATIONALP-X))
 (45 27 (:REWRITE DEFAULT-LESS-THAN-2))
 (40
  40
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (40 40
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (40 40
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (40 40
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (40 40
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (40 40
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (35 27 (:REWRITE DEFAULT-LESS-THAN-1))
 (33 20
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (33 20 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (33 8 (:REWRITE DEFAULT-PLUS-2))
 (32 6 (:REWRITE |(* c (* d x))|))
 (30 1 (:REWRITE ODD-EXPT-THM))
 (29 20 (:REWRITE SIMPLIFY-SUMS-<))
 (27 27 (:REWRITE THE-FLOOR-BELOW))
 (27 27 (:REWRITE THE-FLOOR-ABOVE))
 (24 1 (:DEFINITION RTL::SIGW))
 (22 22 (:REWRITE REDUCE-INTEGERP-+))
 (22 22 (:REWRITE INTEGERP-MINUS-X))
 (22 22 (:META META-INTEGERP-CORRECT))
 (22 8 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (21 21 (:REWRITE DEFAULT-TIMES-1))
 (20 20
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (20 20
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
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
 (13 13 (:REWRITE REDUCE-RATIONALP-+))
 (13 13 (:REWRITE REDUCE-RATIONALP-*))
 (13 13 (:REWRITE RATIONALP-MINUS-X))
 (13 13 (:META META-RATIONALP-CORRECT))
 (13 2 (:REWRITE DEFAULT-EXPT-2))
 (12 12 (:TYPE-PRESCRIPTION BOOLEANP))
 (11 8 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (10 10 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (10 10 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (10 10 (:REWRITE RTL::BITS-NEG-INDICES))
 (9 7 (:REWRITE DEFAULT-PLUS-1))
 (8 8
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (8 8
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (8 8
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (8 8
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (8 8 (:REWRITE |(equal c (/ x))|))
 (8 8 (:REWRITE |(equal c (- x))|))
 (8 8 (:REWRITE |(equal (/ x) c)|))
 (8 8 (:REWRITE |(equal (/ x) (/ y))|))
 (8 8 (:REWRITE |(equal (- x) c)|))
 (8 8 (:REWRITE |(equal (- x) (- y))|))
 (6 6 (:TYPE-PRESCRIPTION ABS))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (5 5 (:REWRITE |(< (/ x) 0)|))
 (5 5 (:REWRITE |(< (* x y) 0)|))
 (4 4 (:REWRITE SUBSETP-MEMBER . 4))
 (4 4 (:REWRITE SUBSETP-MEMBER . 3))
 (4 4 (:REWRITE SUBSETP-MEMBER . 2))
 (4 4 (:REWRITE SUBSETP-MEMBER . 1))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (2 2 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (1 1
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (1 1 (:REWRITE NORMALIZE-ADDENDS))
 (1 1 (:REWRITE DEFAULT-EXPT-1))
 (1 1 (:REWRITE |(expt 1/c n)|))
 (1 1 (:REWRITE |(expt (- x) n)|))
 (1 1 (:REWRITE |(< 0 (/ x))|))
 (1 1 (:REWRITE |(< 0 (* x y))|)))
(RTL::SIGA-NORMP
 (3046 76 (:REWRITE RTL::BITS-TAIL-GEN))
 (1762 327 (:REWRITE DEFAULT-TIMES-2))
 (1164 198
       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (1107 1107
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (1107 1107
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (1107 1107
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (1107 1107
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (822 134 (:REWRITE ACL2-NUMBERP-X))
 (792 327 (:REWRITE DEFAULT-TIMES-1))
 (618 618 (:TYPE-PRESCRIPTION RTL::OPAW))
 (618 3 (:REWRITE |(< x (if a b c))|))
 (600
  600
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (600 600
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (600
     600
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (600 600
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (600 600
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (583 259 (:REWRITE DEFAULT-PLUS-1))
 (486 18 (:REWRITE RTL::BVECP-BITN-0))
 (418 224 (:REWRITE DEFAULT-LESS-THAN-1))
 (417 198 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (414 36 (:REWRITE DEFAULT-MINUS))
 (396 198
      (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (394 194
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (394 194
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (344 86 (:REWRITE RATIONALP-X))
 (262 224 (:REWRITE DEFAULT-LESS-THAN-2))
 (224 224 (:REWRITE THE-FLOOR-BELOW))
 (224 224 (:REWRITE THE-FLOOR-ABOVE))
 (210 210
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (209 206
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (204 194 (:REWRITE SIMPLIFY-SUMS-<))
 (198 198
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (198 198 (:REWRITE |(equal c (/ x))|))
 (198 198 (:REWRITE |(equal c (- x))|))
 (198 198 (:REWRITE |(equal (/ x) c)|))
 (198 198 (:REWRITE |(equal (/ x) (/ y))|))
 (198 198 (:REWRITE |(equal (- x) c)|))
 (198 198 (:REWRITE |(equal (- x) (- y))|))
 (196 196 (:REWRITE CONSTANT-<-INTEGERP))
 (196 196
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (196 196
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (196 196
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (196 196
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (196 196 (:REWRITE |(< c (- x))|))
 (196 196
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (196 196
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (196 196
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (196 196
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (196 196 (:REWRITE |(< (/ x) (/ y))|))
 (196 196 (:REWRITE |(< (- x) c)|))
 (196 196 (:REWRITE |(< (- x) (- y))|))
 (194 194
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (189 189
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (189 189 (:REWRITE NORMALIZE-ADDENDS))
 (180 18 (:REWRITE RTL::NEG-BITN-0))
 (152 142
      (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (151 29 (:REWRITE |(< (+ (- c) x) y)|))
 (127 5 (:REWRITE |(< y (+ (- c) x))|))
 (114 76 (:REWRITE RTL::BITS-NEG-INDICES))
 (111 74 (:REWRITE DEFAULT-EXPT-2))
 (103 103 (:REWRITE REDUCE-INTEGERP-+))
 (103 103 (:REWRITE INTEGERP-MINUS-X))
 (103 103 (:META META-INTEGERP-CORRECT))
 (103 3 (:REWRITE |(< (if a b c) x)|))
 (86 86 (:REWRITE REDUCE-RATIONALP-+))
 (86 86 (:REWRITE REDUCE-RATIONALP-*))
 (86 86 (:REWRITE RATIONALP-MINUS-X))
 (86 86 (:META META-RATIONALP-CORRECT))
 (76 2 (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (75 75
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (72 72 (:TYPE-PRESCRIPTION BOOLEANP))
 (72 72 (:REWRITE DEFAULT-EXPT-1))
 (71 71 (:REWRITE |(expt 1/c n)|))
 (71 71 (:REWRITE |(expt (- x) n)|))
 (43 1 (:DEFINITION NATP))
 (39 39 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (36 1 (:REWRITE ODD-EXPT-THM))
 (35 1 (:LINEAR EXPT->=-1-ONE))
 (35 1 (:LINEAR EXPT-<=-1-TWO))
 (34 1 (:LINEAR EXPT->-1-ONE))
 (34 1 (:LINEAR EXPT-<-1-TWO))
 (33 1 (:LINEAR EXPT-X->=-X))
 (33 1 (:LINEAR EXPT-X->-X))
 (32 32 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (31 1
     (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (29 29 (:REWRITE |(< (+ c/d x) y)|))
 (27 27 (:REWRITE |(equal (+ (- c) x) y)|))
 (22 1 (:REWRITE |(expt x (if a b c))|))
 (18 18 (:REWRITE RTL::NEG-BITN-1))
 (18 18 (:REWRITE RTL::BITN-NEG))
 (16 16 (:REWRITE BUBBLE-DOWN-*-MATCH-3))
 (15 15 (:REWRITE |(< (* x y) 0)|))
 (15 15 (:REWRITE |(- (* c x))|))
 (14 2 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (10 10 (:REWRITE |(< (/ x) 0)|))
 (8 1 (:REWRITE |(+ x (if a b c))|))
 (6 6 (:REWRITE |(< 0 (* x y))|))
 (6 6 (:REWRITE |(* (- x) y)|))
 (5 5 (:REWRITE |(< x (+ c/d y))|))
 (4 4 (:REWRITE SUBSETP-MEMBER . 4))
 (4 4 (:REWRITE SUBSETP-MEMBER . 3))
 (4 4 (:REWRITE SUBSETP-MEMBER . 2))
 (4 4 (:REWRITE SUBSETP-MEMBER . 1))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (3 3 (:REWRITE |(< 0 (/ x))|))
 (3 2 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 (1 1
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (1 1
    (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<))
 (1 1 (:LINEAR EXPT->=-1-TWO))
 (1 1 (:LINEAR EXPT->-1-TWO))
 (1 1 (:LINEAR EXPT-<=-1-ONE))
 (1 1 (:LINEAR EXPT-<-1-ONE)))
(RTL::BVECP-SIGA-1
 (1088 6 (:REWRITE |(< x (if a b c))|))
 (689 1 (:REWRITE RTL::BVECP-BITN-0))
 (208 7 (:REWRITE RTL::BITS-TAIL-GEN))
 (178 7 (:REWRITE |(< (+ (- c) x) y)|))
 (172 5 (:REWRITE |(< (if a b c) x)|))
 (158 84 (:REWRITE DEFAULT-LESS-THAN-2))
 (127 5 (:REWRITE |(< y (+ (- c) x))|))
 (108 12 (:REWRITE ACL2-NUMBERP-X))
 (99 84 (:REWRITE DEFAULT-LESS-THAN-1))
 (97 97 (:TYPE-PRESCRIPTION RTL::OPAW))
 (86 2 (:DEFINITION NATP))
 (84 84 (:REWRITE THE-FLOOR-BELOW))
 (84 84 (:REWRITE THE-FLOOR-ABOVE))
 (82 55
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (82 55 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (80 17 (:REWRITE DEFAULT-PLUS-2))
 (76 69
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (76 2 (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (75 55 (:REWRITE SIMPLIFY-SUMS-<))
 (67 2 (:REWRITE ODD-EXPT-THM))
 (66 9
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (65 2 (:LINEAR EXPT->=-1-ONE))
 (65 2 (:LINEAR EXPT-<=-1-TWO))
 (63 2 (:LINEAR EXPT->-1-ONE))
 (63 2 (:LINEAR EXPT-<-1-TWO))
 (58 2 (:LINEAR EXPT-X->=-X))
 (58 2 (:LINEAR EXPT-X->-X))
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
 (55 55
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (54 8 (:REWRITE DEFAULT-EXPT-2))
 (48 12 (:REWRITE RATIONALP-X))
 (46 1 (:REWRITE RTL::NEG-BITN-0))
 (45 7 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (45 7 (:REWRITE RTL::BITS-NEG-INDICES))
 (39 1 (:REWRITE RTL::BITN-NEG))
 (36 36
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (36
   36
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (36
  36
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (36 36
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (36 36
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (36 36
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (36 36
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (36 36
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (36 36
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (36 2 (:REWRITE |(expt x (if a b c))|))
 (31 1
     (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (27 27 (:REWRITE REDUCE-INTEGERP-+))
 (27 27 (:REWRITE INTEGERP-MINUS-X))
 (27 27 (:META META-INTEGERP-CORRECT))
 (25 25 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (24 9 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (24 1 (:DEFINITION RTL::SIGW))
 (16 16 (:REWRITE |(< (* x y) 0)|))
 (16 15 (:REWRITE DEFAULT-TIMES-2))
 (16 15 (:REWRITE DEFAULT-TIMES-1))
 (14 14 (:REWRITE DEFAULT-PLUS-1))
 (14 2 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (12 12 (:TYPE-PRESCRIPTION BOOLEANP))
 (12 12 (:REWRITE REDUCE-RATIONALP-+))
 (12 12 (:REWRITE REDUCE-RATIONALP-*))
 (12 12 (:REWRITE RATIONALP-MINUS-X))
 (12 12 (:META META-RATIONALP-CORRECT))
 (9 9
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (9 9
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (9 9 (:REWRITE SIMPLIFY-SUMS-EQUAL))
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
 (9 9 (:REWRITE |(< 0 (* x y))|))
 (9 9 (:REWRITE |(< (/ x) 0)|))
 (9 2 (:REWRITE |(* y x)|))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (7 7 (:REWRITE |(< (+ c/d x) y)|))
 (7 1 (:REWRITE |(+ x (if a b c))|))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (6 6 (:REWRITE |(< 0 (/ x))|))
 (5 5
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (5 5 (:REWRITE |(< x (+ c/d y))|))
 (5 1 (:REWRITE RTL::NEG-BITN-1))
 (4 4 (:REWRITE SUBSETP-MEMBER . 4))
 (4 4 (:REWRITE SUBSETP-MEMBER . 3))
 (4 4 (:REWRITE SUBSETP-MEMBER . 2))
 (4 4 (:REWRITE SUBSETP-MEMBER . 1))
 (4 4 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (4 4 (:REWRITE DEFAULT-EXPT-1))
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
    (:TYPE-PRESCRIPTION RTL::BITN-NONNEGATIVE-INTEGER))
 (3 3
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (3 3 (:REWRITE NORMALIZE-ADDENDS))
 (3 2 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 (2 2 (:REWRITE |(expt 1/c n)|))
 (2 2 (:REWRITE |(expt (- x) n)|))
 (2 2
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-ONE))
 (1 1
    (:REWRITE |(<= (/ x) y) with (< x 0)|)))
(RTL::SIGA-1-POS
 (976 113
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (859 99 (:REWRITE ACL2-NUMBERP-X))
 (414 12 (:REWRITE RTL::BITS-TAIL-GEN))
 (380 95 (:REWRITE RATIONALP-X))
 (301 113
      (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (180 180 (:TYPE-PRESCRIPTION BOOLEANP))
 (124 124 (:REWRITE SUBSETP-MEMBER . 4))
 (124 124 (:REWRITE SUBSETP-MEMBER . 3))
 (124 124 (:REWRITE SUBSETP-MEMBER . 2))
 (124 124 (:REWRITE SUBSETP-MEMBER . 1))
 (121 113 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (113 113
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (113 113
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (113 113
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (113 113 (:REWRITE |(equal c (/ x))|))
 (113 113 (:REWRITE |(equal c (- x))|))
 (113 113 (:REWRITE |(equal (/ x) c)|))
 (113 113 (:REWRITE |(equal (/ x) (/ y))|))
 (113 113 (:REWRITE |(equal (- x) c)|))
 (113 113 (:REWRITE |(equal (- x) (- y))|))
 (102 102 (:TYPE-PRESCRIPTION RTL::OPAW))
 (95 95 (:REWRITE REDUCE-RATIONALP-+))
 (95 95 (:REWRITE REDUCE-RATIONALP-*))
 (95 95 (:REWRITE REDUCE-INTEGERP-+))
 (95 95 (:REWRITE RATIONALP-MINUS-X))
 (95 95 (:REWRITE INTEGERP-MINUS-X))
 (95 95 (:META META-RATIONALP-CORRECT))
 (95 95 (:META META-INTEGERP-CORRECT))
 (44 32 (:REWRITE DEFAULT-LESS-THAN-1))
 (40 28
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (40 28 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (36 36
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (32 32 (:REWRITE THE-FLOOR-BELOW))
 (32 32 (:REWRITE THE-FLOOR-ABOVE))
 (32 32 (:REWRITE DEFAULT-LESS-THAN-2))
 (28 28 (:REWRITE SIMPLIFY-SUMS-<))
 (28 28
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (28 28
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (28 28 (:REWRITE INTEGERP-<-CONSTANT))
 (28 28 (:REWRITE CONSTANT-<-INTEGERP))
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
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (28 28
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (28 28
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (28 28
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (28 28 (:REWRITE |(< (/ x) (/ y))|))
 (28 28 (:REWRITE |(< (- x) c)|))
 (28 28 (:REWRITE |(< (- x) (- y))|))
 (12 12 (:REWRITE RTL::BITS-NEG-INDICES))
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
 (10 10 (:REWRITE DEFAULT-TIMES-2))
 (10 10 (:REWRITE DEFAULT-TIMES-1))
 (6 6 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (6 6 (:REWRITE DEFAULT-PLUS-2))
 (6 6 (:REWRITE DEFAULT-PLUS-1))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (3 3 (:REWRITE |(< (/ x) 0)|))
 (3 3 (:REWRITE |(< (* x y) 0)|))
 (2 2
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS)))
(RTL::CLZ-SIGA-1
 (442 13 (:REWRITE RTL::BITS-TAIL-GEN))
 (379 54 (:REWRITE ACL2-NUMBERP-X))
 (360 144 (:REWRITE DEFAULT-TIMES-1))
 (287 45
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (206
  206
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (206 206
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (206
     206
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (206 206
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (206 206
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (196 115 (:REWRITE DEFAULT-LESS-THAN-1))
 (188 105
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (177 45 (:REWRITE RATIONALP-X))
 (136 105
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (130 105
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (130 105
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (128 115 (:REWRITE DEFAULT-LESS-THAN-2))
 (115 115 (:REWRITE THE-FLOOR-BELOW))
 (115 115 (:REWRITE THE-FLOOR-ABOVE))
 (115 107 (:REWRITE DEFAULT-PLUS-2))
 (108 107 (:REWRITE DEFAULT-PLUS-1))
 (105 105
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (105 105 (:REWRITE INTEGERP-<-CONSTANT))
 (105 105 (:REWRITE CONSTANT-<-INTEGERP))
 (105 105
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (105 105
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (105 105
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (105 105
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (105 105 (:REWRITE |(< c (- x))|))
 (105 105
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (105 105
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (105 105
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (105 105
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (105 105 (:REWRITE |(< (/ x) (/ y))|))
 (105 105 (:REWRITE |(< (- x) c)|))
 (105 105 (:REWRITE |(< (- x) (- y))|))
 (105 45 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (104 104 (:REWRITE SIMPLIFY-SUMS-<))
 (102 96 (:REWRITE NORMALIZE-ADDENDS))
 (95 95
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (94 84 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (73 1 (:REWRITE ODD-EXPT-THM))
 (70 70
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (66 45 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (64 64 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (60 60 (:REWRITE REDUCE-INTEGERP-+))
 (60 60 (:REWRITE INTEGERP-MINUS-X))
 (60 60 (:META META-INTEGERP-CORRECT))
 (52 52 (:TYPE-PRESCRIPTION BOOLEANP))
 (45 45 (:REWRITE REDUCE-RATIONALP-+))
 (45 45 (:REWRITE REDUCE-RATIONALP-*))
 (45 45
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (45 45
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (45 45 (:REWRITE RATIONALP-MINUS-X))
 (45 45
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (45 45 (:REWRITE |(equal c (/ x))|))
 (45 45 (:REWRITE |(equal c (- x))|))
 (45 45 (:REWRITE |(equal (/ x) c)|))
 (45 45 (:REWRITE |(equal (/ x) (/ y))|))
 (45 45 (:REWRITE |(equal (- x) c)|))
 (45 45 (:REWRITE |(equal (- x) (- y))|))
 (45 45 (:META META-RATIONALP-CORRECT))
 (34 34 (:REWRITE DEFAULT-EXPT-1))
 (32 32 (:REWRITE |(expt 1/c n)|))
 (32 32 (:REWRITE |(expt (- x) n)|))
 (26 26 (:TYPE-PRESCRIPTION ABS))
 (25 25
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (25 25
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (25 25 (:REWRITE |(< (/ x) 0)|))
 (25 25 (:REWRITE |(< (* x y) 0)|))
 (24 24
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (16 4 (:REWRITE |(* c (* d x))|))
 (15 15 (:REWRITE |(< 0 (/ x))|))
 (15 15 (:REWRITE |(< 0 (* x y))|))
 (14 14
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (14 14
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (13 13 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (13 13 (:REWRITE RTL::BITS-NEG-INDICES))
 (13 13 (:REWRITE |(equal (+ (- c) x) y)|))
 (10 1 (:REWRITE |(+ y (+ x z))|))
 (9 1
    (:REWRITE |(<= x (/ y)) with (< y 0)|))
 (9 1
    (:REWRITE |(<= x (/ y)) with (< 0 y)|))
 (9 1 (:REWRITE |(< (/ x) y) with (< x 0)|))
 (9 1 (:REWRITE |(< (/ x) y) with (< 0 x)|))
 (6 6
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (4 1 (:REWRITE |(+ y x)|))
 (2 2 (:DEFINITION FIX))
 (2 1 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
 (1 1 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (1 1
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (1 1 (:REWRITE DEFAULT-DIVIDE))
 (1 1 (:REWRITE |(< y (+ (- c) x))|))
 (1 1 (:REWRITE |(< x (+ c/d y))|))
 (1 1 (:REWRITE |(+ x (- x))|)))
(RTL::SIGA-SIGA-1
 (3631 2 (:REWRITE RTL::BITS-TAIL-GEN))
 (2271 193 (:REWRITE |(< c (- x))|))
 (1327 139
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (1327 139
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (1239 137 (:REWRITE |(< (- x) c)|))
 (1095 9 (:LINEAR RTL::FL-DEF))
 (1022 16 (:LINEAR EXPT->=-1-ONE))
 (1006 16 (:LINEAR EXPT-<-1-TWO))
 (994 16 (:LINEAR EXPT-<=-1-TWO))
 (978 16 (:LINEAR EXPT->-1-ONE))
 (886 16 (:LINEAR EXPT-X->=-X))
 (886 16 (:LINEAR EXPT-X->-X))
 (747
  747
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (747 747
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (747
     747
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (747 747
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (747 747
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (297 193 (:REWRITE DEFAULT-LESS-THAN-2))
 (293 193 (:REWRITE DEFAULT-LESS-THAN-1))
 (229 109
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (229 109
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (221 193 (:REWRITE |(< (- x) (- y))|))
 (221 23
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3E-EXPT))
 (221 23
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1E-EXPT))
 (193 193 (:REWRITE THE-FLOOR-BELOW))
 (193 193 (:REWRITE THE-FLOOR-ABOVE))
 (193 193
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (193 193
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (193 193
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (193 193
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (193 193
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (193 193
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (193 193
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (193 193
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (193 193
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (193 193
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (193 193 (:REWRITE |(< (/ x) (/ y))|))
 (174 87 (:REWRITE DEFAULT-MINUS))
 (168 84 (:REWRITE |(- (- x))|))
 (144 144 (:REWRITE |arith (expt x c)|))
 (139 139
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (134 134 (:REWRITE |arith (expt 1/c n)|))
 (119 109 (:REWRITE SIMPLIFY-SUMS-<))
 (109 109
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (109 109 (:REWRITE INTEGERP-<-CONSTANT))
 (109 109 (:REWRITE CONSTANT-<-INTEGERP))
 (73 73 (:REWRITE |arith (* c (* d x))|))
 (63 63 (:REWRITE |(< (/ x) 0)|))
 (63 63 (:REWRITE |(< (* x y) 0)|))
 (62 62 (:REWRITE |(< 0 (/ x))|))
 (62 62 (:REWRITE |(< 0 (* x y))|))
 (55 7
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (43 1 (:REWRITE ODD-EXPT-THM))
 (42 42 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (38 6 (:REWRITE ACL2-NUMBERP-X))
 (35 35 (:TYPE-PRESCRIPTION RTL::FL-DEF))
 (35 35
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (35 35
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (34 34
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (34 34
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (34 4 (:REWRITE DEFAULT-TIMES-2))
 (32 32
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (32 32
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (32 32
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (28 28 (:REWRITE |arith (* (- x) y)|))
 (24 24 (:REWRITE |arith (- (* c x))|))
 (23 23
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2E-EXPT))
 (21 7 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (16 16 (:LINEAR EXPT-LINEAR-UPPER-<))
 (16 16 (:LINEAR EXPT-LINEAR-LOWER-<))
 (16 16 (:LINEAR EXPT->=-1-TWO))
 (16 16 (:LINEAR EXPT->-1-TWO))
 (16 16 (:LINEAR EXPT-<=-1-ONE))
 (16 16 (:LINEAR EXPT-<-1-ONE))
 (16 7 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (16 4 (:REWRITE RATIONALP-X))
 (14 4 (:REWRITE DEFAULT-TIMES-1))
 (12 8 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (10 10 (:LINEAR RTL::FL-MONOTONE-LINEAR))
 (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (8 8 (:TYPE-PRESCRIPTION BOOLEANP))
 (8 4 (:REWRITE DEFAULT-PLUS-2))
 (8 4 (:REWRITE DEFAULT-EXPT-2))
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
 (5 5 (:LINEAR RTL::N<=FL-LINEAR))
 (4 4 (:REWRITE REDUCE-RATIONALP-+))
 (4 4 (:REWRITE REDUCE-RATIONALP-*))
 (4 4 (:REWRITE RATIONALP-MINUS-X))
 (4 4
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (4 4 (:REWRITE NORMALIZE-ADDENDS))
 (4 4 (:REWRITE DEFAULT-PLUS-1))
 (4 4 (:REWRITE DEFAULT-EXPT-1))
 (4 4 (:REWRITE |(expt 1/c n)|))
 (4 4 (:REWRITE |(expt (- x) n)|))
 (4 4 (:META META-RATIONALP-CORRECT))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (3 3 (:REWRITE RTL::SIGA-NORMP))
 (3 3
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (2 2 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (2 2 (:REWRITE RTL::BITS-NEG-INDICES))
 (1 1 (:REWRITE |(< y (+ (- c) x))|))
 (1 1 (:REWRITE |(< x (+ c/d y))|)))
(RTL::SIGA-MANA
 (880 252 (:REWRITE DEFAULT-TIMES-1))
 (476 66
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (451
  451
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (451 451
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (451
     451
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (451 451
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (451 451
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (398 184 (:REWRITE DEFAULT-PLUS-2))
 (324 36 (:REWRITE ACL2-NUMBERP-X))
 (242 66 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (206 66 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (196 52 (:REWRITE RATIONALP-X))
 (182 182 (:REWRITE DEFAULT-PLUS-1))
 (172 116
      (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (112 112
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (112 112 (:REWRITE NORMALIZE-ADDENDS))
 (78 66
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (74 66 (:REWRITE |(equal (/ x) (/ y))|))
 (66 66
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (66 66
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (66 66 (:REWRITE |(equal c (/ x))|))
 (66 66 (:REWRITE |(equal c (- x))|))
 (66 66 (:REWRITE |(equal (/ x) c)|))
 (66 66 (:REWRITE |(equal (- x) c)|))
 (66 66 (:REWRITE |(equal (- x) (- y))|))
 (60 60 (:REWRITE DEFAULT-EXPT-1))
 (58 58 (:REWRITE |(expt 1/c n)|))
 (58 58 (:REWRITE |(expt (- x) n)|))
 (56 56 (:REWRITE REDUCE-INTEGERP-+))
 (56 56 (:REWRITE INTEGERP-MINUS-X))
 (56 56 (:META META-INTEGERP-CORRECT))
 (52 52 (:TYPE-PRESCRIPTION BOOLEANP))
 (52 52 (:REWRITE REDUCE-RATIONALP-+))
 (52 52 (:REWRITE REDUCE-RATIONALP-*))
 (52 52 (:REWRITE RATIONALP-MINUS-X))
 (52 52 (:META META-RATIONALP-CORRECT))
 (48 2 (:DEFINITION RTL::SIGW))
 (46 46
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (32 32 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (16 16 (:REWRITE SUBSETP-MEMBER . 4))
 (16 16 (:REWRITE SUBSETP-MEMBER . 3))
 (16 16 (:REWRITE SUBSETP-MEMBER . 2))
 (16 16 (:REWRITE SUBSETP-MEMBER . 1))
 (16 16 (:REWRITE BUBBLE-DOWN-*-MATCH-3))
 (16 16 (:REWRITE |(* c (* d x))|))
 (12 12 (:TYPE-PRESCRIPTION ABS))
 (12 12 (:REWRITE |(equal (* x y) 0)|))
 (8 8 (:REWRITE |(equal (+ (- c) x) y)|)))
(RTL::SIGA-SIG-MANA
 (1113 75 (:REWRITE DEFAULT-LESS-THAN-2))
 (766 89 (:REWRITE ACL2-NUMBERP-X))
 (553
  553
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (553 553
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (553
     553
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (553 553
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (553 553
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (341 86 (:REWRITE RATIONALP-X))
 (312 6 (:LINEAR EXPT->=-1-ONE))
 (306 6 (:LINEAR EXPT-<=-1-TWO))
 (306 6 (:LINEAR EXPT-<-1-TWO))
 (300 6 (:LINEAR EXPT->-1-ONE))
 (276 6 (:LINEAR EXPT-X->=-X))
 (276 6 (:LINEAR EXPT-X->-X))
 (234 21
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (137 21 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (117 21 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (108 40 (:REWRITE DEFAULT-TIMES-1))
 (86 86 (:REWRITE REDUCE-RATIONALP-+))
 (86 86 (:REWRITE REDUCE-RATIONALP-*))
 (86 86 (:REWRITE RATIONALP-MINUS-X))
 (86 86 (:META META-RATIONALP-CORRECT))
 (85 85 (:REWRITE REDUCE-INTEGERP-+))
 (85 85 (:REWRITE INTEGERP-MINUS-X))
 (85 85 (:META META-INTEGERP-CORRECT))
 (75 75 (:REWRITE THE-FLOOR-BELOW))
 (75 75 (:REWRITE THE-FLOOR-ABOVE))
 (74 48 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (50 24 (:REWRITE DEFAULT-EXPT-2))
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
 (37 37 (:REWRITE SIMPLIFY-SUMS-<))
 (37 37
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (37 37 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (30 14 (:REWRITE DEFAULT-PLUS-2))
 (27 21 (:REWRITE |(equal (/ x) (/ y))|))
 (24 24 (:REWRITE DEFAULT-EXPT-1))
 (24 24 (:REWRITE |(expt 1/c n)|))
 (24 24 (:REWRITE |(expt (- x) n)|))
 (22 22 (:TYPE-PRESCRIPTION BOOLEANP))
 (21 21
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (21 21
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (21 21
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (21 21 (:REWRITE |(equal c (/ x))|))
 (21 21 (:REWRITE |(equal c (- x))|))
 (21 21 (:REWRITE |(equal (/ x) c)|))
 (21 21 (:REWRITE |(equal (- x) c)|))
 (21 21 (:REWRITE |(equal (- x) (- y))|))
 (20 14 (:REWRITE DEFAULT-PLUS-1))
 (19 10 (:REWRITE DEFAULT-MINUS))
 (14 14 (:REWRITE |(< (/ x) 0)|))
 (14 14 (:REWRITE |(< (* x y) 0)|))
 (13 13
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (13 13
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (13 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (12 12
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (12 12
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (12 12 (:REWRITE |(< 0 (/ x))|))
 (12 12 (:REWRITE |(< 0 (* x y))|))
 (12 12
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (12 12
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (12 12
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (12 12
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (11 11
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (9 9
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (6 6 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (6 6 (:LINEAR EXPT-LINEAR-UPPER-<))
 (6 6 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (6 6 (:LINEAR EXPT-LINEAR-LOWER-<))
 (6 6 (:LINEAR EXPT->=-1-TWO))
 (6 6 (:LINEAR EXPT->-1-TWO))
 (6 6 (:LINEAR EXPT-<=-1-ONE))
 (6 6 (:LINEAR EXPT-<-1-ONE))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE |(+ c (+ d x))|)))
(RTL::SIGA-DENORMP
 (1770 48 (:REWRITE RTL::BITS-TAIL-GEN))
 (1152 147
       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (948 132 (:REWRITE ACL2-NUMBERP-X))
 (408 102 (:REWRITE RATIONALP-X))
 (360 147
      (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (336 336 (:TYPE-PRESCRIPTION RTL::OPAW))
 (243 147 (:REWRITE SIMPLIFY-SUMS-EQUAL))
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
 (144 144 (:TYPE-PRESCRIPTION BOOLEANP))
 (132 48 (:REWRITE RTL::BITS-TAIL))
 (102 102 (:REWRITE REDUCE-RATIONALP-+))
 (102 102 (:REWRITE REDUCE-RATIONALP-*))
 (102 102 (:REWRITE REDUCE-INTEGERP-+))
 (102 102 (:REWRITE RATIONALP-MINUS-X))
 (102 102 (:REWRITE INTEGERP-MINUS-X))
 (102 102 (:META META-RATIONALP-CORRECT))
 (102 102 (:META META-INTEGERP-CORRECT))
 (94 94 (:REWRITE SUBSETP-MEMBER . 4))
 (94 94 (:REWRITE SUBSETP-MEMBER . 3))
 (94 94 (:REWRITE SUBSETP-MEMBER . 2))
 (94 94 (:REWRITE SUBSETP-MEMBER . 1))
 (84 42
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (84 42 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (84 42 (:REWRITE DEFAULT-LESS-THAN-1))
 (48 48 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (48 48 (:REWRITE RTL::BITS-NEG-INDICES))
 (45
   45
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (45
  45
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (45 45
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (45 45
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (45 45
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (45 45
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (43 43
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
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
 (42 42 (:REWRITE DEFAULT-LESS-THAN-2))
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
 (12 6 (:REWRITE DEFAULT-TIMES-2))
 (6 6
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (6 6 (:REWRITE DEFAULT-TIMES-1)))
(RTL::SIGA-REWRITE
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
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A)))
(RTL::A-POS
     (1420 388
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (842 388
          (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
     (718 94 (:REWRITE ACL2-NUMBERP-X))
     (420 388 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (388 388
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (388 388
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (388 388
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (388 388 (:REWRITE |(equal c (/ x))|))
     (388 388 (:REWRITE |(equal c (- x))|))
     (388 388 (:REWRITE |(equal (/ x) c)|))
     (388 388 (:REWRITE |(equal (/ x) (/ y))|))
     (388 388 (:REWRITE |(equal (- x) c)|))
     (388 388 (:REWRITE |(equal (- x) (- y))|))
     (351 345
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (351 345
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (351 345 (:REWRITE DEFAULT-LESS-THAN-1))
     (345 345 (:REWRITE THE-FLOOR-BELOW))
     (345 345 (:REWRITE THE-FLOOR-ABOVE))
     (345 345 (:REWRITE SIMPLIFY-SUMS-<))
     (345 345 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (345 345
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (345 345
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (345 345
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (345 345 (:REWRITE INTEGERP-<-CONSTANT))
     (345 345 (:REWRITE DEFAULT-LESS-THAN-2))
     (345 345 (:REWRITE CONSTANT-<-INTEGERP))
     (345 345
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (345 345
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (345 345
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (345 345
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (345 345 (:REWRITE |(< c (- x))|))
     (345 345
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (345 345
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (345 345
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (345 345
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (345 345 (:REWRITE |(< (/ x) (/ y))|))
     (345 345 (:REWRITE |(< (- x) c)|))
     (345 345 (:REWRITE |(< (- x) (- y))|))
     (312 78 (:REWRITE RATIONALP-X))
     (188 188
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (138 138
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (138 138
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (138 138 (:REWRITE |(< (/ x) 0)|))
     (138 138 (:REWRITE |(< (* x y) 0)|))
     (124 124 (:TYPE-PRESCRIPTION BOOLEANP))
     (99 99 (:REWRITE SUBSETP-MEMBER . 4))
     (99 99 (:REWRITE SUBSETP-MEMBER . 3))
     (99 99 (:REWRITE SUBSETP-MEMBER . 2))
     (99 99 (:REWRITE SUBSETP-MEMBER . 1))
     (87 87
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (87 87
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (87 87 (:REWRITE |(< 0 (/ x))|))
     (87 87 (:REWRITE |(< 0 (* x y))|))
     (78 78 (:REWRITE REDUCE-RATIONALP-+))
     (78 78 (:REWRITE REDUCE-RATIONALP-*))
     (78 78 (:REWRITE REDUCE-INTEGERP-+))
     (78 78 (:REWRITE RATIONALP-MINUS-X))
     (78 78 (:REWRITE INTEGERP-MINUS-X))
     (78 78 (:META META-RATIONALP-CORRECT))
     (78 78 (:META META-INTEGERP-CORRECT)))
(RTL::SIGA-BOUNDS
 (9 5
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
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
 (7 5
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (7 5
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (7 5
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (7 5 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (6 5 (:REWRITE DEFAULT-LESS-THAN-2))
 (6 5 (:REWRITE DEFAULT-LESS-THAN-1))
 (5 5 (:REWRITE THE-FLOOR-BELOW))
 (5 5 (:REWRITE THE-FLOOR-ABOVE))
 (5 5 (:REWRITE SIMPLIFY-SUMS-<))
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
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (5 5
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (5 5
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (5 5 (:REWRITE |(< (/ x) (/ y))|))
 (5 5 (:REWRITE |(< (- x) c)|))
 (5 5 (:REWRITE |(< (- x) (- y))|))
 (4 4 (:TYPE-PRESCRIPTION ABS))
 (2 2
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (2 2 (:REWRITE DEFAULT-TIMES-2))
 (2 2 (:REWRITE DEFAULT-TIMES-1))
 (2 2
    (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (1 1 (:REWRITE REDUCE-INTEGERP-+))
 (1 1 (:REWRITE INTEGERP-MINUS-X))
 (1 1 (:REWRITE |(< 0 (/ x))|))
 (1 1 (:REWRITE |(< 0 (* x y))|))
 (1 1 (:META META-INTEGERP-CORRECT)))
(RTL::CLZ-MANA
 (285 37 (:REWRITE ACL2-NUMBERP-X))
 (190 89 (:REWRITE DEFAULT-PLUS-2))
 (149 89 (:REWRITE DEFAULT-PLUS-1))
 (137 35 (:REWRITE RATIONALP-X))
 (105 41 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (59 41 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (54 50 (:REWRITE |(equal c (- x))|))
 (54 50 (:REWRITE |(equal (- x) (- y))|))
 (50 50 (:TYPE-PRESCRIPTION BOOLEANP))
 (50 50
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (50 50
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (50 50
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (50 50 (:REWRITE |(equal c (/ x))|))
 (50 50 (:REWRITE |(equal (/ x) c)|))
 (50 50 (:REWRITE |(equal (/ x) (/ y))|))
 (50 50 (:REWRITE |(equal (- x) c)|))
 (38 38 (:REWRITE REDUCE-INTEGERP-+))
 (38 38 (:REWRITE INTEGERP-MINUS-X))
 (38 38 (:META META-INTEGERP-CORRECT))
 (37 37
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (35 35 (:REWRITE REDUCE-RATIONALP-+))
 (35 35 (:REWRITE REDUCE-RATIONALP-*))
 (35 35 (:REWRITE RATIONALP-MINUS-X))
 (35 35 (:META META-RATIONALP-CORRECT))
 (20 10 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (20 10 (:REWRITE DEFAULT-MINUS))
 (19 19
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (19 19 (:REWRITE |(equal (+ (- c) x) y)|))
 (16 4 (:REWRITE RTL::BITS-TAIL-GEN))
 (15
  15
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (15 15
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (15 15
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (15 15
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (15 15
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (15 15
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (12 4 (:REWRITE RTL::BITS-TAIL))
 (6 6 (:REWRITE DEFAULT-TIMES-1))
 (4 4 (:REWRITE SUBSETP-MEMBER . 4))
 (4 4 (:REWRITE SUBSETP-MEMBER . 3))
 (4 4 (:REWRITE SUBSETP-MEMBER . 2))
 (4 4 (:REWRITE SUBSETP-MEMBER . 1))
 (4 4
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (4 4 (:REWRITE FOLD-CONSTS-IN-+))
 (4 4 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (4 4 (:REWRITE RTL::BITS-NEG-INDICES)))
(RTL::EXPSHFT-DENORM (45 5 (:REWRITE ACL2-NUMBERP-X))
                     (25 14 (:REWRITE DEFAULT-PLUS-2))
                     (20 5 (:REWRITE RATIONALP-X))
                     (20 2 (:REWRITE RTL::BITS-TAIL-GEN))
                     (10 1
                         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                     (7 7 (:REWRITE REDUCE-INTEGERP-+))
                     (7 7
                        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                     (7 7 (:REWRITE NORMALIZE-ADDENDS))
                     (7 7 (:REWRITE INTEGERP-MINUS-X))
                     (7 7 (:META META-INTEGERP-CORRECT))
                     (6 2 (:REWRITE RTL::BITS-TAIL))
                     (5 5 (:REWRITE REDUCE-RATIONALP-+))
                     (5 5 (:REWRITE REDUCE-RATIONALP-*))
                     (5 5 (:REWRITE RATIONALP-MINUS-X))
                     (5 5 (:META META-RATIONALP-CORRECT))
                     (3 1 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
                     (2 2 (:TYPE-PRESCRIPTION BOOLEANP))
                     (2 2 (:REWRITE FOLD-CONSTS-IN-+))
                     (2 2 (:REWRITE RTL::BITS-REVERSE-INDICES))
                     (2 2 (:REWRITE RTL::BITS-NEG-INDICES))
                     (2 2 (:REWRITE |(+ c (+ d x))|))
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
                     (1 1 (:REWRITE |(equal (- x) (- y))|)))
(RTL::SI-EXPSHFT-DENORM
 (19281 2401 (:REWRITE ACL2-NUMBERP-X))
 (13896 234 (:REWRITE RTL::BITS-TAIL))
 (12533 1430
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (10195 2812 (:REWRITE RATIONALP-X))
 (7794 7794 (:TYPE-PRESCRIPTION RTL::SI))
 (5401 3694
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (5401 3694
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (4827 2877 (:REWRITE DEFAULT-PLUS-2))
 (4772 4772 (:REWRITE THE-FLOOR-BELOW))
 (4772 4772 (:REWRITE THE-FLOOR-ABOVE))
 (4069 4069
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (4069 4069
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (4051 1430
       (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (3703 3694 (:REWRITE SIMPLIFY-SUMS-<))
 (3697 3697
       (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (3697 3697 (:REWRITE INTEGERP-<-CONSTANT))
 (3697 3697 (:REWRITE CONSTANT-<-INTEGERP))
 (3697 3697
       (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (3697 3697
       (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (3697 3697
       (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (3697 3697
       (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (3697 3697 (:REWRITE |(< c (- x))|))
 (3697 3697
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (3697 3697
       (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (3697 3697
       (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (3697 3697
       (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (3697 3697 (:REWRITE |(< (/ x) (/ y))|))
 (3697 3697 (:REWRITE |(< (- x) c)|))
 (3697 3697 (:REWRITE |(< (- x) (- y))|))
 (3447 2877 (:REWRITE DEFAULT-PLUS-1))
 (2812 2812 (:REWRITE REDUCE-RATIONALP-+))
 (2812 2812 (:REWRITE REDUCE-RATIONALP-*))
 (2812 2812 (:REWRITE RATIONALP-MINUS-X))
 (2812 2812 (:META META-RATIONALP-CORRECT))
 (2464 2464 (:REWRITE REDUCE-INTEGERP-+))
 (2464 2464 (:REWRITE INTEGERP-MINUS-X))
 (2464 2464 (:META META-INTEGERP-CORRECT))
 (2234 2234 (:TYPE-PRESCRIPTION BOOLEANP))
 (2153
  2153
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (2153
      2153
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (2153
     2153
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (2153 2153
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (2153 2153
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (1982 1430 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (1836 1836 (:TYPE-PRESCRIPTION RTL::OPAW))
 (1499 1499 (:REWRITE SUBSETP-MEMBER . 4))
 (1499 1499 (:REWRITE SUBSETP-MEMBER . 3))
 (1499 1499 (:REWRITE SUBSETP-MEMBER . 2))
 (1499 1499 (:REWRITE SUBSETP-MEMBER . 1))
 (1461 1461
       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (1461 1461 (:REWRITE NORMALIZE-ADDENDS))
 (1430 1430
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (1430 1430
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (1430 1430
       (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (1430 1430 (:REWRITE |(equal c (/ x))|))
 (1430 1430 (:REWRITE |(equal c (- x))|))
 (1430 1430 (:REWRITE |(equal (/ x) c)|))
 (1430 1430 (:REWRITE |(equal (/ x) (/ y))|))
 (1430 1430 (:REWRITE |(equal (- x) c)|))
 (1430 1430 (:REWRITE |(equal (- x) (- y))|))
 (829 829 (:REWRITE |(< (* x y) 0)|))
 (703 703 (:REWRITE |(< (/ x) 0)|))
 (700 700
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (700 700
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (612 612 (:REWRITE |(< (+ c/d x) y)|))
 (568 568
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (568 568
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (568 568 (:REWRITE |(< 0 (/ x))|))
 (568 568 (:REWRITE |(< 0 (* x y))|))
 (353 353
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (249 249
      (:REWRITE RTL::BITS-REVERSE-INDICES))
 (249 249 (:REWRITE RTL::BITS-NEG-INDICES))
 (168 168 (:REWRITE |(equal (+ (- c) x) y)|))
 (117 1 (:REWRITE |(< x (if a b c))|))
 (30 1 (:REWRITE ODD-EXPT-THM))
 (13 2 (:REWRITE DEFAULT-EXPT-2))
 (2 2 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (1 1 (:REWRITE DEFAULT-EXPT-1))
 (1 1 (:REWRITE |(expt 1/c n)|))
 (1 1 (:REWRITE |(expt (- x) n)|)))
(RTL::SI-EXPSHFT-NORM
 (5963 845
       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (4807 2143
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (4629 613 (:REWRITE ACL2-NUMBERP-X))
 (4551 108 (:REWRITE RTL::BITS-TAIL))
 (2779 2143
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (2723 2174 (:REWRITE DEFAULT-LESS-THAN-1))
 (2577 2577 (:TYPE-PRESCRIPTION RTL::SI))
 (2393 2174 (:REWRITE DEFAULT-LESS-THAN-2))
 (2215 845
       (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (2174 2174 (:REWRITE THE-FLOOR-BELOW))
 (2174 2174 (:REWRITE THE-FLOOR-ABOVE))
 (2173 2143 (:REWRITE |(< (- x) c)|))
 (2173 2143 (:REWRITE |(< (- x) (- y))|))
 (2158 2158
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (2158 2158
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (2143 2143
       (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (2143 2143 (:REWRITE INTEGERP-<-CONSTANT))
 (2143 2143 (:REWRITE CONSTANT-<-INTEGERP))
 (2143 2143
       (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (2143 2143
       (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (2143 2143
       (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (2143 2143
       (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (2143 2143 (:REWRITE |(< c (- x))|))
 (2143 2143
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (2143 2143
       (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (2143 2143
       (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (2143 2143
       (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (2143 2143 (:REWRITE |(< (/ x) (/ y))|))
 (2122 2113 (:REWRITE SIMPLIFY-SUMS-<))
 (2008 502 (:REWRITE RATIONALP-X))
 (1861 1849
       (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (1734
  1734
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1734
      1734
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1734
     1734
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1734 1734
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1734 1734
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (1506 129 (:REWRITE RTL::NEG-BITN-0))
 (1412 845 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (927 654 (:REWRITE DEFAULT-PLUS-1))
 (894 654 (:REWRITE DEFAULT-PLUS-2))
 (860 860
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (845 845
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (845 845 (:REWRITE |(equal c (/ x))|))
 (845 845 (:REWRITE |(equal c (- x))|))
 (845 845 (:REWRITE |(equal (/ x) c)|))
 (845 845 (:REWRITE |(equal (/ x) (/ y))|))
 (845 845 (:REWRITE |(equal (- x) c)|))
 (845 845 (:REWRITE |(equal (- x) (- y))|))
 (840 15 (:REWRITE |(< (if a b c) x)|))
 (782 782 (:TYPE-PRESCRIPTION BOOLEANP))
 (552 282 (:REWRITE NORMALIZE-ADDENDS))
 (534 534 (:REWRITE REDUCE-INTEGERP-+))
 (534 534 (:REWRITE INTEGERP-MINUS-X))
 (534 534 (:META META-INTEGERP-CORRECT))
 (502 502 (:REWRITE REDUCE-RATIONALP-+))
 (502 502 (:REWRITE REDUCE-RATIONALP-*))
 (502 502 (:REWRITE RATIONALP-MINUS-X))
 (502 502 (:META META-RATIONALP-CORRECT))
 (495 15 (:REWRITE |(< y (+ (- c) x))|))
 (457 457 (:REWRITE |(< (/ x) 0)|))
 (457 457 (:REWRITE |(< (* x y) 0)|))
 (442 442
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (442 442
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (434 434 (:REWRITE SUBSETP-MEMBER . 4))
 (434 434 (:REWRITE SUBSETP-MEMBER . 3))
 (434 434 (:REWRITE SUBSETP-MEMBER . 2))
 (434 434 (:REWRITE SUBSETP-MEMBER . 1))
 (345 129 (:REWRITE RTL::NEG-BITN-1))
 (270 15 (:REWRITE |(+ (if a b c) x)|))
 (252 252
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (228 228
      (:REWRITE RTL::BITS-REVERSE-INDICES))
 (228 228 (:REWRITE RTL::BITS-NEG-INDICES))
 (157 157
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (157 157
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (157 157 (:REWRITE |(< 0 (/ x))|))
 (157 157 (:REWRITE |(< 0 (* x y))|))
 (149 149
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (120 60 (:DEFINITION FIX))
 (117 1 (:REWRITE |(< x (if a b c))|))
 (108 108 (:REWRITE RTL::BITN-NEG))
 (78 78 (:REWRITE RTL::BITS-BVECP-SIMPLE))
 (78 78 (:REWRITE RTL::BITS-BVECP))
 (60 30 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (60 30 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
 (30 30 (:REWRITE |(< (+ c/d x) y)|))
 (30 30 (:REWRITE |(< (+ (- c) x) y)|))
 (30 30 (:REWRITE |(+ x (- x))|))
 (30 15 (:REWRITE DEFAULT-MINUS))
 (30 1 (:REWRITE ODD-EXPT-THM))
 (15 15 (:REWRITE |(< x (+ c/d y))|))
 (13 2 (:REWRITE DEFAULT-EXPT-2))
 (2 2 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (1 1 (:REWRITE DEFAULT-EXPT-1))
 (1 1 (:REWRITE |(expt 1/c n)|))
 (1 1 (:REWRITE |(expt (- x) n)|)))
(RTL::SI-EXPSHFT (5 5 (:TYPE-PRESCRIPTION RTL::SI))
                 (5 5 (:TYPE-PRESCRIPTION RTL::INT-SI)))
(RTL::NREPP-DREPP (565 70
                       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                  (494 62 (:REWRITE ACL2-NUMBERP-X))
                  (216 54 (:REWRITE RATIONALP-X))
                  (171 70 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
                  (92 92 (:TYPE-PRESCRIPTION BOOLEANP))
                  (86 70 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                  (80 80 (:REWRITE SUBSETP-MEMBER . 4))
                  (80 80 (:REWRITE SUBSETP-MEMBER . 3))
                  (80 80 (:REWRITE SUBSETP-MEMBER . 2))
                  (80 80 (:REWRITE SUBSETP-MEMBER . 1))
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
                  (54 54 (:REWRITE REDUCE-RATIONALP-+))
                  (54 54 (:REWRITE REDUCE-RATIONALP-*))
                  (54 54 (:REWRITE REDUCE-INTEGERP-+))
                  (54 54 (:REWRITE RATIONALP-MINUS-X))
                  (54 54 (:REWRITE INTEGERP-MINUS-X))
                  (54 54 (:META META-RATIONALP-CORRECT))
                  (54 54 (:META META-INTEGERP-CORRECT))
                  (21 21
                      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RTL::RATIONALP-ABS
     (4 1 (:REWRITE RATIONALP-X))
     (1 1
        (:TYPE-PRESCRIPTION RTL::RATIONALP-ABS))
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
     (1 1 (:REWRITE REDUCE-RATIONALP-+))
     (1 1 (:REWRITE REDUCE-RATIONALP-*))
     (1 1
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (1 1
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (1 1 (:REWRITE REDUCE-INTEGERP-+))
     (1 1 (:REWRITE RATIONALP-MINUS-X))
     (1 1 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (1 1 (:REWRITE INTEGERP-MINUS-X))
     (1 1 (:REWRITE INTEGERP-<-CONSTANT))
     (1 1 (:REWRITE DEFAULT-MINUS))
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
     (1 1 (:META META-RATIONALP-CORRECT))
     (1 1 (:META META-INTEGERP-CORRECT)))
(RTL::EXACTP-A
 (374 181 (:REWRITE DEFAULT-PLUS-2))
 (356
  356
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (356 356
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (356
     356
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (356 356
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (356 356
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (230 67 (:REWRITE DEFAULT-TIMES-2))
 (170 25
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (153 17 (:REWRITE ACL2-NUMBERP-X))
 (101 101
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (101 101 (:REWRITE NORMALIZE-ADDENDS))
 (97 67 (:REWRITE DEFAULT-TIMES-1))
 (97 1 (:REWRITE |(< x (if a b c))|))
 (71 32 (:REWRITE DEFAULT-LESS-THAN-2))
 (68 17 (:REWRITE RATIONALP-X))
 (66 3 (:REWRITE |(* x (if a b c))|))
 (65 25 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (60 29
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (60 29 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (52 52 (:REWRITE REDUCE-INTEGERP-+))
 (52 52 (:REWRITE INTEGERP-MINUS-X))
 (52 52 (:META META-INTEGERP-CORRECT))
 (43 43
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (38 29 (:REWRITE SIMPLIFY-SUMS-<))
 (32 32 (:REWRITE THE-FLOOR-BELOW))
 (32 32 (:REWRITE THE-FLOOR-ABOVE))
 (31 22 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (30 30 (:TYPE-PRESCRIPTION BOOLEANP))
 (29 29 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (29 29
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (29 29
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (29 29
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (29 29 (:REWRITE INTEGERP-<-CONSTANT))
 (29 29 (:REWRITE CONSTANT-<-INTEGERP))
 (29 29
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (29 29
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (29 29
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (29 29
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (29 29 (:REWRITE |(< c (- x))|))
 (29 29
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (29 29
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (29 29
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (29 29
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (29 29 (:REWRITE |(< (/ x) (/ y))|))
 (29 29 (:REWRITE |(< (- x) c)|))
 (29 29 (:REWRITE |(< (- x) (- y))|))
 (25 25 (:REWRITE SIMPLIFY-SUMS-EQUAL))
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
 (22 1 (:REWRITE |(expt x (if a b c))|))
 (19 19 (:REWRITE |(< y (+ (- c) x))|))
 (19 19 (:REWRITE |(< x (+ c/d y))|))
 (17 17 (:REWRITE REDUCE-RATIONALP-+))
 (17 17 (:REWRITE REDUCE-RATIONALP-*))
 (17 17 (:REWRITE RATIONALP-MINUS-X))
 (17 17 (:META META-RATIONALP-CORRECT))
 (15 15
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (14 2 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (14 1 (:REWRITE |(+ x (if a b c))|))
 (12 12
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (12 12
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (12 12 (:REWRITE DEFAULT-EXPT-1))
 (12 12 (:REWRITE |(< 0 (/ x))|))
 (12 12 (:REWRITE |(< 0 (* x y))|))
 (11 11 (:REWRITE |(expt 1/c n)|))
 (11 11 (:REWRITE |(expt (- x) n)|))
 (11 11 (:REWRITE |(< (+ c/d x) y)|))
 (11 11 (:REWRITE |(< (+ (- c) x) y)|))
 (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (3 1 (:REWRITE RTL::BVECP-EXACTP))
 (2 2 (:TYPE-PRESCRIPTION RTL::BVECP))
 (2 2 (:REWRITE |(+ 0 x)|))
 (1 1 (:TYPE-PRESCRIPTION RTL::FORMATP))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (* x y) 0)|)))
(RTL::EXACTP-SIGA
 (93 24 (:REWRITE DEFAULT-TIMES-2))
 (83 24 (:REWRITE DEFAULT-TIMES-1))
 (55
  55
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (55 55
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (55 55
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (55 55
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (18 2 (:REWRITE ACL2-NUMBERP-X))
 (8 8 (:REWRITE DEFAULT-PLUS-1))
 (8 2 (:REWRITE RATIONALP-X))
 (7 7 (:REWRITE REDUCE-INTEGERP-+))
 (7 7 (:REWRITE INTEGERP-MINUS-X))
 (7 7 (:META META-INTEGERP-CORRECT))
 (6 6 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (5 5
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (5 5 (:REWRITE NORMALIZE-ADDENDS))
 (4 4 (:REWRITE DEFAULT-EXPT-1))
 (3 3 (:REWRITE |(expt 1/c n)|))
 (3 3 (:REWRITE |(expt (- x) n)|))
 (2 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (2 2 (:REWRITE REDUCE-RATIONALP-+))
 (2 2 (:REWRITE REDUCE-RATIONALP-*))
 (2 2 (:REWRITE RATIONALP-MINUS-X))
 (2 2 (:META META-RATIONALP-CORRECT))
 (1 1 (:REWRITE BUBBLE-DOWN-*-MATCH-3)))
(RTL::P-VALS (30 3
                 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
             (27 3 (:REWRITE ACL2-NUMBERP-X))
             (12 3 (:REWRITE RATIONALP-X))
             (9 3 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
             (6 6 (:TYPE-PRESCRIPTION BOOLEANP))
             (4 4 (:REWRITE SUBSETP-MEMBER . 4))
             (4 4 (:REWRITE SUBSETP-MEMBER . 3))
             (4 4 (:REWRITE SUBSETP-MEMBER . 2))
             (4 4 (:REWRITE SUBSETP-MEMBER . 1))
             (3 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
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
             (3 3 (:REWRITE |(equal c (/ x))|))
             (3 3 (:REWRITE |(equal c (- x))|))
             (3 3 (:REWRITE |(equal (/ x) c)|))
             (3 3 (:REWRITE |(equal (/ x) (/ y))|))
             (3 3 (:REWRITE |(equal (- x) c)|))
             (3 3 (:REWRITE |(equal (- x) (- y))|))
             (3 3 (:META META-RATIONALP-CORRECT))
             (3 3 (:META META-INTEGERP-CORRECT))
             (1 1
                (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RTL::SIGA-LOW
 (288 8 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (288 8 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (273 14 (:DEFINITION =))
 (248 84 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (248 84
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (248 84
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (246
  246
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (246 246
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (246
     246
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (246 246
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (200 8 (:REWRITE MOD-ZERO . 4))
 (188 13 (:REWRITE RTL::SIGA-DENORMP))
 (176 176
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (176 176
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (176 176
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (164 82 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
 (160 10 (:REWRITE DEFAULT-MOD-RATIO))
 (154 2 (:REWRITE MOD-X-Y-=-X . 4))
 (154 2 (:REWRITE MOD-X-Y-=-X . 3))
 (125 125
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (125 125
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (125 125
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (123 54 (:REWRITE DEFAULT-TIMES-1))
 (116 54 (:REWRITE DEFAULT-TIMES-2))
 (111 13 (:REWRITE RTL::SIGA-NORMP))
 (100 23
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (84 84 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (84 84
     (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (84 84
     (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (84 2 (:REWRITE RTL::BITS-TAIL-GEN))
 (82 82 (:TYPE-PRESCRIPTION RTL::NATP-MOD-2))
 (82 82 (:TYPE-PRESCRIPTION NATP))
 (82 82 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (82 82 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (82 82 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
 (82 82
     (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
 (81 9 (:REWRITE ACL2-NUMBERP-X))
 (70 19
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (70 19 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (59 19 (:REWRITE DEFAULT-LESS-THAN-1))
 (56 4 (:REWRITE |(* (* x y) z)|))
 (51 23 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (36 9 (:REWRITE RATIONALP-X))
 (35 19
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (35 19
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (30 19 (:REWRITE DEFAULT-LESS-THAN-2))
 (28 10 (:REWRITE DEFAULT-MOD-1))
 (27 23
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (23 23 (:REWRITE SIMPLIFY-SUMS-EQUAL))
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
 (22 2 (:REWRITE MOD-X-Y-=-X . 2))
 (20 20
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (19 19 (:REWRITE THE-FLOOR-BELOW))
 (19 19 (:REWRITE THE-FLOOR-ABOVE))
 (19 19 (:REWRITE SIMPLIFY-SUMS-<))
 (19 19
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
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
     (:TYPE-PRESCRIPTION RTL::RATIONALP-ABS))
 (18 18 (:TYPE-PRESCRIPTION ABS))
 (18 18 (:REWRITE REDUCE-INTEGERP-+))
 (18 18
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (18 18 (:REWRITE INTEGERP-MINUS-X))
 (18 18 (:META META-INTEGERP-CORRECT))
 (18 8 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (18 8 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (16 16 (:REWRITE SUBSETP-MEMBER . 4))
 (16 16 (:REWRITE SUBSETP-MEMBER . 3))
 (16 16 (:REWRITE SUBSETP-MEMBER . 2))
 (16 16 (:REWRITE SUBSETP-MEMBER . 1))
 (14 14 (:TYPE-PRESCRIPTION BOOLEANP))
 (12 2
     (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (11 11 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (10 10 (:REWRITE DEFAULT-MOD-2))
 (9 9 (:REWRITE REDUCE-RATIONALP-+))
 (9 9 (:REWRITE REDUCE-RATIONALP-*))
 (9 9 (:REWRITE RATIONALP-MINUS-X))
 (9 9 (:META META-RATIONALP-CORRECT))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (8 8 (:REWRITE |(< (/ x) 0)|))
 (8 8 (:REWRITE |(< (* x y) 0)|))
 (6 2 (:REWRITE RTL::BITS-TAIL))
 (6 2
    (:REWRITE |(<= 1 (* (/ x) y)) with (< 0 x)|))
 (6 2
    (:REWRITE |(< (* (/ x) y) 1) with (< 0 x)|))
 (4 4
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (4 2
    (:REWRITE |(<= 1 (* (/ x) y)) with (< x 0)|))
 (4 2
    (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (3 3 (:REWRITE DEFAULT-PLUS-1))
 (3 3 (:REWRITE |(< 0 (/ x))|))
 (3 3 (:REWRITE |(< 0 (* x y))|))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-3D))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-2D))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-1D))
 (2 2
    (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (2 2 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (2 2 (:REWRITE DEFAULT-EXPT-1))
 (2 2 (:REWRITE RTL::BITS-NEG-INDICES))
 (2 2 (:REWRITE |(mod x (- y))| . 3))
 (2 2 (:REWRITE |(mod x (- y))| . 2))
 (2 2 (:REWRITE |(mod x (- y))| . 1))
 (2 2
    (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (2 2
    (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (2 2 (:REWRITE |(equal (* x y) 0)|))
 (2 2
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (1 1
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (1 1 (:REWRITE NORMALIZE-ADDENDS))
 (1 1 (:REWRITE |(expt 1/c n)|))
 (1 1 (:REWRITE |(expt (- x) n)|)))
(RTL::A-SIGA
 (426 46 (:REWRITE DEFAULT-TIMES-2))
 (378 366
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (378 366
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (366
  366
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (366 366
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (366
     366
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (171 21
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (154 21 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (87 46 (:REWRITE DEFAULT-TIMES-1))
 (78 52 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (60 21 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (52 26 (:REWRITE DEFAULT-EXPT-2))
 (37 37 (:TYPE-PRESCRIPTION RTL::SI))
 (37 37 (:TYPE-PRESCRIPTION RTL::INT-SI))
 (34 15 (:REWRITE DEFAULT-PLUS-2))
 (30 1
     (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (30 1
     (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (30 1 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (30 1 (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (26 26 (:REWRITE DEFAULT-EXPT-1))
 (26 26 (:REWRITE |(expt 1/c n)|))
 (26 26 (:REWRITE |(expt (- x) n)|))
 (26 15 (:REWRITE DEFAULT-PLUS-1))
 (25 10 (:REWRITE DEFAULT-LESS-THAN-2))
 (22 22
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (22 22
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (22 22 (:REWRITE |(equal c (/ x))|))
 (22 22 (:REWRITE |(equal (/ x) (/ y))|))
 (22 22 (:REWRITE |(equal (- x) (- y))|))
 (21 21
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (21 21 (:REWRITE |(equal c (- x))|))
 (21 21 (:REWRITE |(equal (- x) c)|))
 (17 1 (:REWRITE |(not (equal x (/ y)))|))
 (17 1 (:REWRITE |(equal x (/ y))|))
 (13 9 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (12 9
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (12 9 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (10 10 (:REWRITE THE-FLOOR-BELOW))
 (10 10 (:REWRITE THE-FLOOR-ABOVE))
 (10 10 (:REWRITE DEFAULT-LESS-THAN-1))
 (9 9 (:REWRITE SIMPLIFY-SUMS-<))
 (9 9
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (9 9
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
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
 (8 8 (:REWRITE |(* c (* d x))|))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (7 7 (:REWRITE |(< 0 (/ x))|))
 (7 7 (:REWRITE |(< 0 (* x y))|))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (5 5 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (5 5
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (4 3 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (3 3 (:REWRITE DEFAULT-DIVIDE))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (2 2 (:REWRITE |(< (/ x) 0)|))
 (2 2 (:REWRITE |(< (* x y) 0)|))
 (2 1 (:REWRITE DEFAULT-MINUS))
 (1 1 (:REWRITE FOLD-CONSTS-IN-+))
 (1 1 (:REWRITE BUBBLE-DOWN-*-MATCH-3)))
(RTL::SI-EXPSHFT-BOUNDS
 (467 7 (:REWRITE |(< x (if a b c))|))
 (373 3 (:REWRITE |(< (if a b c) x)|))
 (338 74 (:REWRITE DEFAULT-PLUS-2))
 (284 13 (:REWRITE |(+ x (if a b c))|))
 (210 2 (:DEFINITION RTL::BIAS))
 (147 35 (:REWRITE DEFAULT-LESS-THAN-2))
 (118 118 (:TYPE-PRESCRIPTION RTL::SI))
 (118 118 (:TYPE-PRESCRIPTION RTL::INT-SI))
 (112
   112
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
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
 (112 112
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (112 112
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (112 35 (:REWRITE DEFAULT-LESS-THAN-1))
 (104 72 (:REWRITE DEFAULT-PLUS-1))
 (90 10 (:REWRITE ACL2-NUMBERP-X))
 (84 25
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (84 25 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (75 10 (:REWRITE DEFAULT-EXPT-2))
 (62 7
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (62 2 (:REWRITE |(+ y (+ x z))|))
 (54 25 (:REWRITE SIMPLIFY-SUMS-<))
 (44 2 (:REWRITE |(expt x (if a b c))|))
 (40 10 (:REWRITE RATIONALP-X))
 (35 35 (:REWRITE THE-FLOOR-BELOW))
 (35 35 (:REWRITE THE-FLOOR-ABOVE))
 (28 4 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (27 27
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (27 27 (:REWRITE NORMALIZE-ADDENDS))
 (25 25 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (25 25
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (25 25
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (25 25
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (25 25 (:REWRITE INTEGERP-<-CONSTANT))
 (25 25 (:REWRITE CONSTANT-<-INTEGERP))
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
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (25 25
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (25 25
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (25 25
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (25 25 (:REWRITE |(< (/ x) (/ y))|))
 (25 25 (:REWRITE |(< (- x) c)|))
 (25 25 (:REWRITE |(< (- x) (- y))|))
 (20 20 (:REWRITE REDUCE-INTEGERP-+))
 (20 20 (:REWRITE INTEGERP-MINUS-X))
 (20 20 (:META META-INTEGERP-CORRECT))
 (20 7 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (18 18 (:REWRITE |(< (+ c/d x) y)|))
 (18 18 (:REWRITE |(< (+ (- c) x) y)|))
 (12 12 (:TYPE-PRESCRIPTION BOOLEANP))
 (12 8 (:REWRITE |(+ 0 x)|))
 (10 10 (:REWRITE REDUCE-RATIONALP-+))
 (10 10 (:REWRITE REDUCE-RATIONALP-*))
 (10 10 (:REWRITE RATIONALP-MINUS-X))
 (10 10 (:META META-RATIONALP-CORRECT))
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
 (6 6 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (5 5 (:REWRITE DEFAULT-EXPT-1))
 (5 5 (:REWRITE |(< (/ x) 0)|))
 (5 5 (:REWRITE |(< (* x y) 0)|))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (4 4 (:REWRITE |(< y (+ (- c) x))|))
 (4 4 (:REWRITE |(< x (+ c/d y))|))
 (4 4 (:REWRITE |(< 0 (/ x))|))
 (4 4 (:REWRITE |(< 0 (* x y))|))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (3 3 (:REWRITE |(expt 1/c n)|))
 (3 3 (:REWRITE |(expt (- x) n)|))
 (3 1 (:REWRITE RTL::BVECP-EXACTP))
 (2 2 (:TYPE-PRESCRIPTION RTL::BVECP))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE |(+ c (+ d x))|))
 (1 1 (:TYPE-PRESCRIPTION RTL::FORMATP)))
(RTL::EXPQ-REWRITE-1
 (1191 57 (:REWRITE ACL2-NUMBERP-X))
 (888 15 (:REWRITE RTL::BITS-TAIL-GEN))
 (612 54 (:REWRITE RATIONALP-X))
 (450 12 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (435 87 (:TYPE-PRESCRIPTION RTL::INT-SI))
 (261 87 (:TYPE-PRESCRIPTION RTL::SI))
 (228 6 (:REWRITE |(+ (if a b c) x)|))
 (198 6 (:REWRITE |(< y (+ (- c) x))|))
 (180 27
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (150 114 (:REWRITE DEFAULT-PLUS-2))
 (96 96 (:REWRITE REDUCE-INTEGERP-+))
 (96 96 (:REWRITE INTEGERP-MINUS-X))
 (96 96 (:META META-INTEGERP-CORRECT))
 (96 42 (:REWRITE NORMALIZE-ADDENDS))
 (90 9 (:REWRITE RTL::INT-SI))
 (90 6 (:REWRITE |(+ y (+ x z))|))
 (84 12 (:REWRITE RTL::NEG-BITN-1))
 (84 12 (:REWRITE RTL::NEG-BITN-0))
 (81 27 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (54 54 (:REWRITE REDUCE-RATIONALP-+))
 (54 54 (:REWRITE REDUCE-RATIONALP-*))
 (54 54 (:REWRITE RATIONALP-MINUS-X))
 (54 54 (:META META-RATIONALP-CORRECT))
 (45 15 (:REWRITE RTL::BITS-TAIL))
 (36 36
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (36 12 (:REWRITE RTL::BVECP-BITN-0))
 (30 18 (:REWRITE DEFAULT-LESS-THAN-2))
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
 (24 18 (:REWRITE DEFAULT-LESS-THAN-1))
 (24 12
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (24 12 (:DEFINITION FIX))
 (21 21 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (21 21 (:REWRITE RTL::BITS-NEG-INDICES))
 (18 18 (:TYPE-PRESCRIPTION BOOLEANP))
 (18 18 (:REWRITE THE-FLOOR-BELOW))
 (18 18 (:REWRITE THE-FLOOR-ABOVE))
 (18 18
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (18 18
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (18 12 (:REWRITE |(< (- x) c)|))
 (18 12 (:REWRITE |(< (- x) (- y))|))
 (13 13
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (12 12
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (12
   12
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (12
  12
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (12 12
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (12 12
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (12 12
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (12 12
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (12 12
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (12 12
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (12 12 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (12 12
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (12 12 (:REWRITE INTEGERP-<-CONSTANT))
 (12 12 (:REWRITE CONSTANT-<-INTEGERP))
 (12 12 (:REWRITE RTL::BITN-NEG))
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
 (12 6 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (12 6 (:REWRITE DEFAULT-MINUS))
 (12 6 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
 (6 6 (:REWRITE SIMPLIFY-SUMS-<))
 (6 6 (:REWRITE |(< x (+ c/d y))|))
 (6 6 (:REWRITE |(< (+ c/d x) y)|))
 (6 6 (:REWRITE |(< (+ (- c) x) y)|))
 (6 6 (:REWRITE |(+ x (- x))|))
 (4 4 (:REWRITE SUBSETP-MEMBER . 4))
 (4 4 (:REWRITE SUBSETP-MEMBER . 3))
 (4 4 (:REWRITE SUBSETP-MEMBER . 2))
 (4 4 (:REWRITE SUBSETP-MEMBER . 1)))
(RTL::EXPQ-REWRITE
 (6798 72 (:REWRITE RTL::INTEGERP-FL))
 (5208 24 (:LINEAR MOD-BOUNDS-1))
 (2556 12 (:LINEAR RTL::MOD-BND-2))
 (2556 12 (:LINEAR RTL::MOD-BND-1))
 (2517 159
       (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (2334 60 (:REWRITE MOD-ZERO . 3))
 (2250 60 (:REWRITE MOD-X-Y-=-X . 4))
 (2190 60 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (2100 60 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (1710 60 (:REWRITE MOD-ZERO . 4))
 (1566 606 (:REWRITE DEFAULT-PLUS-2))
 (1452 1452
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (1452 1452
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (1452 1452
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (1377 147
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (1266 1266
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (1266 1266
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (1266 1266
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (1197 609 (:REWRITE DEFAULT-TIMES-1))
 (1122 33 (:REWRITE EVEN-AND-ODD-ALTERNATE))
 (1110 222 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (1110 222 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (1110 222
       (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (1110 222
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (981 609 (:REWRITE DEFAULT-TIMES-2))
 (906 102 (:REWRITE RATIONALP-X))
 (810 60 (:REWRITE |(< y (+ (- c) x))|))
 (573 78 (:REWRITE RTL::FL+INT-REWRITE))
 (561 57 (:REWRITE ACL2-NUMBERP-X))
 (462 12 (:LINEAR MOD-BOUNDS-3))
 (444 222 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
 (390 390 (:REWRITE REDUCE-INTEGERP-+))
 (390 390 (:REWRITE INTEGERP-MINUS-X))
 (390 390 (:META META-INTEGERP-CORRECT))
 (366 366
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (366 366 (:REWRITE NORMALIZE-ADDENDS))
 (363 363
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (354 354 (:REWRITE THE-FLOOR-BELOW))
 (354 354 (:REWRITE THE-FLOOR-ABOVE))
 (354 354 (:REWRITE DEFAULT-LESS-THAN-2))
 (330 330
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (330 330
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (300 60 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (300 60 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (231 222
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (222 222
      (:TYPE-PRESCRIPTION RTL::NATP-MOD-2))
 (222 222 (:TYPE-PRESCRIPTION NATP))
 (222 222 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (222 222
      (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (222 222
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (222 222 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (222 222 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
 (222 222
      (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
 (222 222 (:REWRITE SIMPLIFY-SUMS-<))
 (222 222
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (222 222
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (222 222
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
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
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (222 222
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (222 222
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (222 222 (:REWRITE |(< (/ x) (/ y))|))
 (222 222 (:REWRITE |(< (- x) c)|))
 (222 222 (:REWRITE |(< (- x) (- y))|))
 (192 87
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (180 6 (:REWRITE RTL::MOD-DOES-NOTHING))
 (153 153 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (150 150
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (150 150 (:REWRITE |(< (+ c/d x) y)|))
 (147 147
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (123 87 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (120 24 (:LINEAR MOD-BOUNDS-2))
 (102 102 (:REWRITE RATIONALP-MINUS-X))
 (102 30 (:REWRITE RTL::NEG-BITN-1))
 (102 30 (:REWRITE RTL::NEG-BITN-0))
 (99 87 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (90 30 (:REWRITE RTL::BVECP-BITN-0))
 (87 87
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (87 87 (:REWRITE |(equal c (/ x))|))
 (87 87 (:REWRITE |(equal c (- x))|))
 (87 87 (:REWRITE |(equal (/ x) c)|))
 (87 87 (:REWRITE |(equal (/ x) (/ y))|))
 (87 87 (:REWRITE |(equal (- x) c)|))
 (87 87 (:REWRITE |(equal (- x) (- y))|))
 (84 84
     (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
 (78 78 (:META META-RATIONALP-CORRECT))
 (72 72 (:REWRITE DEFAULT-MOD-2))
 (72 72 (:REWRITE DEFAULT-MOD-1))
 (69 69 (:REWRITE |(< (* x y) 0)|))
 (60 60 (:REWRITE |(< x (+ c/d y))|))
 (60 60 (:REWRITE |(< 0 (* x y))|))
 (54 54 (:TYPE-PRESCRIPTION RTL::SI))
 (54 54 (:TYPE-PRESCRIPTION RTL::INT-SI))
 (48 48 (:LINEAR RTL::FL-MONOTONE-LINEAR))
 (33 33
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (33 33
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (33 33 (:REWRITE |(< (/ x) 0)|))
 (30 30
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (30 30
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (30 30 (:REWRITE RTL::BITN-NEG))
 (30 30 (:REWRITE |(< 0 (/ x))|))
 (30 6 (:REWRITE MOD-X-Y-=-X . 2))
 (30 6
     (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (30 6
     (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 1))
 (30 6
     (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (27
   27
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
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
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (24 24 (:LINEAR RTL::N<=FL-LINEAR))
 (18 18 (:TYPE-PRESCRIPTION BOOLEANP))
 (12 12 (:LINEAR RTL::MOD-BND-3))
 (6 6
    (:REWRITE THIS-NEEDS-TO-BE-ADDED-TO-QUOTIENT-REMAINDER-LEMMAS))
 (6 6
    (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (6 6 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (6 6 (:REWRITE RTL::BITS-NEG-INDICES))
 (6 6 (:REWRITE |(mod x (- y))| . 3))
 (6 6 (:REWRITE |(mod x (- y))| . 2))
 (6 6 (:REWRITE |(mod x (- y))| . 1))
 (6 6
    (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (6 6
    (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (6 6
    (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 3))
 (6 6
    (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 2))
 (6 6
    (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (4 4 (:REWRITE SUBSETP-MEMBER . 4))
 (4 4 (:REWRITE SUBSETP-MEMBER . 3))
 (4 4 (:REWRITE SUBSETP-MEMBER . 2))
 (4 4 (:REWRITE SUBSETP-MEMBER . 1))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RTL::INTEGERP-EXPSHFT
 (1386 33 (:REWRITE RTL::NEG-BITN-0))
 (1376 32 (:REWRITE RTL::BITS-TAIL-GEN))
 (1221 33 (:REWRITE RTL::NEG-BITN-1))
 (744 744
      (:TYPE-PRESCRIPTION RTL::INTEGERP-OPA))
 (473 59
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (310 22 (:REWRITE ACL2-NUMBERP-X))
 (277 277 (:TYPE-PRESCRIPTION RTL::SI))
 (264 98 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (207 59 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (193 99 (:REWRITE DEFAULT-LESS-THAN-1))
 (193 98
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (158 22 (:REWRITE RATIONALP-X))
 (101 99 (:REWRITE DEFAULT-LESS-THAN-2))
 (99 99 (:REWRITE THE-FLOOR-BELOW))
 (99 99 (:REWRITE THE-FLOOR-ABOVE))
 (99 99
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (99 99
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (99 98 (:REWRITE |(< (- x) c)|))
 (99 98 (:REWRITE |(< (- x) (- y))|))
 (99 33 (:REWRITE RTL::BVECP-BITN-0))
 (98 98
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (98 98 (:REWRITE INTEGERP-<-CONSTANT))
 (98 98 (:REWRITE CONSTANT-<-INTEGERP))
 (98 98
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (98 98
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (98 98
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (98 98
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (98 98 (:REWRITE |(< c (- x))|))
 (98 98
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (98 98
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (98 98
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (98 98
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (98 98 (:REWRITE |(< (/ x) (/ y))|))
 (97 97 (:REWRITE SIMPLIFY-SUMS-<))
 (96 32 (:REWRITE RTL::BITS-TAIL))
 (71 71 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (71 71 (:REWRITE RTL::BITS-NEG-INDICES))
 (65 65
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (65
   65
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (65
  65
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (65 65
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (65 65
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (65 65
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (65 65
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (65 65
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (65 65
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (59 59 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (59 59
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (59 59
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (59 59
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (59 59 (:REWRITE |(equal c (/ x))|))
 (59 59 (:REWRITE |(equal c (- x))|))
 (59 59 (:REWRITE |(equal (/ x) c)|))
 (59 59 (:REWRITE |(equal (/ x) (/ y))|))
 (59 59 (:REWRITE |(equal (- x) c)|))
 (59 59 (:REWRITE |(equal (- x) (- y))|))
 (44 44 (:TYPE-PRESCRIPTION BOOLEANP))
 (37 37
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (33 33
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (33 33
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (33 33 (:REWRITE RTL::BITN-NEG))
 (33 33 (:REWRITE |(< (/ x) 0)|))
 (33 33 (:REWRITE |(< (* x y) 0)|))
 (33 1 (:REWRITE |(< y (+ (- c) x))|))
 (31 31 (:REWRITE REDUCE-INTEGERP-+))
 (31 31 (:REWRITE INTEGERP-MINUS-X))
 (31 31 (:META META-INTEGERP-CORRECT))
 (28 7 (:REWRITE RTL::INT-SI))
 (24 24
     (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (22 22 (:REWRITE REDUCE-RATIONALP-+))
 (22 22 (:REWRITE REDUCE-RATIONALP-*))
 (22 22 (:REWRITE RATIONALP-MINUS-X))
 (22 22 (:META META-RATIONALP-CORRECT))
 (21 18 (:REWRITE DEFAULT-LOGAND-2))
 (21 18 (:REWRITE DEFAULT-LOGAND-1))
 (18 18 (:REWRITE LOGAND-CONSTANT-MASK))
 (15 1 (:REWRITE |(+ y (+ x z))|))
 (12 3 (:REWRITE NORMALIZE-ADDENDS))
 (11 6 (:REWRITE DEFAULT-PLUS-2))
 (11 6 (:REWRITE DEFAULT-PLUS-1))
 (6 1 (:REWRITE |(+ y x)|))
 (4 2 (:DEFINITION FIX))
 (2 2 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (2 2
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (2 1
    (:TYPE-PRESCRIPTION RTL::INTEGERP-EXPSHFT))
 (2 1 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (2 1 (:REWRITE DEFAULT-MINUS))
 (2 1 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
 (1 1 (:REWRITE |(< x (+ c/d y))|))
 (1 1 (:REWRITE |(< (+ c/d x) y)|))
 (1 1 (:REWRITE |(< (+ (- c) x) y)|))
 (1 1 (:REWRITE |(+ x (- x))|)))
(RTL::INTEGERP-SI-EXPSHFT (6 2 (:TYPE-PRESCRIPTION RTL::SI))
                          (2 1
                             (:TYPE-PRESCRIPTION RTL::INTEGERP-SI-EXPSHFT)))
(RTL::EXPQ-BOUNDS
 (960 15 (:REWRITE RTL::INTEGERP-FL))
 (795 15
      (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (570 15 (:REWRITE EVEN-AND-ODD-ALTERNATE))
 (312 156
      (:TYPE-PRESCRIPTION RTL::INTEGERP-EXPSHFT))
 (300 30 (:REWRITE RTL::FL+INT-REWRITE))
 (234 78 (:TYPE-PRESCRIPTION RTL::SI))
 (234 78 (:TYPE-PRESCRIPTION RTL::INT-SI))
 (204 204
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (204 204
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (204 204
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (150 39 (:REWRITE DEFAULT-PLUS-2))
 (120 33 (:REWRITE DEFAULT-TIMES-2))
 (68
   68
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (68
  68
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (68 68
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (68 68
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (68 68
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (68 68
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (68 68
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (48 48 (:REWRITE REDUCE-INTEGERP-+))
 (48 48 (:REWRITE INTEGERP-MINUS-X))
 (48 48 (:META META-INTEGERP-CORRECT))
 (45 39 (:REWRITE DEFAULT-PLUS-1))
 (39 33 (:REWRITE DEFAULT-TIMES-1))
 (33 33
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (33 33 (:REWRITE NORMALIZE-ADDENDS))
 (30 15 (:REWRITE |(* a (/ a) b)|))
 (30 3
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (27 3 (:REWRITE ACL2-NUMBERP-X))
 (21 12
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (21 12 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (18 12 (:REWRITE DEFAULT-LESS-THAN-1))
 (15 12 (:REWRITE DEFAULT-LESS-THAN-2))
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
 (12 12
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
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
 (12 12 (:LINEAR RTL::FL-MONOTONE-LINEAR))
 (12 3 (:REWRITE RATIONALP-X))
 (9 3 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (6 6 (:TYPE-PRESCRIPTION BOOLEANP))
 (6 6 (:LINEAR RTL::N<=FL-LINEAR))
 (4 4 (:REWRITE SUBSETP-MEMBER . 4))
 (4 4 (:REWRITE SUBSETP-MEMBER . 3))
 (4 4 (:REWRITE SUBSETP-MEMBER . 2))
 (4 4 (:REWRITE SUBSETP-MEMBER . 1))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
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
 (3 3 (:REWRITE |(< 0 (/ x))|))
 (3 3 (:REWRITE |(< 0 (* x y))|))
 (3 3 (:META META-RATIONALP-CORRECT))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
