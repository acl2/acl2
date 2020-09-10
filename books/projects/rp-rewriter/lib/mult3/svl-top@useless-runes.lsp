(RP::SVL-MULT-RULES_RP-FORMULA-CHECKS)
(RP::SVL-MULT-RULES_RP-RW-META-RULE)
(RP::INTEGERP-OF-NTH
     (75 12
         (:REWRITE INTEGERP-OF-CAR-WHEN-INTEGER-LISTP))
     (26 19 (:REWRITE DEFAULT-LESS-THAN-2))
     (24 18
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (24 18 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (23 18 (:REWRITE SIMPLIFY-SUMS-<))
     (22 18
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (19 19 (:REWRITE THE-FLOOR-BELOW))
     (19 19 (:REWRITE THE-FLOOR-ABOVE))
     (19 19
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (19 19
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (19 19 (:REWRITE REDUCE-INTEGERP-+))
     (19 19
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (19 19 (:REWRITE INTEGERP-MINUS-X))
     (19 19
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (19 19 (:REWRITE DEFAULT-LESS-THAN-1))
     (19 19 (:META META-INTEGERP-CORRECT))
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
     (18 18
         (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
     (18 18
         (:LINEAR LISTPOS-UPPER-BOUND-STRONG-2))
     (18 18 (:LINEAR LEN-WHEN-PREFIXP))
     (17 10 (:REWRITE DEFAULT-PLUS-2))
     (15 15 (:REWRITE DEFAULT-CAR))
     (14 14 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (10 10
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (10 10 (:REWRITE NORMALIZE-ADDENDS))
     (10 10 (:REWRITE DEFAULT-PLUS-1))
     (10 2
         (:REWRITE INTEGER-LISTP-OF-CDR-WHEN-INTEGER-LISTP))
     (9 9
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (9 9
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (9 9 (:REWRITE |(< 0 (/ x))|))
     (9 9 (:REWRITE |(< 0 (* x y))|))
     (9 9 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (9 9 (:LINEAR BOUNDS-POSITION-EQUAL))
     (6 6 (:REWRITE DEFAULT-CDR))
     (5 5 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (4 4 (:REWRITE |(< y (+ (- c) x))|))
     (4 4 (:REWRITE |(< x (+ c/d y))|))
     (4 4 (:REWRITE |(< (/ x) 0)|))
     (4 4 (:REWRITE |(< (* x y) 0)|))
     (3 3 (:REWRITE NTH-WHEN-PREFIXP))
     (1 1 (:REWRITE |(< (+ c/d x) y)|))
     (1 1
        (:LINEAR SV::LHS-VARS-NORMORDEREDP-IMPLIES-LHS-BITPROJ-INDEX-BOUND))
     (1 1
        (:LINEAR SV::LHS-VARS-NORMORDEREDP-IMPLIES-INDEX-BOUND))
     (1 1
        (:LINEAR SV::LHATOM-NORMORDEREDP-IMPLIES-INDEX-BOUND)))
(RP::BITS-IS-BIT-OF-FOR-NTH
     (230 2 (:DEFINITION NTH))
     (151 3 (:REWRITE RP::+-IS-SUM))
     (143 8
          (:REWRITE RP::SUM-OF-NEGATED-ELEMENTS))
     (66 1 (:DEFINITION LEN))
     (64 2 (:REWRITE ZP-WHEN-INTEGERP))
     (60 2 (:REWRITE ZP-WHEN-GT-0))
     (43 43 (:TYPE-PRESCRIPTION RP::--))
     (28 4 (:REWRITE RP::SUM-COMM-1))
     (25 6 (:REWRITE RP::EQUAL-SIDES-TO-S))
     (18 1 (:DEFINITION INTEGER-LISTP))
     (10 10 (:TYPE-PRESCRIPTION BITP))
     (9 7 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (9 6
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (9 6
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (8 7 (:REWRITE SIMPLIFY-SUMS-<))
     (8 7
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (8 7 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (8 7 (:REWRITE DEFAULT-LESS-THAN-2))
     (7 7 (:REWRITE THE-FLOOR-BELOW))
     (7 7 (:REWRITE THE-FLOOR-ABOVE))
     (7 7
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (7 7
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (7 7 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (7 7 (:REWRITE INTEGERP-<-CONSTANT))
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
     (5 5 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (5 1
        (:REWRITE INTEGERP-OF-CAR-WHEN-INTEGER-LISTP))
     (5 1
        (:REWRITE INTEGER-LISTP-OF-CDR-WHEN-INTEGER-LISTP))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (4 4
        (:REWRITE INTEGER-LISTP-WHEN-NOT-CONSP))
     (4 4 (:REWRITE DEFAULT-CDR))
     (4 4 (:REWRITE |(< 0 (/ x))|))
     (4 4 (:REWRITE |(< 0 (* x y))|))
     (4 3 (:REWRITE DEFAULT-PLUS-2))
     (3 3 (:REWRITE REDUCE-INTEGERP-+))
     (3 3
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (3 3 (:REWRITE NORMALIZE-ADDENDS))
     (3 3 (:REWRITE INTEGERP-MINUS-X))
     (3 3
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (3 3 (:REWRITE DEFAULT-PLUS-1))
     (3 3 (:REWRITE DEFAULT-CAR))
     (3 3 (:META META-INTEGERP-CORRECT))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (2 2 (:REWRITE NTH-WHEN-PREFIXP))
     (2 2 (:REWRITE RP::NTH-OF-CONSTANT))
     (2 2 (:REWRITE |(< (/ x) 0)|))
     (2 2 (:REWRITE |(< (* x y) 0)|))
     (2 2
        (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
     (2 2
        (:LINEAR LISTPOS-UPPER-BOUND-STRONG-2))
     (2 2 (:LINEAR LEN-WHEN-PREFIXP))
     (2 1 (:REWRITE RP::BITS-IS-BIT-OF))
     (1 1 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (1 1 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (1 1 (:LINEAR BOUNDS-POSITION-EQUAL)))
(RP::BITS-OF-BIT-OF (8 2 (:REWRITE RP::EQUAL-SIDES-TO-S))
                    (6 1 (:REWRITE O-INFP->NEQ-0))
                    (3 3 (:TYPE-PRESCRIPTION O-FINP))
                    (3 1 (:REWRITE O-FIRST-EXPT-O-INFP))
                    (2 1 (:REWRITE O-FIRST-EXPT-DEF-O-FINP)))
(RP::4VEC-BITXOR-IS-BINARY-XOR-WHEN-BITP
     (24 6 (:REWRITE RP::EQUAL-SIDES-TO-S))
     (18 3 (:REWRITE O-INFP->NEQ-0))
     (9 9 (:TYPE-PRESCRIPTION O-FINP))
     (9 3 (:REWRITE O-FIRST-EXPT-O-INFP))
     (6 3 (:REWRITE O-FIRST-EXPT-DEF-O-FINP)))
(RP::4VEC-BITXOR-IS-BINARY-XOR-WHEN-INTEGERP-1
     (8 2 (:REWRITE RP::EQUAL-SIDES-TO-S))
     (6 1 (:REWRITE O-INFP->NEQ-0))
     (3 3 (:TYPE-PRESCRIPTION O-FINP))
     (3 1 (:REWRITE O-FIRST-EXPT-O-INFP))
     (3 1 (:REWRITE NATP-WHEN-GTE-0))
     (2 2
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (2 1 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
     (2 1 (:REWRITE NATP-WHEN-INTEGERP))
     (1 1 (:REWRITE DEFAULT-<-2))
     (1 1 (:REWRITE DEFAULT-<-1)))
(RP::4VEC-BITXOR-IS-BINARY-XOR-WHEN-INTEGERP-2
     (6 2 (:REWRITE NATP-WHEN-GTE-0))
     (4 4
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (4 2 (:REWRITE NATP-WHEN-INTEGERP))
     (2 2 (:REWRITE DEFAULT-<-2))
     (2 2 (:REWRITE DEFAULT-<-1)))
(RP::4VEC-BITAND-IS-BINARY-AND-WHEN-BITP
     (24 6 (:REWRITE RP::EQUAL-SIDES-TO-S))
     (18 3 (:REWRITE O-INFP->NEQ-0))
     (9 9 (:TYPE-PRESCRIPTION O-FINP))
     (9 3 (:REWRITE O-FIRST-EXPT-O-INFP))
     (6 3 (:REWRITE O-FIRST-EXPT-DEF-O-FINP)))
(RP::4VEC-BITAND-IS-BINARY-AND-WHEN-INTEGERP-1
     (8 2 (:REWRITE RP::EQUAL-SIDES-TO-S))
     (6 1 (:REWRITE O-INFP->NEQ-0))
     (3 3 (:TYPE-PRESCRIPTION O-FINP))
     (3 1 (:REWRITE O-FIRST-EXPT-O-INFP))
     (3 1 (:REWRITE NATP-WHEN-GTE-0))
     (2 2
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (2 1 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
     (2 1 (:REWRITE NATP-WHEN-INTEGERP))
     (1 1 (:REWRITE DEFAULT-<-2))
     (1 1 (:REWRITE DEFAULT-<-1)))
(RP::4VEC-BITAND-IS-BINARY-AND-WHEN-INTEGERP-2
     (6 2 (:REWRITE NATP-WHEN-GTE-0))
     (4 4
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (4 2 (:REWRITE NATP-WHEN-INTEGERP))
     (2 2 (:REWRITE DEFAULT-<-2))
     (2 2 (:REWRITE DEFAULT-<-1)))
(RP::4VEC-BITOR-IS-BINARY-OR-WHEN-BITP
     (24 6 (:REWRITE RP::EQUAL-SIDES-TO-S))
     (18 3 (:REWRITE O-INFP->NEQ-0))
     (9 9 (:TYPE-PRESCRIPTION O-FINP))
     (9 3 (:REWRITE O-FIRST-EXPT-O-INFP))
     (6 3 (:REWRITE O-FIRST-EXPT-DEF-O-FINP)))
(RP::4VEC-BITOR-IS-BINARY-OR-WHEN-INTEGERP-1
     (8 2 (:REWRITE RP::EQUAL-SIDES-TO-S))
     (6 1 (:REWRITE O-INFP->NEQ-0))
     (3 3 (:TYPE-PRESCRIPTION O-FINP))
     (3 1 (:REWRITE O-FIRST-EXPT-O-INFP))
     (3 1 (:REWRITE NATP-WHEN-GTE-0))
     (2 2
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (2 1 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
     (2 1 (:REWRITE NATP-WHEN-INTEGERP))
     (1 1 (:REWRITE DEFAULT-<-2))
     (1 1 (:REWRITE DEFAULT-<-1)))
(RP::4VEC-BITOR-IS-BINARY-OR-WHEN-INTEGERP-2
     (6 2 (:REWRITE NATP-WHEN-GTE-0))
     (4 4
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (4 2 (:REWRITE NATP-WHEN-INTEGERP))
     (2 2 (:REWRITE DEFAULT-<-2))
     (2 2 (:REWRITE DEFAULT-<-1)))
(RP::4VEC-?-IS-BINARY-?-WHEN-BITP (56 14 (:REWRITE RP::EQUAL-SIDES-TO-S))
                                  (42 7 (:REWRITE O-INFP->NEQ-0))
                                  (21 21 (:TYPE-PRESCRIPTION O-FINP))
                                  (21 7 (:REWRITE O-FIRST-EXPT-O-INFP))
                                  (14 7 (:REWRITE O-FIRST-EXPT-DEF-O-FINP)))
(RP::4VEC-?-IS-BINARY-?-WHEN-INTEGERP-1
     (24 6 (:REWRITE RP::EQUAL-SIDES-TO-S))
     (18 3 (:REWRITE O-INFP->NEQ-0))
     (9 9 (:TYPE-PRESCRIPTION O-FINP))
     (9 3 (:REWRITE O-FIRST-EXPT-O-INFP))
     (6 3 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
     (3 1 (:REWRITE NATP-WHEN-GTE-0))
     (2 2
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (2 1 (:REWRITE NATP-WHEN-INTEGERP))
     (1 1 (:REWRITE DEFAULT-<-2))
     (1 1 (:REWRITE DEFAULT-<-1)))
(RP::4VEC-?-IS-BINARY-?-WHEN-INTEGERP-2
     (8 2 (:REWRITE RP::EQUAL-SIDES-TO-S))
     (6 2 (:REWRITE NATP-WHEN-GTE-0))
     (6 1 (:REWRITE O-INFP->NEQ-0))
     (4 4
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (4 2 (:REWRITE NATP-WHEN-INTEGERP))
     (3 3 (:TYPE-PRESCRIPTION O-FINP))
     (3 1 (:REWRITE O-FIRST-EXPT-O-INFP))
     (2 2 (:REWRITE DEFAULT-<-2))
     (2 2 (:REWRITE DEFAULT-<-1))
     (2 1 (:REWRITE O-FIRST-EXPT-DEF-O-FINP)))
(RP::4VEC-?-IS-BINARY-?-WHEN-INTEGERP-3
     (9 3 (:REWRITE NATP-WHEN-GTE-0))
     (6 6
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (6 3 (:REWRITE NATP-WHEN-INTEGERP))
     (3 3 (:REWRITE DEFAULT-<-2))
     (3 3 (:REWRITE DEFAULT-<-1)))
(RP::4VEC-?*-IS-BINARY-?-WHEN-BITP (56 14 (:REWRITE RP::EQUAL-SIDES-TO-S))
                                   (42 7 (:REWRITE O-INFP->NEQ-0))
                                   (21 21 (:TYPE-PRESCRIPTION O-FINP))
                                   (21 7 (:REWRITE O-FIRST-EXPT-O-INFP))
                                   (14 7 (:REWRITE O-FIRST-EXPT-DEF-O-FINP)))
(RP::4VEC-?*-IS-BINARY-?-WHEN-INTEGERP-1
     (24 6 (:REWRITE RP::EQUAL-SIDES-TO-S))
     (18 3 (:REWRITE O-INFP->NEQ-0))
     (9 9 (:TYPE-PRESCRIPTION O-FINP))
     (9 3 (:REWRITE O-FIRST-EXPT-O-INFP))
     (6 3 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
     (3 1 (:REWRITE NATP-WHEN-GTE-0))
     (2 2
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (2 1 (:REWRITE NATP-WHEN-INTEGERP))
     (1 1 (:REWRITE DEFAULT-<-2))
     (1 1 (:REWRITE DEFAULT-<-1)))
(RP::4VEC-?*-IS-BINARY-?-WHEN-INTEGERP-2
     (8 2 (:REWRITE RP::EQUAL-SIDES-TO-S))
     (6 2 (:REWRITE NATP-WHEN-GTE-0))
     (6 1 (:REWRITE O-INFP->NEQ-0))
     (4 4
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (4 2 (:REWRITE NATP-WHEN-INTEGERP))
     (3 3 (:TYPE-PRESCRIPTION O-FINP))
     (3 1 (:REWRITE O-FIRST-EXPT-O-INFP))
     (2 2 (:REWRITE DEFAULT-<-2))
     (2 2 (:REWRITE DEFAULT-<-1))
     (2 1 (:REWRITE O-FIRST-EXPT-DEF-O-FINP)))
(RP::4VEC-?*-IS-BINARY-?-WHEN-INTEGERP-3
     (9 3 (:REWRITE NATP-WHEN-GTE-0))
     (6 6
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (6 3 (:REWRITE NATP-WHEN-INTEGERP))
     (3 3 (:REWRITE DEFAULT-<-2))
     (3 3 (:REWRITE DEFAULT-<-1)))
(RP::CONVERT-4VEC-BITNOT$-BINARY-NOT-0
     (28 2 (:REWRITE DEFAULT-MOD-RATIO))
     (25 25 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (25 25 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (25 25 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (16 12 (:REWRITE DEFAULT-TIMES-2))
     (14 12 (:REWRITE DEFAULT-TIMES-1))
     (11 3 (:REWRITE DEFAULT-PLUS-1))
     (7 7
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (7 3 (:REWRITE DEFAULT-PLUS-2))
     (7 1 (:REWRITE DEFAULT-FLOOR-RATIO))
     (5 1 (:REWRITE DEFAULT-MINUS))
     (4 4 (:REWRITE REDUCE-INTEGERP-+))
     (4 4 (:REWRITE INTEGERP-MINUS-X))
     (4 4
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (4 4 (:META META-INTEGERP-CORRECT))
     (4 2 (:REWRITE DEFAULT-MOD-1))
     (3 3 (:REWRITE RP::INTEGERP-OF-*))
     (2 2 (:REWRITE DEFAULT-MOD-2))
     (2 2 (:REWRITE DEFAULT-LOGNOT))
     (2 2
        (:REWRITE SV::2VEC-P$INLINE-OF-4VEC-FIX-X-NORMALIZE-CONST))
     (2 2 (:REWRITE |(mod x 2)| . 2))
     (1 1 (:REWRITE DEFAULT-FLOOR-2))
     (1 1 (:REWRITE DEFAULT-FLOOR-1))
     (1 1
        (:REWRITE SV::3VEC-BITNOT-OF-4VEC-FIX-X-NORMALIZE-CONST))
     (1 1 (:REWRITE |(* 1 x)|)))
(RP::CONVERT-4VEC-BITNOT$-BINARY-NOT-1
     (26 2
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (24 4 (:REWRITE ACL2-NUMBERP-X))
     (10 2 (:REWRITE RATIONALP-X))
     (8 2 (:REWRITE RP::EQUAL-SIDES-TO-S))
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
(RP::CONVERT-4VEC-BITNOT$-BINARY-NOT-2
     (2 2 (:REWRITE REDUCE-INTEGERP-+))
     (2 2 (:REWRITE INTEGERP-MINUS-X))
     (2 2
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
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
(RP::4VEC-FIX=-OF-BINARY-FNS (4 2 (:REWRITE RP::F2-OF-BIT))
                             (2 2 (:TYPE-PRESCRIPTION BITP)))
(RP::BITS-OF-BINARY-FNS-LEMMA)
(RP::BITS-OF-BINARY-FNS-LEMMA-2
     (1 1 (:REWRITE THE-FLOOR-BELOW))
     (1 1 (:REWRITE THE-FLOOR-ABOVE))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
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
     (1 1
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
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
     (1 1 (:REWRITE |(< (- x) (- y))|))
     (1 1 (:META META-INTEGERP-CORRECT)))
(RP::BITS-OF-BINARY-FNS
     (840 24 (:DEFINITION NATP))
     (656 8 (:REWRITE RP::BITS-IS-BIT-OF))
     (593 17 (:REWRITE ZP-WHEN-GT-0))
     (584 72 (:REWRITE DEFAULT-LESS-THAN-2))
     (512 64 (:REWRITE ACL2-NUMBERP-X))
     (496 8
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (384 8 (:REWRITE RATIONALP-X))
     (368 8 (:REWRITE RP::EQUAL-SIDES-TO-S))
     (328 24 (:REWRITE NATP-WHEN-GTE-0))
     (320 56 (:REWRITE DEFAULT-LESS-THAN-1))
     (320 8 (:REWRITE SVL::INTEGERP-BITS))
     (320 8 (:REWRITE SVL::BITP-BITS-SIZE=1))
     (81 17 (:REWRITE ZP-WHEN-INTEGERP))
     (80 8 (:REWRITE O-INFP->NEQ-0))
     (72 72 (:REWRITE THE-FLOOR-BELOW))
     (72 72 (:REWRITE THE-FLOOR-ABOVE))
     (64 64
         (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (56 56 (:REWRITE REDUCE-INTEGERP-+))
     (56 56 (:REWRITE INTEGERP-MINUS-X))
     (56 56
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (56 56 (:META META-INTEGERP-CORRECT))
     (56 24 (:REWRITE NATP-WHEN-INTEGERP))
     (48 48 (:REWRITE SIMPLIFY-SUMS-<))
     (48 48
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (48 48
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (48 48
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (48 48
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (48 48
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (48 48 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
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
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (48 48
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (48 48
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (48 48
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (48 48 (:REWRITE |(< (/ x) (/ y))|))
     (48 48 (:REWRITE |(< (- x) c)|))
     (48 48 (:REWRITE |(< (- x) (- y))|))
     (48 8
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (32 32
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (32 32
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (32 32 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (32 32 (:REWRITE |(< (/ x) 0)|))
     (32 32 (:REWRITE |(< (* x y) 0)|))
     (32 8 (:REWRITE O-FIRST-EXPT-O-INFP))
     (24 24 (:TYPE-PRESCRIPTION O-FINP))
     (24 24 (:TYPE-PRESCRIPTION NATP))
     (24 8 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
     (17 17 (:REWRITE ZP-OPEN))
     (16 16
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (16 16
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (16 16 (:REWRITE |(< 0 (/ x))|))
     (16 16 (:REWRITE |(< 0 (* x y))|))
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
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
     (8 8 (:META META-RATIONALP-CORRECT)))
(RP::BITS-OF-BINARY-FNS-START=0
     (617 41 (:REWRITE ZP-WHEN-GT-0))
     (552 40 (:REWRITE DEFAULT-LESS-THAN-2))
     (504 56 (:REWRITE ACL2-NUMBERP-X))
     (496 8
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (384 8 (:REWRITE RATIONALP-X))
     (320 8 (:REWRITE SVL::INTEGERP-BITS))
     (280 8 (:DEFINITION NATP))
     (105 41 (:REWRITE ZP-WHEN-INTEGERP))
     (99 8
         (:REWRITE SVL::BITS-OF-BITP-SIZE=POSP-START=0))
     (56 56
         (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (48 8 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (48 8
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (48 8 (:REWRITE RP::EQUAL-SIDES-TO-S))
     (41 41 (:REWRITE ZP-OPEN))
     (40 40 (:REWRITE THE-FLOOR-BELOW))
     (40 40 (:REWRITE THE-FLOOR-ABOVE))
     (32 32 (:REWRITE REDUCE-INTEGERP-+))
     (32 32 (:REWRITE INTEGERP-MINUS-X))
     (32 32
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (32 32 (:META META-INTEGERP-CORRECT))
     (24 24 (:REWRITE SIMPLIFY-SUMS-<))
     (24 24
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (24 24
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (24 24
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (24 24
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (24 24
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (24 24 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (24 24 (:REWRITE INTEGERP-<-CONSTANT))
     (24 24 (:REWRITE DEFAULT-LESS-THAN-1))
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
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (24 24
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (24 24
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (24 24
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (24 24 (:REWRITE |(< (/ x) (/ y))|))
     (24 24 (:REWRITE |(< (- x) c)|))
     (24 24 (:REWRITE |(< (- x) (- y))|))
     (16 16 (:TYPE-PRESCRIPTION POSP))
     (16 16
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (16 16
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (16 16 (:REWRITE |(< 0 (/ x))|))
     (16 16 (:REWRITE |(< 0 (* x y))|))
     (8 8 (:TYPE-PRESCRIPTION NATP))
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (8 8 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (8 8 (:REWRITE REDUCE-RATIONALP-+))
     (8 8 (:REWRITE REDUCE-RATIONALP-*))
     (8 8
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (8 8
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (8 8 (:REWRITE RATIONALP-MINUS-X))
     (8 8
        (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (8 8 (:REWRITE NATP-WHEN-INTEGERP))
     (8 8 (:REWRITE NATP-WHEN-GTE-0))
     (8 8
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (8 8 (:REWRITE |(equal c (/ x))|))
     (8 8 (:REWRITE |(equal c (- x))|))
     (8 8 (:REWRITE |(equal (/ x) c)|))
     (8 8 (:REWRITE |(equal (/ x) (/ y))|))
     (8 8 (:REWRITE |(equal (- x) c)|))
     (8 8 (:REWRITE |(equal (- x) (- y))|))
     (8 8 (:REWRITE |(< (/ x) 0)|))
     (8 8 (:REWRITE |(< (* x y) 0)|))
     (8 8 (:META META-RATIONALP-CORRECT)))
(RP::LEMMA1
 (181 1 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (84 1 (:REWRITE FLOOR-=-X/Y . 3))
 (82 1 (:REWRITE FLOOR-=-X/Y . 2))
 (46 1 (:REWRITE FLOOR-ZERO . 5))
 (42
   42
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (42
  42
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (42 42
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (42 42
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (42 42
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (42 42
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (42 1 (:REWRITE DEFAULT-FLOOR-RATIO))
 (30 3 (:REWRITE DEFAULT-TIMES-2))
 (30 3 (:REWRITE DEFAULT-DIVIDE))
 (25 1 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (25 1 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (25 1 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (20 2 (:REWRITE RP::INTEGERP-OF-*))
 (18 3 (:REWRITE |(/ (expt x n))|))
 (11 2 (:REWRITE SIMPLIFY-SUMS-<))
 (11 2
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (11 2 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (11 2 (:REWRITE DEFAULT-LESS-THAN-2))
 (10 1 (:REWRITE DEFAULT-FLOOR-2))
 (8 8 (:REWRITE DEFAULT-EXPT-2))
 (8 8 (:REWRITE DEFAULT-EXPT-1))
 (8 8 (:REWRITE |(expt 1/c n)|))
 (8 8 (:REWRITE |(expt (- x) n)|))
 (7 7 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (7 7 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (7 7 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (7 7
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (7 7
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (6 6
    (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (6 6
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (6 6
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (6 6
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (3 3
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (3 3 (:REWRITE DEFAULT-TIMES-1))
 (3 3 (:REWRITE DEFAULT-MINUS))
 (2 2 (:REWRITE THE-FLOOR-BELOW))
 (2 2 (:REWRITE THE-FLOOR-ABOVE))
 (2 2 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (2 2 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (2 2
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (2 2
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (2 2 (:REWRITE REDUCE-INTEGERP-+))
 (2 2 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (2 2 (:REWRITE INTEGERP-MINUS-X))
 (2 2 (:REWRITE INTEGERP-<-CONSTANT))
 (2 2
    (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
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
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-TWO))
 (2 2 (:LINEAR EXPT-<-1-ONE))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (1 1 (:REWRITE ODD-EXPT-THM))
 (1 1 (:REWRITE NFIX-WHEN-NOT-NATP))
 (1 1 (:REWRITE DEFAULT-FLOOR-1))
 (1 1 (:REWRITE |(< 0 (/ x))|))
 (1 1 (:REWRITE |(< 0 (* x y))|))
 (1 1 (:LINEAR EXPT-X->=-X))
 (1 1 (:LINEAR EXPT-X->-X)))
(RP::LEMMA2 (26 2
                (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
            (24 4 (:REWRITE ACL2-NUMBERP-X))
            (10 2 (:REWRITE RATIONALP-X))
            (8 2 (:REWRITE RP::EQUAL-SIDES-TO-S))
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
(RP::BIT-OF-BINARY-FNS
     (186 6 (:REWRITE ZP-WHEN-GT-0))
     (170 10 (:REWRITE DEFAULT-LESS-THAN-2))
     (26 6 (:REWRITE ZP-WHEN-INTEGERP))
     (10 10 (:TYPE-PRESCRIPTION ZP))
     (10 10 (:REWRITE THE-FLOOR-BELOW))
     (10 10 (:REWRITE THE-FLOOR-ABOVE))
     (10 10 (:REWRITE ACL2-NUMBERP-X))
     (10 10
         (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (10 5
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (10 5 (:REWRITE O-INFP->NEQ-0))
     (6 6 (:REWRITE ZP-OPEN))
     (6 5
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (5 5 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (5 5 (:REWRITE SIMPLIFY-SUMS-<))
     (5 5
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (5 5 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (5 5
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (5 5
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (5 5
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (5 5 (:REWRITE REDUCE-INTEGERP-+))
     (5 5
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (5 5 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (5 5 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (5 5 (:REWRITE INTEGERP-MINUS-X))
     (5 5 (:REWRITE INTEGERP-<-CONSTANT))
     (5 5
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (5 5
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (5 5 (:REWRITE DEFAULT-LESS-THAN-1))
     (5 5 (:REWRITE CONSTANT-<-INTEGERP))
     (5 5 (:REWRITE |(equal c (/ x))|))
     (5 5 (:REWRITE |(equal c (- x))|))
     (5 5 (:REWRITE |(equal (/ x) c)|))
     (5 5 (:REWRITE |(equal (/ x) (/ y))|))
     (5 5 (:REWRITE |(equal (- x) c)|))
     (5 5 (:REWRITE |(equal (- x) (- y))|))
     (5 5
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (5 5
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (5 5
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (5 5
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (5 5 (:REWRITE |(< c (- x))|))
     (5 5 (:REWRITE |(< 0 (/ x))|))
     (5 5 (:REWRITE |(< 0 (* x y))|))
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
     (5 5 (:META META-INTEGERP-CORRECT)))
(RP::BIT-OF-BINARY-FNS-START=0)
(RP::BITS-OF-4VEC-==-BINARY-FNCS
     (28 2
         (:REWRITE SVL::BITS-OF-BITP-SIZE=POSP-START=0))
     (24 24 (:TYPE-PRESCRIPTION SV::4VEC-==))
     (22 8 (:DEFINITION BITP))
     (20 8 (:REWRITE RP::BIT-FIX-OPENER))
     (12 12 (:TYPE-PRESCRIPTION BITP))
     (10 2 (:REWRITE RP::BITS-IS-BIT-OF))
     (8 4 (:REWRITE O-INFP->NEQ-0))
     (2 2
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (2 2
        (:REWRITE SV::4VEC-==-OF-3VEC-FIX-Y-NORMALIZE-CONST))
     (2 2
        (:REWRITE SV::4VEC-==-OF-3VEC-FIX-X-NORMALIZE-CONST)))
(RP::BIT-OF-4VEC-BITNOT-MAIN (8 2 (:REWRITE RP::EQUAL-SIDES-TO-S))
                             (6 1 (:REWRITE O-INFP->NEQ-0))
                             (3 3 (:TYPE-PRESCRIPTION O-FINP))
                             (3 1 (:REWRITE O-FIRST-EXPT-O-INFP))
                             (2 1 (:REWRITE O-FIRST-EXPT-DEF-O-FINP)))
(RP::BIT-OF-4VEC-BITNOT (8 2 (:REWRITE RP::EQUAL-SIDES-TO-S))
                        (6 1 (:REWRITE O-INFP->NEQ-0))
                        (3 3 (:TYPE-PRESCRIPTION O-FINP))
                        (3 1 (:REWRITE O-FIRST-EXPT-O-INFP))
                        (2 1 (:REWRITE O-FIRST-EXPT-DEF-O-FINP)))
(RP::4VEC-FIX-OF-BIT-OF
 (778 40
      (:REWRITE RP::SUM-OF-NEGATED-ELEMENTS))
 (714 4
      (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
 (572 82 (:REWRITE RP::EQUAL-SIDES-TO-S))
 (458 24 (:DEFINITION BITP))
 (346 346 (:TYPE-PRESCRIPTION RP::--))
 (326 2 (:DEFINITION EXPT))
 (122 2 (:REWRITE ZIP-OPEN))
 (80 80 (:TYPE-PRESCRIPTION BITP))
 (56 8 (:REWRITE DEFAULT-*-2))
 (52 2 (:REWRITE INTEGERP==>NUMERATOR-=-X))
 (46 8 (:REWRITE DEFAULT-*-1))
 (38 12 (:REWRITE NFIX-EQUAL-TO-NONZERO))
 (36 6 (:REWRITE NFIX-WHEN-NATP))
 (32 6 (:REWRITE NFIX-EQUAL-TO-ZERO))
 (30 6 (:REWRITE NFIX-WHEN-NOT-NATP))
 (30 2 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
 (28 12 (:REWRITE DEFAULT-<-2))
 (28 6 (:REWRITE RP::INTEGERP-OF-*))
 (26 8 (:REWRITE DEFAULT-UNARY-MINUS))
 (20 20
     (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
 (20 12 (:REWRITE DEFAULT-<-1))
 (16 16 (:LINEAR LISTPOS-COMPLETE))
 (16 16
     (:LINEAR SV::LHS-VARS-NORMORDEREDP-IMPLIES-RSH-WHEN-INDEX-EQUAL))
 (16
    16
    (:LINEAR
         SV::LHS-VARS-NORMORDEREDP-IMPLIES-LHS-BITPROJ-IDX-WHEN-INDEX-BOUND))
 (16 16
     (:LINEAR SV::LHATOM-NORMORDEREDP-IMPLIES-RSH-WHEN-AT-BOUND))
 (16 16
     (:LINEAR SV::BOUND-OF-SVEXARR-VARS-WITNESS-AUX))
 (14 2 (:REWRITE DEFAULT-UNARY-/))
 (12 4 (:REWRITE ZP-WHEN-GT-0))
 (10 2 (:REWRITE DEFAULT-NUMERATOR))
 (10 2 (:REWRITE DEFAULT-DENOMINATOR))
 (8 8 (:TYPE-PRESCRIPTION NATP))
 (8 6 (:REWRITE RP::IFIX-OPENER))
 (8 4 (:REWRITE ZP-WHEN-INTEGERP))
 (8 4 (:REWRITE NATP-WHEN-GTE-0))
 (6 6
    (:REWRITE NFIX-EQUAL-TO-NONZERO-CONST))
 (6 4 (:REWRITE NATP-WHEN-INTEGERP))
 (4 4 (:REWRITE ZP-OPEN))
 (4 2 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
 (4 2 (:REWRITE IFIX-WHEN-INTEGERP))
 (2 2 (:TYPE-PRESCRIPTION ZP))
 (2 2 (:REWRITE NFIX-POSITIVE-TO-NON-ZP))
 (2 2
    (:REWRITE INEQUALITY-WITH-NFIX-HYP-1)))
(RP::INTEGERP-OF-BIT-OF)
(RP::3VEC-FIX-OF-BINARY-FNCS (48 20 (:REWRITE RP::BIT-FIX-OPENER))
                             (28 28 (:TYPE-PRESCRIPTION BITP))
                             (17 4
                                 (:REWRITE RP::SUM-OF-NEGATED-ELEMENTS))
                             (8 4 (:REWRITE O-INFP->NEQ-0))
                             (7 7 (:TYPE-PRESCRIPTION RP::--))
                             (4 2 (:REWRITE DEFAULT-UNARY-MINUS))
                             (2 2 (:REWRITE RP::SUM-COMM-1)))
(RP::3VEC-FIX-OF-BIT-OF)
(RP::BITS-WHEN-BITP-START=0 (8 2 (:REWRITE RP::EQUAL-SIDES-TO-S))
                            (6 1 (:REWRITE O-INFP->NEQ-0))
                            (3 3 (:TYPE-PRESCRIPTION O-FINP))
                            (3 1 (:REWRITE O-FIRST-EXPT-O-INFP))
                            (2 1 (:REWRITE O-FIRST-EXPT-DEF-O-FINP)))
(RP::BITS-0-1-OF-S (62 8
                       (:REWRITE RP::SUM-OF-NEGATED-ELEMENTS))
                   (14 4 (:REWRITE RP::EQUAL-SIDES-TO-S)))
(RP::BITS-0-1-OF-M2)
(RP::BITS-1-1-OF-S)
(RP::BITS-1-1-OF-M2)
(RP::EQUAL-OF-CONCAT$-WITH-HYP
     (81 11 (:REWRITE RP::EQUAL-SIDES-TO-S))
     (74 4 (:DEFINITION BITP))
     (40 4 (:REWRITE SV::4VEC-FIX-OF-4VEC))
     (34 2
         (:REWRITE SVL::EQUAL-OF-4VEC-CONCAT$-WITH-SIZE=1))
     (22 4 (:REWRITE SVL::BITP-IMPLIES-4VECP))
     (20 4
         (:REWRITE SV::4VEC-P-WHEN-MAYBE-4VEC-P))
     (18 18 (:TYPE-PRESCRIPTION BITP))
     (14 14 (:TYPE-PRESCRIPTION SV::4VEC-P))
     (8 8 (:TYPE-PRESCRIPTION SV::MAYBE-4VEC-P))
     (8 8
        (:REWRITE SV::4VEC-P-WHEN-MEMBER-EQUAL-OF-4VECLIST-P))
     (8 4
        (:REWRITE SV::MAYBE-4VEC-P-WHEN-4VEC-P))
     (8 4
        (:REWRITE SVL::INTEGERP-IMPLIES-4VECP))
     (4 4
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP)))
(RP::BITS-OF-C-WHEN-BIT-WHEN-START>0)
(RP::BITS-OF-C-WHEN-BIT-WHEN-START-0
     (208 10
          (:REWRITE RP::SUM-OF-NEGATED-ELEMENTS))
     (149 27 (:REWRITE RP::EQUAL-SIDES-TO-S))
     (66 1 (:REWRITE RP::--OF-SUM))
     (28 1
         (:REWRITE RP::DUMMY-SUM-CANCEL-LEMMA1))
     (18 1 (:REWRITE RP::F2-OF-BIT))
     (6 2 (:REWRITE RP::--OF---))
     (4 4 (:REWRITE RP::SUM-COMM-1))
     (4 2 (:REWRITE RP::IFIX-OPENER))
     (2 1 (:REWRITE O-INFP->NEQ-0))
     (1 1 (:REWRITE RP::SUM-COMM-2)))
(RP::BITS-OF-C-WHEN-BIT-WHEN-START-0-SIDE-COND)
(RP::BITS-OF-S-C-RES-WHEN-BIT-WHEN-START>0)
(RP::BITS-OF-S-C-RES-WHEN-BIT-WHEN-START=0
     (15 2 (:REWRITE RP::EQUAL-SIDES-TO-S))
     (2 1 (:REWRITE O-INFP->NEQ-0)))
(RP::BITS-OF-S-C-RES-WHEN-BIT-WHEN-START=0-SIDE-COND)
(RP::CONCAT-OF-ADDER-AND-IS-F2 (24 6 (:REWRITE RP::EQUAL-SIDES-TO-S))
                               (18 3 (:REWRITE O-INFP->NEQ-0))
                               (9 9 (:TYPE-PRESCRIPTION O-FINP))
                               (9 3 (:REWRITE O-FIRST-EXPT-O-INFP))
                               (6 3 (:REWRITE O-FIRST-EXPT-DEF-O-FINP)))
(RP::4VEC-CONCAT$-1-OF-BINARY-AND
     (154 16
          (:REWRITE RP::SUM-OF-NEGATED-ELEMENTS))
     (139 1
          (:REWRITE RP::EQUAL-OF-CONCAT$-WITH-HYP))
     (69 69 (:TYPE-PRESCRIPTION RP::--))
     (39 1 (:REWRITE RP::M2-OF-M2))
     (26 26 (:TYPE-PRESCRIPTION BITP))
     (26 7 (:REWRITE RP::SUM-COMM-1))
     (17 1
         (:REWRITE SVL::EQUAL-OF-4VEC-CONCAT$-WITH-SIZE=1))
     (10 4 (:REWRITE RP::BIT-FIX-OPENER))
     (8 4 (:REWRITE O-INFP->NEQ-0))
     (6 6 (:REWRITE RP::BITP-M2))
     (5 1
        (:REWRITE SV::4VEC-P-WHEN-MAYBE-4VEC-P))
     (4 4 (:TYPE-PRESCRIPTION SV::4VEC-P))
     (3 1 (:REWRITE SVL::BITP-IMPLIES-4VECP))
     (2 2 (:TYPE-PRESCRIPTION SV::MAYBE-4VEC-P))
     (2 2
        (:REWRITE SV::4VEC-P-WHEN-MEMBER-EQUAL-OF-4VECLIST-P))
     (2 1
        (:REWRITE SV::MAYBE-4VEC-P-WHEN-4VEC-P))
     (2 1
        (:REWRITE SVL::INTEGERP-IMPLIES-4VECP))
     (1 1
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (1 1 (:REWRITE RP::IFIX-OF-M2))
     (1 1 (:REWRITE SVL::4VEC-P-4VEC-CONCAT$)))
(RP::INSERT-REDUNDANT-LOGHEAD-TO-BITS
 (31539 200 (:REWRITE THE-FLOOR-ABOVE))
 (18716 145
        (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (16016 16016
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (16016 16016
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (16016 16016
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (15920 15920
        (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (15418 17 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (15381 393 (:REWRITE DEFAULT-TIMES-2))
 (14884 246 (:REWRITE DEFAULT-PLUS-2))
 (14541 246 (:REWRITE DEFAULT-PLUS-1))
 (14112 17 (:REWRITE MOD-X-Y-=-X . 3))
 (13747 17 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (12429 17 (:REWRITE MOD-ZERO . 4))
 (11965 149
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (11583 17 (:REWRITE MOD-X-Y-=-X . 4))
 (9139 703 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (9139 703
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (9139 703
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (9139 703
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (9139 703
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (9066 12 (:LINEAR LINEAR-FLOOR-BOUNDS-1))
 (8863 17 (:REWRITE DEFAULT-MOD-RATIO))
 (8356 4 (:REWRITE |(* x (+ y z))|))
 (6661 393 (:REWRITE DEFAULT-TIMES-1))
 (6636 17 (:REWRITE MOD-ZERO . 3))
 (5626 10 (:REWRITE |(* y (* x z))|))
 (5494 28 (:REWRITE CANCEL-FLOOR-+))
 (5434 7
       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (4921 703 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (4921 703 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (4921 703
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (4921 703
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (4921 703
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (4921 703
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (4921 703
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (4921 703
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
 (4921 703
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (4921 703
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (4096 63 (:REWRITE RP::INTEGERP-OF-*))
 (4004 28 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (3882 6 (:LINEAR MOD-BOUNDS-1))
 (3584
  3584
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (3584
      3584
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (3584
     3584
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (3584 3584
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (3584 3584
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (3456 417 (:REWRITE DEFAULT-MINUS))
 (3241 35 (:REWRITE |(integerp (expt x n))|))
 (3028 17 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (3028 17
       (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (2875 17 (:REWRITE MOD-X-Y-=-X . 2))
 (2425 28 (:REWRITE FLOOR-ZERO . 4))
 (2317 53 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (2257 28 (:REWRITE FLOOR-ZERO . 5))
 (2243 28 (:REWRITE FLOOR-ZERO . 3))
 (1939 190 (:REWRITE |(< (- x) c)|))
 (1858 194 (:REWRITE DEFAULT-LESS-THAN-2))
 (1828 200 (:REWRITE THE-FLOOR-BELOW))
 (1740 174 (:REWRITE DEFAULT-DIVIDE))
 (1726 28 (:REWRITE FLOOR-=-X/Y . 3))
 (1641 17 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (1641 17 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (1430 28 (:REWRITE DEFAULT-FLOOR-RATIO))
 (1369 194 (:REWRITE DEFAULT-LESS-THAN-1))
 (1276 28 (:REWRITE FLOOR-=-X/Y . 2))
 (1251 17 (:REWRITE DEFAULT-MOD-1))
 (1160 141 (:REWRITE SIMPLIFY-SUMS-<))
 (1016 152 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (1016 152 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (1016 152
       (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (1016 152
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (829 194 (:REWRITE |(< (- x) (- y))|))
 (805 28 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (788 28 (:REWRITE FLOOR-ZERO . 2))
 (788 28 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (788 28 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (785 7
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (758 15
      (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (756 1 (:REWRITE RP::STUPID-LEMMA1))
 (521 69 (:REWRITE |(- (+ x y))|))
 (386 90 (:REWRITE |(< 0 (/ x))|))
 (356 28
      (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (351 190 (:REWRITE |(< c (- x))|))
 (342 28 (:REWRITE FLOOR-CANCEL-*-CONST))
 (332 15 (:REWRITE MOD-CANCEL-*-CONST))
 (319 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (316 6 (:REWRITE RP::EQUAL-SIDES-TO-S))
 (296 21 (:REWRITE ODD-EXPT-THM))
 (280 28 (:REWRITE DEFAULT-FLOOR-2))
 (238 17 (:LINEAR EXPT->=-1-ONE))
 (236 26
      (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (236 26
      (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (233 233
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (233 233
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (233 233
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (233 233
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (230 230 (:REWRITE DEFAULT-EXPT-2))
 (230 230 (:REWRITE DEFAULT-EXPT-1))
 (230 230 (:REWRITE |(expt 1/c n)|))
 (230 230 (:REWRITE |(expt (- x) n)|))
 (219 67 (:REWRITE INTEGERP-MINUS-X))
 (208 28
      (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (206 26
      (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (206 26
      (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (194 194
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (194 194
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (194 194
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (194 194
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (194 194
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (194 194
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (194 194
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (194 194
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (194 194
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (194 194
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (194 194
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (194 194 (:REWRITE |(< (/ x) (/ y))|))
 (193 2 (:REWRITE FLOOR-=-X/Y . 4))
 (186 6 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (170 17 (:REWRITE DEFAULT-MOD-2))
 (168 7 (:REWRITE |(equal (- x) c)|))
 (168 7 (:REWRITE |(equal (- x) (- y))|))
 (155 155
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (155 155 (:REWRITE INTEGERP-<-CONSTANT))
 (155 155 (:REWRITE CONSTANT-<-INTEGERP))
 (152 152 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (152 152
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (152 152
      (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (152 152
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (150 6 (:LINEAR MOD-BOUNDS-2))
 (116 28 (:REWRITE DEFAULT-FLOOR-1))
 (112 34
      (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (111 111
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (108 108
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (108 108
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (108 108
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (105 15
      (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (101 11
      (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (101 11
      (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (96 6 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (95 17 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (90 90 (:REWRITE |(< 0 (* x y))|))
 (86 11
     (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (86 11
     (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (86 9
     (:REWRITE |(* (expt x m) (expt x n))|))
 (85 85
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (85 85
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (78 78 (:REWRITE |(< (/ x) 0)|))
 (78 78 (:REWRITE |(< (* x y) 0)|))
 (75 3 (:LINEAR MOD-BOUNDS-3))
 (67 67 (:REWRITE REDUCE-INTEGERP-+))
 (67 67
     (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
 (67 67 (:META META-INTEGERP-CORRECT))
 (51 51 (:REWRITE |(- (* c x))|))
 (40 40 (:REWRITE |(< y (+ (- c) x))|))
 (40 40 (:REWRITE |(< x (+ c/d y))|))
 (35 35
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (35 35
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (34 34
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (34 34
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (34 34
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (34 1 (:REWRITE FLOOR-POSITIVE . 3))
 (32 2
     (:REWRITE |(equal (floor (+ x y) z) x)|))
 (31 1 (:REWRITE MOD-POSITIVE . 3))
 (31 1 (:REWRITE FLOOR-POSITIVE . 2))
 (31 1 (:REWRITE FLOOR-NONPOSITIVE . 1))
 (26 26 (:REWRITE |(floor x (- y))| . 2))
 (26 26 (:REWRITE |(floor x (- y))| . 1))
 (26 26 (:REWRITE |(floor (- x) y)| . 2))
 (26 26 (:REWRITE |(floor (- x) y)| . 1))
 (25 1 (:REWRITE MOD-NONPOSITIVE))
 (25 1 (:REWRITE FLOOR-POSITIVE . 4))
 (25 1 (:REWRITE FLOOR-NONPOSITIVE . 3))
 (25 1 (:REWRITE FLOOR-NONPOSITIVE . 2))
 (24 24 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (23 23 (:REWRITE |(< (+ c/d x) y)|))
 (23 23 (:REWRITE |(< (+ (- c) x) y)|))
 (17 17 (:LINEAR EXPT-X->=-X))
 (17 17 (:LINEAR EXPT-X->-X))
 (17 17 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (17 17 (:LINEAR EXPT-LINEAR-UPPER-<))
 (17 17 (:LINEAR EXPT-LINEAR-LOWER-<))
 (17 17 (:LINEAR EXPT->=-1-TWO))
 (17 17 (:LINEAR EXPT->-1-TWO))
 (17 17 (:LINEAR EXPT->-1-ONE))
 (17 17 (:LINEAR EXPT-<=-1-TWO))
 (17 17 (:LINEAR EXPT-<=-1-ONE))
 (17 17 (:LINEAR EXPT-<-1-TWO))
 (17 17 (:LINEAR EXPT-<-1-ONE))
 (12 12
     (:REWRITE SV::2VEC-P$INLINE-OF-4VEC-FIX-X-NORMALIZE-CONST))
 (11 11 (:REWRITE |(mod x (- y))| . 3))
 (11 11 (:REWRITE |(mod x (- y))| . 2))
 (11 11 (:REWRITE |(mod x (- y))| . 1))
 (11 11 (:REWRITE |(mod (- x) y)| . 3))
 (11 11 (:REWRITE |(mod (- x) y)| . 2))
 (11 11 (:REWRITE |(mod (- x) y)| . 1))
 (11 11
     (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (10 10 (:REWRITE |(* c (* d x))|))
 (10 1 (:REWRITE MOD-POSITIVE . 2))
 (9 9 (:REWRITE NFIX-WHEN-NOT-NATP))
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
 (6 6 (:TYPE-PRESCRIPTION BITP))
 (6 6 (:REWRITE |(+ c (+ d x))|))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (4 4 (:REWRITE |(mod (floor x y) z)| . 5))
 (4 4 (:REWRITE |(mod (floor x y) z)| . 4))
 (4 4 (:REWRITE |(mod (floor x y) z)| . 3))
 (4 4 (:REWRITE |(mod (floor x y) z)| . 2))
 (1 1 (:REWRITE MOD-POSITIVE . 1))
 (1 1 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (1 1 (:REWRITE FLOOR-ZERO . 1))
 (1 1 (:REWRITE FLOOR-POSITIVE . 1))
 (1 1 (:REWRITE |(equal (+ (- c) x) y)|)))
(RP::BITS-OF-*)
(RP::NTH-OF-CONS (366 52
                      (:REWRITE RP::SUM-OF-NEGATED-ELEMENTS))
                 (138 47 (:REWRITE RP::EQUAL-SIDES-TO-S))
                 (72 72 (:TYPE-PRESCRIPTION RP::BINARY-SUM))
                 (54 3 (:REWRITE RP::--OF-SUM))
                 (52 52 (:TYPE-PRESCRIPTION BITP))
                 (51 3
                     (:REWRITE RP::DUMMY-SUM-CANCEL-LEMMA1))
                 (39 3 (:REWRITE RP::SUM-COMM-2))
                 (24 3 (:REWRITE ZP-WHEN-INTEGERP))
                 (24 3 (:REWRITE ZP-WHEN-GT-0))
                 (14 8 (:REWRITE DEFAULT-<-2))
                 (8 8 (:REWRITE DEFAULT-<-1))
                 (6 3 (:REWRITE RP::--OF---))
                 (5 5 (:REWRITE NTH-WHEN-PREFIXP))
                 (5 5 (:REWRITE RP::NTH-OF-CONSTANT))
                 (5 5 (:REWRITE DEFAULT-CDR))
                 (3 3 (:REWRITE RP::IFIX-OPENER))
                 (3 3 (:REWRITE DEFAULT-CAR))
                 (2 2
                    (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP)))
(RP::INTEGER-LISTP-OF-CONS
     (30 2 (:DEFINITION INTEGER-LISTP))
     (10 2
         (:REWRITE INTEGERP-OF-CAR-WHEN-INTEGER-LISTP))
     (10 2
         (:REWRITE INTEGER-LISTP-OF-CDR-WHEN-INTEGER-LISTP))
     (9 9
        (:REWRITE INTEGER-LISTP-WHEN-NOT-CONSP))
     (4 4
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (2 2 (:REWRITE DEFAULT-CDR))
     (2 2 (:REWRITE DEFAULT-CAR)))
