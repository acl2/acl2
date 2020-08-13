(RP::IFIX-OPENER (1 1 (:REWRITE REDUCE-INTEGERP-+))
                 (1 1 (:REWRITE INTEGERP-MINUS-X))
                 (1 1
                    (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                 (1 1 (:META META-INTEGERP-CORRECT)))
(RP::INTEGERP-M2-F2-D2 (46 46 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
                       (46 46 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                       (46 46 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                       (46 46 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                       (18 2 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
                       (18 2
                           (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
                       (18 2
                           (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
                       (18 2
                           (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
                       (18 2
                           (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
                       (10 2 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
                       (10 2 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
                       (10 2
                           (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
                       (10 2
                           (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
                       (10 2
                           (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
                       (10 2
                           (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
                       (10 2
                           (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
                       (10 2
                           (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
                       (10 2
                           (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
                       (10 2
                           (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
                       (5 1 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
                       (5 1 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
                       (5 1 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
                       (5 1 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
                       (1 1 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
                       (1 1 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
                       (1 1 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
                       (1 1 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
                       (1 1 (:TYPE-PRESCRIPTION INTEGERP-MOD-2)))
(RP::INTEGERP-IFIX)
(RP::M2-F2-D2-SUM-OF-IFIX (776 776
                               (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                          (776 776
                               (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                          (776 776
                               (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                          (252 28 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
                          (252 28
                               (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
                          (252 28
                               (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
                          (252 28
                               (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
                          (252 28
                               (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
                          (140 28 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
                          (140 28 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
                          (140 28
                               (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
                          (140 28
                               (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
                          (140 28
                               (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
                          (140 28
                               (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
                          (140 28
                               (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
                          (140 28
                               (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
                          (140 28
                               (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
                          (140 28
                               (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
                          (75 15 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
                          (75 15 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
                          (75 15
                              (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
                          (75 15
                              (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
                          (15 15 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
                          (15 15
                              (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
                          (15 15 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
                          (15 15
                              (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
                          (15 15 (:TYPE-PRESCRIPTION INTEGERP-MOD-2)))
(RP::CONSP-OF-RP-TRANS-LST)
(RP::SUM-COMM-ORDER-AUX
     (8785 7 (:REWRITE O<=-O-FINP-DEF))
     (7512 12 (:LINEAR ACL2-COUNT-OF-SUM))
     (5869 85 (:REWRITE SIMPLIFY-SUMS-<))
     (3990 76 (:DEFINITION INTEGER-ABS))
     (2793 125
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (2199 693 (:REWRITE DEFAULT-PLUS-2))
     (1951 693 (:REWRITE DEFAULT-PLUS-1))
     (1330 38 (:REWRITE |(+ (if a b c) x)|))
     (1178 38 (:REWRITE NUMERATOR-NEGATIVE))
     (1102 38 (:DEFINITION LENGTH))
     (950 38 (:DEFINITION LEN))
     (596 410 (:REWRITE NORMALIZE-ADDENDS))
     (570 76 (:REWRITE STR::CONSP-OF-EXPLODE))
     (415 45 (:REWRITE RATIONALP-X))
     (396 396
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (380 76
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (348 234 (:REWRITE DEFAULT-CDR))
     (342 342 (:TYPE-PRESCRIPTION NUMERATOR-ZERO))
     (342 342
          (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 2))
     (342 342
          (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 1))
     (342 342
          (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 2))
     (342 342
          (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 1))
     (329 125 (:REWRITE DEFAULT-LESS-THAN-1))
     (283 11 (:REWRITE |(+ y (+ x z))|))
     (266 76 (:REWRITE DEFAULT-MINUS))
     (228 76 (:DEFINITION APPLY$-BADGEP))
     (217 217 (:REWRITE DEFAULT-CAR))
     (152 76 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (152 38 (:REWRITE O-P-O-INFP-CAR))
     (151 125 (:REWRITE DEFAULT-LESS-THAN-2))
     (144 6
          (:LINEAR ACL2-COUNT-OF-CONSP-POSITIVE))
     (129 45
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (125 125 (:REWRITE THE-FLOOR-BELOW))
     (125 125 (:REWRITE THE-FLOOR-ABOVE))
     (125 125
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (125 125
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (123 123 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (123 123
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (123 123 (:REWRITE INTEGERP-<-CONSTANT))
     (123 123 (:REWRITE CONSTANT-<-INTEGERP))
     (123 123
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (123 123
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (123 123
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (123 123
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (123 123 (:REWRITE |(< c (- x))|))
     (123 123
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (123 123
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (123 123
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (123 123
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (123 123 (:REWRITE |(< (/ x) (/ y))|))
     (123 123 (:REWRITE |(< (- x) c)|))
     (123 123 (:REWRITE |(< (- x) (- y))|))
     (121 85
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (121 85 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (114 114
          (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
     (114 114 (:REWRITE |(< (/ x) 0)|))
     (114 114 (:REWRITE |(< (* x y) 0)|))
     (106 106 (:REWRITE FOLD-CONSTS-IN-+))
     (84 14 (:REWRITE ACL2-NUMBERP-X))
     (83 83 (:REWRITE REDUCE-INTEGERP-+))
     (83 83 (:REWRITE INTEGERP-MINUS-X))
     (83 83
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (83 83 (:META META-INTEGERP-CORRECT))
     (76 76 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (76 76
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (76 76
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (76 38
         (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
     (63 21 (:DEFINITION FIX))
     (59 45
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (45 45 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (45 45 (:REWRITE REDUCE-RATIONALP-+))
     (45 45 (:REWRITE REDUCE-RATIONALP-*))
     (45 45
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (45 45
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (45 45 (:REWRITE RATIONALP-MINUS-X))
     (45 45
         (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (45 45
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (45 45 (:REWRITE |(equal c (/ x))|))
     (45 45 (:REWRITE |(equal c (- x))|))
     (45 45 (:REWRITE |(equal (/ x) c)|))
     (45 45 (:REWRITE |(equal (/ x) (/ y))|))
     (45 45 (:REWRITE |(equal (- x) c)|))
     (45 45 (:REWRITE |(equal (- x) (- y))|))
     (45 45 (:META META-RATIONALP-CORRECT))
     (42 14 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (39 7 (:REWRITE AC-<))
     (38 38 (:TYPE-PRESCRIPTION LEN))
     (38 38 (:REWRITE O-P-DEF-O-FINP-1))
     (38 38 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (38 38 (:REWRITE INTEGERP==>NUMERATOR-=-X))
     (38 38
         (:REWRITE INTEGERP==>DENOMINATOR-=-1))
     (38 38
         (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
     (38 38 (:REWRITE DEFAULT-REALPART))
     (38 38
         (:REWRITE DEFAULT-RATIONAL-NUMERATOR))
     (38 38
         (:REWRITE DEFAULT-RATIONAL-DENOMINATOR))
     (38 38 (:REWRITE DEFAULT-IMAGPART))
     (24 12 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
     (21 7 (:REWRITE O-INFP-O-FINP-O<=))
     (18 18
         (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-3))
     (18 2 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
     (14 14
         (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (14 14 (:REWRITE |(+ x (- x))|))
     (12 12
         (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-2))
     (12 12
         (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-0))
     (9 9 (:REWRITE |(< x (+ c/d y))|))
     (7 7 (:REWRITE |a < b & b < c  =>  a < c|))
     (7 7 (:REWRITE |(< y (+ (- c) x))|))
     (6 6
        (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-1))
     (2 2 (:REWRITE |(< 0 (* x y))|)))
(RP::SUM-COMM-ORDER)
(RP::SUM-COMM-1)
(RP::SUM-COMM-1-LOOP-STOPPER)
(RP::SUM-COMM-2 (47 47 (:REWRITE DEFAULT-PLUS-2))
                (47 47 (:REWRITE DEFAULT-PLUS-1))
                (9 9 (:REWRITE REDUCE-INTEGERP-+))
                (9 9
                   (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                (9 9 (:REWRITE NORMALIZE-ADDENDS))
                (9 9 (:REWRITE INTEGERP-MINUS-X))
                (9 9
                   (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                (9 9 (:META META-INTEGERP-CORRECT))
                (2 2 (:REWRITE FOLD-CONSTS-IN-+))
                (2 2 (:REWRITE |(+ c (+ d x))|)))
(RP::SUM-COMM-2-LOOP-STOPPER
     (47 47 (:REWRITE DEFAULT-PLUS-2))
     (47 47 (:REWRITE DEFAULT-PLUS-1))
     (9 9 (:REWRITE REDUCE-INTEGERP-+))
     (9 9
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (9 9 (:REWRITE NORMALIZE-ADDENDS))
     (9 9 (:REWRITE INTEGERP-MINUS-X))
     (9 9
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (9 9 (:META META-INTEGERP-CORRECT))
     (2 2 (:REWRITE FOLD-CONSTS-IN-+))
     (2 2 (:REWRITE |(+ c (+ d x))|)))
(RP::SUM-ASSOC (50 50 (:REWRITE DEFAULT-PLUS-2))
               (50 50 (:REWRITE DEFAULT-PLUS-1))
               (10 10
                   (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
               (10 10 (:REWRITE NORMALIZE-ADDENDS))
               (9 9 (:REWRITE REDUCE-INTEGERP-+))
               (9 9 (:REWRITE INTEGERP-MINUS-X))
               (9 9
                  (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
               (9 9 (:META META-INTEGERP-CORRECT))
               (2 2 (:REWRITE FOLD-CONSTS-IN-+))
               (2 2 (:REWRITE |(+ c (+ d x))|)))
(RP::SUM-OF-0)
(RP::SUM-OF-IFIX)
(RP::SUM-LIST-OF-APPEND
     (80 40 (:REWRITE DEFAULT-PLUS-2))
     (80 40 (:REWRITE DEFAULT-PLUS-1))
     (57 19 (:REWRITE DEFAULT-CDR))
     (36 18
         (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
     (30 27 (:REWRITE DEFAULT-CAR))
     (24 24
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (24 24 (:REWRITE NORMALIZE-ADDENDS))
     (18 18 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (18 18 (:TYPE-PRESCRIPTION BINARY-APPEND))
     (18 18 (:REWRITE REDUCE-INTEGERP-+))
     (18 18 (:REWRITE INTEGERP-MINUS-X))
     (18 18
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (18 18 (:META META-INTEGERP-CORRECT))
     (16 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (16 4
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (16 4
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (15 5 (:REWRITE CAR-OF-APPEND))
     (10 10 (:REWRITE CONSP-OF-APPEND))
     (5 5 (:REWRITE CDR-OF-APPEND-WHEN-CONSP))
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
     (4 4 (:REWRITE |(equal (+ (- c) x) y)|)))
(RP::SUM-LIST-OF-TRUE-LIST-FIX
     (16 12 (:REWRITE DEFAULT-CDR))
     (10 9 (:REWRITE DEFAULT-CAR))
     (6 3 (:REWRITE DEFAULT-PLUS-2))
     (3 3
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (3 3 (:REWRITE NORMALIZE-ADDENDS))
     (3 3 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (3 3 (:REWRITE DEFAULT-PLUS-1))
     (3 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (3 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (3 1
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (2 2 (:REWRITE CONSP-OF-LIST-FIX))
     (2 1 (:REWRITE CAR-OF-LIST-FIX))
     (1 1
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (1 1
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (1 1 (:REWRITE LIST-FIX-WHEN-NOT-CONSP))
     (1 1
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (1 1 (:REWRITE |(equal c (/ x))|))
     (1 1 (:REWRITE |(equal c (- x))|))
     (1 1 (:REWRITE |(equal (/ x) c)|))
     (1 1 (:REWRITE |(equal (/ x) (/ y))|))
     (1 1 (:REWRITE |(equal (- x) c)|))
     (1 1 (:REWRITE |(equal (- x) (- y))|)))
(RP::AND-LIST-IS-AND$
     (11208 10 (:REWRITE RP::BIT-FIX-OPENER))
     (11188 10 (:DEFINITION BITP))
     (10644 8 (:DEFINITION APPLY$-BADGEP))
     (9176 32
           (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (4948 20 (:DEFINITION SUBSETP-EQUAL))
     (4560 136 (:DEFINITION MEMBER-EQUAL))
     (3916 16
           (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (3560 8 (:DEFINITION TRUE-LISTP))
     (3526 306 (:REWRITE ACL2-NUMBERP-X))
     (3355 314
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (3048 20
           (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (3016 12 (:DEFINITION RP::RP-TERMP))
     (2500 144 (:REWRITE RATIONALP-X))
     (2316 48 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
     (2292 4 (:DEFINITION RP::FALIST-CONSISTENT))
     (2184 92
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (2004 4
           (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (1664 90
           (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (1166 1166 (:REWRITE DEFAULT-CDR))
     (1047 314
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (664 8 (:DEFINITION RP::RP-TERM-LISTP))
     (600 16 (:DEFINITION NATP))
     (554 554 (:REWRITE DEFAULT-CAR))
     (528 20
          (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (460 20 (:DEFINITION QUOTEP))
     (370 314 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (314 314
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (314 314
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (314 314
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (314 314 (:REWRITE |(equal c (/ x))|))
     (314 314 (:REWRITE |(equal c (- x))|))
     (314 314 (:REWRITE |(equal (/ x) c)|))
     (314 314 (:REWRITE |(equal (/ x) (/ y))|))
     (314 314 (:REWRITE |(equal (- x) c)|))
     (314 314 (:REWRITE |(equal (- x) (- y))|))
     (306 306
          (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (292 292 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (280 8 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (276 276
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (250 250 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (236 236 (:REWRITE SUBSETP-IMPLIES-MEMBER))
     (184 184
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (168 48 (:REWRITE O-P-O-INFP-CAR))
     (162 162 (:REWRITE REDUCE-INTEGERP-+))
     (162 162 (:REWRITE INTEGERP-MINUS-X))
     (162 162
          (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (162 162 (:META META-INTEGERP-CORRECT))
     (160 48 (:REWRITE RP::IS-IF-RP-TERMP))
     (152 76
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (144 144 (:REWRITE REDUCE-RATIONALP-+))
     (144 144 (:REWRITE REDUCE-RATIONALP-*))
     (144 144 (:REWRITE RATIONALP-MINUS-X))
     (144 144
          (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (144 144 (:META META-RATIONALP-CORRECT))
     (136 136 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (80 80 (:TYPE-PRESCRIPTION O-P))
     (80 80 (:TYPE-PRESCRIPTION LEN))
     (72 8 (:DEFINITION LEN))
     (64 32
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (64 16 (:REWRITE RP::RP-TERMP-CADDDR))
     (56 56
         (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
     (48 48
         (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
     (48 48
         (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (48 16 (:REWRITE RP::RP-TERMP-CADR))
     (48 16 (:REWRITE RP::RP-TERMP-CADDR))
     (48 16 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (48 8 (:DEFINITION ALL-NILS))
     (40 40 (:TYPE-PRESCRIPTION ALL-NILS))
     (40 40 (:REWRITE O-P-DEF-O-FINP-1))
     (40 20
         (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (36 36
         (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (32 32 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (32 32 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (28 28 (:LINEAR LEN-WHEN-PREFIXP))
     (24 24 (:REWRITE |(equal x (if a b c))|))
     (24 24 (:REWRITE |(equal (if a b c) x)|))
     (20 20 (:TYPE-PRESCRIPTION QUOTEP))
     (20 4
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (16 16
         (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
     (16 8 (:REWRITE DEFAULT-PLUS-2))
     (14 14 (:REWRITE THE-FLOOR-BELOW))
     (14 14 (:REWRITE THE-FLOOR-ABOVE))
     (14 14
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (14 14
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (14 14 (:REWRITE SIMPLIFY-SUMS-<))
     (14 14
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (14 14 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (14 14
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (14 14
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (14 14
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (14 14
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (14 14 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (14 14 (:REWRITE INTEGERP-<-CONSTANT))
     (14 14 (:REWRITE DEFAULT-LESS-THAN-2))
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
     (14 14 (:REWRITE |(< (/ x) 0)|))
     (14 14 (:REWRITE |(< (/ x) (/ y))|))
     (14 14 (:REWRITE |(< (- x) c)|))
     (14 14 (:REWRITE |(< (- x) (- y))|))
     (14 14 (:REWRITE |(< (* x y) 0)|))
     (14 14 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (14 14 (:LINEAR BOUNDS-POSITION-EQUAL))
     (10 10 (:TYPE-PRESCRIPTION BITP))
     (10 10
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (8 8 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (8 8
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (8 8 (:REWRITE NORMALIZE-ADDENDS))
     (8 8 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (8 8 (:REWRITE DEFAULT-PLUS-1))
     (4 4
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP)))
(RP::AND$-IS-AND-LIST
     (220 6 (:REWRITE RP::BIT-FIX-OPENER))
     (210 4 (:DEFINITION BITP))
     (93 13 (:REWRITE ACL2-NUMBERP-X))
     (75 14
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (64 14
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (40 8 (:REWRITE RATIONALP-X))
     (14 14 (:REWRITE SIMPLIFY-SUMS-EQUAL))
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
     (13 13
         (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (8 8 (:REWRITE REDUCE-RATIONALP-+))
     (8 8 (:REWRITE REDUCE-RATIONALP-*))
     (8 8 (:REWRITE REDUCE-INTEGERP-+))
     (8 8 (:REWRITE RATIONALP-MINUS-X))
     (8 8
        (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (8 8 (:REWRITE INTEGERP-MINUS-X))
     (8 8
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (8 8 (:META META-RATIONALP-CORRECT))
     (8 8 (:META META-INTEGERP-CORRECT))
     (4 4 (:TYPE-PRESCRIPTION BITP))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (3 3 (:REWRITE DEFAULT-CDR))
     (2 2 (:REWRITE DEFAULT-CAR)))
(RP::-OF-)
(RP::SUM-OF-SUBTRACTED (35 15 (:REWRITE DEFAULT-PLUS-2))
                       (32 15 (:REWRITE DEFAULT-PLUS-1))
                       (8 4 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
                       (8 4 (:REWRITE DEFAULT-MINUS))
                       (6 6 (:REWRITE REDUCE-INTEGERP-+))
                       (6 6 (:REWRITE INTEGERP-MINUS-X))
                       (6 6
                          (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                       (6 6 (:META META-INTEGERP-CORRECT))
                       (3 3
                          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                       (2 2 (:REWRITE |(+ c (+ d x))|)))
(RP::+-IS-SUM (2 2 (:REWRITE REDUCE-INTEGERP-+))
              (2 2
                 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
              (2 2 (:REWRITE NORMALIZE-ADDENDS))
              (2 2 (:REWRITE INTEGERP-MINUS-X))
              (2 2
                 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
              (2 2 (:REWRITE DEFAULT-PLUS-2))
              (2 2 (:REWRITE DEFAULT-PLUS-1))
              (2 2 (:META META-INTEGERP-CORRECT)))
(RP::MOD2-IS-M2 (220 44 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
                (220 44 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
                (212 44
                     (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
                (212 44
                     (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
                (211 211
                     (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                (211 211
                     (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                (211 211
                     (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                (100 8 (:REWRITE DEFAULT-MOD-RATIO))
                (79 3 (:LINEAR MOD-BOUNDS-3))
                (50 11 (:REWRITE |(* y x)|))
                (44 44 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
                (44 44
                    (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
                (44 44 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
                (44 44
                    (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
                (44 44 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
                (40 30 (:REWRITE DEFAULT-TIMES-2))
                (39 39 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                (39 39 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                (39 39 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                (36 30 (:REWRITE DEFAULT-TIMES-1))
                (34 6 (:LINEAR MOD-BOUNDS-2))
                (19 19
                    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                (12 12 (:REWRITE REDUCE-INTEGERP-+))
                (12 12 (:REWRITE INTEGERP-MINUS-X))
                (12 12
                    (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                (12 12 (:META META-INTEGERP-CORRECT))
                (12 8 (:REWRITE DEFAULT-MOD-1))
                (8 8 (:REWRITE DEFAULT-MOD-2))
                (8 8 (:REWRITE |(mod x 2)| . 2))
                (2 2 (:TYPE-PRESCRIPTION RATIONALP-MOD)))
(RP::FLOOR2-IF-F2 (965 965
                       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                  (965 965
                       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                  (965 965
                       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                  (361 41 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
                  (361 41
                       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
                  (361 41
                       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
                  (361 41
                       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
                  (361 41
                       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
                  (205 41 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
                  (205 41 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
                  (205 41
                       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
                  (205 41
                       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
                  (205 41
                       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
                  (205 41
                       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
                  (205 41
                       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
                  (205 41
                       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
                  (205 41
                       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
                  (205 41
                       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
                  (78 6 (:REWRITE DEFAULT-FLOOR-RATIO))
                  (70 46 (:REWRITE DEFAULT-TIMES-2))
                  (66 2 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
                  (58 46 (:REWRITE DEFAULT-TIMES-1))
                  (56 2 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
                  (42 42 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                  (42 42 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                  (42 42 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                  (32 32
                      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                  (20 10 (:REWRITE DEFAULT-PLUS-2))
                  (20 10 (:REWRITE DEFAULT-PLUS-1))
                  (11 11 (:REWRITE REDUCE-INTEGERP-+))
                  (11 11 (:REWRITE INTEGERP-MINUS-X))
                  (11 11
                      (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                  (11 11 (:META META-INTEGERP-CORRECT))
                  (10 6 (:REWRITE DEFAULT-FLOOR-1))
                  (8 8
                     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                  (8 8 (:REWRITE NORMALIZE-ADDENDS))
                  (6 6 (:REWRITE DEFAULT-FLOOR-2))
                  (6 6 (:REWRITE |(floor x 2)| . 2)))
(RP::C-IS-F2
     (828 828
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (828 828
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (828 828
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (306 34 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (306 34
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (306 34
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (306 34
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (306 34
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (220 6 (:REWRITE DEFAULT-FLOOR-RATIO))
     (196 44 (:REWRITE DEFAULT-PLUS-2))
     (170 34 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (170 34 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (170 34
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (170 34
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (170 34
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (170 34
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (170 34
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (170 34
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (170 34
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (170 34
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (166 78 (:REWRITE DEFAULT-TIMES-2))
     (152 44 (:REWRITE DEFAULT-PLUS-1))
     (118 118
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (118 118
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (118 118
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (105 27 (:REWRITE REDUCE-INTEGERP-+))
     (105 27 (:META META-INTEGERP-CORRECT))
     (96 78 (:REWRITE DEFAULT-TIMES-1))
     (96 4 (:DEFINITION RP::SUM-LIST))
     (84 8 (:REWRITE RP::SUM-COMM-1))
     (66 2 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
     (64 64
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (56 2 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (50 2 (:REWRITE |(floor (+ x r) i)|))
     (34 34
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (34 34 (:REWRITE NORMALIZE-ADDENDS))
     (27 27 (:REWRITE INTEGERP-MINUS-X))
     (27 27
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (16 6 (:REWRITE DEFAULT-FLOOR-1))
     (12 12 (:REWRITE FOLD-CONSTS-IN-+))
     (12 12 (:REWRITE |(+ c (+ d x))|))
     (6 6 (:REWRITE DEFAULT-FLOOR-2))
     (6 6 (:REWRITE |(floor x 2)| . 2))
     (4 4 (:REWRITE DEFAULT-CDR))
     (4 4 (:REWRITE DEFAULT-CAR))
     (3 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (3 1 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (3 1 (:REWRITE DEFAULT-LESS-THAN-1))
     (2 2 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (1 1 (:REWRITE THE-FLOOR-BELOW))
     (1 1 (:REWRITE THE-FLOOR-ABOVE))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (1 1 (:REWRITE SIMPLIFY-SUMS-<))
     (1 1 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (1 1 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (1 1
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (1 1
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (1 1 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
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
     (1 1 (:REWRITE |(< (/ x) 0)|))
     (1 1 (:REWRITE |(< (/ x) (/ y))|))
     (1 1 (:REWRITE |(< (- x) c)|))
     (1 1 (:REWRITE |(< (- x) (- y))|))
     (1 1 (:REWRITE |(< (+ c/d x) y)|))
     (1 1 (:REWRITE |(< (+ (- c) x) y)|))
     (1 1 (:REWRITE |(< (* x y) 0)|)))
(RP::D-SUM-TO-SUM)
(RP::D-IS-D2 (494 494
                  (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
             (494 494
                  (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
             (494 494
                  (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
             (180 20 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
             (180 20
                  (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
             (180 20
                  (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
             (180 20
                  (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
             (180 20
                  (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
             (100 20 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
             (100 20 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
             (100 20
                  (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
             (100 20
                  (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
             (100 20
                  (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
             (100 20
                  (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
             (100 20
                  (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
             (100 20
                  (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
             (100 20
                  (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
             (100 20
                  (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
             (66 2 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
             (56 2 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
             (24 16 (:REWRITE DEFAULT-TIMES-2))
             (24 16 (:REWRITE DEFAULT-TIMES-1))
             (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
             (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
             (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
             (14 4 (:REWRITE DEFAULT-PLUS-2))
             (14 4 (:REWRITE DEFAULT-PLUS-1))
             (8 8
                (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
             (5 5 (:REWRITE REDUCE-INTEGERP-+))
             (5 5 (:REWRITE INTEGERP-MINUS-X))
             (5 5
                (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
             (5 5 (:META META-INTEGERP-CORRECT))
             (4 2 (:REWRITE DEFAULT-MINUS))
             (2 2
                (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
             (2 2 (:REWRITE NORMALIZE-ADDENDS)))
(RP::S-IS-M2 (258 8 (:REWRITE DEFAULT-MOD-RATIO))
             (214 11 (:REWRITE |(* y x)|))
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
             (161 3 (:LINEAR MOD-BOUNDS-3))
             (126 64 (:REWRITE DEFAULT-TIMES-2))
             (123 123
                  (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
             (123 123
                  (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
             (123 123
                  (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
             (105 5 (:REWRITE SUM-IS-EVEN . 2))
             (100 22 (:REWRITE DEFAULT-PLUS-2))
             (100 22 (:REWRITE DEFAULT-PLUS-1))
             (80 64 (:REWRITE DEFAULT-TIMES-1))
             (53 53
                 (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
             (48 2 (:DEFINITION RP::SUM-LIST))
             (42 4 (:REWRITE RP::SUM-COMM-1))
             (38 6 (:LINEAR MOD-BOUNDS-2))
             (37 37 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
             (37 37
                 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
             (37 37 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
             (37 37
                 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
             (37 37 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
             (26 26 (:REWRITE REDUCE-INTEGERP-+))
             (26 26 (:REWRITE INTEGERP-MINUS-X))
             (26 26
                 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
             (26 26 (:META META-INTEGERP-CORRECT))
             (20 8 (:REWRITE DEFAULT-MOD-1))
             (13 13
                 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
             (13 13 (:REWRITE NORMALIZE-ADDENDS))
             (8 8 (:REWRITE DEFAULT-MOD-2))
             (8 8 (:REWRITE |(mod x 2)| . 2))
             (2 2 (:REWRITE DEFAULT-CDR))
             (2 2 (:REWRITE DEFAULT-CAR))
             (1 1
                (:REWRITE INTEGERP-+-REDUCE-CONSTANT)))
(RP::SUM-LIST-IS-SUM (43 5 (:REWRITE RP::SUM-COMM-1))
                     (14 7 (:REWRITE DEFAULT-PLUS-2))
                     (14 7 (:REWRITE DEFAULT-PLUS-1))
                     (14 2 (:REWRITE |(+ y x)|))
                     (5 5 (:REWRITE REDUCE-INTEGERP-+))
                     (5 5
                        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                     (5 5 (:REWRITE NORMALIZE-ADDENDS))
                     (5 5 (:REWRITE INTEGERP-MINUS-X))
                     (5 5
                        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                     (5 5 (:META META-INTEGERP-CORRECT))
                     (3 3 (:REWRITE DEFAULT-CDR))
                     (3 3 (:REWRITE DEFAULT-CAR)))
(RP::S-SPEC-IS-M2 (102 102
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
                  (56 2 (:LINEAR MOD-BOUNDS-3))
                  (24 4 (:LINEAR MOD-BOUNDS-2))
                  (20 20 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
                  (20 20
                      (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
                  (20 20 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
                  (20 20
                      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
                  (20 20 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
                  (10 2 (:REWRITE |(* y x)|))
                  (8 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
                  (6 4 (:REWRITE DEFAULT-TIMES-2))
                  (6 4 (:REWRITE DEFAULT-TIMES-1))
                  (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                  (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                  (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                  (2 2 (:REWRITE REDUCE-INTEGERP-+))
                  (2 2
                     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                  (2 2 (:REWRITE INTEGERP-MINUS-X))
                  (2 2
                     (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                  (2 2 (:META META-INTEGERP-CORRECT)))
(RP::C-SPEC-IS-F2 (482 482
                       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                  (482 482
                       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                  (482 482
                       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                  (180 20 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
                  (180 20
                       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
                  (180 20
                       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
                  (180 20
                       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
                  (180 20
                       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
                  (100 20 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
                  (100 20 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
                  (100 20
                       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
                  (100 20
                       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
                  (100 20
                       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
                  (100 20
                       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
                  (100 20
                       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
                  (100 20
                       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
                  (100 20
                       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
                  (100 20
                       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
                  (66 2 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
                  (56 2 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
                  (24 16 (:REWRITE DEFAULT-TIMES-2))
                  (24 16 (:REWRITE DEFAULT-TIMES-1))
                  (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                  (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                  (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                  (14 4 (:REWRITE DEFAULT-PLUS-2))
                  (14 4 (:REWRITE DEFAULT-PLUS-1))
                  (8 8
                     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                  (4 4 (:REWRITE REDUCE-INTEGERP-+))
                  (4 4 (:REWRITE INTEGERP-MINUS-X))
                  (4 4
                     (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                  (4 4 (:META META-INTEGERP-CORRECT))
                  (2 2
                     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                  (2 2 (:REWRITE NORMALIZE-ADDENDS)))
(RP::S-C-SPEC-IS-LIST-M2-F2)
(RP::C-S-SPEC-IS-LIST-M2-F2)
(RP::S-OF-C-TRIG-DEF (3 3 (:TYPE-PRESCRIPTION RP::S-OF-C-TRIG)))
(RP::S-OF-S-LEMMA1 (360 72 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
                   (360 72 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
                   (360 72
                        (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
                   (360 72
                        (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
                   (336 336
                        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                   (336 336
                        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                   (336 336
                        (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                   (127 127
                        (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                   (127 127
                        (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                   (127 127
                        (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                   (116 4 (:REWRITE DEFAULT-MOD-RATIO))
                   (72 72 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
                   (72 72
                       (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
                   (72 72 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
                   (72 72
                       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
                   (72 72 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
                   (68 4 (:REWRITE |(* y x)|))
                   (56 28 (:REWRITE DEFAULT-TIMES-2))
                   (52 2 (:REWRITE SUM-IS-EVEN . 2))
                   (34 28 (:REWRITE DEFAULT-TIMES-1))
                   (32 8 (:REWRITE DEFAULT-PLUS-2))
                   (32 8 (:REWRITE DEFAULT-PLUS-1))
                   (24 24
                       (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                   (15 15 (:REWRITE REDUCE-INTEGERP-+))
                   (15 15 (:REWRITE INTEGERP-MINUS-X))
                   (15 15
                       (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                   (15 15 (:META META-INTEGERP-CORRECT))
                   (10 4 (:REWRITE DEFAULT-MOD-1))
                   (6 6
                      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                   (6 6 (:REWRITE NORMALIZE-ADDENDS))
                   (4 4 (:REWRITE DEFAULT-MOD-2))
                   (4 4 (:REWRITE |(mod x 2)| . 2))
                   (1 1
                      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                   (1 1
                      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
                   (1 1 (:REWRITE |(equal c (/ x))|))
                   (1 1 (:REWRITE |(equal c (- x))|))
                   (1 1 (:REWRITE |(equal (/ x) c)|))
                   (1 1 (:REWRITE |(equal (/ x) (/ y))|))
                   (1 1 (:REWRITE |(equal (- x) c)|))
                   (1 1 (:REWRITE |(equal (- x) (- y))|)))
(RP::S-OF-S-LEMMA2 (270 54 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
                   (270 54 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
                   (270 54
                        (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
                   (270 54
                        (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
                   (252 252
                        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                   (252 252
                        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                   (252 252
                        (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                   (72 3 (:REWRITE DEFAULT-MOD-RATIO))
                   (54 54 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
                   (54 54
                       (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
                   (54 54 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
                   (54 54
                       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
                   (54 54 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
                   (49 49 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                   (49 49 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                   (49 49 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                   (39 3 (:REWRITE |(* y x)|))
                   (33 17 (:REWRITE DEFAULT-TIMES-2))
                   (26 1 (:REWRITE SUM-IS-EVEN . 2))
                   (21 17 (:REWRITE DEFAULT-TIMES-1))
                   (16 4 (:REWRITE DEFAULT-PLUS-2))
                   (16 4 (:REWRITE DEFAULT-PLUS-1))
                   (14 14
                       (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                   (9 9 (:REWRITE REDUCE-INTEGERP-+))
                   (9 9 (:REWRITE INTEGERP-MINUS-X))
                   (9 9
                      (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                   (9 9 (:META META-INTEGERP-CORRECT))
                   (7 3 (:REWRITE DEFAULT-MOD-1))
                   (3 3
                      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                   (3 3 (:REWRITE NORMALIZE-ADDENDS))
                   (3 3 (:REWRITE DEFAULT-MOD-2))
                   (3 3 (:REWRITE |(mod x 2)| . 2)))
(RP::F2-OF-TIMES2
     (137 51 (:REWRITE DEFAULT-TIMES-2))
     (118 46 (:REWRITE DEFAULT-PLUS-2))
     (95 3 (:REWRITE DEFAULT-FLOOR-RATIO))
     (94 46 (:REWRITE DEFAULT-PLUS-1))
     (88 1 (:REWRITE |(floor (+ x r) i)|))
     (75 2
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (57 3 (:REWRITE |(* y x)|))
     (56 51 (:REWRITE DEFAULT-TIMES-1))
     (54 54 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (54 54 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (54 54 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (29 29
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (18 1 (:REWRITE |(* (* x y) z)|))
     (17 17
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (14 7 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (13 13 (:REWRITE INTEGERP-MINUS-X))
     (12 12
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (12 12 (:META META-INTEGERP-CORRECT))
     (12 4
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (12 4
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (7 3 (:REWRITE DEFAULT-FLOOR-1))
     (6 6 (:REWRITE |(+ c (+ d x))|))
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
     (4 2 (:REWRITE DEFAULT-LESS-THAN-1))
     (3 3 (:REWRITE DEFAULT-FLOOR-2))
     (3 3 (:REWRITE |(floor x 2)| . 2))
     (3 3 (:REWRITE |(equal (+ (- c) x) y)|))
     (2 2 (:REWRITE THE-FLOOR-BELOW))
     (2 2 (:REWRITE THE-FLOOR-ABOVE))
     (2 2 (:REWRITE DEFAULT-LESS-THAN-2))
     (2 2 (:REWRITE |(< (* x y) 0)|))
     (2 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (2 1 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (1 1 (:TYPE-PRESCRIPTION ABS))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (1 1 (:REWRITE SIMPLIFY-SUMS-<))
     (1 1 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (1 1 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (1 1
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (1 1 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (1 1 (:REWRITE INTEGERP-<-CONSTANT))
     (1 1 (:REWRITE FOLD-CONSTS-IN-+))
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
(RP::F2-OF-MINUS-LEMMA1 (27 12 (:REWRITE DEFAULT-PLUS-2))
                        (27 12 (:REWRITE DEFAULT-PLUS-1))
                        (10 5 (:REWRITE DEFAULT-MINUS))
                        (8 4 (:REWRITE DEFAULT-TIMES-2))
                        (6 3 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
                        (4 4
                           (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                        (4 4 (:REWRITE DEFAULT-TIMES-1))
                        (2 2 (:REWRITE REDUCE-INTEGERP-+))
                        (2 2
                           (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                        (2 2 (:REWRITE INTEGERP-MINUS-X))
                        (2 2
                           (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                        (2 2 (:REWRITE |(* (- x) y)|))
                        (2 2 (:META META-INTEGERP-CORRECT))
                        (1 1 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
                        (1 1 (:REWRITE |(+ c (+ d x))|)))
(RP::F2-OF-MINUS)
(RP::M2-OF-TIMES2 (248 248
                       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                  (248 248
                       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                  (248 248
                       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                  (240 48 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
                  (240 48 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
                  (240 48
                       (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
                  (240 48
                       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
                  (207 11 (:REWRITE DEFAULT-MOD-RATIO))
                  (117 15 (:REWRITE |(* y x)|))
                  (112 55 (:REWRITE DEFAULT-TIMES-2))
                  (112 4 (:LINEAR MOD-BOUNDS-3))
                  (72 55 (:REWRITE DEFAULT-TIMES-1))
                  (66 66 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                  (66 66 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                  (66 66 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                  (61 15 (:REWRITE DEFAULT-PLUS-2))
                  (48 48 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
                  (48 48
                      (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
                  (48 48 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
                  (48 48
                      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
                  (48 48 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
                  (48 8 (:LINEAR MOD-BOUNDS-2))
                  (40 15 (:REWRITE DEFAULT-PLUS-1))
                  (32 32
                      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                  (23 11 (:REWRITE DEFAULT-MOD-1))
                  (18 18 (:REWRITE INTEGERP-MINUS-X))
                  (18 1 (:REWRITE |(* (* x y) z)|))
                  (17 17
                      (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                  (17 17 (:META META-INTEGERP-CORRECT))
                  (11 11 (:REWRITE DEFAULT-MOD-2))
                  (11 11 (:REWRITE |(mod x 2)| . 2))
                  (6 3 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
                  (4 4
                     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                  (1 1 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
                  (1 1 (:REWRITE |(+ c (+ d x))|)))
(RP::S-OF-MINUS-LEMMA (27 12 (:REWRITE DEFAULT-PLUS-2))
                      (27 12 (:REWRITE DEFAULT-PLUS-1))
                      (10 5 (:REWRITE DEFAULT-MINUS))
                      (8 4 (:REWRITE DEFAULT-TIMES-2))
                      (6 3 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
                      (4 4
                         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                      (4 4 (:REWRITE DEFAULT-TIMES-1))
                      (2 2 (:REWRITE REDUCE-INTEGERP-+))
                      (2 2
                         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                      (2 2 (:REWRITE INTEGERP-MINUS-X))
                      (2 2
                         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                      (2 2 (:REWRITE |(* (- x) y)|))
                      (2 2 (:META META-INTEGERP-CORRECT))
                      (1 1 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
                      (1 1 (:REWRITE |(+ c (+ d x))|)))
(RP::S-OF-MINUS)
(RP::D2-OF-TIMES2 (2 2 (:REWRITE REDUCE-INTEGERP-+))
                  (2 2 (:REWRITE INTEGERP-MINUS-X))
                  (2 2
                     (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                  (2 2 (:META META-INTEGERP-CORRECT)))
(RP::D2-OF-MINUS-LEMMA1 (27 12 (:REWRITE DEFAULT-PLUS-2))
                        (27 12 (:REWRITE DEFAULT-PLUS-1))
                        (10 5 (:REWRITE DEFAULT-MINUS))
                        (8 4 (:REWRITE DEFAULT-TIMES-2))
                        (6 3 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
                        (4 4
                           (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                        (4 4 (:REWRITE DEFAULT-TIMES-1))
                        (2 2 (:REWRITE REDUCE-INTEGERP-+))
                        (2 2
                           (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                        (2 2 (:REWRITE INTEGERP-MINUS-X))
                        (2 2
                           (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                        (2 2 (:REWRITE |(* (- x) y)|))
                        (2 2 (:META META-INTEGERP-CORRECT))
                        (1 1 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
                        (1 1 (:REWRITE |(+ c (+ d x))|)))
(RP::D2-OF-MINUS)
(RP::M2-OF--- (3 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
              (3 1
                 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
              (3 1
                 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
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
(RP::M2-OF-IFIX)
(RP::F2-OF-IFIX)
(RP::IFIX-OF-F2 (398 398
                     (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                (398 398
                     (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                (398 398
                     (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                (126 14 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
                (126 14
                     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
                (126 14
                     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
                (126 14
                     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
                (126 14
                     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
                (70 14 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
                (70 14 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
                (70 14
                    (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
                (70 14
                    (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
                (70 14
                    (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
                (70 14
                    (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
                (70 14
                    (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
                (70 14
                    (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
                (70 14
                    (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
                (70 14
                    (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
                (50 4 (:REWRITE DEFAULT-FLOOR-RATIO))
                (44 44 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
                (44 44 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                (44 44 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                (44 44 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                (23 23 (:REWRITE DEFAULT-TIMES-2))
                (23 23 (:REWRITE DEFAULT-TIMES-1))
                (16 16
                    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                (16 4 (:REWRITE |(* y x)|))
                (14 2 (:REWRITE |(* (if a b c) x)|))
                (11 11 (:REWRITE REDUCE-INTEGERP-+))
                (11 11 (:REWRITE INTEGERP-MINUS-X))
                (11 11
                    (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                (11 11 (:META META-INTEGERP-CORRECT))
                (6 3
                   (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                (6 3
                   (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                (5 5
                   (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                (5 5 (:REWRITE NORMALIZE-ADDENDS))
                (5 5 (:REWRITE DEFAULT-PLUS-2))
                (5 5 (:REWRITE DEFAULT-PLUS-1))
                (5 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                (4 4 (:REWRITE DEFAULT-FLOOR-2))
                (4 4 (:REWRITE DEFAULT-FLOOR-1))
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
                (2 2 (:REWRITE |(floor x 2)| . 2))
                (2 1 (:REWRITE O-INFP->NEQ-0))
                (1 1
                   (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
                (1 1 (:REWRITE |(equal (+ (- c) x) y)|)))
(RP::IFIX-OF-M2)
(RP::SUM-OF-EQUALS (177 66 (:REWRITE DEFAULT-PLUS-2))
                   (132 66 (:REWRITE DEFAULT-PLUS-1))
                   (53 12
                       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                   (49 12
                       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                   (25 25
                       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                   (16 8 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
                   (15 15 (:REWRITE REDUCE-INTEGERP-+))
                   (15 15 (:REWRITE INTEGERP-MINUS-X))
                   (15 15
                       (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                   (15 15 (:META META-INTEGERP-CORRECT))
                   (14 14 (:REWRITE |(+ c (+ d x))|))
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
                   (8 8 (:REWRITE |(equal (+ (- c) x) y)|))
                   (6 6 (:REWRITE FOLD-CONSTS-IN-+)))
(RP::INTEGERP-F2)
(RP::DUMMY-SUM-CANCEL-LEMMA1
     (31 14 (:REWRITE DEFAULT-PLUS-2))
     (29 14 (:REWRITE DEFAULT-PLUS-1))
     (8 2
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (8 2
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (5 5 (:REWRITE REDUCE-INTEGERP-+))
     (5 5 (:REWRITE INTEGERP-MINUS-X))
     (5 5
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (5 5 (:META META-INTEGERP-CORRECT))
     (4 4
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (4 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (3 1 (:REWRITE O-INFP->NEQ-0))
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
     (2 2 (:REWRITE |(equal (+ (- c) x) y)|))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (1 1 (:REWRITE FOLD-CONSTS-IN-+))
     (1 1 (:REWRITE |(+ c (+ d x))|)))
(RP::F2-OF-BIT (26 2
                   (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
               (24 4 (:REWRITE ACL2-NUMBERP-X))
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
(RP::M2-OF-M2 (398 398
                   (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
              (398 398
                   (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
              (398 398
                   (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
              (376 20 (:REWRITE DEFAULT-MOD-RATIO))
              (370 74 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
              (370 74 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
              (370 74
                   (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
              (370 74
                   (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
              (182 26 (:REWRITE |(* y x)|))
              (168 6 (:LINEAR MOD-BOUNDS-3))
              (146 84 (:REWRITE DEFAULT-TIMES-2))
              (137 137
                   (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
              (137 137
                   (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
              (137 137
                   (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
              (123 84 (:REWRITE DEFAULT-TIMES-1))
              (74 74 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
              (74 74
                  (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
              (74 74 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
              (74 74
                  (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
              (74 74 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
              (72 12 (:LINEAR MOD-BOUNDS-2))
              (55 55
                  (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
              (51 20 (:REWRITE DEFAULT-MOD-1))
              (42 2 (:REWRITE |(* (if a b c) x)|))
              (38 9 (:REWRITE DEFAULT-PLUS-2))
              (30 30 (:REWRITE REDUCE-INTEGERP-+))
              (30 30 (:REWRITE INTEGERP-MINUS-X))
              (30 30
                  (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
              (30 30 (:META META-INTEGERP-CORRECT))
              (26 1 (:REWRITE SUM-IS-EVEN . 2))
              (25 9 (:REWRITE DEFAULT-PLUS-1))
              (20 20 (:REWRITE DEFAULT-MOD-2))
              (18 18 (:REWRITE |(mod x 2)| . 2))
              (7 7
                 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
              (7 7 (:REWRITE NORMALIZE-ADDENDS)))
(RP::M2-OF-M2-EXTENDED)
(RP::SUM-OF-REPEATED-TO-TIMES2)
(RP::D2-TO-F2
     (1728 1728
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (1728 1728
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (1728 1728
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (1000 172 (:REWRITE DEFAULT-PLUS-2))
     (908 46
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (800 800
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (800 800
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (800 800
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (794 8 (:REWRITE |(equal x (/ y))|))
     (672 8 (:REWRITE |(not (equal x (/ y)))|))
     (630 4
          (:REWRITE |(not (equal x (- (/ y))))|))
     (618 230 (:REWRITE DEFAULT-TIMES-2))
     (612 68 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (612 68
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (612 68
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (612 68
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (612 68
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (504 172 (:REWRITE DEFAULT-PLUS-1))
     (478 4 (:REWRITE |(equal x (- (/ y)))|))
     (350 230 (:REWRITE DEFAULT-TIMES-1))
     (340 68 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (340 68 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (340 68
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (340 68
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (340 68
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (340 68
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (340 68
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (340 68
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (340 68
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (340 68
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (304 12 (:REWRITE DEFAULT-FLOOR-RATIO))
     (214 34
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (214 34
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (208 38 (:REWRITE |(equal (- x) c)|))
     (166 46 (:REWRITE |(+ c (+ d x))|))
     (146 146
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (144 6 (:REWRITE DEFAULT-MOD-RATIO))
     (132 4 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
     (130 52 (:REWRITE REDUCE-INTEGERP-+))
     (130 52 (:META META-INTEGERP-CORRECT))
     (112 4 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (98 2 (:REWRITE |(floor (+ x r) i)|))
     (80 80
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (72 8 (:REWRITE O-INFP->NEQ-0))
     (64 8 (:REWRITE |(* c (* d x))|))
     (52 52 (:REWRITE INTEGERP-MINUS-X))
     (52 52
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (52 2 (:REWRITE SUM-IS-EVEN . 2))
     (48 46
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (46 38 (:REWRITE |(equal (- x) (- y))|))
     (44 4 (:REWRITE |(- (+ x y))|))
     (38 38 (:REWRITE |(equal c (/ x))|))
     (38 38 (:REWRITE |(equal c (- x))|))
     (38 38 (:REWRITE |(equal (/ x) c)|))
     (38 38 (:REWRITE |(equal (/ x) (/ y))|))
     (38 38 (:REWRITE |(equal (+ (- c) x) y)|))
     (34 34
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (30 30 (:REWRITE FOLD-CONSTS-IN-+))
     (28 12 (:REWRITE DEFAULT-MINUS))
     (28 12 (:REWRITE DEFAULT-FLOOR-1))
     (24 8 (:REWRITE |(* -1 x)|))
     (22 22 (:REWRITE |(* (- x) y)|))
     (16 16 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (16 8 (:REWRITE RP::-OF-))
     (14 6 (:REWRITE DEFAULT-MOD-1))
     (12 12 (:REWRITE DEFAULT-FLOOR-2))
     (12 12 (:REWRITE |(floor x 2)| . 2))
     (6 6 (:REWRITE DEFAULT-MOD-2))
     (6 6 (:REWRITE |(mod x 2)| . 2))
     (6 2
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (6 2 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (6 2 (:REWRITE DEFAULT-LESS-THAN-1))
     (4 4 (:REWRITE |(* x (- y))|))
     (2 2 (:TYPE-PRESCRIPTION ABS))
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
     (2 2 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (2 2 (:REWRITE INTEGERP-<-CONSTANT))
     (2 2 (:REWRITE DEFAULT-LESS-THAN-2))
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
     (2 2 (:REWRITE |(< (+ c/d x) y)|))
     (2 2 (:REWRITE |(< (+ (- c) x) y)|))
     (2 2 (:REWRITE |(< (* x y) 0)|)))
(RP::F2-TO-D2)
(RP::EQUAL-SUM-OF-NEGATED
     (171 65 (:REWRITE DEFAULT-PLUS-2))
     (130 65 (:REWRITE DEFAULT-PLUS-1))
     (69 12
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (46 8 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (35 35
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (19 19 (:REWRITE REDUCE-INTEGERP-+))
     (19 19 (:REWRITE INTEGERP-MINUS-X))
     (19 19
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (19 19 (:META META-INTEGERP-CORRECT))
     (17 17 (:REWRITE |(+ c (+ d x))|))
     (13 13 (:REWRITE FOLD-CONSTS-IN-+))
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
     (8 4 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (8 4 (:REWRITE DEFAULT-MINUS)))
(RP::EVENPI-OF-TIMES2 (207 39 (:REWRITE DEFAULT-PLUS-2))
                      (106 39 (:REWRITE DEFAULT-PLUS-1))
                      (100 43 (:REWRITE DEFAULT-TIMES-2))
                      (95 95 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                      (95 95 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                      (95 95 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                      (71 71 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                      (71 71 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                      (71 71 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                      (56 43 (:REWRITE DEFAULT-TIMES-1))
                      (28 28
                          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                      (27 2 (:REWRITE SUM-IS-EVEN . 2))
                      (22 22 (:REWRITE INTEGERP-MINUS-X))
                      (19 19
                          (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                      (19 19 (:META META-INTEGERP-CORRECT))
                      (14 14
                          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                      (14 7 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
                      (6 6 (:REWRITE |(+ c (+ d x))|))
                      (3 3 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
                      (3 3 (:REWRITE FOLD-CONSTS-IN-+)))
(RP::SUM-WITH-ODDP (51 51 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                   (51 51 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                   (51 51 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                   (20 1 (:REWRITE SUM-IS-EVEN . 2))
                   (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
                   (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                   (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                   (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                   (12 12 (:REWRITE DEFAULT-TIMES-2))
                   (12 12 (:REWRITE DEFAULT-TIMES-1))
                   (9 9
                      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                   (7 3 (:REWRITE DEFAULT-PLUS-1))
                   (6 6 (:REWRITE REDUCE-INTEGERP-+))
                   (6 6 (:REWRITE INTEGERP-MINUS-X))
                   (6 6
                      (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                   (6 6 (:META META-INTEGERP-CORRECT))
                   (3 3 (:REWRITE DEFAULT-PLUS-2))
                   (2 2
                      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                   (2 2 (:REWRITE NORMALIZE-ADDENDS)))
(RP::SUM-WITH-EVENP (51 51 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                    (51 51 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                    (51 51 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                    (20 1 (:REWRITE SUM-IS-EVEN . 2))
                    (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
                    (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                    (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                    (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                    (12 12 (:REWRITE DEFAULT-TIMES-2))
                    (12 12 (:REWRITE DEFAULT-TIMES-1))
                    (9 9
                       (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                    (7 7 (:REWRITE REDUCE-INTEGERP-+))
                    (7 7 (:REWRITE INTEGERP-MINUS-X))
                    (7 7
                       (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                    (7 7 (:META META-INTEGERP-CORRECT))
                    (7 3 (:REWRITE DEFAULT-PLUS-1))
                    (3 3 (:REWRITE DEFAULT-PLUS-2))
                    (2 2
                       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                    (2 2 (:REWRITE NORMALIZE-ADDENDS)))
(RP::EVENPI-LEMMA-1-LEMMA
     (152 152
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (152 152
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (152 152
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (110 22 (:REWRITE RP::IFIX-OPENER))
     (82 44 (:REWRITE DEFAULT-TIMES-2))
     (70 70 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (70 70 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (70 70 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (66 44 (:REWRITE DEFAULT-TIMES-1))
     (31 31 (:REWRITE REDUCE-INTEGERP-+))
     (31 31 (:REWRITE INTEGERP-MINUS-X))
     (31 31
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (31 31 (:META META-INTEGERP-CORRECT))
     (30 30
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (24 16 (:REWRITE DEFAULT-PLUS-2))
     (24 16 (:REWRITE DEFAULT-PLUS-1))
     (16 16
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (16 16 (:REWRITE NORMALIZE-ADDENDS))
     (3 3
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (3 3
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (3 3 (:REWRITE |(equal c (/ x))|))
     (3 3 (:REWRITE |(equal c (- x))|))
     (3 3 (:REWRITE |(equal (/ x) c)|))
     (3 3 (:REWRITE |(equal (/ x) (/ y))|))
     (3 3 (:REWRITE |(equal (- x) c)|))
     (3 3 (:REWRITE |(equal (- x) (- y))|)))
(RP::EVENPI-LEMMA-1 (30 30 (:REWRITE REDUCE-INTEGERP-+))
                    (30 30 (:REWRITE INTEGERP-MINUS-X))
                    (30 30
                        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                    (30 30 (:META META-INTEGERP-CORRECT))
                    (28 12 (:REWRITE DEFAULT-PLUS-2))
                    (24 12 (:REWRITE DEFAULT-PLUS-1))
                    (12 12
                        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                    (12 12 (:REWRITE NORMALIZE-ADDENDS))
                    (12 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                    (12 6
                        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                    (12 6
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
                    (4 4 (:REWRITE FOLD-CONSTS-IN-+))
                    (4 4 (:REWRITE |(+ c (+ d x))|)))
(RP::D2-IS-DIVIDE-BY-2 (541 541
                            (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                       (541 541
                            (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                       (541 541
                            (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                       (198 22 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
                       (198 22
                            (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
                       (198 22
                            (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
                       (198 22
                            (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
                       (198 22
                            (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
                       (110 22 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
                       (110 22 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
                       (110 22
                            (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
                       (110 22
                            (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
                       (110 22
                            (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
                       (110 22
                            (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
                       (110 22
                            (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
                       (110 22
                            (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
                       (110 22
                            (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
                       (110 22
                            (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
                       (78 47 (:REWRITE DEFAULT-TIMES-2))
                       (66 2 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
                       (65 5 (:REWRITE DEFAULT-FLOOR-RATIO))
                       (63 47 (:REWRITE DEFAULT-TIMES-1))
                       (56 2 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
                       (39 39 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                       (39 39 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                       (39 39 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                       (31 31
                           (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                       (21 10 (:REWRITE DEFAULT-PLUS-2))
                       (21 10 (:REWRITE DEFAULT-PLUS-1))
                       (11 11 (:REWRITE REDUCE-INTEGERP-+))
                       (11 11 (:REWRITE INTEGERP-MINUS-X))
                       (11 11
                           (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                       (11 11 (:META META-INTEGERP-CORRECT))
                       (10 5 (:REWRITE DEFAULT-FLOOR-1))
                       (9 1 (:REWRITE DEFAULT-MOD-RATIO))
                       (6 6
                          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                       (6 6 (:REWRITE NORMALIZE-ADDENDS))
                       (5 5 (:REWRITE DEFAULT-FLOOR-2))
                       (5 5 (:REWRITE |(floor x 2)| . 2))
                       (2 1 (:REWRITE DEFAULT-MOD-1))
                       (1 1 (:REWRITE DEFAULT-MOD-2))
                       (1 1 (:REWRITE |(mod x 2)| . 2)))
(RP::EVENPI-OF-SUM (39 39 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                   (39 39 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                   (39 39 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                   (14 8 (:REWRITE DEFAULT-TIMES-2))
                   (12 8 (:REWRITE DEFAULT-TIMES-1))
                   (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                   (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                   (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                   (6 6 (:REWRITE REDUCE-INTEGERP-+))
                   (6 6 (:REWRITE INTEGERP-MINUS-X))
                   (6 6
                      (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                   (6 6 (:META META-INTEGERP-CORRECT))
                   (5 5
                      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                   (3 2 (:REWRITE DEFAULT-PLUS-2))
                   (3 2 (:REWRITE DEFAULT-PLUS-1))
                   (2 2
                      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                   (2 2 (:REWRITE NORMALIZE-ADDENDS)))
(RP::SUM-OF-D2-LEMMA (29 29 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                     (29 29 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                     (29 29 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                     (24 24 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                     (24 24 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                     (24 24 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                     (17 9 (:REWRITE DEFAULT-TIMES-2))
                     (11 9 (:REWRITE DEFAULT-TIMES-1))
                     (7 7
                        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                     (6 6 (:REWRITE REDUCE-INTEGERP-+))
                     (6 6 (:REWRITE INTEGERP-MINUS-X))
                     (6 6
                        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                     (6 6 (:META META-INTEGERP-CORRECT))
                     (4 3 (:REWRITE DEFAULT-PLUS-2))
                     (4 3 (:REWRITE DEFAULT-PLUS-1))
                     (3 3
                        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                     (3 3 (:REWRITE NORMALIZE-ADDENDS)))
(RP::SUM-OF-D2 (96 3
                   (:REWRITE RP::DUMMY-SUM-CANCEL-LEMMA1))
               (84 12
                   (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
               (58 58 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
               (58 58 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
               (58 58 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
               (51 30 (:REWRITE DEFAULT-TIMES-2))
               (36 30 (:REWRITE DEFAULT-TIMES-1))
               (36 9
                   (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
               (36 9
                   (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
               (33 9 (:REWRITE SIMPLIFY-SUMS-EQUAL))
               (23 23 (:REWRITE RP::SUM-COMM-1))
               (21 21
                   (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
               (18 18 (:TYPE-PRESCRIPTION IFIX))
               (12 12 (:REWRITE REDUCE-INTEGERP-+))
               (12 12 (:REWRITE INTEGERP-MINUS-X))
               (12 12
                   (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
               (12 12 (:META META-INTEGERP-CORRECT))
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
               (6 3 (:REWRITE |(* a (/ a) b)|))
               (3 3 (:TYPE-PRESCRIPTION ABS))
               (3 3 (:REWRITE RP::SUM-COMM-2))
               (3 3
                  (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
               (3 3 (:REWRITE |(equal (* x y) 0)|)))
(RP::EVENPI-OF-TERM-MINUS-ITS-MOD
     (52 2 (:REWRITE SUM-IS-EVEN . 2))
     (46 46 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (46 46 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (46 46 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (42 22 (:REWRITE DEFAULT-TIMES-2))
     (30 30 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (30 30 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (30 30 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (28 22 (:REWRITE DEFAULT-TIMES-1))
     (28 2 (:REWRITE DEFAULT-MOD-RATIO))
     (18 18
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (18 5 (:REWRITE DEFAULT-PLUS-2))
     (18 5 (:REWRITE DEFAULT-PLUS-1))
     (12 12 (:REWRITE REDUCE-INTEGERP-+))
     (12 12 (:REWRITE INTEGERP-MINUS-X))
     (12 12
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (12 12 (:META META-INTEGERP-CORRECT))
     (4 4
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (4 4 (:REWRITE NORMALIZE-ADDENDS))
     (4 2 (:REWRITE DEFAULT-MOD-1))
     (2 2 (:REWRITE DEFAULT-MOD-2))
     (2 2 (:REWRITE |(mod x 2)| . 2)))
(RP::SUM-OF-F2S (215 15
                     (:REWRITE RP::DUMMY-SUM-CANCEL-LEMMA1))
                (16 9
                    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                (11 9
                    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                (9 9
                   (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
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
                (9 9 (:REWRITE |(equal (- x) (- y))|)))
(RP::SUM-OF-F2S-AND-D2
     (100 12
          (:REWRITE RP::DUMMY-SUM-CANCEL-LEMMA1))
     (8 4
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (5 4
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
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
     (4 4 (:REWRITE |(equal (- x) (- y))|)))
(RP::EVENPI-FOR-2-D2-ARGUMENTS
     (137 137
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (137 137
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (137 137
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (70 31 (:REWRITE REDUCE-INTEGERP-+))
     (70 31 (:META META-INTEGERP-CORRECT))
     (67 35 (:REWRITE DEFAULT-TIMES-2))
     (55 24 (:REWRITE DEFAULT-PLUS-2))
     (49 24 (:REWRITE DEFAULT-PLUS-1))
     (44 1 (:REWRITE DEFAULT-MOD-RATIO))
     (40 35 (:REWRITE DEFAULT-TIMES-1))
     (31 31 (:REWRITE INTEGERP-MINUS-X))
     (31 31
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (29 29
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (23 23 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (23 23 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (23 23 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (18 18
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (18 18 (:REWRITE NORMALIZE-ADDENDS))
     (6 6 (:REWRITE FOLD-CONSTS-IN-+))
     (6 6 (:REWRITE |(+ c (+ d x))|))
     (3 1 (:REWRITE DEFAULT-MOD-1))
     (1 1 (:REWRITE DEFAULT-MOD-2))
     (1 1 (:REWRITE |(mod x 2)| . 2)))
(RP::EVENPI-FOR-3-D2-ARGUMENTS
     (259 259
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (259 259
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (259 259
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (214 45 (:REWRITE REDUCE-INTEGERP-+))
     (214 45 (:META META-INTEGERP-CORRECT))
     (198 31 (:REWRITE DEFAULT-PLUS-2))
     (133 31 (:REWRITE DEFAULT-PLUS-1))
     (102 36 (:REWRITE DEFAULT-TIMES-2))
     (82 1 (:REWRITE DEFAULT-MOD-RATIO))
     (45 45 (:REWRITE INTEGERP-MINUS-X))
     (45 45
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (43 36 (:REWRITE DEFAULT-TIMES-1))
     (31 31
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (26 26
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (26 26 (:REWRITE NORMALIZE-ADDENDS))
     (23 23 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (23 23 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (23 23 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (15 15 (:REWRITE FOLD-CONSTS-IN-+))
     (15 15 (:REWRITE |(+ c (+ d x))|))
     (4 1 (:REWRITE DEFAULT-MOD-1))
     (1 1 (:REWRITE DEFAULT-MOD-2))
     (1 1 (:REWRITE |(mod x 2)| . 2)))
(RP::EVENPI-FOR-4-D2-ARGUMENTS
     (365 365
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (365 365
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (365 365
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (360 43 (:REWRITE DEFAULT-PLUS-2))
     (279 58 (:REWRITE REDUCE-INTEGERP-+))
     (279 58 (:META META-INTEGERP-CORRECT))
     (188 43 (:REWRITE DEFAULT-PLUS-1))
     (154 48 (:REWRITE DEFAULT-TIMES-2))
     (126 1 (:REWRITE DEFAULT-MOD-RATIO))
     (58 58 (:REWRITE INTEGERP-MINUS-X))
     (58 58
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (57 48 (:REWRITE DEFAULT-TIMES-1))
     (42 42
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (37 37
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (37 37 (:REWRITE NORMALIZE-ADDENDS))
     (26 26 (:REWRITE FOLD-CONSTS-IN-+))
     (26 26 (:REWRITE |(+ c (+ d x))|))
     (23 23 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (23 23 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (23 23 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (5 1 (:REWRITE DEFAULT-MOD-1))
     (1 1 (:REWRITE DEFAULT-MOD-2))
     (1 1 (:REWRITE |(mod x 2)| . 2)))
(RP::EVENPI-SUM-CLEAR (1045 146 (:REWRITE DEFAULT-PLUS-2))
                      (436 146 (:REWRITE DEFAULT-PLUS-1))
                      (380 380
                           (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                      (380 380
                           (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                      (380 380
                           (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                      (348 88 (:META META-INTEGERP-CORRECT))
                      (296 118 (:REWRITE DEFAULT-TIMES-2))
                      (231 231
                           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                      (231 231
                           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                      (231 231
                           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                      (159 118 (:REWRITE DEFAULT-TIMES-1))
                      (95 95 (:REWRITE INTEGERP-MINUS-X))
                      (88 88
                          (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                      (87 87
                          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                      (76 76
                          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                      (54 4 (:REWRITE SUM-IS-EVEN . 2))
                      (49 49 (:REWRITE |(+ c (+ d x))|))
                      (38 38 (:REWRITE FOLD-CONSTS-IN-+))
                      (30 15 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
                      (13 13
                          (:REWRITE INTEGERP-+-REDUCE-CONSTANT)))
(RP::M2-WITH-EXTRA (410 82 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
                   (410 82 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
                   (410 82
                        (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
                   (410 82
                        (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
                   (386 386
                        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                   (386 386
                        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                   (386 386
                        (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                   (220 10 (:REWRITE DEFAULT-MOD-RATIO))
                   (136 12 (:REWRITE |(* y x)|))
                   (124 64 (:REWRITE DEFAULT-TIMES-2))
                   (82 82 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
                   (82 82
                       (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
                   (82 82 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
                   (82 82
                       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
                   (82 82 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
                   (80 80 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                   (80 80 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                   (80 80 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                   (80 64 (:REWRITE DEFAULT-TIMES-1))
                   (64 16 (:REWRITE DEFAULT-PLUS-1))
                   (56 2 (:LINEAR MOD-BOUNDS-3))
                   (54 4 (:REWRITE SUM-IS-EVEN . 2))
                   (52 52
                       (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                   (25 25 (:REWRITE REDUCE-INTEGERP-+))
                   (25 25 (:REWRITE INTEGERP-MINUS-X))
                   (25 25
                       (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                   (25 25 (:META META-INTEGERP-CORRECT))
                   (24 16 (:REWRITE DEFAULT-PLUS-2))
                   (24 10 (:REWRITE DEFAULT-MOD-1))
                   (24 4 (:LINEAR MOD-BOUNDS-2))
                   (12 12
                       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                   (12 12 (:REWRITE NORMALIZE-ADDENDS))
                   (10 10 (:REWRITE DEFAULT-MOD-2))
                   (10 10 (:REWRITE |(mod x 2)| . 2)))
(RP::M2-WITH-EXTRA-DUMMY-LEMMA
     (313 15
          (:REWRITE RP::DUMMY-SUM-CANCEL-LEMMA1))
     (97 97 (:TYPE-PRESCRIPTION RP::BINARY-SUM))
     (31 17
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (26 17
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (23 17 (:REWRITE SIMPLIFY-SUMS-EQUAL))
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
     (14 14
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RP::EVENPI-WITH-OTHER (79 79 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                       (79 79 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                       (79 79 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                       (56 29 (:REWRITE DEFAULT-TIMES-2))
                       (39 29 (:REWRITE DEFAULT-TIMES-1))
                       (35 35 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                       (35 35 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                       (35 35 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                       (33 4 (:REWRITE SUM-IS-EVEN . 2))
                       (32 8 (:REWRITE DEFAULT-PLUS-2))
                       (23 23
                           (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                       (16 16 (:REWRITE REDUCE-INTEGERP-+))
                       (16 16 (:REWRITE INTEGERP-MINUS-X))
                       (16 16
                           (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                       (16 16 (:META META-INTEGERP-CORRECT))
                       (12 8 (:REWRITE DEFAULT-PLUS-1))
                       (8 8
                          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                       (8 8 (:REWRITE NORMALIZE-ADDENDS))
                       (1 1
                          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                       (1 1
                          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
                       (1 1 (:REWRITE |(equal c (/ x))|))
                       (1 1 (:REWRITE |(equal c (- x))|))
                       (1 1 (:REWRITE |(equal (/ x) c)|))
                       (1 1 (:REWRITE |(equal (/ x) (/ y))|))
                       (1 1 (:REWRITE |(equal (- x) c)|))
                       (1 1 (:REWRITE |(equal (- x) (- y))|)))
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
             (51 4 (:REWRITE DEFAULT-MOD-RATIO))
             (28 1 (:LINEAR MOD-BOUNDS-3))
             (25 5 (:REWRITE |(* y x)|))
             (24 24 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
             (24 24
                 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
             (24 24 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
             (24 24
                 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
             (24 24 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
             (23 14 (:REWRITE DEFAULT-TIMES-2))
             (19 19 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
             (19 19 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
             (19 19 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
             (19 14 (:REWRITE DEFAULT-TIMES-1))
             (12 2 (:LINEAR MOD-BOUNDS-2))
             (10 2 (:REWRITE RP::IFIX-OPENER))
             (9 9
                (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
             (8 4 (:REWRITE DEFAULT-MOD-1))
             (7 7 (:REWRITE REDUCE-INTEGERP-+))
             (7 7 (:REWRITE INTEGERP-MINUS-X))
             (7 7
                (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
             (7 7 (:META META-INTEGERP-CORRECT))
             (4 4 (:REWRITE DEFAULT-MOD-2))
             (4 4 (:REWRITE |(mod x 2)| . 2)))
