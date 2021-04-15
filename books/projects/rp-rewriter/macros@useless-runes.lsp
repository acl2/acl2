(RP::STRLIST-TO-STR (31 1 (:DEFINITION RP::STRLIST-TO-STR))
                    (28 1 (:DEFINITION STRING-APPEND))
                    (16 1 (:DEFINITION BINARY-APPEND))
                    (10 10
                        (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
                    (10 7 (:REWRITE DEFAULT-CDR))
                    (10 7 (:REWRITE DEFAULT-CAR))
                    (9 2 (:REWRITE APPEND-WHEN-NOT-CONSP))
                    (6 4 (:REWRITE STR::CONSP-OF-EXPLODE))
                    (5 2
                       (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
                    (3 2
                       (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
                    (1 1
                       (:REWRITE STR::COERCE-TO-STRING-REMOVAL)))
(RP::SYM-APP-FNC)
(RP::SA-LST)
(RP::GET-DIGIT-COUNT
     (11292 1 (:DEFINITION RP::GET-DIGIT-COUNT))
     (2964 8 (:LINEAR LINEAR-FLOOR-BOUNDS-1))
     (2619 2619
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (2619 2619
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (2619 2619
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (2337 13 (:REWRITE FLOOR-ZERO . 3))
     (2025 5 (:REWRITE ZP-OPEN))
     (1947 13 (:REWRITE FLOOR-ZERO . 4))
     (1878 13 (:REWRITE FLOOR-X-Y-=-1 . 2))
     (1870 41 (:REWRITE THE-FLOOR-BELOW))
     (1750 154 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (1601 13 (:REWRITE CANCEL-FLOOR-+))
     (1513 221
           (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (1329 34 (:REWRITE DEFAULT-PLUS-1))
     (1325 34 (:REWRITE DEFAULT-PLUS-2))
     (1218 154
           (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (1218 154
           (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (722 43 (:REWRITE INTEGERP-MINUS-X))
     (716 180 (:REWRITE DEFAULT-TIMES-2))
     (686 154 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (686 154 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (686 154
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (686 154
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (686 154
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (686 154
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (686 154
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (686 154
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (636 180 (:REWRITE DEFAULT-TIMES-1))
     (600 13 (:REWRITE FLOOR-=-X/Y . 2))
     (564 13 (:REWRITE FLOOR-=-X/Y . 3))
     (525 26 (:REWRITE |(* (- x) y)|))
     (423 5 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (371 13 (:REWRITE DEFAULT-FLOOR-RATIO))
     (354 58
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (288 1
          (:REWRITE |(floor (floor x y) z)| . 1))
     (282 26 (:REWRITE DEFAULT-MINUS))
     (269 26 (:REWRITE |(- (* c x))|))
     (221 221
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (221 221
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (221 221
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (217 13 (:REWRITE FLOOR-ZERO . 5))
     (217 13 (:REWRITE FLOOR-X-Y-=--1 . 2))
     (206 58
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (159 35 (:REWRITE DEFAULT-LESS-THAN-1))
     (159 7
          (:REWRITE |(< (* (/ x) y) 1) with (< 0 x)|))
     (149 29 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (141 13 (:REWRITE FLOOR-ZERO . 2))
     (141 13 (:REWRITE FLOOR-X-Y-=-1 . 3))
     (141 13 (:REWRITE FLOOR-X-Y-=--1 . 3))
     (141 13 (:REWRITE FLOOR-CANCEL-*-CONST))
     (109 13
          (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
     (96 1
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (96 1
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (94 94
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (89 13 (:REWRITE DEFAULT-FLOOR-1))
     (83 7
         (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
     (58 1 (:REWRITE FLOOR-POSITIVE . 1))
     (53 4 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
     (46 35
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (46 35
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (45 13
         (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (44 12
         (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
     (37 4 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (35 35
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (35 35 (:REWRITE DEFAULT-LESS-THAN-2))
     (34 34
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
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
     (30 30 (:REWRITE REDUCE-INTEGERP-+))
     (30 30 (:META META-INTEGERP-CORRECT))
     (29 29 (:REWRITE SIMPLIFY-SUMS-<))
     (28 12
         (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
     (22 22 (:TYPE-PRESCRIPTION ABS))
     (21 21
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (13 13 (:REWRITE DEFAULT-FLOOR-2))
     (12 12 (:REWRITE |(floor x (- y))| . 2))
     (12 12 (:REWRITE |(floor x (- y))| . 1))
     (12 12
         (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
     (12 12
         (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
     (12 12 (:REWRITE |(floor (- x) y)| . 2))
     (12 12 (:REWRITE |(floor (- x) y)| . 1))
     (9 9 (:REWRITE |(< (/ x) 0)|))
     (9 9 (:REWRITE |(< (* x y) 0)|))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (5 5
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (5 1 (:REWRITE FLOOR-=-X/Y . 4))
     (5 1
        (:REWRITE |(equal (floor (+ x y) z) x)|))
     (2 2
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (1 1
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (1 1
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (1 1 (:REWRITE FLOOR-ZERO . 1))
     (1 1 (:REWRITE FLOOR-POSITIVE . 4))
     (1 1 (:REWRITE FLOOR-POSITIVE . 3))
     (1 1 (:REWRITE FLOOR-POSITIVE . 2))
     (1 1
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (1 1
        (:REWRITE |(floor (floor x y) z)| . 5))
     (1 1
        (:REWRITE |(floor (floor x y) z)| . 4))
     (1 1
        (:REWRITE |(floor (floor x y) z)| . 3))
     (1 1
        (:REWRITE |(floor (floor x y) z)| . 2))
     (1 1 (:REWRITE |(equal c (/ x))|))
     (1 1 (:REWRITE |(equal c (- x))|))
     (1 1 (:REWRITE |(equal (/ x) c)|))
     (1 1 (:REWRITE |(equal (/ x) (/ y))|))
     (1 1 (:REWRITE |(equal (- x) c)|))
     (1 1 (:REWRITE |(equal (- x) (- y))|))
     (1 1
        (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (1 1
        (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (1 1 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (1 1 (:REWRITE |(< 0 (* x y))|)))
(RP::SAS-FNC)
(RP::SAS-FNC-ZP)
(RP::SAS2)
(RP::CREATE-EX-CP-FNC-AUX)
(RP::CREATE-EX-CP-FNC)
(RP::CLEAR-RP-WRAPPERS (144 69 (:REWRITE DEFAULT-+-2))
                       (93 69 (:REWRITE DEFAULT-+-1))
                       (84 6 (:DEFINITION LENGTH))
                       (66 6 (:DEFINITION LEN))
                       (63 45 (:REWRITE DEFAULT-CDR))
                       (48 12 (:DEFINITION INTEGER-ABS))
                       (21 16 (:REWRITE DEFAULT-<-2))
                       (20 16 (:REWRITE DEFAULT-<-1))
                       (19 19 (:REWRITE DEFAULT-CAR))
                       (18 18
                           (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
                       (18 12 (:REWRITE STR::CONSP-OF-EXPLODE))
                       (12 12 (:REWRITE DEFAULT-UNARY-MINUS))
                       (12 6
                           (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
                       (6 6 (:TYPE-PRESCRIPTION LEN))
                       (6 6
                          (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
                       (6 6 (:REWRITE DEFAULT-REALPART))
                       (6 6 (:REWRITE DEFAULT-NUMERATOR))
                       (6 6 (:REWRITE DEFAULT-IMAGPART))
                       (6 6 (:REWRITE DEFAULT-DENOMINATOR)))
(RP::GET-VARS-AUX)
(RP::FLAG-GET-VARS-AUX (353 170 (:REWRITE DEFAULT-+-2))
                       (252 18 (:DEFINITION LENGTH))
                       (237 170 (:REWRITE DEFAULT-+-1))
                       (198 18 (:DEFINITION LEN))
                       (144 36 (:REWRITE COMMUTATIVITY-OF-+))
                       (144 36 (:DEFINITION INTEGER-ABS))
                       (106 52 (:REWRITE DEFAULT-CDR))
                       (59 46 (:REWRITE DEFAULT-<-2))
                       (56 46 (:REWRITE DEFAULT-<-1))
                       (54 54
                           (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
                       (54 36 (:REWRITE STR::CONSP-OF-EXPLODE))
                       (49 49 (:REWRITE FOLD-CONSTS-IN-+))
                       (36 36 (:REWRITE DEFAULT-UNARY-MINUS))
                       (36 18
                           (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
                       (34 34 (:REWRITE DEFAULT-CAR))
                       (18 18 (:TYPE-PRESCRIPTION LEN))
                       (18 18
                           (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
                       (18 18 (:REWRITE DEFAULT-REALPART))
                       (18 18 (:REWRITE DEFAULT-NUMERATOR))
                       (18 18 (:REWRITE DEFAULT-IMAGPART))
                       (18 18 (:REWRITE DEFAULT-DENOMINATOR))
                       (12 2 (:TYPE-PRESCRIPTION RETURN-LAST))
                       (2 2
                          (:TYPE-PRESCRIPTION THROW-NONEXEC-ERROR))
                       (2 2 (:REWRITE FN-CHECK-DEF-NOT-QUOTE)))
(FLAG::FLAG-EQUIV-LEMMA)
(RP::FLAG-GET-VARS-AUX-EQUIVALENCES)
(RP::FLAG-LEMMA-FOR-TRUE-LISTP-GET-VARS-AUX
     (32 32 (:REWRITE DEFAULT-CDR))
     (25 25 (:REWRITE DEFAULT-CAR))
     (20 10 (:DEFINITION TRUE-LISTP))
     (6 6 (:REWRITE FN-CHECK-DEF-NOT-QUOTE)))
(RP::TRUE-LISTP-GET-VARS-AUX)
(RP::TRUE-LISTP-GET-VARS-AUX-SUBTERMS)
(RP::GET-VARS-AUX (10 10 (:REWRITE DEFAULT-CDR))
                  (4 4 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
                  (4 4
                     (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
                  (4 4 (:REWRITE DEFAULT-CAR))
                  (1 1 (:REWRITE FN-CHECK-DEF-NOT-QUOTE)))
(RP::GET-ALL-VARS)
(RP::CLEAR-IRRELEVANT-HYP)
