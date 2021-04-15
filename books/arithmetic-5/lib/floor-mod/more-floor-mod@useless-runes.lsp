(|(* 2 (floor x y))|
     (28442 181 (:REWRITE FLOOR-ZERO . 3))
     (7547 37 (:REWRITE FLOOR-=-X/Y . 4))
     (7275 3467 (:REWRITE DEFAULT-PLUS-2))
     (6464 6464
           (:REWRITE NORMALIZE-FACTORS-SCATTER-EXPONENTS))
     (6285 189 (:REWRITE FLOOR-X-Y-=--1 . 3))
     (6285 189 (:REWRITE FLOOR-X-Y-=--1 . 2))
     (4611 189 (:REWRITE FLOOR-=-X/Y . 2))
     (4489 2364 (:META META-INTEGERP-CORRECT))
     (4343 181 (:REWRITE FLOOR-ZERO . 2))
     (4010 780 (:REWRITE REDUCE-RATIONALP-*))
     (4005 4005
           (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (4005 4005
           (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (4005 4005
           (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (4005 4005
           (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (4005 4005
           (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (4005 4005
           (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (4005 4005
           (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (3987 3987
           (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (3983 3983
           (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (3983 3983
           (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (3983 3983
           (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (3983 3983
           (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (3983 3983
           (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (3983 3983
           (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (3703 3467 (:REWRITE DEFAULT-PLUS-1))
     (3576 356
           (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-EQUAL))
     (3515 202 (:REWRITE DEFAULT-FLOOR-RATIO))
     (3479 452
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (3285 3285
           (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (3281 921 (:REWRITE RATIONALP-X))
     (2742 2742 (:REWRITE |(* c (* d x))|))
     (2268 1092
           (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-<))
     (2046 1661
           (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (2046 1661
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (1756 64 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
     (1735 1735 (:REWRITE DEFAULT-LESS-THAN-2))
     (1735 1735 (:REWRITE DEFAULT-LESS-THAN-1))
     (1653 1653 (:REWRITE INTEGERP-<-CONSTANT))
     (1653 1653 (:REWRITE CONSTANT-<-INTEGERP))
     (1653 1653
           (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (1653 1653
           (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (1653 1653
           (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (1653 1653
           (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (1653 1653 (:REWRITE |(< c (- x))|))
     (1653 1653
           (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (1653 1653
           (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (1653 1653
           (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (1653 1653
           (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (1653 1653 (:REWRITE |(< (/ x) (/ y))|))
     (1653 1653 (:REWRITE |(< (- x) c)|))
     (1653 1653 (:REWRITE |(< (- x) (- y))|))
     (1630 1630
           (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (1513 1513
           (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (1488 138 (:DEFINITION RFIX))
     (1436 1436
           (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (1376 64 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (1313 149
           (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
     (1313 149 (:REWRITE FLOOR-CANCEL-*-CONST))
     (1313 149
           (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
     (1313 149
           (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
     (1307 406
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (1269 141 (:REWRITE RATIONALP-/))
     (1174 1092
           (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-<))
     (940 328
          (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-EQUAL))
     (847 508 (:REWRITE INTEGERP-/))
     (828 740 (:META META-RATIONALP-CORRECT))
     (795 795 (:TYPE-PRESCRIPTION ABS))
     (780 780 (:REWRITE RATIONALP-MINUS-X))
     (742 742 (:REWRITE |(< (/ x) 0)|))
     (705 705 (:REWRITE |(< 0 (/ x))|))
     (703 703
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (703 703
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (654 78 (:REWRITE ACL2-NUMBERP-X))
     (652 652
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (652 652
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (567 23 (:REWRITE |(equal x (/ y))|))
     (505 245 (:REWRITE |(* (- x) y)|))
     (466 436 (:REWRITE |(equal (/ x) c)|))
     (437 437
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (436 436 (:REWRITE |(equal c (/ x))|))
     (436 436 (:REWRITE |(equal (/ x) (/ y))|))
     (436 436 (:REWRITE |(equal (- x) (- y))|))
     (434 434
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (434 434 (:REWRITE |(equal c (- x))|))
     (434 434 (:REWRITE |(equal (- x) c)|))
     (421 421
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (367 78
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (344 344
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (296 274
          (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (236 236 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (213 213 (:REWRITE DEFAULT-MINUS))
     (208 52 (:REWRITE |(integerp (- x))|))
     (182 14
          (:REWRITE |(equal (floor (+ x y) z) x)|))
     (181 159
          (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (156 156
          (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
     (154 154 (:REWRITE |(< (+ c/d x) y)|))
     (149 149
          (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (149 149 (:REWRITE |(floor x (- y))| . 2))
     (149 149 (:REWRITE |(floor x (- y))| . 1))
     (149 149
          (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
     (149 149 (:REWRITE |(floor (- x) y)| . 2))
     (149 149 (:REWRITE |(floor (- x) y)| . 1))
     (149 149
          (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
     (146 146 (:REWRITE |(< (+ (- c) x) y)|))
     (140 92
          (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (80 80 (:REWRITE |(< y (+ (- c) x))|))
     (80 80 (:REWRITE |(< x (+ c/d y))|))
     (72 8
         (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
     (72 8
         (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
     (72 8
         (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
     (72 8
         (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
     (68 68
         (:REWRITE |(< (* x (/ y)) 0) rationalp (* x (/ y))|))
     (42 3 (:REWRITE |(* (if a b c) x)|))
     (40 40 (:REWRITE |arith (* c (* d x))|))
     (26 26 (:REWRITE ARITH-NORMALIZE-ADDENDS))
     (16 16 (:REWRITE FOLD-CONSTS-IN-+))
     (15 15 (:REWRITE |(not (equal x (/ y)))|))
     (6 6 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (6 6 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (6 6 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (6 6 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (6 6 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (6 6 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (6 6 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (6 6 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (6 6 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
     (6 6 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (6 6 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (2 2 (:REWRITE |(/ (/ x))|)))
(UGLY-UNHIDE-HACK (1 1
                     (:TYPE-PRESCRIPTION UGLY-UNHIDE-HACK)))
(UGLY-UNHIDE-HACK-FN)
(UGLY-UNHIDE-HACK-THM-1 (3 3
                           (:TYPE-PRESCRIPTION UGLY-UNHIDE-HACK)))
(UGLY-UNHIDE-HACK-THM-2 (3 3
                           (:TYPE-PRESCRIPTION UGLY-UNHIDE-HACK)))
(UGLY-UNHIDE-HACK-LOOP-STOPPER-1
     (10 8 (:REWRITE DEFAULT-PLUS-1))
     (8 8 (:REWRITE DEFAULT-PLUS-2))
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
     (2 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (2 2 (:REWRITE |(< (/ x) 0)|))
     (2 2 (:REWRITE |(< (+ c/d x) y)|))
     (2 2 (:REWRITE |(< (+ (- c) x) y)|))
     (2 2 (:REWRITE |(< (* x y) 0)|))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (1 1 (:REWRITE REDUCE-INTEGERP-+))
     (1 1
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (1 1 (:REWRITE INTEGERP-MINUS-X))
     (1 1 (:REWRITE |(< 0 (/ x))|))
     (1 1 (:REWRITE |(< 0 (* x y))|))
     (1 1 (:META META-INTEGERP-CORRECT)))
(UGLY-UNHIDE-HACK-LOOP-STOPPER)
(|(* 1/2 (floor x y))|
     (2124 2 (:REWRITE FLOOR-=-X/Y . 4))
     (1985 34 (:REWRITE FLOOR-ZERO . 3))
     (1208 34 (:REWRITE CANCEL-FLOOR-+))
     (1117 34 (:REWRITE FLOOR-ZERO . 5))
     (1117 34 (:REWRITE FLOOR-ZERO . 4))
     (1088 34 (:REWRITE FLOOR-X-Y-=-1 . 3))
     (1088 34 (:REWRITE FLOOR-X-Y-=-1 . 2))
     (1088 34 (:REWRITE FLOOR-X-Y-=--1 . 3))
     (1088 34 (:REWRITE FLOOR-X-Y-=--1 . 2))
     (993 993
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (719 134 (:REWRITE |(< (/ x) 0)|))
     (657 34 (:REWRITE FLOOR-ZERO . 2))
     (537 34 (:REWRITE FLOOR-=-X/Y . 3))
     (537 34 (:REWRITE FLOOR-=-X/Y . 2))
     (523 262 (:META META-INTEGERP-CORRECT))
     (470 275 (:REWRITE INTEGERP-MINUS-X))
     (442 39 (:REWRITE DEFAULT-FLOOR-RATIO))
     (417 417
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (332 320 (:REWRITE |(* c (* d x))|))
     (318 47 (:REWRITE |(* (- x) y)|))
     (300 224
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (300 224
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (262 262 (:REWRITE REDUCE-INTEGERP-+))
     (260 260 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (260 260
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (260 260
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (260 260
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (260 260
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (260 260
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (260 260
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (254 254 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (254 254
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (254 254
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (254 254
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (254 254
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (254 254
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (254 254
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (252 12 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
     (246 30 (:REWRITE ACL2-NUMBERP-X))
     (243 32
          (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
     (243 32
          (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
     (224 224
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (224 224 (:REWRITE DEFAULT-LESS-THAN-2))
     (224 224 (:REWRITE DEFAULT-LESS-THAN-1))
     (224 224
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (224 224
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (224 224
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (224 224
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (224 224
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (224 224
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (224 224
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (224 224
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (224 224 (:REWRITE |(< (/ x) (/ y))|))
     (224 224 (:REWRITE |(< (- x) (- y))|))
     (211 211 (:REWRITE SIMPLIFY-SUMS-<))
     (211 211
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (211 211
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (211 211
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (211 211 (:REWRITE INTEGERP-<-CONSTANT))
     (211 211 (:REWRITE CONSTANT-<-INTEGERP))
     (211 211 (:REWRITE |(< c (- x))|))
     (211 211 (:REWRITE |(< (- x) c)|))
     (184 12 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (152 45 (:REWRITE |(- (* c x))|))
     (144 25 (:REWRITE DEFAULT-PLUS-2))
     (134 134 (:REWRITE |(< (* x y) 0)|))
     (129 32 (:REWRITE RATIONALP-X))
     (121 121
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (121 121
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (102 34 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (102 34
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (102 34
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (91 91 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (90 90
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (90 90
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (90 90 (:REWRITE |(< 0 (/ x))|))
     (90 90 (:REWRITE |(< 0 (* x y))|))
     (87 48 (:REWRITE INTEGERP-/))
     (85 31 (:REWRITE REDUCE-RATIONALP-*))
     (84 21 (:REWRITE |(integerp (- x))|))
     (69 69
         (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (45 45 (:REWRITE DEFAULT-MINUS))
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
     (32 32
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (32 32
         (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (32 32 (:REWRITE |(floor x (- y))| . 2))
     (32 32 (:REWRITE |(floor x (- y))| . 1))
     (32 32
         (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
     (32 32 (:REWRITE |(floor (- x) y)| . 2))
     (32 32 (:REWRITE |(floor (- x) y)| . 1))
     (31 31 (:REWRITE REDUCE-RATIONALP-+))
     (31 31 (:REWRITE RATIONALP-MINUS-X))
     (31 31 (:META META-RATIONALP-CORRECT))
     (30 30
         (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
     (28 2 (:REWRITE |(* (if a b c) x)|))
     (25 25 (:REWRITE DEFAULT-PLUS-1))
     (25 25
         (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (24 2 (:DEFINITION RFIX))
     (18 18
         (:REWRITE |(< (* x (/ y)) 0) rationalp (* x (/ y))|))
     (18 1
         (:REWRITE |(equal (floor (+ x y) z) x)|))
     (13 13 (:REWRITE |(/ (/ x))|))
     (12 12
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (12 12 (:REWRITE NORMALIZE-ADDENDS))
     (11 11
         (:TYPE-PRESCRIPTION UGLY-UNHIDE-HACK))
     (11 11 (:REWRITE |(equal (* x y) 0)|))
     (9 1 (:REWRITE RATIONALP-/))
     (6 2 (:REWRITE |(* -1 x)|))
     (1 1 (:REWRITE |(not (equal x (/ y)))|))
     (1 1 (:REWRITE |(equal x (/ y))|))
     (1 1 (:REWRITE |(equal (+ (- c) x) y)|))
     (1 1 (:REWRITE |(* 2 (floor x y))| . 3))
     (1 1 (:REWRITE |(* 2 (floor x y))| . 2)))
(EXTRA-INTP-THM-1 (8 8 (:REWRITE DEFAULT-TIMES-2))
                  (8 8 (:REWRITE DEFAULT-TIMES-1))
                  (5 5
                     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                  (4 4
                     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
                  (4 4 (:REWRITE DEFAULT-DIVIDE))
                  (1 1 (:REWRITE |(* c (* d x))|)))
(EXTRA-INTP-THM-3 (70 5 (:META META-INTEGERP-CORRECT))
                  (63 2 (:REWRITE INTEGERP-/))
                  (27 27 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
                  (27 27 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
                  (27 27 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
                  (27 27 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
                  (27 27
                      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
                  (27 27
                      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
                  (27 27
                      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
                  (27 27
                      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
                  (27 27
                      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
                  (27 27
                      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
                  (27 27
                      (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
                  (27 27
                      (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
                  (27 27
                      (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
                  (27 27
                      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
                  (27 27
                      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
                  (27 27
                      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
                  (11 11 (:REWRITE DEFAULT-TIMES-2))
                  (11 11 (:REWRITE DEFAULT-TIMES-1))
                  (9 1 (:REWRITE DEFAULT-FLOOR-RATIO))
                  (7 7
                     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                  (6 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                  (6 6
                     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                  (6 6
                     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                  (6 6
                     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
                  (6 6
                     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                  (6 6
                     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
                  (6 6
                     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
                  (6 6 (:REWRITE DEFAULT-DIVIDE))
                  (6 6 (:REWRITE |(equal c (/ x))|))
                  (6 6 (:REWRITE |(equal c (- x))|))
                  (6 6 (:REWRITE |(equal (/ x) c)|))
                  (6 6 (:REWRITE |(equal (/ x) (/ y))|))
                  (6 6 (:REWRITE |(equal (- x) c)|))
                  (6 6 (:REWRITE |(equal (- x) (- y))|))
                  (5 5 (:REWRITE REDUCE-INTEGERP-+))
                  (5 5 (:REWRITE INTEGERP-MINUS-X))
                  (4 1 (:REWRITE RATIONALP-X))
                  (2 2
                     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
                  (2 2 (:REWRITE |(* c (* d x))|))
                  (1 1 (:REWRITE REDUCE-RATIONALP-+))
                  (1 1 (:REWRITE REDUCE-RATIONALP-*))
                  (1 1 (:REWRITE RATIONALP-MINUS-X))
                  (1 1 (:REWRITE DEFAULT-FLOOR-2))
                  (1 1 (:REWRITE DEFAULT-FLOOR-1))
                  (1 1 (:META META-RATIONALP-CORRECT)))
(|(floor (+ x r) i)|
     (3702 3 (:REWRITE FLOOR-=-X/Y . 4))
     (1061 27 (:REWRITE FLOOR-ZERO . 3))
     (1055 37 (:REWRITE FLOOR-ZERO . 5))
     (911 37 (:REWRITE FLOOR-X-Y-=-1 . 2))
     (749 37 (:REWRITE FLOOR-X-Y-=--1 . 2))
     (736 736 (:REWRITE DEFAULT-TIMES-2))
     (736 736 (:REWRITE DEFAULT-TIMES-1))
     (712 24 (:REWRITE MOD-X-Y-=-X . 4))
     (702 218 (:REWRITE DEFAULT-PLUS-2))
     (616 24 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (553 24 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (536 37 (:REWRITE FLOOR-=-X/Y . 3))
     (536 37 (:REWRITE FLOOR-=-X/Y . 2))
     (524 218 (:REWRITE DEFAULT-PLUS-1))
     (459 27 (:REWRITE CANCEL-FLOOR-+))
     (413 293 (:REWRITE DEFAULT-LESS-THAN-1))
     (400 37 (:REWRITE DEFAULT-FLOOR-RATIO))
     (388 44 (:REWRITE |(* (- x) y)|))
     (385 385 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (385 385 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (385 385 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (385 385 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (385 385
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (385 385
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (385 385
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (385 385
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (385 385
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (361 19 (:REWRITE CANCEL-MOD-+))
     (344 24 (:REWRITE MOD-ZERO . 4))
     (317 293
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (312 24 (:REWRITE MOD-ZERO . 3))
     (301 221
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (294 294
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (293 293
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (293 293
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (293 293
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (293 293
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (293 293 (:REWRITE INTEGERP-<-CONSTANT))
     (293 293 (:REWRITE DEFAULT-LESS-THAN-2))
     (293 293 (:REWRITE CONSTANT-<-INTEGERP))
     (293 293
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (293 293
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (293 293
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (293 293
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (293 293 (:REWRITE |(< c (- x))|))
     (293 293
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (293 293
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (293 293
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (293 293 (:REWRITE |(< (/ x) (/ y))|))
     (293 293 (:REWRITE |(< (- x) c)|))
     (293 293 (:REWRITE |(< (- x) (- y))|))
     (280 280
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (280 280 (:REWRITE DEFAULT-DIVIDE))
     (216 24 (:REWRITE DEFAULT-MOD-RATIO))
     (215 43 (:REWRITE |(integerp (- x))|))
     (203 203 (:REWRITE INTEGERP-MINUS-X))
     (201 201 (:META META-INTEGERP-CORRECT))
     (189 189 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (189 189 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (189 189 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (189 189
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (189 189
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (189 189
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (189 189
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (189 189
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (189 189
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (189 189
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (189 189
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (189 189
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (189 189
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (189 189
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (189 189
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (152 152 (:REWRITE EXTRA-INTP-THM-1))
     (132 8 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
     (132 8 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (129 129 (:REWRITE |(< (/ x) 0)|))
     (129 129 (:REWRITE |(< (* x y) 0)|))
     (127 127
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (127 127
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (107 67
          (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-<))
     (107 67
          (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-<))
     (104 8 (:LINEAR MOD-BOUNDS-3))
     (96 28
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (92 92
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (90 90
         (:REWRITE NORMALIZE-FACTORS-SCATTER-EXPONENTS))
     (87 19
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (74 74
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (74 74
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (74 74 (:REWRITE |(< 0 (/ x))|))
     (74 74 (:REWRITE |(< 0 (* x y))|))
     (45 11 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (44 44 (:REWRITE DEFAULT-MINUS))
     (43 43 (:REWRITE |(- (* c x))|))
     (38 38 (:REWRITE |(< (+ c/d x) y)|))
     (38 38 (:REWRITE |(< (+ (- c) x) y)|))
     (37 37 (:REWRITE FLOOR-X-Y-=-1 . 3))
     (37 37 (:REWRITE FLOOR-X-Y-=--1 . 3))
     (37 37 (:REWRITE DEFAULT-FLOOR-2))
     (37 37 (:REWRITE DEFAULT-FLOOR-1))
     (36 9 (:REWRITE RATIONALP-X))
     (28 28
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (28 28
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (28 28
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (28 28 (:REWRITE |(equal c (/ x))|))
     (28 28 (:REWRITE |(equal c (- x))|))
     (28 28 (:REWRITE |(equal (/ x) c)|))
     (28 28 (:REWRITE |(equal (/ x) (/ y))|))
     (28 28 (:REWRITE |(equal (- x) c)|))
     (28 28 (:REWRITE |(equal (- x) (- y))|))
     (27 27 (:REWRITE FLOOR-ZERO . 2))
     (27 27
         (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
     (27 27
         (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (27 27 (:REWRITE FLOOR-CANCEL-*-CONST))
     (27 27 (:REWRITE |(floor x (- y))| . 2))
     (27 27 (:REWRITE |(floor x (- y))| . 1))
     (27 27
         (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
     (27 27
         (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
     (27 27 (:REWRITE |(floor (- x) y)| . 2))
     (27 27 (:REWRITE |(floor (- x) y)| . 1))
     (27 27
         (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
     (27 27
         (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
     (25 25
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (24 24 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (24 24 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (24 24 (:REWRITE DEFAULT-MOD-2))
     (24 24 (:REWRITE DEFAULT-MOD-1))
     (21 21
         (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (19 19 (:REWRITE MOD-X-Y-=-X . 2))
     (19 19
         (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (19 19
         (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (19 19 (:REWRITE MOD-CANCEL-*-CONST))
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
     (19 19 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (19 19
         (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (19 19
         (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (19 19
         (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (16 16
         (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (16 16 (:LINEAR MOD-BOUNDS-2))
     (9 9
        (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-EQUAL))
     (9 9 (:REWRITE REDUCE-RATIONALP-+))
     (9 9 (:REWRITE REDUCE-RATIONALP-*))
     (9 9 (:REWRITE RATIONALP-MINUS-X))
     (9 9
        (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-EQUAL))
     (9 9 (:META META-RATIONALP-CORRECT))
     (8 8 (:REWRITE |(< y (+ (- c) x))|))
     (8 8 (:REWRITE |(< x (+ c/d y))|))
     (6 6 (:REWRITE |(+ c (+ d x))|))
     (5 5
        (:REWRITE |(floor (+ x y) z) where (< 0 z)| . 3))
     (5 5
        (:REWRITE |(floor (+ x y) z) where (< 0 z)| . 2))
     (4 4 (:REWRITE FOLD-CONSTS-IN-+))
     (3 3 (:REWRITE |(equal (+ (- c) x) y)|))
     (2 2 (:REWRITE ARITH-NORMALIZE-ADDENDS))
     (2 2
        (:REWRITE |(equal (floor (+ x y) z) x)|))
     (1 1 (:REWRITE |(* x (- y))|)))
(MOD-X-I*J
     (4830 20 (:REWRITE MOD-X-Y-=-X-Y . 1))
     (3228 108 (:LINEAR MOD-BOUNDS-2))
     (3228 108 (:LINEAR MOD-BOUNDS-1))
     (2949 121
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (2446 20 (:REWRITE MOD-X-Y-=-X+Y . 1))
     (1252 54 (:LINEAR MOD-BOUNDS-3))
     (915 813 (:REWRITE DEFAULT-TIMES-2))
     (813 813 (:REWRITE DEFAULT-TIMES-1))
     (718 6 (:REWRITE FLOOR-ZERO . 3))
     (648 648 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (648 648
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (648 648
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (648 648
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (648 648
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (647 647 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (639 253 (:META META-INTEGERP-CORRECT))
     (509 113 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (449 17 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (449 17 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (444 378 (:REWRITE DEFAULT-PLUS-2))
     (430 430 (:REWRITE DEFAULT-LESS-THAN-2))
     (430 430 (:REWRITE DEFAULT-LESS-THAN-1))
     (426 426
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (426 426
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (426 426
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (426 426
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (426 426 (:REWRITE INTEGERP-<-CONSTANT))
     (426 426 (:REWRITE CONSTANT-<-INTEGERP))
     (426 426
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (426 426
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (426 426
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (426 426
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (426 426 (:REWRITE |(< c (- x))|))
     (426 426
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (426 426
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (426 426
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (426 426
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (426 426 (:REWRITE |(< (/ x) (/ y))|))
     (426 426 (:REWRITE |(< (- x) c)|))
     (426 426 (:REWRITE |(< (- x) (- y))|))
     (426 17 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (426 17 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (416 378 (:REWRITE DEFAULT-PLUS-1))
     (398 18 (:REWRITE DEFAULT-MOD-RATIO))
     (379 379
          (:REWRITE NORMALIZE-FACTORS-SCATTER-EXPONENTS))
     (339 314
          (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-<))
     (314 314
          (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-<))
     (313 93
          (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-EQUAL))
     (313 93
          (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-EQUAL))
     (286 286 (:REWRITE DEFAULT-DIVIDE))
     (281 16 (:REWRITE MOD-X-Y-=-X . 4))
     (281 16 (:REWRITE MOD-X-Y-=-X . 3))
     (255 255 (:REWRITE INTEGERP-MINUS-X))
     (237 237
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (204 204 (:REWRITE |(< 0 (/ x))|))
     (204 204 (:REWRITE |(< 0 (* x y))|))
     (203 203
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (203 203
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (198 68 (:REWRITE INTEGERP-/))
     (188 16 (:REWRITE MOD-X-Y-=-X . 2))
     (188 16 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (188 16
          (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (185 185 (:REWRITE |(< (/ x) 0)|))
     (185 185 (:REWRITE |(< (* x y) 0)|))
     (182 6 (:REWRITE FLOOR-ZERO . 5))
     (182 6 (:REWRITE FLOOR-ZERO . 4))
     (180 180
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (180 180
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (176 6 (:REWRITE FLOOR-X-Y-=-1 . 3))
     (176 6 (:REWRITE FLOOR-X-Y-=-1 . 2))
     (176 6 (:REWRITE FLOOR-X-Y-=--1 . 3))
     (176 6 (:REWRITE FLOOR-X-Y-=--1 . 2))
     (162 6 (:REWRITE EXTRA-INTP-THM-3))
     (144 17 (:REWRITE MOD-ZERO . 4))
     (138 28
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (137 122 (:REWRITE |(equal (/ x) c)|))
     (128 128 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
     (128 128 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (128 128 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (128 128 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (128 128
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (128 128
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (128 128
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (128 128
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (128 128
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (128 128
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (128 128
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (128 128
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (128 128
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (128 128
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (128 128
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (128 128
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (124 4 (:REWRITE |(< x (if a b c))|))
     (122 122
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (122 122
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (122 122 (:REWRITE |(equal c (/ x))|))
     (122 122 (:REWRITE |(equal (/ x) (/ y))|))
     (122 122 (:REWRITE |(equal (- x) (- y))|))
     (121 121
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (121 121 (:REWRITE |(equal c (- x))|))
     (121 121 (:REWRITE |(equal (- x) c)|))
     (115 115
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (114 6 (:REWRITE CANCEL-FLOOR-+))
     (111 111 (:REWRITE EXTRA-INTP-THM-1))
     (100 100
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (88 6 (:REWRITE FLOOR-ZERO . 2))
     (81 81
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (78 6 (:REWRITE FLOOR-=-X/Y . 3))
     (78 6 (:REWRITE FLOOR-=-X/Y . 2))
     (66 66
         (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
     (66 66 (:REWRITE |(* c (* d x))|))
     (58 58
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (56 56
         (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (54 6 (:REWRITE DEFAULT-FLOOR-RATIO))
     (50 50
         (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (44 11 (:REWRITE RATIONALP-X))
     (38 38 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (26 26 (:REWRITE |(equal (+ (- c) x) y)|))
     (25 25 (:REWRITE |(equal (* x y) 0)|))
     (24 24 (:REWRITE DEFAULT-MINUS))
     (22 22 (:REWRITE |(- (* c x))|))
     (18 18 (:REWRITE DEFAULT-MOD-2))
     (18 18 (:REWRITE DEFAULT-MOD-1))
     (18 18
         (:REWRITE |(equal (mod (+ x y) z) x)|))
     (14 14
         (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (14 14
         (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (14 14 (:REWRITE MOD-CANCEL-*-CONST))
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
         (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (14 14
         (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (14 14 (:REWRITE |(< (+ c/d x) y)|))
     (14 14 (:REWRITE |(< (+ (- c) x) y)|))
     (12 12 (:REWRITE |(+ c (+ d x))|))
     (11 11 (:REWRITE REDUCE-RATIONALP-+))
     (11 11 (:REWRITE REDUCE-RATIONALP-*))
     (11 11 (:REWRITE RATIONALP-MINUS-X))
     (11 11 (:REWRITE |(< y (+ (- c) x))|))
     (11 11 (:REWRITE |(< x (+ c/d y))|))
     (11 11 (:META META-RATIONALP-CORRECT))
     (6 6 (:REWRITE |arith (* c (* d x))|))
     (6 6
        (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
     (6 6
        (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (6 6 (:REWRITE FLOOR-CANCEL-*-CONST))
     (6 6 (:REWRITE DEFAULT-FLOOR-2))
     (6 6 (:REWRITE DEFAULT-FLOOR-1))
     (6 6 (:REWRITE ARITH-NORMALIZE-ADDENDS))
     (6 6 (:REWRITE |(floor x (- y))| . 2))
     (6 6 (:REWRITE |(floor x (- y))| . 1))
     (6 6
        (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
     (6 6
        (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
     (6 6 (:REWRITE |(floor (- x) y)| . 2))
     (6 6 (:REWRITE |(floor (- x) y)| . 1))
     (6 6
        (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
     (6 6
        (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
     (5 5 (:REWRITE |arith (- (* c x))|))
     (4 4 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (4 4 (:REWRITE FOLD-CONSTS-IN-+))
     (3 3 (:REWRITE |arith (* (- x) y)|))
     (2 2 (:REWRITE |(* x (- y))|))
     (1 1 (:REWRITE |(not (equal x (/ y)))|))
     (1 1 (:REWRITE |(equal x (/ y))|))
     (1 1 (:REWRITE |(/ (/ x))|)))
(MOD-X-I*J-V2
     (5154 14 (:REWRITE MOD-X-Y-=-X-Y . 1))
     (3932 132 (:LINEAR MOD-BOUNDS-2))
     (3932 132 (:LINEAR MOD-BOUNDS-1))
     (3400 168
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (3368 160 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (1168 66 (:LINEAR MOD-BOUNDS-3))
     (1046 452 (:REWRITE DEFAULT-PLUS-2))
     (950 848 (:REWRITE DEFAULT-TIMES-2))
     (922 157 (:META META-INTEGERP-CORRECT))
     (848 848 (:REWRITE DEFAULT-TIMES-1))
     (757 757 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (757 757 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (757 757 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (757 757
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (757 757
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (757 757
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (757 757
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (741 24 (:REWRITE INTEGERP-/))
     (718 6 (:REWRITE FLOOR-ZERO . 3))
     (574 452 (:REWRITE DEFAULT-PLUS-1))
     (475 475 (:REWRITE DEFAULT-LESS-THAN-2))
     (475 475 (:REWRITE DEFAULT-LESS-THAN-1))
     (471 471
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (471 471
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (471 471
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (471 471
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (471 471 (:REWRITE INTEGERP-<-CONSTANT))
     (471 471 (:REWRITE CONSTANT-<-INTEGERP))
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
     (471 471 (:REWRITE |(< (- x) c)|))
     (471 471 (:REWRITE |(< (- x) (- y))|))
     (423 16 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (422 16 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (418 418
          (:REWRITE NORMALIZE-FACTORS-SCATTER-EXPONENTS))
     (392 128
          (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-EQUAL))
     (392 128
          (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-EQUAL))
     (392 16 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (392 16 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (386 16 (:REWRITE MOD-ZERO . 3))
     (368 343
          (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-<))
     (362 16 (:REWRITE DEFAULT-MOD-RATIO))
     (343 343
          (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-<))
     (304 304 (:REWRITE DEFAULT-DIVIDE))
     (257 257
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (256 16 (:REWRITE MOD-X-Y-=-X . 4))
     (256 16 (:REWRITE MOD-X-Y-=-X . 3))
     (222 222 (:REWRITE |(< (/ x) 0)|))
     (222 222 (:REWRITE |(< (* x y) 0)|))
     (217 217
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (217 217
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (214 214 (:REWRITE |(< 0 (/ x))|))
     (214 214 (:REWRITE |(< 0 (* x y))|))
     (213 213
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (213 213
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (188 16 (:REWRITE MOD-X-Y-=-X . 2))
     (188 16 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (188 16
          (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (184 169 (:REWRITE |(equal (/ x) c)|))
     (182 6 (:REWRITE FLOOR-ZERO . 5))
     (182 6 (:REWRITE FLOOR-ZERO . 4))
     (176 6 (:REWRITE FLOOR-X-Y-=-1 . 3))
     (176 6 (:REWRITE FLOOR-X-Y-=-1 . 2))
     (176 6 (:REWRITE FLOOR-X-Y-=--1 . 3))
     (176 6 (:REWRITE FLOOR-X-Y-=--1 . 2))
     (172 40
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (169 169
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (169 169
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (169 169 (:REWRITE |(equal c (/ x))|))
     (169 169 (:REWRITE |(equal (/ x) (/ y))|))
     (169 169 (:REWRITE |(equal (- x) (- y))|))
     (168 168
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (168 168 (:REWRITE |(equal c (- x))|))
     (168 168 (:REWRITE |(equal (- x) c)|))
     (161 161 (:REWRITE INTEGERP-MINUS-X))
     (140 140 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
     (140 140 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (140 140 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (140 140 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (140 140
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (140 140
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (140 140
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (140 140
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (140 140
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (140 140
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (140 140
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (140 140
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (140 140
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (140 140
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (140 140
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (140 140
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (133 133
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (128 16 (:REWRITE MOD-ZERO . 4))
     (124 4 (:REWRITE |(< x (if a b c))|))
     (116 116
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (114 6 (:REWRITE CANCEL-FLOOR-+))
     (100 100 (:REWRITE EXTRA-INTP-THM-1))
     (91 91
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (88 6 (:REWRITE FLOOR-ZERO . 2))
     (84 84 (:REWRITE |(* c (* d x))|))
     (78 6 (:REWRITE FLOOR-=-X/Y . 3))
     (78 6 (:REWRITE FLOOR-=-X/Y . 2))
     (74 74
         (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
     (66 66
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (56 56 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (56 56
         (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (54 6 (:REWRITE DEFAULT-FLOOR-RATIO))
     (51 51
         (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (44 11 (:REWRITE RATIONALP-X))
     (40 8 (:REWRITE |(+ x x)|))
     (33 33 (:REWRITE DEFAULT-MINUS))
     (30 30 (:REWRITE |(equal (+ (- c) x) y)|))
     (30 6 (:REWRITE |(integerp (- x))|))
     (26 26 (:REWRITE |(- (* c x))|))
     (24 24 (:REWRITE |(equal (* x y) 0)|))
     (24 24 (:REWRITE |(+ c (+ d x))|))
     (16 16 (:REWRITE DEFAULT-MOD-2))
     (16 16 (:REWRITE DEFAULT-MOD-1))
     (14 14
         (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (14 14
         (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (14 14 (:REWRITE MOD-CANCEL-*-CONST))
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
         (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (14 14
         (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (14 14 (:REWRITE |(< (+ c/d x) y)|))
     (14 14 (:REWRITE |(< (+ (- c) x) y)|))
     (12 12 (:REWRITE ARITH-NORMALIZE-ADDENDS))
     (12 12
         (:REWRITE |(equal (mod (+ x y) z) x)|))
     (11 11 (:REWRITE REDUCE-RATIONALP-+))
     (11 11 (:REWRITE REDUCE-RATIONALP-*))
     (11 11 (:REWRITE RATIONALP-MINUS-X))
     (11 11 (:REWRITE |(< y (+ (- c) x))|))
     (11 11 (:REWRITE |(< x (+ c/d y))|))
     (11 11 (:META META-RATIONALP-CORRECT))
     (10 10 (:REWRITE MOD-X-I*J))
     (8 8 (:REWRITE |arith (* c (* d x))|))
     (8 8 (:REWRITE |(+ (* c x) (* d x))|))
     (8 8 (:REWRITE |(* 0 x)|))
     (6 6 (:REWRITE |arith (- (* c x))|))
     (6 6 (:REWRITE MOD-X-Y-=-X . 1))
     (6 6
        (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
     (6 6
        (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (6 6 (:REWRITE FLOOR-CANCEL-*-CONST))
     (6 6 (:REWRITE EXTRA-INTP-THM-3))
     (6 6 (:REWRITE DEFAULT-FLOOR-2))
     (6 6 (:REWRITE DEFAULT-FLOOR-1))
     (6 6 (:REWRITE |(floor x (- y))| . 2))
     (6 6 (:REWRITE |(floor x (- y))| . 1))
     (6 6
        (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
     (6 6
        (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
     (6 6 (:REWRITE |(floor (- x) y)| . 2))
     (6 6 (:REWRITE |(floor (- x) y)| . 1))
     (6 6
        (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
     (6 6
        (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
     (4 4 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (4 4 (:REWRITE FOLD-CONSTS-IN-+))
     (3 3 (:REWRITE |arith (* (- x) y)|))
     (2 2 (:REWRITE |(* x (- y))|))
     (1 1 (:REWRITE |(not (equal x (/ y)))|))
     (1 1 (:REWRITE |(equal x (/ y))|))
     (1 1 (:REWRITE |(/ (/ x))|)))
(MOD-X-I*J-X-2
     (56060 20 (:REWRITE MOD-X-Y-=-X+Y . 1))
     (38335 195
            (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (21364 20 (:REWRITE MOD-X-Y-=-X-Y . 1))
     (19718 406
            (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (9016 98 (:REWRITE FLOOR-ZERO . 3))
     (8440 669 (:REWRITE DEFAULT-PLUS-2))
     (7508 672 (:REWRITE |(* y (* x z))|))
     (5821 4105 (:REWRITE DEFAULT-TIMES-2))
     (5716 1582 (:META META-INTEGERP-CORRECT))
     (5142 600 (:REWRITE |(< (/ x) 0)|))
     (4678 98 (:REWRITE CANCEL-FLOOR-+))
     (4139 4105 (:REWRITE DEFAULT-TIMES-1))
     (3235 669 (:REWRITE DEFAULT-PLUS-1))
     (3156 98 (:REWRITE FLOOR-=-X/Y . 2))
     (3092 98 (:REWRITE FLOOR-=-X/Y . 3))
     (2981 266
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (2634 98 (:REWRITE FLOOR-X-Y-=-1 . 3))
     (2634 98 (:REWRITE FLOOR-X-Y-=-1 . 2))
     (2634 98 (:REWRITE FLOOR-X-Y-=--1 . 3))
     (2634 98 (:REWRITE FLOOR-X-Y-=--1 . 2))
     (2586 98 (:REWRITE FLOOR-ZERO . 5))
     (2586 98 (:REWRITE FLOOR-ZERO . 4))
     (2540 2540
           (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (2540 2540
           (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (2540 2540
           (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (2540 2540
           (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (2540 2540
           (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (2540 2540
           (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (2540 2540
           (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (2540 2540
           (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (2540 2540
           (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (2540 2540
           (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (2540 2540
           (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (2540 2540
           (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (2540 2540
           (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (2540 2540
           (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (2540 2540
           (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (2448 128 (:LINEAR MOD-BOUNDS-2))
     (2448 128 (:LINEAR MOD-BOUNDS-1))
     (2434 2434 (:REWRITE DEFAULT-DIVIDE))
     (2214 89 (:REWRITE |(integerp (- x))|))
     (2072 184
           (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-<-2))
     (2008 2008
           (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (1974 98 (:REWRITE DEFAULT-FLOOR-RATIO))
     (1934 756 (:REWRITE INTEGERP-/))
     (1828 52 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
     (1828 52 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (1582 1582 (:REWRITE REDUCE-INTEGERP-+))
     (1582 1582 (:REWRITE INTEGERP-MINUS-X))
     (1498 1498
           (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (1440 110 (:REWRITE |(* (- x) y)|))
     (1379 1379 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (1379 1379 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (1379 1379 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (1379 1379
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (1379 1379
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (1379 1379
           (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (1379 1379
           (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
     (1379 1379
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (1379 1379
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (1126 398 (:REWRITE |(equal (/ x) c)|))
     (1093 1076 (:REWRITE DEFAULT-LESS-THAN-2))
     (1093 1076 (:REWRITE DEFAULT-LESS-THAN-1))
     (1064 1064
           (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (1064 1064
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (1064 1064
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (1064 1064
           (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (1064 1064
           (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (1064 1064
           (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (1064 1064
           (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (1064 1064
           (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (1064 1064
           (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (1064 1064
           (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (1064 1064
           (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (1064 1064 (:REWRITE |(< (/ x) (/ y))|))
     (1064 1064 (:REWRITE |(< (- x) (- y))|))
     (1016 982
           (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (994 994
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (994 994 (:REWRITE INTEGERP-<-CONSTANT))
     (994 994 (:REWRITE CONSTANT-<-INTEGERP))
     (994 994 (:REWRITE |(< c (- x))|))
     (994 994 (:REWRITE |(< (- x) c)|))
     (982 982 (:REWRITE SIMPLIFY-SUMS-<))
     (981 9 (:REWRITE FLOOR-=-X/Y . 4))
     (910 25 (:REWRITE MOD-ZERO . 4))
     (895 19 (:REWRITE MOD-X-Y-=-X . 4))
     (895 19 (:REWRITE MOD-X-Y-=-X . 3))
     (810 810
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (768 768 (:REWRITE |(* c (* d x))|))
     (755 398 (:REWRITE |(equal (- x) (- y))|))
     (724 25 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (724 25 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (724 25 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (724 25 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (600 600 (:REWRITE |(< (* x y) 0)|))
     (518 518
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (518 518
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (472 25 (:REWRITE DEFAULT-MOD-RATIO))
     (466 98 (:REWRITE FLOOR-ZERO . 2))
     (458 386 (:REWRITE |(equal (- x) c)|))
     (456 456
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (456 456
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (456 456 (:REWRITE |(< 0 (/ x))|))
     (456 456 (:REWRITE |(< 0 (* x y))|))
     (418 406
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (417 89 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (408 14 (:REWRITE MOD-X-I*J))
     (398 398 (:REWRITE |(equal c (/ x))|))
     (398 398 (:REWRITE |(equal (/ x) (/ y))|))
     (396 396
          (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (386 386 (:REWRITE |(equal c (- x))|))
     (384 12 (:REWRITE |(< x (if a b c))|))
     (382 382
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (371 75 (:REWRITE |(+ c (+ d x))|))
     (368 368
          (:REWRITE NORMALIZE-FACTORS-SCATTER-EXPONENTS))
     (340 340 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (340 116
          (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-EQUAL))
     (340 116
          (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-EQUAL))
     (313 19 (:REWRITE MOD-X-Y-=-X . 2))
     (313 19 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (313 19
          (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (296 19 (:REWRITE CANCEL-MOD-+))
     (276 8 (:REWRITE |(equal x (/ y))|))
     (244 244
          (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (194 194
          (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
     (192 10 (:REWRITE EXTRA-INTP-THM-3))
     (188 4 (:REWRITE |(equal x (- (/ y)))|))
     (185 117 (:REWRITE DEFAULT-MINUS))
     (177 177
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (172 172
          (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-<))
     (172 172
          (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-<))
     (160 160 (:REWRITE |(/ (/ x))|))
     (131 115 (:REWRITE |(- (* c x))|))
     (128 16 (:REWRITE |(* a (/ a))|))
     (100 100 (:REWRITE |(equal (+ (- c) x) y)|))
     (98 98
         (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
     (98 98
         (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (98 98 (:REWRITE FLOOR-CANCEL-*-CONST))
     (98 98 (:REWRITE DEFAULT-FLOOR-2))
     (98 98 (:REWRITE DEFAULT-FLOOR-1))
     (98 98 (:REWRITE |(floor x (- y))| . 2))
     (98 98 (:REWRITE |(floor x (- y))| . 1))
     (98 98
         (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
     (98 98
         (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
     (98 98 (:REWRITE |(floor (- x) y)| . 2))
     (98 98 (:REWRITE |(floor (- x) y)| . 1))
     (98 98
         (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
     (98 98
         (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
     (82 82 (:REWRITE |(equal (* x y) 0)|))
     (76 76 (:REWRITE |arith (* c (* d x))|))
     (60 15 (:REWRITE RATIONALP-X))
     (56 4 (:REWRITE |(equal (* (/ x) y) -1)|))
     (42 25 (:REWRITE DEFAULT-MOD-1))
     (36 19
         (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (36 19 (:REWRITE MOD-CANCEL-*-CONST))
     (30 30 (:REWRITE FOLD-CONSTS-IN-+))
     (30 6 (:REWRITE |(+ x x)|))
     (25 25 (:REWRITE DEFAULT-MOD-2))
     (20 20 (:REWRITE ARITH-NORMALIZE-ADDENDS))
     (20 20
         (:REWRITE |(equal (mod (+ x y) z) x)|))
     (20 20 (:REWRITE |(* 1 x)|))
     (19 19
         (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
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
         (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (18 18
         (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (15 15 (:REWRITE REDUCE-RATIONALP-+))
     (15 15 (:REWRITE REDUCE-RATIONALP-*))
     (15 15 (:REWRITE RATIONALP-MINUS-X))
     (15 15 (:META META-RATIONALP-CORRECT))
     (12 12 (:TYPE-PRESCRIPTION ABS))
     (9 9
        (:REWRITE |(equal (floor (+ x y) z) x)|))
     (9 1 (:REWRITE MOD-ZERO . 1))
     (8 8
        (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
     (8 8
        (:REWRITE |(< (* (/ x) y) 1) with (< 0 x)|))
     (6 6 (:REWRITE |(+ (* c x) (* d x))|))
     (4 4 (:REWRITE MOD-X-Y-=-X . 1))
     (4 4 (:REWRITE FLOOR-X-Y-=--1 . 1))
     (4 4 (:REWRITE |(not (equal x (/ y)))|))
     (1 1 (:REWRITE MOD-ZERO . 2))
     (1 1 (:REWRITE FLOOR-ZERO . 1))
     (1 1 (:REWRITE FLOOR-POSITIVE . 4))
     (1 1 (:REWRITE FLOOR-POSITIVE . 3))
     (1 1 (:REWRITE FLOOR-POSITIVE . 2))
     (1 1 (:REWRITE FLOOR-POSITIVE . 1))
     (1 1 (:REWRITE FLOOR-NONPOSITIVE . 3))
     (1 1 (:REWRITE FLOOR-NONPOSITIVE . 2))
     (1 1 (:REWRITE FLOOR-NONPOSITIVE . 1))
     (1 1 (:REWRITE FLOOR-NONNEGATIVE . 3))
     (1 1 (:REWRITE FLOOR-NONNEGATIVE . 2))
     (1 1 (:REWRITE FLOOR-NONNEGATIVE . 1))
     (1 1 (:REWRITE FLOOR-NEGATIVE . 4))
     (1 1 (:REWRITE FLOOR-NEGATIVE . 3))
     (1 1 (:REWRITE FLOOR-NEGATIVE . 2))
     (1 1 (:REWRITE FLOOR-NEGATIVE . 1))
     (1 1 (:REWRITE |(mod (floor x y) z)| . 5))
     (1 1 (:REWRITE |(mod (floor x y) z)| . 4))
     (1 1 (:REWRITE |(mod (floor x y) z)| . 3))
     (1 1 (:REWRITE |(mod (floor x y) z)| . 2)))
(MOD-X+I*K-I*J
     (2232 73 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (2066 73 (:REWRITE MOD-X-Y-=-X . 4))
     (2001 1711 (:REWRITE DEFAULT-TIMES-2))
     (1910 2 (:REWRITE MOD-X-Y-=-X-Y . 1))
     (1807 58 (:REWRITE CANCEL-MOD-+))
     (1738 2 (:REWRITE MOD-X-Y-=-X+Y . 1))
     (1711 1711 (:REWRITE DEFAULT-TIMES-1))
     (1591 73 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (1478 73 (:REWRITE MOD-ZERO . 3))
     (1222 73 (:REWRITE DEFAULT-MOD-RATIO))
     (1146 286
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (1048 79 (:REWRITE |(* (- x) y)|))
     (1007 73 (:REWRITE MOD-ZERO . 4))
     (916 326 (:REWRITE DEFAULT-PLUS-2))
     (780 5 (:REWRITE CANCEL-FLOOR-+))
     (699 699 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (699 699 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (699 699 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (699 699
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (699 699
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (699 699
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (699 699
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (699 699
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (665 25 (:REWRITE FLOOR-=-X/Y . 3))
     (644 644
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (536 67 (:REWRITE |(/ (* x y))|))
     (521 401 (:REWRITE DEFAULT-LESS-THAN-1))
     (510 510 (:REWRITE DEFAULT-DIVIDE))
     (485 68 (:REWRITE |(integerp (- x))|))
     (473 326 (:REWRITE DEFAULT-PLUS-1))
     (427 427
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (415 25 (:REWRITE DEFAULT-FLOOR-RATIO))
     (402 262 (:META META-INTEGERP-CORRECT))
     (401 401
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (401 401
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (401 401
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (401 401 (:REWRITE DEFAULT-LESS-THAN-2))
     (386 386
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (386 386 (:REWRITE INTEGERP-<-CONSTANT))
     (386 386 (:REWRITE CONSTANT-<-INTEGERP))
     (386 386
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (386 386
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (386 386
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (386 386
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (386 386 (:REWRITE |(< c (- x))|))
     (386 386
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (386 386
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (386 386
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (386 386
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (386 386 (:REWRITE |(< (/ x) (/ y))|))
     (386 386 (:REWRITE |(< (- x) c)|))
     (386 386 (:REWRITE |(< (- x) (- y))|))
     (300 10 (:REWRITE FLOOR-ZERO . 5))
     (295 5 (:REWRITE FLOOR-ZERO . 3))
     (288 14 (:LINEAR MOD-BOUNDS-3))
     (264 264 (:REWRITE INTEGERP-MINUS-X))
     (230 10 (:REWRITE FLOOR-=-X/Y . 2))
     (179 179 (:REWRITE EXTRA-INTP-THM-1))
     (160 95
          (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-<))
     (160 10 (:REWRITE FLOOR-ZERO . 4))
     (155 10 (:REWRITE FLOOR-X-Y-=--1 . 2))
     (141 141 (:REWRITE |(< (/ x) 0)|))
     (141 141 (:REWRITE |(< (* x y) 0)|))
     (140 10 (:REWRITE FLOOR-X-Y-=-1 . 2))
     (139 139
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (139 139
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (135 95
          (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-<))
     (131 131 (:REWRITE |(< 0 (* x y))|))
     (130 10 (:REWRITE INTEGERP-/))
     (122 122
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (119 119
          (:REWRITE NORMALIZE-FACTORS-SCATTER-EXPONENTS))
     (116 116
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (116 116
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (116 116 (:REWRITE |(< 0 (/ x))|))
     (106 91 (:REWRITE |(equal (/ x) c)|))
     (91 91
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (91 91
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (91 91 (:REWRITE |(equal c (/ x))|))
     (91 91 (:REWRITE |(equal (/ x) (/ y))|))
     (91 91 (:REWRITE |(equal (- x) (- y))|))
     (91 91 (:REWRITE |(* c (* d x))|))
     (90 90
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (90 90 (:REWRITE DEFAULT-MINUS))
     (90 90 (:REWRITE |(equal c (- x))|))
     (90 90 (:REWRITE |(equal (- x) c)|))
     (73 73 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (73 73 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (73 73 (:REWRITE DEFAULT-MOD-2))
     (73 73 (:REWRITE DEFAULT-MOD-1))
     (73 73 (:REWRITE |(- (* c x))|))
     (72 72
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (58 58 (:REWRITE MOD-X-Y-=-X . 2))
     (58 58 (:REWRITE MOD-CANCEL-*-CONST))
     (58 58 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (58 58
         (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (56 56 (:REWRITE |(< (+ c/d x) y)|))
     (56 56 (:REWRITE |(< (+ (- c) x) y)|))
     (56 14 (:REWRITE RATIONALP-X))
     (47 27 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (46 46
         (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
     (43 43
         (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
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
         (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (43 43
         (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (39 39 (:REWRITE |arith (* c (* d x))|))
     (38 38 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
     (38 38
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (38 38
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (38 38
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (38 38
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (38 38
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (38 38
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (35 35 (:REWRITE MOD-X-I*J-V2))
     (30 30
         (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (28 28 (:LINEAR MOD-BOUNDS-2))
     (25 25 (:REWRITE DEFAULT-FLOOR-2))
     (25 25 (:REWRITE DEFAULT-FLOOR-1))
     (23 23 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (23 23 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (23 23
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (23 23
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (23 23
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (23 23
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (23 23
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (23 23
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (20 5 (:REWRITE |(floor (+ x r) i)|))
     (19 19
         (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (18 18 (:REWRITE |(+ c (+ d x))|))
     (15 15 (:REWRITE |(equal (* x y) 0)|))
     (15 15
         (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (15 15
         (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (15 15
         (:REWRITE |(< x (/ y)) with (< y 0)|))
     (15 15
         (:REWRITE |(< x (/ y)) with (< 0 y)|))
     (15 15
         (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (14 14 (:REWRITE REDUCE-RATIONALP-+))
     (14 14 (:REWRITE REDUCE-RATIONALP-*))
     (14 14 (:REWRITE RATIONALP-MINUS-X))
     (14 14 (:META META-RATIONALP-CORRECT))
     (13 13 (:REWRITE |(< y (+ (- c) x))|))
     (13 13 (:REWRITE |(< x (+ c/d y))|))
     (12 12 (:REWRITE |(equal (+ (- c) x) y)|))
     (10 10 (:REWRITE |arith (- (* c x))|))
     (10 10 (:REWRITE |arith (* (- x) y)|))
     (10 10 (:REWRITE FLOOR-X-Y-=-1 . 3))
     (10 10 (:REWRITE FLOOR-X-Y-=--1 . 3))
     (9 9 (:REWRITE FOLD-CONSTS-IN-+))
     (6 6
        (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-EQUAL))
     (6 6
        (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-EQUAL))
     (5 5 (:REWRITE FLOOR-ZERO . 2))
     (5 5
        (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 3))
     (5 5
        (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 2))
     (5 5 (:REWRITE |(- (- x))|))
     (4 1 (:REWRITE |(+ x x)|))
     (3 3 (:REWRITE ARITH-NORMALIZE-ADDENDS))
     (2 2
        (:REWRITE |(equal (mod (+ x y) z) x)|))
     (1 1 (:REWRITE MOD-X-Y-=-X . 1))
     (1 1 (:REWRITE |(not (equal x (/ y)))|))
     (1 1 (:REWRITE |(equal x (/ y))|))
     (1 1 (:REWRITE |(* x (- y))|)))
(FLOOR-X+I*K-I*J
     (8353 4 (:REWRITE FLOOR-=-X/Y . 4))
     (2781 56 (:REWRITE FLOOR-ZERO . 3))
     (2498 2388 (:REWRITE DEFAULT-TIMES-2))
     (2399 56 (:REWRITE CANCEL-FLOOR-+))
     (2388 2388 (:REWRITE DEFAULT-TIMES-1))
     (1896 56 (:REWRITE FLOOR-X-Y-=-1 . 2))
     (1876 61 (:REWRITE FLOOR-=-X/Y . 3))
     (1731 56 (:REWRITE FLOOR-=-X/Y . 2))
     (1616 56 (:REWRITE FLOOR-ZERO . 5))
     (1506 56 (:REWRITE FLOOR-ZERO . 4))
     (1505 541 (:META META-INTEGERP-CORRECT))
     (1352 61 (:REWRITE DEFAULT-FLOOR-RATIO))
     (1291 300 (:REWRITE DEFAULT-PLUS-2))
     (1203 353
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (1143 78 (:REWRITE |(* (- x) y)|))
     (1091 1091
           (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (967 56 (:REWRITE FLOOR-X-Y-=--1 . 2))
     (952 77 (:REWRITE |(integerp (- x))|))
     (928 928 (:REWRITE DEFAULT-DIVIDE))
     (892 300 (:REWRITE DEFAULT-PLUS-1))
     (680 680
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (668 21 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (622 21 (:REWRITE MOD-X-Y-=-X . 4))
     (589 479 (:REWRITE DEFAULT-LESS-THAN-1))
     (543 543 (:REWRITE INTEGERP-MINUS-X))
     (526 166 (:REWRITE INTEGERP-/))
     (479 479
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (479 479
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (479 479
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (479 479 (:REWRITE DEFAULT-LESS-THAN-2))
     (466 21 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (464 464
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (464 464 (:REWRITE INTEGERP-<-CONSTANT))
     (464 464 (:REWRITE CONSTANT-<-INTEGERP))
     (464 464
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (464 464
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (464 464
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (464 464
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (464 464 (:REWRITE |(< c (- x))|))
     (464 464
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (464 464
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (464 464
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (464 464
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (464 464 (:REWRITE |(< (/ x) (/ y))|))
     (464 464 (:REWRITE |(< (- x) c)|))
     (464 464 (:REWRITE |(< (- x) (- y))|))
     (457 457 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (457 457 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (457 457 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (457 457 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (457 457
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (457 457
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (457 457
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (457 457
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (457 457
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (412 12 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
     (412 12 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (404 16 (:REWRITE CANCEL-MOD-+))
     (373 21 (:REWRITE MOD-ZERO . 3))
     (364 364
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (364 364
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (364 364
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (364 364
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (364 364
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (364 364
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (359 359 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (359 359 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (359 359
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (359 359
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (359 359
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (359 359
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (303 21 (:REWRITE MOD-ZERO . 4))
     (295 295 (:REWRITE |(* c (* d x))|))
     (289 21 (:REWRITE DEFAULT-MOD-RATIO))
     (286 60
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (280 54
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (231 231 (:REWRITE EXTRA-INTP-THM-1))
     (224 224
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (170 105
          (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-<))
     (160 160 (:REWRITE |(< (/ x) 0)|))
     (160 160 (:REWRITE |(< (* x y) 0)|))
     (157 157
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (157 157
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (145 105
          (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-<))
     (141 141
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (136 136 (:REWRITE |(< 0 (* x y))|))
     (121 121
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (121 121
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (121 121
          (:REWRITE NORMALIZE-FACTORS-SCATTER-EXPONENTS))
     (121 121 (:REWRITE |(< 0 (/ x))|))
     (107 62 (:REWRITE |(equal (/ x) c)|))
     (85 17 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (78 78 (:REWRITE DEFAULT-MINUS))
     (77 77 (:REWRITE |(- (* c x))|))
     (72 18 (:REWRITE RATIONALP-X))
     (62 62
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (62 62
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (62 62 (:REWRITE |(equal c (/ x))|))
     (62 62 (:REWRITE |(equal (/ x) (/ y))|))
     (62 62 (:REWRITE |(equal (- x) (- y))|))
     (61 61 (:REWRITE DEFAULT-FLOOR-2))
     (61 61 (:REWRITE DEFAULT-FLOOR-1))
     (60 60
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (60 60 (:REWRITE |(equal c (- x))|))
     (60 60 (:REWRITE |(equal (- x) c)|))
     (58 58
         (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (56 56 (:REWRITE FLOOR-ZERO . 2))
     (56 56 (:REWRITE FLOOR-X-Y-=-1 . 3))
     (56 56 (:REWRITE FLOOR-X-Y-=--1 . 3))
     (56 56 (:REWRITE FLOOR-CANCEL-*-CONST))
     (52 4 (:LINEAR MOD-BOUNDS-3))
     (50 50
         (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
     (46 46
         (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (46 46 (:REWRITE |(floor x (- y))| . 2))
     (46 46 (:REWRITE |(floor x (- y))| . 1))
     (46 46
         (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
     (46 46
         (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
     (46 46 (:REWRITE |(floor (- x) y)| . 2))
     (46 46 (:REWRITE |(floor (- x) y)| . 1))
     (46 46
         (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
     (46 46
         (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
     (42 42 (:REWRITE |arith (* c (* d x))|))
     (40 40 (:REWRITE |(< (+ c/d x) y)|))
     (40 40 (:REWRITE |(< (+ (- c) x) y)|))
     (24 24
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (22 22
         (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
     (22 22
         (:REWRITE |(< (* (/ x) y) 1) with (< 0 x)|))
     (21 21 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (21 21 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (21 21 (:REWRITE DEFAULT-MOD-2))
     (21 21 (:REWRITE DEFAULT-MOD-1))
     (20 5 (:REWRITE |(floor (+ x r) i)|))
     (18 18 (:REWRITE REDUCE-RATIONALP-+))
     (18 18 (:REWRITE REDUCE-RATIONALP-*))
     (18 18 (:REWRITE RATIONALP-MINUS-X))
     (18 18 (:META META-RATIONALP-CORRECT))
     (16 16 (:REWRITE MOD-X-Y-=-X . 2))
     (16 16 (:REWRITE MOD-CANCEL-*-CONST))
     (16 16
         (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (16 16 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (16 16
         (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (15 15
         (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (15 15
         (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (15 15
         (:REWRITE |(< x (/ y)) with (< y 0)|))
     (15 15
         (:REWRITE |(< x (/ y)) with (< 0 y)|))
     (15 15
         (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (13 13 (:REWRITE |(+ c (+ d x))|))
     (11 11
         (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (11 11 (:REWRITE |(mod x (- y))| . 3))
     (11 11 (:REWRITE |(mod x (- y))| . 2))
     (11 11 (:REWRITE |(mod x (- y))| . 1))
     (11 11
         (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (11 11
         (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (11 11 (:REWRITE |(mod (- x) y)| . 3))
     (11 11 (:REWRITE |(mod (- x) y)| . 2))
     (11 11 (:REWRITE |(mod (- x) y)| . 1))
     (11 11
         (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (11 11
         (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (10 10 (:REWRITE |arith (- (* c x))|))
     (10 10 (:REWRITE |arith (* (- x) y)|))
     (10 10 (:REWRITE MOD-X-I*J-V2))
     (9 9 (:REWRITE FOLD-CONSTS-IN-+))
     (8 8 (:REWRITE |(< y (+ (- c) x))|))
     (8 8 (:REWRITE |(< x (+ c/d y))|))
     (8 8 (:LINEAR MOD-BOUNDS-2))
     (7 7 (:REWRITE |(equal (* x y) 0)|))
     (6 6
        (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-EQUAL))
     (6 6
        (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-EQUAL))
     (6 6 (:REWRITE |(equal (+ (- c) x) y)|))
     (5 5
        (:REWRITE |(floor (+ x y) z) where (< 0 z)| . 3))
     (5 5
        (:REWRITE |(floor (+ x y) z) where (< 0 z)| . 2))
     (3 3 (:REWRITE ARITH-NORMALIZE-ADDENDS))
     (3 3
        (:REWRITE |(equal (floor (+ x y) z) x)|))
     (1 1 (:REWRITE |(not (equal x (/ y)))|))
     (1 1 (:REWRITE |(equal x (/ y))|))
     (1 1 (:REWRITE |(* x (- y))|)))
(FLOOR-EQUAL-I-OVER-J-REWRITE
     (462 6 (:REWRITE FLOOR-ZERO . 3))
     (268 20
          (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-<-2))
     (213 213 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
     (213 213 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (213 213 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (213 213 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (213 213
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (213 213
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (213 213
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (213 213
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (213 213
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (213 213
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (213 213
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (213 213
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (213 213
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (213 213
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (213 213
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (213 213
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (178 6 (:REWRITE FLOOR-ZERO . 5))
     (178 6 (:REWRITE FLOOR-ZERO . 4))
     (175 73 (:REWRITE DEFAULT-TIMES-2))
     (172 6 (:REWRITE FLOOR-X-Y-=-1 . 3))
     (172 6 (:REWRITE FLOOR-X-Y-=-1 . 2))
     (172 6 (:REWRITE FLOOR-X-Y-=--1 . 3))
     (172 6 (:REWRITE FLOOR-X-Y-=--1 . 2))
     (115 13 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (115 13
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (77 9
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (74 6 (:REWRITE CANCEL-FLOOR-+))
     (73 73 (:REWRITE DEFAULT-TIMES-1))
     (48 48
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (48 48
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (48 48
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (48 48
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (48 48 (:REWRITE INTEGERP-<-CONSTANT))
     (48 48 (:REWRITE DEFAULT-LESS-THAN-2))
     (48 48 (:REWRITE DEFAULT-LESS-THAN-1))
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
     (46 46 (:REWRITE SIMPLIFY-SUMS-<))
     (46 46 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (42 7 (:REWRITE DEFAULT-FLOOR-RATIO))
     (39 6 (:REWRITE FLOOR-=-X/Y . 2))
     (38 4
         (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-EQUAL))
     (38 4
         (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-EQUAL))
     (36 9 (:REWRITE RATIONALP-X))
     (36 6 (:REWRITE |(* (- x) y)|))
     (33 33
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (33 33 (:REWRITE DEFAULT-DIVIDE))
     (28 28
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (27 27
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (26 26 (:REWRITE |(< (/ x) 0)|))
     (26 26 (:REWRITE |(< (* x y) 0)|))
     (24 24
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (24 24
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (24 24 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (22 22
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (22 22
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (22 22 (:REWRITE |(< 0 (/ x))|))
     (22 22 (:REWRITE |(< 0 (* x y))|))
     (20 20 (:REWRITE REDUCE-INTEGERP-+))
     (20 20 (:REWRITE INTEGERP-MINUS-X))
     (20 20 (:META META-INTEGERP-CORRECT))
     (18 18
         (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-<))
     (18 18
         (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-<))
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
     (12 12
         (:REWRITE NORMALIZE-FACTORS-SCATTER-EXPONENTS))
     (9 9 (:REWRITE REDUCE-RATIONALP-+))
     (9 9 (:REWRITE REDUCE-RATIONALP-*))
     (9 9 (:REWRITE RATIONALP-MINUS-X))
     (9 9 (:META META-RATIONALP-CORRECT))
     (8 2 (:REWRITE |(integerp (- x))|))
     (7 7
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (7 7 (:REWRITE DEFAULT-FLOOR-2))
     (7 7 (:REWRITE DEFAULT-FLOOR-1))
     (6 6 (:REWRITE FLOOR-ZERO . 2))
     (6 6
        (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
     (6 6
        (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (6 6 (:REWRITE FLOOR-CANCEL-*-CONST))
     (6 6 (:REWRITE DEFAULT-MINUS))
     (6 6 (:REWRITE |(floor x (- y))| . 2))
     (6 6 (:REWRITE |(floor x (- y))| . 1))
     (6 6
        (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
     (6 6
        (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
     (6 6 (:REWRITE |(floor (- x) y)| . 2))
     (6 6 (:REWRITE |(floor (- x) y)| . 1))
     (6 6
        (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
     (6 6
        (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
     (6 6
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (6 6
        (:REWRITE |(< (* x (/ y)) 0) rationalp (* x (/ y))|))
     (6 6 (:REWRITE |(- (* c x))|))
     (4 4 (:REWRITE |arith (* (- x) y)|))
     (4 4 (:REWRITE |(* 0 x)|))
     (2 2 (:REWRITE ARITH-NORMALIZE-ADDENDS))
     (2 2 (:LINEAR LINEAR-FLOOR-BOUNDS-2)))
(MOD-PLUS-MOD-N
     (26386 59 (:REWRITE MOD-X-Y-=-X-Y . 1))
     (18764 370 (:LINEAR MOD-BOUNDS-2))
     (18764 370 (:LINEAR MOD-BOUNDS-1))
     (17302 59 (:REWRITE MOD-X-Y-=-X+Y . 1))
     (2767 175 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (2767 175 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (2600 175 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (2600 175 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (2491 175 (:REWRITE MOD-ZERO . 4))
     (2438 185 (:LINEAR MOD-BOUNDS-3))
     (2373 2373 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (2373 2373 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (2373 2373 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (2373 2373
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (2373 2373
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (2373 2373
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (2373 2373
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (2029 175 (:REWRITE MOD-ZERO . 3))
     (1749 866 (:REWRITE DEFAULT-PLUS-2))
     (1669 1669 (:REWRITE DEFAULT-TIMES-2))
     (1669 1669 (:REWRITE DEFAULT-TIMES-1))
     (1512 177 (:REWRITE DEFAULT-MOD-RATIO))
     (1328 866 (:REWRITE DEFAULT-PLUS-1))
     (1284 1274 (:REWRITE DEFAULT-LESS-THAN-2))
     (1284 1274 (:REWRITE DEFAULT-LESS-THAN-1))
     (1274 1274
           (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (1274 1274
           (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (1274 1274
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (1274 1274
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (1274 1274 (:REWRITE INTEGERP-<-CONSTANT))
     (1274 1274 (:REWRITE CONSTANT-<-INTEGERP))
     (1274 1274
           (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (1274 1274
           (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (1274 1274
           (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (1274 1274
           (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (1274 1274 (:REWRITE |(< c (- x))|))
     (1274 1274
           (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (1274 1274
           (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (1274 1274
           (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (1274 1274
           (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (1274 1274 (:REWRITE |(< (/ x) (/ y))|))
     (1274 1274 (:REWRITE |(< (- x) c)|))
     (1274 1274 (:REWRITE |(< (- x) (- y))|))
     (1271 343
           (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-EQUAL))
     (1183 343
           (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-EQUAL))
     (1059 1014
           (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-<))
     (1034 1014
           (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-<))
     (823 823
          (:REWRITE NORMALIZE-FACTORS-SCATTER-EXPONENTS))
     (724 724 (:REWRITE DEFAULT-DIVIDE))
     (723 723
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (572 562 (:META META-INTEGERP-CORRECT))
     (564 564 (:REWRITE INTEGERP-MINUS-X))
     (552 552
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (552 552
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (552 552 (:REWRITE |(< 0 (/ x))|))
     (552 552 (:REWRITE |(< 0 (* x y))|))
     (550 169 (:REWRITE MOD-X-Y-=-X . 2))
     (550 169
          (:REWRITE |(mod (+ x (mod a b)) y)|))
     (550 169
          (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (546 546
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (546 546
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (546 546 (:REWRITE |(< (/ x) 0)|))
     (546 546 (:REWRITE |(< (* x y) 0)|))
     (472 472 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (469 454 (:REWRITE |(equal (/ x) c)|))
     (454 454
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (454 454
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (454 454 (:REWRITE |(equal c (/ x))|))
     (454 454 (:REWRITE |(equal (/ x) (/ y))|))
     (454 454 (:REWRITE |(equal (- x) (- y))|))
     (453 453
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (453 453 (:REWRITE |(equal c (- x))|))
     (453 453 (:REWRITE |(equal (- x) c)|))
     (385 110
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (336 336
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (299 299
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (254 254
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (204 14 (:REWRITE MOD-ZERO . 2))
     (177 177 (:REWRITE DEFAULT-MOD-2))
     (177 177 (:REWRITE DEFAULT-MOD-1))
     (174 174 (:REWRITE DEFAULT-MINUS))
     (166 166
          (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (166 166
          (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (166 166 (:REWRITE MOD-CANCEL-*-CONST))
     (166 166 (:REWRITE |(mod x (- y))| . 3))
     (166 166 (:REWRITE |(mod x (- y))| . 2))
     (166 166 (:REWRITE |(mod x (- y))| . 1))
     (166 166
          (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (166 166
          (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (166 166 (:REWRITE |(mod (- x) y)| . 3))
     (166 166 (:REWRITE |(mod (- x) y)| . 2))
     (166 166 (:REWRITE |(mod (- x) y)| . 1))
     (166 166
          (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (166 166
          (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (162 82 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (131 131 (:REWRITE |(- (* c x))|))
     (126 14 (:REWRITE MOD-ZERO . 1))
     (120 120 (:REWRITE |(equal (+ (- c) x) y)|))
     (112 112
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (59 59
         (:REWRITE |(equal (mod (+ x y) z) x)|))
     (56 56 (:REWRITE |(+ c (+ d x))|))
     (48 48 (:REWRITE ARITH-NORMALIZE-ADDENDS))
     (44 44
         (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (43 43 (:REWRITE FOLD-CONSTS-IN-+))
     (33 33 (:REWRITE |(< (+ c/d x) y)|))
     (33 33 (:REWRITE |(< (+ (- c) x) y)|))
     (30 30 (:REWRITE |(< y (+ (- c) x))|))
     (30 30 (:REWRITE |(< x (+ c/d y))|))
     (16 4 (:REWRITE |(+ x x)|))
     (15 15
         (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 3))
     (15 15
         (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 2))
     (14 14
         (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 3))
     (14 14
         (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 2))
     (12 12 (:REWRITE EXTRA-INTP-THM-1))
     (8 8 (:REWRITE |arith (+ c (+ d x))|))
     (6 6 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
     (6 6 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (6 6 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (6 6 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (6 6
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (6 6
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (6 6
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (6 6
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (6 6
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (6 6
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (6 6
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (6 6
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (6 6
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (6 6
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (6 6
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (6 6
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (4 1 (:REWRITE RATIONALP-X))
     (2 2 (:REWRITE |(* x (- y))|))
     (1 1 (:REWRITE REDUCE-RATIONALP-+))
     (1 1 (:REWRITE REDUCE-RATIONALP-*))
     (1 1 (:REWRITE RATIONALP-MINUS-X))
     (1 1 (:REWRITE |(not (equal x (/ y)))|))
     (1 1 (:REWRITE |(equal x (/ y))|))
     (1 1 (:REWRITE |(/ (/ x))|))
     (1 1 (:META META-RATIONALP-CORRECT)))
(MOD-MULT-N
     (20730 160 (:LINEAR MOD-BOUNDS-1))
     (18689 40 (:REWRITE MOD-X-Y-=-X-Y . 1))
     (10625 40 (:REWRITE MOD-X-Y-=-X+Y . 1))
     (8151 77 (:REWRITE |(equal (+ (- c) x) y)|))
     (3271 112 (:REWRITE MOD-X-Y-=-X . 4))
     (3156 113 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (3111 112 (:REWRITE MOD-X-Y-=-X . 3))
     (3035 113 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (2384 160 (:LINEAR MOD-BOUNDS-2))
     (1693 113 (:REWRITE MOD-ZERO . 4))
     (1157 1157 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (1157 1157
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (1157 1157
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (1157 1157
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (1157 1157
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (1156 1156 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (1156 1156
           (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (946 80 (:LINEAR MOD-BOUNDS-3))
     (940 278 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (812 236
          (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-<-2))
     (766 196 (:REWRITE RATIONALP-X))
     (632 278
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (606 70 (:REWRITE ACL2-NUMBERP-X))
     (598 598 (:REWRITE INTEGERP-MINUS-X))
     (597 597 (:META META-INTEGERP-CORRECT))
     (572 572 (:REWRITE DEFAULT-LESS-THAN-2))
     (572 572 (:REWRITE DEFAULT-LESS-THAN-1))
     (570 570
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (570 570
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (568 568 (:REWRITE INTEGERP-<-CONSTANT))
     (568 568 (:REWRITE CONSTANT-<-INTEGERP))
     (568 568
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (568 568
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (568 568
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (568 568
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (568 568 (:REWRITE |(< c (- x))|))
     (568 568
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (568 568
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (568 568
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (568 568
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (568 568 (:REWRITE |(< (/ x) (/ y))|))
     (568 568 (:REWRITE |(< (- x) c)|))
     (568 568 (:REWRITE |(< (- x) (- y))|))
     (560 560
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (539 113 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (539 113 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (470 318 (:REWRITE DEFAULT-DIVIDE))
     (444 344 (:REWRITE DEFAULT-PLUS-2))
     (436 109 (:REWRITE |(integerp (- x))|))
     (412 103 (:REWRITE |(mod x 1)|))
     (378 344 (:REWRITE DEFAULT-PLUS-1))
     (345 345
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (345 345
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (340 324
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (330 330 (:REWRITE |(equal c (/ x))|))
     (330 330 (:REWRITE |(equal (/ x) (/ y))|))
     (330 330 (:REWRITE |(equal (- x) (- y))|))
     (325 236
          (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-<))
     (314 66
          (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-EQUAL))
     (311 311
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (311 311 (:REWRITE |(equal c (- x))|))
     (311 311 (:REWRITE |(equal (- x) c)|))
     (309 111
          (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (296 112 (:REWRITE MOD-X-Y-=-X . 2))
     (296 112
          (:REWRITE |(mod (+ x (mod a b)) y)|))
     (296 112
          (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (291 291
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (279 279 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (245 111 (:REWRITE MOD-CANCEL-*-CONST))
     (245 111
          (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (245 111
          (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (240 240
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (236 236
          (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-<))
     (234 234 (:REWRITE |(< (/ x) 0)|))
     (230 230
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (230 230
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (225 15 (:REWRITE |(* x (- y))|))
     (196 196 (:REWRITE REDUCE-RATIONALP-+))
     (196 196 (:REWRITE REDUCE-RATIONALP-*))
     (196 196 (:REWRITE RATIONALP-MINUS-X))
     (196 196 (:META META-RATIONALP-CORRECT))
     (176 16 (:REWRITE |(+ x (if a b c))|))
     (173 173 (:REWRITE |(< 0 (/ x))|))
     (171 171
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (171 171
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (132 132 (:REWRITE DEFAULT-MINUS))
     (113 113
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (111 111
          (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (111 111 (:REWRITE |(mod x (- y))| . 3))
     (111 111 (:REWRITE |(mod x (- y))| . 2))
     (111 111 (:REWRITE |(mod x (- y))| . 1))
     (111 111
          (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (111 111 (:REWRITE |(mod (- x) y)| . 3))
     (111 111 (:REWRITE |(mod (- x) y)| . 2))
     (111 111 (:REWRITE |(mod (- x) y)| . 1))
     (111 111
          (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (101 37
          (:REWRITE |(equal (mod (+ x y) z) x)|))
     (96 32 (:REWRITE |(+ (if a b c) x)|))
     (92 92
         (:REWRITE NORMALIZE-FACTORS-SCATTER-EXPONENTS))
     (41 41
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (34 34 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (24 24
         (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
     (22 11
         (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (22 11
         (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (19 19 (:REWRITE |(not (equal x (/ y)))|))
     (19 19 (:REWRITE |(equal x (/ y))|))
     (10 10 (:REWRITE ARITH-NORMALIZE-ADDENDS))
     (8 8 (:REWRITE |(equal (* x y) 0)|))
     (8 8 (:REWRITE |(< (+ c/d x) y)|))
     (8 8 (:REWRITE |(- (if a b c))|))
     (6 6 (:REWRITE |(< (+ (- c) x) y)|))
     (4 4 (:REWRITE |arith (* c (* d x))|))
     (3 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
     (3 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (3 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (3 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (3 3 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (2 2 (:REWRITE |arith (- (* c x))|))
     (2 2 (:REWRITE |arith (* (- x) y)|))
     (2 2 (:REWRITE |(< y (+ (- c) x))|))
     (2 2 (:REWRITE |(< x (+ c/d y))|))
     (1 1 (:REWRITE FOLD-CONSTS-IN-+)))
(MOD-THEOREM-ONE-A
     (7114 21 (:REWRITE MOD-X-Y-=-X-Y . 1))
     (4636 64
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (4036 140 (:LINEAR MOD-BOUNDS-2))
     (4036 140 (:LINEAR MOD-BOUNDS-1))
     (3690 21 (:REWRITE MOD-X-Y-=-X+Y . 1))
     (3396 70 (:LINEAR MOD-BOUNDS-3))
     (2785 2105
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (2785 2105
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (2760 2080 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (2105 2105 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (2105 2105
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (2105 2105
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (1913 945 (:REWRITE DEFAULT-TIMES-1))
     (1880 945 (:REWRITE DEFAULT-TIMES-2))
     (1672 27 (:REWRITE MOD-X-Y-=-X . 4))
     (1672 27 (:REWRITE MOD-X-Y-=-X . 3))
     (1581 357 (:META META-INTEGERP-CORRECT))
     (1143 28 (:REWRITE MOD-ZERO . 4))
     (827 57 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (817 29 (:REWRITE DEFAULT-MOD-RATIO))
     (746 284 (:REWRITE DEFAULT-PLUS-2))
     (612 40
          (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-EQUAL))
     (612 40
          (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-EQUAL))
     (466 284 (:REWRITE DEFAULT-PLUS-1))
     (456 379 (:REWRITE DEFAULT-LESS-THAN-2))
     (456 379 (:REWRITE DEFAULT-LESS-THAN-1))
     (453 24
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (379 379
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (379 379
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (379 379
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (379 379
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (379 379 (:REWRITE INTEGERP-<-CONSTANT))
     (379 379 (:REWRITE CONSTANT-<-INTEGERP))
     (379 379
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (379 379
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (379 379
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (379 379
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (379 379 (:REWRITE |(< c (- x))|))
     (379 379
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (379 379
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (379 379
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (379 379
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (379 379 (:REWRITE |(< (/ x) (/ y))|))
     (379 379 (:REWRITE |(< (- x) c)|))
     (379 379 (:REWRITE |(< (- x) (- y))|))
     (360 247
          (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-<))
     (358 358 (:REWRITE INTEGERP-MINUS-X))
     (335 247
          (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-<))
     (317 317
          (:REWRITE NORMALIZE-FACTORS-SCATTER-EXPONENTS))
     (315 28 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (315 28 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (308 28 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (308 28 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (192 126
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (182 182 (:REWRITE DEFAULT-DIVIDE))
     (181 181
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (181 181
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (181 181
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (181 181 (:REWRITE |(< 0 (/ x))|))
     (181 181 (:REWRITE |(< 0 (* x y))|))
     (181 27 (:REWRITE MOD-X-Y-=-X . 2))
     (181 27 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (181 27
          (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (174 174
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (174 174
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (174 174 (:REWRITE |(< (/ x) 0)|))
     (174 174 (:REWRITE |(< (* x y) 0)|))
     (156 96 (:REWRITE INTEGERP-/))
     (123 123 (:REWRITE |(* c (* d x))|))
     (117 40 (:REWRITE DEFAULT-MINUS))
     (106 29 (:REWRITE DEFAULT-MOD-1))
     (102 25
          (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (102 25 (:REWRITE MOD-CANCEL-*-CONST))
     (102 25
          (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (102 25
          (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (101 101
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (99 99
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (98 21
         (:REWRITE |(equal (mod (+ x y) z) x)|))
     (95 95 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (80 65 (:REWRITE |(equal (/ x) c)|))
     (72 18 (:REWRITE RATIONALP-X))
     (65 65
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (65 65
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (65 65 (:REWRITE |(equal c (/ x))|))
     (65 65 (:REWRITE |(equal (/ x) (/ y))|))
     (65 65 (:REWRITE |(equal (- x) (- y))|))
     (64 64
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (64 64 (:REWRITE |(equal c (- x))|))
     (64 64 (:REWRITE |(equal (- x) c)|))
     (36 36
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (31 31 (:REWRITE |(- (* c x))|))
     (29 29 (:REWRITE DEFAULT-MOD-2))
     (28 28 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (28 28
         (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
     (25 25
         (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (25 25 (:REWRITE |(mod x (- y))| . 3))
     (25 25 (:REWRITE |(mod x (- y))| . 2))
     (25 25 (:REWRITE |(mod x (- y))| . 1))
     (25 25
         (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (25 25 (:REWRITE |(mod (- x) y)| . 3))
     (25 25 (:REWRITE |(mod (- x) y)| . 2))
     (25 25 (:REWRITE |(mod (- x) y)| . 1))
     (25 25
         (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (23 23 (:REWRITE |(equal (+ (- c) x) y)|))
     (18 18 (:REWRITE REDUCE-RATIONALP-+))
     (18 18 (:REWRITE REDUCE-RATIONALP-*))
     (18 18 (:REWRITE RATIONALP-MINUS-X))
     (18 18 (:META META-RATIONALP-CORRECT))
     (17 17 (:REWRITE |(equal (* x y) 0)|))
     (17 17
         (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (17 17
         (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (14 14 (:REWRITE |(< (+ c/d x) y)|))
     (14 14 (:REWRITE |(< (+ (- c) x) y)|))
     (14 14 (:REWRITE |(+ c (+ d x))|))
     (11 11 (:REWRITE |(< y (+ (- c) x))|))
     (11 11 (:REWRITE |(< x (+ c/d y))|))
     (6 6 (:REWRITE ARITH-NORMALIZE-ADDENDS))
     (5 5 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (4 4 (:REWRITE FOLD-CONSTS-IN-+))
     (3 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
     (3 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (3 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (3 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (2 2 (:REWRITE EXTRA-INTP-THM-1))
     (2 2 (:REWRITE |(* x (- y))|))
     (1 1 (:REWRITE |(not (equal x (/ y)))|))
     (1 1 (:REWRITE |(equal x (/ y))|))
     (1 1 (:REWRITE |(/ (/ x))|)))
(MOD-THEOREM-ONE-B
     (6144 18 (:REWRITE MOD-X-Y-=-X-Y . 1))
     (3998 56
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (3544 124 (:LINEAR MOD-BOUNDS-2))
     (3544 124 (:LINEAR MOD-BOUNDS-1))
     (3186 18 (:REWRITE MOD-X-Y-=-X+Y . 1))
     (2974 62 (:LINEAR MOD-BOUNDS-3))
     (2490 1890
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (2490 1890
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (2465 1865 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (1890 1890 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (1890 1890
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (1890 1890
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (1699 885 (:REWRITE DEFAULT-TIMES-2))
     (1699 885 (:REWRITE DEFAULT-TIMES-1))
     (1484 24 (:REWRITE MOD-X-Y-=-X . 4))
     (1484 24 (:REWRITE MOD-X-Y-=-X . 3))
     (1386 314 (:META META-INTEGERP-CORRECT))
     (1000 25 (:REWRITE MOD-ZERO . 4))
     (727 26 (:REWRITE DEFAULT-MOD-RATIO))
     (710 50 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (672 276 (:REWRITE DEFAULT-PLUS-2))
     (612 40
          (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-EQUAL))
     (612 40
          (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-EQUAL))
     (435 276 (:REWRITE DEFAULT-PLUS-1))
     (403 337 (:REWRITE DEFAULT-LESS-THAN-2))
     (403 337 (:REWRITE DEFAULT-LESS-THAN-1))
     (360 247
          (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-<))
     (337 337
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (337 337
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (337 337
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (337 337
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (337 337 (:REWRITE INTEGERP-<-CONSTANT))
     (337 337 (:REWRITE CONSTANT-<-INTEGERP))
     (337 337
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (337 337
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (337 337
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (337 337
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (337 337 (:REWRITE |(< c (- x))|))
     (337 337
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (337 337
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (337 337
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (337 337
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (337 337 (:REWRITE |(< (/ x) (/ y))|))
     (337 337 (:REWRITE |(< (- x) c)|))
     (337 337 (:REWRITE |(< (- x) (- y))|))
     (335 247
          (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-<))
     (317 317
          (:REWRITE NORMALIZE-FACTORS-SCATTER-EXPONENTS))
     (315 315 (:REWRITE INTEGERP-MINUS-X))
     (302 16
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (285 25 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (285 25 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (278 25 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (278 25 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (165 165 (:REWRITE DEFAULT-DIVIDE))
     (164 164
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (160 160
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (160 160
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (160 160 (:REWRITE |(< 0 (/ x))|))
     (160 160 (:REWRITE |(< 0 (* x y))|))
     (156 24 (:REWRITE MOD-X-Y-=-X . 2))
     (156 24 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (156 24
          (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (153 153
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (153 153
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (153 153 (:REWRITE |(< (/ x) 0)|))
     (153 153 (:REWRITE |(< (* x y) 0)|))
     (138 84 (:REWRITE INTEGERP-/))
     (128 84
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (109 109 (:REWRITE |(* c (* d x))|))
     (102 36 (:REWRITE DEFAULT-MINUS))
     (96 96
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (92 26 (:REWRITE DEFAULT-MOD-1))
     (89 89 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (88 22
         (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (88 22 (:REWRITE MOD-CANCEL-*-CONST))
     (88 22
         (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (88 22
         (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (84 18
         (:REWRITE |(equal (mod (+ x y) z) x)|))
     (72 57 (:REWRITE |(equal (/ x) c)|))
     (66 66
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (64 16 (:REWRITE RATIONALP-X))
     (57 57
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (57 57
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (57 57 (:REWRITE |(equal c (/ x))|))
     (57 57 (:REWRITE |(equal (/ x) (/ y))|))
     (57 57 (:REWRITE |(equal (- x) (- y))|))
     (56 56
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (56 56 (:REWRITE |(equal c (- x))|))
     (56 56 (:REWRITE |(equal (- x) c)|))
     (32 32
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (28 28
         (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
     (28 28 (:REWRITE |(- (* c x))|))
     (27 27 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (26 26 (:REWRITE DEFAULT-MOD-2))
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
     (20 20 (:REWRITE |(equal (+ (- c) x) y)|))
     (16 16 (:REWRITE REDUCE-RATIONALP-+))
     (16 16 (:REWRITE REDUCE-RATIONALP-*))
     (16 16 (:REWRITE RATIONALP-MINUS-X))
     (16 16 (:META META-RATIONALP-CORRECT))
     (15 15 (:REWRITE |(equal (* x y) 0)|))
     (15 15
         (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (15 15
         (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (14 14 (:REWRITE |(< (+ c/d x) y)|))
     (14 14 (:REWRITE |(< (+ (- c) x) y)|))
     (13 13 (:REWRITE |(+ c (+ d x))|))
     (11 11 (:REWRITE |(< y (+ (- c) x))|))
     (11 11 (:REWRITE |(< x (+ c/d y))|))
     (6 6 (:REWRITE ARITH-NORMALIZE-ADDENDS))
     (5 5 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (4 4 (:REWRITE FOLD-CONSTS-IN-+))
     (3 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
     (3 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (3 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (3 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (2 2 (:REWRITE EXTRA-INTP-THM-1))
     (2 2 (:REWRITE |(* x (- y))|))
     (1 1 (:REWRITE |(not (equal x (/ y)))|))
     (1 1 (:REWRITE |(equal x (/ y))|))
     (1 1 (:REWRITE |(/ (/ x))|)))
(IND-FN)
(MOD-THEOREM-TWO-HELPER-HELPER
     (8400 8400
           (:REWRITE NORMALIZE-FACTORS-SCATTER-EXPONENTS))
     (5544 830
           (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-EQUAL))
     (5512 830
           (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-EQUAL))
     (2310 1990
           (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-<))
     (2214 1990
           (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-<))
     (1438 1438 (:REWRITE |(- (* c x))|))
     (1420 1420 (:REWRITE DEFAULT-MOD-2))
     (1375 1375 (:REWRITE EXTRA-INTP-THM-1))
     (1270 1270
           (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (1270 1270 (:REWRITE |(mod x (- y))| . 3))
     (1270 1270 (:REWRITE |(mod x (- y))| . 2))
     (1270 1270 (:REWRITE |(mod x (- y))| . 1))
     (1270 1270 (:REWRITE |(mod (- x) y)| . 3))
     (1270 1270 (:REWRITE |(mod (- x) y)| . 2))
     (1249 1249
           (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (1249 1249
           (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (1191 1191
           (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (1154 346 (:REWRITE MOD-ZERO . 2))
     (684 524 (:REWRITE DEFAULT-EXPT-1))
     (524 524 (:REWRITE DEFAULT-EXPT-2))
     (518 518 (:REWRITE |(expt 1/c n)|))
     (518 518 (:REWRITE |(expt (- x) n)|))
     (443 443 (:REWRITE ZP-OPEN))
     (352 176 (:REWRITE RATIONALP-X))
     (232 232 (:REWRITE |(+ c (+ d x))|))
     (176 176 (:REWRITE REDUCE-RATIONALP-+))
     (176 176 (:REWRITE REDUCE-RATIONALP-*))
     (176 176 (:REWRITE RATIONALP-MINUS-X))
     (176 176 (:META META-RATIONALP-CORRECT))
     (168 168
          (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (119 119
          (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
     (107 107 (:REWRITE |(equal (+ (- c) x) y)|))
     (105 105 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
     (105 105 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (105 105 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (105 105 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (105 105
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (105 105
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (105 105
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (105 105
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (105 105
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (96 96
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (87 87
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (87 87
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (80 80 (:REWRITE |arith (expt x c)|))
     (80 80 (:REWRITE |arith (expt 1/c n)|))
     (78 78
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (73 73 (:REWRITE FOLD-CONSTS-IN-+))
     (63 63 (:REWRITE |(< (+ c/d x) y)|))
     (63 63 (:REWRITE |(< (+ (- c) x) y)|))
     (52 52 (:REWRITE |(< y (+ (- c) x))|))
     (52 52 (:REWRITE |(< x (+ c/d y))|))
     (52 6 (:REWRITE NOT-INTEGERP-/-1))
     (41 41
         (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 3))
     (41 41
         (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 2))
     (39 39 (:REWRITE ARITH-NORMALIZE-ADDENDS))
     (39 39
         (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 3))
     (39 39
         (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 2))
     (29 6 (:REWRITE NOT-INTEGERP-/-2))
     (15 15 (:REWRITE |arith (* c (* d x))|))
     (12 12 (:REWRITE MOD-POSITIVE . 3))
     (12 12 (:REWRITE MOD-POSITIVE . 2))
     (12 12 (:REWRITE MOD-NEGATIVE . 3))
     (12 12 (:REWRITE MOD-NEGATIVE . 2))
     (8 8 (:REWRITE |(not (equal x (/ y)))|))
     (8 8 (:REWRITE |(equal x (/ y))|))
     (4 4 (:REWRITE |arith (- (* c x))|))
     (3 3
        (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (3 3
        (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (3 3
        (:REWRITE |(< x (/ y)) with (< y 0)|)))
(MOD-THEOREM-TWO-HELPER
 (980 6 (:REWRITE MOD-ZERO . 4))
 (838 6 (:REWRITE MOD-X-Y-=-X-Y . 1))
 (758 6 (:REWRITE CANCEL-MOD-+))
 (708 6 (:REWRITE MOD-X-Y-=-X . 4))
 (708 6 (:REWRITE MOD-X-Y-=-X . 3))
 (672 18
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (475 6 (:REWRITE MOD-X-Y-=-X+Y . 1))
 (449 449
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (449
  449
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (449 449
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (449 449
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (449 449
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (449
     449
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (449 449
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (449 449
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (441 441 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (441 441 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (441 441 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (441 441
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (441 441
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (441 441
      (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (441 441
      (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
 (441 441
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (441 441
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (441 441 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (414 57 (:REWRITE DEFAULT-TIMES-1))
 (397 8 (:LINEAR MOD-BOUNDS-3))
 (391 57 (:REWRITE DEFAULT-TIMES-2))
 (370 16 (:LINEAR MOD-BOUNDS-2))
 (370 16 (:LINEAR MOD-BOUNDS-1))
 (313 6 (:REWRITE MOD-ZERO . 3))
 (292 2 (:REWRITE |(equal (expt x n) 0)|))
 (266 2
      (:REWRITE |(expt x (+ m n)) non-zero x|))
 (261 6 (:REWRITE DEFAULT-MOD-RATIO))
 (261 6 (:REWRITE |(* (- x) y)|))
 (255 6 (:REWRITE |(integerp (- x))|))
 (254 18
      (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-EQUAL))
 (205 5 (:REWRITE |(* (* x y) z)|))
 (168 17 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (120 34
      (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-<))
 (120 34 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (112 6 (:REWRITE MOD-X-Y-=-X . 2))
 (112 6 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (112 6
      (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (102 19 (:META META-INTEGERP-CORRECT))
 (96 10 (:REWRITE DEFAULT-PLUS-2))
 (77 34 (:REWRITE DEFAULT-LESS-THAN-2))
 (77 34 (:REWRITE DEFAULT-LESS-THAN-1))
 (70 6 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (70 6 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (70 6 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (70 6 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (62 6
     (:REWRITE |(equal (mod (+ x y) z) x)|))
 (61 9 (:REWRITE DEFAULT-EXPT-1))
 (60 8 (:LINEAR EXPT-X->=-X))
 (60 8 (:LINEAR EXPT-X->-X))
 (60 8 (:LINEAR EXPT->=-1-TWO))
 (60 8 (:LINEAR EXPT->=-1-ONE))
 (60 8 (:LINEAR EXPT->-1-TWO))
 (60 8 (:LINEAR EXPT->-1-ONE))
 (60 8 (:LINEAR EXPT-<=-1-TWO))
 (60 8 (:LINEAR EXPT-<=-1-ONE))
 (60 8 (:LINEAR EXPT-<-1-TWO))
 (60 8 (:LINEAR EXPT-<-1-ONE))
 (60 7 (:REWRITE DEFAULT-MINUS))
 (59 6
     (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (59 6 (:REWRITE DEFAULT-MOD-1))
 (59 6
     (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (59 6
     (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (51 3 (:REWRITE INTEGERP-/))
 (49 6 (:REWRITE MOD-CANCEL-*-CONST))
 (45 6 (:REWRITE NORMALIZE-ADDENDS))
 (34 34 (:REWRITE SIMPLIFY-SUMS-<))
 (34 34
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (34 34
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (34 34
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (34 34
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
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
 (31 31
     (:REWRITE NORMALIZE-FACTORS-SCATTER-EXPONENTS))
 (31 10 (:REWRITE DEFAULT-PLUS-1))
 (30 2 (:REWRITE |(+ y x)|))
 (28 28
     (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (25 1 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
 (22 22
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (22 22 (:REWRITE DEFAULT-DIVIDE))
 (20 20
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (20 20
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (20 20 (:REWRITE |(equal c (/ x))|))
 (20 20 (:REWRITE |(equal c (- x))|))
 (20 20 (:REWRITE |(equal (/ x) c)|))
 (20 20 (:REWRITE |(equal (/ x) (/ y))|))
 (20 20 (:REWRITE |(equal (- x) c)|))
 (20 20 (:REWRITE |(equal (- x) (- y))|))
 (19 19 (:REWRITE REDUCE-INTEGERP-+))
 (19 19 (:REWRITE INTEGERP-MINUS-X))
 (18 18
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (17 17
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (17 17
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (17 17
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (17 17
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (17 17 (:REWRITE |(< 0 (/ x))|))
 (17 17 (:REWRITE |(< 0 (* x y))|))
 (17 17 (:REWRITE |(< (/ x) 0)|))
 (17 17 (:REWRITE |(< (* x y) 0)|))
 (16 16
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (16 16
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (16 16
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (16 16
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (11 3 (:REWRITE MOD-ZERO . 1))
 (11 1 (:REWRITE |(+ 0 x)|))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (10 10 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (9 9 (:REWRITE DEFAULT-EXPT-2))
 (8 8 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (8 8 (:LINEAR EXPT-LINEAR-UPPER-<))
 (8 8 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (8 8 (:LINEAR EXPT-LINEAR-LOWER-<))
 (7 7 (:REWRITE EXTRA-INTP-THM-1))
 (7 7 (:REWRITE |(expt 1/c n)|))
 (7 7 (:REWRITE |(expt (- x) n)|))
 (6 6
    (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (6 6 (:REWRITE DEFAULT-MOD-2))
 (6 6 (:REWRITE |(mod x (- y))| . 3))
 (6 6 (:REWRITE |(mod x (- y))| . 2))
 (6 6 (:REWRITE |(mod x (- y))| . 1))
 (6 6
    (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (6 6 (:REWRITE |(mod (- x) y)| . 3))
 (6 6 (:REWRITE |(mod (- x) y)| . 2))
 (6 6 (:REWRITE |(mod (- x) y)| . 1))
 (6 6
    (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (6 6 (:REWRITE |(- (* c x))|))
 (5 5
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (5 5 (:REWRITE |(* c (* d x))|))
 (3 3 (:REWRITE MOD-ZERO . 2))
 (3 3 (:REWRITE |(equal (+ (- c) x) y)|))
 (2 2 (:DEFINITION FIX))
 (1 1 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE |(equal (* x y) 0)|))
 (1 1
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (1 1
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (1 1 (:REWRITE |(+ x (- x))|))
 (1 1 (:REWRITE |(+ c (+ d x))|)))
(MOD-THEOREM-TWO
 (5134 19 (:REWRITE MOD-X-Y-=-X-Y . 1))
 (4517 25 (:REWRITE MOD-ZERO . 4))
 (3328 54
       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (3049 25 (:REWRITE MOD-X-Y-=-X . 3))
 (2970 25 (:REWRITE MOD-X-Y-=-X . 4))
 (2716 19 (:REWRITE MOD-X-Y-=-X+Y . 1))
 (2692 52 (:LINEAR MOD-BOUNDS-3))
 (2636 104 (:LINEAR MOD-BOUNDS-2))
 (2636 104 (:LINEAR MOD-BOUNDS-1))
 (2126 24 (:REWRITE CANCEL-MOD-+))
 (1432 1432 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (1432 1432 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (1432 1432 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (1432 1432
       (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (1432 1432
       (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (1432 1432
       (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (1432 1432
       (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
 (1432 1432
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (1432 1432
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (1432 1432
       (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (1394 10 (:REWRITE |(equal (expt x n) 0)|))
 (1338 1338
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (1338
  1338
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1338 1338
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (1338 1338
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (1338
      1338
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1338
     1338
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1338 1338
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1338 1338
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (1325 183 (:REWRITE DEFAULT-TIMES-1))
 (1225 62 (:REWRITE |(* y x)|))
 (1160 183 (:REWRITE DEFAULT-TIMES-2))
 (1121 25 (:REWRITE MOD-ZERO . 3))
 (775 54
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (717 25 (:REWRITE DEFAULT-MOD-RATIO))
 (689 24 (:REWRITE |(integerp (- x))|))
 (649 24 (:REWRITE |(* (- x) y)|))
 (548 192
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (529 50 (:REWRITE DEFAULT-PLUS-2))
 (504 51 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (449 192
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (381 25 (:REWRITE MOD-X-Y-=-X . 2))
 (381 25
      (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (371 193 (:REWRITE DEFAULT-LESS-THAN-2))
 (371 193 (:REWRITE DEFAULT-LESS-THAN-1))
 (300 40 (:LINEAR EXPT-X->=-X))
 (300 40 (:LINEAR EXPT-X->-X))
 (300 40 (:LINEAR EXPT->=-1-TWO))
 (300 40 (:LINEAR EXPT->=-1-ONE))
 (300 40 (:LINEAR EXPT->-1-TWO))
 (300 40 (:LINEAR EXPT->-1-ONE))
 (300 40 (:LINEAR EXPT-<=-1-TWO))
 (300 40 (:LINEAR EXPT-<=-1-ONE))
 (300 40 (:LINEAR EXPT-<-1-TWO))
 (300 40 (:LINEAR EXPT-<-1-ONE))
 (244 50 (:REWRITE DEFAULT-PLUS-1))
 (224 25 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (224 25 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (224 25 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (224 25 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (203 25 (:REWRITE DEFAULT-MOD-1))
 (193 193
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (193 193
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (193 193
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (193 193
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (193 193 (:REWRITE INTEGERP-<-CONSTANT))
 (193 193 (:REWRITE CONSTANT-<-INTEGERP))
 (193 193
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (193 193
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (193 193
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (193 193
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (193 193 (:REWRITE |(< c (- x))|))
 (193 193
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (193 193
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (193 193
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (193 193
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (193 193 (:REWRITE |(< (/ x) (/ y))|))
 (193 193 (:REWRITE |(< (- x) c)|))
 (193 193 (:REWRITE |(< (- x) (- y))|))
 (192 192 (:REWRITE SIMPLIFY-SUMS-<))
 (192 27 (:REWRITE DEFAULT-MINUS))
 (189 24
      (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (189 24 (:REWRITE MOD-CANCEL-*-CONST))
 (189 24
      (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (189 24
      (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (153 3 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
 (148 19
      (:REWRITE |(equal (mod (+ x y) z) x)|))
 (132 80
      (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (132 80
      (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (120 16 (:REWRITE DEFAULT-EXPT-1))
 (102 6 (:REWRITE INTEGERP-/))
 (101 101
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (101 101 (:REWRITE DEFAULT-DIVIDE))
 (100 66
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (95 95
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (95 95
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (95 95 (:REWRITE |(< 0 (/ x))|))
 (95 95 (:REWRITE |(< 0 (* x y))|))
 (94 94 (:REWRITE |(< (/ x) 0)|))
 (94 94 (:REWRITE |(< (* x y) 0)|))
 (93 93
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (93 93
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (89 89
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (80 80
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (80 80
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (76 76 (:REWRITE REDUCE-INTEGERP-+))
 (76 76 (:REWRITE INTEGERP-MINUS-X))
 (76 76 (:META META-INTEGERP-CORRECT))
 (66 66
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (64 64 (:REWRITE |(equal c (/ x))|))
 (64 64 (:REWRITE |(equal c (- x))|))
 (64 64 (:REWRITE |(equal (/ x) c)|))
 (64 64 (:REWRITE |(equal (/ x) (/ y))|))
 (64 64 (:REWRITE |(equal (- x) c)|))
 (64 64 (:REWRITE |(equal (- x) (- y))|))
 (54 54
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (51 51 (:REWRITE EXTRA-INTP-THM-1))
 (50 4 (:REWRITE |(mod (+ 1 x) y)|))
 (48 48
     (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (40 40 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (40 40 (:LINEAR EXPT-LINEAR-UPPER-<))
 (40 40 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (40 40 (:LINEAR EXPT-LINEAR-LOWER-<))
 (29 29
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (25 25 (:REWRITE DEFAULT-MOD-2))
 (24 24
     (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (24 24 (:REWRITE |(mod x (- y))| . 3))
 (24 24 (:REWRITE |(mod x (- y))| . 2))
 (24 24 (:REWRITE |(mod x (- y))| . 1))
 (24 24
     (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (24 24 (:REWRITE |(mod (- x) y)| . 3))
 (24 24 (:REWRITE |(mod (- x) y)| . 2))
 (24 24 (:REWRITE |(mod (- x) y)| . 1))
 (24 24
     (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (21 21
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (20 20 (:REWRITE |(- (* c x))|))
 (17 4 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (16 16 (:REWRITE DEFAULT-EXPT-2))
 (16 16 (:REWRITE |(expt 1/c n)|))
 (16 16 (:REWRITE |(expt (- x) n)|))
 (10 10 (:REWRITE MOD-ZERO . 2))
 (10 10 (:REWRITE MOD-ZERO . 1))
 (9 9 (:REWRITE |(equal (+ (- c) x) y)|))
 (8 4 (:REWRITE |(* -1 x)|))
 (6 6 (:REWRITE |(* 1 x)|))
 (3 3 (:REWRITE |(< y (+ (- c) x))|))
 (3 3 (:REWRITE |(< x (+ c/d y))|))
 (1 1 (:REWRITE MOD-POSITIVE . 3))
 (1 1 (:REWRITE MOD-POSITIVE . 2))
 (1 1 (:REWRITE MOD-POSITIVE . 1))
 (1 1 (:REWRITE MOD-NONPOSITIVE))
 (1 1 (:REWRITE MOD-NONNEGATIVE))
 (1 1 (:REWRITE MOD-NEGATIVE . 3))
 (1 1 (:REWRITE MOD-NEGATIVE . 2))
 (1 1 (:REWRITE MOD-NEGATIVE . 1))
 (1 1 (:REWRITE |(< (+ c/d x) y)|))
 (1 1 (:REWRITE |(< (+ (- c) x) y)|)))
(TWO-XXX
 (28096 6 (:REWRITE MOD-X-Y-=-X-Y . 1))
 (20806 6 (:REWRITE MOD-X-Y-=-X+Y . 1))
 (14886 83 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (14423 19
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (13118 80 (:REWRITE CANCEL-MOD-+))
 (11971 80 (:REWRITE MOD-X-Y-=-X . 3))
 (11277 1604 (:REWRITE DEFAULT-TIMES-2))
 (9843
  9843
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (9843
      9843
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (9843
     9843
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (9843 9843
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (9843 9843
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (7976 80 (:REWRITE MOD-ZERO . 3))
 (5020 969 (:REWRITE DEFAULT-PLUS-2))
 (4965 83 (:REWRITE DEFAULT-MOD-RATIO))
 (4689 4689
       (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (4415 1604 (:REWRITE DEFAULT-TIMES-1))
 (3775 36 (:LINEAR MOD-BOUNDS-3))
 (3371 338 (:REWRITE DEFAULT-DIVIDE))
 (3219 240
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (3116 260 (:META META-INTEGERP-CORRECT))
 (2573 31 (:REWRITE |(integerp (expt x n))|))
 (2502 80 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (2502 80
       (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (2488 110 (:REWRITE |(* (- x) y)|))
 (2443 73 (:REWRITE |(integerp (- x))|))
 (2266 496 (:REWRITE DEFAULT-LESS-THAN-2))
 (2236 969 (:REWRITE DEFAULT-PLUS-1))
 (2072 748 (:REWRITE DEFAULT-MINUS))
 (2052 9 (:REWRITE MOD-X-I*J))
 (1906 80 (:REWRITE MOD-X-Y-=-X . 4))
 (1903 132 (:LINEAR EXPT-X->-X))
 (1895 755 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (1895 755 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (1888 273 (:REWRITE INTEGERP-MINUS-X))
 (1855 755
       (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (1855 755
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (1796 80 (:REWRITE MOD-ZERO . 4))
 (1795 132 (:LINEAR EXPT-X->=-X))
 (1785 83 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (1785 83 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (1782 80 (:REWRITE MOD-X-Y-=-X . 2))
 (1548 72 (:LINEAR MOD-BOUNDS-2))
 (1392 232 (:REWRITE |(- (+ x y))|))
 (1389 428 (:REWRITE |(< (- x) c)|))
 (1105 496 (:REWRITE DEFAULT-LESS-THAN-1))
 (1013 154 (:REWRITE ODD-EXPT-THM))
 (903 80 (:REWRITE MOD-CANCEL-*-CONST))
 (880 32 (:LINEAR LINEAR-FLOOR-BOUNDS-1))
 (852 12 (:REWRITE BUBBLE-DOWN-*-BUBBLE-DOWN))
 (830 83 (:REWRITE DEFAULT-MOD-2))
 (755 755 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (755 755
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (755 755
      (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (755 755
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (747 747 (:REWRITE DEFAULT-EXPT-2))
 (747 747 (:REWRITE DEFAULT-EXPT-1))
 (733 733 (:REWRITE |(expt 1/c n)|))
 (733 733 (:REWRITE |(expt (- x) n)|))
 (714 428
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (681 154
      (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-<))
 (643 154
      (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-<))
 (619 138 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (586 4 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (585 16
      (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (580 17
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (580 4 (:REWRITE FLOOR-ZERO . 3))
 (550 77
      (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (546 73
      (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (546 73
      (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (546 4 (:REWRITE FLOOR-ZERO . 4))
 (541 373 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (520 520
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (503 491
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (503 491
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (498 50 (:REWRITE DEFAULT-FLOOR-RATIO))
 (490 1 (:REWRITE EVEN-AND-ODD-ALTERNATE))
 (485 373
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (485 373
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (485 373
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (437 428 (:REWRITE |(< (- x) (- y))|))
 (436 4 (:REWRITE CANCEL-FLOOR-+))
 (429 373 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (429 373 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (429 373
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (429 373
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (429 373
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (429 373
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (429 373
      (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (429 373
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (429 373
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (428 428
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (428 428
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (428 428
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (428 428
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (428 428 (:REWRITE |(< c (- x))|))
 (428 428
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (428 428
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (428 428
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (428 428 (:REWRITE |(< (/ x) (/ y))|))
 (397 397
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (397 397 (:REWRITE INTEGERP-<-CONSTANT))
 (397 397 (:REWRITE CONSTANT-<-INTEGERP))
 (396 99 (:REWRITE |(- (* c x))|))
 (396 9 (:REWRITE |(* (- (/ c)) (expt d n))|))
 (385 73
      (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (385 73
      (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (346 11 (:REWRITE |(< (+ (- c) x) y)|))
 (338 132 (:LINEAR EXPT-<=-1-TWO))
 (333 46 (:REWRITE |(floor x 2)| . 2))
 (306 9 (:REWRITE |(* (/ c) (expt d n))|))
 (272 16 (:REWRITE |(* x (expt x n))|))
 (268 4 (:REWRITE FLOOR-=-X/Y . 3))
 (264 264
      (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (264 264
      (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (264 264
      (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (260 4 (:REWRITE FLOOR-=-X/Y . 2))
 (223 223 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (171 9 (:REWRITE MOD-X-I*J-V2))
 (164 164 (:REWRITE |(< 0 (* x y))|))
 (162 162
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (162 162
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (162 162 (:REWRITE |(< 0 (/ x))|))
 (143 83 (:REWRITE DEFAULT-MOD-1))
 (138 2 (:REWRITE |(+ x x)|))
 (132 132 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (132 132 (:LINEAR EXPT-LINEAR-UPPER-<))
 (132 132 (:LINEAR EXPT-LINEAR-LOWER-<))
 (132 132 (:LINEAR EXPT->=-1-TWO))
 (132 132 (:LINEAR EXPT->-1-TWO))
 (132 132 (:LINEAR EXPT-<=-1-ONE))
 (132 132 (:LINEAR EXPT-<-1-TWO))
 (132 132 (:LINEAR EXPT-<-1-ONE))
 (127 127 (:REWRITE |(* c (* d x))|))
 (116 65 (:REWRITE |(< x (+ c/d y))|))
 (86 50 (:REWRITE DEFAULT-FLOOR-2))
 (84 4 (:REWRITE FLOOR-ZERO . 2))
 (84 4 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (84 4 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (84 4 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (73 73 (:REWRITE |(mod x (- y))| . 3))
 (73 73 (:REWRITE |(mod x (- y))| . 2))
 (73 73 (:REWRITE |(mod x (- y))| . 1))
 (73 73 (:REWRITE |(mod (- x) y)| . 3))
 (73 73 (:REWRITE |(mod (- x) y)| . 2))
 (73 73 (:REWRITE |(mod (- x) y)| . 1))
 (61 61 (:REWRITE |(< (* x y) 0)|))
 (60 6
     (:REWRITE |(equal (mod (+ x y) z) x)|))
 (57 57 (:REWRITE |(< (/ x) 0)|))
 (52 52 (:REWRITE EXTRA-INTP-THM-1))
 (50 50 (:REWRITE DEFAULT-FLOOR-1))
 (48 4 (:REWRITE FLOOR-ZERO . 5))
 (48 4
     (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (48 4 (:REWRITE FLOOR-CANCEL-*-CONST))
 (48 4
     (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (48 4
     (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (40 21
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (36 36 (:TYPE-PRESCRIPTION RATIONALP-MOD))
 (35 20 (:REWRITE |(equal (/ x) c)|))
 (31 31 (:REWRITE |(- (- x))|))
 (29 20 (:REWRITE |(equal (- x) (- y))|))
 (26 26
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (26 26
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (25 25 (:TYPE-PRESCRIPTION ABS))
 (22 21
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (20 20 (:REWRITE |(equal c (/ x))|))
 (20 20 (:REWRITE |(equal (/ x) (/ y))|))
 (19 19
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (19 19 (:REWRITE |(equal c (- x))|))
 (19 19 (:REWRITE |(equal (- x) c)|))
 (16 16 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (16 16 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (12 12 (:REWRITE |arith (expt x c)|))
 (12 12 (:REWRITE |arith (expt 1/c n)|))
 (12 12 (:REWRITE BUBBLE-DOWN-*-MATCH-3))
 (10 10 (:REWRITE FOLD-CONSTS-IN-+))
 (10 10 (:REWRITE |(equal (+ (- c) x) y)|))
 (7 7
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (6 6
    (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
 (5 5 (:REWRITE |(< y (+ (- c) x))|))
 (5 5
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (4 4
    (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (4 4 (:REWRITE FLOOR-ZERO . 1))
 (4 4 (:REWRITE FLOOR-POSITIVE . 4))
 (4 4 (:REWRITE FLOOR-POSITIVE . 3))
 (4 4 (:REWRITE FLOOR-POSITIVE . 2))
 (4 4 (:REWRITE FLOOR-POSITIVE . 1))
 (4 4 (:REWRITE FLOOR-NONPOSITIVE . 3))
 (4 4 (:REWRITE FLOOR-NONPOSITIVE . 2))
 (4 4 (:REWRITE FLOOR-NONPOSITIVE . 1))
 (4 4
    (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (4 4 (:REWRITE FLOOR-=-X/Y . 4))
 (4 4 (:REWRITE |(mod (floor x y) z)| . 5))
 (4 4 (:REWRITE |(mod (floor x y) z)| . 4))
 (4 4 (:REWRITE |(mod (floor x y) z)| . 3))
 (4 4 (:REWRITE |(mod (floor x y) z)| . 2))
 (4 4 (:REWRITE |(floor x (- y))| . 2))
 (4 4 (:REWRITE |(floor x (- y))| . 1))
 (4 4
    (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (4 4 (:REWRITE |(floor (- x) y)| . 2))
 (4 4 (:REWRITE |(floor (- x) y)| . 1))
 (4 4
    (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (4 4
    (:REWRITE |(equal (floor (+ x y) z) x)|))
 (4 1 (:REWRITE RATIONALP-X))
 (2 2
    (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-EQUAL))
 (2 2
    (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-EQUAL))
 (2 2 (:REWRITE MOD-X-Y-=-X . 1))
 (2 2 (:REWRITE |(equal x (/ y))|))
 (1 1 (:REWRITE REDUCE-RATIONALP-+))
 (1 1 (:REWRITE REDUCE-RATIONALP-*))
 (1 1 (:REWRITE RATIONALP-MINUS-X))
 (1 1 (:REWRITE |(not (equal x (/ y)))|))
 (1 1
    (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 3))
 (1 1
    (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 2))
 (1 1 (:REWRITE |(/ (/ x))|))
 (1 1 (:META META-RATIONALP-CORRECT)))
(MOD-THEOREM-THREE
 (3032 3 (:REWRITE MOD-X-Y-=-X-Y . 1))
 (2496 8 (:LINEAR MOD-BOUNDS-3))
 (2330 20 (:REWRITE |(* (* x y) z)|))
 (1882 156 (:REWRITE DEFAULT-TIMES-2))
 (1831 23
       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (1731 9 (:REWRITE CANCEL-MOD-+))
 (1578 3 (:REWRITE MOD-X-Y-=-X+Y . 1))
 (1212 60 (:META META-INTEGERP-CORRECT))
 (1180 156 (:REWRITE DEFAULT-TIMES-1))
 (1107 9 (:REWRITE MOD-ZERO . 3))
 (1099 9 (:REWRITE MOD-X-Y-=-X . 4))
 (1099 9 (:REWRITE MOD-X-Y-=-X . 3))
 (1050 9 (:REWRITE MOD-ZERO . 4))
 (956 20 (:REWRITE |(* y (* x z))|))
 (800 16 (:LINEAR MOD-BOUNDS-2))
 (800 16 (:LINEAR MOD-BOUNDS-1))
 (702 9 (:REWRITE DEFAULT-MOD-RATIO))
 (702 9 (:REWRITE |(* (- x) y)|))
 (675 675
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (675
  675
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (675 675
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (675 675
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (675 675
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (675
     675
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (675 675
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (675 675
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (616 616 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (616 616 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (616 616 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (616 616
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (616 616
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (616 616
      (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (616 616
      (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
 (616 616
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (616 616
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (608 9 (:REWRITE |(integerp (- x))|))
 (370 10 (:REWRITE |(integerp (expt x n))|))
 (324 23
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (242 54
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (242 54 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (197 9 (:REWRITE MOD-X-Y-=-X . 2))
 (197 9 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (197 9
      (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (195 22 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (148 54 (:REWRITE DEFAULT-LESS-THAN-2))
 (148 54 (:REWRITE DEFAULT-LESS-THAN-1))
 (146 8 (:REWRITE DEFAULT-PLUS-2))
 (112 16 (:REWRITE INTEGERP-/))
 (104 10 (:REWRITE DEFAULT-MINUS))
 (103 9
      (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (103 9 (:REWRITE MOD-CANCEL-*-CONST))
 (103 9 (:REWRITE DEFAULT-MOD-1))
 (103 9
      (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (103 9
      (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (82 2 (:REWRITE |(equal (expt x n) 0)|))
 (77 77
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (76 4 (:REWRITE NORMALIZE-ADDENDS))
 (73 9 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (73 9 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (73 9 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (73 9 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (68 3
     (:REWRITE |(equal (mod (+ x y) z) x)|))
 (60 60 (:REWRITE REDUCE-INTEGERP-+))
 (60 60 (:REWRITE INTEGERP-MINUS-X))
 (54 54 (:REWRITE SIMPLIFY-SUMS-<))
 (54 54
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (54 54
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (54 54
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (54 54
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
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
 (52 2 (:REWRITE |(+ y x)|))
 (51 8 (:REWRITE DEFAULT-PLUS-1))
 (47 1 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
 (40 7 (:REWRITE DEFAULT-EXPT-1))
 (33 33
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (33 33 (:REWRITE DEFAULT-DIVIDE))
 (27 27
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (27 27
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (27 27
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (27 27
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (27 27 (:REWRITE |(< 0 (/ x))|))
 (27 27 (:REWRITE |(< 0 (* x y))|))
 (27 27 (:REWRITE |(< (/ x) 0)|))
 (27 27 (:REWRITE |(< (* x y) 0)|))
 (25 25
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (25 25
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (25 25 (:REWRITE |(equal c (/ x))|))
 (25 25 (:REWRITE |(equal c (- x))|))
 (25 25 (:REWRITE |(equal (/ x) c)|))
 (25 25 (:REWRITE |(equal (/ x) (/ y))|))
 (25 25 (:REWRITE |(equal (- x) c)|))
 (25 25 (:REWRITE |(equal (- x) (- y))|))
 (23 23
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (22 1 (:REWRITE |(+ 0 x)|))
 (20 20 (:REWRITE EXTRA-INTP-THM-1))
 (20 20 (:REWRITE |(* c (* d x))|))
 (16 16
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (16 16
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (16 16
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (16 16
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (14 14 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (13 13
     (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (11 11
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (9 9
    (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (9 9 (:REWRITE DEFAULT-MOD-2))
 (9 9 (:REWRITE |(mod x (- y))| . 3))
 (9 9 (:REWRITE |(mod x (- y))| . 2))
 (9 9 (:REWRITE |(mod x (- y))| . 1))
 (9 9
    (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (9 9 (:REWRITE |(mod (- x) y)| . 3))
 (9 9 (:REWRITE |(mod (- x) y)| . 2))
 (9 9 (:REWRITE |(mod (- x) y)| . 1))
 (9 9
    (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (9 9 (:REWRITE |(- (* c x))|))
 (8 8 (:LINEAR EXPT-X->=-X))
 (8 8 (:LINEAR EXPT-X->-X))
 (8 8 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (8 8 (:LINEAR EXPT-LINEAR-UPPER-<))
 (8 8 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (8 8 (:LINEAR EXPT-LINEAR-LOWER-<))
 (8 8 (:LINEAR EXPT->=-1-TWO))
 (8 8 (:LINEAR EXPT->=-1-ONE))
 (8 8 (:LINEAR EXPT->-1-TWO))
 (8 8 (:LINEAR EXPT->-1-ONE))
 (8 8 (:LINEAR EXPT-<=-1-TWO))
 (8 8 (:LINEAR EXPT-<=-1-ONE))
 (8 8 (:LINEAR EXPT-<-1-TWO))
 (8 8 (:LINEAR EXPT-<-1-ONE))
 (7 7 (:REWRITE DEFAULT-EXPT-2))
 (7 7 (:REWRITE |(expt 1/c n)|))
 (7 7 (:REWRITE |(expt (- x) n)|))
 (4 4 (:REWRITE |(equal (* x y) 0)|))
 (4 4
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (4 4
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (3 3
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (3 3 (:REWRITE |(equal (+ (- c) x) y)|))
 (2 2 (:DEFINITION FIX))
 (1 1 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (1 1 (:REWRITE |(+ x (- x))|))
 (1 1 (:REWRITE |(+ c (+ d x))|)))
(MOD-MULT-2
     (348 4 (:LINEAR MOD-BOUNDS-2))
     (344 4 (:LINEAR MOD-BOUNDS-1))
     (280 40 (:REWRITE ACL2-NUMBERP-X))
     (192 8 (:REWRITE |(* x (if a b c))|))
     (176 24 (:REWRITE DEFAULT-DIVIDE))
     (164 20 (:REWRITE DEFAULT-LESS-THAN-2))
     (160 16 (:REWRITE DEFAULT-LESS-THAN-1))
     (120 30 (:REWRITE RATIONALP-X))
     (106 106 (:REWRITE DEFAULT-TIMES-1))
     (42 1 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (42 1 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (42 1 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (42 1 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (33 2 (:REWRITE DEFAULT-MOD-RATIO))
     (31 31 (:REWRITE REDUCE-INTEGERP-+))
     (31 31 (:REWRITE INTEGERP-MINUS-X))
     (31 31 (:META META-INTEGERP-CORRECT))
     (30 30 (:REWRITE REDUCE-RATIONALP-+))
     (30 30 (:REWRITE REDUCE-RATIONALP-*))
     (30 30 (:REWRITE RATIONALP-MINUS-X))
     (30 30 (:META META-RATIONALP-CORRECT))
     (29 1 (:REWRITE MOD-ZERO . 4))
     (20 2 (:LINEAR MOD-BOUNDS-3))
     (19 19 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (19 19
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (19 19
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (19 19
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (19 19
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (18 18 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (18 18 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (18 18 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (18 18 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
     (16 16
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (13 1 (:REWRITE |(* (if a b c) x)|))
     (12 12 (:REWRITE SIMPLIFY-SUMS-<))
     (12 12
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (12 12
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (12 12
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (12 12
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (12 12
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (12 12 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
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
     (11 2
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (8 8 (:REWRITE |(* 0 x)|))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (6 6 (:REWRITE |(< 0 (/ x))|))
     (6 6 (:REWRITE |(< 0 (* x y))|))
     (6 6 (:REWRITE |(< (/ x) 0)|))
     (6 6 (:REWRITE |(< (* x y) 0)|))
     (3 2
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (2 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (2 2
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (2 2
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (2 2
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (2 2 (:REWRITE DEFAULT-MOD-1))
     (2 2 (:REWRITE |(equal c (/ x))|))
     (2 2 (:REWRITE |(equal c (- x))|))
     (2 2 (:REWRITE |(equal (/ x) c)|))
     (2 2 (:REWRITE |(equal (/ x) (/ y))|))
     (2 2 (:REWRITE |(equal (- x) c)|))
     (2 2 (:REWRITE |(equal (- x) (- y))|))
     (1 1
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (1 1 (:REWRITE |(equal (* x y) 0)|)))
(MOD-PROD (116 4 (:LINEAR MOD-BOUNDS-2))
          (116 4 (:LINEAR MOD-BOUNDS-1))
          (108 4 (:REWRITE |(* (* x y) z)|))
          (84 2 (:LINEAR MOD-BOUNDS-3))
          (81 6 (:REWRITE DEFAULT-MOD-RATIO))
          (78 45 (:REWRITE DEFAULT-TIMES-2))
          (60 60 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
          (60 60
              (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
          (60 60
              (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
          (60 60
              (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
          (60 60
              (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
          (60 3 (:REWRITE MOD-X-Y-=-X . 4))
          (60 3 (:REWRITE MOD-X-Y-=-X . 3))
          (59 59 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
          (59 59 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
          (59 59 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
          (58 3 (:REWRITE MOD-X-Y-=-X-Y . 3))
          (58 3 (:REWRITE MOD-X-Y-=-X-Y . 2))
          (58 3 (:REWRITE MOD-X-Y-=-X+Y . 3))
          (58 3 (:REWRITE MOD-X-Y-=-X+Y . 2))
          (52 3 (:REWRITE MOD-ZERO . 3))
          (45 45 (:REWRITE DEFAULT-TIMES-1))
          (32 4 (:REWRITE |(/ (* x y))|))
          (30 3 (:REWRITE MOD-ZERO . 4))
          (30 3 (:REWRITE MOD-X-Y-=-X . 2))
          (30 3 (:REWRITE CANCEL-MOD-+))
          (30 3 (:REWRITE |(mod (+ x (mod a b)) y)|))
          (30 3
              (:REWRITE |(mod (+ x (- (mod a b))) y)|))
          (28 1 (:REWRITE MOD-X-I*J))
          (23 23
              (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
          (21 21 (:REWRITE SIMPLIFY-SUMS-<))
          (21 21
              (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
          (21 21
              (:REWRITE REMOVE-STRICT-INEQUALITIES))
          (21 21
              (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
          (21 21
              (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
          (21 21
              (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
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
          (20 20 (:REWRITE DEFAULT-DIVIDE))
          (18 18
              (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
          (18 18
              (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
          (18 18 (:REWRITE |(equal c (/ x))|))
          (18 18 (:REWRITE |(equal (/ x) (/ y))|))
          (18 18 (:REWRITE |(equal (- x) (- y))|))
          (17 17
              (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
          (17 17 (:REWRITE SIMPLIFY-SUMS-EQUAL))
          (17 17
              (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
          (17 17
              (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
          (17 17
              (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
          (17 17 (:REWRITE |(equal c (- x))|))
          (17 17 (:REWRITE |(equal (- x) c)|))
          (13 13
              (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
          (12 3 (:REWRITE RATIONALP-X))
          (11 11
              (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
          (11 11
              (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
          (11 11 (:REWRITE |(< 0 (/ x))|))
          (11 11 (:REWRITE |(< 0 (* x y))|))
          (10 10
              (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
          (10 10
              (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
          (10 10 (:REWRITE |(< (/ x) 0)|))
          (10 10 (:REWRITE |(< (* x y) 0)|))
          (10 4 (:REWRITE |(* (if a b c) x)|))
          (8 8 (:REWRITE REDUCE-INTEGERP-+))
          (8 8 (:REWRITE INTEGERP-MINUS-X))
          (8 8 (:META META-INTEGERP-CORRECT))
          (7 7
             (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
          (7 7
             (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
          (6 6 (:REWRITE DEFAULT-MOD-2))
          (6 6 (:REWRITE DEFAULT-MOD-1))
          (5 5 (:REWRITE |(equal (* x y) 0)|))
          (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
          (4 4 (:REWRITE |(* c (* d x))|))
          (4 1 (:REWRITE MOD-X-I*J-V2))
          (3 3 (:REWRITE REDUCE-RATIONALP-+))
          (3 3 (:REWRITE REDUCE-RATIONALP-*))
          (3 3 (:REWRITE RATIONALP-MINUS-X))
          (3 3 (:REWRITE MOD-CANCEL-*-CONST))
          (3 3 (:META META-RATIONALP-CORRECT))
          (3 1 (:REWRITE |(/ (if a b c))|))
          (2 2
             (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
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
             (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
          (2 2
             (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
          (1 1 (:REWRITE |(not (equal x (/ y)))|))
          (1 1 (:REWRITE |(equal x (/ y))|)))
(MOD-MULT
     (4630 18 (:REWRITE MOD-X-Y-=-X-Y . 1))
     (3176 108 (:LINEAR MOD-BOUNDS-2))
     (3176 108 (:LINEAR MOD-BOUNDS-1))
     (2759 109
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (2370 18 (:REWRITE MOD-X-Y-=-X+Y . 1))
     (1774 54 (:LINEAR MOD-BOUNDS-3))
     (1028 1028 (:REWRITE DEFAULT-TIMES-2))
     (1028 1028 (:REWRITE DEFAULT-TIMES-1))
     (727 20 (:REWRITE DEFAULT-MOD-RATIO))
     (612 546 (:REWRITE DEFAULT-PLUS-2))
     (595 595 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (595 595 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (595 595 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (595 595
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (595 595
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (595 595
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (595 595
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (574 546 (:REWRITE DEFAULT-PLUS-1))
     (367 103 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (337 337
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (337 337
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (337 337
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (337 337
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (337 337 (:REWRITE INTEGERP-<-CONSTANT))
     (337 337 (:REWRITE DEFAULT-LESS-THAN-2))
     (337 337 (:REWRITE DEFAULT-LESS-THAN-1))
     (337 337 (:REWRITE CONSTANT-<-INTEGERP))
     (337 337
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (337 337
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (337 337
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (337 337
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (337 337 (:REWRITE |(< c (- x))|))
     (337 337
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (337 337
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (337 337
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (337 337
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (337 337 (:REWRITE |(< (/ x) (/ y))|))
     (337 337 (:REWRITE |(< (- x) c)|))
     (337 337 (:REWRITE |(< (- x) (- y))|))
     (301 81
          (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-EQUAL))
     (301 81
          (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-EQUAL))
     (280 19 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (280 19 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (274 19 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (274 19 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (272 247
          (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-<))
     (268 19 (:REWRITE MOD-ZERO . 4))
     (247 247
          (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-<))
     (224 224
          (:REWRITE NORMALIZE-FACTORS-SCATTER-EXPONENTS))
     (182 6
          (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 1))
     (182 6
          (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 1))
     (168 168
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (160 160
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (160 160
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (160 160 (:REWRITE |(< 0 (/ x))|))
     (160 160 (:REWRITE |(< 0 (* x y))|))
     (153 153
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (153 153
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (153 153 (:REWRITE |(< (/ x) 0)|))
     (153 153 (:REWRITE |(< (* x y) 0)|))
     (145 145 (:REWRITE DEFAULT-DIVIDE))
     (144 144
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (138 28
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (125 110 (:REWRITE |(equal (/ x) c)|))
     (110 110
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (110 110
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (110 110 (:REWRITE |(equal c (/ x))|))
     (110 110 (:REWRITE |(equal (/ x) (/ y))|))
     (110 110 (:REWRITE |(equal (- x) (- y))|))
     (109 109
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (109 109 (:REWRITE |(equal c (- x))|))
     (109 109 (:REWRITE |(equal (- x) c)|))
     (102 102 (:REWRITE REDUCE-INTEGERP-+))
     (102 102 (:REWRITE INTEGERP-MINUS-X))
     (102 102 (:META META-INTEGERP-CORRECT))
     (98 16 (:REWRITE MOD-X-Y-=-X . 2))
     (98 16 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (98 16
         (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (89 89 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (85 85
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (84 84
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (68 17 (:REWRITE RATIONALP-X))
     (34 34
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (34 34 (:REWRITE |(+ c (+ d x))|))
     (29 29 (:REWRITE |(equal (+ (- c) x) y)|))
     (28 28 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (24 24 (:REWRITE FOLD-CONSTS-IN-+))
     (24 24 (:REWRITE |(< (+ c/d x) y)|))
     (24 24 (:REWRITE |(< (+ (- c) x) y)|))
     (21 21 (:REWRITE |(< y (+ (- c) x))|))
     (21 21 (:REWRITE |(< x (+ c/d y))|))
     (20 20 (:REWRITE DEFAULT-MOD-2))
     (20 20 (:REWRITE DEFAULT-MOD-1))
     (20 20 (:REWRITE DEFAULT-MINUS))
     (20 20 (:REWRITE ARITH-NORMALIZE-ADDENDS))
     (18 18
         (:REWRITE |(equal (mod (+ x y) z) x)|))
     (18 4 (:REWRITE |(+ (if a b c) x)|))
     (17 17 (:REWRITE REDUCE-RATIONALP-+))
     (17 17 (:REWRITE REDUCE-RATIONALP-*))
     (17 17 (:REWRITE RATIONALP-MINUS-X))
     (17 17 (:META META-RATIONALP-CORRECT))
     (14 14
         (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
     (12 12
         (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (12 12
         (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (12 12 (:REWRITE MOD-CANCEL-*-CONST))
     (12 12 (:REWRITE |(mod x (- y))| . 3))
     (12 12 (:REWRITE |(mod x (- y))| . 2))
     (12 12 (:REWRITE |(mod x (- y))| . 1))
     (12 12
         (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (12 12
         (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (12 12 (:REWRITE |(mod (- x) y)| . 3))
     (12 12 (:REWRITE |(mod (- x) y)| . 2))
     (12 12 (:REWRITE |(mod (- x) y)| . 1))
     (12 12
         (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (12 12
         (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (6 6 (:REWRITE EXTRA-INTP-THM-1))
     (6 6
        (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 3))
     (6 6
        (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 2))
     (6 6
        (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 3))
     (6 6
        (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 2))
     (4 4 (:REWRITE |arith (+ c (+ d x))|))
     (4 4 (:REWRITE |(- (* c x))|))
     (3 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
     (3 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (3 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (3 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (2 2 (:REWRITE |(* x (- y))|))
     (1 1 (:REWRITE |(not (equal x (/ y)))|))
     (1 1 (:REWRITE |(equal x (/ y))|))
     (1 1 (:REWRITE |(/ (/ x))|)))
(MOD-SUMS-CANCEL-1
     (2574 13 (:REWRITE MOD-X-Y-=-X-Y . 1))
     (1935 13 (:REWRITE MOD-X-Y-=-X+Y . 1))
     (1189 144 (:REWRITE DEFAULT-PLUS-2))
     (835 835 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (835 835 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (835 835 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (835 835
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (835 835
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (835 835
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (835 835
          (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
     (835 835
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (835 835
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (651 144 (:REWRITE DEFAULT-PLUS-1))
     (587 23 (:REWRITE MOD-X-Y-=-X . 4))
     (587 23 (:REWRITE MOD-X-Y-=-X . 3))
     (505 76
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (347 23 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (342 38 (:LINEAR MOD-BOUNDS-3))
     (326 23 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (285 23 (:REWRITE MOD-ZERO . 4))
     (225 23 (:REWRITE MOD-ZERO . 3))
     (186 23 (:REWRITE CANCEL-MOD-+))
     (179 135 (:REWRITE SIMPLIFY-SUMS-<))
     (179 135
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (179 135
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (179 135 (:REWRITE DEFAULT-LESS-THAN-1))
     (179 23 (:REWRITE MOD-X-Y-=-X . 2))
     (178 23 (:REWRITE DEFAULT-MOD-RATIO))
     (135 135
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (135 135
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (135 135
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (135 135
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (135 135 (:REWRITE INTEGERP-<-CONSTANT))
     (135 135 (:REWRITE DEFAULT-LESS-THAN-2))
     (135 135 (:REWRITE CONSTANT-<-INTEGERP))
     (135 135
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (135 135
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (135 135
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (135 135
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (135 135 (:REWRITE |(< c (- x))|))
     (135 135
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (135 135
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (135 135
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (135 135
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (135 135 (:REWRITE |(< (/ x) (/ y))|))
     (135 135 (:REWRITE |(< (- x) c)|))
     (135 135 (:REWRITE |(< (- x) (- y))|))
     (117 117 (:REWRITE DEFAULT-TIMES-2))
     (117 117 (:REWRITE DEFAULT-TIMES-1))
     (111 23 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (98 98
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (98 98
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (98 98
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (98 98 (:REWRITE |(< 0 (/ x))|))
     (98 98 (:REWRITE |(< 0 (* x y))|))
     (88 88
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (88 88 (:REWRITE DEFAULT-DIVIDE))
     (88 23 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (88 23
         (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (84 12 (:REWRITE |(* y x)|))
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
     (76 76 (:LINEAR MOD-BOUNDS-2))
     (69 69 (:REWRITE REDUCE-INTEGERP-+))
     (69 69 (:REWRITE INTEGERP-MINUS-X))
     (69 69 (:META META-INTEGERP-CORRECT))
     (68 4 (:REWRITE |(* x (+ y z))|))
     (50 50 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (47 47
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (45 45
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (42 7 (:REWRITE |(* (- x) y)|))
     (28 28
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (28 28
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (28 28 (:REWRITE |(< (/ x) 0)|))
     (28 28 (:REWRITE |(< (* x y) 0)|))
     (28 7 (:REWRITE |(integerp (- x))|))
     (26 26 (:REWRITE |(equal (+ (- c) x) y)|))
     (23 23 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (23 23 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (23 23
         (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (23 23
         (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (23 23 (:REWRITE MOD-CANCEL-*-CONST))
     (23 23 (:REWRITE DEFAULT-MOD-2))
     (23 23 (:REWRITE DEFAULT-MOD-1))
     (23 23 (:REWRITE |(mod x (- y))| . 3))
     (23 23 (:REWRITE |(mod x (- y))| . 2))
     (23 23 (:REWRITE |(mod x (- y))| . 1))
     (23 23
         (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (23 23
         (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (23 23 (:REWRITE |(mod (- x) y)| . 3))
     (23 23 (:REWRITE |(mod (- x) y)| . 2))
     (23 23 (:REWRITE |(mod (- x) y)| . 1))
     (23 23
         (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (23 23
         (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (20 20 (:REWRITE |(+ c (+ d x))|))
     (16 4 (:REWRITE RATIONALP-X))
     (14 14 (:REWRITE DEFAULT-MINUS))
     (14 7 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
     (13 13
         (:REWRITE |(equal (mod (+ x y) z) x)|))
     (8 2 (:REWRITE |(+ x x)|))
     (7 7 (:REWRITE |(- (* c x))|))
     (4 4 (:REWRITE REDUCE-RATIONALP-+))
     (4 4 (:REWRITE REDUCE-RATIONALP-*))
     (4 4 (:REWRITE RATIONALP-MINUS-X))
     (4 4 (:REWRITE FOLD-CONSTS-IN-+))
     (4 4 (:REWRITE |(< (+ c/d x) y)|))
     (4 4 (:REWRITE |(< (+ (- c) x) y)|))
     (4 4 (:META META-RATIONALP-CORRECT))
     (2 2 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (2 2
        (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 3))
     (2 2
        (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 2))
     (2 2 (:REWRITE |(< y (+ (- c) x))|))
     (2 2 (:REWRITE |(< x (+ c/d y))|)))
(|(equal (mod a n) (mod b n))|
     (5526 32 (:REWRITE MOD-X-Y-=-X-Y . 1))
     (4044 138 (:LINEAR MOD-BOUNDS-2))
     (4044 138 (:LINEAR MOD-BOUNDS-1))
     (2905 32 (:REWRITE MOD-X-Y-=-X+Y . 1))
     (1201 924 (:REWRITE DEFAULT-PLUS-2))
     (1184 1184
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (1184 1184
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (1184 1184
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (1075 924 (:REWRITE DEFAULT-PLUS-1))
     (1008 51 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (979 51 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (918 51 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (918 51 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (857 577 (:REWRITE |(< c (- x))|))
     (854 854 (:REWRITE DEFAULT-TIMES-2))
     (854 854 (:REWRITE DEFAULT-TIMES-1))
     (854 574 (:REWRITE |(< (- x) c)|))
     (849 51 (:REWRITE DEFAULT-MOD-RATIO))
     (667 580 (:REWRITE |(< (- x) (- y))|))
     (598 580 (:REWRITE DEFAULT-LESS-THAN-2))
     (598 580 (:REWRITE DEFAULT-LESS-THAN-1))
     (580 580
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (580 580
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (580 580
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (580 580 (:REWRITE |(< (/ x) (/ y))|))
     (577 577
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (577 577
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (577 577
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (577 577
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (577 577
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (577 577
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (577 577
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (577 577
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (571 571
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (571 571 (:REWRITE INTEGERP-<-CONSTANT))
     (571 571 (:REWRITE CONSTANT-<-INTEGERP))
     (547 97 (:REWRITE |(equal (- x) c)|))
     (456 395
          (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-<))
     (431 395
          (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-<))
     (296 62 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (295 295
          (:REWRITE NORMALIZE-FACTORS-SCATTER-EXPONENTS))
     (268 268
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (260 56
          (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-EQUAL))
     (249 249 (:REWRITE |(< 0 (/ x))|))
     (249 249 (:REWRITE |(< 0 (* x y))|))
     (246 246 (:REWRITE DEFAULT-DIVIDE))
     (245 245
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (242 242 (:REWRITE |(< (/ x) 0)|))
     (242 242 (:REWRITE |(< (* x y) 0)|))
     (235 235 (:REWRITE DEFAULT-MINUS))
     (232 56
          (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-EQUAL))
     (228 228
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (228 228
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (221 221
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (221 221
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (203 203 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (173 167 (:META META-INTEGERP-CORRECT))
     (170 170
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (153 34
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (113 98 (:REWRITE |(equal (/ x) c)|))
     (104 26 (:REWRITE RATIONALP-X))
     (103 103 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (98 98
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (98 98
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (98 98 (:REWRITE |(equal c (/ x))|))
     (98 98 (:REWRITE |(equal (/ x) (/ y))|))
     (98 98 (:REWRITE |(equal (- x) (- y))|))
     (97 97 (:REWRITE |(equal c (- x))|))
     (92 92 (:REWRITE |(- (* c x))|))
     (90 90
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (88 88 (:REWRITE |(+ c (+ d x))|))
     (77 77
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (69 69 (:REWRITE |(equal (+ (- c) x) y)|))
     (51 51 (:REWRITE DEFAULT-MOD-2))
     (51 51 (:REWRITE DEFAULT-MOD-1))
     (49 49 (:REWRITE FOLD-CONSTS-IN-+))
     (45 45 (:REWRITE MOD-X-Y-=-X . 2))
     (45 45 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (45 45
         (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (43 43 (:REWRITE |(< (+ c/d x) y)|))
     (43 43 (:REWRITE |(< (+ (- c) x) y)|))
     (42 42
         (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (42 42
         (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (42 42 (:REWRITE MOD-CANCEL-*-CONST))
     (42 42 (:REWRITE |(mod x (- y))| . 3))
     (42 42 (:REWRITE |(mod x (- y))| . 2))
     (42 42 (:REWRITE |(mod x (- y))| . 1))
     (42 42 (:REWRITE |(mod (- x) y)| . 3))
     (42 42 (:REWRITE |(mod (- x) y)| . 2))
     (40 40 (:REWRITE |(< y (+ (- c) x))|))
     (40 40 (:REWRITE |(< x (+ c/d y))|))
     (36 36
         (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (36 36
         (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (36 36
         (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (36 36
         (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (32 32
         (:REWRITE |(equal (mod (+ x y) z) x)|))
     (28 28 (:REWRITE ARITH-NORMALIZE-ADDENDS))
     (26 26 (:REWRITE REDUCE-RATIONALP-+))
     (26 26 (:REWRITE REDUCE-RATIONALP-*))
     (26 26 (:REWRITE RATIONALP-MINUS-X))
     (26 26 (:META META-RATIONALP-CORRECT))
     (17 17
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (16 16
         (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (13 13
         (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 3))
     (13 13
         (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 2))
     (12 12
         (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 3))
     (12 12
         (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 2))
     (6 6 (:REWRITE |arith (+ c (+ d x))|))
     (3 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
     (3 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (3 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (3 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (3 3 (:REWRITE EXTRA-INTP-THM-1))
     (1 1 (:REWRITE |(not (equal x (/ y)))|))
     (1 1 (:REWRITE |(equal x (/ y))|))
     (1 1 (:REWRITE |(/ (/ x))|)))
(FIND-NASTY-FLOOR-ADDEND-1)
(FIND-NASTY-FLOOR-ADDEND)
(THE-FLOOR-ABOVE
     (237 33 (:REWRITE DEFAULT-PLUS-2))
     (170 33 (:REWRITE DEFAULT-PLUS-1))
     (146 18 (:REWRITE ACL2-NUMBERP-X))
     (144 4 (:REWRITE FLOOR-ZERO . 3))
     (116 4 (:REWRITE FLOOR-ZERO . 5))
     (116 4 (:REWRITE FLOOR-ZERO . 4))
     (112 4 (:REWRITE FLOOR-X-Y-=-1 . 3))
     (112 4 (:REWRITE FLOOR-X-Y-=-1 . 2))
     (112 4 (:REWRITE FLOOR-X-Y-=--1 . 3))
     (112 4 (:REWRITE FLOOR-X-Y-=--1 . 2))
     (105 105 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
     (105 105 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (105 105
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (105 105
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (105 105
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (105 105
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (105 105
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (105 105
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (103 103 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (103 103
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (103 103
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (103 103
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (103 103
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (103 103
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (103 103
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (91 40 (:REWRITE DEFAULT-LESS-THAN-1))
     (72 38
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (68 17 (:REWRITE RATIONALP-X))
     (60 4 (:REWRITE CANCEL-FLOOR-+))
     (58 7 (:REWRITE DEFAULT-MINUS))
     (57 40 (:REWRITE DEFAULT-LESS-THAN-2))
     (56 4 (:REWRITE FLOOR-ZERO . 2))
     (55 38 (:REWRITE |(< (- x) (- y))|))
     (54 37 (:REWRITE SIMPLIFY-SUMS-<))
     (45 45 (:REWRITE DEFAULT-TIMES-2))
     (38 38
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (38 38
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (38 38
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (38 38
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
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
     (36 4 (:REWRITE FLOOR-=-X/Y . 3))
     (36 4 (:REWRITE FLOOR-=-X/Y . 2))
     (35 35 (:REWRITE REDUCE-INTEGERP-+))
     (35 35 (:REWRITE INTEGERP-MINUS-X))
     (35 35 (:META META-INTEGERP-CORRECT))
     (30 30
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (29 29
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (24 4 (:REWRITE DEFAULT-FLOOR-RATIO))
     (24 4 (:REWRITE |(* (- x) y)|))
     (22 22 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (18 2 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
     (18 2 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (18 1 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (17 17 (:REWRITE REDUCE-RATIONALP-+))
     (17 17 (:REWRITE REDUCE-RATIONALP-*))
     (17 17 (:REWRITE RATIONALP-MINUS-X))
     (17 17 (:META META-RATIONALP-CORRECT))
     (16 16
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (16 16
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (16 16 (:REWRITE |(< (/ x) 0)|))
     (16 16 (:REWRITE |(< (* x y) 0)|))
     (16 4 (:REWRITE |(integerp (- x))|))
     (12 12
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (12 12
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (12 12 (:REWRITE |(< 0 (/ x))|))
     (12 12 (:REWRITE |(< 0 (* x y))|))
     (6 6
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (5 5
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (5 5
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (5 5 (:REWRITE |(equal c (/ x))|))
     (5 5 (:REWRITE |(equal c (- x))|))
     (5 5 (:REWRITE |(equal (/ x) c)|))
     (5 5 (:REWRITE |(equal (/ x) (/ y))|))
     (5 5 (:REWRITE |(equal (- x) c)|))
     (5 5 (:REWRITE |(equal (- x) (- y))|))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (4 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (4 4
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (4 4
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (4 4
        (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
     (4 4
        (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (4 4 (:REWRITE FLOOR-CANCEL-*-CONST))
     (4 4 (:REWRITE |(floor x (- y))| . 2))
     (4 4 (:REWRITE |(floor x (- y))| . 1))
     (4 4
        (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
     (4 4
        (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
     (4 4 (:REWRITE |(floor (- x) y)| . 2))
     (4 4 (:REWRITE |(floor (- x) y)| . 1))
     (4 4
        (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
     (4 4
        (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
     (4 4
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (4 4
        (:REWRITE |(< (* x (/ y)) 0) rationalp (* x (/ y))|))
     (4 4 (:REWRITE |(- (* c x))|))
     (2 2 (:REWRITE |(< (+ c/d x) y)|))
     (2 2 (:REWRITE |(< (+ (- c) x) y)|))
     (2 2 (:REWRITE |(+ c (+ d x))|))
     (1 1 (:REWRITE FOLD-CONSTS-IN-+))
     (1 1 (:REWRITE |(< y (+ (- c) x))|))
     (1 1 (:REWRITE |(< x (+ c/d y))|)))
(THE-FLOOR-BELOW
     (237 33 (:REWRITE DEFAULT-PLUS-2))
     (170 33 (:REWRITE DEFAULT-PLUS-1))
     (148 4 (:REWRITE FLOOR-ZERO . 3))
     (146 18 (:REWRITE ACL2-NUMBERP-X))
     (120 4 (:REWRITE FLOOR-ZERO . 5))
     (120 4 (:REWRITE FLOOR-ZERO . 4))
     (116 4 (:REWRITE FLOOR-X-Y-=-1 . 3))
     (116 4 (:REWRITE FLOOR-X-Y-=-1 . 2))
     (116 4 (:REWRITE FLOOR-X-Y-=--1 . 3))
     (116 4 (:REWRITE FLOOR-X-Y-=--1 . 2))
     (112 112 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
     (112 112 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (112 112
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (112 112
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (112 112
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (112 112
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (112 112
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (112 112
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (106 106 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (106 106
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (106 106
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (106 106
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (106 106
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (106 106
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (106 106
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (91 40 (:REWRITE DEFAULT-LESS-THAN-2))
     (72 38
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (68 17 (:REWRITE RATIONALP-X))
     (61 40 (:REWRITE THE-FLOOR-ABOVE))
     (60 4 (:REWRITE CANCEL-FLOOR-+))
     (58 7 (:REWRITE DEFAULT-MINUS))
     (57 40 (:REWRITE DEFAULT-LESS-THAN-1))
     (56 4 (:REWRITE FLOOR-ZERO . 2))
     (54 37 (:REWRITE SIMPLIFY-SUMS-<))
     (45 45 (:REWRITE DEFAULT-TIMES-2))
     (38 38
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (38 38
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (38 38
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (38 38
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
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
     (36 36 (:REWRITE REDUCE-INTEGERP-+))
     (36 36 (:REWRITE INTEGERP-MINUS-X))
     (36 36 (:META META-INTEGERP-CORRECT))
     (36 4 (:REWRITE FLOOR-=-X/Y . 3))
     (36 4 (:REWRITE FLOOR-=-X/Y . 2))
     (30 30
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (29 29
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (24 4 (:REWRITE DEFAULT-FLOOR-RATIO))
     (24 4 (:REWRITE |(* (- x) y)|))
     (22 22 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (18 2 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
     (18 2 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (18 1 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (17 17 (:REWRITE REDUCE-RATIONALP-+))
     (17 17 (:REWRITE REDUCE-RATIONALP-*))
     (17 17 (:REWRITE RATIONALP-MINUS-X))
     (17 17 (:META META-RATIONALP-CORRECT))
     (16 16
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (16 16
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (16 16 (:REWRITE |(< (/ x) 0)|))
     (16 16 (:REWRITE |(< (* x y) 0)|))
     (16 4 (:REWRITE |(integerp (- x))|))
     (12 12
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (12 12
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (12 12 (:REWRITE |(< 0 (/ x))|))
     (12 12 (:REWRITE |(< 0 (* x y))|))
     (8 8
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (8 8
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (8 8 (:REWRITE |(equal c (/ x))|))
     (8 8 (:REWRITE |(equal c (- x))|))
     (8 8 (:REWRITE |(equal (/ x) c)|))
     (8 8 (:REWRITE |(equal (/ x) (/ y))|))
     (8 8 (:REWRITE |(equal (- x) c)|))
     (8 8 (:REWRITE |(equal (- x) (- y))|))
     (7 7 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (7 7
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (7 7
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (6 6
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (4 4
        (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
     (4 4
        (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (4 4 (:REWRITE FLOOR-CANCEL-*-CONST))
     (4 4 (:REWRITE |(floor x (- y))| . 2))
     (4 4 (:REWRITE |(floor x (- y))| . 1))
     (4 4
        (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
     (4 4
        (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
     (4 4 (:REWRITE |(floor (- x) y)| . 2))
     (4 4 (:REWRITE |(floor (- x) y)| . 1))
     (4 4
        (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
     (4 4
        (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
     (4 4
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (4 4
        (:REWRITE |(< (* x (/ y)) 0) rationalp (* x (/ y))|))
     (4 4 (:REWRITE |(- (* c x))|))
     (2 2 (:REWRITE |(< y (+ (- c) x))|))
     (2 2 (:REWRITE |(< x (+ c/d y))|))
     (2 2 (:REWRITE |(+ c (+ d x))|))
     (1 1 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (1 1 (:REWRITE FOLD-CONSTS-IN-+))
     (1 1 (:REWRITE |(< (+ c/d x) y)|))
     (1 1 (:REWRITE |(< (+ (- c) x) y)|)))
